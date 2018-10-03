#!/usr/bin/env python

from __future__ import print_function
from argparse import ArgumentParser, Action
from collections import namedtuple
import sys

from elftools.elf.elffile import ELFFile
from elftools.dwarf.constants import *
from elftools.dwarf.ranges import RangeEntry, BaseAddressEntry

from memoized_property import memoized_property
import sexpdata

# Monkey patch the string representation of a range entry
RangeEntry.__str__ = lambda self: "0x%x - 0x%x" % (self.begin_offset, self.end_offset)

def to_sexp(t):
    if hasattr(t, 'to_sexp'):
        return t.to_sexp()
    return sexpdata.tosexp(t, str_as='symbol')

# You shall not monkey patch builtins!
class my_list(list):
    def to_sexp(self):
        return "({})".format(" ".join(map(lambda x: to_sexp(x), self)))

class LineInfo(object):
    def __init__(self, filename, line, column):
        self.filename = filename if filename else ''
        self.line = line if line else 0
        self.column = column if column else 0

    def __str__(self):
        return "{}:{}:{}".format(self.filename, self.line, self.column)

InlineInfo = namedtuple('InlineInfo', 'callees expansions')

def format_human(data):
    return str(data)
def format_sexp(data):
    if hasattr(data, 'to_sexp'):
        return data.to_sexp()
    return sexpdata.dumps(data, str_as='symbol')

class DIE(object):
    def __init__(self, die):
        self.die = die

    def __getattr__(self, attr):
        if hasattr(self.die, attr):
            return getattr(self.die, attr)
        elif attr.startswith('has_'):
            return lambda : ('DW_AT_' + attr[len('has_'):]) in self.die.attributes
        elif attr.startswith('is_'):
            return lambda : ('DW_TAG_' + attr[len('is_'):]) == self.die.tag
        else:
            die_attr = "DW_AT_%s" % attr
            if die_attr in self.die.attributes:
                return self.die.attributes[die_attr]
            raise AttributeError(attr)

    def __eq__(self, other):
        if isinstance(other, self.__class__):
            # Use the offset in the stream to determine equality
            return self.offset == other.offset
        else:
            return False

    @memoized_property
    def name(self):
        if self.has_name():
            return self.attributes['DW_AT_name'].value
        if self.has_abstract_origin():
            ao = self.abstract_origin
            if ao.has_name():
                return ao.name
        return None

    @memoized_property
    def abstract_origin(self):
        if self.has_abstract_origin():
            ao = self.attributes['DW_AT_abstract_origin']
            ref = ao.value
            form = ao.form
            if form in map(lambda i: "DW_FORM_ref%i" % i, [1,2,4,8]):
                offset = self.cu.cu_offset + ref
                return DIE([die for die in self.cu.iter_DIEs() if die.offset == offset][0])
            elif form == 'DW_FORM_ref_udata':
                raise "Unsupported reference form udata!"
            elif form == 'DW_FORM_ref_addr':
                raise "Unsupported reference form addr!"
            elif form == 'DW_FORM_ref_sig8':
                raise "Unsupported reference form sig8!"
            else:
                raise "Unknown reference form!"
        else:
            return None

    @memoized_property
    def range(self):
        if self.has_low_pc() and not self.has_high_pc():
            return [RangeEntry(self.low_pc.value, self.low_pc.value)]
        elif self.has_low_pc() and self.has_high_pc():
            if self.high_pc.form.startswith('DW_FORM_data'):
                return [RangeEntry(self.low_pc.value, self.low_pc.value + self.high_pc.value)]
            elif self.high_pc.form == 'DW_FORM_addr':
                return [RangeEntry(self.low_pc.value, self.high_pc.value)]
            else:
             raise "Unhandled DW_AT_high_pc class!"
        elif self.has_ranges():
            range_lists = self.dwarfinfo.range_lists()
            range_list = range_lists.get_range_list_at_offset(self.ranges.value)
            def map_entry():
                # range list entries are relative to the CU's base address
                top_die = DIE(self.cu.get_top_DIE())
                offset = [top_die.entry_pc.value] if top_die.has_entry_pc() else [top_die.low_pc.value]
                def f(entry):
                    if type(entry) is BaseAddressEntry:
                        offset[0] = entry.base_address
                        return None
                    elif type(entry) is RangeEntry:
                        return RangeEntry(begin_offset=entry.begin_offset + offset[0],
                                          end_offset=entry.end_offset + offset[0])
                    else:
                        raise "Invalid rangelist entry type!"
                return f
            return filter(None,map(map_entry(), range_list))

        else:
            return None

    @memoized_property
    def lineinfo(self):
        if not self.has_call_file():
            return None
        lineprogram = self.dwarfinfo.line_program_for_CU(self.cu)
        linetable = filter(lambda e : e.state != None, lineprogram.get_entries())

        call_file = self.call_file.value
        # The value zero means not specified according to the DWARF Std, so use
        # this in case it is actually not specified.
        call_line = self.call_line.value if self.has_call_line() else 0
        call_column = self.call_column.value if self.has_call_column() else 0
        entry = [entry for entry in linetable if entry.state.file == call_file and entry.state.line == call_line]
        if len(entry) == 1:
            filename = lineprogram.header['file_entry'][entry[0].state.file - 1].name
            return LineInfo(filename=filename, line=call_line, column=call_column)
        else:
            return None

    @memoized_property
    def parent_subprogram(self):
        parent = self
        while True:
            parent = parent.get_parent()
            if parent:
                parent = DIE(parent)
                if parent.is_subprogram():
                    return parent
            else:
                return None

class InlineInstance(object):
    def __init__(self, caller, inline, callees):
        if isinstance(caller, DIE) and isinstance(inline, DIE):
            self.caller = caller
            self.inline = inline
        else:
            raise ValueError('Invalid type for caller or inline, expected a DIE!')
        if isinstance(callees, list):
            self.callees = callees
        else:
            raise ValueError('Invalid type for callees, expected a list')

    def to_sexp(self):
        sexp = [
        ["caller",
         [["name", "\"{}\"".format(self.caller.name)],
          ["range", self.caller.range]]],
        ["inline",
         [["name", "\"{}\"".format(self.inline.name)],
          ["range", self.inline.range]]],
        ["callees", [["ranges", [callee.range for callee in self.callees]]]]]
        return sexpdata.tosexp(sexp, str_as='symbol')

    def __str__(self):
        return "{0.name!s} {0.range!s} {0.lineinfo!s} > {1.name!s} {1.range!s} {1.lineinfo!s}".format(
            self.caller, self.inline)

class Export(object):
    def __init__(self, binary, inline_instances):
        self.binary = binary
        self.inline_instances = inline_instances

    def to_sexp(self):
        return "((binary {}) (inlines {}))".format(self.binary,
                                                   self.inline_instances.to_sexp())

def process_elf(path):
    with open(path, 'rb') as f:
        elf = ELFFile(f)

        if not elf.has_dwarf_info():
            print("Elf at %s contains no dwarf info" % path)
            return

        dwarfinfo = elf.get_dwarf_info()

        inlines = {}
        for cu in dwarfinfo.iter_CUs():
            for die in [DIE(die) for die in cu.iter_DIEs()]:
                # We are only interested in concrete inline expansions.
                if die.is_inlined_subroutine():
                    if die.has_abstract_origin():
                        ao = die.abstract_origin
                        if ao:
                            if ao.offset in inlines:
                                inline_info = inlines[ao.offset]
                                inline_info.expansions.append(die)
                            else:
                                inline_info = InlineInfo(callees=[], expansions=[die])
                                inlines[ao.offset] = inline_info
                    else:
                        print("Found unknown inline expansion!")
                elif die.is_subprogram():
                    if die.has_abstract_origin():
                        ao = die.abstract_origin
                        if ao:
                            if ao.offset in inlines:
                                inline_info = inlines[ao.offset]
                                inline_info.callees.append(die)
                            else:
                                inlines[ao.offset] = InlineInfo(callees=[die], expansions=[])
        return inlines.values()

def export(args):
    for binary in args.binaries:
        inlines = process_elf(binary)
        inlines_with_callees = filter(lambda x: len(x.callees) > 0 and len(x.expansions) > 0, inlines)
        inlines_without_callees = filter(lambda x: len(x.callees) == 0 and len(x.expansions) > 0, inlines)
        def dump(f, inlines):
            formatted_instances = my_list()
            for inline_info in inlines_with_callees:
                for die in inline_info.expansions:
                    parent = die.parent_subprogram if die.parent_subprogram else None
                    instance = InlineInstance(parent, die, inline_info.callees)
                    formatted_instances.append(instance)
            export = Export(binary, formatted_instances)
            f.write(args.output_formatter(export))
        if args.stdout:
            dump(sys.stdout, inlines_with_callees)
            dump(sys.stdout, inlines_without_callees)
        else:
            with open(binary + '.inlines', 'w') as f:
                dump(f, inlines_with_callees)

            with open(binary + '.useless_inlines', 'w') as f:
                dump(f, inlines_without_callees)

def stats(args):
    for binary in args.binaries:
        inlines = process_elf(binary)
        inlines_with_callees = filter(lambda x: len(x.callees) > 0 and len(x.expansions) > 0, inlines)
        print("{0}: {1} / {2} with callees and {3} / {2} without".format(binary,
                                                                         len(inlines_with_callees),
                                                                         len(inlines),
                                                                         len(inlines) - len(inlines_with_callees)))

class StoreFmt(Action):
    def __call__(self, parser, namespace, values, option_string=None):
        setattr(namespace, self.dest, output_formatters[values[0]])

if __name__ == '__main__':
    output_formatters = {"human": format_human, "sexp": format_sexp}

    # Use parent parser to share the positional arguments among subcommand parsers
    parent_parser = ArgumentParser(add_help=False)
    parent_parser.add_argument('binaries', metavar='BINARY', nargs='+',
                               help='a binary with symbols to parse for inlines')

    parser = ArgumentParser()
    subparsers = parser.add_subparsers()

    export_parser = subparsers.add_parser('export', parents=[parent_parser])
    export_parser.add_argument("-f", "--fmt",
                        dest="output_formatter",
                        action=StoreFmt,
                        choices=output_formatters.keys(),
                        nargs=1,
                        default=output_formatters["sexp"],
                        metavar='FMT',
                        help="specify the output format [human|sexp] (default: human)")

    export_parser.add_argument("-s", "--stdout",
                        dest="stdout",
                        action="store_true",
                        default=False,
                        help="print output to stdout")

    export_parser.set_defaults(func=export)

    stats_parser = subparsers.add_parser('stats', parents=[parent_parser])
    stats_parser.set_defaults(func=stats)

    args = parser.parse_args()
    args.func(args)
