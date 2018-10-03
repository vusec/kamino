# We have to export OPAMLIB so we can use syntax extensions
# If there is a better way to refer to this location in ocp-build
# then we can use that.
export OPAMLIB:=$(shell opam config var lib)

PROGS=kamino various-test gen-batch-spec \
	debug-config eval

fast: deps
	ocp-build $(PROGS)

all: $(PROGS)

scan rescan:
	ocp-build build -scan

# These targets only work if their OCP defintions specify the target.
# By default both are defined, but if one has has_byte = false,
# the *.byte will fail!
asm: $(addsuffix .asm, $(PROGS))
byte: $(addsuffix .byte, $(PROGS))

.PHONY : deps
deps:
ifeq (,$(wildcard deps/bap/Makefile))
	$(error Cannot locate BAP framework in the deps directory!)
endif

ifeq (,$(wildcard ocp-build.root))
	$(info Initializing ocp-build project)
	ocp-build -init
	ocp-build configure -digest -install-bindir bin -install-datadir data
endif

$(PROGS): deps
ifndef VERBOSITY
	ocp-build $@
else
	ocp-build -verbosity $(VERBOSITY) $@
endif

%.asm: deps
ifndef VERBOSITY
	ocp-build -asm $(basename $@)
else
	ocp-build -asm -verbosity $(VERBOSITY) $(basename $@)
endif

%.byte: deps
ifndef VERBOSITY
	ocp-build -byte $(basename $@)
else
	ocp-build -byte -verbosity $(VERBOSITY) $(basename $@)
endif

.PHONY : tests
tests: deps
ifndef VERBOSITY
	ocp-build tests
else
	ocp-build tests -verbosity $(VERBOSITY)
endif

.PHONY: clean
clean: deps
	ocp-build clean

.PHONY : install
install:
	ocp-build install

.PHONY : uninstall
uninstall:
	ocp-build uninstall
