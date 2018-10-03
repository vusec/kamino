FROM jgoerzen/debian-base-standard:jessie

RUN apt update && apt install -y ca-certificates libpcre3-dev m4 opam pkg-config && useradd -m -s /bin/bash kamino
# Protobuf needs C++ and -m32
RUN apt install -y autoconf binutils-dev emacs-nox gcc-multilib lib32stdc++-4.9-dev libgmp-dev libiberty-dev libmagic-dev libtool zlib1g-dev

USER kamino
WORKDIR /home/kamino

ADD easy-format-make.patch /home/kamino/easy-format-make.patch
ADD meta-tpl.patch /home/kamino/meta-tpl.patch
RUN opam init -y && opam switch -A 3.12.1 kamino && eval `opam config env`
RUN opam install -y batteries.2.6.0
RUN opam install -y core.108.08.00 core_extended.108.08.00

RUN opam install -y camlidl.1.05 camomile.0.8.5 fileutils.0.5.2 lwt.2.4.6 magic.0.7.3 objsize.0.17 ocamlgraph.1.8.7 ocp-build.1.99.16-beta ulex.1.1 xmlm.1.1.1 zarith.1.5

# Manually patch easy-format.1.0.1 to produce .cmxa files
RUN (eval `opam config env` && git clone https://github.com/mjambon/easy-format.git && cd easy-format && git checkout v1.0.1 && patch <~/easy-format-make.patch && patch <~/meta-tpl.patch && make && make install && opam install --fake easy-format.1.0.1 )

RUN opam install -y biniou.1.0.9 yojson.1.2.3

RUN git clone https://github.com/vusec/kamino.git
RUN (cd kamino/deps && git clone https://github.com/vusec/bap.git )

# Awkward. piqi-0.6.0 doesn't know about opam, so we need to install it manually.
RUN (eval `opam config env` && git clone https://github.com/alavrik/piqi.git && cd piqi && git checkout v0.6.0 && ./configure --prefix=`opam config var prefix` && make && make install && make ocaml && make ocaml-install)


WORKDIR /home/kamino/kamino/deps/bap
RUN (eval `opam config env` && ./autogen.sh && ./configure && make)

WORKDIR /home/kamino/kamino
RUN (eval `opam config env` && make)

RUN (eval `opam config env` && opam install -y caml-mode tuareg 1>&2 && echo '(load "/home/kamino/.opam/kamino/share/emacs/site-lisp/tuareg-site-file.el")') >>~/.emacs
RUN echo 'eval `opam config env`' >>~/.bashrc
CMD bash
