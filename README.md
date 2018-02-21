# Ott

A tool for writing definitions of programming languages and calculi

by Peter Sewell, Francesco Zappa Nardelli, and Scott Owens.

## Repository and Package

Ott is now [available from github](https://github.com/ott-lang/ott), and as
an [opam](https://opam.ocaml.org) package.

We no longer provide non-github tarballs or a Windows distribution.


## Directory contents

directory                | description
-----------------------  | -------------------------------------------------
`aux/`                   | auxiliary code (y2l) used to build the user guide
`bin/`                   | the Ott binary
`built_doc/`             | the user guide, in html, pdf, and ps
`coq/`                   | auxiliary files for Coq
`doc/`                   | the user guide sources
`emacs/`                 | an Ott Emacs mode
`examples/`              | some larger example Ott files
`tex/`                   | auxiliary files for LaTeX
`hol/`                   | auxiliary files for HOL
`menhir/`                | auxiliary files for menhir
`ocamlgraph-1.7.tar.gz`  | a copy of the ocamlgraph library
`regression/`            | regression-test machinery
`tests/`                 | various small example Ott files
`src/`                   | the (OCaml) Ott sources
`Makefile`               | a Makefile for the examples
`LICENCE`                | the BSD-style licence terms
`README.md`              | this file (Section 2 of the user guide)
`revisionhistory.txt`    | the revision history



## To build

### With OPAM

If you have [OPAM](https://opam.ocaml.org) installed on your system,
`opam install ott` will install the latest Ott version.  The Emacs mode
will be in `` `opam config var prefix`/share/emacs/site-lisp ``, and
documentation in `` `opam config var prefix`/doc/ott ``.

To install the Ott auxiliary files for Coq, first activate the
`coq-released` OPAM repository:

`opam repo add coq-released https://coq.inria.fr/opam/released`

and then run `opam install coq-ott`.

### Without OPAM

Ott depends on OCaml version 4.00.0 or later. It builds with (at
least) OCaml 4.02.3.

The command `make` (`make world`) builds the `ott` binary in the `bin/` subdirectory.

This will compile Ott using `ocamlopt`.  To force it to
compile with `ocamlc` (which may give significantly slower execution
of Ott), do `make world.byt`.

To build the Ott auxiliary files for Coq, go to the `coq/` subdirectory
and run `make`. To install the resulting files in Coq's `user-contrib`,
run `make install`.

## To run

Ott runs as a command-line tool. Executing `bin/ott` shows the
usage and options.  To run Ott on the test file
`tests/test10.ott`, generating LaTeX in `test10.tex` and
Coq in `test10.v`, type:

  `bin/ott -i tests/test10.ott -o test10.tex -o test10.v`

Isabelle, HOL, and Lem can be generated with options `-o test10.thy`,
`-o test10Script.sml`, and `-o test10.lem`, respectively.

The Makefile has various sample targets, `make tests/test10.out`,
`make test7`, etc.  Typically they generate:

filename          | description
----------------  | ----------------------------------
`out.tex`         | LaTeX source for a definition
`out.ps`          | the postscript built from that
`out.v`           | Coq source
`outScript.sml`   | HOL source
`out.thy`         | Isabelle source

from files `test10.ott`, `test8.ott`, etc., in `tests/`.

## Manual

* in the [Ott github](https://github.com/ott-lang/ott) built_doc directory, or
* [here (html)](http://www.cl.cam.ac.uk/~pes20/ott/top2.html)

## Editor Plugins

### Emacs mode

The file `emacs/ott-mode.el` defines a very simple Emacs mode for syntax
highlighting of Ott source files.  It can be used by, for example,
adding the following to your `.emacs` file, replacing `PATH` by a path to your
Ott Emacs directory.

```ELisp
(setq load-path (cons (expand-file-name "PATH") load-path))
(require 'ott-mode)
```

For installations using OPAM on \*nix systems, it is sufficient to use the following code, which will call `opam config var prefix` at load-time.

```ELisp
(setq opam-share (substring (shell-command-to-string "opam config var share") 0 -1))
(add-to-list 'load-path (concat opam-share "/emacs/site-lisp"))
(require 'ott-mode)
```

### Visual Studio Code

There is a [plugin for VSCode](https://marketplace.visualstudio.com/items?itemName=JoeyEremondi.ott), which features syntax highlighting and inline error reporting. 

## Mailing lists

* [cl-ott-announce announcement mailing list](https://lists.cam.ac.uk/mailman/listinfo/cl-ott-announce)
* [cl-ott-discuss discussion mailing list](https://lists.cam.ac.uk/mailman/listinfo/cl-ott-discuss)

## Web page with examples

* [here](http://www.cl.cam.ac.uk/users/pes20/ott)

## Copyright information

The ocamlgraph library is distributed under the LGPL (from
http://www.lri.fr/~filliatr/ftp/ocamlgraph/); we include a snapshot
for convenience. For its authorship and copyright information see the
files therein.

All other files are distributed under the BSD-style licence in LICENCE.
