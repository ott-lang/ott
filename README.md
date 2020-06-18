# Ott

Ott is a tool for writing definitions of programming languages and
calculi.  It takes as input a definition of a language syntax and
semantics, in a concise and readable ASCII notation that is close to
what one would write in informal mathematics.  With appropriate
annotation, it can then generate output:

- a LaTeX source file that defines commands to build a typeset version of  the definition;
- a Coq version of the definition; 
- a HOL version of the definition;
- an Isabelle/HOL version of the definition; 
- a Lem version of the definition; 
- an OCaml version of the syntax of the definition; and
- (experimental) a menhir parser and crude pretty printer for the syntax.

Additionally, it can be run as a filter, taking a
LaTeX/Coq/Isabelle/HOL/Lem/OCaml source file with embedded (symbolic)
terms of the defined language, parsing them and replacing them by
typeset terms.


## Manual

* in the [Ott github](https://github.com/ott-lang/ott) built_doc directory, or
* [here (html)](http://www.cl.cam.ac.uk/~pes20/ott/top2.html)

## Papers

- [Ott: Effective Tool Support for the Working
  Semanticist](http://www.cl.cam.ac.uk/users/pes20/ott-jfp.pdf).
  Peter Sewell, Francesco Zappa Nardelli, Scott Owens, Gilles Peskine,
  Thomas Ridge, Susmit Sarkar, Rok Strni&#353;a. [Journal of
  Functional Programming 20(1):71-122,
  2010](http://journals.cambridge.org/repo_A71Keeig)

- [Ott: Effective Tool Support for the Working
  Semanticist](http://www.cl.cam.ac.uk/users/pes20/paper.pdf).  Peter
  Sewell, Francesco Zappa Nardelli, Scott Owens, Gilles Peskine,
  Thomas Ridge, Susmit Sarkar, Rok Strni&#353;a.  In [ICFP
  2007](http://www.informatik.uni-bonn.de/%7Eralf/icfp07.html)

- [Ott or
  Nott](http://www.cl.cam.ac.uk/users/pes20/wmm2010.pdf). Stephanie
  Weirich, Scott Owens, Peter Sewell, Francesco Zappa Nardelli. In
  [WMM 2010](http://www.cis.upenn.edu/~bcpierce/wmm/): 5th ACM SIGPLAN
  Workshop on Mechanizing Metatheory.

- [Binding and Substitution
  (draft)](http://www.cl.cam.ac.uk/users/pes20/bind-doc.pdf). Susmit
  Sarkar, Peter Sewell, Francesco Zappa Nardelli.  Note, 2007.

- [The experimental Coq locally-nameless backend
  (html)](http://moscova.inria.fr/~zappa/projects/ln_ott). Francesco
  Zappa Nardelli. Note, 2009.


## People

Ott has been principally devloped by 
<a href="http://www.cl.cam.ac.uk/~pes20">Peter Sewell</a>, 
<a href="http://moscova.inria.fr/~zappa">Francesco Zappa Nardelli</a>, and
<a href="http://www.cl.cam.ac.uk/~so294">Scott Owens</a>,
with contributions from many others including
Joey Eremondi,
Hannes Mehnert,
Karl Palmskog,
Matthew Parkinson,
Thibaut Pérami,
Gilles Peskine,
Alastair Reid,
Tom Ridge,
Susmit Sarkar,
Rok Strniša,
Viktor Vafeiadis.



## To install and build

Ott is available as 
an [opam](https://opam.ocaml.org) package and a 
[github repo](https://github.com/ott-lang/ott).

### With OPAM  (released version)

First, ensure you have opam (the OCaml package manager) installed,
version 2.0 or greater (opam 1 versions of ott are no longer
supported).  You can use your system's package manager e.g. `sudo
apt-get install opam` (e.g. on Ubuntu 20.04) or follow the
[instructions from the opam website](https://opam.ocaml.org/doc/Install.html).
On older Ubuntu versions you will not be able to use their package
manager's opam 1 version, and will need to install it following the
instructions on the opam website.

Then `opam install ott` will install the latest Ott version.  The
Emacs mode will be in `` $(opam config var
prefix)/share/emacs/site-lisp ``, and documentation in `` $(opam
config var prefix)/doc/ott ``.

If you want to use Ott with the Coq proof assistant, to install the
Ott auxiliary files for Coq, first activate the `coq-released` OPAM
repository:

`opam repo add coq-released https://coq.inria.fr/opam/released`

and then run `opam install coq-ott`.


### With OPAM (github checkout)

In the checkout directory, run `opam pin add ott .`.

To rebuild and reinstall after local changes, run `opam upgrade --working-dir ott`  (or `opam upgrade -w ott`).

### Without OPAM

Ott depends on OCaml version 4.00.0 or later. It builds with (at
least) OCaml 4.02.3 and 4.10.0. 

The command `make` (`make world`) builds the `ott` binary in the `bin/` subdirectory.

This will compile Ott using `ocamlopt`.  To force it to
compile with `ocamlc` (which may give significantly slower execution
of Ott), do `make world.byt`.

To build the Ott auxiliary files for Coq, go to the `coq/` subdirectory
and run `make`. To install the resulting files in Coq's `user-contrib`,
run `make install`.




## To run

Ott runs as a command-line tool. Executing `ott` shows the
usage and options.  To run Ott on the test file
`tests/test10.ott`, generating LaTeX in `test10.tex` and
Coq in `test10.v`, type:

  `ott -i tests/test10.ott -o test10.tex -o test10.v`

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





## Copyright information

The ocamlgraph library is distributed under the LGPL (from
http://www.lri.fr/~filliatr/ftp/ocamlgraph/); we include a snapshot
for convenience. For its authorship and copyright information see the
files therein.

All other files are distributed under the BSD-style licence in LICENCE.
