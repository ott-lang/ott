# Ott

Ott is a tool for writing definitions of programming languages and
calculi.  It takes as input a definition of a language syntax and
semantics, in a concise and readable ASCII notation that is close to
what one would write in informal mathematics.  With appropriate
annotations, it can then generate output:

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

Most simply, Ott can be used to aid informal LaTeX mathematics.
Here it permits the definition, and terms within proofs and
exposition, to be written in a clear, editable, ASCII  notation, without LaTeX
noise. It generates good-quality typeset output. 
By parsing (and so sort-checking) this input, it quickly catches a
range of simple errors, e.g. inconsistent use of judgement forms or
metavariable naming conventions. 

That same input can be used to generate formal definitions, for Coq,
HOL, Isabelle, and Lem.  It should thereby enable a smooth transition
between use of informal and formal mathematics.  Additionally, the
tool can automatically generate definitions of functions for free
variables, single and multiple substitutions, subgrammar checks
(e.g. for value subgrammars), and binding auxiliary functions.
At present only a fully concrete representation of binding, without
quotienting by alpha equivalence, is fully supported.  An experimental
backend generates a locally-nameless representation of terms for a
subset of the Ott metalanguage: details can be
found at http://moscova.inria.fr/~zappa/projects/ln_ott.

The distribution includes several examples, in varying levels of completeness:
untyped and simply typed lambda-calculus,
a calculus with ML polymorphism, 
the POPLmark Fsub with and without records,
an ML module system taken from (Leroy, JFP 1996) and equipped with an
operational semantics, and 
LJ, a lightweight Java fragment.
More substantially, Ott has been used for work on 
<a href="http://www.cl.cam.ac.uk/research/pls/javasem/">iJAM and LJAM, Java Module
  Systems</a>, by <a href="http://www.cl.cam.ac.uk/~rs456">Rok
  Strnisa</a>, and semantics for 
<a href="http://www.cl.cam.ac.uk/~so294/ocaml">OCaml light</a>, by
  <a href="http://www.cl.cam.ac.uk/~so294">Scott Owens</a>.

As of 2020, Ott remains in continuous use.

## Documentation

* the manual is in the [Ott github](https://github.com/ott-lang/ott)
  built_doc directory, or [here
  (html)](http://www.cl.cam.ac.uk/~pes20/ott/top2.html)

- [Binding and
  Substitution](http://www.cl.cam.ac.uk/users/pes20/ott/bind-doc.pdf). Susmit
  Sarkar, Peter Sewell, Francesco Zappa Nardelli.  Note, 2007.

- [The experimental Coq locally-nameless backend
  (html)](http://moscova.inria.fr/~zappa/projects/ln_ott). Francesco
  Zappa Nardelli. Note, 2009.

## Papers

- [Ott: Effective Tool Support for the Working
  Semanticist](http://www.cl.cam.ac.uk/users/pes20/ott/ott-jfp.pdf).
  Peter Sewell, Francesco Zappa Nardelli, Scott Owens, Gilles Peskine,
  Thomas Ridge, Susmit Sarkar, Rok Strnisa. [Journal of
  Functional Programming 20(1):71-122,
  2010](http://journals.cambridge.org/repo_A71Keeig)

- [Ott: Effective Tool Support for the Working
  Semanticist](http://www.cl.cam.ac.uk/users/pes20/ott/paper.pdf).  Peter
  Sewell, Francesco Zappa Nardelli, Scott Owens, Gilles Peskine,
  Thomas Ridge, Susmit Sarkar, Rok Strnisa.  In [ICFP
  2007](http://www.informatik.uni-bonn.de/%7Eralf/icfp07.html)

- [Ott or
  Nott](http://www.cl.cam.ac.uk/users/pes20/ott/wmm2010.pdf). Stephanie
  Weirich, Scott Owens, Peter Sewell, Francesco Zappa Nardelli. In
  [WMM 2010](http://www.cis.upenn.edu/~bcpierce/wmm/): 5th ACM SIGPLAN
  Workshop on Mechanizing Metatheory.



## People

Ott has been principally developed by
<a href="http://www.cl.cam.ac.uk/~pes20">Peter Sewell</a>, 
<a href="http://moscova.inria.fr/~zappa">Francesco Zappa Nardelli</a>, and
<a href="http://www.cl.cam.ac.uk/~so294">Scott Owens</a>,
with contributions from many others including
Joey Eremondi,
Hannes Mehnert,
Karl Palmskog,
Matthew Parkinson,
Thibaut Perami,
Gilles Peskine,
Alastair Reid,
Tom Ridge,
Susmit Sarkar,
Rok Strnisa,
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
manager's opam 1 version, and will need to install opam 2 following the
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

Ott depends on OCaml version 4.07.0 or later and the ocamlgraph package. It
builds with (at least) OCaml 4.07.0 and 4.14.0, and ocamlgraph 1.8.8. 

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


## Bug Tracker
- Please now use the github issue tracker (though our resources for fixing issues are very limited)
-  The previous issue tracker is <a href="https://gforge.inria.fr/tracker/?group_id=2980">here</a>



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



## Examples

The following LaTeX, Coq, HOL, and Isabelle files, except the proof scripts, are all automatically generated from the Ott sources.


<table>
<tr>
      <th rowspan="2">System</th>
      <th rowspan="2">Rules</th>
      <th rowspan="2">Ott sources</th>
      <th rowspan="2">Latex</th>
      <th rowspan="2">Typeset</th>
      <th rowspan="2">Dot</th>
      <th colspan="2">Coq</th>
      <th colspan="2">HOL</th>
      <th colspan="2">Isabelle</th>
</tr>      
<tr>
      <th> Defn </th>
      <th> Proof </th>
      <th> Defn </th>
      <th> Proof </th>
      <th> Defn </th>
      <th> Proof </th>
      </tr>

        

<tr>
<td>Untyped CBV lambda</td>
<td>3</td>
<td><a  type="text/plain" href="http://www.cl.cam.ac.uk/users/pes20/ott/test10.ott"><code>test10.ott</code></a></td>
<td><a  type="text/plain" href="http://www.cl.cam.ac.uk/users/pes20/ott/test10.tex"><code>test10.tex</code></a></td>
<td> <!-- <a href="http://www.cl.cam.ac.uk/users/pes20/ott/test10.pdf">(pdf)</a>&nbsp;--> <a href="http://www.cl.cam.ac.uk/users/pes20/ott/test10.ps">(ps)</a></td> 
<td></td>
<td><a  type="text/plain" href="http://www.cl.cam.ac.uk/users/pes20/ott/test10.v"><code>test10.v</code></a></td>
<td></td>
<td><a  type="text/plain" href="http://www.cl.cam.ac.uk/users/pes20/ott/test10Script.sml"><code>test10Script.sml</code></a></td>
<td></td>
<td><a  type="text/plain" href="http://www.cl.cam.ac.uk/users/pes20/ott/test10.thy"><code>test10.thy</code></a></td>
<td></td>
</tr>     

<tr>
<td>Simply typed CBV lambda</td>
<td>6</td>
<td><a  type="text/plain" href="http://www.cl.cam.ac.uk/users/pes20/ott/test10st.ott"><code>test10st.ott</code></a></td>
<td><a  type="text/plain" href="http://www.cl.cam.ac.uk/users/pes20/ott/test10st.tex"><code>test10st.tex</code></a></td>
<td> <!-- <a href="http://www.cl.cam.ac.uk/users/pes20/ott/test10st.pdf">(pdf)</a>&nbsp;--> <a href="http://www.cl.cam.ac.uk/users/pes20/ott/test10st.ps">(ps)</a></td> 
<td></td>
<td><a  type="text/plain" href="http://www.cl.cam.ac.uk/users/pes20/ott/test10st.v"><code>test10st.v</code></a></td>
<td><a  type="text/plain" href="http://www.cl.cam.ac.uk/users/pes20/ott/test10st_metatheory.v"><code>test10st_metatheory.v</code></a></td>
<td><a  type="text/plain" href="http://www.cl.cam.ac.uk/users/pes20/ott/test10stScript.sml"><code>test10stScript.sml</code></a></td>
<td><a  type="text/plain" href="http://www.cl.cam.ac.uk/users/pes20/ott/test10st_metatheoryScript.sml"><code>test10st_metatheoryScript.sml</code></a></td>
<td><a  type="text/plain" href="http://www.cl.cam.ac.uk/users/pes20/ott/test10st.thy"><code>test10st.thy</code></a></td>
<td><a  type="text/plain" href="http://www.cl.cam.ac.uk/users/pes20/ott/test10st_metatheory.thy"><code>test10st_metatheory.thy</code></a></td>
</tr>     

<tr>
<td>ML polymorphism</td>
<td>22</td>
<td><a  type="text/plain" href="http://www.cl.cam.ac.uk/users/pes20/ott/test8.ott"><code>test8.ott</code></a></td>
<td><a  type="text/plain" href="http://www.cl.cam.ac.uk/users/pes20/ott/test8.tex"><code>test8.tex</code></a></td>
<td><!-- <a href="http://www.cl.cam.ac.uk/users/pes20/ott/test8.pdf">(pdf)</a>&nbsp; --> <a href="http://www.cl.cam.ac.uk/users/pes20/ott/test8.ps">(ps)</a></td> 
<td></td>
<td><a  type="text/plain" href="http://www.cl.cam.ac.uk/users/pes20/ott/test8.v"><code>test8.v</code></a></td>
<td></td>
<td><a  type="text/plain" href="http://www.cl.cam.ac.uk/users/pes20/ott/test8Script.sml"><code>test8Script.sml</code></a></td>
<td></td>
<td><a  type="text/plain" href="http://www.cl.cam.ac.uk/users/pes20/ott/test8.thy"><code>test8.thy</code></a></td>
<td></td>
</tr>     

<tr>
<td>TAPL roughly-full-simple</td>
<td>63</td>
<td><a href="http://www.cl.cam.ac.uk/users/pes20/ott/examples/tapl">(sources)</a></td>
<td></td>
<td><a href="http://www.cl.cam.ac.uk/users/pes20/ott/examples/tapl/stlc.ps">(ps)</a></td>
<td></td>
<td><a href="http://www.cl.cam.ac.uk/users/pes20/ott/examples/tapl/records_auto.v">(Coq (including records))</a></td>
<td></td>
<td><a href="http://www.cl.cam.ac.uk/users/pes20/ott/examples/tapl/stlcScript.sml">(HOL)</a></td>
<td><a href="http://www.cl.cam.ac.uk/users/pes20/ott/examples/tapl/metatheoryScript.sml">(script)</a></td>
<td><a href="http://www.cl.cam.ac.uk/users/pes20/ott/examples/tapl/stlc.thy">(Isabelle)</a></td>
<td><a href="http://www.cl.cam.ac.uk/users/pes20/ott/examples/tapl/stlc_metatheory.thy">(script)</a></td>
</tr>

<tr>
<td>POPLmark Fsub (*)</td>
<td>48</td>
<td><a href="http://www.cl.cam.ac.uk/users/pes20/ott/tmp_test7.ott">(sources)</a></td>
<td><a href="http://www.cl.cam.ac.uk/users/pes20/ott/test7.tex">(latex)</a></td>
<td><a href="http://www.cl.cam.ac.uk/users/pes20/ott/test7.pdf">(pdf)</a> &nbsp; <a href="http://www.cl.cam.ac.uk/users/pes20/ott/test7.ps">(ps)</a></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>


<tr>
<td>Leroy JFP96 module system (*)</td>
<td>67</td>
<td><a href="http://www.cl.cam.ac.uk/users/pes20/ott/leroy-jfp96.ott"><code>leroy-jfp96.ott</code></a></td>
<td><a href="http://www.cl.cam.ac.uk/users/pes20/ott/leroy-jfp96.tex">(latex)</a></td>
<td><!-- <a href="http://www.cl.cam.ac.uk/users/pes20/ott/leroy-jfp96.pdf">(pdf)</a> &nbsp; --> <a href="http://www.cl.cam.ac.uk/users/pes20/ott/leroy-jfp96.ps">(ps)</a></td>
<td></td>
<td></td>
<td></td>
<td><a  type="text/plain" href="http://www.cl.cam.ac.uk/users/pes20/ott/leroy-jfp96Script.sml">(HOL)</a></td>
<td></td>
<td></td>
<td></td>
</tr>


<tr>
<td><a href="http://www.cl.cam.ac.uk/research/pls/javasem/lj/">LJ: Lightweight Java</a></td>
<td>85</td>
<td><a href="http://www.cl.cam.ac.uk/research/pls/javasem/lj/">(sources)</a></td>
<td></td>
<td><a href="http://www.cl.cam.ac.uk/research/pls/javasem/lj/lj.pdf">(pdf)</a></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td><a href="http://www.cl.cam.ac.uk/research/pls/javasem/lj/lj.thy">(Isabelle)</a></td>
<td><a href="http://www.cl.cam.ac.uk/research/pls/javasem/lj/">(zip)</a></td>
</tr>


<tr>
<td><a href="http://www.cl.cam.ac.uk/research/pls/javasem/ljam/">LJAM: Java Module System</a></td>
<td>163</td>
<td><a href="http://www.cl.cam.ac.uk/research/pls/javasem/ljam/">(sources)</a></td>
<td></td>
<td><a href="http://www.cl.cam.ac.uk/research/pls/javasem/ljam/ljam.pdf">(pdf)</a></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td><a href="http://www.cl.cam.ac.uk/research/pls/javasem/ljam/ljam.thy">(Isabelle)</a></td>
<td><a href="http://www.cl.cam.ac.uk/research/pls/javasem/ljam/ljam_proof.zip">(zip)</a></td>
</tr>


<tr>
<td><a href="http://www.cl.cam.ac.uk/~so294/ocaml">OCaml light</a>                                                                       </td>
<td>310</td>
<td><a href="http://www.cl.cam.ac.uk/users/pes20/ott/examples/caml/src/">(sources)</a>                </td>
<td></td>
<td><a href="http://www.cl.cam.ac.uk/users/pes20/ott/examples/caml/caml_typedef.ps">(ps)</a>                             </td>
<td><a href="http://www.cl.cam.ac.uk/users/pes20/ott/examples/caml/dot.ps">(ps)</a>                       </td>
<td><a type="text/plain" href="http://www.cl.cam.ac.uk/users/pes20/ott/examples/caml/caml_typedef.v">(Coq)</a> </td>
<td></td>
<td><a  type="text/plain" href="http://www.cl.cam.ac.uk/users/pes20/ott/examples/caml/caml_typedefScript.sml">(HOL)</a>           </td>
<td><a href="http://www.cl.cam.ac.uk/users/pes20/ott/examples/caml/hol">(scripts)</a>                </td>
<td><a  type="text/plain" href="http://www.cl.cam.ac.uk/users/pes20/ott/examples/caml/caml_typedef.thy">(Isabelle)</a>        </td>
<td></td>
</tr>

</table>

<p>
<br></br>
(*) These systems would need explicit alpha conversion in the rules to capture the intended semantics using the fully concrete representation.
</p>



## Copyright information

The ocamlgraph library is distributed under the LGPL (from
http://www.lri.fr/~filliatr/ftp/ocamlgraph/); we include a snapshot
for convenience. For its authorship and copyright information see the
files therein.

All other files are distributed under the BSD-style licence in LICENCE.
