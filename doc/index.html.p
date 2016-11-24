<!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Strict//EN"
  "http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd">



<html xmlns="http://www.w3.org/1999/xhtml" xml:lang="en" lang="en">

<head>
  <title>Ott</title>
  <link rel="stylesheet" href="style.css" type="text/css"/> 
  <meta http-equiv="content-type" content="text/html; charset=iso-8859-1"/>
  <meta name="description" content="Ott tool"/>
  <meta name="keywords" content="ott"/>
  <meta http-equiv="Cache-Control" content="no-cache"/>
  <link rel="shortcut icon" href="http://www.cl.cam.ac.uk/users/pes20/ott/favicon.ico" type="image/x-icon" />
     <link rel="icon" href="http://www.cl.cam.ac.uk/users/pes20/ott/favicon.ico" type="image/x-icon" />
  </head>

<body>
<p>
     <a href="test7.dot.ps">
     <img src="test7.dot.png"  alt="[POPLmark Fsub dependency diagram]"></img></a></p>

<h1>Ott</h1>
<h2>
     <a href="http://moscova.inria.fr/~zappa">Francesco Zappa Nardelli</a>,
     <a href="http://www.cl.cam.ac.uk/~pes20">Peter Sewell</a>, and
  <a href="http://www.cl.cam.ac.uk/~so294">Scott Owens</a>
     </h2>
<h4>(with 
  <a href="http://www.cl.cam.ac.uk/~mjp41">Matthew Parkinson</a>,
  <a href="http://www.cl.cam.ac.uk/~gp308">Gilles Peskine</a>,
  <a href="http://www.cl.cam.ac.uk/~tjr22">Tom Ridge</a>,
  <a href="http://www.cl.cam.ac.uk/~ss726">Susmit Sarkar</a>, and
  <a href="http://www.cl.cam.ac.uk/~rs456">Rok Strni&#353;a</a>)
</h4>
<p>
Ott is a tool for writing definitions of programming languages and
calculi.  It takes as input a definition of a language syntax and
semantics, in a concise and readable ASCII notation that is close to
what one would write in informal mathematics.  It generates LaTeX to
build a typeset version of the definition, and Coq, HOL, and Isabelle
versions of the definition.  Additionally, it can be run as a filter,
taking a LaTeX/Coq/Isabelle/HOL source file with embedded (symbolic)
terms of the defined language, parsing them and replacing them by
target-system terms.
For a simple example, here is an 
<a type="text/plain" href="test10.html">Ott source file</a> for an untyped call-by-value
lambda calculus (<code>test10.ott</code>), and
the generated
<a href="test10.pdf">LaTeX  (compiled to pdf)</a>
and <a href="test10.ps">(compiled to ps)</a>,
<a type="text/plain" href="test10.v">Coq</a>,
<a type="text/plain" href="test10.thy">Isabelle</a>, and
<a type="text/plain" href="test10Script.sml">HOL</a>
definitions.
</p><p>
Most simply, the tool can be used to aid completely informal LaTeX mathematics.
Here it permits the definition, and terms within proofs and
exposition, to be written in a clear, editable, ASCII  notation, without LaTeX
noise. It generates good-quality typeset output. 
By parsing (and so sort-checking) this input, it quickly catches a
range of simple errors, e.g. inconsistent use of judgement forms or
metavariable naming conventions. 
</p><p>
That same input can be used to generate formal definitions, for Coq,
HOL, Isabelle, and (experimentally) Lem.  It should thereby enable a smooth transition
between use of informal and formal mathematics.  Additionally, the
tool can automatically generate definitions of functions for free
variables, single and multiple substitutions, subgrammar checks
(e.g. for value subgrammars), and binding auxiliary functions.
At present only a fully concrete representation of binding, without
quotienting by alpha equivalence, is fully supported.  An experimental
backend generates a locally-nameless representation of terms for a
subset of the Ott metalanguage: details can be
found <a href="http://moscova.inria.fr/~zappa/projects/ln_ott">here</a>.
</p><p>
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
  Strni&#353;a</a>, and semantics for 
<a href="http://www.cl.cam.ac.uk/~so294/ocaml">OCaml light</a>, by
  <a href="http://www.cl.cam.ac.uk/~so294">Scott Owens</a>.
</p><p>
A release of the Ott source is available, and comment and 
feedback would be much appreciated.
</p>
<!--<p>
It's not required, but we'd also like to collect bibtex data (and web
links) for any papers written using Ott, and pointers to any courses
that used it.  Please send these to Peter Sewell or Francesco Zappa Nardelli
(include a note if you'd rather they weren't public).
</p>-->


   
<h2>Papers and Documentation</h2>
<ul>
  <li>
      <a href="ott_manual_OTTVERSION.html">User Guide (html)</a>, 
      <a href="ott_manual_OTTVERSION.pdf">(pdf)</a>, and
      <a href="ott_manual_OTTVERSION.ps">(ps)</a></li>
</ul>

<ul>
<li> <a href="wmm2010.pdf">Ott or Nott</a>. Stephanie Weirich, Scott Owens, Peter
  Sewell, Francesco Zappa Nardelli. 
<a href="http://www.cis.upenn.edu/~bcpierce/wmm/">WMM 2010: 5th ACM SIGPLAN Workshop on Mechanizing Metatheory</a>

   <li> <!--<img src="../images/new.gif" alt="NEW:"/> -->
<a href="ott-jfp.pdf">Ott: Effective Tool Support for the Working Semanticist (pdf)</a>. 
Peter Sewell,
Francesco Zappa Nardelli,
Scott Owens,
Gilles Peskine,
Thomas Ridge,
Susmit Sarkar,
Rok Strni&#353;a.  <a href="
                            http://journals.cambridge.org/repo_A71Keeig">Journal
  of Functional Programming 20(1):71-122, 2010</a>
</li>
   <li> <a href="paper.pdf">Ott: Effective Tool Support for the Working Semanticist (pdf)</a> and
      <a href="paper.ps">(ps)</a> <a href="ottbib.bib">[bib]</a>.  In <a href="http://www.informatik.uni-bonn.de/%7Eralf/icfp07.html">ICFP 2007</a>. </li>
   <li> <a href="bind-doc.pdf">Binding and Substitution (draft) (pdf)</a> and
        <a href="bind-doc.ps">(ps)</a></li>
   <li> <a href="http://moscova.inria.fr/~zappa/projects/ln_ott">The experimental Coq locally-nameless backend (html)</a></li>
</ul>
      
<h2>Code</h2>

<ul>

<li> Ott is now <a href="https://github.com/ott-lang/ott">available
    from github</a> and (as described there) as
    an <a href="https://opam.ocaml.org/">opam</a> package.

<!--
  <li><a
  href="ott_distro_OTTVERSION.tar.gz"><code>ott_distro_OTTVERSION.tar.gz</code>
  tarball</a> (includes the manual)</li>

      <li> <a href="ott_distro_windows_OTTVERSION.tar.gz"><code>ott_distro_windows_OTTVERSION.tar.gz</code>
  Windows binary distro</a>  (including exe kindly built
  by <a href="http://www.cl.cam.ac.uk/~ib249/">Ioannis
  Baltopoulos</a>).</li>

<li> (we no longer provide a Windows binary distribution or non-github
  tarball releases)</li>
-->

 <li><a href="README.txt">README file from the distribution</a></li>
  <li><a href="revision_history.txt">revision history summary</a></li>
</ul>

<h2>Bug Tracker</h2>
<ul>
<li> Please now use
  the <a href="https://github.com/ott-lang/ott/issues">github issue tracker</a>
(though our resources for fixing issues are very limited)
<li> The previous issue tracker is <a href="https://gforge.inria.fr/tracker/?group_id=2980">here</a>
</ul>


<h2>Mailing Lists</h2>
<ul>
  <li> <a
  href="https://lists.cam.ac.uk/mailman/listinfo/cl-ott-announce"><code>cl-ott-announce</code> announcement mailing list</a></li>
  <li> <a
  href="https://lists.cam.ac.uk/mailman/listinfo/cl-ott-discuss"><code>cl-ott-discuss</code> discussion mailing list</a></li>
</ul>

      
 <h2>Examples</h2>
 
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
<td><a  type="text/plain" href="test10.ott"><code>test10.ott</code></a></td>
<td><a  type="text/plain" href="test10.tex"><code>test10.tex</code></a></td>
<td> <!-- <a href="test10.pdf">(pdf)</a>&nbsp;--> <a href="test10.ps">(ps)</a></td> 
<td></td>
<td><a  type="text/plain" href="test10.v"><code>test10.v</code></a></td>
<td></td>
<td><a  type="text/plain" href="test10Script.sml"><code>test10Script.sml</code></a></td>
<td></td>
<td><a  type="text/plain" href="test10.thy"><code>test10.thy</code></a></td>
<td></td>
</tr>     

<tr>
<td>Simply typed CBV lambda</td>
<td>6</td>
<td><a  type="text/plain" href="test10st.ott"><code>test10st.ott</code></a></td>
<td><a  type="text/plain" href="test10st.tex"><code>test10st.tex</code></a></td>
<td> <!-- <a href="test10st.pdf">(pdf)</a>&nbsp;--> <a href="test10st.ps">(ps)</a></td> 
<td></td>
<td><a  type="text/plain" href="test10st.v"><code>test10st.v</code></a></td>
<td><a  type="text/plain" href="test10st_metatheory.v"><code>test10st_metatheory.v</code></a></td>
<td><a  type="text/plain" href="test10stScript.sml"><code>test10stScript.sml</code></a></td>
<td><a  type="text/plain" href="test10st_metatheoryScript.sml"><code>test10st_metatheoryScript.sml</code></a></td>
<td><a  type="text/plain" href="test10st.thy"><code>test10st.thy</code></a></td>
<td><a  type="text/plain" href="test10st_metatheory.thy"><code>test10st_metatheory.thy</code></a></td>
</tr>     

<tr>
<td>ML polymorphism</td>
<td>22</td>
<td><a  type="text/plain" href="test8.ott"><code>test8.ott</code></a></td>
<td><a  type="text/plain" href="test8.tex"><code>test8.tex</code></a></td>
<td><!-- <a href="test8.pdf">(pdf)</a>&nbsp; --> <a href="test8.ps">(ps)</a></td> 
<td></td>
<td><a  type="text/plain" href="test8.v"><code>test8.v</code></a></td>
<td></td>
<td><a  type="text/plain" href="test8Script.sml"><code>test8Script.sml</code></a></td>
<td></td>
<td><a  type="text/plain" href="test8.thy"><code>test8.thy</code></a></td>
<td></td>
</tr>     

<tr>
<td>TAPL roughly-full-simple</td>
<td>63</td>
<td><a href="examples/tapl">(sources)</a></td>
<td></td>
<td><a href="examples/tapl/stlc.ps">(ps)</a></td>
<td></td>
<td><a href="examples/tapl/records_auto.v">(Coq (including records))</a></td>
<td></td>
<td><a href="examples/tapl/stlcScript.sml">(HOL)</a></td>
<td><a href="examples/tapl/metatheoryScript.sml">(script)</a></td>
<td><a href="examples/tapl/stlc.thy">(Isabelle)</a></td>
<td><a href="examples/tapl/stlc_metatheory.thy">(script)</a></td>
</tr>

<tr>
<td>POPLmark Fsub (*)</td>
<td>48</td>
<td><a href="tmp_test7.ott">(sources)</a></td>
<td><a href="test7.tex">(latex)</a></td>
<td><a href="test7.pdf">(pdf)</a> &nbsp; <a href="test7.ps">(ps)</a></td>
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
<td><a href="leroy-jfp96.ott"><code>leroy-jfp96.ott</code></a></td>
<td><a href="leroy-jfp96.tex">(latex)</a></td>
<td><!-- <a href="leroy-jfp96.pdf">(pdf)</a> &nbsp; --> <a href="leroy-jfp96.ps">(ps)</a></td>
<td></td>
<td></td>
<td></td>
<td><a  type="text/plain" href="leroy-jfp96Script.sml">(HOL)</a></td>
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
<td><a href="examples/caml/src/">(sources)</a>                </td>
<td></td>
<td><a href="examples/caml/caml_typedef.ps">(ps)</a>                             </td>
<td><a href="examples/caml/dot.ps">(ps)</a>                       </td>
<td><a type="text/plain" href="examples/caml/caml_typedef.v">(Coq)</a> </td>
<td></td>
<td><a  type="text/plain" href="examples/caml/caml_typedefScript.sml">(HOL)</a>           </td>
<td><a href="examples/caml/hol">(scripts)</a>                </td>
<td><a  type="text/plain" href="examples/caml/caml_typedef.thy">(Isabelle)</a>        </td>
<td></td>
</tr>

</table>

<p>
(all files except the proof scripts are generated from the Ott sources)
<br></br>
(*) These systems would need explicit alpha conversion in the rules to capture the intended semantics using the fully concrete representation.
</p>


<!--
<h2>Other Ott Developments</h2>
<ul>
<li> <a href="http://www.cl.cam.ac.uk/~mjp41/RGSep">A marriage of
    Rely/Guarantee and Separation Logic</a>. Vafeiadis and Parkinson,
    CONCUR 2007.
</ul>
-->
<hr/>

<p><a href="http://validator.w3.org/check?uri=referer">[validate]</a></p>
                      
</body>

</html>
