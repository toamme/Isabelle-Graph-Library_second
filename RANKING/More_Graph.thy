(*
  Author: Christoph Madlener
*)

subsection \<open>More on Graphs\label{sec:more-graph}\<close>
theory More_Graph
  imports
    Basic_Matching.Berge
    "HOL-Library.FuncSet"
    "HOL-Library.LaTeXsugar"
begin
text \<open>
  Graphs are modelled as sets of undirected edges, where each edge is a doubleton set in a
  wellformed (finite) graph (\<^term>\<open>graph_invar\<close>), i.e.\ graphs have type \<^typ>\<open>'a set set\<close>.
  The main reason for choosing this representation is the existing formalization of Berge's
  Lemma by Abdulaziz~\cite{abdulaziz2019}.

  Newly introduced definitions are required to specify wellformed inputs for RANKING, and
  properties of the output using those wellformed inputs.
\<close>

subsubsection \<open>More on Matchings\<close>

text \<open>
  Maximal, maximum cardinality, and perfect matchings all play a role in the analysis of the
  algorithm. It is relatively straightforward to prove that RANKING produces a maximal
  matching\<^footnote>\<open>This immediately would lead to a competitive ratio of at least $\frac{1}{2}$.\<close>.
  Maximum cardinality matchings go directly into the competitive ratio, as they are the best
  result an offline algorithm can produce on some input. Perfect matchings are of interest, since
  we can in fact reduce the analysis of the competitive ratio to inputs where a perfect matching
  exists~\cite{birnbaum2008}.
\<close>

subsubsection \<open>Removing Vertices from Graphs\<close>

end
