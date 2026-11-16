theory Edmonds_Blossom_Code_Export
  imports
    Blossom_Executable.Cubic_Blossom_Pipeline
    Blossom_Executable.Edmonds_Blossom_Imperative_Instantiation
    Imperative.Code_Target_Machine_Int
begin

provenance ai_human

section "Code export of the blossom algorithms"

text "Three variants of the blossom algorithm for maximum cardinality matching, with vertices as
  machine integers (see Imperative/Code_Target_Machine_Int.thy):

  - RBT: the functional blossom algorithm on red-black trees of Edmonds_Blossom_Example.
    from_list_rbt builds the adjacency map from a list of directed edges, so an undirected edge is
    given in both directions. find_max_matching_run_impl takes the graph and the list of its
    vertices and returns the final state; current_matching selects the matching from it, a
    red-black tree that maps every matched vertex to its partner, and Tree2.inorder lists its
    pairs.
  - Imperative: the pipeline of Edmonds_Blossom_Imperative_Instantiation. obi_max_matching takes
    the number n of vertices and the arrays of the tails and of the heads of the edges and returns
    the mate array: a vertex v is matched to M[v] if M[v] < n + 1.
  - Cubic: the pipeline of Cubic_Blossom_Pipeline (quadratic path search). quadratic_max_matching takes the same
    input and returns the mate array: a vertex v is matched to M[v] if M[v] < n + n div 2.

  The SML and the Scala code are compiled here. There is no Go compiler in Isabelle's environment,
  so the Go code is only generated."

export_code from_list_rbt find_max_matching_run_impl current_matching Tree2.inorder
  checking SML Scala

export_code obi_max_matching quadratic_max_matching checking SML_imp Scala_imp

text "The code for each target is written to Edmonds_Blossom_code_exports/
  Edmonds_Blossom_<variant>_<target> next to this theory."

ML \<open>
  val rbt_consts =
    [\<^const_name>\<open>from_list_rbt\<close>, \<^const_name>\<open>find_max_matching_run_impl\<close>,
     \<^const_name>\<open>current_matching\<close>, \<^const_name>\<open>Tree2.inorder\<close>];
  val imperative_consts = [\<^const_name>\<open>obi_max_matching\<close>];
  val quadratic_consts = [\<^const_name>\<open>quadratic_max_matching\<close>];

  write_machine_code \<^context> rbt_consts "Edmonds_Blossom_RBT" "SML" "Edmonds_Blossom_RBT_SML"
    "Edmonds_Blossom_RBT.sml";
  write_machine_code \<^context> rbt_consts "Edmonds_Blossom_RBT" "Scala" "Edmonds_Blossom_RBT_Scala"
    "Edmonds_Blossom_RBT.scala";
  write_machine_code \<^context> rbt_consts "Edmonds_Blossom_RBT" "Go" "Edmonds_Blossom_RBT_Go" "";
  write_machine_code \<^context> imperative_consts "Edmonds_Blossom_Imperative" "SML_imp"
    "Edmonds_Blossom_Imperative_SML" "Edmonds_Blossom_Imperative.sml";
  write_machine_code \<^context> imperative_consts "Edmonds_Blossom_Imperative" "Scala_imp"
    "Edmonds_Blossom_Imperative_Scala" "Edmonds_Blossom_Imperative.scala";
  write_machine_code \<^context> imperative_consts "Edmonds_Blossom_Imperative" "Go"
    "Edmonds_Blossom_Imperative_Go" "";
  write_machine_code \<^context> quadratic_consts "Edmonds_Blossom_Quadratic" "SML_imp"
    "Edmonds_Blossom_Quadratic_SML" "Edmonds_Blossom_Quadratic.sml";
  write_machine_code \<^context> quadratic_consts "Edmonds_Blossom_Quadratic" "Scala_imp"
    "Edmonds_Blossom_Quadratic_Scala" "Edmonds_Blossom_Quadratic.scala";
  write_machine_code \<^context> quadratic_consts "Edmonds_Blossom_Quadratic" "Go"
    "Edmonds_Blossom_Quadratic_Go" ""
\<close>

end
