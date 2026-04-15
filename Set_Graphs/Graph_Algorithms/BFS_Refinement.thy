theory BFS_Refinement
  imports BFS_2 BFS_Subprocedures  Directed_Set_Graphs.Pair_Graph_Imperative
begin

record ('imp_dag, 'imp_vis, 'imp_cf) BFS_state_imp =
     parents:: "'imp_dag" current:: "'imp_cf" visited:: "'imp_vis"


locale BFS_Imperative = BFS
  where expand_tree = expand_tree and insert = insert
  for expand_tree::"'adjmap \<Rightarrow> 'vset \<Rightarrow> 'vset \<Rightarrow> 'adjmap"
  and insert :: "'ver \<Rightarrow> 'vset \<Rightarrow> 'vset" +
fixes imp_dag_empty::"'imp_dag Heap"
and imp_dag_assn::"'adjmap \<Rightarrow> 'imp_dag \<Rightarrow> assn"
and G_imp::"'imp_G"
and graph_assn::"'adjmap \<Rightarrow> 'imp_G \<Rightarrow> assn"
and imp_vis_empty::"'imp_vis Heap"
and imp_vis_assn::"'vset \<Rightarrow> 'imp_vis \<Rightarrow> assn"
(*and src_imp::"'imp_src Heap"*)
and imp_src_assn::"'vset \<Rightarrow> 'imp_src \<Rightarrow> assn"
and imp_src_to_cf::"'imp_src \<Rightarrow> 'imp_cf Heap"
and imp_cf_assn::"'vset \<Rightarrow> 'imp_cf \<Rightarrow> assn"
and set_cf_visited::"'imp_vis \<Rightarrow> 'imp_cf \<Rightarrow> 'imp_vis Heap"
and imp_expand_tree::"'imp_dag \<Rightarrow> 'imp_cf \<Rightarrow> 'imp_vis \<Rightarrow> 'imp_dag Heap"
and imp_next_frontier::"'imp_cf \<Rightarrow> 'imp_vis \<Rightarrow> 'imp_cf Heap"
and imp_cf_is_empty::"'imp_cf \<Rightarrow> bool Heap"
assumes imp_dag_empty: "<emp> imp_dag_empty <imp_dag_assn \<emptyset>\<^sub>G>"
and imp_vis_empty: "<emp> imp_vis_empty <imp_vis_assn \<emptyset>\<^sub>N>"
and imp_sf_is_empty: "\<And> S Si. <imp_cf_assn S Si> imp_cf_is_empty Si 
                       <\<lambda> b. imp_cf_assn S Si * \<up>(b \<longleftrightarrow> S = \<emptyset>\<^sub>N)>"
and imp_src_to_cf: "\<And> S Si. <imp_src_assn S Si> imp_src_to_cf Si 
                      <\<lambda> r. imp_src_assn S Si * imp_cf_assn S r>"
and set_cf_visited: 
  "\<And> vis imp_vis cf imp_cf. 
    <imp_vis_assn vis imp_vis * imp_cf_assn cf imp_cf * graph_assn G G_imp>
    set_cf_visited imp_vis imp_cf
    <\<lambda> r. imp_vis_assn (vis \<union>\<^sub>G cf) r * imp_cf_assn cf imp_cf * graph_assn G G_imp>"
and imp_expand_tree:
  "\<And> dag imp_dag cf imp_cf vis imp_vis.
    <imp_dag_assn dag imp_dag * imp_cf_assn cf imp_cf * imp_vis_assn vis imp_vis>
    imp_expand_tree imp_dag imp_cf imp_vis
    <\<lambda> r. imp_dag_assn (expand_tree dag cf vis) r* imp_cf_assn cf imp_cf 
              * imp_vis_assn vis imp_vis * graph_assn G G_imp>"
and imp_next_frontier:  "\<And> cf imp_cf vis imp_vis.
    <imp_cf_assn cf imp_cf * imp_vis_assn vis imp_vis>
    imp_next_frontier imp_cf imp_vis
    <\<lambda> r. imp_cf_assn (next_frontier cf vis) r * imp_vis_assn vis imp_vis * graph_assn G G_imp>"
begin

partial_function (heap) BFS_imp::
  "('imp_dag, 'imp_vis, 'imp_cf) BFS_state_imp \<Rightarrow> ('imp_dag, 'imp_vis, 'imp_cf) BFS_state_imp Heap"
  where 
 "BFS_imp state = 
   do { b \<leftarrow> imp_cf_is_empty (current state);
       if b then Heap_Monad.return state
       else do{ visited' \<leftarrow> set_cf_visited (visited state) (current state);
                parents' \<leftarrow> imp_expand_tree (parents state) (current state) visited';
                current' \<leftarrow> imp_next_frontier (current state) visited';
                BFS_imp (state \<lparr>parents := parents', visited := visited', current := current' \<rparr> )}}"

definition "state_assn (s::('adjmap, 'vset) BFS_state)
    (imp_s::('imp_dag, 'imp_vis, 'imp_cf) BFS_state_imp) = 
  (imp_dag_assn (BFS_state.parents s) (parents imp_s) *
   imp_vis_assn (BFS_state.visited s) (visited imp_s) *
   imp_cf_assn (BFS_state.current s) (current imp_s))"

lemma BFS_refine:
  "<graph_assn G G_imp * state_assn s s_imp >
  BFS_imp s_imp 
  <\<lambda> s_imp'. graph_assn G G_imp * state_assn (BFS_impl s) s_imp'>"
proof(induction arbitrary: s s_imp rule: BFS_imp.fixp_induct, goal_cases)
  case 1
  then show ?case 
    by auto
next
  case (2 s s_imp)
  then show ?case 
    by simp
next
  case (3 f s s_imp)

  note IH = 3(1)[of 
     "\<lparr>BFS_state.parents = parents, current = current, visited = visited\<rparr>"
     "\<lparr>BFS_state_imp.parents = imp_parents, current = imp_current, visited = imp_visited\<rparr>"
     for imp_parents imp_current imp_visited parents current visited] 

  note IH[sep_heap_rules] = IH[unfolded state_assn_def, simplified, rule_format]

  show ?case
    apply(cases s, cases s_imp)
    subgoal for parents current visited imp_parents imp_current imp_visited
      apply (rewrite in "<_> _ <\<hole>>" BFS_impl.simps)
(*OR:
 using  imp_next_frontier IH imp_expand_tree set_cf_visited imp_sf_is_empty
              apply(auto split!: if_split simp add: state_assn_def Let_def)
              by sep_auto
*)
(*here in detail: which rules need to be applied*)
      apply (clarsimp split!: if_split simp add: Let_def)
      subgoal
        apply(rule ht_bind[where R = "\<lambda> b. graph_assn G G_imp* state_assn s s_imp * \<up>(b \<longleftrightarrow> BFS_state.current s = \<emptyset>\<^sub>N)"])
        subgoal
          unfolding state_assn_def
          using imp_sf_is_empty by sep_auto 
        subgoal for b
          by sep_auto
        done
      subgoal
        apply(rule ht_bind[where R = "\<lambda> b. graph_assn G G_imp * state_assn s s_imp * \<up>(b \<longleftrightarrow> BFS_state.current s = \<emptyset>\<^sub>N)"])
        subgoal
          unfolding state_assn_def
          using imp_sf_is_empty by sep_auto 
        apply clarsimp
        apply(rule ht_bind[where R = "\<lambda> r. imp_vis_assn (visited \<union>\<^sub>G current) r * graph_assn G G_imp * 
       imp_cf_assn current imp_current * imp_dag_assn parents imp_parents"])
          subgoal
            using set_cf_visited[of visited imp_visited current imp_current]
            apply(auto simp add: state_assn_def)
            by sep_auto
          subgoal for b visited'
            apply(rule ht_bind[where R = "\<lambda> r. imp_dag_assn (expand_tree parents current (visited \<union>\<^sub>G current)) r*
            graph_assn G G_imp * imp_vis_assn (visited \<union>\<^sub>G current) visited' * imp_cf_assn current imp_current"])
            subgoal
              using imp_expand_tree[of parents imp_parents current imp_current "visited \<union>\<^sub>G current" visited']
              by sep_auto
            subgoal for parents'
            apply(rule ht_bind[where R = "\<lambda> r. imp_cf_assn (next_frontier current (visited \<union>\<^sub>G current)) r *
           graph_assn G G_imp * imp_dag_assn (expand_tree parents current (visited \<union>\<^sub>G current)) parents'*
            imp_vis_assn (visited \<union>\<^sub>G current) visited' "])
              subgoal
                using imp_next_frontier[of current imp_current "visited \<union>\<^sub>G current" visited']
                by sep_auto
              subgoal for current'
              unfolding state_assn_def
              using IH by sep_auto
            done
          done
        done
      done
    done     
qed


definition "initial_state_imp src_imp=  
  do {cf \<leftarrow> imp_src_to_cf src_imp;
      p \<leftarrow> imp_dag_empty;
      v \<leftarrow> imp_vis_empty;
        return \<lparr>parents = p, current = cf, visited = v\<rparr>}"

lemma initial_refine:
 "<imp_src_assn srcs srcs_imp>
  initial_state_imp srcs_imp
 <\<lambda> si. state_assn initial_state si * imp_src_assn srcs srcs_imp>"
  apply(auto simp add: initial_state_def state_assn_def initial_state_imp_def)
(*OR:
  using imp_src_to_cf imp_dag_empty imp_vis_empty by sep_auto
*)
(*details:*)
  apply(rule ht_bind)
   apply(rule imp_src_to_cf)
  apply(rule ht_bind)
   apply(rule ht_frame[OF imp_dag_empty, simplified norm_assertion_simps(1)])
  apply(rule ht_bind)
   apply(rule ht_frame[OF imp_vis_empty, simplified norm_assertion_simps(1)])
  apply(rule ht_cons_prec[OF ent_refl _ ht_return_sp])
  by sep_auto

lemma BFS_program_behaviour:
  "<imp_src_assn srcs srcs_imp * graph_assn G G_imp>
   do { si \<leftarrow> initial_state_imp srcs_imp;
        BFS_imp si }
   < \<lambda> si'. state_assn (BFS_impl initial_state) si' * imp_src_assn srcs srcs_imp * graph_assn G G_imp>"
  using initial_refine BFS_refine 
  by sep_auto

 
end

end