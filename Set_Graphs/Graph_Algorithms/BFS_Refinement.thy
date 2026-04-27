theory BFS_Refinement
  imports BFS_2 BFS_Subprocedures  Directed_Set_Graphs.Pair_Graph_Imperative
"HOL-Imperative_HOL.Imperative_HOL" "HOL-Library.IArray"
begin

record ('imp_dag, 'imp_vis, 'imp_cf) BFS_state_imp =
     parents:: "'imp_dag" current:: "'imp_cf" visited:: "'imp_vis"

locale BFS_Imperative_spec = 
fixes imp_dag_empty::"'imp_dag Heap"
and imp_vis_empty::"'imp_vis Heap"
and imp_src_to_cf::"'imp_src \<Rightarrow> 'imp_cf Heap"
and set_cf_visited::"'imp_vis \<Rightarrow> 'imp_cf \<Rightarrow> 'imp_vis Heap"
and imp_expand_tree::"'imp_dag \<Rightarrow> 'imp_cf \<Rightarrow> 'imp_vis \<Rightarrow> 'imp_dag Heap"
and imp_next_frontier::"'imp_cf \<Rightarrow> 'imp_vis \<Rightarrow> 'imp_cf Heap"
and imp_cf_is_empty::"'imp_cf \<Rightarrow> bool Heap"
and change_dag_format::"'imp_dag \<Rightarrow> 'imp_G Heap"
and in_vis::"'ver \<Rightarrow> 'imp_vis \<Rightarrow> bool Heap"
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

definition "initial_state_imp src_imp=  
  do {cf \<leftarrow> imp_src_to_cf src_imp;
      p \<leftarrow> imp_dag_empty;
      v \<leftarrow> imp_vis_empty;
        return \<lparr>parents = p, current = cf, visited = v\<rparr>}"

definition "compute_dag src_imp =
    do {init \<leftarrow> initial_state_imp src_imp;
        final \<leftarrow> BFS_imp init;
        change_dag_format (parents final)}"

definition "check_reachable src_imp t =
    do {init \<leftarrow> initial_state_imp src_imp;
        final \<leftarrow> BFS_imp init;
        in_vis t (visited final)}"
end

locale BFS_Imperative = 
 BFS  where expand_tree = expand_tree and insert = insert +
 BFS_Imperative_spec where  imp_src_to_cf = imp_src_to_cf and imp_expand_tree = imp_expand_tree
  and change_dag_format = change_dag_format
  and in_vis = in_vis
 for  imp_src_to_cf :: "'imp_src \<Rightarrow> 'imp_cf Heap"
  and expand_tree::"'adjmap \<Rightarrow> 'vset \<Rightarrow> 'vset \<Rightarrow> 'adjmap"
  and insert :: "'ver \<Rightarrow> 'vset \<Rightarrow> 'vset" 
  and imp_expand_tree::"'imp_dag \<Rightarrow> 'imp_cf \<Rightarrow> 'imp_vis \<Rightarrow> 'imp_dag Heap"
  and change_dag_format::"'imp_dag \<Rightarrow> 'imp_G Heap"
  and in_vis::"'ver \<Rightarrow> 'imp_vis \<Rightarrow> bool Heap"+
fixes  G_imp::"'imp_G"
 and graph_assn::"'adjmap \<Rightarrow> 'imp_G \<Rightarrow> assn"
 and imp_src_assn::"'vset \<Rightarrow> 'imp_src \<Rightarrow> assn"
 and imp_dag_assn::"'adjmap \<Rightarrow> 'imp_dag \<Rightarrow> assn"
 and imp_cf_assn::"'vset \<Rightarrow> 'imp_cf \<Rightarrow> assn"
 and imp_vis_assn::"'vset \<Rightarrow> 'imp_vis \<Rightarrow> assn"
assumes imp_dag_empty: "<emp> imp_dag_empty <imp_dag_assn \<emptyset>\<^sub>G>"
 and imp_vis_empty: "<emp> imp_vis_empty <imp_vis_assn \<emptyset>\<^sub>N>"
 and imp_sf_is_empty: "\<And> S Si. <imp_cf_assn S Si> imp_cf_is_empty Si 
                       <\<lambda> b. imp_cf_assn S Si * \<up>(b \<longleftrightarrow> S = \<emptyset>\<^sub>N)>"
 and imp_src_to_cf: "\<And> S Si. <imp_src_assn S Si> imp_src_to_cf Si 
                      <\<lambda> r. imp_src_assn S Si * imp_cf_assn S r>"
 and set_cf_visited: 
  "\<And> vis imp_vis cf imp_cf. 
    <imp_vis_assn vis imp_vis * imp_cf_assn cf imp_cf>
    set_cf_visited imp_vis imp_cf
    <\<lambda> r. imp_vis_assn (vis \<union>\<^sub>G cf) r * imp_cf_assn cf imp_cf>"
 and imp_expand_tree:
  "\<And> dag imp_dag cf imp_cf vis imp_vis.
    <imp_dag_assn dag imp_dag * imp_cf_assn cf imp_cf * imp_vis_assn vis imp_vis * graph_assn G G_imp>
    imp_expand_tree imp_dag imp_cf imp_vis
    <\<lambda> r. imp_dag_assn (expand_tree dag cf vis) r* imp_cf_assn cf imp_cf 
              * imp_vis_assn vis imp_vis * graph_assn G G_imp>"
 and imp_next_frontier:  "\<And> cf imp_cf vis imp_vis.
    <imp_cf_assn cf imp_cf * imp_vis_assn vis imp_vis * graph_assn G G_imp>
    imp_next_frontier imp_cf imp_vis
    <\<lambda> r. imp_cf_assn (next_frontier cf vis) r * imp_vis_assn vis imp_vis * graph_assn G G_imp
          * imp_cf_assn cf imp_cf>"
and change_dag_format_rule: 
 "\<And> dag dagi. < imp_dag_assn dag dagi>
      change_dag_format dagi
     <\<lambda> r. imp_dag_assn dag dagi * graph_assn dag r>"
and in_vis_rule: "\<And>vis visi s. <imp_vis_assn vis visi> in_vis s visi 
            <\<lambda> r. imp_vis_assn vis visi * \<up> (r \<longleftrightarrow> isin vis s)>"
begin

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

lemma compute_dag_rule:
 "<imp_src_assn srcs srcs_imp * graph_assn G G_imp> 
   compute_dag srcs_imp
  <\<lambda> dag. imp_src_assn srcs srcs_imp * graph_assn G G_imp *
      graph_assn (BFS_state.parents (BFS_impl initial_state)) dag>" 
  unfolding compute_dag_def
  using initial_refine BFS_refine change_dag_format_rule
  by (sep_auto simp: state_assn_def)

lemma check_reachable_rule:
 "<imp_src_assn srcs srcs_imp * graph_assn G G_imp> 
   check_reachable srcs_imp t
  <\<lambda> b. imp_src_assn srcs srcs_imp * graph_assn G G_imp *
      \<up> (b \<longleftrightarrow> isin (BFS_state.visited (BFS_impl initial_state)) t)>" 
  unfolding check_reachable_def
  using initial_refine BFS_refine change_dag_format_rule in_vis_rule
  by (sep_auto simp: state_assn_def)
end

locale imp_2d_array =
   outer_lookup: imp_map_lookup where lookup = lookup1 and is_map = is_map1+
   inner_lookup: imp_map_lookup where lookup = lookup2 and is_map = is_map2+
   outer_empty: imp_map_empty where empty = empty1 and is_map = is_map1 +
   inner_empty: imp_map_empty where empty = empty2 and is_map = is_map2+
   outer_upd: imp_map_update where is_map = is_map1 and update = update1+
   inner_upd: imp_map_update where is_map = is_map2 and update = update2
 for lookup1 :: "nat \<Rightarrow> 'outer \<Rightarrow> 'inner option Heap"
   and lookup2 :: "nat \<Rightarrow> 'inner \<Rightarrow> 'val option Heap"
   and is_map1 and is_map2 and empty1::"'outer Heap" and empty2::"'inner Heap"
   and update1 and update2
begin

definition lookup_2d :: "'outer \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'val option Heap" where
  "lookup_2d M i j = do {
    opt_row \<leftarrow> lookup1 i M;
    (case opt_row of
      None \<Rightarrow> return None
    | Some row_map \<Rightarrow> do {
        val \<leftarrow> lookup2 j row_map;
        return val
      })
  }"

definition update_2d :: "nat \<Rightarrow> nat \<Rightarrow> 'val \<Rightarrow> 'outer \<Rightarrow> 'outer Heap" where
  "update_2d i j v M = do {
    opt_row \<leftarrow> lookup1 i M;
    row_map \<leftarrow> (case opt_row of
                 None \<Rightarrow> empty2   
               | Some rm \<Rightarrow> return rm); 
    row_map' \<leftarrow> update2 j v row_map;
    M' \<leftarrow> update1 i row_map' M; 
    return M'
  }"

definition 
"prog v = do {
  empt \<leftarrow> empty1;
  arr2 \<leftarrow> update_2d 0 0 v  empt;
  val \<leftarrow> lookup_2d arr2 0 0;
  return val
}"

lemma "<emp> prog v <\<lambda> r. \<up> (r = Some v)>"
  unfolding prog_def update_2d_def lookup_2d_def
  apply auto
  by sep_auto

lemma "<emp> prog v <\<lambda> r. \<up> (r = Some v) *  true>"
  unfolding prog_def update_2d_def lookup_2d_def
  apply auto
  by sep_auto

end

setup Locale_Code.open_block 
interpretation matr: imp_2d_array iam_lookup iam_lookup
   is_iam is_iam iam_new iam_new iam_update iam_update
by unfold_locales
setup Locale_Code.close_block 
print_theorems

definition "iam_2dim_update = 
(matr.update_2d::(nat \<Rightarrow> nat \<Rightarrow> nat 
\<Rightarrow> nat option array option array \<Rightarrow> nat option array option array Heap))"
definition "iam_2dim_lookup =
( matr.lookup_2d::(nat option array option array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat option Heap))"
definition "iam_2dim_empty = (iam_new::nat option array option array Heap)"
definition "prog = (matr.prog::(nat \<Rightarrow> nat option Heap))"

export_code iam_2dim_update iam_2dim_lookup iam_2dim_empty nat_of_integer prog checking SML_imp

ML \<open>val prog = @{code prog}
    val noi = @{code nat_of_integer} 
    val final = prog (noi 1) ()\<close>

ML \<open>
   val iam_2dim_empty = @{code iam_2dim_empty} ()
   val iam_2dim_lookup = @{code iam_2dim_lookup}
   val iam_2dim_update = @{code iam_2dim_update}
   val noi = @{code nat_of_integer}
   val _ = iam_2dim_update (noi 1) (noi 1) (noi 10) iam_2dim_empty ()
   val _ = iam_2dim_update (noi 2) (noi 1) (noi 33) iam_2dim_empty ()
   val array_at_1_1 = iam_2dim_lookup iam_2dim_empty (noi 1) (noi 1) ()
   val array_at_2_1 = iam_2dim_lookup iam_2dim_empty (noi 2) (noi 1) ()
   \<close>

lemma "i \<in> set xs \<Longrightarrow> foldr (\<lambda> i as. assn (f i) (g i) * as) xs emp \<Longrightarrow>\<^sub>A assn (f i) (g i) * true"
  apply(induction xs)
   apply auto
   apply sep_auto
  using ent_true_drop(1) star_aci(2) by fastforce

lemma assn_over_finite_extract_one:
     "\<lbrakk>finite S; i \<in> S\<rbrakk> \<Longrightarrow> Finite_Set.fold (\<lambda> i as. assn (f i) (g i) * as) emp S
           = assn (f i) (g i) * Finite_Set.fold (\<lambda> i as. assn (f i) (g i) * as) emp (S - {i})"
  apply(induction rule: finite_induct)
  subgoal
    by simp
  apply(subst comp_fun_commute_on.fold_insert_remove[where S = UNIV])
  subgoal
    by(auto intro!: comp_fun_commute_on.intro ext simp add: star_aci(3))
  subgoal
    by simp
  subgoal
    by simp
  subgoal for x F
    apply(cases "i = x")
    subgoal
      by auto
    subgoal
      apply(subst insert_minus_eq)
       apply simp
      apply(subst comp_fun_commute_on.fold_insert_remove[where S = UNIV])
      subgoal
        by(auto intro!: comp_fun_commute_on.intro ext simp add: star_aci(3))
      subgoal by simp
      subgoal by simp
      apply auto
      apply sep_auto
      by (smt (verit, del_insts) assn_aci(11) fr_refl star_aci(2))
    done
  done

lemma assn_take_one_from_dom: 
  "\<up> (finite (dom S)) * \<up> (S i = Some x) * Finite_Set.fold (\<lambda> i as. assn (f i) (g i) * as) emp (dom S)
 = \<up> (finite (dom S)) *  \<up> (S i = Some x) *
          assn (f i) (g i) * Finite_Set.fold (\<lambda> i as. assn (f i) (g i) * as) emp (dom S - {i})"
  apply(rule ent_iffI)
  by(sep_auto | subst assn_over_finite_extract_one[of "dom S" i] | force)+
  
lemma assn_over_finite_insert_one:
     "\<lbrakk>finite S; i \<notin> S\<rbrakk> \<Longrightarrow> Finite_Set.fold (\<lambda> i as. assn (f i) (g i) * as) emp (Set.insert i S)
           = assn (f i) (g i) * Finite_Set.fold (\<lambda> i as. assn (f i) (g i) * as) emp S"
  by(simp add: assn_over_finite_extract_one[of "Set.insert i S" i, simplified])

lemma assns_over_set_cong:
  "\<lbrakk>finite S; \<And> i. i \<in> S \<Longrightarrow> assn (f i) (g i) = assn' (f' i) (g' i)\<rbrakk> \<Longrightarrow>
     Finite_Set.fold (\<lambda> i as. assn (f i) (g i) * as) emp S = 
     Finite_Set.fold (\<lambda> i as. assn' (f' i) (g' i) * as) emp S"
  apply(rule Finite_Set.fold_cong[where S = UNIV])
  using star_aci(3) by (auto intro!: comp_fun_commute_on.intro)

lemma pure_assn_over_finite_set:
   "finite S \<Longrightarrow> Finite_Set.fold (\<lambda> i as. \<up> (P i) * as) emp S = \<up> (\<forall> i \<in> S. P i)"
  by(induction rule: finite_induct)
    (simp add: assn_over_finite_insert_one[where assn = "\<lambda> i j. \<up> (P i)" and f = id, simplified])+

context
  imp_2d_array
begin

definition is_2d_map :: "(nat \<Rightarrow> nat \<Rightarrow> 'val option) \<Rightarrow> 'outer \<Rightarrow> assn" where
  "is_2d_map f M = (\<exists>\<^sub>A A . 
      is_map1 A M * \<up> (finite (dom A)) *  \<up> (\<forall> i j. A i = None \<longrightarrow> f i j = None)*
       Finite_Set.fold (\<lambda> i ass. is_map2 (f i) (the (A i)) * ass) emp (dom A))"

definition is_2d_map' :: "(nat \<Rightarrow> nat \<Rightarrow> 'val option) \<Rightarrow> 'outer \<Rightarrow> (nat \<Rightarrow> 'inner option) \<Rightarrow> assn" where
  "is_2d_map' f M A = ( 
      is_map1 A M * \<up> (finite (dom A)) *  \<up> (\<forall> i j. A i = None \<longrightarrow> f i j = None)*
       Finite_Set.fold (\<lambda> i ass. is_map2 (f i) (the (A i)) * ass) emp (dom A))"


lemma forw_subst_assn:
  "x = y \<Longrightarrow> P x \<Longrightarrow>\<^sub>A Q x \<Longrightarrow> P x \<Longrightarrow>\<^sub>A Q y"
  by sep_auto

lemma impl_of_exes_assn:"(\<And> x. P x \<Longrightarrow>\<^sub>A Q x) \<Longrightarrow> \<exists>\<^sub>A x. P x \<Longrightarrow>\<^sub>A \<exists>\<^sub>A x. Q x"
  apply(rule ent_ex_preI)
  apply(rule ent_ex_postI)
  by auto

lemma same_assn: "A = B \<Longrightarrow> A \<Longrightarrow>\<^sub>A B" for A B
  by simp

lemma update_2d_rule:
 "<is_2d_map M Mi>
  update_2d i j v Mi
  <\<lambda> Mi. is_2d_map (\<lambda> x y. if x = i \<and> y= j then Some v else M x y) Mi >"
  unfolding update_2d_def is_2d_map_def
  apply(rule ht_bind[where R =
        "\<lambda> r. \<exists>\<^sub>AA. is_map1 A Mi * \<up> (finite (dom A)) * \<up> (\<forall>i j. A i = None \<longrightarrow> M i j = None) *
           Finite_Set.fold (\<lambda>i. (*) (is_map2 (M i) (the (A i)))) emp (dom A) * \<up> (r = A i)"])
  subgoal
    by sep_auto
  subgoal for or
    apply(clarsimp split!: option.split)
    subgoal
      apply(rule ht_bind[where R =
            "\<lambda> r. \<exists>\<^sub>AA. is_map1 A Mi * \<up> (finite (dom A)) * \<up> (\<forall>i. A i = None \<longrightarrow> (\<forall>j. M i j = None)) *
           Finite_Set.fold (\<lambda>i. (*) (is_map2 (M i) (the (A i)))) emp (dom A) *
           \<up> (A i = None) * is_map2 (\<lambda>x. None) r * \<up> (\<forall>j. M i j = None)"])
      subgoal
        by sep_auto
      subgoal for row_map
        apply(rule ht_bind[where R =
          "\<lambda> r. \<exists>\<^sub>AA. is_map1 A Mi * \<up> (finite (dom A)) * \<up> (\<forall>i. A i = None \<longrightarrow> (\<forall>j. M i j = None)) *
           Finite_Set.fold (\<lambda>i. (*) (is_map2 (M i) (the (A i)))) emp (dom A) *
           \<up> (A i = None) *is_map2 [j \<mapsto> v] r * \<up> (\<forall>j. M i j = None)"])
        subgoal
          by sep_auto
        subgoal for row_map'
          apply(rule ht_cons_prec[where P = P and P' = P for P , where Q =
                "\<lambda> Mi. \<exists>\<^sub>AA. is_map1 A Mi * \<up> (finite (dom A)) * \<up> (\<forall>ia ja. A ia = None \<longrightarrow> M ia ja = None) *
           Finite_Set.fold (\<lambda>i. (*) (is_map2 (M i) (the (A i)))) emp (dom A - {i}) * \<up> (A i = Some row_map') *
           is_map2 [j \<mapsto> v] row_map' * \<up> (\<forall>j. M i j = None)"])
          subgoal by sep_auto
          subgoal for Mi
            apply(rule ent_ex_preI)
            subgoal for A
              apply(rule ent_ex_postI[of _ _ A])
              apply sep_auto
              subgoal
                apply(subst assn_over_finite_extract_one[of "dom A" i])
                  apply simp
                 apply force
                apply simp

                apply sep_auto
                apply(subst assns_over_set_cong[of "dom A - {i}" is_map2
                       "\<lambda> ia y. if ia = i \<and> y = j then Some v else M ia y" "\<lambda> ia. the (A ia)"
                      is_map2 M "\<lambda> ia. the (A ia)"])
                  apply simp
                 apply simp
                apply(rule forw_subst_assn[of "[j \<mapsto> v]" "\<lambda>y. if y = j then Some v else M i y"])
                subgoal 
                  by (auto intro!: ext) 
                by sep_auto
               by sep_auto
             done
          apply sep_auto
          subgoal for A a b r
            apply(rule mod_exI[of _ "A(i \<mapsto> row_map')"])
            apply sep_auto
            apply(subst (asm) assns_over_set_cong[of "dom A" is_map2 M "\<lambda> i. the (A i)" is_map2 M
 "\<lambda> ia. the (if ia = i then Some row_map' else A ia)"])
              apply simp
             apply force
            apply(subst set_minus_singleton_eq)
             apply force
            by simp
          done
        done
      done
    subgoal for opt_row
      apply(rule ht_cons_prec[where P' = "\<exists>\<^sub>AA. is_map1 A Mi * \<up> (finite (dom A)) * \<up> (\<forall>i. A i = None \<longrightarrow> (\<forall>j. M i j = None)) *
          Finite_Set.fold (\<lambda>i. (*) (is_map2 (M i) (the (A i)))) emp (dom A - {i}) *
          \<up> (A i = Some opt_row) * is_map2 (M i) (the (A i))", where Q = Q and Q' = Q for Q ])
      subgoal
        apply(rule impl_of_exes_assn)
        subgoal for A
          apply sep_auto
          subgoal
            apply(subst assn_over_finite_extract_one[of "dom A" i is_map2 M "\<lambda> i. the (A i)"])
              apply simp
             apply (metis domI)
            by sep_auto
          using mod_pure_star_dist by auto
        done
      subgoal by sep_auto
      apply(rule ht_bind[where R = "\<lambda> r. \<exists>\<^sub>AA. is_map1 A Mi * \<up> (finite (dom A)) * \<up> (\<forall>i. A i = None \<longrightarrow> (\<forall>j. M i j = None)) *
           Finite_Set.fold (\<lambda>i. (*) (is_map2 (M i) (the (A i)))) emp (dom A - {i}) *
           \<up> (A i = Some opt_row) *
           is_map2 ((M i)(j \<mapsto> v)) r"])
      subgoal
        by sep_auto
      subgoal for opt_row'
        apply(rule ht_cons_prec[where P = P and P' = P for P, where Q =
                "\<lambda> r. \<exists>\<^sub>AA. is_map1 (A(i \<mapsto> opt_row')) r * \<up> (finite (dom A)) * \<up> (\<forall>i. A i = None \<longrightarrow> (\<forall>j. M i j = None)) *
           Finite_Set.fold (\<lambda>i. (*) (is_map2 (M i) (the (A i)))) emp (dom A - {i}) *
           \<up> (A i = Some opt_row) *
           is_map2 ((M i)(j \<mapsto> v)) opt_row'"])
      subgoal by sep_auto
       defer
      subgoal
        by sep_auto
      subgoal for Mi'
        apply(rule ent_ex_preI)
        subgoal for A
          apply(rule ent_ex_postI[of _ _ "A(i \<mapsto> opt_row')"])
          apply (sep_auto simp: mod_pure_star_dist)
          apply(rule same_assn)
          apply(subst semigroup_mult_class.mult.assoc)
          apply(rule arg_cong2[where f = "(*)"])
           apply simp
          apply(subst insert_absorb[of i "dom A"])
           apply force
          apply(subst assn_over_finite_extract_one[of "dom A" i])
            apply simp
           apply force
          apply(subst ab_semigroup_mult_class.mult.commute)
          apply(rule arg_cong2[where f = "(*)"])
          subgoal
            apply sep_auto
            by(auto intro!: arg_cong2[where f = is_map2])
          by(auto intro!: assns_over_set_cong arg_cong2[where f = is_map2])
        done
      done
    done
  done
  done

lemma empty_2d_rule:
  "<emp> empty1 <\<lambda> r. is_2d_map (\<lambda> x y. None) r>"
  unfolding is_2d_map_def
  using outer_empty.empty_rule
  by (sep_auto intro: mod_exI[of _ "\<lambda> x. None"])

definition 
"prog' v v' v''= do {
  arr \<leftarrow> empty1;
  arr \<leftarrow> update_2d 0 0 v arr;
  arr \<leftarrow> update_2d 0 1 v' arr;
  arr \<leftarrow> update_2d 4 1 v'' arr;
  arr \<leftarrow> update_2d 4 6 v'' arr;
  val \<leftarrow> lookup_2d arr 4 1;
  val' \<leftarrow> lookup_2d arr 0 10;
  case val of Some val \<Rightarrow> do 
        {
        case val' of Some val' \<Rightarrow> return (val = val') |
           None \<Rightarrow> return False
        }
  | None \<Rightarrow> return False
}"

lemma lookup_2d_rule:
 "<is_2d_map M Mi>
  lookup_2d Mi i j
  <\<lambda> r. is_2d_map M Mi * \<up> (r = M i j)>"
  unfolding lookup_2d_def is_2d_map_def
  apply(rule ht_bind[where R =
     "\<lambda> r. \<exists>\<^sub>AA. is_map1 A Mi * \<up> (finite (dom A)) * \<up> (\<forall>i j. A i = None \<longrightarrow> M i j = None) *
           Finite_Set.fold (\<lambda>i. (*) (is_map2 (M i) (the (A i)))) emp (dom A) * \<up> (r = A i)"])
  subgoal
    by sep_auto
  subgoal for mm
    apply(clarsimp split!: option.split)
    subgoal
      using ht_frame
      using outer_lookup.lookup_rule  
      by sep_auto 
    subgoal for m
      apply(rule ht_cons_prec[where P'=
       "\<exists>\<^sub>AA. is_map1 A Mi * \<up> (finite (dom A)) * \<up> (\<forall>i. A i = None \<longrightarrow> (\<forall>j. M i j = None)) *
          Finite_Set.fold (\<lambda>i. (*) (is_map2 (M i) (the (A i)))) emp (dom A - {i}) *
          \<up> (Some m = A i) * is_map2 (M i) m"
      and Q = "\<lambda> x. \<exists>\<^sub>AA. is_map1 A Mi * \<up> (finite (dom A)) * \<up> (\<forall>i. A i = None \<longrightarrow> (\<forall>j. M i j = None)) *
          Finite_Set.fold (\<lambda>i. (*) (is_map2 (M i) (the (A i)))) emp (dom A - {i}) *
          \<up> (Some m = A i) * is_map2 (M i) m *\<up> (x = M i j)"])
      subgoal
        apply sep_auto
        apply(rule ent_ex_preI)
        subgoal for A
          apply sep_auto
          apply(subst assn_over_finite_extract_one[of "dom A" i])
            apply simp
          subgoal
            apply auto
            by metis
          apply(rule ent_ex_postI[of _ _ A])
          apply sep_auto
          by (metis (no_types, lifting) assn_aci(11) ent_refl option.sel)
        done
      subgoal for r
        apply sep_auto
        apply(rule ent_ex_preI)
        subgoal for A
          apply(rule ent_ex_postI[of _ _ A])
          apply sep_auto
          apply(subst assn_over_finite_extract_one[of "dom A" i])
            apply simp
          subgoal
            apply auto
            by metis
          subgoal
            apply sep_auto
            by (metis (no_types, lifting) assn_aci(11) ent_refl option.sel)
          by sep_auto
        done
      by sep_auto
    done
  done

lemma "<emp> prog' v v' v''<\<lambda> r. \<up> (\<not> r)>"
  using update_2d_rule lookup_2d_rule empty_2d_rule
  unfolding prog'_def 
  by sep_auto

end

locale BFS_subprocedures_Imperative_spec =
fixes unvisited_neighbs::"'nh \<Rightarrow> 'vis \<Rightarrow> 'nh_nv Heap"
and add_to_working_frontier::"'wfront \<Rightarrow> 'nh_nv \<Rightarrow> 'wfront Heap"
and to_ordinary_frontier::"'wfront \<Rightarrow> 'front Heap"
and frontier_fold_imp::"('ver \<Rightarrow> 'wfront \<Rightarrow> 'wfront Heap) \<Rightarrow> 'front \<Rightarrow> 'wfront \<Rightarrow> 'wfront Heap"
and lookup_imp :: "'ver \<Rightarrow> 'adjmap_imp \<Rightarrow> 'nh option Heap"
and nh_emp::"'nh Heap"
and wf_empty::"'wfront Heap"
and add_to_dag_nh::"'nh_ex \<Rightarrow> 'nh_nv \<Rightarrow> 'nh_ex Heap"
and update_dag_imp::"'ver \<Rightarrow> 'nh_ex \<Rightarrow> 'dag \<Rightarrow> 'dag Heap"
and to_dag_nh::"'nh_nv \<Rightarrow> 'nh_ex Heap"
and lookup_dag_imp::"'ver \<Rightarrow> 'dag \<Rightarrow> 'nh_ex option Heap"
and is_neighb_nv_emp::"'nh_nv \<Rightarrow> bool Heap"
and dag_fold_imp::"('ver \<Rightarrow> 'dag \<Rightarrow> 'dag Heap) \<Rightarrow> 'front \<Rightarrow> 'dag \<Rightarrow> 'dag Heap"
and imp_adjmap_empty::"'adjmap_imp Heap" 
and imp_adjmap_upd::"'ver \<Rightarrow> 'nh \<Rightarrow> 'adjmap_imp \<Rightarrow> 'adjmap_imp Heap"
and to_ordinary_neighb::"'nh_ex \<Rightarrow> 'nh Heap"
and dag_it_init :: "'dag \<Rightarrow> 'it Heap"
and dag_it_has_next :: "'it \<Rightarrow> bool Heap"
and dag_it_next :: "'it \<Rightarrow> (('ver \<times> 'nh_ex) \<times> 'it) Heap"
begin

definition "neighbourhood_imp Gi v = 
  do {nhd \<leftarrow> lookup_imp v Gi;
      case nhd of None \<Rightarrow> nh_emp
      | Some nhd \<Rightarrow> return nhd}"

definition "next_frontier_body Gi vis u nf = 
   do {nhd \<leftarrow> neighbourhood_imp Gi u;
       uv_nhd \<leftarrow> unvisited_neighbs nhd vis;
       add_to_working_frontier nf uv_nhd}"

definition "next_frontier_imperative Gi frontier vis =
    do {nf \<leftarrow> wf_empty;
        nf' \<leftarrow> frontier_fold_imp (next_frontier_body Gi vis) frontier nf;
        to_ordinary_frontier nf'}"

definition "add_dag_neighbs_imp Gi u more_nh = 
 do {is_emp \<leftarrow> is_neighb_nv_emp more_nh;
   if is_emp then return Gi
   else
   do { nho \<leftarrow> lookup_dag_imp u Gi;
      case nho of None \<Rightarrow>
        do { nho \<leftarrow> to_dag_nh more_nh;
             update_dag_imp u nho Gi
            }
     | Some nho \<Rightarrow>
      do {nho \<leftarrow> add_to_dag_nh nho more_nh;
          update_dag_imp u nho Gi }
    }
  }"

definition "expand_tree_body Gi vis u dag = 
   do {nhd \<leftarrow> neighbourhood_imp Gi u;
       uv_nhd \<leftarrow> unvisited_neighbs nhd vis;
       add_dag_neighbs_imp dag u uv_nhd}"

definition "expand_tree_imp Gi dag front vis = dag_fold_imp (expand_tree_body Gi vis) front dag"

definition "put_graph_neighb Gi v new_nh =
            imp_adjmap_upd v new_nh Gi"

definition "change_dag_format_body = (\<lambda> (x, y) G.
    do {nh \<leftarrow> to_ordinary_neighb y;
      put_graph_neighb G x nh})"

partial_function (heap) change_dag_format_loop where
  "change_dag_format_loop iter Gr= 
   do {b \<leftarrow> dag_it_has_next iter;
       if \<not> b then return Gr
       else do{ res \<leftarrow> dag_it_next iter;
          case res of ((v, nh), iter') \<Rightarrow>
               do {Gr' \<leftarrow> change_dag_format_body (v, nh) Gr;
                   change_dag_format_loop iter' Gr'}}}"

definition "change_dag_format dag = 
           do {start \<leftarrow> imp_adjmap_empty;
            iter \<leftarrow> dag_it_init dag;
            change_dag_format_loop iter start}"

end

lemma ht_exPI:"<P> c <\<lambda> r. Q x r> \<Longrightarrow> <P> c <\<lambda> r. \<exists>\<^sub>A x. Q x r>"
  by sep_auto

lemma ht_ex_pre_and_post_I:"(\<And> x. <P x> c <\<lambda> r. Q x r>) \<Longrightarrow> <\<exists>\<^sub>A x. P x> c <\<lambda> r. \<exists>\<^sub>A x. Q x r>"
  by sep_auto

lemma ht_ex_with_change_pre_and_post_I: 
  "(\<And> x. <P x> c <\<lambda> r. Q (f x) r>) \<Longrightarrow> <\<exists>\<^sub>A x. P x> c <\<lambda> r. \<exists>\<^sub>A x. Q x r>"
  by sep_auto

context imp_map_iterate
begin

lemma it_return_rule:
  "<is_it m p m' it>return x<\<lambda> r. \<up> (r = x) * is_map m p>"
  apply(rule ht_cons_pre[OF _ ht_frame[OF ], of _ true, 
                 OF quit_iteration[simplified assn_times_comm[of _ true]]])
  by sep_auto

lemma it_return_rule_frame:
  "<is_it m p m' it * F>return x<\<lambda> r. \<up> (r = x) * is_map m p * F>"
  apply(rule ht_frame)
  by(rule it_return_rule) 

end

locale BFS_subprocedures_Imperative =

BFS_subprocedures where fold_vset = fold_vset and fold_adjmap = fold_adjmap +
imp_map_empty is_dag dag_empty +
BFS_subprocedures_Imperative_spec where unvisited_neighbs= unvisited_neighbs and
  add_to_working_frontier = add_to_working_frontier and
  to_ordinary_frontier = to_ordinary_frontier and 
  frontier_fold_imp = frontier_fold_imp and
  lookup_imp = lookup_imp and 
  nh_emp = nh_emp and
  wf_empty = wf_empty and
  add_to_dag_nh = add_to_dag_nh and
  update_dag_imp = update_dag_imp and
  to_dag_nh = to_dag_nh and
  lookup_dag_imp = lookup_dag_imp and
  is_neighb_nv_emp = is_neighb_nv_emp and
  dag_fold_imp = dag_fold_imp+
imp_graph_map: imp_map_lookup is_map lookup_imp +
imp_dag_map: imp_map_lookup is_dag lookup_dag_imp +
imp_dag_map_upd: imp_map_update is_dag update_dag_imp +
adj_map_imp_upd: imp_map_update is_map imp_adjmap_upd +
adj_map_imp_empty: imp_map_empty is_map imp_adjmap_empty +
imp_map_iterate is_dag is_dag_it dag_it_init dag_it_has_next dag_it_next
for  fold_vset::"('ver \<Rightarrow> 'vset \<Rightarrow> 'vset) \<Rightarrow> 'vset \<Rightarrow> 'vset \<Rightarrow> 'vset"
and fold_adjmap::"('ver \<Rightarrow> 'adjmap \<Rightarrow> 'adjmap) \<Rightarrow> 'vset \<Rightarrow> 'adjmap \<Rightarrow> 'adjmap"
and unvisited_neighbs::"'nh \<Rightarrow> 'vis \<Rightarrow> 'nh_nv Heap"
and add_to_working_frontier::"'wfront \<Rightarrow> 'nh_nv \<Rightarrow> 'wfront Heap"
and to_ordinary_frontier::"'wfront \<Rightarrow> 'front Heap"
and frontier_fold_imp::"('ver \<Rightarrow> 'wfront \<Rightarrow> 'wfront Heap) \<Rightarrow> 'front \<Rightarrow> 'wfront \<Rightarrow> 'wfront Heap"
and lookup_imp :: "'ver \<Rightarrow> 'adjmap_imp \<Rightarrow> 'nh option Heap"
and nh_emp::"'nh Heap"
and wf_empty::"'wfront Heap"
and is_map 
and is_dag
and lookup_dag_imp::"'ver \<Rightarrow> 'dag \<Rightarrow> 'nh_ex option Heap"
and update_dag_imp
and add_to_dag_nh::"'nh_ex \<Rightarrow> 'nh_nv \<Rightarrow> 'nh_ex Heap"
and to_dag_nh::"'nh_nv \<Rightarrow> 'nh_ex Heap"
and is_neighb_nv_emp::"'nh_nv \<Rightarrow> bool Heap"
and dag_fold_imp::"('ver \<Rightarrow> 'dag \<Rightarrow> 'dag Heap) \<Rightarrow> 'front \<Rightarrow> 'dag \<Rightarrow> 'dag Heap"
and dag_empty is_dag_it+
fixes is_neighb::"'vset \<Rightarrow> 'nh \<Rightarrow> assn"
and is_vis::"'vset \<Rightarrow> 'vis \<Rightarrow> assn"
and is_neighb_nv::"'vset \<Rightarrow> 'nh_nv \<Rightarrow> assn"
and is_wfront::"'vset \<Rightarrow> 'wfront \<Rightarrow> assn"
and is_front::"'vset \<Rightarrow> 'front \<Rightarrow> assn"
and is_dag_nh::"'vset \<Rightarrow> 'nh_ex \<Rightarrow> assn"
and map_fold::"(('ver \<times> 'vset) \<Rightarrow> 'adjmap \<Rightarrow>  'adjmap)
                 \<Rightarrow> 'adjmap \<Rightarrow> 'adjmap \<Rightarrow>  'adjmap"
assumes nd_emp_rule: "<emp> nh_emp <is_neighb \<emptyset>\<^sub>N >"
and wf_empty_rule: "<emp> wf_empty<is_wfront \<emptyset>\<^sub>N>"
and is_neighb_nv_emp_rule: 
  "\<And> nnh nnhi. <is_neighb_nv nnh nnhi> 
     is_neighb_nv_emp nnhi
     <\<lambda> r. is_neighb_nv nnh nnhi * \<up> (r \<longleftrightarrow> (nnh = \<emptyset>\<^sub>N))>"
and is_neighb_nv_invar: "\<And> nnh nnhi. is_neighb_nv nnh nnhi = is_neighb_nv nnh nnhi * \<up> (vset_inv nnh) "
and unvisited_neighbs_rule: 
  "\<And> nd ndi vis visi. 
     <is_neighb nd ndi * is_vis vis visi> 
         unvisited_neighbs  ndi visi 
     <\<lambda> r. is_neighb nd ndi * is_vis vis visi * is_neighb_nv (diff nd vis) r>"
and add_to_working_frontier_rule:
   "\<And> f fi nh nhi.
     <is_wfront f fi * is_neighb_nv nh nhi>
         add_to_working_frontier fi nhi
     <\<lambda> r. is_wfront (f \<union>\<^sub>G nh) r * is_neighb_nv nh nhi>"
and frontier_fold_rule:
   "\<And> front fronti init initi F fi f. 
      (\<And> u front fronti. 
          <F * is_wfront front fronti> 
            fi u fronti 
          <\<lambda> r. F * is_wfront (f u front) r>) \<Longrightarrow>
      <F* is_front front fronti * is_wfront init initi> 
         frontier_fold_imp fi fronti initi 
      <\<lambda>r. F * is_front front fronti * is_wfront (fold_vset f front init) r>"
and to_ordinary_frontier_rule:
  "\<And> f wfi. <is_wfront f wfi> to_ordinary_frontier wfi <\<lambda> r. is_wfront f wfi * is_front f r>"
and add_to_dag_nh_rule: 
   "\<And> dag_nh dag_nhi nnh nnhi.
      <is_dag_nh dag_nh dag_nhi * is_neighb_nv nnh nnhi> 
         add_to_dag_nh dag_nhi nnhi
       <\<lambda> r. is_dag_nh (dag_nh \<union>\<^sub>G nnh) r * is_neighb_nv nnh nnhi>"
and to_dag_nh_rule: 
   "\<And> nh nhi.
      <is_neighb_nv nh nhi> 
         to_dag_nh nhi
       <\<lambda> dag_nhi. is_dag_nh nh dag_nhi * is_neighb_nv nh nhi>"
and dag_fold_imp:
   "\<And> front fronti init initi dag_assn F fi f. 
      (\<And> dag dagi u.
        < F * dag_assn dag dagi> fi u dagi  <\<lambda>r. F * dag_assn (f u dag) r>) \<Longrightarrow>
      < F * is_front front fronti * dag_assn init initi> 
         dag_fold_imp fi fronti initi 
      <\<lambda>r. F * is_front front fronti * dag_assn (fold_adjmap f front init) r>"
and to_ordinary_neighb_rule:
   "<is_dag_nh dag_nh dag_nhi> to_ordinary_neighb dag_nhi
    <\<lambda> r. is_dag_nh dag_nh dag_nhi * is_neighb dag_nh r>"
begin

definition "graph_assn Gr Gri = 
  (\<exists>\<^sub>A A. is_map A Gri * \<up> (adjmap_inv Gr) * \<up> (finite (dom A)) *  \<up> (dom (lookup Gr) = dom A)*
       Finite_Set.fold (\<lambda> i ass. is_neighb (the (lookup Gr i)) (the (A i)) * ass) emp (dom A))"

lemma graph_assn_invar_extract:
   "graph_assn Gr Gri = graph_assn Gr Gri *  \<up> (adjmap_inv Gr)"
  unfolding graph_assn_def
  apply simp
  apply(rule ent_iffI)
  by sep_auto

lemma graph_assn_abstract_transfer:
  assumes "\<And> x. lookup Gr x = lookup Gr' x" "adjmap_inv Gr'"
  shows  "graph_assn Gr Gri \<Longrightarrow>\<^sub>A graph_assn Gr' Gri"
  unfolding graph_assn_def
  apply(rule ent_ex_preI)
  subgoal for A
    apply(rule ent_ex_postI[of _ _ A])
    apply (sep_auto simp: assms)
    by (metis domIff assms(1) not_None_eq)
  done

lemma graph_assn_abstract_cong:
  assumes "\<And> x. lookup Gr x = lookup Gr' x"  "adjmap_inv Gr"  "adjmap_inv Gr'"
  shows  "graph_assn Gr Gri = graph_assn Gr' Gri"
  apply(rule ent_iffI)
  using assms 
  by(sep_auto intro: graph_assn_abstract_transfer)

lemma "<emp> do {x \<leftarrow> nh_emp; z \<leftarrow> nh_emp;  y \<leftarrow> if x = x then return y else undefined; return y} 
       <\<lambda> r. \<up> (r = y)>"
  using nd_emp_rule
  by sep_auto

lemma next_frontier_body_rule:
   "<graph_assn G Gi  * is_vis vis visi * is_wfront nf nfi>
     next_frontier_body Gi visi u nfi
    <\<lambda> r. graph_assn G Gi * is_vis vis visi * is_wfront (nf \<union>\<^sub>G (diff (\<N>\<^sub>G u) vis)) r>"
  unfolding next_frontier_body_def neighbourhood_imp_def
            graph_assn_def ex_distrib_star[symmetric]
  apply(rule ht_ex_pre_and_post_I)
  subgoal for A
    apply simp
    apply(rule ht_bind[where R = "\<lambda> r. is_map A Gi * \<up> (adjmap_inv G) * \<up> (finite (dom A)) * \<up> (dom (lookup G) = dom A) *
     Finite_Set.fold (\<lambda>i. (*) (is_neighb (the (lookup G i)) (the (A i)))) emp (dom A) *
     is_vis vis visi *
     is_wfront nf nfi * \<up> (r = A u)"])
    subgoal
      by sep_auto
    subgoal for nho
      apply(clarsimp split!: option.split)
      subgoal
        apply(rule ht_bind[where R = "\<lambda> r. is_map A Gi * \<up> (adjmap_inv G) * \<up> (finite (dom A)) * \<up> (dom (lookup G) = dom A) *
     Finite_Set.fold (\<lambda>i. (*) (is_neighb (the (lookup G i)) (the (A i)))) emp (dom A) *
     is_vis vis visi *
     is_wfront nf nfi *
     \<up> (A u = None) * is_neighb \<emptyset>\<^sub>N r"])
        subgoal
          using nd_emp_rule
          by sep_auto
        subgoal for empi
        apply(rule ht_bind[where R = "\<lambda> r. is_map A Gi * \<up> (adjmap_inv G) * \<up> (finite (dom A)) * \<up> (dom (lookup G) = dom A) *
     Finite_Set.fold (\<lambda>i. (*) (is_neighb (the (lookup G i)) (the (A i)))) emp (dom A) *
     is_vis vis visi *
     is_wfront nf nfi *
     \<up> (A u = None) *
     is_neighb \<emptyset>\<^sub>N empi * is_neighb_nv (\<emptyset>\<^sub>N -\<^sub>G vis) r"])
          subgoal
            using unvisited_neighbs_rule by sep_auto
          subgoal for nh_without_vis
            using add_to_working_frontier_rule[of nf nfi "\<emptyset>\<^sub>N -\<^sub>G vis" nh_without_vis]
            by (sep_auto simp: Graph.neighbourhood_def split: option.split)
          done
        done
      subgoal for nho

        apply(rule ht_cons_prec[where P' = "is_map A Gi * \<up> (adjmap_inv G) * \<up> (finite (dom A)) * \<up> (dom (lookup G) = dom A) *
     Finite_Set.fold (\<lambda>i. (*) (is_neighb (the (lookup G i)) (the (A i)))) emp (dom A - {u}) *
     is_vis vis visi *
     is_wfront nf nfi *
     \<up> (A u = Some nho) 
     *is_neighb (the (lookup G u)) (the (A u))"
       and Q = "\<lambda> r. is_map A Gi * \<up> (adjmap_inv G) * \<up> (finite (dom A)) * \<up> (dom (lookup G) = dom A) *
         Finite_Set.fold (\<lambda>i. (*) (is_neighb (the (lookup G i)) (the (A i)))) emp (dom A - {u}) *
         is_vis vis visi *is_neighb (the (lookup G u)) (the (A u)) * \<up> (Some nho = A u)*
         is_wfront (nf \<union>\<^sub>G (\<N>\<^sub>G u -\<^sub>G vis)) r "])
        subgoal
          apply sep_auto
          subgoal
            apply(subst assn_over_finite_extract_one[of "dom A" u])
            by sep_auto
          by sep_auto
        subgoal
          apply sep_auto
          subgoal
            apply(subst assn_over_finite_extract_one[of "dom A" u])
            by sep_auto
          by sep_auto
        apply(rule ht_bind[where R = "\<lambda> r. is_map A Gi * \<up> (adjmap_inv G) * \<up> (finite (dom A)) * \<up> (dom (lookup G) = dom A) *
     Finite_Set.fold (\<lambda>i. (*) (is_neighb (the (lookup G i)) (the (A i)))) emp (dom A - {u}) *
     is_vis vis visi *
     is_wfront nf nfi *
     \<up> (A u = Some nho) *
     is_neighb (the (lookup G u)) (the (A u)) * is_neighb_nv (the (lookup G u) -\<^sub>G vis) r"])
        subgoal
          using unvisited_neighbs_rule
          by sep_auto
        apply(cases "lookup G u")
        subgoal
          by sep_auto
        unfolding Graph.neighbourhood_def
        apply simp

        using add_to_working_frontier_rule
        by sep_auto
      done
    done
  done

lemma next_frontier_imperative_rule:
   "<graph_assn G Gi * is_front frontier frontieri * is_vis vis visi> 
     next_frontier_imperative Gi frontieri visi 
    <\<lambda> r. graph_assn G Gi * is_front frontier frontieri * is_vis vis visi 
          * is_front (next_frontier frontier vis) r >"
  unfolding next_frontier_imperative_def
  apply(rule ht_bind[where R = "\<lambda> r. graph_assn G Gi * is_front frontier frontieri * is_vis vis visi * is_wfront \<emptyset>\<^sub>N r"])
  subgoal
    using wf_empty_rule
    by sep_auto
  subgoal for empi
    apply(rule ht_bind)
     (*apply(rule ht_cons_prec)*)
    apply(rule ht_cons_pre)
    defer
    apply(rule frontier_fold_rule[of "is_vis vis visi * graph_assn G Gi" "next_frontier_body Gi visi"
                 "\<lambda> u frontier. frontier \<union>\<^sub>G (\<N>\<^sub>G u -\<^sub>G vis)" frontier frontieri "\<emptyset>\<^sub>N" "empi"])
    subgoal  for u f fi
      using next_frontier_body_rule[of Gi vis visi f fi u] by sep_auto
    subgoal for new_wf
      using to_ordinary_frontier_rule[of _  new_wf]
      by(sep_auto simp: next_frontier_def)
    subgoal
      by sep_auto
    done
  done

definition "dag_assn D Di = 
  (\<exists>\<^sub>A A. is_dag A Di * \<up> (adjmap_inv D) * \<up> (finite (dom A)) *  \<up> (dom (lookup D) = dom A)*
       Finite_Set.fold (\<lambda> i ass. is_dag_nh (the (lookup D i)) (the (A i)) * ass) emp (dom A))"

lemma add_dag_neighbs_imp_rule:
 "<dag_assn D Di * is_neighb_nv more_nh more_nhi>
   add_dag_neighbs_imp Di u more_nhi
  <\<lambda> r. dag_assn (add_neighbs D u more_nh) r * is_neighb_nv more_nh more_nhi>"
  unfolding add_dag_neighbs_imp_def unfolding dag_assn_def ex_assn_move_out(1)
  apply(rule ht_exEI)
  subgoal for A
    apply(rule ht_bind[where R = "\<lambda> r. is_dag A Di * \<up> (adjmap_inv D)* \<up> (finite (dom A)) * \<up> (dom (lookup D) = dom A) *
     Finite_Set.fold (\<lambda>i. (*) (is_dag_nh (the (lookup D i)) (the (A i)))) emp (dom A) *
     is_neighb_nv more_nh more_nhi  * \<up> (r = (more_nh = \<emptyset>\<^sub>N))"])
    subgoal
      using is_neighb_nv_emp_rule by sep_auto
    subgoal for b
      apply(clarsimp split!: if_split)
      subgoal
        by (sep_auto simp: add_neighbs_def)
    apply(rule ht_bind[where R = "\<lambda> r. is_dag A Di * \<up> (adjmap_inv D)* \<up> (finite (dom A)) * \<up> (dom (lookup D) = dom A) *
     Finite_Set.fold (\<lambda>i. (*) (is_dag_nh (the (lookup D i)) (the (A i)))) emp (dom A) *
     is_neighb_nv more_nh more_nhi  * \<up> (r = A u) * \<up> (more_nh \<noteq> \<emptyset>\<^sub>N)"])
    subgoal 
      by sep_auto
    subgoal for nhuo
      apply(clarsimp split!: option.split)
      subgoal
        apply(rule ht_bind[where R = "\<lambda> r. is_dag A Di * \<up> (adjmap_inv D) * \<up> (finite (dom A)) * \<up> (dom (lookup D) = dom A) *
     Finite_Set.fold (\<lambda>i. (*) (is_dag_nh (the (lookup D i)) (the (A i)))) emp (dom A) *
     is_neighb_nv more_nh more_nhi *
     \<up> (None = A u) * is_dag_nh more_nh r * \<up> (more_nh \<noteq> \<emptyset>\<^sub>N)"])
        subgoal
          using to_dag_nh_rule by sep_auto
          subgoal
            for new_dag_nh
            apply(rule ht_exPI[of  _ _ _ "A(u\<mapsto>new_dag_nh)"])
            using imp_dag_map_upd.update_rule[of A Di u new_dag_nh]
            apply sep_auto
            apply(subst assn_over_finite_insert_one)
              apply simp
             apply force
            apply(subst assns_over_set_cong[where assn' = is_dag_nh
              and f' = "\<lambda> i. the (lookup D i)" and g' = "the o A"])
              apply simp
            subgoal
              by(auto simp add: add_neighbs_def Graph.adjmap.map_update split: option.split)
            apply (sep_auto simp: add_neighbs_def Graph.adjmap.map_update Graph.adjmap.invar_update 
                           split: option.split)
            by force
          done
        subgoal for nhu
          apply(rule ht_cons_pre[of _ "is_dag A Di * \<up> (adjmap_inv D) * \<up> (finite (dom A)) * \<up> (dom (lookup D) = dom A) *
    Finite_Set.fold (\<lambda>i. (*) (is_dag_nh (the (lookup D i)) (the (A i)))) emp (dom A - {u}) *
    is_neighb_nv more_nh more_nhi *
    is_dag_nh (the (lookup D u)) nhu *
    \<up> (A u = Some nhu ) *
    \<up> (more_nh \<noteq> \<emptyset>\<^sub>N)"])
          subgoal
            apply sep_auto
            subgoal
              apply(subst assn_over_finite_extract_one[where i = u])
                apply simp
               apply force
              apply sep_auto
              by (smt (verit, best) assn_aci(11) entails_def option.sel)
            by sep_auto
          apply(rule ht_bind[where R = "\<lambda> r. is_dag A Di * \<up> (adjmap_inv D) * \<up> (finite (dom A)) * \<up> (dom (lookup D) = dom A) *
     Finite_Set.fold (\<lambda>i. (*) (is_dag_nh (the (lookup D i)) (the (A i)))) emp (dom A - {u}) *
     is_neighb_nv more_nh more_nhi *
     is_dag_nh (the (lookup D u) \<union>\<^sub>G more_nh) r *
     \<up> (A u = Some nhu) *
     \<up> (more_nh \<noteq> \<emptyset>\<^sub>N)"])
          subgoal
            using  add_to_dag_nh_rule
            by sep_auto
          subgoal for bigger_nh
            apply(rule ht_exPI[of _ _ _ "A(u \<mapsto> bigger_nh)"])
            apply(rule ht_cons_post_prec[where Q = 
     "\<lambda> r. is_dag (A(u \<mapsto> bigger_nh)) r * \<up> (adjmap_inv D) * 
          \<up> (finite (dom (A(u \<mapsto> bigger_nh)))) *
          \<up> (dom (lookup (add_neighbs D u more_nh)) = dom (A(u \<mapsto> bigger_nh))) *
          Finite_Set.fold
           (\<lambda>i. (*) (is_dag_nh (the (lookup D i)) (the ((A) i)))) emp
           (dom A - {u}) * is_neighb_nv more_nh more_nhi
         *is_dag_nh (the (lookup (add_neighbs D u more_nh) u)) bigger_nh * \<up> (more_nh \<noteq> \<emptyset>\<^sub>N)"])
            subgoal
              using imp_dag_map_upd.update_rule[of A Di u bigger_nh]
              by (sep_auto simp: add_neighbs_def Graph.adjmap.map_update  Graph.adjmap.invar_update split: option.split)
            subgoal for new_Gi
              apply sep_auto
              subgoal
                apply(subst assn_over_finite_extract_one[where S = "Set.insert u (dom A)" and i = u])
                  apply simp
                 apply simp
                apply simp
                apply(subst (2) assns_over_set_cong[where assn' = is_dag_nh and f' = "\<lambda> i. (the (lookup D i))"
                         and g'="the o A"])
                  apply simp
                subgoal
                  by(auto simp add: add_neighbs_def Graph.adjmap.map_update split: option.split)
                by sep_auto
              by (sep_auto simp: add_neighbs_def Graph.adjmap.invar_update Graph.adjmap.map_update
                          split: option.split)
            done
          done
        done
      done
    done
  done

lemma expand_tree_body_rule:
   "<graph_assn G Gi * is_vis vis visi * dag_assn D Di>
     expand_tree_body Gi visi u Di
    <\<lambda> r. graph_assn G Gi * is_vis vis visi * dag_assn (add_neighbs D u (\<N>\<^sub>G u -\<^sub>G vis)) r>"
  unfolding expand_tree_body_def neighbourhood_imp_def
            graph_assn_def ex_distrib_star[symmetric]
  apply(rule ht_ex_pre_and_post_I)
  subgoal for A
    apply simp
    apply(rule ht_bind[where R = "\<lambda> r. is_map A Gi * \<up> (adjmap_inv G) * \<up> (finite (dom A)) * \<up> (dom (lookup G) = dom A) *
     Finite_Set.fold (\<lambda>i. (*) (is_neighb (the (lookup G i)) (the (A i)))) emp (dom A) *
     is_vis vis visi *
     dag_assn D Di * \<up> (r = A u)"])
    subgoal
      by sep_auto
    subgoal for nho
      apply(clarsimp split!: option.split)
      subgoal
        apply(rule ht_bind[where R = "\<lambda> r. is_map A Gi * \<up> (adjmap_inv G) * \<up> (finite (dom A)) * \<up> (dom (lookup G) = dom A) *
     Finite_Set.fold (\<lambda>i. (*) (is_neighb (the (lookup G i)) (the (A i)))) emp (dom A) *
     is_vis vis visi *
     dag_assn D Di *
     \<up> (None = A u) *
     \<up> (A u = None) * is_neighb \<emptyset>\<^sub>N r"])
        subgoal
          using nd_emp_rule
          by sep_auto
        subgoal for empi
        apply(rule ht_bind[where R = "\<lambda> r. is_map A Gi * \<up> (adjmap_inv G) * \<up> (finite (dom A)) * \<up> (dom (lookup G) = dom A) *
     Finite_Set.fold (\<lambda>i. (*) (is_neighb (the (lookup G i)) (the (A i)))) emp (dom A) *
     is_vis vis visi *
     dag_assn D Di *
     \<up> (A u = None) *
     is_neighb \<emptyset>\<^sub>N empi * is_neighb_nv (\<emptyset>\<^sub>N -\<^sub>G vis) r"])
          subgoal
            using unvisited_neighbs_rule by sep_auto
          subgoal for nh_without_vis
            using add_dag_neighbs_imp_rule[of D Di "\<emptyset>\<^sub>N -\<^sub>G vis" nh_without_vis u]
            by (sep_auto simp: Graph.neighbourhood_def split: option.split)
          done
        done
      subgoal for nho

        apply(rule ht_cons_prec[where P' = "is_map A Gi * \<up> (adjmap_inv G) * \<up> (finite (dom A)) * \<up> (dom (lookup G) = dom A) *
     Finite_Set.fold (\<lambda>i. (*) (is_neighb (the (lookup G i)) (the (A i)))) emp (dom A - {u}) *
     is_vis vis visi *
     dag_assn D Di *
     \<up> (A u = Some nho) 
     *is_neighb (the (lookup G u)) (the (A u))"
       and Q = "\<lambda> r. is_map A Gi * \<up> (adjmap_inv G) * \<up> (finite (dom A)) * \<up> (dom (lookup G) = dom A) *
         Finite_Set.fold (\<lambda>i. (*) (is_neighb (the (lookup G i)) (the (A i)))) emp (dom A - {u}) *
         is_vis vis visi *is_neighb (the (lookup G u)) (the (A u)) * \<up> (Some nho = A u)*
         dag_assn (add_neighbs D u (\<N>\<^sub>G u -\<^sub>G vis)) r "])
        subgoal
          apply sep_auto
          subgoal
            apply(subst assn_over_finite_extract_one[of "dom A" u])
            by sep_auto
          by sep_auto
        subgoal
          apply sep_auto
          subgoal
            apply(subst assn_over_finite_extract_one[of "dom A" u])
            by sep_auto
          by sep_auto
        apply(rule ht_bind[where R = "\<lambda> r. is_map A Gi * \<up> (adjmap_inv G) * \<up> (finite (dom A)) * \<up> (dom (lookup G) = dom A) *
     Finite_Set.fold (\<lambda>i. (*) (is_neighb (the (lookup G i)) (the (A i)))) emp (dom A - {u}) *
     is_vis vis visi *
     dag_assn D Di *
     \<up> (A u = Some nho) *
     is_neighb (the (lookup G u)) (the (A u)) * is_neighb_nv (the (lookup G u) -\<^sub>G vis) r"])
        subgoal
          using unvisited_neighbs_rule
          by sep_auto
        apply(cases "lookup G u")
        subgoal
          by sep_auto
        using add_dag_neighbs_imp_rule 
        by (sep_auto simp: Graph.neighbourhood_def)
      done
    done
  done

lemma expand_tree_rule:
   "<graph_assn G Gi * is_front front fronti * is_vis vis visi * dag_assn D Di>
     expand_tree_imp Gi Di fronti visi
    <\<lambda> r. graph_assn G Gi * is_front front fronti * is_vis vis visi * 
           dag_assn (expand_tree D front vis) r>"
  unfolding expand_tree_imp_def expand_tree_def
  using expand_tree_body_rule[of Gi vis visi]
  using dag_fold_imp[of "graph_assn G Gi * is_vis vis visi" dag_assn  "expand_tree_body Gi visi"  ] 
  by sep_auto


lemma dag_empty_rule:
 "<emp>dag_empty<dag_assn empty>"
  unfolding dag_assn_def
  by(rule ht_exPI[where x = "\<lambda> x. None"])
    (sep_auto simp: Graph.adjmap.invar_empty Graph.adjmap.map_empty)

lemma change_graph_neighb_rule:
  shows "<graph_assn Gr Gi * is_neighb new_nh new_nhi> 
    put_graph_neighb Gi v new_nhi
   <\<lambda> r. graph_assn (update v new_nh Gr) r>" 
  unfolding put_graph_neighb_def graph_assn_def ex_distrib_star[symmetric]
  apply(rule ht_ex_with_change_pre_and_post_I[where f = "\<lambda> A. A(v \<mapsto> new_nhi)"])
  subgoal for A
    using adj_map_imp_upd.update_rule[of A Gi v new_nhi]
    apply sep_auto
    subgoal
      apply(cases "v \<in> dom A")
      subgoal
        (* Case v \<in> dom A *)
        (* First simplify: Set.insert v (dom A) = dom A when v \<in> dom A *)
        apply(simp add: insert_absorb)
        (* Extract v from LHS fold (assumption) *)
        apply(subst (asm) assn_over_finite_extract_one[of "dom A" v])
          apply simp
         apply simp
        (* Extract v from RHS fold (conclusion) *)
        apply(subst assn_over_finite_extract_one[of "dom A" v])
          apply simp
         apply simp
        (* Rewrite the RHS fold to match LHS using map_update simplification *)
        apply(subst assns_over_set_cong[where S = "dom A - {v}" and assn' = is_neighb 
            and f' = "\<lambda> i. the (lookup Gr i)" and g' = "\<lambda> i. the (A i)"])
          apply simp
        subgoal for y
          by(auto simp add: Graph.adjmap.map_update split: option.split)
        by (sep_auto simp: Graph.adjmap.map_update Graph.adjmap.invar_update split: option.split)
      subgoal
        (* Case v \<notin> dom A: Need to handle insert *)
        (* Extract v from RHS fold (conclusion) - it's in insert v (dom A) *)
        apply(subst assn_over_finite_insert_one[of "dom A" v])
          apply simp
         apply simp
        (* Rewrite the RHS fold over dom A to match LHS by showing the if-then-else simplifies to A i *)
        apply(subst assns_over_set_cong[where S = "dom A" and assn' = is_neighb 
            and f' = "\<lambda> i. the (lookup Gr i)" and g' = "\<lambda> i. the (A i)"])
          apply simp
        subgoal for i
          by(auto simp add: Graph.adjmap.map_update split: option.split)
        (* Simplify the extracted element: lookup (update v new_nh Gr) v = Some new_nh *)
        apply(simp add: Graph.adjmap.map_update Graph.adjmap.invar_update)
        by sep_auto
      done
    done
  done

lemma change_dag_format_body_rule:
  shows "<graph_assn Gr Gi * is_dag_nh nhd nhdi>
    change_dag_format_body (v, nhdi) Gi
   <\<lambda> r. graph_assn (update v nhd Gr) r * is_dag_nh nhd nhdi>"
  unfolding change_dag_format_body_def prod.case
  apply(rule ht_bind[where R = "\<lambda> r. graph_assn Gr Gi * is_dag_nh nhd nhdi * is_neighb nhd r"])
  subgoal
    using to_ordinary_neighb_rule by sep_auto
  subgoal for nhi
    using change_graph_neighb_rule[of Gr Gi nhd nhi v]
    by sep_auto
  done

lemma graph_empty_rule:
  shows "<emp> imp_adjmap_empty <graph_assn empty>"
  unfolding graph_assn_def
  apply(rule ht_exPI[where x = "\<lambda> x. None"])
  by (sep_auto simp: Graph.adjmap.invar_empty Graph.adjmap.map_empty)

lemma  change_dag_format_loop_induction:
       "<is_dag_it D dagi D' it * \<up> (adjmap_inv dag) * \<up> (finite (dom D)) * \<up> (dom (lookup dag) = dom D) *
          Finite_Set.fold (\<lambda>i. (*) (is_dag_nh (the (lookup dag i)) (the (D i)))) emp (dom D) *
          graph_assn sG sGi * \<up> (dom D' \<subseteq> dom D \<and> (\<forall> x \<in> dom D'. D' x = D x))>
         change_dag_format_loop it sGi
         <\<lambda>r. is_dag D dagi * \<up> (adjmap_inv dag) * \<up> (finite (dom D)) * \<up> (dom (lookup dag) = dom D) *
               Finite_Set.fold (\<lambda>i. (*) (is_dag_nh (the (lookup dag i)) (the (D i)))) emp (dom D) *
              (\<exists>\<^sub>A xs. graph_assn (foldr (\<lambda> x G. update x (the (lookup dag x)) G) xs sG) r * \<up> (set xs = dom D'))>"
proof(induction arbitrary: D' it sGi sG rule: change_dag_format_loop.fixp_induct, goal_cases)
  case 1
  then show ?case 
    by simp
next
  case 2
  then show ?case 
    by simp
next
  case (3 f D' it sGi sG)
  show ?case 
    apply(rule ht_bind[where R = "\<lambda> r. is_dag_it D dagi D' it * \<up> (adjmap_inv dag) * \<up> (finite (dom D)) * \<up> (dom (lookup dag) = dom D) *
     Finite_Set.fold (\<lambda>i. (*) (is_dag_nh (the (lookup dag i)) (the (D i)))) emp (dom D) *
     graph_assn sG sGi * \<up> (r = (D' \<noteq> (\<lambda>x. None))) * \<up> (dom D' \<subseteq> dom D \<and> (\<forall> x \<in> dom D'. D' x = D x))"])
    subgoal
      by sep_auto
    subgoal for b
      apply (clarsimp split!: if_split )
      subgoal
        apply(rule ht_bind[where R = "\<lambda>((k, v), it').
        \<up> (adjmap_inv dag) * \<up> (finite (dom D)) * \<up> (dom (lookup dag) = dom D) *
     Finite_Set.fold (\<lambda>i. (*) (is_dag_nh (the (lookup dag i)) (the (D i)))) emp (dom D) *
     graph_assn sG sGi* is_dag_it D dagi (D' |` (- {k})) it' * \<up> (D' k = Some v)* \<up> (dom D' \<subseteq> dom D \<and> (\<forall> x \<in> dom D'. D' x = D x))"])
        subgoal
          by (sep_auto split: prod.split)
        subgoal for x
          apply(cases x)
          subgoal for a it
            apply(cases a)
            subgoal for v ex_nh
              apply (simp)
              apply(rule ht_cons_pre[where P' = "\<up> (adjmap_inv dag \<and> finite (dom D) \<and> dom (lookup dag) = dom D) *
     Finite_Set.fold (\<lambda>i. (*) (is_dag_nh (the (lookup dag i)) (the (D i)))) emp (dom D - {v}) *
     is_dag_nh (the (lookup dag v)) (the (D v)) *
     graph_assn sG sGi *
     is_dag_it D dagi (D' |` (- {v})) it *
     \<up> (D' v = Some ex_nh) *  \<up> (D v = Some ex_nh)  * \<up> (dom D' \<subseteq> dom D \<and> (\<forall> x \<in> dom D'. D' x = D x))"])
              subgoal
                apply sep_auto
                subgoal
                  apply(subst assn_over_finite_extract_one[of "dom D" v])
                  by sep_auto
                       apply sep_auto
                  apply force
                using mod_pure_star_dist apply auto[1]
                using mod_pure_star_dist by fastforce
              apply(rule ht_bind[where R = "\<lambda> r. \<up> (adjmap_inv dag \<and> finite (dom D) \<and> dom (lookup dag) = dom D) *
     Finite_Set.fold (\<lambda>i. (*) (is_dag_nh (the (lookup dag i)) (the (D i)))) emp (dom D - {v}) *
     is_dag_nh (the (lookup dag v)) (the (D v)) *
     graph_assn (update v (the (lookup dag v)) sG) r *
     is_dag_it D dagi (D' |` (- {v})) it *
     \<up> (D' v = Some ex_nh) *
     \<up> (D v = Some ex_nh) *
     \<up> (dom D' \<subseteq> dom D \<and> (\<forall>r\<in>dom D'. D' r = D r))"])
              subgoal
                using change_dag_format_body_rule[of sG sGi "the (lookup dag v)" ex_nh v]
                by sep_auto
              subgoal for sGi'
                apply(rule ht_cons_prec)
                  defer
                  defer
                apply(rule ht_frame[where R = "\<up> (D' v = Some ex_nh) *
     \<up> (D v = Some ex_nh) *
     \<up> (dom D' \<subseteq> dom D \<and> (\<forall>r\<in>dom D'. D' r = D r))"])
                  apply(rule 3[where D'="D' |` (- {v})" and sG = "update v (the (lookup dag v)) sG"])
                subgoal
                  apply sep_auto
                  subgoal
                    apply(subst assn_over_finite_extract_one[of "dom D" v])
                    by sep_auto
                  by (sep_auto simp: mod_pure_star_dist | force)+
                subgoal
                  apply simp
                  apply(rule ent_ex_preI)
                  subgoal for xs
                    apply(rule ent_ex_postI[of _ _ "xs@[v]"])
                    by sep_auto
                  done
                done
              done
            done
          done
        done
      subgoal
        apply(rule ht_exPI[where x = Nil])
        apply(rule ht_cons_post[where Q ="\<lambda> sGi. is_dag D dagi * \<up> (adjmap_inv dag) * \<up> (finite (dom D)) * \<up> (dom (lookup dag) = dom D) *
     Finite_Set.fold (\<lambda>i. (*) (is_dag_nh (the (lookup dag i)) (the (D i)))) emp (dom D) *
     graph_assn sG sGi *
     \<up> (D' = (\<lambda>x. None)) *
     \<up> (dom D' \<subseteq> dom D \<and> (\<forall>x\<in>dom D'. D' x = D x))"])
        subgoal
          apply(rule ht_frame)+
          apply(rule ht_cons_prec)
            defer
          defer
          apply(rule it_return_rule_frame[of D dagi D' it "\<up> (adjmap_inv dag) * \<up> (finite (dom D)) * \<up> (dom (lookup dag) = dom D) *
    Finite_Set.fold (\<lambda>i. (*) (is_dag_nh (the (lookup dag i)) (the (D i)))) emp (dom D) *
    graph_assn sG sGi"])
          subgoal
            by sep_auto
          subgoal
            by sep_auto
          done
        subgoal
          by sep_auto
        done
      done
    done
qed
 
lemma change_dag_format_rule:
  shows "<dag_assn dag dagi>
   change_dag_format dagi
  <\<lambda> r. dag_assn dag dagi * graph_assn dag r>"
  unfolding change_dag_format_def
  apply(rule ht_bind[where R = "\<lambda> r. dag_assn dag dagi * graph_assn \<emptyset>\<^sub>G r"])
  subgoal
    using graph_empty_rule by sep_auto
  subgoal for init
    unfolding dag_assn_def ex_assn_move_out(1)
    apply(rule ht_ex_pre_and_post_I)
    subgoal for D
      apply(rule ht_bind[where R = "\<lambda> r. is_dag_it D dagi D r* \<up> (adjmap_inv dag) * \<up> (finite (dom D)) * \<up> (dom (lookup dag) = dom D) *
     Finite_Set.fold (\<lambda>i. (*) (is_dag_nh (the (lookup dag i)) (the (D i)))) emp (dom D) * graph_assn \<emptyset>\<^sub>G init"])
      subgoal
        by sep_auto
      subgoal for it
        apply(rule ht_cons_prec)
        defer
        defer
          apply(rule change_dag_format_loop_induction[of D dagi D it dag empty init])
        subgoal
          by sep_auto
        subgoal for Res
          apply simp
          apply(rule ent_ex_preI)
          subgoal for xs
            apply(subst graph_assn_invar_extract)
            apply sep_auto
            subgoal 
              apply(subst graph_assn_abstract_cong[of _ dag])
              subgoal for x
                apply(cases "lookup dag x")
                by (auto simp add: Graph.update_by_foldr Graph.adjmap.invar_empty Graph.adjmap.map_empty)
             by sep_auto
           by sep_auto
         done
       done
     done
   done
  done

end

end 