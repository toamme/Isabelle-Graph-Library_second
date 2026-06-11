theory BFS_Refinement_2
  imports BFS_3 BFS_Subprocedures  Directed_Set_Graphs.Pair_Graph_Imperative
"HOL-Imperative_HOL.Imperative_HOL" "HOL-Library.IArray" BFS_Refinement
begin

lemma "<a \<mapsto>\<^sub>a xs * a' \<mapsto>\<^sub>a xs' * \<up> (i < length xs \<and> j < length xs')>
       do {Array.upd i x a; Array.upd j x' a'}
      <\<lambda> r. a \<mapsto>\<^sub>a xs[i:=x] * r \<mapsto>\<^sub>a xs'[j:=x'] * \<up> (i < length xs \<and> j < length xs')>"
  by sep_auto

record ('imp_dist, 'imp_vis, 'imp_cf) BFS_state_imp =
     dists:: "'imp_dist" current:: "'imp_cf" visited:: "'imp_vis" current_dist::nat

locale BFS_Imperative_spec = 
fixes imp_src_to_cf::"'imp_src \<Rightarrow> 'imp_cf Heap"
and set_srcs_visited::"'imp_src \<Rightarrow> 'imp_vis Heap"
and next_frontier_and_current_imp::"'imp_cf \<Rightarrow> 'imp_vis \<Rightarrow> ('imp_cf \<times> 'imp_vis) Heap"
and imp_cf_is_empty::"'imp_cf \<Rightarrow> bool Heap"
and in_vis::"'ver \<Rightarrow> 'imp_vis \<Rightarrow> bool Heap"
and set_all_dists_in_front_imp::"'imp_dist \<Rightarrow> 'imp_cf \<Rightarrow> nat \<Rightarrow> 'imp_dist Heap"
begin

partial_function (heap) BFS_dist_imp::
  "('imp_dist, 'imp_vis, 'imp_cf) BFS_state_imp \<Rightarrow> ('imp_dist, 'imp_vis, 'imp_cf) BFS_state_imp Heap"
  where 
 "BFS_dist_imp state = 
   do { b \<leftarrow> imp_cf_is_empty (current state);
       if b then Heap_Monad.return state
       else do{ (current', visited') \<leftarrow>  next_frontier_and_current_imp (current state)  (visited state);
               let d = current_dist state;
               dist' \<leftarrow> set_all_dists_in_front_imp (dists state) current' (Suc d);
               BFS_dist_imp (state \<lparr>dists:= dist', visited := visited', current := current',
                                 current_dist := Suc d\<rparr>)}}"

definition "initial_state_imp src_imp imp_some_dist=  
  do {cf \<leftarrow> imp_src_to_cf src_imp;
      dists \<leftarrow> set_all_dists_in_front_imp  imp_some_dist cf 0;
      v \<leftarrow> set_srcs_visited src_imp;
        return \<lparr>dists = dists, current = cf, visited = v, current_dist = 0\<rparr>}"

definition "check_reachable src_imp imp_some_dist t =
    do {init \<leftarrow> initial_state_imp src_imp imp_some_dist;
        final \<leftarrow> BFS_dist_imp init;
        in_vis t (visited final)}"
end

locale BFS_Imperative = 
 BFS_3.BFS_distance  where expand_tree = expand_tree and insert = insert and some_dist = some_dist+
 BFS_Imperative_spec where  imp_src_to_cf = imp_src_to_cf
  and in_vis = in_vis and set_all_dists_in_front_imp = set_all_dists_in_front_imp
 for  imp_src_to_cf :: "'imp_src \<Rightarrow> 'imp_cf Heap"
  and expand_tree::"'adjmap \<Rightarrow> 'vset \<Rightarrow> 'vset \<Rightarrow> 'adjmap"
  and insert :: "'ver \<Rightarrow> 'vset \<Rightarrow> 'vset" 
  and in_vis::"'ver \<Rightarrow> 'imp_vis \<Rightarrow> bool Heap"
  and some_dist::"'dist" and set_all_dists_in_front_imp::"'imp_dist \<Rightarrow> 'imp_cf \<Rightarrow> nat \<Rightarrow> 'imp_dist Heap"+
fixes  G_imp::"'imp_G"
 and graph_assn::"'adjmap \<Rightarrow> 'imp_G \<Rightarrow> assn"
 and imp_src_assn::"'vset \<Rightarrow> 'imp_src \<Rightarrow> assn"
 and imp_dag_assn::"'adjmap \<Rightarrow> 'imp_dag \<Rightarrow> assn"
 and imp_cf_assn::"'vset \<Rightarrow> 'imp_cf \<Rightarrow> assn"
 and imp_vis_assn::"'vset \<Rightarrow> 'imp_vis \<Rightarrow> assn"
 and imp_dist_assn::"'dist \<Rightarrow> 'imp_dist \<Rightarrow> assn"
assumes imp_sf_is_empty: "\<And> S Si. <imp_cf_assn S Si> imp_cf_is_empty Si 
                       <\<lambda> b. imp_cf_assn S Si * \<up>(b \<longleftrightarrow> S = \<emptyset>\<^sub>N)>"
 and imp_src_to_cf: "\<And> S Si. <imp_src_assn S Si> imp_src_to_cf Si 
                      <\<lambda> r. imp_src_assn S Si * imp_cf_assn S r>"
 and set_srcs_visited: 
  "\<And> S Si. 
    <imp_src_assn S Si> set_srcs_visited Si  <\<lambda> r. imp_vis_assn S r * imp_src_assn S Si>"
 and next_frontier_and_current_imp:  "\<And> cf imp_cf vis imp_vis.
    <imp_cf_assn cf imp_cf * imp_vis_assn vis imp_vis * graph_assn G G_imp>
    next_frontier_and_current_imp imp_cf imp_vis
    <\<lambda> (r1, r2). imp_cf_assn (fst (next_frontier_and_current cf vis)) r1 * 
                 imp_vis_assn (snd (next_frontier_and_current cf vis)) r2 * graph_assn G G_imp>"
and in_vis_rule: "\<And>vis visi s. <imp_vis_assn vis visi> in_vis s visi 
            <\<lambda> r. imp_vis_assn vis visi * \<up> (r \<longleftrightarrow> isin vis s)>"
and set_all_dists_in_front_imp:
    "\<And> d id. <imp_dist_assn d id * imp_cf_assn cf cfi> set_all_dists_in_front_imp id cfi n
            <\<lambda> r. imp_dist_assn (set_all_dists_in_set d cf n) r * imp_cf_assn cf cfi>"
begin

definition "state_assn (s::('dist, 'vset) BFS_dist_state)
    (imp_s::('imp_dist, 'imp_vis, 'imp_cf) BFS_state_imp) = 
  (imp_vis_assn (BFS_dist_state.visited s) (BFS_state_imp.visited imp_s) *
   imp_cf_assn (BFS_dist_state.current s) (BFS_state_imp.current imp_s)*
   imp_dist_assn (BFS_dist_state.dists s) (BFS_state_imp.dists imp_s) *
    \<up> (BFS_dist_state.current_dist s = BFS_state_imp.current_dist imp_s))"

lemma BFS_refine:
  "<graph_assn G G_imp * state_assn s s_imp >
  BFS_dist_imp s_imp 
  <\<lambda> s_imp'. graph_assn G G_imp * state_assn (BFS_dist_impl s) s_imp'>"
proof(induction arbitrary: s s_imp rule: BFS_dist_imp.fixp_induct, goal_cases)
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
     "\<lparr>BFS_dist_state.dists = dists, current = current, visited = visited, BFS_dist_state.current_dist = n\<rparr>"
     "\<lparr>BFS_state_imp.dists = imp_dists, current = imp_current, visited = imp_visited, BFS_state_imp.current_dist = n\<rparr>"
     for imp_dists imp_current imp_visited dists current visited n] 

  note IH[sep_heap_rules] = IH[unfolded state_assn_def, simplified, rule_format]

  show ?case
    apply(cases s, cases s_imp)
    subgoal for dists current visited current_dist imp_dists imp_current imp_visited imp_current_dist
      apply (rewrite in "<_> _ <\<hole>>" BFS_dist_impl.simps)
      using next_frontier_and_current_imp IH  imp_sf_is_empty set_all_dists_in_front_imp
      apply(auto split!: if_split prod.split simp add: state_assn_def Let_def mod_pure_star_dist)
      by sep_auto
    done
qed

lemma initial_refine:
 "<imp_src_assn srcs srcs_imp * imp_dist_assn some_dist imp_some_dist>
  initial_state_imp srcs_imp imp_some_dist
 <\<lambda> si. state_assn initial_dist_state si * imp_src_assn srcs srcs_imp>"
  apply(auto simp add: initial_dist_state_def state_assn_def initial_state_imp_def)
  using imp_src_to_cf set_all_dists_in_front_imp set_srcs_visited 
  by sep_auto

lemma BFS_program_behaviour:
  "<imp_src_assn srcs srcs_imp * imp_dist_assn some_dist imp_some_dist * graph_assn G G_imp>
   do { si \<leftarrow> initial_state_imp srcs_imp imp_some_dist;
        BFS_dist_imp si }
   < \<lambda> si'. state_assn (BFS_dist_impl initial_dist_state) si' * imp_src_assn srcs srcs_imp * graph_assn G G_imp>"
  using initial_refine BFS_refine 
  by sep_auto

lemma check_reachable_rule:
 "<imp_src_assn srcs srcs_imp * imp_dist_assn some_dist imp_some_dist * graph_assn G G_imp> 
   check_reachable srcs_imp imp_some_dist t
  <\<lambda> b. imp_src_assn srcs srcs_imp * graph_assn G G_imp *
      \<up> (b \<longleftrightarrow> isin (BFS_dist_state.visited (BFS_dist_impl initial_dist_state)) t)>" 
  unfolding check_reachable_def
  using initial_refine BFS_refine in_vis_rule
  by (sep_auto simp: state_assn_def)
end

locale BFS_subprocedures_lists =
  fixes G::"'a \<Rightarrow> 'a list option"
begin

sublocale BFS_subprocedures_3
  where empty = "\<lambda> x. None"
  and delete = "\<lambda> x M. \<lambda> y. if y = x then None else M y"
  and insert = Cons
  and isin = "\<lambda> xs x. x \<in> set xs"
  and t_set = set
  and sel = hd
  and  update = "\<lambda> x z M. \<lambda> y. if y = x then Some z else M y"
  and adjmap_inv = "\<lambda> _. True"
  and vset_empty = Nil
  and vset_delete = "\<lambda> x xs. filter (\<lambda> y. x \<noteq> y) xs"
  and vset_inv = "\<lambda> _. True"
  and union = append
  and inter = "\<lambda> xs ys. filter (\<lambda> y. y \<in> set ys) xs"
  and diff = "\<lambda> xs ys. filter (\<lambda> y. y \<notin> set ys) xs"
  and fold_vset = "\<lambda>  f xs a. foldl (\<lambda>x y. f y x) a xs"
  and fold_adjmap = "\<lambda>  f xs a. foldl (\<lambda>x y. f y x) a xs"
  and lookup = "\<lambda> M x. M x"
  and fold2_vset = "\<lambda>  f xs a. foldl (\<lambda>x y. f y x) a xs"
  and fast_insert = Cons
  and vset_inv2 = distinct
  apply unfold_locales
  by (auto intro: exI[of _ "rev _"] simp add: foldl_conv_foldr) 


thm next_frontier_and_curent_correct



end