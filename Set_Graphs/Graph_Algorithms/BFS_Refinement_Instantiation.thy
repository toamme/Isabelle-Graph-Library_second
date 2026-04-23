theory BFS_Refinement_Instantiation
  imports BFS_Refinement "HOL-Imperative_HOL.Array"
begin

definition "list_union xs ys = fold (\<lambda> y ys. if y \<in> set ys then ys else y#ys) ys xs"

fun list_union' where
 "list_union' xs Nil = xs" |
 "list_union' xs (y#ys) = (if y \<in> set ys then list_union' xs ys else y#list_union' xs ys)"

lemma list_union'_is:
  "list_union' xs ys = remdups ys @ xs"
  by(induction ys) auto

lemma list_union_set_rev:"set (list_union xs (rev ys)) = set xs \<union> set ys"
  unfolding list_union_def
  unfolding foldr_conv_fold[symmetric]
  by(induction ys) auto

lemma list_union_set:"set (list_union xs ys) = set xs \<union> set ys"
  using list_union_set_rev[of xs "rev ys"] by simp

lemma list_union_distinct_rev:"\<lbrakk>distinct xs; distinct ys\<rbrakk> \<Longrightarrow> distinct (list_union xs (rev ys))"
  unfolding list_union_def
  unfolding foldr_conv_fold[symmetric]
  by(induction ys) auto

lemma list_union_distinct:"\<lbrakk>distinct xs; distinct ys\<rbrakk> \<Longrightarrow> distinct (list_union xs ys)"
  using list_union_distinct_rev[of xs "rev ys"] by simp

definition "is_front xs xsi = \<up> (xs = xsi)"

definition "imp_cf_is_empty xs = return (xs = Nil)"

lemma imp_cf_is_empty_rule:
  "<is_front S Si> imp_cf_is_empty Si <\<lambda>b. is_front S Si * \<up> (b = (S = []))>"
  by(sep_auto simp: imp_cf_is_empty_def is_front_def)

locale guarded_list =
imp_set_ins +
imp_set_memb +
imp_set_empty
begin

fun guarded_list_assn where 
"guarded_list_assn xs (S, xsi) = 
  is_set (set xs) S * \<up> (xs = xsi) * \<up> (distinct xsi)"

definition "guarded_list_empty = do {i \<leftarrow> empty; return (i, Nil)}"

lemma guarded_list_empty_rule:
  "<emp> guarded_list_empty <guarded_list_assn Nil>"
  by(sep_auto simp: guarded_list_empty_def)

fun add_one_to_guarded_list where
 "add_one_to_guarded_list x (S, xsi) =
   do{b \<leftarrow> memb x S;
      if b then return (S, xsi)
      else do{
         S' \<leftarrow> ins x S;
         return (S', x#xsi)}}"

lemma add_one_to_guarded_list_rule:
 "<guarded_list_assn xs S>
   add_one_to_guarded_list x S
 <\<lambda> S. guarded_list_assn (if x \<in> set xs then xs else x#xs) S>"
  by(cases S) sep_auto

definition "add_all_to_guarded_list S xs = 
  foldM add_one_to_guarded_list xs S"

lemma add_all_to_guarded_list_rule:
  "<guarded_list_assn xs S>
   add_all_to_guarded_list S ys
 <\<lambda> S. guarded_list_assn (list_union xs ys) S>"
  unfolding add_all_to_guarded_list_def list_union_def
  apply(rule foldM_refine[where fi = add_one_to_guarded_list and xs = ys and si = S
            and f = "\<lambda>y ys. if y \<in> set ys then ys else y # ys" 
             and I = "\<lambda> _ _. guarded_list_assn"])
  using add_one_to_guarded_list_rule
  by sep_auto

fun to_ordinary_list where
 "to_ordinary_list (S, xs) = return xs"

lemma to_ordinary_list_rule:
  "<guarded_list_assn xs S>
    to_ordinary_list S
   <\<lambda> r. guarded_list_assn xs S * \<up>(r = xs)>"
  by(cases S) sep_auto

definition to_guarded_list where
 "to_guarded_list xs =
  do {i \<leftarrow> empty;
      S \<leftarrow> foldM ins xs i;
      return (S, xs)}"

lemma foldM_ins: "<is_set S Si>foldM ins xs Si <is_set (S \<union> set xs)>"
proof-
  have  "<is_set S Si>foldM ins xs Si <is_set (fold Set.insert xs S)>"
    using foldM_refine[of "\<lambda> a b. is_set" xs ins Set.insert S Si]
    by sep_auto
  moreover have "fold Set.insert xs S =  S \<union> set xs"
    using union_set_fold[of xs] by auto
  ultimately show ?thesis
    by simp
qed

lemma to_guarded_list_rule:
 "<\<up> (distinct xs)> to_guarded_list xs <\<lambda> r. guarded_list_assn xs r>"
  unfolding to_guarded_list_def
  using foldM_ins
  by sep_auto

end

locale list_set_diff = imp_set_memb
begin

fun list_cleared_of_set where
  "list_cleared_of_set Nil S = return Nil" |
  "list_cleared_of_set (x#xs) S =
    do {b \<leftarrow> memb x S;
        if b 
        then list_cleared_of_set xs S
        else do {rest \<leftarrow> list_cleared_of_set xs S;
                 return (x#rest)}}"

lemma list_cleared_of_set_rule:
  "<is_set S Si * \<up> (distinct xs)> list_cleared_of_set xs Si 
   <\<lambda> r. is_set S Si * \<up> (distinct r) * \<up> (r = filter (\<lambda> x. x \<notin> S) xs)>"
  by(induction xs) sep_auto

end

locale add_list_to_a_set = imp_set_ins
begin

definition "add_list_to_set xs S= foldM ins xs S"

end


(*
setup Locale_Code.open_block 
interpretation hash_guarded_list: guarded_list is_hashset hs_ins hs_memb hs_new
  by unfold_locales
setup Locale_Code.close_block 
*)

locale list_array_map_based_bfs = 
imp_set_ins is_set1 ins1 +
imp_set_memb is_set1 memb1+
imp_set_empty is_set1 empty1 +
imp_set_memb is_set2 memb2 +
imp_set_ins is_set2 ins2 +
imp_set_empty is_set2 empty2 +
imp_set_memb is_set3 memb3 +
imp_set_ins is_set3 ins3 +
imp_set_empty is_set3 empty3 +
imp_map_lookup is_map lookup_imp +
imp_map_lookup is_dag lookup_dag_imp +
imp_map_update is_dag update_dag_imp +
imp_map_empty is_dag dag_empty 
for is_set1:: "'v set \<Rightarrow> 'nset \<Rightarrow> assn" and ins1 memb1 empty1 
and is_set2 :: "'v set \<Rightarrow> 'vis \<Rightarrow> assn" and memb2
and is_set3 :: "'v set \<Rightarrow> 'dag_nh_set \<Rightarrow> assn" and memb3 and ins3 and empty3
and is_map::"('v \<Rightarrow> 'v list option) \<Rightarrow> 'g_array \<Rightarrow> assn" and  lookup_imp
and is_dag :: "('v \<Rightarrow> ('dag_nh_set \<times> 'v list) option) \<Rightarrow> 'a \<Rightarrow> assn"
and lookup_dag_imp update_dag_imp dag_empty empty2 ins2
begin

interpretation guarded_list is_set1 ins1 memb1 empty1
  by unfold_locales

abbreviation "gl_empty \<equiv> guarded_list_empty"
abbreviation "gl_assn \<equiv> guarded_list_assn"

definition "nh_emp = return Nil"
definition "is_neighb xs xsi = \<up> (xs = xsi) * \<up> (distinct xs)"

definition "is_neighb_nv xs xsi = \<up> (xs = xsi) * \<up> (distinct xs)"
definition "is_neighb_nv_emp xsi = return (xsi = Nil)"

interpretation list_set_diff is_set2 memb2
  by unfold_locales

definition "is_vis xs S = is_set2 (set xs) S"

definition "vis_empty = empty2"

lemma vis_empty_rule: "<emp> vis_empty <is_vis []>"
  by(sep_auto simp: is_vis_def vis_empty_def)

definition "imp_src_to_cf xs = return xs"

definition "imp_src_assn S Si = \<up> (S = Si)"

lemma imp_src_to_cf_rule:  
  "<imp_src_assn S Si> imp_src_to_cf Si <\<lambda>r. imp_src_assn S Si * is_front S r>"
  by(sep_auto simp: imp_src_assn_def imp_src_to_cf_def is_front_def)

find_theorems "_::'vis"

definition "set_cf_visited imp_vis imp_cf = foldM ins2 imp_cf imp_vis"

lemma set_cf_visited_rule:
   "<is_vis vis imp_vis * is_front cf imp_cf> set_cf_visited imp_vis imp_cf
    <\<lambda>r. is_vis (list_union vis cf) r * is_front cf imp_cf>"
  unfolding set_cf_visited_def list_union_def
  apply(rule ht_cons_prec[rotated, rotated])
  apply(rule foldM_refine[where fi = ins2 and xs = imp_cf and si = imp_vis 
         and f = "\<lambda>y ys. if y \<in> set ys then ys else y # ys" and s = vis
      and I = "\<lambda> _ _ vis imp_vis. is_vis vis imp_vis * is_front cf imp_cf"])
  subgoal for xs\<^sub>1 x xs\<^sub>2 s si
    by(sep_auto simp: is_vis_def is_front_def insert_absorb)
  subgoal
    by sep_auto
  subgoal for x
    by (sep_auto simp: is_front_def)
  done

interpretation dag_nh: guarded_list is_set3 ins3 memb3 empty3
  by unfold_locales

interpretation subprocedures: BFS_subprocedures_Imperative
  where empty = "\<lambda> x. None"
  and delete = "\<lambda> x M y. if y = x then None else M y"
  and update =  "\<lambda> x y M. M (x\<mapsto> y)"
  and adjmap_inv = "\<lambda> x. True"
  and lookup = "\<lambda> M x. M x"
  and G = G
  and vset_empty = Nil
  and vset_delete = "\<lambda> x xs. filter (\<lambda> y. y\<noteq> x) xs"
  and vset_inv = distinct
  and union = list_union
  and inter = "\<lambda> xs ys. filter (\<lambda> y. y \<in> set xs) ys"
  and insert = "\<lambda> x xs. if x \<in> set xs then xs else x#xs"
  and diff = "\<lambda> xs ys. filter (\<lambda> y. y \<notin> set ys) xs"
  and fold_vset = fold
  and fold_adjmap = fold
  and isin = "\<lambda> xs x. x \<in> set xs"
  and t_set = set
  and sel = hd
  and dag_fold_imp = foldM
  and is_front = is_front
  and frontier_fold_imp = foldM
  and is_wfront = gl_assn
  and wf_empty = gl_empty
  and nh_emp = nh_emp
  and is_neighb = is_neighb
  and is_neighb_nv = is_neighb_nv
  and is_neighb_nv_emp= is_neighb_nv_emp
  and unvisited_neighbs=list_cleared_of_set
  and is_vis = is_vis
  and add_to_working_frontier = add_all_to_guarded_list
  and to_ordinary_frontier = to_ordinary_list
  and add_to_dag_nh = dag_nh.add_all_to_guarded_list
  and is_dag_nh = dag_nh.guarded_list_assn
  and to_dag_nh = dag_nh.to_guarded_list
  and lookup_imp = lookup_imp
  and is_map = is_map
  and is_dag = is_dag
  and lookup_dag_imp = lookup_dag_imp
  and update_dag_imp = update_dag_imp
  and dag_empty = dag_empty
for G :: "'v \<Rightarrow> 'v list option"
proof(rule BFS_subprocedures_Imperative.intro, goal_cases)
  case 1
  then show ?case 
    by(auto intro!: BFS_subprocedures.intro Pair_Graph_Sepcs_Set2.intro
                    Pair_Graph_Specs.intro Map.intro  Set_Choose.intro Set.intro
                    Set_Choose_axioms.intro Set2.intro 
                    Set2_axioms.intro BFS_subprocedures_axioms.intro exI[of _ "rev _"] 
          simp add: foldr_conv_fold if_split[of "\<lambda> x. _ \<in> set x"] list_union_set list_union_distinct) 
next
  case 2
  then show ?case
    by unfold_locales
next
  case 3
  then show ?case 
   by unfold_locales
next
  case 4
  then show ?case 
   by unfold_locales
next
  case 5
  then show ?case 
    by unfold_locales
next
  case 6
  thus ?case
  proof(rule BFS_subprocedures_Imperative_axioms.intro, goal_cases)
    case 1
    then show ?case 
      by(sep_auto simp: nh_emp_def is_neighb_def)
  next
    case 2
    then show ?case
      using guarded_list_empty_rule by simp
  next
    case (3 nnh nnhi)
    then show ?case 
      by(sep_auto simp: is_neighb_nv_def is_neighb_nv_emp_def)
  next
    case (4 nnh nnhi)
    then show ?case 
      by(simp add: is_neighb_nv_def)
  next
    case (5 nd ndi vis visi)
    then show ?case
      using list_cleared_of_set_rule[of "set vis" visi nd]
      by(sep_auto simp: is_neighb_nv_def is_vis_def is_neighb_def)
  next
    case (6 f fi nh nhi)
    then show ?case 
      using add_all_to_guarded_list_rule[of f fi nhi]
      by(sep_auto simp: is_neighb_nv_def)
  next
    case (7 front fronti init initi F fi f)
    have "<F * is_front front fronti * gl_assn init initi> foldM fi fronti initi
  <\<lambda>si. F * is_front front fronti * gl_assn (fold f fronti init) si>"
      apply(rule foldM_refine[where fi = fi and f = f and xs = fronti and si = initi and s = init
            and I = "\<lambda> a b x xi.  F * is_front front fronti * gl_assn x xi"])
      subgoal for xs\<^sub>1 x xs\<^sub>2 s si
        using 7[of s si x] by sep_auto
      done
    thus ?case
      by(sep_auto simp: is_front_def)
  next
    case (8 f wfi)
    then show ?case 
      using to_ordinary_list_rule
      by(sep_auto simp: is_front_def)
  next
    case (9 dag_nh dag_nhi nnh nnhi)
    then show ?case
      using dag_nh.add_all_to_guarded_list_rule
      by(cases dag_nhi)(sep_auto simp: is_neighb_nv_def)
  next
    case (10 nh nhi)
    then show ?case
      using dag_nh.to_guarded_list_rule
      by(sep_auto simp: is_neighb_nv_def)
  next
    case (11 front fronti init initi dag_assn F fi f)
    have "<F * is_front front fronti * dag_assn init initi> foldM fi front initi
      <\<lambda>si. F * is_front front fronti * dag_assn (fold f front init) si>"
      apply(rule foldM_refine[where fi= fi and xs = front and si = initi and f= f and s = init
             and I = "\<lambda> a b dag dagi. F * is_front front fronti * dag_assn dag dagi"])
      subgoal for xs\<^sub>1 x xs\<^sub>2 s si
        using 11[of s si x] by sep_auto
      done
    thus ?case
      by(sep_auto simp: is_front_def)
  qed
qed

interpretation bfs_imp: BFS_Imperative
  where  empty = "\<lambda> x. None"
  and delete = "\<lambda> x M y. if y = x then None else M y"
  and update =  "\<lambda> x y M. M (x\<mapsto> y)"
  and adjmap_inv = "\<lambda> x. True"
  and lookup = "\<lambda> M x. M x"
  and G = G
  and vset_empty = Nil
  and vset_delete = "\<lambda> x xs. filter (\<lambda> y. y\<noteq> x) xs"
  and vset_inv = distinct
  and union = list_union
  and inter = "\<lambda> xs ys. filter (\<lambda> y. y \<in> set xs) ys"
  and insert = "\<lambda> x xs. if x \<in> set xs then xs else x#xs"
  and diff = "\<lambda> xs ys. filter (\<lambda> y. y \<notin> set ys) xs"
  and isin = "\<lambda> xs x. x \<in> set xs"
  and t_set = set
  and sel = hd
  and next_frontier = "subprocedures.next_frontier G"
  and imp_dag_empty = dag_empty
  and expand_tree = "subprocedures.expand_tree G"
  and graph_assn = subprocedures.graph_assn
  and imp_vis_empty = vis_empty
  and set_cf_visited = set_cf_visited
  and imp_expand_tree = "subprocedures.expand_tree_imp Gi"
  and imp_next_frontier = "subprocedures.next_frontier_imperative Gi"
  and imp_cf_is_empty = imp_cf_is_empty
  and imp_dag_assn = subprocedures.dag_assn
  and imp_vis_assn = is_vis
  and imp_cf_assn = is_front
  and imp_src_to_cf = imp_src_to_cf
  and imp_src_assn = imp_src_assn 
  and G_imp = Gi
  and srcs = srcs
for Gi G srcs
proof(rule BFS_Imperative.intro, goal_cases)
  case 1
  then show ?case 
    by(intro BFS.intro subprocedures.Graph.Pair_Graph_Specs_axioms
             subprocedures.set_ops.Set2_axioms BFS_axioms.intro 
             subprocedures.expand_tree subprocedures.next_frontier 
      | assumption)+
next
  case 2
  then show ?case 
  proof(rule BFS_Imperative_axioms.intro, goal_cases)
    case 1
    then show ?case 
      using subprocedures.dag_empty_rule by simp
  next
    case 2
    then show ?case
      using vis_empty_rule by simp
  next
    case (3 S Si)
    then show ?case 
      using imp_cf_is_empty_rule by auto
  next
    case (4 S Si)
    then show ?case 
      using imp_src_to_cf_rule[of S Si] by auto
  next
    case (5 vis imp_vis cf imp_cf)
    then show ?case
      using set_cf_visited_rule by simp
  next
    case (6 dag imp_dag cf imp_cf vis imp_vis)
    then show ?case 
      using subprocedures.expand_tree_rule[of G Gi cf imp_cf vis imp_vis dag imp_dag] 
      by sep_auto
  next
    case (7 cf imp_cf vis imp_vis)
    then show ?case 
      using subprocedures.next_frontier_imperative_rule[of G Gi cf imp_cf vis imp_vis]
      by sep_auto
  qed
qed

lemmas BFS_refine = bfs_imp.BFS_refine
lemmas graph_assn_def = subprocedures.graph_assn_def
abbreviation "state_assn \<equiv> bfs_imp.state_assn"

abbreviation "BFS_imp \<equiv> bfs_imp.BFS_imp"
abbreviation "BFS_fun \<equiv> bfs_imp.BFS_impl"

find_theorems  BFS.BFS_impl

find_theorems subprocedures.expand_tree
find_theorems BFS_subprocedures.expand_tree


lemma "BFS_fun = 
  (\<lambda> G. BFS.BFS_impl Nil list_union (subprocedures.expand_tree G)
                  (subprocedures.next_frontier G))"
  by simp

term is_set1
term is_set2
term is_set3
term empty2
term ins2
term lookup_imp
end
(*
definition "ias_is_empty S = do {s \<leftarrow> Array.len S;
                                 return (s = 0)}"


interpretation imp_set_is_empty is_ias ias_is_empty
  apply unfold_locales
  apply(sep_auto simp: is_ias_def ias_of_list_def ias_is_empty_def)
 *)

setup Locale_Code.open_block 
interpretation hash_guarded_list: guarded_list is_hashset hs_ins hs_memb hs_new
  by unfold_locales

interpretation visited_set_diff: list_set_diff is_ias ias_memb
  by unfold_locales

abbreviation "gl_empty \<equiv> hash_guarded_list.guarded_list_empty"
definition "nh_emp = return Nil"
definition "is_neighb_nv_emp xsi = return (xsi = Nil)"

definition "vis_empty = ias_new"

definition "imp_src_to_cf xs = return xs"

definition "set_cf_visited imp_vis imp_cf = foldM ias_ins imp_cf imp_vis"

interpretation subprocedures: BFS_subprocedures_Imperative_spec
  where dag_fold_imp = foldM
  and frontier_fold_imp = foldM
  and wf_empty = gl_empty
  and nh_emp = nh_emp
  and is_neighb_nv_emp= is_neighb_nv_emp
  and unvisited_neighbs= visited_set_diff.list_cleared_of_set
  and add_to_working_frontier = hash_guarded_list.add_all_to_guarded_list
  and to_ordinary_frontier = hash_guarded_list.to_ordinary_list
  and add_to_dag_nh = hash_guarded_list.add_all_to_guarded_list
  and to_dag_nh = hash_guarded_list.to_guarded_list
  and lookup_imp = iam_lookup
  and lookup_dag_imp = iam_lookup
  and update_dag_imp = iam_update
  done

interpretation top_loop: BFS_Imperative_spec
  where imp_dag_empty = iam_new
  and imp_vis_empty = vis_empty
  and set_cf_visited = set_cf_visited
  and imp_expand_tree = "subprocedures.expand_tree_imp Gi"
  and imp_next_frontier = "subprocedures.next_frontier_imperative Gi"
  and imp_cf_is_empty = imp_cf_is_empty
  and imp_src_to_cf = imp_src_to_cf for Gi
  done

interpretation iam_graph: Pair_Graph_Imperative  
    is_iam iam_new iam_lookup iam_update 
    by unfold_locales

setup Locale_Code.close_block

definition "BFS_imp = top_loop.BFS_imp"
definition "initial_state = top_loop.initial_state_imp"
definition "iam_graph_from_list = iam_graph.from_list_impl"

thm top_loop.initial_state_imp_def
thm top_loop.BFS_imp.simps
(*
export_code BFS_imp imp_src_to_cf iam_new vis_empty

in SML_imp module_name exported file_prefix BFS_imperative
*)
ML_val \<open>
val noi = @{code nat_of_integer}
val graph_from_list = @{code iam_graph_from_list} o map (apply2 noi)
val G = graph_from_list [(1,2), (2,3), (3,4), (3,5), (10,8), (11,12),
    (1,10), (1,11), (1,12), (4,13), (5,1)] ()
val initial_state = @{code initial_state} [noi 1] ()
val bfs = @{code BFS_imp}
val final_state = bfs G initial_state ()
\<close>

interpretation proofs: list_array_map_based_bfs
   (*aux set for frontier building*)
   is_hashset hs_ins hs_memb hs_new
   (*visited*)
   is_ias ias_memb
   (*aux set for building dag nh*)
   is_hashset hs_memb hs_ins hs_new
   (*map for actual graph*)
   is_iam iam_lookup
   (**map for dag*)
   is_iam iam_lookup iam_update iam_new 
   (*visited part 2*)
   ias_new ias_ins
  by unfold_locales

find_theorems proofs.BFS_imp
find_theorems top_loop.BFS_imp

abbreviation "bfs_graph_assn \<equiv> BFS_subprocedures_Imperative.graph_assn"
abbreviation "state_assn \<equiv> BFS_Imperative.state_assn"
abbreviation "bfs_loop \<equiv> BFS_Imperative_spec.BFS_imp"

thm proofs.BFS_refine
thm iam_graph.from_list_impl_rule

lemma "bfs_graph_assn (\<lambda>M. M) is_iam proofs.is_neighb = iam_graph.finite_graph_assn"
  apply(rule ext)+
  unfolding proofs.graph_assn_def
  unfolding iam_graph.finite_graph_assn_def
  unfolding iam_graph.graph_inv_def
  unfolding proofs.is_neighb_def
  subgoal for amap map
    apply(rule ent_iffI)

     apply sep_auto
    subgoal
      apply(rule ent_ex_preI)
      subgoal for A
        apply sep_auto
        subgoal
          apply(sep_auto simp: pure_assn_over_finite_set)
          apply(rule forw_subst[where P = "\<lambda> m. _ \<Longrightarrow>\<^sub>A is_iam m map" and b = A])
          subgoal
            apply(rule ext)
            subgoal for x 
              by(cases "amap x", all \<open>cases "A x"\<close>) force+
            done
          by simp
        done
      done
    subgoal for a b v vset
      apply (sep_auto simp: pure_assn_over_finite_set)
      by force
    subgoal
     by (sep_auto simp: pure_assn_over_finite_set)
    subgoal
      apply(rule ent_ex_postI[of _ _ amap])
      by (sep_auto simp: pure_assn_over_finite_set)
    done
  done

lemma BFS_imp_def': "BFS_imp = proofs.BFS_imp"
  unfolding BFS_imp_def is_neighb_nv_emp_def nh_emp_def proofs.is_neighb_nv_emp_def
      proofs.nh_emp_def proofs.set_cf_visited_def set_cf_visited_def
  by simp

lemma BFS_imp_rule:
"<bfs_graph_assn (\<lambda>M. M) is_iam proofs.is_neighb G Gi * proofs.state_assn s s_imp>
BFS_imp Gi s_imp
<\<lambda>s_imp'. bfs_graph_assn (\<lambda>M. M) is_iam proofs.is_neighb G Gi *
    proofs.state_assn (proofs.BFS_fun G s) s_imp'>"
  unfolding BFS_imp_def'
  using proofs.BFS_refine
  by simp

end