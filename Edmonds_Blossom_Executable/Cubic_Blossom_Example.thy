theory Cubic_Blossom_Example
  imports Blossom_Executable.Quadratic_Blossom_Search_Preservation
    Blossom_Executable.Edmonds_Blossom_Example
    Blossom_Executable.Blossom_Forest
    Graph_Algorithms_Dev.RBT_Map_Extension
    Data_Structures.List_Cursor
    Data_Structures.Imp_Array_Ring_Queue
    Data_Structures.Imp_Array_Stack
begin

provenance ai

section "Functional data structures"

definition "quadratic_cursors_invar V C \<longleftrightarrow>
  (\<forall>v \<in> V. v < length C \<and> lc_invar (C ! v))"

definition "quadratic_cursor_move C v =
  (if lc_has (C ! v) then list_update C v (lc_move (C ! v)) else C)"

definition "quadratic_cursor_reset C v = list_update C v ((C ! v)\<lparr>lc_pos := 0\<rparr>)"

lemma quadratic_cursors:
  "indexed_iterable_set (quadratic_cursors_invar V)
    (\<lambda>C v. lc_abstract (C ! v)) (\<lambda>C v. lc_current (C ! v))
    (\<lambda>C v. lc_has (C ! v)) (\<lambda>C v. lc_iterated (C ! v))
    (\<lambda>C v. lc_remaining (C ! v)) quadratic_cursor_move quadratic_cursor_reset V"
  by unfold_locales
    (auto simp: quadratic_cursors_invar_def quadratic_cursor_move_def quadratic_cursor_reset_def
      nth_list_update lc_defs lc_remaining_ne not_le set_take_disj_set_drop_if_distinct
      take_Suc_conv_app_nth Cons_nth_drop_Suc[symmetric]
      set_append[of "take _ _" "drop _ _", symmetric] in_set_conv_nth nth_eq_iff_index_eq)

lemma quadratic_set_union:
  "\<lbrakk>blossom_set_invar nil S; blossom_set_invar nil T\<rbrakk> \<Longrightarrow>
    blossom_set_invar nil (vset_union S T) \<and>
    t_set (vset_union S T) = t_set S \<union> t_set T"
  by(auto simp: blossom_set_invar_def vset_inv_def RBT.invar_union RBT.set_union)

global_interpretation quadratic_forest: forest_contract_manipulation
  where K = "{..<nil}"
    and parent_invar = M.invar and parent_upd = blossom_map_update
    and parent_get = "blossom_map_get nil"
    and origin_invar = M.invar and origin_upd = blossom_map_update
    and origin_get = "blossom_map_get nil"
    and vset_invar = "blossom_set_invar nil" and vset_to_set = t_set
    and vset_empty = vset_empty and vset_insert = vset_insert
    and vset_delete = vset_delete and vset_isin = isin
    and vset_iterate = blossom_set_iterate and vset_iterate_parent = blossom_set_iterate
    and vset_union = vset_union
    and parent_empty = Leaf and origin_empty = Leaf and nil = nil
  for nil
  defines quadratic_forest_contract = quadratic_forest.contract_fork
    and quadratic_forest_contract_path = quadratic_forest.contract_path
  by(intro forest_contract_manipulation.intro forest_contract_manipulation_axioms.intro
      forest_contract_manipulation_spec.intro forest_rbt.forest_manipulation_spec_axioms
      forest_rbt.forest_manipulation_axioms)
    (auto intro: blossom_rbt_iterate dest: quadratic_set_union)

section "The ordered blossom hierarchy"

lemma quadratic_set_iterate:
  assumes "vset_inv (S :: (nat \<times> color) tree)"
  shows "\<exists>xs. t_set S = set xs \<and> distinct xs \<and>
    blossom_set_iterate f init S = foldl f init xs"
proof-
  have "blossom_set_invar (sentinel (Tree2.inorder S)) S"
    using assms vs_strict_sentinel[of "Tree2.inorder S"]
    by(auto simp: blossom_set_invar_def)
  thus ?thesis
    by(rule blossom_rbt_iterate)
qed


context laminar_tree
begin

interpretation ordered_family: laminar_family_spec
  "\<lambda>(tops, L). dom (lookup L)" "\<lambda>(tops, L). all_verts L"
  "\<lambda>(tops, L). collect_verts L" "\<lambda>(tops, L). max_ids L" blossom_forest_invar
  "\<lambda>(tops, L). {collect_verts L i |i. i \<in> dom (lookup L)}" compound
  using laminar_family_spec_statisfied_axioms
  unfolding laminar_family_spec_def
  by(fastforce dest: blossom_forest_invarD(1))

interpretation ordered_base: blossom_forest_spec
  where all_ids = "\<lambda>(tops, L). dom (lookup L)"
    and universe = "\<lambda>(tops, L). all_verts L"
    and collect_elems = "\<lambda>(tops, L). collect_verts L"
    and max_ids = "\<lambda>(tops, L). max_ids L"
    and blossom_forest_invar = blossom_forest_invar
    and laminar_abstract = "\<lambda>(tops, L). {collect_verts L i |i. i \<in> dom (lookup L)}"
    and compound = compound and blossom_edges = blossom_edges
proof(intro blossom_forest_spec.intro ordered_family.laminar_family_spec_axioms
    blossom_forest_spec_axioms.intro, goal_cases)
  case (1 H i)
  thus ?case
    by(cases H) (auto dest: branching_odd_collect_verts_odd)
next
  case (2 H)
  thus ?case
    using blossom_edges_props(1)
    by(cases H) auto
next
  case (3 H)
  thus ?case
    using blossom_edges_props(2)
    by(cases H) auto
next
  case (4 H i j)
  thus ?case
    by(cases H) (force intro!: blossom_edges_props(3)[of _ _ i j])
qed

interpretation ordered_merge: blossom_forest_merge_spec
  where all_ids = "\<lambda>(tops, L). dom (lookup L)"
    and universe = "\<lambda>(tops, L). all_verts L"
    and collect_elems = "\<lambda>(tops, L). collect_verts L"
    and max_ids = "\<lambda>(tops, L). max_ids L"
    and blossom_forest_invar = blossom_forest_invar
    and laminar_abstract = "\<lambda>(tops, L). {collect_verts L i |i. i \<in> dom (lookup L)}"
    and compound = compound and blossom_edges = blossom_edges and merge = merge
  using merge_props
  by(intro blossom_forest_merge_spec.intro ordered_base.blossom_forest_spec_axioms)
    (auto simp: blossom_forest_merge_spec_axioms_def split_paired_all all_verts_def)

lemma laminar_ordered_children:
  "Blossom_Forest_Ordered_axioms (\<lambda>(tops, L). dom (lookup L))
    (\<lambda>(tops, L). max_ids L) blossom_forest_invar merge
    (\<lambda>H b. case lookup (snd H) b of Some (subverts cs) \<Rightarrow> cs | _ \<Rightarrow> [])"
  by(auto simp: Blossom_Forest_Ordered_axioms_def split_paired_all
    ordered_base.blossom_forest_merge_precond_def ordered_family.laminar_merge_precond_def
    map.map_update split: if_splits)

lemmas laminar_blossom_merge_spec = ordered_merge.blossom_forest_merge_spec_axioms

end

lemma quadratic_laminar_tree:
  "laminar_tree Leaf RBT_Map.delete lookup M.invar isin vset_insert update
    (vset_empty :: (nat \<times> color) tree) vset_delete vset_inv t_set blossom_set_iterate"
  by(intro laminar_tree.intro laminar_tree_axioms.intro Map_axioms_as_needed
      set.Set_axioms[folded RBT_Set.empty_def])
    (drule quadratic_set_iterate, auto)
type_synonym quadratic_hierarchy =
  "(nat \<times> color) tree \<times> ((nat \<times> (nat, nat) contracted_laminar) \<times> color) tree"

definition "quadratic_hierarchy_merge (H :: quadratic_hierarchy) =
  laminar_tree.merge vset_insert update vset_delete H"
definition "quadratic_hierarchy_universe = (laminar_tree.all_verts lookup :: 
  ((nat \<times> (nat, nat) contracted_laminar) \<times> color) tree \<Rightarrow> nat set)"
definition "quadratic_hierarchy_members = (laminar_tree.collect_verts lookup :: 
  ((nat \<times> (nat, nat) contracted_laminar) \<times> color) tree \<Rightarrow> nat \<Rightarrow> nat set)"
definition "quadratic_hierarchy_tops = (laminar_tree.max_ids lookup :: 
  ((nat \<times> (nat, nat) contracted_laminar) \<times> color) tree \<Rightarrow> nat set)"
definition "quadratic_hierarchy_invar (H :: quadratic_hierarchy) =
  laminar_tree.blossom_forest_invar lookup M.invar vset_inv t_set H"
definition "quadratic_hierarchy_compound (H :: quadratic_hierarchy) = laminar_tree.compound lookup H"
definition "quadratic_hierarchy_edges (H :: quadratic_hierarchy) = laminar_tree.blossom_edges lookup H"
definition "quadratic_hierarchy_relation = (laminar_tree.laminar_forest_cons lookup :: 
  ((nat \<times> (nat, nat) contracted_laminar) \<times> color) tree \<Rightarrow> (nat \<times> nat) set)"
definition "quadratic_hierarchy_subids = (laminar_tree.ids_of_sub_laminars lookup :: 
  ((nat \<times> (nat, nat) contracted_laminar) \<times> color) tree \<Rightarrow> nat \<Rightarrow> nat set)"

lemmas quadratic_hierarchy_defs = quadratic_hierarchy_merge_def quadratic_hierarchy_universe_def
  quadratic_hierarchy_members_def quadratic_hierarchy_tops_def quadratic_hierarchy_invar_def
  quadratic_hierarchy_compound_def quadratic_hierarchy_edges_def quadratic_hierarchy_relation_def
  quadratic_hierarchy_subids_def

definition "quadratic_hierarchy_children H b =
  (case lookup (snd H) b of Some (subverts cs) \<Rightarrow> cs | _ \<Rightarrow> [])"

global_interpretation quadratic_hierarchy: Blossom_Forest_Ordered
  where all_ids = "\<lambda>H. dom (lookup (snd H))"
    and universe = "\<lambda>H. quadratic_hierarchy_universe (snd H)"
    and collect_elems = "\<lambda>H. quadratic_hierarchy_members (snd H)"
    and max_ids = "\<lambda>H. quadratic_hierarchy_tops (snd H)"
    and blossom_forest_invar = quadratic_hierarchy_invar
    and laminar_abstract = "\<lambda>H. {quadratic_hierarchy_members (snd H) i |i. i \<in> dom (lookup (snd H))}"
    and compound = quadratic_hierarchy_compound and blossom_edges = quadratic_hierarchy_edges
    and merge = quadratic_hierarchy_merge and children = quadratic_hierarchy_children
  unfolding quadratic_hierarchy_defs quadratic_hierarchy_children_def
  using laminar_tree.laminar_blossom_merge_spec[OF quadratic_laminar_tree]
    laminar_tree.laminar_ordered_children[OF quadratic_laminar_tree]
  by(intro Blossom_Forest_Ordered.intro) (simp_all add: case_prod_unfold)

section "Concrete initial workspaces"

definition quadratic_singletons :: "nat list \<Rightarrow> quadratic_hierarchy" where
  "quadratic_singletons vs =
  foldl (\<lambda>(S, L) v. (vset_insert v S, update v (elem_vert v) L)) (vset_empty, Leaf) vs"

lemma quadratic_singletons_fold:
  "\<lbrakk>vset_inv S; M.invar (L :: ((nat \<times> (nat, nat) contracted_laminar) \<times> color) tree)\<rbrakk>
    \<Longrightarrow>
    (let H = foldl (\<lambda>(S, L) v. (vset_insert v S, update v (elem_vert v) L)) (S, L) vs
     in vset_inv (fst H) \<and> M.invar (snd H) \<and>
       t_set (fst H) = set vs \<union> t_set S \<and>
       lookup (snd H) = (\<lambda>v. if v \<in> set vs then Some (elem_vert v) else lookup L v))"
  by(induction vs arbitrary: S L)
    (auto simp: M.map_update M.invar_update set.invar_insert set.set_insert fun_eq_iff)

lemma quadratic_singletons_props[simp]:
  "vset_inv (fst (quadratic_singletons vs))"
  "M.invar (snd (quadratic_singletons vs))"
  "t_set (fst (quadratic_singletons vs)) = set vs"
  "lookup (snd (quadratic_singletons vs)) v = (if v \<in> set vs then Some (elem_vert v) else None)"
  using quadratic_singletons_fold[OF set.invar_empty M.invar_empty[unfolded RBT_Set.empty_def], of vs]
  by(auto simp: quadratic_singletons_def set.invar_empty RBT_Set.empty_def M.map_empty[unfolded RBT_Set.empty_def]
    fun_eq_iff)

lemma quadratic_singletons_relation[simp]:
  "quadratic_hierarchy_relation (snd (quadratic_singletons vs)) = {}"
  unfolding quadratic_hierarchy_relation_def
  by(auto simp: laminar_tree.laminar_forest_cons_def[OF quadratic_laminar_tree] split: if_splits)

lemma quadratic_singletons_members[simp]:
  "quadratic_hierarchy_subids (snd (quadratic_singletons vs)) v =
    (if v \<in> set vs then {v} else {})"
  "quadratic_hierarchy_members (snd (quadratic_singletons vs)) v =
    (if v \<in> set vs then {v} else {})"
  by(simp_all add: quadratic_hierarchy_defs quadratic_singletons_relation[unfolded quadratic_hierarchy_defs]
    laminar_tree.ids_of_sub_laminars_simps[OF quadratic_laminar_tree] laminar_tree.collect_verts_simps[OF
    quadratic_laminar_tree])

lemma quadratic_singletons_observations[simp]:
  "dom (lookup (snd (quadratic_singletons vs))) = set vs"
  "quadratic_hierarchy_tops (snd (quadratic_singletons vs)) = set vs"
  "quadratic_hierarchy_universe (snd (quadratic_singletons vs)) = set vs"
  "quadratic_hierarchy_children (quadratic_singletons vs) v = []"
  by(auto simp: quadratic_hierarchy_defs quadratic_singletons_members[unfolded quadratic_hierarchy_defs] dom_def
    laminar_tree.max_ids_def[OF quadratic_laminar_tree] laminar_tree.all_verts_def[OF quadratic_laminar_tree]
    quadratic_hierarchy_children_def split: if_splits)

lemma quadratic_singletons_invar[simp]:
  "quadratic_hierarchy_invar (quadratic_singletons vs)"
proof-
  have "quadratic_hierarchy_invar
    (fst (quadratic_singletons vs), snd (quadratic_singletons vs))"
    using quadratic_singletons_props(1-3)[of vs]
    unfolding quadratic_hierarchy_invar_def
    by(intro laminar_tree.blossom_forest_invarI[OF quadratic_laminar_tree] laminar_tree.laminar_forest_invarI[OF
      quadratic_laminar_tree])
      (auto simp: quadratic_hierarchy_defs quadratic_singletons_members[unfolded quadratic_hierarchy_defs]
        quadratic_singletons_observations(2,3)[unfolded quadratic_hierarchy_defs]
        quadratic_singletons_relation[unfolded quadratic_hierarchy_defs]
        laminar_tree.disjoint_subids_def[OF quadratic_laminar_tree] laminar_tree.disjoint_trees_def[OF
          quadratic_laminar_tree]
        laminar_tree.elem_unique_id_def[OF quadratic_laminar_tree] laminar_tree.branching_properly_def[OF
          quadratic_laminar_tree]
        laminar_tree.domain_recursive_def[OF quadratic_laminar_tree] laminar_tree.distinct_children_def[OF
          quadratic_laminar_tree] laminar_tree.branching_odd_def[OF quadratic_laminar_tree]
        split: if_splits)
  thus ?thesis
    by simp
qed

definition "quadratic_nil vs = Suc (Suc (foldr max vs 0) + length vs div 2)"

definition "quadratic_fresh vs =
  ((\<lambda>i. Suc (foldr max vs 0) + i), 0, length vs div 2)"

definition "quadratic_cursors nil G =
  map (\<lambda>v. \<lparr>lc_list = neighbour_list_rbt G v, lc_pos = 0\<rparr>) [0..<nil]"

definition "quadratic_tasks vs =
  ars_empty (Suc (length vs + length vs div 2)) (Quadratic_Visit (quadratic_nil vs) 0 0)"


lemma quadratic_universe:
  "set vs \<subset> {..<quadratic_nil vs}"
  using vs_strict_sentinel[of vs]
  by(rule psubset_subset_trans) (auto simp: sentinel_def quadratic_nil_def)

lemma quadratic_fresh_abstract:
  "arq_abstract (length vs) (quadratic_fresh vs) =
    map (\<lambda>i. Suc (foldr max vs 0) + i) [0..<length vs div 2]"
  unfolding quadratic_fresh_def arq_abstract_def
  by(simp only: case_prod_beta; intro map_cong refl)
    (auto intro: less_le_trans[OF _ div_le_dividend])

lemma quadratic_fresh_props:
  "arq_invar (length vs) (quadratic_fresh vs)"
  "distinct (arq_abstract (length vs) (quadratic_fresh vs))"
  "set (arq_abstract (length vs) (quadratic_fresh vs)) \<subseteq> {..<quadratic_nil vs} - set vs"
  "length (arq_abstract (length vs) (quadratic_fresh vs)) = length vs div 2"
  unfolding quadratic_fresh_abstract
  using foldr_max_ge[of _ vs 0]
  by(auto simp: quadratic_fresh_def arq_invar_def
    quadratic_nil_def distinct_map inj_on_def dest!: foldr_max_ge[where a = 0])
section "The executable search"

context Quadratic_Blossom_Search_Lifting
begin

lemma run_correct_from_initial:
  fixes U L C H P B D N J fresh T out
  assumes "initial_axioms U L C H P B D N J fresh" "initial_recovery_axioms T out"
  shows "augmenting_path_result_spec (Quadratic_Blossom_Search_run U L C H P B D N J fresh T out)"
  using Quadratic_Blossom_Search_thms.Quadratic_Blossom_Search_run_correct[
    OF Quadratic_Blossom_Search_thms.intro[OF Quadratic_Blossom_Search_Lifting_axioms
      Quadratic_Blossom_Search_thms_axioms.intro[OF assms]]]
  .

end
lemma quadratic_matching_lookup:
  "matching_invar_abs_rbt nil G N \<Longrightarrow>
    ((if x < nil \<and> matching_partner_rbt nil N x \<noteq> nil
      then Some (matching_partner_rbt nil N x) else None) = Some y) \<longleftrightarrow>
    {x, y} \<in> matching_abs_rbt nil N"
  using gm.Mate.lookup_partner[of nil G N x y] gm.Mate.matching(1)[of nil G N]
    matching_rbt.matching.universe[of nil G N, folded matching_invar_abs_rbt_def]
  by(auto simp: matching_lookup_rbt_def matching_rbt.buddy_lookup_def matching_rbt.get_partner_def Vs_def
    split: if_splits)

lemma quadratic_function_map:
  "fixed_univ_map K (\<lambda>_. True) fun_upd (\<lambda>A x. A x)"
  by unfold_locales auto

lemma quadratic_search_instance:
  "Quadratic_Blossom_Search_Lifting {..<nil} (set vs) nil vset_insert isin t_set sel vset_empty vset_delete vset_inv
    (blossom_set_invar nil) t_set vset_empty vset_insert vset_delete isin evens odds roots (forest_get_path_rbt nil)
    (forest_abs_rbt nil) (forest_invar_rbt nil) forest_empty_rbt (forest_extend_rbt nil) (quadratic_forest_contract
    nil) Leaf (matching_invar_abs_rbt nil) (matching_partner_rbt nil) augment_rbt (matching_abs_rbt nil)
    (contract_path_rbt nil) (expand_path_rbt nil) add_alternatingly_rbt (\<lambda>H. dom (lookup (snd H)))
    (\<lambda>H. quadratic_hierarchy_tops (snd H)) (\<lambda>H. quadratic_hierarchy_universe (snd H)) (\<lambda>H.
    quadratic_hierarchy_members (snd H)) quadratic_hierarchy_invar (\<lambda>H. {quadratic_hierarchy_members (snd H)
    i |i. i \<in> dom (lookup (snd H))}) quadratic_hierarchy_compound quadratic_hierarchy_edges
    quadratic_hierarchy_children (length vs) (arq_invar (length vs)) (arq_abstract (length vs)) (arq_empty nil)
    (arq_push (length vs)) (arq_pop (length vs)) arq_is_empty (\<lambda>R. \<forall>x\<in>{..<nil}. R x \<in>
    {..<nil} \<and> R (R x) = R x) (\<lambda>R. R) (\<lambda>R x. (R x, R)) (\<lambda>R x y z. if R z = R x then R y
    else R z) (\<lambda>_. id) (\<lambda>_. True) fun_upd (\<lambda>A. A) (\<lambda>_. True) fun_upd
    (quadratic_cursors_invar (set vs)) (\<lambda>C v. lc_abstract (C ! v)) (\<lambda>C v. lc_iterated (C ! v))
    (\<lambda>C v. lc_remaining (C ! v)) (\<lambda>C v. lc_current (C ! v)) (\<lambda>C v. lc_has (C ! v))
    quadratic_cursor_move quadratic_cursor_reset (\<lambda>_. True) fun_upd (\<lambda>_. True) fun_upd (Suc (length
    vs + length vs div 2)) (length vs) (ars_invar (Suc (length vs + length vs div 2))) ars_abstract (ars_empty (Suc
    (length vs + length vs div 2)) (Quadratic_Visit nil nil nil)) ars_push ars_pop ars_top ars_is_empty (\<lambda>_.
    True) fun_upd (\<lambda>A. A) quadratic_hierarchy_merge (\<lambda>A. A) (\<lambda>A. A) (\<lambda>A. A)"
  by(intro Quadratic_Blossom_Search_Lifting.intro Quadratic_Blossom_Search.intro
      Blossom_Path_Recovery.intro Blossom_Routing.intro
      G.Pair_Graph_Specs_Read_Only_axioms[folded RBT_Set.empty_def] blossom_rbt_set
      forest_rbt.satisified[folded forest_get_path_rbt_def forest_abs_rbt_def forest_invar_rbt_def
        forest_extend_rbt_def forest_empty_rbt_def]
      quadratic_forest.spec_satisfied[folded forest_get_path_rbt_def forest_abs_rbt_def forest_invar_rbt_def
        quadratic_forest_contract_def]
      quadratic_hierarchy.Blossom_Forest_Ordered_axioms arq_bounded_queue function_union_find
      quadratic_function_map quadratic_cursors ars_bounded_stack)
    (unfold_locales; rule gm.Mate.matching gm.Mate.augment gm.Mate.contract gm.Mate.expand
      gm.Mate.add_alternatingly quadratic_matching_lookup[folded lessThan_iff]; assumption)

definition "quadratic_search_run vs N =
  Quadratic_Blossom_Search_Lifting.Quadratic_Blossom_Search_run (quadratic_nil vs) vset_empty vset_insert isin evens
    odds (forest_get_path_rbt (quadratic_nil vs)) forest_empty_rbt (forest_extend_rbt (quadratic_nil vs))
    (quadratic_forest_contract (quadratic_nil vs)) (matching_partner_rbt (quadratic_nil vs)) (contract_path_rbt
    (quadratic_nil vs)) quadratic_hierarchy_children (arq_empty (quadratic_nil vs)) (arq_push (length vs)) (arq_pop
    (length vs)) arq_is_empty (\<lambda>R x. (R x, R)) (\<lambda>R x y z. if R z = R x then R y else R z)
    (\<lambda>_. id) fun_upd (\<lambda>A. A) fun_upd (\<lambda>C v. lc_current (C ! v)) (\<lambda>C v. lc_has (C !
    v)) quadratic_cursor_move quadratic_cursor_reset fun_upd fun_upd vs N ars_push ars_pop ars_top ars_is_empty
    fun_upd quadratic_hierarchy_merge (\<lambda>A. A) (\<lambda>A. A) (\<lambda>A. A)"

definition quadratic_recovered_path ::
    "('a, 'b, 'c, nat => nat, 'e) Blossom_Path_Recovery_state_scheme => nat list" where
  "quadratic_recovered_path = Blossom_Path_Recovery.recovered_path (%A x. A x)"

definition "quadratic_path_result G vs N =
  quadratic_search_run vs N id (\<lambda>_. 0)
    (quadratic_cursors (quadratic_nil vs) G) (quadratic_singletons vs)
    (\<lambda>_. (0, 0)) (\<lambda>_. (0, 0)) (\<lambda>_. 0) (\<lambda>_. (0, 0)) (\<lambda>_. (0, 0))
    (quadratic_fresh vs) (quadratic_tasks vs) (\<lambda>_. 0)"

definition "quadratic_path G vs N =
  (let result = quadratic_path_result G vs N
   in if qbr_length result = 0 then None else Some (quadratic_recovered_path result))"

section "Correctness of the concrete search"

lemma quadratic_cursors_initial:
  assumes "graph_input_rbt nil G vs"
  shows "quadratic_cursors_invar (set vs) (quadratic_cursors nil G)"
    "u \<in> set vs \<Longrightarrow> lc_abstract (quadratic_cursors nil G ! u) = t_set (neighbourhood_rbt G u)"
  using gm.graph_inputD(7)[folded graph_input_rbt_def, OF assms]
    gm.Graph.neighbourhood_invars'[OF gm.graph_inputD(1)[folded graph_input_rbt_def, OF assms]]
  by(auto simp: quadratic_cursors_invar_def quadratic_cursors_def lc_defs gm.neighbour_list_def
      vset_inv_def subset_iff intro: bst_distinct_inorder)

lemmas quadratic_search_axioms =
  quadratic_search_instance[unfolded Quadratic_Blossom_Search_Lifting_def, THEN conjunct1]
lemmas quadratic_recovery_axioms =
  quadratic_search_instance[unfolded Quadratic_Blossom_Search_Lifting_def, THEN conjunct2]

lemmas quadratic_search_correct =
  Quadratic_Blossom_Search_Lifting.run_correct_from_initial[OF quadratic_search_instance[where nil="quadratic_nil vs"
    and vs=vs], where graph_lookup=lookup and graph_invar=adj_inv and vs=vs and G=G and ?M0.0=N,
    folded quadratic_search_run_def,
    unfolded Quadratic_Blossom_Search_Lifting.augmenting_path_result_spec_def[OF quadratic_search_instance]
      Quadratic_Blossom_Search.input_graph_def[OF quadratic_search_axioms],
    folded gm.ugraph_abs_def quadratic_recovered_path_def] for vs G N

lemma quadratic_path_result_correct:
  assumes "distinct vs" "graph_input_rbt (quadratic_nil vs) G vs"
    "matching_invar_rbt (quadratic_nil vs) G N"
  shows "if qbr_length (quadratic_path_result G vs N) = 0
    then \<not> (\<exists>p. graph_augmenting_path (ugraph_abs_rbt G) (matching_abs_rbt (quadratic_nil vs) N) p)
    else graph_augmenting_path (ugraph_abs_rbt G) (matching_abs_rbt (quadratic_nil vs) N)
      (quadratic_recovered_path (quadratic_path_result G vs N))"
  unfolding quadratic_path_result_def
  by(rule quadratic_search_correct;
    unfold Quadratic_Blossom_Search.initial_axioms_def[OF quadratic_search_axioms]
      Quadratic_Blossom_Search.input_axioms_def[OF quadratic_search_axioms]
      Quadratic_Blossom_Search.input_graph_def[OF quadratic_search_axioms]
      Quadratic_Blossom_Search_Lifting.initial_recovery_axioms_def[OF quadratic_search_instance];
    insert assms quadratic_fresh_props[of vs] quadratic_cursors_initial[of "quadratic_nil vs" G vs]
      quadratic_universe[of vs])
    (auto simp: gm.graph_input_def gm.matching_invar_def gm.ugraph_abs_def neighbourhood_rbt_def
        quadratic_tasks_def ars_invar_def ars_abstract_def ars_empty_def)

lemma quadratic_path_correct:
  assumes "distinct vs" "graph_input_rbt (quadratic_nil vs) G vs"
    "matching_invar_rbt (quadratic_nil vs) G N"
  shows "quadratic_path G vs N = Some p \<Longrightarrow>
      graph_augmenting_path (ugraph_abs_rbt G) (matching_abs_rbt (quadratic_nil vs) N) p"
    "(\<exists>p. graph_augmenting_path (ugraph_abs_rbt G) (matching_abs_rbt (quadratic_nil vs) N) p)
      \<Longrightarrow>
      quadratic_path G vs N \<noteq> None"
  using quadratic_path_result_correct[OF assms]
  by(auto simp: quadratic_path_def split: if_splits)


section "Maximum-cardinality matching"

global_interpretation quadratic_max: Find_Max_Matching
  where empty = map_empty and delete = RBT_Map.delete and lookup = lookup and insert = vset_insert
    and isin = isin and t_set = t_set and sel = sel and update = update and adjmap_inv = adj_inv
    and vset_empty = vset_empty and vset_delete = vset_delete and vset_inv = vset_inv
    and K = "{..<(quadratic_nil (remdups vs))}" and nil = "quadratic_nil (remdups vs)"
    and mate_empty = Leaf
    and matching_invar_abs = "matching_invar_abs_rbt (quadratic_nil (remdups vs))" and matching_abs =
      "matching_abs_rbt (quadratic_nil (remdups vs))"
    and mate_lookup = "matching_lookup_rbt (quadratic_nil (remdups vs))" and mate_partner = "matching_partner_rbt
      (quadratic_nil (remdups vs))"
    and mate_augment = augment_rbt and mate_contract = "contract_path_rbt (quadratic_nil (remdups vs))"
    and mate_expand = "expand_path_rbt (quadratic_nil (remdups vs))" and mate_add_alternatingly =
      add_alternatingly_rbt
    and vset_to_list = Tree2.inorder
    and G = G and vs = "remdups vs" and aug_path_search = "quadratic_path G (remdups vs)"
  for G vs
  defines quadratic_max_impl = quadratic_max.Find_Max_Matching_impl
    and quadratic_max_initial_state = quadratic_max.initial_state
    and quadratic_max_run = quadratic_max.Find_Max_Matching_run_impl
  by(intro Find_Max_Matching.intro gm.Graph_Matching_Specs_axioms Find_Max_Matching_axioms.intro;
      fold graph_input_rbt_def matching_invar_rbt_def ugraph_abs_rbt_def matching_abs_rbt_def)
    (rule quadratic_path_correct[OF distinct_remdups]; assumption)+

lemma cubic_blossom_correct:
  assumes "graph_input_rbt (quadratic_nil (remdups vs)) G vs"
  shows "max_card_matching (ugraph_abs_rbt G)
      (matching_abs_rbt (quadratic_nil (remdups vs)) (current_matching (quadratic_max_run G vs)))"
    "matching_invar_rbt (quadratic_nil (remdups vs)) G
      (current_matching (quadratic_max_run G vs))"
proof-
interpret quadratic_max_proofs: Find_Max_Matching_thms
  where empty = map_empty and delete = RBT_Map.delete and lookup = lookup and insert = vset_insert
    and isin = isin and t_set = t_set and sel = sel and update = update and adjmap_inv = adj_inv
    and vset_empty = vset_empty and vset_delete = vset_delete and vset_inv = vset_inv
    and K = "{..<(quadratic_nil (remdups vs))}" and nil = "quadratic_nil (remdups vs)"
    and mate_empty = Leaf
    and matching_invar_abs = "matching_invar_abs_rbt (quadratic_nil (remdups vs))" and matching_abs =
      "matching_abs_rbt (quadratic_nil (remdups vs))"
    and mate_lookup = "matching_lookup_rbt (quadratic_nil (remdups vs))" and mate_partner = "matching_partner_rbt
      (quadratic_nil (remdups vs))"
    and mate_augment = augment_rbt and mate_contract = "contract_path_rbt (quadratic_nil (remdups vs))"
    and mate_expand = "expand_path_rbt (quadratic_nil (remdups vs))" and mate_add_alternatingly =
      add_alternatingly_rbt
    and vset_to_list = Tree2.inorder
    and G = G and vs = "remdups vs" and aug_path_search = "quadratic_path G (remdups vs)"
    using assms quadratic_universe[of "remdups vs"]
    by(intro Find_Max_Matching_thms.intro quadratic_max.Find_Max_Matching_axioms
        Find_Max_Matching_thms_axioms.intro)
      (auto simp: quadratic_max.Find_Max_Matching_axiom_def graph_input_rbt_def gm.graph_input_def[unfolded
        graph_input_rbt_def])
  show "max_card_matching (ugraph_abs_rbt G)
      (matching_abs_rbt (quadratic_nil (remdups vs)) (current_matching (quadratic_max_run G vs)))"
        "matching_invar_rbt (quadratic_nil (remdups vs)) G
      (current_matching (quadratic_max_run G vs))"
    using quadratic_max_proofs.Find_Max_Matching_correct_1 quadratic_max_proofs.Find_Max_Matching_correct_2
    unfolding quadratic_max.Find_Max_Matching_run_impl_def
      quadratic_max_impl_def quadratic_max_initial_state_def
      graph_input_rbt_def matching_invar_rbt_def ugraph_abs_rbt_def matching_abs_rbt_def
    by(simp_all only: quadratic_max_proofs.Find_Max_Matching_impl_to_Find_Max_Matching)
qed

section "Code generation"

text "The concrete loop aliases keep the universe and capacities fixed across iterations.
  The result-path alias shares the completed search state with path recovery."

lemmas quadratic_hierarchy_merge_code[code] =
  laminar_tree.merge.simps[OF quadratic_laminar_tree, where 'v = nat,
    folded quadratic_hierarchy_merge_def[abs_def]]

lemmas quadratic_contract_code[code] =
  quadratic_forest.contract_path_def[unfolded quadratic_forest.vset_from_list_def
    forest_rbt.parent_lookup_def forest_rbt.origin_lookup_def]

definition "quadratic_search_loop_core nil cap =
  Quadratic_Blossom_Search.Quadratic_Blossom_Search_impl nil isin evens odds
    (forest_get_path_rbt nil) (forest_extend_rbt nil) (quadratic_forest_contract nil)
    (matching_partner_rbt nil) (contract_path_rbt nil) quadratic_hierarchy_merge
    (arq_push cap) (arq_pop cap) arq_is_empty
    (\<lambda>R x. (R x, R)) (\<lambda>R x y z. if R z = R x then R y else R z)
    fun_upd (\<lambda>A. A) fun_upd (\<lambda>A. A)
    (\<lambda>C v. lc_current (C ! v)) (\<lambda>C v. lc_has (C ! v))
    quadratic_cursor_move fun_upd (\<lambda>A. A) fun_upd"

definition "quadratic_initial_state nil cap vs m0 (u0 :: nat \<Rightarrow> nat) l0
    (c0 :: nat list_cursor list) (h0 :: quadratic_hierarchy)
    (p0 :: nat \<Rightarrow> nat \<times> nat) b0 d0 (n0 :: nat \<Rightarrow> nat \<times> nat) j0 fresh0 =
  Quadratic_Blossom_Search.initial_state nil vset_empty vset_insert forest_empty_rbt
    (matching_partner_rbt nil) (arq_empty nil) (arq_push cap) (\<lambda>_. id)
    fun_upd quadratic_cursor_reset fun_upd vs m0 u0 l0 c0 h0 p0 b0 d0 n0 j0 fresh0"

definition "quadratic_cache_loop (N :: nat \<Rightarrow> nat \<times> nat) =
  Blossom_Path_Recovery.Cache_Route_impl fun_upd (\<lambda>A. A) N"

definition "quadratic_recovery_loop nil (H :: quadratic_hierarchy) =
  Blossom_Path_Recovery.Blossom_Path_Recovery_impl nil
    ars_push ars_pop ars_top ars_is_empty (\<lambda>A. A) fun_upd (\<lambda>A. A) fun_upd
    quadratic_hierarchy_children (\<lambda>A. A) H"

definition "quadratic_result_path_exec (nil :: nat) =
  Quadratic_Blossom_Search_Lifting.result_path nil
    (quadratic_hierarchy_children :: quadratic_hierarchy \<Rightarrow> nat \<Rightarrow> nat list)
    fun_upd ars_push ars_pop ars_top ars_is_empty fun_upd (\<lambda>A. A) (\<lambda>A. A) (\<lambda>A. A)"

lemmas quadratic_search_capacity_axioms =
  quadratic_search_axioms[where vs="replicate cap 0", simplified length_replicate] for cap

lemmas quadratic_search_defs =
  Quadratic_Blossom_Search.search_step_def[OF quadratic_search_capacity_axioms]
  Quadratic_Blossom_Search.start_scan_def[OF quadratic_search_capacity_axioms]
  Quadratic_Blossom_Search.resolve_target_def[OF quadratic_search_capacity_axioms]
  Quadratic_Blossom_Search.extend_search_def[OF quadratic_search_capacity_axioms]
  Quadratic_Blossom_Search.finish_search_def[OF quadratic_search_capacity_axioms]
  Quadratic_Blossom_Search.contract_search_def[OF quadratic_search_capacity_axioms]
  Quadratic_Blossom_Search.process_cycle_def[OF quadratic_search_capacity_axioms]
  Quadratic_Blossom_Search.enqueue_vertex_def[OF quadratic_search_capacity_axioms]
  Quadratic_Blossom_Search.rootward_edges_def[OF quadratic_search_capacity_axioms]
  Quadratic_Blossom_Search.outward_edges_def[OF quadratic_search_capacity_axioms]
  Quadratic_Blossom_Search.initial_state_def[OF quadratic_search_capacity_axioms]
  Quadratic_Blossom_Search.initial_frontier_def[OF quadratic_search_capacity_axioms]

lemmas quadratic_recovery_defs =
  Blossom_Path_Recovery.Blossom_Path_Recovery_call_1_conds_def[OF quadratic_recovery_axioms]
  Blossom_Path_Recovery.Blossom_Path_Recovery_upd1_def[OF quadratic_recovery_axioms]
  Blossom_Path_Recovery.Blossom_Path_Recovery_ret1_def[OF quadratic_recovery_axioms]
  Blossom_Path_Recovery.recovery_done_def[OF quadratic_recovery_axioms]
  Blossom_Path_Recovery.recovery_step_def[OF quadratic_recovery_axioms]
  Blossom_Path_Recovery.visit_step_def[OF quadratic_recovery_axioms]
  Blossom_Path_Recovery.cycle_step_def[OF quadratic_recovery_axioms]
  Blossom_Path_Recovery.next_component_def[OF quadratic_recovery_axioms]
  Blossom_Path_Recovery.emit_vertex_def[OF quadratic_recovery_axioms]
  Blossom_Path_Recovery.cache_route_def[OF quadratic_recovery_axioms]
  Blossom_Path_Recovery.initial_recovery_def[OF quadratic_recovery_axioms]
  Blossom_Path_Recovery.lift_path_def[OF quadratic_recovery_axioms]

lemmas quadratic_routing_axioms =
  Blossom_Path_Recovery.axioms(2)[OF quadratic_recovery_axioms]

lemmas quadratic_recovered_path_code[code] =
  Blossom_Path_Recovery.recovered_path_def[OF quadratic_recovery_axioms,
    folded quadratic_recovered_path_def]

lemmas quadratic_search_loop_core_code[code] =
  Quadratic_Blossom_Search.Quadratic_Blossom_Search_impl.simps[
    OF quadratic_search_capacity_axioms, folded quadratic_search_loop_core_def,
    unfolded quadratic_search_defs]

lemmas quadratic_initial_state_code[code] =
  quadratic_initial_state_def[unfolded quadratic_search_defs
    Blossom_Routing.initial_bases_def[OF quadratic_routing_axioms]]

lemmas quadratic_cache_loop_code[code] =
  Blossom_Path_Recovery.Cache_Route_impl.simps[OF quadratic_recovery_axioms,
    unfolded Blossom_Path_Recovery.Cache_Route_call_1_conds_def[OF quadratic_recovery_axioms]
      Blossom_Path_Recovery.Cache_Route_upd1_def[OF quadratic_recovery_axioms]
      Blossom_Path_Recovery.Cache_Route_ret1_def[OF quadratic_recovery_axioms],
    folded quadratic_cache_loop_def]

lemmas quadratic_recovery_loop_code[code] =
  Blossom_Path_Recovery.Blossom_Path_Recovery_impl.simps[OF quadratic_recovery_axioms,
    where hierarchy_children="quadratic_hierarchy_children :: quadratic_hierarchy \<Rightarrow> nat \<Rightarrow> nat
      list"
      and edge_lookup="\<lambda>A. A",
    unfolded quadratic_recovery_defs,
    folded quadratic_cache_loop_def quadratic_recovery_loop_def]

lemmas quadratic_result_path_code[code] =
  Quadratic_Blossom_Search_Lifting.result_path_def[OF quadratic_search_instance,
    folded quadratic_result_path_exec_def, unfolded quadratic_recovery_defs,
    folded quadratic_recovery_loop_def]

lemmas quadratic_search_run_code[code] =
  Quadratic_Blossom_Search_Lifting.Quadratic_Blossom_Search_run_def[
    OF quadratic_search_instance[where nil="quadratic_nil vs" and vs=vs], of vs N,
    folded quadratic_search_run_def quadratic_result_path_exec_def
      quadratic_search_loop_core_def quadratic_initial_state_def] for vs N

section "Demonstrations"

lemma quadratic_demo_input:
  "graph_input_rbt (quadratic_nil (remdups demo_vs)) demo_G demo_vs"
  using demo_input
  by(auto simp: gm.graph_input_def demo_vs_def quadratic_nil_def)

lemma quadratic_demo_max:
  "max_card_matching (ugraph_abs_rbt demo_G)
    (matching_abs_rbt (quadratic_nil (remdups demo_vs)) (current_matching (quadratic_max_run demo_G demo_vs)))"
  using cubic_blossom_correct(1)[OF quadratic_demo_input]
  .


value "let M = current_matching (quadratic_max_run demo_G demo_vs)
  in (Tree2.inorder M, quadratic_path demo_G demo_vs M)"
value "quadratic_path demo_G demo_vs (add_alternatingly_rbt Leaf [1,2,3,4])"
value "map (\<lambda>vs. Tree2.inorder (current_matching (quadratic_max_run (from_list_rbt []) vs))) [[], [0],
  [0,0]]"

export_code quadratic_max_run in SML module_name Cubic_Blossom

end
