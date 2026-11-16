theory Quadratic_Blossom_Search_Preservation
  imports Blossom_Executable.Quadratic_Blossom_Search
    Blossom_Executable.Compute_Alt_Path_Invars Blossom_Executable.Graph_Quotient_Lifting
begin

provenance ai_human

section "Map updates"

context fixed_univ_map
begin

lemma indexed_map_updates:
  "\<lbrakk>fixed_univ_map_invar A; set xs \<subseteq> K; distinct xs\<rbrakk> \<Longrightarrow>
    let B = snd (foldl (\<lambda>(i, B) c. (Suc i, fixed_univ_map_upd B c (f i c))) (n, A) xs)
    in fixed_univ_map_invar B \<and>
      (\<forall>c. c \<notin> set xs \<longrightarrow> fixed_univ_map_lookup B c = fixed_univ_map_lookup A c) \<and>
      (\<forall>i < length xs. fixed_univ_map_lookup B (xs ! i) = f (n + i) (xs ! i))"
  by(induction xs arbitrary: n A)
    (auto simp: Let_def fixed_univ_map_upd fixed_univ_map_upd_invar nth_Cons split: nat.splits)

lemma map_updates:
  "\<lbrakk>fixed_univ_map_invar A; set xs \<subseteq> K\<rbrakk> \<Longrightarrow>
    fixed_univ_map_invar (foldl (\<lambda>A v. fixed_univ_map_upd A v (f v)) A xs) \<and>
    (\<forall>v. fixed_univ_map_lookup (foldl (\<lambda>A v. fixed_univ_map_upd A v (f v)) A xs) v =
      (if v \<in> set xs then f v else fixed_univ_map_lookup A v))"
  by(induction xs arbitrary: A)
    (auto simp: fixed_univ_map_upd fixed_univ_map_upd_invar)

end

context Blossom_Routing
begin

lemma record_parents_props:
  assumes "link_invar N" "set cs \<subseteq> K" "distinct cs"
  shows "link_invar (record_parents N cs b)"
    "c \<notin> set cs \<Longrightarrow> link_lookup (record_parents N cs b) c = link_lookup N c"
    "i < length cs \<Longrightarrow> link_lookup (record_parents N cs b) (cs ! i) = (b, i)"
  using Links.indexed_map_updates[OF assms, where f = "\<lambda>i c. (b, i)" and n = 0]
  by(auto simp: record_parents_def Let_def)

end

section "Matching coverage and quotient projections"

lemma matching_component_boundary:
  "\<lbrakk>matching M; Vs (M\<lbrakk>S\<rbrakk>) = S - {b}; {u, v} \<in> M; u \<in> S; v \<notin> S\<rbrakk> \<Longrightarrow> u = b"
  using matched_vertex_not_in_Vs_of_graph_inter_Vs[of M "{u, v}" u S]
  by auto

lemma matching_coverage_union:
  assumes "matching M" "dblton_graph M" "distinct cs" "odd (length cs)"
    "pairwise (\<lambda>c d. S c \<inter> S d = {}) (set cs)"
    "\<And>c. c \<in> set cs \<Longrightarrow> Vs (M\<lbrakk>S c\<rbrakk>) = S c - {base c}"
    "odd (card (\<Union>(S ` set cs)))"
    "\<And>i. \<lbrakk>i < length cs - 1; odd i\<rbrakk> \<Longrightarrow>
      fst (W i) \<in> S (cs ! i) \<and> snd (W i) \<in> S (cs ! Suc i) \<and> {fst (W i), snd (W i)} \<in> M"
  shows "Vs (M\<lbrakk>\<Union>(S ` set cs)\<rbrakk>) = \<Union>(S ` set cs) - {base (hd cs)}"
proof-
  let ?U = "\<Union>(S ` set cs)"
  have bases: "fst (W i) = base (cs ! i)" "snd (W i) = base (cs ! Suc i)"
    if "i < length cs - 1" "odd i" for i
  proof-
    have "S (cs ! i) \<inter> S (cs ! Suc i) = {}"
      using assms(3,5) that
      by(auto simp: pairwise_def nth_eq_iff_index_eq)
    thus "fst (W i) = base (cs ! i)" "snd (W i) = base (cs ! Suc i)"
      using assms(1,6) assms(8)[of i] that
        matching_component_boundary[of M "S (cs ! i)" "base (cs ! i)" "fst (W i)" "snd (W i)"]
        matching_component_boundary[of M "S (cs ! Suc i)" "base (cs ! Suc i)" "snd (W i)" "fst (W i)"]
      by(auto simp: insert_commute)
  qed
  have "Vs {edges_of_path (map base cs) ! i |i. i < length (map base cs) - 1 \<and> odd i} \<subseteq> Vs (M\<lbrakk>?U\<rbrakk>)"
    using assms(8) bases
    by(intro Vs_subset) (auto simp: edges_of_path_index graph_inter_Vs_def; fastforce)
  hence "base ` set (tl cs) \<subseteq> Vs (M\<lbrakk>?U\<rbrakk>)"
    using assms(4)
    by(simp only: verts_of_odd_edges; cases cs) auto
  moreover have "S c - {base c} \<subseteq> Vs (M\<lbrakk>?U\<rbrakk>)" if "c \<in> set cs" for c
    unfolding assms(6)[OF that, symmetric]
    using that
    by(intro Vs_subset) (auto simp: graph_inter_Vs_def)
  ultimately have covered: "?U - {base (hd cs)} \<subseteq> Vs (M\<lbrakk>?U\<rbrakk>)"
    by(cases cs) auto
  have bounds: "Vs (M\<lbrakk>?U\<rbrakk>) \<subseteq> ?U" "even (card (Vs (M\<lbrakk>?U\<rbrakk>)))"
    by(intro graph_inter_Vs_subset even_number_of_matching_verts
      matching_subgraph[OF assms(1)] dblton_graph_Vs_inter assms(2))+
  have "Vs (M\<lbrakk>?U\<rbrakk>) = ?U \<or> Vs (M\<lbrakk>?U\<rbrakk>) = ?U - {base (hd cs)}"
    using covered bounds(1)
    by blast
  thus ?thesis
    using bounds(2) assms(7)
    by auto
qed

lemma projected_graph_contract:
  fixes R A S b
  defines "C \<equiv> \<lambda>x. if x \<in> S then b else x"
  shows "quot_graph C {{R u, R v} | u v. {u, v} \<in> A \<and> R u \<noteq> R v} - {{b}} =
    {{C (R u), C (R v)} | u v. {u, v} \<in> A \<and> C (R u) \<noteq> C (R v)}"
proof-
  have "C u \<noteq> C v \<longleftrightarrow> u \<noteq> v \<and> {C u, C v} \<noteq> {b}" for u v
    by(auto simp: C_def split: if_splits)
  thus ?thesis
    by(auto simp: quot_graph_def; blast)
qed

section "Initialization"

context Quadratic_Blossom_Search
begin

lemma initial_cursors_fold:
  "\<lbrakk>cursor_invar C; set xs \<subseteq> V0\<rbrakk> \<Longrightarrow>
    cursor_invar (foldl cursor_reset C xs) \<and>
    (\<forall>u. cursor_abstract (foldl cursor_reset C xs) u = cursor_abstract C u \<and>
      cursor_iterated (foldl cursor_reset C xs) u =
        (if u \<in> set xs then {} else cursor_iterated C u) \<and>
      cursor_remaining (foldl cursor_reset C xs) u =
        (if u \<in> set xs then cursor_abstract C u else cursor_remaining C u))"
  by(induction xs arbitrary: C)
    (auto simp: Neighbours.idx_reset_invar Neighbours.idx_reset_abstract
      Neighbours.idx_reset_iterated Neighbours.idx_reset_remaining
      Neighbours.idx_reset_iterated_other Neighbours.idx_reset_remaining_other)

lemma initial_frontier_fold:
  "\<lbrakk>fset_invar S; queue_invar Q; set xs \<subseteq> K;
    length (queue_abstract Q) + length xs \<le> cap\<rbrakk> \<Longrightarrow>
    (let (S', Q') = foldl (\<lambda>(S, Q) v. if mate_partner M0 v = nil
          then (fset_insert v S, queue_push Q v) else (S, Q)) (S, Q) xs
     in fset_invar S' \<and> queue_invar Q' \<and>
       fset_abstract S' = fset_abstract S \<union> {v \<in> set xs. mate_partner M0 v = nil} \<and>
       queue_abstract Q' = queue_abstract Q @ filter (\<lambda>v. mate_partner M0 v = nil) xs)"
  by(induction xs arbitrary: S Q)
    (auto simp: Let_def case_prod_beta Fset.fixed_univ_set_insert Work.queue_push)

end

context Quadratic_Blossom_Search_thms
begin

lemmas [simp] = initial_inputs(2-12,14,15)

lemma input_props[simp]:
  "distinct vs" "set vs = V0" "V0 \<subseteq> K" "nil \<notin> K" "length vs \<le> cap"
  "Graph.graph_inv G" "Graph.finite_graph G" "Graph.finite_vsets G"
  "dVs (Graph.digraph_abs G) \<subseteq> V0"
  "(u, v) \<in> Graph.digraph_abs G \<longleftrightarrow> (v, u) \<in> Graph.digraph_abs G"
  "(u, u) \<notin> Graph.digraph_abs G"
  "mate_invar input_graph M0" "cursor_invar C0"
  "u \<in> V0 \<Longrightarrow> cursor_abstract C0 u = adj_abstract (Graph.neighbourhood G u)"
  using initial_inputs(1)
  by(auto simp: input_axioms_def)

lemma input_vertex_in_universe[simp, intro]: "v \<in> V0 \<Longrightarrow> v \<in> K"
  using input_props(3)
  by blast

lemma initial_finite[simp]: "finite V0" "card V0 = length vs"
  using finite_set[of vs] distinct_card[of vs]
  by auto

lemma input_graph_vertices: "Vs input_graph \<subseteq> V0"
  using input_props(9)
  by(auto simp: input_graph_def Vs_def dVs_def)

lemma input_graph_doubleton: "dblton_graph input_graph"
  using input_props(11)
  by(auto simp: input_graph_def dblton_graph_def; blast)

lemmas input_graph_props = input_graph_vertices input_graph_doubleton

lemma input_matching_props:
  "matching (mate_abstract M0)" "mate_abstract M0 \<subseteq> input_graph"
  "Vs (mate_abstract M0) \<subseteq> V0" "Vs (mate_abstract M0) \<subseteq> K"
  using Mate.matching(1)[of input_graph M0] input_graph_props(1)
  by(auto dest: Vs_subset)

lemma initial_unmatched[simp]:
  "v \<in> V0 \<Longrightarrow> (mate_partner M0 v = nil \<longleftrightarrow> v \<notin> Vs (mate_abstract M0))"
  "v \<in> V0 \<Longrightarrow> (nil = mate_partner M0 v \<longleftrightarrow> v \<notin> Vs (mate_abstract M0))"
  using Mate.lookup_partner[of input_graph M0 v "mate_partner M0 v"]
  by(auto dest: edges_are_Vs Mate.matching(5)[of input_graph M0, simplified] split: if_splits)

lemma initial_frontier_props[simp]:
  "fset_invar (fst initial_frontier)" "queue_invar (snd initial_frontier)"
  "fset_abstract (fst initial_frontier) = V0 - Vs (mate_abstract M0)"
  "queue_abstract (snd initial_frontier) = filter (\<lambda>v. v \<notin> Vs (mate_abstract M0)) vs"
  using initial_frontier_fold[of fset_empty queue_empty vs]
  by(auto intro!: filter_cong
    simp: initial_frontier_def Fset.fixed_univ_set_empty Work.queue_empty case_prod_beta)

lemma initial_map_props[simp]:
  "owner_invar (foldl (\<lambda>L v. owner_update L v v) L0 vs)"
  "v \<in> V0 \<Longrightarrow> owner_lookup (foldl (\<lambda>L v. owner_update L v v) L0 vs) v = v"
  "base_invar (Routing.initial_bases D0 vs)"
  "v \<in> V0 \<Longrightarrow> base_lookup (Routing.initial_bases D0 vs) v = v"
  using Owners.map_updates[of L0 vs id] Routing.Bases.map_updates[of D0 vs id]
  by(auto simp: Routing.initial_bases_def)

lemma initial_cursor_props[simp]:
  "cursor_invar (foldl cursor_reset C0 vs)"
  "cursor_abstract (foldl cursor_reset C0 vs) u = cursor_abstract C0 u"
  "u \<in> V0 \<Longrightarrow> cursor_iterated (foldl cursor_reset C0 vs) u = {}"
  "u \<in> V0 \<Longrightarrow> cursor_remaining (foldl cursor_reset C0 vs) u = cursor_abstract C0 u"
  using initial_cursors_fold[of C0 vs]
  by auto

lemma input_edge_vertices[dest]:
  "{u, v} \<in> input_graph \<Longrightarrow> u \<in> V0 \<and> v \<in> V0 \<and> u \<noteq> v"
  using input_graph_props
  by(auto simp: Vs_def dblton_graph_def)

lemma input_edge_iff[simp]: "{u, v} \<in> input_graph \<longleftrightarrow> (u, v) \<in> Graph.digraph_abs G"
  by(auto simp: input_graph_def doubleton_eq_iff)

lemma initial_hierarchy[simp]:
  "v \<in> V0 \<Longrightarrow> hierarchy_members H0 v = {v}"
  "v \<in> V0 \<Longrightarrow> hierarchy_children H0 v = []"
  using initial_inputs(13)
  by auto

lemma initial_hierarchy_relation[simp]: "hierarchy_relation H0 = {}"
  by(auto simp: hierarchy_relation_def)

lemma initial_representative[simp]:
  "v \<in> V0 \<Longrightarrow> representative initial_search_state v = v"
  by(auto simp: initial_state_def Let_def case_prod_beta Components.reset_representatives)

lemma projected_graph:
  assumes "A \<subseteq> input_graph"
  shows "{{R u, R v} | u v. {u, v} \<in> A \<and> R u \<noteq> R v} = {e \<in> quot_graph R A. card e = 2}"
proof(standard; safe)
  fix u v
  assume "{u, v} \<in> A" "R u \<noteq> R v"
  thus "{R u, R v} \<in> quot_graph R A" "card {R u, R v} = 2"
    using edge_in_graph_in_quot[of "{u, v}" A R]
    by(auto)
next
  fix e
  assume card: "e \<in> quot_graph R A" "card e = 2"
  then obtain d where "d \<in> A" "e = R ` d"
    by(auto simp: quot_graph_def)
  then obtain u v where "{u, v} \<in> A" "e = {R u, R v}"
    using assms input_graph_doubleton
    by(auto)
  thus "\<exists>u v. e = {R u, R v} \<and> {u, v} \<in> A \<and> R u \<noteq> R v"
    using card(2)
    by(auto simp: card_insert_if split: if_splits; blast)
qed

lemma initial_projection:
  assumes "A \<subseteq> input_graph"
  shows "{{representative initial_search_state u, representative initial_search_state v} | u v.
    {u, v} \<in> A \<and> representative initial_search_state u \<noteq> representative initial_search_state v} = A"
proof-
  have "quot_graph (representative initial_search_state) A = quot_graph id A"
    using assms input_graph_vertices
    by(intro quot_graph_cong image_cong) (auto intro!: initial_representative simp: Vs_def)
  thus ?thesis
    using assms input_graph_doubleton
    by(auto simp: projected_graph[OF assms] quot_graph_def dblton_graph_def; fastforce)
qed

lemma initial_quotient[simp]: "quotient_graph initial_search_state = input_graph"
  by(simp only: quotient_graph_def initial_projection subset_refl)

lemma initial_state_observations:
  "qbs_forest initial_search_state = forest_empty (fst initial_frontier)"
  "qbs_matching initial_search_state = M0" "qbs_hierarchy initial_search_state = H0"
  "qbs_current initial_search_state = nil" "qbs_status initial_search_state = Quadratic_Searching"
  "qbs_queue initial_search_state = snd initial_frontier"
  "qbs_neighbours initial_search_state = foldl cursor_reset C0 vs"
  "qbs_fresh initial_search_state = fresh0"
  "qbs_cycle_edges initial_search_state = B0"
  "qbs_bases initial_search_state = Routing.initial_bases D0 vs"
  "qbs_parents initial_search_state = N0" "qbs_hints initial_search_state = J0"
  "qbs_components initial_search_state = uf_reset U0"
  "qbs_owners initial_search_state = foldl (\<lambda>L v. owner_update L v v) L0 vs"
  "qbs_forest_edges initial_search_state = P0"
  by(auto simp: initial_state_def Let_def case_prod_beta)

lemmas [simp] = initial_state_observations(1-12)

lemma initial_forest_invar[simp]:
  "forest_invar (mate_abstract M0) (forest_empty (fst initial_frontier))"
  using input_matching_props
  by(auto intro!: Forest.empty_forest(5))

lemmas [simp] = Forest.empty_forest(1-4) Fset.fixed_univ_set_empty

lemma initial_effectively_even[simp]:
  "effectively_even initial_search_state = V0 - Vs (mate_abstract M0)"
  by(auto simp: effectively_even_def)

lemma initial_singleton_matching: "{e \<in> mate_abstract M0. e \<subseteq> {v}} = {}"
  using Vs_inter_single_empty[of "mate_abstract M0" v] input_graph_doubleton input_matching_props(2)
  by(auto simp: graph_inter_Vs_def)

lemma initial_recovering_structure:
  "invar_recovering_structure H0 B0 (Routing.initial_bases D0 vs) N0"
  using initial_inputs(13)
  by(auto simp: invar_recovering_structure_def recovery_tree_def invar_navigation_def
    initial_singleton_matching Let_def)

lemma initial_matching_projection[invar_holds_intros]:
  "invar_matching_projection initial_search_state"
  by(simp only: invar_matching_projection_def initial_state_observations(1-12)
    initial_projection input_matching_props)

lemma initial_state_props[invar_holds_intros]: "invar_search initial_search_state"
  using initial_recovering_structure initial_matching_projection initial_inputs(13,16,17)
  by(auto intro!: invar_props_intros
    simp: initial_state_observations Components.reset_invar Components.reset_representatives
      input_matching_props pending_arcs_def Pair_Graph.neighbourhood_def)

end

section "Preservation"

context Quadratic_Blossom_Search_Lifting
begin

subsection "Routes through the blossom hierarchy"

lemmas invar_recovering_structure_props[invar_props_elims] =
  invar_recovering_structure_def[THEN iffD1, elim_format, unfolded atomize_conjL[symmetric]]

lemmas recovery_tree_node = recovery_tree_def[THEN iffD1,
  THEN conjunct2, THEN conjunct2, rule_format, simplified Let_def]

lemma hierarchy_top_disjoint:
  assumes "hierarchy_invar H" "S \<subseteq> hierarchy_tops H"
  shows "pairwise (\<lambda>c d. hierarchy_members H c \<inter> hierarchy_members H d = {}) S"
  using assms
proof(intro pairwiseI, goal_cases)
  case (1 c d)
  have "hierarchy_members H c \<noteq> hierarchy_members H d"
    using 1 Hierarchy.max_ids[of H] Hierarchy.collect_elems_bijection[of H]
    by(auto simp: bij_betw_def inj_on_def; blast)
  moreover have "laminar (hierarchy_universe H) (hierarchy_abstract H)"
    using assms(1) Hierarchy.laminarity[of H] Hierarchy.collect_elems_bijection[of H]
    by(auto simp: bij_betw_def)
  ultimately show ?case
    using 1 Hierarchy.max_ids[of H]
    by(intro laminar_maximal_sets_disjoint[of "hierarchy_universe H" "hierarchy_abstract H"]) auto
qed

lemma hierarchy_children_ids:
  "\<lbrakk>recovery_tree H; b \<in> hierarchy_ids H\<rbrakk> \<Longrightarrow>
    set (hierarchy_children H b) \<subseteq> hierarchy_ids H"
  by(auto simp: recovery_tree_def Let_def split: if_splits)

lemma hierarchy_child_not_top:
  assumes "hierarchy_invar H" "recovery_tree H" "b \<in> hierarchy_ids H"
    "c \<in> set (hierarchy_children H b)"
  shows "c \<notin> hierarchy_tops H"
proof-
  have "c \<noteq> b"
    using assms(2-4) wf_not_refl[of "hierarchy_relation H" b]
    by(auto simp: recovery_tree_def hierarchy_relation_def)
  moreover have "c \<in> hierarchy_ids H" "hierarchy_members H c \<subseteq> hierarchy_members H b"
    using assms(2-4)
    by(fastforce simp: recovery_tree_def Let_def split: if_splits)+
  ultimately have "hierarchy_members H c \<subset> hierarchy_members H b"
    using assms(1,3) Hierarchy.collect_elems_bijection[of H]
    by(auto simp: bij_betw_def inj_on_def; blast)
  moreover have "hierarchy_members H b \<in> hierarchy_abstract H"
    using assms(1,3) Hierarchy.collect_elems_bijection[of H]
    by(auto simp: bij_betw_def)
  ultimately show ?thesis
    using assms(1) Hierarchy.max_ids[of H]
    by(auto simp: maximal_sets_def)
qed

lemma hierarchy_edge_navigation:
  assumes "invar_navigation H D N" "(c, b) \<in> hierarchy_relation H"
  shows "fst (link_lookup N c) = b"
    "snd (link_lookup N c) < length (hierarchy_children H b)"
    "hierarchy_children H b ! snd (link_lookup N c) = c"
  using assms
  by(auto simp: hierarchy_relation_def in_set_conv_nth invar_navigation_def)

lemma hierarchy_edge_members:
  "\<lbrakk>recovery_tree H; (c,b) \<in> hierarchy_relation H\<rbrakk> \<Longrightarrow>
    hierarchy_members H c \<subseteq> hierarchy_members H b"
  by(fastforce simp: recovery_tree_def hierarchy_relation_def Let_def split: if_splits)

lemma hierarchy_members_mono:
  assumes "recovery_tree H" "(c, b) \<in> rtrancl (hierarchy_relation H)"
  shows "hierarchy_members H c \<subseteq> hierarchy_members H b"
  using assms(2)
  by(induction rule: rtrancl_induct)
    (auto dest: hierarchy_edge_members[OF assms(1)] intro: subset_trans)

lemma hierarchy_members_props:
  assumes "recovery_tree H" "b \<in> hierarchy_ids H"
  shows "(finite (hierarchy_members H b) \<and> hierarchy_members H b \<noteq> {}) \<and>
    (\<forall>v \<in> hierarchy_members H b. v \<in> hierarchy_ids H \<and> hierarchy_children H v = [] \<and>
      (v,b) \<in> rtrancl (hierarchy_relation H))"
  using assms(2)
proof(induction b rule: wf_induct_rule[OF recovery_tree_def[THEN iffD1,
      THEN conjunct2, THEN conjunct1, OF assms(1)]])
  case IH: (1 b)
  have "(finite (hierarchy_members H c) \<and> hierarchy_members H c \<noteq> {}) \<and>
    (\<forall>v \<in> hierarchy_members H c. v \<in> hierarchy_ids H \<and> hierarchy_children H v = [] \<and>
      (v,c) \<in> rtrancl (hierarchy_relation H))"
    if "c \<in> set (hierarchy_children H b)" for c
    using that recovery_tree_node[OF assms(1) IH.prems] IH.prems
    by(intro IH.IH) (auto simp: hierarchy_relation_def split: if_splits)
  thus ?case
    using recovery_tree_node[OF assms(1) IH.prems] IH.prems
    by(auto simp: hierarchy_relation_def split: if_splits intro: rtrancl_into_rtrancl)
qed

lemmas hierarchy_members_finite_nonempty = hierarchy_members_props[THEN conjunct1]

lemmas hierarchy_member_leaf = hierarchy_members_props[THEN conjunct2, rule_format]

lemma hierarchy_member_ancestor:
  "\<lbrakk>recovery_tree H; b \<in> hierarchy_ids H; v \<in> hierarchy_members H b;
    (v,c) \<in> rtrancl (hierarchy_relation H)\<rbrakk> \<Longrightarrow> v \<in> hierarchy_members H c"
  using hierarchy_member_leaf[of H b v] hierarchy_members_mono[of H v c]
  by(auto simp: recovery_tree_def Let_def; blast)

lemma route_ancestors_step:
  assumes "recovery_tree H" "invar_navigation H D N"
    "(target,c) \<in> rtrancl (hierarchy_relation H)" "(c,p) \<in> hierarchy_relation H"
  shows "route_ancestors H p target = insert p (route_ancestors H c target)"
proof-
  let ?R = "hierarchy_relation H"
  have functional: "single_valued ?R"
    using assms(2)
    by(auto intro!: single_valuedI dest: hierarchy_edge_navigation(1))
  have "(c,x) \<in> rtrancl ?R \<Longrightarrow> x = c \<or> (p,x) \<in> rtrancl ?R" for x
    using assms(4) functional
    by(auto elim: converse_rtranclE dest: single_valuedD)
  moreover have "antisym (rtrancl ?R)"
    using assms(1)
    by(auto simp: recovery_tree_def intro: acyclic_impl_antisym_rtrancl wf_acyclic)
  ultimately have "\<lbrakk>(target,x) \<in> trancl ?R; (x,p) \<in> rtrancl ?R\<rbrakk> \<Longrightarrow>
      x = p \<or> (x,c) \<in> rtrancl ?R" for x
    using single_valued_confluent[OF functional assms(3), of x]
      trancl_into_rtrancl[of target x ?R]
    by(blast dest: antisymD)
  moreover have "p \<in> hierarchy_ids H"
    using assms(4)
    by(auto simp: hierarchy_relation_def)
  ultimately show ?thesis
    using assms(3,4)
    by(auto simp: route_ancestors_def
      intro: rtrancl_into_rtrancl rtrancl_into_trancl1; blast)
qed

lemma cache_route_next:
  assumes "invar_navigation H D N" "Recovery.Cache_Route_call_1_conds b state"
    "invar_cache_route H b target state"
  shows "(cache_current state, fst (link_lookup N (cache_current state))) \<in> hierarchy_relation H"
    "fst (link_lookup N (cache_current state)) \<in> route_ancestors H b target"
proof-
  obtain p where "(cache_current state,p) \<in> hierarchy_relation H"
    "(p,b) \<in> rtrancl (hierarchy_relation H)"
    using assms(2,3)
    by(auto simp: Recovery.Cache_Route_call_1_conds_def
      elim!: invar_cache_route_props elim: converse_rtranclE)
  thus "(cache_current state, fst (link_lookup N (cache_current state))) \<in> hierarchy_relation H"
    "fst (link_lookup N (cache_current state)) \<in> route_ancestors H b target"
    using assms hierarchy_edge_navigation[OF assms(1), of "cache_current state" p]
    by(auto simp: route_ancestors_def hierarchy_relation_def
      elim!: invar_cache_route_props intro: rtrancl_into_trancl1)
qed

lemma invar_cache_route_holds_1[invar_holds_intros]:
  assumes "recovery_tree H" "invar_navigation H D N" "hierarchy_ids H \<subseteq> K"
    "Recovery.Cache_Route_call_1_conds b state" "invar_cache_route H b target state"
  shows "invar_cache_route H b target (Recovery.Cache_Route_upd1 N target state)"
proof-
  let ?c = "cache_current state"
  let ?p = "fst (link_lookup N ?c)"
  let ?i = "snd (link_lookup N ?c)"
  note step = cache_route_next[OF assms(2,4,5)]
  have input: "target \<in> hierarchy_members H ?c" "?p \<in> K"
    using hierarchy_member_ancestor[of H b target ?c] assms(1,3,5) step(2)
    by(auto simp: route_ancestors_def elim!: invar_cache_route_props dest: hierarchy_edge_navigation)
  hence "invar_route_cache H (link_update (cache_hints state) ?p (target,?i))"
    using assms(2,3,5) step hierarchy_edge_navigation(2,3)[OF assms(2) step(1)]
    by(auto simp: invar_route_cache_def route_ancestors_def
      Routing.Links.fixed_univ_map_upd Routing.Links.fixed_univ_map_upd_invar
      elim!: invar_cache_route_props dest: hierarchy_edge_navigation split: if_splits)
  moreover have "route_ancestors H ?p target = insert ?p (route_ancestors H ?c target)"
    using assms(1,2,5) step(1)
    by(intro route_ancestors_step[where D = D and N = N])
      (auto elim!: invar_cache_route_props)
  hence "route_cached H ?p target (link_update (cache_hints state) ?p (target,?i))"
    using assms(3,5) step(2) input(2)
    by(auto simp: route_cached_def invar_route_cache_def route_ancestors_def
      Routing.Links.fixed_univ_map_upd elim!: invar_cache_route_props split: if_splits)
  ultimately show ?thesis
    using assms(5) step
    by(auto simp: invar_cache_route_def route_ancestors_def Recovery.Cache_Route_upd1_def Let_def case_prod_beta
      intro: rtrancl_into_rtrancl)
qed

lemma wf_Cache_Route_term_rel:
  assumes "recovery_tree H"
  shows "wf (Cache_Route_term_rel' H)"
proof-
  have "finite (hierarchy_relation H)"
    unfolding hierarchy_relation_def
    by(rule finite_subset[of _ "converse (Sigma (hierarchy_ids H) (\<lambda>b. set (hierarchy_children H b)))"])
      (auto simp: assms[unfolded recovery_tree_def, THEN conjunct1])
  thus ?thesis
    using assms[unfolded recovery_tree_def, THEN conjunct2, THEN conjunct1]
    by(auto simp: Cache_Route_term_rel'_def intro: finite_acyclic_wf_converse wf_acyclic)
qed

lemma cache_route_call_1_terminates[termination_intros]:
  assumes "recovery_tree H" "invar_navigation H D N"
    "Recovery.Cache_Route_call_1_conds b state" "invar_cache_route H b target state"
  shows "(Recovery.Cache_Route_upd1 N target state, state) \<in> Cache_Route_term_rel' H"
  using cache_route_next(1)[OF assms(2-4)]
  by(simp add: Cache_Route_term_rel'_def Recovery.Cache_Route_upd1_def Let_def case_prod_beta inv_image_def)

lemma Cache_Route_termination:
  assumes "recovery_tree H" "invar_navigation H D N" "hierarchy_ids H \<subseteq> K"
    "invar_cache_route H b target state"
  shows "Recovery.Cache_Route_dom N target b state"
  using assms(4)
proof(induction state rule: wf_induct_rule[OF wf_Cache_Route_term_rel[OF assms(1)]])
  case IH: (1 state)
  show ?case
    by(rule Recovery.Cache_Route_domintros)
      (insert assms(1-3) IH cache_route_call_1_terminates[of H D N b state target],
       auto intro: invar_cache_route_holds_1)
qed

lemma cache_route_step_frame:
  "\<lbrakk>invar_navigation H D N; hierarchy_ids H \<subseteq> K; Recovery.Cache_Route_call_1_conds b state;
    invar_cache_route H b target state; a \<notin> route_ancestors H b target\<rbrakk> \<Longrightarrow>
    link_lookup (cache_hints (Recovery.Cache_Route_upd1 N target state)) a = link_lookup (cache_hints state) a"
  using cache_route_next(2)[of H D N b state target]
  by(auto simp: route_ancestors_def Recovery.Cache_Route_upd1_def Let_def case_prod_beta
    Routing.Links.fixed_univ_map_upd elim!: invar_cache_route_props invar_route_cache_props)

lemma Cache_Route_props:
  assumes "recovery_tree H" "invar_navigation H D N" "hierarchy_ids H \<subseteq> K"
    "invar_cache_route H b target state"
  shows "invar_cache_route H b target (Recovery.Cache_Route N target b state) \<and>
    (\<forall>a. a \<notin> route_ancestors H b target \<longrightarrow>
      link_lookup (cache_hints (Recovery.Cache_Route N target b state)) a =
        link_lookup (cache_hints state) a)"
  using Cache_Route_termination[OF assms] assms(4)
proof(induction rule: Recovery.Cache_Route_induct[consumes 1])
  case IH: (1 state)
  show ?case
    using assms(1-3) IH cache_route_step_frame[of H D N b state target]
    by(cases "Recovery.Cache_Route_call_1_conds b state")
      (auto simp: Recovery.Cache_Route_simps Recovery.Cache_Route_ret_1_conds_def
        Recovery.Cache_Route_ret1_def intro: invar_cache_route_holds_1)
qed

lemmas invar_cache_route_holds = Cache_Route_props[THEN conjunct1]

lemmas Cache_Route_frame = Cache_Route_props[THEN conjunct2, rule_format]

lemma Cache_Route_correct:
  assumes "recovery_tree H" "invar_navigation H D N" "hierarchy_ids H \<subseteq> K"
    "invar_cache_route H b target state"
  shows "cache_current (Recovery.Cache_Route N target b state) = b"
    "invar_route_cache H (cache_hints (Recovery.Cache_Route N target b state))"
    "route_cached H b target (cache_hints (Recovery.Cache_Route N target b state))"
  using assms invar_cache_route_holds[of H D N b target state]
    Cache_Route_termination[of H D N b target state] Recovery.Cache_Route_ret[of N target b state]
  by(auto simp: Recovery.Cache_Route_ret_1_conds_def Recovery.Cache_Route_call_1_conds_def
    invar_cache_route_def)

lemma route_ancestors_self[simp]:
  "recovery_tree H \<Longrightarrow> route_ancestors H b b = {}"
  by(auto simp: recovery_tree_def route_ancestors_def
    dest: trancl_rtrancl_trancl wf_trancl[THEN wf_not_refl])

lemma invar_cache_route_initial:
  "\<lbrakk>recovery_tree H; b \<in> hierarchy_ids H; target \<in> hierarchy_members H b;
    invar_route_cache H J\<rbrakk> \<Longrightarrow>
    invar_cache_route H b target \<lparr>cache_current = target, cache_hints = J\<rparr>"
  using hierarchy_member_leaf[of H b target]
  by(auto simp: invar_cache_route_def route_cached_def)

context
  fixes H D N b target J
  assumes cache_input: "recovery_tree H" "invar_navigation H D N" "hierarchy_ids H \<subseteq> K"
    "b \<in> hierarchy_ids H" "target \<in> hierarchy_members H b" "invar_route_cache H J"
begin

lemma cache_route_initial_dom:
  "Recovery.Cache_Route_dom N target b \<lparr>cache_current = target, cache_hints = J\<rparr>"
  using cache_input
  by(auto intro: Cache_Route_termination invar_cache_route_initial)

lemma cache_route_correct:
  assumes "fst (link_lookup J b) = target \<Longrightarrow> route_cached H b target J"
  shows "invar_route_cache H (Recovery.cache_route N target b J)"
    "route_cached H b target (Recovery.cache_route N target b J)"
  using cache_input assms invar_cache_route_initial[OF cache_input(1,4-6)]
  by(auto simp: Recovery.cache_route_def
    Recovery.Cache_Route_impl_same[OF cache_route_initial_dom]
    intro: Cache_Route_correct split: if_splits)

lemma cache_route_frame:
  "a \<notin> route_ancestors H b target \<Longrightarrow>
    link_lookup (Recovery.cache_route N target b J) a = link_lookup J a"
  using cache_input invar_cache_route_initial[OF cache_input(1,4-6)]
    Cache_Route_frame[where state = "\<lparr>cache_current = target, cache_hints = J\<rparr>", simplified]
  by(auto simp: Recovery.cache_route_def
    Recovery.Cache_Route_impl_same[OF cache_route_initial_dom] split: if_splits)

end

subsection "Exhausting the queue"

lemma
  assumes "Quadratic_Blossom_Search_call_1_conds state"
  shows invar_adts_holds_1[invar_holds_intros]:
      "invar_adts state \<Longrightarrow> invar_adts (Quadratic_Blossom_Search_upd1 state)"
    and invar_forest_holds_1[invar_holds_intros]:
      "invar_forest state \<Longrightarrow> invar_forest (Quadratic_Blossom_Search_upd1 state)"
    and invar_matching_projection_holds_1[invar_holds_intros]:
      "invar_matching_projection state \<Longrightarrow> invar_matching_projection (Quadratic_Blossom_Search_upd1 state)"
    and invar_representatives_holds_1[invar_holds_intros]:
      "invar_representatives state \<Longrightarrow> invar_representatives (Quadratic_Blossom_Search_upd1 state)"
    and invar_components_holds_1[invar_holds_intros]:
      "invar_components state \<Longrightarrow> invar_components (Quadratic_Blossom_Search_upd1 state)"
    and invar_neighbours_holds_1[invar_holds_intros]:
      "invar_neighbours state \<Longrightarrow> invar_neighbours (Quadratic_Blossom_Search_upd1 state)"
    and invar_current_holds_1[invar_holds_intros]:
      "invar_current state \<Longrightarrow> invar_current (Quadratic_Blossom_Search_upd1 state)"
    and invar_queue_holds_1[invar_holds_intros]:
      "invar_queue state \<Longrightarrow> invar_queue (Quadratic_Blossom_Search_upd1 state)"
    and invar_fresh_holds_1[invar_holds_intros]:
      "invar_fresh state \<Longrightarrow> invar_fresh (Quadratic_Blossom_Search_upd1 state)"
    and invar_annotations_holds_1[invar_holds_intros]:
      "invar_annotations state \<Longrightarrow> invar_annotations (Quadratic_Blossom_Search_upd1 state)"
    and invar_hierarchy_size_holds_1[invar_holds_intros]:
      "invar_hierarchy_size state \<Longrightarrow> invar_hierarchy_size (Quadratic_Blossom_Search_upd1 state)"
    and invar_existence_holds_1[invar_holds_intros]:
      "invar_existence state \<Longrightarrow> invar_existence (Quadratic_Blossom_Search_upd1 state)"
    and invar_result_holds_1[invar_holds_intros]:
      "invar_result state \<Longrightarrow> invar_result (Quadratic_Blossom_Search_upd1 state)"
  unfolding Quadratic_Blossom_Search_upd1_def quotient_graph_def effectively_even_def invar_adts_def
    invar_forest_def invar_matching_projection_def invar_representatives_def invar_components_def
    invar_neighbours_def invar_current_def invar_queue_def invar_fresh_def invar_annotations_def
    invar_hierarchy_size_def invar_existence_def invar_result_def
  by(simp_all (no_asm_use) split: if_splits) blast+

lemma invar_scanned_holds_1[invar_holds_intros]:
  "\<lbrakk>Quadratic_Blossom_Search_call_1_conds state; invar_scanned state\<rbrakk>
    \<Longrightarrow> invar_scanned (Quadratic_Blossom_Search_upd1 state)"
  by(auto elim!: call_cond_elims
    simp: invar_scanned_def Quadratic_Blossom_Search_upd1_def pending_arcs_def effectively_even_def; blast)

lemma invar_search_holds_1[invar_holds_intros]:
  "\<lbrakk>Quadratic_Blossom_Search_call_1_conds state; invar_search state\<rbrakk>
    \<Longrightarrow> invar_search (Quadratic_Blossom_Search_upd1 state)"
  by(auto elim!: invar_search_props intro!: invar_search_intro intro: invar_holds_intros)
    (auto simp: Quadratic_Blossom_Search_upd1_def)

lemma state_rel_exploration_holds_1[state_rel_holds_intros]:
  "state_rel_exploration state (Quadratic_Blossom_Search_upd1 state)"
  by(auto intro!: state_rel_exploration_intro simp: Quadratic_Blossom_Search_upd1_def effectively_even_def)

subsection "Finishing a vertex scan"

lemma
  assumes "Quadratic_Blossom_Search_call_3_conds state"
  shows invar_adts_holds_3[invar_holds_intros]:
      "invar_adts state \<Longrightarrow> invar_adts (Quadratic_Blossom_Search_upd3 state)"
    and invar_forest_holds_3[invar_holds_intros]:
      "invar_forest state \<Longrightarrow> invar_forest (Quadratic_Blossom_Search_upd3 state)"
    and invar_matching_projection_holds_3[invar_holds_intros]:
      "invar_matching_projection state \<Longrightarrow> invar_matching_projection (Quadratic_Blossom_Search_upd3 state)"
    and invar_representatives_holds_3[invar_holds_intros]:
      "invar_representatives state \<Longrightarrow> invar_representatives (Quadratic_Blossom_Search_upd3 state)"
    and invar_components_holds_3[invar_holds_intros]:
      "invar_components state \<Longrightarrow> invar_components (Quadratic_Blossom_Search_upd3 state)"
    and invar_neighbours_holds_3[invar_holds_intros]:
      "invar_neighbours state \<Longrightarrow> invar_neighbours (Quadratic_Blossom_Search_upd3 state)"
    and invar_current_holds_3[invar_holds_intros]:
      "invar_current state \<Longrightarrow> invar_current (Quadratic_Blossom_Search_upd3 state)"
    and invar_fresh_holds_3[invar_holds_intros]:
      "invar_fresh state \<Longrightarrow> invar_fresh (Quadratic_Blossom_Search_upd3 state)"
    and invar_annotations_holds_3[invar_holds_intros]:
      "invar_annotations state \<Longrightarrow> invar_annotations (Quadratic_Blossom_Search_upd3 state)"
    and invar_hierarchy_size_holds_3[invar_holds_intros]:
      "invar_hierarchy_size state \<Longrightarrow> invar_hierarchy_size (Quadratic_Blossom_Search_upd3 state)"
    and invar_existence_holds_3[invar_holds_intros]:
      "invar_existence state \<Longrightarrow> invar_existence (Quadratic_Blossom_Search_upd3 state)"
    and invar_result_holds_3[invar_holds_intros]:
      "invar_result state \<Longrightarrow> invar_result (Quadratic_Blossom_Search_upd3 state)"
  unfolding Quadratic_Blossom_Search_upd3_def quotient_graph_def invar_recovering_path_def invar_adts_def
    invar_forest_def invar_matching_projection_def invar_representatives_def invar_components_def
    invar_neighbours_def invar_current_def invar_fresh_def invar_annotations_def invar_hierarchy_size_def
    invar_existence_def invar_result_def
  by(simp_all (no_asm_use) split: if_splits Quadratic_Blossom_Search_status.splits) auto

lemma invar_queue_holds_3[invar_holds_intros]:
  "\<lbrakk>Quadratic_Blossom_Search_call_3_conds state; invar_adts state; invar_queue state\<rbrakk>
    \<Longrightarrow> invar_queue (Quadratic_Blossom_Search_upd3 state)"
  by(auto elim!: call_cond_elims invar_props_elims intro!: invar_queue_intro
    simp: Quadratic_Blossom_Search_upd3_def effectively_even_def Neighbours.idx_has; blast)

lemma invar_scanned_holds_3[invar_holds_intros]:
  "\<lbrakk>Quadratic_Blossom_Search_call_3_conds state; invar_scanned state\<rbrakk>
    \<Longrightarrow> invar_scanned (Quadratic_Blossom_Search_upd3 state)"
  by(auto elim!: call_cond_elims
    simp: invar_scanned_def Quadratic_Blossom_Search_upd3_def pending_arcs_def effectively_even_def; blast)

lemma invar_search_holds_3[invar_holds_intros]:
  "\<lbrakk>Quadratic_Blossom_Search_call_3_conds state; invar_search state\<rbrakk>
    \<Longrightarrow> invar_search (Quadratic_Blossom_Search_upd3 state)"
  by(auto elim!: invar_search_props intro!: invar_search_intro intro: invar_holds_intros)
    (auto simp: Quadratic_Blossom_Search_upd3_def)

lemma state_rel_exploration_holds_3[state_rel_holds_intros]:
  "state_rel_exploration state (Quadratic_Blossom_Search_upd3 state)"
  by(auto intro!: state_rel_exploration_intro simp: Quadratic_Blossom_Search_upd3_def effectively_even_def)

subsection "Termination of administrative steps"

lemma call_1_terminates[termination_intros]:
  "Quadratic_Blossom_Search_call_1_conds state \<Longrightarrow>
    (Quadratic_Blossom_Search_upd1 state, state) \<in> Quadratic_Blossom_Search_term_rel'"
  by(auto elim!: call_cond_elims intro!: mlex_less
    simp: Quadratic_Blossom_Search_term_rel'_def search_phase_measure_def Quadratic_Blossom_Search_upd1_def)

lemma call_3_terminates[termination_intros]:
  "Quadratic_Blossom_Search_call_3_conds state \<Longrightarrow>
    (Quadratic_Blossom_Search_upd3 state, state) \<in> Quadratic_Blossom_Search_term_rel'"
  by(auto elim!: call_cond_elims intro!: mlex_less
    simp: Quadratic_Blossom_Search_term_rel'_def mlex_iff search_phase_measure_def
      search_edges_measure_def search_queue_measure_def search_scan_measure_def
      Quadratic_Blossom_Search_upd3_def effectively_even_def)

lemma wf_term_rel:
  "wf Quadratic_Blossom_Search_term_rel'"
  by(auto simp: Quadratic_Blossom_Search_term_rel'_def wf_mlex)

end

context Quadratic_Blossom_Search_thms
begin

subsection "Reusing the graph quotient"

lemma components_quot_graph:
  assumes "A \<subseteq> input_graph"
    "\<And>v. v \<in> K \<Longrightarrow> uf_representative U v = uf_representative (qbs_components state) v"
  shows "quot_graph (\<lambda>v. owner_lookup (qbs_owners state) (uf_representative U v)) A =
    quot_graph (representative state) A"
  using assms(1) input_graph_vertices input_props(3)
  by(intro quot_graph_cong image_cong)
    (simp; intro arg_cong[where f = "owner_lookup (qbs_owners state)"] assms(2);
      auto simp: Vs_def; blast)+

lemma components_transport:
  assumes "invar_representatives state" "hierarchy_invar (qbs_hierarchy state)"
    "qbs_hierarchy next = qbs_hierarchy state"
    "\<And>v. v \<in> K \<Longrightarrow>
      uf_representative (qbs_components next) v = uf_representative (qbs_components state) v"
  shows "invar_components next = invar_components state"
proof-
  have "hierarchy_ids (qbs_hierarchy state) \<subseteq> K"
    "\<forall>c \<in> hierarchy_ids (qbs_hierarchy state). hierarchy_members (qbs_hierarchy state) c \<subseteq> K"
    using assms(1,2) Hierarchy.elems_in_universe[of "qbs_hierarchy state"] input_props(3)
    by(auto elim!: invar_representatives_props; blast)+
  thus ?thesis
    by(fastforce simp: invar_components_def assms(3,4))
qed

subsection "Starting a vertex scan"

lemma start_scan_source:
  "\<lbrakk>Quadratic_Blossom_Search_call_2_conds state; invar_adts state; invar_queue state\<rbrakk>
    \<Longrightarrow> queue_abstract (qbs_queue state) \<noteq> [] \<and> hd (queue_abstract (qbs_queue state))
    \<in> V0 \<and> hd (queue_abstract (qbs_queue state)) \<noteq> nil"
  using input_vertex_in_universe[of nil]
  by(cases "queue_abstract (qbs_queue state)")
    (auto elim!: call_cond_elims invar_adts_props invar_queue_props
      simp: Work.queue_is_empty effectively_even_def)

lemma start_scan_props:
  assumes "Quadratic_Blossom_Search_call_2_conds state" "invar_adts state" "invar_queue state"
  shows "qbs_current (Quadratic_Blossom_Search_upd2 state) = hd (queue_abstract (qbs_queue state))"
    "queue_abstract (qbs_queue (Quadratic_Blossom_Search_upd2 state)) = tl (queue_abstract (qbs_queue state))"
    "uf_invar (qbs_components (Quadratic_Blossom_Search_upd2 state))"
    "qbs_component (Quadratic_Blossom_Search_upd2 state) =
      representative state (hd (queue_abstract (qbs_queue state)))"
    "v \<in> K \<Longrightarrow> uf_representative (qbs_components (Quadratic_Blossom_Search_upd2 state)) v =
      uf_representative (qbs_components state) v"
  using assms start_scan_source[of state]
  by(auto elim!: invar_adts_props
    simp: Quadratic_Blossom_Search_upd2_def start_scan_def Let_def case_prod_beta
      Work.queue_pop Components.find_result Components.find_invar Components.find_representatives)

lemma start_scan_unchanged[simp]:
  "qbs_forest (Quadratic_Blossom_Search_upd2 state) = qbs_forest state"
  "qbs_matching (Quadratic_Blossom_Search_upd2 state) = qbs_matching state"
  "qbs_hierarchy (Quadratic_Blossom_Search_upd2 state) = qbs_hierarchy state"
  "qbs_owners (Quadratic_Blossom_Search_upd2 state) = qbs_owners state"
  "qbs_neighbours (Quadratic_Blossom_Search_upd2 state) = qbs_neighbours state"
  "qbs_forest_edges (Quadratic_Blossom_Search_upd2 state) = qbs_forest_edges state"
  "qbs_cycle_edges (Quadratic_Blossom_Search_upd2 state) = qbs_cycle_edges state"
  "qbs_bases (Quadratic_Blossom_Search_upd2 state) = qbs_bases state"
  "qbs_parents (Quadratic_Blossom_Search_upd2 state) = qbs_parents state"
  "qbs_hints (Quadratic_Blossom_Search_upd2 state) = qbs_hints state"
  "qbs_fresh (Quadratic_Blossom_Search_upd2 state) = qbs_fresh state"
  "qbs_status (Quadratic_Blossom_Search_upd2 state) = qbs_status state"
  by(auto simp: Quadratic_Blossom_Search_upd2_def start_scan_def Let_def case_prod_beta)

lemma start_scan_even:
  "\<lbrakk>Quadratic_Blossom_Search_call_2_conds state; invar_adts state; invar_queue state\<rbrakk> \<Longrightarrow>
    effectively_even (Quadratic_Blossom_Search_upd2 state) = effectively_even state"
  by(auto simp: effectively_even_def start_scan_props(5))

lemma start_scan_quotient:
  "\<lbrakk>Quadratic_Blossom_Search_call_2_conds state; invar_adts state; invar_queue state\<rbrakk> \<Longrightarrow>
    quotient_graph (Quadratic_Blossom_Search_upd2 state) = quotient_graph state"
  by(simp only: quotient_graph_def projected_graph[OF subset_refl] start_scan_unchanged
    components_quot_graph[OF subset_refl start_scan_props(5)])

lemma invar_adts_holds_2[invar_holds_intros]:
  "\<lbrakk>Quadratic_Blossom_Search_call_2_conds state; invar_adts state; invar_queue state\<rbrakk>
    \<Longrightarrow> invar_adts (Quadratic_Blossom_Search_upd2 state)"
  using start_scan_source[of state]
  by(auto elim!: invar_adts_props intro!: invar_adts_intro
    simp: Quadratic_Blossom_Search_upd2_def start_scan_def Let_def case_prod_beta
      Work.queue_pop Components.find_invar)

lemma invar_current_holds_2[invar_holds_intros]:
  "\<lbrakk>Quadratic_Blossom_Search_call_2_conds state; invar_adts state; invar_queue state\<rbrakk>
    \<Longrightarrow> invar_current (Quadratic_Blossom_Search_upd2 state)"
  by(auto intro!: invar_current_intro simp: start_scan_props start_scan_source)

lemma invar_forest_holds_2[invar_holds_intros]:
  "\<lbrakk>Quadratic_Blossom_Search_call_2_conds state; invar_adts state; invar_queue state;
    invar_forest state\<rbrakk> \<Longrightarrow> invar_forest (Quadratic_Blossom_Search_upd2 state)"
  by(auto elim!: invar_forest_props intro!: invar_forest_intro simp: start_scan_quotient)

lemma invar_existence_holds_2[invar_holds_intros]:
  "\<lbrakk>Quadratic_Blossom_Search_call_2_conds state; invar_adts state; invar_queue state;
    invar_existence state\<rbrakk> \<Longrightarrow> invar_existence (Quadratic_Blossom_Search_upd2 state)"
  by(auto elim!: invar_existence_props intro!: invar_existence_intro simp: start_scan_quotient)

lemma invar_matching_projection_holds_2[invar_holds_intros]:
  "\<lbrakk>Quadratic_Blossom_Search_call_2_conds state; invar_adts state; invar_queue state;
    invar_matching_projection state\<rbrakk> \<Longrightarrow> invar_matching_projection (Quadratic_Blossom_Search_upd2 state)"
  by(simp only: invar_matching_projection_def start_scan_unchanged projected_graph[OF input_matching_props(2)]
    components_quot_graph[OF input_matching_props(2) start_scan_props(5)])

lemma invar_queue_holds_2[invar_holds_intros]:
  "\<lbrakk>Quadratic_Blossom_Search_call_2_conds state; invar_adts state; invar_queue state\<rbrakk>
    \<Longrightarrow> invar_queue (Quadratic_Blossom_Search_upd2 state)"
  using start_scan_source[of state]
  by(cases "queue_abstract (qbs_queue state)")
    (auto elim!: call_cond_elims simp: invar_queue_def start_scan_even start_scan_props)

lemma invar_representatives_holds_2[invar_holds_intros]:
  "\<lbrakk>Quadratic_Blossom_Search_call_2_conds state; invar_adts state; invar_queue state;
    invar_representatives state\<rbrakk> \<Longrightarrow> invar_representatives (Quadratic_Blossom_Search_upd2 state)"
  unfolding invar_representatives_def
  by(simp(no_asm_simp) add: start_scan_props(5) cong: conj_cong; blast)

lemma invar_components_holds_2[invar_holds_intros]:
  "\<lbrakk>Quadratic_Blossom_Search_call_2_conds state; invar_adts state; invar_queue state; invar_representatives
    state; invar_components state; hierarchy_invar (qbs_hierarchy state)\<rbrakk> \<Longrightarrow>
    invar_components (Quadratic_Blossom_Search_upd2 state)"
  using components_transport[of state "Quadratic_Blossom_Search_upd2 state"]
  by(auto simp: start_scan_props(5))

lemma invar_neighbours_holds_2[invar_holds_intros]:
  "invar_neighbours state \<Longrightarrow> invar_neighbours (Quadratic_Blossom_Search_upd2 state)"
  by(auto elim!: invar_neighbours_props intro!: invar_neighbours_intro)

lemma invar_fresh_holds_2[invar_holds_intros]:
  "invar_fresh state \<Longrightarrow> invar_fresh (Quadratic_Blossom_Search_upd2 state)"
  by(auto elim!: invar_fresh_props intro!: invar_fresh_intro)

lemma invar_hierarchy_size_holds_2[invar_holds_intros]:
  "invar_hierarchy_size state \<Longrightarrow> invar_hierarchy_size (Quadratic_Blossom_Search_upd2 state)"
  by(auto elim!: invar_hierarchy_size_props intro!: invar_hierarchy_size_intro)

lemma invar_result_holds_2[invar_holds_intros]:
  "Quadratic_Blossom_Search_call_2_conds state \<Longrightarrow> invar_result (Quadratic_Blossom_Search_upd2 state)"
  by(auto elim!: call_cond_elims simp: invar_result_def)

lemma invar_scanned_holds_2[invar_holds_intros]:
  "\<lbrakk>Quadratic_Blossom_Search_call_2_conds state; invar_adts state; invar_queue state;
    invar_scanned state\<rbrakk> \<Longrightarrow> invar_scanned (Quadratic_Blossom_Search_upd2 state)"
  by(auto simp: invar_scanned_def start_scan_props(5) start_scan_even pending_arcs_def
    split: Quadratic_Blossom_Search_status.splits)

lemma invar_annotations_holds_2[invar_holds_intros]:
  "\<lbrakk>Quadratic_Blossom_Search_call_2_conds state; invar_adts state; invar_queue state;
    invar_annotations state\<rbrakk> \<Longrightarrow> invar_annotations (Quadratic_Blossom_Search_upd2 state)"
  by(fastforce elim!: invar_annotations_props intro!: invar_annotations_intro
    simp: start_scan_props(5) Let_def simp del: input_edge_iff)

lemma invar_search_holds_2[invar_holds_intros]:
  "\<lbrakk>Quadratic_Blossom_Search_call_2_conds state; invar_search state\<rbrakk>
    \<Longrightarrow> invar_search (Quadratic_Blossom_Search_upd2 state)"
  by(auto elim!: invar_search_props intro!: invar_search_intro intro: invar_holds_intros
    simp: invar_recovering_structure_def)

lemma state_rel_exploration_holds_2[state_rel_holds_intros]:
  "\<lbrakk>Quadratic_Blossom_Search_call_2_conds state; invar_adts state; invar_queue state\<rbrakk>
    \<Longrightarrow> state_rel_exploration state (Quadratic_Blossom_Search_upd2 state)"
  by(auto intro!: state_rel_exploration_intro simp: start_scan_even)

lemma call_2_terminates[termination_intros]:
  "\<lbrakk>Quadratic_Blossom_Search_call_2_conds state; invar_adts state; invar_queue state\<rbrakk> \<Longrightarrow>
    (Quadratic_Blossom_Search_upd2 state, state) \<in> Quadratic_Blossom_Search_term_rel'"
  using start_scan_source[of state]
  by(cases "queue_abstract (qbs_queue state)")
    (auto intro!: mlex_less
      simp: Quadratic_Blossom_Search_term_rel'_def mlex_iff search_phase_measure_def
        search_edges_measure_def search_queue_measure_def start_scan_even start_scan_props)

subsection "Skipping an explored or odd target"

lemma input_arc_vertices[dest]:
  "(u,v) \<in> Graph.digraph_abs G \<Longrightarrow> u \<in> V0 \<and> v \<in> V0"
  using input_edge_vertices[of u v]
  by auto

lemma scanning_source:
  "\<lbrakk>scanning_edge state; invar_queue state\<rbrakk> \<Longrightarrow> qbs_current state \<in> V0"
  by(auto elim!: invar_queue_props simp: scanning_edge_def effectively_even_def)

lemma scanning_neighbour_remaining:
  "\<lbrakk>scanning_edge state; invar_adts state; invar_queue state\<rbrakk> \<Longrightarrow>
    scanned_neighbour state \<in> cursor_remaining (qbs_neighbours state) (qbs_current state)"
  using scanning_source[of state]
  by(auto elim!: invar_adts_props simp: scanning_edge_def Neighbours.idx_has Neighbours.idx_current)

lemma cursor_remaining_subset:
  "\<lbrakk>cursor_invar C; u \<in> V0\<rbrakk> \<Longrightarrow> cursor_remaining C u \<subseteq> cursor_abstract C u"
  using Neighbours.idx_partition_union[of C u]
  by blast

lemma scanning_neighbour:
  assumes "scanning_edge state" "invar_adts state" "invar_queue state" "invar_neighbours state"
  shows "scanned_neighbour state \<in> V0"
    "{qbs_current state, scanned_neighbour state} \<in> input_graph"
  using assms scanning_source[of state] scanning_neighbour_remaining[of state]
    cursor_remaining_subset[of "qbs_neighbours state" "qbs_current state"]
  by(auto elim!: invar_adts_props invar_neighbours_props simp: Pair_Graph.neighbourhood_def;
    blast intro: input_props(10)[THEN iffD1])+

lemma scanning_target_correct:
  assumes "scanning_edge state" "invar_adts state" "invar_queue state" "invar_neighbours state"
  shows "target_component state = representative state (scanned_neighbour state)"
    "uf_invar (snd (scanned_target state))"
    "w \<in> K \<Longrightarrow> uf_representative (snd (scanned_target state)) w =
      uf_representative (qbs_components state) w"
  using assms scanning_neighbour[of state] resolve_target_correct[of state "scanned_neighbour state"]
  by(auto elim!: invar_adts_props)

lemma scanning_representative[simp]:
  "\<lbrakk>scanning_edge state; invar_adts state; invar_queue state; invar_neighbours state; v \<in> K\<rbrakk> \<Longrightarrow>
    representative (Quadratic_Blossom_Search_upd4 state) v = representative state v"
  using scanning_target_correct(3)[of state v]
  by(auto simp: Quadratic_Blossom_Search_upd4_def)

lemma scanning_even[simp]:
  "\<lbrakk>scanning_edge state; invar_adts state; invar_queue state; invar_neighbours state\<rbrakk> \<Longrightarrow>
    effectively_even (Quadratic_Blossom_Search_upd4 state) = effectively_even state"
  by(auto simp: effectively_even_def Quadratic_Blossom_Search_upd4_def
    scanning_target_correct(3))

lemma scanning_cursor:
  assumes "scanning_edge state" "invar_adts state" "invar_queue state"
  shows "cursor_invar (qbs_neighbours state)" "qbs_current state \<in> V0"
    "cursor_remaining (qbs_neighbours state) (qbs_current state) \<noteq> {}"
  using assms scanning_source[of state]
  by(auto elim!: invar_adts_props simp: scanning_edge_def Neighbours.idx_has)

lemma scanning_remaining:
  "\<lbrakk>scanning_edge state; invar_adts state; invar_queue state\<rbrakk> \<Longrightarrow>
    cursor_remaining (cursor_move (qbs_neighbours state) (qbs_current state)) w =
      cursor_remaining (qbs_neighbours state) w -
        (if w = qbs_current state then {scanned_neighbour state} else {})"
  using scanning_cursor[of state]
  by(auto simp: Neighbours.idx_move_remaining Neighbours.idx_move_remaining_other split: if_splits)

lemma scanning_pending_arcs:
  "\<lbrakk>scanning_edge state; invar_adts state; invar_queue state; invar_neighbours state\<rbrakk> \<Longrightarrow>
    pending_arcs (Quadratic_Blossom_Search_upd4 state) =
      pending_arcs state - {(qbs_current state, scanned_neighbour state)}"
  by(simp only: pending_arcs_def scanning_even)
    (auto simp: Quadratic_Blossom_Search_upd4_def scanning_remaining split: if_splits)

lemma scanning_source_component:
  "\<lbrakk>scanning_edge state; invar_current state\<rbrakk> \<Longrightarrow>
    source_component state = representative state (qbs_current state)"
  by(auto simp: scanning_edge_def invar_current_def)

lemma skipped_edge:
  "\<lbrakk>Quadratic_Blossom_Search_call_4_conds state; invar_adts state; invar_queue state;
    invar_neighbours state; invar_forest state; invar_current state\<rbrakk> \<Longrightarrow>
    representative state (qbs_current state) = representative state (scanned_neighbour state) \<or>
      representative state (scanned_neighbour state) \<in> odd_ids state"
  using scanning_target_correct(1)[of state] scanning_source_component[of state]
    Forest.evens_and_odds(2)[of "mate_abstract (qbs_matching state)" "qbs_forest state"]
  by(auto elim!: invar_forest_props
    simp: Quadratic_Blossom_Search_call_4_conds_def Fset.fixed_univ_set_isin)

lemma invar_scanned_holds_4[invar_holds_intros]:
  "\<lbrakk>Quadratic_Blossom_Search_call_4_conds state; invar_adts state; invar_queue state;
    invar_neighbours state; invar_forest state; invar_current state; invar_scanned state\<rbrakk> \<Longrightarrow>
    invar_scanned (Quadratic_Blossom_Search_upd4 state)"
  using skipped_edge[of state] scanning_pending_arcs[of state]
    Forest.evens_and_odds(4)[of "mate_abstract (qbs_matching state)" "qbs_forest state"]
  by(auto elim!: invar_forest_props simp: invar_scanned_def
    Quadratic_Blossom_Search_call_4_conds_def scanning_edge_def
    Quadratic_Blossom_Search_upd4_def scanning_target_correct(3))

lemma invar_adts_holds_4[invar_holds_intros]:
  "\<lbrakk>scanning_edge state; invar_adts state; invar_queue state;
    invar_neighbours state\<rbrakk> \<Longrightarrow> invar_adts (Quadratic_Blossom_Search_upd4 state)"
  using scanning_target_correct(2)[of state] scanning_source[of state]
  by(auto elim!: invar_adts_props intro!: invar_adts_intro
    simp: Quadratic_Blossom_Search_upd4_def
      Neighbours.idx_move_invar)

lemma invar_neighbours_holds_4[invar_holds_intros]:
  "\<lbrakk>scanning_edge state; invar_adts state; invar_queue state;
    invar_neighbours state\<rbrakk> \<Longrightarrow> invar_neighbours (Quadratic_Blossom_Search_upd4 state)"
  by(auto simp: Quadratic_Blossom_Search_upd4_def invar_neighbours_def
    Neighbours.idx_move_abstract scanning_cursor)

lemma invar_current_holds_4[invar_holds_intros]:
  "\<lbrakk>scanning_edge state; invar_adts state; invar_queue state; invar_neighbours state; invar_current
    state\<rbrakk> \<Longrightarrow> invar_current (Quadratic_Blossom_Search_upd4 state)"
  using scanning_source[of state] scanning_representative[of state "qbs_current state"]
  by(simp only: invar_current_def) (auto simp: Quadratic_Blossom_Search_upd4_def)

lemma scanning_iterated:
  "\<lbrakk>scanning_edge state; invar_adts state; invar_queue state\<rbrakk> \<Longrightarrow>
    cursor_iterated (cursor_move (qbs_neighbours state) (qbs_current state)) w =
      cursor_iterated (qbs_neighbours state) w \<union>
        (if w = qbs_current state then {scanned_neighbour state} else {})"
  using scanning_cursor[of state]
  by(auto simp: Neighbours.idx_move_iterated Neighbours.idx_move_iterated_other split: if_splits)

lemma invar_queue_holds_4[invar_holds_intros]:
  "\<lbrakk>scanning_edge state; invar_adts state; invar_queue state;
    invar_neighbours state\<rbrakk> \<Longrightarrow> invar_queue (Quadratic_Blossom_Search_upd4 state)"
  using scanning_even[of state] scanning_iterated[of state] scanning_remaining[of state]
  by(auto simp: invar_queue_def
    Quadratic_Blossom_Search_upd4_def scanning_edge_def split: if_splits)

lemma scanning_quotient_graph[simp]:
  "\<lbrakk>scanning_edge state; invar_adts state; invar_queue state; invar_neighbours state\<rbrakk> \<Longrightarrow>
    quotient_graph (Quadratic_Blossom_Search_upd4 state) = quotient_graph state"
  using components_quot_graph[where A = input_graph and U = "snd (scanned_target state)" and state = state]
  by(simp only: quotient_graph_def projected_graph[OF subset_refl])
    (auto simp: Quadratic_Blossom_Search_upd4_def scanning_target_correct(3))

lemma invar_forest_holds_4[invar_holds_intros]:
  "\<lbrakk>scanning_edge state; invar_adts state; invar_queue state;
    invar_neighbours state; invar_forest state\<rbrakk> \<Longrightarrow>
    invar_forest (Quadratic_Blossom_Search_upd4 state)"
  by(simp only: invar_forest_def scanning_quotient_graph)
    (simp add: Quadratic_Blossom_Search_upd4_def)

lemma invar_matching_projection_holds_4[invar_holds_intros]:
  "\<lbrakk>scanning_edge state; invar_adts state; invar_queue state;
    invar_neighbours state; invar_matching_projection state\<rbrakk> \<Longrightarrow>
    invar_matching_projection (Quadratic_Blossom_Search_upd4 state)"
  using components_quot_graph[where A = "mate_abstract M0" and U = "snd (scanned_target state)" and state = state]
  by(simp only: invar_matching_projection_def projected_graph[OF input_matching_props(2)])
    (auto simp: Quadratic_Blossom_Search_upd4_def
      input_matching_props(2) scanning_target_correct(3))

lemma invar_representatives_holds_4[invar_holds_intros]:
  "\<lbrakk>scanning_edge state; invar_adts state; invar_queue state;
    invar_neighbours state; invar_representatives state\<rbrakk> \<Longrightarrow>
    invar_representatives (Quadratic_Blossom_Search_upd4 state)"
  by(auto simp: invar_representatives_def
    Quadratic_Blossom_Search_upd4_def scanning_target_correct(3); blast)

lemma invar_components_holds_4[invar_holds_intros]:
  "\<lbrakk>scanning_edge state; invar_adts state; invar_queue state; invar_neighbours state; invar_representatives
    state; invar_components state; hierarchy_invar (qbs_hierarchy state)\<rbrakk> \<Longrightarrow>
    invar_components (Quadratic_Blossom_Search_upd4 state)"
  using components_transport[of state "Quadratic_Blossom_Search_upd4 state"]
  by(auto simp: Quadratic_Blossom_Search_upd4_def scanning_target_correct(3))

lemma invar_annotations_holds_4[invar_holds_intros]:
  "\<lbrakk>scanning_edge state; invar_adts state; invar_queue state;
    invar_neighbours state; invar_annotations state\<rbrakk> \<Longrightarrow>
    invar_annotations (Quadratic_Blossom_Search_upd4 state)"
  by(fastforce simp: invar_annotations_def Quadratic_Blossom_Search_upd4_def
    Let_def scanning_target_correct(3) simp del: input_edge_iff)

lemma invar_fresh_holds_4[invar_holds_intros]:
  "\<lbrakk>scanning_edge state; invar_fresh state\<rbrakk> \<Longrightarrow>
    invar_fresh (Quadratic_Blossom_Search_upd4 state)"
  by(auto simp: invar_fresh_def Quadratic_Blossom_Search_upd4_def)

lemma invar_hierarchy_size_holds_4[invar_holds_intros]:
  "\<lbrakk>scanning_edge state; invar_hierarchy_size state\<rbrakk> \<Longrightarrow>
    invar_hierarchy_size (Quadratic_Blossom_Search_upd4 state)"
  by(auto simp: invar_hierarchy_size_def Quadratic_Blossom_Search_upd4_def)

lemma invar_existence_holds_4[invar_holds_intros]:
  "\<lbrakk>scanning_edge state; invar_adts state; invar_queue state;
    invar_neighbours state; invar_existence state\<rbrakk> \<Longrightarrow>
    invar_existence (Quadratic_Blossom_Search_upd4 state)"
  by(simp only: invar_existence_def scanning_quotient_graph)
    (simp add: Quadratic_Blossom_Search_upd4_def)

lemma invar_result_holds_4[invar_holds_intros]:
  "scanning_edge state \<Longrightarrow>
    invar_result (Quadratic_Blossom_Search_upd4 state)"
  by(auto simp: scanning_edge_def
    invar_result_def Quadratic_Blossom_Search_upd4_def)

lemma invar_search_holds_4[invar_holds_intros]:
  "\<lbrakk>Quadratic_Blossom_Search_call_4_conds state; invar_search state\<rbrakk> \<Longrightarrow>
    invar_search (Quadratic_Blossom_Search_upd4 state)"
  by(auto elim!: call_cond_elims invar_search_props intro!: invar_search_intro intro: invar_holds_intros call_cond_intros
    simp: invar_recovering_structure_def)
    (auto simp: Quadratic_Blossom_Search_upd4_def)

lemma state_rel_exploration_holds_4[state_rel_holds_intros]:
  "\<lbrakk>scanning_edge state; invar_adts state; invar_queue state;
    invar_neighbours state\<rbrakk> \<Longrightarrow> state_rel_exploration state (Quadratic_Blossom_Search_upd4 state)"
  using scanning_even[of state] scanning_remaining[of state]
  by(auto intro!: state_rel_exploration_intro
    simp: Quadratic_Blossom_Search_upd4_def
    split: if_splits)

subsection "Progress of edge scanning"

lemma cursor_remaining_finite:
  "\<lbrakk>invar_adts state; invar_neighbours state; u \<in> V0\<rbrakk> \<Longrightarrow>
    finite (cursor_remaining (qbs_neighbours state) u)"
  using Graph.finite_neighbourhoods[of G u]
  by(auto elim!: invar_adts_props invar_neighbours_props intro!: finite_subset[OF cursor_remaining_subset])

lemma scanning_edges_measure:
  "\<lbrakk>scanning_edge state; invar_adts state; invar_queue state; invar_neighbours state\<rbrakk>
    \<Longrightarrow> search_edges_measure (Quadratic_Blossom_Search_upd4 state) < search_edges_measure state"
  unfolding search_edges_measure_def
  using scanning_source[of state] scanning_neighbour_remaining[of state]
    cursor_remaining_finite[of state "qbs_current state"]
  by(intro sum_strict_mono_ex1)
    (auto simp: Quadratic_Blossom_Search_upd4_def scanning_remaining card_gt_0_iff split: if_splits
      intro!: diff_less intro: card_Diff1_less less_imp_le)

lemma call_4_terminates[termination_intros]:
  "\<lbrakk>Quadratic_Blossom_Search_call_4_conds state; invar_adts state; invar_queue state;
    invar_neighbours state\<rbrakk> \<Longrightarrow>
    (Quadratic_Blossom_Search_upd4 state, state) \<in> Quadratic_Blossom_Search_term_rel'"
  using scanning_edges_measure[of state]
  by(auto simp: Quadratic_Blossom_Search_call_4_conds_def Quadratic_Blossom_Search_term_rel'_def
    mlex_iff search_phase_measure_def Quadratic_Blossom_Search_upd4_def)

subsection "Reusing alternating forest path search"

lemma quotient_vertices:
  "Vs (quotient_graph state) \<subseteq> representative state ` V0"
  by(auto simp: quotient_graph_def Vs_def)

lemma quotient_doubleton:
  "dblton_graph (quotient_graph state)"
  by(auto simp: quotient_graph_def dblton_graph_def)

lemma quotient_graph_invar:
  "Undirected_Set_Graphs.graph_invar (quotient_graph state)"
  using quotient_vertices[of state] quotient_doubleton[of state]
  by(auto intro: finite_subset)

lemma search_matching:
  assumes "invar_forest state"
  shows "matching (mate_abstract (qbs_matching state))"
    "mate_abstract (qbs_matching state) \<subseteq> quotient_graph state"
  using assms Mate.matching(1)[of "quotient_graph state" "qbs_matching state"]
  by(auto elim!: invar_forest_props)

lemma quotient_active_vertices:
  "invar_representatives state \<Longrightarrow> Vs (quotient_graph state) \<subseteq> active_ids state"
  using quotient_vertices[of state]
  by(auto elim!: invar_representatives_props)

lemma quotient_search:
  "invar_forest state \<Longrightarrow>
    compute_alt_path fset_invar fset_abstract forest_odds forest_path forest_invar forest_roots
      forest_extend forest_empty K fset_empty forest_abstract forest_evens
      (quotient_graph state) (mate_abstract (qbs_matching state))"
  using search_matching[of state] quotient_graph_invar[of state]
  by(intro compute_alt_path.intro Forest.alternating_forest_ordinary_extension_spec_axioms
      match.intro graph_abs.intro match_axioms.intro)
    auto

lemma search_forest_paths:
  "\<lbrakk>invar_forest state; {x, y} \<in> quotient_graph state; x \<in> even_ids state; y \<in> even_ids state\<rbrakk> \<Longrightarrow>
    compute_alt_path_spec (quotient_graph state) (mate_abstract (qbs_matching state))
      (Some (forest_path (qbs_forest state) x, forest_path (qbs_forest state) y))"
  using quotient_search[of state]
  by(auto elim!: invar_forest_props intro: compute_alt_path.forest_paths_sound)

lemma scanning_quotient_edge:
  "\<lbrakk>scanning_edge state; invar_adts state; invar_queue state; invar_neighbours state; invar_current state;
    source_component state \<noteq> target_component state\<rbrakk> \<Longrightarrow> {source_component state,
    target_component state} \<in> quotient_graph state"
  unfolding quotient_graph_def
  by(intro CollectI, rule exI[of _ "qbs_current state"], rule exI[of _ "scanned_neighbour state"])
    (insert scanning_neighbour(2)[of state] scanning_source_component[of state]
      scanning_target_correct(1)[of state], auto)

subsection "Progress of extension and contraction"

lemma process_cycle_scan:
  "qbs_neighbours (process_cycle state cs k edge b) = qbs_neighbours state \<and>
    qbs_status (process_cycle state cs k edge b) = qbs_status state"
  unfolding process_cycle_def
  by(simp add: Let_def case_prod_beta,
      rule foldl_invar[where inv = "\<lambda>next. qbs_neighbours (snd next) = qbs_neighbours state \<and>
        qbs_status (snd next) = qbs_status state"])
    (auto simp: enqueue_vertex_def Let_def case_prod_beta split: if_splits)

lemma contraction_scan[simp]:
  "qbs_neighbours (Quadratic_Blossom_Search_upd7 state) =
    qbs_neighbours (Quadratic_Blossom_Search_upd4 state)"
  "qbs_status (Quadratic_Blossom_Search_upd7 state) = qbs_status state"
  by(auto simp: Quadratic_Blossom_Search_upd7_def contract_search_def
    process_cycle_scan Let_def case_prod_beta Quadratic_Blossom_Search_upd4_def)

lemma call_5_terminates[termination_intros]:
  "\<lbrakk>Quadratic_Blossom_Search_call_5_conds state; invar_adts state; invar_queue state;
    invar_neighbours state\<rbrakk> \<Longrightarrow>
    (Quadratic_Blossom_Search_upd5 state, state) \<in> Quadratic_Blossom_Search_term_rel'"
  using scanning_edges_measure[of state]
  by(auto simp: Quadratic_Blossom_Search_call_5_conds_def Quadratic_Blossom_Search_term_rel'_def
    mlex_iff search_phase_measure_def search_edges_measure_def
    Quadratic_Blossom_Search_upd5_def extend_search_def enqueue_vertex_def Let_def
    Quadratic_Blossom_Search_upd4_def)

lemmas finish_step_simps =
  Quadratic_Blossom_Search_call_6_conds_def Quadratic_Blossom_Search_upd6_def
  finish_search_def Let_def

lemma call_6_terminates[termination_intros]:
  "Quadratic_Blossom_Search_call_6_conds state \<Longrightarrow>
    (Quadratic_Blossom_Search_upd6 state, state) \<in> Quadratic_Blossom_Search_term_rel'"
  by(auto elim!: call_cond_elims intro!: mlex_less
    simp: Quadratic_Blossom_Search_term_rel'_def search_phase_measure_def scanning_edge_def finish_step_simps)

lemma call_7_terminates[termination_intros]:
  "\<lbrakk>Quadratic_Blossom_Search_call_7_conds state; invar_adts state; invar_queue state;
    invar_neighbours state\<rbrakk> \<Longrightarrow>
    (Quadratic_Blossom_Search_upd7 state, state) \<in> Quadratic_Blossom_Search_term_rel'"
  using scanning_edges_measure[of state]
  by(auto simp: Quadratic_Blossom_Search_call_7_conds_def Quadratic_Blossom_Search_term_rel'_def
    mlex_iff search_phase_measure_def search_edges_measure_def)

subsection "Finding an augmenting path"

lemma outward_edges_rev:
  "outward_edges state (rev p) = rev (map prod.swap (rootward_edges state p))"
  by(simp add: outward_edges_def rootward_edges_def tl_rev rev_map comp_def prod.swap_def split_def)

lemma forest_path_suffix:
  assumes "forest_invar M F" "v \<in> fset_abstract (forest_evens F)"
    "forest_path F a = prefix @ v # suffix"
  shows "forest_path F v = v # suffix"
  using assms Forest.get_path[OF assms(1,2) refl]
    Forest.get_path_prefices[OF assms(1), of prefix v suffix a "[]" "tl (forest_path F v)" v]
  by(cases "forest_path F v") (auto simp: walk_betw_def)

lemma forest_path_step:
  assumes "forest_invar M F" "a \<in> fset_abstract (forest_evens F)"
    "forest_path F a \<noteq> [a]"
  obtains x b P where "forest_path F a = a # x # b # P" "{a,x} \<in> M"
    "{x,b} \<notin> M" "b \<in> fset_abstract (forest_evens F)" "forest_path F b = b # P"
proof-
  note path = Forest.get_path[OF assms(1,2) refl]
  obtain x b P where shape: "forest_path F a = a # x # b # P"
    using path assms(3)
    by(cases "forest_path F a" rule: list_cases4) (auto simp: walk_betw_def)
  have "b \<in> fset_abstract (forest_evens F)"
    using path shape assms(1,2)
    by(auto simp: walk_betw_def insert_commute dest: Forest.higher_forest_properties(3))
  thus ?thesis
    using path shape assms(1)
    by(intro that[of x b P])
      (auto simp: alt_list_step intro!: forest_path_suffix[where prefix="[a,x]" and a=a])
qed

lemma rootward_edge_witnesses:
  assumes "invar_annotations state" "invar_forest state" "b \<in> even_ids state"
  shows "list_all2 (edge_witness state) (rootward_edges state (forest_path (qbs_forest state) b))
    (edges_of_vwalk (forest_path (qbs_forest state) b))"
  using assms(3)
proof(induction b rule: measure_induct_rule[where f = "\<lambda>b. length (forest_path (qbs_forest state) b)"])
  case (less b)
  show ?case
  proof(cases "forest_path (qbs_forest state) b = [b]")
    case True
    thus ?thesis
      by(simp add: rootward_edges_def)
  next
    case False
    then obtain x z P where path:
      "forest_path (qbs_forest state) b = b # x # z # P"
      "z \<in> even_ids state" "forest_path (qbs_forest state) z = z # P"
      using assms(2) less.prems
      by(blast elim: invar_forest_props forest_path_step)
    have invar: "forest_invar (mate_abstract (qbs_matching state)) (qbs_forest state)"
      using assms(2)
      by(auto elim!: invar_forest_props)
    have edges: "{b,x} \<in> mate_abstract (qbs_matching state)"
      "{x,z} \<in> forest_abstract (qbs_forest state)" "z \<noteq> b"
      using Forest.get_path[OF invar less.prems refl] path
      by(auto simp: walk_betw_def alt_list_step)
    have "edge_witness state (forest_edge state b) (b,x) \<and>
        edge_witness state (forest_edge state x) (x,z)"
      using assms(1) less.prems path(2) edges
      by(auto simp: invar_annotations_def)
    thus ?thesis
      using less.IH[of z] less.prems path
      by(simp add: rootward_edges_def)
  qed
qed

lemma edge_witness_swap[simp]:
  "edge_witness state (prod.swap e) (prod.swap xy) \<longleftrightarrow> edge_witness state e xy"
  by(auto simp: prod.swap_def insert_commute)

lemma invar_recovering_path_witnesses:
  "invar_recovering_path state p es \<longleftrightarrow>
    graph_augmenting_path (quotient_graph state) (mate_abstract (qbs_matching state)) p \<and>
    p \<noteq> [] \<and> list_all2 (edge_witness state) es (edges_of_vwalk p)"
  by(auto simp: invar_recovering_path_def list_all2_conv_all_nth
    edges_of_vwalk_length edges_of_vwalk_index Let_def split_def)

lemma prefix_edge_witnesses:
  assumes "invar_annotations state" "invar_forest state" "b \<in> even_ids state"
    "forest_path (qbs_forest state) b = p @ q"
  shows "list_all2 (edge_witness state) (rootward_edges state p) (edges_of_vwalk p)"
  using list_all2_takeI[OF rootward_edge_witnesses[OF assms(1-3)], where n = "length p - 1"]
  by(cases "p = []"; cases "q = []")
    (auto simp: assms(4) rootward_edges_def edges_of_vwalk_append_3
      butlast_append butlast_conv_take edges_of_vwalk_length take_map)

lemma reversed_prefix_edge_witnesses:
  assumes "invar_annotations s" "invar_forest s" "v \<in> even_ids s"
    "forest_path (qbs_forest s) v = p @ q"
  shows "list_all2 (edge_witness s) (outward_edges s (rev p)) (edges_of_vwalk (rev p))"
  using prefix_edge_witnesses[OF assms]
  by(simp only: outward_edges_rev edges_of_vwalk_rev rev_map
    list_all2_map1 list_all2_map2 edge_witness_swap list_all2_rev)

lemmas outward_edge_witnesses =
  reversed_prefix_edge_witnesses[where s = state and v = b
    and p = "forest_path (qbs_forest state) b" and q = "[]", simplified append_Nil2, OF _ _ _ refl]
  for state b

lemma edge_witness_members:
  "\<lbrakk>invar_representatives s; edge_witness s e (x,y)\<rbrakk> \<Longrightarrow>
    fst e \<in> hierarchy_members (qbs_hierarchy s) x \<and>
    snd e \<in> hierarchy_members (qbs_hierarchy s) y"
  using input_edge_vertices[of "fst e" "snd e"]
  by(auto elim!: invar_representatives_props simp del: input_edge_iff)

lemma witnessed_alternating_edge:
  assumes "list_all2 (edge_witness s) es (edges_of_vwalk p)"
    "alt_path (mate_abstract (qbs_matching s)) p" "i < length es"
  shows "{fst (es ! i), snd (es ! i)} \<in> mate_abstract M0 \<longleftrightarrow> odd i"
  using assms alternating_list_odd_index[OF assms(2), of i]
    alternating_list_even_index[OF assms(2), of i]
  by(cases "odd i")
    (auto simp: list_all2_conv_all_nth path_edges_set_of_pair_of_vwalk_edges
      set_of_pair_def case_prod_beta)

lemma joined_edge_witnesses:
  assumes "p \<noteq> []" "q \<noteq> []"
    "list_all2 (edge_witness state) es (edges_of_vwalk p)"
    "edge_witness state (u,v) (last p, hd q)"
    "list_all2 (edge_witness state) fs (edges_of_vwalk q)"
  shows "list_all2 (edge_witness state) (es @ [(u,v)] @ fs) (edges_of_vwalk (p @ q))"
  using assms
  by(simp only: edges_of_vwalk_append_2[OF assms(2)]
    edges_of_vwalk_snoc[OF assms(1)] append_assoc)
    (auto intro!: list_all2_appendI)

lemma scanning_source_even:
  "\<lbrakk>scanning_edge state; invar_queue state; invar_current state\<rbrakk> \<Longrightarrow>
    source_component state \<in> even_ids state"
  using scanning_source_component[of state]
  by(auto elim!: invar_queue_props simp: scanning_edge_def effectively_even_def)

lemma scanning_path_components:
  assumes "Quadratic_Blossom_Search_call_6_conds state \<or> Quadratic_Blossom_Search_call_7_conds state"
    "invar_forest state" "invar_queue state" "invar_current state"
  shows "source_component state \<in> even_ids state" "target_component state \<in> even_ids state"
  using assms scanning_source_even[of state]
    Forest.evens_and_odds(1)[of "mate_abstract (qbs_matching state)" "qbs_forest state"]
  by(auto elim!: invar_forest_props
    simp: Quadratic_Blossom_Search_call_6_conds_def Quadratic_Blossom_Search_call_7_conds_def
      Fset.fixed_univ_set_isin)

lemmas found_path_components = scanning_path_components[OF disjI1]
lemmas contraction_path_components = scanning_path_components[OF disjI2]

lemma scanning_path_spec:
  "\<lbrakk>Quadratic_Blossom_Search_call_6_conds state \<or> Quadratic_Blossom_Search_call_7_conds state;
    invar_adts state; invar_queue state;
    invar_neighbours state; invar_current state; invar_forest state\<rbrakk> \<Longrightarrow>
    compute_alt_path_spec (quotient_graph state) (mate_abstract (qbs_matching state))
      (Some (forest_path (qbs_forest state) (source_component state),
        forest_path (qbs_forest state) (target_component state)))"
  using scanning_path_components[of state] scanning_quotient_edge[of state]
  by(auto intro: search_forest_paths simp: Quadratic_Blossom_Search_call_6_conds_def
      Quadratic_Blossom_Search_call_7_conds_def)

lemmas found_path_spec = scanning_path_spec[OF disjI1]
lemmas contraction_path_spec = scanning_path_spec[OF disjI2]

lemma joined_forest_paths:
  "\<lbrakk>compute_alt_path_spec A M (Some (p,q)); last p \<noteq> last q\<rbrakk> \<Longrightarrow>
    graph_augmenting_path A M (rev p @ q)"
  by(auto dest: compute_alt_path_specD(2-13) common_suffix_disj_iff
    intro!: construct_path construct_aug_path')

lemma even_edge_unmatched:
  "\<lbrakk>invar_forest state; x \<in> even_ids state; y \<in> even_ids state\<rbrakk> \<Longrightarrow>
    {x,y} \<notin> mate_abstract (qbs_matching state)"
  using Forest.higher_forest_properties(2,3)[of "mate_abstract (qbs_matching state)" "qbs_forest state" x y]
    Forest.evens_and_odds(3,4)[of "mate_abstract (qbs_matching state)" "qbs_forest state"]
  by(blast elim: invar_forest_props)

lemma scanning_edge_witness:
  "\<lbrakk>scanning_edge state; invar_adts state; invar_queue state; invar_neighbours state; invar_current state;
    invar_matching_projection state; {source_component state, target_component state} \<notin> mate_abstract
    (qbs_matching state); source_component state \<noteq> target_component state\<rbrakk> \<Longrightarrow>
    edge_witness state (scanned_vertex state, scanned_neighbour state) (source_component state, target_component
    state)"
  using scanning_neighbour(2)[of state]
  by(auto simp: invar_matching_projection_def scanning_source_component scanning_target_correct(1))

lemma search_forest_path_head:
  assumes "invar_forest state" "b \<in> even_ids state"
  shows "forest_path (qbs_forest state) b \<noteq> []" "hd (forest_path (qbs_forest state) b) = b"
  using assms
  by(auto elim!: invar_forest_props dest: Forest.get_path[OF _ _ refl] simp: walk_betw_def)

lemma scanning_edge_witness_iff:
  "\<lbrakk>scanning_edge state; invar_adts state; invar_queue state; invar_neighbours state\<rbrakk> \<Longrightarrow>
    edge_witness (Quadratic_Blossom_Search_upd4 state) e xy \<longleftrightarrow> edge_witness state e xy"
  using input_edge_vertices[of "fst e" "snd e"]
  by(auto simp: Quadratic_Blossom_Search_upd4_def scanning_target_correct(3))

lemma found_path_recovering_invariant:
  "\<lbrakk>Quadratic_Blossom_Search_call_6_conds state; invar_adts state; invar_queue state;
    invar_neighbours state; invar_current state; invar_forest state;
    invar_matching_projection state; invar_annotations state\<rbrakk> \<Longrightarrow>
    invar_recovering_path state
      (rev (forest_path (qbs_forest state) (source_component state)) @
        forest_path (qbs_forest state) (target_component state))
      (outward_edges state (rev (forest_path (qbs_forest state) (source_component state))) @
        [(scanned_vertex state, scanned_neighbour state)] @
          rootward_edges state (forest_path (qbs_forest state) (target_component state)))"
  using joined_forest_paths[OF found_path_spec[of state]] found_path_components[of state]
    search_forest_path_head[of state] scanning_edge_witness[of state]
    even_edge_unmatched[of state "source_component state" "target_component state"]
  by(auto intro!: joined_edge_witnesses[simplified append_Cons append_Nil]
      intro: outward_edge_witnesses rootward_edge_witnesses
    simp: invar_recovering_path_witnesses Quadratic_Blossom_Search_call_6_conds_def last_rev
    simp del: input_edge_iff)

lemma scanning_path_recovering_invariant:
  "\<lbrakk>scanning_edge state; invar_adts state; invar_queue state; invar_neighbours state\<rbrakk> \<Longrightarrow>
    invar_recovering_path (Quadratic_Blossom_Search_upd4 state) p es \<longleftrightarrow>
      invar_recovering_path state p es"
  by(simp only: invar_recovering_path_witnesses list_all2_conv_all_nth
    scanning_quotient_graph scanning_edge_witness_iff)
    (simp add: Quadratic_Blossom_Search_upd4_def)

lemma finish_search_result:
  "invar_result (finish_search state u v p q) \<longleftrightarrow>
    invar_recovering_path state (rev p @ q)
      (outward_edges state (rev p) @ [(u,v)] @ rootward_edges state q)"
  by(simp add: invar_result_def finish_search_def invar_recovering_path_def
    quotient_graph_def Let_def)

lemma invar_result_holds_6[invar_holds_intros]:
  "\<lbrakk>Quadratic_Blossom_Search_call_6_conds state; invar_adts state; invar_queue state;
    invar_neighbours state; invar_current state; invar_forest state;
    invar_matching_projection state; invar_annotations state\<rbrakk> \<Longrightarrow>
    invar_result (Quadratic_Blossom_Search_upd6 state)"
  using found_path_recovering_invariant[of state]
  by(simp only: Quadratic_Blossom_Search_upd6_def finish_search_result;
      subst scanning_path_recovering_invariant)
    (auto simp: Quadratic_Blossom_Search_call_6_conds_def
      outward_edges_def rootward_edges_def Quadratic_Blossom_Search_upd4_def)

lemma finish_search_invariants:
  "\<And>state. invar_adts (Quadratic_Blossom_Search_upd4 state) =
    invar_adts (Quadratic_Blossom_Search_upd6 state)"
  "\<And>state. invar_forest (Quadratic_Blossom_Search_upd4 state) =
    invar_forest (Quadratic_Blossom_Search_upd6 state)"
  "\<And>state. invar_matching_projection (Quadratic_Blossom_Search_upd4 state) =
    invar_matching_projection (Quadratic_Blossom_Search_upd6 state)"
  "\<And>state. invar_representatives (Quadratic_Blossom_Search_upd4 state) =
    invar_representatives (Quadratic_Blossom_Search_upd6 state)"
  "\<And>state. invar_components (Quadratic_Blossom_Search_upd4 state) =
    invar_components (Quadratic_Blossom_Search_upd6 state)"
  "\<And>state. invar_neighbours (Quadratic_Blossom_Search_upd4 state) =
    invar_neighbours (Quadratic_Blossom_Search_upd6 state)"
  "\<And>state. invar_current (Quadratic_Blossom_Search_upd4 state) =
    invar_current (Quadratic_Blossom_Search_upd6 state)"
  "\<And>state. invar_queue (Quadratic_Blossom_Search_upd4 state) =
    invar_queue (Quadratic_Blossom_Search_upd6 state)"
  "\<And>state. invar_fresh (Quadratic_Blossom_Search_upd4 state) =
    invar_fresh (Quadratic_Blossom_Search_upd6 state)"
  "\<And>state. invar_annotations (Quadratic_Blossom_Search_upd4 state) =
    invar_annotations (Quadratic_Blossom_Search_upd6 state)"
  "\<And>state. invar_hierarchy_size (Quadratic_Blossom_Search_upd4 state) =
    invar_hierarchy_size (Quadratic_Blossom_Search_upd6 state)"
  "\<And>state. invar_existence (Quadratic_Blossom_Search_upd4 state) =
    invar_existence (Quadratic_Blossom_Search_upd6 state)"
  by(simp_all add: Quadratic_Blossom_Search_upd6_def finish_search_def Let_def
    invar_adts_def invar_forest_def invar_matching_projection_def invar_representatives_def invar_components_def
    invar_neighbours_def invar_current_def invar_queue_def invar_fresh_def invar_annotations_def
    invar_hierarchy_size_def invar_existence_def quotient_graph_def effectively_even_def)

lemmas finish_search_scanning =
  Quadratic_Blossom_Search_call_6_conds_def[THEN iffD1, THEN conjunct1]

lemmas invar_adts_holds_6[invar_holds_intros] =
  finish_search_scanning[THEN invar_adts_holds_4, unfolded finish_search_invariants]

lemmas invar_forest_holds_6[invar_holds_intros] =
  finish_search_scanning[THEN invar_forest_holds_4, unfolded finish_search_invariants]

lemmas invar_matching_projection_holds_6[invar_holds_intros] =
  finish_search_scanning[THEN invar_matching_projection_holds_4, unfolded finish_search_invariants]

lemmas invar_representatives_holds_6[invar_holds_intros] =
  finish_search_scanning[THEN invar_representatives_holds_4, unfolded finish_search_invariants]

lemmas invar_components_holds_6[invar_holds_intros] =
  finish_search_scanning[THEN invar_components_holds_4, unfolded finish_search_invariants]

lemmas invar_neighbours_holds_6[invar_holds_intros] =
  finish_search_scanning[THEN invar_neighbours_holds_4, unfolded finish_search_invariants]

lemmas invar_current_holds_6[invar_holds_intros] =
  finish_search_scanning[THEN invar_current_holds_4, unfolded finish_search_invariants]

lemmas invar_queue_holds_6[invar_holds_intros] =
  finish_search_scanning[THEN invar_queue_holds_4, unfolded finish_search_invariants]

lemmas invar_fresh_holds_6[invar_holds_intros] =
  finish_search_scanning[THEN invar_fresh_holds_4,
    THEN finish_search_invariants(9)[THEN iffD1]]

lemmas invar_annotations_holds_6[invar_holds_intros] =
  finish_search_scanning[THEN invar_annotations_holds_4, unfolded finish_search_invariants]

lemmas invar_hierarchy_size_holds_6[invar_holds_intros] =
  finish_search_scanning[THEN invar_hierarchy_size_holds_4,
    THEN finish_search_invariants(11)[THEN iffD1]]

lemmas invar_existence_holds_6[invar_holds_intros] =
  finish_search_scanning[THEN invar_existence_holds_4, unfolded finish_search_invariants]

lemma invar_scanned_holds_6[invar_holds_intros]:
  "invar_scanned (Quadratic_Blossom_Search_upd6 state)"
  by(simp add: Quadratic_Blossom_Search_upd6_def finish_search_def invar_scanned_def Let_def)

lemma invar_search_holds_6[invar_holds_intros]:
  "\<lbrakk>Quadratic_Blossom_Search_call_6_conds state; invar_search state\<rbrakk> \<Longrightarrow>
    invar_search (Quadratic_Blossom_Search_upd6 state)"
  by(auto elim!: invar_search_props intro!: invar_search_intro intro: invar_holds_intros
    simp: invar_recovering_structure_def)
    (auto simp: Quadratic_Blossom_Search_upd6_def finish_search_def Let_def
      Quadratic_Blossom_Search_upd4_def)

lemma state_rel_exploration_holds_6[state_rel_holds_intros]:
  "\<lbrakk>Quadratic_Blossom_Search_call_6_conds state; invar_adts state; invar_queue state;
    invar_neighbours state\<rbrakk> \<Longrightarrow> state_rel_exploration state (Quadratic_Blossom_Search_upd6 state)"
  using state_rel_exploration_holds_4[of state]
  by(auto simp: finish_step_simps state_rel_exploration_def effectively_even_def)

subsection "Extending the alternating forest"

lemma extension_vertices:
  assumes "Quadratic_Blossom_Search_call_5_conds state" "invar_search state"
  shows "source_component state \<in> even_ids state"
    "target_component state \<notin> even_ids state \<union> odd_ids state"
  using assms scanning_source_component[of state]
    Forest.evens_and_odds(1,2)[of "mate_abstract (qbs_matching state)" "qbs_forest state"]
  by(auto elim!: invar_search_props invar_forest_props invar_queue_props
    simp: Quadratic_Blossom_Search_call_5_conds_def effectively_even_def
      scanning_edge_def Fset.fixed_univ_set_isin)

lemma extension_target:
  "\<lbrakk>Quadratic_Blossom_Search_call_5_conds state; invar_search state\<rbrakk> \<Longrightarrow>
    target_component state \<in> active_ids state"
  using scanning_target_correct(1)[of state] scanning_neighbour(1)[of state]
  by(auto elim!: call_cond_elims invar_search_props invar_representatives_props)

lemma extension_partner:
  "\<lbrakk>Quadratic_Blossom_Search_call_5_conds state; invar_search state\<rbrakk> \<Longrightarrow>
    {target_component state, mate_partner (qbs_matching state) (target_component state)}
      \<in> mate_abstract (qbs_matching state)"
  using extension_target[of state] extension_vertices(2)[of state]
    Forest.roots(2)[of "mate_abstract (qbs_matching state)" "qbs_forest state"]
  by(auto elim!: invar_search_props invar_forest_props intro!: Mate.matching(5))

lemma extension_precond:
  "\<lbrakk>Quadratic_Blossom_Search_call_5_conds state; invar_search state\<rbrakk> \<Longrightarrow>
    Forest.forest_extension_precond (qbs_forest state) (mate_abstract (qbs_matching state))
      (source_component state) (target_component state)
      (mate_partner (qbs_matching state) (target_component state))"
  using extension_vertices[of state] extension_partner[of state]
    Mate.matching(1)[of "quotient_graph state" "qbs_matching state"] quotient_doubleton[of state]
  by(auto elim!: invar_search_props invar_forest_props intro!: Forest.forest_extension_precondI; blast)

lemma non_even_component:
  "\<lbrakk>invar_representatives state; b \<in> active_ids state - even_ids state\<rbrakk> \<Longrightarrow>
    {u \<in> V0. representative state u = b} = {b} \<and> b \<in> V0 \<and> representative state b = b"
  by(auto elim!: invar_representatives_props; blast)

lemma non_even_component_eq:
  "\<lbrakk>invar_representatives state; b \<in> active_ids state - even_ids state; u \<in> V0\<rbrakk> \<Longrightarrow>
    (representative state u = b) = (u = b)"
  using non_even_component[of state b]
  by(auto simp: set_eq_iff)

lemma non_even_representative:
  "\<lbrakk>invar_representatives state; u \<in> V0;
    representative state u \<in> active_ids state - even_ids state\<rbrakk> \<Longrightarrow> representative state u = u"
  using non_even_component_eq[of state "representative state u" u]
  by auto

lemma extension_partner_vertices:
  "\<lbrakk>Quadratic_Blossom_Search_call_5_conds state; invar_search state\<rbrakk> \<Longrightarrow>
    mate_partner (qbs_matching state) (target_component state) \<in>
      active_ids state - (even_ids state \<union> odd_ids state)"
  using extension_precond[of state] search_matching(2)[of state] quotient_active_vertices[of state]
  by(auto elim!: invar_search_props simp: Forest.forest_extension_precond_def Vs_def; blast)

lemma extension_original_vertices:
  assumes "Quadratic_Blossom_Search_call_5_conds state" "invar_search state"
  shows "target_component state = scanned_neighbour state"
    "mate_partner (qbs_matching state) (target_component state) \<in> V0"
    "representative state (mate_partner (qbs_matching state) (target_component state)) =
      mate_partner (qbs_matching state) (target_component state)"
  using assms scanning_neighbour(1)[of state] scanning_target_correct(1)[of state]
    extension_vertices(2)[of state] extension_target[of state] extension_partner_vertices[of state]
  by(auto elim!: invar_search_props dest: non_even_component non_even_representative
    simp: Quadratic_Blossom_Search_call_5_conds_def)

lemma queue_batch_space:
  assumes "invar_queue state" "distinct xs" "set xs \<subseteq> V0 - effectively_even state"
  shows "length (queue_abstract (qbs_queue state)) + length xs \<le> cap"
proof-
  have "length (queue_abstract (qbs_queue state) @ xs) =
    card (set (queue_abstract (qbs_queue state) @ xs))"
    using assms
    by(intro distinct_card[symmetric]) (auto elim!: invar_queue_props; blast)
  also have "... \<le> card V0"
    using assms
    by(intro card_mono)
      (auto elim!: invar_queue_props simp: effectively_even_def)
  finally show ?thesis
    by(auto intro: order_trans[OF _ input_props(5)])
qed

lemma queue_space:
  "\<lbrakk>invar_queue state; v \<in> V0 - effectively_even state\<rbrakk> \<Longrightarrow>
    length (queue_abstract (qbs_queue state)) < cap"
  using queue_batch_space[of state "[v]"]
  by auto

lemma non_even_preimage:
  "\<lbrakk>invar_representatives state; B \<subseteq> active_ids state - even_ids state\<rbrakk> \<Longrightarrow>
    {u \<in> V0. representative state u \<in> B} = B"
  by(auto dest: non_even_component non_even_representative)

lemma extension_new_even:
  "\<lbrakk>Quadratic_Blossom_Search_call_5_conds state; invar_search state\<rbrakk> \<Longrightarrow>
    mate_partner (qbs_matching state) (target_component state) \<in> V0 - effectively_even state"
  using extension_original_vertices(2,3)[of state] extension_partner_vertices[of state]
  by(auto simp: effectively_even_def)

lemma extension_forest_sets:
  assumes "Quadratic_Blossom_Search_call_5_conds state" "invar_search state"
  shows "even_ids (Quadratic_Blossom_Search_upd5 state) =
      insert (mate_partner (qbs_matching state) (target_component state)) (even_ids state)"
    "odd_ids (Quadratic_Blossom_Search_upd5 state) = insert (target_component state) (odd_ids state)"
  using Forest.forest_extend(3,4)[OF extension_precond[OF assms]]
  by(simp_all add: Quadratic_Blossom_Search_upd5_def extend_search_def enqueue_vertex_def Let_def
    Quadratic_Blossom_Search_upd4_def)

lemma extension_representative:
  "\<lbrakk>Quadratic_Blossom_Search_call_5_conds state; invar_search state; u \<in> V0\<rbrakk> \<Longrightarrow>
    representative (Quadratic_Blossom_Search_upd5 state) u = representative state u"
  by(auto elim!: call_cond_elims invar_search_props
    simp: Quadratic_Blossom_Search_upd5_def extend_search_def enqueue_vertex_def Let_def)

lemma extension_even:
  assumes "Quadratic_Blossom_Search_call_5_conds state" "invar_search state"
  shows "effectively_even (Quadratic_Blossom_Search_upd5 state) =
    insert (mate_partner (qbs_matching state) (target_component state)) (effectively_even state)"
  using assms extension_partner_vertices[of state] extension_original_vertices(2)[of state]
  by(auto elim!: invar_search_props
    simp: effectively_even_def extension_forest_sets[OF assms]
      extension_representative[OF assms] non_even_component_eq)



lemma extend_search_queue:
  assumes "invar_adts state" "invar_queue state"
    "mate_partner (qbs_matching state) y \<in> V0 - effectively_even state"
    "effectively_even (extend_search state u v x y) =
      insert (mate_partner (qbs_matching state) y) (effectively_even state)"
  shows "invar_queue (extend_search state u v x y)"
  using assms queue_space[OF assms(2,3)]
  by(auto elim!: invar_adts_props
    simp: invar_queue_def extend_search_def enqueue_vertex_def Let_def Work.queue_push)





lemma extend_search_unchanged[simp]:
  "invar_matching_projection (extend_search state u v x y) = invar_matching_projection state"
  "invar_components (extend_search state u v x y) = invar_components state"
  "invar_neighbours (extend_search state u v x y) = invar_neighbours state"
  "invar_current (extend_search state u v x y) = invar_current state"
  "invar_fresh (extend_search state u v x y) = invar_fresh state"
  "invar_hierarchy_size (extend_search state u v x y) = invar_hierarchy_size state"
  "invar_existence (extend_search state u v x y) = invar_existence state"
  "invar_result (extend_search state u v x y) = invar_result state"
  by(simp_all add: extend_search_def enqueue_vertex_def Let_def
    invar_matching_projection_def invar_components_def invar_neighbours_def invar_current_def invar_fresh_def invar_hierarchy_size_def invar_existence_def invar_result_def
    quotient_graph_def invar_recovering_path_def split: Quadratic_Blossom_Search_status.splits)

context
  fixes state
  assumes extension: "Quadratic_Blossom_Search_call_5_conds state" "invar_search state"
begin

lemmas extension_props = extension[unfolded Quadratic_Blossom_Search_call_5_conds_def invar_search_def
  invar_recovering_structure_def]

lemma invar_forest_holds_5[invar_holds_intros]:
  "invar_forest (Quadratic_Blossom_Search_upd5 state)"
proof-
  have "invar_forest (Quadratic_Blossom_Search_upd4 state)"
    by(auto intro: invar_forest_holds_4 simp: extension_props)
  thus ?thesis
    using extension extension_precond[of state] extension_target[of state]
      scanning_quotient_edge[of state] search_matching(2)[of state]
      extension_partner_vertices[of state] scanning_quotient_graph[of state]
      Forest.forest_extend[OF extension_precond[OF extension]]
    by(auto simp: invar_forest_def Quadratic_Blossom_Search_upd5_def extend_search_def
        enqueue_vertex_def Let_def Quadratic_Blossom_Search_upd4_def quotient_graph_def
        extension_props Forest.forest_extension_precond_def)
qed

lemma invar_queue_holds_5[invar_holds_intros]:
  "invar_queue (Quadratic_Blossom_Search_upd5 state)"
  using extension extension_new_even[of state] extension_even[of state]
  unfolding Quadratic_Blossom_Search_upd5_def
  by(auto elim!: invar_search_props intro!: extend_search_queue intro: invar_holds_intros
    simp: Quadratic_Blossom_Search_call_5_conds_def extension_props)
    (auto simp: Quadratic_Blossom_Search_upd4_def)

lemma invar_adts_holds_5[invar_holds_intros]:
  "invar_adts (Quadratic_Blossom_Search_upd5 state)"
  using extension invar_adts_holds_4[of state] extension_new_even[of state]
    extension_original_vertices[of state] scanning_neighbour(1)[of state]
    queue_space[of state "mate_partner (qbs_matching state) (target_component state)"]
  by(auto elim!: invar_search_props invar_adts_props intro!: invar_adts_intro
    simp: Quadratic_Blossom_Search_upd5_def extend_search_def enqueue_vertex_def Let_def
      Quadratic_Blossom_Search_upd4_def Work.queue_push Edges.fixed_univ_map_upd_invar extension_props)

lemma invar_matching_projection_holds_5[invar_holds_intros]:
  "invar_matching_projection (Quadratic_Blossom_Search_upd5 state)"
  by(auto intro: invar_holds_intros simp: Quadratic_Blossom_Search_upd5_def extension_props)

lemma invar_components_holds_5[invar_holds_intros]:
  "invar_components (Quadratic_Blossom_Search_upd5 state)"
  by(auto intro: invar_holds_intros simp: Quadratic_Blossom_Search_upd5_def extension_props)

lemma invar_neighbours_holds_5[invar_holds_intros]:
  "invar_neighbours (Quadratic_Blossom_Search_upd5 state)"
  by(auto intro: invar_holds_intros simp: Quadratic_Blossom_Search_upd5_def extension_props)

lemma invar_current_holds_5[invar_holds_intros]:
  "invar_current (Quadratic_Blossom_Search_upd5 state)"
  by(auto intro: invar_holds_intros simp: Quadratic_Blossom_Search_upd5_def extension_props)

lemma invar_fresh_holds_5[invar_holds_intros]:
  "invar_fresh (Quadratic_Blossom_Search_upd5 state)"
  by(auto intro: invar_holds_intros simp: Quadratic_Blossom_Search_upd5_def extension_props)

lemma invar_hierarchy_size_holds_5[invar_holds_intros]:
  "invar_hierarchy_size (Quadratic_Blossom_Search_upd5 state)"
  by(auto intro: invar_holds_intros simp: Quadratic_Blossom_Search_upd5_def extension_props)

lemma invar_existence_holds_5[invar_holds_intros]:
  "invar_existence (Quadratic_Blossom_Search_upd5 state)"
  by(auto intro: invar_holds_intros simp: Quadratic_Blossom_Search_upd5_def extension_props)

lemma invar_result_holds_5[invar_holds_intros]:
  "invar_result (Quadratic_Blossom_Search_upd5 state)"
  by(auto intro: invar_holds_intros simp: Quadratic_Blossom_Search_upd5_def extension_props)

end

lemma extend_search_representatives:
  "\<lbrakk>invar_representatives state; even_ids state \<subseteq> even_ids (extend_search state u v x y)\<rbrakk> \<Longrightarrow>
    invar_representatives (extend_search state u v x y)"
  by(auto simp: invar_representatives_def extend_search_def enqueue_vertex_def Let_def; blast)

lemma invar_representatives_holds_5[invar_holds_intros]:
  "\<lbrakk>Quadratic_Blossom_Search_call_5_conds state; invar_search state\<rbrakk> \<Longrightarrow>
    invar_representatives (Quadratic_Blossom_Search_upd5 state)"
  using Forest.forest_extend(3)[OF extension_precond[of state]]
  unfolding Quadratic_Blossom_Search_upd5_def
  by(auto elim!: invar_search_props intro!: extend_search_representatives intro: invar_holds_intros
    simp: Quadratic_Blossom_Search_call_5_conds_def)
    (auto simp: Quadratic_Blossom_Search_upd4_def extend_search_def enqueue_vertex_def Let_def)

lemma pending_unscanned:
  "\<lbrakk>invar_adts before; invar_queue before; invar_neighbours before;
    u \<in> V0 - effectively_even before; {u,v} \<in> input_graph;
    cursor_remaining (qbs_neighbours after) u = cursor_remaining (qbs_neighbours before) u;
    u \<in> effectively_even after\<rbrakk> \<Longrightarrow> (u,v) \<in> pending_arcs after"
  using Neighbours.idx_partition_union[of "qbs_neighbours before" u]
  by(auto elim!: invar_adts_props invar_queue_props invar_neighbours_props
    simp: Pair_Graph.neighbourhood_def pending_arcs_def; blast)

lemma extension_pending_arcs:
  "\<lbrakk>Quadratic_Blossom_Search_call_5_conds state; invar_search state\<rbrakk> \<Longrightarrow> pending_arcs
    (Quadratic_Blossom_Search_upd5 state) = pending_arcs (Quadratic_Blossom_Search_upd4 state) \<union>
    {mate_partner (qbs_matching state) (target_component state)} \<times> cursor_remaining (qbs_neighbours
    (Quadratic_Blossom_Search_upd4 state)) (mate_partner (qbs_matching state) (target_component state))"
  using extension_even[of state] scanning_even[of state]
  by(auto elim!: invar_search_props
    simp: pending_arcs_def Quadratic_Blossom_Search_upd5_def extend_search_def enqueue_vertex_def
      Let_def Quadratic_Blossom_Search_upd4_def Quadratic_Blossom_Search_call_5_conds_def)



lemma extension_new_arcs:
  assumes "Quadratic_Blossom_Search_call_5_conds state" "invar_search state"
    "{mate_partner (qbs_matching state) (target_component state), v} \<in> input_graph"
  shows "(mate_partner (qbs_matching state) (target_component state), v) \<in>
    pending_arcs (Quadratic_Blossom_Search_upd5 state)"
  by(rule pending_unscanned[where before = "Quadratic_Blossom_Search_upd4 state"])
    (insert assms assms(2)[unfolded invar_search_def]
      extension_new_even[OF assms(1,2)] extension_even[OF assms(1,2)],
      auto intro: invar_holds_intros simp: Quadratic_Blossom_Search_call_5_conds_def
        Quadratic_Blossom_Search_upd5_def extend_search_def enqueue_vertex_def Let_def)

lemma extension_component_eq:
  assumes "Quadratic_Blossom_Search_call_5_conds state" "invar_search state" "u \<in> V0"
  shows "(representative state u = mate_partner (qbs_matching state) (target_component state)) =
    (u = mate_partner (qbs_matching state) (target_component state))"
  using assms non_even_component_eq[of state
    "mate_partner (qbs_matching state) (target_component state)" u]
    extension_partner_vertices[OF assms(1,2)]
  by(auto elim!: invar_search_props)

lemma invar_scanned_holds_5[invar_holds_intros]:
  assumes "Quadratic_Blossom_Search_call_5_conds state" "invar_search state"
  shows "invar_scanned (Quadratic_Blossom_Search_upd5 state)"
proof-
  have "invar_scanned state"
    using assms(2)
    by(auto elim!: invar_search_props)
  moreover have "qbs_status state = Quadratic_Searching"
    "qbs_status (Quadratic_Blossom_Search_upd5 state) = Quadratic_Searching"
    using assms(1)
    by(auto simp: Quadratic_Blossom_Search_call_5_conds_def scanning_edge_def
      Quadratic_Blossom_Search_upd5_def extend_search_def enqueue_vertex_def Let_def
      Quadratic_Blossom_Search_upd4_def)
  moreover have "pending_arcs state - {(qbs_current state, scanned_neighbour state)} \<subseteq>
    pending_arcs (Quadratic_Blossom_Search_upd5 state)"
    using assms extension_pending_arcs[of state] scanning_pending_arcs[of state]
    by(auto elim!: invar_search_props simp: Quadratic_Blossom_Search_call_5_conds_def)
  moreover have "representative state (scanned_neighbour state) = target_component state"
    using assms scanning_target_correct(1)[of state]
    by(auto elim!: invar_search_props simp: Quadratic_Blossom_Search_call_5_conds_def)
  ultimately show ?thesis
    using extension_vertices(2)[OF assms]
  proof(auto simp: invar_scanned_def assms
        extension_representative extension_forest_sets
        extension_component_eq
      intro: extension_new_arcs, goal_cases)
    case pending: (1 u v)
    have "(u, v) \<in> pending_arcs state \<or> (v, u) \<in> pending_arcs state"
      using pending(1)[rule_format, OF pending(6,7)] pending(10-14)
      by auto
    thus ?case
      using pending(4,5,8,12,14,15)
      by auto
  qed
qed

lemma state_rel_exploration_holds_5[state_rel_holds_intros]:
  "\<lbrakk>Quadratic_Blossom_Search_call_5_conds state; invar_search state\<rbrakk> \<Longrightarrow>
    state_rel_exploration state (Quadratic_Blossom_Search_upd5 state)"
  using extension_even[of state] scanning_remaining[of state]
  by(auto elim!: invar_search_props intro!: state_rel_exploration_intro
    simp: Quadratic_Blossom_Search_call_5_conds_def Quadratic_Blossom_Search_upd5_def
      extend_search_def enqueue_vertex_def Let_def Quadratic_Blossom_Search_upd4_def
    split: if_splits)



lemma non_even_matching_edge:
  assumes "invar_matching_projection state" "invar_representatives state"
    "x \<in> active_ids state - even_ids state" "y \<in> active_ids state - even_ids state"
    "{x, y} \<in> mate_abstract (qbs_matching state)"
  shows "{x, y} \<in> mate_abstract M0"
proof-
  obtain u v where "{u, v} \<in> mate_abstract M0"
    "{x, y} = {representative state u, representative state v}" "u \<in> V0" "v \<in> V0"
    using assms(1,5) input_matching_props(3)
    by(auto elim!: invar_matching_projection_props simp: Vs_def; blast)
  thus ?thesis
    using assms(2-4) non_even_representative[of state u] non_even_representative[of state v]
    by(auto simp: doubleton_eq_iff insert_commute)
qed

lemma forest_path_vertices:
  "\<lbrakk>forest_invar M F; v \<in> fset_abstract (forest_evens F)\<rbrakk> \<Longrightarrow>
    set (forest_path F v) \<subseteq> fset_abstract (forest_evens F) \<union> fset_abstract (forest_odds F)"
  using Forest.get_path[of M F v "forest_path F v"] Forest.evens_and_odds(3)[of M F]
  by(auto simp: walk_betw_def dest: subset_path_Vs; blast)

lemma search_matching_doubleton:
  "invar_forest state \<Longrightarrow> dblton_graph (mate_abstract (qbs_matching state))"
  using search_matching(2)[of state] quotient_doubleton[of state]
  by auto



lemma extension_edge_witness_iff:
  "\<lbrakk>Quadratic_Blossom_Search_call_5_conds state; invar_search state\<rbrakk> \<Longrightarrow>
    edge_witness (Quadratic_Blossom_Search_upd5 state) e xy \<longleftrightarrow> edge_witness state e xy"
  using scanning_edge_witness_iff[of state e xy]
  by(auto elim!: invar_search_props
    simp: Quadratic_Blossom_Search_call_5_conds_def Quadratic_Blossom_Search_upd5_def
      extend_search_def enqueue_vertex_def Let_def)

lemma extension_edge_lookups:
  assumes "Quadratic_Blossom_Search_call_5_conds state" "invar_search state"
  shows "forest_edge (Quadratic_Blossom_Search_upd5 state)
      (mate_partner (qbs_matching state) (target_component state)) =
        (mate_partner (qbs_matching state) (target_component state), target_component state)"
    "forest_edge (Quadratic_Blossom_Search_upd5 state) (target_component state) =
      (scanned_neighbour state, qbs_current state)"
    "a \<in> even_ids state \<union> odd_ids state \<Longrightarrow>
      forest_edge (Quadratic_Blossom_Search_upd5 state) a = forest_edge state a"
  using assms extension_precond[of state] extension_original_vertices(2)[of state]
    extension_target[of state] non_even_component[of state "target_component state"]
  by(auto elim!: invar_search_props invar_adts_props invar_forest_props
    dest: Forest.evens_and_odds(1,2) Fset.fixed_univ_set_universe
    simp: Forest.forest_extension_precond_def Quadratic_Blossom_Search_upd5_def
      extend_search_def enqueue_vertex_def Let_def Quadratic_Blossom_Search_upd4_def
      Edges.fixed_univ_map_upd_invar Edges.fixed_univ_map_upd)

lemma invar_annotations_holds_5[invar_holds_intros]:
  assumes "Quadratic_Blossom_Search_call_5_conds state" "invar_search state"
  shows "invar_annotations (Quadratic_Blossom_Search_upd5 state)"
proof-
  let ?s = "Quadratic_Blossom_Search_upd5 state"
  let ?F = "qbs_forest state"
  let ?M = "mate_abstract (qbs_matching state)"
  let ?x = "source_component state"
  let ?y = "target_component state"
  let ?z = "mate_partner (qbs_matching state) ?y"
  let ?E = "forest_extend ?F ?x ?y ?z"
  note pre = extension_precond[OF assms, unfolded Forest.forest_extension_precond_def]
  note extension = Forest.forest_extend[OF extension_precond[OF assms]]
  have annotations: "invar_annotations state"
    using assms(2)
    by(auto elim: invar_search_props)
  have "{?y, ?z} \<in> mate_abstract M0"
    using assms extension_target[of state] extension_vertices(2)[of state]
      extension_partner_vertices[of state] extension_partner[of state]
    by(auto elim!: invar_search_props intro!: non_even_matching_edge)
  then have "edge_witness state (?z, ?y) (?z, ?y)"
    using input_matching_props(2) extension_partner[of state] extension_original_vertices(3)[of state]
      assms extension_target[of state] extension_vertices(2)[of state] non_even_component[of state ?y]
    by(auto elim!: invar_search_props simp: insert_commute simp del: input_edge_iff)
  moreover have "edge_witness state (scanned_neighbour state, qbs_current state) (?y, ?x)"
    using assms extension_precond[of state] scanning_edge_witness[of state]
      edge_witness_swap[where state = state and e = "(qbs_current state, scanned_neighbour state)"
        and xy = "(?x, ?y)"]
    by(auto elim!: invar_search_props
      simp: Quadratic_Blossom_Search_call_5_conds_def Forest.forest_extension_precond_def)
  ultimately have added: "edge_witness state (?z,?y) (?z,?y)"
    "edge_witness state (scanned_neighbour state, qbs_current state) (?y,?x)"
    by auto
  show ?thesis
  proof(unfold invar_annotations_def, intro ballI allI impI, elim conjE)
    fix a v c
    assume "a \<in> even_ids ?s" "{a,v} \<in> mate_abstract (qbs_matching ?s)"
      "{v,c} \<in> forest_abstract (qbs_forest ?s)" "c \<in> even_ids ?s" "c \<noteq> a"
    hence path: "{a,v} \<in> ?M" "{v,c} \<in> forest_abstract ?F \<union> {{?x,?y},{?y,?z}}" "a \<noteq> c"
      "v \<in> insert ?y (odd_ids state)" "c \<in> insert ?z (even_ids state)"
      "a \<in> insert ?z (even_ids state)"
      using Forest.higher_forest_properties(3)[OF extension(1), of c v]
      by(auto simp: Quadratic_Blossom_Search_upd5_def extend_search_def enqueue_vertex_def
        Let_def Quadratic_Blossom_Search_upd4_def extension(2-4) insert_commute)
    have fresh: "?y \<notin> Vs (forest_abstract ?F)" "?z \<notin> Vs (forest_abstract ?F)"
      using pre Forest.evens_and_odds(3)[OF pre[THEN conjunct1]]
      by blast+
    have "v = ?y \<longleftrightarrow> a = ?z"
      using pre path(1) doubleton_in_matching(1)[of ?M ?y ?z a]
        doubleton_in_matching(2)[of ?M ?y ?z v]
      by(auto simp: insert_commute)
    moreover have "?y \<notin> even_ids state" "?y \<noteq> ?z"
      using pre
      by auto
    ultimately consider (new) "a = ?z" "v = ?y" "c = ?x"
      | (old) "a \<in> even_ids state" "v \<in> odd_ids state"
        "{v,c} \<in> forest_abstract ?F" "c \<in> even_ids state"
      using path(2-6) fresh
      by(atomize_elim, cases "v = ?y")
        (auto simp: doubleton_eq_iff dest: edges_are_Vs edges_are_Vs_2)
    hence "edge_witness state (forest_edge ?s a) (a,v) \<and>
      edge_witness state (forest_edge ?s v) (v,c)"
      using annotations[unfolded invar_annotations_def, rule_format, of a v c] path(1,3) added
      by cases (auto simp: extension_edge_lookups[OF assms])
    thus "edge_witness ?s (forest_edge ?s a) (a,v) \<and>
      edge_witness ?s (forest_edge ?s v) (v,c)"
      using extension_edge_witness_iff[OF assms, of "forest_edge ?s a" "(a,v)"]
        extension_edge_witness_iff[OF assms, of "forest_edge ?s v" "(v,c)"]
      by blast
  qed
qed

lemma invar_search_holds_5[invar_holds_intros]:
  "\<lbrakk>Quadratic_Blossom_Search_call_5_conds state; invar_search state\<rbrakk> \<Longrightarrow>
    invar_search (Quadratic_Blossom_Search_upd5 state)"
  by(auto intro!: invar_search_intro intro: invar_holds_intros)
    (auto elim!: invar_search_props
      simp: Quadratic_Blossom_Search_upd5_def extend_search_def enqueue_vertex_def Let_def
        Quadratic_Blossom_Search_upd4_def)
subsection "Component unions"

lemma active_ids_subset:
  "hierarchy_invar (qbs_hierarchy state) \<Longrightarrow> active_ids state \<subseteq> hierarchy_ids (qbs_hierarchy state)"
  by(auto simp: Hierarchy.max_ids)

lemma representative_active:
  assumes "invar_representatives state" "invar_components state"
    "hierarchy_invar (qbs_hierarchy state)" "c \<in> active_ids state"
  shows "representative state c = c"
proof-
  have id: "c \<in> hierarchy_ids (qbs_hierarchy state)"
    using assms(3,4) active_ids_subset[of state]
    by auto
  then obtain u where member: "u \<in> hierarchy_members (qbs_hierarchy state) c"
    using Hierarchy.odd_sets[OF assms(3), of c]
    by fastforce
  have "uf_representative (qbs_components state) u = uf_representative (qbs_components state) c"
    using assms(2) id member
    by(auto elim!: invar_components_props)
  thus ?thesis
    using assms(1,4) member
    by(auto elim!: invar_representatives_props)
qed

lemma union_cycle_representatives:
  "\<lbrakk>uf_invar U; b \<in> K; set cs \<subseteq> K\<rbrakk> \<Longrightarrow>
    (let U' = foldl (\<lambda>U c. uf_union U b c) U cs;
         R = insert (uf_representative U b) (uf_representative U ` set cs)
     in uf_invar U' \<and> uf_representative U' b \<in> R \<and>
       (\<forall>x \<in> K. uf_representative U' x =
         (if uf_representative U x \<in> R then uf_representative U' b
          else uf_representative U x)))"
proof(induction cs rule: rev_induct)
  case Nil
  then show ?case
    by simp
next
  case (snoc c cs)
  let ?U = "foldl (\<lambda>U c. uf_union U b c) U cs"
  let ?R = "insert (uf_representative U b) (uf_representative U ` set cs)"
  have "set cs \<subseteq> K"
    using snoc.prems(3)
    by auto
  note ih = snoc.IH[OF snoc.prems(1,2) this, unfolded Let_def]
  note facts = ih[THEN conjunct1] ih[THEN conjunct2, THEN conjunct1]
  note reps = ih[THEN conjunct2, THEN conjunct2, rule_format]
  have "uf_representative (uf_union ?U b c) b \<in> insert (uf_representative U c) ?R"
    using facts reps[of c] snoc.prems(2,3) Components.union_representative[of ?U b c]
    by(auto split: if_splits)
  moreover have "\<forall>x\<in>K. uf_representative (uf_union ?U b c) x =
      (if uf_representative U x \<in> insert (uf_representative U c) ?R
       then uf_representative (uf_union ?U b c) b else uf_representative U x)"
  proof(intro ballI)
    fix x
    assume x: "x \<in> K"
    show "uf_representative (uf_union ?U b c) x =
      (if uf_representative U x \<in> insert (uf_representative U c) ?R
       then uf_representative (uf_union ?U b c) b else uf_representative U x)"
      using facts(2) reps[OF x] reps[of c] snoc.prems(3)
        Components.union_representatives[OF facts(1) snoc.prems(2) _ x]
      by(auto split: if_splits)
  qed
  ultimately show ?case
    using Components.union_invar[OF facts(1) snoc.prems(2)] snoc.prems(3)
    by(simp add: Let_def insert_commute)
qed

abbreviation "cycle_witness state cs k edge i c \<equiv>
  if Suc i < k then case forest_edge state (cs ! Suc i) of (x, y) \<Rightarrow> (y, x)
  else if Suc i = k then edge else forest_edge state c"

abbreviation "cycle_iteration state cs k edge b \<equiv>
  \<lambda>(i, next) c.
       let witness = cycle_witness state cs k edge i c;
           next = (if fset_isin (forest_odds (qbs_forest state)) c
             then enqueue_vertex next c else next)
       in (Suc i, next \<lparr>
         qbs_components := uf_union (qbs_components next) b c,
         qbs_cycle_edges := edge_update (qbs_cycle_edges next) c witness,
         qbs_parents := link_update (qbs_parents next) c (b, i)\<rparr>)"

lemma cycle_iteration_fields:
  "let next = foldl (cycle_iteration state cs k edge b) (i, s) xs in
    qbs_components (snd next) = foldl (\<lambda>U c. uf_union U b c) (qbs_components s) xs \<and>
    qbs_owners (snd next) = qbs_owners s \<and>
    qbs_queue (snd next) = foldl (\<lambda>Q c.
      if fset_isin (forest_odds (qbs_forest state)) c then queue_push Q c else Q) (qbs_queue s) xs \<and>
    (fst next, qbs_cycle_edges (snd next)) =
      foldl (\<lambda>(i, B) c. (Suc i, edge_update B c (cycle_witness state cs k edge i c)))
        (i, qbs_cycle_edges s) xs \<and>
    (fst next, qbs_parents (snd next)) =
      foldl (\<lambda>(i, N) c. (Suc i, link_update N c (b, i))) (i, qbs_parents s) xs"
  by(induction xs arbitrary: i s)
    (auto simp: Let_def case_prod_beta enqueue_vertex_def split: if_splits)

lemma process_cycle_components:
  assumes "uf_invar (qbs_components state)" "b \<in> K" "set cs \<subseteq> K" "u \<in> K"
  defines "R \<equiv> insert (uf_representative (qbs_components state) b)
    (uf_representative (qbs_components state) ` set cs)"
  shows "uf_representative (qbs_components (process_cycle state cs k edge b)) b \<in> R" (is ?root)
    "uf_representative (qbs_components (process_cycle state cs k edge b)) u =
      (if uf_representative (qbs_components state) u \<in> R
       then uf_representative (qbs_components (process_cycle state cs k edge b)) b
       else uf_representative (qbs_components state) u)" (is ?representatives)
    "uf_invar (qbs_components (process_cycle state cs k edge b))" (is ?invar)
    "uf_representative (qbs_components (process_cycle state cs k edge b)) b \<in> K" (is ?closed)
    "qbs_owners (process_cycle state cs k edge b) =
      owner_update (qbs_owners state)
        (uf_representative (qbs_components (process_cycle state cs k edge b)) b) b" (is ?owners)
proof-
  let ?U = "foldl (\<lambda>U c. uf_union U b c) (qbs_components state) cs"
  note union = union_cycle_representatives[OF assms(1-3), unfolded Let_def]
  note inv = union[THEN conjunct1]
  note root = union[THEN conjunct2, THEN conjunct1, folded R_def]
  note rep = union[THEN conjunct2, THEN conjunct2, rule_format, OF assms(4)]
  show ?root ?representatives ?invar ?closed ?owners
    using root rep inv assms(2) Components.representative_closed[of ?U b]
      cycle_iteration_fields[of k state cs edge b 0 state cs]
    by(simp_all add: R_def process_cycle_def Let_def case_prod_beta
      Components.find_invar Components.find_result Components.find_representatives[OF inv] assms(1-4))
qed

lemma process_cycle_owner:
  assumes "uf_invar (qbs_components state)" "owner_invar (qbs_owners state)"
    "b \<in> K" "set cs \<subseteq> K" "u \<in> K"
  shows "uf_invar (qbs_components (process_cycle state cs k edge b))"
    "owner_invar (qbs_owners (process_cycle state cs k edge b))"
    "representative (process_cycle state cs k edge b) u =
      (if uf_representative (qbs_components state) u \<in>
          insert (uf_representative (qbs_components state) b)
            (uf_representative (qbs_components state) ` set cs)
       then b else representative state u)"
  using process_cycle_components[OF assms(1,3-5), where k = k and edge = edge] assms(2)
  by(auto simp: Owners.fixed_univ_map_upd_invar Owners.fixed_univ_map_upd split: if_splits)

lemma process_cycle_frame:
  "qbs_current (process_cycle state cs k edge b) = qbs_current state"
  unfolding process_cycle_def
  by(simp add: Let_def case_prod_beta,
      rule foldl_invar)
    (auto simp: enqueue_vertex_def Let_def case_prod_beta split: if_splits)

lemma process_cycle_representative:
  assumes "invar_adts state" "invar_representatives state" "invar_components state"
    "invar_hierarchy_size state" "hierarchy_invar (qbs_hierarchy state)"
    "set cs \<subseteq> active_ids state" "b \<in> K - hierarchy_ids (qbs_hierarchy state)" "u \<in> V0"
  shows "representative (process_cycle state cs k edge b) u =
    (if representative state u \<in> set cs then b else representative state u)"
proof-
  have "set cs \<subseteq> K" "u \<in> K" "b \<in> K"
    using assms active_ids_subset[of state] input_props(3)
    by(auto elim!: invar_representatives_props)
  moreover have "uf_representative (qbs_components state) b = b"
    using assms(3,7)
    by(auto elim!: invar_components_props)
  moreover have "uf_representative (qbs_components state) u \<in>
      insert b (uf_representative (qbs_components state) ` set cs)
    \<longleftrightarrow> representative state u \<in> set cs"
  proof-
    have "uf_representative (qbs_components state) u \<in> hierarchy_ids (qbs_hierarchy state)"
      using assms(3,4,8)
      by(auto elim!: invar_components_props invar_hierarchy_size_props)
    moreover have "(uf_representative (qbs_components state) u = uf_representative (qbs_components state) c
        \<longleftrightarrow> representative state u = c)" if "c \<in> set cs" for c
      using assms(2,3,8) active_ids_subset[OF assms(5)]
        representative_active[OF assms(2,3,5) subsetD[OF assms(6) that]]
      by(fastforce simp only: invar_representatives_def invar_components_def)
    ultimately show ?thesis
      using assms(7)
      by auto
  qed
  ultimately show ?thesis
    using process_cycle_owner(3)[of state b cs u k edge]
      assms(1)
    by(auto elim!: invar_adts_props)
qed

lemma queue_push_fold:
  "\<lbrakk>queue_invar Q; length (queue_abstract Q) + length xs \<le> cap\<rbrakk> \<Longrightarrow>
    queue_invar (foldl queue_push Q xs) \<and>
    queue_abstract (foldl queue_push Q xs) = queue_abstract Q @ xs"
  by(induction xs arbitrary: Q) (auto simp: Work.queue_push)

lemma process_cycle_queue:
  "qbs_queue (process_cycle state cs k edge b) =
    foldl queue_push (qbs_queue state)
      (filter (fset_isin (forest_odds (qbs_forest state))) cs)"
  using cycle_iteration_fields[of k state cs edge b 0 state cs]
  by(simp add: process_cycle_def Let_def case_prod_beta foldl_filter_if)

subsection "Recovering invariants for the hierarchy"

lemma process_cycle_maps:
  "qbs_cycle_edges (process_cycle state cs k edge b) =
    snd (foldl (\<lambda>(i, B) c. (Suc i, edge_update B c (cycle_witness state cs k edge i c)))
      (0, qbs_cycle_edges state) cs)"
  "qbs_parents (process_cycle state cs k edge b) =
    Routing.record_parents (qbs_parents state) cs b"
  using cycle_iteration_fields[of k state cs edge b 0 state cs]
  by(auto simp: process_cycle_def Routing.record_parents_def Let_def case_prod_beta
    dest!: arg_cong[where f = snd])

lemma process_cycle_maps_props:
  assumes "edge_invar (qbs_cycle_edges state)" "set cs \<subseteq> K" "distinct cs"
  shows "edge_invar (qbs_cycle_edges (process_cycle state cs k edge b))"
    "c \<notin> set cs \<Longrightarrow> edge_lookup (qbs_cycle_edges (process_cycle state cs k edge b)) c =
      edge_lookup (qbs_cycle_edges state) c"
    "i < length cs \<Longrightarrow> edge_lookup (qbs_cycle_edges (process_cycle state cs k edge b)) (cs ! i) =
      cycle_witness state cs k edge i (cs ! i)"
  using Edges.indexed_map_updates[OF assms,
      where f = "cycle_witness state cs k edge" and n = 0]
  by(auto simp: process_cycle_maps Let_def)


lemma hierarchy_relation_merge:
  "Hierarchy.blossom_forest_merge_precond H cs b \<Longrightarrow>
    hierarchy_relation (hierarchy_merge H cs b) = hierarchy_relation H \<union> set cs \<times> {b}"
  using Hierarchy.merge_spec(2)[of H cs b] Hierarchy.children_merge[of H cs b]
    Hierarchy.blossom_forest_merge_precondD(5)[of H cs b]
  by(auto simp: hierarchy_relation_def)

lemma recovery_tree_merge:
  assumes "recovery_tree H" "Hierarchy.blossom_forest_merge_precond H cs b"
  shows "recovery_tree (hierarchy_merge H cs b)"
proof-
  note pre = Hierarchy.blossom_forest_merge_precondD[OF assms(2)]
  note merge = Hierarchy.merge_spec[OF assms(2)]
  have children: "set cs \<subseteq> hierarchy_ids H"
    using pre(2) Hierarchy.max_ids[OF pre(1)]
    by auto
  note old_wf = assms(1)[unfolded recovery_tree_def, THEN conjunct2, THEN conjunct1]
  have new_wf: "wf (set cs \<times> {b})"
    by(rule wf_subset[OF wf_measure[of "\<lambda>c. if c = b then 1 else 0"]])
      (insert children pre(5), auto)
  have "Domain (hierarchy_relation H) \<inter> Range (set cs \<times> {b}) = {}"
    using hierarchy_children_ids[OF assms(1)] pre(5)
    by(auto simp: hierarchy_relation_def)
  hence wf: "wf (hierarchy_relation (hierarchy_merge H cs b))"
    unfolding hierarchy_relation_merge[OF assms(2)]
    by(rule wf_Un[OF old_wf new_wf])
  note nodes = assms(1)[unfolded recovery_tree_def, THEN conjunct2, THEN conjunct2]
  show ?thesis
    unfolding recovery_tree_def
  proof(simp only: merge(2) finite_insert wf
      assms(1)[unfolded recovery_tree_def, THEN conjunct1] simp_thms,
      intro ballI, goal_cases)
    case (1 a)
    show ?case
      using 1 nodes[THEN bspec, of a] hierarchy_children_ids[OF assms(1), of a]
        pre children hierarchy_top_disjoint[OF pre(1,2)]
      by(cases "a = b"; auto simp: Let_def merge(2,4)
        Hierarchy.children_merge[OF assms(2)] pairwise_def; blast)
  qed
qed

lemma invar_navigation_merge:
  assumes "Hierarchy.blossom_forest_merge_precond H cs b" "recovery_tree H"
    "invar_navigation H D N" "hierarchy_ids H \<subseteq> K" "b \<in> K"
  shows "invar_navigation (hierarchy_merge H cs b)
    (base_update D b (base_lookup D (hd cs))) (Routing.record_parents N cs b)"
proof-
  note pre = Hierarchy.blossom_forest_merge_precondD[OF assms(1)]
  note merge = Hierarchy.merge_spec[OF assms(1)]
  let ?N = "Routing.record_parents N cs b"
  have maps: "base_invar D" "link_invar N"
    using assms(3)
    by(auto simp: invar_navigation_def)
  have children: "set cs \<subseteq> hierarchy_ids H" "set cs \<subseteq> K" "cs \<noteq> []"
    using pre(2,3) assms(4) Hierarchy.max_ids[OF pre(1)]
    by auto
  note parents = Routing.record_parents_props[OF maps(2) children(2) pre(4)]
  note navigation = assms(3)[unfolded invar_navigation_def]
  note base_update = Routing.Bases.fixed_univ_map_upd[OF maps(1) assms(5)]
  show ?thesis
  proof(rule invar_navigation_intro,
      simp_all only: Routing.Bases.fixed_univ_map_upd_invar[OF maps(1) assms(5)] parents(1), goal_cases)
    case 1
    show ?case
      using navigation children pre(5) hierarchy_children_ids[OF assms(2)]
      by(auto simp: merge(2,4) Hierarchy.children_merge[OF assms(1)] base_update
          split: if_splits; blast intro: hd_in_set)
  next
    case 2
    have "link_lookup ?N c = link_lookup N c"
      if "a \<in> hierarchy_ids H" "c \<in> set (hierarchy_children H a)" for a c
      using hierarchy_child_not_top[OF pre(1) assms(2) that] pre(2)
      by(intro parents(2)) auto
    thus ?case
      using navigation parents(3)
      by(auto simp: merge(2) Hierarchy.children_merge[OF assms(1)])
  qed
qed

lemma invar_recovering_structure_merge:
  assumes "invar_recovering_structure H B D N" "Hierarchy.blossom_forest_merge_precond H cs b"
    "hierarchy_ids H \<subseteq> K" "b \<in> K" "edge_invar B'"
    "\<And>c. c \<notin> set cs \<Longrightarrow> edge_lookup B' c = edge_lookup B c"
    "\<And>i. i < length cs \<Longrightarrow>
      fst (edge_lookup B' (cs ! i)) \<in> hierarchy_members H (cs ! i) \<and>
      snd (edge_lookup B' (cs ! i)) \<in> hierarchy_members H (cs ! (Suc i mod length cs)) \<and>
      {fst (edge_lookup B' (cs ! i)), snd (edge_lookup B' (cs ! i))} \<in> input_graph \<and>
      ({fst (edge_lookup B' (cs ! i)), snd (edge_lookup B' (cs ! i))} \<in> mate_abstract M0 \<longleftrightarrow> odd i)"
  shows "invar_recovering_structure (hierarchy_merge H cs b) B'
    (base_update D b (base_lookup D (hd cs))) (Routing.record_parents N cs b)"
proof-
  note pre = Hierarchy.blossom_forest_merge_precondD[OF assms(2)]
  note merge = Hierarchy.merge_spec[OF assms(2)]
  have old: "recovery_tree H" "invar_navigation H D N" "base_invar D"
    using assms(1)
    by(auto simp: invar_recovering_structure_def invar_navigation_def)
  have children: "set cs \<subseteq> hierarchy_ids H"
    using pre(2) Hierarchy.max_ids[OF pre(1)]
    by auto
  note indices = subsetD[OF _ nth_mem]
  have next_indices: "\<lbrakk>set xs \<subseteq> hierarchy_ids H; i < length xs\<rbrakk> \<Longrightarrow>
    xs ! (Suc i mod length xs) \<in> hierarchy_ids H" for xs i
    by(rule indices, assumption, rule mod_less_divisor) arith
  note recovering = assms(1)[unfolded invar_recovering_structure_def]
  have odd_union: "odd (card (\<Union>(hierarchy_members H ` set cs)))"
    using Hierarchy.odd_sets[OF merge(1), of b]
    by(simp add: merge(2,4))
  have coverage: "Vs (mate_abstract M0\<lbrakk>\<Union>(hierarchy_members H ` set cs)\<rbrakk>) =
      \<Union>(hierarchy_members H ` set cs) - {base_lookup D (hd cs)}"
  proof(rule matching_coverage_union[OF input_matching_props(1)
      dblton_graph_subset[OF input_graph_doubleton input_matching_props(2)] pre(4,6)
      hierarchy_top_disjoint[OF pre(1,2)] _ odd_union,
      where W = "\<lambda>i. edge_lookup B' (cs ! i)"], goal_cases)
    case (1 c)
    show ?case
      using 1 recovering children
      by(auto simp: graph_inter_Vs_def)
  next
    case (2 i)
    have "i < length cs" "Suc i < length cs"
      using 2
      by arith+
    thus ?case
      using assms(7)[of i] 2(2)
      by auto
  qed
  have unchanged: "edge_lookup B' c = edge_lookup B c"
    if "a \<in> hierarchy_ids H" "c \<in> set (hierarchy_children H a)" for a c
    using hierarchy_child_not_top[OF pre(1) old(1) that] pre(2)
    by(intro assms(6)) auto
  show ?thesis
    unfolding invar_recovering_structure_def
  proof(simp only: merge(1) assms(5) recovery_tree_merge[OF old(1) assms(2)]
      invar_navigation_merge[OF assms(2) old(1,2) assms(3,4)] simp_thms,
      intro conjI, goal_cases)
    case 1
    show ?case
      using recovering pre(5) coverage
      by(auto simp: merge(2,4) graph_inter_Vs_def
        Routing.Bases.fixed_univ_map_upd[OF old(3) assms(4)])
  next
    case 2
    show ?case
    proof(intro ballI, goal_cases)
      case (1 a)
      show ?case
        using 1 assms(7) children pre(3,5) recovering
          hierarchy_children_ids[OF old(1), of a]
        by(cases "a = b"; auto simp: merge(2,4) Let_def case_prod_beta unchanged[of a]
          Hierarchy.children_merge[OF assms(2)] split: if_splits dest: indices next_indices)
    qed
  qed
qed

lemma cycle_witness_index:
  "\<lbrakk>c1 \<noteq> []; c2 \<noteq> []; cs = c1 @ butlast (rev c2); i < length cs\<rbrakk> \<Longrightarrow>
    (outward_edges state c1 @ [edge] @ rootward_edges state (rev c2)) ! i =
      cycle_witness state cs (length c1) edge i (cs ! i)"
  by(auto simp: outward_edges_def rootward_edges_def nth_append nth_tl nth_butlast nth_Cons'
    split: if_splits)

lemma closed_cycle_edge:
  assumes "i < length cs"
  shows "edges_of_vwalk (cs @ [hd cs]) ! i = (cs ! i, cs ! (Suc i mod length cs))"
proof(cases "Suc i < length cs")
  case True
  show ?thesis
    using assms True
    by(simp add: edges_of_vwalk_index nth_append)
next
  case False
  have "cs \<noteq> []" "Suc i = length cs"
    using assms False
    by(auto; arith)+
  thus ?thesis
    using assms
    by(simp add: edges_of_vwalk_index nth_append hd_conv_nth)
qed

subsection "Contracting a blossom"

lemma common_suffix_blossom:
  assumes "compute_alt_path_spec A M (Some (p, q))" "last p = last q"
    "longest_disj_sfx (rev p) (rev q) = (c1, c2)" "matching M"
  shows "blossom A M (rev (drop (length c1) p)) (c1 @ rev c2)"
proof-
  have prefixes: "(Some (rev c1), Some (rev c2)) = longest_disj_pfx p q"
    using assms longest_disj_pfx_rev[of A M p q]
    by simp
  obtain r where "p = rev c1 @ r" "q = rev c2 @ r"
    by(rule common_suffix[OF assms(1) prefixes])
  hence "match_blossom M (rev (drop (length c1) p)) (c1 @ rev c2)"
    using common_pfxs_form_match_blossom'[OF prefixes] assms(4) compute_alt_path_specD(2-10)[OF assms(1)]
    by auto
  moreover have "path A (rev (drop (length c1) p) @ c1 @ rev c2)"
    using pfxs_path[OF prefixes] compute_alt_path_specD(11-13)[OF assms(1)]
    by simp
  ultimately show ?thesis
    by simp
qed

lemma common_suffix_geometry:
  assumes "compute_alt_path_spec A M (Some (p, q))" "last p = last q"
    "longest_disj_sfx (rev p) (rev q) = (c1, c2)"
  shows "c1 \<noteq> []" "c2 \<noteq> []" "hd c1 = hd c2"
    "p = rev c1 @ drop (length c1) p" "q = rev c2 @ drop (length c1) p"
    "set (butlast (rev c1)) \<inter> set (butlast (rev c2)) = {}"
proof-
  have prefixes: "(Some (rev c1), Some (rev c2)) = longest_disj_pfx p q"
    using assms longest_disj_pfx_rev[of A M p q]
      by simp
  obtain r where "p = rev c1 @ r" "q = rev c2 @ r"
    by(rule common_suffix[OF assms(1) prefixes])
  thus "c1 \<noteq> []" "c2 \<noteq> []" "hd c1 = hd c2"
    "p = rev c1 @ drop (length c1) p" "q = rev c2 @ drop (length c1) p"
    "set (butlast (rev c1)) \<inter> set (butlast (rev c2)) = {}"
    using first_pfx_nempty[OF prefixes] snd_pfx_nempty[OF prefixes]
      pfx_common_end[OF prefixes] disj_pfx_are_disj_3[OF prefixes]
    by(auto simp: last_rev)
qed


lemma common_suffix_cycle:
  assumes "compute_alt_path_spec A M (Some (p, q))" "last p = last q"
    "longest_disj_sfx (rev p) (rev q) = (c1, c2)" "matching M"
  defines "cs \<equiv> c1 @ butlast (rev c2)"
  shows "distinct cs" "odd (length cs)" "3 \<le> length cs"
    "set cs = set (c1 @ rev c2)" "alt_path M cs"
proof-
  let ?C = "c1 @ rev c2"
  have cycle: "match_blossom M (rev (drop (length c1) p)) ?C"
    using common_suffix_blossom[OF assms(1-4)]
      by simp
  have shape: "cs = butlast ?C"
    using common_suffix_geometry(2)[OF assms(1-3)]
      by(simp add: cs_def butlast_append)
  show "distinct cs" "odd (length cs)" "3 \<le> length cs"
    using match_blossomD(2,3)[OF cycle] odd_cycle_even_verts[of ?C]
      odd_cycle_length_verts_ge_4[of ?C]
        by(auto simp: shape)
  show "set cs = set ?C"
    using common_suffix_geometry(1-3)[OF assms(1-3)]
    by(cases c1; cases c2; auto simp: cs_def)
  show "alt_path M cs"
    using alt_path_split_off_last[OF match_blossom_alt_cycle[OF cycle]]
      by(simp add: shape)
qed

context
  fixes state c1 c2 b fresh
  assumes contraction: "Quadratic_Blossom_Search_call_7_conds state" "invar_search state"
    "longest_disj_sfx (rev (forest_path (qbs_forest state) (source_component state)))
      (rev (forest_path (qbs_forest state) (target_component state))) = (c1, c2)"
    "queue_pop (qbs_fresh state) = (b, fresh)"
begin

lemma contraction_spec:
  "compute_alt_path_spec (quotient_graph state) (mate_abstract (qbs_matching state))
    (Some (forest_path (qbs_forest state) (source_component state),
      forest_path (qbs_forest state) (target_component state)))"
  using contraction
    by(auto intro: contraction_path_spec elim!: invar_search_props)

lemma contraction_geometry:
  "c1 \<noteq> []" "c2 \<noteq> []" "hd c1 = hd c2"
  "forest_path (qbs_forest state) (source_component state) =
    rev c1 @ drop (length c1) (forest_path (qbs_forest state) (source_component state))"
  "forest_path (qbs_forest state) (target_component state) =
    rev c2 @ drop (length c1) (forest_path (qbs_forest state) (source_component state))"
  "set (butlast (rev c1)) \<inter> set (butlast (rev c2)) = {}"
  using common_suffix_geometry[OF contraction_spec] contraction(1,3)
  by(auto simp: Quadratic_Blossom_Search_call_7_conds_def)

lemma contraction_blossom:
  "blossom (quotient_graph state) (mate_abstract (qbs_matching state))
    (rev (drop (length c1) (forest_path (qbs_forest state) (source_component state))))
    (c1 @ rev c2)"
  using common_suffix_blossom[OF contraction_spec] contraction
  by(auto elim!: call_cond_elims invar_search_props intro: search_matching(1))

lemma contraction_cycle:
  "distinct (c1 @ butlast (rev c2))" "odd (length (c1 @ butlast (rev c2)))"
  "3 \<le> length (c1 @ butlast (rev c2))"
  "set (c1 @ butlast (rev c2)) = set (c1 @ rev c2)"
  "alt_path (mate_abstract (qbs_matching state)) (c1 @ butlast (rev c2))"
  using common_suffix_cycle[OF contraction_spec] contraction search_matching(1)[of state]
  by(auto elim!: call_cond_elims invar_search_props)

lemma contraction_cycle_active:
  "set (c1 @ butlast (rev c2)) \<subseteq> active_ids state"
  using subset_path_Vs[OF blossomD(1)[OF contraction_blossom]]
    contraction(2) quotient_active_vertices[of state] contraction_cycle(4)
  by(auto elim!: invar_search_props; blast)

lemma contraction_finite:
  "finite (hierarchy_ids (qbs_hierarchy state))" "finite (active_ids state)"
  using contraction(2) active_ids_subset[of state]
  by(auto elim!: invar_search_props simp: invar_recovering_structure_def recovery_tree_def; blast intro: finite_subset)+

lemma contraction_fresh_nonempty:
  "queue_abstract (qbs_fresh state) \<noteq> []"
proof-
  have "3 \<le> card (active_ids state)"
    using card_mono[OF contraction_finite(2) contraction_cycle_active] contraction_cycle(3)
    by(simp only: distinct_card[OF contraction_cycle(1)]; arith)
  thus ?thesis
    using contraction(2)
    by(auto simp: invar_search_def invar_fresh_def; presburger)
qed

lemma contraction_fresh:
  "b \<in> K - hierarchy_ids (qbs_hierarchy state)" "queue_invar fresh"
  "queue_abstract fresh = tl (queue_abstract (qbs_fresh state))"
  using Work.queue_pop[of "qbs_fresh state"] contraction_fresh_nonempty contraction(2,4)
  by(auto simp: invar_search_def invar_adts_def invar_fresh_def dest: hd_in_set)

lemma contraction_matching_vertices:
  "Vs (mate_abstract (qbs_matching state)) \<subseteq> active_ids state"
  using contraction(2) search_matching(2)[of state] quotient_active_vertices[of state]
  by(auto elim!: invar_search_props dest: Vs_subset)

lemma contraction_active_bounds:
  "active_ids state \<subseteq> K" "b \<notin> active_ids state" "b \<notin> Vs (quotient_graph state)"
  using quotient_active_vertices[of state] active_ids_subset[of state] contraction_fresh(1) contraction(2)
  by(auto simp: invar_search_def invar_representatives_def invar_recovering_structure_def; blast)+

lemma contraction_hierarchy_precond:
  "Hierarchy.blossom_forest_merge_precond (qbs_hierarchy state) (c1 @ butlast (rev c2)) b"
  using contraction_cycle contraction_cycle_active contraction_fresh contraction(2)
  by(auto intro!: Hierarchy.blossom_forest_merge_precondI
    simp: invar_search_def invar_recovering_structure_def)

lemma contraction_matching_precond:
  "Mate.contract_path_precond (quotient_graph state) (qbs_matching state)
    (c1 @ butlast (rev c2)) b (\<lambda>x. if x \<in> set (c1 @ butlast (rev c2)) then b else x)"
  using contraction(2) contraction_cycle(1,2,5) contraction_cycle_active contraction_fresh(1)
    contraction_matching_vertices contraction_active_bounds
  by(auto intro!: Mate.contract_path_precondI elim!: invar_search_props invar_forest_props; blast)

lemma contraction_endpoints:
  "source_component state \<in> set (c1 @ butlast (rev c2))"
  "target_component state \<in> set (c1 @ butlast (rev c2))"
  "source_component state = last c1" "target_component state = last c2"
proof-
  show "source_component state = last c1" "target_component state = last c2"
    using search_forest_path_head[of state "source_component state"]
      search_forest_path_head[of state "target_component state"]
      contraction_path_components[of state] contraction_geometry(1,2)
      contraction_geometry(4,5)[THEN arg_cong[where f=hd]] contraction(1,2)
    by(auto elim!: invar_search_props simp: hd_append hd_rev)
  thus "source_component state \<in> set (c1 @ butlast (rev c2))"
    "target_component state \<in> set (c1 @ butlast (rev c2))"
    using contraction_geometry(1,2) contraction_cycle(4)
    by(auto intro: last_in_set)
qed

lemma contraction_even:
  "source_component state \<in> even_ids state" "target_component state \<in> even_ids state"
  using contraction(1,2) contraction_path_components[of state]
  by(auto elim!: invar_search_props)

lemma contraction_cycle_forest:
  "set (c1 @ butlast (rev c2)) \<subseteq> even_ids state \<union> odd_ids state"
  using contraction_even
    forest_path_vertices[of "mate_abstract (qbs_matching state)" "qbs_forest state" "source_component state"]
    forest_path_vertices[of "mate_abstract (qbs_matching state)" "qbs_forest state" "target_component state"]
    contraction_cycle(4) contraction_geometry(4,5)[THEN arg_cong[where f=set]] contraction(2)
  by(auto elim!: invar_search_props invar_forest_props; blast)

lemma contraction_forest_precond:
  "Forest.contract_fork_precond (mate_abstract (qbs_matching state)) (qbs_forest state)
    (source_component state) (target_component state)
    (butlast (rev c1)) (butlast (rev c2)) (hd c1) b
    (drop (length c1) (forest_path (qbs_forest state) (source_component state)))
    (\<lambda>x. if x \<in> set (c1 @ butlast (rev c2)) then b else x)"
proof-
  obtain P where
    "forest_path (qbs_forest state) (source_component state) = rev c1 @ P"
    "forest_path (qbs_forest state) (target_component state) = rev c2 @ P"
    using contraction_geometry(4,5)
    by blast
  thus ?thesis
    using contraction_geometry(1-3,6) contraction_path_components[of state] contraction(1,2)
      search_matching(1)[of state] search_matching_doubleton[of state]
      contraction_matching_vertices contraction_active_bounds
    by(cases c1; cases c2;
      auto intro!: Forest.contract_fork_precondI
        elim!: invar_search_props simp: invar_forest_def; blast)
qed

lemmas contraction_invariants =
  contraction(2)[unfolded invar_search_def]
  contraction(2)[unfolded invar_search_def invar_adts_def invar_forest_def]

lemma contraction_selectors:
  "qbs_forest (Quadratic_Blossom_Search_upd7 state) =
    forest_contract (qbs_forest state) (rev c1) (rev c2) b"
  "qbs_matching (Quadratic_Blossom_Search_upd7 state) =
    mate_contract (qbs_matching state) (c1 @ butlast (rev c2)) b"
  "qbs_hierarchy (Quadratic_Blossom_Search_upd7 state) =
    hierarchy_merge (qbs_hierarchy state) (c1 @ butlast (rev c2)) b"
  "qbs_component (Quadratic_Blossom_Search_upd7 state) = b"
  "qbs_fresh (Quadratic_Blossom_Search_upd7 state) = fresh"
  "qbs_forest_edges (Quadratic_Blossom_Search_upd7 state) =
    edge_update (qbs_forest_edges state) b (forest_edge state (hd c1))"
  "qbs_current (Quadratic_Blossom_Search_upd7 state) = qbs_current state"
  "qbs_hints (Quadratic_Blossom_Search_upd7 state) = link_update (qbs_hints state) b (nil,0)"
  "qbs_components (Quadratic_Blossom_Search_upd7 state) =
    qbs_components (process_cycle (Quadratic_Blossom_Search_upd4 state)
      (c1 @ butlast (rev c2)) (length c1) (scanned_vertex state, scanned_neighbour state) b)"
  "qbs_owners (Quadratic_Blossom_Search_upd7 state) =
    qbs_owners (process_cycle (Quadratic_Blossom_Search_upd4 state)
      (c1 @ butlast (rev c2)) (length c1) (scanned_vertex state, scanned_neighbour state) b)"
  using contraction(3,4)
  by(auto simp: Quadratic_Blossom_Search_upd7_def contract_search_def
    Quadratic_Blossom_Search_upd4_def process_cycle_frame Let_def)

lemma contraction_scanning_invariants:
  "invar_adts (Quadratic_Blossom_Search_upd4 state)"
  "invar_representatives (Quadratic_Blossom_Search_upd4 state)"
  "invar_components (Quadratic_Blossom_Search_upd4 state)"
  "invar_hierarchy_size (Quadratic_Blossom_Search_upd4 state)"
  "invar_queue (Quadratic_Blossom_Search_upd4 state)"
  "invar_neighbours (Quadratic_Blossom_Search_upd4 state)"
  "effectively_even (Quadratic_Blossom_Search_upd4 state) = effectively_even state"
  "u \<in> V0 \<Longrightarrow> representative (Quadratic_Blossom_Search_upd4 state) u = representative state u"
  "u \<in> K \<Longrightarrow> uf_representative (qbs_components (Quadratic_Blossom_Search_upd4 state)) u =
    uf_representative (qbs_components state) u"
  "pending_arcs state - {(qbs_current state, scanned_neighbour state)} =
    pending_arcs (Quadratic_Blossom_Search_upd4 state)"
  using contraction(1) Hierarchy.blossom_forest_merge_precondD(1)[OF contraction_hierarchy_precond]
  by(auto simp: contraction_invariants Quadratic_Blossom_Search_call_7_conds_def
      invar_adts_holds_4 invar_representatives_holds_4 invar_components_holds_4
      invar_hierarchy_size_holds_4 invar_queue_holds_4 invar_neighbours_holds_4
      scanning_even scanning_representative scanning_pending_arcs)
    (auto simp: Quadratic_Blossom_Search_upd4_def contraction_invariants
      scanning_target_correct(3))

lemma contraction_matching:
  "mate_invar
    (quot_graph (\<lambda>x. if x \<in> set (c1 @ butlast (rev c2)) then b else x) (quotient_graph state) - {{b}})
    (qbs_matching (Quadratic_Blossom_Search_upd7 state))"
  "mate_abstract (qbs_matching (Quadratic_Blossom_Search_upd7 state)) =
    quot_graph (\<lambda>x. if x \<in> set (c1 @ butlast (rev c2)) then b else x)
      (mate_abstract (qbs_matching state)) - {{b}}"
  using contraction_matching_precond
  by(auto simp only: contraction_selectors dest: Mate.contract)

lemma contraction_forest:
  "forest_invar (mate_abstract (qbs_matching (Quadratic_Blossom_Search_upd7 state)))
    (qbs_forest (Quadratic_Blossom_Search_upd7 state))"
  "forest_abstract (qbs_forest (Quadratic_Blossom_Search_upd7 state)) =
    quot_graph (\<lambda>x. if x \<in> set (c1 @ butlast (rev c2)) then b else x)
      (forest_abstract (qbs_forest state)) - {{b}}"
  "even_ids (Quadratic_Blossom_Search_upd7 state) =
    even_ids state - set (c1 @ butlast (rev c2)) \<union> {b}"
  "odd_ids (Quadratic_Blossom_Search_upd7 state) =
    odd_ids state - set (c1 @ butlast (rev c2))"
  using Contract.contract_fork_spec(1-4)[OF contraction_forest_precond]
    contraction_geometry(1-3) contraction_fresh(1) contraction_matching(2)
  by(cases c1; cases c2; auto simp: contraction_selectors)+

lemma contraction_hierarchy:
  "hierarchy_invar (qbs_hierarchy (Quadratic_Blossom_Search_upd7 state))"
  "hierarchy_ids (qbs_hierarchy (Quadratic_Blossom_Search_upd7 state)) =
    insert b (hierarchy_ids (qbs_hierarchy state))"
  "active_ids (Quadratic_Blossom_Search_upd7 state) =
    active_ids state - set (c1 @ butlast (rev c2)) \<union> {b}"
  using contraction_hierarchy_precond
  by(auto simp only: contraction_selectors dest: Hierarchy.merge_spec)

lemma contraction_forest_edges:
  "edge_invar (qbs_forest_edges (Quadratic_Blossom_Search_upd7 state))"
  "edge_lookup (qbs_forest_edges (Quadratic_Blossom_Search_upd7 state)) =
    (edge_lookup (qbs_forest_edges state))(b := forest_edge state (hd c1))"
  using contraction(2) contraction_fresh(1)
  by(auto simp: contraction_selectors invar_search_def invar_adts_def
    Edges.fixed_univ_map_upd Edges.fixed_univ_map_upd_invar)

lemma contraction_base_even:
  "hd c1 \<in> even_ids state"
proof-
  have invar: "forest_invar (mate_abstract (qbs_matching state)) (qbs_forest state)"
    using contraction(2)
    by(auto elim!: invar_search_props invar_forest_props)
  have "even (length (drop (length c1) (forest_path (qbs_forest state) (source_component state))))"
    using match_blossom_stem_even[OF blossomD(2)[OF contraction_blossom]]
    by simp
  hence "odd (length c1)"
    using compute_alt_path_specD(7)[OF contraction_spec]
      contraction_geometry(4)[THEN arg_cong[where f=length]]
    by(simp only: length_append length_rev; presburger)
  moreover have "path (forest_abstract (qbs_forest state)) c1 \<or> c1 = [source_component state]"
    using Forest.get_path_basis[OF invar contraction_even(1) contraction_geometry(4)[symmetric],
        THEN conjunct2, THEN conjunct2] contraction_geometry(1)
    by(auto simp: walk_betw_def append_eq_Cons_conv rev_path_is_path_iff dest: path_pref)
  ultimately show ?thesis
    using Forest.forest_path_parity[OF invar, of c1]
      Forest.evens_and_odds(4)[OF invar]
      contraction_endpoints(3) contraction_geometry(1)
      contraction_even
    by(cases c1; auto)
qed

lemma contraction_representative:
  "u \<in> V0 \<Longrightarrow> representative (Quadratic_Blossom_Search_upd7 state) u = (if representative state u
    \<in> set (c1 @ butlast (rev c2)) then b else representative state u)"
  using process_cycle_representative[of "Quadratic_Blossom_Search_upd4 state"
      "c1 @ butlast (rev c2)" b u "length c1" "(scanned_vertex state, scanned_neighbour state)"]
    contraction_scanning_invariants(1-4,8) contraction_cycle_active contraction_fresh(1)
    Hierarchy.blossom_forest_merge_precondD(1)[OF contraction_hierarchy_precond]
  by(simp only: contraction_selectors(9,10))
    (auto simp: Quadratic_Blossom_Search_upd4_def)

lemma contraction_projected_graph:
  assumes "A \<subseteq> input_graph"
  shows "{e \<in> quot_graph (representative (Quadratic_Blossom_Search_upd7 state)) A. card e = 2} =
    quot_graph (\<lambda>x. if x \<in> set (c1 @ butlast (rev c2)) then b else x)
      {e \<in> quot_graph (representative state) A. card e = 2} - {{b}}"
proof-
  have "Vs A \<subseteq> V0"
    using assms input_graph_vertices
    by(auto simp: Vs_def)
  hence "quot_graph (representative (Quadratic_Blossom_Search_upd7 state)) A =
    quot_graph (\<lambda>u. if representative state u \<in> set (c1 @ butlast (rev c2))
      then b else representative state u) A"
    by(intro quot_graph_cong image_cong) (auto simp: Vs_def contraction_representative)
  thus ?thesis
    using projected_graph_contract[where R="representative state" and A=A
      and S="set (c1 @ butlast (rev c2))" and b=b]
    by(simp only: projected_graph[OF assms])
qed

lemma contraction_quotient:
  "quotient_graph (Quadratic_Blossom_Search_upd7 state) =
    quot_graph (\<lambda>x. if x \<in> set (c1 @ butlast (rev c2)) then b else x)
      (quotient_graph state) - {{b}}"
  unfolding quotient_graph_def
  by(simp only: projected_graph subset_refl contraction_projected_graph)

lemma contraction_matching_boundary:
  assumes "{u,v} \<in> mate_abstract (qbs_matching state)"
    "u \<in> set (c1 @ butlast (rev c2))" "v \<notin> set (c1 @ butlast (rev c2))"
  shows "u = hd c1"
  using assms contraction_cycle(4) contraction(2) contraction_blossom
    matching_edge_incident_on_cycle[of "c1 @ rev c2" "mate_abstract (qbs_matching state)" "{u,v}" u v]
    contraction_geometry(1-3)
  by(auto simp: last_append last_rev intro: match_blossom_alt_cycle search_matching(1)
    dest: match_blossomD(3) elim!: invar_search_props)

lemma contraction_edge_witness:
  "\<lbrakk>edge_witness state e (x,y); ({x,y} \<in> mate_abstract (qbs_matching state)) = ({if x \<in> set (c1 @
    butlast (rev c2)) then b else x, if y \<in> set (c1 @ butlast (rev c2)) then b else y} \<in> mate_abstract
    (qbs_matching (Quadratic_Blossom_Search_upd7 state)))\<rbrakk> \<Longrightarrow> edge_witness
    (Quadratic_Blossom_Search_upd7 state) e (if x \<in> set (c1 @ butlast (rev c2)) then b else x, if y \<in> set
    (c1 @ butlast (rev c2)) then b else y)"
  using contraction_representative[of "fst e"] contraction_representative[of "snd e"]
    input_edge_vertices[of "fst e" "snd e"]
  by(auto simp del: input_edge_iff)

lemma contraction_annotation_step:
  assumes "a \<in> even_ids (Quadratic_Blossom_Search_upd7 state)"
    "{a,x} \<in> mate_abstract (qbs_matching (Quadratic_Blossom_Search_upd7 state))"
    "{x,z} \<in> forest_abstract (qbs_forest (Quadratic_Blossom_Search_upd7 state))"
    "z \<in> even_ids (Quadratic_Blossom_Search_upd7 state)" "z \<noteq> a"
  shows "edge_witness (Quadratic_Blossom_Search_upd7 state)
      (forest_edge (Quadratic_Blossom_Search_upd7 state) a) (a,x) \<and>
    edge_witness (Quadratic_Blossom_Search_upd7 state)
      (forest_edge (Quadratic_Blossom_Search_upd7 state) x) (x,z)"
proof-
  let ?S = "Quadratic_Blossom_Search_upd7 state"
  let ?M = "mate_abstract (qbs_matching state)"
  let ?F = "qbs_forest state"
  let ?C = "set (c1 @ butlast (rev c2))"
  let ?c = "\<lambda>v. if v \<in> ?C then b else v"
  let ?a = "if a = b then hd c1 else a"
  have "invar_forest state"
    using contraction(2)
    by(auto elim!: invar_search_props)
  from this contraction_forest(1)
  have inv: "forest_invar ?M ?F"
    "forest_invar (mate_abstract (qbs_matching ?S)) (qbs_forest ?S)"
    "matching ?M" "dblton_graph ?M"
    by(auto intro: search_matching(1) search_matching_doubleton elim: invar_forest_props)
  have odd: "x \<in> odd_ids state - ?C" "x \<noteq> b"
    using Forest.higher_forest_properties(3)[OF inv(2), of z x] assms(3,4)
      contraction_forest(4) contraction_active_bounds(2) contraction(2)
    by(auto elim!: invar_search_props invar_forest_props simp: insert_commute)
  have origin: "?a \<in> even_ids state" "?c ?a = a"
    using assms(1) contraction_forest(3) contraction_base_even contraction_geometry(1)
    by(auto split: if_splits)
  obtain u v where "{u,v} \<in> ?M" "{?c u, ?c v} = {a,x}"
    using assms(2) inv(4) contraction_matching(2)
    by(auto simp: quot_graph_def)
  then obtain r where matched: "{r,x} \<in> ?M" "?c r = a"
    using odd
    by(fastforce simp: doubleton_eq_iff insert_commute split: if_splits)
  have first: "{?a,x} \<in> ?M"
    using matched contraction_matching_vertices contraction_active_bounds(2) odd
      contraction_matching_boundary[of r x]
    by(auto split: if_splits dest: edges_are_Vs)
  obtain u v where "{u,v} \<in> forest_abstract ?F" "{?c u, ?c v} = {x,z}"
    using assms(3) Forest.dblton[of ?M ?F] inv(1) contraction_forest(2)
    by(auto simp: quot_graph_def)
  then obtain r where parent: "{x,r} \<in> forest_abstract ?F" "?c r = z"
    using odd
    by(fastforce simp: doubleton_eq_iff insert_commute split: if_splits)
  have "r \<in> even_ids state"
    using Forest.higher_forest_properties(3)[of ?M ?F r x] inv(1) parent(1) odd(1)
    by(auto simp: insert_commute)
  moreover have "r \<noteq> ?a"
    using parent(2) origin(2) assms(5)
    by(auto simp only:)
  ultimately have witnesses: "edge_witness state (forest_edge state ?a) (?a,x)"
    "edge_witness state (forest_edge state x) (x,r)"
    using contraction(2) origin(1) first parent(1)
    by(auto elim!: invar_search_props simp: invar_annotations_def)
  have "{x,r} \<notin> ?M" "{x,z} \<notin> mate_abstract (qbs_matching ?S)"
    using first inv(3) origin(2) parent(2) assms(2,5)
      Mate.matching(1)[OF contraction_matching(1)]
    by(auto dest: doubleton_in_matching[of _ _ x] simp: insert_commute)
  hence "edge_witness ?S (forest_edge state ?a) (a,x)"
    "edge_witness ?S (forest_edge state x) (x,z)"
    using contraction_edge_witness[of "forest_edge state ?a" ?a x]
      contraction_edge_witness[of "forest_edge state x" x r]
      first witnesses assms(2) origin(2) parent(2) odd
    by auto
  thus ?thesis
    using contraction_forest_edges(2) odd(2)
    by(auto split: if_splits)
qed

lemma contraction_annotations:
  "invar_annotations (Quadratic_Blossom_Search_upd7 state)"
  unfolding invar_annotations_def
  by(intro ballI allI impI; rule contraction_annotation_step; blast)

lemma invar_matching_projection_holds_7[invar_holds_intros]:
  "invar_matching_projection (Quadratic_Blossom_Search_upd7 state)"
  using contraction_projected_graph[OF input_matching_props(2)]
    contraction_matching(2) contraction(2)
  by(auto simp: invar_matching_projection_def invar_search_def
    projected_graph[OF input_matching_props(2)])

interpretation Contraction_Quotient: quot "quotient_graph state"
  "Vs (quotient_graph state) - set (c1 @ butlast (rev c2))" b
proof-
  have "Vs (quotient_graph state) - set (c1 @ butlast (rev c2)) \<subset> Vs (quotient_graph state)"
    using blossom_diff[OF quotient_graph_invar blossomD(2)[OF contraction_blossom]
      blossomD(1)[OF contraction_blossom]] contraction_cycle(4)
    by simp
  thus "quot (quotient_graph state) (Vs (quotient_graph state) - set (c1 @ butlast (rev c2))) b"
    using quotient_graph_invar contraction_active_bounds(3)
    by(unfold_locales) auto
qed

lemma contraction_quotient_maps:
  "A \<subseteq> quotient_graph state \<Longrightarrow>
    quot_graph (\<lambda>x. if x \<in> set (c1 @ butlast (rev c2)) then b else x) A =
    quot_graph (\<lambda>x. if x \<in> Vs (quotient_graph state) - set (c1 @ butlast (rev c2)) then x else b) A"
  by(intro quot_graph_cong image_cong) (auto simp: Vs_def split: if_splits)

lemma contraction_matched_outside:
  assumes "v \<in> Vs (mate_abstract (qbs_matching state)) - set (c1 @ butlast (rev c2))"
  shows "v \<in> Vs (mate_abstract (qbs_matching (Quadratic_Blossom_Search_upd7 state)))"
proof-
  have subset: "mate_abstract (qbs_matching state) \<subseteq> quotient_graph state"
    using search_matching(2)[of state] contraction(2)
    by(auto elim!: invar_search_props)
  show ?thesis
    using Contraction_Quotient.vert_in_graph_iff_in_quot_diff_u[of v "mate_abstract (qbs_matching state)"]
      assms subset Vs_subset[OF subset] contraction_matching(2) contraction_quotient_maps[OF subset]
    by auto
qed


lemma contraction_non_even_matched:
  "active_ids (Quadratic_Blossom_Search_upd7 state) - even_ids (Quadratic_Blossom_Search_upd7 state)
    \<subseteq> Vs (mate_abstract (qbs_matching (Quadratic_Blossom_Search_upd7 state)))"
  using Forest.roots(2)[of "mate_abstract (qbs_matching state)" "qbs_forest state"]
    contraction(2) contraction_hierarchy(3) contraction_forest(3)
  by(auto simp: invar_search_def invar_forest_def intro: contraction_matched_outside)


lemma invar_forest_holds_7[invar_holds_intros]:
  "invar_forest (Quadratic_Blossom_Search_upd7 state)"
proof-
  have old: "forest_abstract (qbs_forest state) \<subseteq> quotient_graph state"
    "even_ids state \<union> odd_ids state \<subseteq> active_ids state"
    using contraction(2)
    by(auto elim!: invar_search_props invar_forest_props)
  show ?thesis
    using quot_graph_subset[OF old(1), of "\<lambda>x. if x \<in> set (c1 @ butlast (rev c2)) then b else x"]
      contraction_matching(1) contraction_forest contraction_hierarchy(3) old(2)
      Forest.roots_are_unmatched_evens[OF contraction_forest(1)] contraction_non_even_matched
    by(auto simp: invar_forest_def contraction_quotient)
qed


lemma invar_existence_holds_7[invar_holds_intros]:
  "invar_existence (Quadratic_Blossom_Search_upd7 state)"
proof-
  let ?next = "Quadratic_Blossom_Search_upd7 state"
  let ?E = "quotient_graph state"
  let ?M = "mate_abstract (qbs_matching state)"
  let ?N = "mate_abstract (qbs_matching ?next)"
  have paths_iff: "(\<exists>p. graph_augmenting_path A N p) = (\<not> max_card_matching A N)"
    if "finite N" "matching N" "N \<subseteq> A" "Undirected_Set_Graphs.graph_invar A" for N A :: "'v set set"
    using Berge[OF that(1-3)] that
    by(auto simp: max_card_matching_def)
  have "invar_forest state"
    using contraction(2)
    by(auto elim!: invar_search_props)
  note matching = search_matching[OF this] search_matching[OF invar_forest_holds_7]
  have finite: "finite ?M" "finite ?N"
    using matching(2,4) graph_invar_finite[OF quotient_graph_invar[of state]]
      graph_invar_finite[OF quotient_graph_invar[of ?next]]
    by(blast intro: finite_subset)+
  have "max_card_matching (quotient_graph ?next) ?N = max_card_matching ?E ?M"
    using Contraction_Quotient.max_card_matching_equiv_blossom_contraction[OF contraction_blossom]
      matching(1,2) contraction_cycle(4) contraction_active_bounds(3)
      contraction_quotient_maps[OF subset_refl] contraction_quotient_maps[OF matching(2)]
    by(simp add: contraction_quotient contraction_matching(2))
  hence "(\<exists>p. graph_augmenting_path (quotient_graph ?next) ?N p) =
    (\<exists>p. graph_augmenting_path ?E ?M p)"
    using paths_iff[OF finite(1) matching(1,2) quotient_graph_invar[of state]]
      paths_iff[OF finite(2) matching(3,4) quotient_graph_invar[of ?next]]
    by simp
  thus ?thesis
    using contraction(2)
    by(auto elim!: invar_search_props simp: invar_existence_def)
qed
lemmas contraction_current_vertex = contraction_selectors(7)

lemma contraction_hints:
  "link_invar (qbs_hints (Quadratic_Blossom_Search_upd7 state))"
  "link_lookup (qbs_hints (Quadratic_Blossom_Search_upd7 state)) =
    (link_lookup (qbs_hints state))(b := (nil, 0))"
  using contraction_fresh(1)
  by(auto simp: contraction_invariants contraction_selectors(8)
    Routing.Links.fixed_univ_map_upd_invar Routing.Links.fixed_univ_map_upd)

lemma contraction_scheduled:
  "distinct (filter (fset_isin (forest_odds (qbs_forest state))) (c1 @ butlast (rev c2)))"
  "set (filter (fset_isin (forest_odds (qbs_forest state))) (c1 @ butlast (rev c2))) =
    odd_ids state \<inter> set (c1 @ butlast (rev c2))"
  "set (filter (fset_isin (forest_odds (qbs_forest state))) (c1 @ butlast (rev c2))) \<subseteq>
    V0 - effectively_even state"
  "{u \<in> V0. representative state u \<in> odd_ids state \<inter> set (c1 @ butlast (rev c2))} =
    odd_ids state \<inter> set (c1 @ butlast (rev c2))"
proof-
  have inv: "forest_invar (mate_abstract (qbs_matching state)) (qbs_forest state)"
    "invar_representatives state"
    using contraction(2)
    by(auto elim!: invar_search_props invar_forest_props)
  show "distinct (filter (fset_isin (forest_odds (qbs_forest state))) (c1 @ butlast (rev c2)))"
    using contraction_cycle(1)
    by(rule distinct_filter)
  show "set (filter (fset_isin (forest_odds (qbs_forest state))) (c1 @ butlast (rev c2))) =
    odd_ids state \<inter> set (c1 @ butlast (rev c2))"
    using Forest.evens_and_odds(2)[OF inv(1)]
    by(auto simp: Fset.fixed_univ_set_isin)
  have "odd_ids state \<inter> set (c1 @ butlast (rev c2)) \<subseteq> active_ids state - even_ids state"
    using contraction(2) Forest.evens_and_odds(4)[OF inv(1)]
    by(auto elim!: invar_search_props invar_forest_props)
  thus preimage: "{u \<in> V0. representative state u \<in> odd_ids state \<inter> set (c1 @ butlast (rev c2))} =
    odd_ids state \<inter> set (c1 @ butlast (rev c2))"
    by(rule non_even_preimage[OF inv(2)])
  show "set (filter (fset_isin (forest_odds (qbs_forest state))) (c1 @ butlast (rev c2))) \<subseteq>
    V0 - effectively_even state"
    using preimage Forest.evens_and_odds(2,4)[OF inv(1)]
    by(auto simp: Fset.fixed_univ_set_isin effectively_even_def; blast)
qed

lemma contraction_effectively_even:
  "effectively_even (Quadratic_Blossom_Search_upd7 state) =
    effectively_even state \<union> (odd_ids state \<inter> set (c1 @ butlast (rev c2)))"
proof-
  have "u \<in> V0 \<Longrightarrow> representative state u \<noteq> b" for u
    using contraction(2) contraction_active_bounds(2)
    by(auto elim!: invar_search_props invar_representatives_props)
  hence "effectively_even (Quadratic_Blossom_Search_upd7 state) =
    {u \<in> V0. representative state u \<in> even_ids state \<or>
      representative state u \<in> odd_ids state \<inter> set (c1 @ butlast (rev c2))}"
    using contraction_cycle_forest
    by(auto simp: effectively_even_def contraction_forest(3) contraction_representative
      split: if_splits; blast)
  also have "... = effectively_even state \<union> (odd_ids state \<inter> set (c1 @ butlast (rev c2)))"
    using contraction_scheduled(4)
    by(auto simp: effectively_even_def)
  finally show ?thesis .
qed

lemma contraction_queue:
  "queue_invar (qbs_queue (Quadratic_Blossom_Search_upd7 state))"
  "queue_abstract (qbs_queue (Quadratic_Blossom_Search_upd7 state)) =
    queue_abstract (qbs_queue state) @
      filter (fset_isin (forest_odds (qbs_forest state))) (c1 @ butlast (rev c2))"
  using queue_push_fold[of "qbs_queue state"
      "filter (fset_isin (forest_odds (qbs_forest state))) (c1 @ butlast (rev c2))"]
    queue_batch_space[OF _ contraction_scheduled(1,3)] contraction(2-4)
  by(auto elim!: invar_search_props invar_adts_props
    simp: Quadratic_Blossom_Search_upd7_def contract_search_def
      process_cycle_queue Let_def Quadratic_Blossom_Search_upd4_def)

lemma contraction_queue_invar:
  "invar_queue (Quadratic_Blossom_Search_upd7 state)"
  using contraction_scanning_invariants(5,7) contraction_queue(2) contraction_scheduled(1-3)
  by(auto simp: invar_queue_def contraction_effectively_even contraction_current_vertex
    Quadratic_Blossom_Search_upd4_def)

lemma contraction_adts:
  "invar_adts (Quadratic_Blossom_Search_upd7 state)"
  using process_cycle_owner(1,2)[of "Quadratic_Blossom_Search_upd4 state" b
      "c1 @ butlast (rev c2)" b "length c1" "(scanned_vertex state, scanned_neighbour state)"]
    contraction_scanning_invariants(1) contraction_cycle_active contraction_active_bounds(1)
    contraction_fresh(1,2) contraction_queue(1) contraction_forest_edges(1) contraction_hints(1)
  by(auto simp: invar_adts_def contraction_selectors(5,9,10))

lemma contraction_scanned_representatives:
  "representative (Quadratic_Blossom_Search_upd7 state) (qbs_current state) = b"
  "representative (Quadratic_Blossom_Search_upd7 state) (scanned_neighbour state) = b"
  using contraction(1,2) contraction_endpoints(1,2)
    scanning_source[of state] scanning_neighbour(1)[of state]
    scanning_source_component[of state] scanning_target_correct(1)[of state]
    contraction_representative[of "qbs_current state"]
    contraction_representative[of "scanned_neighbour state"]
  by(auto elim!: invar_search_props simp: Quadratic_Blossom_Search_call_7_conds_def)

lemma contraction_old_labels:
  assumes "u \<in> V0" "u \<notin> odd_ids state \<inter> set (c1 @ butlast (rev c2))"
  shows "representative (Quadratic_Blossom_Search_upd7 state) u \<in>
      even_ids (Quadratic_Blossom_Search_upd7 state) \<longleftrightarrow> representative state u \<in> even_ids state"
    "representative (Quadratic_Blossom_Search_upd7 state) u \<in>
      odd_ids (Quadratic_Blossom_Search_upd7 state) \<longleftrightarrow> representative state u \<in> odd_ids state"
proof-
  show "representative (Quadratic_Blossom_Search_upd7 state) u \<in>
    even_ids (Quadratic_Blossom_Search_upd7 state) \<longleftrightarrow> representative state u \<in> even_ids state"
    using assms contraction_effectively_even
    by(auto simp: effectively_even_def)
  have "representative state u \<notin> odd_ids state \<inter> set (c1 @ butlast (rev c2))"
    "b \<notin> odd_ids state"
    using assms contraction_scheduled(4) contraction(2) contraction_active_bounds(2)
    by(auto elim!: invar_search_props invar_forest_props)
  thus "representative (Quadratic_Blossom_Search_upd7 state) u \<in>
    odd_ids (Quadratic_Blossom_Search_upd7 state) \<longleftrightarrow> representative state u \<in> odd_ids state"
    by(auto simp: contraction_representative[OF assms(1)] contraction_forest(4) split: if_splits)
qed

lemma contraction_pending_arcs:
  "pending_arcs state - {(qbs_current state, scanned_neighbour state)} \<subseteq>
    pending_arcs (Quadratic_Blossom_Search_upd7 state)"
  using contraction_scanning_invariants(10) contraction_scanning_invariants(7)
  by(auto simp: pending_arcs_def contraction_effectively_even)

lemma contraction_pending_pair:
  "\<lbrakk>(u,v) \<in> pending_arcs state;
    representative (Quadratic_Blossom_Search_upd7 state) u \<noteq>
      representative (Quadratic_Blossom_Search_upd7 state) v\<rbrakk> \<Longrightarrow>
    (u,v) \<in> pending_arcs (Quadratic_Blossom_Search_upd7 state)"
  using contraction_pending_arcs contraction_scanned_representatives
  by auto

lemma contraction_new_arcs:
  "\<lbrakk>u \<in> odd_ids state \<inter> set (c1 @ butlast (rev c2)); {u,v} \<in> input_graph\<rbrakk>
    \<Longrightarrow> (u,v) \<in> pending_arcs (Quadratic_Blossom_Search_upd7 state)"
  by(rule pending_unscanned[where before = "Quadratic_Blossom_Search_upd4 state"])
    (insert contraction_scheduled(2,3) contraction_scanning_invariants(1,5-7),
      auto simp: contraction_effectively_even)

lemma contraction_scanned:
  "invar_scanned (Quadratic_Blossom_Search_upd7 state)"
proof-
  let ?B = "odd_ids state \<inter> set (c1 @ butlast (rev c2))"
  have status: "qbs_status state = Quadratic_Searching"
    using contraction(1)
    by(auto simp: Quadratic_Blossom_Search_call_7_conds_def scanning_edge_def)
  show ?thesis
  proof(clarsimp simp: invar_scanned_def status simp del: input_edge_iff, rule ccontr, goal_cases)
    case edge: (1 u v)
    have outside: "u \<notin> ?B" "v \<notin> ?B"
      using edge contraction_new_arcs[of u v] contraction_new_arcs[of v u]
        contraction_effectively_even
      by(auto simp: effectively_even_def insert_commute simp del: input_edge_iff)
    have "representative state u \<noteq> representative state v"
      using edge(1,2,4)
      by(auto simp: contraction_representative split: if_splits)
    moreover have "representative state u \<in> even_ids state"
      "representative state v \<notin> odd_ids state"
      using edge contraction_old_labels[OF edge(1) outside(1)]
        contraction_old_labels[OF edge(2) outside(2)]
      by auto
    ultimately have "(u,v) \<in> pending_arcs state \<or>
      (representative state v \<in> even_ids state \<and> (v,u) \<in> pending_arcs state)"
      using contraction(2) edge(1-3) status
      by(auto elim!: invar_search_props simp: invar_scanned_def; blast)
    thus ?case
      using edge(4,7,8) contraction_old_labels(1)[OF edge(2) outside(2)]
      by(auto intro: contraction_pending_pair)
  qed
qed

lemma contraction_hierarchy_observations:
  "hierarchy_universe (qbs_hierarchy (Quadratic_Blossom_Search_upd7 state)) =
    hierarchy_universe (qbs_hierarchy state)"
  "hierarchy_members (qbs_hierarchy (Quadratic_Blossom_Search_upd7 state)) =
    (\<lambda>c. if c = b then \<Union>(hierarchy_members (qbs_hierarchy state) ` set (c1 @ butlast (rev c2)))
         else hierarchy_members (qbs_hierarchy state) c)"
  "c \<in> hierarchy_ids (qbs_hierarchy state) \<Longrightarrow>
    hierarchy_children (qbs_hierarchy (Quadratic_Blossom_Search_upd7 state)) c =
      hierarchy_children (qbs_hierarchy state) c"
  using contraction_hierarchy_precond contraction_fresh(1)
  by(simp_all add: contraction_selectors(3) Hierarchy.merge_spec Hierarchy.children_merge fun_eq_iff)

lemma contraction_representatives:
  "invar_representatives (Quadratic_Blossom_Search_upd7 state)"
proof(intro invar_representatives_intro ballI, goal_cases)
  case 1
  show ?case
    using contraction(2) contraction_fresh(1)
    by(auto elim!: invar_search_props invar_representatives_props simp: contraction_hierarchy(2))
next
  case 2
  show ?case
    using contraction(2)
    by(auto elim!: invar_search_props invar_representatives_props simp: contraction_hierarchy_observations(1))
next
  case (3 u)
  show ?case
    using 3 contraction(2) contraction_representative[of u]
    by(auto elim!: invar_search_props invar_representatives_props simp: contraction_hierarchy(3))
next
  case (4 c)
  have "\<And>d. d \<in> active_ids state \<Longrightarrow> hierarchy_members (qbs_hierarchy state) d =
      {u \<in> V0. representative state u = d}"
    "\<And>u. u \<in> V0 \<Longrightarrow> representative state u \<noteq> b"
    using contraction(2) contraction_active_bounds(2)
    by(auto elim!: invar_search_props invar_representatives_props)
  thus ?case
    using 4 contraction_active_bounds(2) contraction_cycle_active
    by(simp only: contraction_hierarchy_observations(2);
      auto simp: contraction_hierarchy(3) contraction_representative split: if_splits; blast)

next
  case (5 c)
  show ?case
    using 5 contraction(2)
    by(auto elim!: invar_search_props invar_representatives_props
      simp: contraction_hierarchy(3) contraction_hierarchy_observations(2) contraction_forest(3))
qed

lemma contraction_components:
  assumes "u \<in> K"
  defines "R \<equiv> insert b (uf_representative (qbs_components state) ` set (c1 @ butlast (rev c2)))"
  shows "uf_representative (qbs_components (Quadratic_Blossom_Search_upd7 state)) b \<in> R" (is ?root)
    "uf_representative (qbs_components (Quadratic_Blossom_Search_upd7 state)) u =
      (if uf_representative (qbs_components state) u \<in> R
       then uf_representative (qbs_components (Quadratic_Blossom_Search_upd7 state)) b
       else uf_representative (qbs_components state) u)" (is ?representatives)
proof-
  let ?next = "Quadratic_Blossom_Search_upd4 state"
  let ?cs = "c1 @ butlast (rev c2)"
  have inputs: "uf_invar (qbs_components ?next)" "b \<in> K" "set ?cs \<subseteq> K"
    using contraction_scanning_invariants(1) contraction_fresh(1)
      contraction_cycle_active contraction_active_bounds(1)
    by(auto elim!: invar_adts_props)
  have "uf_representative (qbs_components state) b = b"
    using contraction_fresh(1) contraction_invariants
    by(auto elim!: invar_components_props)
  moreover have "uf_representative (qbs_components ?next) ` set ?cs =
    uf_representative (qbs_components state) ` set ?cs"
    by(rule image_cong) (insert inputs, auto simp: contraction_scanning_invariants(9))
  ultimately show ?root ?representatives
    using process_cycle_components[OF inputs assms(1), of "length c1"
      "(scanned_vertex state, scanned_neighbour state)"]
    by(simp_all only: R_def contraction_selectors(9) contraction_scanning_invariants(9) inputs assms(1))
qed

lemma contraction_component_invariant:
  "invar_components (Quadratic_Blossom_Search_upd7 state)"
proof-
  let ?S = "Quadratic_Blossom_Search_upd7 state"
  let ?H = "qbs_hierarchy state"
  let ?R = "insert b (uf_representative (qbs_components state) ` set (c1 @ butlast (rev c2)))"
  have old: "invar_components state" "hierarchy_ids ?H \<subseteq> K"
    "set (c1 @ butlast (rev c2)) \<subseteq> hierarchy_ids ?H"
    using contraction(2) contraction_cycle_active
      Hierarchy.max_ids[OF Hierarchy.blossom_forest_merge_precondD(1)[OF contraction_hierarchy_precond]]
    by(auto elim!: invar_search_props invar_representatives_props)
  have region: "?R \<subseteq> insert b (hierarchy_ids ?H)"
    using old
    by(auto simp: invar_components_def)
  hence root: "uf_representative (qbs_components ?S) b \<in> insert b (hierarchy_ids ?H)"
    using contraction_components(1)[of b] contraction_fresh(1)
    by blast
  show ?thesis
  proof(intro invar_components_intro ballI, goal_cases)
    case (1 c)
    show ?case
      using 1 old root contraction_components(2)[of c] contraction_fresh(1)
      by(auto simp: contraction_hierarchy(2) invar_components_def split: if_splits)
  next
    case (2 c)
    show ?case
      using 2 old region contraction_components(2)[of c]
      by(auto simp: contraction_hierarchy(2) invar_components_def split: if_splits)
  next
    case (3 c u)
    have "c \<in> K" "u \<in> K"
      using 3 input_props(3) contraction_representatives
        Hierarchy.elems_in_universe[OF contraction_hierarchy(1), of c]
      by(auto elim!: invar_representatives_props)
    thus ?case
      using 3 old(1,3) contraction_components(2)[of u] contraction_components(2)[of c]
      by(cases "c = b"; auto simp: contraction_hierarchy(2)
        contraction_hierarchy_observations(2) invar_components_def; blast)
  qed
qed


lemma contraction_cardinalities:
  "card (hierarchy_ids (qbs_hierarchy (Quadratic_Blossom_Search_upd7 state)) - V0) =
    Suc (card (hierarchy_ids (qbs_hierarchy state) - V0))"
  "card (active_ids (Quadratic_Blossom_Search_upd7 state)) + length (c1 @ butlast (rev c2)) =
    Suc (card (active_ids state))"
proof-
  have "b \<notin> V0"
    using contraction_fresh(1) contraction(2)
    by(auto elim!: invar_search_props invar_hierarchy_size_props)
  thus "card (hierarchy_ids (qbs_hierarchy (Quadratic_Blossom_Search_upd7 state)) - V0) =
    Suc (card (hierarchy_ids (qbs_hierarchy state) - V0))"
    using contraction_finite(1) contraction_fresh(1)
    by(simp add: contraction_hierarchy(2) insert_Diff_if)
  have "card (set (c1 @ butlast (rev c2))) \<le> card (active_ids state)"
    by(rule card_mono) (use contraction_finite(2) contraction_cycle_active in auto)
  thus "card (active_ids (Quadratic_Blossom_Search_upd7 state)) + length (c1 @ butlast (rev c2)) =
    Suc (card (active_ids state))"
    using contraction_finite(2) contraction_cycle_active contraction_active_bounds(2) distinct_card[OF contraction_cycle(1)]
    by(simp add: contraction_hierarchy(3) card_Diff_subset distinct_card)
qed

lemma contraction_fresh_queue:
  "queue_abstract (qbs_fresh state) = b # queue_abstract fresh"
  using Work.queue_pop(2)[of "qbs_fresh state"] contraction_fresh_nonempty contraction_fresh(3) contraction(2,4)
  by(auto elim!: invar_search_props invar_adts_props simp: neq_Nil_conv)

lemma contraction_fresh_invariant:
  "invar_fresh (Quadratic_Blossom_Search_upd7 state)"
proof-
  have "card (active_ids (Quadratic_Blossom_Search_upd7 state)) div 2 \<le> length (queue_abstract fresh)"
    using contraction(2) contraction_cardinalities(2) contraction_cycle(3) contraction_fresh_queue
    by(auto elim!: invar_search_props invar_fresh_props; presburger)
  thus ?thesis
    using contraction(2) contraction_fresh_queue
    by(auto elim!: invar_search_props invar_fresh_props intro!: invar_fresh_intro
      simp: contraction_selectors(5) contraction_hierarchy(2))
qed

lemma contraction_hierarchy_size:
  "invar_hierarchy_size (Quadratic_Blossom_Search_upd7 state)"
  using contraction(2) contraction_cardinalities contraction_cycle(3)
  by(auto elim!: invar_search_props invar_hierarchy_size_props
    simp: invar_hierarchy_size_def contraction_hierarchy(2); presburger)

lemma contraction_neighbours:
  "invar_neighbours (Quadratic_Blossom_Search_upd7 state)"
  using invar_neighbours_holds_4[of state] contraction(1,2)
  by(auto elim!: invar_search_props call_cond_elims simp: invar_neighbours_def)

lemma contraction_current:
  "invar_current (Quadratic_Blossom_Search_upd7 state)"
  using contraction_scanned_representatives(1) contraction_current_vertex contraction_selectors(4)
  by(simp add: invar_current_def)

lemma contraction_result:
  "invar_result (Quadratic_Blossom_Search_upd7 state)"
  using contraction(1)
  by(auto elim!: call_cond_elims simp: invar_result_def scanning_edge_def)

lemma contraction_clear_hints:
  "\<forall>c \<in> hierarchy_ids (qbs_hierarchy (Quadratic_Blossom_Search_upd7 state)).
    hierarchy_children (qbs_hierarchy (Quadratic_Blossom_Search_upd7 state)) c \<noteq> [] \<longrightarrow>
      fst (link_lookup (qbs_hints (Quadratic_Blossom_Search_upd7 state)) c) = nil"
  using contraction(2) contraction_hints(2) contraction_fresh(1)
    contraction_hierarchy_observations(3)
  by(auto elim!: invar_search_props simp: contraction_hierarchy(2) split: if_splits)

lemma contraction_exploration:
  "state_rel_exploration state (Quadratic_Blossom_Search_upd7 state)"
  using contraction_effectively_even contraction_hierarchy(2) state_rel_exploration_holds_4[of state]
    contraction(1,2)
  by(auto elim!: invar_search_props call_cond_elims simp: state_rel_exploration_def)

lemma contraction_recovery_maps:
  "qbs_cycle_edges (Quadratic_Blossom_Search_upd7 state) =
    qbs_cycle_edges (process_cycle (Quadratic_Blossom_Search_upd4 state)
      (c1 @ butlast (rev c2)) (length c1) (scanned_vertex state, scanned_neighbour state) b)"
  "qbs_bases (Quadratic_Blossom_Search_upd7 state) =
    base_update (qbs_bases state) b (base_lookup (qbs_bases state) (hd (c1 @ butlast (rev c2))))"
  "qbs_parents (Quadratic_Blossom_Search_upd7 state) =
    Routing.record_parents (qbs_parents state) (c1 @ butlast (rev c2)) b"
  using contraction(3,4)
  by(simp_all add: Quadratic_Blossom_Search_upd7_def contract_search_def
    process_cycle_maps Quadratic_Blossom_Search_upd4_def Let_def)
lemma scanning_cycle_witness:
  "cycle_witness (Quadratic_Blossom_Search_upd4 state) cs k edge i c = cycle_witness state cs k edge i c"
  by(simp add: Quadratic_Blossom_Search_upd4_def)


lemma contraction_cycle_witnesses:
  "list_all2 (edge_witness state)
    (outward_edges state c1 @ [(scanned_vertex state, scanned_neighbour state)] @
      rootward_edges state (rev c2)) (edges_of_vwalk (c1 @ rev c2))"
proof-
  have "list_all2 (edge_witness state) (outward_edges state c1) (edges_of_vwalk c1)"
    using reversed_prefix_edge_witnesses[where s = state and v = "source_component state"
      and p = "rev c1", simplified rev_rev_ident] contraction contraction_geometry(4)
      contraction_path_components[of state]
    by(auto elim!: invar_search_props simp del: input_edge_iff)
  thus ?thesis
    using contraction contraction_geometry contraction_path_components[of state]
      scanning_edge_witness[of state] even_edge_unmatched[of state] contraction_endpoints(3,4)
    by(intro joined_edge_witnesses)
      (auto intro: prefix_edge_witnesses[where b = "target_component state"]
        simp: Quadratic_Blossom_Search_call_7_conds_def hd_rev
        elim!: invar_search_props simp del: input_edge_iff)
qed

lemma contraction_cycle_annotation:
  defines "cs \<equiv> c1 @ butlast (rev c2)"
  assumes "i < length cs"
  shows "let e = cycle_witness state cs (length c1)
      (scanned_vertex state, scanned_neighbour state) i (cs ! i)
    in fst e \<in> hierarchy_members (qbs_hierarchy state) (cs ! i) \<and>
      snd e \<in> hierarchy_members (qbs_hierarchy state) (cs ! (Suc i mod length cs)) \<and>
      {fst e, snd e} \<in> input_graph \<and> ({fst e, snd e} \<in> mate_abstract M0 \<longleftrightarrow> odd i)"
proof-
  let ?C = "c1 @ rev c2"
  let ?W = "outward_edges state c1 @ [(scanned_vertex state, scanned_neighbour state)] @
    rootward_edges state (rev c2)"
  let ?e = "cycle_witness state cs (length c1)
    (scanned_vertex state, scanned_neighbour state) i (cs ! i)"
  have "butlast (rev c2) @ [hd c1] = rev c2"
    using append_butlast_last_id[of "rev c2"] contraction_geometry(2,3)
    by(simp add: last_rev)
  hence closed: "?C = cs @ [hd cs]"
    using contraction_geometry(1)
    by(simp add: cs_def)
  have "alt_path (mate_abstract (qbs_matching state)) ?C"
    using contraction_blossom
    by(auto intro: match_blossom_alt_cycle)
  moreover have "?W ! i = ?e"
    using assms(2)
    by(intro cycle_witness_index) (simp_all add: contraction_geometry(1,2) cs_def)
  ultimately have "edge_witness state ?e (cs ! i, cs ! (Suc i mod length cs))"
    "{fst ?e, snd ?e} \<in> mate_abstract M0 \<longleftrightarrow> odd i"
    using contraction_cycle_witnesses
      witnessed_alternating_edge[of state ?W ?C i] assms(2)
    by(auto simp: closed closed_cycle_edge list_all2_conv_all_nth edges_of_vwalk_length
      simp del: input_edge_iff)
  thus ?thesis
    using contraction(2) edge_witness_members[of state ?e "cs ! i"
      "cs ! (Suc i mod length cs)"]
    by(auto simp: Let_def elim!: invar_search_props simp del: input_edge_iff)
qed

lemma contraction_recovering_structure:
  "invar_recovering_structure (qbs_hierarchy (Quadratic_Blossom_Search_upd7 state))
    (qbs_cycle_edges (Quadratic_Blossom_Search_upd7 state))
    (qbs_bases (Quadratic_Blossom_Search_upd7 state))
    (qbs_parents (Quadratic_Blossom_Search_upd7 state))"
proof-
  let ?cs = "c1 @ butlast (rev c2)"
  let ?S = "Quadratic_Blossom_Search_upd4 state"
  have invars: "invar_recovering_structure (qbs_hierarchy state) (qbs_cycle_edges state)
      (qbs_bases state) (qbs_parents state)"
    "hierarchy_ids (qbs_hierarchy state) \<subseteq> K"
    "edge_invar (qbs_cycle_edges ?S)"
    using contraction(2)
    by(auto simp: invar_search_def Quadratic_Blossom_Search_upd4_def
      invar_recovering_structure_def invar_representatives_def)
  have "set ?cs \<subseteq> K"
    using contraction_cycle_active contraction_active_bounds(1)
    by blast
  note recorded = process_cycle_maps_props[OF invars(3) this contraction_cycle(1),
    where k = "length c1" and edge = "(scanned_vertex state, scanned_neighbour state)" and b = b]
  show ?thesis
    unfolding contraction_selectors(3) contraction_recovery_maps
  proof(rule invar_recovering_structure_merge[OF invars(1) contraction_hierarchy_precond invars(2) _ recorded(1)], goal_cases)
    case (3 i)
    show ?case
      using contraction_cycle_annotation[OF 3]
      by(simp only: Let_def recorded(3)[OF 3] scanning_cycle_witness)
  qed(insert contraction_fresh(1) recorded(2), auto simp: Quadratic_Blossom_Search_upd4_def)
qed


lemma contraction_search:
  "invar_search (Quadratic_Blossom_Search_upd7 state)"
  using contraction_adts invar_forest_holds_7 invar_matching_projection_holds_7
    contraction_representatives contraction_component_invariant contraction_neighbours
    contraction_current contraction_queue_invar contraction_scanned contraction_fresh_invariant
    contraction_annotations contraction_hierarchy_size invar_existence_holds_7
    contraction_result contraction_recovering_structure contraction_clear_hints
  by(auto intro!: invar_search_intro)

end

lemma
  assumes "Quadratic_Blossom_Search_call_7_conds state" "invar_search state"
  shows invar_search_holds_7[invar_holds_intros]:
      "invar_search (Quadratic_Blossom_Search_upd7 state)"
    and state_rel_exploration_holds_7[state_rel_holds_intros]:
      "state_rel_exploration state (Quadratic_Blossom_Search_upd7 state)"
  by(cases "longest_disj_sfx
        (rev (forest_path (qbs_forest state) (source_component state)))
        (rev (forest_path (qbs_forest state) (target_component state)))";
      cases "queue_pop (qbs_fresh state)";
      auto intro: contraction_search[OF assms] contraction_exploration[OF assms])+

lemma invar_adts_holds_7[invar_holds_intros]:
  "\<lbrakk>Quadratic_Blossom_Search_call_7_conds state; invar_search state\<rbrakk> \<Longrightarrow>
    invar_adts (Quadratic_Blossom_Search_upd7 state)"
  by(blast dest: invar_search_holds_7 elim: invar_search_props)

lemma invar_queue_holds_7[invar_holds_intros]:
  "\<lbrakk>Quadratic_Blossom_Search_call_7_conds state; invar_search state\<rbrakk> \<Longrightarrow>
    invar_queue (Quadratic_Blossom_Search_upd7 state)"
  by(blast dest: invar_search_holds_7 elim: invar_search_props)

lemma invar_scanned_holds_7[invar_holds_intros]:
  "\<lbrakk>Quadratic_Blossom_Search_call_7_conds state; invar_search state\<rbrakk> \<Longrightarrow>
    invar_scanned (Quadratic_Blossom_Search_upd7 state)"
  by(blast dest: invar_search_holds_7 elim: invar_search_props)

lemma invar_recovering_structure_holds_7[invar_holds_intros]:
  "\<lbrakk>Quadratic_Blossom_Search_call_7_conds state; invar_search state\<rbrakk> \<Longrightarrow>
    invar_recovering_structure (qbs_hierarchy (Quadratic_Blossom_Search_upd7 state))
    (qbs_cycle_edges (Quadratic_Blossom_Search_upd7 state))
    (qbs_bases (Quadratic_Blossom_Search_upd7 state))
    (qbs_parents (Quadratic_Blossom_Search_upd7 state))"
  by(blast dest: invar_search_holds_7 elim: invar_search_props)

lemma invar_annotations_holds_7[invar_holds_intros]:
  "\<lbrakk>Quadratic_Blossom_Search_call_7_conds state; invar_search state\<rbrakk> \<Longrightarrow>
    invar_annotations (Quadratic_Blossom_Search_upd7 state)"
  by(blast dest: invar_search_holds_7 elim: invar_search_props)

subsection "Preservation and termination of the search loop"

lemma Quadratic_Blossom_Search_terminates:
  "invar_search state \<Longrightarrow> Quadratic_Blossom_Search_dom state"
proof(induction state rule: wf_induct_rule[OF wf_term_rel])
  case (1 state)
  show ?case
    by(rule Quadratic_Blossom_Search_domintros)
      (insert 1, auto intro: invar_holds_intros termination_intros elim: invar_search_props)
qed

lemma state_rel_exploration_refl[simp]:
  "state_rel_exploration state state"
  by(auto simp: state_rel_exploration_def)

lemma state_rel_exploration_trans:
  "\<lbrakk>state_rel_exploration a b; state_rel_exploration b c\<rbrakk> \<Longrightarrow> state_rel_exploration a c"
  by(auto simp: state_rel_exploration_def; blast)

lemmas search_exploration_step =
  state_rel_exploration_trans[of _ s "Quadratic_Blossom_Search s"] for s

lemma search_loop_preservation:
  assumes "Quadratic_Blossom_Search_dom state"
  shows "invar_search state \<Longrightarrow> invar_search (Quadratic_Blossom_Search state) \<and>
    state_rel_exploration state (Quadratic_Blossom_Search state)"
proof(induction rule: Quadratic_Blossom_Search_induct[OF assms])
  case IH: (1 state)
  note recursive = IH(2-8)[THEN conjunct1] IH(2-8)[THEN conjunct2]
  show ?case
    by(rule Quadratic_Blossom_Search_cases[where state = state])
      (insert IH(1,9), auto simp: Quadratic_Blossom_Search_simps Quadratic_Blossom_Search_ret1_def
        Quadratic_Blossom_Search_ret2_def intro!: search_exploration_step[where a = state] recursive
        intro: state_rel_holds_intros invar_holds_intros elim: invar_search_props call_cond_elims)
qed

lemmas invar_search_holds[invar_holds_intros] = search_loop_preservation[THEN conjunct1]
lemmas state_rel_exploration_holds[state_rel_holds_intros] = search_loop_preservation[THEN conjunct2]

lemma initial_search_properties:
  "Quadratic_Blossom_Search_dom initial_search_state"
  "invar_search (Quadratic_Blossom_Search_impl initial_search_state)"
  "state_rel_exploration initial_search_state (Quadratic_Blossom_Search_impl initial_search_state)"
  using initial_state_props Quadratic_Blossom_Search_terminates[of initial_search_state]
  by(auto simp: Quadratic_Blossom_Search_impl_same intro: invar_search_holds state_rel_exploration_holds)
subsection "Exhaustion and correctness of the search"

lemma exhausted_pending_arcs:
  "\<lbrakk>invar_search state; Quadratic_Blossom_Search_call_1_conds state\<rbrakk> \<Longrightarrow> pending_arcs state = {}"
  unfolding invar_search_def invar_adts_def invar_queue_def
  by(auto elim!: call_cond_elims simp: pending_arcs_def Work.queue_is_empty)

lemma exhausted_original_edge:
  assumes "invar_search state" "Quadratic_Blossom_Search_call_1_conds state"
    "{u,v} \<in> input_graph" "representative state u \<noteq> representative state v"
    "representative state u \<in> even_ids state"
  shows "representative state v \<in> odd_ids state"
  using assms exhausted_pending_arcs[OF assms(1,2)] input_edge_vertices[OF assms(3)]
  by(auto elim!: invar_search_props call_cond_elims
    simp: invar_scanned_def simp del: input_edge_iff; blast)

lemma exhausted_neighbours:
  "\<lbrakk>invar_search state; Quadratic_Blossom_Search_call_1_conds state;
    {x,y} \<in> quotient_graph state; x \<in> even_ids state\<rbrakk> \<Longrightarrow> y \<in> odd_ids state"
  by(auto simp: quotient_graph_def doubleton_eq_iff simp del: input_edge_iff
    intro: exhausted_original_edge; fastforce simp: insert_commute intro: exhausted_original_edge)

lemma closed_search_no_augpath:
  assumes "invar_forest state" "invar_representatives state"
    "\<And>x y. \<lbrakk>{x,y} \<in> quotient_graph state; x \<in> even_ids state\<rbrakk> \<Longrightarrow> y \<in> odd_ids state"
  shows "\<not> graph_augmenting_path (quotient_graph state) (mate_abstract (qbs_matching state)) p"
proof-
  interpret search: compute_alt_path fset_invar fset_abstract forest_odds forest_path forest_invar forest_roots
    forest_extend forest_empty K fset_empty forest_abstract forest_evens
    "quotient_graph state" "mate_abstract (qbs_matching state)"
    using assms(1)
    by(rule quotient_search)
  have forest: "forest_invar (mate_abstract (qbs_matching state)) (qbs_forest state)"
    using assms(1)
    by(auto elim!: invar_forest_props)
  show ?thesis
    by(intro notI, rule search.termination_conditions_no_augpath[where F = "qbs_forest state" and p = p])
      (insert assms forest quotient_active_vertices[of state]
        Forest.evens_and_odds_basis(4)[OF forest] Forest.evens_and_odds(4)[OF forest]
        Forest.roots(2)[OF forest],
        auto elim!: invar_forest_props simp: search.if1_cond_def search.if2_cond_def; blast)+
qed

lemma exhausted_no_augpath:
  "\<lbrakk>invar_search state; Quadratic_Blossom_Search_call_1_conds state\<rbrakk> \<Longrightarrow>
    \<not> (\<exists>p. graph_augmenting_path input_graph (mate_abstract M0) p)"
  using closed_search_no_augpath[of state] exhausted_neighbours[of state]
  by(auto elim!: invar_search_props simp: invar_existence_def)

lemma search_status_steps[simp]:
  "qbs_status (Quadratic_Blossom_Search_upd2 state) = qbs_status state"
  "qbs_status (Quadratic_Blossom_Search_upd3 state) = qbs_status state"
  "qbs_status (Quadratic_Blossom_Search_upd4 state) = qbs_status state"
  "qbs_status (Quadratic_Blossom_Search_upd5 state) = qbs_status state"
  "qbs_status (Quadratic_Blossom_Search_upd6 state) \<noteq> Quadratic_Exhausted"
  by(auto simp: Quadratic_Blossom_Search_upd2_def Quadratic_Blossom_Search_upd3_def
    Quadratic_Blossom_Search_upd4_def Quadratic_Blossom_Search_upd5_def
    Quadratic_Blossom_Search_upd6_def start_scan_def extend_search_def enqueue_vertex_def
    finish_search_def Let_def case_prod_beta)

lemma Quadratic_Blossom_Search_exhaustion:
  assumes "Quadratic_Blossom_Search_dom state" "invar_search state"
    "qbs_status state \<noteq> Quadratic_Exhausted"
    "qbs_status (Quadratic_Blossom_Search state) = Quadratic_Exhausted"
  shows "\<not> (\<exists>p. graph_augmenting_path input_graph (mate_abstract M0) p)"
proof(rule contrapos_pn[OF assms(4)], insert assms(2,3),
    induction rule: Quadratic_Blossom_Search_induct[OF assms(1)])
  case IH: (1 state)
  show ?case
    by(rule Quadratic_Blossom_Search_cases[where state = state])
      (insert IH, auto simp: Quadratic_Blossom_Search_simps[OF IH.hyps(1)]
        search_status_steps contraction_scan(2) Quadratic_Blossom_Search_ret_1_conds_def
        Quadratic_Blossom_Search_ret_2_conds_def Quadratic_Blossom_Search_ret2_def
        intro: invar_holds_intros dest: exhausted_no_augpath)
qed

lemma Quadratic_Blossom_Search_correct:
  "search_result_spec (Quadratic_Blossom_Search initial_search_state)"
  using initial_state_props initial_search_properties
    Quadratic_Blossom_Search_exhaustion[of initial_search_state]
    Quadratic_Blossom_Search_ret[of initial_search_state]
  by(cases "qbs_status (Quadratic_Blossom_Search initial_search_state)")
    (auto simp: search_result_spec_def invar_result_def Quadratic_Blossom_Search_impl_same
      Quadratic_Blossom_Search_ret_1_conds_def Quadratic_Blossom_Search_ret_2_conds_def
      elim!: invar_search_props)

lemma Quadratic_Blossom_Search_impl_correct:
  "search_result_spec (Quadratic_Blossom_Search_impl initial_search_state)"
  using Quadratic_Blossom_Search_correct initial_search_properties(1)
  by(simp add: Quadratic_Blossom_Search_impl_same)

end

section "Path recovery"

context Blossom_Path_Recovery
begin

lemma emit_vertex_adts[invar_holds_intros]:
  "\<lbrakk>invar_recovery_adts state; qbr_length state < output_cap\<rbrakk> \<Longrightarrow>
    invar_recovery_adts (emit_vertex v state)"
  by(auto simp: invar_recovery_adts_def emit_vertex_def Output.fixed_univ_map_upd_invar)

lemma next_component_adts[invar_holds_intros]:
  "\<lbrakk>invar_recovery_adts state; length (task_abstract (qbr_tasks state)) < task_cap\<rbrakk> \<Longrightarrow>
    invar_recovery_adts (next_component D state)"
  by(auto simp: invar_recovery_adts_def next_component_def Let_def Tasks.stack_push
    split: list.splits)

lemma visit_step_adts[invar_holds_intros]:
  "\<lbrakk>invar_recovery_adts state; a = z \<Longrightarrow> qbr_length state < output_cap;
    a \<noteq> z \<Longrightarrow> length (task_abstract (qbr_tasks state)) < task_cap\<rbrakk> \<Longrightarrow>
    invar_recovery_adts (visit_step D N b a z state)"
  by(auto simp: invar_recovery_adts_def visit_step_def emit_vertex_def Let_def
    Tasks.stack_push Output.fixed_univ_map_upd_invar)

lemma cycle_step_adts[invar_holds_intros]:
  "\<lbrakk>invar_recovery_adts state; length (task_abstract (qbr_tasks state)) + 2 \<le> task_cap\<rbrakk> \<Longrightarrow>
    invar_recovery_adts (cycle_step H B b i j forward a z state)"
  by(auto simp: invar_recovery_adts_def cycle_step_def Let_def case_prod_beta Tasks.stack_push)

lemma recovered_path_length[simp]:
  "length (recovered_path state) = qbr_length state"
  by(simp add: recovered_path_def)

lemma emit_vertex_path:
  "\<lbrakk>output_invar (qbr_output state); qbr_length state < output_cap\<rbrakk> \<Longrightarrow>
    recovered_path (emit_vertex v state) = recovered_path state @ [v]"
  by(auto simp: recovered_path_def emit_vertex_def upt_Suc_append
    Output.fixed_univ_map_upd intro!: map_cong)

end

context Quadratic_Blossom_Search_Lifting
begin

lemmas recovery_stack_simps = Recovery.Tasks.stack_push Recovery.Tasks.stack_pop
  Recovery.Tasks.stack_top Recovery.Tasks.stack_is_empty

lemma cycle_indices_rotation:
  assumes "0 < length (hierarchy_children H b)"
  shows "cycle_indices H b i j forward =
    take (Suc ((if forward then j + length (hierarchy_children H b) - i
      else i + length (hierarchy_children H b) - j) mod length (hierarchy_children H b)))
      (if forward then rotate i [0..<length (hierarchy_children H b)]
       else rev (rotate (Suc i) [0..<length (hierarchy_children H b)]))"
  using assms
  by(simp add: cycle_indices_def Let_def)

lemma cycle_indices_props:
  assumes "0 < length (hierarchy_children H b)"
  shows "cycle_indices H b i j forward \<noteq> []"
    "distinct (cycle_indices H b i j forward)"
    "set (cycle_indices H b i j forward) \<subseteq> {..<length (hierarchy_children H b)}"
    "length (cycle_indices H b i j forward) \<le> length (hierarchy_children H b)"
using assms cycle_indices_rotation[of H b i j forward]
  by(cases forward; auto simp: cycle_indices_def Let_def dest: in_set_takeD)+

lemma cycle_indices_head:
  "i < length (hierarchy_children H b) \<Longrightarrow> hd (cycle_indices H b i j forward) = i"
  by(auto simp: cycle_indices_def Let_def hd_conv_nth nth_rotate rev_nth add.commute
    simp del: upt_Suc rotate_Suc split: if_splits)

lemma cycle_indices_distance:
  fixes i j n :: nat
  assumes "i < n" "j < n"
  shows "(j + n - i) mod n = (if i \<le> j then j - i else j + n - i)"
proof(cases "i \<le> j")
  case True
  thus ?thesis
    using assms
    by(simp only: True if_True Nat.diff_add_assoc2[OF True] mod_add_self2; auto intro!: mod_less)
next
  case False
  thus ?thesis
    using assms
    by(auto intro!: mod_less; arith)
qed

lemma cycle_indices_forward:
  "\<lbrakk>i < length (hierarchy_children H b); j < length (hierarchy_children H b)\<rbrakk> \<Longrightarrow>
    cycle_indices H b i j True = (if i \<le> j then [i..<Suc j] else [i..<length (hierarchy_children H b)] @
    [0..<Suc j])"
  using gt_zero[of i "length (hierarchy_children H b)"]
  by(auto simp: cycle_indices_rotation rotate_drop_take cycle_indices_distance
    min_def simp del: upt_Suc; presburger)

lemma cycle_indices_backward:
  "\<lbrakk>i < length (hierarchy_children H b); j < length (hierarchy_children H b)\<rbrakk> \<Longrightarrow>
    cycle_indices H b i j False = (if j \<le> i then rev [j..<Suc i] else rev [0..<Suc i] @ rev [j..<length
    (hierarchy_children H b)])"
  using gt_zero[of i "length (hierarchy_children H b)"]
  by(cases "Suc i = length (hierarchy_children H b)";
    auto simp: cycle_indices_rotation rotate_drop_take cycle_indices_distance take_rev min_def
      simp del: upt_Suc rotate_Suc; presburger)

lemma cycle_indices_step:
  fixes forward
  assumes "i < length (hierarchy_children H b)" "j < length (hierarchy_children H b)"
  defines "k \<equiv> if forward then if Suc i = length (hierarchy_children H b) then 0 else Suc i
    else if i = 0 then length (hierarchy_children H b) - 1 else i - 1"
  shows "cycle_indices H b i j forward =
    (if i = j then [i] else i # cycle_indices H b k j forward)"
proof(cases forward)
  case True
  show ?thesis
    using assms(1,2) gt_zero[OF assms(1)] upt_conv_Cons[of i "Suc j"]
      upt_conv_Cons[of i "length (hierarchy_children H b)"]
    by(cases "Suc i = length (hierarchy_children H b)";
      auto simp: True k_def cycle_indices_forward simp del: upt_Suc; presburger)
next
  case False
  show ?thesis
    using assms(1,2) gt_zero[OF assms(1)]
    by(cases "i = 0";
      auto simp: False k_def cycle_indices_backward upt_Suc_append; presburger)
qed

lemma cycle_visits_step:
  fixes forward
  assumes "i < length (hierarchy_children H b)" "j < length (hierarchy_children H b)"
  defines "k \<equiv> if forward then if Suc i = length (hierarchy_children H b) then 0 else Suc i
    else if i = 0 then length (hierarchy_children H b) - 1 else i - 1"
  shows "cycle_visits H B b i j forward a z =
    (if i = j then [(hierarchy_children H b ! i, a, z)]
     else let e = cycle_edge B (hierarchy_children H b ! i) (hierarchy_children H b ! k) forward
       in (hierarchy_children H b ! i, a, fst e) #
         cycle_visits H B b k j forward (snd e) z)"
proof-
  have bounds: "0 < length (hierarchy_children H b)" "k < length (hierarchy_children H b)"
    using assms(1)
    by(auto simp: k_def; arith)+
  have route: "cycle_indices H b i j forward = (if i = j then [i] else i # cycle_indices H b k j forward)"
    using cycle_indices_step[OF assms(1,2), of forward]
    by(simp add: k_def)
  show ?thesis
    using cycle_indices_props(1)[OF bounds(1), of k j forward]
      cycle_indices_head[OF bounds(2), of j forward]
    unfolding cycle_visits_def route
    by(cases "i = j"; intro nth_equalityI;
      auto simp: Let_def map_upt_Suc nth_Cons' nth_map_upt hd_conv_nth Suc_diff_Suc simp del: upt_Suc)
qed

lemma cycle_visits_components:
  "map fst (cycle_visits H B b i j forward a z) =
    map ((!) (hierarchy_children H b)) (cycle_indices H b i j forward)"
  by(rule nth_equalityI) (simp_all add: cycle_visits_def Let_def)

lemma cycle_visits_components_props:
  assumes "0 < length (hierarchy_children H b)" "distinct (hierarchy_children H b)"
  shows "distinct (map fst (cycle_visits H B b i j forward a z))"
    "set (map fst (cycle_visits H B b i j forward a z)) \<subseteq> set (hierarchy_children H b)"
using assms cycle_indices_props(2,3)[of H b i j forward]
  by(auto simp: cycle_visits_components distinct_map
    intro!: inj_on_nth intro: nth_mem)

lemmas route_cached_targets = route_cached_def

lemma cache_route_index:
  assumes "recovery_tree H" "invar_navigation H D N" "hierarchy_ids H \<subseteq> K"
    "b \<in> hierarchy_ids H" "hierarchy_children H b \<noteq> []"
    "target \<in> hierarchy_members H b" "target \<noteq> nil" "invar_route_cache H J"
    "fst (link_lookup J b) = target \<Longrightarrow> route_cached H b target J"
  defines "J' \<equiv> Recovery.cache_route N target b J"
  shows "snd (link_lookup J' b) < length (hierarchy_children H b)"
    "target \<in> hierarchy_members H (hierarchy_children H b ! snd (link_lookup J' b))"
proof-
  have "b \<in> route_ancestors H b target"
    using assms(1,4-6) hierarchy_member_leaf[of H b target]
    by(auto simp: route_ancestors_def dest: rtranclD)
  thus "snd (link_lookup J' b) < length (hierarchy_children H b)"
    "target \<in> hierarchy_members H (hierarchy_children H b ! snd (link_lookup J' b))"
    using cache_route_correct[OF assms(1-4,6,8,9)] assms(4,5,7)
    by(auto simp: J'_def route_cached_targets invar_route_cache_def prod_eq_iff)
qed

lemma hierarchy_ancestor_internal:
  "(a,b) \<in> trancl (hierarchy_relation H) \<Longrightarrow> b \<in> hierarchy_ids H \<and> hierarchy_children H b \<noteq> []"
  by(auto simp: hierarchy_relation_def elim: tranclE)

lemma route_cached_mono:
  "\<lbrakk>route_cached H b target J; (c,b) \<in> rtrancl (hierarchy_relation H)\<rbrakk> \<Longrightarrow> route_cached H c target J"
  by(auto simp: route_cached_def route_ancestors_def intro: rtrancl_trans)

lemma route_cache_target_member:
  "\<lbrakk>recovery_tree H; invar_route_cache H J; c \<in> hierarchy_ids H;
    hierarchy_children H c \<noteq> []; fst (link_lookup J c) \<noteq> nil\<rbrakk> \<Longrightarrow>
    fst (link_lookup J c) \<in> hierarchy_members H c"
  by(fastforce simp: invar_route_cache_def recovery_tree_def Let_def)

lemma route_ancestors_members:
  "\<lbrakk>recovery_tree H; b \<in> hierarchy_ids H; target \<in> hierarchy_members H b;
    c \<in> route_ancestors H b target\<rbrakk> \<Longrightarrow> target \<in> hierarchy_members H c"
  by(auto simp: route_ancestors_def intro: hierarchy_member_ancestor)

lemma route_cached_preserved:
  "\<lbrakk>route_cached H b target J; target \<noteq> nil;
    \<And>c. fst (link_lookup J c) \<noteq> nil \<Longrightarrow> fst (link_lookup J' c) = fst (link_lookup J c)\<rbrakk> \<Longrightarrow>
    route_cached H b target J'"
  by(auto simp: route_cached_targets)

lemma invar_recovery_routing_mono:
  "\<lbrakk>invar_recovery_routing H B D before;
    set (pending_visits H B D after) \<subseteq> set (pending_visits H B D before);
    qbr_hints after = qbr_hints before\<rbrakk> \<Longrightarrow> invar_recovery_routing H B D after"
  by(auto simp: invar_recovery_routing_def; blast)

lemmas invar_recovery_routing_targets = invar_recovery_routing_def

lemma hierarchy_disjoint_route:
  "\<lbrakk>recovery_tree H; b \<in> hierarchy_ids H; target \<in> hierarchy_members H b;
    hierarchy_members H b \<inter> hierarchy_members H d = {}; (c,d) \<in> rtrancl (hierarchy_relation H)\<rbrakk> \<Longrightarrow>
    c \<notin> route_ancestors H b target"
  using route_ancestors_members[of H b target c] hierarchy_members_mono[of H c d]
  by blast

lemma routing_compatibility:
  "\<lbrakk>invar_recovery_routing H B D state; (b,a,z) \<in> set (pending_visits H B D state);
    a \<noteq> z; c \<in> hierarchy_ids H; hierarchy_children H c \<noteq> [];
    (c,b) \<in> rtrancl (hierarchy_relation H); fst (link_lookup (qbr_hints state) c) \<noteq> nil\<rbrakk> \<Longrightarrow>
    fst (link_lookup (qbr_hints state) c) = visit_target D b a z"
  by(auto simp: invar_recovery_routing_targets; blast)

lemma recovery_member_vertex:
  assumes "recovery_tree H" "b \<in> hierarchy_ids H" "v \<in> hierarchy_members H b"
  shows "v \<in> V0"
  using hierarchy_member_leaf[OF assms] assms(1)
  by(auto simp: recovery_tree_def Let_def)
lemma recovering_visit_props:
  assumes "recovery_tree H" "visit_admissible H D b a z" "a \<noteq> z"
  shows "b \<in> hierarchy_ids H" "hierarchy_children H b \<noteq> []"
    "visit_target D b a z \<in> hierarchy_members H b" "visit_target D b a z \<in> V0"
  using assms recovery_tree_node[of H b]
    recovery_member_vertex[where b=b and v="visit_target D b a z"]
  by(auto simp: visit_admissible_def visit_target_def)

lemma routing_visit_cache:
  fixes target J
  assumes "recovery_tree H" "invar_navigation H D N" "hierarchy_ids H \<subseteq> K" "nil \<notin> V0"
    "invar_recovery_routing H B D state" "(b,a,z) \<in> set (pending_visits H B D state)"
    "visit_admissible H D b a z" "a \<noteq> z"
  defines "target \<equiv> visit_target D b a z"
    and "J \<equiv> Recovery.cache_route N target b (qbr_hints state)"
  shows "invar_route_cache H J" (is ?cache)
    "\<forall>c \<in> hierarchy_ids H. \<forall>v i. hierarchy_children H c \<noteq> [] \<and> v \<noteq> nil \<and>
      link_lookup J c = (v,i) \<longrightarrow> route_cached H c v J" (is ?consistent)
    "\<forall>c \<in> hierarchy_ids H. hierarchy_children H c \<noteq> [] \<and>
      (c,b) \<in> rtrancl (hierarchy_relation H) \<and> fst (link_lookup J c) \<noteq> nil \<longrightarrow>
      fst (link_lookup J c) = target" (is ?targets)
proof-
  have input: "b \<in> hierarchy_ids H" "target \<in> hierarchy_members H b"
    "invar_route_cache H (qbr_hints state)" "hierarchy_children H b \<noteq> []" "target \<noteq> nil"
    using assms(1,4,5,7,8) recovering_visit_props[of H D b a z]
    by(auto simp: target_def invar_recovery_routing_def)
  have cache: "fst (link_lookup (qbr_hints state) b) = target \<Longrightarrow>
      route_cached H b target (qbr_hints state)"
    "\<And>c. \<lbrakk>c \<in> route_ancestors H b target; fst (link_lookup (qbr_hints state) c) \<noteq> nil\<rbrakk> \<Longrightarrow>
      fst (link_lookup (qbr_hints state) c) = target"
    using input assms(5,6,8)
    by(force simp: invar_recovery_routing_targets)
      (insert assms(5,6,8), auto simp: route_ancestors_def target_def dest: hierarchy_ancestor_internal
        intro: routing_compatibility[where b=b and a=a and z=z])
  note correct = cache_route_correct[OF assms(1-3) input(1-3) cache(1), folded J_def]
  have targets: "fst (link_lookup J c) = (if c \<in> route_ancestors H b target
      then target else fst (link_lookup (qbr_hints state) c))" for c
    using correct(2) cache_route_frame[OF assms(1-3) input(1-3), of c]
    by(auto simp: J_def route_cached_targets)
  have preserved: "fst (link_lookup (qbr_hints state) c) \<noteq> nil \<Longrightarrow>
      fst (link_lookup J c) = fst (link_lookup (qbr_hints state) c)" for c
    using cache(2)[of c]
    by(auto simp: targets)
  show ?cache ?consistent ?targets
    using correct assms(5,6,8) preserved
    by(auto simp: targets target_def invar_recovery_routing_targets prod_eq_iff route_ancestors_def
      intro: route_cached_mono route_cached_preserved split: if_splits)
qed

lemma recovery_pending_partition:
  assumes "invar_recovery_disjoint H B D state" "pending_visits H B D state = (b,a,z) # rest"
  shows "hierarchy_members H b \<inter> \<Union>(hierarchy_members H ` set (map fst rest)) = {}"
  using assms
  by(auto simp: invar_recovery_disjoint_def pending_members_def pairwise_def; blast)

lemma recovery_pending_head_disjoint:
  assumes "invar_recovery_disjoint H B D state"
    "pending_visits H B D state = (b,a,z) # rest" "(d,x,y) \<in> set rest"
  shows "hierarchy_members H b \<inter> hierarchy_members H d = {}"
  using recovery_pending_partition[OF assms(1,2)] assms(3)
  by force

lemma recovering_routing_replace:
  assumes "recovery_tree H" "invar_navigation H D N" "hierarchy_ids H \<subseteq> K" "nil \<notin> V0"
    "invar_recovery_routing H B D before" "invar_recovery_disjoint H B D before"
    "pending_visits H B D before = (b,a,z) # rest" "visit_admissible H D b a z" "a \<noteq> z"
    "pending_visits H B D after = visits @ rest"
    "qbr_hints after = Recovery.cache_route N (visit_target D b a z) b (qbr_hints before)"
    "\<And>d x y. (d,x,y) \<in> set visits \<Longrightarrow> (d,b) \<in> rtrancl (hierarchy_relation H)"
    "\<And>d x y. \<lbrakk>(d,x,y) \<in> set visits; x \<noteq> y; visit_target D b a z \<in> hierarchy_members H d\<rbrakk> \<Longrightarrow>
      visit_target D d x y = visit_target D b a z"
  shows "invar_recovery_routing H B D after"
proof-
  let ?J = "Recovery.cache_route N (visit_target D b a z) b (qbr_hints before)"
  have "(b,a,z) \<in> set (pending_visits H B D before)"
    using assms(7)
    by simp
  note cached = routing_visit_cache[OF assms(1-5) this assms(8,9)]
  show ?thesis
    using cached(1,2)
  proof(auto simp: invar_recovery_routing_targets assms(10,11) prod_eq_iff, goal_cases)
    case (1 d x y c)
    have "fst (link_lookup ?J c) = visit_target D b a z"
      using 1 cached(3) rtrancl_trans[OF 1(6) assms(12)[OF 1(8)]]
      by auto
    moreover have "fst (link_lookup ?J c) \<in> hierarchy_members H d"
      using 1 assms(1) route_cache_target_member[of H ?J c] hierarchy_members_mono[of H c d]
      by auto
    ultimately show ?case
      using 1 assms(13)
      by auto
  next
    case (2 d x y c)
    have "c \<notin> route_ancestors H b (visit_target D b a z)"
      using 2 assms(1,6-8)
      by(intro hierarchy_disjoint_route[where d=d] recovery_pending_head_disjoint)
        (auto simp: visit_admissible_def visit_target_def)
    hence "link_lookup ?J c = link_lookup (qbr_hints before) c"
      using assms(1-3,5,8) cache_route_frame[of H D N b "visit_target D b a z" "qbr_hints before" c]
      by(auto simp: invar_recovery_routing_targets visit_admissible_def visit_target_def)
    thus ?case
      using 2 assms(5,7) routing_compatibility[of H B D before d x y c]
      by auto
  qed
qed

lemma visit_route_singleton:
  "visit_admissible H D b a a \<Longrightarrow> visit_route H D b a a [a]"
  by(auto simp: visit_route_def visit_admissible_def alt_list_empty)

lemma visit_route_same:
  "visit_route H D b a a p \<Longrightarrow> p = [a]"
  by(cases p; auto simp: visit_route_def split: if_splits dest: last_in_set)

lemma cycle_indices_reverse:
  "\<lbrakk>i < length (hierarchy_children H b); j < length (hierarchy_children H b)\<rbrakk> \<Longrightarrow>
    rev (cycle_indices H b i j forward) = cycle_indices H b j i (\<not> forward)"
  by(cases forward; auto simp: cycle_indices_forward cycle_indices_backward)

lemma cycle_edge_reverse:
  "cycle_edge B d c (\<not> forward) = prod.swap (cycle_edge B c d forward)"
  by(cases forward; simp add: cycle_edge_def prod.swap_def case_prod_beta)

lemma visit_route_reverse:
  assumes "visit_route H D b a z p"
  shows "visit_route H D b z a (rev p)"
proof(cases "a = z")
  case True
  show ?thesis
    using assms visit_route_same[of H D b a p] True
    by simp
next
  case False
  show ?thesis
    using assms False alt_list_rev_even[of "\<lambda>e. e \<notin> mate_abstract M0" "\<lambda>e. e \<in> mate_abstract M0"
        "edges_of_path p"]
      rev_of_rev_alt_path_is_alt_path[of "mate_abstract M0" p]
    by(auto simp: visit_route_def visit_admissible_def hd_rev last_rev
      edges_of_path_rev[symmetric] edges_of_path_length split: if_splits)
qed

lemma cycle_indices_last:
  "\<lbrakk>i < length (hierarchy_children H b); j < length (hierarchy_children H b)\<rbrakk> \<Longrightarrow>
    last (cycle_indices H b i j forward) = j"
  by(cases forward; auto simp: cycle_indices_forward cycle_indices_backward last_rev last_append)

lemma cycle_base_indices_odd:
  "\<lbrakk>odd (length (hierarchy_children H b)); i < length (hierarchy_children H b)\<rbrakk> \<Longrightarrow>
    odd (length (cycle_indices H b 0 i (even i)))"
  using gt_zero[of i "length (hierarchy_children H b)"]
  by(cases "even i"; auto simp: cycle_indices_forward cycle_indices_backward; presburger)

lemma cycle_base_indices_edges:
  assumes "odd (length (hierarchy_children H b))" "i < length (hierarchy_children H b)"
  defines "rs \<equiv> cycle_indices H b 0 i (even i)"
  assumes "k < length rs - 1"
  shows "(if even i then Suc (rs ! k) mod length (hierarchy_children H b) = rs ! Suc k \<and>
      (odd (rs ! k) \<longleftrightarrow> odd k)
    else Suc (rs ! Suc k) mod length (hierarchy_children H b) = rs ! k \<and>
      (odd (rs ! Suc k) \<longleftrightarrow> odd k))"
using assms(1,2,4) gt_zero[of i "length (hierarchy_children H b)"]
  by(cases "even i"; cases "k = 0";
    auto simp: rs_def cycle_indices_forward cycle_indices_backward nth_Cons' rev_nth
      Suc_diff_Suc upt_Suc[of 0 0] simp del: upt_Suc; presburger)

lemma recovering_cycle_edge:
  "\<lbrakk>invar_recovering_structure H B D N; b \<in> hierarchy_ids H;
    i < length (hierarchy_children H b)\<rbrakk> \<Longrightarrow>
    let cs = hierarchy_children H b; e = edge_lookup B (cs ! i)
    in fst e \<in> hierarchy_members H (cs ! i) \<and>
      snd e \<in> hierarchy_members H (cs ! (Suc i mod length cs)) \<and>
      {fst e, snd e} \<in> input_graph \<and> ({fst e, snd e} \<in> mate_abstract M0 \<longleftrightarrow> odd i)"
  by(auto simp: invar_recovering_structure_def Let_def case_prod_beta)

lemma cycle_base_crossing:
  assumes "invar_recovering_structure H B D N" "b \<in> hierarchy_ids H"
    "i < length (hierarchy_children H b)"
  defines "rs \<equiv> cycle_indices H b 0 i (even i)"
  assumes "k < length rs - 1"
  shows "let cs = hierarchy_children H b; c = cs ! (rs ! k); d = cs ! (rs ! Suc k);
       e = cycle_edge B c d (even i)
    in fst e \<in> hierarchy_members H c \<and> snd e \<in> hierarchy_members H d \<and>
      {fst e, snd e} \<in> input_graph \<and> ({fst e, snd e} \<in> mate_abstract M0 \<longleftrightarrow> odd k)"
proof-
  have bounds: "0 < length (hierarchy_children H b)" "k < length rs" "Suc k < length rs"
    using assms(3,5)
    by arith+
  have "odd (length (hierarchy_children H b))"
    using assms(1,2) bounds(1)
    by(auto simp: invar_recovering_structure_def recovery_tree_def Let_def)
  moreover have "rs ! k < length (hierarchy_children H b)"
    "rs ! Suc k < length (hierarchy_children H b)"
    using cycle_indices_props(3)[of H b 0 i "even i"] bounds
    by(auto simp only: rs_def subset_iff lessThan_iff dest: nth_mem)
  ultimately show ?thesis
    using assms recovering_cycle_edge[of H B D N b "rs ! k"]
      recovering_cycle_edge[of H B D N b "rs ! Suc k"]
      cycle_base_indices_edges[of H b i k, folded rs_def]
    by(auto simp: Let_def cycle_edge_def case_prod_beta insert_commute split: if_splits)
qed

lemma visit_route_directions:
  assumes "visit_route H D b a z p"
  shows "a = base_lookup D b \<Longrightarrow> alt_path (mate_abstract M0) p"
    "z = base_lookup D b \<Longrightarrow> rev_alt_path (mate_abstract M0) p"
  using assms visit_route_same[of H D b a p]
  by(cases "a = z"; auto simp: visit_route_def alt_list_empty)+

lemma visit_routes_concat:
  assumes "list_all2 (\<lambda>(c,a,z) p. visit_route H D c a z p) visits ps"
    "distinct (map fst visits)"
    "pairwise (\<lambda>c d. hierarchy_members H c \<inter> hierarchy_members H d = {}) (set (map fst visits))"
    "\<And>k. k < length visits \<Longrightarrow> if even k = forward
      then fst (snd (visits ! k)) = base_lookup D (fst (visits ! k))
      else snd (snd (visits ! k)) = base_lookup D (fst (visits ! k))"
    "\<And>k. k < length visits - 1 \<Longrightarrow>
      {snd (snd (visits ! k)), fst (snd (visits ! Suc k))} \<in> input_graph \<and>
      ({snd (snd (visits ! k)), fst (snd (visits ! Suc k))} \<in> mate_abstract M0 \<longleftrightarrow> odd k = forward)"
  shows "(visits \<noteq> [] \<longrightarrow> concat ps \<noteq> [] \<and>
      hd (concat ps) = fst (snd (hd visits)) \<and> last (concat ps) = snd (snd (last visits))) \<and>
    distinct (concat ps) \<and> set (concat ps) \<subseteq> \<Union>(hierarchy_members H ` set (map fst visits)) \<and>
    odd (length (concat ps)) = odd (length visits) \<and>
    set (edges_of_path (concat ps)) \<subseteq> input_graph \<and>
    alt_list (if forward then (\<lambda>e. e \<notin> mate_abstract M0) else (\<lambda>e. e \<in> mate_abstract M0))
      (if forward then (\<lambda>e. e \<in> mate_abstract M0) else (\<lambda>e. e \<notin> mate_abstract M0))
      (edges_of_path (concat ps))" (is "?properties visits ps forward")
using assms
proof(induction arbitrary: forward rule: list_all2_induct)
  case Nil
  then show ?case
    by(simp add: alt_list_empty)
next
  case (Cons v visits p ps)
  have tail: "?properties visits ps (\<not> forward)"
    by(rule Cons.IH)
      (insert Cons.prems(1,2),
       auto dest: Cons.prems(3,4)[of "Suc _", simplified] simp: pairwise_def less_diff_conv)
  have first: "p \<noteq> []" "distinct p" "odd (length p)" "even (length (edges_of_path p))"
    "hd p = fst (snd v)" "last p = snd (snd v)"
    "set p \<subseteq> hierarchy_members H (fst v)" "set (edges_of_path p) \<subseteq> input_graph"
    "alt_list (if forward then (\<lambda>e. e \<notin> mate_abstract M0) else (\<lambda>e. e \<in> mate_abstract M0))
      (if forward then (\<lambda>e. e \<in> mate_abstract M0) else (\<lambda>e. e \<notin> mate_abstract M0))
      (edges_of_path p)"
    using Cons.hyps(1) Cons.prems(3)[of 0]
      visit_route_directions[of H D "fst v" "fst (snd v)" "snd (snd v)" p]
    by(cases v; cases forward; auto simp: visit_route_def edges_of_path_length case_prod_beta)+
  have "\<And>d. d \<in> set (map fst visits) \<Longrightarrow> hierarchy_members H (fst v) \<inter> hierarchy_members H d = {}"
    using Cons.prems(1,2)
    by(auto simp: pairwise_def)
  hence disjoint: "set p \<inter> set (concat ps) = {}"
    using first(7) tail
    by blast
  have crossing: "visits \<noteq> [] \<Longrightarrow> {last p, hd (concat ps)} \<in> input_graph \<and>
      ({last p, hd (concat ps)} \<in> mate_abstract M0 \<longleftrightarrow> \<not> forward)"
    using first tail Cons.prems(4)[of 0]
    by(cases visits; auto)
  show ?case
    using tail first disjoint crossing Cons.hyps(2)
    by(cases visits; cases "concat ps"; cases forward;
      auto simp: distinct_append edges_of_path_append_3[of p] alt_list_step
        intro!: alt_list_append_3)
qed

lemma recovering_children:
  assumes "invar_recovering_structure H B D N" "b \<in> hierarchy_ids H"
    "hierarchy_children H b \<noteq> []"
  shows "distinct (hierarchy_children H b)" "odd (length (hierarchy_children H b))"
    "3 \<le> length (hierarchy_children H b)" "set (hierarchy_children H b) \<subseteq> hierarchy_ids H"
    "hierarchy_members H b = \<Union>(hierarchy_members H ` set (hierarchy_children H b))"
    "pairwise (\<lambda>c d. hierarchy_members H c \<inter> hierarchy_members H d = {}) (set (hierarchy_children H b))"
    "base_lookup D b = base_lookup D (hd (hierarchy_children H b))"
  using assms
  by(auto simp: invar_recovering_structure_def recovery_tree_def invar_navigation_def Let_def)

lemma recovering_children_disjoint:
  "\<lbrakk>invar_recovering_structure H B D N; b \<in> hierarchy_ids H; i < length (hierarchy_children H b); j <
    length (hierarchy_children H b); i \<noteq> j\<rbrakk> \<Longrightarrow> hierarchy_members H
    (hierarchy_children H b ! i) \<inter> hierarchy_members H (hierarchy_children H b ! j) = {}"
  using recovering_children(1,6)[of H B D N b]
  by(cases "hierarchy_children H b = []") (auto simp: pairwise_def nth_eq_iff_index_eq dest: nth_mem)

lemmas visit_routes_concat_properties = visit_routes_concat[where forward=True, simplified HOL.eq_True if_True]

lemma cycle_visits_endpoints:
  "fst (snd (hd (cycle_visits H B b i j forward a z))) = a"
  "snd (snd (last (cycle_visits H B b i j forward a z))) = z"
  by(simp_all add: cycle_visits_def cycle_indices_def Let_def hd_map last_map
    del: upt_Suc)

lemma cycle_visits_reverse:
  assumes "i < length (hierarchy_children H b)" "j < length (hierarchy_children H b)"
  shows "cycle_visits H B b j i (\<not> forward) z a =
    map (\<lambda>(c, x, y). (c, y, x)) (rev (cycle_visits H B b i j forward a z))"
unfolding cycle_visits_def cycle_indices_reverse[OF assms, symmetric]
  by(intro nth_equalityI; auto simp: Let_def rev_nth nth_map_upt cycle_edge_reverse
    prod.swap_def case_prod_beta Suc_diff_Suc split: if_splits)

lemma recovering_completion_replace_visit:
  assumes "invar_recovery_completion H B D before"
    "pending_visits H B D before = (b, a, z) # rest"
    "pending_visits H B D after = visits @ rest"
    "Recovery.recovered_path after = Recovery.recovered_path before"
    "\<And>paths. list_all2 (\<lambda>(c, x, y) p. visit_route H D c x y p) visits paths \<Longrightarrow>
      visit_route H D b a z (concat paths)"
  shows "invar_recovery_completion H B D after"
proof(unfold invar_recovery_completion_def assms(3,4) list_all2_append1, clarify, goal_cases)
  case (1 ps paths rest_paths)
  show ?case
    using assms(1)[unfolded invar_recovery_completion_def, rule_format, of "concat paths # rest_paths"]
      assms(5)[OF 1(3)] 1(4)
    by(simp add: assms(2))
qed

lemma hierarchy_size_positive:
  "\<lbrakk>recovery_tree H; b \<in> hierarchy_ids H\<rbrakk> \<Longrightarrow> 0 < hierarchy_size H b"
  using hierarchy_members_finite_nonempty[of H b]
  by(auto simp: hierarchy_size_def card_gt_0_iff)

lemma hierarchy_members_card_children:
  assumes "recovery_tree H" "b \<in> hierarchy_ids H" "hierarchy_children H b \<noteq> []"
  shows "card (hierarchy_members H b) =
    sum_list (map (\<lambda>c. card (hierarchy_members H c)) (hierarchy_children H b))"
proof-
  have "card (\<Union>c \<in> set (hierarchy_children H b). hierarchy_members H c) =
      (\<Sum>c \<in> set (hierarchy_children H b). card (hierarchy_members H c))"
    using assms recovery_tree_node[OF assms(1,2)] hierarchy_members_finite_nonempty[of H]
    by(intro card_UN_disjoint) (auto simp: pairwise_def)
  thus ?thesis
    using assms(3) recovery_tree_node[OF assms(1,2)]
    by(simp add: sum_list_distinct_conv_sum_set)
qed

lemma sum_list_positive_weights:
  assumes "\<forall>c \<in> set cs. 0 < f c"
  shows "sum_list (map (\<lambda>c. 4 * f c - 1) cs) + length cs = 4 * sum_list (map f cs)"
    "sum_list (map (\<lambda>c. 4 * f c - 2) cs) + length cs =
      sum_list (map (\<lambda>c. 4 * f c - 1) cs)"
  using assms
  by(induction cs) (auto; linarith)+

lemma hierarchy_selected_tasks_measure:
  assumes "recovery_tree H" "b \<in> hierarchy_ids H"
    "distinct cs" "set cs \<subseteq> set (hierarchy_children H b)"
  shows "sum_list (map (\<lambda>c. 4 * hierarchy_size H c - 2) cs) + length cs < 4 * hierarchy_size H b - 2"
proof(cases "hierarchy_children H b = []")
  case True
  thus ?thesis
    using assms(4) recovery_tree_node[OF assms(1,2)]
    by(auto simp: hierarchy_size_def)
next
  case False
  have "\<forall>c \<in> set (hierarchy_children H b). 0 < card (hierarchy_members H c)"
    using hierarchy_members_finite_nonempty[of H] recovery_tree_node[OF assms(1,2)] assms(1) False
    by(auto simp: card_gt_0_iff)
  hence "sum_list (map (\<lambda>c. 4 * card (hierarchy_members H c) - 1) (hierarchy_children H b)) +
      length (hierarchy_children H b) =
      4 * sum_list (map (\<lambda>c. card (hierarchy_members H c)) (hierarchy_children H b))"
    "sum_list (map (\<lambda>c. 4 * card (hierarchy_members H c) - 2) cs) + length cs =
      sum_list (map (\<lambda>c. 4 * card (hierarchy_members H c) - 1) cs)"
    using assms(4)
    by(intro sum_list_positive_weights; blast)+
  moreover have "sum_list (map (\<lambda>c. 4 * card (hierarchy_members H c) - 1) cs) \<le>
    sum_list (map (\<lambda>c. 4 * card (hierarchy_members H c) - 1) (hierarchy_children H b))"
    using assms(3,4) recovery_tree_node[OF assms(1,2)] False
    by(auto simp: sum_list_distinct_conv_sum_set intro: sum_mono2)
  ultimately show ?thesis
    using hierarchy_members_card_children[OF assms(1,2) False] recovery_tree_node[OF assms(1,2)] False
    by(auto simp: hierarchy_size_def; linarith)
qed

lemma next_component_decreases:
  "\<lbrakk>task_invar (qbr_tasks state); task_is_empty (qbr_tasks state);
    qbr_path state \<noteq> []; 0 < task_cap\<rbrakk> \<Longrightarrow>
    recovery_measure H B (Recovery.next_component D state) < recovery_measure H B state"
  by(cases "qbr_path state") (auto simp: Recovery.next_component_def Let_def recovery_measure_def
    task_measure_def task_visits_def recovery_stack_simps split: list.splits)

lemma cycle_task_less_visit:
  assumes "recovery_tree H" "invar_navigation H D N" "b \<in> hierarchy_ids H"
    "hierarchy_children H b \<noteq> []"
  shows "task_measure H B (Quadratic_Cycle b i j forward a z) <
    task_measure H B (Quadratic_Visit b a z)"
  using hierarchy_selected_tasks_measure[OF assms(1,3),
    where cs = "map fst (cycle_visits H B b i j forward a z)"]
    cycle_visits_components_props[of H b B i j forward a z] assms(1,3,4)
  by(auto simp: task_measure_def task_visits_def map_map comp_def case_prod_beta
    cycle_visits_def Let_def recovery_tree_def)

lemma cycle_step_decreases:
  assumes "task_invar (qbr_tasks state)" "task_abstract (qbr_tasks state) \<noteq> []"
    "task_top (qbr_tasks state) = Quadratic_Cycle b i j forward a z"
    "length (task_abstract (qbr_tasks state)) < task_cap"
    "i < length (hierarchy_children H b)" "j < length (hierarchy_children H b)"
  shows "recovery_measure H B (Recovery.cycle_step H B b i j forward a z
      (state\<lparr>qbr_tasks := task_pop (qbr_tasks state)\<rparr>)) < recovery_measure H B state"
  using assms cycle_visits_step[OF assms(5,6), where forward = forward and B = B and a = a and z = z]
    cycle_indices_step[OF assms(5,6), where forward = forward]
  by(cases "task_abstract (qbr_tasks state)"; cases "i = j"; cases forward) (auto simp: Recovery.cycle_step_def
    recovery_measure_def task_measure_def task_visits_def recovery_stack_simps Let_def case_prod_beta
    cycle_edge_def split: if_splits)

lemma visit_step_decreases:
  assumes "recovery_tree H" "invar_navigation H D N"
    "task_invar (qbr_tasks state)" "task_abstract (qbr_tasks state) \<noteq> []"
    "task_top (qbr_tasks state) = Quadratic_Visit b a z"
    "length (task_abstract (qbr_tasks state)) < task_cap" "visit_admissible H D b a z"
  shows "recovery_measure H B (Recovery.visit_step D N b a z
      (state\<lparr>qbr_tasks := task_pop (qbr_tasks state)\<rparr>)) < recovery_measure H B state"
proof-
  have vertex: "b \<in> hierarchy_ids H"
    using assms(7)
    by(simp add: visit_admissible_def)
  have "a \<noteq> z \<Longrightarrow> task_measure H B (Quadratic_Cycle b i j forward a z) <
      task_measure H B (Quadratic_Visit b a z)" for i j forward
    using assms(1,7) recovering_visit_props(2)[of H D b a z]
    by(intro cycle_task_less_visit[OF assms(1,2) vertex]) auto
  thus ?thesis
    using assms(3-6) hierarchy_size_positive[OF assms(1) vertex]
    by(cases "task_abstract (qbr_tasks state)"; cases "a = z";
      auto simp: Recovery.visit_step_def Recovery.emit_vertex_def recovery_measure_def
        recovery_stack_simps Let_def split: if_splits;
        auto simp: task_measure_def task_visits_def)
qed

lemma recovery_stack_properties:
  assumes "invar_recovery H B D N state" "\<not> task_is_empty (qbr_tasks state)"
  defines "popped \<equiv> state\<lparr>qbr_tasks := task_pop (qbr_tasks state)\<rparr>"
  shows "task_invar (qbr_tasks state)" "task_abstract (qbr_tasks state) \<noteq> []"
    "task_admissible H B D (task_top (qbr_tasks state))"
    "Recovery.invar_recovery_adts popped"
    "list_all (task_admissible H B D) (task_abstract (qbr_tasks popped))"
    "length (task_abstract (qbr_tasks popped)) < card (hierarchy_ids H)"
    "pending_visits H B D state = task_visits H B (task_top (qbr_tasks state)) @ pending_visits H B D popped"
  using assms(1,2)
  by(cases "task_abstract (qbr_tasks state)"; auto simp: popped_def invar_recovery_def
    Recovery.invar_recovery_adts_def invar_recovery_tasks_def pending_visits_def quotient_visits_def Let_def
    recovery_stack_simps)+

lemma recovery_call_1_terminates[termination_intros]:
  assumes "invar_recovery H B D N state" "Suc (card (hierarchy_ids H)) \<le> task_cap"
    "Recovery.Blossom_Path_Recovery_call_1_conds state"
  shows "(Recovery.Blossom_Path_Recovery_upd1 H B D N state, state) \<in> Blossom_Path_Recovery_term_rel' H B"
proof-
  have "task_invar (qbr_tasks state)" "recovery_tree H" "invar_navigation H D N"
    "length (task_abstract (qbr_tasks state)) < task_cap"
    using assms(1,2)
    by(auto elim!: invar_recovery_props Recovery.invar_recovery_adts_props invar_recovery_tasks_props simp:
      invar_recovering_structure_def)
  thus ?thesis
    using assms(3) recovery_stack_properties(3)[OF assms(1)]
    by(cases "task_is_empty (qbr_tasks state)"; cases "task_top (qbr_tasks state)"; auto simp:
      Blossom_Path_Recovery_term_rel'_def Recovery.Blossom_Path_Recovery_upd1_def Recovery.recovery_step_def
      task_admissible_def Let_def recovery_stack_simps Recovery.Blossom_Path_Recovery_call_1_conds_def
      Recovery.recovery_done_def intro: next_component_decreases visit_step_decreases cycle_step_decreases)
qed

lemma recovery_pending_admissible:
  "\<lbrakk>invar_recovery_tasks H B D state; (b,a,z) \<in> set (pending_visits H B D state)\<rbrakk> \<Longrightarrow>
    visit_admissible H D b a z"
  by(auto simp: invar_recovery_tasks_def list_all_iff)

lemma recovery_stack_space:
  "\<lbrakk>invar_recovery_tasks H B D state; Suc (card (hierarchy_ids H)) \<le> task_cap\<rbrakk> \<Longrightarrow>
    length (task_abstract (qbr_tasks state)) < task_cap"
  by(auto simp: invar_recovery_tasks_def)

lemma recovery_output_space:
  assumes "recovery_tree H" "finite V0" "card V0 \<le> output_cap"
    "invar_recovery_tasks H B D state" "invar_recovery_disjoint H B D state"
    "(b,a,z) \<in> set (pending_visits H B D state)"
  shows "qbr_length state < output_cap"
proof-
  have "a \<in> V0" "a \<in> pending_members H B D state"
    using assms(1,6) recovery_pending_admissible[OF assms(4,6)]
    by(auto simp: visit_admissible_def pending_members_def
      intro!: bexI[where x="(b,a,z)"] intro: recovery_member_vertex)
  hence "card (set (Recovery.recovered_path state)) < card V0"
    using assms(2,5)
    by(intro psubset_card_mono) (auto simp: invar_recovery_disjoint_def)
  thus ?thesis
    using assms(3,5)
    by(auto simp: invar_recovery_disjoint_def distinct_card intro: less_le_trans)
qed

lemma task_visits_nonempty[simp]: "task_visits H B task \<noteq> []"
  by(cases task) (auto simp: task_visits_def cycle_visits_def cycle_indices_def Let_def)

lemma recovery_stack_output_space:
  assumes "invar_recovery H B D N state" "\<not> task_is_empty (qbr_tasks state)"
    "finite V0" "card V0 \<le> output_cap"
  shows "qbr_length state < output_cap"
proof-
  obtain b a z where "(b,a,z) \<in> set (pending_visits H B D state)"
    using recovery_stack_properties(7)[OF assms(1,2)]
    by(cases "task_visits H B (task_top (qbr_tasks state))"; auto)
  thus ?thesis
    using assms
    by(intro recovery_output_space[where H=H and B=B and D=D and b=b and a=a and z=z])
      (auto elim!: invar_recovery_props simp: invar_recovering_structure_def)
qed

lemma invar_recovery_adts_holds_1[invar_holds_intros]:
  assumes "finite V0" "card V0 \<le> output_cap" "Suc (card (hierarchy_ids H)) \<le> task_cap"
    "invar_recovery H B D N state"
  shows "Recovery.invar_recovery_adts (Recovery.Blossom_Path_Recovery_upd1 H B D N state)"
proof-
  have inv: "Recovery.invar_recovery_adts state" "length (task_abstract (qbr_tasks state)) < task_cap"
    using assms
    by(auto elim!: invar_recovery_props intro: recovery_stack_space)
  have pop: "\<not> task_is_empty (qbr_tasks state) \<Longrightarrow>
      Recovery.invar_recovery_adts (state\<lparr>qbr_tasks := task_pop (qbr_tasks state)\<rparr>) \<and>
      length (task_abstract (task_pop (qbr_tasks state))) + 2 \<le> task_cap"
    using recovery_stack_properties(4,6)[OF assms(4)] assms(3)
    by auto
  show ?thesis
    using inv pop recovery_stack_output_space[OF assms(4) _ assms(1,2)]
    by(cases "task_is_empty (qbr_tasks state)"; cases "task_top (qbr_tasks state)";
      auto simp: Recovery.Blossom_Path_Recovery_upd1_def Recovery.recovery_step_def Let_def
      intro: Recovery.next_component_adts Recovery.visit_step_adts Recovery.cycle_step_adts)
qed

lemma initial_recovery_adts:
  "recovery_workspaces H T out \<Longrightarrow>
    Recovery.invar_recovery_adts (Recovery.initial_recovery p es T J out)"
  by(simp add: recovery_workspaces_def Recovery.invar_recovery_adts_def Recovery.initial_recovery_def)

lemma initial_recovery_tasks:
  "\<lbrakk>task_abstract T = [];
    list_all (\<lambda>(b, a, z). visit_admissible H D b a z)
      (pending_visits H B D (Recovery.initial_recovery p es T J out))\<rbrakk> \<Longrightarrow>
    invar_recovery_tasks H B D (Recovery.initial_recovery p es T J out)"
  by(simp add: invar_recovery_tasks_def Recovery.initial_recovery_def)

lemma initial_recovery_pending:
  "task_abstract T = [] \<Longrightarrow>
    map fst (pending_visits H B D (Recovery.initial_recovery p es T J out)) = p"
  by(simp add: pending_visits_def quotient_visits_def Recovery.initial_recovery_def
    comp_def Let_def map_nth)

lemma initial_recovery_routing:
  "\<lbrakk>link_invar J;
    \<And>b. \<lbrakk>b \<in> hierarchy_ids H; hierarchy_children H b \<noteq> []\<rbrakk> \<Longrightarrow> fst (link_lookup J b) = nil\<rbrakk> \<Longrightarrow>
    invar_recovery_routing H B D (Recovery.initial_recovery p es T J out)"
  by(fastforce simp: invar_recovery_routing_def invar_route_cache_def Recovery.initial_recovery_def)

lemma initial_recovery_disjoint:
  assumes "task_abstract T = []" "distinct p" "set p \<subseteq> active_ids state"
    "invar_representatives state"
  shows "invar_recovery_disjoint (qbs_hierarchy state) B D
    (Recovery.initial_recovery p es T J out)"
proof-
  have members: "hierarchy_members (qbs_hierarchy state) b = {u \<in> V0. representative state u = b}"
    if "b \<in> set p" for b
    using assms(3,4) that
    by(auto simp: invar_representatives_def)
  show ?thesis
    using assms(1,2)
    by(simp only: invar_recovery_disjoint_def initial_recovery_pending)
      (auto simp: Recovery.recovered_path_def Recovery.initial_recovery_def pairwise_def members)
qed

lemma visit_target_reverse:
  "visit_admissible H D b a z \<Longrightarrow> visit_target D b z a = visit_target D b a z"
  by(auto simp: visit_target_def visit_admissible_def)

lemma visit_routes_reverse:
  "list_all2 (\<lambda>(c, a, z) p. visit_route H D c a z p) visits ps \<Longrightarrow>
    list_all2 (\<lambda>(c, a, z) p. visit_route H D c a z p)
      (map (\<lambda>(c, a, z). (c, z, a)) (rev visits)) (map rev (rev ps))"
  unfolding list_all2_map1 list_all2_map2 list_all2_rev
  by(erule list_all2_mono) (auto intro: visit_route_reverse split: prod.splits)

lemma cycle_selected_visits:
  assumes "visit_admissible H D b a z" "i < length (hierarchy_children H b)"
  defines "target \<equiv> visit_target D b a z"
  shows "cycle_visits H B b (if a = base_lookup D b then 0 else i)
      (if a = base_lookup D b then i else 0) (even i = (a = base_lookup D b)) a z =
    (if a = base_lookup D b then cycle_visits H B b 0 i (even i) (base_lookup D b) target
     else map (\<lambda>(c, x, y). (c, y, x))
       (rev (cycle_visits H B b 0 i (even i) (base_lookup D b) target)))"
using assms(1,2) gt_zero[of i "length (hierarchy_children H b)"]
    cycle_visits_reverse[where H = H and b = b and j = i and i = 0 and B = B
      and forward = "even i" and z = a and a = "base_lookup D b"]
  by(auto simp: target_def visit_target_def visit_admissible_def)

lemma initial_recovery_visits_observations:
  assumes "task_abstract T = []"
  shows "length (pending_visits H B D (Recovery.initial_recovery p es T J out)) = length p"
    "i < length p \<Longrightarrow>
      pending_visits H B D (Recovery.initial_recovery p es T J out) ! i =
      (p ! i, if i = 0 then base_lookup D (p ! i) else snd (es ! (i - 1)),
        if i < length es then fst (es ! i) else base_lookup D (p ! i))"
    "p \<noteq> [] \<Longrightarrow>
      fst (snd (hd (pending_visits H B D (Recovery.initial_recovery p es T J out)))) = base_lookup D (hd p)"
    "\<lbrakk>p \<noteq> []; length es = length p - 1\<rbrakk> \<Longrightarrow>
      snd (snd (last (pending_visits H B D (Recovery.initial_recovery p es T J out)))) = base_lookup D (last p)"
  by(auto simp: assms pending_visits_def quotient_visits_def Recovery.initial_recovery_def Let_def
    hd_map last_map hd_conv_nth last_conv_nth)

context fixes H :: 'hierarchy and B :: 'edges and D :: 'bases and N :: 'links begin

lemma invar_recovery_alignment_next:
  "invar_recovery_alignment state \<Longrightarrow>
    invar_recovery_alignment (Recovery.next_component D state)"
  by(cases "qbr_path state"; cases "qbr_crossings state";
    auto simp: invar_recovery_alignment_def Recovery.next_component_def Let_def)

lemma invar_recovery_alignment_unchanged[simp]:
  "invar_recovery_alignment (state\<lparr>qbr_tasks := T\<rparr>) = invar_recovery_alignment state"
  "invar_recovery_alignment (Recovery.visit_step D N b a z state) = invar_recovery_alignment state"
  "invar_recovery_alignment (Recovery.cycle_step H B b i j forward a z state) = invar_recovery_alignment state"
  by(auto simp: invar_recovery_alignment_def Recovery.visit_step_def Recovery.cycle_step_def
    Recovery.emit_vertex_def Let_def case_prod_beta)

lemma invar_recovery_alignment_holds_1[invar_holds_intros]:
  "\<lbrakk>Recovery.Blossom_Path_Recovery_call_1_conds state; invar_recovery_alignment state\<rbrakk> \<Longrightarrow>
    invar_recovery_alignment (Recovery.Blossom_Path_Recovery_upd1 H B D N state)"
  by(auto simp: Recovery.Blossom_Path_Recovery_call_1_conds_def Recovery.recovery_done_def
    Recovery.Blossom_Path_Recovery_upd1_def Recovery.recovery_step_def Let_def
    split: Quadratic_Blossom_Search_Recovery_task.splits intro: invar_recovery_alignment_next)

lemma task_visits_length:
  "length tasks \<le> length (concat (map (task_visits H B) tasks))"
  using sum_list_mono[where xs=tasks and f="\<lambda>_. 1::nat"
    and g="\<lambda>task. length (task_visits H B task)"]
  by(auto simp: length_concat comp_def sum_list_triv Suc_le_eq)

lemma next_component_quotient_visits:
  "\<lbrakk>qbr_path state \<noteq> []; length (qbr_crossings state) = length (qbr_path state) - 1; qbr_crossings
    state \<noteq> [] \<Longrightarrow> snd (hd (qbr_crossings state)) \<noteq> nil\<rbrakk> \<Longrightarrow>
    quotient_visits D state = (hd (qbr_path state), if qbr_entry state = nil then original_base D (hd (qbr_path
    state)) else qbr_entry state, if qbr_crossings state = [] then original_base D (hd (qbr_path state)) else fst
    (hd (qbr_crossings state))) # quotient_visits D (Recovery.next_component D state)"
  by(cases "qbr_path state"; cases "qbr_crossings state")
    (auto simp: quotient_visits_def Recovery.next_component_def Let_def map_upt_Suc
      nth_Cons' nth_map_upt Suc_diff_Suc simp del: upt_Suc intro!: nth_equalityI)

lemma next_component_pending_visits:
  "\<lbrakk>task_invar (qbr_tasks state); task_abstract (qbr_tasks state) = []; 0 < task_cap;
    qbr_path state \<noteq> []; length (qbr_crossings state) = length (qbr_path state) - 1;
    qbr_crossings state \<noteq> [] \<Longrightarrow> snd (hd (qbr_crossings state)) \<noteq> nil\<rbrakk> \<Longrightarrow>
    pending_visits H B D (Recovery.next_component D state) = pending_visits H B D state"
  using next_component_quotient_visits[of state]
  by(auto simp: pending_visits_def Recovery.next_component_def Let_def list.case_eq_if task_visits_def
    recovery_stack_simps)

lemma pending_visits_pop:
  "\<lbrakk>task_invar (qbr_tasks state); \<not> task_is_empty (qbr_tasks state)\<rbrakk> \<Longrightarrow>
    pending_visits H B D state = task_visits H B (task_top (qbr_tasks state)) @
      pending_visits H B D (state\<lparr>qbr_tasks := task_pop (qbr_tasks state)\<rparr>)"
  by(cases "task_abstract (qbr_tasks state)") (auto simp: pending_visits_def quotient_visits_def Let_def
    recovery_stack_simps)

lemma cycle_step_pending_visits:
  "\<lbrakk>task_invar (qbr_tasks state); length (task_abstract (qbr_tasks state)) + 2 \<le> task_cap;
    i < length (hierarchy_children H b); j < length (hierarchy_children H b)\<rbrakk> \<Longrightarrow>
    pending_visits H B D (Recovery.cycle_step H B b i j forward a z state) =
      cycle_visits H B b i j forward a z @ pending_visits H B D state"
  using cycle_visits_step[where i=i and b=b and j=j and forward=forward and a=a and z=z]
  by(auto simp: pending_visits_def quotient_visits_def Recovery.cycle_step_def Let_def case_prod_beta
    task_visits_def recovery_stack_simps cycle_edge_def)

lemma recovery_tasks_bound:
  assumes "recovery_tree H"
    "list_all (\<lambda>(b,a,z). visit_admissible H D b a z) (pending_visits H B D state)"
    "distinct (map fst (pending_visits H B D state))"
  shows "length (task_abstract (qbr_tasks state)) \<le> card (hierarchy_ids H)"
proof-
  have "card (set (map fst (pending_visits H B D state))) \<le> card (hierarchy_ids H)"
    using assms(1,2)
    by(intro card_mono) (auto simp: recovery_tree_def list_all_iff visit_admissible_def)
  thus ?thesis
    using assms(3)[THEN distinct_card] task_visits_length[of "task_abstract (qbr_tasks state)"]
    by(simp only: pending_visits_def length_map length_append; arith)
qed

lemma recovered_path_unchanged[simp]:
  "Recovery.recovered_path (state\<lparr>qbr_tasks := T\<rparr>) = Recovery.recovered_path state"
  "Recovery.recovered_path (Recovery.next_component D state) = Recovery.recovered_path state"
  "Recovery.recovered_path (Recovery.cycle_step H B b i j forward a z state) = Recovery.recovered_path state"
  by(auto simp: Recovery.recovered_path_def Recovery.next_component_def Recovery.cycle_step_def
    Let_def case_prod_beta split: list.splits)

lemma recovering_invariants_cong:
  assumes "pending_visits H B D s = pending_visits H B D t"
    "Recovery.recovered_path s = Recovery.recovered_path t"
  shows "invar_recovery_disjoint H B D s = invar_recovery_disjoint H B D t"
    "invar_recovery_completion H B D s = invar_recovery_completion H B D t"
  using assms
  by(simp_all add: invar_recovery_disjoint_def pending_members_def invar_recovery_completion_def)

lemma Blossom_Path_Recovery_correct_ret_1:
  "\<lbrakk>invar_recovery H B D N state; Recovery.Blossom_Path_Recovery_ret_1_conds state\<rbrakk> \<Longrightarrow>
    graph_augmenting_path input_graph (mate_abstract M0) (Recovery.recovered_path state)"
  by(auto simp: Recovery.Blossom_Path_Recovery_ret_1_conds_def Recovery.Blossom_Path_Recovery_call_1_conds_def
    Recovery.recovery_done_def invar_recovery_completion_def pending_visits_def quotient_visits_def Let_def
    recovery_stack_simps elim!: invar_recovery_props Recovery.invar_recovery_adts_props)

lemma recovery_cycle_pending:
  "\<lbrakk>task_invar (qbr_tasks state); task_abstract (qbr_tasks state) \<noteq> []; task_top (qbr_tasks state) =
    Quadratic_Cycle b i j forward a z; length (task_abstract (qbr_tasks state)) < task_cap; i < length
    (hierarchy_children H b); j < length (hierarchy_children H b)\<rbrakk> \<Longrightarrow> pending_visits H B D
    (Recovery.cycle_step H B b i j forward a z (state\<lparr>qbr_tasks := task_pop (qbr_tasks state)\<rparr>)) =
    pending_visits H B D state"
  using pending_visits_pop[of state]
  by(subst cycle_step_pending_visits) (cases "task_abstract (qbr_tasks state)"; auto simp: recovery_stack_simps
    task_visits_def)+

lemma recovering_disjoint_replace:
  assumes "invar_recovery_disjoint H B D state"
    "pending_visits H B D state = (b,a,z) # rest"
    "pending_visits H B D next = visits @ rest"
    "Recovery.recovered_path next = Recovery.recovered_path state"
    "distinct (map fst visits)"
    "pairwise (\<lambda>c d. hierarchy_members H c \<inter> hierarchy_members H d = {}) (set (map fst visits))"
    "\<And>c. c \<in> set (map fst visits) \<Longrightarrow>
      hierarchy_members H c \<subseteq> hierarchy_members H b \<and> hierarchy_members H c \<noteq> {}"
  shows "invar_recovery_disjoint H B D next"
proof-
  have old: "b \<notin> set (map fst rest)"
    "pairwise (\<lambda>c d. hierarchy_members H c \<inter> hierarchy_members H d = {}) (insert b (set (map fst rest)))"
    using assms(1,2)
    by(auto simp: invar_recovery_disjoint_def)
  have cross: "hierarchy_members H c \<inter> hierarchy_members H d = {}"
    if "c \<in> set (map fst visits)" "d \<in> set (map fst rest)" for c d
    using assms(7)[OF that(1)] old that(2)
    by(auto simp: pairwise_def; blast)
  have "set (map fst visits) \<inter> set (map fst rest) = {}"
    using cross assms(7)
    by blast
  moreover have "pairwise (\<lambda>c d. hierarchy_members H c \<inter> hierarchy_members H d = {})
      (set (map fst (pending_visits H B D next)))"
    using assms(6) old(2) cross
    by(auto simp only: assms(3) map_append set_append pairwise_def; blast)
  moreover have "pending_members H B D next \<subseteq> pending_members H B D state"
    using assms(2,3,7)
    by(auto simp: pending_members_def; blast)
  ultimately show ?thesis
    using assms(1-5)
    by(auto simp: invar_recovery_disjoint_def; blast)
qed

lemma recovering_disjoint_emit:
  "\<lbrakk>invar_recovery_disjoint H B D state; pending_visits H B D state = (b,a,a) # rest;
    pending_visits H B D next = rest;
    Recovery.recovered_path next = Recovery.recovered_path state @ [a];
    a \<in> hierarchy_members H b; a \<in> V0\<rbrakk> \<Longrightarrow>
    invar_recovery_disjoint H B D next"
  by(auto simp: invar_recovery_disjoint_def pending_members_def pairwise_def; blast)


lemma recovering_visit_children:
  assumes "recovery_tree H" "b \<in> hierarchy_ids H"
    "set (map fst visits) \<subseteq> set (hierarchy_children H b)"
  shows "pairwise (\<lambda>c d. hierarchy_members H c \<inter> hierarchy_members H d = {})
      (set (map fst visits))"
    "\<forall>c \<in> set (map fst visits). hierarchy_members H c \<subseteq> hierarchy_members H b \<and>
      hierarchy_members H c \<noteq> {}"
  using assms recovery_tree_node[of H b]
  by(auto simp: hierarchy_relation_def intro: pairwise_mono
    dest: hierarchy_edge_members hierarchy_members_finite_nonempty[THEN conjunct2] split: if_splits)

lemma recovery_visit_index:
  assumes "invar_recovering_structure H B D N" "invar_recovery_routing H B D state"
    "visit_admissible H D b a z" "a \<noteq> z" "hierarchy_ids H \<subseteq> K" "nil \<notin> V0"
  defines "J \<equiv> Recovery.cache_route N (visit_target D b a z) b (qbr_hints state)"
  shows "snd (link_lookup J b) < length (hierarchy_children H b)"
    "visit_target D b a z \<in> hierarchy_members H (hierarchy_children H b ! snd (link_lookup J b))"
  using assms(1-6) recovering_visit_props[of H D b a z]
  unfolding J_def
  by(intro cache_route_index[where D = D];
    auto simp: invar_recovery_routing_def prod_eq_iff elim!: invar_recovering_structure_props)+

lemma pending_visits_emit[simp]:
  "pending_visits H B D (Recovery.emit_vertex v state) = pending_visits H B D state"
  by(simp add: pending_visits_def quotient_visits_def Recovery.emit_vertex_def Let_def)

lemma visit_step_pending_visits:
  "\<lbrakk>task_invar (qbr_tasks state); length (task_abstract (qbr_tasks state)) < task_cap; a \<noteq> z\<rbrakk> \<Longrightarrow>
    pending_visits H B D (Recovery.visit_step D N b a z state) =
      (let from_base = a = original_base D b;
           J = Recovery.cache_route N (visit_target D b a z) b (qbr_hints state);
           i = snd (link_lookup J b)
       in cycle_visits H B b (if from_base then 0 else i) (if from_base then i else 0)
         (even i = from_base) a z) @ pending_visits H B D state"
  by(auto simp: pending_visits_def quotient_visits_def Recovery.visit_step_def Let_def task_visits_def
    recovery_stack_simps visit_target_def)

lemma recovery_next_task:
  "\<lbrakk>task_invar (qbr_tasks state); task_is_empty (qbr_tasks state); 0 < task_cap\<rbrakk> \<Longrightarrow>
    \<exists>b a z. task_abstract (qbr_tasks (Recovery.next_component D state)) = [Quadratic_Visit b a z]"
  by(auto simp: Recovery.next_component_def Let_def recovery_stack_simps split: list.splits)

lemma recovering_invariants_unchanged:
  assumes "invar_recovery H B D N state"
    "pending_visits H B D next = pending_visits H B D state"
    "Recovery.recovered_path next = Recovery.recovered_path state"
    "qbr_hints next = qbr_hints state"
    "list_all (task_admissible H B D) (task_abstract (qbr_tasks next))"
  shows "invar_recovery_tasks H B D next" "invar_recovery_disjoint H B D next"
    "invar_recovery_completion H B D next" "invar_recovery_routing H B D next"
  using assms recovering_invariants_cong[of "next" state] recovery_tasks_bound[of "next"]
  by(auto simp: invar_recovery_def invar_recovery_tasks_def invar_recovery_disjoint_def
    invar_recovery_routing_def elim!: invar_recovering_structure_props)

lemma cycle_step_tasks_admissible:
  "\<lbrakk>task_invar (qbr_tasks state); length (task_abstract (qbr_tasks state)) + 2 \<le> task_cap; list_all
    (task_admissible H B D) (task_abstract (qbr_tasks state)); task_admissible H B D (Quadratic_Cycle b i j forward
    a z)\<rbrakk> \<Longrightarrow> list_all (task_admissible H B D) (task_abstract (qbr_tasks (Recovery.cycle_step
    H B b i j forward a z state)))"
  using cycle_visits_step[where H=H and B=B and b=b and i=i and j=j and forward=forward and a=a and z=z]
  by(auto simp: task_admissible_def Recovery.cycle_step_def Let_def case_prod_beta recovery_stack_simps
    cycle_edge_def split: if_splits)

lemma recovering_completion_emit:
  "\<lbrakk>invar_recovery_completion H B D before; visit_admissible H D b a a;
    pending_visits H B D before = (b,a,a) # rest;
    pending_visits H B D after = rest;
    Recovery.recovered_path after = Recovery.recovered_path before @ [a]\<rbrakk> \<Longrightarrow>
    invar_recovery_completion H B D after"
  unfolding invar_recovery_completion_def
  by(fastforce dest: visit_route_singleton)

lemma recovery_cycle_invariants:
  assumes "invar_recovery H B D N state" "\<not> task_is_empty (qbr_tasks state)"
    "task_top (qbr_tasks state) = Quadratic_Cycle b i j forward a z"
    "length (task_abstract (qbr_tasks state)) < task_cap"
  defines "next \<equiv> Recovery.cycle_step H B b i j forward a z
    (state\<lparr>qbr_tasks := task_pop (qbr_tasks state)\<rparr>)"
  shows "invar_recovery_tasks H B D next" "invar_recovery_disjoint H B D next"
    "invar_recovery_completion H B D next" "invar_recovery_routing H B D next"
proof-
  note stack = recovery_stack_properties[OF assms(1,2)]
  have "pending_visits H B D next = pending_visits H B D state"
    using stack(1-3) assms(3,4)
    by(auto simp: next_def task_admissible_def intro!: recovery_cycle_pending)
  moreover have "list_all (task_admissible H B D) (task_abstract (qbr_tasks next))"
    using stack assms(3,4)
    by(auto simp: next_def recovery_stack_simps neq_Nil_conv intro!: cycle_step_tasks_admissible
      elim!: Recovery.invar_recovery_adts_props)
  ultimately show "invar_recovery_tasks H B D next" "invar_recovery_disjoint H B D next"
    "invar_recovery_completion H B D next" "invar_recovery_routing H B D next"
    using assms(1) recovering_invariants_unchanged[of state "next"]
    by(auto simp: next_def Recovery.cycle_step_def Let_def case_prod_beta)
qed

lemma recovery_emit_invariants:
  assumes "invar_recovery H B D N state" "\<not> task_is_empty (qbr_tasks state)"
    "task_top (qbr_tasks state) = Quadratic_Visit b a a" "qbr_length state < output_cap"
  defines "next \<equiv> Recovery.emit_vertex a (state\<lparr>qbr_tasks := task_pop (qbr_tasks state)\<rparr>)"
  shows "invar_recovery_tasks H B D next" "invar_recovery_disjoint H B D next"
    "invar_recovery_completion H B D next" "invar_recovery_routing H B D next"
proof-
  note stack = recovery_stack_properties[OF assms(1,2)]
  have pending: "pending_visits H B D state = (b,a,a) # pending_visits H B D next"
    using stack(7) assms(3)
    by(simp add: next_def task_visits_def)
  show "invar_recovery_tasks H B D next"
    using stack(5,6) assms(1) pending
    by(auto simp: next_def Recovery.emit_vertex_def invar_recovery_def invar_recovery_tasks_def)
  have "a \<in> hierarchy_members H b \<and> a \<in> V0"
    using stack(3) assms(1,3) recovery_member_vertex[of H b a]
    by(auto simp: task_admissible_def visit_admissible_def invar_recovery_def invar_recovering_structure_def)
  moreover have "Recovery.recovered_path next = Recovery.recovered_path state @ [a]"
    using assms(1,4)
    by(auto simp: next_def Recovery.emit_vertex_path invar_recovery_def Recovery.invar_recovery_adts_def)
  ultimately show "invar_recovery_disjoint H B D next" "invar_recovery_completion H B D next"
    using assms(1,3) pending stack(3)
    by(auto simp: task_admissible_def elim!: invar_recovery_props
      intro: recovering_disjoint_emit[where state=state and b=b and rest="pending_visits H B D next"]
        recovering_completion_emit[where before=state and b=b and rest="pending_visits H B D next"])
  show "invar_recovery_routing H B D next"
    by(rule invar_recovery_routing_mono[where before=state])
      (insert assms(1) pending, auto simp: next_def Recovery.emit_vertex_def elim!: invar_recovery_props)
qed

lemma invar_recovery_next:
  assumes "invar_recovery H B D N state" "Recovery.Blossom_Path_Recovery_call_1_conds state"
    "task_is_empty (qbr_tasks state)" "0 < task_cap"
  shows "invar_recovery H B D N (Recovery.next_component D state)"
proof-
  let ?next = "Recovery.next_component D state"
  have props: "task_invar (qbr_tasks state)" "task_abstract (qbr_tasks state) = []" "qbr_path state \<noteq> []"
    using assms(1-3)
    by(auto elim!: invar_recovery_props Recovery.invar_recovery_adts_props
      simp: recovery_stack_simps Recovery.Blossom_Path_Recovery_call_1_conds_def Recovery.recovery_done_def)
  have pending: "pending_visits H B D ?next = pending_visits H B D state"
    using props assms(1,4)
    by(auto simp: invar_recovery_def invar_recovery_alignment_def
      intro!: next_component_pending_visits intro: hd_in_set)
  have "list_all (\<lambda>(b,a,z). visit_admissible H D b a z) (pending_visits H B D ?next)"
    using assms(1) pending
    by(auto simp: invar_recovery_def invar_recovery_tasks_def)
  hence "list_all (task_admissible H B D) (task_abstract (qbr_tasks ?next))"
    using recovery_next_task[of state] props assms(3,4)
    by(auto simp: pending_visits_def task_visits_def task_admissible_def)
  thus ?thesis
    using assms(1,4) pending props recovering_invariants_unchanged[of state "?next"]
    by(auto simp: invar_recovery_def
      intro: Recovery.next_component_adts invar_recovery_alignment_next
      Recovery.invar_recovery_adts_intro elim!: Recovery.invar_recovery_adts_props)
      (auto simp: Recovery.next_component_def Recovery.recovered_path_def Let_def)
qed

end

end

context Quadratic_Blossom_Search_thms
begin

lemma recovering_path_active:
  "\<lbrakk>invar_representatives state; invar_recovering_path state p es\<rbrakk> \<Longrightarrow> set p
    \<subseteq> active_ids state"
  using quotient_active_vertices[of state]
  by(auto simp: invar_recovering_path_def dest: subset_path_Vs)

lemma recovering_matching_boundary:
  "\<lbrakk>invar_recovering_structure H B D N; b \<in> hierarchy_ids H; {u, v} \<in> mate_abstract M0; u \<in>
    hierarchy_members H b; v \<notin> hierarchy_members H b\<rbrakk> \<Longrightarrow> u = base_lookup D b"
  using input_matching_props(1)
  by(intro matching_component_boundary[where S = "hierarchy_members H b"])
    (auto simp: invar_recovering_structure_def graph_inter_Vs_def)

lemma recovering_crossing:
  assumes "invar_recovering_path state p es" "i < length es"
  shows "{fst (es ! i), snd (es ! i)} \<in> input_graph"
    "representative state (fst (es ! i)) = p ! i"
    "representative state (snd (es ! i)) = p ! Suc i"
    "({fst (es ! i), snd (es ! i)} \<in> mate_abstract M0) \<longleftrightarrow>
      {p ! i, p ! Suc i} \<in> mate_abstract (qbs_matching state)"
  using assms
  by(auto simp: invar_recovering_path_def Let_def split_def)

lemma recovering_crossing_members:
  assumes "invar_representatives state" "invar_recovering_path state p es" "i < length es"
  shows "fst (es ! i) \<in> hierarchy_members (qbs_hierarchy state) (p ! i)"
    "snd (es ! i) \<in> hierarchy_members (qbs_hierarchy state) (p ! Suc i)"
  using assms(1) recovering_crossing[OF assms(2,3)]
    edge_witness_members[of state "es ! i" "p ! i" "p ! Suc i"]
  by(auto simp del: input_edge_iff)

lemma recovering_crossing_matched:
  "\<lbrakk>invar_recovering_path state p es; i < length es\<rbrakk> \<Longrightarrow> ({fst (es ! i), snd (es !
    i)} \<in> mate_abstract M0) \<longleftrightarrow> odd i"
  using witnessed_alternating_edge[of state es p i]
  by(auto simp: invar_recovering_path_witnesses matching_augmenting_path_def)

lemma recovering_path_length:
  "invar_recovering_path state p es \<Longrightarrow> length es = length p - 1"
  by(auto simp: invar_recovering_path_def)

lemma recovering_crossing_not_nil:
  assumes "invar_recovering_path state p es" "i < length es"
  shows "fst (es ! i) \<noteq> nil" "snd (es ! i) \<noteq> nil"
  using input_edge_vertices[OF recovering_crossing(1)[OF assms]] input_props(3,4)
  by blast+

lemma recovering_crossing_bases:
  "\<lbrakk>invar_recovering_structure H B D N; c \<in> hierarchy_ids H; d \<in> hierarchy_ids H;
    hierarchy_members H c \<inter> hierarchy_members H d = {};
    fst e \<in> hierarchy_members H c; snd e \<in> hierarchy_members H d;
    {fst e, snd e} \<in> mate_abstract M0\<rbrakk> \<Longrightarrow>
    fst e = base_lookup D c \<and> snd e = base_lookup D d"
  by(auto simp: insert_commute intro: recovering_matching_boundary)

lemma recovering_matched_crossing_bases:
  assumes "invar_recovering_structure (qbs_hierarchy state) B D N"
    "invar_representatives state" "invar_recovering_path state p es"
    "i < length es" "odd i"
  shows "fst (es ! i) = base_lookup D (p ! i)"
    "snd (es ! i) = base_lookup D (p ! Suc i)"
proof-
  have "p ! i \<in> active_ids state" "p ! Suc i \<in> active_ids state" "p ! i \<noteq> p ! Suc i"
    "hierarchy_invar (qbs_hierarchy state)"
    using assms recovering_path_active[of state p es]
    by(auto simp: invar_recovering_path_def invar_recovering_structure_def nth_eq_iff_index_eq)
  hence "fst (es ! i) = base_lookup D (p ! i) \<and> snd (es ! i) = base_lookup D (p ! Suc i)"
    using assms active_ids_subset[of state] recovering_crossing[of state p es i]
      recovering_crossing_members[of state p es i] recovering_crossing_matched[of state p es i]
    by(intro recovering_crossing_bases[where B=B and N=N]) (auto simp: invar_representatives_def)
  thus "fst (es ! i) = base_lookup D (p ! i)" "snd (es ! i) = base_lookup D (p ! Suc i)"
    by auto
qed


lemma recovering_chain_visit:
  assumes "k \<le> m" "C k \<in> hierarchy_ids H" "base_lookup D (C k) \<in> hierarchy_members H (C k)"
    "k = 0 \<Longrightarrow> a = base_lookup D (C k)" "k = m \<Longrightarrow> z \<in> hierarchy_members H (C k)"
    "\<lbrakk>k = m; odd k\<rbrakk> \<Longrightarrow> z = base_lookup D (C k)"
    "\<And>j. j < m \<Longrightarrow> fst (E j) \<in> hierarchy_members H (C j) \<and>
      snd (E j) \<in> hierarchy_members H (C (Suc j))"
    "\<And>j. \<lbrakk>j < m; odd j\<rbrakk> \<Longrightarrow> fst (E j) = base_lookup D (C j) \<and>
      snd (E j) = base_lookup D (C (Suc j))"
  shows "let x = if k = 0 then a else snd (E (k - 1)); y = if k < m then fst (E k) else z
    in visit_admissible H D (C k) x y \<and>
      (if even k then x = base_lookup D (C k) else y = base_lookup D (C k))"
  using assms(1-6) assms(7,8)[of k] assms(7,8)[of "k - 1"]
  by(cases k; cases "k < m"; cases "odd k"; auto simp: Let_def visit_admissible_def)

lemma recovering_quotient_visit:
  assumes "invar_recovering_structure (qbs_hierarchy state) B D N"
    "invar_representatives state" "invar_recovering_path state p es" "i < length p"
  shows "let a = if i = 0 then base_lookup D (p ! i) else snd (es ! (i - 1));
      z = if i < length es then fst (es ! i) else base_lookup D (p ! i)
    in visit_admissible (qbs_hierarchy state) D (p ! i) a z \<and>
      (if even i then a = base_lookup D (p ! i) else z = base_lookup D (p ! i))"
  using assms recovering_path_active[OF assms(2,3)] active_ids_subset[of state]
    recovering_crossing_members[OF assms(2,3)] recovering_matched_crossing_bases[OF assms(1-3)]
  by(intro recovering_chain_visit)
    (auto simp: invar_recovering_structure_def invar_navigation_def invar_recovering_path_def subset_iff)

lemmas recovering_quotient_visit_admissible = recovering_quotient_visit[unfolded Let_def, THEN conjunct1]


lemma initial_recovery_visits:
  assumes "invar_recovering_structure (qbs_hierarchy state) B D N"
    "invar_representatives state" "invar_recovering_path state p es" "task_abstract T = []"
  shows "list_all (\<lambda>(b, a, z). visit_admissible (qbs_hierarchy state) D b a z)
    (pending_visits (qbs_hierarchy state) B D (Recovery.initial_recovery p es T J out))"
  using assms(4)
  by(auto simp: pending_visits_def quotient_visits_def Recovery.initial_recovery_def
    list_all_iff Let_def cong: if_cong split del: if_split
    dest!: recovering_quotient_visit_admissible[OF assms(1-3)])

lemma initial_recovery_alignment:
  "invar_recovering_path state p es \<Longrightarrow>
    invar_recovery_alignment (Recovery.initial_recovery p es T J out)"
  using recovering_path_length[of state p es] recovering_crossing_not_nil(2)[of state p es]
  by(fastforce simp: invar_recovery_alignment_def Recovery.initial_recovery_def in_set_conv_nth)

lemma recovering_base_unmatched:
  assumes "invar_recovering_structure (qbs_hierarchy state) B D N"
    "invar_representatives state" "invar_matching_projection state"
    "b \<in> active_ids state" "b \<notin> Vs (mate_abstract (qbs_matching state))"
  shows "base_lookup D b \<notin> Vs (mate_abstract M0)"
proof-
  let ?S = "hierarchy_members (qbs_hierarchy state) b"
  have "b \<in> hierarchy_ids (qbs_hierarchy state)"
    using assms(1,4) active_ids_subset[of state]
    by(auto simp: invar_recovering_structure_def)
  hence component: "?S = {u \<in> V0. representative state u = b}"
    "base_lookup D b \<in> ?S"
    "Vs {e \<in> mate_abstract M0. e \<subseteq> ?S} = ?S - {base_lookup D b}"
    using assms(1,2,4)
    by(auto simp: invar_representatives_def invar_recovering_structure_def invar_navigation_def)
  show ?thesis
  proof
    assume "base_lookup D b \<in> Vs (mate_abstract M0)"
    then have edge: "{base_lookup D b, mate_partner M0 (base_lookup D b)} \<in> mate_abstract M0"
      by(rule Mate.matching(5)[OF input_props(12)])
    let ?v = "mate_partner M0 (base_lookup D b)"
    have "?v \<notin> ?S"
      using component(2,3) edge
      by(auto simp: Vs_def)
    hence "{b, representative state ?v} \<in> mate_abstract (qbs_matching state)"
      using assms(3) edge component(1,2) input_matching_props(2)
      by(auto simp: invar_matching_projection_def)
        (rule exI[of _ "base_lookup D b"], rule exI[of _ "?v"], auto)
    thus False
      using assms(5)
      by(auto simp: Vs_def)
  qed
qed

lemma recovering_path_endpoints_unmatched:
  assumes "invar_recovering_structure (qbs_hierarchy state) B D N"
    "invar_representatives state" "invar_matching_projection state" "invar_recovering_path state p es"
  shows "base_lookup D (hd p) \<notin> Vs (mate_abstract M0)"
    "base_lookup D (last p) \<notin> Vs (mate_abstract M0)"
  using assms recovering_path_active[OF assms(2,4)]
  by(intro recovering_base_unmatched[OF assms(1-3)]; cases p;
    auto simp: invar_recovering_path_def matching_augmenting_path_def
      dest: hd_in_set last_in_set)+

context
  fixes H B D N b i
  assumes cycle: "invar_recovering_structure H B D N" "b \<in> hierarchy_ids H"
    "i < length (hierarchy_children H b)"
begin

lemma cycle_children_nonempty[simp]: "hierarchy_children H b \<noteq> []"
  using cycle(3)
  by auto

lemmas cycle_children = recovering_children[OF cycle(1,2) cycle_children_nonempty]

lemma cycle_traversal:
  defines "rs \<equiv> cycle_indices H b 0 i (even i)"
  shows "rs \<noteq> []" "distinct rs" "odd (length rs)"
    "set rs \<subseteq> {..<length (hierarchy_children H b)}" "rs ! 0 = 0" "rs ! (length rs - 1) = i"
    "k < length rs \<Longrightarrow> rs ! k < length (hierarchy_children H b)"
    "k < length rs \<Longrightarrow> hierarchy_children H b ! (rs ! k) \<in> hierarchy_ids H"
  using cycle(3) cycle_children(2,4) cycle_indices_props[of H b 0 i "even i"]
    cycle_indices_head[of 0 H b i "even i"] cycle_indices_last[of 0 H b i "even i"]
    cycle_base_indices_odd[of H b i]
  by(auto simp: rs_def hd_conv_nth last_conv_nth subset_iff dest: nth_mem)

lemma cycle_base_matched_bases:
  defines "rs \<equiv> cycle_indices H b 0 i (even i)"
  assumes "k < length rs - 1" "odd k"
  shows "let cs = hierarchy_children H b; c = cs ! (rs ! k); d = cs ! (rs ! Suc k);
      e = cycle_edge B c d (even i)
    in fst e = base_lookup D c \<and> snd e = base_lookup D d"
  using cycle assms cycle_base_crossing[of H B D N b i k]
    cycle_traversal(2) cycle_traversal(7,8)[of k] cycle_traversal(7,8)[of "Suc k"]
  unfolding Let_def
  by(intro recovering_crossing_bases[where H=H and B=B and N=N]
    recovering_children_disjoint[where B=B and N=N and b=b]) (auto simp: rs_def nth_eq_iff_index_eq)


lemma cycle_base_visit:
  assumes "target \<in> hierarchy_members H (hierarchy_children H b ! i)"
  defines "rs \<equiv> cycle_indices H b 0 i (even i)"
  assumes "k < length rs"
  shows "case cycle_visits H B b 0 i (even i) (base_lookup D b) target ! k of (c, a, z) \<Rightarrow>
    visit_admissible H D c a z \<and> (if even k then a = base_lookup D c else z = base_lookup D c)"
proof-
  have last: "(if Suc k = length rs then x else y) = (if k < length rs - 1 then y else x)" for x y :: "'v"
    using assms(3)
    by(auto; arith)
  show ?thesis
    using assms cycle(1) cycle_children(7) cycle_traversal(3,5,6)[folded rs_def]
      cycle_traversal(8)[of k, folded rs_def]
      cycle_base_crossing[OF cycle, folded rs_def] cycle_base_matched_bases[folded rs_def]
    unfolding cycle_visits_def Let_def
    by(simp only: rs_def[symmetric] length_upt diff_zero nth_map assms(3) nth_upt add_0
        prod.case last;
      intro recovering_chain_visit[unfolded Let_def, where m="length rs - 1"
        and C="\<lambda>j. hierarchy_children H b ! (rs ! j)"])
      (auto simp: hd_conv_nth elim!: invar_recovering_structure_props invar_navigation_props)
qed


lemma cycle_base_routes:
  assumes "target \<in> hierarchy_members H (hierarchy_children H b ! i)"
    "list_all2 (\<lambda>(c, a, z) p. visit_route H D c a z p)
      (cycle_visits H B b 0 i (even i) (base_lookup D b) target) ps"
  shows "visit_route H D b (base_lookup D b) target (concat ps)"
proof-
  let ?visits = "cycle_visits H B b 0 i (even i) (base_lookup D b) target"
  let ?rs = "cycle_indices H b 0 i (even i)"
  have length: "length ?visits = length ?rs"
    by(simp add: cycle_visits_def Let_def)
  have components: "distinct (map fst ?visits)"
    "set (map fst ?visits) \<subseteq> set (hierarchy_children H b)"
    using cycle_visits_components_props[of H b B 0 i "even i" "base_lookup D b" target] cycle_children(1)
    by simp_all
  have orientation: "if even k then fst (snd (?visits ! k)) = base_lookup D (fst (?visits ! k))
    else snd (snd (?visits ! k)) = base_lookup D (fst (?visits ! k))"
    if "k < length ?visits" for k
    using assms(1) that cycle_base_visit[of target k]
    by(auto simp: length case_prod_beta)
  have crossing: "{snd (snd (?visits ! k)), fst (snd (?visits ! Suc k))} \<in> input_graph \<and>
    ({snd (snd (?visits ! k)), fst (snd (?visits ! Suc k))} \<in> mate_abstract M0 \<longleftrightarrow> odd k)"
    if "k < length ?visits - 1" for k
    using cycle that cycle_base_crossing[of H B D N b i k]
    by(auto simp: cycle_visits_def Let_def less_diff_conv)
  have "?visits \<noteq> []" "pairwise (\<lambda>c d. hierarchy_members H c \<inter> hierarchy_members H d = {})
    (set (map fst ?visits))"
    using cycle_traversal(1) components(2) cycle_children(6)
    by(auto simp: cycle_visits_def Let_def pairwise_def)
  note joined = visit_routes_concat_properties[OF assms(2) components(1) this(2) orientation crossing] this(1)
  have "visit_admissible H D b (base_lookup D b) target"
    using cycle assms(1) cycle_children(5)
    by(auto simp: visit_admissible_def invar_recovering_structure_def invar_navigation_def dest: nth_mem)
  moreover have "set (concat ps) \<subseteq> hierarchy_members H b"
    using joined components(2) cycle_children(5)
    by blast
  ultimately show ?thesis
    using joined cycle_traversal(3)
    by(simp add: visit_route_def cycle_visits_endpoints length)
qed

lemma cycle_base_visits_admissible:
  "target \<in> hierarchy_members H (hierarchy_children H b ! i) \<Longrightarrow> list_all (\<lambda>(c, a, z).
    visit_admissible H D c a z) (cycle_visits H B b 0 i (even i) (base_lookup D b) target)"
  using cycle_base_visit[of target]
  by(auto simp: list_all_length case_prod_beta cycle_visits_def Let_def)

lemma cycle_base_visit_target:
  assumes "target \<in> hierarchy_members H (hierarchy_children H b ! i)"
    "(c, a, z) \<in> set (cycle_visits H B b 0 i (even i) (base_lookup D b) target)"
    "target \<in> hierarchy_members H c"
  shows "visit_target D c a z = target"
proof-
  let ?rs = "cycle_indices H b 0 i (even i)"
  let ?visits = "cycle_visits H B b 0 i (even i) (base_lookup D b) target"
  obtain k where position: "k < length ?rs" "?visits ! k = (c, a, z)"
    using assms(2)
    by(auto simp: in_set_conv_nth cycle_visits_def Let_def)
  have "c = hierarchy_children H b ! (?rs ! k)"
    using position
    by(simp add: cycle_visits_def Let_def)
  hence "?rs ! k = i"
    using cycle assms(1,3) position(1) cycle_traversal(7)[of k]
    by(blast dest: recovering_children_disjoint)
  hence last: "k = length ?rs - 1"
    using cycle_traversal(1,2,6) position(1)
    by(auto intro: nth_eq_iff_index_eq[THEN iffD1])
  thus ?thesis
    using assms(1) cycle_base_visit[of target k] position cycle_traversal(1,3)
    by(auto simp: visit_target_def cycle_visits_def Let_def case_prod_beta)
qed

declare cycle_children_nonempty[simp del]

end

lemma cycle_visits_properties:
  assumes "invar_recovering_structure H B D N" "visit_admissible H D b a z"
    "i < length (hierarchy_children H b)"
    "visit_target D b a z \<in> hierarchy_members H (hierarchy_children H b ! i)"
  defines "visits \<equiv> cycle_visits H B b (if a = base_lookup D b then 0 else i)
    (if a = base_lookup D b then i else 0) (even i = (a = base_lookup D b)) a z"
  shows "list_all (\<lambda>(c,x,y). visit_admissible H D c x y) visits"
    "\<And>c x y. \<lbrakk>(c,x,y) \<in> set visits; visit_target D b a z \<in> hierarchy_members H c\<rbrakk> \<Longrightarrow>
      visit_target D c x y = visit_target D b a z"
    "\<And>ps. list_all2 (\<lambda>(c,x,y) p. visit_route H D c x y p) visits ps \<Longrightarrow>
      visit_route H D b a z (concat ps)"
proof-
  note selected = cycle_selected_visits[OF assms(2,3)]
  show admissible: "list_all (\<lambda>(c,x,y). visit_admissible H D c x y) visits"
    using cycle_base_visits_admissible[of H B D N b i "visit_target D b a z"] selected assms(1-4)
    by(auto simp: visits_def list_all_iff visit_admissible_def)
  show "visit_target D c x y = visit_target D b a z"
    if "(c,x,y) \<in> set visits" "visit_target D b a z \<in> hierarchy_members H c" for c x y
    using cycle_base_visit_target[of H B D N b i "visit_target D b a z" c x y]
      cycle_base_visit_target[of H B D N b i "visit_target D b a z" c y x]
      visit_target_reverse[of H D c x y] admissible selected assms(1-4) that
    by(auto simp: visits_def list_all_iff visit_admissible_def split: if_splits)
  show "visit_route H D b a z (concat ps)"
    if "list_all2 (\<lambda>(c,x,y) p. visit_route H D c x y p) visits ps" for ps
  proof(cases "a = base_lookup D b")
    case True
    show ?thesis
      using assms(1-4) that True
      by(auto simp: visits_def visit_target_def visit_admissible_def intro!: cycle_base_routes)
  next
    case False
    have "visit_route H D b (base_lookup D b) a (concat (map rev (rev ps)))"
      using assms(1-4) visit_routes_reverse[OF that] selected False
      by(intro cycle_base_routes)
        (auto simp: visits_def visit_admissible_def visit_target_def rev_map case_prod_beta comp_def)
    from visit_route_reverse[OF this] show ?thesis
      using assms(2) False
      by(auto simp: visit_admissible_def rev_concat rev_map comp_def)
  qed
qed

lemmas cycle_visits_admissible = cycle_visits_properties(1)
lemmas cycle_visits_target = cycle_visits_properties(2)
lemmas cycle_visits_routes = cycle_visits_properties(3)

lemma initial_recovery_visits_alternation:
  fixes J out
  assumes "invar_recovering_structure (qbs_hierarchy state) B D N"
    "invar_representatives state" "invar_recovering_path state p es" "task_abstract T = []"
  defines "visits \<equiv> pending_visits (qbs_hierarchy state) B D
    (Recovery.initial_recovery p es T J out)"
  shows "i < length visits \<Longrightarrow> (if even i
      then fst (snd (visits ! i)) = base_lookup D (fst (visits ! i))
      else snd (snd (visits ! i)) = base_lookup D (fst (visits ! i)))"
    "i < length visits - 1 \<Longrightarrow>
      {snd (snd (visits ! i)), fst (snd (visits ! Suc i))} \<in> input_graph \<and>
      ({snd (snd (visits ! i)), fst (snd (visits ! Suc i))} \<in> mate_abstract M0 \<longleftrightarrow> odd i)"
  using recovering_quotient_visit[OF assms(1-3), of i]
    recovering_crossing(1)[OF assms(3), of i] recovering_crossing_matched[OF assms(3), of i]
  by(auto simp: visits_def Let_def initial_recovery_visits_observations[OF assms(4)]
    recovering_path_length[OF assms(3)])


lemma initial_recovery_realization:
  assumes "invar_recovering_structure (qbs_hierarchy state) B D N"
    "invar_representatives state" "invar_matching_projection state" "invar_recovering_path state p es"
    "task_abstract T = []"
    "list_all2 (\<lambda>(b, a, z) q. visit_route (qbs_hierarchy state) D b a z q)
      (pending_visits (qbs_hierarchy state) B D (Recovery.initial_recovery p es T J out)) ps"
  shows "graph_augmenting_path input_graph (mate_abstract M0) (concat ps)"
proof-
  let ?r = "Recovery.initial_recovery p es T J out"
  let ?visits = "pending_visits (qbs_hierarchy state) B D ?r"
  have path: "p \<noteq> []" "distinct p" "even (length p)" "length es = length p - 1"
    using assms(4)
    by(auto simp: invar_recovering_path_def dest: aug_paths_are_even)
  have components: "map fst ?visits = p"
    by(rule initial_recovery_pending[OF assms(5)])
  have geometry: "?visits \<noteq> []" "distinct (map fst ?visits)"
    "pairwise (\<lambda>c d. hierarchy_members (qbs_hierarchy state) c \<inter>
      hierarchy_members (qbs_hierarchy state) d = {}) (set (map fst ?visits))"
    using components path assms(1) recovering_path_active[OF assms(2,4)]
    by(auto simp: invar_recovering_structure_def intro: hierarchy_top_disjoint)
  note observations = initial_recovery_visits_observations[OF assms(5),
    where H = "qbs_hierarchy state" and B = B and D = D and p = p and es = es and J = J and out = out]
  note orientation = initial_recovery_visits_alternation[OF assms(1,2,4,5), where J = J and out = out]
  note concat = visit_routes_concat_properties[OF assms(6) geometry(2,3) orientation(1) orientation(2)] geometry(1)
  have length: "2 \<le> length (concat ps)"
    using concat observations(1) path(3)
    by(cases "concat ps" rule: list_cases3) auto
  show ?thesis
    using concat length path observations(3,4) recovering_path_endpoints_unmatched[OF assms(1-4)]
    by(auto simp: matching_augmenting_path_def intro: path_subset[OF path_edges_of_path_refl])
qed


lemma initial_recovery_full:
  assumes "recovery_precond state T out" "qbs_status state = Quadratic_Path p es"
    "invar_matching_projection state"
  shows "invar_recovery (qbs_hierarchy state) (qbs_cycle_edges state) (qbs_bases state)
    (qbs_parents state) (Recovery.initial_recovery p es T (qbs_hints state) out)"
proof-
  have "list_all2 (\<lambda>(b,a,z) q. visit_route (qbs_hierarchy state) (qbs_bases state) b a z q)
      (pending_visits (qbs_hierarchy state) (qbs_cycle_edges state) (qbs_bases state)
        (Recovery.initial_recovery p es T (qbs_hints state) out)) ps \<Longrightarrow>
    graph_augmenting_path input_graph (mate_abstract M0) (concat ps)" for ps
    using assms
    by(intro initial_recovery_realization[where N = "qbs_parents state"])
      (auto simp: recovery_precond_def recovery_workspaces_def)
  thus ?thesis
    using assms recovering_path_active[of state p es]
    by(auto simp only: invar_recovery_def intro!: initial_recovery_adts[where H = "qbs_hierarchy state"]
      initial_recovery_alignment initial_recovery_tasks initial_recovery_disjoint initial_recovery_routing
      initial_recovery_visits[where N = "qbs_parents state"])
      (auto simp: invar_recovery_completion_def recovery_precond_def recovery_workspaces_def
        invar_recovering_path_def Recovery.recovered_path_def Recovery.initial_recovery_def)
qed

lemma search_recovery_capacity:
  assumes "invar_search state"
  shows "Suc (card (hierarchy_ids (qbs_hierarchy state))) \<le> task_cap"
proof-
  let ?ids = "hierarchy_ids (qbs_hierarchy state)"
  have facts: "finite ?ids" "V0 \<subseteq> ?ids"
    "2 * card (?ids - V0) \<le> length vs"
    using assms
    by(auto simp: recovery_tree_def invar_hierarchy_size_def
      elim!: invar_search_props invar_recovering_structure_props)
  hence "card ?ids = length vs + card (?ids - V0)"
    using card_Diff_subset[of V0 ?ids] card_mono[of ?ids V0]
    by simp
  thus ?thesis
    using facts(3) initial_workspaces(5)
    by presburger
qed

lemma search_recovery_precond:
  "\<lbrakk>invar_search state; qbs_status state = Quadratic_Path p es\<rbrakk> \<Longrightarrow> recovery_precond
    state T0 out0"
  using search_recovery_capacity[of state] initial_workspaces
  by(auto simp: recovery_precond_def recovery_workspaces_def invar_search_def invar_adts_def
    invar_result_def)

lemma recovery_visit_invariants:
  assumes "invar_recovery H B D N state" "task_abstract (qbr_tasks state) \<noteq> []"
    "task_top (qbr_tasks state) = Quadratic_Visit b a z" "a \<noteq> z"
    "hierarchy_ids H \<subseteq> K" "Suc (card (hierarchy_ids H)) \<le> task_cap"
  defines "next \<equiv> Recovery.visit_step D N b a z
    (state\<lparr>qbr_tasks := task_pop (qbr_tasks state)\<rparr>)"
  shows "invar_recovery H B D N next"
proof-
  let ?tail = "state\<lparr>qbr_tasks := task_pop (qbr_tasks state)\<rparr>"
  let ?target = "visit_target D b a z"
  let ?J = "Recovery.cache_route N ?target b (qbr_hints state)"
  let ?i = "snd (link_lookup ?J b)"
  let ?visits = "cycle_visits H B b (if a = base_lookup D b then 0 else ?i)
    (if a = base_lookup D b then ?i else 0) (even ?i = (a = base_lookup D b)) a z"
  have "\<not> task_is_empty (qbr_tasks state)"
    using assms(1,2)
    by(auto simp: recovery_stack_simps elim!: invar_recovery_props Recovery.invar_recovery_adts_props)
  note stack = recovery_stack_properties[OF assms(1) this]
  have props: "invar_recovering_structure H B D N" "invar_recovery_disjoint H B D state"
    "invar_recovery_completion H B D state" "invar_recovery_routing H B D state"
    using assms(1)
    by(auto elim!: invar_recovery_props)
  have admissible: "visit_admissible H D b a z"
    using stack(3) assms(3)
    by(simp add: task_admissible_def)
  have pending: "pending_visits H B D state = (b,a,z) # pending_visits H B D ?tail"
    using stack(7) assms(3)
    by(simp add: task_visits_def)
  have index: "?i < length (hierarchy_children H b)"
    "?target \<in> hierarchy_members H (hierarchy_children H b ! ?i)"
    using props(1,4) admissible assms(4,5) input_props(3,4)
    by(blast intro: recovery_visit_index)+
  have visits: "list_all (\<lambda>(c,x,y). visit_admissible H D c x y) ?visits"
    using props(1) admissible index
    by(rule cycle_visits_admissible)
  have "0 < length (hierarchy_children H b)" "distinct (hierarchy_children H b)"
    using props(1) admissible index(1)
    by(auto simp: visit_admissible_def length_greater_0_conv intro: recovering_children(1))
  hence selection: "distinct (map fst ?visits)"
    "set (map fst ?visits) \<subseteq> set (hierarchy_children H b)"
    using cycle_visits_components_props[where H=H and b=b]
    by blast+
  have tail: "task_invar (qbr_tasks ?tail)"
    "length (task_abstract (qbr_tasks ?tail)) < task_cap"
    "list_all (task_admissible H B D) (task_abstract (qbr_tasks ?tail))"
    using stack(4-6) assms(6)
    by(auto elim!: Recovery.invar_recovery_adts_props)
  have updated: "pending_visits H B D next = ?visits @ pending_visits H B D ?tail"
    "Recovery.recovered_path next = Recovery.recovered_path state" "qbr_hints next = ?J"
    using visit_step_pending_visits[OF tail(1,2) assms(4)] assms(4)
    by(simp_all add: next_def visit_target_def Recovery.visit_step_def Recovery.recovered_path_def Let_def)
  have children: "pairwise (\<lambda>c d. hierarchy_members H c \<inter> hierarchy_members H d = {}) (set (map fst ?visits))"
    "\<forall>c \<in> set (map fst ?visits). hierarchy_members H c \<subseteq> hierarchy_members H b \<and> hierarchy_members H c \<noteq> {}"
    using recovering_visit_children[OF _ _ selection(2)] props(1) admissible
    by(auto simp: invar_recovering_structure_def visit_admissible_def)
  have "invar_recovery_disjoint H B D next"
    using props(2) pending updated(1,2) selection(1) children(1)
    by(rule recovering_disjoint_replace) (insert children(2), auto)
  moreover have "invar_recovery_completion H B D next"
    using props(3) pending updated(1,2)
    by(rule recovering_completion_replace_visit)
      (blast intro: cycle_visits_routes[OF props(1) admissible index])
  moreover have "invar_recovery_routing H B D next"
  proof(rule recovering_routing_replace[OF _ _ assms(5) _ props(4,2) pending admissible assms(4) updated(1,3)])
    show "recovery_tree H" "invar_navigation H D N"
      using props(1)
      by(auto simp: invar_recovering_structure_def)
    show "nil \<notin> V0"
      using input_props(3,4)
      by blast
    show "(d,b) \<in> rtrancl (hierarchy_relation H)" if "(d,x,y) \<in> set ?visits" for d x y
      using selection(2) admissible that
      by(force simp: visit_admissible_def hierarchy_relation_def)
    show "visit_target D d x y = ?target"
      if "(d,x,y) \<in> set ?visits" "x \<noteq> y" "?target \<in> hierarchy_members H d" for d x y
      using props(1) admissible index that
      by(blast intro: cycle_visits_target)
  qed
  moreover have "list_all (task_admissible H B D) (task_abstract (qbr_tasks next))"
    using tail visits admissible[unfolded visit_admissible_def] index(1) assms(4)
    by(auto simp: next_def Recovery.visit_step_def Let_def recovery_stack_simps task_admissible_def
      visit_target_def)
  ultimately show ?thesis
    using props(1) assms(1,4) stack(4) tail(2) visits pending updated(1)
    by(auto intro!: invar_recovery_intro invar_recovery_tasks_intro
      intro: recovery_tasks_bound[where B = B and D = D] Recovery.visit_step_adts
      simp: next_def invar_recovering_structure_def invar_recovery_disjoint_def image_Un
      elim!: invar_recovery_props invar_recovery_tasks_props)
qed

lemma invar_recovery_holds_1[invar_holds_intros]:
  assumes "invar_recovery H B D N state"
    "Recovery.Blossom_Path_Recovery_call_1_conds state"
    "hierarchy_ids H \<subseteq> K" "card V0 \<le> output_cap"
    "Suc (card (hierarchy_ids H)) \<le> task_cap"
  shows "invar_recovery H B D N (Recovery.Blossom_Path_Recovery_upd1 H B D N state)"
proof(cases "task_is_empty (qbr_tasks state)")
  case True
  thus ?thesis
    using assms
    by(auto simp: Recovery.Blossom_Path_Recovery_upd1_def Recovery.recovery_step_def
      intro!: invar_recovery_next)
next
  case False
  note stack = recovery_stack_properties[OF assms(1) False]
  have space: "length (task_abstract (qbr_tasks state)) < task_cap" "qbr_length state < output_cap"
    using assms(1,4,5) False
    by(auto intro: recovery_stack_space recovery_stack_output_space elim: invar_recovery_props)
  show ?thesis
    using False space assms assms(1)[unfolded invar_recovery_def] stack(2) recovery_visit_invariants[OF assms(1) stack(2)]
      invar_recovery_adts_holds_1[of H B D N state] invar_recovery_alignment_holds_1[OF assms(2)]
    by(cases "task_top (qbr_tasks state)"; auto simp: Recovery.Blossom_Path_Recovery_upd1_def
      Recovery.recovery_step_def Recovery.visit_step_def Let_def
      intro: invar_recovery_intro recovery_cycle_invariants recovery_emit_invariants
      elim: invar_recovery_props)
qed

subsection "Termination and correctness of recovery"

context
  fixes H :: 'g and B :: 'k and D :: 'm and N :: 'n
  assumes recovery_inputs: "hierarchy_ids H \<subseteq> K" "card V0 \<le> output_cap"
    "Suc (card (hierarchy_ids H)) \<le> task_cap"
begin

lemma Blossom_Path_Recovery_terminates:
  assumes "invar_recovery H B D N state"
  shows "Recovery.Blossom_Path_Recovery_dom H B D N state"
  using wf_measure[of "recovery_measure H B", folded Blossom_Path_Recovery_term_rel'_def] assms
proof(induction state rule: wf_induct_rule)
  case IH: (less state)
  show ?case
    by(rule Recovery.Blossom_Path_Recovery_domintros)
      (insert IH.prems recovery_inputs, auto intro!: IH.IH intro: invar_recovery_holds_1[OF IH.prems _ recovery_inputs]
        recovery_call_1_terminates[OF IH.prems recovery_inputs(3)])
qed

lemma invar_recovery_holds[invar_holds_intros]:
  assumes "Recovery.Blossom_Path_Recovery_dom H B D N state"
  shows "invar_recovery H B D N state \<Longrightarrow>
    invar_recovery H B D N (Recovery.Blossom_Path_Recovery H B D N state)"
  using assms
proof(induction rule: Recovery.Blossom_Path_Recovery_induct[consumes 1])
  case IH: (1 state)
  show ?case
    by(rule Recovery.Blossom_Path_Recovery_cases[where state=state])
      (insert IH recovery_inputs invar_recovery_holds_1[of H B D N state],
        auto simp: Recovery.Blossom_Path_Recovery_simps Recovery.Blossom_Path_Recovery_ret1_def)
qed

lemma Blossom_Path_Recovery_correct:
  "invar_recovery H B D N state \<Longrightarrow> graph_augmenting_path input_graph (mate_abstract M0)
    (Recovery.recovered_path (Recovery.Blossom_Path_Recovery H B D N state))"
  using Blossom_Path_Recovery_terminates[of state]
  by(intro Blossom_Path_Recovery_correct_ret_1)
    (auto intro: invar_recovery_holds Recovery.Blossom_Path_Recovery_ret)

lemma Blossom_Path_Recovery_impl_correct:
  "invar_recovery H B D N state \<Longrightarrow> graph_augmenting_path input_graph (mate_abstract M0)
    (Recovery.recovered_path (Recovery.Blossom_Path_Recovery_impl H B D N state))"
  using Blossom_Path_Recovery_terminates[of state] Blossom_Path_Recovery_correct[of state]
  by(simp add: Recovery.Blossom_Path_Recovery_impl_same)

end

subsection "Search and recovery composition"

lemma result_path_properties:
  assumes "invar_search state" "qbs_status state = Quadratic_Path p es"
  shows "Recovery.Blossom_Path_Recovery_dom (qbs_hierarchy state) (qbs_cycle_edges state)
      (qbs_bases state) (qbs_parents state)
      (Recovery.initial_recovery p es T0 (qbs_hints state) out0)"
    "graph_augmenting_path input_graph (mate_abstract M0)
      (Recovery.recovered_path (result_path state T0 out0))"
  using assms search_recovery_precond[OF assms] initial_workspaces(4)
  by(simp only: result_path_def assms(2) Quadratic_Blossom_Search_status.simps Recovery.lift_path_def;
    intro Blossom_Path_Recovery_terminates Blossom_Path_Recovery_impl_correct initial_recovery_full;
    auto simp: recovery_precond_def recovery_workspaces_def
      elim!: invar_search_props invar_representatives_props)+

lemma Quadratic_Blossom_Search_run_path:
  "qbs_status (Quadratic_Blossom_Search_impl initial_search_state) = Quadratic_Path p es \<Longrightarrow>
    graph_augmenting_path input_graph (mate_abstract M0) (Recovery.recovered_path (Quadratic_Blossom_Search_run U0
    L0 C0 H0 P0 B0 D0 N0 J0 fresh0 T0 out0))"
  using result_path_properties(2)[OF initial_search_properties(2)]
  by(simp add: Quadratic_Blossom_Search_run_def)
lemma Quadratic_Blossom_Search_run_correct:
  "augmenting_path_result_spec
    (Quadratic_Blossom_Search_run U0 L0 C0 H0 P0 B0 D0 N0 J0 fresh0 T0 out0)"
proof(cases "qbs_status (Quadratic_Blossom_Search_impl initial_search_state)")
  case Quadratic_Searching
  thus ?thesis
    using Quadratic_Blossom_Search_impl_correct
    by(simp add: search_result_spec_def)
next
  case Quadratic_Exhausted
  thus ?thesis
    using Quadratic_Blossom_Search_impl_correct
    by(simp add: search_result_spec_def augmenting_path_result_spec_def
      Quadratic_Blossom_Search_run_def result_path_def Recovery.initial_recovery_def)
next
  case (Quadratic_Path p es)
  hence "graph_augmenting_path input_graph (mate_abstract M0)
    (Recovery.recovered_path (Quadratic_Blossom_Search_run U0 L0 C0 H0 P0 B0 D0 N0 J0 fresh0 T0 out0))"
    by(rule Quadratic_Blossom_Search_run_path)
  thus ?thesis
    by(auto simp: augmenting_path_result_spec_def matching_augmenting_path_def)
qed

end

end
