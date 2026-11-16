theory Cubic_Blossom_Concrete
  imports Blossom_Executable.Cubic_Blossom_Instantiation
begin

provenance ai

section "The concrete search and matching loop"

text "The generic composition of Cubic_Blossom_Imperative is instantiated with flat arrays: a
  prepared CSR graph, the array union-find, nil-valued and pair-valued maps, prefix buffers and the
  flat cycle stack. Vertex names below n are original vertices; the names from n up to
  n + n div 2 name blossoms, and n + n div 2 is the nil value. The workspace is one record of
  array handles that every search reuses."

record Quadratic_Search_Workspace =
  qsw_forest :: "nat array * nat array * nat array * nat array * nat array"
  qsw_components :: "nat array * nat array * nat array"
  qsw_owners :: "nat array"
  qsw_forest_edges :: "nat array"
  qsw_cycle_edges :: "nat array"
  qsw_frontier :: "nat array"
  qsw_navigation :: "nat array"
  qsw_bases :: "nat array"
  qsw_hints :: "nat array"
  qsw_headers :: "nat array"
  qsw_pool :: "nat array"
  qsw_left :: "nat array"
  qsw_right :: "nat array"
  qsw_marks :: "nat array"
  qsw_positions :: "nat array"
  qsw_tasks :: "nat array"

locale Cubic_Blossom_Prepared = csr_graph_imp n "{..<n}" B E
  for n :: nat and B :: "nat list" and E :: "nat list" +
  fixes graph :: "nat set set"
  assumes rows: "!!v. v < n ==> (!) E ` {B ! v..<B ! Suc v} = {w. {v, w} : graph}"
    and edges: "!!e. e : graph ==> EX u<n. EX v<n. u ~= v & e = {u, v}"
begin

definition "adjacency v = (if v < n then Some {w. {v, w} : graph} else None)"

lemma quadratic_matching_lookup_bounded:
  assumes "quadratic_matching_invar (n + n div 2) G M"
  shows "((if x : {..<n + n div 2} & quadratic_matching_partner M x ~= n + n div 2
      then Some (quadratic_matching_partner M x) else None) = Some y) =
    (quadratic_matching_lookup (n + n div 2) M x = Some y)"
proof(cases "x < n + n div 2")
  case True
  thus ?thesis
    by(simp add: quadratic_matching.buddy_lookup_def quadratic_matching.get_partner_def)
next
  case False
  note inst = quadratic_matching_instance[of "n + n div 2"]
  have "graph_matching G (quadratic_matching_abstract (n + n div 2) M)"
    using blossom_matching.matching(1)[OF inst] assms
    by blast
  hence "Vs (quadratic_matching_abstract (n + n div 2) M) <= {..<n + n div 2}"
    using quadratic_matching.matching.universe[of "n + n div 2" G M] assms Vs_subset[of _ G]
    unfolding quadratic_matching_invar_def
    by blast
  moreover have "(quadratic_matching_lookup (n + n div 2) M x = Some y) =
      ({x, y} : quadratic_matching_abstract (n + n div 2) M)"
    using blossom_matching.lookup_partner[OF inst] assms
    by blast
  ultimately show ?thesis
    using False
    by(auto intro: ccontr dest!: vs_member_intro[of x "{x, y}", OF insertI1])
qed

end

locale Cubic_Blossom_Models = Cubic_Blossom_Prepared +
  fixes M :: "nat => nat" and U :: "(nat => nat) Quadratic_Union_Find_state"
    and L D out :: "nat => nat" and P Bc :: "nat => nat * nat" and Nl J :: "nat => nat * nat"
  assumes models: "quadratic_matching_invar (n + n div 2) graph M" "array_uf_invar (n + n div 2) U"

sublocale Cubic_Blossom_Models \<subseteq> Abs: Quadratic_Blossom_Search_Lifting
  where K = "{..<n + n div 2}" and V0 = "{..<n}" and nil = "n + n div 2" and graph_lookup = "%G. G"
    and adj_insert = insert and adj_isin = "%S x. x : S" and adj_abstract = id
    and adj_choose = "%S. SOME x. x : S" and adj_empty = "{}" and adj_delete = "%x S. S - {x}"
    and adj_invar = finite and graph_invar = "%_. True"
    and fset_invar = "%S. S <= {..<n + n div 2}" and fset_abstract = id and fset_empty = "{}"
    and fset_insert = insert and fset_delete = "%x S. S - {x}" and fset_isin = "%S x. x : S"
    and forest_evens = evens and forest_odds = odds and forest_roots = roots
    and forest_path = "quadratic_forest_model_path (n + n div 2)"
    and forest_abstract = "quadratic_forest.abstract_forest (n + n div 2)"
    and forest_invar = "quadratic_forest.forest_invar (n + n div 2)"
    and forest_empty = "quadratic_forest_model_empty (n + n div 2)" and forest_extend = quadratic_forest_model_extend
    and forest_contract = "quadratic_forest.contract_fork (n + n div 2)"
    and mate_empty = "%_. n + n div 2" and mate_invar = "quadratic_matching_invar (n + n div 2)"
    and mate_partner = quadratic_matching_partner and mate_augment = quadratic_matching_augment
    and mate_abstract = "quadratic_matching_abstract (n + n div 2)"
    and mate_contract = "quadratic_matching_contract (n + n div 2)"
    and mate_expand = "quadratic_matching_expand (n + n div 2)" and mate_add = quadratic_matching_add
    and hierarchy_ids = quadratic_hierarchy_ids and hierarchy_tops = quadratic_hierarchy_tops
    and hierarchy_universe = quadratic_hierarchy_universe and hierarchy_members = quadratic_hierarchy_members
    and hierarchy_invar = quadratic_hierarchy_invar and hierarchy_abstract = quadratic_hierarchy_abstract
    and hierarchy_compound = quadratic_hierarchy_compound and hierarchy_edges = quadratic_hierarchy_edges
    and hierarchy_children = quadratic_hierarchy_children and hierarchy_merge = quadratic_hierarchy_merge
    and cap = n and queue_invar = "%xs. length xs <= n" and queue_abstract = id and queue_empty = "[]"
    and queue_push = "%xs x. xs @ [x]" and queue_pop = "%xs. (hd xs, tl xs)" and queue_is_empty = "%xs. xs = []"
    and uf_invar = "array_uf_invar (n + n div 2)" and uf_representative = array_uf_representative
    and uf_find = array_uf_find and uf_union = array_uf_union and uf_reset = "array_uf_reset (n + n div 2)"
    and owner_invar = "%_. True" and owner_update = fun_upd and owner_lookup = id
    and edge_invar = "%_. True" and edge_update = fun_upd and edge_lookup = id
    and cursor_invar = csr_invar and cursor_abstract = csr_abstract and cursor_iterated = csr_iterated
    and cursor_remaining = csr_remaining and cursor_current = csr_current and cursor_has = csr_has
    and cursor_move = csr_move and cursor_reset = csr_reset
    and base_invar = "%_. True" and base_update = fun_upd and base_lookup = id
    and link_invar = "%_. True" and link_update = fun_upd and link_lookup = id
    and G = adjacency and vs = "[0..<n]" and M0 = M
    and task_cap = "Suc (n + n div 2)" and output_cap = n and task_invar = "%xs. length xs <= Suc (n + n div 2)"
    and task_abstract = id and task_empty = "[]" and task_push = "%xs x. x # xs" and task_pop = tl
    and task_top = hd and task_is_empty = "%xs. xs = []"
    and output_invar = "%_. True" and output_update = fun_upd and output_lookup = id
proof intro_locales
  show "Set {} insert (%x S. S - {x}) (%S x. x : S) id finite"
    by unfold_locales auto
  show "Set_Choose_axioms {} (%S x. x : S) (%S. SOME x. x : S)"
    by unfold_locales (auto intro: someI_ex)
  show "alternating_forest_spec evens odds (quadratic_forest_model_path (n + n div 2))
      (quadratic_forest.abstract_forest (n + n div 2)) (quadratic_forest.forest_invar (n + n div 2)) roots
      (%S. S <= {..<n + n div 2}) id"
    "alternating_forest_ordinary_extension_spec_axioms (%S. S <= {..<n + n div 2}) id evens odds
      (quadratic_forest.abstract_forest (n + n div 2)) (quadratic_forest.forest_invar (n + n div 2)) roots
      quadratic_forest_model_extend (quadratic_forest_model_empty (n + n div 2)) {..<n + n div 2} {}"
    using quadratic_forest.satisified[of "n + n div 2"]
    by(simp_all add: alternating_forest_ordinary_extension_spec_def)
  show "alternating_forest_fork_contraction_spec_axioms id evens odds
      (quadratic_forest_model_path (n + n div 2)) (quadratic_forest.abstract_forest (n + n div 2))
      (quadratic_forest.forest_invar (n + n div 2)) roots {..<n + n div 2}
      (quadratic_forest.contract_fork (n + n div 2))"
    using quadratic_forest.spec_satisfied[of "n + n div 2"]
    by(simp add: alternating_forest_fork_contraction_spec_def)
  show "bounded_queue n (%xs. length xs <= n) id [] (%xs x. xs @ [x]) (%xs. (hd xs, tl xs)) (%xs. xs = [])"
    "fixed_univ_map {..<n + n div 2} (%_. True) fun_upd id"
    "bounded_stack (Suc (n + n div 2)) (%xs. length xs <= Suc (n + n div 2)) id [] (%xs x. x # xs) tl hd
      (%xs. xs = [])"
    by(rule quadratic_list_queue recovery_list_stack
      array_fun_fixed_univ_map[unfolded array_fun_upd_def array_fun_lookup_def, folded id_def])+
  show "Matching_Specs {..<n + n div 2} (n + n div 2) (quadratic_matching_invar (n + n div 2))
      (quadratic_matching_abstract (n + n div 2)) quadratic_matching_partner"
    by(rule conjunct1[OF quadratic_matching_instance[unfolded blossom_matching_def]])
  show "blossom_matching_axioms {..<n + n div 2} (%_. n + n div 2)
      (quadratic_matching_invar (n + n div 2))
      (%M v. if v : {..<n + n div 2} & quadratic_matching_partner M v ~= n + n div 2
        then Some (quadratic_matching_partner M v) else None)
      quadratic_matching_partner quadratic_matching_augment (quadratic_matching_abstract (n + n div 2))
      (quadratic_matching_contract (n + n div 2)) (quadratic_matching_expand (n + n div 2)) quadratic_matching_add"
    unfolding blossom_matching_axioms_def
    by(simp only: quadratic_matching_lookup_bounded cong: imp_cong)
      (rule conjunct2[OF quadratic_matching_instance[unfolded blossom_matching_def blossom_matching_axioms_def]])
qed

context Cubic_Blossom_Models
begin

lemma digraph_adjacency: "Abs.Graph.digraph_abs adjacency = {(u, v). u < n & {u, v} : graph}"
  by(auto simp: Abs.Graph.digraph_abs_def Abs.Graph.neighbourhood_def adjacency_def split: if_splits)

lemma input_graph_eq: "Abs.input_graph = graph"
  using edges
  by(auto simp: Abs.input_graph_def digraph_adjacency; blast)

lemma graph_edge: "{v, w} : graph ==> v < n & w < n & v ~= w"
  using edges[of "{v, w}"]
  by(auto simp: doubleton_eq_iff)

lemma initial_models:
  "Abs.initial_axioms U L (%v. B ! v) (quadratic_singletons n) P Bc D Nl J [n..<n + n div 2]"
proof-
  have finite: "finite {w. {v, w} : graph}" for v
    by(rule finite_subset[of _ "{..<n}"]) (auto dest: graph_edge)
  have loop: "{u} ~: graph" for u
    using graph_edge[of u u]
    by(simp only: insert_absorb2) blast
  show ?thesis
    unfolding Abs.initial_axioms_def Abs.input_axioms_def input_graph_eq
    using finite loop rows
    by(auto simp: models csr_init_invar Abs.Graph.graph_inv_def Abs.Graph.finite_graph_def
      Abs.Graph.finite_vsets_def digraph_adjacency Abs.Graph.neighbourhood_def adjacency_def
      csr_abstract_def seg_def dVs_def insert_commute dest: graph_edge)
qed

lemma initial_recovery: "Abs.initial_recovery_axioms [] out"
  by(simp add: Abs.initial_recovery_axioms_def)

end

lemma quadratic_buffer_prefix:
  assumes "k <= n" "Quadratic_Blossom_Search_Path_Buffer.buffer_view id R 0 k False = xs"
  shows "xs @ drop k (map R [0..<n]) = map R [0..<n]" "length xs = k"
  using assms append_take_drop_id[of k "map R [0..<n]"]
  by(auto simp: Quadratic_Blossom_Search_Path_Buffer.buffer_view_def[OF quadratic_buffer_instance] take_map)

lemma longest_disj_sfx_common:
  "s1 = [] | s2 = [] | hd s1 ~= hd s2 ==> longest_disj_sfx (c @ b # s1) (c @ b # s2) = (b # s1, b # s2)"
proof(induction c arbitrary: b)
  case Nil
  thus ?case
    by(cases s1; cases s2) auto
next
  case (Cons a c)
  thus ?case
    by(cases c) (auto simp: neq_Nil_conv)
qed

lemma paired_prefixes_disjoint_suffix:
  assumes "quadratic_forest.paired_prefixes_result px py shared p q" "px ~= []" "py ~= []"
  shows "shared = (last px = last py)"
    "shared ==> longest_disj_sfx (rev px) (rev py) = (rev p, rev q)"
    "~ shared ==> p = px & q = py"
proof-
  show "~ shared ==> p = px & q = py"
    using assms(1)
    by(simp add: quadratic_forest.paired_prefixes_result_def)
  show "shared = (last px = last py)"
  proof(cases shared)
    case True
    then obtain r where "px = p @ r" "py = q @ r" "p ~= []" "q ~= []" "last p = last q"
      using assms(1)
      by(auto simp: quadratic_forest.paired_prefixes_result_def)
    thus ?thesis
      using True
      by(cases r rule: rev_cases) auto
  next
    case False
    hence "set px Int set py = {}"
      using assms(1)
      by(simp add: quadratic_forest.paired_prefixes_result_def)
    thus ?thesis
      using False assms(2,3) last_in_set[of px] last_in_set[of py]
      by auto
  qed
  show "longest_disj_sfx (rev px) (rev py) = (rev p, rev q)" if sh: shared
  proof-
    obtain r where r: "px = p @ r" "py = q @ r" and ne: "p ~= []" "q ~= []" and last: "last p = last q"
      and disj: "set (butlast p) Int set (butlast q) = {}"
      using assms(1) sh
      by(auto simp: quadratic_forest.paired_prefixes_result_def)
    have p: "rev p = last p # rev (butlast p)" and q: "rev q = last q # rev (butlast q)"
      using arg_cong[OF append_butlast_last_id[OF ne(1)], of rev]
        arg_cong[OF append_butlast_last_id[OF ne(2)], of rev]
          by simp_all
    have "rev (butlast p) = [] | rev (butlast q) = [] | hd (rev (butlast p)) ~= hd (rev (butlast q))"
      using disj
      by(auto simp: hd_rev neq_Nil_conv)
    thus ?thesis
      unfolding r rev_append p q last
      by(rule longest_disj_sfx_common)
  qed
qed

text "The forest storage of a reused workspace is only known by its array lengths."

definition "quadratic_forest_workspace N Fi = (case Fi of (li, pai, Hi, NXi, PVi) =>
  len_assn N li * len_assn N pai * len_assn N Hi * len_assn N NXi * len_assn N PVi)"

lemma nil_buckets_release:
  "nil_buckets_assn n nb C (Hi, NXi, PVi) \<Longrightarrow>\<^sub>A len_assn nb Hi * len_assn n NXi * len_assn n PVi"
  by(cases C) (sep_auto simp: len_assn_def array_fun_val_assn_def array_fun_assn_def)

lemma quadratic_forest_release:
  "quadratic_forest_assn N F Fi \<Longrightarrow>\<^sub>A quadratic_forest_workspace N Fi"
proof(cases Fi)
  case (fields li pai Hi NXi PVi)
  have "quadratic_forest_assn N F (li, pai, Hi, NXi, PVi) \<Longrightarrow>\<^sub>A
      len_assn N li * len_assn N pai * (\<exists>\<^sub>AC. nil_buckets_assn N N C (Hi, NXi, PVi))"
    unfolding quadratic_forest.contractable_forest_assn_def quadratic_forest.forest_storage_assn_def
      quadratic_forest.forest_labels_assn_def quadratic_forest.indexed_parents_assn_def
    by(sep_auto simp: len_assn_def array_fun_assn_def)
  also have "... \<Longrightarrow>\<^sub>A len_assn N li * len_assn N pai * (len_assn N Hi * len_assn N NXi * len_assn N PVi)"
    by(intro ent_star_mono ent_refl ent_ex_preI nil_buckets_release)
  finally show ?thesis
    by(simp add: fields quadratic_forest_workspace_def mult.assoc)
qed

definition "quadratic_recover_into N (Wi :: Quadratic_Search_Workspace) Bi u v plen qlen =
  Blossom_Path_Recovery_Buffer.recover_into N (%Wi. array_fun_lookup_imp (qsw_bases Wi))
    (Cubic_Blossom_Refinement.recovery_route_into pair_map_update pair_map_read qsw_navigation qsw_hints)
    (Cubic_Blossom_Refinement.recovery_route_index pair_map_read qsw_hints)
    (%Wi. pair_map_read (qsw_headers Wi)) (%Wi. array_fun_lookup_imp (qsw_pool Wi))
    (%Wi. pair_map_read (qsw_cycle_edges Wi)) (%Wi. cycle_stack_read (qsw_tasks Wi))
    (Cubic_Blossom_Refinement.recovery_stack_write cycle_stack_update qsw_tasks)
    (%Wi plen qlen. Quadratic_Blossom_Search_Cycle_Imperative.augmenting_read array_fun_lookup_imp
      (qsw_left Wi) plen (qsw_right Wi) qlen)
    (%Wi plen qlen. Quadratic_Blossom_Search_Cycle_Imperative.cycle_edge_into pair_map_read array_fun_lookup_imp
      (qsw_forest_edges Wi) (qsw_left Wi) plen (qsw_right Wi) qlen)
    array_fun_upd_imp Wi Bi plen qlen u v"

sublocale Cubic_Blossom_Models \<subseteq> Imp: Cubic_Blossom_Refinement
  where K = "{..<n + n div 2}" and V0 = "{..<n}" and nil = "n + n div 2" and graph_lookup = "%G. G"
    and adj_insert = insert and adj_isin = "%S x. x : S" and adj_abstract = id
    and adj_choose = "%S. SOME x. x : S" and adj_empty = "{}" and adj_delete = "%x S. S - {x}"
    and adj_invar = finite and graph_invar = "%_. True"
    and fset_invar = "%S. S <= {..<n + n div 2}" and fset_abstract = id and fset_empty = "{}"
    and fset_insert = insert and fset_delete = "%x S. S - {x}" and fset_isin = "%S x. x : S"
    and forest_evens = evens and forest_odds = odds and forest_roots = roots
    and forest_path = "quadratic_forest_model_path (n + n div 2)"
    and forest_abstract = "quadratic_forest.abstract_forest (n + n div 2)"
    and forest_invar = "quadratic_forest.forest_invar (n + n div 2)"
    and forest_empty = "quadratic_forest_model_empty (n + n div 2)" and forest_extend = quadratic_forest_model_extend
    and forest_contract = "quadratic_forest.contract_fork (n + n div 2)"
    and mate_empty = "%_. n + n div 2" and mate_invar = "quadratic_matching_invar (n + n div 2)"
    and mate_partner = quadratic_matching_partner and mate_augment = quadratic_matching_augment
    and mate_abstract = "quadratic_matching_abstract (n + n div 2)"
    and mate_contract = "quadratic_matching_contract (n + n div 2)"
    and mate_expand = "quadratic_matching_expand (n + n div 2)" and mate_add = quadratic_matching_add
    and hierarchy_ids = quadratic_hierarchy_ids and hierarchy_tops = quadratic_hierarchy_tops
    and hierarchy_universe = quadratic_hierarchy_universe and hierarchy_members = quadratic_hierarchy_members
    and hierarchy_invar = quadratic_hierarchy_invar and hierarchy_abstract = quadratic_hierarchy_abstract
    and hierarchy_compound = quadratic_hierarchy_compound and hierarchy_edges = quadratic_hierarchy_edges
    and hierarchy_children = quadratic_hierarchy_children and hierarchy_merge = quadratic_hierarchy_merge
    and cap = n and queue_invar = "%xs. length xs <= n" and queue_abstract = id and queue_empty = "[]"
    and queue_push = "%xs x. xs @ [x]" and queue_pop = "%xs. (hd xs, tl xs)" and queue_is_empty = "%xs. xs = []"
    and uf_invar = "array_uf_invar (n + n div 2)" and uf_representative = array_uf_representative
    and uf_find = array_uf_find and uf_union = array_uf_union and uf_reset = "array_uf_reset (n + n div 2)"
    and owner_invar = "%_. True" and owner_update = fun_upd and owner_lookup = id
    and edge_invar = "%_. True" and edge_update = fun_upd and edge_lookup = id
    and cursor_invar = csr_invar and cursor_abstract = csr_abstract and cursor_iterated = csr_iterated
    and cursor_remaining = csr_remaining and cursor_current = csr_current and cursor_has = csr_has
    and cursor_move = csr_move and cursor_reset = csr_reset
    and base_invar = "%_. True" and base_update = fun_upd and base_lookup = id
    and link_invar = "%_. True" and link_update = fun_upd and link_lookup = id
    and G = adjacency and vs = "[0..<n]" and M0 = M
    and task_cap = "Suc (n + n div 2)" and output_cap = n
    and output_invar = "%_. True" and output_update = fun_upd and output_lookup = id
    and U0 = U and L0 = L and C0 = "%v. B ! v" and H0 = "quadratic_singletons n" and P0 = P and B0 = Bc
    and D0 = D and N0 = Nl and J0 = J and fresh0 = "[n..<n + n div 2]" and T0 = "[]" and out0 = out
    and edge_update_imp = pair_map_update and edge_lookup_imp = pair_map_read
    and frontier_invar = "%_. True" and frontier_update = fun_upd and frontier_lookup = id
    and frontier_update_imp = array_fun_upd_imp and frontier_lookup_imp = array_fun_lookup_imp
    and forest_extend_imp = "%Fi x y z. quadratic_forest_extend_into (n + n div 2) x y z Fi"
    and link_update_imp = pair_map_update and link_lookup_imp = pair_map_read
    and owner_update_imp = array_fun_upd_imp and owner_lookup_imp = array_fun_lookup_imp
    and pool_cap = "n + n div 2" and pool_invar = "%_. True" and pool_update = fun_upd and pool_lookup = id
    and pool_update_imp = array_fun_upd_imp and pool_lookup_imp = array_fun_lookup_imp
    and path_cap = n and path_invar = "%_. True" and path_update = fun_upd and path_lookup = id
    and path_update_imp = array_fun_upd_imp and path_lookup_imp = array_fun_lookup_imp
    and uf_union_imp = array_uf_union_into and uf_find_imp = array_uf_query
    and forest_classify_imp = quadratic_forest_classify
    and base_update_imp = array_fun_upd_imp and base_lookup_imp = array_fun_lookup_imp
    and header_invar = "%_. True" and header_update = fun_upd and header_lookup = id
    and header_update_imp = pair_map_update and header_lookup_imp = pair_map_read
    and forest_contract_into = "quadratic_forest_contract_into (n + n div 2)" and vertex_at = "%i. i"
    and forest_workspace_assn = "quadratic_forest_workspace (n + n div 2)"
    and matching_assn = "quadratic_matching_assn n (n + n div 2)" and mate_read_imp = array_fun_lookup_imp
    and forest_clear_into = "quadratic_forest_clear_into (n + n div 2)"
    and forest_root_into = "%Fi v. quadratic_forest_add_root_into v Fi"
    and forest_assn = "quadratic_forest_assn (n + n div 2)" and uf_assn = "array_uf_handle_assn (n + n div 2)"
    and owner_assn = "array_fun_assn (n + n div 2)" and edge_assn = "pair_map_assn (n + n div 2)"
    and frontier_assn = "array_fun_assn n" and link_assn = "pair_map_assn (n + n div 2)"
    and base_assn = "array_fun_assn (n + n div 2)" and header_assn = "pair_map_assn (n + n div 2)"
    and pool_assn = "array_fun_assn (n + n div 2)" and path_assn = "array_fun_assn n"
    and get_forest = qsw_forest and get_union_find = qsw_components and get_owners = qsw_owners
    and get_forest_edges = qsw_forest_edges and get_cycle_edges = qsw_cycle_edges
    and get_frontier = qsw_frontier and get_navigation = qsw_navigation and get_bases = qsw_bases
    and get_hints = qsw_hints and get_headers = qsw_headers and get_pool = qsw_pool
    and get_left = qsw_left and get_right = qsw_right and get_marks = qsw_marks
    and get_positions = qsw_positions and get_tasks = qsw_tasks
    and reset_components_into = "array_uf_reset_into (n + n div 2)"
    and clear_marks_into = "array_fun_clear_unit 0 (n + n div 2)"
    and forest_paths_into = "quadratic_forest_paths_into (n + n div 2)"
    and empty_cursor = "(0, 0)" and row_begin = csr_row_begin and row_has = csr_row_has
    and row_read = csr_row_read and row_advance = csr_row_advance
    and first_fresh = n and fresh_vertex = "%i. i" and fresh_limit = "n + n div 2"
    and recover_path_into = "quadratic_recover_into (n + n div 2)"
    and slot_invar = "%_. True" and slot_update = fun_upd and slot_lookup = id
    and slot_assn = "cycle_stack_map_assn (Suc (n + n div 2))" and slot_update_imp = cycle_stack_update
    and slot_lookup_imp = cycle_stack_read
    and output_assn = "array_fun_assn n" and output_update_imp = array_fun_upd_imp
    and output_lookup_imp = array_fun_lookup_imp
    and graph_storage = "csr_blocks_assn (%v. B ! v)"
    and marks_assn = "%tag Ai Ii. quadratic_forest.paired_marks_assn (n + n div 2) tag [] [] Ai Ii"
    and cursor_register = csr_row_rel
proof intro_locales
  note stack_inst = cycle_stack_map_instance[of "Suc (n + n div 2)",
    unfolded array_fun_upd_def array_fun_lookup_def, folded id_def]
  show "fixed_univ_map {..<Suc (n + n div 2)} (%_. True) (fun_upd :: (nat => quadratic_cycle_slot) => _) id"
    "fixed_univ_map_basic_imp {..<Suc (n + n div 2)} (%_. True) id id (cycle_stack_map_assn (Suc (n + n div 2)))
      cycle_stack_read"
    "fixed_univ_map_imp_axioms {..<Suc (n + n div 2)} (%_. True) fun_upd id (cycle_stack_map_assn (Suc (n + n div 2)))
      cycle_stack_update"
    by(rule fixed_univ_map_imp.axioms[OF stack_inst])+
  note pair_inst = pair_map_instance[of "n + n div 2", unfolded array_fun_upd_def array_fun_lookup_def, folded id_def]
  show "fixed_univ_map_basic_imp {..<n + n div 2} (%_. True) id id (pair_map_assn (n + n div 2)) pair_map_read"
    "fixed_univ_map_imp_axioms {..<n + n div 2} (%_. True) fun_upd id (pair_map_assn (n + n div 2)) pair_map_update"
    by(rule fixed_univ_map_imp.axioms[OF pair_inst])+
  show "Quadratic_Blossom_Search_thms_axioms {..<n + n div 2} {..<n} (n + n div 2) (%G. G) (%S x. x : S) id {}
      finite (%_. True) (quadratic_matching_invar (n + n div 2)) quadratic_hierarchy_ids quadratic_hierarchy_tops
      quadratic_hierarchy_universe quadratic_hierarchy_members quadratic_hierarchy_invar quadratic_hierarchy_children
      n (%xs. length xs <= n) id (array_uf_invar (n + n div 2)) (%_. True) (%_. True) csr_invar csr_abstract
      (%_. True) (%_. True) adjacency [0..<n] M (Suc (n + n div 2)) n (%xs. length xs <= Suc (n + n div 2)) id
      (%_. True) U L ((!) B) (quadratic_singletons n) P Bc D Nl J [n..<n + n div 2] [] out"
    by(rule Quadratic_Blossom_Search_thms_axioms.intro initial_models initial_recovery)+
  show "Quadratic_Blossom_Search_Extension_Imperative_axioms id evens odds (quadratic_forest.forest_invar (n + n div 2))
      quadratic_forest_model_extend (quadratic_forest_assn (n + n div 2))
      (%Fi x y z. quadratic_forest_extend_into (n + n div 2) x y z Fi)"
  proof unfold_locales
    show "<quadratic_forest_assn (n + n div 2) F Fi> quadratic_forest_extend_into (n + n div 2) x y z Fi
        <%_. quadratic_forest_assn (n + n div 2) (quadratic_forest_model_extend F x y z) Fi>"
      if "Abs.Forest.forest_extension_precond F E x y z" for F E x y z Fi
      using that
      by(intro quadratic_forest.contractable_extend_into_rule[of _ _ E])
        (simp add: Abs.Forest.forest_extension_precond_def quadratic_forest.forest_extension_precond_def)
  qed
  show "Quadratic_Blossom_Search_Cycle_Imperative_axioms (%S x. x : S) evens odds
      (quadratic_forest.forest_invar (n + n div 2)) (array_uf_invar (n + n div 2)) array_uf_find array_uf_union
      (quadratic_forest_assn (n + n div 2)) {..<n + n div 2} (array_uf_handle_assn (n + n div 2))
      array_uf_union_into array_uf_query quadratic_forest_classify"
  proof unfold_locales
    show "<array_uf_handle_assn (n + n div 2) U Ui> array_uf_union_into Ui x y
        <%_. array_uf_handle_assn (n + n div 2) (array_uf_union U x y) Ui>"
      if "array_uf_invar (n + n div 2) U" "x : {..<n + n div 2}" "y : {..<n + n div 2}"
      for U :: "(nat => nat, 'z) Quadratic_Union_Find_state_scheme" and x y Ui
      using that
      by(intro array_uf_union_into_rule) simp_all
    show "<array_uf_handle_assn (n + n div 2) U Ui> array_uf_query Ui x
        <%r. array_uf_handle_assn (n + n div 2) (snd (array_uf_find U x)) Ui * \<up>(r = fst (array_uf_find U x))>"
      if "array_uf_invar (n + n div 2) U" "x : {..<n + n div 2}"
      for U :: "(nat => nat, 'z) Quadratic_Union_Find_state_scheme" and x Ui
      using that
      by(sep_auto heap: array_uf_query_rule simp: Array_Union_Find.find_rep_def)
    show "<quadratic_forest_assn (n + n div 2) F Fi> quadratic_forest_classify Fi c
        <%label. quadratic_forest_assn (n + n div 2) F Fi *
          \<up>(label = (if c : odds F then 1 else if c : evens F then 2 else 0))>"
      if "quadratic_forest.forest_invar (n + n div 2) M F" "c : {..<n + n div 2}" for M F c Fi
      using that unfolding quadratic_forest.contractable_forest_assn_def
      by(sep_auto heap: quadratic_forest.classify_rule)
  qed
  show "Quadratic_Blossom_Search_Contraction_Imperative_axioms id evens odds (quadratic_forest_model_path (n + n div 2))
      (quadratic_forest.forest_invar (n + n div 2)) (quadratic_forest.contract_fork (n + n div 2))
      (quadratic_forest_assn (n + n div 2)) n (%_. True) id (array_fun_assn n) {..<n + n div 2}
      (quadratic_forest_contract_into (n + n div 2))"
  proof unfold_locales
    show "<quadratic_forest_assn (n + n div 2) F Fi * array_fun_assn n P P_i * array_fun_assn n Q Q_i>
        quadratic_forest_contract_into (n + n div 2) Fi P_i plen Q_i qlen b
        <%_. quadratic_forest_assn (n + n div 2) (quadratic_forest.contract_fork (n + n div 2) F (p @ [a]) (q @ [a]) b) Fi *
          array_fun_assn n P P_i * array_fun_assn n Q Q_i>"
      if pre: "Abs.Forest.contract_fork_precond M F x y p q a b rest contr" "a : id (evens F)"
        "b : {..<n + n div 2}" "plen <= n" "qlen <= n"
        "Quadratic_Blossom_Search_Path_Buffer.buffer_view id P 0 plen False = p @ [a]"
        "Quadratic_Blossom_Search_Path_Buffer.buffer_view id Q 0 qlen False = q @ [a]"
      for M F x y p q a b rest contr P Q plen qlen Fi P_i Q_i
    proof-
      note P = quadratic_buffer_prefix[OF pre(4,6)] and Q = quadratic_buffer_prefix[OF pre(5,7)]
      show ?thesis
        unfolding array_fun_assn_def
        using quadratic_forest_contract_into_rule[OF pre(1-3), where Ci = Fi and Pa = P_i and Qa = Q_i
          and ps = "drop plen (map P [0..<n])" and qs = "drop qlen (map Q [0..<n])"]
        by(simp only: P Q)
    qed
  qed
  show "Quadratic_Blossom_Search_Initialisation_Imperative_axioms {..<n} (%G. G) (%S x. x : S) {}
      (%S. S <= {..<n + n div 2}) {} insert (quadratic_forest_model_empty (n + n div 2))
      (quadratic_matching_invar (n + n div 2)) quadratic_matching_partner adjacency M {..<n + n div 2}
      (quadratic_forest_assn (n + n div 2)) (quadratic_forest_workspace (n + n div 2))
      (quadratic_matching_assn n (n + n div 2)) array_fun_lookup_imp (quadratic_forest_clear_into (n + n div 2))
      (%Fi v. quadratic_forest_add_root_into v Fi)"
  proof unfold_locales
    show "<quadratic_matching_assn n (n + n div 2) M Mi> array_fun_lookup_imp Mi v
        <%z. quadratic_matching_assn n (n + n div 2) M Mi * \<up>(z = quadratic_matching_partner M v)>"
      if "v : {..<n}" for v Mi
      using that
      by(sep_auto heap: quadratic_matching_read_rule simp: quadratic_matching.get_partner_def)
    show "<quadratic_forest_workspace (n + n div 2) Fi> quadratic_forest_clear_into (n + n div 2) Fi
        <%_. quadratic_forest_assn (n + n div 2) (quadratic_forest_model_empty (n + n div 2) {}) Fi>" for Fi
      by(cases Fi) (simp add: quadratic_forest_workspace_def quadratic_forest_clear_storage_rule)
    show "<quadratic_forest_assn (n + n div 2) (quadratic_forest_model_empty (n + n div 2) S) Fi>
        quadratic_forest_add_root_into v Fi
        <%_. quadratic_forest_assn (n + n div 2) (quadratic_forest_model_empty (n + n div 2) (insert v S)) Fi>"
      if "S <= {..<n + n div 2}" "v : {..<n + n div 2}" for S v Fi
      using that
      by(intro quadratic_forest.contractable_add_root_into_rule) auto
  qed

qed

sublocale Cubic_Blossom_Models \<subseteq> Imp: Cubic_Blossom_Refinement_Contracts
  where K = "{..<n + n div 2}" and V0 = "{..<n}" and nil = "n + n div 2" and graph_lookup = "%G. G"
    and adj_insert = insert and adj_isin = "%S x. x : S" and adj_abstract = id
    and adj_choose = "%S. SOME x. x : S" and adj_empty = "{}" and adj_delete = "%x S. S - {x}"
    and adj_invar = finite and graph_invar = "%_. True"
    and fset_invar = "%S. S <= {..<n + n div 2}" and fset_abstract = id and fset_empty = "{}"
    and fset_insert = insert and fset_delete = "%x S. S - {x}" and fset_isin = "%S x. x : S"
    and forest_evens = evens and forest_odds = odds and forest_roots = roots
    and forest_path = "quadratic_forest_model_path (n + n div 2)"
    and forest_abstract = "quadratic_forest.abstract_forest (n + n div 2)"
    and forest_invar = "quadratic_forest.forest_invar (n + n div 2)"
    and forest_empty = "quadratic_forest_model_empty (n + n div 2)" and forest_extend = quadratic_forest_model_extend
    and forest_contract = "quadratic_forest.contract_fork (n + n div 2)"
    and mate_empty = "%_. n + n div 2" and mate_invar = "quadratic_matching_invar (n + n div 2)"
    and mate_partner = quadratic_matching_partner and mate_augment = quadratic_matching_augment
    and mate_abstract = "quadratic_matching_abstract (n + n div 2)"
    and mate_contract = "quadratic_matching_contract (n + n div 2)"
    and mate_expand = "quadratic_matching_expand (n + n div 2)" and mate_add = quadratic_matching_add
    and hierarchy_ids = quadratic_hierarchy_ids and hierarchy_tops = quadratic_hierarchy_tops
    and hierarchy_universe = quadratic_hierarchy_universe and hierarchy_members = quadratic_hierarchy_members
    and hierarchy_invar = quadratic_hierarchy_invar and hierarchy_abstract = quadratic_hierarchy_abstract
    and hierarchy_compound = quadratic_hierarchy_compound and hierarchy_edges = quadratic_hierarchy_edges
    and hierarchy_children = quadratic_hierarchy_children and hierarchy_merge = quadratic_hierarchy_merge
    and cap = n and queue_invar = "%xs. length xs <= n" and queue_abstract = id and queue_empty = "[]"
    and queue_push = "%xs x. xs @ [x]" and queue_pop = "%xs. (hd xs, tl xs)" and queue_is_empty = "%xs. xs = []"
    and uf_invar = "array_uf_invar (n + n div 2)" and uf_representative = array_uf_representative
    and uf_find = array_uf_find and uf_union = array_uf_union and uf_reset = "array_uf_reset (n + n div 2)"
    and owner_invar = "%_. True" and owner_update = fun_upd and owner_lookup = id
    and edge_invar = "%_. True" and edge_update = fun_upd and edge_lookup = id
    and cursor_invar = csr_invar and cursor_abstract = csr_abstract and cursor_iterated = csr_iterated
    and cursor_remaining = csr_remaining and cursor_current = csr_current and cursor_has = csr_has
    and cursor_move = csr_move and cursor_reset = csr_reset
    and base_invar = "%_. True" and base_update = fun_upd and base_lookup = id
    and link_invar = "%_. True" and link_update = fun_upd and link_lookup = id
    and G = adjacency and vs = "[0..<n]" and M0 = M
    and task_cap = "Suc (n + n div 2)" and output_cap = n
    and output_invar = "%_. True" and output_update = fun_upd and output_lookup = id
    and U0 = U and L0 = L and C0 = "%v. B ! v" and H0 = "quadratic_singletons n" and P0 = P and B0 = Bc
    and D0 = D and N0 = Nl and J0 = J and fresh0 = "[n..<n + n div 2]" and T0 = "[]" and out0 = out
    and edge_update_imp = pair_map_update and edge_lookup_imp = pair_map_read
    and frontier_invar = "%_. True" and frontier_update = fun_upd and frontier_lookup = id
    and frontier_update_imp = array_fun_upd_imp and frontier_lookup_imp = array_fun_lookup_imp
    and forest_extend_imp = "%Fi x y z. quadratic_forest_extend_into (n + n div 2) x y z Fi"
    and link_update_imp = pair_map_update and link_lookup_imp = pair_map_read
    and owner_update_imp = array_fun_upd_imp and owner_lookup_imp = array_fun_lookup_imp
    and pool_cap = "n + n div 2" and pool_invar = "%_. True" and pool_update = fun_upd and pool_lookup = id
    and pool_update_imp = array_fun_upd_imp and pool_lookup_imp = array_fun_lookup_imp
    and path_cap = n and path_invar = "%_. True" and path_update = fun_upd and path_lookup = id
    and path_update_imp = array_fun_upd_imp and path_lookup_imp = array_fun_lookup_imp
    and uf_union_imp = array_uf_union_into and uf_find_imp = array_uf_query
    and forest_classify_imp = quadratic_forest_classify
    and base_update_imp = array_fun_upd_imp and base_lookup_imp = array_fun_lookup_imp
    and header_invar = "%_. True" and header_update = fun_upd and header_lookup = id
    and header_update_imp = pair_map_update and header_lookup_imp = pair_map_read
    and forest_contract_into = "quadratic_forest_contract_into (n + n div 2)" and vertex_at = "%i. i"
    and forest_workspace_assn = "quadratic_forest_workspace (n + n div 2)"
    and matching_assn = "quadratic_matching_assn n (n + n div 2)" and mate_read_imp = array_fun_lookup_imp
    and forest_clear_into = "quadratic_forest_clear_into (n + n div 2)"
    and forest_root_into = "%Fi v. quadratic_forest_add_root_into v Fi"
    and forest_assn = "quadratic_forest_assn (n + n div 2)" and uf_assn = "array_uf_handle_assn (n + n div 2)"
    and owner_assn = "array_fun_assn (n + n div 2)" and edge_assn = "pair_map_assn (n + n div 2)"
    and frontier_assn = "array_fun_assn n" and link_assn = "pair_map_assn (n + n div 2)"
    and base_assn = "array_fun_assn (n + n div 2)" and header_assn = "pair_map_assn (n + n div 2)"
    and pool_assn = "array_fun_assn (n + n div 2)" and path_assn = "array_fun_assn n"
    and get_forest = qsw_forest and get_union_find = qsw_components and get_owners = qsw_owners
    and get_forest_edges = qsw_forest_edges and get_cycle_edges = qsw_cycle_edges
    and get_frontier = qsw_frontier and get_navigation = qsw_navigation and get_bases = qsw_bases
    and get_hints = qsw_hints and get_headers = qsw_headers and get_pool = qsw_pool
    and get_left = qsw_left and get_right = qsw_right and get_marks = qsw_marks
    and get_positions = qsw_positions and get_tasks = qsw_tasks
    and reset_components_into = "array_uf_reset_into (n + n div 2)"
    and clear_marks_into = "array_fun_clear_unit 0 (n + n div 2)"
    and forest_paths_into = "quadratic_forest_paths_into (n + n div 2)"
    and empty_cursor = "(0, 0)" and row_begin = csr_row_begin and row_has = csr_row_has
    and row_read = csr_row_read and row_advance = csr_row_advance
    and first_fresh = n and fresh_vertex = "%i. i" and fresh_limit = "n + n div 2"
    and recover_path_into = "quadratic_recover_into (n + n div 2)"
    and slot_invar = "%_. True" and slot_update = fun_upd and slot_lookup = id
    and slot_assn = "cycle_stack_map_assn (Suc (n + n div 2))" and slot_update_imp = cycle_stack_update
    and slot_lookup_imp = cycle_stack_read
    and output_assn = "array_fun_assn n" and output_update_imp = array_fun_upd_imp
    and output_lookup_imp = array_fun_lookup_imp
    and graph_storage = "csr_blocks_assn (%v. B ! v)"
    and marks_assn = "%tag Ai Ii. quadratic_forest.paired_marks_assn (n + n div 2) tag [] [] Ai Ii"
    and cursor_register = csr_row_rel
proof(intro_locales, goal_cases)
  case 1
  show ?case
  proof unfold_locales
    have blocks: "csr_blocks_assn c = csr_blocks_assn c'" for c c'
      by(simp add: csr_blocks_assn_def)
    show "snd (array_uf_find U v) = U" for U :: "(nat => nat, 'z) Quadratic_Union_Find_state_scheme" and v
      by(simp add: Array_Union_Find.find_rep_def)
    show "<csr_blocks_assn ((!) B) Gi> csr_row_begin Gi v
        <%it. csr_blocks_assn ((!) B) Gi * \<up>(csr_row_rel C v it)>"
      if "csr_invar C" "v : {..<n}" "csr_iterated C v = {}" for C v Gi
      using csr_row_begin_unscanned_rule[OF that] blocks[of C "(!) B"]
      by simp
    show "<csr_blocks_assn ((!) B) Gi> csr_row_read Gi it
        <%x. csr_blocks_assn ((!) B) Gi * \<up>(x = csr_current C v)>"
      if "csr_invar C" "v : {..<n}" "csr_row_rel C v it" "csr_has C v" for C v it Gi
      using csr_row_read_rule[OF that(2,3)] csr_row_has_refine[OF that(3)] that(4) blocks[of C "(!) B"]
      by simp
    show "csr_row_has it = csr_has C v" if "csr_row_rel C v it" for C v it
      by(rule csr_row_has_refine[OF that])
    show "csr_row_rel (csr_move C v) v (csr_row_advance it)"
      if "csr_invar C" "v : {..<n}" "csr_row_rel C v it" "csr_has C v" for C v it
      using that
      by(intro csr_row_advance_refine) (simp_all add: csr_row_has_refine)
  qed
next
  case 2
  show ?case
  proof(unfold_locales, goal_cases)
    case (1 M F Fi Ai Ii P Q Pi Qi x y tag)
    have view: "Imp.Contraction.Pool.buffer_view (%i. xs ! i) 0 k False = take k xs"
      if "length xs = n" "k <= n" for xs :: "nat list" and k
      using that
      by(simp add: Imp.Contraction.Pool.buffer_view_def) (intro nth_equalityI; simp)
    have ne: "quadratic_forest_model_path (n + n div 2) F x ~= []" "quadratic_forest_model_path (n + n div 2) F y ~= []"
      using Abs.Forest.get_path[OF 1(1) _ refl, of x] Abs.Forest.get_path[OF 1(1) _ refl, of y] 1(2,3)
      by auto
    have arrays: "quadratic_forest_assn (n + n div 2) F Fi *
          quadratic_forest.paired_marks_assn (n + n div 2) (Suc tag) [] [] Ai Ii * Pi \<mapsto>\<^sub>a xs * Qi \<mapsto>\<^sub>a ys
        \<Longrightarrow>\<^sub>A quadratic_forest_assn (n + n div 2) F Fi *
          quadratic_forest.paired_marks_assn (n + n div 2) (Suc tag) [] [] Ai Ii *
          (\<exists>\<^sub>AP' Q'. array_fun_assn n P' Pi * array_fun_assn n Q' Qi *
            \<up>(Imp.paths_result F x y (shared, plen, qlen) P' Q'))"
      if pure: "length xs = n" "length ys = n" "plen <= n" "qlen <= n"
          "quadratic_forest.paired_prefixes_result (quadratic_forest_model_path (n + n div 2) F x)
            (quadratic_forest_model_path (n + n div 2) F y) shared (take plen xs) (take qlen ys)"
      for xs ys shared plen qlen
    proof-
      note glue = paired_prefixes_disjoint_suffix[OF pure(5) ne]
      have result: "Imp.paths_result F x y (shared, plen, qlen) ((!) xs) ((!) ys)"
        using pure glue view[of xs plen] view[of ys qlen]
        by(auto simp: Imp.paths_result_def)
      have "Pi \<mapsto>\<^sub>a xs = array_fun_assn n ((!) xs) Pi" "Qi \<mapsto>\<^sub>a ys = array_fun_assn n ((!) ys) Qi"
        using pure map_nth[of xs] map_nth[of ys]
        by(simp_all add: array_fun_assn_def)
      thus ?thesis
        using result
        by sep_auto
    qed
    have pre: "array_fun_assn n P Pi = Pi \<mapsto>\<^sub>a map P [0..<n]" "array_fun_assn n Q Qi = Qi \<mapsto>\<^sub>a map Q [0..<n]"
      by(simp_all add: array_fun_assn_def)
    have rule: "<quadratic_forest_assn (n + n div 2) F Fi *
        quadratic_forest.paired_marks_assn (n + n div 2) tag [] [] Ai Ii *
        Pi \<mapsto>\<^sub>a map P [0..<n] * Qi \<mapsto>\<^sub>a map Q [0..<n]> quadratic_forest_paths_into (n + n div 2) Fi Ai Ii Pi Qi x y tag
        <quadratic_forest.forest_paths_array_post (n + n div 2) F Fi x y tag n n Ai Ii Pi Qi>"
      using quadratic_forest.paths_into_array_rule[OF 1(1-3), of "map P [0..<n]" "map Q [0..<n]"] 1(4,5)
      by simp
    show ?case
      unfolding pre
    proof(rule ht_cons_post[OF rule], rule ent_true_drop(2), goal_cases)
      case (1 r)
      show ?case
      proof(cases r)
        case (fields shared plen qlen)
        show ?thesis
          unfolding fields quadratic_forest.forest_paths_array_post_def prod.case
          by(intro ent_ex_preI, rule ent_pure_preI, elim conjE, rule arrays)
      qed
    qed
  next
    case 2
    show ?case
      by simp
  qed
next
  case 3
  show ?case
  proof(unfold_locales, goal_cases)
    case (3 Wi Bi u v plen qlen)
    show ?case
      by(simp add: quadratic_recover_into_def Imp.Recovery_Ops.recover_into_def)
  next
    case (4 F Fi)
    show ?case
      by(rule quadratic_forest_release)
  next
    case (8 U Ui)
    show ?case
      by(rule array_uf_reset_into_rule)
  next
    case (9 tag Ai Ii)
    show ?case
      using quadratic_forest.paired_workspace_clear_rule[of "n + n div 2" tag "[]" "[]" Ai Ii "Suc 0"]
      by(simp add: quadratic_forest.paired_workspace_clear_def)
  qed simp_all
qed

lemma (in Cubic_Blossom_Models) refinement_contracts:
  "Cubic_Blossom_Refinement_Contracts {..<n} (n + n div 2) (%G. G) insert (%S x. x : S) id (%S. SOME x. x : S) {}
    (%x S. S - {x}) finite (%_. True) (%S. S <= {..<n + n div 2}) id {} insert (%x S. S - {x}) (%S x. x : S)
    evens odds roots (quadratic_forest_model_path (n + n div 2)) (quadratic_forest.abstract_forest (n + n div 2))
    (quadratic_forest.forest_invar (n + n div 2)) (quadratic_forest_model_empty (n + n div 2))
    quadratic_forest_model_extend (quadratic_forest.contract_fork (n + n div 2)) (%_. n + n div 2)
    (quadratic_matching_invar (n + n div 2)) quadratic_matching_partner quadratic_matching_augment
    (quadratic_matching_abstract (n + n div 2)) (quadratic_matching_contract (n + n div 2))
    (quadratic_matching_expand (n + n div 2)) quadratic_matching_add quadratic_hierarchy_ids
    quadratic_hierarchy_tops quadratic_hierarchy_universe quadratic_hierarchy_members quadratic_hierarchy_invar
    quadratic_hierarchy_abstract quadratic_hierarchy_compound quadratic_hierarchy_edges quadratic_hierarchy_merge
    quadratic_hierarchy_children n (%xs. length xs <= n) id [] (%xs x. xs @ [x]) (%xs. (hd xs, tl xs))
    (%xs. xs = []) (array_uf_invar (n + n div 2)) array_uf_representative array_uf_find array_uf_union
    (array_uf_reset (n + n div 2)) (%_. True) fun_upd id (%_. True) fun_upd id csr_abstract csr_iterated
    csr_remaining csr_current csr_has csr_move csr_reset (%_. True) fun_upd id (%_. True) fun_upd id adjacency
    [0..<n] M pair_map_update pair_map_read (%_. True) fun_upd id array_fun_upd_imp array_fun_lookup_imp
    (%Fi x y z. quadratic_forest_extend_into (n + n div 2) x y z Fi) pair_map_update pair_map_read
    array_fun_upd_imp array_fun_lookup_imp (n + n div 2) (%_. True) fun_upd id array_fun_upd_imp
    array_fun_lookup_imp n (%_. True) fun_upd id array_fun_upd_imp array_fun_lookup_imp array_uf_union_into
    array_uf_query quadratic_forest_classify array_fun_upd_imp array_fun_lookup_imp (%_. True) fun_upd id
    pair_map_update pair_map_read (quadratic_forest_contract_into (n + n div 2)) (%i. i)
    (quadratic_forest_workspace (n + n div 2)) (quadratic_matching_assn n (n + n div 2)) array_fun_lookup_imp
    (quadratic_forest_clear_into (n + n div 2)) (%Fi v. quadratic_forest_add_root_into v Fi)
    (quadratic_forest_assn (n + n div 2)) (array_uf_handle_assn (n + n div 2)) (array_fun_assn (n + n div 2))
    (pair_map_assn (n + n div 2)) (array_fun_assn n) (pair_map_assn (n + n div 2)) (array_fun_assn (n + n div 2))
    (pair_map_assn (n + n div 2)) (array_fun_assn (n + n div 2)) (array_fun_assn n) n qsw_forest_edges
    qsw_cycle_edges qsw_navigation qsw_bases qsw_hints qsw_headers qsw_pool qsw_left qsw_right
    (array_uf_reset_into (n + n div 2)) (array_fun_clear_unit 0 (n + n div 2))
    (quadratic_forest_paths_into (n + n div 2)) csr_row_has csr_row_read csr_row_advance n (%i. i)
    (Suc (n + n div 2)) n fun_upd id U L ((!) B) (quadratic_singletons n) P Bc D Nl J [n..<n + n div 2] [] out
    {..<n + n div 2} csr_row_begin (quadratic_recover_into (n + n div 2)) csr_invar (%_. True) (%_. True)
    fun_upd id (cycle_stack_map_assn (Suc (n + n div 2))) cycle_stack_update cycle_stack_read (array_fun_assn n)
    array_fun_upd_imp array_fun_lookup_imp (csr_blocks_assn ((!) B))
    (%tag. quadratic_forest.paired_marks_assn (n + n div 2) tag [] []) qsw_tasks csr_row_rel (n + n div 2)"
  by(rule Imp.Cubic_Blossom_Refinement_Contracts_axioms)

context Cubic_Blossom_Prepared
begin

lemma graph_vertices: "Vs graph <= {..<n}"
  by(auto simp: Vs_def dest!: edges)

lemma models_intro:
  "[| quadratic_matching_invar (n + n div 2) graph M; array_uf_invar (n + n div 2) U |] ==>
    Cubic_Blossom_Models n B E graph M U"
  by(intro Cubic_Blossom_Models.intro Cubic_Blossom_Models_axioms.intro Cubic_Blossom_Prepared_axioms)

lemma empty_models: "Cubic_Blossom_Models n B E graph (%_. n + n div 2) array_uf_singletons"
  using graph_vertices
  by(intro models_intro quadratic_matching_empty) auto

lemmas input_graph = Cubic_Blossom_Models.input_graph_eq[OF empty_models]

end

sublocale Cubic_Blossom_Prepared \<subseteq> Run: Cubic_Blossom_Matching
  where K = "{..<n + n div 2}" and V0 = "{..<n}" and nil = "n + n div 2" and graph_lookup = "%G. G"
    and adj_insert = insert and adj_isin = "%S x. x : S" and adj_abstract = id
    and adj_choose = "%S. SOME x. x : S" and adj_empty = "{}" and adj_delete = "%x S. S - {x}"
    and adj_invar = finite and graph_invar = "%_. True"
    and fset_invar = "%S. S <= {..<n + n div 2}" and fset_abstract = id and fset_empty = "{}"
    and fset_insert = insert and fset_delete = "%x S. S - {x}" and fset_isin = "%S x. x : S"
    and forest_evens = evens and forest_odds = odds and forest_roots = roots
    and forest_path = "quadratic_forest_model_path (n + n div 2)"
    and forest_abstract = "quadratic_forest.abstract_forest (n + n div 2)"
    and forest_invar = "quadratic_forest.forest_invar (n + n div 2)"
    and forest_empty = "quadratic_forest_model_empty (n + n div 2)" and forest_extend = quadratic_forest_model_extend
    and forest_contract = "quadratic_forest.contract_fork (n + n div 2)"
    and mate_empty = "%_. n + n div 2" and mate_invar = "quadratic_matching_invar (n + n div 2)"
    and mate_partner = quadratic_matching_partner and mate_augment = quadratic_matching_augment
    and mate_abstract = "quadratic_matching_abstract (n + n div 2)"
    and mate_contract = "quadratic_matching_contract (n + n div 2)"
    and mate_expand = "quadratic_matching_expand (n + n div 2)" and mate_add = quadratic_matching_add
    and hierarchy_ids = quadratic_hierarchy_ids and hierarchy_tops = quadratic_hierarchy_tops
    and hierarchy_universe = quadratic_hierarchy_universe and hierarchy_members = quadratic_hierarchy_members
    and hierarchy_invar = quadratic_hierarchy_invar and hierarchy_abstract = quadratic_hierarchy_abstract
    and hierarchy_compound = quadratic_hierarchy_compound and hierarchy_edges = quadratic_hierarchy_edges
    and hierarchy_children = quadratic_hierarchy_children and hierarchy_merge = quadratic_hierarchy_merge
    and cap = n and queue_invar = "%xs. length xs <= n" and queue_abstract = id and queue_empty = "[]"
    and queue_push = "%xs x. xs @ [x]" and queue_pop = "%xs. (hd xs, tl xs)" and queue_is_empty = "%xs. xs = []"
    and uf_invar = "array_uf_invar (n + n div 2)" and uf_representative = array_uf_representative
    and uf_find = array_uf_find and uf_union = array_uf_union and uf_reset = "array_uf_reset (n + n div 2)"
    and owner_invar = "%_. True" and owner_update = fun_upd and owner_lookup = id
    and edge_invar = "%_. True" and edge_update = fun_upd and edge_lookup = id
    and cursor_invar = csr_invar and cursor_abstract = csr_abstract and cursor_iterated = csr_iterated
    and cursor_remaining = csr_remaining and cursor_current = csr_current and cursor_has = csr_has
    and cursor_move = csr_move and cursor_reset = csr_reset
    and base_invar = "%_. True" and base_update = fun_upd and base_lookup = id
    and link_invar = "%_. True" and link_update = fun_upd and link_lookup = id
    and G = adjacency and vs = "[0..<n]" and M0 = "%_. n + n div 2"
    and task_cap = "Suc (n + n div 2)" and output_cap = n
    and output_invar = "%_. True" and output_update = fun_upd and output_lookup = id
    and U0 = array_uf_singletons and L0 = "%_. 0" and C0 = "%v. B ! v" and H0 = "quadratic_singletons n"
    and P0 = "%_. (0, 0)" and B0 = "%_. (0, 0)" and D0 = "%_. 0" and N0 = "%_. (0, 0)" and J0 = "%_. (0, 0)"
    and fresh0 = "[n..<n + n div 2]" and T0 = "[]" and out0 = "%_. 0"
    and edge_update_imp = pair_map_update and edge_lookup_imp = pair_map_read
    and frontier_invar = "%_. True" and frontier_update = fun_upd and frontier_lookup = id
    and frontier_update_imp = array_fun_upd_imp and frontier_lookup_imp = array_fun_lookup_imp
    and forest_extend_imp = "%Fi x y z. quadratic_forest_extend_into (n + n div 2) x y z Fi"
    and link_update_imp = pair_map_update and link_lookup_imp = pair_map_read
    and owner_update_imp = array_fun_upd_imp and owner_lookup_imp = array_fun_lookup_imp
    and pool_cap = "n + n div 2" and pool_invar = "%_. True" and pool_update = fun_upd and pool_lookup = id
    and pool_update_imp = array_fun_upd_imp and pool_lookup_imp = array_fun_lookup_imp
    and path_cap = n and path_invar = "%_. True" and path_update = fun_upd and path_lookup = id
    and path_update_imp = array_fun_upd_imp and path_lookup_imp = array_fun_lookup_imp
    and uf_union_imp = array_uf_union_into and uf_find_imp = array_uf_query
    and forest_classify_imp = quadratic_forest_classify
    and base_update_imp = array_fun_upd_imp and base_lookup_imp = array_fun_lookup_imp
    and header_invar = "%_. True" and header_update = fun_upd and header_lookup = id
    and header_update_imp = pair_map_update and header_lookup_imp = pair_map_read
    and forest_contract_into = "quadratic_forest_contract_into (n + n div 2)" and vertex_at = "%i. i"
    and forest_workspace_assn = "quadratic_forest_workspace (n + n div 2)"
    and matching_assn = "quadratic_matching_assn n (n + n div 2)" and mate_read_imp = array_fun_lookup_imp
    and forest_clear_into = "quadratic_forest_clear_into (n + n div 2)"
    and forest_root_into = "%Fi v. quadratic_forest_add_root_into v Fi"
    and forest_assn = "quadratic_forest_assn (n + n div 2)" and uf_assn = "array_uf_handle_assn (n + n div 2)"
    and owner_assn = "array_fun_assn (n + n div 2)" and edge_assn = "pair_map_assn (n + n div 2)"
    and frontier_assn = "array_fun_assn n" and link_assn = "pair_map_assn (n + n div 2)"
    and base_assn = "array_fun_assn (n + n div 2)" and header_assn = "pair_map_assn (n + n div 2)"
    and pool_assn = "array_fun_assn (n + n div 2)" and path_assn = "array_fun_assn n"
    and get_forest = qsw_forest and get_union_find = qsw_components and get_owners = qsw_owners
    and get_forest_edges = qsw_forest_edges and get_cycle_edges = qsw_cycle_edges
    and get_frontier = qsw_frontier and get_navigation = qsw_navigation and get_bases = qsw_bases
    and get_hints = qsw_hints and get_headers = qsw_headers and get_pool = qsw_pool
    and get_left = qsw_left and get_right = qsw_right and get_marks = qsw_marks
    and get_positions = qsw_positions and get_tasks = qsw_tasks
    and reset_components_into = "array_uf_reset_into (n + n div 2)"
    and clear_marks_into = "array_fun_clear_unit 0 (n + n div 2)"
    and forest_paths_into = "quadratic_forest_paths_into (n + n div 2)"
    and empty_cursor = "(0, 0)" and row_begin = csr_row_begin and row_has = csr_row_has
    and row_read = csr_row_read and row_advance = csr_row_advance
    and first_fresh = n and fresh_vertex = "%i. i" and fresh_limit = "n + n div 2"
    and recover_path_into = "quadratic_recover_into (n + n div 2)"
    and slot_invar = "%_. True" and slot_update = fun_upd and slot_lookup = id
    and slot_assn = "cycle_stack_map_assn (Suc (n + n div 2))" and slot_update_imp = cycle_stack_update
    and slot_lookup_imp = cycle_stack_read
    and output_assn = "array_fun_assn n" and output_update_imp = array_fun_upd_imp
    and output_lookup_imp = array_fun_lookup_imp
    and graph_storage = "csr_blocks_assn (%v. B ! v)"
    and marks_assn = "%tag Ai Ii. quadratic_forest.paired_marks_assn (n + n div 2) tag [] [] Ai Ii"
    and cursor_register = csr_row_rel and augment_prefix = quadratic_matching_augment_into
proof(rule Cubic_Blossom_Matching.intro, goal_cases)
  case 1
  show ?case
    by(rule Cubic_Blossom_Models.refinement_contracts[OF empty_models])
next
  case 2
  show ?case
  proof(rule Cubic_Blossom_Matching_axioms.intro, goal_cases)
    case 1
    show ?case
      using 1(1,2) unfolding input_graph
      by(intro Cubic_Blossom_Models.refinement_contracts models_intro)
  next
    case (2 M Mi Bi k out)
    have "set (take k (map out [0..<n])) <= {..<n}"
      using 2(2) graph_vertices unfolding input_graph
      by(auto dest!: subset_path_Vs)
    thus ?case
      using 2(3) unfolding array_fun_assn_def
      by(simp add: quadratic_matching_augment_rule)
  qed
qed

section "Allocating the workspace"

text "All arrays are allocated once, before the first search; every search reuses them."

definition "quadratic_search_workspace_new n = do {
  li \<leftarrow> Array.new (n + n div 2) (0::nat); pai \<leftarrow> Array.new (n + n div 2) (n + n div 2);
  Hi \<leftarrow> Array.new (n + n div 2) (n + n div 2); NXi \<leftarrow> Array.new (n + n div 2) (n + n div 2);
  PVi \<leftarrow> Array.new (n + n div 2) (n + n div 2);
  Ui \<leftarrow> array_uf_new (n + n div 2); Oi \<leftarrow> Array.new (n + n div 2) 0;
  Ei \<leftarrow> pair_map_new (n + n div 2) 0 0; Ci \<leftarrow> pair_map_new (n + n div 2) 0 0;
  Qi \<leftarrow> Array.new n 0; Ni \<leftarrow> pair_map_new (n + n div 2) 0 0; Di \<leftarrow> Array.new (n + n div 2) 0;
  Ji \<leftarrow> pair_map_new (n + n div 2) 0 0; Ri \<leftarrow> pair_map_new (n + n div 2) 0 0;
  Pooli \<leftarrow> Array.new (n + n div 2) 0; Pi \<leftarrow> Array.new n 0; Qli \<leftarrow> Array.new n 0;
  marks \<leftarrow> quadratic_forest.paired_workspace_new (n + n div 2);
  Ti \<leftarrow> cycle_stack_new (Suc (n + n div 2));
  return \<lparr>qsw_forest = (li, pai, Hi, NXi, PVi), qsw_components = Ui, qsw_owners = Oi,
    qsw_forest_edges = Ei, qsw_cycle_edges = Ci, qsw_frontier = Qi, qsw_navigation = Ni, qsw_bases = Di,
    qsw_hints = Ji, qsw_headers = Ri, qsw_pool = Pooli, qsw_left = Pi, qsw_right = Qli,
    qsw_marks = fst marks, qsw_positions = snd marks, qsw_tasks = Ti\<rparr> }"

lemma workspace_new_arrays:
  "<emp> quadratic_search_workspace_new n
    <%W. quadratic_forest_workspace (n + n div 2) (qsw_forest W) *
      array_uf_handle_assn (n + n div 2) (array_uf_initial (n + n div 2)) (qsw_components W) *
      array_fun_assn (n + n div 2) (%_. 0) (qsw_owners W) * pair_map_assn (n + n div 2) (%_. (0, 0)) (qsw_forest_edges W) *
      pair_map_assn (n + n div 2) (%_. (0, 0)) (qsw_cycle_edges W) * array_fun_assn n (%_. 0) (qsw_frontier W) *
      pair_map_assn (n + n div 2) (%_. (0, 0)) (qsw_navigation W) * array_fun_assn (n + n div 2) (%_. 0) (qsw_bases W) *
      pair_map_assn (n + n div 2) (%_. (0, 0)) (qsw_hints W) * pair_map_assn (n + n div 2) (%_. (0, 0)) (qsw_headers W) *
      array_fun_assn (n + n div 2) (%_. 0) (qsw_pool W) * array_fun_assn n (%_. 0) (qsw_left W) *
      array_fun_assn n (%_. 0) (qsw_right W) *
      quadratic_forest.paired_marks_assn (n + n div 2) 0 [] [] (qsw_marks W) (qsw_positions W) *
      cycle_stack_map_assn (Suc (n + n div 2)) (%_. (0, 0, 0, 0, False, 0, 0)) (qsw_tasks W)>"
  unfolding quadratic_search_workspace_new_def
  by(sep_auto heap: array_fun_assn_new pair_map_new_rule cycle_stack_new_rule array_uf_new_rule
      quadratic_forest.paired_workspace_new_rule[where tag = 0]
    simp: quadratic_forest_workspace_def len_assn_def array_fun_assn_def)

section "Maximum matching on a prepared CSR graph"

text "The concrete maximum-matching loop. It depends only on the vertex count."

definition "quadratic_matching_run n = Cubic_Blossom_In_Place.matching_into (n + n div 2)
  pair_map_update pair_map_read array_fun_upd_imp array_fun_lookup_imp
  (%Fi x y z. quadratic_forest_extend_into (n + n div 2) x y z Fi) pair_map_update array_fun_upd_imp
  array_fun_lookup_imp array_fun_upd_imp array_fun_lookup_imp array_uf_union_into array_uf_query
  quadratic_forest_classify array_fun_upd_imp array_fun_lookup_imp pair_map_update
  (quadratic_forest_contract_into (n + n div 2)) (%i. i) array_fun_lookup_imp
  (quadratic_forest_clear_into (n + n div 2)) (%Fi v. quadratic_forest_add_root_into v Fi) n qsw_forest
  qsw_components qsw_owners qsw_forest_edges qsw_cycle_edges qsw_frontier qsw_navigation qsw_bases qsw_hints
  qsw_headers qsw_pool qsw_left qsw_right qsw_marks qsw_positions (array_uf_reset_into (n + n div 2))
  (array_fun_clear_unit 0 (n + n div 2)) (quadratic_forest_paths_into (n + n div 2))
  (quadratic_recover_into (n + n div 2)) (0, 0) csr_row_begin csr_row_has csr_row_read csr_row_advance n
  (%i. i) quadratic_matching_augment_into"

context Cubic_Blossom_Prepared
begin

lemma matching_run: "Run.matching_into quadratic_matching_augment_into = quadratic_matching_run n"
  by(simp add: quadratic_matching_run_def)

lemma storage_intro:
  "array_uf_invar (n + n div 2) (U :: (nat => nat) Quadratic_Union_Find_state) ==>
    quadratic_forest_workspace (n + n div 2) (qsw_forest W) * array_uf_handle_assn (n + n div 2) U (qsw_components W) *
    array_fun_assn (n + n div 2) L (qsw_owners W) * pair_map_assn (n + n div 2) Pe (qsw_forest_edges W) *
    pair_map_assn (n + n div 2) Ce (qsw_cycle_edges W) * array_fun_assn n T (qsw_frontier W) *
    pair_map_assn (n + n div 2) Nv (qsw_navigation W) * array_fun_assn (n + n div 2) D (qsw_bases W) *
    pair_map_assn (n + n div 2) J (qsw_hints W) * pair_map_assn (n + n div 2) R (qsw_headers W) *
    array_fun_assn (n + n div 2) C (qsw_pool W) * array_fun_assn n P (qsw_left W) *
    array_fun_assn n Q (qsw_right W) *
    quadratic_forest.paired_marks_assn (n + n div 2) tag [] [] (qsw_marks W) (qsw_positions W) *
    cycle_stack_map_assn (Suc (n + n div 2)) F (qsw_tasks W) \<Longrightarrow>\<^sub>A Run.matching_storage W"
  unfolding Run.matching_storage_def Run.task_storage_def Run.reusable_storage_def
  by sep_auto

lemma workspace_new_rule: "<emp> quadratic_search_workspace_new n <Run.matching_storage>"
  by(rule ht_cons_post[OF workspace_new_arrays], rule ent_true_drop(2), rule storage_intro) simp

lemma buffer_array: "Run.matching_buffer xs Bi = (\<exists>\<^sub>Aout. array_fun_assn n out Bi * \<up>(xs = map out [0..<n]))"
  by(simp add: Run.matching_buffer_def)

text "From the empty matching the loop returns a maximum-cardinality matching of the graph. The
  graph, the workspace and the output buffer are kept for further use."

theorem matching_into_maximum:
  "<csr_blocks_assn ((!) B) Gi * array_fun_assn n (%_. n + n div 2) Mi * Run.matching_storage Wi *
      array_fun_assn n out Bi>
    quadratic_matching_run n Gi Mi Wi Bi
    <%_. \<exists>\<^sub>AM out'. csr_blocks_assn ((!) B) Gi * array_fun_assn n M Mi * Run.matching_storage Wi *
      array_fun_assn n out' Bi * \<up>(max_card_matching graph (quadratic_matching_abstract (n + n div 2) M))>"
proof-
  note run = Run.matching_into_correct[of Gi Mi Wi "map out [0..<n]" Bi,
    unfolded input_graph quadratic_matching_empty_storage buffer_array matching_run]
  show ?thesis
    by(intro ht_cons_post[OF ht_cons_pre[OF _ run]]) (sep_auto simp: quadratic_matching_assn_def)+
qed


end

end
