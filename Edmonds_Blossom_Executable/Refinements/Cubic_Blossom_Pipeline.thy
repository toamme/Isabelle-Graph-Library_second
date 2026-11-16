theory Cubic_Blossom_Pipeline
  imports Blossom_Executable.Cubic_Blossom_Concrete Blossom_Executable.Cubic_Blossom_Input
begin

provenance ai_human

section "Maximum matching from two endpoint arrays"

text "The input graph is given by a vertex count n and two arrays of endpoints, with each undirected
  edge occurring once. The CSR graph is built once. The mate array, workspace and output buffer
  are allocated once, then the matching loop runs."

context Cubic_Blossom_Input
begin

lemma prepared: "Cubic_Blossom_Prepared n prepared_offsets prepared_neighbours input_graph"
  by(intro_locales)
    (auto simp: Cubic_Blossom_Prepared_axioms_def prepared_neighbours intro: input_graph_edges)

sublocale Prep: Cubic_Blossom_Prepared n prepared_offsets prepared_neighbours input_graph
  by(rule prepared)

end

definition "quadratic_max_matching n Ta Ha = do {
  G \<leftarrow> quadratic_csr_build n Ta Ha;
  Ma \<leftarrow> Array.new n (n + n div 2);
  Wi \<leftarrow> quadratic_search_workspace_new n;
  Bi \<leftarrow> Array.new n (0::nat);
  quadratic_matching_run n G Ma Wi Bi;
  return Ma }"

context Cubic_Blossom_Input
begin

lemma csr_build_fun_rule:
  "<Ta \<mapsto>\<^sub>a tails * Ha \<mapsto>\<^sub>a heads> quadratic_csr_build n Ta Ha
    <%G. Ta \<mapsto>\<^sub>a tails * Ha \<mapsto>\<^sub>a heads * Prep.csr_blocks_assn ((!) prepared_offsets) G>"
  by(sep_auto heap: quadratic_csr_build_rule simp: Prep.csr_blocks_assn_def split: prod.splits)

text "The returned mate array represents a maximum-cardinality matching of the input graph, and the
  endpoint arrays are unchanged."

theorem max_matching_rule:
  "<Ta \<mapsto>\<^sub>a tails * Ha \<mapsto>\<^sub>a heads> quadratic_max_matching n Ta Ha
    <%Ma. Ta \<mapsto>\<^sub>a tails * Ha \<mapsto>\<^sub>a heads * (\<exists>\<^sub>AM. array_fun_assn n M Ma *
      \<up>(max_card_matching input_graph (quadratic_matching_abstract (n + n div 2) M))) * true>"
  by(sep_auto simp: quadratic_max_matching_def heap: array_fun_assn_new csr_build_fun_rule
    Prep.workspace_new_rule Prep.matching_into_maximum)

end

section "Code generation"

text "The operations of the generic composition are defined in locales with assumptions. An instance
  on the empty graph holds for every vertex count; it gives unconditional definitions of the
  concrete operations. The generic loops are specialised by interpretations of their
  assumption-free locales."

lemma empty_prepared: "Cubic_Blossom_Prepared n (replicate (Suc n) 0) [] {}"
  by(intro Cubic_Blossom_Prepared.intro Cubic_Blossom_Prepared_axioms.intro csr_graph_imp.intro
    csr_graph.intro csr_ranges.intro csr_blocks.intro csr_ranges_axioms.intro) (auto simp: nth_Cons split: nat.splits)

global_interpretation QC: Cubic_Blossom_Models n "replicate (Suc n) 0" "[]" "{}" "%_. n + n div 2"
  array_uf_singletons "%_. 0" "%_. 0" "%_. 0" "%_. (0, 0)" "%_. (0, 0)" "%_. (0, 0)" "%_. (0, 0)" for n
  defines qc_matching_loop = QC.Run.Loop.matching_loop
    and qc_search_into = QC.Run.Runtime.search_into
    and qc_search_loop = QC.Run.Runtime.search_loop
    and qc_neighbourhood = QC.Run.Contraction.Graph.neighbourhood
    and qc_cache_route = QC.Run.Search.Recovery.Cache_Route_impl
    and qc_path_recovery = QC.Run.Search.Recovery.Blossom_Path_Recovery_impl
    and qc_view_read = QC.Run.Contraction.Frontier.view_read
    and qc_joined_read = QC.Run.Contraction.Frontier.joined_read
    and qc_cycle_edge_into = QC.Run.Contraction.cycle_edge_into
    and qc_cycle_step_into = QC.Run.Contraction.cycle_step_into
    and qc_cycle_loop = QC.Run.Contraction.cycle_loop
    and qc_cycle_commit_into = QC.Run.Contraction.cycle_commit_into
    and qc_cycle_schedule_into = QC.Run.Contraction.cycle_schedule_into
    and qc_process_cycle_into = QC.Run.Contraction.process_cycle_into
    and qc_extend_into = QC.Run.Contraction.extend_into
    and qc_commit_contraction_into = QC.Run.Contraction.commit_contraction_into
    and qc_contract_into = QC.Run.Contraction.contract_into
    and qc_initial_vertex_into = QC.Run.Initialisation.initial_vertex_into
    and qc_initial_vertices_into = QC.Run.Initialisation.initial_vertices_into
    and qc_initial_roots_into = QC.Run.Initialisation.initial_roots_into
    and qc_initialise_into = QC.Run.initialise_into
    and qc_representative_into = QC.Run.representative_into
    and qc_extend_search_into = QC.Run.extend_search_into
    and qc_query_paths_into = QC.Run.query_paths_into
    and qc_contract_search_into = QC.Run.contract_search_into
    and qc_recovery_route_into = QC.Run.recovery_route_into
    and qc_recovery_route_index = QC.Run.recovery_route_index
    and qc_recovery_stack_write = QC.Run.recovery_stack_write
  by(rule Cubic_Blossom_Prepared.empty_models[OF empty_prepared])

declare QC.Run.Contraction.cycle_loop.simps[code] QC.Run.Initialisation.initial_vertices_into.simps[code]

text "The search loop takes defined operations as parameters, so the interpretation cannot fold it.
  Its code equations are folded explicitly."

lemmas qc_search_loop_fold = qc_search_loop_def[folded qc_representative_into_def
  qc_extend_search_into_def qc_query_paths_into_def qc_contract_search_into_def]
lemmas qc_search_into_fold = qc_search_into_def[folded qc_initialise_into_def qc_representative_into_def
  qc_extend_search_into_def qc_query_paths_into_def qc_contract_search_into_def qc_search_loop_fold]
lemmas qc_matching_loop_fold = qc_matching_loop_def[folded qc_initialise_into_def
  qc_representative_into_def qc_extend_search_into_def qc_query_paths_into_def
  qc_contract_search_into_def qc_search_loop_fold qc_search_into_fold]

lemmas [code] = QC.Run.Runtime.search_loop.simps[folded qc_search_loop_fold]
  QC.Run.Runtime.search_into_def[folded qc_search_loop_fold qc_search_into_fold]
  QC.Run.Loop.matching_loop.simps[folded qc_search_into_fold qc_matching_loop_fold]

global_interpretation QCache: Blossom_Path_Recovery_Imperative
  where task_cap = "Suc (n + n div 2)" and output_cap = n and nil = "n + n div 2"
    and task_invar = "%xs. length xs <= Suc (n + n div 2)" and task_abstract = id and task_empty = "[]"
    and task_push = "%xs x. x # xs" and task_pop = tl and task_top = hd and task_is_empty = "%xs. xs = []"
    and base_invar = "%_. True" and base_update = fun_upd and base_lookup = id
    and output_invar = "%_. True" and output_update = fun_upd and output_lookup = id
    and hierarchy_children = quadratic_hierarchy_children and edge_lookup = "id :: (nat => nat * nat) => _"
    and K = "{..<n + n div 2}" and link_invar = "%_. True" and link_update = fun_upd and link_lookup = id
    and link_assn = "pair_map_assn (n + n div 2)" and link_update_imp = pair_map_update
    and link_lookup_imp = pair_map_read
  for n
  defines qc_cache_loop = QCache.cache_loop and qc_cache_into = QCache.cache_into
  by(rule QC.Run.recovery_registers[unfolded Blossom_Path_Recovery_Registers_def])

declare QCache.cache_loop.simps[code]

global_interpretation QRec: Blossom_Path_Recovery_Buffer N "%Wi. array_fun_lookup_imp (qsw_bases Wi)"
  qc_recovery_route_into qc_recovery_route_index "%Wi. pair_map_read (qsw_headers Wi)"
  "%Wi. array_fun_lookup_imp (qsw_pool Wi)" "%Wi. pair_map_read (qsw_cycle_edges Wi)"
  "%Wi. cycle_stack_read (qsw_tasks Wi)" qc_recovery_stack_write
  "%Wi plen qlen. qc_joined_read (qsw_left Wi) 0 plen True (qsw_right Wi) 0 qlen False"
  "%Wi plen qlen. qc_cycle_edge_into (qsw_forest_edges Wi) (qsw_left Wi) plen (qsw_right Wi) qlen"
  array_fun_upd_imp for N
  defines quadratic_cycle_child = QRec.cycle_child and quadratic_recovery_loop = QRec.recovery_loop
    and quadratic_recover = QRec.recover_into
  done

declare QRec.recovery_loop.simps[code]

lemmas [code] = QC.Run.recovery_route_into_def[folded qc_cache_into_def]

lemmas [code] = quadratic_recover_into_def[folded qc_recovery_route_into_def qc_recovery_route_index_def
    qc_recovery_stack_write_def qc_joined_read_def qc_cycle_edge_into_def, folded quadratic_recover_def]
  quadratic_matching_run_def[unfolded QC.Run.matching_into_def[abs_def],
    folded qc_search_into_fold qc_matching_loop_fold]

end

