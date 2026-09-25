theory Network_Simplex_Int
  imports Network_Simplex_Initial_Basis_Selector
begin

section ‹The integer instance›

text ‹The executable pipeline is generic over a linearly ordered integral domain @{typ 'n} that
      embeds into the reals via @{locale real_embedding}. Here we take @{typ 'n} to be @{typ int}
      and the embedding to be @{const of_int}, which turns the generic correctness statement into a
      statement about a genuine arbitrary-precision integer program: every capacity, cost, balance
      and flow value is an @{typ int}, and code generation emits SML ‹IntInf›, OCaml ‹zarith› or
      Haskell ‹Integer› arithmetic — no floating point anywhere.›

interpretation int_embedding: real_embedding "of_int :: int ⇒ real"
  by unfold_locales (simp_all add: of_int_less_iff)

text ‹The integer solver locale. Every assumption below is a condition on the input lists alone:
      the homomorphism obligations of @{locale real_embedding} are discharged once and for all by
      @{const of_int}, so nothing about the embedding is left for the caller to supply.›

locale int_selector =
  initial_basis_code_spec where capacity_list = capacity_list
  for capacity_list :: "int list" +
  assumes length_edges: "length capacity_list = m"
      and length_cost: "length cost_list = length capacity_list"
      and length_fst:  "length fst_list  = length capacity_list"
      and length_snd:  "length snd_list  = length capacity_list"
      and length_flow: "length flow_list = length capacity_list"
      and length_b:    "length b_list    = n"
      and cap_neg:     "∀ c ∈ set capacity_list. 0 ≤ c ∨ c = - 1"
      and edges_in_range: "set fst_list ∪ set snd_list ⊆ {1..n}"
      and num_edges_gtr_0: "m > 0"
      and isolated_zero: "⋀i. i < n ⟹ Suc i ∉ set fst_list ∪ set snd_list ⟹ b_list ! i = 0"
      and flow_nonneg: "⋀e. e < m ⟹ 0 ≤ flow_list ! e"
      and flow_le_cap: "⋀e. e < m ⟹ capacity_list ! e ≠ - 1 ⟹ flow_list ! e ≤ capacity_list ! e"
      and balance_sum_zero: "sum_list b_list = 0"
      and block_size_pos:     "0 < block_size"
      and min_candidates_pos: "0 < min_candidates"
      and min_le_max:         "min_candidates ≤ max_candidates"
begin

sublocale initial_basis_selector where capacity_list = capacity_list
                                   and h = "of_int :: int ⇒ real"
  by unfold_locales
     (use edges_in_range in
        ‹simp_all add: length_edges length_cost length_fst length_snd length_flow length_b
                       cap_neg num_edges_gtr_0 isolated_zero
                       flow_nonneg flow_le_cap balance_sum_zero
                       block_size_pos min_candidates_pos min_le_max of_int_less_iff›)

text ‹The three verdicts, now for the integer program. The returned flow @{term fs} is an
      @{typ "int list"}; it is read as the real-valued flow @{term ‹of_int ∘ nth fs›} in order to
      meet the library's real-valued specification.›

theorem int_solve_correct:
  "solve = Optimum fs ⟹
     length fs = m ∧ original_network.is_Opt (λv. of_int (b_lookup v)) (of_int ∘ nth fs)"
  "solve = Infeasible ⟹ ∄ f. original_network.isbflow f (λv. of_int (b_lookup v))"
  "solve = Neg_inf_cycle ⟹ neg_infty_cycle"
  by (rule solve_correct; assumption)+

end

end
