theory Cubic_Blossom_Input
  imports Directed_Set_Graphs.CSR_Edge_Input
begin

provenance ai

section "The two orientations of an input edge"

definition quadratic_edge_has_next :: "nat array \<times> nat array \<Rightarrow> nat \<Rightarrow> bool Heap" where
  "quadratic_edge_has_next = (\<lambda>(Ta, Ha) i. do {
    m \<leftarrow> Array.len Ta; return (i < 2 * m) })"

definition quadratic_edge_source :: "nat array \<times> nat array \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "quadratic_edge_source A i =
    (if i mod 2 = 0 then src_imp A (i div 2) else tgt_imp A (i div 2))"

definition quadratic_edge_target :: "nat array \<times> nat array \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "quadratic_edge_target A i =
    (if i mod 2 = 0 then tgt_imp A (i div 2) else src_imp A (i div 2))"

global_interpretation quadratic_raw: imp_csr_buildup_code n quadratic_edge_has_next
  edge_cur edge_adv quadratic_edge_source quadratic_edge_target
  for n
  defines quadratic_csr_raw = quadratic_raw.csr_build_imp
    and quadratic_csr_count = quadratic_raw.count_imp
    and quadratic_csr_prefix = quadratic_raw.prefix_imp
    and quadratic_csr_init = quadratic_raw.init_E_imp
    and quadratic_csr_fill = quadratic_raw.fill_imp
  done

declare quadratic_raw.count_imp.simps[code] quadratic_raw.prefix_imp.simps[code]
  quadratic_raw.fill_imp.simps[code]

definition "quadratic_csr_build n Ta Ha = quadratic_csr_raw n (Ta, Ha) 0"

section "Well-formed endpoint lists"

locale Cubic_Blossom_Input =
  fixes n :: nat and tails heads :: "nat list"
  assumes input: "length heads = length tails"
    "\<And>i. i < length tails \<Longrightarrow> tails ! i < n"
    "\<And>i. i < length tails \<Longrightarrow> heads ! i < n"
    "\<And>i. i < length tails \<Longrightarrow> tails ! i \<noteq> heads ! i"
    and edges_distinct: "inj_on (\<lambda>i. {tails ! i, heads ! i}) {..<length tails}"
begin

definition "input_graph = {{tails ! i, heads ! i} |i. i < length tails}"

definition "input_source i = (if even i then tails ! (i div 2) else heads ! (i div 2))"
definition "input_target i = (if even i then heads ! (i div 2) else tails ! (i div 2))"

lemma orientation_index:
  "i < 2 * length tails \<Longrightarrow> i div 2 < length tails"
  by(simp add: div_less_iff_less_mult mult.commute)

lemma input_endpoint_bounds:
  "i < 2 * length tails \<Longrightarrow> input_source i < n"
  "i < 2 * length tails \<Longrightarrow> input_target i < n"
  using input(2,3) orientation_index
  by(auto simp: input_source_def input_target_def)


lemma input_orientation_inj:
  "inj_on (\<lambda>i. (input_source i, input_target i)) {..<2 * length tails}"
proof(rule inj_onI)
  fix i j
  assume "i \<in> {..<2 * length tails}" "j \<in> {..<2 * length tails}"
    "(input_source i, input_target i) = (input_source j, input_target j)"
  hence bounds: "i div 2 < length tails" "j div 2 < length tails"
    and endpoints: "input_source i = input_source j" "input_target i = input_target j"
    using orientation_index
    by auto
  have "i div 2 = j div 2"
    using edges_distinct bounds endpoints
    by(auto simp: inj_on_def input_source_def input_target_def doubleton_eq_iff split: if_splits)
  moreover have "even i = even j"
    using endpoints input(4)[of "i div 2"] bounds calculation
    by(auto simp: input_source_def input_target_def split: if_splits)
  ultimately show "i = j"
    by(simp add: even_iff_mod_2_eq_zero; presburger)
qed

sublocale raw: csr_buildup "range_next (2 * length tails)" "range_seq (2 * length tails)"
  "\<lambda>_. True" input_source n 0
  by unfold_locales
    (auto simp: range_next_def range_seq_def upt_conv_Cons input_endpoint_bounds split: if_splits)

lemma quadratic_edge_source_rule:
  "i < 2 * length tails \<Longrightarrow>
    <ends_assn tails heads A> quadratic_edge_source A i
    <\<lambda>x. ends_assn tails heads A * \<up>(x = input_source i)>"
  using orientation_index[of i] input(1)
  by(cases "even i")
    (sep_auto simp: quadratic_edge_source_def input_source_def
      heap: src_imp_rule tgt_imp_rule)+

lemma quadratic_edge_target_rule:
  "i < 2 * length tails \<Longrightarrow>
    <ends_assn tails heads A> quadratic_edge_target A i
    <\<lambda>x. ends_assn tails heads A * \<up>(x = input_target i)>"
  using orientation_index[of i] input(1)
  by(cases "even i")
    (sep_auto simp: quadratic_edge_target_def input_target_def
      heap: src_imp_rule tgt_imp_rule)+

sublocale build: imp_csr_buildup "range_next (2 * length tails)" "range_seq (2 * length tails)"
  "\<lambda>_. True" input_source n 0 quadratic_edge_has_next edge_cur edge_adv
  quadratic_edge_source quadratic_edge_target input_target "\<lambda>s si. si = s" "ends_assn tails heads"
proof(unfold_locales, goal_cases)
  case (1 s si A)
  thus ?case
    by(cases A) (sep_auto simp: quadratic_edge_has_next_def ends_assn_def range_next_def)
qed (sep_auto heap: quadratic_edge_source_rule quadratic_edge_target_rule
    simp: edge_cur_def edge_adv_def range_next_def range_seq_def split: if_splits)+

lemma quadratic_csr_raw_rule:
  "<Ta \<mapsto>\<^sub>a tails * Ha \<mapsto>\<^sub>a heads>
    quadratic_csr_raw n (Ta, Ha) 0
    <\<lambda>(Ba, Ea). Ta \<mapsto>\<^sub>a tails * Ha \<mapsto>\<^sub>a heads *
      Ba \<mapsto>\<^sub>a raw.B_spec * Ea \<mapsto>\<^sub>a map input_target raw.E_spec>"
  using build.csr_build_imp_rule[of "(Ta, Ha)" 0]
  by(simp add: quadratic_csr_raw_def ends_assn_def)

lemma input_orientations:
  "(v, w) \<in> (\<lambda>i. (input_source i, input_target i)) ` {..<2 * length tails} \<longleftrightarrow>
    {v, w} \<in> input_graph"
proof
  assume "(v, w) \<in> (\<lambda>i. (input_source i, input_target i)) ` {..<2 * length tails}"
  then obtain i where "i < 2 * length tails" "v = input_source i" "w = input_target i"
    by auto
  thus "{v, w} \<in> input_graph"
    using orientation_index[of i]
    by(auto simp: input_graph_def input_source_def input_target_def doubleton_eq_iff)
next
  assume "{v, w} \<in> input_graph"
  then obtain i where "i < length tails" "{v, w} = {tails ! i, heads ! i}"
    by(auto simp: input_graph_def)
  moreover have "(tails ! i, heads ! i) \<in> (\<lambda>i. (input_source i, input_target i)) ` {..<2 * length tails}"
    using calculation(1)
    by(intro image_eqI[where x="2 * i"]) (auto simp: input_source_def input_target_def)
  moreover have "(heads ! i, tails ! i) \<in> (\<lambda>i. (input_source i, input_target i)) ` {..<2 * length tails}"
    using calculation(1)
    by(intro image_eqI[where x="Suc (2 * i)"]) (auto simp: input_source_def input_target_def)
  ultimately show "(v, w) \<in> (\<lambda>i. (input_source i, input_target i)) ` {..<2 * length tails}"
    by(auto simp: doubleton_eq_iff)
qed

lemma raw_bounds:
  "\<lbrakk>i \<le> j; j \<le> n\<rbrakk> \<Longrightarrow> raw.B_spec ! i \<le> raw.B_spec ! j"
  "i \<le> n \<Longrightarrow> raw.B_spec ! i \<le> length raw.E_spec"
  using raw.start_mono[of i j] raw.start_mono[of i n] raw.start_n raw.length_E_spec
  by(auto simp: raw.B_spec_nth)

sublocale rows: csr_graph_blocks_imp n "{..<n}" raw.B_spec "map input_target raw.E_spec"
  by unfold_locales (auto simp: raw.length_B_spec intro: raw_bounds)

lemma raw_row:
  "v < n \<Longrightarrow>
    map ((!) (map input_target raw.E_spec)) [raw.B_spec ! v..<raw.B_spec ! Suc v] =
    map input_target (raw.blk v)"
  using raw.csr_block[of v] raw_bounds(2)[of "Suc v"]
  by(simp add: map_nth_upt_take_drop take_map drop_map)

lemma raw_neighbours:
  "v < n \<Longrightarrow>
    (!) (map input_target raw.E_spec) ` {raw.B_spec ! v..<raw.B_spec ! Suc v} =
    {w. {v, w} \<in> input_graph}"
  using raw_row[of v, THEN arg_cong[where f=set]]
  by(auto simp: raw.blk_def raw.es_def range_seq_def input_orientations[symmetric])

lemma raw_targets:
  "set (map input_target raw.E_spec) \<subseteq> {..<n}"
  by(auto simp: raw.E_spec_def raw.blk_def raw.es_def range_seq_def
      intro: input_endpoint_bounds(2))

lemma raw_row_distinct:
  "distinct (map input_target (raw.blk v))"
  using input_orientation_inj
  by(auto simp: distinct_map raw.blk_def raw.es_def range_seq_def inj_on_def)

lemma raw_distinct:
  "v < n \<Longrightarrow>
    inj_on ((!) (map input_target raw.E_spec)) {raw.B_spec ! v..<raw.B_spec ! Suc v}"
  using raw_row_distinct[of v]
  by(simp add: raw_row[symmetric] distinct_map)

definition "prepared_offsets = raw.B_spec"
definition "prepared_neighbours = map input_target raw.E_spec"

sublocale prepared: csr_graph n "{..<n}" prepared_offsets prepared_neighbours
  by unfold_locales
    (auto simp: prepared_offsets_def prepared_neighbours_def raw.length_B_spec
      intro: raw_bounds raw_distinct)

lemma prepared_neighbours:
  "v < n \<Longrightarrow>
    (!) prepared_neighbours ` {prepared_offsets ! v..<prepared_offsets ! Suc v} =
    {w. {v, w} \<in> input_graph}"
  using raw_neighbours
  by(simp add: prepared_offsets_def prepared_neighbours_def)

lemma prepared_capacity:
  "length prepared_neighbours = 2 * length tails"
  by(simp add: prepared_neighbours_def raw.length_E_spec raw.es_def range_seq_def)

lemma quadratic_csr_build_rule:
  "<Ta \<mapsto>\<^sub>a tails * Ha \<mapsto>\<^sub>a heads>
    quadratic_csr_build n Ta Ha
    <\<lambda>(Ba, Ea). Ta \<mapsto>\<^sub>a tails * Ha \<mapsto>\<^sub>a heads *
      Ba \<mapsto>\<^sub>a prepared_offsets * Ea \<mapsto>\<^sub>a prepared_neighbours>"
  using quadratic_csr_raw_rule
  by(simp add: quadratic_csr_build_def prepared_offsets_def prepared_neighbours_def)

lemma prepared_offsets_zero[simp]: "prepared_offsets ! 0 = 0"
  by(simp add: prepared_offsets_def raw.B_spec_nth raw.start_def)

lemma prepared_offsets_last: "prepared_offsets ! n = length prepared_neighbours"
  by(simp add: prepared_offsets_def prepared_neighbours_def raw.B_spec_nth
    raw.start_n raw.length_E_spec)

lemma input_graph_edges:
  "e \<in> input_graph \<Longrightarrow> \<exists>u<n. \<exists>v<n. u \<noteq> v \<and> e = {u, v}"
  using input(2-4)
  by(auto simp: input_graph_def; blast)

lemma input_graph_finite: "finite input_graph"
  by(simp add: input_graph_def)

end

end

