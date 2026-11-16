theory Cubic_Blossom_Imperative
  imports Blossom_Executable.Quadratic_Blossom_Search_Imperative Blossom_Executable.Alternating_Forest_Contraction_Imperative
begin

provenance ai_human

section "Assembling contraction from its components"

locale Quadratic_Blossom_Search_Contraction_Imperative =
  Quadratic_Blossom_Search_Cycle_Imperative where K = K +
  Base_Imp: fixed_univ_map_imp K base_invar base_update base_lookup id
    base_assn base_update_imp base_lookup_imp +
  Headers: fixed_univ_map_imp K header_invar header_update header_lookup id
    header_assn header_update_imp header_lookup_imp
  for K :: "'v::heap set"
    and base_assn base_update_imp base_lookup_imp
    and header_invar :: "'headers \<Rightarrow> bool"
    and header_update :: "'headers \<Rightarrow> 'v \<Rightarrow> (nat \<times> nat) \<Rightarrow> 'headers" and header_lookup
    and header_assn header_update_imp header_lookup_imp +
  fixes forest_contract_into :: "_ \<Rightarrow> _ \<Rightarrow> nat \<Rightarrow> _ \<Rightarrow> nat \<Rightarrow> 'v \<Rightarrow> unit Heap"
  assumes forest_contract_rule:
    "\<lbrakk>Forest.contract_fork_precond M F x y p q a b rest contr;
      a \<in> fset_abstract (forest_evens F); b \<in> K;
      path_invar P; path_invar Q; plen \<le> path_cap; qlen \<le> path_cap;
      Paths.buffer_view P 0 plen False = p @ [a]; Paths.buffer_view Q 0 qlen False = q @ [a]\<rbrakk> \<Longrightarrow>
      <forest_assn F Fi * path_assn P P_i * path_assn Q Q_i>
      forest_contract_into Fi P_i plen Q_i qlen b
      <\<lambda>_. forest_assn (forest_contract F (p @ [a]) (q @ [a]) b) Fi *
        path_assn P P_i * path_assn Q Q_i>"
begin

definition "commit_contraction_into Fi E_i Di Ji Ri P_i plen Q_i qlen b base edge used = do {
  forest_contract_into Fi P_i plen Q_i qlen b;
  edge_update_imp E_i b edge;
  base_update_imp Di b base;
  link_update_imp Ji b (nil,0);
  header_update_imp Ri b (used,plen + (qlen-1)) }"

definition "contract_into Fi E_i B_i Ni Ui Oi Qi Ci Di Ji Ri P_i plen Q_i qlen u v b used t = do {
  a \<leftarrow> cycle_read P_i plen Q_i qlen 0;
  base \<leftarrow> base_lookup_imp Di a;
  edge \<leftarrow> edge_lookup_imp E_i a;
  t' \<leftarrow> process_cycle_into Fi E_i B_i Ni Ui Oi Qi Ci P_i plen Q_i qlen u v b used t;
  commit_contraction_into Fi E_i Di Ji Ri P_i plen Q_i qlen b base edge used;
  return t' }"

lemma commit_contraction_into_rule:
  assumes "Forest.contract_fork_precond M F x y p q a b rest contr"
    "a \<in> fset_abstract (forest_evens F)" "b \<in> K"
    "path_invar P" "path_invar Q" "plen \<le> path_cap" "qlen \<le> path_cap"
    "Paths.buffer_view P 0 plen False = p @ [a]" "Paths.buffer_view Q 0 qlen False = q @ [a]"
    "edge_invar E" "base_invar D" "link_invar J" "header_invar R"
  shows "<forest_assn F Fi * path_assn P P_i * path_assn Q Q_i *
    edge_assn E E_i * base_assn D Di * link_assn J Ji * header_assn R Ri>
    commit_contraction_into Fi E_i Di Ji Ri P_i plen Q_i qlen b base edge used
    <\<lambda>_. forest_assn (forest_contract F (p @ [a]) (q @ [a]) b) Fi *
      path_assn P P_i * path_assn Q Q_i * edge_assn (edge_update E b edge) E_i *
      base_assn (base_update D b base) Di * link_assn (link_update J b (nil,0)) Ji *
      header_assn (header_update R b (used,plen + (qlen-1))) Ri>"
  using assms
  unfolding commit_contraction_into_def
  by(sep_auto heap: forest_contract_rule)

lemma path_view_take:
  "k \<le> n \<Longrightarrow> Paths.buffer_view P 0 k False = take k (Paths.buffer_view P 0 n False)"
  by(simp add: Paths.buffer_view_def take_map)

lemma cycle_view_prefixes:
  assumes "Paths.buffer_view P 0 plen False = p @ [a]"
    "Paths.buffer_view Q 0 qlen False = q @ [a]"
  shows "cycle_view P plen Q qlen = rev (p @ [a]) @ q"
proof-
  have "qlen = Suc (length q)"
    using assms(2)
    by (fastforce dest: arg_cong[where f = length])
  with assms show ?thesis
    by (simp add: cycle_view_def Paths.buffer_view_def flip: take_map)
qed
lemma contract_into_rule:
  assumes "Forest.contract_fork_precond M (qbs_forest state) x y p q a b rest contr"
    "a \<in> fset_abstract (forest_evens (qbs_forest state))" "b \<in> K"
    "path_invar P" "path_invar Q" "plen \<le> path_cap" "qlen \<le> path_cap"
    "Paths.buffer_view P 0 plen False = p @ [a]" "Paths.buffer_view Q 0 qlen False = q @ [a]"
    "edge_invar (qbs_forest_edges state)" "cycle_storage_valid state T C"
    "owner_invar (qbs_owners state)" "base_invar (qbs_bases state)" "link_invar (qbs_hints state)"
    "header_invar R" "used + length (cycle_view P plen Q qlen) \<le> pool_cap"
    "t + length (filter (cycle_old_odd state) (cycle_view P plen Q qlen)) \<le> cap"
    "set (cycle_view P plen Q qlen) \<subseteq> K"
  shows "<forest_assn (qbs_forest state) Fi * edge_assn (qbs_forest_edges state) E_i *
    path_assn P P_i * path_assn Q Q_i * cycle_storage state T C Ui B_i Ni Qi Ci *
    owner_assn (qbs_owners state) Oi * base_assn (qbs_bases state) Di *
    link_assn (qbs_hints state) Ji * header_assn R Ri>
    contract_into Fi E_i B_i Ni Ui Oi Qi Ci Di Ji Ri P_i plen Q_i qlen u v b used t
    <\<lambda>t'. \<exists>\<^sub>AT' C'. (let next = process_cycle state (cycle_view P plen Q qlen) plen (u,v) b in
      forest_assn (forest_contract (qbs_forest state) (p @ [a]) (q @ [a]) b) Fi *
      edge_assn (edge_update (qbs_forest_edges state) b (forest_edge state a)) E_i *
      path_assn P P_i * path_assn Q Q_i * cycle_storage next T' C' Ui B_i Ni Qi Ci *
      owner_assn (qbs_owners next) Oi *
      base_assn (base_update (qbs_bases state) b (base_lookup (qbs_bases state) a)) Di *
      link_assn (link_update (qbs_hints state) b (nil,0)) Ji *
      header_assn (header_update R b (used,plen + (qlen-1))) Ri *
      \<up>(cycle_storage_valid next T' C' \<and> owner_invar (qbs_owners next) \<and>
        cycle_buffers state (cycle_view P plen Q qlen) T C used 0 t T' C' t'))>"
proof-
  have forest: "forest_invar M (qbs_forest state)"
    using assms(1)
    by(auto simp: Forest.contract_fork_precond_def)
  have first: "cycle_view P plen Q qlen ! 0 = a" and key: "a \<in> K"
    using cycle_view_prefixes[OF assms(8,9)] assms(18)
    by auto
  have length: "0 < plen + (qlen-1)"
    using cycle_view_prefixes[OF assms(8,9)] cycle_view_length[of P plen Q qlen]
    by(simp only: rev_append list.simps length_append length_Cons length_rev)
  note process = process_cycle_into_rule[OF forest assms(10,4-7,18,3,16,11,12,17), where u=u and v=v]
  note commit = commit_contraction_into_rule[OF assms(1-10,13-15),
    where base="base_lookup (qbs_bases state) a" and edge="forest_edge state a"]
  show ?thesis
    using assms(10,13) key
    unfolding contract_into_def
    by(sep_auto heap: cycle_read_rule[OF assms(4-7) length, simplified first] process commit simp: Let_def)
qed

lemma contract_search_prefixes:
  assumes "Paths.buffer_view P 0 plen False = p @ [a]"
    "Paths.buffer_view Q 0 qlen False = q @ [a]"
    "longest_disj_sfx (rev fullp) (rev fullq) = (rev (p @ [a]), rev (q @ [a]))"
    "fst (queue_pop (qbs_fresh state)) = b"
  shows "contract_search state u v fullp fullq =
    (process_cycle state (cycle_view P plen Q qlen) plen (u,v) b) \<lparr>
      qbs_forest := forest_contract (qbs_forest state) (p @ [a]) (q @ [a]) b,
      qbs_matching := mate_contract (qbs_matching state) (cycle_view P plen Q qlen) b,
      qbs_hierarchy := hierarchy_merge (qbs_hierarchy state) (cycle_view P plen Q qlen) b,
      qbs_component := b,
      qbs_forest_edges := edge_update (qbs_forest_edges state) b (forest_edge state a),
      qbs_bases := base_update (qbs_bases state) b (base_lookup (qbs_bases state) a),
      qbs_hints := link_update (qbs_hints state) b (nil,0),
      qbs_fresh := snd (queue_pop (qbs_fresh state))\<rparr>"
proof-
  have "plen = Suc (length p)"
    using assms(1)
    by (fastforce dest: arg_cong[where f = length])
  with assms show ?thesis
    by (simp add: contract_search_def Let_def case_prod_beta cycle_view_prefixes)
qed

end

section "One workspace for all searches"

locale Cubic_Blossom_In_Place =
  Contraction: Quadratic_Blossom_Search_Contraction_Imperative where K = K
    and forest_assn = forest_assn and uf_assn = uf_assn and owner_assn = owner_assn and edge_assn = edge_assn and frontier_assn = frontier_assn and link_assn = link_assn and base_assn = base_assn and header_assn = header_assn and pool_assn = pool_assn and path_assn = path_assn +
  Initialisation: Quadratic_Blossom_Search_Initialisation_Imperative where K = K
    and forest_assn = forest_assn and owner_assn = owner_assn and base_assn = base_assn and frontier_assn = frontier_assn
  for K :: "'v::heap set"
    and forest_assn :: "_ \<Rightarrow> 'fi \<Rightarrow> assn"
    and uf_assn :: "_ \<Rightarrow> 'ui \<Rightarrow> assn"
    and owner_assn :: "_ \<Rightarrow> 'oi \<Rightarrow> assn"
    and edge_assn :: "_ \<Rightarrow> 'ei \<Rightarrow> assn"
    and frontier_assn :: "_ \<Rightarrow> 'qi \<Rightarrow> assn"
    and link_assn :: "_ \<Rightarrow> 'li \<Rightarrow> assn"
    and base_assn :: "_ \<Rightarrow> 'di \<Rightarrow> assn"
    and header_assn :: "_ \<Rightarrow> 'hi \<Rightarrow> assn"
    and pool_assn :: "_ \<Rightarrow> 'ci \<Rightarrow> assn"
    and path_assn :: "_ \<Rightarrow> 'pi \<Rightarrow> assn" +
  fixes n :: nat
    and get_forest :: "'wi \<Rightarrow> 'fi"
    and get_union_find :: "'wi \<Rightarrow> 'ui"
    and get_owners :: "'wi \<Rightarrow> 'oi"
    and get_forest_edges :: "'wi \<Rightarrow> 'ei"
    and get_cycle_edges :: "'wi \<Rightarrow> 'ei"
    and get_frontier :: "'wi \<Rightarrow> 'qi"
    and get_navigation :: "'wi \<Rightarrow> 'li"
    and get_bases :: "'wi \<Rightarrow> 'di"
    and get_hints :: "'wi \<Rightarrow> 'li"
    and get_headers :: "'wi \<Rightarrow> 'hi"
    and get_pool :: "'wi \<Rightarrow> 'ci"
    and get_left :: "'wi \<Rightarrow> 'pi"
    and get_right :: "'wi \<Rightarrow> 'pi"
    and get_marks :: "'wi \<Rightarrow> 'marks"
    and get_positions :: "'wi \<Rightarrow> 'positions"
    and reset_components_into :: "'ui \<Rightarrow> unit Heap"
    and clear_marks_into :: "'marks \<Rightarrow> unit Heap"
    and forest_paths_into :: "'fi \<Rightarrow> 'marks \<Rightarrow> 'positions \<Rightarrow> 'pi \<Rightarrow> 'pi \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> nat \<Rightarrow> (bool \<times> nat \<times> nat) Heap"
    and recover_path_into :: "'wi \<Rightarrow> 'bi \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat Heap"
    and empty_cursor :: 'iterator
    and row_begin :: "'gi \<Rightarrow> 'v \<Rightarrow> 'iterator Heap"
    and row_has :: "'iterator \<Rightarrow> bool"
    and row_read :: "'gi \<Rightarrow> 'iterator \<Rightarrow> 'v Heap"
    and row_advance :: "'iterator \<Rightarrow> 'iterator"
    and first_fresh :: nat and fresh_vertex :: "nat \<Rightarrow> 'v"
begin
definition "initialise_into (Gi::'gi) Mi Wi = do {
  reset_components_into (get_union_find Wi);
  clear_marks_into (get_marks Wi);
  Initialisation.initial_roots_into Mi (get_forest Wi) (get_owners Wi)
    (get_bases Wi) (get_frontier Wi) n }"

definition "representative_into Wi v = do {
  r \<leftarrow> uf_find_imp (get_union_find Wi) v;
  owner_lookup_imp (get_owners Wi) r }"

definition "extend_search_into Wi x y z u v t =
  Contraction.extend_into (get_forest Wi) (get_forest_edges Wi) (get_frontier Wi) x y z u v t"

definition "query_paths_into Wi tag x y =
  forest_paths_into (get_forest Wi) (get_marks Wi) (get_positions Wi)
    (get_left Wi) (get_right Wi) x y tag"

definition "contract_search_into Wi u v plen qlen b t used =
  Contraction.contract_into (get_forest Wi) (get_forest_edges Wi) (get_cycle_edges Wi)
    (get_navigation Wi) (get_union_find Wi) (get_owners Wi) (get_frontier Wi)
    (get_pool Wi) (get_bases Wi) (get_hints Wi) (get_headers Wi)
    (get_left Wi) plen (get_right Wi) qlen u v b used t"

sublocale Runtime: Quadratic_Blossom_Search_Buffer nil empty_cursor first_fresh fresh_vertex
  initialise_into "\<lambda>Wi. frontier_lookup_imp (get_frontier Wi)" representative_into
  row_begin row_has row_read row_advance "\<lambda>Wi. forest_classify_imp (get_forest Wi)"
  mate_read_imp extend_search_into query_paths_into contract_search_into recover_path_into
  by unfold_locales

definition "matching_into augment_prefix Gi Mi Wi Bi =
  Find_Max_Matching_Buffer.matching_loop Runtime.search_into augment_prefix Gi Mi Wi Bi"


end

section "Bounds for contraction storage and path buffers"

context Quadratic_Blossom_Search_thms
begin

lemma contraction_storage_space:
  assumes "Quadratic_Blossom_Search_call_7_conds state" "invar_search state"
    "longest_disj_sfx (rev (forest_path (qbs_forest state) (source_component state)))
      (rev (forest_path (qbs_forest state) (target_component state))) = (c1,c2)"
    "queue_pop (qbs_fresh state) = (b,fresh)" "frontier_history state xs h"
    "used = (\<Sum>a \<in> hierarchy_ids (qbs_hierarchy state). length (hierarchy_children (qbs_hierarchy state) a))"
    "finite K" "card K \<le> pool_cap"
  shows "used + length (c1 @ butlast (rev c2)) \<le> pool_cap"
    "length xs + length (filter (fset_isin (forest_odds (qbs_forest state))) (c1 @ butlast (rev c2))) \<le> cap"
proof-
  have props: "hierarchy_invar (qbs_hierarchy state)" "recovery_tree (qbs_hierarchy state)"
    "invar_navigation (qbs_hierarchy state) (qbs_bases state) (qbs_parents state)"
    using assms(2)
    by (auto elim!: invar_search_props invar_recovering_structure_props)
  have "(\<Sum>a \<in> hierarchy_ids (qbs_hierarchy state). length (hierarchy_children (qbs_hierarchy state) a)) +
      length (c1 @ butlast (rev c2)) \<le> card (hierarchy_ids (qbs_hierarchy state))"
    by (rule hierarchy_merge_children_space[OF props contraction_hierarchy_precond[OF assms(1-4)]])
  also have "... \<le> card K"
    using assms(2,7)
    by (intro card_mono) (auto elim!: invar_search_props invar_representatives_props)
  also have "... \<le> pool_cap"
    by (rule assms(8))
  finally show "used + length (c1 @ butlast (rev c2)) \<le> pool_cap"
    by (simp only: assms(6))
  show "length xs + length (filter (fset_isin (forest_odds (qbs_forest state))) (c1 @ butlast (rev c2))) \<le> cap"
    using frontier_history_bound[OF frontier_history_contraction[OF assms(1-5)]]
    by simp
qed

definition "fresh_counter state first limit vertex fresh \<longleftrightarrow>
  first \<le> fresh \<and> fresh \<le> limit \<and>
  queue_abstract (qbs_fresh state) = map vertex [fresh..<limit]"

lemma fresh_counter_initial:
  "\<lbrakk>first \<le> limit; queue_abstract fresh0 = map vertex [first..<limit]\<rbrakk> \<Longrightarrow>
    fresh_counter initial_search_state first limit vertex first"
  by (simp add: fresh_counter_def)

lemma fresh_counter_same:
  "\<lbrakk>fresh_counter state first limit vertex fresh;
    queue_abstract (qbs_fresh state') = queue_abstract (qbs_fresh state)\<rbrakk> \<Longrightarrow>
    fresh_counter state' first limit vertex fresh"
  by (simp add: fresh_counter_def)

lemma fresh_counter_pop:
  "\<lbrakk>fresh_counter state first limit vertex fresh; queue_abstract (qbs_fresh state) \<noteq> [];
    queue_abstract (qbs_fresh state') = tl (queue_abstract (qbs_fresh state))\<rbrakk> \<Longrightarrow>
    fresh_counter state' first limit vertex (Suc fresh)"
  by (auto simp: fresh_counter_def map_tl[symmetric])

lemma fresh_counter_contraction:
  assumes "Quadratic_Blossom_Search_call_7_conds state" "invar_search state"
    "fresh_counter state first limit vertex fresh"
  shows "fresh < limit"
    "fst (queue_pop (qbs_fresh state)) = vertex fresh"
    "fresh_counter (Quadratic_Blossom_Search_upd7 state) first limit vertex (Suc fresh)"
proof-
  obtain c1 c2 b Q where parts:
    "longest_disj_sfx (rev (forest_path (qbs_forest state) (source_component state)))
      (rev (forest_path (qbs_forest state) (target_component state))) = (c1,c2)"
    "queue_pop (qbs_fresh state) = (b,Q)"
    by (cases "longest_disj_sfx (rev (forest_path (qbs_forest state) (source_component state)))
      (rev (forest_path (qbs_forest state) (target_component state)))"; cases "queue_pop (qbs_fresh state)") auto
  have nonempty: "queue_abstract (qbs_fresh state) \<noteq> []"
    by (rule contraction_fresh_nonempty[OF assms(1,2) parts])
  show bound: "fresh < limit"
    using assms(3) nonempty
    by (auto simp: fresh_counter_def)
  have "queue_invar (qbs_fresh state)"
    using assms(2)
    by (auto elim!: invar_search_props invar_adts_props)
  thus "fst (queue_pop (qbs_fresh state)) = vertex fresh"
    using Work.queue_pop(2)[of "qbs_fresh state"] nonempty assms(3) bound
    by (auto simp: fresh_counter_def upt_conv_Cons)
  have "queue_abstract (qbs_fresh (Quadratic_Blossom_Search_upd7 state)) = tl (queue_abstract (qbs_fresh state))"
    using contraction_fresh(3)[OF assms(1,2) parts] contraction_selectors(5)[OF assms(1,2) parts]
    by simp
  thus "fresh_counter (Quadratic_Blossom_Search_upd7 state) first limit vertex (Suc fresh)"
    by (rule fresh_counter_pop[OF assms(3) nonempty])
qed

lemma search_forest_path_length:
  assumes "invar_search state" "x \<in> even_ids state"
  shows "length (forest_path (qbs_forest state) x) \<le> length vs"
proof-
  have forest: "forest_invar (mate_abstract (qbs_matching state)) (qbs_forest state)"
    "even_ids state \<union> odd_ids state \<subseteq> active_ids state"
    using assms(1)
    by (auto elim!: invar_search_props invar_forest_props)
  have hierarchy: "hierarchy_invar (qbs_hierarchy state)" "finite (hierarchy_ids (qbs_hierarchy state))"
    using assms(1)
    by (auto simp: recovery_tree_def elim!: invar_search_props invar_recovering_structure_props)
  have "length (forest_path (qbs_forest state) x) = card (set (forest_path (qbs_forest state) x))"
    by (simp only: distinct_card[OF Forest.get_path_distinct[OF forest(1)]])
  also have "... \<le> card (active_ids state)"
    by (rule card_mono[OF finite_subset[OF active_ids_subset[OF hierarchy(1)] hierarchy(2)]])
      (use forest_path_vertices[OF forest(1) assms(2)] forest(2) in auto)
  also have "... \<le> length vs"
    using assms(1)
    by (auto simp: invar_hierarchy_size_def elim!: invar_search_props)
  finally show ?thesis .
qed

end

context Quadratic_Blossom_Search_Packed_Hierarchy
begin

lemma packed_hierarchy_merge_buffer:
  assumes "packed_hierarchy H R P used" "pool_invar P'"
    "Pool.buffer_view P' 0 (used + length cs) False = Pool.buffer_view P 0 used False @ cs"
    "Hierarchy.blossom_forest_merge_precond H cs b" "b \<in> K" "used + length cs \<le> capacity"
  shows "packed_hierarchy (hierarchy_merge H cs b)
    (header_update R b (used,length cs)) P' (used + length cs)"
  using assms packed_hierarchy_pool Pool.appended_view
  by (blast intro: packed_hierarchy_commit)
end
section "Relating the retained workspace to the search state"

locale Cubic_Blossom_Refinement =
  Cubic_Blossom_In_Place where K = K
    and row_begin = row_begin and get_marks = get_marks and get_positions = get_positions
    and recover_path_into = recover_path_into and cursor_invar = cursor_invar +
  Search: Quadratic_Blossom_Search_thms where K = K
    and cursor_invar = cursor_invar and output_invar = output_invar
    and task_invar = "\<lambda>xs. length xs \<le> task_cap" and task_abstract = id and task_empty = "[]"
    and task_push = "\<lambda>xs x. x # xs" and task_pop = tl and task_top = hd and task_is_empty = "\<lambda>xs. xs = []" +
  Packed: Quadratic_Blossom_Search_Packed_Hierarchy
    where K = K and capacity = pool_cap
      and hierarchy_invar = hierarchy_invar and hierarchy_ids = hierarchy_ids
      and hierarchy_merge = hierarchy_merge and hierarchy_children = hierarchy_children
      and max_ids = hierarchy_tops and universe = hierarchy_universe
      and collect_elems = hierarchy_members and laminar_abstract = hierarchy_abstract
      and compound = hierarchy_compound and blossom_edges = hierarchy_edges +
  Slots: fixed_univ_map_imp "{..<task_cap}" slot_invar slot_update slot_lookup id
    slot_assn slot_update_imp slot_lookup_imp +
  Output_Imp: fixed_univ_map_imp "{..<output_cap}" output_invar output_update output_lookup id
    output_assn output_update_imp output_lookup_imp
  for K :: "'v::heap set"
    and row_begin :: "'gi \<Rightarrow> 'v \<Rightarrow> 'iterator Heap"
    and get_marks :: "'wi \<Rightarrow> 'marks" and get_positions :: "'wi \<Rightarrow> 'positions"
    and recover_path_into :: "'wi \<Rightarrow> 'bi \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat Heap"
    and cursor_invar :: "'cursor \<Rightarrow> bool" and output_invar :: "'output \<Rightarrow> bool"
    and slot_invar :: "'slots \<Rightarrow> bool"
    and slot_update :: "'slots \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<times> nat \<times> nat \<times> bool \<times> 'v \<times> 'v) \<Rightarrow> 'slots"
    and slot_lookup :: "'slots \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<times> nat \<times> nat \<times> bool \<times> 'v \<times> 'v)"
    and slot_assn :: "'slots \<Rightarrow> 'ti \<Rightarrow> assn"
    and slot_update_imp :: "'ti \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<times> nat \<times> nat \<times> bool \<times> 'v \<times> 'v) \<Rightarrow> unit Heap"
    and slot_lookup_imp :: "'ti \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<times> nat \<times> nat \<times> bool \<times> 'v \<times> 'v) Heap"
    and output_assn :: "'output \<Rightarrow> 'bi \<Rightarrow> assn"
    and output_update_imp :: "'bi \<Rightarrow> nat \<Rightarrow> 'v \<Rightarrow> unit Heap"
    and output_lookup_imp :: "'bi \<Rightarrow> nat \<Rightarrow> 'v Heap" +
  fixes graph_storage :: "'gi \<Rightarrow> assn"
    and marks_assn :: "nat \<Rightarrow> 'marks \<Rightarrow> 'positions \<Rightarrow> assn"
    and get_tasks :: "'wi \<Rightarrow> 'ti"
    and cursor_register :: "'cursor \<Rightarrow> 'v \<Rightarrow> 'iterator \<Rightarrow> bool"
    and fresh_limit :: nat
begin

definition "task_storage Wi = (\<exists>\<^sub>AF. slot_assn F (get_tasks Wi) * \<up>(slot_invar F))"

definition "registers state it h t fresh used \<longleftrightarrow>
  queue_invar (qbs_queue state) \<and> h \<le> t \<and> t \<le> cap \<and>
  length (queue_abstract (qbs_queue state)) = t-h \<and>
  (qbs_current state \<noteq> nil \<longrightarrow> cursor_register (qbs_neighbours state) (qbs_current state) it) \<and>
  first_fresh \<le> fresh \<and> fresh \<le> fresh_limit \<and>
  queue_abstract (qbs_fresh state) = map fresh_vertex [fresh..<fresh_limit] \<and>
  used = (\<Sum>b\<in>hierarchy_ids (qbs_hierarchy state). length (hierarchy_children (qbs_hierarchy state) b))"

definition "state_storage state Wi =
  forest_assn (qbs_forest state) (get_forest Wi) *
  uf_assn (qbs_components state) (get_union_find Wi) *
  owner_assn (qbs_owners state) (get_owners Wi) *
  edge_assn (qbs_forest_edges state) (get_forest_edges Wi) *
  edge_assn (qbs_cycle_edges state) (get_cycle_edges Wi) *
  link_assn (qbs_parents state) (get_navigation Wi) *
  base_assn (qbs_bases state) (get_bases Wi) * link_assn (qbs_hints state) (get_hints Wi)"

definition "buffer_storage state h t used Wi =
  (\<exists>\<^sub>AT R C. frontier_assn T (get_frontier Wi) * header_assn R (get_headers Wi) *
    pool_assn C (get_pool Wi) * \<up>(frontier_invar T \<and>
      Search.frontier_history state (Contraction.Frontier.buffer_view T 0 t False) h \<and>
      Packed.packed_hierarchy (qbs_hierarchy state) R C used))"

definition "query_storage tag Wi = (\<exists>\<^sub>AP Q.
  path_assn P (get_left Wi) * path_assn Q (get_right Wi) *
  marks_assn tag (get_marks Wi) (get_positions Wi) * \<up>(path_invar P \<and> path_invar Q))"

definition "workspace_assn state it h t fresh used Gi Mi Wi Bi =
  graph_storage Gi * matching_assn M0 Mi * task_storage Wi * output_assn out0 Bi *
  state_storage state Wi * buffer_storage state h t used Wi *
  query_storage (Suc (fresh-first_fresh)) Wi"

lemma register_queue:
  "registers state it h t fresh used \<Longrightarrow> queue_is_empty (qbs_queue state) = (h=t)"
  by(auto simp: registers_def Contraction.Work.queue_is_empty)

lemma frontier_head:
  "\<lbrakk>Search.frontier_history state (Contraction.Frontier.buffer_view T 0 t False) h; h<t\<rbrakk> \<Longrightarrow>
    frontier_lookup T h = hd (queue_abstract (qbs_queue state))"
  by(auto simp: Search.frontier_history_def hd_drop_conv_nth Contraction.Frontier.view_nth)

lemma frontier_read_rule:
  assumes "Contraction.Quadratic_Blossom_Search_call_2_conds state" "registers state it h t fresh used"
  shows "<workspace_assn state it h t fresh used Gi Mi Wi Bi>
    frontier_lookup_imp (get_frontier Wi) h
    <\<lambda>v. workspace_assn state it h t fresh used Gi Mi Wi Bi *
      \<up>(v = hd (queue_abstract (qbs_queue state)))>"
proof-
  have "h < t" "t \<le> cap"
    using assms register_queue[OF assms(2)]
    by(auto simp: Contraction.Quadratic_Blossom_Search_call_2_conds_def registers_def)
  thus ?thesis
    unfolding workspace_assn_def buffer_storage_def
    by(sep_auto simp: frontier_head)
qed


lemma classify_rule:
  assumes "Search.invar_search state" "v\<in>K"
  shows "<workspace_assn state it h t fresh used Gi Mi Wi Bi> forest_classify_imp (get_forest Wi) v
    <\<lambda>label. workspace_assn state it h t fresh used Gi Mi Wi Bi *
      \<up>(label = (if fset_isin (forest_odds (qbs_forest state)) v then 1
        else if fset_isin (forest_evens (qbs_forest state)) v then 2 else 0))>"
using assms
  unfolding workspace_assn_def state_storage_def
  by(sep_auto heap: Contraction.forest_classify_rule[where M = "mate_abstract (qbs_matching state)"]
    elim': Search.invar_search_props Contraction.invar_forest_props)
lemma mate_read_rule:
  "v\<in>V0 \<Longrightarrow> <workspace_assn state it h t fresh used Gi Mi Wi Bi> mate_read_imp Mi v
    <\<lambda>z. workspace_assn state it h t fresh used Gi Mi Wi Bi * \<up>(z = mate_partner M0 v)>"
  unfolding workspace_assn_def
  by(sep_auto heap: Initialisation.mate_read_rule)

lemma storage_finished[simp]:
  "state_storage (Contraction.Quadratic_Blossom_Search_upd1 state) Wi = state_storage state Wi"
  "state_storage (Contraction.Quadratic_Blossom_Search_upd3 state) Wi = state_storage state Wi"
  by(simp_all add: state_storage_def Contraction.Quadratic_Blossom_Search_upd1_def
    Contraction.Quadratic_Blossom_Search_upd3_def)

lemma registers_row_finished:
  "registers state it h t fresh used \<Longrightarrow>
    registers (Contraction.Quadratic_Blossom_Search_upd3 state) it h t fresh used"
  by(simp add: registers_def Contraction.Quadratic_Blossom_Search_upd3_def)

lemma row_finished_entails:
  "workspace_assn state it h t fresh used Gi Mi Wi Bi \<Longrightarrow>\<^sub>A
    workspace_assn (Contraction.Quadratic_Blossom_Search_upd3 state) it h t fresh used Gi Mi Wi Bi"
  by(simp add: workspace_assn_def buffer_storage_def state_storage_def Search.frontier_history_def
    Contraction.effectively_even_def Contraction.Quadratic_Blossom_Search_upd3_def)

lemma row_finished_refine:
  "registers state it h t fresh used \<Longrightarrow> workspace_assn state it h t fresh used Gi Mi Wi Bi \<Longrightarrow>\<^sub>A
    workspace_assn (Contraction.Quadratic_Blossom_Search_upd3 state) it h t fresh used Gi Mi Wi Bi *
      \<up>(registers (Contraction.Quadratic_Blossom_Search_upd3 state) it h t fresh used)"
  by (simp add: registers_row_finished row_finished_entails)

text "A path query either reports the two prefixes up to their common base or two complete
  paths from different trees. The search only needs that observation."

definition "paths_result F x y r P Q \<longleftrightarrow> (case r of (shared, plen, qlen) \<Rightarrow>
  path_invar P \<and> path_invar Q \<and> plen \<le> path_cap \<and> qlen \<le> path_cap \<and>
  shared = (last (forest_path F x) = last (forest_path F y)) \<and>
  (if shared then longest_disj_sfx (rev (forest_path F x)) (rev (forest_path F y)) =
      (rev (Contraction.Paths.buffer_view P 0 plen False), rev (Contraction.Paths.buffer_view Q 0 qlen False))
   else Contraction.Paths.buffer_view P 0 plen False = forest_path F x \<and>
     Contraction.Paths.buffer_view Q 0 qlen False = forest_path F y))"

definition "search_paths_assn state it h t fresh used plen qlen Gi Mi Wi Bi =
  graph_storage Gi * matching_assn M0 Mi * task_storage Wi * output_assn out0 Bi *
  state_storage state Wi * buffer_storage state h t used Wi *
  (\<exists>\<^sub>AP Q. path_assn P (get_left Wi) * path_assn Q (get_right Wi) *
    marks_assn (Suc (Suc (fresh - first_fresh))) (get_marks Wi) (get_positions Wi) *
    \<up>(paths_result (qbs_forest state) (qbs_component state) (Contraction.target_component state)
      (last (forest_path (qbs_forest state) (qbs_component state)) =
        last (forest_path (qbs_forest state) (Contraction.target_component state)), plen, qlen) P Q))"
text "The graph is read through scalar row iterators. Only the row of the scanned vertex has a
  register; every other cursor of the search is a proof-only observation."

end

locale Cubic_Blossom_Rows = Cubic_Blossom_Refinement +
  assumes find_read_only: "\<And>U v. \<lbrakk>uf_invar U; v\<in>K\<rbrakk> \<Longrightarrow> snd (uf_find U v) = U"
    and graph_row_begin_rule: "\<And>C v Gi. \<lbrakk>cursor_invar C; v \<in> V0; cursor_iterated C v = {}\<rbrakk> \<Longrightarrow>
      <graph_storage Gi> row_begin Gi v <\<lambda>it. graph_storage Gi * \<up>(cursor_register C v it)>"
    and graph_row_read_rule: "\<And>C v it Gi. \<lbrakk>cursor_invar C; v \<in> V0; cursor_register C v it; cursor_has C v\<rbrakk> \<Longrightarrow>
      <graph_storage Gi> row_read Gi it <\<lambda>x. graph_storage Gi * \<up>(x = cursor_current C v)>"
    and row_has_register: "\<And>C v it. cursor_register C v it \<Longrightarrow> row_has it = cursor_has C v"
    and row_advance_register: "\<And>C v it. \<lbrakk>cursor_invar C; v \<in> V0; cursor_register C v it; cursor_has C v\<rbrakk> \<Longrightarrow>
      cursor_register (cursor_move C v) v (row_advance it)"
begin

lemma representative_rule:
  assumes "Search.invar_search state" "v\<in>V0"
  shows "<workspace_assn state it h t fresh used Gi Mi Wi Bi> representative_into Wi v
    <\<lambda>x. workspace_assn state it h t fresh used Gi Mi Wi Bi * \<up>(x = Contraction.representative state v)>"
proof-
  have valid: "uf_invar (qbs_components state)" "owner_invar (qbs_owners state)" "v\<in>K"
    using assms
    by(auto elim!: Search.invar_search_props Contraction.invar_adts_props)
  note read = Contraction.uf_find_rule[OF valid(1,3), simplified find_read_only[OF valid(1,3)] Contraction.Components.find_result[OF valid(1,3)]]
  from valid show ?thesis
    unfolding workspace_assn_def state_storage_def representative_into_def
    by(sep_auto heap: read simp: find_read_only Contraction.Components.find_result
      Contraction.Components.representative_closed)
qed

lemma register_cursor_refine:
  "\<lbrakk>registers state it h t fresh used; qbs_current state \<noteq> nil\<rbrakk> \<Longrightarrow>
    row_has it = cursor_has (qbs_neighbours state) (qbs_current state)"
  by (auto simp: registers_def row_has_register)

lemma start_scan_components:
  assumes "Contraction.Quadratic_Blossom_Search_call_2_conds state" "Search.invar_search state"
  shows "qbs_components (Contraction.Quadratic_Blossom_Search_upd2 state) = qbs_components state"
using assms Search.start_scan_source[of state] Search.input_vertex_in_universe
  by (auto elim!: Search.invar_search_props
    simp: Contraction.invar_adts_def Contraction.Quadratic_Blossom_Search_upd2_def
      Contraction.start_scan_def case_prod_beta find_read_only Contraction.Work.queue_pop)
lemma start_scan_storage:
  assumes "Contraction.Quadratic_Blossom_Search_call_2_conds state" "Search.invar_search state"
  shows "workspace_assn state it h t fresh used Gi Mi Wi Bi \<Longrightarrow>\<^sub>A
    workspace_assn (Contraction.Quadratic_Blossom_Search_upd2 state) it' (Suc h) t fresh used Gi Mi Wi Bi"
  using Search.frontier_history_start_scan[OF assms]
  by (sep_auto simp: workspace_assn_def buffer_storage_def state_storage_def start_scan_components[OF assms])

lemma start_scan_registers:
  assumes "Contraction.Quadratic_Blossom_Search_call_2_conds state" "Search.invar_search state"
    "registers state it h t fresh used"
    "cursor_register (qbs_neighbours state) (hd (queue_abstract (qbs_queue state))) row"
  shows "registers (Contraction.Quadratic_Blossom_Search_upd2 state) row (Suc h) t fresh used"
proof-
  have "Contraction.invar_adts state" "Contraction.invar_queue state"
    using assms(2)
    by (auto elim!: Search.invar_search_props)
  note source = Search.start_scan_source[OF assms(1) this]
  have "Suc h \<le> t"
    using source assms(3)
    by (cases "queue_abstract (qbs_queue state)") (auto simp: registers_def)
  thus ?thesis
    using assms(3,4) source Search.start_scan_props[OF assms(1)]
    by (auto simp: registers_def Contraction.Quadratic_Blossom_Search_upd2_def Contraction.start_scan_def
      case_prod_beta Contraction.Work.queue_pop)
qed

lemma row_begin_refine:
  assumes "Contraction.Quadratic_Blossom_Search_call_2_conds state" "Search.invar_search state"
    "registers state it h t fresh used"
  shows "<workspace_assn state it h t fresh used Gi Mi Wi Bi>
    row_begin Gi (hd (queue_abstract (qbs_queue state)))
    <\<lambda>row. workspace_assn (Contraction.Quadratic_Blossom_Search_upd2 state) row (Suc h) t fresh used Gi Mi Wi Bi *
      \<up>(registers (Contraction.Quadratic_Blossom_Search_upd2 state) row (Suc h) t fresh used)>"
proof-
  have invars: "Contraction.invar_adts state" "Contraction.invar_queue state"
    using assms(2)
    by (auto elim!: Search.invar_search_props)
  note source = Search.start_scan_source[OF assms(1) invars]
  have row: "cursor_invar (qbs_neighbours state)"
    "cursor_iterated (qbs_neighbours state) (hd (queue_abstract (qbs_queue state))) = {}"
    using invars source
    by (auto elim!: Contraction.invar_adts_props Contraction.invar_queue_props)
  have "<workspace_assn state it h t fresh used Gi Mi Wi Bi>
    row_begin Gi (hd (queue_abstract (qbs_queue state)))
    <\<lambda>row. workspace_assn state it h t fresh used Gi Mi Wi Bi *
      \<up>(cursor_register (qbs_neighbours state) (hd (queue_abstract (qbs_queue state))) row)>"
    unfolding workspace_assn_def
    by (sep_auto heap: graph_row_begin_rule[OF row(1) conjunct1[OF conjunct2[OF source]] row(2)])
  thus ?thesis
    by (rule ht_cons_post_prec)
      (sep_auto intro: start_scan_registers[OF assms] start_scan_storage[OF assms(1,2)])
qed

lemma row_read_refine:
  assumes "Contraction.scanning_edge state" "Search.invar_search state" "registers state it h t fresh used"
  shows "<workspace_assn state it h t fresh used Gi Mi Wi Bi> row_read Gi it
    <\<lambda>v. workspace_assn state it h t fresh used Gi Mi Wi Bi * \<up>(v = Contraction.scanned_neighbour state)>"
proof-
  have "cursor_invar (qbs_neighbours state)" "qbs_current state \<in> V0"
    using assms(1,2) Search.scanning_cursor
    by (auto elim!: Search.invar_search_props)
  with assms(1,3) show ?thesis
    unfolding workspace_assn_def
    by (sep_auto heap: graph_row_read_rule[where C = "qbs_neighbours state"]
      simp: registers_def Contraction.scanning_edge_def)
qed
lemma scan_components:
  assumes "Contraction.scanning_edge state" "Search.invar_search state"
  shows "qbs_components (Contraction.Quadratic_Blossom_Search_upd4 state) = qbs_components state"
using assms Search.scanning_neighbour[of state] Search.input_vertex_in_universe
  by (auto elim!: Search.invar_search_props simp: Contraction.invar_adts_def
    Contraction.Quadratic_Blossom_Search_upd4_def Contraction.resolve_target_def
    case_prod_beta find_read_only)
lemma scan_storage:
  assumes "Contraction.scanning_edge state" "Search.invar_search state"
  shows "workspace_assn state it h t fresh used Gi Mi Wi Bi \<Longrightarrow>\<^sub>A
    workspace_assn (Contraction.Quadratic_Blossom_Search_upd4 state) it' h t fresh used Gi Mi Wi Bi"
  using Search.frontier_history_stable(3)[OF assms]
    scan_components[OF assms, unfolded Contraction.Quadratic_Blossom_Search_upd4_def, simplified]
  by (sep_auto simp: workspace_assn_def buffer_storage_def state_storage_def
    Contraction.Quadratic_Blossom_Search_upd4_def)

lemma scan_registers:
  assumes "Contraction.scanning_edge state" "Search.invar_search state" "registers state it h t fresh used"
  shows "registers (Contraction.Quadratic_Blossom_Search_upd4 state) (row_advance it) h t fresh used"
proof-
  have "cursor_invar (qbs_neighbours state)" "qbs_current state \<in> V0"
    using assms(1,2) Search.scanning_cursor
    by (auto elim!: Search.invar_search_props)
  with assms(1,3) show ?thesis
    by (auto simp: registers_def Contraction.scanning_edge_def
      Contraction.Quadratic_Blossom_Search_upd4_def intro: row_advance_register)
qed
lemma skipped_edge_refine:
  assumes "Contraction.Quadratic_Blossom_Search_call_4_conds state" "Search.invar_search state"
    "registers state it h t fresh used"
  shows "workspace_assn state it h t fresh used Gi Mi Wi Bi \<Longrightarrow>\<^sub>A
    workspace_assn (Contraction.Quadratic_Blossom_Search_upd4 state) (row_advance it) h t fresh used Gi Mi Wi Bi *
      \<up>(registers (Contraction.Quadratic_Blossom_Search_upd4 state) (row_advance it) h t fresh used)"
using assms
  by (auto simp: Contraction.Quadratic_Blossom_Search_call_4_conds_def
    intro: scan_registers scan_storage)
lemma extension_registers:
  assumes "Contraction.Quadratic_Blossom_Search_call_5_conds state" "Search.invar_search state"
    "registers state it h t fresh used" "Suc t \<le> cap"
  shows "registers (Contraction.Quadratic_Blossom_Search_upd5 state) (row_advance it) h (Suc t) fresh used"
using assms scan_registers[of state it h t fresh used]
  by (auto simp: registers_def Contraction.Quadratic_Blossom_Search_call_5_conds_def
    Contraction.Quadratic_Blossom_Search_upd5_def Contraction.extend_search_def
    Contraction.enqueue_vertex_def Contraction.Quadratic_Blossom_Search_upd4_def
    Let_def Contraction.Work.queue_push elim!: Search.invar_search_props Contraction.invar_adts_props)
lemma extension_capacity:
  assumes "Contraction.Quadratic_Blossom_Search_call_5_conds state" "Search.invar_search state"
    "Search.frontier_history state (Contraction.Frontier.buffer_view T 0 t False) h"
  shows "t < cap"
  using assms Search.frontier_history_bound Search.frontier_history_extension
  by (fastforce simp: Contraction.Frontier.buffer_view_def)
lemma extend_refine:
  assumes "Contraction.Quadratic_Blossom_Search_call_5_conds state" "Search.invar_search state"
    "registers state it h t fresh used"
  shows "<workspace_assn state it h t fresh used Gi Mi Wi Bi>
    extend_search_into Wi (Contraction.source_component state) (Contraction.target_component state)
      (mate_partner (qbs_matching state) (Contraction.target_component state))
      (Contraction.scanned_vertex state) (Contraction.scanned_neighbour state) t
    <\<lambda>_. workspace_assn (Contraction.Quadratic_Blossom_Search_upd5 state) (row_advance it) h (Suc t) fresh used Gi Mi Wi Bi *
      \<up>(registers (Contraction.Quadratic_Blossom_Search_upd5 state) (row_advance it) h (Suc t) fresh used)>"
proof-
  let ?y = "Contraction.target_component state"
    and ?z = "mate_partner (qbs_matching state) (Contraction.target_component state)"
  have scan: "Contraction.scanning_edge state"
    using assms(1)
    by (simp add: Contraction.Quadratic_Blossom_Search_call_5_conds_def)
  have invars: "Contraction.invar_adts state" "Contraction.invar_queue state" "Contraction.invar_neighbours state"
    using assms(2)
    by (auto elim!: Search.invar_search_props)
  have keys: "?y \<in> K" "?z \<in> K" "edge_invar (qbs_forest_edges state)"
    using Search.extension_original_vertices(1,2)[OF assms(1,2)] Search.scanning_neighbour(1)[OF scan invars]
      Search.input_vertex_in_universe invars(1)
    by (auto elim!: Contraction.invar_adts_props)
  have storage: "state_storage (Contraction.Quadratic_Blossom_Search_upd5 state) Wi =
      forest_assn (forest_extend (qbs_forest state) (qbs_component state) ?y ?z) (get_forest Wi) *
      uf_assn (qbs_components state) (get_union_find Wi) *
      owner_assn (qbs_owners state) (get_owners Wi) *
      edge_assn (edge_update (edge_update (qbs_forest_edges state) ?y
        (Contraction.scanned_neighbour state, qbs_current state)) ?z (?z, ?y)) (get_forest_edges Wi) *
      edge_assn (qbs_cycle_edges state) (get_cycle_edges Wi) *
      link_assn (qbs_parents state) (get_navigation Wi) *
      base_assn (qbs_bases state) (get_bases Wi) * link_assn (qbs_hints state) (get_hints Wi)"
    and same: "qbs_hierarchy (Contraction.Quadratic_Blossom_Search_upd5 state) = qbs_hierarchy state"
    using scan_components[OF scan assms(2)]
    by (simp_all add: Contraction.Quadratic_Blossom_Search_upd5_def Contraction.extend_search_def
      Contraction.enqueue_vertex_def Let_def state_storage_def,
      simp_all add: Contraction.Quadratic_Blossom_Search_upd4_def)
  note rule = Contraction.extend_into_rule[OF Search.extension_precond[OF assms(1,2)] keys(3,1,2)]
  have frontier: "frontier_invar (frontier_update T t ?z) \<and>
      Search.frontier_history (Contraction.Quadratic_Blossom_Search_upd5 state)
        (Contraction.Frontier.buffer_view (frontier_update T t ?z) 0 (Suc t) False) h"
    if "frontier_invar T" "Search.frontier_history state (Contraction.Frontier.buffer_view T 0 t False) h" for T
    using that extension_capacity[OF assms(1,2) that(2)] Search.frontier_history_extension[OF assms(1,2) that(2)]
    by (simp add: Contraction.Frontier.append_prefix Contraction.Frontier.Buffer.fixed_univ_map_upd_invar)
  have buffers: "frontier_assn (frontier_update T t ?z) (get_frontier Wi) * header_assn R (get_headers Wi) *
      pool_assn C (get_pool Wi) \<Longrightarrow>\<^sub>A buffer_storage (Contraction.Quadratic_Blossom_Search_upd5 state) h (Suc t) used Wi"
    if "frontier_invar T" "Search.frontier_history state (Contraction.Frontier.buffer_view T 0 t False) h"
      "Packed.packed_hierarchy (qbs_hierarchy state) R C used" for T R C
    unfolding buffer_storage_def same
    by (rule ent_ex_postI[where x = "frontier_update T t ?z"], rule ent_ex_postI[where x = R],
      rule ent_ex_postI[where x = C]) (sep_auto simp: frontier[OF that(1,2)] that(3))
  have triple: "<workspace_assn state it h t fresh used Gi Mi Wi Bi>
    extend_search_into Wi (qbs_component state) ?y ?z (qbs_current state) (Contraction.scanned_neighbour state) t
    <\<lambda>_. \<exists>\<^sub>AT R C. graph_storage Gi * matching_assn M0 Mi * task_storage Wi * output_assn out0 Bi *
      state_storage (Contraction.Quadratic_Blossom_Search_upd5 state) Wi *
      (frontier_assn (frontier_update T t ?z) (get_frontier Wi) * header_assn R (get_headers Wi) *
        pool_assn C (get_pool Wi)) *
      query_storage (Suc (fresh - first_fresh)) Wi *
      \<up>(frontier_invar T \<and> Search.frontier_history state (Contraction.Frontier.buffer_view T 0 t False) h \<and>
        Packed.packed_hierarchy (qbs_hierarchy state) R C used \<and> t < cap)>"
    unfolding workspace_assn_def buffer_storage_def storage extend_search_into_def
    unfolding state_storage_def
    by (sep_auto heap: rule dest: extension_capacity[OF assms(1,2)])
  show ?thesis
  proof(rule ht_cons_post_prec[OF triple], intro ent_ex_preI)
    fix x T R C
    show "graph_storage Gi * matching_assn M0 Mi * task_storage Wi * output_assn out0 Bi *
      state_storage (Contraction.Quadratic_Blossom_Search_upd5 state) Wi *
      (frontier_assn (frontier_update T t ?z) (get_frontier Wi) * header_assn R (get_headers Wi) *
        pool_assn C (get_pool Wi)) *
      query_storage (Suc (fresh - first_fresh)) Wi *
      \<up>(frontier_invar T \<and> Search.frontier_history state (Contraction.Frontier.buffer_view T 0 t False) h \<and>
        Packed.packed_hierarchy (qbs_hierarchy state) R C used \<and> t < cap) \<Longrightarrow>\<^sub>A
      workspace_assn (Contraction.Quadratic_Blossom_Search_upd5 state) (row_advance it) h (Suc t) fresh used Gi Mi Wi Bi *
      \<up>(registers (Contraction.Quadratic_Blossom_Search_upd5 state) (row_advance it) h (Suc t) fresh used)"
      unfolding workspace_assn_def
      by (auto simp: extension_registers[OF assms] mod_pure_star_dist
        intro!: ent_star_mono[OF ent_star_mono[OF ent_refl buffers] ent_refl])
  qed
qed


end

locale Cubic_Blossom_Paths = Cubic_Blossom_Rows +
  assumes forest_paths_rule: "\<And>M F Fi Ai Ii P Q Pi Qi x y tag.
      \<lbrakk>forest_invar M F; x \<in> fset_abstract (forest_evens F); y \<in> fset_abstract (forest_evens F);
        length (forest_path F x) \<le> path_cap; length (forest_path F y) \<le> path_cap; path_invar P; path_invar Q\<rbrakk> \<Longrightarrow>
      <forest_assn F Fi * marks_assn tag Ai Ii * path_assn P Pi * path_assn Q Qi>
        forest_paths_into Fi Ai Ii Pi Qi x y tag
      <\<lambda>r. forest_assn F Fi * marks_assn (Suc tag) Ai Ii *
        (\<exists>\<^sub>AP' Q'. path_assn P' Pi * path_assn Q' Qi * \<up>(paths_result F x y r P' Q'))>"
    and path_capacity: "length vs \<le> path_cap"
begin

lemma paths_refine:
  assumes "Contraction.Quadratic_Blossom_Search_call_6_conds state \<or> Contraction.Quadratic_Blossom_Search_call_7_conds state"
    "Search.invar_search state" "registers state it h t fresh used"
  shows "<workspace_assn state it h t fresh used Gi Mi Wi Bi>
    query_paths_into Wi (Suc (fresh - first_fresh)) (Contraction.source_component state) (Contraction.target_component state)
    <\<lambda>r. search_paths_assn state it h t fresh used (fst (snd r)) (snd (snd r)) Gi Mi Wi Bi *
      \<up>(fst r = (last (forest_path (qbs_forest state) (Contraction.source_component state)) =
        last (forest_path (qbs_forest state) (Contraction.target_component state))))>"
proof-
  have invars: "Contraction.invar_forest state" "Contraction.invar_queue state" "Contraction.invar_current state"
    "forest_invar (mate_abstract (qbs_matching state)) (qbs_forest state)"
    using assms(2)
    by (auto elim!: Search.invar_search_props Contraction.invar_forest_props)
  note even = Search.scanning_path_components[OF assms(1) invars(1-3)]
  note rule = forest_paths_rule[OF invars(4) even
    order_trans[OF Search.search_forest_path_length[OF assms(2) even(1)] path_capacity]
    order_trans[OF Search.search_forest_path_length[OF assms(2) even(2)] path_capacity]]
  show ?thesis
    unfolding workspace_assn_def search_paths_assn_def state_storage_def query_storage_def query_paths_into_def
    by (sep_auto heap: rule simp: paths_result_def)
qed

context
  assumes key_bounds: "finite K" "card K \<le> pool_cap"
begin

lemma contraction_paths:
  assumes "Contraction.Quadratic_Blossom_Search_call_7_conds state"
    "paths_result (qbs_forest state) (qbs_component state) (Contraction.target_component state)
      (last (forest_path (qbs_forest state) (qbs_component state)) =
        last (forest_path (qbs_forest state) (Contraction.target_component state)), plen, qlen) P Q"
  shows "longest_disj_sfx (rev (forest_path (qbs_forest state) (qbs_component state)))
      (rev (forest_path (qbs_forest state) (Contraction.target_component state))) =
    (rev (Contraction.Paths.buffer_view P 0 plen False), rev (Contraction.Paths.buffer_view Q 0 qlen False))"
    "path_invar P" "path_invar Q" "plen \<le> path_cap" "qlen \<le> path_cap"
  using assms
  by (auto simp: paths_result_def Contraction.Quadratic_Blossom_Search_call_7_conds_def)

text "The premises of the contraction operation at a contracting step of the search."

lemma contraction_inputs:
  assumes  "Contraction.Quadratic_Blossom_Search_call_7_conds state" and  "Search.invar_search state"
    and  "registers state it h t fresh used"
    and  "paths_result (qbs_forest state) (qbs_component state) (Contraction.target_component state)
      (last (forest_path (qbs_forest state) (qbs_component state)) =
        last (forest_path (qbs_forest state) (Contraction.target_component state)), plen, qlen) P Q"
    and  "frontier_invar T" "Search.frontier_history state (Contraction.Frontier.buffer_view T 0 t False) h"
      "Packed.packed_hierarchy (qbs_hierarchy state) R C used"
  defines "s4 == Contraction.Quadratic_Blossom_Search_upd4 state"
    and "Pv == Contraction.Paths.buffer_view P 0 plen False" and "Qv == Contraction.Paths.buffer_view Q 0 qlen False"
    and "cs == Contraction.cycle_view P plen Q qlen"
  shows "Contraction.Forest.contract_fork_precond (mate_abstract (qbs_matching state)) (qbs_forest s4)
      (qbs_component state) (Contraction.target_component state) (butlast Pv) (butlast Qv) (last Pv) (fresh_vertex fresh)
      (drop (length (rev Pv)) (forest_path (qbs_forest state) (qbs_component state)))
      (%x. if x : set (rev Pv @ butlast (rev (rev Qv))) then fresh_vertex fresh else x)"
    "last Pv : fset_abstract (forest_evens (qbs_forest s4))" "fresh_vertex fresh : K"
    "path_invar P" "path_invar Q" "plen <= path_cap" "qlen <= path_cap"
    "Pv = butlast Pv @ [last Pv]" "Qv = butlast Qv @ [last Pv]"
    "edge_invar (qbs_forest_edges s4)" "Contraction.cycle_storage_valid s4 T C"
    "owner_invar (qbs_owners s4)" "base_invar (qbs_bases s4)" "link_invar (qbs_hints s4)"
    "header_invar R" "used + length cs <= pool_cap" "t + length (filter (Contraction.cycle_old_odd s4) cs) <= cap"
    "set cs <= K"
proof-
  note path_facts = contraction_paths[OF assms(1) assms(4)]
  have counter: "Search.fresh_counter state first_fresh fresh_limit fresh_vertex fresh"
    using assms(3)
    by (simp add: registers_def Search.fresh_counter_def)
  obtain fresh2 where pop: "queue_pop (qbs_fresh state) = (fresh_vertex fresh, fresh2)"
    using Search.fresh_counter_contraction(2)[OF assms(1,2) counter]
    by(cases "queue_pop (qbs_fresh state)") auto
  note geometry = Search.contraction_geometry[OF assms(1) assms(2) path_facts(1) pop]
  have nonempty: "Pv ~= []" "Qv ~= []" and base: "last Qv = last Pv"
    using geometry(1-3)
    by (simp_all add: hd_rev Pv_def Qv_def)
  show views: "Pv = butlast Pv @ [last Pv]" "Qv = butlast Qv @ [last Pv]"
    using append_butlast_last_id[OF nonempty(1)] append_butlast_last_id[OF nonempty(2)] base
    by simp_all
  have scan: "Contraction.scanning_edge state"
    using assms(1)
    by (simp add: Contraction.Quadratic_Blossom_Search_call_7_conds_def)
  have s4: "qbs_forest s4 = qbs_forest state" "qbs_forest_edges s4 = qbs_forest_edges state"
    "qbs_owners s4 = qbs_owners state" "qbs_bases s4 = qbs_bases state" "qbs_hints s4 = qbs_hints state"
    "qbs_hierarchy s4 = qbs_hierarchy state" "qbs_fresh s4 = qbs_fresh state"
    "qbs_components s4 = qbs_components state" "qbs_cycle_edges s4 = qbs_cycle_edges state"
    "qbs_parents s4 = qbs_parents state"
    using scan_components[OF scan assms(2)]
    by (simp_all add: s4_def Contraction.Quadratic_Blossom_Search_upd4_def)
  have "rev Pv = last Pv # rev (butlast Pv)"
    by (subst views(1)) simp
  hence cycle: "cs = rev Pv @ butlast Qv"
    using Contraction.cycle_view_prefixes[OF views[unfolded Pv_def Qv_def], folded Pv_def Qv_def cs_def]
    by simp
  have valid: "owner_invar (qbs_owners state)" "edge_invar (qbs_forest_edges state)" "link_invar (qbs_hints state)"
    "base_invar (qbs_bases state)" "uf_invar (qbs_components state)" "edge_invar (qbs_cycle_edges state)"
    "link_invar (qbs_parents state)"
    using assms(2)
    by (auto elim!: Search.invar_search_props Contraction.invar_adts_props
      Search.invar_recovering_structure_props Search.invar_navigation_props)
  thus "edge_invar (qbs_forest_edges s4)" "owner_invar (qbs_owners s4)" "base_invar (qbs_bases s4)"
    "link_invar (qbs_hints s4)"
    by (simp_all add: s4)
  have packed: "header_invar R" "pool_invar C"
    "used = (SUM a:hierarchy_ids (qbs_hierarchy state). length (hierarchy_children (qbs_hierarchy state) a))"
    using assms(7)
    by (auto elim!: Packed.packed_hierarchy_props)
  thus "header_invar R"
    by simp
  show "Contraction.cycle_storage_valid s4 T C"
    using valid assms(5) packed(2)
    by (simp add: Contraction.cycle_storage_valid_def s4)
  note space = Search.contraction_storage_space[OF assms(1) assms(2) path_facts(1) pop assms(6) packed(3) key_bounds]
  show "used + length cs <= pool_cap" "t + length (filter (Contraction.cycle_old_odd s4) cs) <= cap"
    using space
    by (simp_all add: cycle s4 Pv_def Qv_def)
  show "set cs <= K" "fresh_vertex fresh : K"
    using Search.contraction_cycle_forest[OF assms(1) assms(2) path_facts(1) pop]
      Search.contraction_active_bounds(1)[OF assms(1) assms(2) path_facts(1) pop]
      Search.contraction_fresh(1)[OF assms(1) assms(2) path_facts(1) pop] assms(2)
    by (auto simp: cycle Pv_def Qv_def elim!: Search.invar_search_props Contraction.invar_forest_props)
  show "Contraction.Forest.contract_fork_precond (mate_abstract (qbs_matching state)) (qbs_forest s4)
      (qbs_component state) (Contraction.target_component state) (butlast Pv) (butlast Qv) (last Pv) (fresh_vertex fresh)
      (drop (length (rev Pv)) (forest_path (qbs_forest state) (qbs_component state)))
      (%x. if x : set (rev Pv @ butlast (rev (rev Qv))) then fresh_vertex fresh else x)"
    using Search.contraction_forest_precond[OF assms(1) assms(2) path_facts(1) pop] nonempty
    by (simp add: s4 hd_rev butlast_rev Pv_def Qv_def)
  show "last Pv : fset_abstract (forest_evens (qbs_forest s4))"
    using Search.contraction_base_even[OF assms(1) assms(2) path_facts(1) pop] nonempty
    by (simp add: s4 hd_rev Pv_def Qv_def)
  show "path_invar P" "path_invar Q" "plen <= path_cap" "qlen <= path_cap"
    by (rule path_facts(2-5))+
qed
lemma contract_core_refine:
  assumes  "Contraction.Quadratic_Blossom_Search_call_7_conds state" and  "Search.invar_search state"
    and  "registers state it h t fresh used"
    and  "paths_result (qbs_forest state) (qbs_component state) (Contraction.target_component state)
      (last (forest_path (qbs_forest state) (qbs_component state)) =
        last (forest_path (qbs_forest state) (Contraction.target_component state)), plen, qlen) P Q"
    and  "frontier_invar T" "Search.frontier_history state (Contraction.Frontier.buffer_view T 0 t False) h"
      "Packed.packed_hierarchy (qbs_hierarchy state) R C used"
  shows "<graph_storage Gi * matching_assn M0 Mi * task_storage Wi * output_assn out0 Bi * state_storage state Wi *
      (frontier_assn T (get_frontier Wi) * header_assn R (get_headers Wi) * pool_assn C (get_pool Wi)) *
      (path_assn P (get_left Wi) * path_assn Q (get_right Wi) *
        marks_assn (Suc (Suc (fresh - first_fresh))) (get_marks Wi) (get_positions Wi))>
    contract_search_into Wi (Contraction.scanned_vertex state) (Contraction.scanned_neighbour state) plen qlen
      (fresh_vertex fresh) t used
    <\<lambda>t'. workspace_assn (Contraction.Quadratic_Blossom_Search_upd7 state) (row_advance it) h t' (Suc fresh)
        (used + (plen + qlen - 1)) Gi Mi Wi Bi *
      \<up>(registers (Contraction.Quadratic_Blossom_Search_upd7 state) (row_advance it) h t' (Suc fresh)
        (used + (plen + qlen - 1)) \<and>
        qbs_component (Contraction.Quadratic_Blossom_Search_upd7 state) = fresh_vertex fresh)>"
proof-
  let ?fp = "forest_path (qbs_forest state) (qbs_component state)"
    and ?fq = "forest_path (qbs_forest state) (Contraction.target_component state)"
    and ?P = "Contraction.Paths.buffer_view P 0 plen False" and ?Q = "Contraction.Paths.buffer_view Q 0 qlen False"
    and ?s4 = "Contraction.Quadratic_Blossom_Search_upd4 state"
    and ?cs = "Contraction.cycle_view P plen Q qlen"
  obtain b fresh' where pop: "queue_pop (qbs_fresh state) = (b, fresh')"
    by (cases "queue_pop (qbs_fresh state)") auto
  note path_facts = contraction_paths[OF assms(1) assms(4)]
  have counter: "Search.fresh_counter state first_fresh fresh_limit fresh_vertex fresh"
    using assms(3)
    by (simp add: registers_def Search.fresh_counter_def)
  have fresh_b: "b = fresh_vertex fresh"
    using Search.fresh_counter_contraction(2)[OF assms(1) assms(2) counter] pop
    by simp
  note inputs = contraction_inputs[OF assms, folded fresh_b]
  note views = inputs(8,9)
  have scan: "Contraction.scanning_edge state"
    using assms(1)
    by (simp add: Contraction.Quadratic_Blossom_Search_call_7_conds_def)
  have s4: "qbs_forest ?s4 = qbs_forest state" "qbs_forest_edges ?s4 = qbs_forest_edges state"
    "qbs_cycle_edges ?s4 = qbs_cycle_edges state" "qbs_parents ?s4 = qbs_parents state"
    "qbs_owners ?s4 = qbs_owners state" "qbs_bases ?s4 = qbs_bases state" "qbs_hints ?s4 = qbs_hints state"
    "qbs_hierarchy ?s4 = qbs_hierarchy state" "qbs_fresh ?s4 = qbs_fresh state"
    "qbs_components ?s4 = qbs_components state"
    using scan_components[OF scan assms(2)]
    by (simp_all add: Contraction.Quadratic_Blossom_Search_upd4_def)
  have cycle: "?cs = rev ?P @ butlast ?Q"
    using Contraction.cycle_view_prefixes[OF views] views(1)
    by simp
  note rule = Contraction.contract_into_rule[where state = ?s4, OF inputs]
  have pop4: "fst (queue_pop (qbs_fresh ?s4)) = b"
    using pop
    by (simp add: s4)
  have sfx: "longest_disj_sfx (rev ?fp) (rev ?fq) =
      (rev (butlast ?P @ [last ?P]), rev (butlast ?Q @ [last ?P]))"
    using path_facts(1) views
    by simp
  have upd7: "Contraction.Quadratic_Blossom_Search_upd7 state =
    (Contraction.process_cycle ?s4 ?cs plen (qbs_current state, Contraction.scanned_neighbour state) b) \<lparr>
      qbs_forest := forest_contract (qbs_forest ?s4) (butlast ?P @ [last ?P]) (butlast ?Q @ [last ?P]) b,
      qbs_matching := mate_contract (qbs_matching ?s4) ?cs b,
      qbs_hierarchy := hierarchy_merge (qbs_hierarchy ?s4) ?cs b,
      qbs_component := b,
      qbs_forest_edges := edge_update (qbs_forest_edges ?s4) b (Contraction.forest_edge ?s4 (last ?P)),
      qbs_bases := base_update (qbs_bases ?s4) b (base_lookup (qbs_bases ?s4) (last ?P)),
      qbs_hints := link_update (qbs_hints ?s4) b (nil,0),
      qbs_fresh := snd (queue_pop (qbs_fresh ?s4))\<rparr>"
    unfolding Contraction.Quadratic_Blossom_Search_upd7_def
    by (rule Contraction.contract_search_prefixes[OF views sfx pop4])
  let ?next = "Contraction.process_cycle ?s4 ?cs plen (qbs_current state, Contraction.scanned_neighbour state) b"
  note rule' = rule[unfolded Contraction.cycle_storage_def s4 Let_def]
  have triple: "<graph_storage Gi * matching_assn M0 Mi * task_storage Wi * output_assn out0 Bi * state_storage state Wi *
      (frontier_assn T (get_frontier Wi) * header_assn R (get_headers Wi) * pool_assn C (get_pool Wi)) *
      (path_assn P (get_left Wi) * path_assn Q (get_right Wi) *
        marks_assn (Suc (Suc (fresh - first_fresh))) (get_marks Wi) (get_positions Wi))>
    contract_search_into Wi (Contraction.scanned_vertex state) (Contraction.scanned_neighbour state) plen qlen b t used
    <\<lambda>t'. \<exists>\<^sub>AT' C'. graph_storage Gi * matching_assn M0 Mi * task_storage Wi * output_assn out0 Bi *
      state_storage (Contraction.Quadratic_Blossom_Search_upd7 state) Wi *
      (frontier_assn T' (get_frontier Wi) * header_assn (header_update R b (used, plen + (qlen - 1))) (get_headers Wi) *
        pool_assn C' (get_pool Wi)) *
      (path_assn P (get_left Wi) * path_assn Q (get_right Wi) *
        marks_assn (Suc (Suc (fresh - first_fresh))) (get_marks Wi) (get_positions Wi)) *
      \<up>(Contraction.cycle_storage_valid ?next T' C' \<and> t' = t + length (filter (Contraction.cycle_old_odd ?s4) ?cs) \<and>
        Contraction.Frontier.buffer_view T' 0 t' False =
          Contraction.Frontier.buffer_view T 0 t False @ filter (Contraction.cycle_old_odd ?s4) ?cs \<and>
        Contraction.Pool.buffer_view C' 0 (used + length ?cs) False = Contraction.Pool.buffer_view C 0 used False @ ?cs)>"
    unfolding contract_search_into_def state_storage_def upd7
    by (sep_auto heap: rule' simp: s4)
  have "0 < qlen"
    using views(2)
    by (cases qlen) (auto simp: Contraction.Paths.buffer_view_def)
  hence lengths: "length ?cs = plen + (qlen - 1)" "plen + (qlen - 1) = plen + qlen - 1"
    by auto
  have hierarchy7: "qbs_hierarchy (Contraction.Quadratic_Blossom_Search_upd7 state) =
      hierarchy_merge (qbs_hierarchy state) ?cs b"
    by (simp add: upd7 s4)
  have merge: "Contraction.Hierarchy.blossom_forest_merge_precond (qbs_hierarchy state) ?cs b"
    using Search.contraction_hierarchy_precond[OF assms(1) assms(2) path_facts(1) pop]
    by (simp add: cycle)
  have packed7: "Packed.packed_hierarchy (qbs_hierarchy (Contraction.Quadratic_Blossom_Search_upd7 state))
      (header_update R b (used, plen + (qlen - 1))) C' (used + (plen + qlen - 1))"
    if "pool_invar C'" "Contraction.Pool.buffer_view C' 0 (used + length ?cs) False =
      Contraction.Pool.buffer_view C 0 used False @ ?cs" for C'
    using Packed.packed_hierarchy_merge_buffer[OF assms(7) that merge inputs(3,16)]
    unfolding hierarchy7 lengths(2)[symmetric] lengths(1) .
  have history7: "Search.frontier_history (Contraction.Quadratic_Blossom_Search_upd7 state)
      (Contraction.Frontier.buffer_view T 0 t False @ filter (Contraction.cycle_old_odd ?s4) ?cs) h"
    using Search.frontier_history_contraction[OF assms(1) assms(2) path_facts(1) pop assms(6)]
    by (simp add: cycle s4)
  have registers7: "registers (Contraction.Quadratic_Blossom_Search_upd7 state) (row_advance it) h
      (t + length (filter (Contraction.cycle_old_odd ?s4) ?cs)) (Suc fresh) used'"
    if "used' = (\<Sum>a\<in>hierarchy_ids (qbs_hierarchy (Contraction.Quadratic_Blossom_Search_upd7 state)).
      length (hierarchy_children (qbs_hierarchy (Contraction.Quadratic_Blossom_Search_upd7 state)) a))" for used'
  proof-
    note queue = Search.contraction_queue[OF assms(1) assms(2) path_facts(1) pop]
    have "registers ?s4 (row_advance it) h t fresh used"
      by (rule scan_registers[OF scan assms(2) assms(3)])
    moreover have "qbs_neighbours (Contraction.Quadratic_Blossom_Search_upd7 state) = qbs_neighbours ?s4"
      "qbs_current (Contraction.Quadratic_Blossom_Search_upd7 state) = qbs_current state"
      by (simp_all add: upd7 Search.process_cycle_scan, simp add: Contraction.Quadratic_Blossom_Search_upd4_def Search.process_cycle_frame)
    ultimately show ?thesis
      using that inputs(17) queue Search.fresh_counter_contraction(3)[OF assms(1) assms(2) counter]
      by (auto simp: registers_def Search.fresh_counter_def cycle s4 Contraction.Quadratic_Blossom_Search_upd4_def)
  qed
  have buffers7: "frontier_assn T' (get_frontier Wi) * header_assn (header_update R b (used, plen + (qlen - 1))) (get_headers Wi) *
      pool_assn C' (get_pool Wi) \<Longrightarrow>\<^sub>A buffer_storage (Contraction.Quadratic_Blossom_Search_upd7 state) h t' (used + (plen + qlen - 1)) Wi"
    if "Contraction.cycle_storage_valid ?next T' C'" "t' = t + length (filter (Contraction.cycle_old_odd ?s4) ?cs)"
      "Contraction.Frontier.buffer_view T' 0 t' False =
        Contraction.Frontier.buffer_view T 0 t False @ filter (Contraction.cycle_old_odd ?s4) ?cs"
      "Contraction.Pool.buffer_view C' 0 (used + length ?cs) False = Contraction.Pool.buffer_view C 0 used False @ ?cs"
    for T' C' t'
  proof-
    have valid': "frontier_invar T'" "pool_invar C'"
      using that(1)
      by (simp_all add: Contraction.cycle_storage_valid_def)
    show ?thesis
      unfolding buffer_storage_def
      by (rule ent_ex_postI[where x = T'], rule ent_ex_postI[where x = "header_update R b (used, plen + (qlen - 1))"],
        rule ent_ex_postI[where x = C']) (sep_auto simp: valid' that(3) history7 packed7[OF valid'(2) that(4), simplified])
  qed
  have first: "Suc (Suc fresh - first_fresh) = Suc (Suc (fresh - first_fresh))"
    using assms(3)
    by (simp add: registers_def Suc_diff_le)
  have query7: "path_assn P (get_left Wi) * path_assn Q (get_right Wi) *
      marks_assn (Suc (Suc (fresh - first_fresh))) (get_marks Wi) (get_positions Wi) \<Longrightarrow>\<^sub>A
    query_storage (Suc (Suc fresh - first_fresh)) Wi"
    unfolding query_storage_def first
    by (rule ent_ex_postI[where x = P], rule ent_ex_postI[where x = Q]) (sep_auto simp: path_facts(2,3))
  have component7: "qbs_component (Contraction.Quadratic_Blossom_Search_upd7 state) = b"
    by (simp add: upd7)
  have used7: "used + (plen + qlen - 1) = (\<Sum>a\<in>hierarchy_ids (qbs_hierarchy (Contraction.Quadratic_Blossom_Search_upd7 state)).
      length (hierarchy_children (qbs_hierarchy (Contraction.Quadratic_Blossom_Search_upd7 state)) a))"
    if "Contraction.cycle_storage_valid ?next T' C'"
      "Contraction.Pool.buffer_view C' 0 (used + length ?cs) False = Contraction.Pool.buffer_view C 0 used False @ ?cs"
    for T' C'
    using packed7[OF _ that(2)] that(1)
    by (auto simp: Contraction.cycle_storage_valid_def elim!: Packed.packed_hierarchy_props)
  show ?thesis
    unfolding fresh_b[symmetric]
    by(rule ht_cons_post_prec[OF triple], intro ent_ex_preI ent_pure_preI, elim conjE)
      (auto simp: workspace_assn_def ent_pure_post_iff component7
        intro: ent_star_mono[OF ent_star_mono[OF ent_refl buffers7[simplified]] query7]
          registers7[simplified] used7[simplified])
qed
lemma contract_refine:
  assumes "Contraction.Quadratic_Blossom_Search_call_7_conds state" "Search.invar_search state"
    "registers state it h t fresh used"
  shows "<search_paths_assn state it h t fresh used plen qlen Gi Mi Wi Bi>
    contract_search_into Wi (Contraction.scanned_vertex state) (Contraction.scanned_neighbour state) plen qlen
      (fresh_vertex fresh) t used
    <\<lambda>t'. workspace_assn (Contraction.Quadratic_Blossom_Search_upd7 state) (row_advance it) h t' (Suc fresh)
        (used + (plen + qlen - 1)) Gi Mi Wi Bi *
      \<up>(registers (Contraction.Quadratic_Blossom_Search_upd7 state) (row_advance it) h t' (Suc fresh)
        (used + (plen + qlen - 1)) \<and>
        qbs_component (Contraction.Quadratic_Blossom_Search_upd7 state) = fresh_vertex fresh)>"
  using assms
  unfolding search_paths_assn_def buffer_storage_def
  by (sep_auto heap: contract_core_refine)
end

end

context Cubic_Blossom_Refinement
begin

text "Recovery reads the found path from the two path buffers and the bridge scalars, the
  packed hierarchy, the retained annotations, the route hints and the saved-cycle slots."

definition "recovery_route_into Wi target b =
  Blossom_Path_Recovery_Imperative.cache_into link_update_imp link_lookup_imp (get_navigation Wi) (get_hints Wi) target b"

definition "recovery_route_index Wi b = do { x \<leftarrow> link_lookup_imp (get_hints Wi) b; return (snd x) }"

definition "recovery_stack_write Wi i off len cur stop forward a z =
  slot_update_imp (get_tasks Wi) i (off, len, cur, stop, forward, a, z)"

sublocale Recovery_Ops: Blossom_Path_Recovery_Buffer nil "\<lambda>Wi. base_lookup_imp (get_bases Wi)" recovery_route_into
  recovery_route_index "\<lambda>Wi. header_lookup_imp (get_headers Wi)" "\<lambda>Wi. pool_lookup_imp (get_pool Wi)"
  "\<lambda>Wi. edge_lookup_imp (get_cycle_edges Wi)" "\<lambda>Wi. slot_lookup_imp (get_tasks Wi)" recovery_stack_write
  "\<lambda>Wi plen qlen. Contraction.augmenting_read (get_left Wi) plen (get_right Wi) qlen"
  "\<lambda>Wi plen qlen. Contraction.cycle_edge_into (get_forest_edges Wi) (get_left Wi) plen (get_right Wi) qlen"
  output_update_imp .

definition "recovery_range H R C b off len \<longleftrightarrow> b \<in> hierarchy_ids H \<and> (off, len) = header_lookup R b \<and>
  off + len \<le> pool_cap \<and> Contraction.Pool.buffer_view C off len False = hierarchy_children H b"

definition "recovery_structure B D N R C E P Q Wi = base_assn D (get_bases Wi) * link_assn N (get_navigation Wi) *
  header_assn R (get_headers Wi) * pool_assn C (get_pool Wi) * edge_assn B (get_cycle_edges Wi) *
  edge_assn E (get_forest_edges Wi) * path_assn P (get_left Wi) * path_assn Q (get_right Wi) *
  \<up>(base_invar D \<and> link_invar N \<and> header_invar R \<and> pool_invar C \<and> edge_invar B \<and> edge_invar E \<and>
    path_invar P \<and> path_invar Q)"

definition "recovery_stack H R C ts Wi =
  Quadratic_Cycle_Stack.cycle_stack_assn task_cap slot_invar slot_lookup slot_assn (recovery_range H R C) ts (get_tasks Wi)"

lemma recovery_registers:
  "Blossom_Path_Recovery_Registers task_cap output_cap base_invar base_update base_lookup output_invar
    output_update output_lookup K link_invar link_update link_lookup link_assn link_update_imp link_lookup_imp"
  unfolding Blossom_Path_Recovery_Registers_def Blossom_Path_Recovery_Imperative_def
  by (intro conjI Search.Recovery.Blossom_Path_Recovery_axioms Contraction.Link_Imp.fixed_univ_map_imp_axioms)

lemma recovery_slots:
  "Quadratic_Cycle_Stack task_cap slot_invar slot_update slot_lookup slot_assn slot_update_imp slot_lookup_imp"
  unfolding Quadratic_Cycle_Stack_def
  by (rule Slots.fixed_univ_map_imp_axioms)

lemma recovery_range_props:
  assumes "Search.recovery_tree H" "hierarchy_ids H \<subseteq> K" "recovery_range H R C b off len"
  shows "length (hierarchy_children H b) = len" "set (hierarchy_children H b) \<subseteq> K"
    "i < len \<Longrightarrow> off + i < pool_cap" "i < len \<Longrightarrow> pool_lookup C (off + i) = hierarchy_children H b ! i"
proof-
  have "set (hierarchy_children H b) <= hierarchy_ids H"
    using assms(1,3)
    by (cases "hierarchy_children H b = []")
      (auto simp: recovery_range_def Search.recovery_tree_def Let_def)
  with assms show "length (hierarchy_children H b) = len" "set (hierarchy_children H b) <= K"
    "i < len ==> off + i < pool_cap"
    "i < len ==> pool_lookup C (off + i) = hierarchy_children H b ! i"
    using Contraction.Pool.view_nth[of i len C off False]
    by (auto simp: recovery_range_def dest: arg_cong[where f = length])
qed
lemma recovery_range_exists:
  assumes "Packed.packed_hierarchy H R C used" "b \<in> hierarchy_ids H" "hierarchy_children H b \<noteq> []"
  shows "recovery_range H R C b (fst (header_lookup R b)) (snd (header_lookup R b))"
  using assms
  by (auto simp: recovery_range_def elim!: Packed.packed_hierarchy_props)

lemma recovery_stack_axioms:
  assumes "Search.recovery_tree H" "hierarchy_ids H \<subseteq> K"
  shows "Blossom_Path_Recovery_Stack_Refinement_axioms task_cap K (\<lambda>Wi. header_lookup_imp (get_headers Wi))
    (\<lambda>Wi. edge_lookup_imp (get_cycle_edges Wi)) (\<lambda>Wi. slot_lookup_imp (get_tasks Wi)) recovery_stack_write
    hierarchy_children edge_lookup (\<lambda>Wi. pool_lookup_imp (get_pool Wi)) H B
    (recovery_structure B D N R C E P Q) (recovery_stack H R C) (recovery_range H R C)"
proof-
  note props = recovery_range_props[OF assms]
  note stack = Quadratic_Cycle_Stack.cycle_stack_write_rule[OF recovery_slots,
      unfolded Quadratic_Cycle_Stack.cycle_stack_write_def[OF recovery_slots]]
    Quadratic_Cycle_Stack.cycle_stack_read_rule[OF recovery_slots]
  have range: "<recovery_structure B D N R C E P Q Wi> header_lookup_imp (get_headers Wi) b
      <\<lambda>r. recovery_structure B D N R C E P Q Wi * \<up>(recovery_range H R C b (fst r) (snd r))>"
    if "b \<in> K" "recovery_range H R C b off len" for b off len Wi
  proof-
    have "header_lookup R b = (off, len)"
      using that(2)
      by (simp add: recovery_range_def)
    thus ?thesis
      using that
      unfolding recovery_structure_def
      by (sep_auto heap: Contraction.Headers.fixed_univ_map_lookup_rule)
  qed
  have child: "<recovery_structure B D N R C E P Q Wi> pool_lookup_imp (get_pool Wi) (off + i)
      <\<lambda>c. recovery_structure B D N R C E P Q Wi * \<up>(c = hierarchy_children H b ! i)>"
    if "recovery_range H R C b off len" "i < len" for b off len i Wi
    using props[OF that(1)] that(2)
    unfolding recovery_structure_def
    by (sep_auto heap: Contraction.Pool.Buffer.fixed_univ_map_lookup_rule)
  have edge: "<recovery_structure B D N R C E P Q Wi> edge_lookup_imp (get_cycle_edges Wi) v
      <\<lambda>e. recovery_structure B D N R C E P Q Wi * \<up>(e = edge_lookup B v)>" if "v \<in> K" for v Wi
    using that
    unfolding recovery_structure_def
    by (sep_auto heap: Contraction.Edge_Imp.fixed_univ_map_lookup_rule)
  show ?thesis
    unfolding Blossom_Path_Recovery_Stack_Refinement_axioms_def recovery_stack_def
    using props range child edge
    by (auto simp: recovery_stack_write_def intro!: stack)
qed

lemma recovery_cache_rule:
  assumes "Search.recovery_tree H" "Search.invar_navigation H D N" "hierarchy_ids H \<subseteq> K"
    "b \<in> hierarchy_ids H" "target \<in> hierarchy_members H b" "Search.invar_route_cache H J"
  shows "<link_assn N Ni * link_assn J Ji>
    Blossom_Path_Recovery_Imperative.cache_into link_update_imp link_lookup_imp Ni Ji target b
    <\<lambda>_. link_assn N Ni * link_assn (Search.Recovery.cache_route N target b J) Ji>"
  using assms
  by (intro Blossom_Path_Recovery_Imperative.cache_into_refine[OF recovery_registers[unfolded Blossom_Path_Recovery_Registers_def],
      where I = "Search.invar_cache_route H b target", OF _ _ _ _ Search.cache_refinement_ready[OF assms(1-3)]])
    (auto simp: Search.invar_route_cache_def intro: Search.cache_route_initial_dom[where D = D] Search.invar_cache_route_initial)

lemma recovery_buffer_axioms:
  assumes  "Search.recovery_tree H" "Search.invar_navigation H D N" "hierarchy_ids H \<subseteq> K"
    and  "ps = Contraction.augmenting_view P plen Q qlen"
      "es = Contraction.outward_edges s (Contraction.Paths.buffer_view P 0 plen True) @ [(u,v)] @
        Contraction.rootward_edges s (Contraction.Paths.buffer_view Q 0 qlen False)"
      "set ps \<subseteq> K" "0 < plen" "0 < qlen" "plen \<le> path_cap" "qlen \<le> path_cap"
  shows "Blossom_Path_Recovery_Buffer_Refinement_axioms output_cap output_invar output_update K link_invar link_update
    (\<lambda>Wi. base_lookup_imp (get_bases Wi)) recovery_route_into recovery_route_index
    (\<lambda>Wi plen qlen. Contraction.augmenting_read (get_left Wi) plen (get_right Wi) qlen)
    (\<lambda>Wi plen qlen. Contraction.cycle_edge_into (get_forest_edges Wi) (get_left Wi) plen (get_right Wi) qlen)
    (recovery_structure B D N R C (qbs_forest_edges s) P Q) nil output_update_imp base_lookup link_lookup D N ps es
    plen qlen u v (\<lambda>J Wi. link_assn J (get_hints Wi)) output_assn
    (\<lambda>J target b. Search.invar_route_cache H J \<and> b \<in> hierarchy_ids H \<and> target \<in> hierarchy_members H b)"
proof-
  have lengths: "length es = length ps - 1" "length ps = plen + qlen"
    using assms(4,5,7,8)
      Contraction.augmenting_crossings_length[OF assms(7,8), where state = s and u = u and v = v and P = P and Q = Q]
    by simp_all
  have base: "<recovery_structure B D N R C (qbs_forest_edges s) P Q Wi> base_lookup_imp (get_bases Wi) b
      <\<lambda>a. recovery_structure B D N R C (qbs_forest_edges s) P Q Wi * \<up>(a = base_lookup D b)>" if "b \<in> K" for b Wi
    using that unfolding recovery_structure_def
    by (sep_auto heap: Contraction.Base_Imp.fixed_univ_map_lookup_rule)
  have route: "<recovery_structure B D N R C (qbs_forest_edges s) P Q Wi * link_assn J (get_hints Wi)>
      recovery_route_into Wi target b
      <\<lambda>_. recovery_structure B D N R C (qbs_forest_edges s) P Q Wi *
        link_assn (Search.Recovery.cache_route N target b J) (get_hints Wi)>"
    if "Search.invar_route_cache H J" "b \<in> hierarchy_ids H" "target \<in> hierarchy_members H b" for J target b Wi
    unfolding recovery_structure_def recovery_route_into_def
    by (sep_auto heap: recovery_cache_rule[OF assms(1,2,3) that(2,3,1)])
  have index: "<link_assn J (get_hints Wi)> recovery_route_index Wi b
      <\<lambda>i. link_assn J (get_hints Wi) * \<up>(i = snd (link_lookup J b))>" if "link_invar J" "b \<in> K" for J b Wi
    using that unfolding recovery_route_index_def
    by (sep_auto heap: Contraction.Link_Imp.fixed_univ_map_lookup_rule)
  have component: "<recovery_structure B D N R C (qbs_forest_edges s) P Q Wi>
      Contraction.augmenting_read (get_left Wi) plen (get_right Wi) qlen i
      <\<lambda>c. recovery_structure B D N R C (qbs_forest_edges s) P Q Wi * \<up>(c = ps ! i)>" if "i < length ps" for i Wi
    using that assms(9,10) lengths(2) unfolding recovery_structure_def assms(4)
    by (sep_auto heap: Contraction.augmenting_read_rule)
  have crossing: "<recovery_structure B D N R C (qbs_forest_edges s) P Q Wi>
      Contraction.cycle_edge_into (get_forest_edges Wi) (get_left Wi) plen (get_right Wi) qlen u v i (ps ! i)
      <\<lambda>e. recovery_structure B D N R C (qbs_forest_edges s) P Q Wi * \<up>(e = es ! i)>" if "i < length es" for i Wi
    using that assms(4,5,6,7,8,9,10) lengths unfolding recovery_structure_def
    by (sep_auto heap: Contraction.augmenting_crossing_rule[where state = s])
  have emit: "<output_assn out Bi> output_update_imp Bi k v <\<lambda>_. output_assn (output_update out k v) Bi>"
    if "output_invar out" "k < output_cap" for out k Bi v
    using that
    by (sep_auto heap: Output_Imp.fixed_univ_map_upd_rule)
  show ?thesis
    unfolding Blossom_Path_Recovery_Buffer_Refinement_axioms_def
    using Search.input_props(4) lengths base route index component crossing emit
    by blast
qed

lemma recovery_instance:
  assumes "Search.recovery_tree H" "Search.invar_navigation H D N" "hierarchy_ids H \<subseteq> K"
    "ps = Contraction.augmenting_view P plen Q qlen"
    "es = Contraction.outward_edges s (Contraction.Paths.buffer_view P 0 plen True) @ [(u,v)] @
      Contraction.rootward_edges s (Contraction.Paths.buffer_view Q 0 qlen False)"
    "set ps \<subseteq> K" "0 < plen" "0 < qlen" "plen \<le> path_cap" "qlen \<le> path_cap"
  shows "Blossom_Path_Recovery_Buffer_Refinement task_cap output_cap base_invar base_update output_invar output_update K
    link_invar link_update link_assn link_update_imp link_lookup_imp
    (\<lambda>Wi. base_lookup_imp (get_bases Wi)) recovery_route_into recovery_route_index
    (\<lambda>Wi. header_lookup_imp (get_headers Wi)) (\<lambda>Wi. edge_lookup_imp (get_cycle_edges Wi))
    (\<lambda>Wi. slot_lookup_imp (get_tasks Wi)) recovery_stack_write
    (\<lambda>Wi plen qlen. Contraction.augmenting_read (get_left Wi) plen (get_right Wi) qlen)
    (\<lambda>Wi plen qlen. Contraction.cycle_edge_into (get_forest_edges Wi) (get_left Wi) plen (get_right Wi) qlen)
    hierarchy_children edge_lookup H B (recovery_structure B D N R C (qbs_forest_edges s) P Q) (recovery_stack H R C)
    (recovery_range H R C) nil (\<lambda>Wi. pool_lookup_imp (get_pool Wi)) output_update_imp base_lookup output_lookup link_lookup
    D N ps es plen qlen u v (\<lambda>J Wi. link_assn J (get_hints Wi)) output_assn
    (\<lambda>J target b. Search.invar_route_cache H J \<and> b \<in> hierarchy_ids H \<and> target \<in> hierarchy_members H b)"
  using assms
  unfolding Blossom_Path_Recovery_Buffer_Refinement_def Blossom_Path_Recovery_Stack_Refinement_def
  by (intro conjI recovery_registers recovery_stack_axioms recovery_buffer_axioms) assumption+
lemma initial_tasks_empty: "T0 = []"
  using Search.initial_workspaces(2)
  by simp

lemma found_status:
  "qbs_status (Contraction.Quadratic_Blossom_Search_upd6 state) =
    Quadratic_Path (rev (forest_path (qbs_forest state) (qbs_component state)) @
        forest_path (qbs_forest state) (Contraction.target_component state))
      (Contraction.outward_edges (Contraction.Quadratic_Blossom_Search_upd4 state)
          (rev (forest_path (qbs_forest state) (qbs_component state))) @
        [(qbs_current state, Contraction.scanned_neighbour state)] @
        Contraction.rootward_edges (Contraction.Quadratic_Blossom_Search_upd4 state)
          (forest_path (qbs_forest state) (Contraction.target_component state)))"
  by (simp add: Contraction.Quadratic_Blossom_Search_upd6_def Contraction.finish_search_def Let_def)

lemma found_fields:
  "qbs_hierarchy (Contraction.Quadratic_Blossom_Search_upd6 state) = qbs_hierarchy state"
  "qbs_cycle_edges (Contraction.Quadratic_Blossom_Search_upd6 state) = qbs_cycle_edges state"
  "qbs_bases (Contraction.Quadratic_Blossom_Search_upd6 state) = qbs_bases state"
  "qbs_parents (Contraction.Quadratic_Blossom_Search_upd6 state) = qbs_parents state"
  "qbs_hints (Contraction.Quadratic_Blossom_Search_upd6 state) = qbs_hints state"
  "qbs_forest_edges (Contraction.Quadratic_Blossom_Search_upd4 state) = qbs_forest_edges state"
  by (simp_all add: Contraction.Quadratic_Blossom_Search_upd6_def Contraction.finish_search_def Let_def
    Contraction.Quadratic_Blossom_Search_upd4_def)

lemma found_result_invar:
  assumes  "Contraction.Quadratic_Blossom_Search_call_6_conds state" and  "Search.invar_search state"
  shows "output_invar (qbr_output (Search.result_path (Contraction.Quadratic_Blossom_Search_upd6 state) T0 out0)) &
    qbr_length (Search.result_path (Contraction.Quadratic_Blossom_Search_upd6 state) T0 out0) <= output_cap &
    link_invar (qbr_hints (Search.result_path (Contraction.Quadratic_Blossom_Search_upd6 state) T0 out0))"
proof-
  let ?s6 = "Contraction.Quadratic_Blossom_Search_upd6 state"
  have inv6: "Search.invar_search ?s6"
    by (rule Search.invar_search_holds_6[OF assms(1) assms(2)])
  obtain p es where status: "qbs_status ?s6 = Quadratic_Path p es"
    using found_status
    by blast
  note dom = Search.result_path_properties(1)[OF inv6 status]
  have "Contraction.invar_matching_projection ?s6"
    using inv6
    by (auto elim!: Search.invar_search_props)
  note init = Search.initial_recovery_full[OF Search.search_recovery_precond[OF inv6 status] status this]
  have "card V0 = length vs"
    using distinct_card[OF Search.input_props(1)] Search.input_props(2)
    by simp
  hence space: "card V0 <= output_cap" "Suc (card (hierarchy_ids (qbs_hierarchy ?s6))) <= task_cap"
    using Search.initial_workspaces(4) Search.search_recovery_capacity[OF assms(2)]
    by (simp_all add: found_fields)
  have ids: "hierarchy_ids (qbs_hierarchy ?s6) <= K"
    using inv6
    by (auto elim!: Search.invar_search_props Contraction.invar_representatives_props)
  show ?thesis
    using Search.invar_recovery_holds[OF ids space dom init]
    by (auto simp: Search.result_path_def status Search.Recovery.lift_path_def
      Search.Recovery.Blossom_Path_Recovery_impl_same[OF dom] Search.invar_recovery_def
      Search.invar_recovery_routing_def Search.invar_route_cache_def
      elim!: Search.Recovery.invar_recovery_adts_props)
qed

text "Between two searches the workspace keeps only its invariants: the forest storage is
  released, all other components keep stale but valid contents."

definition "reusable_storage Wi = forest_workspace_assn (get_forest Wi) *
  (\<exists>\<^sub>AU L E B N D J T R C P Q tag. uf_assn U (get_union_find Wi) * owner_assn L (get_owners Wi) *
    edge_assn E (get_forest_edges Wi) * edge_assn B (get_cycle_edges Wi) * link_assn N (get_navigation Wi) *
    base_assn D (get_bases Wi) * link_assn J (get_hints Wi) * frontier_assn T (get_frontier Wi) *
    header_assn R (get_headers Wi) * pool_assn C (get_pool Wi) * path_assn P (get_left Wi) *
    path_assn Q (get_right Wi) * marks_assn tag (get_marks Wi) (get_positions Wi) *
    \<up>(uf_invar U & owner_invar L & edge_invar E & edge_invar B & link_invar N & base_invar D &
      link_invar J & frontier_invar T & header_invar R & pool_invar C & path_invar P & path_invar Q))"

definition "search_output_assn xs Gi Mi Wi Bi = graph_storage Gi * matching_assn M0 Mi * task_storage Wi *
  reusable_storage Wi * (\<exists>\<^sub>Aout. output_assn out Bi *
    \<up>(output_invar out & xs = map (output_lookup out) [0..<output_cap]))"

definition "search_input_assn Gi Mi Wi Bi = graph_storage Gi * matching_assn M0 Mi * task_storage Wi *
  output_assn out0 Bi * forest_workspace_assn (get_forest Wi) * uf_assn U0 (get_union_find Wi) *
  owner_assn L0 (get_owners Wi) * edge_assn P0 (get_forest_edges Wi) * edge_assn B0 (get_cycle_edges Wi) *
  link_assn N0 (get_navigation Wi) * base_assn D0 (get_bases Wi) * link_assn J0 (get_hints Wi) *
  (\<exists>\<^sub>AT R C P Q tag. frontier_assn T (get_frontier Wi) * header_assn R (get_headers Wi) *
    pool_assn C (get_pool Wi) * path_assn P (get_left Wi) * path_assn Q (get_right Wi) *
    marks_assn tag (get_marks Wi) (get_positions Wi) *
    \<up>(frontier_invar T & header_invar R & pool_invar C & path_invar P & path_invar Q))"

context
  assumes forest_release: "!!F Fi. forest_assn F Fi \<Longrightarrow>\<^sub>A forest_workspace_assn Fi"
begin

lemma exhausted_refine:
  assumes  "Search.invar_search state"
  shows "workspace_assn state it h t fresh used Gi Mi Wi Bi \<Longrightarrow>\<^sub>A
    (\<exists>\<^sub>Axs. search_output_assn xs Gi Mi Wi Bi * \<up>(length xs = output_cap))"
unfolding workspace_assn_def state_storage_def buffer_storage_def query_storage_def
    search_output_assn_def reusable_storage_def
  by (sep_frame_fwd rule: forest_release, insert assms Search.initial_workspaces(3),
    sep_auto simp: Packed.packed_hierarchy_def
      elim': Search.invar_search_props Contraction.invar_adts_props
        Search.invar_recovering_structure_props Search.invar_navigation_props)
end

context
  assumes vertex_order: "map vertex_at [0..<n] = vs"
    and fresh_names: "first_fresh \<le> fresh_limit" "queue_abstract fresh0 = map fresh_vertex [first_fresh..<fresh_limit]"
    and reset_components_rule: "\<And>U Ui. uf_invar U \<Longrightarrow> <uf_assn U Ui> reset_components_into Ui <\<lambda>_. uf_assn (uf_reset U) Ui>"
    and clear_marks_rule: "\<And>tag Ai Ii. <marks_assn tag Ai Ii> clear_marks_into Ai <\<lambda>_. marks_assn (Suc 0) Ai Ii>"
begin

lemma initialise_refine:
  "<search_input_assn Gi Mi Wi Bi> initialise_into Gi Mi Wi
    <%t. workspace_assn Search.initial_search_state empty_cursor 0 t first_fresh 0 Gi Mi Wi Bi *
      \<up>(registers Search.initial_search_state empty_cursor 0 t first_fresh 0)>"
proof-
  have n: "n <= cap" "set vs <= K Int V0"
    using arg_cong[OF vertex_order, of length]
    by auto
  have L: "owner_invar L0" "base_invar D0" "uf_invar U0"
    by simp_all
  note roots = Initialisation.initial_roots_into_rule[OF L(1,2) _ vertex_order n Search.input_props(12)]
  have hist: "Search.frontier_history Search.initial_search_state (queue_abstract (snd Contraction.initial_frontier)) 0"
    by (rule Search.frontier_history_initial)
  have queue: "queue_invar (snd Contraction.initial_frontier)"
    using Search.initial_state_props
    by (auto elim!: Search.invar_search_props Contraction.invar_adts_props)
  have packed: "Packed.packed_hierarchy H0 R C 0" if "header_invar R" "pool_invar C" for R C
    using that Search.initial_inputs(10,13)
    by (intro Packed.packed_hierarchy_initial) auto
  have used: "(\<Sum>b\<in>hierarchy_ids H0. length (hierarchy_children H0 b)) = 0"
    using Search.initial_inputs(10,13)
    by simp
  have regs: "registers Search.initial_search_state empty_cursor 0
      (length (queue_abstract (snd Contraction.initial_frontier))) first_fresh 0"
    using queue Search.frontier_history_bound[OF hist] fresh_names used
    by (simp add: registers_def)
  have inst: "<graph_storage Gi * matching_assn M0 Mi * task_storage Wi * output_assn out0 Bi *
      forest_workspace_assn (get_forest Wi) * uf_assn U0 (get_union_find Wi) * owner_assn L0 (get_owners Wi) *
      edge_assn P0 (get_forest_edges Wi) * edge_assn B0 (get_cycle_edges Wi) * link_assn N0 (get_navigation Wi) *
      base_assn D0 (get_bases Wi) * link_assn J0 (get_hints Wi) * frontier_assn T (get_frontier Wi) *
      header_assn R (get_headers Wi) * pool_assn C (get_pool Wi) * path_assn P (get_left Wi) *
      path_assn Q (get_right Wi) * marks_assn tag (get_marks Wi) (get_positions Wi)>
    initialise_into Gi Mi Wi
    <%t. workspace_assn Search.initial_search_state empty_cursor 0 t first_fresh 0 Gi Mi Wi Bi *
      \<up>(registers Search.initial_search_state empty_cursor 0 t first_fresh 0)>"
    if inv: "frontier_invar T" "header_invar R" "pool_invar C" "path_invar P" "path_invar Q" for T R C P Q tag
  proof-
    have "length vs <= cap"
      by simp
    note props = Initialisation.initial_models_props[OF L(1,2) inv(1) n(2)[THEN subset_trans[OF _ Int_lower1]] this]
    obtain S L' D' T' t' where m: "Initialisation.initial_models L0 D0 T = (S,L',D',T',t')"
      by (cases "Initialisation.initial_models L0 D0 T") auto
    show ?thesis
      unfolding initialise_into_def workspace_assn_def state_storage_def buffer_storage_def query_storage_def
      using props[unfolded m, simplified] regs hist packed[OF inv(2,3)] inv(4,5)
      by (sep_auto heap: reset_components_rule[OF L(3)] clear_marks_rule roots[OF inv(1)]
        simp: Initialisation.initial_storage_def Initialisation.initial_models_valid_def m
          Search.initial_state_observations(13-15))
  qed
  show ?thesis
    unfolding search_input_assn_def
    by (sep_auto heap: inst)
qed

end


lemma found_path_facts:
  assumes  "Contraction.Quadratic_Blossom_Search_call_6_conds state" and  "Search.invar_search state"
    and  "paths_result (qbs_forest state) (qbs_component state) (Contraction.target_component state)
      (last (forest_path (qbs_forest state) (qbs_component state)) =
        last (forest_path (qbs_forest state) (Contraction.target_component state)), plen, qlen) P Q"
  shows "Contraction.augmenting_view P plen Q qlen = rev (forest_path (qbs_forest state) (qbs_component state)) @
      forest_path (qbs_forest state) (Contraction.target_component state)"
    "Contraction.Paths.buffer_view P 0 plen True = rev (forest_path (qbs_forest state) (qbs_component state))"
    "Contraction.Paths.buffer_view Q 0 qlen False = forest_path (qbs_forest state) (Contraction.target_component state)"
    "path_invar P" "path_invar Q" "plen \<le> path_cap" "qlen \<le> path_cap" "0 < plen" "0 < qlen"
    "set (Contraction.augmenting_view P plen Q qlen) \<subseteq> K"
proof-
  have views: "Contraction.Paths.buffer_view P 0 plen False = forest_path (qbs_forest state) (qbs_component state)"
    "Contraction.Paths.buffer_view Q 0 qlen False = forest_path (qbs_forest state) (Contraction.target_component state)"
    "path_invar P" "path_invar Q" "plen \<le> path_cap" "qlen \<le> path_cap"
    using assms(1) assms(3)
    by (auto simp: paths_result_def Contraction.Quadratic_Blossom_Search_call_6_conds_def)
  thus view_facts: "Contraction.augmenting_view P plen Q qlen =
      rev (forest_path (qbs_forest state) (qbs_component state)) @
        forest_path (qbs_forest state) (Contraction.target_component state)"
    "Contraction.Paths.buffer_view P 0 plen True = rev (forest_path (qbs_forest state) (qbs_component state))"
    "Contraction.Paths.buffer_view Q 0 qlen False = forest_path (qbs_forest state) (Contraction.target_component state)"
    "path_invar P" "path_invar Q" "plen \<le> path_cap" "qlen \<le> path_cap"
    by (simp_all add: Contraction.augmenting_view_prefixes Contraction.Paths.buffer_view_def Let_def)
  have invars: "Contraction.invar_forest state" "Contraction.invar_queue state" "Contraction.invar_current state"
    "forest_invar (mate_abstract (qbs_matching state)) (qbs_forest state)"
    "Contraction.even_ids state \<union> Contraction.odd_ids state \<subseteq> Contraction.active_ids state"
    "hierarchy_ids (qbs_hierarchy state) \<subseteq> K"
    using assms(2)
    by (auto elim!: Search.invar_search_props Contraction.invar_forest_props Contraction.invar_representatives_props)
  have hierarchy: "hierarchy_invar (qbs_hierarchy state)"
    using assms(2)
    by (auto elim!: Search.invar_search_props Search.invar_recovering_structure_props)
  note even = Search.found_path_components[OF assms(1) invars(1-3)]
  have nonempty: "forest_path (qbs_forest state) (qbs_component state) \<noteq> []"
    "forest_path (qbs_forest state) (Contraction.target_component state) \<noteq> []"
    using Search.search_forest_path_head(1)[OF invars(1)] even
    by simp_all
  show "0 < plen" "0 < qlen"
    using nonempty arg_cong[OF views(1), of length] arg_cong[OF views(2), of length]
    by simp_all
  have "set (forest_path (qbs_forest state) (qbs_component state)) \<union>
      set (forest_path (qbs_forest state) (Contraction.target_component state)) \<subseteq> K"
    using Search.forest_path_vertices[OF invars(4) even(1)] Search.forest_path_vertices[OF invars(4) even(2)]
      invars(5,6) Search.active_ids_subset[OF hierarchy]
    by blast
  thus "set (Contraction.augmenting_view P plen Q qlen) \<subseteq> K"
    by (simp add: view_facts(1))
qed

text "The obligations of the recovery refinement at a step that finds an augmenting path."

lemma recovery_setup:
  assumes  "Contraction.Quadratic_Blossom_Search_call_6_conds state" and  "Search.invar_search state"
    and  "paths_result (qbs_forest state) (qbs_component state) (Contraction.target_component state)
      (last (forest_path (qbs_forest state) (qbs_component state)) =
        last (forest_path (qbs_forest state) (Contraction.target_component state)), plen, qlen) P Q"
    and  "Packed.packed_hierarchy (qbs_hierarchy state) R C used"
  defines "H == qbs_hierarchy state" and "B == qbs_cycle_edges state" and "D == qbs_bases state"
    and "N == qbs_parents state" and "ps == Contraction.augmenting_view P plen Q qlen"
    and "es == Contraction.outward_edges (Contraction.Quadratic_Blossom_Search_upd4 state)
      (Contraction.Paths.buffer_view P 0 plen True) @ [(qbs_current state, Contraction.scanned_neighbour state)] @
      Contraction.rootward_edges (Contraction.Quadratic_Blossom_Search_upd4 state)
        (Contraction.Paths.buffer_view Q 0 qlen False)"
  shows "Search.recovery_tree H" "Search.invar_navigation H D N" "hierarchy_ids H <= K"
    "set ps <= K" "0 < plen" "0 < qlen" "plen <= path_cap" "qlen <= path_cap"
    "Search.Recovery.Blossom_Path_Recovery_dom H B D N (Search.Recovery.initial_recovery ps es [] (qbs_hints state) out0)"
    "Search.invar_recovery H B D N (Search.Recovery.initial_recovery ps es [] (qbs_hints state) out0)"
    "!!s. Search.invar_recovery H B D N s ==>
      Blossom_Path_Recovery_Buffer_Refinement.recovery_ready task_cap output_cap output_invar K link_invar
        link_update hierarchy_children H (recovery_range H R C) base_lookup link_lookup D N
        (%J target b. Search.invar_route_cache H J & b : hierarchy_ids H & target : hierarchy_members H b) s"
    "!!s. [| Search.invar_recovery H B D N s; Search.Recovery.Blossom_Path_Recovery_call_1_conds s |] ==>
      Search.invar_recovery H B D N (Search.Recovery.Blossom_Path_Recovery_upd1 H B D N s)"
    "Search.result_path (Contraction.Quadratic_Blossom_Search_upd6 state) T0 out0 =
      Search.Recovery.Blossom_Path_Recovery H B D N
        (Search.Recovery.initial_recovery ps es [] (qbs_hints state) out0)"
  unfolding H_def B_def D_def N_def ps_def es_def
proof-
  let ?s6 = "Contraction.Quadratic_Blossom_Search_upd6 state"
    and ?H = "qbs_hierarchy state" and ?B = "qbs_cycle_edges state" and ?D = "qbs_bases state"
    and ?N = "qbs_parents state" and ?J = "qbs_hints state"
  let ?ps = "Contraction.augmenting_view P plen Q qlen"
    and ?es = "Contraction.outward_edges (Contraction.Quadratic_Blossom_Search_upd4 state)
      (Contraction.Paths.buffer_view P 0 plen True) @ [(qbs_current state, Contraction.scanned_neighbour state)] @
      Contraction.rootward_edges (Contraction.Quadratic_Blossom_Search_upd4 state)
        (Contraction.Paths.buffer_view Q 0 qlen False)"
  note facts = found_path_facts[OF assms(1) assms(2) assms(3)]
  show "set ?ps <= K" "0 < plen" "0 < qlen" "plen <= path_cap" "qlen <= path_cap"
    by (rule facts(10,8,9,6,7))+
  have inv6: "Search.invar_search ?s6"
    by (rule Search.invar_search_holds_6[OF assms(1) assms(2)])
  note status = found_status[of state, folded facts(1,2)]
  have "Search.invar_recovering_structure ?H ?B ?D ?N" "hierarchy_ids ?H <= K"
    "Contraction.invar_matching_projection ?s6"
    using assms(2) inv6
    by (auto elim!: Search.invar_search_props Contraction.invar_representatives_props)
  hence tree: "Search.recovery_tree ?H" "Search.invar_navigation ?H ?D ?N" "hierarchy_ids ?H <= K"
    "Contraction.invar_matching_projection ?s6"
    by (simp_all add: Search.invar_recovering_structure_def)
  thus "Search.recovery_tree ?H" "Search.invar_navigation ?H ?D ?N" "hierarchy_ids ?H <= K"
    by simp_all
  show dom: "Search.Recovery.Blossom_Path_Recovery_dom ?H ?B ?D ?N (Search.Recovery.initial_recovery ?ps ?es [] ?J out0)"
    using Search.result_path_properties(1)[OF inv6 status]
    by (simp add: found_fields initial_tasks_empty facts(3))
  show "Search.invar_recovery ?H ?B ?D ?N (Search.Recovery.initial_recovery ?ps ?es [] ?J out0)"
    using Search.initial_recovery_full[OF Search.search_recovery_precond[OF inv6 status] status tree(4)]
    by (simp add: found_fields initial_tasks_empty facts(3))
  have "card V0 = length vs"
    using distinct_card[OF Search.input_props(1)] Search.input_props(2)
    by simp
  hence space: "card V0 <= output_cap" "Suc (card (hierarchy_ids ?H)) <= task_cap"
    using Search.initial_workspaces(4) Search.search_recovery_capacity[OF assms(2)]
    by simp_all
  note inst = recovery_instance[OF tree(1-3) refl refl facts(10) facts(8,9) facts(6,7),
    where s = "Contraction.Quadratic_Blossom_Search_upd4 state" and u = "qbs_current state"
      and v = "Contraction.scanned_neighbour state" and B = ?B and R = R and C = C, unfolded found_fields(6)]
  have nil: "nil ~: V0" "finite V0"
    using Search.input_props(2-4)
    by (auto simp flip: Search.input_props(2))
  show "Blossom_Path_Recovery_Buffer_Refinement.recovery_ready task_cap output_cap output_invar K link_invar
      link_update hierarchy_children ?H (recovery_range ?H R C) base_lookup link_lookup ?D ?N
      (%J target b. Search.invar_route_cache ?H J & b : hierarchy_ids ?H & target : hierarchy_members ?H b) s"
    if rec: "Search.invar_recovery ?H ?B ?D ?N s" for s
  proof-
    note common = Search.recovery_register_ready[OF rec space(2)]
    show ?thesis
    proof(cases "qbr_tasks s")
      case Nil
      thus ?thesis
        using common Search.recovery_next_component_key[OF rec tree(3)]
        by (simp add: Blossom_Path_Recovery_Buffer_Refinement.recovery_ready_def[OF inst])
    next
      case (Cons task ts)
      show ?thesis
      proof(cases task)
        case (Quadratic_Visit b a z)
        note visit = Search.recovery_visit_ready[OF rec _ _ tree(3) nil(1), of b a z]
        have emit_space: "a = z ==> qbr_length s < output_cap"
          using Search.recovery_stack_output_space[OF rec _ nil(2) space(1)] Cons
          by simp
        show ?thesis
          using common Cons Quadratic_Visit visit emit_space recovery_range_exists[OF assms(4), of b]
          by (auto simp: Blossom_Path_Recovery_Buffer_Refinement.recovery_ready_def[OF inst]
            Search.visit_target_def Let_def)
      next
        case (Quadratic_Cycle b i j forward a z)
        thus ?thesis
          using common Cons Search.recovery_cycle_ready[OF rec _ _ tree(3), of b i j forward a z]
          by (simp add: Blossom_Path_Recovery_Buffer_Refinement.recovery_ready_def[OF inst])
      qed
    qed
  qed
  show "Search.invar_recovery ?H ?B ?D ?N (Search.Recovery.Blossom_Path_Recovery_upd1 ?H ?B ?D ?N s)"
    if "Search.invar_recovery ?H ?B ?D ?N s" "Search.Recovery.Blossom_Path_Recovery_call_1_conds s" for s
    by (rule Search.invar_recovery_holds_1[OF that tree(3) space])
  show "Search.result_path ?s6 T0 out0 =
    Search.Recovery.Blossom_Path_Recovery ?H ?B ?D ?N (Search.Recovery.initial_recovery ?ps ?es [] ?J out0)"
    using dom
    by (simp add: Search.result_path_def status Search.Recovery.lift_path_def found_fields initial_tasks_empty
      Search.Recovery.Blossom_Path_Recovery_impl_same facts(3))
qed
context
  assumes recover_path_into_def: "\<And>Wi Bi u v plen qlen.
    recover_path_into Wi Bi u v plen qlen = Recovery_Ops.recover_into Wi Bi plen qlen u v"
begin
lemma recover_core_refine:
  assumes  "Contraction.Quadratic_Blossom_Search_call_6_conds state" and  "Search.invar_search state"
    and  "paths_result (qbs_forest state) (qbs_component state) (Contraction.target_component state)
      (last (forest_path (qbs_forest state) (qbs_component state)) =
        last (forest_path (qbs_forest state) (Contraction.target_component state)), plen, qlen) P Q"
    and  "Packed.packed_hierarchy (qbs_hierarchy state) R C used"
  shows "<recovery_structure (qbs_cycle_edges state) (qbs_bases state) (qbs_parents state) R C (qbs_forest_edges state) P Q Wi *
      task_storage Wi * link_assn (qbs_hints state) (get_hints Wi) * output_assn out0 Bi>
    recover_path_into Wi Bi (qbs_current state) (Contraction.scanned_neighbour state) plen qlen
    <\<lambda>k. recovery_structure (qbs_cycle_edges state) (qbs_bases state) (qbs_parents state) R C (qbs_forest_edges state) P Q Wi *
      task_storage Wi *
      link_assn (qbr_hints (Search.result_path (Contraction.Quadratic_Blossom_Search_upd6 state) T0 out0)) (get_hints Wi) *
      output_assn (qbr_output (Search.result_path (Contraction.Quadratic_Blossom_Search_upd6 state) T0 out0)) Bi *
      \<up>(k = qbr_length (Search.result_path (Contraction.Quadratic_Blossom_Search_upd6 state) T0 out0))>"
proof-
  note recovery = recovery_setup[OF assms(1) assms(2) assms(3) assms(4)]
  note inst = recovery_instance[OF recovery(1-3) refl refl recovery(4-8),
    where s = "Contraction.Quadratic_Blossom_Search_upd4 state" and u = "qbs_current state"
      and v = "Contraction.scanned_neighbour state" and B = "qbs_cycle_edges state" and R = R and C = C,
    unfolded found_fields(6)]
  note rule = Blossom_Path_Recovery_Buffer_Refinement.recover_into_refine[OF inst recovery(9-12), where Wi = Wi and Bi = Bi]
  have stack_in: "task_storage Wi \<Longrightarrow>\<^sub>A recovery_stack (qbs_hierarchy state) R C [] Wi"
    unfolding task_storage_def recovery_stack_def Quadratic_Cycle_Stack.cycle_stack_assn_def[OF recovery_slots]
    by (sep_auto simp: Quadratic_Cycle_Stack.cycle_stack_invar_def[OF recovery_slots])
  have stack_out: "recovery_stack (qbs_hierarchy state) R C ts Wi \<Longrightarrow>\<^sub>A task_storage Wi" for ts
    unfolding task_storage_def recovery_stack_def Quadratic_Cycle_Stack.cycle_stack_assn_def[OF recovery_slots]
    by (sep_auto simp: Quadratic_Cycle_Stack.cycle_stack_invar_def[OF recovery_slots])
  show ?thesis
    unfolding recover_path_into_def recovery(13)
    by (rule ht_cons_post_prec[OF ht_cons_pre[OF _ rule]], intro ent_star_mono ent_refl stack_in, assumption+,
      unfold Blossom_Path_Recovery_Buffer_Refinement.recovery_result_def[OF inst]
        Blossom_Path_Recovery_Buffer_Refinement.recovery_storage_def[OF inst],
      intro ent_star_mono ent_refl stack_out)
qed

context
  assumes forest_release: "\<And>F Fi. forest_assn F Fi \<Longrightarrow>\<^sub>A forest_workspace_assn Fi"
begin

lemma recover_refine:
  assumes  "Contraction.Quadratic_Blossom_Search_call_6_conds state" and  "Search.invar_search state"
  shows "<search_paths_assn state it h t fresh used plen qlen Gi Mi Wi Bi>
    recover_path_into Wi Bi (qbs_current state) (Contraction.scanned_neighbour state) plen qlen
    <\<lambda>k. \<exists>\<^sub>Axs. search_output_assn xs Gi Mi Wi Bi * \<up>(length xs = output_cap \<and> k \<le> output_cap \<and>
      take k xs = Search.Recovery.recovered_path (Search.result_path (Contraction.Quadratic_Blossom_Search_upd6 state) T0 out0))>"
proof-
  note result = found_result_invar[OF assms(1) assms(2)]
  have adts: "uf_invar (qbs_components state)" "owner_invar (qbs_owners state)" "edge_invar (qbs_forest_edges state)"
    "edge_invar (qbs_cycle_edges state)" "link_invar (qbs_parents state)" "base_invar (qbs_bases state)"
    using assms(2)
    by (auto elim!: Search.invar_search_props Contraction.invar_adts_props
      Search.invar_recovering_structure_props Search.invar_navigation_props)
  have inst: "<recovery_structure (qbs_cycle_edges state) (qbs_bases state) (qbs_parents state) R C (qbs_forest_edges state) P Q Wi *
      task_storage Wi * link_assn (qbs_hints state) (get_hints Wi) * output_assn out0 Bi *
      (graph_storage Gi * matching_assn M0 Mi * forest_assn (qbs_forest state) (get_forest Wi) *
       uf_assn (qbs_components state) (get_union_find Wi) * owner_assn (qbs_owners state) (get_owners Wi) *
       frontier_assn T (get_frontier Wi) * marks_assn tag (get_marks Wi) (get_positions Wi))>
    recover_path_into Wi Bi (qbs_current state) (Contraction.scanned_neighbour state) plen qlen
    <\<lambda>k. \<exists>\<^sub>Axs. search_output_assn xs Gi Mi Wi Bi * \<up>(length xs = output_cap \<and> k \<le> output_cap \<and>
      take k xs = Search.Recovery.recovered_path (Search.result_path (Contraction.Quadratic_Blossom_Search_upd6 state) T0 out0))>"
    if paths: "paths_result (qbs_forest state) (qbs_component state) (Contraction.target_component state)
      (last (forest_path (qbs_forest state) (qbs_component state)) =
        last (forest_path (qbs_forest state) (Contraction.target_component state)), plen, qlen) P Q"
      and packed: "Packed.packed_hierarchy (qbs_hierarchy state) R C used" and frontier: "frontier_invar T"
    for P Q T R C tag
    by (rule ht_cons_post[OF ht_frame[OF recover_core_refine[OF assms(1) assms(2) paths packed]]],
      unfold recovery_structure_def search_output_assn_def reusable_storage_def,
      sep_frame_fwd rule: forest_release, insert result adts frontier,
      sep_auto simp: Search.Recovery.recovered_path_def take_map)
  show ?thesis
    unfolding search_paths_assn_def buffer_storage_def state_storage_def
    using adts
    by (sep_auto heap: inst[unfolded recovery_structure_def] simp: paths_result_def Packed.packed_hierarchy_def)
qed

end

end
end

section "The generic search refinement"

text "The remaining assumptions are contracts of the basic operations: read-only finds,
  graph row iteration, the paired forest-path query, the recovery and reset operations,
  the release of the forest storage, and the capacities."

locale Cubic_Blossom_Refinement_Contracts = Cubic_Blossom_Paths +
  assumes key_bounds: "finite K" "card K \<le> pool_cap"
    and recover_path_into_def: "\<And>Wi Bi u v plen qlen.
      recover_path_into Wi Bi u v plen qlen = Recovery_Ops.recover_into Wi Bi plen qlen u v"
    and forest_release: "\<And>F Fi. forest_assn F Fi \<Longrightarrow>\<^sub>A forest_workspace_assn Fi"
    and vertex_order: "map vertex_at [0..<n] = vs"
    and fresh_names: "first_fresh \<le> fresh_limit" "queue_abstract fresh0 = map fresh_vertex [first_fresh..<fresh_limit]"
    and reset_components_rule: "\<And>U Ui. uf_invar U \<Longrightarrow>
      <uf_assn U Ui> reset_components_into Ui <\<lambda>_. uf_assn (uf_reset U) Ui>"
    and clear_marks_rule: "\<And>tag Ai Ii.
      <marks_assn tag Ai Ii> clear_marks_into Ai <\<lambda>_. marks_assn (Suc 0) Ai Ii>"
begin

lemma scanning_target_key:
  assumes "Contraction.scanning_edge state" "Search.invar_search state"
  shows "Contraction.target_component state \<in> K"
proof-
  have invars: "Contraction.invar_adts state" "Contraction.invar_queue state" "Contraction.invar_neighbours state"
    "Contraction.invar_representatives state" "hierarchy_invar (qbs_hierarchy state)"
    using assms(2)
    by (auto elim!: Search.invar_search_props Search.invar_recovering_structure_props)
  show ?thesis
    using Search.scanning_target_correct(1)[OF assms(1) invars(1-3)] Search.scanning_neighbour(1)[OF assms(1) invars(1-3)]
      Search.active_ids_subset[OF invars(5)] invars(4)
    by (auto elim!: Contraction.invar_representatives_props)
qed

sublocale Search_Ref: Quadratic_Blossom_Search_Buffer_Refinement
  where task_invar = "\<lambda>xs. length xs \<le> task_cap" and task_abstract = id and task_empty = "[]"
    and task_push = "\<lambda>xs x. x # xs" and task_pop = tl and task_top = hd and task_is_empty = "\<lambda>xs. xs = []"
    and initialise_into = initialise_into and recover_into = recover_path_into
    and frontier_read = "\<lambda>Wi. frontier_lookup_imp (get_frontier Wi)" and representative_imp = representative_into
    and classify = "\<lambda>Wi. forest_classify_imp (get_forest Wi)" and mate_read = mate_read_imp
    and extend_into = extend_search_into and paths_into = query_paths_into and contract_into = contract_search_into
    and registers = registers and workspace_assn = workspace_assn and paths_assn = search_paths_assn
    and input_assn = search_input_assn and output_assn = search_output_assn
  by (intro_locales, unfold_locales, (rule register_queue, assumption), (rule register_cursor_refine, assumption+),
    (rule initialise_refine[OF vertex_order fresh_names reset_components_rule clear_marks_rule], assumption),
    (rule exhausted_refine[OF forest_release], assumption), (rule frontier_read_rule, assumption+),
    (rule representative_rule, assumption+), (rule row_begin_refine, assumption+),
    (rule row_finished_refine, assumption), (rule row_read_refine, assumption+),
    (rule classify_rule, assumption, rule scanning_target_key, assumption+),
    (rule skipped_edge_refine, assumption+), (rule mate_read_rule, assumption), (rule extend_refine, assumption+),
    (rule paths_refine, assumption+), (rule contract_refine[OF key_bounds], assumption+),
    rule recover_refine[OF recover_path_into_def forest_release], assumption+)

text "The search theorem with the input and output assertions unfolded. Apart from the matching
  and the workspace models it only mentions constants that do not depend on them."

lemma search_into_storage:
  "<graph_storage Gi * matching_assn M0 Mi * task_storage Wi * output_assn out0 Bi *
      forest_workspace_assn (get_forest Wi) * uf_assn U0 (get_union_find Wi) *
      owner_assn L0 (get_owners Wi) * edge_assn P0 (get_forest_edges Wi) * edge_assn B0 (get_cycle_edges Wi) *
      link_assn N0 (get_navigation Wi) * base_assn D0 (get_bases Wi) * link_assn J0 (get_hints Wi) *
      (\<exists>\<^sub>AT R C P Q tag. frontier_assn T (get_frontier Wi) * header_assn R (get_headers Wi) *
        pool_assn C (get_pool Wi) * path_assn P (get_left Wi) * path_assn Q (get_right Wi) *
        marks_assn tag (get_marks Wi) (get_positions Wi) *
        \<up>(frontier_invar T \<and> header_invar R \<and> pool_invar C \<and> path_invar P \<and> path_invar Q))>
    Runtime.search_into Gi Mi Wi Bi
    <\<lambda>k. \<exists>\<^sub>Axs. graph_storage Gi * matching_assn M0 Mi * task_storage Wi * reusable_storage Wi *
      (\<exists>\<^sub>Aout. output_assn out Bi * \<up>(output_invar out \<and> xs = map (output_lookup out) [0..<output_cap])) *
      \<up>(length xs = output_cap \<and> k \<le> output_cap \<and>
        (if k = 0 then \<nexists>p. graph_augmenting_path Contraction.input_graph (mate_abstract M0) p
         else graph_augmenting_path Contraction.input_graph (mate_abstract M0) (take k xs)))>"
  using Search_Ref.search_into_correct unfolding search_input_assn_def search_output_assn_def .

end

section "The maximum-matching loop"

text "The search is proved for one matching and one set of workspace models. The loop needs it
  for every valid matching and for whatever valid contents the reused workspace holds, so the
  contracts are assumed for all of them. The concrete instantiation discharges this assumption."

locale Cubic_Blossom_Matching = Cubic_Blossom_Refinement_Contracts +
  fixes augment_prefix :: "_ \<Rightarrow> _ \<Rightarrow> nat \<Rightarrow> unit Heap"
  assumes instances: "\<And>M U L P B D N J out.
    \<lbrakk>mate_invar Contraction.input_graph M; uf_invar U; owner_invar L; edge_invar P; edge_invar B;
      base_invar D; link_invar N; link_invar J; output_invar out\<rbrakk> \<Longrightarrow>
    Cubic_Blossom_Refinement_Contracts
      V0 nil graph_lookup adj_insert adj_isin adj_abstract adj_choose adj_empty adj_delete adj_invar
      graph_invar fset_invar fset_abstract fset_empty fset_insert fset_delete fset_isin forest_evens
      forest_odds forest_roots forest_path forest_abstract forest_invar forest_empty forest_extend
      forest_contract mate_empty mate_invar mate_partner mate_augment mate_abstract mate_contract
      mate_expand mate_add hierarchy_ids hierarchy_tops hierarchy_universe hierarchy_members
      hierarchy_invar hierarchy_abstract hierarchy_compound hierarchy_edges hierarchy_merge
      hierarchy_children cap queue_invar queue_abstract queue_empty queue_push queue_pop queue_is_empty
      uf_invar uf_representative uf_find uf_union uf_reset owner_invar owner_update owner_lookup
      edge_invar edge_update edge_lookup cursor_abstract cursor_iterated cursor_remaining
      cursor_current cursor_has cursor_move cursor_reset base_invar base_update base_lookup link_invar
      link_update link_lookup G vs M edge_update_imp edge_lookup_imp frontier_invar frontier_update
      frontier_lookup frontier_update_imp frontier_lookup_imp forest_extend_imp link_update_imp
      link_lookup_imp owner_update_imp owner_lookup_imp pool_cap pool_invar pool_update pool_lookup
      pool_update_imp pool_lookup_imp path_cap path_invar path_update path_lookup path_update_imp
      path_lookup_imp uf_union_imp uf_find_imp forest_classify_imp base_update_imp base_lookup_imp
      header_invar header_update header_lookup header_update_imp header_lookup_imp forest_contract_into
      vertex_at forest_workspace_assn matching_assn mate_read_imp forest_clear_into forest_root_into
      forest_assn uf_assn owner_assn edge_assn frontier_assn link_assn base_assn header_assn pool_assn
      path_assn n get_forest_edges get_cycle_edges get_navigation get_bases get_hints get_headers
      get_pool get_left get_right reset_components_into clear_marks_into forest_paths_into row_has
      row_read row_advance first_fresh fresh_vertex task_cap output_cap output_update output_lookup U L
      C0 H0 P B D N J fresh0 T0 out K row_begin recover_path_into cursor_invar output_invar slot_invar
      slot_update slot_lookup slot_assn slot_update_imp slot_lookup_imp output_assn output_update_imp
      output_lookup_imp graph_storage marks_assn get_tasks cursor_register fresh_limit"
    and augment_prefix_rule: "\<And>M Mi Bi k out.
    \<lbrakk>mate_invar Contraction.input_graph M;
      graph_augmenting_path Contraction.input_graph (mate_abstract M) (take k (map (output_lookup out) [0..<output_cap]));
      k \<le> output_cap; output_invar out\<rbrakk> \<Longrightarrow>
    <matching_assn M Mi * output_assn out Bi> augment_prefix Mi Bi k
    <\<lambda>_. matching_assn (mate_augment M (take k (map (output_lookup out) [0..<output_cap]))) Mi * output_assn out Bi>"
begin

definition "matching_buffer xs Bi = (\<exists>\<^sub>Aout. output_assn out Bi *
  \<up>(output_invar out \<and> xs = map (output_lookup out) [0..<output_cap]))"

definition "matching_storage Wi = task_storage Wi * reusable_storage Wi"

lemma search_instance:
  assumes "mate_invar Contraction.input_graph M" "uf_invar U" "owner_invar L" "edge_invar P" "edge_invar B"
    "base_invar D" "link_invar N" "link_invar J" "output_invar out"
  shows "<graph_storage Gi * matching_assn M Mi * task_storage Wi * output_assn out Bi *
      forest_workspace_assn (get_forest Wi) * uf_assn U (get_union_find Wi) *
      owner_assn L (get_owners Wi) * edge_assn P (get_forest_edges Wi) * edge_assn B (get_cycle_edges Wi) *
      link_assn N (get_navigation Wi) * base_assn D (get_bases Wi) * link_assn J (get_hints Wi) *
      (\<exists>\<^sub>AT R C P Q tag. frontier_assn T (get_frontier Wi) * header_assn R (get_headers Wi) *
        pool_assn C (get_pool Wi) * path_assn P (get_left Wi) * path_assn Q (get_right Wi) *
        marks_assn tag (get_marks Wi) (get_positions Wi) *
        \<up>(frontier_invar T \<and> header_invar R \<and> pool_invar C \<and> path_invar P \<and> path_invar Q))>
    Runtime.search_into Gi Mi Wi Bi
    <\<lambda>k. \<exists>\<^sub>Axs. graph_storage Gi * matching_assn M Mi * task_storage Wi * reusable_storage Wi *
      (\<exists>\<^sub>Aout. output_assn out Bi * \<up>(output_invar out \<and> xs = map (output_lookup out) [0..<output_cap])) *
      \<up>(length xs = output_cap \<and> k \<le> output_cap \<and>
        (if k = 0 then \<nexists>p. graph_augmenting_path Contraction.input_graph (mate_abstract M) p
         else graph_augmenting_path Contraction.input_graph (mate_abstract M) (take k xs)))>"
  by (rule Cubic_Blossom_Refinement_Contracts.search_into_storage[OF instances[OF assms]])
lemma search_for_matching:
  assumes  "mate_invar Contraction.input_graph M"
  shows "<graph_storage Gi * matching_assn M Mi * matching_storage Wi * matching_buffer xs Bi>
    Runtime.search_into Gi Mi Wi Bi
    <\<lambda>k. \<exists>\<^sub>Ays. graph_storage Gi * matching_assn M Mi * matching_storage Wi * matching_buffer ys Bi *
      \<up>(length ys = output_cap \<and> k \<le> output_cap \<and>
        (if k = 0 then \<nexists>p. graph_augmenting_path Contraction.input_graph (mate_abstract M) p
         else graph_augmenting_path Contraction.input_graph (mate_abstract M) (take k ys)))>"
  using assms
  unfolding matching_storage_def matching_buffer_def reusable_storage_def
  by (sep_auto heap: search_instance[unfolded reusable_storage_def])
lemma input_graph_valid:
  "dblton_graph Contraction.input_graph \<and> finite (Vs Contraction.input_graph)"
  "Vs Contraction.input_graph \<subseteq> K"
  using finite_subset[OF Search.input_graph_props(1) Search.initial_finite(1)] Search.input_graph_props(2)
    order_trans[OF Search.input_graph_props(1) Search.input_props(3)]
  by simp_all

sublocale Loop: Find_Max_Matching_Buffer_Refinement
  where K = K and nil = nil and empty_matching = mate_empty and matching_invar = mate_invar
    and lookup_partner = "\<lambda>M v. if v \<in> K \<and> mate_partner M v \<noteq> nil then Some (mate_partner M v) else None"
    and get_partner = mate_partner and augment = mate_augment and matching_abstract = mate_abstract
    and contract_path = mate_contract and expand_path_at_matched = mate_expand and add_alternatingly = mate_add
    and search_into = Runtime.search_into and augment_prefix = augment_prefix and E = Contraction.input_graph
    and graph_assn = graph_storage and matching_assn = matching_assn and workspace_assn = matching_storage
    and buffer_assn = matching_buffer and capacity = output_cap
by (intro_locales, unfold_locales, (rule input_graph_valid)+,
    rule search_for_matching, assumption,
    unfold matching_buffer_def, sep_auto heap: augment_prefix_rule)
theorem matching_into_correct:
  "<graph_storage Gi * matching_assn mate_empty Mi * matching_storage Wi * matching_buffer xs Bi *
      \<up>(length xs = output_cap)>
    matching_into augment_prefix Gi Mi Wi Bi
    <\<lambda>_. \<exists>\<^sub>AN ys. graph_storage Gi * matching_assn N Mi * matching_storage Wi * matching_buffer ys Bi *
      \<up>(mate_invar Contraction.input_graph N \<and> max_card_matching Contraction.input_graph (mate_abstract N))>"
  unfolding matching_into_def
  by (rule ht_cons_prec[rotated 2, OF Loop.matching_run_correct]) (sep_auto simp: Loop.matching_workspace_def)+

end

end
