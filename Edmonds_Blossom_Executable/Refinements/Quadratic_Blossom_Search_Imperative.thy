theory Quadratic_Blossom_Search_Imperative
  imports
    Blossom_Executable.Quadratic_Blossom_Search_Preservation
    Blossom_Executable.Find_Max_Matching
    Basic_Matching.Matching_Augmentation_Imperative
    Data_Structures.Bounded_Stack_Specs_Imp
    Data_Structures.Bounded_Queue_Specs_Imp
begin

provenance ai_human

section "Erasing the contracted matching"

context Quadratic_Blossom_Search_thms
begin

lemma extension_partner_input:
  "\<lbrakk>Quadratic_Blossom_Search_call_5_conds state; invar_search state\<rbrakk> \<Longrightarrow>
    mate_partner (qbs_matching state) (target_component state) = mate_partner M0 (scanned_neighbour state)"
proof-
  assume call: "Quadratic_Blossom_Search_call_5_conds state" and inv: "invar_search state"
  have "{target_component state, mate_partner (qbs_matching state) (target_component state)} \<in> mate_abstract M0"
    using call inv extension_precond[of state] extension_partner_vertices[of state] extension_target[of state]
    by (auto elim!: invar_search_props intro!: non_even_matching_edge simp: Forest.forest_extension_precond_def)
  thus ?thesis
    using extension_original_vertices(1)[OF call inv]
      Mate.lookup_partner[of input_graph M0 "target_component state" "mate_partner (qbs_matching state) (target_component state)"]
    by (auto split: if_splits)
qed

end

section "Recovering routes through the hierarchy"

locale Blossom_Path_Recovery_Imperative =
  Blossom_Path_Recovery where K = K and link_invar = link_invar
    and link_update = link_update and link_lookup = link_lookup +
  Links: fixed_univ_map_imp K link_invar link_update link_lookup id
    link_assn link_update_imp link_lookup_imp
  for K :: "'v::heap set" and link_invar :: "'links \<Rightarrow> bool"
    and link_update :: "'links \<Rightarrow> 'v \<Rightarrow> ('v \<times> nat) \<Rightarrow> 'links"
    and link_lookup :: "'links \<Rightarrow> 'v \<Rightarrow> ('v \<times> nat)"
    and link_assn :: "'links \<Rightarrow> 'li \<Rightarrow> assn"
    and link_update_imp :: "'li \<Rightarrow> 'v \<Rightarrow> ('v \<times> nat) \<Rightarrow> unit Heap"
    and link_lookup_imp :: "'li \<Rightarrow> 'v \<Rightarrow> ('v \<times> nat) Heap"
begin

partial_function (heap) cache_loop :: "'li \<Rightarrow> 'li \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> unit Heap" where
  "cache_loop Ni Ji target b v =
    (if v = b then return () else do {
      pi \<leftarrow> link_lookup_imp Ni v;
      link_update_imp Ji (fst pi) (target, snd pi);
      cache_loop Ni Ji target b (fst pi) })"

definition "cache_into Ni Ji target b = do {
  ai \<leftarrow> link_lookup_imp Ji b;
  if fst ai = target then return () else cache_loop Ni Ji target b target }"

lemma cache_loop_refine:
  assumes "Cache_Route_dom N target b state" "I state"
    and  "\<And>s. \<lbrakk> I s; cache_current s \<noteq> b \<rbrakk> \<Longrightarrow>
      link_invar N \<and> link_invar (cache_hints s) \<and> cache_current s \<in> K &
      fst (link_lookup N (cache_current s)) \<in> K \<and> I (Cache_Route_upd1 N target s)"
  shows "<link_assn N Ni * link_assn (cache_hints state) Ji>
    cache_loop Ni Ji target b (cache_current state)
    <\<lambda>_. link_assn N Ni * link_assn (cache_hints (Cache_Route N target b state)) Ji>"
  using assms(2)
proof(induction rule: Cache_Route_induct[OF assms(1)])
  case IH: (1 state)
  show ?case
    using assms(3)[OF IH.prems] IH.prems
    by (subst cache_loop.simps)
      (sep_auto heap: IH.IH[unfolded Cache_Route_call_1_conds_def Cache_Route_upd1_def Let_def case_prod_beta, simplified] simp: Cache_Route.psimps[OF IH.hyps]
        Cache_Route_call_1_conds_def Cache_Route_upd1_def Cache_Route_ret1_def
        Let_def case_prod_beta split: if_splits)
qed

lemma cache_into_refine:
  assumes "link_invar J" "b \<in> K"
    "Cache_Route_dom N target b \<lparr>cache_current = target, cache_hints = J\<rparr>"
    "I \<lparr>cache_current = target, cache_hints = J\<rparr>"
    and  "\<And>s. \<lbrakk> I s; cache_current s \<noteq> b \<rbrakk> \<Longrightarrow>
      link_invar N \<and> link_invar (cache_hints s) \<and> cache_current s \<in> K &
      fst (link_lookup N (cache_current s)) \<in> K \<and> I (Cache_Route_upd1 N target s)"
  shows "<link_assn N Ni * link_assn J Ji> cache_into Ni Ji target b
    <\<lambda>_. link_assn N Ni * link_assn (cache_route N target b J) Ji>"
  using assms(1,2)
  unfolding cache_into_def cache_route_def Cache_Route_impl_same[OF assms(3)]
  by (sep_auto heap: cache_loop_refine[OF assms(3,4,5), simplified])
end

context Quadratic_Blossom_Search_Lifting begin
lemma cache_refinement_ready:
  "\<lbrakk> recovery_tree H; invar_navigation H D N; hierarchy_ids H \<subseteq> K;
    invar_cache_route H b target state; cache_current state \<noteq> b \<rbrakk> \<Longrightarrow>
    link_invar N \<and> link_invar (cache_hints state) \<and> cache_current state \<in> K &
    fst (link_lookup N (cache_current state)) \<in> K &
    invar_cache_route H b target (Recovery.Cache_Route_upd1 N target state)"
  using invar_cache_route_holds_1[of H D N b state target]
    cache_route_next(2)[of H D N b state target]
  by (auto simp: invar_navigation_def invar_cache_route_def invar_route_cache_def
    route_ancestors_def Recovery.Cache_Route_call_1_conds_def)
end

section "Views of caller-owned buffers"

locale Quadratic_Blossom_Search_Path_Buffer =
  Buffer: fixed_univ_map_imp "{..<capacity}" buffer_invar buffer_update buffer_lookup id
    buffer_assn buffer_update_imp buffer_lookup_imp
  for capacity :: nat and buffer_invar :: "'buffer \<Rightarrow> bool"
    and buffer_update :: "'buffer \<Rightarrow> nat \<Rightarrow> 'v::heap \<Rightarrow> 'buffer"
    and buffer_lookup :: "'buffer \<Rightarrow> nat \<Rightarrow> 'v"
    and buffer_assn :: "'buffer \<Rightarrow> 'bi \<Rightarrow> assn"
    and buffer_update_imp :: "'bi \<Rightarrow> nat \<Rightarrow> 'v \<Rightarrow> unit Heap"
    and buffer_lookup_imp :: "'bi \<Rightarrow> nat \<Rightarrow> 'v Heap"
begin

definition "buffer_view B a n backward =
  (let xs = map (buffer_lookup B) [a..<a + n] in if backward then rev xs else xs)"

definition "view_read Bi a n backward i =
  buffer_lookup_imp Bi (a + (if backward then n - Suc i else i))"

lemma view_length[simp]: "length (buffer_view B a n backward) = n"
  by (simp add: buffer_view_def Let_def)

lemma view_nth:
  "i < n \<Longrightarrow> buffer_view B a n backward ! i =
    buffer_lookup B (a + (if backward then n - Suc i else i))"
  by (auto simp: buffer_view_def Let_def rev_nth)

lemma view_slice:
  "a+n \<le> m \<Longrightarrow> buffer_view B a n False = take n (drop a (buffer_view B 0 m False))"
  by (simp add: buffer_view_def drop_map take_map)

lemma appended_view:
  "buffer_view B' 0 (used + length xs) False = buffer_view B 0 used False @ xs \<Longrightarrow>
    buffer_view B' used (length xs) False = xs"
  by (drule arg_cong[where f = "drop used"])
    (simp add: buffer_view_def drop_map)

lemma preserved_view:
  "\<lbrakk>buffer_view B' 0 (used + length xs) False = buffer_view B 0 used False @ xs; a+n \<le> used\<rbrakk>
    \<Longrightarrow> buffer_view B' a n False = buffer_view B a n False"
proof-
  assume extended: "buffer_view B' 0 (used + length xs) False = buffer_view B 0 used False @ xs"
    and range: "a+n \<le> used"
  have "buffer_view B' 0 used False = buffer_view B 0 used False"
    using arg_cong[OF extended, where f = "take used"]
    by (simp add: buffer_view_def take_map)
  thus ?thesis
    by (simp only: view_slice[OF range])
qed


lemma view_read_rule:
  "\<lbrakk> buffer_invar B; a + n <= capacity; i < n \<rbrakk> \<Longrightarrow>
    <buffer_assn B Bi> view_read Bi a n backward i
    <\<lambda>v. buffer_assn B Bi * \<up>(v = buffer_view B a n backward ! i)>"
  unfolding view_read_def
  by (sep_auto simp: view_nth)

definition "joined_read Bi a n backward Ci a' n' backward' i =
  (if i < n then view_read Bi a n backward i else view_read Ci a' n' backward' (i - n))"

lemma joined_read_rule:
  "\<lbrakk> buffer_invar P; buffer_invar Q; a + n <= capacity; a' + n' <= capacity; i < n + n' \<rbrakk> \<Longrightarrow>
    <buffer_assn P Bi * buffer_assn Q Ci> joined_read Bi a n backward Ci a' n' backward' i
    <\<lambda>v. buffer_assn P Bi * buffer_assn Q Ci *
      \<up>(v = (buffer_view P a n backward @ buffer_view Q a' n' backward') ! i)>"
  unfolding joined_read_def
  by (sep_auto heap: view_read_rule simp: nth_append)

lemma append_prefix:
  "\<lbrakk> buffer_invar B; k < capacity \<rbrakk> \<Longrightarrow>
    buffer_view (buffer_update B k v) 0 (Suc k) False = buffer_view B 0 k False @ [v]"
  by (auto simp: buffer_view_def Let_def upt_Suc_append Buffer.fixed_univ_map_upd intro!: map_cong)

lemma append_prefix_rule:
  "\<lbrakk> buffer_invar B; k < capacity \<rbrakk> \<Longrightarrow>
    <buffer_assn B Bi> buffer_update_imp Bi k v
    <\<lambda>_. buffer_assn (buffer_update B k v) Bi *
      \<up>(buffer_view (buffer_update B k v) 0 (Suc k) False = buffer_view B 0 k False @ [v])>"
  by (sep_auto simp: append_prefix)

end

section "Packed children of contracted blossoms"

locale Quadratic_Blossom_Search_Packed_Hierarchy =
  Hierarchy: Blossom_Forest_Ordered
    where blossom_forest_invar = hierarchy_invar and all_ids = hierarchy_ids
      and merge = hierarchy_merge and children = hierarchy_children +
  Headers: fixed_univ_map_imp K header_invar header_update header_lookup id
    header_assn header_update_imp header_lookup_imp +
  Pool: Quadratic_Blossom_Search_Path_Buffer capacity pool_invar pool_update pool_lookup
    pool_assn pool_update_imp pool_lookup_imp
  for hierarchy_invar :: "'hierarchy \<Rightarrow> bool"
    and hierarchy_ids :: "'hierarchy \<Rightarrow> 'v::heap set"
    and hierarchy_merge :: "'hierarchy \<Rightarrow> 'v list \<Rightarrow> 'v \<Rightarrow> 'hierarchy"
    and hierarchy_children :: "'hierarchy \<Rightarrow> 'v \<Rightarrow> 'v list"
    and K :: "'v set"
    and header_invar :: "'headers \<Rightarrow> bool"
    and header_update :: "'headers \<Rightarrow> 'v \<Rightarrow> (nat \<times> nat) \<Rightarrow> 'headers"
    and header_lookup :: "'headers \<Rightarrow> 'v \<Rightarrow> (nat \<times> nat)"
    and header_assn :: "'headers \<Rightarrow> 'hi \<Rightarrow> assn"
    and header_update_imp :: "'hi \<Rightarrow> 'v \<Rightarrow> (nat \<times> nat) \<Rightarrow> unit Heap"
    and header_lookup_imp :: "'hi \<Rightarrow> 'v \<Rightarrow> (nat \<times> nat) Heap"
    and capacity :: nat and pool_invar :: "'pool \<Rightarrow> bool"
    and pool_update :: "'pool \<Rightarrow> nat \<Rightarrow> 'v \<Rightarrow> 'pool"
    and pool_lookup :: "'pool \<Rightarrow> nat \<Rightarrow> 'v"
    and pool_assn :: "'pool \<Rightarrow> 'pi \<Rightarrow> assn"
    and pool_update_imp :: "'pi \<Rightarrow> nat \<Rightarrow> 'v \<Rightarrow> unit Heap"
    and pool_lookup_imp :: "'pi \<Rightarrow> nat \<Rightarrow> 'v Heap"
begin

definition "packed_hierarchy H R P used \<longleftrightarrow>
  finite (hierarchy_ids H) \<and> hierarchy_ids H \<subseteq> K \<and>
  header_invar R \<and> pool_invar P \<and> used \<le> capacity \<and>
  used = (\<Sum>b \<in> hierarchy_ids H. length (hierarchy_children H b)) \<and>
  (\<forall>b \<in> hierarchy_ids H. hierarchy_children H b \<noteq> [] \<longrightarrow>
    fst (header_lookup R b) + snd (header_lookup R b) \<le> used \<and>
    Pool.buffer_view P (fst (header_lookup R b)) (snd (header_lookup R b)) False =
      hierarchy_children H b)"

lemmas packed_hierarchy_props =
  packed_hierarchy_def[THEN iffD1, elim_format, unfolded atomize_conjL[symmetric]]

lemma packed_hierarchy_initial:
  "\<lbrakk>finite (hierarchy_ids H); hierarchy_ids H \<subseteq> K;
     header_invar R; pool_invar P; \<And>b. b \<in> hierarchy_ids H \<Longrightarrow> hierarchy_children H b = []\<rbrakk>
   \<Longrightarrow> packed_hierarchy H R P 0"
  by (auto simp: packed_hierarchy_def)

lemma packed_hierarchy_range:
  assumes "packed_hierarchy H R P used" "b \<in> hierarchy_ids H" "hierarchy_children H b \<noteq> []"
  shows "fst (header_lookup R b) + snd (header_lookup R b) \<le> used \<and>
    Pool.buffer_view P (fst (header_lookup R b)) (snd (header_lookup R b)) False = hierarchy_children H b \<and>
    snd (header_lookup R b) = length (hierarchy_children H b)"
using assms
by (fastforce elim!: packed_hierarchy_props dest: arg_cong[where f = length])


lemma packed_header_rule:
  assumes "packed_hierarchy H R P used" "b \<in> hierarchy_ids H" "hierarchy_children H b \<noteq> []"
  shows "<header_assn R Ri> header_lookup_imp Ri b
    <\<lambda>r. header_assn R Ri * \<up>(fst r + snd r \<le> used \<and>
      Pool.buffer_view P (fst r) (snd r) False = hierarchy_children H b \<and>
      snd r = length (hierarchy_children H b))>"
  using assms packed_hierarchy_range[OF assms]
  by (elim packed_hierarchy_props) sep_auto

lemma packed_child_rule:
  "\<lbrakk>pool_invar P; a + n \<le> capacity; i < n;
     Pool.buffer_view P a n False = hierarchy_children H b\<rbrakk>
   \<Longrightarrow> <pool_assn P P_i> pool_lookup_imp P_i (a + i)
     <\<lambda>c. pool_assn P P_i * \<up>(c = hierarchy_children H b ! i)>"
  using Pool.view_read_rule[of P a n i P_i False]
  by (simp add: Pool.view_read_def)

lemma pool_view_unchanged:
  "\<lbrakk>pool_invar P; k < capacity; a + n \<le> k\<rbrakk> \<Longrightarrow>
   Pool.buffer_view (pool_update P k c) a n False = Pool.buffer_view P a n False"
  by (auto simp: Pool.buffer_view_def Let_def Pool.Buffer.fixed_univ_map_upd intro!: map_cong)

lemma pool_view_append:
  "\<lbrakk>pool_invar P; a + n < capacity\<rbrakk> \<Longrightarrow>
   Pool.buffer_view (pool_update P (a + n) c) a (Suc n) False =
     Pool.buffer_view P a n False @ [c]"
  by (auto simp: Pool.buffer_view_def Let_def upt_Suc_append Pool.Buffer.fixed_univ_map_upd intro!: map_cong)

lemma packed_hierarchy_append:
  "\<lbrakk>packed_hierarchy H R P used; used \<le> k; k < capacity\<rbrakk> \<Longrightarrow>
   packed_hierarchy H R (pool_update P k c) used"
  by (auto simp: packed_hierarchy_def Pool.Buffer.fixed_univ_map_upd_invar
      intro!: trans[OF pool_view_unchanged])

lemma packed_hierarchy_pool:
  assumes "packed_hierarchy H R P used" "pool_invar P'"
    "Pool.buffer_view P' 0 (used + length cs) False = Pool.buffer_view P 0 used False @ cs"
  shows "packed_hierarchy H R P' used"
  using assms(1,2)
  by (auto simp: packed_hierarchy_def intro!: trans[OF Pool.preserved_view[OF assms(3)]])


lemma packed_hierarchy_commit:
  "\<lbrakk>packed_hierarchy H R P used; Hierarchy.blossom_forest_merge_precond H cs b;
     b \<in> K; used + length cs \<le> capacity;
     Pool.buffer_view P used (length cs) False = cs\<rbrakk> \<Longrightarrow>
   packed_hierarchy (hierarchy_merge H cs b) (header_update R b (used, length cs)) P (used + length cs)"
  by (auto simp: packed_hierarchy_def Hierarchy.merge_spec Hierarchy.children_merge
      Hierarchy.blossom_forest_merge_precondD(5) Headers.fixed_univ_map_upd
      Headers.fixed_univ_map_upd_invar cong: sum.cong)

lemma packed_append_rule:
  assumes "packed_hierarchy H R P used" "used + length cs < capacity"
    "Pool.buffer_view P used (length cs) False = cs"
  shows "<pool_assn P P_i> pool_update_imp P_i (used + length cs) c
    <\<lambda>_. pool_assn (pool_update P (used + length cs) c) P_i *
      \<up>(packed_hierarchy H R (pool_update P (used + length cs) c) used \<and>
        Pool.buffer_view (pool_update P (used + length cs) c) used (Suc (length cs)) False = cs @ [c])>"
using assms packed_hierarchy_append[OF assms(1), of "used + length cs" c]
by (sep_auto simp: packed_hierarchy_def pool_view_append)


lemma packed_commit_rule:
  assumes "packed_hierarchy H R P used" "Hierarchy.blossom_forest_merge_precond H cs b"
    "b \<in> K" "used + length cs \<le> capacity"
    "Pool.buffer_view P used (length cs) False = cs"
  shows "<header_assn R Ri> header_update_imp Ri b (used, length cs)
    <\<lambda>_. header_assn (header_update R b (used, length cs)) Ri *
      \<up>(packed_hierarchy (hierarchy_merge H cs b) (header_update R b (used, length cs)) P (used + length cs))>"
using assms packed_hierarchy_commit[OF assms]
by (sep_auto simp: packed_hierarchy_def)


end

context Quadratic_Blossom_Search_Lifting
begin

lemma hierarchy_children_card:
  assumes "hierarchy_invar H" "recovery_tree H" "invar_navigation H D N"
  shows "(\<Sum>b \<in> hierarchy_ids H. length (hierarchy_children H b)) \<le>
    card (hierarchy_ids H - hierarchy_tops H)"
proof-
  let ?positions = "Sigma (hierarchy_ids H) (\<lambda>b. {..<length (hierarchy_children H b)})"
  let ?child = "\<lambda>(b, i). hierarchy_children H b ! i"
  have distinct: "inj_on ?child ?positions"
    using assms(3)
    by (intro inj_on_inverseI[where g = "link_lookup N"]) (auto simp: invar_navigation_def)
  have "?child ` ?positions \<subseteq> hierarchy_ids H - hierarchy_tops H"
    using assms(1,2) hierarchy_children_ids[of H]
    by (auto intro: hierarchy_child_not_top nth_mem; blast intro: nth_mem dest: hierarchy_child_not_top)
  moreover have "finite (hierarchy_ids H)"
    using assms(2)
    by (simp add: recovery_tree_def)
  ultimately have "card (?child ` ?positions) \<le> card (hierarchy_ids H - hierarchy_tops H)"
    by (intro card_mono) auto
  then show ?thesis
    using distinct assms(2)
    by (simp add: card_image recovery_tree_def)
qed

lemma hierarchy_merge_children_space:
  assumes "hierarchy_invar H" "recovery_tree H" "invar_navigation H D N"
    "Hierarchy.blossom_forest_merge_precond H cs b"
  shows "(\<Sum>b \<in> hierarchy_ids H. length (hierarchy_children H b)) + length cs \<le>
    card (hierarchy_ids H)"
proof-
  have tops: "hierarchy_tops H \<subseteq> hierarchy_ids H" "finite (hierarchy_tops H)"
    using Hierarchy.max_ids[of H] assms(1,2)
    by (auto simp: recovery_tree_def)
  have "length cs \<le> card (hierarchy_tops H)"
    using tops(2) Hierarchy.blossom_forest_merge_precondD(2,4)[OF assms(4)]
    by (auto simp flip: distinct_card intro: card_mono)
  moreover have "card (hierarchy_tops H) \<le> card (hierarchy_ids H)"
    using assms(2) tops(1)
    by (intro card_mono) (auto simp: recovery_tree_def)
  ultimately show ?thesis
    using hierarchy_children_card[OF assms(1-3)] card_Diff_subset[OF tops(2,1)]
    by linarith
qed

end

context Quadratic_Blossom_Search_thms
begin

lemma search_hierarchy_ids_bound:
  assumes "invar_search state"
  shows "card (hierarchy_ids (qbs_hierarchy state)) \<le> length vs + length vs div 2"
proof-
  let ?ids = "hierarchy_ids (qbs_hierarchy state)"
  have facts: "finite ?ids" "V0 \<subseteq> ?ids" "2 * card (?ids - V0) \<le> length vs"
    using assms
    by (auto simp: recovery_tree_def invar_hierarchy_size_def
        elim!: invar_search_props invar_recovering_structure_props)
  hence "card ?ids = length vs + card (?ids - V0)"
    using card_Diff_subset[of V0 ?ids] card_mono[of ?ids V0]
    by simp
  then show ?thesis
    using facts(3)
    by presburger
qed

lemma search_hierarchy_merge_space:
  assumes "invar_search state"
    "Hierarchy.blossom_forest_merge_precond (qbs_hierarchy state) cs b"
  shows "(\<Sum>a \<in> hierarchy_ids (qbs_hierarchy state). length (hierarchy_children (qbs_hierarchy state) a)) +
    length cs \<le> length vs + length vs div 2"
proof-
  have "(\<Sum>a \<in> hierarchy_ids (qbs_hierarchy state). length (hierarchy_children (qbs_hierarchy state) a)) +
    length cs \<le> card (hierarchy_ids (qbs_hierarchy state))"
    using assms
    by (intro hierarchy_merge_children_space[where D = "qbs_bases state" and N = "qbs_parents state"])
       (auto elim!: invar_search_props invar_recovering_structure_props)
  also have "... \<le> length vs + length vs div 2"
    using assms(1)
    by (rule search_hierarchy_ids_bound)
  finally show ?thesis .
qed

end

section "Recovery with a current visit in registers"

lemma recovery_list_stack:
  "bounded_stack cap (\<lambda>xs. length xs <= cap) id [] (\<lambda>xs x. x # xs) tl hd (\<lambda>xs. xs = [])"
  by unfold_locales auto

locale Blossom_Path_Recovery_Registers =
  Blossom_Path_Recovery_Imperative where task_invar = "\<lambda>xs. length xs <= task_cap"
    and task_abstract = id and task_empty = "[]" and task_push = "\<lambda>xs x. x # xs"
    and task_pop = tl and task_top = hd and task_is_empty = "\<lambda>xs. xs = []"
begin


lemma cycle_visit:
  "cycle_step H B b i j forward a z state =
    (let cs = hierarchy_children H b; c = cs ! i in
      if i = j then state \<lparr>qbr_tasks := Quadratic_Visit c a z # qbr_tasks state\<rparr>
      else let k = (if forward then if Suc i = length cs then 0 else Suc i
                    else if i = 0 then length cs - 1 else i - 1);
               edge = (if forward then edge_lookup B c else
                         (snd (edge_lookup B (cs ! k)), fst (edge_lookup B (cs ! k))))
        in state \<lparr>qbr_tasks := Quadratic_Visit c a (fst edge) #
          Quadratic_Cycle b k j forward (snd edge) z # qbr_tasks state\<rparr>)"
  by (simp add: cycle_step_def Let_def case_prod_beta)

lemma recovery_pop_visit:
  "qbr_tasks state = Quadratic_Visit b a z # ts \<Longrightarrow>
    recovery_step H B D N state = visit_step D N b a z (state \<lparr>qbr_tasks := ts\<rparr>)"
  by (simp add: recovery_step_def Let_def)

lemma recovery_pop_cycle:
  "qbr_tasks state = Quadratic_Cycle b i j forward a z # ts \<Longrightarrow>
    recovery_step H B D N state = cycle_step H B b i j forward a z (state \<lparr>qbr_tasks := ts\<rparr>)"
  by (simp add: recovery_step_def Let_def)

end

locale Blossom_Path_Recovery_Buffer =
  fixes nil :: "'v::heap"
    and base_read :: "'wi \<Rightarrow> 'v \<Rightarrow> 'v Heap"
    and route_into :: "'wi \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> unit Heap"
    and route_index :: "'wi \<Rightarrow> 'v \<Rightarrow> nat Heap"
    and children_range :: "'wi \<Rightarrow> 'v \<Rightarrow> (nat \<times> nat) Heap"
    and child_read :: "'wi \<Rightarrow> nat \<Rightarrow> 'v Heap"
    and cycle_edge :: "'wi \<Rightarrow> 'v \<Rightarrow> ('v \<times> 'v) Heap"
    and cycle_stack_read :: "'wi \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<times> nat \<times> nat \<times> bool \<times> 'v \<times> 'v) Heap"
    and cycle_stack_write :: "'wi \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> unit Heap"
    and component_read :: "'wi \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'v Heap"
    and crossing_read :: "'wi \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> nat \<Rightarrow> 'v \<Rightarrow> ('v \<times> 'v) Heap"
    and emit_into :: "'bi \<Rightarrow> nat \<Rightarrow> 'v \<Rightarrow> unit Heap"
begin

definition "cycle_child Wi off len i j forward a z sp = do {
  c \<leftarrow> child_read Wi (off + i);
  if i = j then return (c, a, z, sp)
  else do {
    let k = (if forward then if Suc i = len then 0 else Suc i
               else if i = 0 then len - 1 else i - 1);
    edge \<leftarrow> (if forward then cycle_edge Wi c
              else do { d \<leftarrow> child_read Wi (off + k); e \<leftarrow> cycle_edge Wi d;
                        return (snd e, fst e) });
    cycle_stack_write Wi sp off len k j forward (snd edge) z;
    return (c, a, fst edge, Suc sp) } }"

context fixes Wi :: 'wi and Bi :: 'bi and plen qlen :: nat and u v :: 'v begin

partial_function (heap) recovery_loop ::
  "'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> nat \<Rightarrow> 'v \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "recovery_loop b a z pos entry sp k =
    (if b \<noteq> nil then
       if a = z then do {
         emit_into Bi k a;
         recovery_loop nil nil nil pos entry sp (Suc k) }
       else do {
         base \<leftarrow> base_read Wi b;
         let from_base = (a = base);
         route_into Wi (if from_base then z else a) b;
         i \<leftarrow> route_index Wi b;
         range \<leftarrow> children_range Wi b;
         next \<leftarrow> cycle_child Wi (fst range) (snd range)
           (if from_base then 0 else i) (if from_base then i else 0)
           ((i mod 2 = 0) = from_base) a z sp;
         recovery_loop (fst next) (fst (snd next)) (fst (snd (snd next)))
           pos entry (snd (snd (snd next))) k }
     else if sp \<noteq> 0 then do {
       saved_cycle \<leftarrow> cycle_stack_read Wi (sp - 1);
       next \<leftarrow> (case saved_cycle of (off, len, i, j, forward, a, z) \<Rightarrow>
         cycle_child Wi off len i j forward a z (sp - 1));
       recovery_loop (fst next) (fst (snd next)) (fst (snd (snd next)))
         pos entry (snd (snd (snd next))) k }
     else if pos < plen + qlen then do {
       c \<leftarrow> component_read Wi plen qlen pos;
       a \<leftarrow> (if entry = nil then base_read Wi c else return entry);
       if Suc pos < plen + qlen then do {
         edge \<leftarrow> crossing_read Wi plen qlen u v pos c;
         recovery_loop c a (fst edge) (Suc pos) (snd edge) 0 k }
       else do {
         z \<leftarrow> base_read Wi c;
         recovery_loop c a z (Suc pos) nil 0 k } }
     else return k)"

end

definition "recover_into Wi Bi plen qlen u v = recovery_loop Wi Bi plen qlen u v nil nil nil 0 nil 0 0"

end

locale Quadratic_Cycle_Stack =
  Slots: fixed_univ_map_imp "{..<task_cap}" map_invar map_update map_lookup id
    map_assn map_update_imp map_lookup_imp
  for task_cap :: nat and map_invar :: "'map \<Rightarrow> bool"
    and map_update :: "'map \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<times> nat \<times> nat \<times> bool \<times> 'v::heap \<times> 'v) \<Rightarrow> 'map"
    and map_lookup :: "'map \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<times> nat \<times> nat \<times> bool \<times> 'v \<times> 'v)"
    and map_assn :: "'map \<Rightarrow> 'mi \<Rightarrow> assn"
    and map_update_imp :: "'mi \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<times> nat \<times> nat \<times> bool \<times> 'v \<times> 'v) \<Rightarrow> unit Heap"
    and map_lookup_imp :: "'mi \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<times> nat \<times> nat \<times> bool \<times> 'v \<times> 'v) Heap" +
  fixes range_valid :: "'v \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
begin

definition "cycle_slot task slot \<longleftrightarrow> (case task of
    Quadratic_Visit b a z \<Rightarrow> False
  | Quadratic_Cycle b i j forward a z \<Rightarrow>
      (\<exists>off len. range_valid b off len \<and> slot = (off,len,i,j,forward,a,z)))"

definition "cycle_stack_invar ts F \<longleftrightarrow> map_invar F \<and> length ts \<le> task_cap \<and>
  (\<forall>i < length ts. cycle_slot (rev ts ! i) (map_lookup F i))"

definition "cycle_stack_assn ts Ai = (\<exists>\<^sub>AF. map_assn F Ai * \<up>(cycle_stack_invar ts F))"

definition "cycle_stack_write Ai k off len i j forward a z =
  map_update_imp Ai k (off,len,i,j,forward,a,z)"

abbreviation "cycle_stack_read \<equiv> map_lookup_imp"

lemma cycle_stack_invar_empty:
  "map_invar F \<Longrightarrow> cycle_stack_invar [] F"
  by(simp add: cycle_stack_invar_def)

lemma cycle_stack_invar_push:
  "\<lbrakk>cycle_stack_invar ts F; length ts < task_cap; range_valid b off len\<rbrakk> \<Longrightarrow>
    cycle_stack_invar (Quadratic_Cycle b i j forward a z # ts)
      (map_update F (length ts) (off,len,i,j,forward,a,z))"
  by(auto simp: cycle_stack_invar_def cycle_slot_def nth_append
      Slots.fixed_univ_map_upd Slots.fixed_univ_map_upd_invar)

lemma cycle_stack_invar_pop:
  assumes "cycle_stack_invar (task # ts) F"
  shows "cycle_stack_invar ts F"
proof-
  have "cycle_slot (rev ts ! i) (map_lookup F i)" if "i < length ts" for i
    using assms that
    by(auto simp: cycle_stack_invar_def nth_append dest!: spec[where x=i])
  with assms show ?thesis
    by(auto simp: cycle_stack_invar_def)
qed
lemma cycle_stack_invar_top:
  "cycle_stack_invar (Quadratic_Cycle b i j forward a z # ts) F \<Longrightarrow>
    \<exists>off len. range_valid b off len \<and>
      map_lookup F (length ts) = (off,len,i,j,forward,a,z)"
  by(auto simp: cycle_stack_invar_def nth_append cycle_slot_def
      dest!: spec[where x="length ts"])

lemmas cycle_stack_invar_props = cycle_stack_invar_def[THEN iffD1]

lemma cycle_stack_write_rule:
  "\<lbrakk>range_valid b off len; length ts < task_cap\<rbrakk> \<Longrightarrow>
    <cycle_stack_assn ts Ai> cycle_stack_write Ai (length ts) off len i j forward a z
    <\<lambda>_. cycle_stack_assn (Quadratic_Cycle b i j forward a z # ts) Ai>"
  unfolding cycle_stack_assn_def cycle_stack_write_def
  by(sep_auto heap: Slots.fixed_univ_map_upd_rule intro: cycle_stack_invar_push
      dest: cycle_stack_invar_props)

lemma cycle_stack_read_rule:
  "<cycle_stack_assn (Quadratic_Cycle b i j forward a z # ts) Ai>
    cycle_stack_read Ai (length ts)
    <\<lambda>slot. cycle_stack_assn ts Ai * \<up>(\<exists>off len.
      range_valid b off len \<and> slot = (off,len,i,j,forward,a,z))>"
  unfolding cycle_stack_assn_def
  by(sep_auto heap: Slots.fixed_univ_map_lookup_rule
      dest: cycle_stack_invar_props cycle_stack_invar_pop cycle_stack_invar_top)

lemma cycle_stack_new_rule:
  "\<lbrakk>map_invar F; <emp> allocate <map_assn F>\<rbrakk> \<Longrightarrow>
    <emp> allocate <cycle_stack_assn []>"
  unfolding cycle_stack_assn_def
  by(sep_auto intro: cycle_stack_invar_empty)

lemma cycle_stack_reset_rule:
  "<cycle_stack_assn ts Ai> return () <\<lambda>_. cycle_stack_assn [] Ai>"
  unfolding cycle_stack_assn_def
  by(sep_auto intro: cycle_stack_invar_empty dest: cycle_stack_invar_props)

lemma cycle_stack_cycles:
  assumes "cycle_stack_invar ts F"
  shows "list_all (\<lambda>task. case task of Quadratic_Visit b a z \<Rightarrow> False
    | Quadratic_Cycle b i j forward a z \<Rightarrow> True) ts"
using assms
by (subst list_all_rev[symmetric])
  (auto simp: list_all_length cycle_stack_invar_def cycle_slot_def split: Quadratic_Blossom_Search_Recovery_task.splits)


end

locale Blossom_Path_Recovery_Stack_Refinement =
  Blossom_Path_Recovery_Registers where nil = nil and hierarchy_children = hierarchy_children
    and edge_lookup = edge_lookup +
  Blossom_Path_Recovery_Buffer where nil = nil and child_read = child_read
  for nil :: "'v::heap" and hierarchy_children :: "'hierarchy \<Rightarrow> 'v \<Rightarrow> 'v list"
    and edge_lookup :: "'edges \<Rightarrow> 'v \<Rightarrow> ('v \<times> 'v)"
    and child_read :: "'wi \<Rightarrow> nat \<Rightarrow> 'v Heap" +
  fixes H :: 'hierarchy and B :: 'edges
    and structure_assn :: "'wi \<Rightarrow> assn"
    and cycle_stack_assn :: "'v Quadratic_Blossom_Search_Recovery_task list \<Rightarrow> 'wi \<Rightarrow> assn"
    and range_valid :: "'v \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
  assumes range_length: "range_valid b off len \<Longrightarrow> length (hierarchy_children H b) = len"
    and range_children: "range_valid b off len \<Longrightarrow> set (hierarchy_children H b) \<subseteq> K"
    and children_range_rule: "\<lbrakk>b \<in> K; hierarchy_children H b \<noteq> []; \<exists>off len. range_valid b off len\<rbrakk> \<Longrightarrow>
      <structure_assn Wi> children_range Wi b
      <\<lambda>range. structure_assn Wi * \<up>(range_valid b (fst range) (snd range))>"
    and child_read_rule: "\<lbrakk>range_valid b off len; i < len\<rbrakk> \<Longrightarrow>
      <structure_assn Wi> child_read Wi (off + i)
      <\<lambda>c. structure_assn Wi * \<up>(c = hierarchy_children H b ! i)>"
    and cycle_edge_rule: "v \<in> K \<Longrightarrow> <structure_assn Wi> cycle_edge Wi v
      <\<lambda>e. structure_assn Wi * \<up>(e = edge_lookup B v)>"
    and cycle_stack_write_rule: "\<lbrakk>range_valid b off len; length ts < task_cap\<rbrakk> \<Longrightarrow>
      <cycle_stack_assn ts Wi> cycle_stack_write Wi (length ts) off len i j forward a z
      <\<lambda>_. cycle_stack_assn (Quadratic_Cycle b i j forward a z # ts) Wi>"
    and cycle_stack_read_rule: "<cycle_stack_assn (Quadratic_Cycle b i j forward a z # ts) Wi>
      cycle_stack_read Wi (length ts)
      <\<lambda>saved_cycle. cycle_stack_assn ts Wi * \<up>(\<exists>off len. range_valid b off len \<and>
        saved_cycle = (off, len, i, j, forward, a, z))>"
begin

lemma cycle_child_last:
  assumes "range_valid b off len" "i < len"
  shows "<structure_assn Wi * cycle_stack_assn ts Wi> cycle_child Wi off len i i forward a z (length ts)
    <\<lambda>next. structure_assn Wi * cycle_stack_assn ts Wi * \<up>(next = (hierarchy_children H b ! i, a, z, length ts))>"
  using assms
  unfolding cycle_child_def
  by (sep_auto heap: child_read_rule[OF assms(1)] simp: Let_def)

lemma cycle_child_next:
  fixes forward :: bool and k :: nat
  assumes "range_valid b off len" "i < len" "j < len" "i \<noteq> j" "length ts < task_cap"
  defines "k \<equiv> if forward then if Suc i = len then 0 else Suc i
                  else if i = 0 then len - 1 else i - 1"
    and "e \<equiv> if forward then edge_lookup B (hierarchy_children H b ! i)
      else (snd (edge_lookup B (hierarchy_children H b ! k)), fst (edge_lookup B (hierarchy_children H b ! k)))"
  shows "<structure_assn Wi * cycle_stack_assn ts Wi> cycle_child Wi off len i j forward a z (length ts)
    <\<lambda>next. structure_assn Wi * cycle_stack_assn (Quadratic_Cycle b k j forward (snd e) z # ts) Wi *
      \<up>(next = (hierarchy_children H b ! i, a, fst e, Suc (length ts)))>"
proof-
  have bounds: "k < len"
    using assms(2)
    by (auto simp: k_def)
  have vertices: "hierarchy_children H b ! i \<in> K" "hierarchy_children H b ! k \<in> K"
    using assms(2) bounds range_children[OF assms(1)] range_length[OF assms(1)]
    by auto
  show ?thesis
    using assms(2-5) bounds vertices
    unfolding cycle_child_def[of Wi off len i j forward a z "length ts", folded k_def] e_def
    by (cases forward)
      (sep_auto heap: child_read_rule[OF assms(1,2)] child_read_rule[OF assms(1) bounds]
        cycle_edge_rule[OF vertices(1)] cycle_edge_rule[OF vertices(2)] cycle_stack_write_rule[OF assms(1,5)] simp: Let_def)+
qed

lemma cycle_child_rule:
  assumes "range_valid b off len" "i < len" "j < len" "length (qbr_tasks state) < task_cap"
  shows "<structure_assn Wi * cycle_stack_assn (qbr_tasks state) Wi>
    cycle_child Wi off len i j forward a z (length (qbr_tasks state))
    <\<lambda>next. \<exists>\<^sub>Ats. structure_assn Wi * cycle_stack_assn ts Wi * \<up>(
      snd (snd (snd next)) = length ts \<and>
      Quadratic_Visit (fst next) (fst (snd next)) (fst (snd (snd next))) # ts =
        qbr_tasks (cycle_step H B b i j forward a z state))>"
  using assms
  by (cases "i = j")
    (sep_auto heap: cycle_child_last[OF assms(1)] cycle_child_next[OF assms(1)]
      simp: cycle_visit range_length[OF assms(1)] Let_def case_prod_beta)+

end

locale Blossom_Path_Recovery_Buffer_Refinement =
  Blossom_Path_Recovery_Stack_Refinement where nil = nil and child_read = child_read
    and emit_into = emit_into and base_lookup = base_lookup
    and output_lookup = output_lookup and link_lookup = link_lookup
  for nil :: "'v::heap" and child_read :: "'wi \<Rightarrow> nat \<Rightarrow> 'v Heap"
    and emit_into :: "'bi \<Rightarrow> nat \<Rightarrow> 'v \<Rightarrow> unit Heap"
    and base_lookup :: "'bases \<Rightarrow> 'v \<Rightarrow> 'v"
    and output_lookup :: "'output \<Rightarrow> nat \<Rightarrow> 'v"
    and link_lookup :: "'links \<Rightarrow> 'v \<Rightarrow> ('v \<times> nat)" +
  fixes D :: 'bases and N :: 'links and path :: "'v list" and crossings :: "('v \<times> 'v) list"
    and plen qlen :: nat and bu bv :: 'v
    and hints_assn :: "'links \<Rightarrow> 'wi \<Rightarrow> assn"
    and output_assn :: "'output \<Rightarrow> 'bi \<Rightarrow> assn"
    and route_ready :: "'links \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> bool"
  assumes nil_outside: "nil \<notin> K"
    and crossing_length: "length crossings = length path - 1"
    and path_length: "length path = plen + qlen"
    and base_read_rule: "b \<in> K \<Longrightarrow> <structure_assn Wi> base_read Wi b
      <\<lambda>a. structure_assn Wi * \<up>(a = base_lookup D b)>"
    and route_into_rule: "route_ready J target b \<Longrightarrow>
      <structure_assn Wi * hints_assn J Wi> route_into Wi target b
      <\<lambda>_. structure_assn Wi * hints_assn (cache_route N target b J) Wi>"
    and route_index_rule: "\<lbrakk>link_invar J; b \<in> K\<rbrakk> \<Longrightarrow>
      <hints_assn J Wi> route_index Wi b <\<lambda>i. hints_assn J Wi * \<up>(i = snd (link_lookup J b))>"
    and component_read_rule: "i < length path \<Longrightarrow> <structure_assn Wi> component_read Wi plen qlen i
      <\<lambda>b. structure_assn Wi * \<up>(b = path ! i)>"
    and crossing_read_rule: "i < length crossings \<Longrightarrow> <structure_assn Wi> crossing_read Wi plen qlen bu bv i (path ! i)
      <\<lambda>e. structure_assn Wi * \<up>(e = crossings ! i)>"
    and emit_into_rule: "\<lbrakk>output_invar out; k < output_cap\<rbrakk> \<Longrightarrow>
      <output_assn out Bi> emit_into Bi k v <\<lambda>_. output_assn (output_update out k v) Bi>"
begin

definition "saved_cycles ts \<longleftrightarrow> list_all
  (\<lambda>task. case task of Quadratic_Visit b a z \<Rightarrow> False | Quadratic_Cycle b i j forward a z \<Rightarrow> True) ts"

definition "recovery_at state pos entry \<longleftrightarrow> qbr_path state = drop pos path \<and>
  qbr_crossings state = drop pos crossings \<and> qbr_entry state = entry \<and> pos \<le> length path"

definition "recovery_storage state ts Wi Bi = structure_assn Wi * cycle_stack_assn ts Wi *
  hints_assn (qbr_hints state) Wi * output_assn (qbr_output state) Bi"

definition "recovery_result state Wi Bi k =
  recovery_storage state (qbr_tasks state) Wi Bi * \<up>(k = qbr_length state)"

definition "recovery_ready state \<longleftrightarrow> output_invar (qbr_output state) \<and> link_invar (qbr_hints state) \<and>
  length (qbr_tasks state) < task_cap \<and>
  (case qbr_tasks state of
    [] \<Rightarrow> (qbr_path state \<noteq> [] \<longrightarrow> hd (qbr_path state) \<in> K)
  | Quadratic_Visit b a z # ts \<Rightarrow> b \<in> K \<and>
      (if a = z then qbr_length state < output_cap
       else let target = (if a = base_lookup D b then z else a);
                J = cache_route N target b (qbr_hints state)
         in route_ready (qbr_hints state) target b \<and> link_invar J \<and>
           hierarchy_children H b \<noteq> [] \<and> (\<exists>off len. range_valid b off len) \<and>
           snd (link_lookup J b) < length (hierarchy_children H b))
  | Quadratic_Cycle b i j forward a z # ts \<Rightarrow> b \<in> K \<and>
      i < length (hierarchy_children H b) \<and> j < length (hierarchy_children H b))"

definition "cycle_program Wi Bi off len i j forward a z pos entry sp k = do {
  next \<leftarrow> cycle_child Wi off len i j forward a z sp;
  recovery_loop Wi Bi plen qlen bu bv (fst next) (fst (snd next)) (fst (snd (snd next)))
    pos entry (snd (snd (snd next))) k }"

definition "recovery_simulates state \<longleftrightarrow> (\<forall>pos entry Wi Bi. recovery_at state pos entry \<longrightarrow>
  (\<forall>b a z ts. qbr_tasks state = Quadratic_Visit b a z # ts \<and> saved_cycles ts \<longrightarrow>
    <recovery_storage state ts Wi Bi>
      recovery_loop Wi Bi plen qlen bu bv b a z pos entry (length ts) (qbr_length state)
    <recovery_result (Blossom_Path_Recovery H B D N state) Wi Bi>) \<and>
  (\<forall>b i j forward a z ts off len. qbr_tasks state = Quadratic_Cycle b i j forward a z # ts \<and>
      saved_cycles ts \<and> range_valid b off len \<longrightarrow>
    <recovery_storage state ts Wi Bi>
      cycle_program Wi Bi off len i j forward a z pos entry (length ts) (qbr_length state)
    <recovery_result (Blossom_Path_Recovery H B D N state) Wi Bi>) \<and>
  (saved_cycles (qbr_tasks state) \<longrightarrow>
    <recovery_storage state (qbr_tasks state) Wi Bi>
      recovery_loop Wi Bi plen qlen bu bv nil nil nil pos entry (length (qbr_tasks state)) (qbr_length state)
    <recovery_result (Blossom_Path_Recovery H B D N state) Wi Bi>))"

lemma saved_cycles_simps[simp]:
  "saved_cycles []"
  "saved_cycles (Quadratic_Cycle b i j forward a z # ts) = saved_cycles ts"
  "\<not> saved_cycles (Quadratic_Visit b a z # ts)"
  by (simp_all add: saved_cycles_def)

lemma recovery_at_tasks[simp]:
  "recovery_at (state \<lparr>qbr_tasks := ts\<rparr>) pos entry = recovery_at state pos entry"
  "recovery_at (emit_vertex v state) pos entry = recovery_at state pos entry"
  "recovery_at (cycle_step H B b i j forward a z state) pos entry = recovery_at state pos entry"
  "recovery_at (visit_step D N b a z state) pos entry = recovery_at state pos entry"
  by (auto simp: recovery_at_def emit_vertex_def cycle_step_def visit_step_def Let_def case_prod_beta)

lemma recovery_at_path:
  assumes "recovery_at state pos entry"
  shows "(qbr_path state \<noteq> []) = (pos < length path)"
    "pos < length path \<Longrightarrow> hd (qbr_path state) = path ! pos"
    "(qbr_crossings state \<noteq> []) = (pos < length crossings)"
    "pos < length crossings \<Longrightarrow> hd (qbr_crossings state) = crossings ! pos"
  using assms
  by (auto simp: recovery_at_def hd_drop_conv_nth)

lemma recovery_at_next:
  "\<lbrakk>recovery_at state pos entry; qbr_path state \<noteq> []\<rbrakk> \<Longrightarrow>
    recovery_at (next_component D state) (Suc pos)
      (if Suc pos < length path then snd (crossings ! pos) else nil)"
  by (auto simp: recovery_at_def next_component_def Let_def list.case_eq_if
    hd_drop_conv_nth drop_Suc drop_tl crossing_length)

lemma recovery_next_task:
  "\<lbrakk>recovery_at state pos entry; qbr_path state \<noteq> []; qbr_tasks state = []\<rbrakk> \<Longrightarrow>
    qbr_tasks (next_component D state) = [Quadratic_Visit (path ! pos)
      (if entry = nil then base_lookup D (path ! pos) else entry)
      (if Suc pos < length path then fst (crossings ! pos) else base_lookup D (path ! pos))]"
  by (auto simp: recovery_at_def next_component_def Let_def list.case_eq_if
    hd_drop_conv_nth crossing_length)

lemma recovery_simulates_visit:
  "\<lbrakk>recovery_simulates state; recovery_at state pos entry;
    qbr_tasks state = Quadratic_Visit b a z # ts; saved_cycles ts\<rbrakk> \<Longrightarrow>
    <recovery_storage state ts Wi Bi>
      recovery_loop Wi Bi plen qlen bu bv b a z pos entry (length ts) (qbr_length state)
    <recovery_result (Blossom_Path_Recovery H B D N state) Wi Bi>"
  by (auto simp: recovery_simulates_def)

lemma recovery_simulates_cycle:
  "\<lbrakk>recovery_simulates state; recovery_at state pos entry;
    qbr_tasks state = Quadratic_Cycle b i j forward a z # ts; saved_cycles ts; range_valid b off len\<rbrakk> \<Longrightarrow>
    <recovery_storage state ts Wi Bi>
      cycle_program Wi Bi off len i j forward a z pos entry (length ts) (qbr_length state)
    <recovery_result (Blossom_Path_Recovery H B D N state) Wi Bi>"
  by (auto simp: recovery_simulates_def)

lemma recovery_simulates_stack:
  "\<lbrakk>recovery_simulates state; recovery_at state pos entry; saved_cycles (qbr_tasks state)\<rbrakk> \<Longrightarrow>
    <recovery_storage state (qbr_tasks state) Wi Bi>
      recovery_loop Wi Bi plen qlen bu bv nil nil nil pos entry (length (qbr_tasks state)) (qbr_length state)
    <recovery_result (Blossom_Path_Recovery H B D N state) Wi Bi>"
  by (auto simp: recovery_simulates_def)

lemma recovery_simulates_step:
  assumes "Blossom_Path_Recovery_dom H B D N state" "recovery_ready state"
    "Blossom_Path_Recovery_call_1_conds state \<Longrightarrow>
      recovery_simulates (Blossom_Path_Recovery_upd1 H B D N state)"
  shows "recovery_simulates state"
proof-
  have visit: "<recovery_storage state ts Wi Bi>
      recovery_loop Wi Bi plen qlen bu bv b a z pos entry (length ts) (qbr_length state)
      <recovery_result (Blossom_Path_Recovery H B D N state) Wi Bi>"
    if task: "qbr_tasks state = Quadratic_Visit b a z # ts"
      and at: "recovery_at state pos entry" and stack: "saved_cycles ts"
    for b a z ts pos entry Wi Bi
  proof-
    have transition: "recovery_simulates (visit_step D N b a z (state \<lparr>qbr_tasks := ts\<rparr>))"
      "Blossom_Path_Recovery H B D N state =
        Blossom_Path_Recovery H B D N (visit_step D N b a z (state \<lparr>qbr_tasks := ts\<rparr>))"
      using assms(3) Blossom_Path_Recovery_simps(1)[OF assms(1)] task
      by(auto simp: Blossom_Path_Recovery_call_1_conds_def recovery_done_def
        Blossom_Path_Recovery_upd1_def recovery_pop_visit)
    have vertex: "b \<noteq> nil"
      using assms(2) task nil_outside
      by (auto simp: recovery_ready_def)
    show ?thesis
    proof(cases "a = z")
      case True
      note recursive = recovery_simulates_stack[OF transition(1), unfolded visit_step_def emit_vertex_def,
        simplified True, unfolded recovery_storage_def, simplified]
      show ?thesis
        using assms(2) task at stack vertex True
        by (subst recovery_loop.simps)
          (sep_auto heap: emit_into_rule recursive
            simp: recovery_at_def recovery_ready_def recovery_storage_def transition(2) visit_step_def emit_vertex_def Let_def)
    next
      case False
      have loop: "recovery_loop Wi Bi plen qlen bu bv b a z pos entry (length ts) (qbr_length state) = do {
          base \<leftarrow> base_read Wi b;
          let from_base = (a = base);
          route_into Wi (if from_base then z else a) b;
          i \<leftarrow> route_index Wi b;
          range \<leftarrow> children_range Wi b;
          cycle_program Wi Bi (fst range) (snd range) (if from_base then 0 else i)
            (if from_base then i else 0) (even i = from_base) a z pos entry (length ts) (qbr_length state) }"
        using vertex False
        by (subst recovery_loop.simps) (simp add: cycle_program_def even_iff_mod_2_eq_zero)
      note recursive = recovery_simulates_cycle[OF transition(1), unfolded visit_step_def,
        simplified False, unfolded Let_def recovery_storage_def, simplified]
      show ?thesis
        using assms(2) task at stack vertex False
        unfolding loop
        by(cases "a = base_lookup D b")
          (sep_auto heap: base_read_rule route_into_rule route_index_rule children_range_rule recursive
            simp: recovery_at_def recovery_ready_def recovery_storage_def transition(2) visit_step_def Let_def)+

    qed
  qed
  have cycle: "<recovery_storage state ts Wi Bi>
      cycle_program Wi Bi off len i j forward a z pos entry (length ts) (qbr_length state)
      <recovery_result (Blossom_Path_Recovery H B D N state) Wi Bi>"
    if task: "qbr_tasks state = Quadratic_Cycle b i j forward a z # ts"
      and at: "recovery_at state pos entry" and stack: "saved_cycles ts" and range: "range_valid b off len"
    for b i j forward a z ts off len pos entry Wi Bi
  proof-
    have transition: "recovery_simulates (cycle_step H B b i j forward a z (state \<lparr>qbr_tasks := ts\<rparr>))"
      "Blossom_Path_Recovery H B D N state =
        Blossom_Path_Recovery H B D N (cycle_step H B b i j forward a z (state \<lparr>qbr_tasks := ts\<rparr>))"
      using assms(3) Blossom_Path_Recovery_simps(1)[OF assms(1)] task
      by(auto simp: Blossom_Path_Recovery_call_1_conds_def recovery_done_def
        Blossom_Path_Recovery_upd1_def recovery_pop_cycle)
    let ?s = "cycle_step H B b i j forward a z (state \<lparr>qbr_tasks := ts\<rparr>)"
    have tail: "saved_cycles rest" if "qbr_tasks ?s = Quadratic_Visit c x y # rest" for c x y rest
      using stack that
      by (auto simp: cycle_visit Let_def case_prod_beta split: if_splits)
    have "qbr_hints ?s = qbr_hints state" "qbr_output ?s = qbr_output state"
      "qbr_length ?s = qbr_length state"
      by (auto simp: cycle_step_def Let_def case_prod_beta)
    note recursive = recovery_simulates_visit[OF transition(1), unfolded recovery_storage_def, simplified this]
    show ?thesis
      using assms(2) task at stack range
      unfolding cycle_program_def
      by (sep_auto heap: cycle_child_rule[OF range, where state="state \<lparr>qbr_tasks := ts\<rparr>", simplified] recursive
        simp: recovery_ready_def recovery_storage_def transition(2) range_length[OF range] dest: tail[OF sym])
  qed
  have inactive: "<recovery_storage state (qbr_tasks state) Wi Bi>
      recovery_loop Wi Bi plen qlen bu bv nil nil nil pos entry (length (qbr_tasks state)) (qbr_length state)
      <recovery_result (Blossom_Path_Recovery H B D N state) Wi Bi>"
    if at: "recovery_at state pos entry" and stack: "saved_cycles (qbr_tasks state)"
    for pos entry Wi Bi
  proof(cases "qbr_tasks state")
    case Nil
    show ?thesis
    proof(cases "qbr_path state = []")
      case True
      hence result: "Blossom_Path_Recovery H B D N state = state"
        using assms(1) Nil
        by (simp add: Blossom_Path_Recovery_simps Blossom_Path_Recovery_ret_1_conds_def
          Blossom_Path_Recovery_call_1_conds_def recovery_done_def Blossom_Path_Recovery_ret1_def)
      show ?thesis
        using Nil True at
        by (subst recovery_loop.simps)
          (sep_auto simp: recovery_at_def recovery_storage_def recovery_result_def result path_length)
    next
      case False
      have transition: "recovery_simulates (next_component D state)"
        "Blossom_Path_Recovery H B D N state = Blossom_Path_Recovery H B D N (next_component D state)"
        using assms(3) Blossom_Path_Recovery_simps(1)[OF assms(1)] Nil False
        by(auto simp: Blossom_Path_Recovery_call_1_conds_def recovery_done_def
          Blossom_Path_Recovery_upd1_def recovery_step_def)
      have component: "path ! pos \<in> K"
        using assms(2) Nil False recovery_at_path[OF at]
        by (auto simp: recovery_ready_def)
      have "qbr_hints (next_component D state) = qbr_hints state"
        "qbr_output (next_component D state) = qbr_output state"
        "qbr_length (next_component D state) = qbr_length state"
        by (simp_all add: next_component_def Let_def)
      note recursive = recovery_simulates_visit[OF transition(1), where ts="[]", unfolded recovery_storage_def, simplified this, simplified]
      show ?thesis
        using Nil False at component recovery_at_path(1)[OF at] recovery_at_next[OF at False]
          recovery_next_task[OF at False Nil]
        by (subst recovery_loop.simps)
          (sep_auto heap: component_read_rule base_read_rule crossing_read_rule recursive
            simp: recovery_storage_def transition(2) crossing_length path_length)
    qed
  next
    case (Cons task ts)
    obtain b i j forward a z where "task = Quadratic_Cycle b i j forward a z"
      using stack Cons
      by(cases task) auto
    then have task: "qbr_tasks state = Quadratic_Cycle b i j forward a z # ts" "saved_cycles ts"
      using Cons stack
      by auto
    note continuation = cycle[OF task(1) at task(2), unfolded recovery_storage_def]
    have "recovery_loop Wi Bi plen qlen bu bv nil nil nil pos entry
        (length (qbr_tasks state)) (qbr_length state) = do {
        saved_cycle \<leftarrow> cycle_stack_read Wi (length ts);
        case saved_cycle of (off, len, i, j, forward, a, z) \<Rightarrow>
          cycle_program Wi Bi off len i j forward a z pos entry (length ts) (qbr_length state) }"
      using task
      by (subst recovery_loop.simps) (simp add: cycle_program_def case_prod_beta split_def)
    then show ?thesis
      using task
      by (sep_auto heap: cycle_stack_read_rule continuation simp: recovery_storage_def case_prod_beta)
  qed
  show ?thesis
    using visit cycle inactive
    by (auto simp: recovery_simulates_def)
qed

lemma recovery_simulates:
  assumes "Blossom_Path_Recovery_dom H B D N state" "I state"
    "\<And>s. I s \<Longrightarrow> recovery_ready s"
    "\<And>s. \<lbrakk>I s; Blossom_Path_Recovery_call_1_conds s\<rbrakk> \<Longrightarrow> I (Blossom_Path_Recovery_upd1 H B D N s)"
  shows "recovery_simulates state"
  using assms(2)
proof(induction rule: Blossom_Path_Recovery_induct[OF assms(1)])
  case IH: (1 state)
  show ?case
    by (intro recovery_simulates_step[OF IH.hyps(1)])
      (use IH assms(3,4) in auto)
qed

lemma recover_into_refine:
  assumes "Blossom_Path_Recovery_dom H B D N (initial_recovery path crossings [] J out)"
    "I (initial_recovery path crossings [] J out)"
    "\<And>s. I s \<Longrightarrow> recovery_ready s"
    "\<And>s. \<lbrakk>I s; Blossom_Path_Recovery_call_1_conds s\<rbrakk> \<Longrightarrow> I (Blossom_Path_Recovery_upd1 H B D N s)"
  shows "<structure_assn Wi * cycle_stack_assn [] Wi * hints_assn J Wi * output_assn out Bi>
    recover_into Wi Bi plen qlen bu bv
    <recovery_result (Blossom_Path_Recovery H B D N (initial_recovery path crossings [] J out)) Wi Bi>"
  using recovery_simulates_stack[OF recovery_simulates[OF assms], where pos=0 and entry=nil and Wi=Wi and Bi=Bi]
  by (simp add: initial_recovery_def recovery_at_def recovery_storage_def recover_into_def)

end

context Quadratic_Blossom_Search_Lifting
begin

lemma recovery_register_ready:
  assumes "invar_recovery H B D N state" "Suc (card (hierarchy_ids H)) \<le> task_cap"
  shows "output_invar (qbr_output state)" "link_invar (qbr_hints state)"
    "task_invar (qbr_tasks state)" "length (task_abstract (qbr_tasks state)) < task_cap"
  using assms
  by (auto elim!: invar_recovery_props Recovery.invar_recovery_adts_props
      invar_recovery_routing_props invar_route_cache_props intro: recovery_stack_space)+

lemma recovery_next_component_key:
  "\<lbrakk>invar_recovery H B D N state; hierarchy_ids H \<subseteq> K; qbr_path state \<noteq> []\<rbrakk>
   \<Longrightarrow> hd (qbr_path state) \<in> K"
  by (cases "qbr_path state"; auto simp: invar_recovery_def invar_recovery_tasks_def
      pending_visits_def quotient_visits_def visit_admissible_def list_all_iff Let_def map_upt_Suc simp del: upt_Suc)


lemma recovery_cycle_ready:
  assumes "invar_recovery H B D N state" "\<not> task_is_empty (qbr_tasks state)"
    "task_top (qbr_tasks state) = Quadratic_Cycle b i j forward a z" "hierarchy_ids H \<subseteq> K"
  shows "b \<in> K" "i < length (hierarchy_children H b)" "j < length (hierarchy_children H b)"
  using assms recovery_stack_properties(3)[OF assms(1,2)]
  by (auto simp: task_admissible_def)+

lemma recovery_visit_ready:
  fixes target J
  assumes "invar_recovery H B D N state" "\<not> task_is_empty (qbr_tasks state)"
    "task_top (qbr_tasks state) = Quadratic_Visit b a z" "hierarchy_ids H \<subseteq> K" "nil \<notin> V0"
  defines "target \<equiv> visit_target D b a z"
    and "J \<equiv> Recovery.cache_route N target b (qbr_hints state)"
  shows "b \<in> K"
    "a \<noteq> z \<Longrightarrow> invar_route_cache H (qbr_hints state) \<and> b \<in> hierarchy_ids H \<and>
      target \<in> hierarchy_members H b \<and> link_invar J \<and> hierarchy_children H b \<noteq> [] \<and>
      snd (link_lookup J b) < length (hierarchy_children H b)"
proof-
  have visit: "visit_admissible H D b a z"
    using assms(3) recovery_stack_properties(3)[OF assms(1,2)]
    by (simp add: task_admissible_def)
  show "b \<in> K"
    using visit assms(4)
    by (auto simp: visit_admissible_def)
  have cache: "a \<noteq> z \<Longrightarrow> invar_route_cache H J"
    using assms(1,4,5) visit recovering_visit_props[of H D b a z]
    unfolding J_def target_def
    by (intro cache_route_correct[where D = D];
      auto simp: invar_recovery_routing_def invar_recovering_structure_def visit_target_def
        elim!: invar_recovery_props)
  show "a \<noteq> z \<Longrightarrow> invar_route_cache H (qbr_hints state) \<and> b \<in> hierarchy_ids H \<and>
      target \<in> hierarchy_members H b \<and> link_invar J \<and> hierarchy_children H b \<noteq> [] \<and>
      snd (link_lookup J b) < length (hierarchy_children H b)"
    using assms(1,4,5) visit cache recovering_visit_props[of H D b a z]
      recovery_visit_index(1)[of H B D N state b a z]
    by (auto simp: target_def J_def invar_recovery_routing_def invar_route_cache_def
        invar_recovering_structure_def elim!: invar_recovery_props)
qed

end

locale Quadratic_Blossom_Search_Recovery_Refinement =
  Quadratic_Blossom_Search_Lifting where K = K and link_invar = link_invar
    and link_update = link_update and link_lookup = link_lookup +
  Cache: Blossom_Path_Recovery_Imperative where K = K and link_invar = link_invar
    and link_update = link_update and link_lookup = link_lookup
    and link_assn = link_assn and link_update_imp = link_update_imp and link_lookup_imp = link_lookup_imp
  for K :: "'v::heap set" and link_invar :: "'links \<Rightarrow> bool"
    and link_update :: "'links \<Rightarrow> 'v \<Rightarrow> ('v \<times> nat) \<Rightarrow> 'links"
    and link_lookup :: "'links \<Rightarrow> 'v \<Rightarrow> ('v \<times> nat)"
    and link_assn :: "'links \<Rightarrow> 'li \<Rightarrow> assn"
    and link_update_imp :: "'li \<Rightarrow> 'v \<Rightarrow> ('v \<times> nat) \<Rightarrow> unit Heap"
    and link_lookup_imp :: "'li \<Rightarrow> 'v \<Rightarrow> ('v \<times> nat) Heap"
begin

lemma cache_into_rule:
  assumes "recovery_tree H" "invar_navigation H D N" "hierarchy_ids H \<subseteq> K"
    "b \<in> hierarchy_ids H" "target \<in> hierarchy_members H b" "invar_route_cache H J"
  shows "<link_assn N Ni * link_assn J Ji> Cache.cache_into Ni Ji target b
    <\<lambda>_. link_assn N Ni * link_assn (Recovery.cache_route N target b J) Ji>"
  using assms
  by (intro Cache.cache_into_refine[where I = "invar_cache_route H b target",
        OF _ _ _ _ cache_refinement_ready[OF assms(1-3)]])
    (auto simp: invar_route_cache_def intro: cache_route_initial_dom[where D = D] invar_cache_route_initial)

end

section "A frontier that only appends"

context Quadratic_Blossom_Search_thms
begin

definition "frontier_history state xs h \<longleftrightarrow> distinct xs \<and> set xs = effectively_even state &
  h <= length xs \<and> queue_abstract (qbs_queue state) = drop h xs"

lemma frontier_history_bound:
  "frontier_history state xs h \<Longrightarrow> length xs <= cap"
proof-
  assume "frontier_history state xs h"
  hence "card (set xs) <= card V0" "distinct xs"
    by (auto simp: frontier_history_def effectively_even_def simp del: initial_finite(2) intro!: card_mono)
  thus ?thesis
    using input_props(5)
    by (auto simp: distinct_card intro: order_trans)
qed

lemma frontier_history_initial:
  "frontier_history initial_search_state (queue_abstract (snd initial_frontier)) 0"
  by (auto simp: frontier_history_def)

lemma frontier_history_same:
  "\<lbrakk> frontier_history state xs h; effectively_even next = effectively_even state;
    queue_abstract (qbs_queue next) = queue_abstract (qbs_queue state) \<rbrakk> \<Longrightarrow>
    frontier_history next xs h"
  by (simp add: frontier_history_def)

lemma frontier_history_pop:
  "\<lbrakk> frontier_history state xs h; queue_abstract (qbs_queue state) \<noteq> [];
    effectively_even next = effectively_even state;
    queue_abstract (qbs_queue next) = tl (queue_abstract (qbs_queue state)) \<rbrakk> \<Longrightarrow>
    frontier_history next xs (Suc h)"
  by (auto simp: frontier_history_def drop_Suc drop_tl)

lemma frontier_history_append:
  "\<lbrakk> frontier_history state xs h; distinct ys; set ys \<subseteq> V0 - effectively_even state;
    effectively_even next = effectively_even state \<union> set ys;
    queue_abstract (qbs_queue next) = queue_abstract (qbs_queue state) @ ys \<rbrakk> \<Longrightarrow>
    frontier_history next (xs @ ys) h"
  by (auto simp: frontier_history_def; blast)

lemma frontier_history_start_scan:
  "\<lbrakk> Quadratic_Blossom_Search_call_2_conds state; invar_search state; frontier_history state xs h \<rbrakk> \<Longrightarrow>
    frontier_history (Quadratic_Blossom_Search_upd2 state) xs (Suc h)"
  by (rule frontier_history_pop[where state = state])
    (auto elim!: invar_search_props simp: start_scan_props start_scan_source effectively_even_def)

lemma frontier_history_extension:
  assumes "Quadratic_Blossom_Search_call_5_conds state" "invar_search state" "frontier_history state xs h"
  shows "frontier_history (Quadratic_Blossom_Search_upd5 state)
    (xs @ [mate_partner (qbs_matching state) (target_component state)]) h"
  using assms extension_new_even[OF assms(1,2)] extension_even[OF assms(1,2)]
    queue_space[of state "mate_partner (qbs_matching state) (target_component state)"]
  by (intro frontier_history_append[where state = state])
    (auto elim!: invar_search_props invar_adts_props simp: Quadratic_Blossom_Search_upd5_def
      extend_search_def enqueue_vertex_def Quadratic_Blossom_Search_upd4_def Let_def Work.queue_push)

lemma frontier_history_contraction:
  assumes "Quadratic_Blossom_Search_call_7_conds state" "invar_search state"
    "longest_disj_sfx (rev (forest_path (qbs_forest state) (source_component state)))
      (rev (forest_path (qbs_forest state) (target_component state))) = (c1, c2)"
    "queue_pop (qbs_fresh state) = (b, fresh)" "frontier_history state xs h"
  shows "frontier_history (Quadratic_Blossom_Search_upd7 state)
    (xs @ filter (fset_isin (forest_odds (qbs_forest state))) (c1 @ butlast (rev c2))) h"
  using assms(5) contraction_scheduled(1-3)[OF assms(1-4)]
    contraction_effectively_even[OF assms(1-4)] contraction_queue(2)[OF assms(1-4)]
  by (intro frontier_history_append[where state = state]) auto

lemma frontier_history_stable:
  "frontier_history state xs h \<Longrightarrow> frontier_history (Quadratic_Blossom_Search_upd1 state) xs h"
  "frontier_history state xs h \<Longrightarrow> frontier_history (Quadratic_Blossom_Search_upd3 state) xs h"
  "\<lbrakk> scanning_edge state; invar_search state; frontier_history state xs h \<rbrakk> \<Longrightarrow> frontier_history (Quadratic_Blossom_Search_upd4 state) xs h"
  "\<lbrakk> Quadratic_Blossom_Search_call_6_conds state; invar_search state; frontier_history state xs h \<rbrakk> \<Longrightarrow> frontier_history (Quadratic_Blossom_Search_upd6 state) xs h"
  by (auto elim!: invar_search_props call_cond_elims simp: frontier_history_def effectively_even_def
    Quadratic_Blossom_Search_upd1_def Quadratic_Blossom_Search_upd3_def Quadratic_Blossom_Search_upd4_def
    Quadratic_Blossom_Search_upd6_def finish_search_def Quadratic_Blossom_Search_call_6_conds_def scanning_target_correct(3) Let_def)

end

locale Quadratic_Blossom_Search_Extension_Imperative =
  Quadratic_Blossom_Search where K = K +
  Edge_Imp: fixed_univ_map_imp K edge_invar edge_update edge_lookup id
    edge_assn edge_update_imp edge_lookup_imp +
  Frontier: Quadratic_Blossom_Search_Path_Buffer cap frontier_invar frontier_update frontier_lookup
    frontier_assn frontier_update_imp frontier_lookup_imp
  for K :: "'v::heap set" and edge_assn and edge_update_imp edge_lookup_imp
    and frontier_invar :: "'frontier \<Rightarrow> bool" and frontier_update :: "'frontier \<Rightarrow> nat \<Rightarrow> 'v \<Rightarrow> 'frontier" and frontier_lookup
    and frontier_assn :: "'frontier \<Rightarrow> 'qi \<Rightarrow> assn" and frontier_update_imp frontier_lookup_imp +
  fixes forest_assn and forest_extend_imp :: "'fi \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> unit Heap"
  assumes forest_extend_rule: "Forest.forest_extension_precond F E x y z \<Longrightarrow>
    <forest_assn F Fi> forest_extend_imp Fi x y z <\<lambda>_. forest_assn (forest_extend F x y z) Fi>"
begin

definition "extend_into Fi P_i Qi x y z u v t = do {
  forest_extend_imp Fi x y z;
  edge_update_imp P_i y (v,u);
  edge_update_imp P_i z (z,y);
  frontier_update_imp Qi t z }"

lemma extend_into_rule:
  assumes "Forest.forest_extension_precond F M x y z" "edge_invar P"
    "y \<in> K" "z \<in> K" "frontier_invar Q" "t < cap"
  shows "<forest_assn F Fi * edge_assn P P_i * frontier_assn Q Qi>
    extend_into Fi P_i Qi x y z u v t
    <\<lambda>_. forest_assn (forest_extend F x y z) Fi *
      edge_assn (edge_update (edge_update P y (v,u)) z (z,y)) P_i *
      frontier_assn (frontier_update Q t z) Qi *
      \<up>(Frontier.buffer_view (frontier_update Q t z) 0 (Suc t) False =
        Frontier.buffer_view Q 0 t False @ [z])>"
  using assms(2-)
  unfolding extend_into_def
  by (sep_auto heap: forest_extend_rule[OF assms(1)] Frontier.append_prefix_rule
      simp: Edges.fixed_univ_map_upd_invar)
lemma extend_search_rule:
  assumes "Forest.forest_extension_precond (qbs_forest state) M x y z"
    "z = mate_partner (qbs_matching state) y" "edge_invar (qbs_forest_edges state)"
    "y \<in> K" "z \<in> K" "frontier_invar Q" "t < cap"
  shows "<forest_assn (qbs_forest state) Fi * edge_assn (qbs_forest_edges state) P_i * frontier_assn Q Qi>
    extend_into Fi P_i Qi x y z u v t
    <\<lambda>_. forest_assn (qbs_forest (extend_search state u v x y)) Fi *
      edge_assn (qbs_forest_edges (extend_search state u v x y)) P_i *
      frontier_assn (frontier_update Q t z) Qi *
      \<up>(Frontier.buffer_view (frontier_update Q t z) 0 (Suc t) False =
        Frontier.buffer_view Q 0 t False @ [z])>"
  using extend_into_rule[OF assms(1,3-7), where u=u and v=v and Fi=Fi and P_i=P_i and Qi=Qi] assms(2)
  by (simp add: extend_search_def enqueue_vertex_def Let_def)

end

section "Fused cycle bookkeeping"

locale Quadratic_Blossom_Search_Cycle_Imperative =
  Quadratic_Blossom_Search_Extension_Imperative where K = K +
  Link_Imp: fixed_univ_map_imp K link_invar link_update link_lookup id
    link_assn link_update_imp link_lookup_imp +
  Owner_Imp: fixed_univ_map_imp K owner_invar owner_update owner_lookup id
    owner_assn owner_update_imp owner_lookup_imp +
  Pool: Quadratic_Blossom_Search_Path_Buffer pool_cap pool_invar pool_update pool_lookup
    pool_assn pool_update_imp pool_lookup_imp +
  Paths: Quadratic_Blossom_Search_Path_Buffer path_cap path_invar path_update path_lookup
    path_assn path_update_imp path_lookup_imp
  for K :: "'v::heap set"
    and link_assn link_update_imp link_lookup_imp
    and owner_assn owner_update_imp owner_lookup_imp
    and pool_cap :: nat and pool_invar :: "'pool \<Rightarrow> bool"
    and pool_update :: "'pool \<Rightarrow> nat \<Rightarrow> 'v \<Rightarrow> 'pool" and pool_lookup
    and pool_assn pool_update_imp pool_lookup_imp
    and path_cap :: nat and path_invar :: "'path \<Rightarrow> bool"
    and path_update :: "'path \<Rightarrow> nat \<Rightarrow> 'v \<Rightarrow> 'path" and path_lookup
    and path_assn path_update_imp path_lookup_imp +
  fixes uf_assn and uf_union_imp :: "_ \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> unit Heap"
    and uf_find_imp and forest_classify_imp
  assumes uf_union_rule: "\<lbrakk>uf_invar U; x \<in> K; y \<in> K\<rbrakk> \<Longrightarrow>
    <uf_assn U Ui> uf_union_imp Ui x y <\<lambda>_. uf_assn (uf_union U x y) Ui>"
    and uf_find_rule: "\<lbrakk>uf_invar U; x \<in> K\<rbrakk> \<Longrightarrow>
    <uf_assn U Ui> uf_find_imp Ui x <\<lambda>r. uf_assn (snd (uf_find U x)) Ui * \<up>(r = fst (uf_find U x))>"
    and forest_classify_rule: "\<lbrakk>forest_invar M F; c \<in> K\<rbrakk> \<Longrightarrow>
    <forest_assn F Fi> forest_classify_imp Fi c
      <\<lambda>label. forest_assn F Fi * \<up>(label = (if fset_isin (forest_odds F) c then (1::nat)
        else if fset_isin (forest_evens F) c then 2 else 0))>"
begin
definition "cycle_view P plen Q qlen =
  Paths.buffer_view P 0 plen True @ Paths.buffer_view Q 0 (qlen - 1) False"

abbreviation "cycle_read P_i plen Q_i qlen \<equiv>
  Paths.joined_read P_i 0 plen True Q_i 0 (qlen - 1) False"

lemma cycle_read_rule:
  "\<lbrakk>path_invar P; path_invar Q; plen \<le> path_cap; qlen \<le> path_cap; i < plen + (qlen - 1)\<rbrakk> \<Longrightarrow>
    <path_assn P P_i * path_assn Q Q_i> cycle_read P_i plen Q_i qlen i
    <\<lambda>c. path_assn P P_i * path_assn Q Q_i * \<up>(c = cycle_view P plen Q qlen ! i)>"
  unfolding cycle_view_def
  by (intro Paths.joined_read_rule) auto

definition "cycle_edge_into E_i P_i plen Q_i qlen u v i c =
  (if Suc i < plen then do {
    next_child \<leftarrow> cycle_read P_i plen Q_i qlen (Suc i);
    edge \<leftarrow> edge_lookup_imp E_i next_child;
    return (snd edge, fst edge) }
  else if Suc i = plen then return (u,v) else edge_lookup_imp E_i c)"

definition "cycle_step_into Fi E_i B_i Ni Ui Qi Ci P_i plen Q_i qlen u v b used i t = do {
  c \<leftarrow> cycle_read P_i plen Q_i qlen i;
  edge \<leftarrow> cycle_edge_into E_i P_i plen Q_i qlen u v i c;
  label \<leftarrow> forest_classify_imp Fi c;
  t' \<leftarrow> (if label = 1 then do { frontier_update_imp Qi t c; return (Suc t) } else return t);
  uf_union_imp Ui b c;
  edge_update_imp B_i c edge;
  link_update_imp Ni c (b,i);
  pool_update_imp Ci (used + i) c;
  return t' }"

partial_function (heap) cycle_loop where
  "cycle_loop Fi E_i B_i Ni Ui Qi Ci P_i plen Q_i qlen u v b used i t =
    (if i < plen + (qlen - 1) then do {
      t' \<leftarrow> cycle_step_into Fi E_i B_i Ni Ui Qi Ci P_i plen Q_i qlen u v b used i t;
      cycle_loop Fi E_i B_i Ni Ui Qi Ci P_i plen Q_i qlen u v b used (Suc i) t' }
    else return t)"

definition "process_cycle_into Fi E_i B_i Ni Ui Oi Qi Ci P_i plen Q_i qlen u v b used t = do {
  t' \<leftarrow> cycle_loop Fi E_i B_i Ni Ui Qi Ci P_i plen Q_i qlen u v b used 0 t;
  r \<leftarrow> uf_find_imp Ui b;
  owner_update_imp Oi r b;
  return t' }"

abbreviation "cycle_witness \<equiv> Quadratic_Blossom_Search_thms.cycle_witness edge_lookup"

abbreviation "cycle_iteration \<equiv> Quadratic_Blossom_Search_thms.cycle_iteration
  fset_isin forest_odds queue_push uf_union edge_update link_update edge_lookup"

lemma cycle_view_length[simp]:
  "length (cycle_view P plen Q qlen) = plen + (qlen - 1)"
  by (simp add: cycle_view_def)


lemma cycle_edge_into_rule:
  assumes "path_invar P" "path_invar Q" "plen \<le> path_cap" "qlen \<le> path_cap"
    "edge_invar (qbs_forest_edges state)" "set (cycle_view P plen Q qlen) \<subseteq> K"
    "i < plen + (qlen - 1)"
  shows "<edge_assn (qbs_forest_edges state) E_i * path_assn P P_i * path_assn Q Q_i>
    cycle_edge_into E_i P_i plen Q_i qlen u v i (cycle_view P plen Q qlen ! i)
    <\<lambda>edge. edge_assn (qbs_forest_edges state) E_i * path_assn P P_i * path_assn Q Q_i *
      \<up>(edge = cycle_witness state (cycle_view P plen Q qlen) plen (u,v) i
        (cycle_view P plen Q qlen ! i))>"
proof-
  have keys: "cycle_view P plen Q qlen ! j \<in> K" if "j < plen + (qlen - 1)" for j
    using assms(6) that
    by (auto intro: nth_mem)
  show ?thesis
    using assms(1-5,7)
    unfolding cycle_edge_into_def
    by (sep_auto heap: cycle_read_rule simp: keys case_prod_unfold)
qed

definition "cycle_storage next T C Ui B_i Ni Qi Ci =
  uf_assn (qbs_components next) Ui * edge_assn (qbs_cycle_edges next) B_i *
    link_assn (qbs_parents next) Ni * frontier_assn T Qi * pool_assn C Ci"


definition "cycle_commit_into Ui B_i Ni Qi Ci b used i c edge was_odd t = do {
  t' \<leftarrow> (if was_odd then do { frontier_update_imp Qi t c; return (Suc t) } else return t);
  uf_union_imp Ui b c;
  edge_update_imp B_i c edge;
  link_update_imp Ni c (b,i);
  pool_update_imp Ci (used+i) c;
  return t' }"

lemma classify_odd_rule:
  "\<lbrakk>forest_invar M F; c \<in> K\<rbrakk> \<Longrightarrow>
    <forest_assn F Fi> forest_classify_imp Fi c
    <\<lambda>label. forest_assn F Fi * \<up>((label = 1) = fset_isin (forest_odds F) c)>"
  by (sep_auto heap: forest_classify_rule)

lemma cycle_commit_storage_rule:
  assumes "uf_invar (qbs_components next)" "edge_invar (qbs_cycle_edges next)"
    "link_invar (qbs_parents next)" "frontier_invar T" "pool_invar C"
    "b \<in> K" "c \<in> K" "used + i < pool_cap" "was_odd \<longrightarrow> t < cap"
  shows "<cycle_storage next T C Ui B_i Ni Qi Ci>
    cycle_commit_into Ui B_i Ni Qi Ci b used i c edge was_odd t
    <\<lambda>t'. uf_assn (uf_union (qbs_components next) b c) Ui *
      edge_assn (edge_update (qbs_cycle_edges next) c edge) B_i *
      link_assn (link_update (qbs_parents next) c (b,i)) Ni *
      frontier_assn (if was_odd then frontier_update T t c else T) Qi *
      pool_assn (pool_update C (used+i) c) Ci * \<up>(t' = (if was_odd then Suc t else t))>"
  using assms
  unfolding cycle_commit_into_def cycle_storage_def
  by (sep_auto heap: uf_union_rule)

definition "cycle_schedule_into Fi Ui B_i Ni Qi Ci b used i c edge t = do {
  label \<leftarrow> forest_classify_imp Fi c;
  cycle_commit_into Ui B_i Ni Qi Ci b used i c edge (label = 1) t }"

lemma cycle_schedule_storage_rule:
  assumes "forest_invar M F" "uf_invar (qbs_components next)"
    "edge_invar (qbs_cycle_edges next)" "link_invar (qbs_parents next)"
    "frontier_invar T" "pool_invar C" "b \<in> K" "c \<in> K" "used + i < pool_cap"
    "fset_isin (forest_odds F) c \<longrightarrow> t < cap"
  shows "<forest_assn F Fi * cycle_storage next T C Ui B_i Ni Qi Ci>
    cycle_schedule_into Fi Ui B_i Ni Qi Ci b used i c edge t
    <\<lambda>t'. forest_assn F Fi * uf_assn (uf_union (qbs_components next) b c) Ui *
      edge_assn (edge_update (qbs_cycle_edges next) c edge) B_i *
      link_assn (link_update (qbs_parents next) c (b,i)) Ni *
      frontier_assn (if fset_isin (forest_odds F) c then frontier_update T t c else T) Qi *
      pool_assn (pool_update C (used+i) c) Ci *
      \<up>(t' = (if fset_isin (forest_odds F) c then Suc t else t))>"
proof(cases "fset_isin (forest_odds F) c")
  case True
  show ?thesis
    using True
    unfolding cycle_schedule_into_def
    by (sep_auto heap: classify_odd_rule[OF assms(1,8), simplified True]
      cycle_commit_storage_rule[OF assms(2-10), simplified True])
next
  case False
  show ?thesis
    using False
    unfolding cycle_schedule_into_def
    by (sep_auto heap: classify_odd_rule[OF assms(1,8), simplified False]
      cycle_commit_storage_rule[OF assms(2-10), simplified False])
qed

lemma cycle_step_into_rule:
  assumes "forest_invar M (qbs_forest state)" "edge_invar (qbs_forest_edges state)"
    "path_invar P" "path_invar Q" "plen \<le> path_cap" "qlen \<le> path_cap"
    "set (cycle_view P plen Q qlen) \<subseteq> K" "i < plen + (qlen - 1)" "b \<in> K"
    "uf_invar (qbs_components next)" "edge_invar (qbs_cycle_edges next)"
    "link_invar (qbs_parents next)" "frontier_invar T" "pool_invar C"
    "fset_isin (forest_odds (qbs_forest state)) (cycle_view P plen Q qlen ! i) \<longrightarrow> t < cap"
    "used + i < pool_cap"
  shows "<forest_assn (qbs_forest state) Fi * edge_assn (qbs_forest_edges state) E_i *
    path_assn P P_i * path_assn Q Q_i * cycle_storage next T C Ui B_i Ni Qi Ci>
    cycle_step_into Fi E_i B_i Ni Ui Qi Ci P_i plen Q_i qlen u v b used i t
    <\<lambda>t'. let c = cycle_view P plen Q qlen ! i;
      odd = fset_isin (forest_odds (qbs_forest state)) c;
      next' = snd (cycle_iteration state (cycle_view P plen Q qlen) plen (u,v) b (i,next) c)
      in forest_assn (qbs_forest state) Fi * edge_assn (qbs_forest_edges state) E_i *
        path_assn P P_i * path_assn Q Q_i *
        cycle_storage next' (if odd then frontier_update T t c else T)
          (pool_update C (used + i) c) Ui B_i Ni Qi Ci * \<up>(t' = (if odd then Suc t else t))>"
proof-
  define c where "c = cycle_view P plen Q qlen ! i"
  define w where "w = cycle_witness state (cycle_view P plen Q qlen) plen (u,v) i c"
  have key: "c \<in> K"
    using assms(7,8)
    by (auto simp: c_def intro: nth_mem)
  have edge_read: "<edge_assn (qbs_forest_edges state) E_i * path_assn P P_i * path_assn Q Q_i> cycle_edge_into E_i P_i plen Q_i qlen u v i c <\<lambda>edge. edge_assn (qbs_forest_edges state) E_i * path_assn P P_i * path_assn Q Q_i * \<up>(edge=w)>"
    unfolding c_def w_def
    by (rule cycle_edge_into_rule[OF assms(3-6,2,7,8)])
  have refined: "<forest_assn (qbs_forest state) Fi * edge_assn (qbs_forest_edges state) E_i *
      path_assn P P_i * path_assn Q Q_i * cycle_storage next T C Ui B_i Ni Qi Ci>
      cycle_step_into Fi E_i B_i Ni Ui Qi Ci P_i plen Q_i qlen u v b used i t
      <\<lambda>t'. forest_assn (qbs_forest state) Fi * edge_assn (qbs_forest_edges state) E_i *
        path_assn P P_i * path_assn Q Q_i * uf_assn (uf_union (qbs_components next) b c) Ui *
        edge_assn (edge_update (qbs_cycle_edges next) c w) B_i *
        link_assn (link_update (qbs_parents next) c (b,i)) Ni *
        frontier_assn (if fset_isin (forest_odds (qbs_forest state)) c then frontier_update T t c else T) Qi *
        pool_assn (pool_update C (used+i) c) Ci *
        \<up>(t' = (if fset_isin (forest_odds (qbs_forest state)) c then Suc t else t))>"
    unfolding cycle_step_into_def[folded cycle_commit_into_def, folded cycle_schedule_into_def]
    by (sep_auto heap: cycle_read_rule[OF assms(3-6,8), folded c_def]
      edge_read
      cycle_schedule_storage_rule[OF assms(1,10-14,9) key assms(16) assms(15)[folded c_def], where edge=w])
  show ?thesis
    using refined[unfolded w_def c_def cycle_storage_def]
    by (auto simp: Let_def cycle_storage_def enqueue_vertex_def case_prod_beta mult.assoc split: if_splits prod.splits)
qed

end

context Quadratic_Blossom_Search_Cycle_Imperative
begin

definition "cycle_storage_valid next T C \<longleftrightarrow>
  uf_invar (qbs_components next) \<and> edge_invar (qbs_cycle_edges next) \<and>
  link_invar (qbs_parents next) \<and> frontier_invar T \<and> pool_invar C"

abbreviation "cycle_old_odd state c \<equiv> fset_isin (forest_odds (qbs_forest state)) c"

lemma cycle_storage_step:
  "\<lbrakk>cycle_storage_valid next T C; b \<in> K; c \<in> K; used + i < pool_cap;
    cycle_old_odd state c \<longrightarrow> t < cap\<rbrakk> \<Longrightarrow>
    cycle_storage_valid (snd (cycle_iteration state cs plen edge b (i,next) c))
      (if cycle_old_odd state c then frontier_update T t c else T) (pool_update C (used+i) c)"
  by (auto simp: cycle_storage_valid_def Let_def case_prod_beta enqueue_vertex_def
    intro!: Components.union_invar Edges.fixed_univ_map_upd_invar Routing.Links.fixed_univ_map_upd_invar
      Frontier.Buffer.fixed_univ_map_upd_invar Pool.Buffer.fixed_univ_map_upd_invar split: if_splits)

abbreviation "cycle_buffers state cs T C used i t T' C' t' \<equiv>
  t' = t + length (filter (cycle_old_odd state) cs) \<and>
  Frontier.buffer_view T' 0 t' False = Frontier.buffer_view T 0 t False @ filter (cycle_old_odd state) cs \<and>
  Pool.buffer_view C' 0 (used + i + length cs) False = Pool.buffer_view C 0 (used + i) False @ cs"

lemma cycle_fold_owner:
  "qbs_owners (snd (foldl (cycle_iteration state cs plen edge b) (i,s) xs)) = qbs_owners s"
  by (induction xs arbitrary: i s) (auto simp: Let_def case_prod_beta enqueue_vertex_def)

lemma cycle_finish_rule:
  assumes "b \<in> K" "cycle_storage_valid s T C" "owner_invar L"
  shows "<cycle_storage s T C Ui B_i Ni Qi Ci * owner_assn L Oi>
    (do {r \<leftarrow> uf_find_imp Ui b; owner_update_imp Oi r b; return t})
    <\<lambda>r. cycle_storage (s \<lparr>qbs_components := snd (uf_find (qbs_components s) b)\<rparr>) T C Ui B_i Ni Qi Ci *
      owner_assn (owner_update L (fst (uf_find (qbs_components s) b)) b) Oi *
      \<up>(r = t \<and> cycle_storage_valid (s \<lparr>qbs_components := snd (uf_find (qbs_components s) b)\<rparr>) T C \<and>
        owner_invar (owner_update L (fst (uf_find (qbs_components s) b)) b))>"
  using assms
  unfolding cycle_storage_def cycle_storage_valid_def
  by (sep_auto heap: uf_find_rule simp: Components.find_closed Components.find_invar Owners.fixed_univ_map_upd_invar)

context
  fixes state P Q plen qlen M b used and u v :: 'v
  assumes cycle_input: "forest_invar M (qbs_forest state)" "edge_invar (qbs_forest_edges state)"
    "path_invar P" "path_invar Q" "plen \<le> path_cap" "qlen \<le> path_cap"
    "set (cycle_view P plen Q qlen) \<subseteq> K" "b \<in> K"
    "used + length (cycle_view P plen Q qlen) \<le> pool_cap"
begin

lemma cycle_loop_rule:
  assumes "xs = drop i (cycle_view P plen Q qlen)" "i \<le> length (cycle_view P plen Q qlen)"
    "cycle_storage_valid s T C" "t + length (filter (cycle_old_odd state) xs) \<le> cap"
  shows "<forest_assn (qbs_forest state) Fi * edge_assn (qbs_forest_edges state) E_i *
    path_assn P P_i * path_assn Q Q_i * cycle_storage s T C Ui B_i Ni Qi Ci>
    cycle_loop Fi E_i B_i Ni Ui Qi Ci P_i plen Q_i qlen u v b used i t
    <\<lambda>t'. \<exists>\<^sub>AT' C'. (let next' = snd (foldl (cycle_iteration state (cycle_view P plen Q qlen) plen (u,v) b) (i,s) xs)
      in forest_assn (qbs_forest state) Fi * edge_assn (qbs_forest_edges state) E_i *
        path_assn P P_i * path_assn Q Q_i * cycle_storage next' T' C' Ui B_i Ni Qi Ci *
        \<up>(cycle_storage_valid next' T' C' \<and> cycle_buffers state xs T C used i t T' C' t'))>"
  using assms
proof(induction xs arbitrary: i s T C t)
  case Nil
  hence "i = length (cycle_view P plen Q qlen)"
    by simp
  then show ?case
    using Nil.prems(3)
    by (subst cycle_loop.simps) (sep_auto simp: Let_def)
next
  case (Cons c xs)
  have within: "i < length (cycle_view P plen Q qlen)"
    using Cons.prems(1)
    by (cases "i < length (cycle_view P plen Q qlen)") auto
  have position: "c = cycle_view P plen Q qlen ! i" "xs = drop (Suc i) (cycle_view P plen Q qlen)"
    using Cons_nth_drop_Suc[OF within]
    by (auto simp only: Cons.prems(1)[symmetric] list.inject)
  let ?s = "snd (cycle_iteration state (cycle_view P plen Q qlen) plen (u,v) b (i,s) c)"
  let ?T = "if cycle_old_odd state c then frontier_update T t c else T"
  let ?C = "pool_update C (used+i) c"
  let ?t = "if cycle_old_odd state c then Suc t else t"
  have key: "c \<in> K"
    using cycle_input(7) within position(1)
    by (auto intro: nth_mem)
  have space: "used + i < pool_cap" "cycle_old_odd state c \<longrightarrow> t < cap"
    using cycle_input(9) within Cons.prems(4)
    by (auto split: if_splits)
  have adts: "uf_invar (qbs_components s)" "edge_invar (qbs_cycle_edges s)"
    "link_invar (qbs_parents s)" "frontier_invar T" "pool_invar C"
    using Cons.prems(3)
    by (auto simp: cycle_storage_valid_def)
  have valid: "cycle_storage_valid ?s ?T ?C"
    by (rule cycle_storage_step[OF Cons.prems(3) cycle_input(8) key space])
  have capacity: "?t + length (filter (cycle_old_odd state) xs) \<le> cap"
    using Cons.prems(4)
    by auto
  note recursive = Cons.IH[OF position(2) Suc_leI[OF within] valid capacity]
  note step = cycle_step_into_rule[OF cycle_input(1-7) within[unfolded cycle_view_length]
    cycle_input(8) adts space(2)[unfolded position(1)] space(1)]
  define s1 where "s1 = ?s"
  define T1 where "T1 = ?T"
  define C1 where "C1 = ?C"
  define t1 where "t1 = ?t"
  define final where "final = snd (foldl (cycle_iteration state (cycle_view P plen Q qlen) plen (u,v) b) (Suc i,s1) xs)"
  note recursive_compact = recursive[folded s1_def T1_def C1_def t1_def final_def]
  note step_compact = step[where u = u and v = v, unfolded position(1)[symmetric] Let_def case_prod_beta,
    folded s1_def[unfolded Let_def case_prod_beta] T1_def C1_def t1_def]
  have folded: "snd (foldl (cycle_iteration state (cycle_view P plen Q qlen) plen (u,v) b) (i,s) (c # xs)) = final"
    unfolding final_def s1_def
    by (simp only: foldl.simps Let_def case_prod_beta fst_conv snd_conv)
  let ?result = "\<lambda>t'. \<exists>\<^sub>AT' C'.
      forest_assn (qbs_forest state) Fi * edge_assn (qbs_forest_edges state) E_i *
      path_assn P P_i * path_assn Q Q_i * cycle_storage final T' C' Ui B_i Ni Qi Ci *
      \<up>(cycle_storage_valid final T' C' \<and> cycle_buffers state (c#xs) T C used i t T' C' t')"
  have recursive_final: "<forest_assn (qbs_forest state) Fi * edge_assn (qbs_forest_edges state) E_i *
      path_assn P P_i * path_assn Q Q_i * cycle_storage s1 T1 C1 Ui B_i Ni Qi Ci>
      cycle_loop Fi E_i B_i Ni Ui Qi Ci P_i plen Q_i qlen u v b used (Suc i) t1 <?result>"
    by (rule ht_cons_post_prec[OF recursive_compact[unfolded Let_def case_prod_beta,
      folded final_def[unfolded Let_def case_prod_beta]]])
      (insert space, sep_auto simp: T1_def C1_def t1_def Pool.append_prefix[OF adts(5) space(1)]
        Frontier.append_prefix[OF adts(4)])
  show ?case
    unfolding folded
    by (subst cycle_loop.simps, simp only: within[unfolded cycle_view_length] if_True,
      rule ht_bind[OF step_compact]) (sep_auto heap: recursive_final simp: Let_def)
qed

end

lemma process_cycle_into_rule:
  assumes  "forest_invar M (qbs_forest state)" "edge_invar (qbs_forest_edges state)"
    "path_invar P" "path_invar Q" "plen \<le> path_cap" "qlen \<le> path_cap"
    "set (cycle_view P plen Q qlen) \<subseteq> K" "b \<in> K"
    "used + length (cycle_view P plen Q qlen) \<le> pool_cap"
    and  "cycle_storage_valid state T C" "owner_invar (qbs_owners state)"
    "t + length (filter (cycle_old_odd state) (cycle_view P plen Q qlen)) \<le> cap"
  shows "<forest_assn (qbs_forest state) Fi * edge_assn (qbs_forest_edges state) E_i *
    path_assn P P_i * path_assn Q Q_i * cycle_storage state T C Ui B_i Ni Qi Ci * owner_assn (qbs_owners state) Oi>
    process_cycle_into Fi E_i B_i Ni Ui Oi Qi Ci P_i plen Q_i qlen u v b used t
    <\<lambda>t'. \<exists>\<^sub>AT' C'. (let final = process_cycle state (cycle_view P plen Q qlen) plen (u,v) b
      in forest_assn (qbs_forest state) Fi * edge_assn (qbs_forest_edges state) E_i *
        path_assn P P_i * path_assn Q Q_i * cycle_storage final T' C' Ui B_i Ni Qi Ci *
        owner_assn (qbs_owners final) Oi * \<up>(cycle_storage_valid final T' C' \<and> owner_invar (qbs_owners final) \<and>
          cycle_buffers state (cycle_view P plen Q qlen) T C used 0 t T' C' t'))>"
proof-
  define s1 where "s1 = snd (foldl (cycle_iteration state (cycle_view P plen Q qlen) plen (u,v) b)
    (0,state) (cycle_view P plen Q qlen))"
  have owner: "qbs_owners s1 = qbs_owners state"
    unfolding s1_def
    by (rule cycle_fold_owner)
  have final: "process_cycle state (cycle_view P plen Q qlen) plen (u,v) b =
    s1 \<lparr>qbs_components := snd (uf_find (qbs_components s1) b),
      qbs_owners := owner_update (qbs_owners state) (fst (uf_find (qbs_components s1) b)) b\<rparr>"
    using owner
    unfolding s1_def process_cycle_def
    by (simp only: Let_def case_prod_beta)
  note loop = cycle_loop_rule[OF assms(1,2,3,4,5,6,7,8,9), where i = 0 and s = state and u = u and v = v and xs = "cycle_view P plen Q qlen",
    OF _ _ assms(10,12), simplified, unfolded Let_def case_prod_beta, folded s1_def[unfolded Let_def case_prod_beta]]
  define finish where "finish = (\<lambda>t'::nat. do {r \<leftarrow> uf_find_imp Ui b; owner_update_imp Oi r b; return t'})"
  note finish = cycle_finish_rule[OF assms(8) _ assms(11), where Ui = Ui and Oi = Oi
      and t = "t + length (filter (cycle_old_odd state) (cycle_view P plen Q qlen))",
    folded finish_def[THEN fun_cong, simplified]]
  show ?thesis
    unfolding process_cycle_into_def
    by (fold finish_def[THEN fun_cong, simplified])
      (sep_auto heap: loop finish[unfolded cycle_storage_def cycle_storage_valid_def]
      simp: Let_def final cycle_storage_def cycle_storage_valid_def)
qed

end

section "Initializing the search in caller-owned storage"

locale Quadratic_Blossom_Search_Initialisation_Imperative =
  Quadratic_Blossom_Search where K = K +
  Owner_Imp: fixed_univ_map_imp K owner_invar owner_update owner_lookup id
    owner_assn owner_update_imp owner_lookup_imp +
  Base_Imp: fixed_univ_map_imp K base_invar base_update base_lookup id
    base_assn base_update_imp base_lookup_imp +
  Frontier: Quadratic_Blossom_Search_Path_Buffer cap frontier_invar frontier_update frontier_lookup
    frontier_assn frontier_update_imp frontier_lookup_imp
  for K :: "'v::heap set"
    and owner_assn owner_update_imp owner_lookup_imp
    and base_assn base_update_imp base_lookup_imp
    and frontier_invar :: "'frontier \<Rightarrow> bool"
    and frontier_update :: "'frontier \<Rightarrow> nat \<Rightarrow> 'v \<Rightarrow> 'frontier" and frontier_lookup
    and frontier_assn frontier_update_imp frontier_lookup_imp +
  fixes vertex_at :: "nat \<Rightarrow> 'v"
    and forest_assn :: "_ \<Rightarrow> 'fi \<Rightarrow> assn"
    and forest_workspace_assn :: "'fi \<Rightarrow> assn"
    and matching_assn :: "_ \<Rightarrow> 'mi \<Rightarrow> assn"
    and mate_read_imp :: "'mi \<Rightarrow> 'v \<Rightarrow> 'v Heap"
    and forest_clear_into :: "'fi \<Rightarrow> unit Heap"
    and forest_root_into :: "'fi \<Rightarrow> 'v \<Rightarrow> unit Heap"
  assumes mate_read_rule: "\<lbrakk>mate_invar input_graph M0; v \<in> V0\<rbrakk> \<Longrightarrow>
    <matching_assn M0 Mi> mate_read_imp Mi v <\<lambda>z. matching_assn M0 Mi * \<up>(z = mate_partner M0 v)>"
    and forest_clear_rule: "<forest_workspace_assn Fi> forest_clear_into Fi
      <\<lambda>_. forest_assn (forest_empty fset_empty) Fi>"
    and forest_root_rule: "\<lbrakk>fset_invar S; v \<in> K\<rbrakk> \<Longrightarrow>
      <forest_assn (forest_empty S) Fi> forest_root_into Fi v
      <\<lambda>_. forest_assn (forest_empty (fset_insert v S)) Fi>"
begin

definition "initial_vertex_models model v =
  (case model of (S,L,D,T,t) \<Rightarrow> let L' = owner_update L v v; D' = base_update D v v in
   if mate_partner M0 v = nil
   then (fset_insert v S,L',D',frontier_update T t v,Suc t)
   else (S,L',D',T,t))"

definition "initial_models_valid model \<longleftrightarrow>
  (case model of (S,L,D,T,t) \<Rightarrow> fset_invar S \<and> owner_invar L \<and> base_invar D \<and> frontier_invar T)"

definition "initial_storage model Fi Oi Di Qi =
  (case model of (S,L,D,T,t) \<Rightarrow> forest_assn (forest_empty S) Fi * owner_assn L Oi * base_assn D Di * frontier_assn T Qi)"

abbreviation "initial_tail model \<equiv> snd (snd (snd (snd model)))"

definition "initial_vertex_into Mi Fi Oi Di Qi v t = do {
  owner_update_imp Oi v v;
  base_update_imp Di v v;
  z \<leftarrow> mate_read_imp Mi v;
  if z = nil then do {forest_root_into Fi v; frontier_update_imp Qi t v; return (Suc t)}
  else return t }"

partial_function (heap) initial_vertices_into where
  "initial_vertices_into Mi Fi Oi Di Qi n i t =
    (if i < n then do {
      t' \<leftarrow> initial_vertex_into Mi Fi Oi Di Qi (vertex_at i) t;
      initial_vertices_into Mi Fi Oi Di Qi n (Suc i) t' }
    else return t)"


lemma initial_vertex_valid:
  "\<lbrakk>initial_models_valid model; v \<in> K; initial_tail model < cap\<rbrakk> \<Longrightarrow>
    initial_models_valid (initial_vertex_models model v)"
  by(cases model) (auto simp: initial_models_valid_def initial_vertex_models_def Let_def
      Owners.fixed_univ_map_upd_invar Routing.Bases.fixed_univ_map_upd_invar
      Frontier.Buffer.fixed_univ_map_upd_invar Fset.fixed_univ_set_insert split: prod.splits if_splits)

lemma initial_vertex_into_rule:
  "\<lbrakk>initial_models_valid model; v \<in> K \<inter> V0; initial_tail model < cap; mate_invar input_graph M0\<rbrakk> \<Longrightarrow>
    <matching_assn M0 Mi * initial_storage model Fi Oi Di Qi>
      initial_vertex_into Mi Fi Oi Di Qi v (initial_tail model)
    <\<lambda>t. matching_assn M0 Mi * initial_storage (initial_vertex_models model v) Fi Oi Di Qi *
      \<up>(t = initial_tail (initial_vertex_models model v))>"
  unfolding initial_models_valid_def initial_storage_def initial_vertex_models_def initial_vertex_into_def
  by(sep_auto heap: mate_read_rule forest_root_rule simp: Let_def split: prod.splits)

lemma initial_vertex_tail:
  "initial_tail (initial_vertex_models model v) \<le> Suc (initial_tail model)"
  by(cases model) (auto simp: initial_vertex_models_def Let_def split: prod.splits)

lemma initial_vertices_into_rule:
  assumes "initial_models_valid model" "initial_tail model + (n-i) \<le> cap"
    "set (map vertex_at [i..<n]) \<subseteq> K \<inter> V0" "mate_invar input_graph M0"
  shows "<matching_assn M0 Mi * initial_storage model Fi Oi Di Qi>
    initial_vertices_into Mi Fi Oi Di Qi n i (initial_tail model)
    <\<lambda>t. let final = foldl initial_vertex_models model (map vertex_at [i..<n]) in
      matching_assn M0 Mi * initial_storage final Fi Oi Di Qi * \<up>(t = initial_tail final)>"
  using assms
proof(induction "n-i" arbitrary: i model rule: less_induct)
  case IH: less
  show ?case
  proof(cases "i<n")
    case True
    have key: "vertex_at i \<in> K \<inter> V0" "set (map vertex_at [Suc i..<n]) \<subseteq> K \<inter> V0"
      using IH.prems(3) True
      by(auto simp: upt_conv_Cons)
    have valid: "initial_models_valid (initial_vertex_models model (vertex_at i))"
      using IH.prems(1,2) True key(1)
      by(intro initial_vertex_valid) auto
    have bounds: "initial_tail model < cap"
      "initial_tail (initial_vertex_models model (vertex_at i)) + (n - Suc i) \<le> cap"
      using IH.prems(2) True initial_vertex_tail[of model "vertex_at i"]
      by arith+
    have step: "<matching_assn M0 Mi * initial_storage (initial_vertex_models model (vertex_at i)) Fi Oi Di Qi>
      initial_vertices_into Mi Fi Oi Di Qi n (Suc i) (initial_tail (initial_vertex_models model (vertex_at i)))
      <\<lambda>t. let final = foldl initial_vertex_models model (map vertex_at [i..<n]) in
        matching_assn M0 Mi * initial_storage final Fi Oi Di Qi * \<up>(t = initial_tail final)>"
      using IH.hyps[of "Suc i" "initial_vertex_models model (vertex_at i)"] True valid bounds(2) key(2) IH.prems(4)
      by(simp add: upt_conv_Cons)
    show ?thesis
      by(subst initial_vertices_into.simps)
        (sep_auto simp: True heap: initial_vertex_into_rule[OF IH.prems(1) key(1) bounds(1) IH.prems(4)] step)
  next
    case False
    thus ?thesis
      by(subst initial_vertices_into.simps) (sep_auto simp: initial_storage_def)
  qed
qed

lemma initial_models_fold:
  assumes "initial_models_valid (S,L,D,T,t)" "set xs \<subseteq> K" "t + length xs \<le> cap"
  shows "(let final = foldl initial_vertex_models (S,L,D,T,t) xs in
    initial_models_valid final \<and>
    fst final = fst (foldl (\<lambda>(S,Q) v. if mate_partner M0 v = nil
      then (fset_insert v S,queue_push Q v) else (S,Q)) (S,Q) xs) \<and>
    fst (snd final) = foldl (\<lambda>L v. owner_update L v v) L xs \<and>
    fst (snd (snd final)) = Routing.initial_bases D xs \<and>
    initial_tail final = t + length (filter (\<lambda>v. mate_partner M0 v = nil) xs) \<and>
    Frontier.buffer_view (fst (snd (snd (snd final)))) 0 (initial_tail final) False =
      Frontier.buffer_view T 0 t False @ filter (\<lambda>v. mate_partner M0 v = nil) xs)"
  using assms
proof(induction xs arbitrary: S L D T t Q)
  case Nil
  thus ?case
    by(simp add: Routing.initial_bases_def)
next
  case IH: (Cons v xs)
  show ?case
    using IH.IH[of "if mate_partner M0 v = nil then fset_insert v S else S"
      "owner_update L v v" "base_update D v v"
      "if mate_partner M0 v = nil then frontier_update T t v else T"
      "if mate_partner M0 v = nil then Suc t else t"
      "if mate_partner M0 v = nil then queue_push Q v else Q"] IH.prems
    by(auto simp: initial_models_valid_def initial_vertex_models_def Routing.initial_bases_def Let_def
      Owners.fixed_univ_map_upd_invar Routing.Bases.fixed_univ_map_upd_invar
      Frontier.Buffer.fixed_univ_map_upd_invar Fset.fixed_univ_set_insert
      Frontier.append_prefix case_prod_beta split: if_splits)
qed

definition "initial_models L D T = foldl initial_vertex_models (fset_empty,L,D,T,0) vs"

definition "initial_roots_into Mi Fi Oi Di Qi n = do {
  forest_clear_into Fi;
  initial_vertices_into Mi Fi Oi Di Qi n 0 0 }"

lemma initial_roots_into_rule:
  assumes "owner_invar L" "base_invar D" "frontier_invar T"
    "map vertex_at [0..<n] = vs" "n \<le> cap" "set vs \<subseteq> K \<inter> V0" "mate_invar input_graph M0"
  shows "<matching_assn M0 Mi * forest_workspace_assn Fi * owner_assn L Oi * base_assn D Di * frontier_assn T Qi>
    initial_roots_into Mi Fi Oi Di Qi n
    <\<lambda>t. matching_assn M0 Mi * initial_storage (initial_models L D T) Fi Oi Di Qi *
      \<up>(t = initial_tail (initial_models L D T))>"
proof-
  have valid: "initial_models_valid (fset_empty,L,D,T,0)"
    using assms(1-3)
    by(simp add: initial_models_valid_def Fset.fixed_univ_set_empty)
  have loop: "<matching_assn M0 Mi * forest_assn (forest_empty fset_empty) Fi * owner_assn L Oi * base_assn D Di * frontier_assn T Qi>
    initial_vertices_into Mi Fi Oi Di Qi n 0 0
    <\<lambda>t. matching_assn M0 Mi * initial_storage (initial_models L D T) Fi Oi Di Qi *
      \<up>(t = initial_tail (initial_models L D T))>"
    using initial_vertices_into_rule[OF valid, of n 0] assms(4-7)
    by(auto simp: initial_storage_def initial_models_def assn_times_assoc Let_def)
  show ?thesis
    unfolding initial_roots_into_def
    by(sep_auto heap: forest_clear_rule loop)
qed

lemma initial_models_props:
  assumes "owner_invar L" "base_invar D" "frontier_invar T" "set vs \<subseteq> K" "length vs \<le> cap"
  shows "initial_models_valid (initial_models L D T)"
    "fst (initial_models L D T) = fst initial_frontier"
    "fst (snd (initial_models L D T)) = foldl (\<lambda>L v. owner_update L v v) L vs"
    "fst (snd (snd (initial_models L D T))) = Routing.initial_bases D vs"
    "initial_tail (initial_models L D T) = length (queue_abstract (snd initial_frontier))"
    "Frontier.buffer_view (fst (snd (snd (snd (initial_models L D T))))) 0
      (initial_tail (initial_models L D T)) False = queue_abstract (snd initial_frontier)"
  using initial_models_fold[of fset_empty L D T 0 vs queue_empty]
    initial_frontier_fold[of fset_empty queue_empty vs] assms
  by(auto simp: initial_models_def initial_models_valid_def initial_frontier_def
      Fset.fixed_univ_set_empty Work.queue_empty Frontier.buffer_view_def Let_def)

end

section "Imperative exploration and contraction"

locale Quadratic_Blossom_Search_Buffer =
  fixes nil :: "'v::heap" and empty_cursor :: 'iterator and first_fresh :: nat
    and fresh_vertex :: "nat \<Rightarrow> 'v"
    and initialise_into :: "'gi \<Rightarrow> 'mi \<Rightarrow> 'wi \<Rightarrow> nat Heap"
    and frontier_read :: "'wi \<Rightarrow> nat \<Rightarrow> 'v Heap"
    and representative_imp :: "'wi \<Rightarrow> 'v \<Rightarrow> 'v Heap"
    and row_begin :: "'gi \<Rightarrow> 'v \<Rightarrow> 'iterator Heap"
    and row_has :: "'iterator \<Rightarrow> bool"
    and row_read :: "'gi \<Rightarrow> 'iterator \<Rightarrow> 'v Heap"
    and row_advance :: "'iterator \<Rightarrow> 'iterator"
    and classify :: "'wi \<Rightarrow> 'v \<Rightarrow> nat Heap"
    and mate_read :: "'mi \<Rightarrow> 'v \<Rightarrow> 'v Heap"
    and extend_into :: "'wi \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> nat \<Rightarrow> unit Heap"
    and paths_into :: "'wi \<Rightarrow> nat \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> (bool \<times> nat \<times> nat) Heap"
    and contract_into :: "'wi \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'v \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat Heap"
    and recover_into :: "'wi \<Rightarrow> 'bi \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat Heap"
begin

context fixes Gi :: 'gi and Mi :: 'mi and Wi :: 'wi and Bi :: 'bi begin

partial_function (heap) search_loop ::
  "'v \<Rightarrow> 'v \<Rightarrow> 'iterator \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "search_loop u x it h t fresh pool_used =
    (if u = nil then
       if h = t then return 0
       else do {
         v \<leftarrow> frontier_read Wi h;
         y \<leftarrow> representative_imp Wi v;
         row \<leftarrow> row_begin Gi v;
         search_loop v y row (Suc h) t fresh pool_used }
     else if \<not> row_has it then search_loop nil nil it h t fresh pool_used
     else do {
       v \<leftarrow> row_read Gi it;
       y \<leftarrow> representative_imp Wi v;
       if x = y then search_loop u x (row_advance it) h t fresh pool_used
       else do {
         label \<leftarrow> classify Wi y;
         if label = 1 then search_loop u x (row_advance it) h t fresh pool_used
         else if label = 0 then do {
           z \<leftarrow> mate_read Mi v;
           extend_into Wi x y z u v t;
           search_loop u x (row_advance it) h (Suc t) fresh pool_used }
         else do {
           paths \<leftarrow> paths_into Wi (Suc (fresh - first_fresh)) x y;
           if fst paths then do {
             t' \<leftarrow> contract_into Wi u v (fst (snd paths)) (snd (snd paths)) (fresh_vertex fresh) t pool_used;
             search_loop u (fresh_vertex fresh) (row_advance it) h t' (Suc fresh)
               (pool_used + (fst (snd paths) + snd (snd paths) - 1)) }
           else recover_into Wi Bi u v (fst (snd paths)) (snd (snd paths)) } } })"

end

definition "search_into Gi Mi Wi Bi = do {
  t \<leftarrow> initialise_into Gi Mi Wi;
  search_loop Gi Mi Wi Bi nil nil empty_cursor 0 t first_fresh 0 }"

end

locale Quadratic_Blossom_Search_Buffer_Refinement =
  Quadratic_Blossom_Search_thms where nil = nil +
  Runtime: Quadratic_Blossom_Search_Buffer where nil = nil and empty_cursor = empty_cursor
    and initialise_into = initialise_into and recover_into = recover_into
  for nil :: "'v::heap" and empty_cursor :: 'iterator
    and initialise_into :: "'gi \<Rightarrow> 'mi \<Rightarrow> 'wi \<Rightarrow> nat Heap"
    and recover_into :: "'wi \<Rightarrow> 'bi \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat Heap" +
  fixes registers :: "_ \<Rightarrow> 'iterator \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
    and workspace_assn :: "_ \<Rightarrow> 'iterator \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      'gi \<Rightarrow> 'mi \<Rightarrow> 'wi \<Rightarrow> 'bi \<Rightarrow> assn"
    and paths_assn :: "_ \<Rightarrow> 'iterator \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> 'gi \<Rightarrow> 'mi \<Rightarrow> 'wi \<Rightarrow> 'bi \<Rightarrow> assn"
    and input_assn :: "'gi \<Rightarrow> 'mi \<Rightarrow> 'wi \<Rightarrow> 'bi \<Rightarrow> assn"
    and output_assn :: "'v list \<Rightarrow> 'gi \<Rightarrow> 'mi \<Rightarrow> 'wi \<Rightarrow> 'bi \<Rightarrow> assn"
  assumes register_queue:
    "registers state it h t fresh pool_used \<Longrightarrow> queue_is_empty (qbs_queue state) = (h = t)"
    and register_cursor:
    "\<lbrakk>registers state it h t fresh pool_used; qbs_current state \<noteq> nil\<rbrakk> \<Longrightarrow>
      row_has it = cursor_has (qbs_neighbours state) (qbs_current state)"
    and initialise_rule:
    "<input_assn Gi Mi Wi Bi> initialise_into Gi Mi Wi
      <\<lambda>t. workspace_assn initial_search_state empty_cursor 0 t first_fresh 0 Gi Mi Wi Bi *
        \<up>(registers initial_search_state empty_cursor 0 t first_fresh 0)>"
    and exhausted_entails:
    "\<lbrakk>Quadratic_Blossom_Search_call_1_conds state; invar_search state; registers state it h t fresh pool_used\<rbrakk>
      \<Longrightarrow> workspace_assn state it h t fresh pool_used Gi Mi Wi Bi \<Longrightarrow>\<^sub>A
        (\<exists>\<^sub>Axs. output_assn xs Gi Mi Wi Bi * \<up>(length xs = output_cap))"
    and frontier_read_rule:
    "\<lbrakk>Quadratic_Blossom_Search_call_2_conds state; invar_search state; registers state it h t fresh pool_used\<rbrakk>
      \<Longrightarrow> <workspace_assn state it h t fresh pool_used Gi Mi Wi Bi> frontier_read Wi h
        <\<lambda>v. workspace_assn state it h t fresh pool_used Gi Mi Wi Bi *
          \<up>(v = hd (queue_abstract (qbs_queue state)))>"
    and representative_rule:
    "\<lbrakk>invar_search state; registers state it h t fresh pool_used; v \<in> V0\<rbrakk>
      \<Longrightarrow> <workspace_assn state it h t fresh pool_used Gi Mi Wi Bi> representative_imp Wi v
        <\<lambda>x. workspace_assn state it h t fresh pool_used Gi Mi Wi Bi * \<up>(x = representative state v)>"
    and row_begin_rule:
    "\<lbrakk>Quadratic_Blossom_Search_call_2_conds state; invar_search state; registers state it h t fresh pool_used\<rbrakk>
      \<Longrightarrow> <workspace_assn state it h t fresh pool_used Gi Mi Wi Bi>
        row_begin Gi (hd (queue_abstract (qbs_queue state)))
        <\<lambda>row. workspace_assn (Quadratic_Blossom_Search_upd2 state) row (Suc h) t fresh pool_used Gi Mi Wi Bi *
          \<up>(registers (Quadratic_Blossom_Search_upd2 state) row (Suc h) t fresh pool_used)>"
    and row_finished_entails:
    "\<lbrakk>Quadratic_Blossom_Search_call_3_conds state; invar_search state; registers state it h t fresh pool_used\<rbrakk>
      \<Longrightarrow> workspace_assn state it h t fresh pool_used Gi Mi Wi Bi \<Longrightarrow>\<^sub>A
        workspace_assn (Quadratic_Blossom_Search_upd3 state) it h t fresh pool_used Gi Mi Wi Bi *
          \<up>(registers (Quadratic_Blossom_Search_upd3 state) it h t fresh pool_used)"
    and row_read_rule:
    "\<lbrakk>scanning_edge state; invar_search state; registers state it h t fresh pool_used\<rbrakk>
      \<Longrightarrow> <workspace_assn state it h t fresh pool_used Gi Mi Wi Bi> row_read Gi it
        <\<lambda>v. workspace_assn state it h t fresh pool_used Gi Mi Wi Bi * \<up>(v = scanned_neighbour state)>"
    and classify_rule:
    "\<lbrakk>scanning_edge state; invar_search state; registers state it h t fresh pool_used\<rbrakk>
      \<Longrightarrow> <workspace_assn state it h t fresh pool_used Gi Mi Wi Bi> classify Wi (target_component state)
        <\<lambda>label. workspace_assn state it h t fresh pool_used Gi Mi Wi Bi *
          \<up>(label = (if fset_isin (forest_odds (qbs_forest state)) (target_component state) then 1
            else if fset_isin (forest_evens (qbs_forest state)) (target_component state) then 2 else 0))>"
    and skipped_edge_entails:
    "\<lbrakk>Quadratic_Blossom_Search_call_4_conds state; invar_search state; registers state it h t fresh pool_used\<rbrakk>
      \<Longrightarrow> workspace_assn state it h t fresh pool_used Gi Mi Wi Bi \<Longrightarrow>\<^sub>A
        workspace_assn (Quadratic_Blossom_Search_upd4 state) (row_advance it) h t fresh pool_used Gi Mi Wi Bi *
          \<up>(registers (Quadratic_Blossom_Search_upd4 state) (row_advance it) h t fresh pool_used)"
    and mate_read_rule:
    "\<lbrakk>invar_search state; registers state it h t fresh pool_used; v \<in> V0\<rbrakk>
      \<Longrightarrow> <workspace_assn state it h t fresh pool_used Gi Mi Wi Bi> mate_read Mi v
        <\<lambda>z. workspace_assn state it h t fresh pool_used Gi Mi Wi Bi * \<up>(z = mate_partner M0 v)>"
    and extend_rule:
    "\<lbrakk>Quadratic_Blossom_Search_call_5_conds state; invar_search state; registers state it h t fresh pool_used\<rbrakk>
      \<Longrightarrow> <workspace_assn state it h t fresh pool_used Gi Mi Wi Bi>
        extend_into Wi (source_component state) (target_component state)
          (mate_partner (qbs_matching state) (target_component state)) (scanned_vertex state) (scanned_neighbour state) t
        <\<lambda>_. workspace_assn (Quadratic_Blossom_Search_upd5 state) (row_advance it) h (Suc t) fresh pool_used Gi Mi Wi Bi *
          \<up>(registers (Quadratic_Blossom_Search_upd5 state) (row_advance it) h (Suc t) fresh pool_used)>"
    and paths_rule:
    "\<lbrakk>Quadratic_Blossom_Search_call_6_conds state \<or> Quadratic_Blossom_Search_call_7_conds state;
        invar_search state; registers state it h t fresh pool_used\<rbrakk>
      \<Longrightarrow> <workspace_assn state it h t fresh pool_used Gi Mi Wi Bi>
        paths_into Wi (Suc (fresh - first_fresh)) (source_component state) (target_component state)
        <\<lambda>r. paths_assn state it h t fresh pool_used (fst (snd r)) (snd (snd r)) Gi Mi Wi Bi *
          \<up>(fst r = (last (forest_path (qbs_forest state) (source_component state)) =
            last (forest_path (qbs_forest state) (target_component state))))>"
    and contract_rule:
    "\<lbrakk>Quadratic_Blossom_Search_call_7_conds state; invar_search state; registers state it h t fresh pool_used\<rbrakk>
      \<Longrightarrow> <paths_assn state it h t fresh pool_used n m Gi Mi Wi Bi>
        contract_into Wi (scanned_vertex state) (scanned_neighbour state) n m (fresh_vertex fresh) t pool_used
        <\<lambda>t'. workspace_assn (Quadratic_Blossom_Search_upd7 state) (row_advance it) h t' (Suc fresh) (pool_used + (n + m - 1)) Gi Mi Wi Bi *
          \<up>(registers (Quadratic_Blossom_Search_upd7 state) (row_advance it) h t' (Suc fresh) (pool_used + (n + m - 1)) \<and>
            qbs_component (Quadratic_Blossom_Search_upd7 state) = fresh_vertex fresh)>"
    and recover_rule:
    "\<lbrakk>Quadratic_Blossom_Search_call_6_conds state; invar_search state; registers state it h t fresh pool_used\<rbrakk>
      \<Longrightarrow> <paths_assn state it h t fresh pool_used n m Gi Mi Wi Bi>
        recover_into Wi Bi (scanned_vertex state) (scanned_neighbour state) n m
        <\<lambda>k. \<exists>\<^sub>Axs. output_assn xs Gi Mi Wi Bi * \<up>(length xs = output_cap \<and> k \<le> output_cap \<and>
          take k xs = Recovery.recovered_path (result_path (Quadratic_Blossom_Search_upd6 state) T0 out0))>"
begin

abbreviation "source_register state \<equiv> if qbs_current state = nil then nil else qbs_component state"

definition "search_result_assn state k Gi Mi Wi Bi =
  (\<exists>\<^sub>Axs. output_assn xs Gi Mi Wi Bi * \<up>(length xs = output_cap \<and> k \<le> output_cap \<and>
    take k xs = Recovery.recovered_path (result_path state T0 out0)))"
lemma search_stopped:
  assumes "qbs_status state \<noteq> Quadratic_Searching"
  shows "Quadratic_Blossom_Search state = state"
proof-
  have "Quadratic_Blossom_Search_dom state"
    by (rule Quadratic_Blossom_Search.domintros) (simp add: assms)
  then show ?thesis
    using assms
    by (simp add: Quadratic_Blossom_Search.psimps)
qed

lemma search_terminal_step:
  "\<lbrakk>Quadratic_Blossom_Search_dom state; Quadratic_Blossom_Search_call_1_conds state\<rbrakk>
   \<Longrightarrow> Quadratic_Blossom_Search state = Quadratic_Blossom_Search_upd1 state"
  "\<lbrakk>Quadratic_Blossom_Search_dom state; Quadratic_Blossom_Search_call_6_conds state\<rbrakk>
   \<Longrightarrow> Quadratic_Blossom_Search state = Quadratic_Blossom_Search_upd6 state"
  by (subst Quadratic_Blossom_Search_simps(1),
      auto simp: search_stopped Quadratic_Blossom_Search_upd1_def)
    (subst Quadratic_Blossom_Search_simps(6),
      auto simp: search_stopped Quadratic_Blossom_Search_upd6_def finish_search_def Let_def)
lemma exhausted_refine:
  assumes "Quadratic_Blossom_Search_call_1_conds state" "invar_search state"
    "registers state it h t fresh pool_used"
  shows "<workspace_assn state it h t fresh pool_used Gi Mi Wi Bi> return 0
    <\<lambda>k. search_result_assn (Quadratic_Blossom_Search_upd1 state) k Gi Mi Wi Bi>"
  by (rule ht_cons_pre[OF exhausted_entails[OF assms]])
    (sep_auto simp: search_result_assn_def result_path_def Quadratic_Blossom_Search_upd1_def
      Recovery.initial_recovery_def Recovery.recovered_path_def)
lemma scanning_register_props:
  assumes "scanning_edge state" "invar_search state" "registers state it h t fresh pool_used"
  shows "qbs_current state \<noteq> nil" "row_has it" "scanned_neighbour state \<in> V0"
    "target_component state = representative state (scanned_neighbour state)"
  using assms register_cursor[OF assms(3)] scanning_neighbour[of state] scanning_target_correct[of state]
  by (auto elim!: invar_search_props simp: scanning_edge_def)
lemma search_loop_refine:
  assumes "Quadratic_Blossom_Search_dom state" "invar_search state"
    "qbs_status state = Quadratic_Searching" "registers state it h t fresh pool_used"
  shows "<workspace_assn state it h t fresh pool_used Gi Mi Wi Bi>
    Runtime.search_loop Gi Mi Wi Bi (qbs_current state) (source_register state) it h t fresh pool_used
    <\<lambda>k. search_result_assn (Quadratic_Blossom_Search state) k Gi Mi Wi Bi>"
  using assms(2-4)
proof(induction arbitrary: it h t fresh pool_used rule: Quadratic_Blossom_Search_induct[OF assms(1)])
  case IH: (1 state)
  note equations = Quadratic_Blossom_Search_simps[OF IH.hyps(1)]
  show ?case
  proof(rule Quadratic_Blossom_Search_cases[where state = state])
    assume call: "Quadratic_Blossom_Search_call_1_conds state"
    have current: "qbs_current state = nil" and queue: "h = t"
      using call register_queue[OF IH.prems(3)]
      by (auto simp: Quadratic_Blossom_Search_call_1_conds_def)
    show ?thesis
      by (subst Runtime.search_loop.simps, simp only: if_P[OF current] if_P[OF queue]
        search_terminal_step(1)[OF IH.hyps(1) call])
        (rule exhausted_refine[OF call IH.prems(1,3)])
  next
    assume call: "Quadratic_Blossom_Search_call_2_conds state"
    have current: "qbs_current state = nil" and queue: "h \<noteq> t"
      using call register_queue[OF IH.prems(3)]
      by (auto simp: Quadratic_Blossom_Search_call_2_conds_def)
    have vertex: "hd (queue_abstract (qbs_queue state)) \<in> V0"
      using call IH.prems(1) start_scan_source[of state]
      by (auto elim!: invar_search_props)
    have step: "registers (Quadratic_Blossom_Search_upd2 state) row (Suc h) t fresh pool_used \<Longrightarrow>
      <workspace_assn (Quadratic_Blossom_Search_upd2 state) row (Suc h) t fresh pool_used Gi Mi Wi Bi>
        Runtime.search_loop Gi Mi Wi Bi (hd (queue_abstract (qbs_queue state)))
          (representative state (hd (queue_abstract (qbs_queue state)))) row (Suc h) t fresh pool_used
        <\<lambda>k. search_result_assn (Quadratic_Blossom_Search state) k Gi Mi Wi Bi>" for row
      using IH.IH(2)[OF call invar_search_holds_2[OF call IH.prems(1)]] IH.prems(1,2) call
      by (auto elim!: invar_search_props simp: start_scan_props[OF call] start_scan_source[OF call]
        equations(2))
    show ?thesis
      by (subst Runtime.search_loop.simps, simp only: if_P[OF current] if_not_P[OF queue])
        (sep_auto heap: frontier_read_rule
          representative_rule row_begin_rule step simp: call IH.prems vertex)
  next
    assume call: "Quadratic_Blossom_Search_call_3_conds state"
    have current: "qbs_current state \<noteq> nil" and row: "\<not> row_has it"
      using call register_cursor[OF IH.prems(3)]
      by (auto simp: Quadratic_Blossom_Search_call_3_conds_def)
    have step: "registers (Quadratic_Blossom_Search_upd3 state) it h t fresh pool_used \<Longrightarrow>
      <workspace_assn (Quadratic_Blossom_Search_upd3 state) it h t fresh pool_used Gi Mi Wi Bi>
        Runtime.search_loop Gi Mi Wi Bi nil nil it h t fresh pool_used
        <\<lambda>k. search_result_assn (Quadratic_Blossom_Search state) k Gi Mi Wi Bi>"
      using IH.IH(3)[OF call invar_search_holds_3[OF call IH.prems(1)]] IH.prems(2) call
      by (simp add: Quadratic_Blossom_Search_upd3_def
        equations(3))
    show ?thesis
      by (subst Runtime.search_loop.simps, simp only: if_not_P[OF current] if_P[OF row],
        rule ht_cons_pre[OF row_finished_entails[OF call IH.prems(1,3)]])
        (sep_auto heap: step)
  next
    assume call: "Quadratic_Blossom_Search_call_4_conds state"
    have scan: "scanning_edge state" and choice:
      "source_component state = target_component state \<or>
        fset_isin (forest_odds (qbs_forest state)) (target_component state)"
      using call
      by (auto simp: Quadratic_Blossom_Search_call_4_conds_def)
    note observed = scanning_register_props[OF scan IH.prems(1,3)]
    have step: "registers (Quadratic_Blossom_Search_upd4 state) (row_advance it) h t fresh pool_used \<Longrightarrow>
      <workspace_assn (Quadratic_Blossom_Search_upd4 state) (row_advance it) h t fresh pool_used Gi Mi Wi Bi>
        Runtime.search_loop Gi Mi Wi Bi (qbs_current state) (qbs_component state) (row_advance it) h t fresh pool_used
        <\<lambda>k. search_result_assn (Quadratic_Blossom_Search state) k Gi Mi Wi Bi>"
      using IH.IH(4)[OF call invar_search_holds_4[OF call IH.prems(1)]] IH.prems(2) observed(1) call
      by (simp add: Quadratic_Blossom_Search_upd4_def
        equations(4))
    have skip: "<workspace_assn state it h t fresh pool_used Gi Mi Wi Bi>
        Runtime.search_loop Gi Mi Wi Bi (qbs_current state) (qbs_component state) (row_advance it) h t fresh pool_used
        <\<lambda>k. search_result_assn (Quadratic_Blossom_Search state) k Gi Mi Wi Bi>"
      by (rule ht_cons_pre[OF skipped_edge_entails[OF call IH.prems(1,3)]])
        (sep_auto heap: step)
    show ?thesis
    proof(cases "source_component state = target_component state")
      case True
      show ?thesis
        by (subst Runtime.search_loop.simps, simp only: if_not_P[OF observed(1)] observed(2) not_True_eq_False if_False)
          (sep_auto heap: row_read_rule
            representative_rule[where state=state and v="scanned_neighbour state", folded observed(4)]
            skip[unfolded True] simp: True call IH.prems scan observed(3))
    next
      case False
      have odd: "fset_isin (forest_odds (qbs_forest state)) (target_component state)"
        using choice False
        by auto
      show ?thesis
        by (subst Runtime.search_loop.simps, simp only: if_not_P[OF observed(1)] observed(2) not_True_eq_False if_False)
          (sep_auto heap: row_read_rule
            representative_rule[where state=state and v="scanned_neighbour state", folded observed(4)]
            classify_rule[where state=state, simplified odd] skip simp: False call IH.prems scan observed(3) odd)
    qed
  next
    assume call: "Quadratic_Blossom_Search_call_5_conds state"
    have scan: "scanning_edge state" and labels:
      "source_component state \<noteq> target_component state"
      "\<not> fset_isin (forest_odds (qbs_forest state)) (target_component state)"
      "\<not> fset_isin (forest_evens (qbs_forest state)) (target_component state)"
      using call
      by (auto simp: Quadratic_Blossom_Search_call_5_conds_def)
    note observed = scanning_register_props[OF scan IH.prems(1,3)]
    have step: "registers (Quadratic_Blossom_Search_upd5 state) (row_advance it) h (Suc t) fresh pool_used \<Longrightarrow>
      <workspace_assn (Quadratic_Blossom_Search_upd5 state) (row_advance it) h (Suc t) fresh pool_used Gi Mi Wi Bi>
        Runtime.search_loop Gi Mi Wi Bi (qbs_current state) (qbs_component state) (row_advance it) h (Suc t) fresh pool_used
        <\<lambda>k. search_result_assn (Quadratic_Blossom_Search state) k Gi Mi Wi Bi>"
      using IH.IH(5)[OF call invar_search_holds_5[OF call IH.prems(1)]] IH.prems(2) observed(1) call
      by (simp add: Quadratic_Blossom_Search_upd5_def extend_search_def enqueue_vertex_def
        Quadratic_Blossom_Search_upd4_def Let_def equations(5))
    show ?thesis
      by (subst Runtime.search_loop.simps, simp only: if_not_P[OF observed(1)] observed(2) not_True_eq_False if_False)
        (sep_auto heap: row_read_rule
          representative_rule[where state=state and v="scanned_neighbour state", folded observed(4)]
          classify_rule[where state=state, simplified labels]
          mate_read_rule
          extend_rule[where state=state, unfolded extension_partner_input[OF call IH.prems(1)]] step
          simp: labels call IH.prems scan observed(3))
  next
    assume call: "Quadratic_Blossom_Search_call_6_conds state"
    have scan: "scanning_edge state" and labels:
      "source_component state \<noteq> target_component state"
      "\<not> fset_isin (forest_odds (qbs_forest state)) (target_component state)"
      "fset_isin (forest_evens (qbs_forest state)) (target_component state)"
      "last (forest_path (qbs_forest state) (source_component state)) \<noteq>
        last (forest_path (qbs_forest state) (target_component state))"
      using call
      by (auto simp: Quadratic_Blossom_Search_call_6_conds_def)
    note observed = scanning_register_props[OF scan IH.prems(1,3)]
    show ?thesis
      by (subst Runtime.search_loop.simps, simp only: if_not_P[OF observed(1)] observed(2) not_True_eq_False if_False
        search_terminal_step(2)[OF IH.hyps(1) call])
        (sep_auto heap: row_read_rule
          representative_rule[where state=state and v="scanned_neighbour state", folded observed(4)]
          classify_rule[where state=state, simplified labels]
          paths_rule[where state=state, simplified labels]
          recover_rule simp: labels call IH.prems scan observed(3) search_result_assn_def)
  next
    assume call: "Quadratic_Blossom_Search_call_7_conds state"
    have scan: "scanning_edge state" and labels:
      "source_component state \<noteq> target_component state"
      "\<not> fset_isin (forest_odds (qbs_forest state)) (target_component state)"
      "fset_isin (forest_evens (qbs_forest state)) (target_component state)"
      "last (forest_path (qbs_forest state) (source_component state)) =
        last (forest_path (qbs_forest state) (target_component state))"
      using call
      by (auto simp: Quadratic_Blossom_Search_call_7_conds_def)
    note observed = scanning_register_props[OF scan IH.prems(1,3)]
    have next_current: "qbs_current (Quadratic_Blossom_Search_upd7 state) = qbs_current state"
      by (simp add: Quadratic_Blossom_Search_upd7_def contract_search_def Let_def case_prod_beta
        process_cycle_frame Quadratic_Blossom_Search_upd4_def)
    have step: "\<lbrakk>registers (Quadratic_Blossom_Search_upd7 state) (row_advance it) h t' (Suc fresh) used;
      qbs_component (Quadratic_Blossom_Search_upd7 state) = fresh_vertex fresh\<rbrakk> \<Longrightarrow>
      <workspace_assn (Quadratic_Blossom_Search_upd7 state) (row_advance it) h t' (Suc fresh) used Gi Mi Wi Bi>
        Runtime.search_loop Gi Mi Wi Bi (qbs_current state) (fresh_vertex fresh) (row_advance it) h t' (Suc fresh) used
        <\<lambda>k. search_result_assn (Quadratic_Blossom_Search state) k Gi Mi Wi Bi>" for t' used
      using IH.IH(7)[OF call invar_search_holds_7[OF call IH.prems(1)]] IH.prems(2) observed(1) call
      by (simp add: next_current equations(7))
    show ?thesis
      by (subst Runtime.search_loop.simps, simp only: if_not_P[OF observed(1)] observed(2) not_True_eq_False if_False)
        (sep_auto heap: row_read_rule
          representative_rule[where state=state and v="scanned_neighbour state", folded observed(4)]
          classify_rule[where state=state, simplified labels]
          paths_rule[where state=state, simplified labels]
          contract_rule step simp: labels call IH.prems scan observed(3))
  next
    assume "Quadratic_Blossom_Search_ret_1_conds state"
    with IH.prems(2) show ?thesis
      by (simp add: Quadratic_Blossom_Search_ret_1_conds_def)
  next
    assume "Quadratic_Blossom_Search_ret_2_conds state"
    with IH.prems(2) show ?thesis
      by (auto simp: Quadratic_Blossom_Search_ret_2_conds_def)
  qed
qed


lemma search_into_refine:
  "<input_assn Gi Mi Wi Bi> Runtime.search_into Gi Mi Wi Bi
    <\<lambda>k. search_result_assn (Quadratic_Blossom_Search initial_search_state) k Gi Mi Wi Bi>"
  unfolding Runtime.search_into_def
  by (sep_auto heap: initialise_rule
    search_loop_refine[OF initial_search_properties(1) initial_state_props initial_state_observations(5),
      simplified initial_state_observations(4), simplified])

lemma search_into_correct:
  "<input_assn Gi Mi Wi Bi> Runtime.search_into Gi Mi Wi Bi
    <\<lambda>k. \<exists>\<^sub>Axs. output_assn xs Gi Mi Wi Bi * \<up>(length xs = output_cap \<and> k \<le> output_cap \<and>
      (if k = 0 then \<not> (\<exists>p. graph_augmenting_path input_graph (mate_abstract M0) p)
       else graph_augmenting_path input_graph (mate_abstract M0) (take k xs)))>"
proof-
  let ?result = "result_path (Quadratic_Blossom_Search initial_search_state) T0 out0"
  have length: "\<lbrakk>k \<le> length xs; take k xs = Recovery.recovered_path ?result\<rbrakk>
    \<Longrightarrow> k = qbr_length ?result" for k xs
    by (drule arg_cong[where f = length]) auto
  show ?thesis
    using Quadratic_Blossom_Search_run_correct
    by (sep_auto heap: search_into_refine[unfolded search_result_assn_def] dest: length
      simp: augmenting_path_result_spec_def Quadratic_Blossom_Search_run_def
        Quadratic_Blossom_Search_impl_same[OF initial_search_properties(1)] split: if_splits)
qed

end

context Quadratic_Blossom_Search_Cycle_Imperative
begin

abbreviation "augmenting_view P plen Q qlen \<equiv>
  Paths.buffer_view P 0 plen True @ Paths.buffer_view Q 0 qlen False"

abbreviation "augmenting_read P_i plen Q_i qlen \<equiv>
  Paths.joined_read P_i 0 plen True Q_i 0 qlen False"

lemma augmenting_read_rule:
  "\<lbrakk>path_invar P; path_invar Q; plen \<le> path_cap; qlen \<le> path_cap; i < plen + qlen\<rbrakk> \<Longrightarrow>
   <path_assn P P_i * path_assn Q Q_i> augmenting_read P_i plen Q_i qlen i
   <\<lambda>c. path_assn P P_i * path_assn Q Q_i * \<up>(c = augmenting_view P plen Q qlen ! i)>"
  by(intro Paths.joined_read_rule) auto

lemma cycle_view_butlast:
  "0 < qlen \<Longrightarrow> cycle_view P plen Q qlen = butlast (augmenting_view P plen Q qlen)"
  by(cases qlen) (simp_all add: cycle_view_def Paths.buffer_view_def Let_def upt_Suc_append butlast_append)

lemma augmenting_cycle_nth:
  "\<lbrakk>0 < qlen; i < plen + qlen - 1\<rbrakk> \<Longrightarrow>
   cycle_view P plen Q qlen ! i = augmenting_view P plen Q qlen ! i"
  by(simp add: cycle_view_butlast nth_butlast)

lemma augmenting_edges_index:
  "\<lbrakk>p \<noteq> []; q \<noteq> []; i < length p + length q - 1\<rbrakk> \<Longrightarrow>
   (outward_edges state p @ [edge] @ rootward_edges state q) ! i =
     cycle_witness state (p @ butlast q) (length p) edge i ((p @ q) ! i)"
  by(auto simp: outward_edges_def rootward_edges_def nth_append nth_tl nth_butlast nth_Cons'
    split: if_splits)

lemma augmenting_view_prefixes:
  "augmenting_view P plen Q qlen =
   rev (Paths.buffer_view P 0 plen False) @ Paths.buffer_view Q 0 qlen False"
  by(simp add: Paths.buffer_view_def Let_def)

lemma cycle_view_split:
  "0 < qlen \<Longrightarrow> cycle_view P plen Q qlen =
   Paths.buffer_view P 0 plen True @ butlast (Paths.buffer_view Q 0 qlen False)"
  by(cases qlen) (simp_all add: cycle_view_def Paths.buffer_view_def Let_def upt_Suc_append butlast_append)

lemma augmenting_crossings_length:
  "\<lbrakk>0 < plen; 0 < qlen\<rbrakk> \<Longrightarrow>
   length (outward_edges state (Paths.buffer_view P 0 plen True) @ [(u,v)] @
     rootward_edges state (Paths.buffer_view Q 0 qlen False)) = plen + qlen - 1"
  by(simp add: outward_edges_def rootward_edges_def; arith)

lemma augmenting_crossing_rule:
  assumes "path_invar P" "path_invar Q" "plen \<le> path_cap" "qlen \<le> path_cap"
    "edge_invar (qbs_forest_edges state)" "set (augmenting_view P plen Q qlen) \<subseteq> K"
    "0 < plen" "0 < qlen" "i < plen + qlen - 1"
  shows "<edge_assn (qbs_forest_edges state) E_i * path_assn P P_i * path_assn Q Q_i>
    cycle_edge_into E_i P_i plen Q_i qlen u v i (augmenting_view P plen Q qlen ! i)
    <\<lambda>edge. edge_assn (qbs_forest_edges state) E_i * path_assn P P_i * path_assn Q Q_i *
      \<up>(edge = (outward_edges state (Paths.buffer_view P 0 plen True) @ [(u,v)] @
        rootward_edges state (Paths.buffer_view Q 0 qlen False)) ! i)>"
proof-
  have keys: "set (cycle_view P plen Q qlen) \<subseteq> K"
    using assms(6,8) bulast_subset[of "augmenting_view P plen Q qlen"]
    by(auto simp: cycle_view_butlast)
  have bound: "i < plen + (qlen - 1)"
    using assms(8,9)
    by arith
  have nonempty: "Paths.buffer_view P 0 plen True \<noteq> []"
      "Paths.buffer_view Q 0 qlen False \<noteq> []"
    using assms(7,8)
    by(simp_all only: length_greater_0_conv[symmetric] Paths.view_length)
  have witness: "(outward_edges state (Paths.buffer_view P 0 plen True) @ [(u,v)] @
      rootward_edges state (Paths.buffer_view Q 0 qlen False)) ! i =
    cycle_witness state (cycle_view P plen Q qlen) plen (u,v) i (augmenting_view P plen Q qlen ! i)"
    using augmenting_edges_index[OF nonempty, of i state "(u,v)"] assms(8,9)
    by(simp add: cycle_view_split)
  show ?thesis
    by(rule cycle_edge_into_rule[OF assms(1-5) keys bound, where u=u and v=v,
      unfolded augmenting_cycle_nth[OF assms(8,9)], folded witness])
qed

end

section "Repeated searches with one workspace and output buffer"

locale Find_Max_Matching_Buffer =
  fixes search_into :: "'gi \<Rightarrow> 'mi \<Rightarrow> 'wi \<Rightarrow> 'bi \<Rightarrow> nat Heap"
    and augment_prefix :: "'mi \<Rightarrow> 'bi \<Rightarrow> nat \<Rightarrow> unit Heap"
begin

partial_function (heap) matching_loop ::
  "'gi \<Rightarrow> 'mi \<Rightarrow> 'wi \<Rightarrow> 'bi \<Rightarrow> unit Heap" where
  "matching_loop Gi Mi Wi Bi = do {
    k \<leftarrow> search_into Gi Mi Wi Bi;
    if k = 0 then return ()
    else do { augment_prefix Mi Bi k; matching_loop Gi Mi Wi Bi } }"

end

text "The loop works on the abstract graph E and the matching interface blossom_matching.
  The search only has to return some augmenting path, not the result of one fixed functional
  search: its choice may depend on stale workspace contents. The proof uses the measure of the
  functional loop in Find_Max_Matching."

locale Find_Max_Matching_Buffer_Refinement =
  blossom_matching + Find_Max_Matching_Buffer search_into augment_prefix
  for search_into :: "'gi \<Rightarrow> 'mi \<Rightarrow> 'wi \<Rightarrow> 'bi \<Rightarrow> nat Heap"
    and augment_prefix :: "'mi \<Rightarrow> 'bi \<Rightarrow> nat \<Rightarrow> unit Heap" +
  fixes E and graph_assn :: "'gi \<Rightarrow> assn" and matching_assn and workspace_assn :: "'wi \<Rightarrow> assn"
    and buffer_assn and capacity :: nat
  assumes graph: "graph_invar E" "Vs E \<subseteq> K"
    and search_into_rule:
    "\<lbrakk>matching_invar E M; length xs = capacity\<rbrakk> \<Longrightarrow>
      <graph_assn Gi * matching_assn M Mi * workspace_assn Wi * buffer_assn xs Bi>
        search_into Gi Mi Wi Bi
      <\<lambda>k. \<exists>\<^sub>Ays. graph_assn Gi * matching_assn M Mi * workspace_assn Wi *
        buffer_assn ys Bi * \<up>(length ys = capacity \<and> k \<le> capacity \<and>
          (if k = 0 then \<nexists>p. graph_augmenting_path E (matching_abstract M) p
           else graph_augmenting_path E (matching_abstract M) (take k ys)))>"
    and augment_prefix_rule:
    "\<lbrakk>matching_invar E M; graph_augmenting_path E (matching_abstract M) (take k xs);
      k \<le> length xs\<rbrakk> \<Longrightarrow>
      <matching_assn M Mi * buffer_assn xs Bi> augment_prefix Mi Bi k
      <\<lambda>_. matching_assn (augment M (take k xs)) Mi * buffer_assn xs Bi>"
begin

definition "matching_workspace M Gi Mi Wi Bi =
  (\<exists>\<^sub>Axs. graph_assn Gi * matching_assn M Mi * workspace_assn Wi *
    buffer_assn xs Bi * \<up>(length xs = capacity))"

definition "matching_measure M = card E - card (matching_abstract M)"

lemma augment_step:
  assumes  "matching_invar E M" and  "graph_augmenting_path E (matching_abstract M) p"
  shows "matching_invar E (augment M p)" "matching_measure (augment M p) < matching_measure M"
proof-
  show "matching_invar E (augment M p)"
    using assms
    by(rule augment(1))
  have fin: "finite E"
    using graph(1)
    by(simp add: finite_Vs_then_finite)
  have "card (matching_abstract M) < card (matching_abstract (augment M p))"
    using assms matching(1)[of E M] finite_subset[of "matching_abstract M" E] fin
    by(simp add: augment(2) new_matching_bigger)
  moreover have "card (matching_abstract (augment M p)) \<le> card E"
    using assms fin augment(1)[of E M p] matching(1)[of E "augment M p"]
    by(auto intro: card_mono)
  ultimately show "matching_measure (augment M p) < matching_measure M"
    by(simp add: matching_measure_def)
qed

lemma maximum_if_exhausted:
  assumes  "matching_invar E M" and  "\<nexists>p. graph_augmenting_path E (matching_abstract M) p"
  shows "max_card_matching E (matching_abstract M)"
  using assms matching(1)[of E M] graph(1) finite_Vs_then_finite[of E]
    finite_subset[of "matching_abstract M" E] Berge[of "matching_abstract M" E]
  by(auto simp: max_card_matching_def not_le)

theorem matching_loop_correct:
  "matching_invar E M \<Longrightarrow>
    <matching_workspace M Gi Mi Wi Bi> matching_loop Gi Mi Wi Bi
    <\<lambda>_. \<exists>\<^sub>AN. matching_workspace N Gi Mi Wi Bi *
      \<up>(matching_invar E N \<and> max_card_matching E (matching_abstract N))>"
proof(induction "matching_measure M" arbitrary: M rule: less_induct)
  case (less M)
  have step: "<graph_assn Gi * matching_assn M Mi * workspace_assn Wi * buffer_assn ys Bi>
      do { augment_prefix Mi Bi k; matching_loop Gi Mi Wi Bi }
      <\<lambda>_. \<exists>\<^sub>AN. matching_workspace N Gi Mi Wi Bi *
        \<up>(matching_invar E N \<and> max_card_matching E (matching_abstract N))>"
    if aug: "graph_augmenting_path E (matching_abstract M) (take k ys)" "length ys = capacity" "k \<le> capacity"
    for k ys
  proof-
    note succ = augment_step[OF less.prems aug(1)]
    have rec: "<matching_assn (augment M (take k ys)) Mi * buffer_assn ys Bi * (graph_assn Gi * workspace_assn Wi)>
        matching_loop Gi Mi Wi Bi
        <\<lambda>_. \<exists>\<^sub>AN. matching_workspace N Gi Mi Wi Bi *
          \<up>(matching_invar E N \<and> max_card_matching E (matching_abstract N))>"
      by (rule ht_cons_pre[OF _ less.hyps[OF succ(2,1)]], unfold matching_workspace_def,
        rule ent_ex_postI[where x = ys]) (sep_auto simp: aug(2))
    show ?thesis
      using aug(2,3)
      by (sep_auto heap: augment_prefix_rule[OF less.prems aug(1)] rec)
  qed
  have cont: "<graph_assn Gi * matching_assn M Mi * workspace_assn Wi * buffer_assn ys Bi *
      \<up>(length ys = capacity \<and> k \<le> capacity \<and>
        (if k = 0 then \<nexists>p. graph_augmenting_path E (matching_abstract M) p
         else graph_augmenting_path E (matching_abstract M) (take k ys)))>
      (if k = 0 then return () else do { augment_prefix Mi Bi k; matching_loop Gi Mi Wi Bi })
      <\<lambda>_. \<exists>\<^sub>AN. matching_workspace N Gi Mi Wi Bi *
        \<up>(matching_invar E N \<and> max_card_matching E (matching_abstract N))>" for k ys
  proof(cases "k = 0")
    case True
    show ?thesis
      using True maximum_if_exhausted[OF less.prems] less.prems
      by (intro ht_extract_pre_pure(1)) (sep_auto simp: matching_workspace_def)
  next
    case False
    show ?thesis
      using step[of k ys] False
      by (intro ht_extract_pre_pure(1)) simp
  qed
  show ?case
    unfolding matching_workspace_def[of M]
    by (intro ht_exEI ht_extract_pre_pure(1), subst matching_loop.simps,
      rule ht_bind[OF search_into_rule[OF less.prems]], assumption, intro ht_exEI, rule cont)
qed

theorem matching_run_correct:
  "<matching_workspace empty_matching Gi Mi Wi Bi> matching_loop Gi Mi Wi Bi
    <\<lambda>_. \<exists>\<^sub>AN. matching_workspace N Gi Mi Wi Bi *
      \<up>(matching_invar E N \<and> max_card_matching E (matching_abstract N))>"
  by (rule matching_loop_correct[OF matching(2)[OF graph(2)]])

lemma matching_search_rule:
  "matching_invar E M \<Longrightarrow>
    <matching_workspace M Gi Mi Wi Bi> search_into Gi Mi Wi Bi
    <\<lambda>k. \<exists>\<^sub>Ays. graph_assn Gi * matching_assn M Mi * workspace_assn Wi * buffer_assn ys Bi *
      \<up>(length ys = capacity \<and> k \<le> capacity \<and>
        (if k = 0 then \<nexists>p. graph_augmenting_path E (matching_abstract M) p
         else graph_augmenting_path E (matching_abstract M) (take k ys)))>"
  unfolding matching_workspace_def
  by (intro ht_exEI ht_extract_pre_pure(1)) (rule search_into_rule)

end

end

