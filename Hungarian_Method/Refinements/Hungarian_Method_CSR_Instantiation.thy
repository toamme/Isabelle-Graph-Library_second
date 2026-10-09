theory Hungarian_Method_CSR_Instantiation
  imports Directed_Set_Graphs.CSR_Graph Data_Structures.Indexed_Heap
          Data_Structures.Array_Map_Set_Addons
          Basic_Matching.Alternating_Forest_Imperative
          Basic_Matching.Matching_Augmentation_Imperative
          Primal_Dual_Path_Search_Imperative Init_Potential_Imperative
          Hungarian_Method_Top_Loop_Imperative
          Data_Structures.Indexed_Heap_Imperative  Path_Search_Shortcut_Imperative
begin

section \<open>An Imperative Instantiation of the Hungarian Method\<close>

text \<open>The imperative modules of the Hungarian method are instantiated with data structures of
      fixed size, allocated once at the beginning:

        \<^item> the maps (best even neighbours, missed values, potential, parents, buddies) are array maps
          @{const is_iam} of size \<open>n\<close>, the sets (left vertices, even and odd vertices) are array
          sets @{const is_ias} of size \<open>n\<close>; they are cleared in place and iterated in increasing
          order,
        \<^item> the queue is the indexed binary heap of size \<open>n\<close>, and
        \<^item> the neighbourhoods are given in compressed sparse row (CSR) form, together with the
          weights in CSR order.

      The functional ADT types become the functional models that these data structures represent:
      maps @{typ \<open>nat \<rightharpoonup> 'a\<close>} and finite sets of naturals, iterated in the order
      @{const sorted_list_of_set}. The functional models are not executed.\<close>

subsection \<open>Functional Models of the Iterations over Sets\<close>

definition "fset_iterate f init V = foldl f init (sorted_list_of_set V)"
definition "fset_filter P (V :: 'a set) = V \<inter> Collect P"
definition "fset_is_empty (V :: 'a set) = (V = {})"

lemma fset_iterate_foldl:
  "finite V \<Longrightarrow> \<exists>vs. fset_set V = set vs \<and> distinct vs \<and> fset_iterate f init V = foldl f init vs"
  by (auto simp: fset_iterate_def fset_set_def intro!: exI[of _ "sorted_list_of_set V"])

lemma fset_iterate_foldl':
  "finite V \<Longrightarrow> \<exists>vs. set vs = fset_set V \<and> distinct vs \<and> fset_iterate f init V = foldl f init vs"
  by (auto simp: fset_iterate_def fset_set_def intro!: exI[of _ "sorted_list_of_set V"])

lemma fset_iterate_foldl_set:
  "finite V \<Longrightarrow> \<exists>vs. set vs = V \<and> distinct vs \<and> fset_iterate f init V = foldl f init vs"
  using fset_iterate_foldl'[of V f init] by (simp add: fset_set_def)

lemma iam_empty_sz: "imp_map_empty is_iam (iam_new_sz n)"
  by unfold_locales

section \<open>The Code\<close>

text \<open>The global interpretations of the implementation modules (the forest and the augmentation),
      whose assumptions do not depend on the graph, and of the code locales of the algorithms.\<close>

subsection \<open>The Forest\<close>

global_interpretation forest_csr: forest_imp
  where parent_empty = Map.empty and parent_upd = fmap_update and parent_delete = fmap_delete
    and parent_lookup = fmap_lookup and parent_invar = fmap_invar
    and origin_empty = Map.empty and origin_upd = fmap_update and origin_delete = fmap_delete
    and origin_lookup = fmap_lookup and origin_invar = fmap_invar
    and vset_empty = "{}" and vset_insert = fset_insert and vset_delete = fset_delete
    and vset_isin = fset_isin and vset_to_set = fset_set and vset_invar = finite
    and vset_iterate = fset_iterate
    and is_set = is_ias and memb_imp = ias_memb and ins_imp = ias_ins and set_clear_imp = ias_clear
    and set_empty_imp = "ias_new_sz n" and lst = sorted_list_of_set and is_it = ias_is_it
    and it_init = ias_it_init and it_has_next = ias_it_has_next and it_next = ias_it_next
    and is_map = is_iam and lookup_imp = iam_lookup and update_imp = iam_update
    and map_clear_imp = iam_clear and map_empty_imp = "iam_new_sz n"
  for n
  defines forest_csr_empty = forest_csr.forest_empty_imp
    and forest_csr_clear = forest_csr.forest_clear_imp
    and forest_csr_add_root = forest_csr.forest_add_root_imp
    and forest_csr_extend = forest_csr.forest_extend_imp
    and forest_csr_it_init = forest_csr.forest_it_init
    and forest_csr_get_path_loop = forest_csr.get_path_loop
    and forest_csr_get_path = forest_csr.get_path_imp
  by (intro forest_imp.intro forest_manipulation.intro forest_manipulation_spec.intro
            forest_manipulation_axioms.intro fmap_Map fset_Set ias_imp_set_conn ias_empty_sz_impl
            iam_imp_map_conn_clear iam_empty_sz fset_iterate_foldl fmap_conn_facts)

subsection \<open>The Augmentation\<close>

global_interpretation aug_csr: matching_augmentation_imp
  where buddy_empty = Map.empty and buddy_upd = fmap_update and buddy_delete = fmap_delete
    and buddy_lookup = fmap_lookup and buddy_invar = fmap_invar
    and is_map = is_iam and lookup_imp = iam_lookup and update_imp = iam_update
  defines augment_csr_loop = aug_csr.augment_loop
    and augment_csr = aug_csr.augment_imp
    and augment_counted_csr = aug_csr.augment_counted_imp
    and matching_card_csr = aug_csr.matching_card_imp
  by (intro matching_augmentation_imp.intro matching_augmentation_spec.intro fmap_Map
            iam_imp_map_conn fmap_conn_facts)

subsection \<open>The Path Search\<close>

global_interpretation pds_csr: primal_dual_path_search_imp_code
  where ben_lookup_imp = iam_lookup and ben_update_imp = iam_update and ben_clear_imp = iam_clear
    and missed_lookup_imp = iam_lookup and missed_update_imp = iam_update
    and missed_clear_imp = iam_clear
    and pot_lookup_imp = iam_lookup and pot_update_imp = iam_update
    and buddy_imp = "\<lambda>Bdi v. iam_lookup v Bdi"
    and left_it_init = ias_it_init and left_it_has_next = ias_it_has_next
    and left_it_next = ias_it_next
    and forest_clear_imp = forest_csr_clear and forest_add_root_imp = forest_csr_add_root
    and forest_extend_imp = forest_csr_extend and forest_it_init = forest_csr_it_init
    and forest_it_has_next = ias_it_has_next and forest_it_next = ias_it_next
    and get_path_imp = forest_csr_get_path
    and queue_clear_imp = heap_clear_imp and queue_extract_min_imp = heap_extract_min_key_imp
    and queue_key_of_imp = heap_key_of_imp and queue_decrease_key_imp = heap_decrease_key_imp
    and queue_insert_imp = heap_insert_imp
    and has_imp = wnb_has_imp and current_imp = "wnb_current_imp e_tgt"
    and current_cost_imp = wnb_current_cost_imp and move_imp = wnb_move_imp
    and reset_imp = wnb_reset_imp and reset_all_imp = "wnb_reset_all_imp n"
  for n
  defines pds_csr_pot_val = pds_csr.pot_val
    and pds_csr_missed_val = pds_csr.missed_val
    and pds_csr_relax_new = pds_csr.relax_new_imp
    and pds_csr_relax_old = pds_csr.relax_old_imp
    and pds_csr_relax = pds_csr.relax_imp
    and pds_csr_scan = pds_csr.scan_imp
    and pds_csr_update_ben = pds_csr.update_ben_imp
    and pds_csr_clear = pds_csr.clear_imp
    and pds_csr_init_step = pds_csr.init_step
    and pds_csr_init = pds_csr.init_imp
    and pds_csr_pot_step_even = pds_csr.pot_step_even
    and pds_csr_pot_step_odd = pds_csr.pot_step_odd
    and pds_csr_new_pot = pds_csr.new_pot_imp
    and pds_csr_loop = pds_csr.loop_imp
    and pds_csr_search = pds_csr.search_imp
  done

text \<open>The data structures of the path search form a single handle: the collection of
      neighbourhoods, the queue, the left vertices, the forest, the best even neighbours and the
      missed values.\<close>

definition path_search_csr where
  "path_search_csr n = (\<lambda>(Ci, Qi, Li, Fi, Bi, Mi) Bdi Pti Ra. do {
     (res, Pti', Fi', Bi', Mi') \<leftarrow> pds_csr_search n Ci Qi Pti Bdi Li Ra Fi Bi Mi;
     return (res, Pti', (Ci, Qi, Li, Fi', Bi', Mi')) })"

subsection \<open>The Shortcut\<close>

global_interpretation sc_csr: path_search_shortcut_imp_code
  where pot_lookup_imp = iam_lookup and pot_update_imp = iam_update
    and buddy_imp = "\<lambda>Bdi v. iam_lookup v Bdi"
    and left_it_init = ias_it_init and left_it_has_next = ias_it_has_next
    and left_it_next = ias_it_next
    and has_imp = wnb_has_imp and current_imp = "wnb_current_imp e_tgt"
    and current_cost_imp = wnb_current_cost_imp and move_imp = wnb_move_imp
    and reset_imp = wnb_reset_imp and reset_all_imp = "wnb_reset_all_imp n"
  for n
  defines sc_csr_scan_best = sc_csr.bs.scan_best_imp
    and sc_csr_best_of = sc_csr.bs.best_of_imp
    and sc_csr_cur_red = sc_csr.cur_red_imp
    and sc_csr_row_try = sc_csr.row_try_imp
    and sc_csr_first_success = sc_csr.first_success_imp
    and sc_csr_shortcut = sc_csr.shortcut_imp
  done

text \<open>The path search of the instantiation: while the matching has fewer than @{term theta}
      edges, the shortcut is tried first. Otherwise, or if it fails, the full path search is run.
      The matching carries its cardinality, hence the test takes constant time.\<close>

definition path_search_sc_csr where
  "path_search_sc_csr n theta = (\<lambda>Si Mt Pti Ra.
   case (Si, Mt) of ((Ci, Qi, Li, Fi, Bi, Mi), (Bdi, _)) \<Rightarrow> do {
     k \<leftarrow> matching_card_csr Mt;
     (if k < theta then do {
        (b, Pti') \<leftarrow> sc_csr_shortcut n Ci Li Bdi Pti Ra;
        (if b then return (Imp_Path 2, Pti', Si) else path_search_csr n Si Bdi Pti' Ra) }
      else path_search_csr n Si Bdi Pti Ra) })"

subsection \<open>The Initial Potential\<close>

global_interpretation ip_csr: init_potential_imp_code
  where has_imp = wnb_has_imp and current_cost_imp = wnb_current_cost_imp
    and move_imp = wnb_move_imp and reset_imp = wnb_reset_imp
    and pot_lookup_imp = iam_lookup and pot_update_imp = iam_update
    and left_it_init = ias_it_init and left_it_has_next = ias_it_has_next
    and left_it_next = ias_it_next
  defines init_pot_csr_upd_min = ip_csr.upd_min_imp
    and init_pot_csr_scan = ip_csr.scan_min_imp
    and init_pot_csr_step = ip_csr.init_pot_step
    and init_pot_csr = ip_csr.init_pot_imp
  done

subsection \<open>The Top Loop\<close>

global_interpretation hl_csr: hungarian_top_loop_imp_code "path_search_sc_csr n theta" augment_counted_csr
  for n theta
  defines hungarian_csr_main_loop = hl_csr.main_loop_imp
    and hungarian_csr = hl_csr.hungarian_imp
  done

subsection \<open>Initialisation\<close>

text \<open>The weights are given per input edge. They are permuted into CSR order once, so that the
      weights of a neighbourhood are read sequentially during the search.\<close>

partial_function (heap) perm_weights_imp ::
  "edge array \<Rightarrow> 'n::heap array \<Rightarrow> 'n array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "perm_weights_imp Ea Wa Wc i m =
     (if i < m then do {
        e \<leftarrow> Array.nth Ea i;
        w \<leftarrow> Array.nth Wa (e_id e);
        _ \<leftarrow> Array.upd i w Wc;
        perm_weights_imp Ea Wa Wc (Suc i) m }
      else return ())"

text \<open>Inserting the elements of an array into an array set.\<close>

partial_function (heap) ias_insert_all :: "nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> array_set \<Rightarrow> array_set Heap" where
  "ias_insert_all La i m s =
     (if i < m then do {
        v \<leftarrow> Array.nth La i;
        s' \<leftarrow> ias_ins v s;
        ias_insert_all La (Suc i) m s' }
      else return s)"

text \<open>The final program takes the number of vertices \<open>n\<close>, the threshold \<open>theta\<close> for the
      shortcut, the arrays \<open>Fa\<close>, \<open>Ta\<close> of the left and the right endpoints of the edges, the weight
      array \<open>Wa\<close>, and the arrays \<open>La\<close>, \<open>Ra\<close> of the left and the right vertices. It builds the CSR
      representation, allocates all other data structures, computes the initial potential and runs
      the Hungarian method. It returns the result flag, the matching and the final potential. This
      is the only place with allocations. With \<open>theta = 0\<close>, the shortcut is never tried.\<close>

definition hungarian_csr_run ::
  "nat \<Rightarrow> nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> 'n::{linordered_idom, heap} array \<Rightarrow> nat array \<Rightarrow>
   nat array \<Rightarrow> (result \<times> nat array_map \<times> 'n array_map) Heap" where
  "hungarian_csr_run n theta Fa Ta Wa La Rv = do {
     (Ba, Ea) \<leftarrow> csr_build_edges n (Fa, Ta) 0;
     m \<leftarrow> Array.len Ea;
     Wc \<leftarrow> Array.new m 0;
     perm_weights_imp Ea Wa Wc 0 m;
     Ca \<leftarrow> csr_cursor_init n Ba;
     cL \<leftarrow> Array.len La;
     cR \<leftarrow> Array.len Rv;
     Li0 \<leftarrow> ias_new_sz n;
     Li \<leftarrow> ias_insert_all La 0 cL Li0;
     Pti0 \<leftarrow> iam_new_sz n;
     Pti \<leftarrow> init_pot_csr ((Ba, Ea, Ca), Wc) Li Pti0;
     Qi \<leftarrow> heap_empty_imp n 0;
     Fi \<leftarrow> forest_csr_empty n;
     Bi \<leftarrow> iam_new_sz n;
     Mi \<leftarrow> iam_new_sz n;
     Mm \<leftarrow> iam_new_sz n;
     Ki \<leftarrow> ref 0;
     Ra \<leftarrow> Array.new n 0;
     (r, (Mm', _), Pti', _) \<leftarrow>
       hungarian_csr n theta cL cR (((Ba, Ea, Ca), Wc), Qi, Li, Fi, Bi, Mi) (Mm, Ki) Pti Ra;
     return (r, Mm', Pti') }"

definition hungarian_csr_run_int ::
  "nat \<Rightarrow> nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> int array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow>
   (result \<times> nat array_map \<times> int array_map) Heap" where
  "hungarian_csr_run_int = hungarian_csr_run"

declare perm_weights_imp.simps[code] ias_insert_all.simps[code] iter_fold.simps[code]
  forest_csr.get_path_loop.simps[code] aug_csr.augment_loop.simps[code]
  pds_csr.scan_imp.simps[code] pds_csr.loop_imp.simps[code] ip_csr.scan_min_imp.simps[code]
  hl_csr.main_loop_imp.simps[code] csr_copy_imp.simps[code] array_fill.simps[code]
  ias_scan.simps[code] sc_csr.bs.scan_best_imp.simps[code] iter_find.simps[code]
  nb_best_scan_imp_code.best_upd_imp_def[code] nb_best_scan_imp_code.better_imp_def[code]
  sift_down_imp.simps[code] sift_up_imp.simps[code]

export_code hungarian_csr_run_int checking SML_imp

text \<open>In the generated code, the computation of the initial potential and the main loop contain no
      allocation except for @{const array_grow} in @{const iam_update} and @{const ias_ins}, which
      is only executed for keys beyond the size of the array. All keys are vertices below \<open>n\<close>, so
      it never is. All other allocations are in @{const hungarian_csr_run} before the computation
      begins.\<close>

section \<open>Correctness\<close>

subsection \<open>The Input\<close>

text \<open>The input consists of the lists @{term fs}, @{term ts} of the left and the right endpoints of
      the edges, the weights @{term ws}, and the lists @{term ls}, @{term rs} of the left and the
      right vertices. Every vertex has an edge, the sides are disjoint, all vertices are below
      @{term n}, and there are no parallel edges. The threshold @{term theta} for the shortcut is
      arbitrary.\<close>

locale hungarian_csr_input = real_embedding h
  for h :: "'n::{linordered_idom, heap} \<Rightarrow> real" +
  fixes n :: nat
    and fs :: "nat list"
    and ts :: "nat list"
    and ws :: "'n list"
    and ls :: "nat list"
    and rs :: "nat list"
    and theta :: nat
  assumes ts_length: "length ts = length fs"
    and ws_length: "length ws = length fs"
    and ls_distinct: "distinct ls"
    and rs_distinct: "distinct rs"
    and fs_ls: "set fs = set ls"
    and ts_rs: "set ts = set rs"
    and sides_disjoint: "set ls \<inter> set rs = {}"
    and verts_below: "set ls \<union> set rs \<subseteq> {..<n}"
    and no_parallel: "distinct (zip fs ts)"
begin

abbreviation "L \<equiv> set ls"
abbreviation "R \<equiv> set rs"

definition "G = {{fs ! i, ts ! i} | i. i < length fs}"

definition "eidx u v = (THE i. i < length fs \<and> fs ! i = u \<and> ts ! i = v)"

definition "ecost u v = (if u \<in> L then h (ws ! eidx u v) else h (ws ! eidx v u))"

lemma fs_L: "i < length fs \<Longrightarrow> fs ! i \<in> L"
  using fs_ls nth_mem by blast

lemma ts_R: "i < length fs \<Longrightarrow> ts ! i \<in> R"
  using ts_rs ts_length nth_mem by metis

lemma L_less: "v \<in> L \<Longrightarrow> v < n" and R_less: "v \<in> R \<Longrightarrow> v < n"
  using verts_below by auto

lemma edge_unique:
  assumes "i < length fs" "j < length fs" "fs ! i = fs ! j" "ts ! i = ts ! j"
  shows "i = j"
proof -
  have z: "zip fs ts ! i = zip fs ts ! j" using assms ts_length by simp
  have "\<forall>i<length (zip fs ts). \<forall>j<length (zip fs ts). i \<noteq> j \<longrightarrow> zip fs ts ! i \<noteq> zip fs ts ! j"
    using no_parallel by (simp only: distinct_conv_nth)
  thus ?thesis using z assms(1,2) ts_length by auto
qed

lemma eidx_eq: "i < length fs \<Longrightarrow> eidx (fs ! i) (ts ! i) = i"
  unfolding eidx_def by (rule the_equality) (auto intro: edge_unique)

lemma ecost_edge: "i < length fs \<Longrightarrow> ecost (fs ! i) (ts ! i) = h (ws ! i)"
  by (simp add: ecost_def fs_L eidx_eq)

lemma ecost_edge_sym: "i < length fs \<Longrightarrow> ecost (ts ! i) (fs ! i) = h (ws ! i)"
  using ts_R fs_L sides_disjoint by (auto simp: ecost_def eidx_eq)

lemma G_edgeE:
  assumes "{u, v} \<in> G"
  obtains i where "i < length fs" "u = fs ! i" "v = ts ! i"
        | i where "i < length fs" "v = fs ! i" "u = ts ! i"
  using assms unfolding G_def by (auto simp: doubleton_eq_iff)

lemma ecost_sym: "{u, v} \<in> G \<Longrightarrow> ecost u v = ecost v u"
  by (erule G_edgeE) (simp_all add: ecost_edge ecost_edge_sym)

lemma bipartite_G: "bipartite G L R"
  unfolding bipartite_def G_def
  using fs_L ts_R sides_disjoint by (fastforce simp: doubleton_eq_iff)

lemma Vs_G: "Vs G = L \<union> R"
proof
  show "Vs G \<subseteq> L \<union> R" using fs_L ts_R by (auto simp: Vs_def G_def)
  show "L \<union> R \<subseteq> Vs G"
  proof
    fix v assume "v \<in> L \<union> R"
    hence "v \<in> set fs \<or> v \<in> set ts" using fs_ls ts_rs by auto
    thus "v \<in> Vs G"
    proof (elim disjE)
      assume "v \<in> set fs"
      then obtain i where "i < length fs" "v = fs ! i" by (auto simp: in_set_conv_nth)
      thus ?thesis by (auto simp: Vs_def G_def)
    next
      assume "v \<in> set ts"
      then obtain i where "i < length fs" "v = ts ! i"
        using ts_length by (auto simp: in_set_conv_nth)
      thus ?thesis by (auto simp: Vs_def G_def)
    qed
  qed
qed

lemma neighbours_G: "v \<in> L \<Longrightarrow> {u. {v, u} \<in> G} = {ts ! i | i. i < length fs \<and> fs ! i = v}"
  using fs_L ts_R sides_disjoint by (auto simp: G_def doubleton_eq_iff)

subsection \<open>The CSR Representation\<close>

sublocale inp: csr_buildup "edge_next fs ts" "edge_seq fs ts" "\<lambda>_. True" e_src n 0
  by (rule csr_buildup.intro[OF edge_iterator])
     (unfold_locales, auto simp: edge_seq_def fs_L L_less)

sublocale ci: imp_csr_buildup "edge_next fs ts" "edge_seq fs ts" "\<lambda>_. True" e_src n 0
    edge_has_next edge_cur edge_adv edge_key "\<lambda>s si. si = s"
    "\<lambda>(Fa, Ta). Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts"
proof (unfold_locales, goal_cases)
  case (1 s si c)
  have "(edge_next fs ts s \<noteq> None) = (s < length fs)" by (simp add: edge_next_def mk_edge_def)
  with 1 show ?case by (cases c) (sep_auto simp: edge_has_next_def)
next
  case (2 s si e s' c) then show ?case
    using ts_length
    by (cases c) (sep_auto simp: edge_cur_def edge_next_def mk_edge_def split: if_splits)
next
  case (3 s si e s' c) then show ?case
    by (cases c) (sep_auto simp: edge_adv_def edge_next_def split: if_splits)
next
  case (4 e) then show ?case
    by (sep_auto simp: edge_key_def)
qed

lemma E_spec_distinct: "distinct inp.E_spec"
proof -
  have "distinct (concat (map inp.blk [0..<k])) \<and>
        set (concat (map inp.blk [0..<k])) \<subseteq> {e. e_src e < k}" for k
  proof (induction k)
    case 0 show ?case by simp
  next
    case (Suc k) then show ?case
      using edge_seq_distinct[of fs ts 0] by (fastforce simp: inp.blk_def inp.es_def)
  qed
  then show ?thesis by (simp add: inp.E_spec_def)
qed

sublocale graph: csr_graph n L inp.B_spec inp.E_spec
proof (unfold_locales, goal_cases)
  case 1 show ?case using L_less by auto
next
  case 2 show ?case by (rule inp.length_B_spec)
next
  case (3 v) then show ?case by (simp add: inp.B_spec_nth inp.start_mono)
next
  case (4 v) then show ?case
    using inp.start_mono[of "Suc v" n] by (simp add: inp.B_spec_nth inp.start_n inp.length_E_spec)
next
  case 5 show ?case by (rule E_spec_distinct)
qed

lemma csr_abstract_edges:
  assumes "v < n"
  shows "graph.csr_abstract c v = {mk_edge fs ts i | i. i < length fs \<and> fs ! i = v}"
proof -
  have "graph.csr_abstract c v = set (map ((!) inp.E_spec) [inp.B_spec ! v..<inp.B_spec ! Suc v])"
    by (simp add: graph.csr_abstract_def graph.seg_def)
  also have "\<dots> = set (take (inp.B_spec ! Suc v - inp.B_spec ! v) (drop (inp.B_spec ! v) inp.E_spec))"
    using graph.B_bound[OF assms] by (simp add: map_nth_upt_take_drop)
  also have "\<dots> = set (inp.blk v)"
    using inp.csr_block[OF assms] by simp
  also have "\<dots> = {mk_edge fs ts i | i. i < length fs \<and> fs ! i = v}"
    by (auto simp: inp.blk_def inp.es_def edge_seq_def)
  finally show ?thesis .
qed

text \<open>The weights in CSR order.\<close>

definition "W = map (\<lambda>e. ws ! e_id e) inp.E_spec"

lemma seg_edge:
  assumes "v \<in> L" "inp.B_spec ! v \<le> j" "j < inp.B_spec ! Suc v"
  shows "\<exists>i. i < length fs \<and> fs ! i = v \<and> inp.E_spec ! j = mk_edge fs ts i"
proof -
  have "inp.E_spec ! j \<in> graph.csr_abstract c v"
    using assms by (auto simp: graph.csr_abstract_def graph.seg_def)
  thus ?thesis using csr_abstract_edges[OF L_less[OF assms(1)]] by auto
qed

sublocale wcsr: weighted_csr n L inp.B_spec inp.E_spec e_tgt W ecost h
proof (unfold_locales, goal_cases)
  case (1 v)
  have "(!) inp.E_spec ` {inp.B_spec ! v..<inp.B_spec ! Suc v} =
        {mk_edge fs ts i | i. i < length fs \<and> fs ! i = v}"
    using csr_abstract_edges[OF L_less[OF 1]]
    by (simp add: graph.csr_abstract_def graph.seg_def)
  moreover have "inj_on e_tgt {mk_edge fs ts i | i. i < length fs \<and> fs ! i = v}"
  proof (rule inj_onI)
    fix x y assume "x \<in> {mk_edge fs ts i | i. i < length fs \<and> fs ! i = v}"
                   "y \<in> {mk_edge fs ts i | i. i < length fs \<and> fs ! i = v}" "e_tgt x = e_tgt y"
    then obtain i j where "x = mk_edge fs ts i" "y = mk_edge fs ts j" "i < length fs"
                          "j < length fs" "fs ! i = fs ! j" "ts ! i = ts ! j"
      by auto
    moreover have "i = j" by (rule edge_unique) (fact calculation)+
    ultimately show "x = y" by simp
  qed
  ultimately show ?case by simp
next
  case 2 show ?case by (simp add: W_def)
next
  case (3 v j)
  obtain i where i: "i < length fs" "fs ! i = v" "inp.E_spec ! j = mk_edge fs ts i"
    using seg_edge[OF 3] by blast
  have "j < length inp.E_spec"
    using 3 graph.B_bound[OF L_less[OF 3(1)]] by simp
  thus ?case using i by (simp add: W_def ecost_edge flip: i(2))
qed

subsection \<open>The Queue\<close>

lemma h_less_iff: "h a < h b \<longleftrightarrow> a < b"
  using h_strict_mono by (metis not_less_iff_gr_or_eq order_less_asym)

sublocale hp: indexed_heap_imp n "Vs G" h 0
  by unfold_locales (auto simp: Vs_G L_less R_less h_less_iff)

end

subsection \<open>The Maps, the Path Search and the Initial Potential\<close>

context hungarian_csr_input
begin

text \<open>The potential and the missed values are array maps whose values are read into the reals.\<close>

sublocale potm: imp_map_conn is_iam iam_lookup iam_update fmap_update fmap_lookup fmap_invar
    "\<lambda>_ c x. h c = x"
  by (intro iam_imp_map_conn fmap_conn_facts)

abbreviation "nb_init \<equiv> (\<lambda>v. inp.B_spec ! v)"

lemma wnb_abstract_init:
  "v \<in> L \<Longrightarrow> wcsr.wnb_abstract nb_init v = {u. {v, u} \<in> G}"
proof -
  assume v: "v \<in> L"
  have "wcsr.wnb_abstract nb_init v = e_tgt ` {mk_edge fs ts i | i. i < length fs \<and> fs ! i = v}"
    by (simp add: wcsr.wnb_abstract_def csr_abstract_edges[OF L_less[OF v]])
  also have "\<dots> = {ts ! i | i. i < length fs \<and> fs ! i = v}"
    by (simp add: setcompr_eq_image image_image)
  finally show ?thesis using neighbours_G[OF v] by simp
qed

lemma wnb_abstract_finite: "finite (wcsr.wnb_abstract C v)"
  by (simp add: wcsr.wnb_abstract_def graph.csr_abstract_def graph.seg_def)

text \<open>The data structures of the path search, with arbitrary contents; only the collection of
      neighbourhoods has to be one of the graph.\<close>

definition "csr_scratch_assn Si = (case Si of (Ci, Qi, Li, Fi, Bi, Mi) \<Rightarrow>
   (\<exists>\<^sub>AC H (F :: (nat set, nat set, nat set, nat \<rightharpoonup> nat, nat \<rightharpoonup> nat) alt_forest) B Mm.
      wcsr.wnb_assn C Ci * hp.heap_assn H Qi * forest_csr.forest_assn F Fi *
                   aug_csr.buddy_assn B Bi * potm.map_assn Mm Mi *
                   \<up>(graph.csr_invar C \<and>
                     (\<forall>i\<in>L. wcsr.wnb_abstract C i = wcsr.wnb_abstract nb_init i))) *
   is_ias L Li)"

text \<open>The functional path search for the matching @{term M} and the potential @{term \<pi>}.\<close>

definition "fsearch M \<pi> =
  primal_dual_path_search_spec.search_path Map.empty fmap_update fmap_lookup Map.empty fmap_update
    fmap_lookup ecost L wcsr.wnb_current graph.csr_has graph.csr_move graph.csr_reset nb_init M
    forest_csr.extend_forest_even_unclassified evens odds forest_csr.get_path
    forest_csr.empty_forest fmap_update fmap_lookup \<pi> heap_empty heap_extract_min
    heap_decrease_key heap_insert fset_iterate fset_iterate fset_filter fset_is_empty"

text \<open>The initial potential.\<close>

sublocale ipot: init_potential_imp
  where potential_upd = fmap_update and potential_lookup = fmap_lookup
    and rnb_current = wcsr.wnb_current and rnb_has = graph.csr_has and rnb_move = graph.csr_move
    and rnb_reset = graph.csr_reset and cost = ecost and vset_iterate = fset_iterate
    and potential_empty = Map.empty and potential_delete = fmap_delete
    and potential_invar = fmap_invar
    and rnb_invar = graph.csr_invar and rnb_abstract = wcsr.wnb_abstract
    and rnb_iterated = wcsr.wnb_iterated and rnb_remaining = wcsr.wnb_remaining and K = L
    and vset_to_set = fset_set and vset_invar = finite and lst = sorted_list_of_set
    and h = h and nb_init = nb_init and nb_assn = wcsr.wnb_assn and has_imp = wnb_has_imp
    and current_imp = "wnb_current_imp e_tgt" and current_cost_imp = wnb_current_cost_imp
    and move_imp = wnb_move_imp and reset_imp = wnb_reset_imp
    and reset_all_imp = "wnb_reset_all_imp n"
    and pot_is_map = is_iam and pot_lookup_imp = iam_lookup and pot_update_imp = iam_update
    and left_is_set = is_ias and left_is_it = ias_is_it and left_it_init = ias_it_init
    and left_it_has_next = ias_it_has_next and left_it_next = ias_it_next
  apply (intro init_potential_imp.intro init_potential_coll.intro init_potential_coll_axioms.intro
               fmap_Map wcsr.wnb.indexed_iterable_set_axioms real_embedding_axioms
               wcsr.wnb_imp.weighted_neighbourhoods_imp_spec_axioms iam_imp_map_conn
               fmap_conn_facts ias_imp_set_ordered_iterate)
  by (simp_all add: fset_iterate_def fset_set_def)

end

subsection \<open>One Path Search\<close>

text \<open>For a matching @{term M} and a potential @{term \<pi>} that satisfy the precondition of the path
      search, the imperative path search of @{locale primal_dual_path_search_imp} is interpreted on
      the data structures of the instantiation.\<close>

lemma pds_M_eq: "primal_dual_path_search_spec.\<M> M = {{u, v} |u v. Some v = M u}"
  by (rule primal_dual_path_search_spec.\<M>_def[OF primal_dual_path_search_spec.intro[OF fmap_Map
                                                    fmap_Map fset_Set]])

lemma M_abs: "{{u, v} |u v. Some v = M u} = aug_csr.\<M> M"
  unfolding aug_csr.\<M>_def' fmap_lookup_def by (metis (no_types, lifting))

locale hungarian_csr_search = hungarian_csr_input +
  fixes M :: "nat \<rightharpoonup> nat" and \<pi> :: "nat \<rightharpoonup> real"
  assumes buddy_sym: "\<And>u v. M u = Some v \<Longrightarrow> M v = Some u"
    and buddy_matching: "graph_matching G {{u, v} | u v. M u = Some v}"
    and buddy_tight: "\<And>u v. {u, v} \<in> {{u, v} | u v. Some v = M u} \<Longrightarrow>
                       abstract_real_map \<pi> u + abstract_real_map \<pi> v = ecost u v"
    and pot_feasible: "\<And>u v. {u, v} \<in> G \<Longrightarrow>
                       abstract_real_map \<pi> u + abstract_real_map \<pi> v \<le> ecost u v"
    and pot_dom: "dom \<pi> \<subseteq> L \<union> R"
begin

lemma buddy_lookup_rule:
  "<aug_csr.buddy_assn M Bdi> iam_lookup v Bdi <\<lambda>r. aug_csr.buddy_assn M Bdi * \<up>(r = M v)>"
  using aug_csr.buddy_lookup_rule[of M Bdi v] by (simp add: fmap_lookup_def)

sublocale ps: primal_dual_path_search_imp
  where ben_empty = Map.empty and ben_upd = fmap_update and ben_delete = fmap_delete
    and ben_lookup = fmap_lookup and ben_invar = fmap_invar
    and missed_empty = Map.empty and missed_upd = fmap_update and missed_delete = fmap_delete
    and missed_lookup = fmap_lookup and missed_invar = fmap_invar
    and vset_empty = "{}" and vset_insert = fset_insert and vset_delete = fset_delete
    and vset_isin = fset_isin and vset_to_set = fset_set and vset_invar = finite
    and G = G and edge_costs = ecost and edge_costs_code = ecost and left = L and right = R
    and in_G = "\<lambda>u v. {u, v} \<in> G"
    and rnb_invar = graph.csr_invar and rnb_abstract = wcsr.wnb_abstract
    and rnb_current = wcsr.wnb_current and rnb_has = graph.csr_has
    and rnb_iterated = wcsr.wnb_iterated and rnb_remaining = wcsr.wnb_remaining
    and rnb_move = graph.csr_move and rnb_reset = graph.csr_reset and rnb_init = nb_init
    and buddy = M
    and extend_forest_even_unclassified = forest_csr.extend_forest_even_unclassified
    and evens = evens and odds = odds and get_path = forest_csr.get_path
    and abstract_forest = forest_csr.abstract_forest and empty_forest = forest_csr.empty_forest
    and forest_invar = forest_csr.forest_invar and roots = roots
    and potential_upd = fmap_update and potential_lookup = fmap_lookup
    and potential_invar = fmap_invar and initial_pot = \<pi>
    and heap_empty = heap_empty and heap_extract_min = heap_extract_min
    and heap_decrease_key = heap_decrease_key and heap_insert = heap_insert
    and heap_invar = "heap_invar (Vs G)" and heap_abstract = heap_abstract
    and vset_iterate_ben = fset_iterate and vset_iterate_pot = fset_iterate
    and vset_filter = fset_filter and vset_is_empty = fset_is_empty
    and h = h
    and queue_assn = hp.heap_assn and queue_empty_imp = "heap_empty_imp n 0"
    and queue_clear_imp = heap_clear_imp and queue_extract_min_imp = heap_extract_min_key_imp
    and queue_key_of_imp = heap_key_of_imp and queue_decrease_key_imp = heap_decrease_key_imp
    and queue_insert_imp = heap_insert_imp
    and nb_assn = wcsr.wnb_assn and has_imp = wnb_has_imp and current_imp = "wnb_current_imp e_tgt"
    and current_cost_imp = wnb_current_cost_imp and move_imp = wnb_move_imp
    and reset_imp = wnb_reset_imp and reset_all_imp = "wnb_reset_all_imp n"
    and lst = sorted_list_of_set and forest_assn = forest_csr.forest_assn
    and forest_empty_imp = "forest_csr_empty n" and forest_clear_imp = forest_csr_clear
    and forest_add_root_imp = forest_csr_add_root and forest_extend_imp = forest_csr_extend
    and evens_memb_imp = forest_csr.evens_memb_imp and odds_memb_imp = forest_csr.odds_memb_imp
    and forest_is_it = forest_csr.forest_is_it and forest_it_init = forest_csr_it_init
    and forest_it_has_next = ias_it_has_next and forest_it_next = ias_it_next
    and get_path_imp = forest_csr_get_path
    and ben_is_map = is_iam and ben_lookup_imp = iam_lookup and ben_update_imp = iam_update
    and ben_clear_imp = iam_clear
    and missed_is_map = is_iam and missed_lookup_imp = iam_lookup
    and missed_update_imp = iam_update and missed_clear_imp = iam_clear
    and pot_is_map = is_iam and pot_lookup_imp = iam_lookup and pot_update_imp = iam_update
    and left_is_set = is_ias and left_is_it = ias_is_it and left_it_init = ias_it_init
    and left_it_has_next = ias_it_has_next and left_it_next = ias_it_next
    and buddy_assn = "aug_csr.buddy_assn M" and buddy_imp = "\<lambda>Bdi v. iam_lookup v Bdi"
  apply (intro primal_dual_path_search_imp.intro primal_dual_path_search_imp_axioms.intro
               primal_dual_path_search.intro primal_dual_path_search_spec.intro
               primal_dual_path_search_axioms.intro
               fmap_Map fset_Set forest_csr.satisified hp.heap_key_value_queue_hungarian
               wcsr.wnb.indexed_iterable_set_axioms
               real_embedding_axioms hp.hqueue.key_value_queue_imp_axioms
               wcsr.wnb_imp.weighted_neighbourhoods_imp_spec_axioms
               forest_csr.alternating_forest_imp_spec
               iam_imp_map_conn_clear iam_imp_map_conn fmap_conn_facts ias_imp_set_ordered_iterate
               buddy_lookup_rule)
  apply (unfold fset_set_def fmap_lookup_def)
  apply (all \<open>((rule bipartite_G wcsr.wnb.indexed_iterable_set_axioms wcsr.csr_init_invar
                     ecost_sym pot_feasible buddy_sym buddy_matching buddy_tight pot_dom
                     fmap_conn_facts fset_iterate_foldl_set
                     wcsr.wnb_imp.weighted_neighbourhoods_imp_spec_axioms); assumption?)?\<close>)
  apply (all \<open>(simp add: wnb_abstract_init primal_dual_path_search_spec.\<M>_def fset_filter_def
                         fset_is_empty_def fmap_invar_def fset_iterate_def)?\<close>)
  apply (all \<open>(simp only: pds_M_eq, blast)?\<close>)
  done

lemma fsearch_eq: "ps.search_path = fsearch M \<pi>"
  by (simp add: fsearch_def)

lemma scratch_eq:
  "csr_scratch_assn (Ci, Qi, Li, Fi, Bi, Mi) = ps.scratch_assn Ci Qi Fi Bi Mi * is_ias L Li"
  by (simp add: csr_scratch_assn_def ps.scratch_assn_def fset_set_def)

theorem path_search_csr_rule:
  assumes len: "card (L \<union> R) \<le> length xs"
  shows "<csr_scratch_assn Si * aug_csr.buddy_assn M Bdi * potm.map_assn \<pi> Pti * Ra \<mapsto>\<^sub>a xs>
         path_search_csr n Si Bdi Pti Ra
         <\<lambda>(res, Pti', Si'). \<exists>\<^sub>Axs'. csr_scratch_assn Si' * aug_csr.buddy_assn M Bdi * Ra \<mapsto>\<^sub>a xs' *
            \<up>(length xs' = length xs) *
            (case fsearch M \<pi> of
               Dual_Unbounded \<Rightarrow> \<up>(res = Imp_Unbounded) * potm.map_assn \<pi> Pti'
             | Lefts_Matched \<Rightarrow> \<up>(res = Imp_Matched) * potm.map_assn \<pi> Pti'
             | Next_Iteration p \<pi>' \<Rightarrow>
                 \<up>(\<exists>k. res = Imp_Path k \<and> k \<le> length xs' \<and> take k xs' = p) * potm.map_assn \<pi>' Pti')>"
proof -
  obtain Ci Qi Li Fi Bi Mi where Si: "Si = (Ci, Qi, Li, Fi, Bi, Mi)"
    by (cases Si) (metis prod_cases5)
  have len': "card (fset_set L \<union> fset_set R) \<le> length xs" using len by (simp add: fset_set_def)
  have r: "<ps.scratch_assn Ci Qi Fi Bi Mi * is_ias L Li * aug_csr.buddy_assn M Bdi *
            potm.map_assn \<pi> Pti * Ra \<mapsto>\<^sub>a xs>
           pds_csr_search n Ci Qi Pti Bdi Li Ra Fi Bi Mi
           <\<lambda>(res, Pti', Fi', Bi', Mi'). \<exists>\<^sub>Axs'.
              ps.scratch_assn Ci Qi Fi' Bi' Mi' * is_ias L Li * aug_csr.buddy_assn M Bdi *
              Ra \<mapsto>\<^sub>a xs' * \<up>(length xs' = length xs) * ps.search_post Pti' res xs'>"
    using ps.search_imp_rule[OF len', of Ci Qi Fi Bi Mi Li Bdi Pti Ra]
    by (simp add: pds_csr_search_def fset_set_def)
  note [simp del] = ps.scratch_assn_def
  show ?thesis
    unfolding Si path_search_csr_def prod.case scratch_eq
    by (sep_auto heap: r simp: ps.search_post_def fsearch_eq scratch_eq
                  split: path_search_result.splits)
qed

lemmas fsearch_correct =
  ps.search_path_correct[unfolded fsearch_eq pds_M_eq M_abs fset_set_def]

end

subsection \<open>The Top Loop\<close>

context hungarian_csr_input
begin

abbreviation "wfun \<equiv> \<lambda>e. ecost (pick_one e) (pick_another e)"

definition "pot_invar \<pi> = (fmap_invar \<pi> \<and> dom (fmap_lookup \<pi>) \<subseteq> Vs G)"

abbreviation "init_pot \<equiv> snd (ipot.init_potential_coll nb_init Map.empty L)"

lemma wfun_eq:
  assumes "{u, v} \<in> G"
  shows "wfun {u, v} = ecost u v"
proof -
  have "u \<noteq> v"
    by (rule bipartite_edgeE[OF assms bipartite_G]) (auto simp: doubleton_eq_iff)
  thus ?thesis
    using pick_one_and_another_props(3)[of "{u, v}", OF exI[of _ u]]
    by (auto simp: doubleton_eq_iff ecost_sym[OF assms])
qed

lemma init_pot_props:
  "fmap_invar init_pot"
  "\<And>u v. \<lbrakk>u \<in> L; v \<in> wcsr.wnb_abstract nb_init u\<rbrakk> \<Longrightarrow>
          abstract_real_map (fmap_lookup init_pot) u \<le> ecost u v"
  "dom (fmap_lookup init_pot) \<subseteq> L"
  using ipot.init_potential_coll_props[of nb_init L, OF wcsr.csr_init_invar]
  by (auto simp: fset_set_def wnb_abstract_finite)

lemma feasible_init:
  "feasible_min_perfect_dual G wfun (\<lambda>v. abstract_real_map (fmap_lookup init_pot) v)"
proof (rule feasible_min_perfect_dualI)
  fix e u v assume e: "e \<in> G" "e = {u, v}"
  then obtain i where i: "i < length fs" "e = {fs ! i, ts ! i}" by (auto simp: G_def)
  have l: "fs ! i \<in> L" and r: "ts ! i \<in> R" using fs_L ts_R i(1) by auto
  hence "ts ! i \<notin> dom (fmap_lookup init_pot)" using init_pot_props(3) sides_disjoint by auto
  hence r0: "abstract_real_map (fmap_lookup init_pot) (ts ! i) = 0"
    by (simp add: abstract_real_map_outside_dom)
  have "ts ! i \<in> wcsr.wnb_abstract nb_init (fs ! i)"
    using wnb_abstract_init[OF l] i e by auto
  hence le: "abstract_real_map (fmap_lookup init_pot) (fs ! i) \<le> ecost (fs ! i) (ts ! i)"
    by (rule init_pot_props(2)[OF l])
  have w: "wfun e = ecost (fs ! i) (ts ! i)"
    using wfun_eq[of "fs ! i" "ts ! i"] e(1) i(2) by simp
  have "(f::nat \<Rightarrow> real) u + f v = f (fs ! i) + f (ts ! i)" for f
    using e(2) i(2) by (auto simp: doubleton_eq_iff)
  thus "abstract_real_map (fmap_lookup init_pot) u + abstract_real_map (fmap_lookup init_pot) v
        \<le> wfun e"
    using r0 le w by simp
qed

text \<open>The precondition of the path search gives an instance of @{locale hungarian_csr_search}.\<close>

lemma search_instance:
  assumes "aug_csr.invar_matching G M" "pot_invar \<pi>"
          "aug_csr.\<M> M \<subseteq> tight_subgraph G wfun (\<lambda>v. abstract_real_map (fmap_lookup \<pi>) v)"
          "feasible_min_perfect_dual G wfun (\<lambda>v. abstract_real_map (fmap_lookup \<pi>) v)"
  shows "hungarian_csr_search h n fs ts ws ls rs M \<pi>"
proof (intro hungarian_csr_search.intro hungarian_csr_input.intro real_embedding_axioms
             hungarian_csr_search_axioms.intro)
  show "hungarian_csr_input_axioms n fs ts ws ls rs"
    by (intro hungarian_csr_input_axioms.intro ts_length ws_length ls_distinct rs_distinct fs_ls
              ts_rs sides_disjoint verts_below no_parallel)
  show "\<And>u v. M u = Some v \<Longrightarrow> M v = Some u"
    using assms(1)
    by (auto simp: aug_csr.invar_matching_def aug_csr.symmetric_buddies_def fmap_lookup_def)
  show "graph_matching G {{u, v} |u v. M u = Some v}"
    using assms(1) by (simp add: aug_csr.invar_matching_def aug_csr.\<M>_def' fmap_lookup_def)
  show "dom \<pi> \<subseteq> L \<union> R" using assms(2) by (simp add: pot_invar_def Vs_G fmap_lookup_def)
  show "\<And>u v. {u, v} \<in> G \<Longrightarrow> abstract_real_map \<pi> u + abstract_real_map \<pi> v \<le> ecost u v"
    using assms(4) wfun_eq by (fastforce simp: feasible_min_perfect_dual_def fmap_lookup_def)
  fix u v assume "{u, v} \<in> {{u, v} |u v. Some v = M u}"
  hence "{u, v} \<in> tight_subgraph G wfun (\<lambda>v. abstract_real_map (fmap_lookup \<pi>) v)"
    using assms(3) M_abs by blast
  hence "{u, v} \<in> G" "wfun {u, v} = abstract_real_map \<pi> u + abstract_real_map \<pi> v"
    by (auto simp: tight_subgraph_def doubleton_eq_iff fmap_lookup_def add.commute insert_commute)
  thus "abstract_real_map \<pi> u + abstract_real_map \<pi> v = ecost u v" using wfun_eq by simp
qed

sublocale maug: matching_augmentation Map.empty fmap_update fmap_delete fmap_lookup fmap_invar
  by (intro matching_augmentation.intro matching_augmentation_spec.intro fmap_Map)

abbreviation "csr_precond \<equiv>
  hungarian_loop_spec.path_search_precond (\<lambda>\<pi> v. abstract_real_map (fmap_lookup \<pi>) v) pot_invar
    (maug.invar_matching G) maug.\<M> wfun G"

lemma precond_instance:
  assumes "csr_precond M \<pi>"
  shows "hungarian_csr_search h n fs ts ws ls rs M \<pi>"
proof -
  note d = hungarian_loop_spec.path_search_precondD[OF assms]
  show ?thesis by (rule search_instance[OF d(1) d(2) d(4) d(5)])
qed

lemma path_search_rule_csr:
  assumes "csr_precond M \<pi>" "card (L \<union> R) \<le> length xs"
  shows "<csr_scratch_assn Si * aug_csr.buddy_assn M Bdi * potm.map_assn \<pi> Pti * Ra \<mapsto>\<^sub>a xs>
         path_search_csr n Si Bdi Pti Ra
         <\<lambda>(res, Pti', Si'). \<exists>\<^sub>Axs'. csr_scratch_assn Si' * aug_csr.buddy_assn M Bdi * Ra \<mapsto>\<^sub>a xs' *
            \<up>(length xs' = length xs) *
            (case fsearch M \<pi> of
               Dual_Unbounded \<Rightarrow> \<up>(res = Imp_Unbounded) * potm.map_assn \<pi> Pti'
             | Lefts_Matched \<Rightarrow> \<up>(res = Imp_Matched) * potm.map_assn \<pi> Pti'
             | Next_Iteration p \<pi>' \<Rightarrow>
                 \<up>(\<exists>k. res = Imp_Path k \<and> k \<le> length xs' \<and> take k xs' = p) * potm.map_assn \<pi>' Pti')>"
proof -
  interpret s: hungarian_csr_search h n fs ts ws ls rs theta M \<pi>
    by (rule precond_instance[OF assms(1)])
  show ?thesis by (rule s.path_search_csr_rule[OF assms(2)])
qed

text \<open>The full path search satisfies the contract of the path search of @{locale hungarian_loop}.\<close>

lemma fsearch_contract:
  "\<And>M \<pi> B. \<lbrakk>csr_precond M \<pi>; fsearch M \<pi> = Dual_Unbounded\<rbrakk>
     \<Longrightarrow> \<exists>\<pi>'. feasible_min_perfect_dual G wfun \<pi>' \<and> sum \<pi>' (L \<union> R) > B"
  "\<And>M \<pi>. \<lbrakk>csr_precond M \<pi>; fsearch M \<pi> = Lefts_Matched\<rbrakk> \<Longrightarrow> L \<subseteq> Vs (maug.\<M> M)"
  "\<And>M \<pi> \<pi>' p. \<lbrakk>csr_precond M \<pi>; fsearch M \<pi> = Next_Iteration p \<pi>'\<rbrakk> \<Longrightarrow>
     hungarian_loop_spec.good_search_result (\<lambda>\<pi> v. abstract_real_map (fmap_lookup \<pi>) v) pot_invar
       maug.\<M> wfun G M \<pi>' p"
proof-
  fix M \<pi> B assume a: "csr_precond M \<pi>" "fsearch M \<pi> = Dual_Unbounded"
  interpret s: hungarian_csr_search h n fs ts ws ls rs theta M \<pi> by (rule precond_instance[OF a(1)])
  obtain p where p: "\<forall>u v. {u, v} \<in> G \<longrightarrow> p u + p v \<le> ecost u v" "B + 1 \<le> sum p (L \<union> R)"
    using s.fsearch_correct(2)[OF a(2), of "B + 1"] by auto
  have "feasible_min_perfect_dual G wfun p"
  proof (rule feasible_min_perfect_dualI)
    fix e u v assume "e \<in> G" "e = {u, v}"
    thus "p u + p v \<le> wfun e" using p(1) wfun_eq by auto
  qed
  thus "\<exists>\<pi>'. feasible_min_perfect_dual G wfun \<pi>' \<and> sum \<pi>' (L \<union> R) > B" using p(2) by force
next
  fix M \<pi> assume a: "csr_precond M \<pi>" "fsearch M \<pi> = Lefts_Matched"
  interpret s: hungarian_csr_search h n fs ts ws ls rs theta M \<pi> by (rule precond_instance[OF a(1)])
  show "L \<subseteq> Vs (maug.\<M> M)" using s.fsearch_correct(1)[OF a(2)] by simp
next
  fix M \<pi> \<pi>' p assume a: "csr_precond M \<pi>" "fsearch M \<pi> = Next_Iteration p \<pi>'"
  interpret s: hungarian_csr_search h n fs ts ws ls rs theta M \<pi> by (rule precond_instance[OF a(1)])
  note r = s.fsearch_correct(3-8)[OF a(2)]
  have inG: "{u, v} \<in> G" if "{u, v} \<in> maug.\<M> M" for u v
    using s.buddy_matching that M_abs[of M] by (auto simp: eq_commute[of "Some _"])
  show "hungarian_loop_spec.good_search_result (\<lambda>\<pi> v. abstract_real_map (fmap_lookup \<pi>) v) pot_invar
          maug.\<M> wfun G M \<pi>' p"
  proof (rule hungarian_loop_spec.good_search_resultI)
    show "pot_invar \<pi>'" using r(5,6) by (simp add: pot_invar_def Vs_G fmap_lookup_def)
    show "maug.\<M> M \<subseteq> tight_subgraph G wfun (\<lambda>v. abstract_real_map (fmap_lookup \<pi>') v)"
    proof
      fix e assume e: "e \<in> maug.\<M> M"
      then obtain u v where uv: "e = {u, v}" using M_abs[of M] by blast
      have "{u, v} \<in> maug.\<M> M" using e uv by simp
      thus "e \<in> tight_subgraph G wfun (\<lambda>v. abstract_real_map (fmap_lookup \<pi>') v)"
        using r(2) inG wfun_eq uv by (intro in_tight_subgraphI) (auto simp: fmap_lookup_def)
    qed
    show "feasible_min_perfect_dual G wfun (\<lambda>v. abstract_real_map (fmap_lookup \<pi>') v)"
    proof (rule feasible_min_perfect_dualI)
      fix e u v assume "e \<in> G" "e = {u, v}"
      thus "abstract_real_map (fmap_lookup \<pi>') u + abstract_real_map (fmap_lookup \<pi>') v \<le> wfun e"
        using r(1) wfun_eq by (auto simp: fmap_lookup_def)
    qed
    have pG: "set (edges_of_path p) \<subseteq> G" using r(4) by (auto dest: path_edges_subset)
    show "set (edges_of_path p) \<subseteq> tight_subgraph G wfun (\<lambda>v. abstract_real_map (fmap_lookup \<pi>') v)"
    proof
      fix e assume e: "e \<in> set (edges_of_path p)"
      have eG: "e \<in> G" by (rule subsetD[OF pG e])
      obtain u v where uv0: "e = {u, v}" using bipartite_edgeE[OF eG bipartite_G] by blast
      hence uv: "e = {u, v}" "{u, v} \<in> G" using eG by simp_all
      thus "e \<in> tight_subgraph G wfun (\<lambda>v. abstract_real_map (fmap_lookup \<pi>') v)"
        using r(3) e wfun_eq by (intro in_tight_subgraphI) (auto simp: fmap_lookup_def)
    qed
    show "graph_augmenting_path G (maug.\<M> M) p" by (rule r(4))
  qed
qed

text \<open>The path search with the shortcut, for the threshold @{term theta}.\<close>

definition "fsearch_sc M \<pi> =
  path_search_shortcut_spec.path_search_sc fsearch wcsr.wnb_current graph.csr_has graph.csr_move
    graph.csr_reset fmap_lookup fmap_lookup fmap_update nb_init ecost (sorted_list_of_set L)
    (card (maug.\<M> M) < theta) M \<pi>"

lemma buddy_lookup_rule_gen:
  "<aug_csr.buddy_assn M Bdi> iam_lookup v Bdi
   <\<lambda>r. aug_csr.buddy_assn M Bdi * \<up>(r = fmap_lookup M v)>"
  using aug_csr.buddy_lookup_rule[of M Bdi v] .

lemma buddy_free:
  assumes "maug.invar_matching G M"
  shows "fmap_lookup M v = None \<longleftrightarrow> v \<notin> Vs (maug.\<M> M)"
proof
  have sym: "\<And>u w. fmap_lookup M u = Some w \<Longrightarrow> fmap_lookup M w = Some u"
    using assms by (simp add: maug.invar_matching_def maug.symmetric_buddies_def)
  assume none: "fmap_lookup M v = None"
  show "v \<notin> Vs (maug.\<M> M)"
  proof
    assume "v \<in> Vs (maug.\<M> M)"
    then obtain e where e: "e \<in> maug.\<M> M" "v \<in> e" by (auto simp: Vs_def)
    then obtain a b where ab: "e = {a, b}" "fmap_lookup M a = Some b"
      by (auto simp: maug.\<M>_def')
    have "v = a \<or> v = b" using e(2) ab(1) by simp
    thus False using ab(2) sym[OF ab(2)] none by auto
  qed
next
  assume nV: "v \<notin> Vs (maug.\<M> M)"
  show "fmap_lookup M v = None"
  proof (rule ccontr)
    assume "fmap_lookup M v \<noteq> None"
    then obtain w where w: "fmap_lookup M v = Some w" by auto
    have "{v, w} \<in> maug.\<M> M" unfolding maug.\<M>_def' using w by blast
    hence "v \<in> Vs (maug.\<M> M)" by (auto simp: Vs_def)
    thus False using nV by simp
  qed
qed

sublocale sc: path_search_shortcut_imp
  where potential_abstract = "\<lambda>\<pi> v. abstract_real_map (fmap_lookup \<pi>) v"
    and init_potential = init_pot and potential_invar = pot_invar
    and empty_matching = Map.empty and matching_invar = "maug.invar_matching G"
    and augment = maug.augment_impl and matching_abstract = maug.\<M>
    and edge_costs = wfun and card_L = "length ls" and card_R = "length rs"
    and path_search = fsearch and G = G
    and rnb_current = wcsr.wnb_current and rnb_has = graph.csr_has and rnb_move = graph.csr_move
    and rnb_reset = graph.csr_reset and buddy_lookup = fmap_lookup
    and potential_lookup = fmap_lookup and potential_upd = fmap_update and rnb_init = nb_init
    and edge_costs_code = ecost and left_order = "sorted_list_of_set L"
    and rnb_invar = graph.csr_invar and rnb_abstract = wcsr.wnb_abstract
    and rnb_iterated = wcsr.wnb_iterated and rnb_remaining = wcsr.wnb_remaining and K = L
    and L = L and R = R and h = h
    and nb_assn = wcsr.wnb_assn and has_imp = wnb_has_imp and current_imp = "wnb_current_imp e_tgt"
    and current_cost_imp = wnb_current_cost_imp and move_imp = wnb_move_imp
    and reset_imp = wnb_reset_imp and reset_all_imp = "wnb_reset_all_imp n"
    and pot_is_map = is_iam and pot_lookup_imp = iam_lookup and pot_update_imp = iam_update
    and pot_m_invar = fmap_invar
    and left_is_set = is_ias and lst = sorted_list_of_set and left_is_it = ias_is_it
    and left_it_init = ias_it_init and left_it_has_next = ias_it_has_next
    and left_it_next = ias_it_next
    and buddy_assn = aug_csr.buddy_assn and buddy_imp = "\<lambda>Bdi v. iam_lookup v Bdi"
  apply (intro path_search_shortcut_imp.intro path_search_shortcut_imp_axioms.intro
               path_search_shortcut.intro path_search_shortcut_axioms.intro
               nb_best_scan_imp.intro nb_best_scan.intro
               wcsr.wnb.indexed_iterable_set_axioms real_embedding_axioms
               wcsr.wnb_imp.weighted_neighbourhoods_imp_spec_axioms
               iam_imp_map_conn fmap_conn_facts ias_imp_set_ordered_iterate buddy_lookup_rule_gen)
  apply (rule bipartite_G)
  apply (simp add: L_less)
  apply (rule subset_refl)
  apply (rule wcsr.csr_init_invar)
  apply (simp add: wnb_abstract_init)
  apply (rule wnb_abstract_finite)
  apply (simp add: wfun_eq)
  apply (rule buddy_free, assumption)
  apply (rule refl)
  apply (auto simp: pot_invar_def Vs_G fmap_lookup_def fmap_invar_def fmap_update_def
              split: if_splits)[2]
  apply (rule fsearch_contract(1); assumption)
  apply (rule fsearch_contract(2); assumption)
  apply (rule fsearch_contract(3); assumption)
  apply (assumption | rule refl)+
  done

lemma path_search_sc_rule_csr:
  assumes "csr_precond M \<pi>" "card (L \<union> R) \<le> length xs"
  shows "<csr_scratch_assn Si * aug_csr.counted_assn M Mt * potm.map_assn \<pi> Pti * Ra \<mapsto>\<^sub>a xs>
         path_search_sc_csr n theta Si Mt Pti Ra
         <\<lambda>(res, Pti', Si'). \<exists>\<^sub>Axs'. csr_scratch_assn Si' * aug_csr.counted_assn M Mt * Ra \<mapsto>\<^sub>a xs' *
            \<up>(length xs' = length xs) *
            (case fsearch_sc M \<pi> of
               Dual_Unbounded \<Rightarrow> \<up>(res = Imp_Unbounded) * potm.map_assn \<pi> Pti'
             | Lefts_Matched \<Rightarrow> \<up>(res = Imp_Matched) * potm.map_assn \<pi> Pti'
             | Next_Iteration p \<pi>' \<Rightarrow>
                 \<up>(\<exists>k. res = Imp_Path k \<and> k \<le> length xs' \<and> take k xs' = p) * potm.map_assn \<pi>' Pti')>"
proof -
  obtain Ci Qi Li Fi Bi Mi where Si: "Si = (Ci, Qi, Li, Fi, Bi, Mi)"
    by (cases Si) (metis prod_cases5)
  obtain Bdi Ki where Mt: "Mt = (Bdi, Ki)" by (cases Mt)
  note ps = path_search_rule_csr[OF assms]
  note mc = aug_csr.matching_card_imp_rule[of M "(Bdi, Ki)", unfolded aug_csr.counted_assn_pair]
  have len2: "2 \<le> length xs" if "sc.shortcut M \<pi> = Some (l, j, \<pi>')" for l j \<pi>'
  proof -
    have "\<exists>x. snd (sc.first_success M \<pi>) = Some (l, j, x)"
      using that by (cases "snd (sc.first_success M \<pi>)")
                    (auto simp: path_search_shortcut_spec.shortcut_def)
    then obtain x where "snd (sc.first_success M \<pi>) = Some (l, j, x)" ..
    hence "sc.row_ok M \<pi> l j x" by (rule sc.first_success_props(3))
    hence l: "l \<in> L" "{l, j} \<in> G" by (auto simp: sc.row_ok_def)
    hence j: "j \<in> R - L" using bipartite_edgeD(1)[OF l(2) bipartite_G] by simp
    have "card {l, j} \<le> card (L \<union> R)" using l(1) j by (intro card_mono) auto
    moreover have "card {l, j} = 2" using l(1) j by auto
    ultimately show ?thesis using assms(2) by linarith
  qed
  have sh: "<csr_scratch_assn Si * aug_csr.buddy_assn M Bdi * potm.map_assn \<pi> Pti * Ra \<mapsto>\<^sub>a xs>
            sc_csr_shortcut n Ci Li Bdi Pti Ra
            <\<lambda>(b, Pti'). \<exists>\<^sub>Axs'. csr_scratch_assn Si * aug_csr.buddy_assn M Bdi * Ra \<mapsto>\<^sub>a xs' *
               \<up>(length xs' = length xs) *
               (case sc.shortcut M \<pi> of
                  None \<Rightarrow> \<up>(\<not> b \<and> xs' = xs) * potm.map_assn \<pi> Pti'
                | Some (l, j, \<pi>') \<Rightarrow> \<up>(b \<and> take 2 xs' = [l, j]) * potm.map_assn \<pi>' Pti')>"
    unfolding Si csr_scratch_assn_def prod.case
    by (sep_auto heap: sc.shortcut_imp_rule[OF _ _ len2]
                 simp: sc_csr_shortcut_def sc.first_success_props)
  have eq: "fsearch_sc M \<pi> =
    (if card (maug.\<M> M) < theta then
       (case sc.shortcut M \<pi> of Some (l, j, \<pi>') \<Rightarrow> Next_Iteration [l, j] \<pi>' | None \<Rightarrow> fsearch M \<pi>)
     else fsearch M \<pi>)"
    by (simp add: fsearch_sc_def path_search_shortcut_spec.path_search_sc_def)
  note sh' = sh[unfolded Si]
  show ?thesis
  proof (cases "card (maug.\<M> M) < theta")
    case False
    thus ?thesis
      unfolding path_search_sc_csr_def Si Mt prod.case eq aug_csr.counted_assn_pair
      by (cases "fsearch M \<pi>") (sep_auto heap: mc ps)+
  next
    case True
    show ?thesis
    proof (cases "sc.shortcut M \<pi>")
      case None
      thus ?thesis
        unfolding path_search_sc_csr_def Si Mt prod.case eq aug_csr.counted_assn_pair
        using True by (cases "fsearch M \<pi>") (sep_auto heap: mc sh' ps)+
    next
      case (Some a)
      then obtain l j \<pi>' where a: "sc.shortcut M \<pi> = Some (l, j, \<pi>')" by (cases a) auto
      have l2: "2 \<le> length xs" by (rule len2[OF a])
      show ?thesis
        unfolding path_search_sc_csr_def Si Mt prod.case eq aug_csr.counted_assn_pair
        using True l2 by (sep_auto heap: mc sh' simp: a)
    qed
  qed
qed

lemma augment_card:
  assumes "maug.invar_matching G M" "graph_augmenting_path G (maug.\<M> M) p"
  shows "card (maug.\<M> (maug.augment_impl M p)) = Suc (card (maug.\<M> M))"
  using new_matching_plus_one[of "maug.\<M> M" p] maug.augmentation_correct(2)[OF assms] assms
  by (simp add: maug.invar_matching_def)
sublocale hl: hungarian_top_loop_imp
  where potential_abstract = "\<lambda>\<pi> v. abstract_real_map (fmap_lookup \<pi>) v"
    and init_potential = init_pot and potential_invar = pot_invar
    and empty_matching = Map.empty and matching_invar = "maug.invar_matching G"
    and augment = maug.augment_impl and matching_abstract = maug.\<M>
    and edge_costs = wfun and card_L = "length ls" and card_R = "length rs"
    and path_search = fsearch_sc and G = G and L = L and R = R
    and path_search_imp = "path_search_sc_csr n theta" and augment_imp = augment_counted_csr
    and scratch_assn = csr_scratch_assn and matching_assn = aug_csr.counted_assn
    and pot_assn = potm.map_assn and len_bound = "card (L \<union> R)"
proof (intro hungarian_top_loop_imp.intro hungarian_top_loop_imp_axioms.intro hungarian_loop.intro,
       goal_cases)
  case 1 show ?case by (rule bipartite_G)
next
  case 2 show ?case by (simp add: distinct_card[OF ls_distinct])
next
  case 3 show ?case by (simp add: distinct_card[OF rs_distinct])
next
  case 4 show ?case by simp
next
  case 5 show ?case by simp
next
  case 6 show ?case by (simp add: Vs_G)
next
  case 7 show ?case using init_pot_props(1,3) by (auto simp: pot_invar_def Vs_G)
next
  case 8 show ?case by (rule feasible_init)
next
  case (9 M) thus ?case by (simp add: maug.invar_matching_def)
next
  case 10 show ?case by (rule maug.empty_matching_props(1))
next
  case 11 show ?case by (rule maug.empty_matching_props(2))
next
  case (12 M p) thus ?case by (rule maug.augmentation_correct(1))
next
  case (13 M p) thus ?case by (rule maug.augmentation_correct(2))
next
  case (14 M \<pi> B) thus ?case unfolding fsearch_sc_def by (rule sc.path_search_sc_correct(1))
next
  case (15 M \<pi>) thus ?case unfolding fsearch_sc_def by (rule sc.path_search_sc_correct(2))
next
  case (16 M \<pi> \<pi>' p) thus ?case unfolding fsearch_sc_def by (rule sc.path_search_sc_correct(3))
next
  case 17 thus ?case by (rule path_search_sc_rule_csr)
next
  case (18 M p k xs Mi Ra)
  thus ?case using aug_csr.augment_counted_imp_rule[of k xs M Mi Ra] augment_card[OF 18(1,2)]
    by simp
qed

end

subsection \<open>Initialisation\<close>

lemma perm_weights_rule:
  "\<lbrakk>i \<le> length es; length xs = length es; \<forall>e\<in>set es. e_id e < length vs\<rbrakk> \<Longrightarrow>
   <Ea \<mapsto>\<^sub>a es * Wa \<mapsto>\<^sub>a vs * Wc \<mapsto>\<^sub>a xs> perm_weights_imp Ea Wa Wc i (length es)
   <\<lambda>_. Ea \<mapsto>\<^sub>a es * Wa \<mapsto>\<^sub>a vs * Wc \<mapsto>\<^sub>a (take i xs @ drop i (map (\<lambda>e. vs ! e_id e) es))>"
proof (induction "length es - i" arbitrary: i xs)
  case 0
  hence "i = length es" by simp
  thus ?case using 0 by (subst perm_weights_imp.simps) sep_auto
next
  case (Suc d)
  hence i: "i < length es" by simp
  have eid: "e_id (es ! i) < length vs" using Suc.prems(3) i by simp
  have IH: "<Ea \<mapsto>\<^sub>a es * Wa \<mapsto>\<^sub>a vs * Wc \<mapsto>\<^sub>a xs[i := vs ! e_id (es ! i)]>
            perm_weights_imp Ea Wa Wc (Suc i) (length es)
            <\<lambda>_. Ea \<mapsto>\<^sub>a es * Wa \<mapsto>\<^sub>a vs * Wc \<mapsto>\<^sub>a (take (Suc i) (xs[i := vs ! e_id (es ! i)]) @
                                           drop (Suc i) (map (\<lambda>e. vs ! e_id e) es))>"
    by (rule Suc.hyps(1)) (use Suc i in auto)
  have t: "(take (Suc i) xs)[i := vs ! e_id (es ! i)] = take i xs @ [vs ! e_id (es ! i)]"
    using i Suc.prems(2) by (simp add: take_Suc_conv_app_nth list_update_append)
  have dr: "drop i (map (\<lambda>e. vs ! e_id e) es) =
            vs ! e_id (es ! i) # drop (Suc i) (map (\<lambda>e. vs ! e_id e) es)"
    using i Cons_nth_drop_Suc[of i "map (\<lambda>e. vs ! e_id e) es"] by simp
  show ?case
    using i eid Suc.prems(2) by (subst perm_weights_imp.simps) (sep_auto heap: IH simp: t dr)
qed

lemma ias_insert_all_rule:
  "i \<le> length xs \<Longrightarrow>
   <La \<mapsto>\<^sub>a xs * is_ias S s> ias_insert_all La i (length xs) s
   <\<lambda>s'. La \<mapsto>\<^sub>a xs * is_ias (S \<union> set (drop i xs)) s'>"
proof (induction "length xs - i" arbitrary: i S s)
  case 0
  hence "i = length xs" by simp
  thus ?case by (subst ias_insert_all.simps) sep_auto
next
  case (Suc d)
  hence i: "i < length xs" by simp
  have IH: "<La \<mapsto>\<^sub>a xs * is_ias (insert (xs ! i) S) s'> ias_insert_all La (Suc i) (length xs) s'
            <\<lambda>s''. La \<mapsto>\<^sub>a xs * is_ias (insert (xs ! i) S \<union> set (drop (Suc i) xs)) s''>" for s'
    by (rule Suc.hyps(1)) (use Suc i in auto)
  have eq: "insert (xs ! i) (S \<union> set (drop (Suc i) xs)) = S \<union> set (drop i xs)"
    using i by (simp add: Cons_nth_drop_Suc[symmetric])
  show ?case
    using i by (subst ias_insert_all.simps) (sep_auto heap: ias_ins_rule IH simp: eq)
qed

context hungarian_csr_input
begin

lemma potm_empty_eq: "potm.map_assn Map.empty p = is_iam Map.empty p"
  by (rule potm.map_assn_empty_eq) (simp_all add: fmap_invar_def fmap_lookup_def)

interpretation budm: imp_map_conn is_iam iam_lookup iam_update fmap_update fmap_lookup fmap_invar
    "\<lambda>_ vi v. vi = v"
  by (intro iam_imp_map_conn fmap_conn_facts)

lemma buddy_empty_eq: "aug_csr.buddy_assn Map.empty p = is_iam Map.empty p"
  by (rule budm.map_assn_empty_eq) (simp_all add: fmap_invar_def fmap_lookup_def)

lemma init_pot_rule:
  "<graph.csr_assn nb_init (Ba, Ea, Ca) * Wc \<mapsto>\<^sub>a map (\<lambda>e. ws ! e_id e) inp.E_spec *
    is_iam Map.empty Pti *
    is_ias L Li>
   init_pot_csr ((Ba, Ea, Ca), Wc) Li Pti
   <\<lambda>Pti'. wcsr.wnb_assn (fst (ipot.init_potential_coll nb_init Map.empty L)) ((Ba, Ea, Ca), Wc) *
          potm.map_assn init_pot Pti' * is_ias L Li>"
proof -
  have r: "<wcsr.wnb_assn nb_init ((Ba, Ea, Ca), Wc) * potm.map_assn Map.empty Pti * is_ias L Li>
           init_pot_csr ((Ba, Ea, Ca), Wc) Li Pti
           <\<lambda>Pti'. wcsr.wnb_assn (fst (ipot.init_potential_coll nb_init Map.empty L)) ((Ba, Ea, Ca), Wc) *
                  potm.map_assn init_pot Pti' * is_ias L Li>"
    using ipot.init_pot_imp_rule[of nb_init L, OF wcsr.csr_init_invar]
    by (simp add: init_pot_csr_def fset_set_def wnb_abstract_finite)
  show ?thesis
    by (rule ht_cons_pre[OF _ r[unfolded potm_empty_eq]])
       (simp only: wcsr.wnb_assn_split, simp only: W_def, rule ent_refl)
qed

lemma init_coll_props:
  "graph.csr_invar (fst (ipot.init_potential_coll nb_init Map.empty L))"
  "wcsr.wnb_abstract (fst (ipot.init_potential_coll nb_init Map.empty L)) = wcsr.wnb_abstract nb_init"
  using ipot.init_potential_coll_props[of nb_init L, OF wcsr.csr_init_invar]
  by (auto simp: fset_set_def wnb_abstract_finite)

lemma card_LR: "card (L \<union> R) \<le> n"
  using card_mono[OF finite_lessThan verts_below] by simp

lemma hungarian_step:
  defines "C1 \<equiv> fst (ipot.init_potential_coll nb_init Map.empty L)"
  shows
  "<wcsr.wnb_assn C1 Ci * hp.heap_assn heap_empty Qi * forest_csr.forest_assn (forest_csr.empty_forest {}) Fi *
    is_iam Map.empty Bi * is_iam Map.empty Mi * is_ias L Li * is_iam Map.empty Mm * Ki \<mapsto>\<^sub>r 0 *
    potm.map_assn init_pot Pti * Ra \<mapsto>\<^sub>a replicate n 0>
   hungarian_csr n theta (length ls) (length rs) (Ci, Qi, Li, Fi, Bi, Mi) (Mm, Ki) Pti Ra
   <\<lambda>(r, (Mm', _), Pti', Si'). \<exists>\<^sub>AM \<pi>. aug_csr.buddy_assn M Mm' * potm.map_assn \<pi> Pti' * true *
      \<up>((r = result.success \<and> hl.hungarian = Some M) \<or> (r = result.failure \<and> hl.hungarian = None))>"
proof -
  have pre: "wcsr.wnb_assn C1 Ci * hp.heap_assn heap_empty Qi *
             forest_csr.forest_assn (forest_csr.empty_forest {}) Fi *
             is_iam Map.empty Bi * is_iam Map.empty Mi * is_ias L Li * is_iam Map.empty Mm *
             Ki \<mapsto>\<^sub>r 0 * potm.map_assn init_pot Pti * Ra \<mapsto>\<^sub>a replicate n 0
             \<Longrightarrow>\<^sub>A csr_scratch_assn (Ci, Qi, Li, Fi, Bi, Mi) * aug_csr.counted_assn Map.empty (Mm, Ki) *
                 potm.map_assn init_pot Pti * Ra \<mapsto>\<^sub>a replicate n 0"
    unfolding aug_csr.counted_assn_pair maug.empty_matching_props(2) buddy_empty_eq[symmetric]
              potm_empty_eq[symmetric]
    using init_coll_props
    by (sep_auto simp: csr_scratch_assn_def C1_def)
  have hr: "<csr_scratch_assn (Ci, Qi, Li, Fi, Bi, Mi) * aug_csr.counted_assn Map.empty (Mm, Ki) *
              potm.map_assn init_pot Pti * Ra \<mapsto>\<^sub>a replicate n 0>
            hungarian_csr n theta (length ls) (length rs) (Ci, Qi, Li, Fi, Bi, Mi) (Mm, Ki) Pti Ra
            <\<lambda>(r, Mi', Pti', Si'). \<exists>\<^sub>Axs' M \<pi>. csr_scratch_assn Si' * Ra \<mapsto>\<^sub>a xs' *
               aug_csr.counted_assn M Mi' * potm.map_assn \<pi> Pti' * \<up>(length xs' = length (replicate n (0::nat))) *
               \<up>((r = result.success \<and> hl.hungarian = Some M) \<or> (r = result.failure \<and> hl.hungarian = None))>"
    using hl.hungarian_imp_rule[of "replicate n 0"] card_LR by (simp add: hungarian_csr_def)
  show ?thesis
    by (rule ht_cons_pre[OF pre, OF ht_cons_post[OF hr]])
       (sep_auto simp: aug_csr.counted_assn_pair split: prod.splits)
qed

lemma E_spec_id: "e \<in> set inp.E_spec \<Longrightarrow> e_id e < length ws"
  using ws_length by (auto simp: inp.E_spec_def inp.blk_def inp.es_def edge_seq_def)

lemma csr_build_rule:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts> csr_build_edges n (Fa, Ta) 0
   <\<lambda>(Ba, Ea). Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Ba \<mapsto>\<^sub>a inp.B_spec * Ea \<mapsto>\<^sub>a inp.E_spec>"
  using ci.csr_build_imp_rule[of "(Fa, Ta)" 0] by (simp add: csr_build_edges_def)

text \<open>The imperative Hungarian method on the CSR representation computes the result of the
      functional @{term hl.hungarian}.\<close>

theorem hungarian_csr_run_rule:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs>
   hungarian_csr_run n theta Fa Ta Wa La Rv
   <\<lambda>(r, Mi, Pti). \<exists>\<^sub>AM \<pi>. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs *
      aug_csr.buddy_assn M Mi * potm.map_assn \<pi> Pti * true *
      \<up>((r = result.success \<and> hl.hungarian = Some M) \<or> (r = result.failure \<and> hl.hungarian = None))>"
  unfolding hungarian_csr_run_def
  by (sep_auto heap: csr_build_rule graph.csr_cursor_init_rule perm_weights_rule ias_insert_all_rule
                     ias_new_sz_rule iam_new_sz_rule init_pot_rule hp.heap_empty_imp_rule
                     forest_csr.forest_empty_imp_rule hungarian_step
               simp: E_spec_id fset_set_def)

text \<open>Together with the correctness of the functional Hungarian method: on success, the matching
      is a perfect matching of minimum weight; on failure, there is no perfect matching.\<close>

corollary hungarian_csr_run_correct:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs>
   hungarian_csr_run n theta Fa Ta Wa La Rv
   <\<lambda>(r, Mi, Pti). \<exists>\<^sub>AM \<pi>. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs *
      aug_csr.buddy_assn M Mi * potm.map_assn \<pi> Pti * true *
      \<up>((r = result.success \<and> min_weight_perfect_matching G wfun (maug.\<M> M)) \<or>
        (r = result.failure \<and> (\<nexists>M'. perfect_matching G M')))>"
  apply (rule ht_cons_post_prec[OF hungarian_csr_run_rule])
  apply (clarsimp split: prod.splits)
  apply (intro ent_ex_preI)
  apply (rule ent_ex_postI, rule ent_ex_postI)
  by (sep_auto simp: hl.hungarian_correctness(2) dest: hl.hungarian_correctness(1))

end

end