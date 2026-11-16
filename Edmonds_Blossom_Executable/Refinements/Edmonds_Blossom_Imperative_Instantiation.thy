theory Edmonds_Blossom_Imperative_Instantiation
  imports
    Blossom_Executable.Edmonds_Blossom_Imperative
    Blossom_Executable.Edmonds_Blossom_Example
    Basic_Matching.Alternating_Forest_Imperative
    Basic_Matching.Matching_Augmentation_Imperative
    Data_Structures.Imp_Array_Fun
    Data_Structures.Imp_Bool_Set_Iterate
    Data_Structures.Imp_Array_Stack
begin

provenance ai_human

section "An imperative instantiation of the blossom algorithm"

text "The imperative blossom algorithm of Edmonds_Blossom_Imperative is instantiated with arrays
  over the universe {..<nil} of vertices, where the sentinel nil is one more than the largest
  input vertex:
  \<^item> the matching is a mate array that maps a free vertex to nil,
  \<^item> the sets of the forest search and of the forest are Boolean arrays,
  \<^item> the parents of the forest are an array,
  \<^item> the queue of the forest search and the stack of contractions are array stacks, and
  \<^item> a graph is an array of neighbour lists, to which an edge is added in constant time, since the
    algorithm builds every contracted graph edge by edge.
  The functional models of the matching and the forest are total functions and sets, those of the
  graphs are red-black tree maps of neighbour lists, which may contain duplicates. The functional
  models are not executed."

subsection "The matching"

global_interpretation matching_arr: matching_augmentation
  where K = "{..<nil}" and buddy_invar = "%_. True" and buddy_upd = array_fun_upd
    and buddy_get = array_fun_lookup and buddy_empty = "%_. nil" and nil = nil
  for nil
  defines matching_abs_arr = matching_arr.\<M>
    and matching_invar_abs_arr = matching_arr.invar_matching
    and matching_lookup_arr = matching_arr.buddy_lookup
    and matching_partner_arr = matching_arr.get_partner
    and augment_arr = matching_arr.augment_impl
    and contract_path_arr = matching_arr.contract_path
    and contract_at_matched_arr = matching_arr.contract_path_at_matched
    and expand_path_arr = matching_arr.expand_path_at_matched
    and add_alternatingly_arr = matching_arr.add_alternatingly
  by(intro matching_augmentation.intro Matching_Augmentation_Specs.intro array_fun_fixed_univ_map
        matching_augmentation_axioms.intro) (auto simp: array_fun_lookup_def)

lemmas blossom_matching_arr = matching_arr.blossom_matching_spec_satisfied[
  folded matching_abs_arr_def matching_invar_abs_arr_def matching_lookup_arr_def
    matching_partner_arr_def augment_arr_def contract_path_arr_def expand_path_arr_def
    add_alternatingly_arr_def]

subsection "Graphs and matchings"

text "The functional model of a neighbourhood is a list that may contain duplicates, to which a
  neighbour is added by Cons, so that it is the neighbour list of the imperative graph. The
  adjacency maps are red-black tree maps."

definition "lset_delete x xs = filter (%y. y ~= x) xs"

definition "lset_isin xs x = (x : set xs)"

global_interpretation lset: Set_Choose
  where empty = "[]" and insert = Cons and delete = lset_delete and isin = lset_isin
    and t_set = set and invar = "%_. True" and sel = hd
  by unfold_locales (auto simp: lset_delete_def lset_isin_def)

global_interpretation gma: Graph_Matching_Specs
  where empty = Leaf and delete = RBT_Map.delete and lookup = lookup and insert = Cons
    and isin = lset_isin and t_set = set and sel = hd and update = update and adjmap_inv = M.invar
    and vset_empty = "[]" and vset_delete = lset_delete and vset_inv = "%_. True"
    and K = "{..<nil}" and nil = nil and mate_empty = "%_. nil"
    and matching_invar_abs = "matching_invar_abs_arr nil" and matching_abs = "matching_abs_arr nil"
    and mate_lookup = "matching_lookup_arr nil" and mate_partner = matching_partner_arr
    and mate_augment = augment_arr and mate_contract = "contract_path_arr nil"
    and mate_expand = "expand_path_arr nil" and mate_add_alternatingly = add_alternatingly_arr
    and vset_to_list = id
  for nil
  defines ugraph_abs_arr = gma.ugraph_abs
    and graph_input_arr = gma.graph_input
    and matching_invar_arr = gma.matching_invar
    and neighbour_list_arr = gma.neighbour_list
    and adjacency_edges_arr = gma.adjacency_edges
    and graph_inv_lg = gma.Graph.graph_inv
    and neighbourhood_lg = gma.Graph.neighbourhood
    and add_edge_lg = gma.Graph.add_edge
    and from_list_lg = gma.Graph.from_list
    and digraph_abs_lg = gma.Graph.digraph_abs
proof(rule Graph_Matching_Specs.intro)
  show "Pair_Graph_Specs Leaf RBT_Map.delete lookup Cons lset_isin set hd update M.invar
          [] lset_delete (%_. True)"
    using Map_axioms_as_needed lset.Set_Choose_axioms
    by(intro Pair_Graph_Specs.intro Pair_Graph_Specs_Read_Only.intro) simp_all
  show "blossom_matching {..<nil} (%_. nil) (matching_invar_abs_arr nil) (matching_lookup_arr nil)
    matching_partner_arr augment_arr (matching_abs_arr nil) (contract_path_arr nil)
    (expand_path_arr nil) add_alternatingly_arr nil"
    by(rule blossom_matching_arr)
  show "Graph_Matching_Specs_axioms set (%_. True) id"
  by(rule Graph_Matching_Specs_axioms.intro) simp
qed

subsection "The forest"

global_interpretation forest_arr: forest_imp
  where K = "{..<nil}" and parent_invar = "%_. True" and parent_upd = array_fun_upd
    and parent_get = array_fun_lookup and origin_invar = "%_. True" and origin_upd = array_fun_upd
    and origin_get = array_fun_lookup and vset_invar = "%X. X \<subseteq> {..<nil}" and vset_to_set = id
    and vset_empty = "{}" and vset_insert = Set.insert and vset_delete = "%x X. X - {x}"
    and vset_isin = "%X x. x \<in> X" and vset_iterate = fset_iterate
    and parent_empty = "%_. nil" and origin_empty = "%_. nil" and nil = nil
    and vset_assn = "bool_array_set_assn nil" and vset_empty_imp = "Array.new nil False"
    and vset_insert_imp = bool_array_set_insert_imp and vset_delete_imp = bool_array_set_delete_imp
    and vset_isin_imp = bool_array_set_isin_imp and lst = sorted_list_of_set
    and is_it = "bool_array_set_is_it nil" and it_init = bool_array_set_it_init
    and it_has_next = bool_array_set_it_has_next and it_next = bool_array_set_it_next
    and parent_assn = "array_fun_assn nil" and parent_upd_imp = array_fun_upd_imp
    and parent_get_imp = array_fun_lookup_imp
    and vset_clear_imp = "bool_array_set_clear_unit nil"
    and parent_clear_imp = "array_fun_clear_unit nil nil" and parent_empty_imp = "Array.new nil nil"
  for nil
  defines forest_arr_empty = forest_arr.empty_forest
    and forest_arr_extend_fun = forest_arr.extend_forest_even_unclassified
    and forest_arr_path_fun = forest_arr.get_path
    and forest_arr_path_loop_fun = forest_arr.get_path_loop
    and forest_arr_extend = forest_arr.forest_extend_imp
    and forest_arr_evens_memb = forest_arr.evens_memb_imp
    and forest_arr_odds_memb = forest_arr.odds_memb_imp
    and forest_arr_get_path_loop = forest_arr.get_path_imp_loop
    and forest_arr_get_path = forest_arr.get_path_imp
proof(intro forest_imp.intro forest_manipulation.intro forest_manipulation_axioms.intro
    forest_manipulation_spec.intro[OF array_fun_fixed_univ_map array_fun_fixed_univ_map
      set_fixed_univ_set] bool_array_set_fixed_univ_set_imp bool_array_set_fixed_univ_set_iterate_imp
    array_fun_fixed_univ_map_imp bool_array_set_fixed_univ_set_clear_imp
    array_fun_fixed_univ_map_clear_imp array_fun_fixed_univ_map_init_imp, goal_cases)
  case (6 S)
  thus ?case
  by(rule fset_iterate_below)
qed (simp_all add: array_fun_lookup_def)

text "The interface of the blossom algorithm returns a path as an array of its exact length. The
  length is found by following the parents before the path is written."

partial_function (heap) forest_arr_path_length :: "nat \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "forest_arr_path_length nil pai k v = do {
     u \<leftarrow> Array.nth pai v;
     (if u = nil then return (Suc k) else forest_arr_path_length nil pai (Suc k) u) }"

lemma forest_arr_path_length_rule:
  assumes "parent_spec_i.follow_dom (forest_arr.parent_lookup nil P) v"
  shows "set (follow (forest_arr.parent_lookup nil P) v) \<subseteq> {..<nil} \<Longrightarrow>
    <array_fun_assn nil P pai> forest_arr_path_length nil pai k v
    <\<lambda>r. array_fun_assn nil P pai * \<up>(r = k + length (follow (forest_arr.parent_lookup nil P) v))>"
  using assms
proof(induction arbitrary: k rule: parent_spec_i.follow.pinduct)
  case IH: (1 v)
  have v: "v < nil"
    using IH(3)
    by(subst (asm) parent_spec_i.follow.psimps[OF IH(1)]) (auto split: option.splits)
  show ?case
  proof(cases "forest_arr.parent_lookup nil P v")
    case None
    hence "P v = nil" "follow (forest_arr.parent_lookup nil P) v = [v]"
    by(auto simp: parent_spec_i.follow.psimps[OF IH(1)] forest_arr.parent_lookup_def
            array_fun_lookup_def split: if_splits)
    thus ?thesis
      using v
      by(subst forest_arr_path_length.simps) (sep_auto heap: array_fun_lookup_rule)
  next
    case (Some v')
    hence step: "P v = v'" "v' \<noteq> nil"
      "follow (forest_arr.parent_lookup nil P) v = v # follow (forest_arr.parent_lookup nil P) v'"
      by(auto simp: parent_spec_i.follow.psimps[OF IH(1)] forest_arr.parent_lookup_def
        array_fun_lookup_def split: if_splits)
    have rec: "<array_fun_assn nil P pai> forest_arr_path_length nil pai (Suc k) v'
      <\<lambda>r. array_fun_assn nil P pai * \<up>(r = k + length (follow (forest_arr.parent_lookup nil P) v))>"
      using IH(2)[of v' "Suc k"] IH(3) Some
      by(simp add: step(3))
    show ?thesis
      using v step(2)
      by(subst forest_arr_path_length.simps)
         (sep_auto heap: array_fun_lookup_rule rec simp: step(1))
  qed
qed

lemma forest_arr_follow:
  assumes "forest_arr.forest_invar nil M F" "v \<in> evens F"
  shows "parent_spec_i.follow_dom (forest_arr.parent_lookup nil (parents F)) v"
    "set (follow (forest_arr.parent_lookup nil (parents F)) v) \<subseteq> {..<nil}"
    "forest_arr_path_fun nil F v = follow (forest_arr.parent_lookup nil (parents F)) v"
proof-
  note basic = forest_arr.invar_basicD[OF forest_arr.forest_invarD(1)[OF assms(1)]]
  show "parent_spec_i.follow_dom (forest_arr.parent_lookup nil (parents F)) v"
    using assms(1)
    by(intro forest_arr.follow_dom_invar_parent_wf(2)) (auto dest: forest_arr.forest_invarD)
  have "set (follow (forest_arr.parent_lookup nil (parents F)) v) \<subseteq> forest_arr.verts nil F"
    using assms basic(6)
    by(intro forest_arr.path_follow_verts_in_verts_F[of nil M]) (auto dest: forest_arr.forest_invarD)
  moreover have "forest_arr.verts nil F \<subseteq> {..<nil}"
    using basic(2,3,6) forest_arr.vset.fixed_univ_set_universe
    by blast
  ultimately show "set (follow (forest_arr.parent_lookup nil (parents F)) v) \<subseteq> {..<nil}"
    by auto
  show "forest_arr_path_fun nil F v = follow (forest_arr.parent_lookup nil (parents F)) v"
  by(rule forest_arr.get_path_follow[OF assms(1)])
qed

text "The operations of the interface: the forest takes over the Boolean array of its roots as
  the set of its even vertices."

definition "forest_arr_empty_roots nil Ri = do {
  oi \<leftarrow> Array.new nil False;
  pai \<leftarrow> Array.new nil nil;
  return (Ri, oi, pai) }"

definition "forest_arr_evens_isin Fi v = forest_arr_evens_memb v Fi"

definition "forest_arr_odds_isin Fi v = forest_arr_odds_memb v Fi"

definition "forest_arr_extend_unit Fi x y z = do { _ \<leftarrow> forest_arr_extend x y z Fi; return () }"

definition "forest_arr_path nil Fi v = (case Fi of (ei, oi, pai) \<Rightarrow> do {
  k \<leftarrow> forest_arr_path_length nil pai 0 v;
  Ra \<leftarrow> Array.new k 0;
  _ \<leftarrow> forest_arr_get_path nil Fi Ra 0 v;
  return Ra })"

lemma forest_arr_alternating_forest_imp:
  "alternating_forest_imp evens odds roots (forest_arr_path_fun nil) (forest_arr.abstract_forest nil)
     (forest_arr.forest_invar nil) (%X. X \<subseteq> {..<nil}) id forest_arr_extend_fun (forest_arr_empty nil)
     {..<nil} {} (forest_arr.forest_assn nil) (bool_array_set_assn nil) (%p Pt. Pt \<mapsto>\<^sub>a p)
     (forest_arr_empty_roots nil) forest_arr_evens_isin forest_arr_odds_isin forest_arr_extend_unit
     (forest_arr_path nil)"
proof(intro alternating_forest_imp.intro forest_arr.satisified alternating_forest_imp_axioms.intro, goal_cases)
  case (1 R Ri)
  then show ?case
    unfolding forest_arr_empty_roots_def forest_arr.forest_assn_def forest_arr.vs_assn_def
    by(sep_auto heap: bool_array_set_assn_new array_fun_assn_new)
next
  case (2 M F v Fi)
  show ?case
    unfolding forest_arr_evens_isin_def
    by(rule forest_arr.evens_memb_imp_rule[OF 2(2)])
next
  case (3 M F v Fi)
  show ?case
    unfolding forest_arr_odds_isin_def
    by(rule forest_arr.odds_memb_imp_rule[OF 3(2)])
next
  case (4 F M x y z Fi)
  have "forest_arr.forest_extension_precond nil F M x y z"
    using 4(1)
    by(simp add: forest_arr.satisfied_simple_extension_precond_same)
  note K = forest_arr.forest_extension_precond_in_K[OF this]
  show ?case
    using K
    unfolding forest_arr_extend_unit_def forest_arr.forest_extend_imp_def forest_arr.forest_assn_def
      forest_arr.vs_assn_def
    by(sep_auto split: prod.splits simp: forest_arr.vset.fixed_univ_set_insert)
next
  case (5 M F v Fi)
  note follow = forest_arr_follow[OF 5(1) 5(2)[simplified]]
  show ?case
    unfolding forest_arr_path_def forest_arr.forest_assn_def forest_arr.get_path_imp_def follow(3)
    by(sep_auto split: prod.splits heap: forest_arr_path_length_rule[OF follow(1,2)]
          forest_arr.get_path_imp_loop_rule[OF follow(1) TrueI follow(2)])
qed

subsection "The imperative matching"

global_interpretation aug_arr: matching_augmentation_imp
  where K = "{..<nil}" and buddy_invar = "%_. True" and buddy_upd = array_fun_upd
    and buddy_get = array_fun_lookup and buddy_empty = "%_. nil" and nil = nil
    and buddy_assn = "array_fun_assn nil" and buddy_upd_imp = array_fun_upd_imp
    and buddy_get_imp = array_fun_lookup_imp
  for nil
  defines augment_arr_loop = aug_arr.augment_loop
    and augment_arr_imp = aug_arr.augment_imp
  by(intro matching_augmentation_imp.intro Matching_Augmentation_Specs.intro array_fun_fixed_univ_map
        array_fun_fixed_univ_map_imp)

text "The operations of the interface. Contraction frees the vertices of the path and matches the
  new vertex to the partner of the first vertex of the path, as the functional contraction does."

definition "mate_lookup_imp nil Mi v = do {
  u \<leftarrow> Array.nth Mi v;
  return (if u = nil then None else Some u) }"

definition "mate_augment_imp Mi Pt = do { k \<leftarrow> Array.len Pt; augment_arr_imp Mi Pt k }"

definition "mate_clear_imp nil x Mi = do { _ \<leftarrow> Array.upd x nil Mi; return Mi }"

definition "mate_contract_imp nil Mi Pt u = do {
  h \<leftarrow> Array.nth Pt 0;
  v \<leftarrow> Array.nth Mi h;
  k \<leftarrow> Array.len Pt;
  _ \<leftarrow> array_foldl Pt 0 k (mate_clear_imp nil) Mi;
  (if v = nil then return ()
   else do { _ \<leftarrow> Array.upd v u Mi; _ \<leftarrow> Array.upd u v Mi; return () }) }"

lemma mate_value_in_univ:
  "\<lbrakk>matching_invar_abs_arr nil G M; M x \<noteq> nil\<rbrakk> \<Longrightarrow> M x < nil"
  using matching_arr.buddy_get_in_\<M>[of M x nil] matching_arr.invar_matchingD(4,6)[of nil G M]
  by(auto simp: matching_invar_abs_arr_def array_fun_lookup_def Vs_def)

lemma mate_clear_fold_rule:
  "set p \<subseteq> {..<nil} \<Longrightarrow>
   <array_fun_assn nil M Mi * Pt \<mapsto>\<^sub>a p> array_foldl Pt 0 (length p) (mate_clear_imp nil) Mi
   <\<lambda>r. array_fun_assn nil (foldl (%M x. array_fun_upd M x nil) M p) Mi * Pt \<mapsto>\<^sub>a p * \<up>(r = Mi)>"
  using array_foldl_all_rule[of p "%M r. array_fun_assn nil M r * \<up>(r = Mi)" emp "mate_clear_imp nil"
      "%M x. array_fun_upd M x nil" Pt M Mi]
  by(sep_auto simp: mate_clear_imp_def array_fun_upd_def heap: array_fun_upd_rule)

lemma mate_contract_imp_rule:
  assumes "blossom_matching_spec.contract_path_precond {..<nil} (matching_invar_abs_arr nil)
    (matching_abs_arr nil) G M p u contr"
  shows "<array_fun_assn nil M Mi * Pt \<mapsto>\<^sub>a p> mate_contract_imp nil Mi Pt u
    <\<lambda>_. array_fun_assn nil (contract_path_arr nil M p u) Mi * Pt \<mapsto>\<^sub>a p>"
  using assms
  unfolding blossom_matching_spec.contract_path_precond_def mate_contract_imp_def
    matching_arr.contract_path_def matching_arr.contract_path_at_matched_def
  by(sep_auto heap: array_fun_lookup_rule mate_clear_fold_rule array_fun_upd_rule
      simp: array_fun_lookup_def array_fun_upd_def hd_conv_nth
      intro: mate_value_in_univ dest: hd_in_set)

lemma mate_blossom_matching_imp:
  "blossom_matching_imp nil {..<nil} (%_. nil) (matching_invar_abs_arr nil) (matching_lookup_arr nil)
     matching_partner_arr augment_arr (matching_abs_arr nil) (contract_path_arr nil)
     (expand_path_arr nil) add_alternatingly_arr (array_fun_assn nil) (%p Pt. Pt \<mapsto>\<^sub>a p)
     (Array.new nil nil) (mate_lookup_imp nil) mate_augment_imp (mate_contract_imp nil) copy_array_imp"
proof(intro blossom_matching_imp.intro blossom_matching_arr blossom_matching_imp_axioms.intro, goal_cases)
  case (2 G M x Mi)
  thus ?case
    unfolding mate_lookup_imp_def
    by(sep_auto heap: array_fun_lookup_rule simp: matching_arr.buddy_lookup_def array_fun_lookup_def)
next
  case (3 G M p Mi Pti)
  thus ?case
    unfolding mate_augment_imp_def augment_arr_def
    by(sep_auto heap: aug_arr.augment_imp_rule)
next
  case (5 G M Mi)
  show ?case
    unfolding array_fun_assn_def
    by(rule copy_array_imp_rule)
qed (auto intro!: array_fun_assn_new mate_contract_imp_rule)

subsection "The imperative graphs"

text "A graph is an array of the neighbour lists of the vertices in the universe. Adding an edge
  puts the new neighbour in front, as in the functional graph, so the lists may contain duplicates.
  An edge whose source is outside the universe is ignored by the array; the functional graph
  records it, but the algorithm never adds one."

lemma neighbourhood_add_edge_lg:
  "graph_inv_lg H ==> neighbourhood_lg (add_edge_lg H a b) x =
    (if x = a then b # neighbourhood_lg H a else neighbourhood_lg H x)"
  by(cases "lookup H a") (auto simp: gma.Graph.add_edge_def gma.Graph.neighbourhood_def
    gma.Graph.graph_inv_def M.map_update)

definition "graph_arr_assn nil H Gi =
  Gi \<mapsto>\<^sub>a map (neighbourhood_lg H) [0..<nil] * \<up>(graph_inv_lg H)"

definition "graph_arr_add_edge nil Gi a b =
  (if a < nil then do { l <- Array.nth Gi a; Array.upd a (b # l) Gi } else return Gi)"

definition "graph_arr_neighbours Gi v = do { l <- Array.nth Gi v; Array.of_list l }"

definition "graph_arr_isin Gi v w = do { l <- Array.nth Gi v; return (w \<in> set l) }"

lemma graph_arr_empty_rule: "<emp> Array.new nil [] <%Hi. graph_arr_assn nil Leaf Hi>"
  by(sep_auto simp: graph_arr_assn_def gma.Graph.neighbourhood_def[abs_def]
    map_replicate_const gma.Graph.graph_inv_empty)

lemma graph_arr_add_edge_rule:
  "<graph_arr_assn nil H Hi> graph_arr_add_edge nil Hi a b
   <%Hi'. graph_arr_assn nil (add_edge_lg H a b) Hi'>"
proof(cases "graph_inv_lg H")
  case True
  have "map (neighbourhood_lg (add_edge_lg H a b)) [0..<nil] =
    (if a < nil then list_update (map (neighbourhood_lg H) [0..<nil]) a (b # neighbourhood_lg H a)
     else map (neighbourhood_lg H) [0..<nil])"
    by(rule nth_equalityI) (auto simp: neighbourhood_add_edge_lg True nth_list_update)
  thus ?thesis
    unfolding graph_arr_add_edge_def graph_arr_assn_def
    using True gma.Graph.adjmap_inv_insert[of H a b]
    by sep_auto
qed (simp add: graph_arr_assn_def)

lemma graph_arr_neighbours_rule:
  "v < nil ==> <graph_arr_assn nil H Gi> graph_arr_neighbours Gi v
   <%A. graph_arr_assn nil H Gi * A \<mapsto>\<^sub>a neighbour_list_arr H v>"
  unfolding graph_arr_neighbours_def graph_arr_assn_def
  by(sep_auto simp: gma.neighbour_list_def)

lemma graph_arr_isin_rule:
  "v < nil ==> <graph_arr_assn nil H Gi> graph_arr_isin Gi v w
   <%r. graph_arr_assn nil H Gi * \<up>(r = lset_isin (neighbourhood_lg H v) w)>"
  unfolding graph_arr_isin_def graph_arr_assn_def
  by(sep_auto simp: lset_isin_def)

subsection "Fresh vertices"

text "A fresh vertex is the smallest number that is not in the array of the current vertices,
  as for the functional algorithm. The vertices below the length of the array are marked in a
  Boolean array, whose first unmarked position is the fresh vertex."

definition "fresh_mark_imp x Bi = do {
  l \<leftarrow> Array.len Bi;
  (if x < l then do { _ \<leftarrow> Array.upd x True Bi; return Bi } else return Bi) }"

definition "fresh_vert_imp Wi = do {
  k \<leftarrow> Array.len Wi;
  Bi \<leftarrow> Array.new (Suc k) False;
  Bi \<leftarrow> array_foldl Wi 0 k fresh_mark_imp Bi;
  first_pos_imp (%b. return (\<not> b)) Bi (Suc k) 0 }"

lemma first_pos_map: "first_pos P (map f xs) = first_pos (%x. P (f x)) xs"
  by(induction xs) auto

lemma first_pos_cong: "(\<And>x. x \<in> set xs \<Longrightarrow> P x = Q x) \<Longrightarrow> first_pos P xs = first_pos Q xs"
  by(induction xs) auto

lemma fresh_nat_first_pos: "fresh_nat ws = first_pos (%n. n \<notin> set ws) [0..<Suc (length ws)]"
  using fresh_nat_exists[of ws] first_pos_less_iff[of "\<lambda>n. n \<notin> set ws" "[0..<Suc (length ws)]"]
  by(auto simp: fresh_nat_def find_first_pos simp del: upt_Suc)

lemma fresh_mark_fold:
  "foldl (%S x. if x < n then Set.insert x S else S) S0 ws = S0 \<union> (set ws \<inter> {..<n})"
  by(induction ws arbitrary: S0) auto

lemma fresh_mark_imp_rule:
  "<Bi \<mapsto>\<^sub>a map (%i. i \<in> S) [0..<n] * \<up>(Bi = Bo) * emp> fresh_mark_imp x Bi
   <\<lambda>r. r \<mapsto>\<^sub>a map (%i. i \<in> (if x < n then Set.insert x S else S)) [0..<n] * \<up>(r = Bo) * emp>"
  unfolding fresh_mark_imp_def
  by(sep_auto simp: map_mem_update)

lemma fresh_vert_imp_rule: "<Wi \<mapsto>\<^sub>a ws> fresh_vert_imp Wi <\<lambda>u. Wi \<mapsto>\<^sub>a ws * \<up>(u = fresh_nat ws)>"
proof-
  let ?n = "Suc (length ws)"
  let ?bs = "map (\<lambda>i. i \<in> set ws \<inter> {..<?n}) [0..<?n]"
  have fold: "<Wi \<mapsto>\<^sub>a ws * (Bi \<mapsto>\<^sub>a replicate ?n False * \<up>(Bi = Bi)) * emp>
    array_foldl Wi 0 (length ws) fresh_mark_imp Bi
    <\<lambda>r. Wi \<mapsto>\<^sub>a ws * (r \<mapsto>\<^sub>a ?bs * \<up>(r = Bi)) * emp>" for Bi
    using array_foldl_all_rule[of ws "\<lambda>S r. r \<mapsto>\<^sub>a map (\<lambda>i. i \<in> S) [0..<?n] * \<up>(r = Bi)" emp
        fresh_mark_imp "\<lambda>S x. if x < ?n then Set.insert x S else S" Wi "{}" Bi] fresh_mark_imp_rule
    by(simp only: fresh_mark_fold Un_empty_left empty_iff map_replicate_const length_upt diff_zero)
  have "first_pos Not ?bs = fresh_nat ws"
    unfolding fresh_nat_first_pos first_pos_map
    by(rule first_pos_cong) (auto simp del: upt_Suc)
  then have find: "<Bi \<mapsto>\<^sub>a ?bs * Wi \<mapsto>\<^sub>a ws> first_pos_imp (\<lambda>b. return (\<not> b)) Bi ?n 0
    <\<lambda>r. Bi \<mapsto>\<^sub>a ?bs * Wi \<mapsto>\<^sub>a ws * \<up>(r = fresh_nat ws)>" for Bi
    using first_pos_imp_rule[of 0 ?bs "Wi \<mapsto>\<^sub>a ws" "\<lambda>b. return (\<not> b)" Not Bi]
    by(sep_auto)
  show ?thesis
    unfolding fresh_vert_imp_def
    by(sep_auto heap: fold find)
qed

subsection "The programs"

text "The global interpretations of the code locales of the imperative blossom algorithm, whose
  assumptions do not depend on the input. The queue of the forest search is an array stack of
  capacity 2 * nil, the stack of contractions one of capacity nil, whose unused cells hold the
  dummy entry dflt."

global_interpretation obi_cap: Compute_Alt_Path_Imperative_spec
  where stack_empty_imp = "ars_empty_imp (2 * nil) 0" and stack_push_imp = ars_push_imp
    and stack_pop_imp = ars_pop_imp and stack_top_imp = ars_top_imp
    and stack_is_empty_imp = ars_is_empty_imp
    and fset_empty_imp = "Array.new nil False" and fset_insert_imp = bool_array_set_insert_imp
    and empty_forest_imp = "forest_arr_empty_roots nil" and evens_isin_imp = forest_arr_evens_isin
    and odds_isin_imp = forest_arr_odds_isin
    and extend_forest_even_unclassified_imp = forest_arr_extend_unit
    and get_path_imp = "forest_arr_path nil" and lookup_partner_imp = "mate_lookup_imp nil"
    and neighbours_imp = graph_arr_neighbours and dummy_vert = 0
  for nil
  defines obi_cap_loop = obi_cap.Compute_Alt_Path_imp
    and obi_is_free = obi_cap.is_free_imp
    and obi_insert_if_free = obi_cap.insert_if_free_imp
    and obi_push_if_free = obi_cap.push_if_free_imp
    and obi_cap_init = obi_cap.initial_state_imp
    and obi_alt_paths = obi_cap.alternating_paths_imp
    and obi_cap_run = obi_cap.Compute_Alt_Path_run_imp
  .

global_interpretation obi_fsub: Find_Aug_Path_Subprocedures_Imperative_spec "obi_cap_run nil"
  for nil
  defines obi_match_blossom = obi_fsub.compute_match_blossom_imp
  .

global_interpretation obi_fap: Find_Aug_Path_Imperative_spec
  where blos_search_imp = "obi_match_blossom nil" and create_vert_imp = fresh_vert_imp
    and g_empty_imp = "Array.new nil []" and g_add_edge_imp = "graph_arr_add_edge nil"
    and neighbours_imp = graph_arr_neighbours and g_isin_imp = graph_arr_isin
    and lookup_partner_imp = "mate_lookup_imp nil" and copy_matching_imp = copy_array_imp
    and contract_path_imp = "mate_contract_imp nil"
    and stack_empty_imp = "ars_empty_imp nil dflt" and stack_push_imp = ars_push_imp
    and stack_pop_imp = ars_pop_imp and stack_top_imp = ars_top_imp
    and stack_is_empty_imp = ars_is_empty_imp
  for nil dflt
  defines obi_contract_nbs = obi_fap.contract_nbs_imp
    and obi_contract_edges = obi_fap.contract_edges_imp
    and obi_contract_graph = obi_fap.contract_graph_imp
    and obi_contract_matching = obi_fap.contract_matching_imp
    and obi_fap_loop = obi_fap.Find_Aug_Path_imp
    and obi_lift_path = obi_fap.lift_path_imp
    and obi_fap_init = obi_fap.initial_state_imp
    and obi_aug_path = obi_fap.augmenting_path_imp
    and obi_fap_run = obi_fap.Find_Aug_Path_run_imp
  .

global_interpretation obi_fmm: Find_Max_Matching_Imperative_spec "obi_fap_run nil dflt"
    "Array.new nil nil" mate_augment_imp
  for nil dflt
  defines obi_fmm_loop = obi_fmm.Find_Max_Matching_imp
    and obi_fmm_run = obi_fmm.Find_Max_Matching_run_imp
  .

declare obi_fmm.Find_Max_Matching_imp.simps[code] obi_fap.Find_Aug_Path_imp.simps[code]
  obi_fap.lift_path_imp.simps[code] obi_fap.contract_nbs_imp.simps[code]
  obi_fap.contract_edges_imp.simps[code] obi_cap.Compute_Alt_Path_imp.simps[code]
  forest_arr.get_path_imp_loop.simps[code] forest_arr_path_length.simps[code]
  aug_arr.augment_loop.simps[code] common_tail_imp.simps[code] copy_rev_imp.simps[code]
  copy_fwd_imp.simps[code] first_pos_imp.simps[code] count_outside_imp.simps[code]
  copy_outside_imp.simps[code] array_foldr.simps[code] array_foldl.simps[code]

subsection "Correctness"

text "For every input, the data structures above instantiate the locale of the imperative blossom
  algorithm, whose program is the one of the global interpretations."

locale obi_input =
  fixes nil :: nat and dflt :: "nat list array \<times> nat array \<times> nat array \<times> nat"
    and G and vs :: "nat list"
  assumes input: "graph_input_arr nil G vs" and strict: "set vs \<subset> {..<nil}"
    and len: "length vs \<le> nil"

sublocale obi_input \<subseteq> EBI: Edmonds_Blossom_Imperative
  where empty = Leaf and delete = RBT_Map.delete and lookup = lookup and insert = Cons
    and isin = lset_isin and t_set = set and sel = hd and update = update and adjmap_inv = M.invar
    and vset_empty = "[]" and vset_delete = lset_delete and vset_inv = "%_. True"
    and K = "{..<nil}" and nil = nil and mate_empty = "%_. nil"
    and matching_invar_abs = "matching_invar_abs_arr nil" and matching_abs = "matching_abs_arr nil"
    and mate_lookup = "matching_lookup_arr nil" and mate_partner = matching_partner_arr
    and mate_augment = augment_arr and mate_contract = "contract_path_arr nil"
    and mate_expand = "expand_path_arr nil" and mate_add_alternatingly = add_alternatingly_arr
    and vset_to_list = id and matching_assn = "array_fun_assn nil"
    and fset_invar = "%X. X \<subseteq> {..<nil}" and fset_to_set = id and fset_empty = "{}"
    and fset_insert = Set.insert and fset_delete = "%x X. X - {x}" and fset_isin = "%X x. x \<in> X"
    and fset_assn = "bool_array_set_assn nil" and fset_empty_imp = "Array.new nil False"
    and fset_insert_imp = bool_array_set_insert_imp and fset_delete_imp = bool_array_set_delete_imp
    and fset_isin_imp = bool_array_set_isin_imp
    and evens = evens and odds = odds and roots = roots and get_path = "forest_arr_path_fun nil"
    and abstract_forest = "forest_arr.abstract_forest nil"
    and forest_invar = "forest_arr.forest_invar nil"
    and extend_forest_even_unclassified = forest_arr_extend_fun
    and empty_forest = "forest_arr_empty nil"
    and forest_assn = "forest_arr.forest_assn nil" and empty_forest_imp = "forest_arr_empty_roots nil"
    and evens_isin_imp = forest_arr_evens_isin and odds_isin_imp = forest_arr_odds_isin
    and extend_forest_even_unclassified_imp = forest_arr_extend_unit
    and get_path_imp = "forest_arr_path nil"
    and empty_matching_imp = "Array.new nil nil" and lookup_partner_imp = "mate_lookup_imp nil"
    and augment_imp = mate_augment_imp and contract_path_imp = "mate_contract_imp nil"
    and copy_matching_imp = copy_array_imp
    and q_cap = "2 * nil" and q_invar = "ars_invar (2 * nil)" and q_abstract = ars_abstract
    and q_empty = "ars_empty (2 * nil) 0" and q_push = ars_push and q_pop = ars_pop
    and q_top = ars_top and q_is_empty = ars_is_empty and q_assn = ars_assn
    and q_empty_imp = "ars_empty_imp (2 * nil) 0" and q_push_imp = ars_push_imp
    and q_pop_imp = ars_pop_imp and q_top_imp = ars_top_imp and q_is_empty_imp = ars_is_empty_imp
    and cs_cap = nil and cs_invar = "ars_invar nil" and cs_abstract = ars_abstract
    and cs_empty = "ars_empty nil dflt" and cs_push = ars_push and cs_pop = ars_pop
    and cs_top = ars_top and cs_is_empty = ars_is_empty and cs_assn = ars_assn
    and cs_empty_imp = "ars_empty_imp nil dflt" and cs_push_imp = ars_push_imp
    and cs_pop_imp = ars_pop_imp and cs_top_imp = ars_top_imp and cs_is_empty_imp = ars_is_empty_imp
    and graph_assn = "graph_arr_assn nil" and g_empty_imp = "Array.new nil []"
    and g_add_edge_imp = "graph_arr_add_edge nil" and neighbours_imp = graph_arr_neighbours
    and g_isin_imp = graph_arr_isin and create_vert = fresh_nat and create_vert_imp = fresh_vert_imp
    and G = G and vs = vs and dummy_vert = 0
proof(intro_locales, goal_cases)
  case 9
  show ?case
  proof(unfold_locales, goal_cases)
    case 1
    show ?case
    by(rule graph_arr_empty_rule)
  next
    case (2 H Hi a b)
    show ?case
    by(rule graph_arr_add_edge_rule[unfolded add_edge_lg_def])
  next
    case (3 H Gi v)
    thus ?case
    by(intro graph_arr_neighbours_rule[unfolded neighbour_list_arr_def]) simp
  next
    case (4 H Gi v w)
    thus ?case
    by(intro graph_arr_isin_rule[unfolded neighbourhood_lg_def]) simp
  next
    case (5 ws)
    thus ?case
    by(rule fresh_nat_in_univ(1))
  next
    case (6 ws)
    thus ?case
      using fresh_nat_in_univ(2)[of ws nil]
      by(simp add: lessThan_def)
  next
    case (7 ws Wi)
    show ?case
    by(rule fresh_vert_imp_rule)
  next
    case 8
    show ?case
    by(rule input[unfolded graph_input_arr_def])
  next
    case 9
    show ?case
    by(rule strict)
  next
    case 10
    show ?case
      using len
      by simp
  next
    case 11
    show ?case
    by(rule len)
  qed
qed((insert forest_arr_alternating_forest_imp[of nil] mate_blossom_matching_imp[of nil]
    ars_bounded_stack_imp[of "2 * nil" 0] ars_bounded_stack_imp[of nil dflt];
  auto simp: alternating_forest_imp_def alternating_forest_ordinary_extension_spec_def
    blossom_matching_imp_def bounded_stack_imp_def)+)

lemma (in obi_input) obi_run_eq: "EBI.edmonds_blossom_imp = obi_fmm_run nil dflt"
  by(simp only: EBI.edmonds_blossom_imp_def[abs_def] obi_fmm_run_def obi_fap_run_def
    obi_match_blossom_def obi_cap_run_def)

lemma (in obi_input) obi_fmm_run_correct:
  "<graph_arr_assn nil G Gi * Vi \<mapsto>\<^sub>a vs> obi_fmm_run nil dflt Gi Vi
   <\<lambda>Mi. \<exists>\<^sub>A M. graph_arr_assn nil G Gi * Vi \<mapsto>\<^sub>a vs * array_fun_assn nil M Mi *
        \<up>(max_card_matching (ugraph_abs_arr G) (matching_abs_arr nil M)) * true>"
  by(rule ht_cons_post[OF EBI.edmonds_blossom_imp_correct[unfolded obi_run_eq]])
     (sep_auto simp: ugraph_abs_arr_def)

section "The pipeline from endpoint arrays"

text "The input is the number n of vertices and the arrays of the tails and of the heads of the
  edges, as for quadratic_max_matching. The graph is built by adding every edge in both directions,
  the vertices are 0, ..., n - 1, and the sentinel is n + 1. The dummy entry of the stack of
  contractions is allocated once. The result is the mate array of size n + 1, where n + 1 marks a
  free vertex."

partial_function (heap) obi_build_loop ::
  "nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list array \<Rightarrow> nat list array Heap" where
  "obi_build_loop nil Ta Ha m i Gi =
     (if i < m then do {
        t \<leftarrow> Array.nth Ta i;
        h \<leftarrow> Array.nth Ha i;
        Gi \<leftarrow> graph_arr_add_edge nil Gi t h;
        Gi \<leftarrow> graph_arr_add_edge nil Gi h t;
        obi_build_loop nil Ta Ha m (Suc i) Gi }
      else return Gi)"

declare obi_build_loop.simps[code]

definition "obi_max_matching n Ta Ha = do {
  m \<leftarrow> Array.len Ta;
  Gi \<leftarrow> Array.new (Suc n) [];
  Gi \<leftarrow> obi_build_loop (Suc n) Ta Ha m 0 Gi;
  Vi \<leftarrow> Array.make n id;
  g0 \<leftarrow> Array.new 0 [];
  m0 \<leftarrow> Array.new 0 0;
  c0 \<leftarrow> Array.new 0 0;
  obi_fmm_run (Suc n) (g0, m0, c0, 0) Gi Vi }"

definition "obi_edges tails heads i =
  concat (map (%j. [(tails ! j, heads ! j), (heads ! j, tails ! j)]) [0..<i])"

lemma obi_build_loop_rule:
  assumes "length heads = length tails" "i \<le> length tails"
  shows "<Ta \<mapsto>\<^sub>a tails * Ha \<mapsto>\<^sub>a heads * graph_arr_assn nil (from_list_lg (obi_edges tails heads i)) Gi>
    obi_build_loop nil Ta Ha (length tails) i Gi
    <%Gi'. Ta \<mapsto>\<^sub>a tails * Ha \<mapsto>\<^sub>a heads *
      graph_arr_assn nil (from_list_lg (obi_edges tails heads (length tails))) Gi'>"
  using assms(2)
proof(induction "length tails - i" arbitrary: i Gi)
  case 0
  thus ?case
  by(subst obi_build_loop.simps) sep_auto
next
  case (Suc k)
  have "add_edge_lg (add_edge_lg (from_list_lg (obi_edges tails heads i)) (tails ! i) (heads ! i))
      (heads ! i) (tails ! i) = from_list_lg (obi_edges tails heads (Suc i))"
    by(simp add: obi_edges_def gma.Graph.from_list_def)
  thus ?case
    using Suc assms(1)
    by(subst obi_build_loop.simps) (sep_auto heap: graph_arr_add_edge_rule Suc(1))
qed

lemma set_obi_edges:
  "set (obi_edges tails heads i) =
    {(tails ! j, heads ! j) | j. j < i} \<union> {(heads ! j, tails ! j) | j. j < i}"
  by(auto simp: obi_edges_def)

lemma obi_graph_input:
  assumes "length heads = length tails" "!!i. i < length tails ==> tails ! i < n"
    "!!i. i < length tails ==> heads ! i < n" "!!i. i < length tails ==> tails ! i \<noteq> heads ! i"
  shows "graph_input_arr (Suc n) (from_list_lg (obi_edges tails heads (length tails))) [0..<n]"
    "ugraph_abs_arr (from_list_lg (obi_edges tails heads (length tails))) =
       {{tails ! i, heads ! i} |i. i < length tails}"
  using assms gma.Graph.from_list_correct(2)
  by(auto simp: gma.graph_input_def gma.ugraph_abs_def set_obi_edges dVs_def insert_commute
      dest: assms(4))

text "The returned mate array represents a maximum-cardinality matching of the input graph."

theorem obi_max_matching_rule:
  assumes "length heads = length tails" "!!i. i < length tails ==> tails ! i < n"
    "!!i. i < length tails ==> heads ! i < n" "!!i. i < length tails ==> tails ! i \<noteq> heads ! i"
  shows "<Ta \<mapsto>\<^sub>a tails * Ha \<mapsto>\<^sub>a heads> obi_max_matching n Ta Ha
    <%Ma. Ta \<mapsto>\<^sub>a tails * Ha \<mapsto>\<^sub>a heads * (\<exists>\<^sub>AM. array_fun_assn (Suc n) M Ma *
      \<up>(max_card_matching {{tails ! i, heads ! i} |i. i < length tails} (matching_abs_arr (Suc n) M))) *
      true>"
proof-
  have inst: "obi_input (Suc n) (from_list_lg (obi_edges tails heads (length tails))) [0..<n]"
    using assms
    by(intro obi_input.intro obi_graph_input(1))
      (simp_all add: atLeast0LessThan lessThan_Suc psubset_insert_iff)
  have abs: "ugraph_abs_arr (from_list_lg (obi_edges tails heads (length tails))) =
    {{tails ! i, heads ! i} |i. i < length tails}"
    using assms
    by(rule obi_graph_input(2))
  have empty: "graph_arr_assn (Suc n) Leaf Gi =
    graph_arr_assn (Suc n) (from_list_lg (obi_edges tails heads 0)) Gi" for Gi
    by(simp add: obi_edges_def gma.Graph.from_list_def)
  show ?thesis
    unfolding obi_max_matching_def
    using assms(1)
    by(sep_auto heap: graph_arr_empty_rule obi_build_loop_rule obi_input.obi_fmm_run_correct[OF inst]
      simp: empty abs)
qed

end
