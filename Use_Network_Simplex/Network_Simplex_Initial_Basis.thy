theory Network_Simplex_Initial_Basis
  imports Network_Simplex_Initial_Basis_Code
begin

text \<open>Proof layer of the list instantiation: it imports the single code theory
      \<open>Network_Simplex_Initial_Basis_Code\<close> (all executable definitions) and adds the
      cost-flow-network and acyclic-flow-instance interpretations, the eleven well-formedness
      assumptions, the proof-only constants (bigM, sized, dfs\_sized, is\_free) and every lemma.\<close>

locale initial_basis_lists =
  initial_basis_code_spec where capacity_list = capacity_list +
  real_embedding where h = "h :: 'n ⇒ real"
  for capacity_list :: "('n :: linordered_idom) list" and h :: "'n ⇒ real" +
  assumes length_edges: "length capacity_list = m"
      and length_cost: "length cost_list = length capacity_list"
      and length_fst:  "length fst_list  = length capacity_list"
      and length_snd:  "length snd_list  = length capacity_list"
      and length_flow: "length flow_list = length capacity_list"      and length_b:    "length b_list    = n"
      and cap_neg:     "∀ c ∈ set capacity_list. 0 ≤ c ∨ c = - 1"
      and edges_in_range: "set fst_list ∪ set snd_list ⊆ {1..n}"
      and num_edges_gtr_0: "m > 0"
      and isolated_zero: "⋀i. i < n ⟹ Suc i ∉ set fst_list ∪ set snd_list ⟹ b_list ! i = 0"
begin

text ‹With the dense vertex model the vertex list is no longer an input: @{term vs_list} is the range
      @{term ‹[Suc 0..<Suc n]›} (materialised in the code locale), so distinctness, the absence of the
      null name @{term 0}, and the containment of every edge endpoint in @{term ‹set vs_list›} are all
      facts, not assumptions.  They keep their old names so downstream proofs are unaffected.›

lemma no_zero_node: "0 ∉ set vs_list" by (rule zero_notin_vs_list)
lemma distinct_vs_list: "distinct vs_list" by (rule distinct_vs_list_code)
lemma fst_snd_vs: "set fst_list ∪ set snd_list ⊆ set vs_list"
  using edges_in_range by (simp add: set_vs_list)


text ‹We read the lists as a cost-flow network.  The genuine edges are the indices @{term ‹{0..<m}›};
      for such an edge the endpoints, cost and capacity are looked up in the parallel lists, a capacity
      of @{term ‹- 1›} being decoded as an infinite (@{term \<infinity>}) capacity.  The edge constructor
      @{term create_edge}, however, must return an edge for \<^emph>‹every› pair of endpoints, so it maps a
      pair to @{term ‹m + prod_encode (u, v)›}, an index beyond the input range; the tail and head of
      such a synthetic edge are recovered through @{term prod_decode}, and its capacity is set to
      @{term \<infinity>}.  Discharging the multigraph and non-negativity axioms this way makes the context an
      instance of @{locale cost_flow_network}, and hence of @{locale cost_flow_spec}.›

sublocale original_network: cost_flow_network
  where ℰ           = "{0..<m}"
    and fst          = "\<lambda> e. if e < m then fst_list ! e else Product_Type.fst (prod_decode (e - m))"
    and snd          = "\<lambda> e. if e < m then snd_list ! e else Product_Type.snd (prod_decode (e - m))"
    and create_edge  = "\<lambda> u v. m + prod_encode (u, v)"    and 𝗎           = "λ e. if e < m then (if capacity_list ! e = - 1 then ∞ else ereal (h (capacity_list ! e))) else ∞"
    and 𝖼           = "λ e. h (cost_list ! e)"
proof(unfold_locales, goal_cases)
  case (1 x y)
  show ?case by simp
next
  case (2 x y)
  show ?case by simp
next
  case 3
  show ?case by simp
next
  case 4
  show ?case using num_edges_gtr_0 by simp
next
  case (5 e)
  show ?case
  proof(cases "e < m")
    case True
    hence "capacity_list ! e \<in> set capacity_list"
      by (metis length_edges nth_mem)
    thus ?thesis using cap_neg True by (auto simp add: zero_ereal_def)
  next
    case False
    thus ?thesis by simp
  qed
qed

lemma length_foldl_list_update:
  "length (foldl (\<lambda> arr (v, x). arr[v := x]) init ps) = length init"
  by (induct ps arbitrary: init) auto

lemma length_b_arr: "length b_arr = Suc vcount"
  by (simp add: b_arr_def length_foldl_list_update)

lemma le_foldr_max: "x \<in> set xs \<Longrightarrow> x \<le> foldr max xs (0::nat)"
proof (induct xs)
  case Nil then show ?case by simp
next
  case (Cons a xs)
  from Cons.prems have "x = a \<or> x \<in> set xs" by simp
  then show ?case
  proof
    assume "x = a" thus ?thesis by (simp add: max.cobounded1)
  next
    assume "x \<in> set xs"
    hence "x \<le> foldr max xs 0" using Cons.hyps by blast
    thus ?thesis by (simp add: max.coboundedI2)
  qed
qed

lemma vs_less_vcount: "v ∈ set vs_list ⟹ v < vcount"
  using le_foldr_max[of _ vs_list] by (simp add: vcount_foldr less_Suc_eq_le)

text ‹The balance of the artificial root.  Every name scattered into ‹b_arr› comes from
      vs_list and is therefore smaller than vcount, so the last slot keeps the 0 it was initialised
      with.  The augmented network of the initial basis needs exactly this: the root neither supplies
      nor demands, and the artificial edges carry as much flow into it as out of it.›

lemma foldl_scatter_miss:
  assumes "⋀v x. (v, x) ∈ set ps ⟹ v ≠ k"
  shows "foldl (λ arr (v, x). arr[v := x]) init ps ! k = init ! k"
  using assms
proof (induct ps arbitrary: init)
  case Nil
  show ?case by simp
next
  case (Cons p ps)
  obtain v x where p: "p = (v, x)" by (cases p)
  have vn: "v ≠ k" using Cons.prems p by auto
  have pr: "⋀v' x'. (v', x') ∈ set ps ⟹ v' ≠ k" using Cons.prems by auto
  show ?case using Cons.hyps[OF pr] vn by (simp add: p)
qed

lemma b_lookup_root: "b_lookup vcount = 0"
proof -
  have "⋀v x. (v, x) ∈ set (zip vs_list b_list) ⟹ v ≠ vcount"
    using vs_less_vcount by (auto dest: set_zip_leftD)
  hence "b_arr ! vcount = replicate (Suc vcount) (0::'n) ! vcount"
    unfolding b_arr_def by (rule foldl_scatter_miss)
  moreover have "replicate (Suc vcount) (0::'n) ! vcount = 0" by (rule nth_replicate) simp
  ultimately show ?thesis by (simp add: b_lookup_def)
qed

lemma fst_list_nth_vertex: "e < m ⟹ fst_list ! e ∈ set vs_list"
  using fst_snd_vs length_fst length_edges by (metis UnI1 nth_mem subsetD)

lemma snd_list_nth_vertex: "e < m ⟹ snd_list ! e ∈ set vs_list"
  using fst_snd_vs length_snd length_edges by (metis UnI2 nth_mem subsetD)

lemma keys_fst_lt: "\<forall>e\<in>set [0..<m]. fst_list ! e < vcount"
  using fst_list_nth_vertex vs_less_vcount by auto

lemma keys_snd_lt: "\<forall>e\<in>set [0..<m]. snd_list ! e < vcount"
  using snd_list_nth_vertex vs_less_vcount by auto

lemma V_lt_vcount:
  assumes "v \<in> original_network.\<V>"
  shows "v < vcount"
proof (rule vs_less_vcount)
  from assms obtain a b where ab: "(a, b) \<in> original_network.make_pair ` {0..<m}" "v \<in> {a, b}"
    by (auto simp: dVs_def)
  from ab(1) obtain e where e: "e < m" and me: "original_network.make_pair e = (a, b)" by auto
  have "a = fst_list ! e" and "b = snd_list ! e"
    using e me by (auto simp: original_network.make_pair_def)
  thus "v \<in> set vs_list"
    using ab(2) fst_list_nth_vertex[OF e] snd_list_nth_vertex[OF e] by auto
qed

text ‹An endpoint of some edge really is a vertex of the network.  Under the dense model this is the
      right converse of @{thm V_lt_vcount}: not every name in @{term vs_list} is a vertex any more
      (the edge-less ones are not), only the endpoints are.›

lemma edged_in_V:
  assumes "v ∈ set fst_list ∪ set snd_list"
  shows "v ∈ original_network.𝒱"
proof -
  from assms consider (f) "v ∈ set fst_list" | (s) "v ∈ set snd_list" by blast
  thus ?thesis
  proof cases
    case f
    then obtain e where e0: "e < length fst_list" and ve: "fst_list ! e = v"
      by (auto simp: in_set_conv_nth)
    have e: "e < m" using e0 length_fst length_edges by simp
    have "(v, snd_list ! e) ∈ original_network.make_pair ` {0..<m}"
      using e ve by (force simp: original_network.make_pair_def)
    thus ?thesis by (rule dVsI(1))
  next
    case s
    then obtain e where e0: "e < length snd_list" and ve: "snd_list ! e = v"
      by (auto simp: in_set_conv_nth)
    have e: "e < m" using e0 length_snd length_edges by simp
    have "(fst_list ! e, v) ∈ original_network.make_pair ` {0..<m}"
      using e ve by (force simp: original_network.make_pair_def)
    thus ?thesis by (rule dVsI(2))
  qed
qed

lemma fold_prod_fst: "fst (fold (λe (a,b). (f e a, g e b)) es (a0,b0)) = fold f es a0"
  by (induct es arbitrary: a0 b0) auto

lemma fold_prod_snd: "snd (fold (λe (a,b). (f e a, g e b)) es (a0,b0)) = fold g es b0"
  by (induct es arbitrary: a0 b0) auto

lemma build_two_csr_fst: "fst (build_two_csr nn k1 k2 es dflt) = build_csr_scatter nn k1 es dflt"
  by (simp add: build_two_csr_def build_csr_scatter_def Let_def fold_prod_fst ct_def)

lemma build_two_csr_snd: "snd (build_two_csr nn k1 k2 es dflt) = build_csr_scatter nn k2 es dflt"
  by (simp add: build_two_csr_def build_csr_scatter_def Let_def fold_prod_snd ct_def)

lemma out_csr_eq: "out_csr = build_csr_scatter vcount (nth fst_list) [0..<m] 0"
  by (simp add: out_csr_def two_csr_def build_two_csr_fst)

lemma in_csr_eq: "in_csr = build_csr_scatter vcount (nth snd_list) [0..<m] 0"
  by (simp add: in_csr_def two_csr_def build_two_csr_snd)

text ‹The acyclic-flow procedure is now an instance.  The two edge iterators are the counting-sort
      CSRs @{const build_csr_scatter} keyed on tail resp.\ head; the flow and vertex-state arrays are
      plain lists read with @{const nth} and written with @{const list_update} (‹xs[k := v]›);
      the vertex iterator is the vertex list with a
      cursor; ‹fst_exec› / ‹snd_exec› are the ‹O(1)› tail / head array reads; and
      the program capacity ‹cap› decodes the @{term ‹- 1›} sentinel as an infinite capacity.›

sublocale acyclic_flow_impl
  where fst = "\<lambda> e. if e < m then fst_list ! e else Product_Type.fst (prod_decode (e - m))"
    and snd = "\<lambda> e. if e < m then snd_list ! e else Product_Type.snd (prod_decode (e - m))"
    and \<E> = "{0..<m}"
    and create_edge = "\<lambda> u v. m + prod_encode (u, v)"    and 𝗎 = "λ e. if e < m then (if capacity_list ! e = - 1 then ∞ else ereal (h (capacity_list ! e))) else ∞"
    and 𝖼 = "λ e. h (cost_list ! e)"
    and out_invar = csr_invar and out_abstract = csr_abstract and out_current = csr_current
    and out_has = csr_has and out_iterated = csr_iterated and out_remaining = csr_remaining
    and out_move = csr_move and out_reset = csr_reset
    and in_invar = csr_invar and in_abstract = csr_abstract and in_current = csr_current
    and in_has = csr_has and in_iterated = csr_iterated and in_remaining = csr_remaining
    and in_move = csr_move and in_reset = csr_reset
    and flow_invar = "λxs. length xs = m" and flow_upd = list_update and flow_lookup = nth
    and st_invar = "\<lambda>xs. \<forall>v\<in>original_network.\<V>. v < length xs" and st_upd = list_update and st_lookup = nth
    and vit_invar = vtx_invar and vit_abstract = vtx_abstract and current_vertex = vtx_current
    and has_vertex = vtx_has and vit_iterated = vtx_iterated and vit_remaining = vtx_remaining
    and move_on_vertex = vtx_move
    and out_arr = out_csr
    and in_arr = in_csr    and all_vertices = "⦇ vi_list = edged_vs_list, vi_pos = 0 ⦈"    and cap = "λ e.  capacity_list ! e "
    and cost = "λ e. cost_list ! e"
    and h = "h :: 'n ⇒ real"
    and state_init = "replicate vcount Unseen"
    and fst_exec = "λ e. fst_list ! e"
    and snd_exec = "λ e. snd_list ! e"
  apply (rule acyclic_flow_impl.intro)
  apply (all ‹(rule csr_outgoing_edge_iterator csr_ingoing_edge_iterator
                    list_abstract_array list_abstract_array_len vtx_iterable_set)?›)
  apply unfold_locales
  using V_lt_vcount apply auto
  done

lemma length_out_lo: "length out_lo = vcount"
  unfolding out_lo_def by (simp add: out_csr_eq psums_length)

lemma length_in_lo: "length in_lo = vcount"
  unfolding in_lo_def by (simp add: in_csr_eq psums_length)

subsection ‹The CSR arrays are a faithful multigraph›

text ‹The two CSR arrays built by @{const build_two_csr} really do represent the outgoing / ingoing
      incidences: every key is a genuine vertex (@{thm keys_fst_lt} / @{thm keys_snd_lt}), so the
      scatter build coincides with the reference @{const build_csr} and its abstraction is exactly
      @{const original_network.delta_plus} / @{const original_network.delta_minus}.  This discharges the standing @{term ‹multigraph_inv
      out_csr in_csr›} hypothesis of the acyclifier's correctness theorems.›

lemma out_csr_build: "out_csr = build_csr vcount (nth fst_list) [0..<m]"
  using keys_fst_lt by (simp add: out_csr_eq build_csr_scatter_eq)

lemma in_csr_build: "in_csr = build_csr vcount (nth snd_list) [0..<m]"
  using keys_snd_lt by (simp add: in_csr_eq build_csr_scatter_eq)

lemma out_graph_inv_csr: "out_graph_inv out_csr"
  unfolding out_graph_inv_def
proof (intro conjI ballI)
  show "csr_invar out_csr" by (simp add: out_csr_build build_csr_invar)
next
  fix v assume v: "v ∈ original_network.𝒱"
  have "csr_abstract out_csr v = {e ∈ set [0..<m]. fst_list ! e = v}"
    by (simp add: out_csr_build build_csr_abstract[OF V_lt_vcount[OF v]])
  also have "… = original_network.delta_plus v" 
    by (auto simp: original_network.delta_plus_def)
  finally show "csr_abstract out_csr v = original_network.delta_plus v" .
qed

lemma in_graph_inv_csr: "in_graph_inv in_csr"
  unfolding in_graph_inv_def
proof (intro conjI ballI)
  show "csr_invar in_csr" by (simp add: in_csr_build build_csr_invar)
next
  fix v assume v: "v ∈ original_network.𝒱"
  have "csr_abstract in_csr v = {e ∈ set [0..<m]. snd_list ! e = v}"
    by (simp add: in_csr_build build_csr_abstract[OF V_lt_vcount[OF v]])
  also have "… = original_network.delta_minus v" by (auto simp: original_network.delta_minus_def)
  finally show "csr_abstract in_csr v = original_network.delta_minus v" .
qed

lemma multigraph_inv_csr: "multigraph_inv out_csr in_csr"
  by (simp add: multigraph_inv_def out_graph_inv_csr in_graph_inv_csr)

text ‹A vertex that is an endpoint of some edge has a nonempty CSR block, so it is never
      @{const is_lonely}.  Conversely, a name whose two CSR blocks are both empty carries no edge.
      Together these characterise @{const is_lonely} as exactly ``carries no edge'', which is what
      makes the lonely guard skip precisely the edge-less names.›

lemma edged_not_lonely:
  assumes v: "v ∈ set fst_list ∪ set snd_list"
  shows "¬ is_lonely v"
proof -
  have vlt: "v < vcount" using v fst_snd_vs vs_less_vcount by blast
  from v consider (f) "v ∈ set fst_list" | (s) "v ∈ set snd_list" by blast
  thus ?thesis
  proof cases
    case f
    then obtain e where e0: "e < length fst_list" and fe: "fst_list ! e = v"
      by (auto simp: in_set_conv_nth)
    have e: "e < m" using e0 length_fst length_edges by simp
    have "csr_abstract out_csr v = {e ∈ set [0..<m]. fst_list ! e = v}"
      by (simp add: out_csr_build build_csr_abstract[OF vlt])
    hence "e ∈ csr_abstract out_csr v" using e fe by simp
    hence "csr_seg out_csr v ≠ {}" by (auto simp: csr_abstract_def)
    hence "csr_lo out_csr ! v < csr_hi out_csr ! v" by (auto simp: csr_seg_def split: if_splits)
    thus ?thesis by (simp add: is_lonely_def out_lo_def out_hi_def)
  next
    case s
    then obtain e where e: "e < m" and fe: "snd_list ! e = v"
      by (metis in_set_conv_nth length_snd length_edges)
    have "csr_abstract in_csr v = {e ∈ set [0..<m]. snd_list ! e = v}"
      by (simp add: in_csr_build build_csr_abstract[OF vlt])
    hence "e ∈ csr_abstract in_csr v" using e fe by simp
    hence "csr_seg in_csr v ≠ {}" by (auto simp: csr_abstract_def)
    hence "csr_lo in_csr ! v < csr_hi in_csr ! v" by (auto simp: csr_seg_def split: if_splits)
    thus ?thesis by (simp add: is_lonely_def in_lo_def in_hi_def)
  qed
qed

lemma not_lonely_edged:
  assumes vlt: "v < vcount" and nl: "¬ is_lonely v"
  shows "v ∈ set fst_list ∪ set snd_list"
proof -
  have coinv: "csr_invar out_csr" by (simp add: out_csr_build build_csr_invar)
  have cninv: "csr_invar in_csr" by (simp add: in_csr_build build_csr_invar)
  have vno: "v < csr_n out_csr" using vlt by (simp add: out_csr_build build_csr_n)
  have vni: "v < csr_n in_csr" using vlt by (simp add: in_csr_build build_csr_n)
  have leo: "out_lo ! v ≤ out_hi ! v"
    using csr_lo_le_hi[OF coinv vno] by (simp add: out_lo_def out_hi_def)
  have lei: "in_lo ! v ≤ in_hi ! v"
    using csr_lo_le_hi[OF cninv vni] by (simp add: in_lo_def in_hi_def)
  from nl consider (o) "out_lo ! v < out_hi ! v" | (i) "in_lo ! v < in_hi ! v"
    using leo lei by (auto simp: is_lonely_def)
  thus ?thesis
  proof cases
    case o
    hence "csr_seg out_csr v ≠ {}" using vno by (simp add: csr_seg_def out_lo_def out_hi_def)
    hence "csr_abstract out_csr v ≠ {}" by (auto simp: csr_abstract_def)
    then obtain e where "e ∈ {e ∈ set [0..<m]. fst_list ! e = v}"
      by (auto simp: out_csr_build build_csr_abstract[OF vlt])
    thus ?thesis by (auto simp: in_set_conv_nth length_fst length_edges)
  next
    case i
    hence "csr_seg in_csr v ≠ {}" using vni by (simp add: csr_seg_def in_lo_def in_hi_def)
    hence "csr_abstract in_csr v ≠ {}" by (auto simp: csr_abstract_def)
    then obtain e where "e ∈ {e ∈ set [0..<m]. snd_list ! e = v}"
      by (auto simp: in_csr_build build_csr_abstract[OF vlt])
    thus ?thesis by (auto simp: in_set_conv_nth length_snd length_edges)
  qed
qed

lemma is_lonely_iff:
  assumes v: "v ∈ set vs_list"
  shows "is_lonely v ⟷ v ∉ set fst_list ∪ set snd_list"
  using edged_not_lonely not_lonely_edged[OF vs_less_vcount[OF v]] by blast

text ‹The graph vertex set is exactly the set of edge endpoints, and — since every endpoint lies in
      the dense range and is non-lonely — exactly @{term ‹set edged_vs_list›}, the list fed to the
      acyclifier.  This is what keeps the acyclifier's @{term ‹vit_abstract all_vertices = 𝒱›}
      hypothesis intact under the dense model.›

lemma V_orig_eq: "original_network.𝒱 = set fst_list ∪ set snd_list"
proof
  show "original_network.𝒱 ⊆ set fst_list ∪ set snd_list"
  proof
    fix v assume "v ∈ original_network.𝒱"
    then obtain a b where ab: "(a, b) ∈ original_network.make_pair ` {0..<m}" "v ∈ {a, b}"
      by (auto simp: dVs_def)
    from ab(1) obtain e where e: "e < m" and me: "original_network.make_pair e = (a, b)" by auto
    have "a = fst_list ! e" "b = snd_list ! e" using e me by (auto simp: original_network.make_pair_def)
    thus "v ∈ set fst_list ∪ set snd_list"
      using ab(2) e length_fst length_snd length_edges by (auto simp: in_set_conv_nth)
  qed
next
  show "set fst_list ∪ set snd_list ⊆ original_network.𝒱" using edged_in_V by blast
qed

lemma set_edged_vs_list: "set edged_vs_list = set fst_list ∪ set snd_list"
proof
  show "set edged_vs_list ⊆ set fst_list ∪ set snd_list"
    using not_lonely_edged vs_less_vcount by (auto simp: edged_vs_list_def)
next
  show "set fst_list ∪ set snd_list ⊆ set edged_vs_list"
    using edged_not_lonely fst_snd_vs by (auto simp: edged_vs_list_def)
qed

lemma V_orig_eq_edged: "original_network.𝒱 = set edged_vs_list"
  by (simp add: V_orig_eq set_edged_vs_list)

text ‹The provable replacement for the (now false) ‹v ∈ set vs_list ⟹ v ∈ 𝒱›: every graph vertex is
      a name in the dense range, i.e. the inclusion holds one way only.›

lemma V_sub_vs_list: "original_network.𝒱 ⊆ set vs_list"
  using V_orig_eq fst_snd_vs by simp
text ‹All six arrays keep their sizes through the fold (@{const list_update} preserves length).›

definition sized ::
  "edge_tag list × 'n list × nat list × nat list × nat list × nat list ⇒ bool" where
  "sized s ⟷ (case s of (est, exc, oe, oc, ie, ic) ⇒
     length est = m ∧ length exc = Suc vcount ∧ length oe = m ∧ length oc = vcount
     ∧ length ie = m ∧ length ic = vcount)"

lemma passA_step_sized: "sized s ⟹ sized (passA_step fl e s)"
  by (cases s) (simp add: sized_def passA_step_def Let_def split: if_split)

lemma sized_passA: "sized (passA fl)"
  unfolding passA_def
  apply (rule fold_invariant[where Q = "λ_. True" and P = sized])
    apply simp
   apply (simp add: sized_def length_out_lo length_in_lo out_csr_eq in_csr_eq)
  apply (erule passA_step_sized)
  done

lemma length_excess[simp]: "length excess = Suc vcount"
  using sized_passA[of flow_list]
  by (auto simp: sized_def excess_def split: prod.splits)

lemma length_edge_state[simp]: "length (edge_state fl) = m"
  and length_free_out_edges[simp]: "length (free_out_edges fl) = m"
  and length_free_out_hi[simp]: "length (free_out_hi fl) = vcount"
  and length_free_in_edges[simp]: "length (free_in_edges fl) = m"
  and length_free_in_hi[simp]: "length (free_in_hi fl) = vcount"
  using sized_passA[of fl]
  by (auto simp: sized_def edge_state_def free_out_edges_def free_out_hi_def
                 free_in_edges_def free_in_hi_def split: prod.splits)

definition is_free :: "'n list ⇒ nat ⇒ bool" where
  "is_free fl e ⟷ edge_state fl ! e = InTree"
 
lemma length_fold_add_body:
  "length (fold (λv arr. arr[v := arr ! v + b_lookup v]) xs init) = length init"
  by (induct xs arbitrary: init) simp_all

lemma length_imbalance[simp]: "length imbalance = Suc vcount"
  by (simp add: imbalance_def length_fold_add_body)

subsection ‹Big-M, artificial-edge orientation and the augmented endpoints›

text ‹A single large cost @{term bigM} makes the tagged-pair potential representation faithful
      (‹bigM > 6 * sum of the absolute edge costs›) and is the artificial-edge cost (§2).›

definition bigM :: real where
  "bigM = 6 * h (sum_list (map abs cost_list)) + 1"

lemma bigM_gt: "bigM > 6 * h (sum_list (map abs cost_list))"
  by (simp add: bigM_def)

text ‹The potential/reduced-cost descriptor abstraction.  It sends the code-level tagged pair
      @{typ ‹mtag × 'n›} to a real value: the tagged M-coefficient scaled by the (proof-time)
      constant @{term bigM}, plus the homomorphic image of the ordinary part.  This is the ∗‹only›
      place the homomorphism @{term h} enters the potential abstraction; keeping it here (rather than
      in the executable code locale) is what makes the whole executable pipeline compute over @{typ 'n}.›

definition pval_abstract :: "real ⇒ mtag × 'n ⇒ real" where
  "pval_abstract M p = real_of_int (of_mtag (fst p)) * M + h (snd p)"

text ‹Every vertex-indexed array keeps length @{term ‹Suc vcount›} across the non-recursive state
      transformers (the recursive @{const build_dfs} is handled with its induction rule in the
      correctness development).›

definition dfs_sized :: "'n dfs_state ⇒ bool" where
  "dfs_sized s ⟷ length (ds_seen s) = Suc vcount ∧ length (ds_prnt s) = Suc vcount ∧
     length (ds_par s) = Suc vcount ∧ length (ds_dir s) = Suc vcount ∧
     length (ds_pot s) = Suc vcount ∧ length (ds_thrd s) = Suc vcount ∧
     length (ds_rvth s) = Suc vcount ∧ length (ds_lsuc s) = Suc vcount ∧
     length (ds_snum s) = Suc vcount"

lemma dfs_init_sized: "dfs_sized dfs_init"
  by (simp add: dfs_sized_def dfs_init_def del: replicate_Suc)

lemma dfs_discover_sized: "dfs_sized s ⟹ dfs_sized (dfs_discover s v w e)"
  by (simp add: dfs_sized_def dfs_discover_def Let_def)

lemma dfs_finish_sized: "dfs_sized s ⟹ dfs_sized (dfs_finish s v rest)"
  by (simp add: dfs_sized_def dfs_finish_def Let_def)

lemma emit_U_edge_sized: "dfs_sized s ⟹ dfs_sized (emit_U_edge s v)"
  by (simp add: dfs_sized_def emit_U_edge_def Let_def)

end

end
