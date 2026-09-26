theory Network_Simplex_Final
  imports Network_Simplex_Preservation
Flow_Theory.Optimality_Certification
begin

text \<open>\<^bold>\<open>Consequences of the terminating branches.\<close> When the loop stops it does so in one of two
      terminal branches. In the success branch the selector found no entering edge, so the current
      flow is a genuine minimum-cost \<open>b\<close>-flow (via \<open>optimality_from_potentials\<close>). In the unbounded
      branch the bottleneck search exposed an all-infinite-capacity negative circuit, i.e.
      \<open>has_neg_infty_cycle\<close> holds and the instance is unbounded.\<close>

context network_simplex
begin

subsection \<open>Success branch: the flow is optimal\<close>

text \<open>At @{const ns_success_cond} the selector returns @{term None}, so @{const no_entering_edge}
      holds: every @{term L}-edge has non-negative and every @{term U}-edge non-positive reduced cost.
      Together with the structural invariants (@{term L}-edges carry zero flow, @{term U}-edges are
      saturated, tree edges have zero reduced cost) this discharges the three complementary-slackness
      hypotheses of @{thm optimality_from_potentials} pointwise, by cases on the partition
      @{term \<open>\<E> = T \<union> U \<union> L\<close>}.\<close>

lemma ns_success_optimal:
  assumes inv: "ns_invar s" and cond: "ns_success_cond s"
  shows "is_Opt b (ns_flow_of s)"
proof -
  have selN: "ns_select s = None" using cond by (rule ns_success_condE)
  have precond: "selection_precond (edge_sel s) (potentials s) (edge_state s)"
    using ns_invar_implD[OF ns_invarD(1)[OF inv]] ns_invar_pot_fitsD[OF ns_invarD(5)[OF inv]]
    by (simp add: selection_precond_def potential_fits_spanning_tree_partition_def)
  have "sel_select (edge_sel s) (potentials s) (edge_state s) = None"
    using selN by (simp add: ns_select_def)
  hence noent: "no_entering_edge (potentials s) (edge_state s)"
    using sel_select_NoneD[OF precond] by simp
  have noentL: "\<And>e. e \<in> ns_L_of s \<Longrightarrow> 0 \<le> reduced_cost (potentials s) e"
    and noentU: "\<And>e. e \<in> ns_U_of s \<Longrightarrow> reduced_cost (potentials s) e \<le> 0"
    using noent by (auto simp: no_entering_edge_def ns_L_of_def ns_U_of_def)
  have slinv: "ns_invar_selfloop s" using ns_invarD(8)[OF inv] .
  have Eeq: "\<E> = ns_tree_edges s \<union> (ns_U_of s \<union> ns_selfloops_U) \<union> (ns_L_of s \<union> ns_selfloops_L)"
    using ns_invar_partitionD[OF ns_invarD(3)[OF inv]] by (simp add: spanning_tree_partition_def)
  have flowL: "\<And>e. e \<in> ns_L_of s \<union> ns_selfloops_L \<Longrightarrow> ns_flow_of s e = 0"
    and flowU: "\<And>e. e \<in> ns_U_of s \<union> ns_selfloops_U \<Longrightarrow> ereal (ns_flow_of s e) = \<u> e"
    using ns_invar_flow_fitsD[OF ns_invarD(4)[OF inv]] slinv
    by (auto simp: flow_fits_spanning_tree_partition_def ns_selfloops_L_def ns_selfloops_U_def
                   ns_invar_selfloop_def)
  have potT: "\<And>e. e \<in> ns_tree_edges s \<Longrightarrow> \<c> e + ns_pot_of s (fst e) - ns_pot_of s (snd e) = 0"
    using ns_invar_pot_fitsD[OF ns_invarD(5)[OF inv]] by (auto simp: potential_fits_spanning_tree_partition_def)
  have rc: "\<And>e. reduced_cost (potentials s) e = \<c> e + ns_pot_of s (fst e) - ns_pot_of s (snd e)"
    by (simp add: reduced_cost_def)
  have slrcL: "\<And>e. e \<in> ns_selfloops_L \<Longrightarrow> 0 \<le> \<c> e + ns_pot_of s (fst e) - ns_pot_of s (snd e)"
    by (auto simp: ns_selfloops_L_def)
  have slrcU: "\<And>e. e \<in> ns_selfloops_U \<Longrightarrow> \<c> e + ns_pot_of s (fst e) - ns_pot_of s (snd e) \<le> 0"
    by (auto simp: ns_selfloops_U_def)
  show ?thesis
  proof (rule optimality_from_potentials[where \<pi> = "ns_pot_of s"])
    show "(ns_flow_of s) is b flow" using ns_invar_bflowD[OF ns_invarD(2)[OF inv]] .
  next
    fix e assume e: "e \<in> \<E>" and f0: "ns_flow_of s e = 0" and une: "\<u> e \<noteq> 0"
    show "0 \<le> \<c> e + ns_pot_of s (fst e) - ns_pot_of s (snd e)"
    proof (cases "e \<in> ns_tree_edges s")
      case True thus ?thesis using potT[OF True] by simp
    next
      case False
      hence "e \<in> ns_U_of s \<union> ns_selfloops_U \<or> e \<in> ns_L_of s \<union> ns_selfloops_L" using e Eeq by auto
      thus ?thesis
      proof (elim disjE)
        assume eU: "e \<in> ns_U_of s \<union> ns_selfloops_U"
        have "ereal (ns_flow_of s e) = \<u> e" using flowU[OF eU] .
        thus ?thesis using f0 une by (simp add: zero_ereal_def)
      next
        assume eL: "e \<in> ns_L_of s \<union> ns_selfloops_L"
        thus ?thesis using noentL slrcL rc by auto
      qed
    qed
  next
    fix e assume e: "e \<in> \<E>" and fu: "ereal (ns_flow_of s e) = \<u> e" and une: "\<u> e \<noteq> 0"
    show "\<c> e + ns_pot_of s (fst e) - ns_pot_of s (snd e) \<le> 0"
    proof (cases "e \<in> ns_tree_edges s")
      case True thus ?thesis using potT[OF True] by simp
    next
      case False
      hence "e \<in> ns_U_of s \<union> ns_selfloops_U \<or> e \<in> ns_L_of s \<union> ns_selfloops_L" using e Eeq by auto
      thus ?thesis
      proof (elim disjE)
        assume eU: "e \<in> ns_U_of s \<union> ns_selfloops_U"
        thus ?thesis using noentU slrcU rc by auto
      next
        assume eL: "e \<in> ns_L_of s \<union> ns_selfloops_L"
        have "ns_flow_of s e = 0" using flowL[OF eL] .
        thus ?thesis using fu une by (simp add: zero_ereal_def)
      qed
    qed
  next
    fix e assume e: "e \<in> \<E>" and fpos: "0 < ns_flow_of s e" and flt: "ereal (ns_flow_of s e) < \<u> e"
    show "\<c> e + ns_pot_of s (fst e) - ns_pot_of s (snd e) = 0"
    proof (cases "e \<in> ns_tree_edges s")
      case True thus ?thesis using potT[OF True] by simp
    next
      case False
      hence "e \<in> ns_U_of s \<union> ns_selfloops_U \<or> e \<in> ns_L_of s \<union> ns_selfloops_L" using e Eeq by auto
      thus ?thesis
      proof (elim disjE)
        assume eU: "e \<in> ns_U_of s \<union> ns_selfloops_U"
        have "ereal (ns_flow_of s e) = \<u> e" using flowU[OF eU] .
        thus ?thesis using flt by simp
      next
        assume eL: "e \<in> ns_L_of s \<union> ns_selfloops_L"
        have "ns_flow_of s e = 0" using flowL[OF eL] .
        thus ?thesis using fpos by simp
      qed
    qed
  qed
qed

text \<open>Directed walk built from the parent edges along an up-path (all edges point child$\rightarrow$parent):
      @{term \<open>map (par_edge s) P\<close>} is a directed walk from @{term \<open>hd P\<close>} to the junction @{term a}.\<close>

lemma up_walk_cas:
  assumes inv: "ns_invar s"
  shows "set P \<subseteq> \<V> - {r} \<Longrightarrow> (\<And>v. v \<in> set P \<Longrightarrow> par_up s v)
     \<Longrightarrow> (\<And>i. Suc i < length P \<Longrightarrow> par_vx s (P ! i) = P ! Suc i)
     \<Longrightarrow> P \<noteq> [] \<Longrightarrow> par_vx s (last P) = a
     \<Longrightarrow> cas (hd P) (map make_pair (map (par_edge s) P)) a"
proof (induction P arbitrary: a)
  case Nil thus ?case by simp
next
  case (Cons v P')
  have vV: "v \<in> \<V> - {r}" using Cons.prems(1) by simp
  have vu: "par_up s v" using Cons.prems(2) by simp
  have mk: "make_pair (par_edge s v) = (v, par_vx s v)"
    using ns_invar_tree_dirD[OF ns_invarD(7)[OF inv] vV] vu by (simp add: make_pair_def par_vx_def)
  show ?case
  proof (cases "P' = []")
    case True
    thus ?thesis using mk Cons.prems(5) by simp
  next
    case False
    have pv_hd: "par_vx s v = hd P'"
      using Cons.prems(3)[of 0] False by (simp add: hd_conv_nth)
    have "cas (hd P') (map make_pair (map (par_edge s) P')) a"
    proof (rule Cons.IH)
      show "set P' \<subseteq> \<V> - {r}" using Cons.prems(1) by simp
      show "\<And>w. w \<in> set P' \<Longrightarrow> par_up s w" using Cons.prems(2) by simp
      show "\<And>i. Suc i < length P' \<Longrightarrow> par_vx s (P' ! i) = P' ! Suc i"
        using Cons.prems(3)[of "Suc i" for i] by simp
      show "P' \<noteq> []" using False .
      show "par_vx s (last P') = a" using Cons.prems(5) False by simp
    qed
    thus ?thesis using mk pv_hd by simp
  qed
qed

text \<open>Directed walk from the parent edges along a down-path (all edges point parent$\rightarrow$child), taken in
      reverse: @{term \<open>map (par_edge s) (rev P)\<close>} is a directed walk from the junction @{term a} to
      @{term \<open>hd P\<close>}.\<close>

lemma dn_walk_cas:
  assumes inv: "ns_invar s"
  shows "set P \<subseteq> \<V> - {r} \<Longrightarrow> (\<And>v. v \<in> set P \<Longrightarrow> \<not> par_up s v)
     \<Longrightarrow> (\<And>i. Suc i < length P \<Longrightarrow> par_vx s (P ! i) = P ! Suc i)
     \<Longrightarrow> P \<noteq> [] \<Longrightarrow> par_vx s (last P) = a
     \<Longrightarrow> cas a (map make_pair (map (par_edge s) (rev P))) (hd P)"
proof (induction P arbitrary: a rule: rev_induct)
  case Nil thus ?case by simp
next
  case (snoc x P')
  have xV: "x \<in> \<V> - {r}" using snoc.prems(1) by simp
  have xd: "\<not> par_up s x" using snoc.prems(2) by simp
  have mk: "make_pair (par_edge s x) = (par_vx s x, x)"
    using ns_invar_tree_dirD[OF ns_invarD(7)[OF inv] xV] xd by (simp add: make_pair_def par_vx_def)
  have ax: "par_vx s x = a" using snoc.prems(5) by simp
  show ?case
  proof (cases "P' = []")
    case True
    thus ?thesis using mk ax by simp
  next
    case False
    have junc: "par_vx s (last P') = x"
      using snoc.prems(3)[of "length P' - 1"] False
      by (simp add: nth_append last_conv_nth)
    have "cas x (map make_pair (map (par_edge s) (rev P'))) (hd P')"
    proof (rule snoc.IH)
      show "set P' \<subseteq> \<V> - {r}" using snoc.prems(1) by simp
      show "\<And>w. w \<in> set P' \<Longrightarrow> \<not> par_up s w" using snoc.prems(2) by simp
      show "\<And>i. Suc i < length P' \<Longrightarrow> par_vx s (P' ! i) = P' ! Suc i"
        using snoc.prems(3) by (simp add: nth_append)
      show "P' \<noteq> []" using False .
      show "par_vx s (last P') = x" using junc .
    qed
    thus ?thesis using mk ax False by (simp add: hd_append)
  qed
qed

subsection \<open>Consequences of an infinite bottleneck\<close>

lemma res_fwd_m1_cap:
  assumes inv: "ns_invar s" and aE: "a \<in> \<E>" and r1: "res_fwd s a = - 1"
  shows "cap a = - 1"
proof (rule ccontr)
  assume cne: "cap a \<noteq> - 1"
  hence cnn: "0 \<le> cap a" using cap_nonneg[OF aE] by simp
  have ue: "\<u> a = ereal (h (cap a))" using cap_finite[OF aE cnn] .
  have "isuflow (ns_flow_of s)" using ns_invar_bflowD[OF ns_invarD(2)[OF inv]] by (simp add: isbflow_def)
  hence "ereal (ns_flow_of s a) \<le> \<u> a" using aE by (auto simp: isuflow_def)
  hence "ns_flow_of s a \<le> h (cap a)" using ue by simp
  hence "flow_lookup (current_flow s) a \<le> cap a" by (simp add: comp_def)
  hence "0 \<le> res_fwd s a" using cne by (simp add: res_fwd_def)
  thus False using r1 by simp
qed

lemma flow_nonneg:
  assumes inv: "ns_invar s" and aE: "a \<in> \<E>" shows "0 \<le> ns_flow_of s a"
  using ns_invar_bflowD[OF ns_invarD(2)[OF inv]] aE by (auto simp: isbflow_def isuflow_def)

lemma res_up_inf:
  assumes inv: "ns_invar s" and vV: "v \<in> \<V> - {r}" and r1: "res_up s v = - 1"
  shows "par_up s v \<and> \<u> (par_edge s v) = \<infinity>"
proof -
  have peE: "par_edge s v \<in> \<E>" using ns_invar_tree_edgeD[OF ns_invarD(7)[OF inv] vV] .
  have pu: "par_up s v"
  proof (rule ccontr)
    assume "\<not> par_up s v"
    hence "res_up s v = flow_lookup (current_flow s) (par_edge s v)" by (simp add: res_up_def res_bwd_def)
    thus False using r1 flow_nonneg[OF inv peE] by (simp add: comp_def)
  qed
  hence "res_fwd s (par_edge s v) = - 1" using r1 by (simp add: res_up_def)
  hence "cap (par_edge s v) = - 1" using res_fwd_m1_cap[OF inv peE] by simp
  thus ?thesis using pu cap_infinite[OF peE] by simp
qed

lemma res_down_inf:
  assumes inv: "ns_invar s" and vV: "v \<in> \<V> - {r}" and r1: "res_down s v = - 1"
  shows "\<not> par_up s v \<and> \<u> (par_edge s v) = \<infinity>"
proof -
  have peE: "par_edge s v \<in> \<E>" using ns_invar_tree_edgeD[OF ns_invarD(7)[OF inv] vV] .
  have pd: "\<not> par_up s v"
  proof (rule ccontr)
    assume "\<not> \<not> par_up s v"
    hence "res_down s v = flow_lookup (current_flow s) (par_edge s v)" by (simp add: res_down_def res_bwd_def)
    thus False using r1 flow_nonneg[OF inv peE] by (simp add: comp_def)
  qed
  hence "res_fwd s (par_edge s v) = - 1" using r1 by (simp add: res_down_def)
  hence "cap (par_edge s v) = - 1" using res_fwd_m1_cap[OF inv peE] by simp
  thus ?thesis using pd cap_infinite[OF peE] by simp
qed

lemma scan_up_all_inf: "scan_up s p = (- 1, best) \<Longrightarrow> v \<in> set p \<Longrightarrow> res_up s v = - 1"
  using scan_up_min[of s p "- 1" best v] by auto

lemma scan_down_all_inf: "scan_down s p = (- 1, best) \<Longrightarrow> v \<in> set p \<Longrightarrow> res_down s v = - 1"
  using scan_down_min[of s p "- 1" best v] by auto

lemma mininf_m1_iff: "mininf x y = - 1 \<longleftrightarrow> x = - 1 \<and> y = - 1"
  by (auto simp: mininf_def)

lemma mininf_eq_cases: "mininf x y = x \<or> mininf x y = y"
  by (auto simp: mininf_def min_def)

lemma bottleneck_None_facts:
  assumes inv: "ns_invar s"
    and sel: "ns_select s = Some (e, in_U, \<gamma>, sel')"
    and pp:  "get_path_pair (spanning_tree s) (fst_exec e) (snd_exec e) = (p1, p2)"
    and bn:  "bottleneck s e in_U p1 p2 = (- 1, isf, lv, lfw, lus)"
  shows "\<not> in_U" and "\<u> e = \<infinity>"
    and "\<And>v. v \<in> set p2 \<Longrightarrow> par_up s v \<and> \<u> (par_edge s v) = \<infinity>"
    and "\<And>v. v \<in> set p1 \<Longrightarrow> \<not> par_up s v \<and> \<u> (par_edge s v) = \<infinity>"
proof -
  have eE: "e \<in> \<E>" using ns_select_SomeD(2)[OF inv sel] .
  hence same_eps:"fst_exec e = fst e" "snd_exec e = snd e"
    by auto
  have p1V: "set p1 \<subseteq> \<V> - {r}" and p2V: "set p2 \<subseteq> \<V> - {r}"
    using get_path_pair_verts[OF inv eE entering_not_selfloop[OF inv sel] pp[simplified same_eps]] by auto
  obtain mu vu where su: "scan_up s (if in_U then p1 else p2) = (mu, vu)"
    by (cases "scan_up s (if in_U then p1 else p2)")
  obtain md vd where sd: "scan_down s (if in_U then p2 else p1) = (md, vd)"
    by (cases "scan_down s (if in_U then p2 else p1)")
  let ?re = "if in_U then res_bwd s e else res_fwd s e"
  let ?d = "mininf ?re (mininf mu md)"
  have bform: "bottleneck s e in_U p1 p2 =
     (if ?d = - 1 then (- 1, True, r, False, False)
      else if mu \<noteq> - 1 \<and> mu = ?d then (?d, False, vu, par_up s vu, True)
      else if ?re = ?d then (?d, True, r, False, False)
      else (?d, False, vd, \<not> par_up s vd, False))"
    unfolding bottleneck_def Let_def su sd by simp
  have dm1: "?d = - 1"
    using bn unfolding bform by (auto split: if_splits)
  have re1: "?re = - 1" and mu1: "mu = - 1" and md1: "md = - 1"
    using dm1 by (auto simp: mininf_def split: if_splits)
  have iu: "\<not> in_U"
  proof (rule ccontr)
    assume "\<not> \<not> in_U" hence "in_U" by simp
    hence "res_bwd s e = - 1" using re1 by simp
    thus False using flow_nonneg[OF inv eE] by (simp add: res_bwd_def)
  qed
  have ue_inf: "\<u> e = \<infinity>"
  proof -
    have "res_fwd s e = - 1" using re1 iu by simp
    hence "cap e = - 1" using res_fwd_m1_cap[OF inv eE] by simp
    thus ?thesis using cap_infinite[OF eE] by simp
  qed
  have p2fact: "\<And>v. v \<in> set p2 \<Longrightarrow> par_up s v \<and> \<u> (par_edge s v) = \<infinity>"
  proof -
    fix v assume vp: "v \<in> set p2"
    have vV: "v \<in> \<V> - {r}" using vp p2V by auto
    have su2: "scan_up s p2 = (- 1, vu)" using su iu mu1 by simp
    have "res_up s v = - 1" using scan_up_all_inf[OF su2 vp] .
    thus "par_up s v \<and> \<u> (par_edge s v) = \<infinity>" using res_up_inf[OF inv vV] by simp
  qed
  have p1fact: "\<And>v. v \<in> set p1 \<Longrightarrow> \<not> par_up s v \<and> \<u> (par_edge s v) = \<infinity>"
  proof -
    fix v assume vp: "v \<in> set p1"
    have vV: "v \<in> \<V> - {r}" using vp p1V by auto
    have sd2: "scan_down s p1 = (- 1, vd)" using sd iu md1 by simp
    have "res_down s v = - 1" using scan_down_all_inf[OF sd2 vp] .
    thus "\<not> par_up s v \<and> \<u> (par_edge s v) = \<infinity>" using res_down_inf[OF inv vV] by simp
  qed
  show "\<not> in_U" using iu .
  show "\<u> e = \<infinity>" using ue_inf .
  show "\<And>v. v \<in> set p2 \<Longrightarrow> par_up s v \<and> \<u> (par_edge s v) = \<infinity>" using p2fact .
  show "\<And>v. v \<in> set p1 \<Longrightarrow> \<not> par_up s v \<and> \<u> (par_edge s v) = \<infinity>" using p1fact .
qed

subsection \<open>The negative infinite-capacity fundamental circuit\<close>

lemma foldr_c_sum_list: "foldr (\<lambda>e. (+) (\<c> e)) D 0 = (\<Sum>ee\<leftarrow>D. \<c> ee)"
  by (induct D) auto

lemma ns_unbounded_neg_cycle:
  assumes inv: "ns_invar s" and cond: "ns_unbounded_cond s"
  shows "has_neg_infty_cycle make_pair \<E> \<c> \<u>"
proof (rule ns_unbounded_condE[OF cond], goal_cases)
  case (1 e in_U \<gamma> sel' p1 p2 is_flip v e0fwd up_side)
  note sel = 1(1) and pp = 1(2) and bn = 1(3)
  let ?absT = "abstract_arborescense (spanning_tree s)"
  have eE: "e \<in> \<E>" using ns_select_SomeD(2)[OF inv sel] .
  hence same_eps:"fst_exec e = fst e" "snd_exec e = snd e"
    by auto
  have fV: "fst e \<in> \<V>" using fst_E_V[OF eE] .
  have sV: "snd e \<in> \<V>" using snd_E_V[OF eE] .
  note bf = bottleneck_None_facts[OF inv sel pp bn]
  have ueE: "\<u> e = \<infinity>" using bf(2) .
  have p2up: "\<And>v. v \<in> set p2 \<Longrightarrow> par_up s v" using bf(3) by simp
  have p1dn: "\<And>v. v \<in> set p1 \<Longrightarrow> \<not> par_up s v" using bf(4) by simp
  note al = get_path_pair_align[OF inv sel pp[simplified same_eps]]
  obtain a p3 where w1: "walk_betw ?absT (fst e) (p1 @ a # p3) r"
    and w2: "walk_betw ?absT (snd e) (p2 @ a # p3) r"
    and d1: "distinct (p1 @ a # p3)" and d2: "distinct (p2 @ a # p3)"
    using al(1) by blast
  have p1V: "set p1 \<subseteq> \<V> - {r}" and p2V: "set p2 \<subseteq> \<V> - {r}"
    using get_path_pair_verts[OF inv eE entering_not_selfloop[OF inv sel] pp[simplified same_eps]] by auto
  have al1: "\<And>i. Suc i < length p1 \<Longrightarrow> par_vx s (p1 ! i) = p1 ! Suc i" using al(2) .
  have arbb: "arborescense_invar (spanning_tree s)" using ns_invar_implD(7)[OF ns_invarD(1)[OF inv]] .
  have aV: "a \<in> \<V>" using walk_in_Vs[OF w2] general(4)[OF arbb] by auto
  have edgeE: "\<And>v. v \<in> set p1 \<union> set p2 \<Longrightarrow> par_edge s v \<in> \<E>"
    using p1V p2V ns_invar_tree_edgeD[OF ns_invarD(7)[OF inv]] by auto
  have mkE: "\<And>v. v \<in> set p1 \<union> set p2 \<Longrightarrow> make_pair (par_edge s v) \<in> make_pair ` \<E>"
    using edgeE by blast
  \<comment> \<open>junction: the last path vertex's parent is the apex @{term a}\<close>
  have junc1: "p1 \<noteq> [] \<Longrightarrow> par_vx s (last p1) = a"
  proof -
    assume ne: "p1 \<noteq> []"
    have lp: "0 < length p1" using ne by simp
    have se: "Suc (length p1 - 1) = length p1" using lp by simp
    have e1: "(p1 @ a # p3) ! (length p1 - 1) = last p1"
      using ne by (simp add: nth_append last_conv_nth)
    have e2: "(p1 @ a # p3) ! Suc (length p1 - 1) = a" using se by (simp add: nth_append)
    have idx: "Suc (length p1 - 1) < length (p1 @ a # p3)" using se by simp
    have mem: "(p1 @ a # p3) ! (length p1 - 1) \<in> \<V> - {r}"
      using e1 ne p1V by (metis last_in_set subsetD)
    show "par_vx s (last p1) = a"
      using walk_succ_is_par_vx[OF inv w1 d1 idx mem] e1 e2 by simp
  qed
  have junc2: "p2 \<noteq> [] \<Longrightarrow> par_vx s (last p2) = a"
  proof -
    assume ne: "p2 \<noteq> []"
    have lp: "0 < length p2" using ne by simp
    have se: "Suc (length p2 - 1) = length p2" using lp by simp
    have e1: "(p2 @ a # p3) ! (length p2 - 1) = last p2"
      using ne by (simp add: nth_append last_conv_nth)
    have e2: "(p2 @ a # p3) ! Suc (length p2 - 1) = a" using se by (simp add: nth_append)
    have idx: "Suc (length p2 - 1) < length (p2 @ a # p3)" using se by simp
    have mem: "(p2 @ a # p3) ! (length p2 - 1) \<in> \<V> - {r}"
      using e1 ne p2V by (metis last_in_set subsetD)
    show "par_vx s (last p2) = a"
      using walk_succ_is_par_vx[OF inv w2 d2 idx mem] e1 e2 by simp
  qed
  \<comment> \<open>the three directed pieces of the fundamental circuit\<close>
  have adown: "awalk (make_pair ` \<E>) a (map make_pair (map (par_edge s) (rev p1))) (fst e)"
  proof (cases "p1 = []")
    case True
    hence "fst e = a" using w1 by (auto simp: walk_betw_def)
    thus ?thesis using True aV by (simp add: awalk_Nil_iff)
  next
    case ne: False
    have hd1: "hd p1 = fst e" using w1 ne by (auto simp: walk_betw_def)
    have "cas a (map make_pair (map (par_edge s) (rev p1))) (hd p1)"
      using dn_walk_cas[OF inv p1V p1dn al1 ne junc1[OF ne]] .
    hence "cas a (map make_pair (map (par_edge s) (rev p1))) (fst e)" using hd1 by simp
    moreover have "set (map make_pair (map (par_edge s) (rev p1))) \<subseteq> make_pair ` \<E>"
      using mkE by auto
    ultimately show ?thesis using aV by (simp add: awalk_def)
  qed
  have aup: "awalk (make_pair ` \<E>) (snd e) (map make_pair (map (par_edge s) p2)) a"
  proof (cases "p2 = []")
    case True
    hence "snd e = a" using w2 by (auto simp: walk_betw_def)
    thus ?thesis using True aV by (simp add: awalk_Nil_iff)
  next
    case ne: False
    have hd2: "hd p2 = snd e" using w2 ne by (auto simp: walk_betw_def)
    have "cas (hd p2) (map make_pair (map (par_edge s) p2)) a"
      using up_walk_cas[OF inv p2V p2up al(3) ne junc2[OF ne]] .
    hence "cas (snd e) (map make_pair (map (par_edge s) p2)) a" using hd2 by simp
    moreover have "set (map make_pair (map (par_edge s) p2)) \<subseteq> make_pair ` \<E>"
      using mkE by auto
    moreover have "snd e \<in> dVs (make_pair ` \<E>)" using sV by simp
    ultimately show ?thesis by (simp add: awalk_def)
  qed
  have aedge: "awalk (make_pair ` \<E>) (fst e) [make_pair e] (snd e)"
    using eE by (auto intro!: arc_implies_awalk simp: make_pair_def)
  define D where "D = map (par_edge s) (rev p1) @ e # map (par_edge s) p2"
  have mkD: "map make_pair D = map make_pair (map (par_edge s) (rev p1))
                              @ make_pair e # map make_pair (map (par_edge s) p2)"
    by (simp add: D_def)
  have awalkD: "awalk (make_pair ` \<E>) a (map make_pair D) a"
    unfolding mkD using adown aedge aup by (simp add: awalk_append_iff awalk_Cons_iff make_pair_def)
  have closedD: "closed_w (make_pair ` \<E>) (map make_pair D)"
    unfolding closed_w_def using awalkD by (auto simp: D_def)
  \<comment> \<open>all circuit edges have infinite capacity\<close>
  have infD: "\<And>ee. ee \<in> set D \<Longrightarrow> \<u> ee = PInfty"
  proof -
    fix ee assume "ee \<in> set D"
    then consider "ee = e" | v where "v \<in> set p1" "ee = par_edge s v"
      | v where "v \<in> set p2" "ee = par_edge s v" by (auto simp: D_def)
    thus "\<u> ee = PInfty"
    proof cases
      case 1 thus ?thesis using ueE by simp
    next
      case (2 v) thus ?thesis using bf(4) by simp
    next
      case (3 v) thus ?thesis using bf(3) by simp
    qed
  qed
  have setD: "set D \<subseteq> \<E>" using eE edgeE by (auto simp: D_def)
  \<comment> \<open>the circuit cost telescopes to the (negative) reduced cost of the entering edge\<close>
  have cp2: "(\<Sum>w\<leftarrow>p2. \<c> (par_edge s w)) = ns_pot_of s a - ns_pot_of s (snd e)"
  proof -
    have "(\<Sum>w\<leftarrow>p2. \<c> (par_edge s w)) = (\<Sum>w\<leftarrow>p2. \<c> (par_edge s w) * (if par_up s w then 1 else - 1))"
      by (rule arg_cong[where f=sum_list], rule map_cong[OF refl]) (simp add: p2up)
    also have "... = 1 * (ns_pot_of s a - ns_pot_of s (snd e))"
      using up_cost_sum[OF inv w2 d2 p2V, of 1] by simp
    finally show ?thesis by simp
  qed
  have cp1: "(\<Sum>w\<leftarrow>p1. \<c> (par_edge s w)) = ns_pot_of s (fst e) - ns_pot_of s a"
  proof -
    have "(\<Sum>w\<leftarrow>p1. \<c> (par_edge s w)) = (\<Sum>w\<leftarrow>p1. \<c> (par_edge s w) * (if par_up s w then - 1 else 1))"
      by (rule arg_cong[where f=sum_list], rule map_cong[OF refl]) (simp add: p1dn)
    also have "... = 1 * (ns_pot_of s (fst e) - ns_pot_of s a)"
      using down_cost_sum[OF inv w1 d1 p1V, of 1] by simp
    finally show ?thesis by simp
  qed
  have costD: "(\<Sum>ee\<leftarrow>D. \<c> ee) = reduced_cost (potentials s) e"
  proof -
    have revp1: "(\<Sum>w\<leftarrow>rev p1. \<c> (par_edge s w)) = (\<Sum>w\<leftarrow>p1. \<c> (par_edge s w))"
      by (metis rev_map sum_list_rev)
    have "(\<Sum>ee\<leftarrow>D. \<c> ee) = (\<Sum>w\<leftarrow>rev p1. \<c> (par_edge s w)) + \<c> e + (\<Sum>w\<leftarrow>p2. \<c> (par_edge s w))"
      by (simp add: D_def comp_def)
    also have "... = (ns_pot_of s (fst e) - ns_pot_of s a) + \<c> e + (ns_pot_of s a - ns_pot_of s (snd e))"
      using revp1 cp1 cp2 by simp
    finally show ?thesis by (simp add: reduced_cost_def)
  qed
  \<comment> \<open>the entering edge is in @{term L}, so its reduced cost is strictly negative\<close>
  have precond: "selection_precond (edge_sel s) (potentials s) (edge_state s)"
    using ns_invar_implD[OF ns_invarD(1)[OF inv]] ns_invar_pot_fitsD[OF ns_invarD(5)[OF inv]]
    by (simp add: selection_precond_def potential_fits_spanning_tree_partition_def)
  have selS: "sel_select (edge_sel s) (potentials s) (edge_state s) = Some (e, in_U, \<gamma>, sel')"
    using sel by (simp add: ns_select_def)
  have "entering_edge (potentials s) (edge_state s) e in_U"
    using sel_select_SomeD(4)[OF precond selS] .
  hence rcneg: "reduced_cost (potentials s) e < 0" using bf(1) by (simp add: entering_edge_def)
  have costneg: "foldr (\<lambda>e. (+) (\<c> e)) D 0 < 0" using costD rcneg by (simp add: foldr_c_sum_list)
  show ?case
    by (rule has_neg_infty_cycleI[OF closedD costneg setD]) (rule infD)
qed

subsection \<open>Total correctness of the loop\<close>

text \<open>The three ingredients --- termination, the success-branch optimality and the unbounded-branch
      circuit --- are assembled into one statement about @{const ns_loop}. The building blocks are the
      case analysis @{thm ns_loop_cases}, the guarded one-step unfoldings @{thm ns_loop_simps} and the
      tailored induction @{thm ns_loop_induct} together with the preservation/decrease lemmas
      @{thm ns_flip_preservation} and @{thm ns_pivot_preservation}.\<close>

text \<open>The per-step decrease relation @{const ns_less} is well-founded: it embeds into the
      lexicographic product of the (finite) tree-count and the violation count.\<close>

lemma wf_ns_less: "wf {(s', s). ns_less s' s}"
proof (rule wf_subset)
  show "wf (inv_image (less_than <*lex*> less_than) (\<lambda>s. (card (possible_trees s), ns_violation s)))"
    by (rule wf_inv_image[OF wf_lex_prod[OF wf_less_than wf_less_than]])
  show "{(s', s). ns_less s' s} \<subseteq> inv_image (less_than <*lex*> less_than) (\<lambda>s. (card (possible_trees s), ns_violation s))"
    by (auto simp: ns_less_def)
qed

text \<open>\<^bold>\<open>(a) Termination.\<close> From any state satisfying the invariant the loop is defined: by well-founded
      induction on @{const ns_less}, each recursive branch reaches an invariant-preserving successor
      that is strictly smaller, so the domain predicate propagates back.\<close>

lemma ns_loop_dom_of_invar:
  "ns_invar s \<Longrightarrow> ns_loop_dom s"
proof (induction s rule: wf_induct_rule[OF wf_ns_less])
  case (1 s)
  show ?case
  proof (cases s rule: ns_loop_cases)
    case 1
    thus ?thesis by (rule ns_loop_dom_success)
  next
    case 2
    thus ?thesis by (rule ns_loop_dom_unbounded)
  next
    case 3
    have iv: "ns_invar (ns_flip_upd s)" using ns_flip_preservation(1)[OF "1.prems" 3] .
    have ls: "ns_less (ns_flip_upd s) s" using ns_flip_preservation(2)[OF "1.prems" 3] .
    have "ns_loop_dom (ns_flip_upd s)" using "1.IH"[of "ns_flip_upd s"] ls iv by simp
    thus ?thesis using ns_loop_dom_flip[OF 3] by simp
  next
    case 4
    have iv: "ns_invar (ns_pivot_upd s)" using ns_pivot_preservation(1)[OF "1.prems" 4] .
    have ls: "ns_less (ns_pivot_upd s) s" using ns_pivot_preservation(2)[OF "1.prems" 4] .
    have "ns_loop_dom (ns_pivot_upd s)" using "1.IH"[of "ns_pivot_upd s"] ls iv by simp
    thus ?thesis using ns_loop_dom_pivot[OF 4] by simp
  qed
qed

text \<open>\<^bold>\<open>(b)+(c) Result classification.\<close> Induction along the loop's own recursion: the two recursive
      branches preserve the invariant and hand the property to the successor, while the two terminal
      branches close it with @{thm ns_success_optimal} and @{thm ns_unbounded_neg_cycle}.\<close>

lemma ns_loop_return_correct_aux:
  assumes dom: "ns_loop_dom s"
  shows "ns_invar s \<longrightarrow> (return (ns_loop s) = unbounded \<longrightarrow> has_neg_infty_cycle make_pair \<E> \<c> \<u>)
       \<and> (return (ns_loop s) = success \<longrightarrow> is_Opt b (ns_flow_of (ns_loop s)))"
proof (induction rule: ns_loop_induct[OF dom])
  case (1 s)
  note IH = this
  show ?case
  proof (rule impI)
    assume inv: "ns_invar s"
    show "(return (ns_loop s) = unbounded \<longrightarrow> has_neg_infty_cycle make_pair \<E> \<c> \<u>)
        \<and> (return (ns_loop s) = success \<longrightarrow> is_Opt b (ns_flow_of (ns_loop s)))"
    proof (cases s rule: ns_loop_cases)
      case 1
      have loop: "ns_loop s = ns_optimal s" using ns_loop_simps_without_dom(1)[OF 1] .
      have opt: "is_Opt b (ns_flow_of s)" using ns_success_optimal[OF inv 1] .
      show ?thesis using loop opt by (simp add: ns_optimal_def)
    next
      case 2
      have loop: "ns_loop s = ns_unbounded_upd s" using ns_loop_simps_without_dom(2)[OF 2] .
      have cyc: "has_neg_infty_cycle make_pair \<E> \<c> \<u>" using ns_unbounded_neg_cycle[OF inv 2] .
      show ?thesis using loop cyc by (simp add: ns_unbounded_upd_def)
    next
      case 3
      have inv': "ns_invar (ns_flip_upd s)" using ns_flip_preservation(1)[OF inv 3] .
      have loop: "ns_loop s = ns_loop (ns_flip_upd s)" using ns_loop_simps(3)[OF IH(1) 3] .
      show ?thesis using IH(2)[OF 3] inv' loop by (simp add: comp_def)
    next
      case 4
      have inv': "ns_invar (ns_pivot_upd s)" using ns_pivot_preservation(1)[OF inv 4] .
      have loop: "ns_loop s = ns_loop (ns_pivot_upd s)" using ns_loop_simps(4)[OF IH(1) 4] .
      show ?thesis using IH(3)[OF 4] inv' loop by (simp add: comp_def)
    qed
  qed
qed

text \<open>\<^bold>\<open>Total correctness.\<close> For every state meeting the loop invariant the algorithm terminates, and
      its terminal flag is faithful: @{const unbounded} exhibits a negative infinite-capacity cycle
      (so the instance has no finite optimum), and @{const success} certifies that the returned flow
      is a minimum-cost @{term b}-flow.\<close>

theorem ns_loop_correct:
  assumes inv: "ns_invar s"
  shows "ns_loop_dom s"
    and "return (ns_loop s) = unbounded \<Longrightarrow> has_neg_infty_cycle make_pair \<E> \<c> \<u>"
    and "return (ns_loop s) = success \<Longrightarrow> is_Opt b (ns_flow_of (ns_loop s))"
proof -
  show dom: "ns_loop_dom s" using ns_loop_dom_of_invar[OF inv] .
  have aux: "(return (ns_loop s) = unbounded \<longrightarrow> has_neg_infty_cycle make_pair \<E> \<c> \<u>)
           \<and> (return (ns_loop s) = success \<longrightarrow> is_Opt b (ns_flow_of (ns_loop s)))"
    using ns_loop_return_correct_aux[OF dom] inv by simp
  show "return (ns_loop s) = unbounded \<Longrightarrow> has_neg_infty_cycle make_pair \<E> \<c> \<u>" using aux by blast
  show "return (ns_loop s) = success \<Longrightarrow> is_Opt b (ns_flow_of (ns_loop s))" using aux by blast
qed

end

section \<open>A constructed initial state\<close>

text \<open>The correctness theorem @{thm [source] network_simplex.ns_loop_correct} presupposes an
      input state satisfying the seven-part loop invariant @{const network_simplex.ns_invar}. We
      package that presupposition as a locale extending @{locale network_simplex_spec}. Rather than
      bundling it as @{const network_simplex.ns_invar} applied to an assembled state, we assume
      exactly the individual properties the seven starting components must have --- the flow store
      @{term init_flow}, the potential store @{term init_pot}, the abstract tree @{term init_tree},
      the parent-edge array @{term init_parent}, the direction array @{term init_dir}, the edge-state
      tag array @{term init_edge_state}, and the entering-edge selector
      @{term init_sel}:
      \<^item> \<^bold>\<open>data-structure well-formedness\<close> --- each store meets its array/set/selector invariant and the
        abstract tree is a valid arborescence (the eight \<open>init_\<dots>_invar\<close>/\<open>init_pot_valid\<close> facts);
      \<^item> \<^bold>\<open>feasible \<open>b\<close>-flow\<close> --- @{term init_flow} decodes to a flow respecting the capacity bounds and
        conserving the balances @{term b} (@{term init_bflow});
      \<^item> \<^bold>\<open>spanning-tree partition\<close> --- @{term \<open>\<E>\<close>} splits disjointly into the tree edges
        @{term \<open>parent_lookup init_parent ` (\<V> - {r})\<close>}, @{term L} and @{term U}, the tree spanning
        and rooted at @{term r} (@{term init_partition});
      \<^item> \<^bold>\<open>flow fits the partition\<close> --- @{term L}-edges carry zero flow, @{term U}-edges are saturated
        (@{term init_flow_fits});
      \<^item> \<^bold>\<open>potential fits the partition\<close> --- root potential @{term 0}, zero reduced cost on tree edges
        (@{term init_pot_fits});
      \<^item> \<^bold>\<open>strict feasibility on the tree\<close> --- for every non-root vertex, an upward parent edge
        (@{term \<open>dir_lookup init_dir v\<close>}) is strictly below capacity, a downward one carries strictly
        positive flow (@{term init_strict});
      \<^item> \<^bold>\<open>array $\leftrightarrow$ tree correspondence\<close> --- every parent edge is a graph edge oriented consistently with the
        direction flag, its other endpoint is the predecessor towards the root, and the concrete
        parent array denotes exactly the abstract arborescence (@{term init_tree_corr}).
      These are the componentwise unfoldings of the seven @{const network_simplex.ns_invar}
      conjuncts, with the state selectors replaced by the fixed components --- so the assembled state
      satisfies the packaged invariant.\<close>


text \<open>The initial-basis specification locale fixes the seven starting components and
      builds the concrete starting state @{term init_state}. It carries no assumptions.\<close>

locale network_simplex_init_spec =
  network_simplex_spec where flow_lookup = flow_lookup and pot_lookup = pot_lookup
    and parent_lookup = parent_lookup and dir_lookup = dir_lookup and es_lookup = es_lookup
    and sel_select = sel_select and swap_edge = swap_edge
  for flow_lookup :: "'farr \<Rightarrow> 'edge \<Rightarrow> ('n::linordered_idom)" and pot_lookup :: "'parr \<Rightarrow> 'a \<Rightarrow> 'p"
    and parent_lookup :: "'pearr \<Rightarrow> 'a \<Rightarrow> 'edge" and dir_lookup :: "'darr \<Rightarrow> 'a \<Rightarrow> bool"
    and es_lookup :: "'earr \<Rightarrow> 'edge \<Rightarrow> edge_tag"
    and sel_select :: "'selector \<Rightarrow> 'parr \<Rightarrow> 'earr \<Rightarrow> ('edge \<times> bool \<times> 'r \<times> 'selector) option"
    and swap_edge :: "'arbor \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'arbor" +
  fixes init_flow :: "'farr" and init_pot :: "'parr" and init_tree :: "'arbor"
    and init_parent :: "'pearr" and init_dir :: "'darr" and init_edge_state :: "'earr"
    and init_sel :: "'selector"
begin

text \<open>The constructed starting state, assembled from the fixed components with the loop still running.\<close>

definition "init_state \<equiv>
  \<lparr> current_flow = init_flow, potentials = init_pot,
    spanning_tree = init_tree, parent_edge = init_parent,
    edge_dir = init_dir, edge_state = init_edge_state,
    edge_sel = init_sel,
    return = notyetterm \<rparr>"

end

text \<open>The initial-basis proof locale adds the well-formedness / feasibility assumptions on
      the fixed components and derives total correctness for the constructed state.\<close>

locale network_simplex_init = network_simplex + network_simplex_init_spec +
  assumes
      init_flow_invar:   "flow_invar init_flow"
  and init_pot_valid:    "pot_valid init_pot"
  and init_parent_invar: "parent_invar init_parent"
  and init_dir_invar:    "dir_invar init_dir"
  and init_edge_state_invar: "es_invar init_edge_state"
  and init_sel_invar:    "sel_invar init_sel"
  and init_tree_invar:   "arborescense_invar init_tree"
  and init_bflow:        "(h \<circ> flow_lookup init_flow) is b flow"
  and init_partition:
        "spanning_tree_partition r (parent_lookup init_parent ` (\<V> - {r}))
             ({e \<in> \<E>. fst e \<noteq> snd e \<and> es_lookup init_edge_state e = InL} \<union> ns_selfloops_L)
             ({e \<in> \<E>. fst e \<noteq> snd e \<and> es_lookup init_edge_state e = InU} \<union> ns_selfloops_U)"
  and init_flow_fits:
        "flow_fits_spanning_tree_partition (parent_lookup init_parent ` (\<V> - {r}))
             {e \<in> \<E>. fst e \<noteq> snd e \<and> es_lookup init_edge_state e = InL}
             {e \<in> \<E>. fst e \<noteq> snd e \<and> es_lookup init_edge_state e = InU}
             (h \<circ> flow_lookup init_flow)"
  and init_pot_fits:
        "potential_fits_spanning_tree_partition r (parent_lookup init_parent ` (\<V> - {r}))
             (abstract_pot init_pot)"
  and init_strict:
        "\<forall> v \<in> \<V> - {r}.
           if dir_lookup init_dir v
           then ereal (h (flow_lookup init_flow (parent_lookup init_parent v))) < \<u> (parent_lookup init_parent v)
           else flow_lookup init_flow (parent_lookup init_parent v) > 0"
  and init_tree_corr:
        "(\<forall> v \<in> \<V> - {r}.
             parent_lookup init_parent v \<in> \<E>
           \<and> (if dir_lookup init_dir v then fst (parent_lookup init_parent v) = v
                                        else snd (parent_lookup init_parent v) = v)
           \<and> (\<exists> q. distinct (v # (if dir_lookup init_dir v then snd (parent_lookup init_parent v)
                                                            else fst (parent_lookup init_parent v)) # q)
                   \<and> walk_betw (abstract_arborescense init_tree) v
                       (v # (if dir_lookup init_dir v then snd (parent_lookup init_parent v)
                                                       else fst (parent_lookup init_parent v)) # q) r))
         \<and> (\<lambda> e. {fst e, snd e}) ` (parent_lookup init_parent ` (\<V> - {r}))
             = abstract_arborescense init_tree"
  and init_selfloop:
        "\<forall> e \<in> \<E>. fst e = snd e \<longrightarrow> (0 \<le> \<c> e \<longrightarrow> flow_lookup init_flow e = 0)
                                  \<and> (\<c> e < 0 \<longrightarrow> ereal (h (flow_lookup init_flow e)) = \<u> e)"
begin

text \<open>The assembled state satisfies the packaged loop invariant: the componentwise assumptions above
      are exactly the unfoldings of the seven @{const network_simplex.ns_invar} conjuncts (the
      only bridging step is a case split on the direction flag inside the tree-correspondence
      conjunct).\<close>

lemma init_state_invar: "ns_invar init_state"
  using init_flow_invar init_pot_valid init_parent_invar init_dir_invar
        init_edge_state_invar init_sel_invar init_tree_invar
        init_bflow init_partition init_flow_fits init_pot_fits init_strict init_tree_corr
        init_selfloop
  by (auto simp: ns_invar_def ns_invar_impl_def ns_invar_bflow_def ns_invar_partition_def
                 ns_invar_flow_fits_def ns_invar_pot_fits_def ns_invar_strict_def ns_invar_tree_def
                 ns_invar_selfloop_def ns_L_of_def ns_U_of_def comp_def
                 par_up_def par_edge_def par_vx_def init_state_def
           split: if_splits)

lemma init_state_notyetterm: "return init_state = notyetterm"
  by (simp add: init_state_def)

text \<open>Total correctness specialised to the constructed initial state: the loop terminates on it, an
      @{term unbounded} result witnesses an infinite-capacity negative circuit, and a @{term success}
      result is a minimum-cost \<open>b\<close>-flow.\<close>

theorem network_simplex_correct:
  "ns_loop_dom init_state"
  "return (ns_loop init_state) = unbounded \<Longrightarrow> has_neg_infty_cycle make_pair \<E> \<c> \<u>"
  "return (ns_loop init_state) = success \<Longrightarrow> is_Opt b (ns_flow_of (ns_loop init_state))"
  using ns_loop_correct[OF init_state_invar] by blast+

end

end