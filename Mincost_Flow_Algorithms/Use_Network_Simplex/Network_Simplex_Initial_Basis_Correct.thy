theory Network_Simplex_Initial_Basis_Correct
  imports Network_Simplex_Initial_Basis
begin

section \<open>Correctness of the initial-basis construction\<close>

text \<open>We prove the construction correct in a context that adds the only genuine hypothesis on the
      frozen input flow @{term flow_list}: it is \<^emph>\<open>capacity-complying\<close> --- every real edge carries a
      non-negative flow that does not exceed its (finite) capacity. The \<open>- 1\<close> capacity encodes
      an infinite capacity, which no flow can exceed, so that case carries no constraint. We also
      assume the instance is \<^emph>\<open>balanced\<close> --- the target balances sum to zero (\<open>sum b_list = 0\<close>) --- which
      is the feasibility precondition making the root vertex balance automatically (an unbalanced
      instance admits no \<open>b\<close>-flow at all). One further hypothesis, acyclicity of @{term flow_list}
      (needed for the free edges to form a forest, L1), will be added as the tree-shaped obligations
      demand it.\<close>

locale initial_basis_correct =
  initial_basis_lists where capacity_list = capacity_list and h = h
  for capacity_list :: "('n :: linordered_idom) list" and h :: "'n \<Rightarrow> real" +
  assumes flow_nonneg: "\<And>e. e < m \<Longrightarrow> 0 \<le> flow_list ! e"
      and flow_le_cap: "\<And>e. e < m \<Longrightarrow> capacity_list ! e \<noteq> - 1 \<Longrightarrow> flow_list ! e \<le> capacity_list ! e"
      and balance_sum_zero: "sum_list b_list = 0"
begin

subsection \<open>Pass A records each real edge's status faithfully\<close>

text \<open>The classification a single Pass-A step assigns to edge @{term e}: at its lower bound when it
      carries no flow, at its (finite) upper bound when saturated, and \<^emph>\<open>free\<close> (a tree candidate)
      otherwise. These three cases are exactly @{const passA_step}'s inner @{term st}.\<close>

definition classify :: "'n list \<Rightarrow> nat \<Rightarrow> edge_tag" where
  "classify fl e = (if fl ! e = 0 then InL
                 else if capacity_list ! e \<noteq> - 1 \<and> fl ! e = capacity_list ! e then InU
                 else InTree)"

text \<open>The first component of the Pass-A tuple is the status array; a step overwrites exactly its own
      edge's slot with that edge's @{const classify}.  (A nested wildcard tuple pattern
      \<open>case s of (est, _, _, _, _, _) \<Rightarrow> est\<close> is definitionally \<open>fst s\<close>; we phrase the
      projections with @{const fst} to keep the rewriting robust.)\<close>

lemma case6_is_fst: "(case s of (est, _, _, _, _, _) \<Rightarrow> est) = fst s"
  by (cases s) auto

lemma passA_step_fst: "fst (passA_step fl e s) = (fst s)[e := classify fl e]"
  by (cases s) (auto simp: passA_step_def classify_def Let_def)

lemma passA_fold_fst:
  assumes "sized s" "e < m"
  shows "fst (fold (passA_step fl) xs s) ! e = (if e \<in> set xs then classify fl e else fst s ! e)"
  using assms
proof (induct xs arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have sz: "sized (passA_step fl a s)" using Cons.prems(1) by (rule passA_step_sized)
  have len: "length (fst s) = m" using Cons.prems(1) by (cases s) (simp add: sized_def)
  show ?case
    using Cons.hyps[OF sz Cons.prems(2)] Cons.prems(2) len
    by (simp add: passA_step_fst nth_list_update)
qed

lemma edge_state_nth:
  assumes "e < m"
  shows "edge_state fl ! e = classify fl e"
proof -
  have sz0: "sized (replicate m InL, replicate (Suc vcount) (0::'n), csr_edges out_csr, out_lo,
                csr_edges in_csr, in_lo)"
    by (simp add: sized_def length_out_lo length_in_lo out_csr_eq in_csr_eq)
  have "edge_state fl = fst (passA fl)" by (simp add: edge_state_def case6_is_fst)
  then show ?thesis
    using passA_fold_fst[OF sz0 assms, where xs = "[0..<m]"] assms
    by (simp add: passA_def)
qed

subsection \<open>Status characterisation: the L / U / free partition of the real edges\<close>

text \<open>Under capacity-compliance the three tags mean exactly what the simplex partition needs: an
      @{const InTree} (free) edge is \<^emph>\<open>strictly interior in both directions\<close>
      (\<open>0 < f\<close> and \<open>f < u\<close>, the \<open>- 1\<close> case being genuinely unbounded above),
      which is the residual-in-both-directions fact underpinning ``free edges form a forest'' (L1). An
      @{const InL} edge carries no flow; an @{const InU} edge is saturated at a finite positive
      capacity. Every real edge is exactly one of the three.\<close>

text \<open>@{const edge_state}'s \<open>InTree\<close> characterisation and @{const is_free} need capacity-compliance
      of \<open>fl\<close>; they are stated in the \<open>fl\<close>-fixing context (\<open>flow_props\<close>) near the forest lemmas below,
      not here at locale level.\<close>

lemma edge_state_InL_iff:
  assumes "e < m"
  shows "edge_state fl ! e = InL \<longleftrightarrow> fl ! e = 0"
  by (simp add: edge_state_nth[OF assms] classify_def)

lemma edge_state_InU_iff:
  assumes "e < m"
  shows "edge_state fl ! e = InU \<longleftrightarrow>
           fl ! e \<noteq> 0 \<and> capacity_list ! e \<noteq> - 1 \<and> fl ! e = capacity_list ! e"
  by (auto simp: edge_state_nth[OF assms] classify_def)

lemma edge_state_cases:
  assumes "e < m"
  shows "edge_state fl ! e = InL \<or> edge_state fl ! e = InU \<or> edge_state fl ! e = InTree"
  by (simp add: edge_state_nth[OF assms] classify_def)

subsection \<open>Pass A computes the achieved balance (excess), and the imbalance\<close>

text \<open>The second Pass-A component is the excess accumulator.  A step adds the edge's flow at its head
      and subtracts it at its tail; a self-loop cancels.  Pointwise this is a signed indicator update.\<close>

lemma case6_snd: "(case s of (_, exc, _, _, _, _) \<Rightarrow> exc) = fst (snd s)"
  by (cases s) auto

lemma passA_step_exc:
  "fst (snd (passA_step fl e s)) =
     (let x = fst_list ! e; y = snd_list ! e; f = fl ! e; exc = fst (snd s)
      in (exc[y := exc ! y + f])[x := (exc[y := exc ! y + f]) ! x - f])"
  by (cases s) (auto simp: passA_step_def Let_def)

lemma exc_upd_nth:
  assumes "v < length (exc :: 'n list)"
  shows "((exc[y := exc ! y + f])[x := (exc[y := exc ! y + f]) ! x - f]) ! v =
          exc ! v + (if y = v then f else 0) - (if x = v then f else 0)"
  using assms by (cases "x = v"; cases "y = v") (auto simp: nth_list_update)

text \<open>Hence over the whole edge sweep the excess at @{term v} is the signed net flow into @{term v}:
      the flow on edges \<^emph>\<open>headed\<close> at @{term v} minus the flow on edges \<^emph>\<open>tailed\<close> at @{term v} --- i.e.
      the balance the frozen flow \<^emph>\<open>achieves\<close> at @{term v} (@{text "b\<^sub>0 v = - ex flow_list v"}).\<close>

lemma passA_fold_exc:
  assumes "sized s" "v < Suc vcount"
  shows "fst (snd (fold (passA_step fl) xs s)) ! v =
           fst (snd s) ! v
           + (\<Sum>e\<leftarrow>xs. (if snd_list ! e = v then fl ! e else 0))
           - (\<Sum>e\<leftarrow>xs. (if fst_list ! e = v then fl ! e else 0))"
  using assms
proof (induct xs arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have sz: "sized (passA_step fl a s)" using Cons.prems(1) by (rule passA_step_sized)
  have len: "length (fst (snd s)) = Suc vcount"
    using Cons.prems(1) by (cases s) (simp add: sized_def)
  have step: "fst (snd (passA_step fl a s)) ! v =
                fst (snd s) ! v + (if snd_list ! a = v then fl ! a else 0)
                                - (if fst_list ! a = v then fl ! a else 0)"
    using len Cons.prems(2)
    by (simp add: passA_step_exc Let_def exc_upd_nth)
  show ?case
    using Cons.hyps[OF sz Cons.prems(2)] step
    by (simp add: algebra_simps)
qed

lemma excess_nth:
  assumes "v < Suc vcount"
  shows "excess ! v =
           (\<Sum>e\<leftarrow>[0..<m]. (if snd_list ! e = v then flow_list ! e else 0))
         - (\<Sum>e\<leftarrow>[0..<m]. (if fst_list ! e = v then flow_list ! e else 0))"
proof -
  have sz0: "sized (replicate m InL, replicate (Suc vcount) (0::'n), csr_edges out_csr, out_lo,
                csr_edges in_csr, in_lo)"
    by (simp add: sized_def length_out_lo length_in_lo out_csr_eq in_csr_eq)
  have "excess = fst (snd (passA flow_list))" by (simp add: excess_def case6_snd)
  then show ?thesis
    using passA_fold_exc[OF sz0 assms, where xs = "[0..<m]"] assms
    by (simp add: passA_def del: replicate_Suc)
qed

text \<open>The imbalance is the achieved balance minus the target balance --- the signed amount that
      @{term v}'s artificial edge must ship toward the root.  It is @{const excess} transformed in
      place by one vertex sweep, subtracting @{const b_lookup} at each real vertex; the root slot
      (index @{term vcount}, outside the sweep range) is untouched.\<close>

lemma fold_add_nth:
  assumes "w < length init" "distinct xs"
  shows "fold (\<lambda>v arr. arr[v := arr ! v + g v]) xs init ! w =
           (if w \<in> set xs then init ! w + g w else init ! w)"
  using assms
proof (induct xs arbitrary: init)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have IH: "fold (\<lambda>v arr. arr[v := arr ! v + g v]) xs (init[a := init ! a + g a]) ! w =
              (if w \<in> set xs then (init[a := init ! a + g a]) ! w + g w
               else (init[a := init ! a + g a]) ! w)"
    using Cons.hyps[of "init[a := init ! a + g a]"] Cons.prems by simp
  show ?case
  proof (cases "w = a")
    case True
    then show ?thesis using Cons.prems IH by (auto simp: nth_list_update)
  next
    case False
    then show ?thesis using Cons.prems IH by (auto simp: nth_list_update_neq)
  qed
qed

lemma imbalance_nth:
  assumes "v < vcount"
  shows "imbalance ! v = excess ! v + b_lookup v"
  using fold_add_nth[of v excess "[0..<vcount]" b_lookup] assms
  by (simp add: imbalance_def)

lemma imbalance_root: "imbalance ! vcount = excess ! vcount"
  using fold_add_nth[of vcount excess "[0..<vcount]" b_lookup]
  by (simp add: imbalance_def)

subsection \<open>Conservation: the imbalances sum to zero, so the root balances\<close>

text \<open>Both endpoints of a real edge are genuine vertices, hence below @{term \<open>Suc vcount\<close>} --- every
      edge's flow is counted once as an inflow and once as an outflow across the vertex range.\<close>

lemma fst_lt_Suc_vcount: "e < m \<Longrightarrow> fst_list ! e < Suc vcount"
  using fst_list_nth_vertex vs_less_vcount by (simp add: less_Suc_eq)

lemma snd_lt_Suc_vcount: "e < m \<Longrightarrow> snd_list ! e < Suc vcount"
  using snd_list_nth_vertex vs_less_vcount by (simp add: less_Suc_eq)

text \<open>The excess as a finite-set sum (rather than a list sum), so Fubini applies.\<close>

lemma excess_nth_sum:
  assumes "v < Suc vcount"
  shows "excess ! v =
           (\<Sum>e\<in>{0..<m}. (if snd_list ! e = v then flow_list ! e else 0))
         - (\<Sum>e\<in>{0..<m}. (if fst_list ! e = v then flow_list ! e else 0))"
  using excess_nth[OF assms]
  by (simp add: interv_sum_list_conv_sum_set_nat)

lemma sum_indicator_snd:
  assumes "e < m"
  shows "(\<Sum>v\<in>{0..<Suc vcount}. if snd_list ! e = v then flow_list ! e else 0) = flow_list ! e"
proof -
  have "snd_list ! e \<in> {0..<Suc vcount}" using snd_lt_Suc_vcount[OF assms] by simp
  thus ?thesis by (simp add: sum.delta')
qed

lemma sum_indicator_fst:
  assumes "e < m"
  shows "(\<Sum>v\<in>{0..<Suc vcount}. if fst_list ! e = v then flow_list ! e else 0) = flow_list ! e"
proof -
  have "fst_list ! e \<in> {0..<Suc vcount}" using fst_lt_Suc_vcount[OF assms] by simp
  thus ?thesis by (simp add: sum.delta')
qed

text \<open>Summing the achieved balance over all augmented vertices telescopes to
      @{term \<open>(\<Sum>e\<in>{0..<m}. flow_list ! e) - (\<Sum>e\<in>{0..<m}. flow_list ! e)\<close>}, hence zero: the total
      excess of any flow is zero (Fubini over the vertex/edge double sum).\<close>

lemma sum_excess_zero: "(\<Sum>v\<in>{0..<Suc vcount}. excess ! v) = 0"
proof -
  have "(\<Sum>v\<in>{0..<Suc vcount}. excess ! v)
      = (\<Sum>v\<in>{0..<Suc vcount}. (\<Sum>e\<in>{0..<m}. if snd_list ! e = v then flow_list ! e else 0))
      - (\<Sum>v\<in>{0..<Suc vcount}. (\<Sum>e\<in>{0..<m}. if fst_list ! e = v then flow_list ! e else 0))"
    by (simp add: excess_nth_sum sum_subtractf)
  also have "(\<Sum>v\<in>{0..<Suc vcount}. (\<Sum>e\<in>{0..<m}. if snd_list ! e = v then flow_list ! e else 0))
      = (\<Sum>e\<in>{0..<m}. flow_list ! e)"
    by (subst sum.swap) (rule sum.cong[OF refl], rule sum_indicator_snd, simp)
  also have "(\<Sum>v\<in>{0..<Suc vcount}. (\<Sum>e\<in>{0..<m}. if fst_list ! e = v then flow_list ! e else 0))
      = (\<Sum>e\<in>{0..<m}. flow_list ! e)"
    by (subst sum.swap) (rule sum.cong[OF refl], rule sum_indicator_fst, simp)
  finally show ?thesis by simp
qed

text \<open>A scatter into an array with \<^emph>\<open>distinct\<close> keys writes each slot at most once; summing the result
      adds, per key, its written value minus the slot's initial content (over a group so the ordinary
      @{const sum_list} update law holds --- the library's is restricted to truncated subtraction).\<close>

lemma sum_list_update_group:
  fixes xs :: "'a::ab_group_add list"
  assumes "k < length xs"
  shows "sum_list (xs[k := x]) = sum_list xs - xs ! k + x"
  using assms
proof (induct xs arbitrary: k)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  show ?case
  proof (cases k)
    case 0
    then show ?thesis by simp
  next
    case (Suc j)
    then show ?thesis using Cons by simp
  qed
qed

lemma foldl_scatter_sum_list:
  fixes init :: "'a::ab_group_add list"
  assumes "distinct (map fst ps)" "\<forall>(k,x)\<in>set ps. k < length init"
  shows "sum_list (foldl (\<lambda>arr (k, x). arr[k := x]) init ps)
           = sum_list init + (\<Sum>(k,x)\<leftarrow>ps. x - init ! k)"
  using assms
proof (induct ps arbitrary: init)
  case Nil
  then show ?case by simp
next
  case (Cons kx ps)
  obtain k x where kx: "kx = (k, x)" by (cases kx)
  have klt: "k < length init" using Cons.prems(2) kx by auto
  have dist: "distinct (map fst ps)" and knotin: "k \<notin> set (map fst ps)"
    using Cons.prems(1) kx by auto
  have rng: "\<forall>(k',x')\<in>set ps. k' < length (init[k := x])" using Cons.prems(2) kx by auto
  have eqmap: "(\<Sum>(k',x')\<leftarrow>ps. x' - init[k := x] ! k') = (\<Sum>(k',x')\<leftarrow>ps. x' - init ! k')"
  proof (intro arg_cong[where f = sum_list] map_cong refl)
    fix p assume "p \<in> set ps"
    then have "fst p \<noteq> k" using knotin by (metis image_eqI set_map)
    thus "(case p of (k',x') \<Rightarrow> x' - init[k := x] ! k') = (case p of (k',x') \<Rightarrow> x' - init ! k')"
      by (cases p) (simp add: nth_list_update_neq)
  qed
  have "sum_list (foldl (\<lambda>arr (k, x). arr[k := x]) (init[k := x]) ps)
        = sum_list (init[k := x]) + (\<Sum>(k',x')\<leftarrow>ps. x' - init[k := x] ! k')"
    using Cons.hyps[OF dist rng] .
  also have "\<dots> = sum_list init + x - init ! k + (\<Sum>(k',x')\<leftarrow>ps. x' - init ! k')"
    by (simp add: sum_list_update_group klt eqmap)
  finally show ?case using kx by simp
qed

text \<open>Applied to @{const b_arr}: the balance array (scattered from the distinct vertex names) sums to
      @{term \<open>sum_list b_list\<close>}.\<close>

lemma sum_b_arr: "sum_list b_arr = sum_list b_list"
proof -
  have leq: "length vs_list = length b_list" using length_b length_vs_list by simp
  have dist: "distinct (map fst (zip vs_list b_list))"
    using distinct_vs_list leq by (simp add: map_fst_zip)
  have rng: "\<forall>(k,x)\<in>set (zip vs_list b_list). k < length (replicate (Suc vcount) (0::'n))"
  proof (clarify)
    fix k x assume "(k, x) \<in> set (zip vs_list b_list)"
    then have "k \<in> set vs_list" using set_zip_leftD by fastforce
    thus "k < length (replicate (Suc vcount) (0::'n))" using vs_less_vcount by fastforce
  qed
  have "sum_list b_arr = sum_list (replicate (Suc vcount) (0::'n))
          + (\<Sum>(k,x)\<leftarrow>zip vs_list b_list. x - replicate (Suc vcount) (0::'n) ! k)"
    unfolding b_arr_def using foldl_scatter_sum_list[OF dist rng] .
  also have "(\<Sum>(k,x)\<leftarrow>zip vs_list b_list. x - replicate (Suc vcount) (0::'n) ! k)
           = (\<Sum>(k,x)\<leftarrow>zip vs_list b_list. x)"
  proof (intro arg_cong[where f = sum_list] map_cong refl)
    fix p assume "p \<in> set (zip vs_list b_list)"
    then have "fst p \<in> set vs_list" using set_zip_leftD by (metis prod.collapse)
    then have "fst p < vcount" by (simp add: vs_less_vcount)
    thus "(case p of (k,x) \<Rightarrow> x - replicate (Suc vcount) (0::'n) ! k) = (case p of (k,x) \<Rightarrow> x)"
      by (cases p) (simp del: replicate_Suc add: nth_replicate)
  qed
  also have "(\<Sum>(k,x)\<leftarrow>zip vs_list b_list. x) = sum_list b_list"
    using leq by (simp add: case_prod_beta map_snd_zip cong: map_cong)
  finally show ?thesis by (simp add: sum_list_replicate)
qed

text \<open>The array now has a slot for the artificial root as well, so the sum over its indices runs to
      @{term \<open>Suc vcount\<close>}.  That extra slot holds @{term \<open>0::'n\<close>} (@{thm b_lookup_root}), hence the
      sum over the real vertex names is unchanged.\<close>

lemma sum_b_lookup: "(\<Sum>v\<in>{0..<vcount}. b_lookup v) = sum_list b_list"
proof -
  have "(\<Sum>v\<in>{0..<Suc vcount}. b_lookup v) = (\<Sum>v\<in>{0..<length b_arr}. b_arr ! v)"
    by (simp add: b_lookup_def length_b_arr)
  also have "\<dots> = sum_list b_arr" by (simp add: sum_list_sum_nth atLeast0LessThan)
  also have "\<dots> = sum_list b_list" by (rule sum_b_arr)
  finally have all: "(\<Sum>v\<in>{0..<Suc vcount}. b_lookup v) = sum_list b_list" .
  have "(\<Sum>v\<in>{0..<Suc vcount}. b_lookup v) = (\<Sum>v\<in>{0..<vcount}. b_lookup v) + b_lookup vcount"
    by simp
  thus ?thesis using all b_lookup_root by simp
qed

text \<open>Hence the imbalances telescope to @{term \<open>- sum_list b_list\<close>}; with the instance balanced
      (@{thm balance_sum_zero}) they sum to zero, so the artificial edges ship a globally consistent
      amount and the root vertex balances automatically.\<close>

lemma sum_imbalance: "(\<Sum>v\<in>{0..<Suc vcount}. imbalance ! v) = sum_list b_list"
proof -
  have split: "(\<Sum>v\<in>{0..<Suc vcount}. imbalance ! v)
      = (\<Sum>v\<in>{0..<vcount}. imbalance ! v) + imbalance ! vcount"
    by (simp add: sum.atLeast0_lessThan_Suc)
  have low: "(\<Sum>v\<in>{0..<vcount}. imbalance ! v)
      = (\<Sum>v\<in>{0..<vcount}. excess ! v) + (\<Sum>v\<in>{0..<vcount}. b_lookup v)"
  proof -
    have "(\<Sum>v\<in>{0..<vcount}. imbalance ! v) = (\<Sum>v\<in>{0..<vcount}. excess ! v + b_lookup v)"
      by (rule sum.cong[OF refl]) (simp add: imbalance_nth)
    thus ?thesis by (simp add: sum.distrib)
  qed
  have exc0: "(\<Sum>v\<in>{0..<vcount}. excess ! v) + excess ! vcount = 0"
    using sum_excess_zero by (simp add: sum.atLeast0_lessThan_Suc)
  show ?thesis
    using split low imbalance_root exc0 by (simp add: sum_b_lookup)
qed

lemma sum_imbalance_zero: "(\<Sum>v\<in>{0..<Suc vcount}. imbalance ! v) = 0"
  using sum_imbalance balance_sum_zero by linarith

section \<open>The free-edge DFS: sizedness and termination\<close>

text \<open>We equip the recursive @{const build_dfs} with the standard call-abstraction scaffold (call
      conditions, per-call state updates, and the derived case / simp / induction / domain-intro
      rules), then use it to show that @{const build_dfs} preserves the vertex-array lengths
      (@{const dfs_sized}) and --- under a well-formedness invariant and the fact that every scanned
      free-edge slot holds a real edge id (so a discovered neighbour is a genuine vertex) --- that the
      traversal terminates.\<close>

subsection \<open>Call-abstraction scaffold\<close>

definition "bd_call1_conds fl s \<longleftrightarrow> (case ds_stk s of [] \<Rightarrow> False | (v,oc,ic)#rest \<Rightarrow> oc < free_out_hi fl ! v)"
definition "bd_upd1 fl s = (case ds_stk s of (v,oc,ic)#rest \<Rightarrow>
     (let e = free_out_edges fl ! oc; w = snd_list ! e; s1 = s\<lparr>ds_stk := (v, Suc oc, ic) # rest\<rparr>
      in if ds_seen s ! w then s1 else dfs_discover s1 v w e))"
definition "bd_call2_conds fl s \<longleftrightarrow> (case ds_stk s of [] \<Rightarrow> False | (v,oc,ic)#rest \<Rightarrow> \<not> oc < free_out_hi fl ! v \<and> ic < free_in_hi fl ! v)"
definition "bd_upd2 fl s = (case ds_stk s of (v,oc,ic)#rest \<Rightarrow>
     (let e = free_in_edges fl ! ic; w = fst_list ! e; s1 = s\<lparr>ds_stk := (v, oc, Suc ic) # rest\<rparr>
      in if ds_seen s ! w then s1 else dfs_discover s1 v w e))"
definition "bd_call3_conds fl s \<longleftrightarrow> (case ds_stk s of [] \<Rightarrow> False | (v,oc,ic)#rest \<Rightarrow> \<not> oc < free_out_hi fl ! v \<and> \<not> ic < free_in_hi fl ! v)"
definition "bd_upd3 s = (case ds_stk s of (v,oc,ic)#rest \<Rightarrow> dfs_finish s v rest)"
definition "bd_ret_conds s \<longleftrightarrow> ds_stk s = []"

lemma bd_cases:
  assumes "bd_call1_conds fl s \<Longrightarrow> P" "bd_call2_conds fl s \<Longrightarrow> P" "bd_call3_conds fl s \<Longrightarrow> P" "bd_ret_conds s \<Longrightarrow> P"
  shows P
proof (cases "ds_stk s")
  case Nil
  thus ?thesis using assms(4) by (simp add: bd_ret_conds_def)
next
  case (Cons f rest)
  obtain v oc ic where "f = (v, oc, ic)" by (cases f)
  thus ?thesis using Cons assms
    by (cases "oc < free_out_hi fl ! v"; cases "ic < free_in_hi fl ! v")
       (auto simp: bd_call1_conds_def bd_call2_conds_def bd_call3_conds_def)
qed

lemma bd_simps:
  assumes "build_dfs_dom (fl, s)"
  shows "bd_call1_conds fl s \<Longrightarrow> build_dfs fl s = build_dfs fl (bd_upd1 fl s)"
        "bd_call2_conds fl s \<Longrightarrow> build_dfs fl s = build_dfs fl (bd_upd2 fl s)"
        "bd_call3_conds fl s \<Longrightarrow> build_dfs fl s = build_dfs fl (bd_upd3 s)"
        "bd_ret_conds s \<Longrightarrow> build_dfs fl s = s"
  by (auto simp add: build_dfs_psimps[OF assms] Let_def
                     bd_call1_conds_def bd_upd1_def bd_call2_conds_def bd_upd2_def
                     bd_call3_conds_def bd_upd3_def bd_ret_conds_def
           split: list.splits prod.splits)

text \<open>The induction rule. @{const build_dfs} is now defined by handing the four Pass-A arrays to the
      array-indexed recursion @{const build_dfs_a}, so the raw induction principle ranges over those
      arrays while @{term P} is indexed by the flow. The arrays are constant throughout the descent,
      so it suffices to carry \<open>oe = free_out_edges fl \<dots> ih = free_in_hi fl\<close> as side conditions
      through the induction and discharge them at the end; the resulting rule is \<^emph>\<open>verbatim\<close> the one
      the flow-indexed recursion used to generate.\<close>

lemma bd_induct:
  assumes dom: "build_dfs_dom (fl, s)"
  assumes step: "\<And>fl s. \<lbrakk>build_dfs_dom (fl, s); bd_call1_conds fl s \<Longrightarrow> P fl (bd_upd1 fl s); bd_call2_conds fl s \<Longrightarrow> P fl (bd_upd2 fl s); bd_call3_conds fl s \<Longrightarrow> P fl (bd_upd3 s)\<rbrakk> \<Longrightarrow> P fl s"
  shows "P fl s"
proof -
  have gen: "build_dfs_a_dom (oe,oh,ie,ih,t) \<Longrightarrow> oe = free_out_edges fl \<longrightarrow> oh = free_out_hi fl \<longrightarrow> ie = free_in_edges fl \<longrightarrow> ih = free_in_hi fl \<longrightarrow> P fl t" for oe oh ie ih t
  proof (induction oe oh ie ih t rule: build_dfs_a.pinduct)
    case (1 oe oh ie ih t)
    show ?case
    proof (intro impI)
      assume e1: "oe = free_out_edges fl" and e2: "oh = free_out_hi fl" and e3: "ie = free_in_edges fl" and e4: "ih = free_in_hi fl"
      show "P fl t"
      proof (rule step)
        show "build_dfs_dom (fl, t)" using 1(1) e1 e2 e3 e4 by (simp add: build_dfs_dom_iff)
      next
        assume c: "bd_call1_conds fl t"
        show "P fl (bd_upd1 fl t)" using 1(2) e1 e2 e3 e4 c
          by (auto simp: bd_call1_conds_def bd_upd1_def Let_def split: list.splits prod.splits)
      next
        assume c: "bd_call2_conds fl t"
        show "P fl (bd_upd2 fl t)" using 1(3) e1 e2 e3 e4 c
          by (auto simp: bd_call2_conds_def bd_upd2_def Let_def split: list.splits prod.splits)
      next
        assume c: "bd_call3_conds fl t"
        show "P fl (bd_upd3 t)" using 1(4) e1 e2 e3 e4 c
          by (auto simp: bd_call3_conds_def bd_upd3_def Let_def split: list.splits prod.splits)
      qed
    qed
  qed
  show ?thesis
    using gen[of "free_out_edges fl" "free_out_hi fl" "free_in_edges fl" "free_in_hi fl" s] dom
    by (simp add: build_dfs_dom_iff)
qed

lemma bd_domintros:
  assumes "bd_call1_conds fl s \<Longrightarrow> build_dfs_dom (fl, bd_upd1 fl s)"
      and "bd_call2_conds fl s \<Longrightarrow> build_dfs_dom (fl, bd_upd2 fl s)"
      and "bd_call3_conds fl s \<Longrightarrow> build_dfs_dom (fl, bd_upd3 s)"
  shows "build_dfs_dom (fl, s)"
  unfolding build_dfs_dom_iff
  apply (rule build_dfs_a.domintros)
  using assms(1)[simplified bd_call1_conds_def bd_upd1_def build_dfs_dom_iff]
        assms(2)[simplified bd_call2_conds_def bd_upd2_def build_dfs_dom_iff]
        assms(3)[simplified bd_call3_conds_def bd_upd3_def build_dfs_dom_iff]
  by (auto simp: Let_def split: list.splits prod.splits if_splits)

subsection \<open>@{const build_dfs} preserves the vertex-array lengths\<close>

lemma bd_upd1_sized: "dfs_sized s \<Longrightarrow> bd_call1_conds fl s \<Longrightarrow> dfs_sized (bd_upd1 fl s)"
  by (auto simp: bd_upd1_def bd_call1_conds_def dfs_sized_def dfs_discover_def Let_def split: list.splits prod.splits)

lemma bd_upd2_sized: "dfs_sized s \<Longrightarrow> bd_call2_conds fl s \<Longrightarrow> dfs_sized (bd_upd2 fl s)"
  by (auto simp: bd_upd2_def bd_call2_conds_def dfs_sized_def dfs_discover_def Let_def split: list.splits prod.splits)

lemma bd_upd3_sized: "dfs_sized s \<Longrightarrow> bd_call3_conds fl s \<Longrightarrow> dfs_sized (bd_upd3 s)"
  by (auto simp: bd_upd3_def bd_call3_conds_def dfs_sized_def dfs_finish_def Let_def split: list.splits prod.splits)

lemma build_dfs_sized:
  assumes "build_dfs_dom (fl, s)" "dfs_sized s"
  shows "dfs_sized (build_dfs fl s)"
  using assms(2)
proof (induct rule: bd_induct[OF assms(1)])
  case IH: (1 fl s)
  show ?case
    apply (rule bd_cases[where s = s and fl = fl])
    by (auto intro!: IH(2-4) bd_upd1_sized bd_upd2_sized bd_upd3_sized IH(5)
             simp: bd_simps[OF IH(1)])
qed

subsection \<open>Termination under a well-formedness invariant\<close>

text \<open>A lexicographic measure decreases along every recursive call: discovering a fresh vertex lowers
      the count of unseen vertices; advancing a cursor without discovery lowers the total remaining
      cursor budget over the stack; finishing a vertex (both cursors exhausted, so its budget is
      already zero) shortens the stack.\<close>

definition dfs_unseen :: "'n dfs_state \<Rightarrow> nat" where
  "dfs_unseen s = card {v. v < Suc vcount \<and> \<not> ds_seen s ! v}"

definition dfs_budget :: "'n list \<Rightarrow> 'n dfs_state \<Rightarrow> nat" where
  "dfs_budget fl s = (\<Sum>(v,oc,ic)\<leftarrow>ds_stk s. (free_out_hi fl ! v - oc) + (free_in_hi fl ! v - ic))"

definition dfs_stklen :: "'n dfs_state \<Rightarrow> nat" where
  "dfs_stklen s = length (ds_stk s)"

definition dfs_meas :: "'n list \<Rightarrow> ('n dfs_state \<times> 'n dfs_state) set" where
  "dfs_meas fl = measures [dfs_unseen, dfs_budget fl, dfs_stklen]"

text \<open>The invariant carried through the recursion: the visited array has the fixed length, and every
      stack frame names a real vertex with cursors at or beyond their block starts.\<close>

definition dfs_wf :: "'n dfs_state \<Rightarrow> bool" where
  "dfs_wf s \<longleftrightarrow> length (ds_seen s) = Suc vcount \<and>
     (\<forall>(v,oc,ic)\<in>set (ds_stk s). v < vcount \<and> out_lo ! v \<le> oc \<and> in_lo ! v \<le> ic)"

lemma dfs_unseen_mark_lt:
  assumes len: "length seen = Suc vcount" and w: "w < Suc vcount" and un: "\<not> seen ! w"
  shows "card {x. x < Suc vcount \<and> \<not> seen[w := True] ! x} < card {x. x < Suc vcount \<and> \<not> seen ! x}"
proof -
  have fin: "finite {x. x < Suc vcount \<and> \<not> seen ! x}" by simp
  have eq: "{x. x < Suc vcount \<and> \<not> seen[w := True] ! x} = {x. x < Suc vcount \<and> \<not> seen ! x} - {w}"
    using len w by (auto simp: nth_list_update)
  have wS: "w \<in> {x. x < Suc vcount \<and> \<not> seen ! x}" using w un by simp
  show ?thesis unfolding eq by (rule card_Diff1_less[OF fin wS])
qed

text \<open>The two hypotheses \<open>Hout\<close> / \<open>Hin\<close> below record exactly the ``holed-scatter'' fact
      the Pass-A free-CSR construction guarantees: every slot the DFS actually scans in a vertex's
      free out/in block holds a real edge id, whose far endpoint is therefore a genuine vertex
      (below \<open>vcount\<close>). They are discharged separately from the Pass-A analysis; here they are the
      only inputs the measure arguments need.\<close>

lemma bd_meas1:
  assumes Hout: "\<And>u j. u < vcount \<Longrightarrow> out_lo ! u \<le> j \<Longrightarrow> j < free_out_hi fl ! u \<Longrightarrow> snd_list ! (free_out_edges fl ! j) < vcount"
      and wf: "dfs_wf s" and c: "bd_call1_conds fl s"
  shows "(bd_upd1 fl s, s) \<in> dfs_meas fl"
proof -
  from c obtain v oc ic rest where stk: "ds_stk s = (v, oc, ic) # rest" and oclt: "oc < free_out_hi fl ! v"
    by (auto simp: bd_call1_conds_def split: list.splits prod.splits)
  from wf stk have vlt: "v < vcount" and olo: "out_lo ! v \<le> oc" and len: "length (ds_seen s) = Suc vcount"
    by (auto simp: dfs_wf_def)
  let ?e = "free_out_edges fl ! oc" and ?w = "snd_list ! (free_out_edges fl ! oc)"
  let ?s1 = "s\<lparr>ds_stk := (v, Suc oc, ic) # rest\<rparr>"
  have wlt: "?w < vcount" using Hout[OF vlt olo oclt] .
  show ?thesis
  proof (cases "ds_seen s ! ?w")
    case True
    have up: "bd_upd1 fl s = ?s1" using stk True by (simp add: bd_upd1_def Let_def)
    have "dfs_budget fl ?s1 < dfs_budget fl s" using stk oclt by (simp add: dfs_budget_def)
    moreover have "dfs_unseen ?s1 = dfs_unseen s" by (simp add: dfs_unseen_def)
    ultimately show ?thesis using up by (simp add: dfs_meas_def in_measures)
  next
    case False
    have up: "bd_upd1 fl s = dfs_discover ?s1 v ?w ?e" using stk False by (simp add: bd_upd1_def Let_def)
    have "dfs_unseen (dfs_discover ?s1 v ?w ?e)
            = card {x. x < Suc vcount \<and> \<not> (ds_seen s)[?w := True] ! x}"
      by (simp add: dfs_unseen_def dfs_discover_def Let_def)
    also have "\<dots> < dfs_unseen s" unfolding dfs_unseen_def
      using dfs_unseen_mark_lt[OF len _ False] wlt by simp
    finally show ?thesis using up by (simp add: dfs_meas_def in_measures)
  qed
qed

lemma bd_meas2:
  assumes Hin: "\<And>u j. u < vcount \<Longrightarrow> in_lo ! u \<le> j \<Longrightarrow> j < free_in_hi fl ! u \<Longrightarrow> fst_list ! (free_in_edges fl ! j) < vcount"
      and wf: "dfs_wf s" and c: "bd_call2_conds fl s"
  shows "(bd_upd2 fl s, s) \<in> dfs_meas fl"
proof -
  from c obtain v oc ic rest where stk: "ds_stk s = (v, oc, ic) # rest"
      and noc: "\<not> oc < free_out_hi fl ! v" and iclt: "ic < free_in_hi fl ! v"
    by (auto simp: bd_call2_conds_def split: list.splits prod.splits)
  from wf stk have vlt: "v < vcount" and ilo: "in_lo ! v \<le> ic" and len: "length (ds_seen s) = Suc vcount"
    by (auto simp: dfs_wf_def)
  let ?e = "free_in_edges fl ! ic" and ?w = "fst_list ! (free_in_edges fl ! ic)"
  let ?s1 = "s\<lparr>ds_stk := (v, oc, Suc ic) # rest\<rparr>"
  have wlt: "?w < vcount" using Hin[OF vlt ilo iclt] .
  show ?thesis
  proof (cases "ds_seen s ! ?w")
    case True
    have up: "bd_upd2 fl s = ?s1" using stk True noc by (simp add: bd_upd2_def Let_def)
    have "dfs_budget fl ?s1 < dfs_budget fl s" using stk iclt by (simp add: dfs_budget_def)
    moreover have "dfs_unseen ?s1 = dfs_unseen s" by (simp add: dfs_unseen_def)
    ultimately show ?thesis using up by (simp add: dfs_meas_def in_measures)
  next
    case False
    have up: "bd_upd2 fl s = dfs_discover ?s1 v ?w ?e" using stk False noc by (simp add: bd_upd2_def Let_def)
    have "dfs_unseen (dfs_discover ?s1 v ?w ?e)
            = card {x. x < Suc vcount \<and> \<not> (ds_seen s)[?w := True] ! x}"
      by (simp add: dfs_unseen_def dfs_discover_def Let_def)
    also have "\<dots> < dfs_unseen s" unfolding dfs_unseen_def
      using dfs_unseen_mark_lt[OF len _ False] wlt by simp
    finally show ?thesis using up by (simp add: dfs_meas_def in_measures)
  qed
qed

lemma bd_meas3:
  assumes wf: "dfs_wf s" and c: "bd_call3_conds fl s"
  shows "(bd_upd3 s, s) \<in> dfs_meas fl"
proof -
  from c obtain v oc ic rest where stk: "ds_stk s = (v, oc, ic) # rest"
      and o: "\<not> oc < free_out_hi fl ! v" and i: "\<not> ic < free_in_hi fl ! v"
    by (auto simp: bd_call3_conds_def split: list.splits prod.splits)
  have up: "bd_upd3 s = dfs_finish s v rest" using stk by (simp add: bd_upd3_def)
  have unseen: "dfs_unseen (dfs_finish s v rest) = dfs_unseen s"
    by (simp add: dfs_unseen_def dfs_finish_def Let_def)
  have budget: "dfs_budget fl (dfs_finish s v rest) = dfs_budget fl s"
    using stk o i by (simp add: dfs_budget_def dfs_finish_def Let_def)
  have stklen: "dfs_stklen (dfs_finish s v rest) < dfs_stklen s"
    using stk by (simp add: dfs_stklen_def dfs_finish_def Let_def)
  show ?thesis using up unseen budget stklen by (simp add: dfs_meas_def in_measures)
qed

lemma bd_upd1_wf:
  assumes Hout: "\<And>u j. u < vcount \<Longrightarrow> out_lo ! u \<le> j \<Longrightarrow> j < free_out_hi fl ! u \<Longrightarrow> snd_list ! (free_out_edges fl ! j) < vcount"
      and wf: "dfs_wf s" and c: "bd_call1_conds fl s"
  shows "dfs_wf (bd_upd1 fl s)"
proof -
  from c obtain v oc ic rest where stk: "ds_stk s = (v, oc, ic) # rest" and oclt: "oc < free_out_hi fl ! v"
    by (auto simp: bd_call1_conds_def split: list.splits prod.splits)
  from wf stk have vlt: "v < vcount" and olo: "out_lo ! v \<le> oc" and ilo: "in_lo ! v \<le> ic"
      and len: "length (ds_seen s) = Suc vcount"
      and restwf: "\<forall>(v',oc',ic')\<in>set rest. v' < vcount \<and> out_lo ! v' \<le> oc' \<and> in_lo ! v' \<le> ic'"
    by (auto simp: dfs_wf_def)
  let ?w = "snd_list ! (free_out_edges fl ! oc)"
  have wlt: "?w < vcount" using Hout[OF vlt olo oclt] .
  show ?thesis
  proof (cases "ds_seen s ! ?w")
    case True
    with stk show ?thesis using vlt olo ilo len restwf
      by (auto simp: bd_upd1_def dfs_wf_def Let_def)
  next
    case False
    with stk show ?thesis using vlt olo ilo len restwf wlt
      by (auto simp: bd_upd1_def dfs_wf_def dfs_discover_def Let_def)
  qed
qed

lemma bd_upd2_wf:
  assumes Hin: "\<And>u j. u < vcount \<Longrightarrow> in_lo ! u \<le> j \<Longrightarrow> j < free_in_hi fl ! u \<Longrightarrow> fst_list ! (free_in_edges fl ! j) < vcount"
      and wf: "dfs_wf s" and c: "bd_call2_conds fl s"
  shows "dfs_wf (bd_upd2 fl s)"
proof -
  from c obtain v oc ic rest where stk: "ds_stk s = (v, oc, ic) # rest"
      and noc: "\<not> oc < free_out_hi fl ! v" and iclt: "ic < free_in_hi fl ! v"
    by (auto simp: bd_call2_conds_def split: list.splits prod.splits)
  from wf stk have vlt: "v < vcount" and olo: "out_lo ! v \<le> oc" and ilo: "in_lo ! v \<le> ic"
      and len: "length (ds_seen s) = Suc vcount"
      and restwf: "\<forall>(v',oc',ic')\<in>set rest. v' < vcount \<and> out_lo ! v' \<le> oc' \<and> in_lo ! v' \<le> ic'"
    by (auto simp: dfs_wf_def)
  let ?w = "fst_list ! (free_in_edges fl ! ic)"
  have wlt: "?w < vcount" using Hin[OF vlt ilo iclt] .
  show ?thesis
  proof (cases "ds_seen s ! ?w")
    case True
    with stk noc show ?thesis using vlt olo ilo len restwf
      by (auto simp: bd_upd2_def dfs_wf_def Let_def)
  next
    case False
    with stk noc show ?thesis using vlt olo ilo len restwf wlt
      by (auto simp: bd_upd2_def dfs_wf_def dfs_discover_def Let_def)
  qed
qed

lemma bd_upd3_wf:
  assumes wf: "dfs_wf s" and c: "bd_call3_conds fl s"
  shows "dfs_wf (bd_upd3 s)"
proof -
  from c obtain v oc ic rest where stk: "ds_stk s = (v, oc, ic) # rest"
    by (auto simp: bd_call3_conds_def split: list.splits prod.splits)
  from wf stk have len: "length (ds_seen s) = Suc vcount"
      and restwf: "\<forall>(v',oc',ic')\<in>set rest. v' < vcount \<and> out_lo ! v' \<le> oc' \<and> in_lo ! v' \<le> ic'"
    by (auto simp: dfs_wf_def)
  from stk show ?thesis using len restwf by (auto simp: bd_upd3_def dfs_wf_def dfs_finish_def Let_def)
qed

text \<open>Well-founded induction on the measure then discharges the domain predicate: the DFS terminates
      on every well-formed state whose scanned free-edge slots are valid.\<close>

lemma build_dfs_dom_wf:
  assumes Hout: "\<And>u j. u < vcount \<Longrightarrow> out_lo ! u \<le> j \<Longrightarrow> j < free_out_hi fl ! u \<Longrightarrow> snd_list ! (free_out_edges fl ! j) < vcount"
      and Hin: "\<And>u j. u < vcount \<Longrightarrow> in_lo ! u \<le> j \<Longrightarrow> j < free_in_hi fl ! u \<Longrightarrow> fst_list ! (free_in_edges fl ! j) < vcount"
      and wfs: "dfs_wf s"
  shows "build_dfs_dom (fl, s)"
proof -
  have wfr: "wf (dfs_meas fl)" by (simp add: dfs_meas_def)
  have "dfs_wf s \<longrightarrow> build_dfs_dom (fl, s)"
    using wfr
  proof (induction s rule: wf_induct_rule)
    case (less s)
    show ?case
    proof
      assume wf: "dfs_wf s"
      show "build_dfs_dom (fl, s)"
      proof (rule bd_domintros)
        assume c: "bd_call1_conds fl s"
        have "(bd_upd1 fl s, s) \<in> dfs_meas fl" using bd_meas1[OF Hout wf c] .
        moreover have "dfs_wf (bd_upd1 fl s)" using bd_upd1_wf[OF Hout wf c] .
        ultimately show "build_dfs_dom (fl, bd_upd1 fl s)" using less by blast
      next
        assume c: "bd_call2_conds fl s"
        have "(bd_upd2 fl s, s) \<in> dfs_meas fl" using bd_meas2[OF Hin wf c] .
        moreover have "dfs_wf (bd_upd2 fl s)" using bd_upd2_wf[OF Hin wf c] .
        ultimately show "build_dfs_dom (fl, bd_upd2 fl s)" using less by blast
      next
        assume c: "bd_call3_conds fl s"
        have "(bd_upd3 s, s) \<in> dfs_meas fl" using bd_meas3[OF wf c] .
        moreover have "dfs_wf (bd_upd3 s)" using bd_upd3_wf[OF wf c] .
        ultimately show "build_dfs_dom (fl, bd_upd3 s)" using less by blast
      qed
    qed
  qed
  thus ?thesis using wfs by blast
qed

subsection \<open>Discharging the edge-validity: the holed-scatter facts\<close>

text \<open>The remaining inputs \<open>Hout_valid\<close> / \<open>Hin_valid\<close> are proved from Pass A.
      Two facts suffice: every entry of the free-edge CSRs is a real edge id (\<open>< m\<close>) --- the initial
      graph CSR holds only input edges and Pass A only ever overwrites with a real edge --- and every
      cursor stays within the length-\<open>m\<close> array (\<open>free_out_hi ! v \<le> m\<close>), because the number of free
      edges keyed on \<open>v\<close> never exceeds \<open>v\<close>'s block size.\<close>

lemma set_concat_csr_groups_sub: "set (concat (csr_groups nn key es)) \<subseteq> set es"
  by (auto simp: csr_groups_def)

text \<open>Projections onto the six components of the Pass-A tuple.\<close>

lemma case6_3rd: "(case s of (_, _, oe, _, _, _) \<Rightarrow> oe) = fst (snd (snd s))"
  by (cases s) auto
lemma case6_4th: "(case s of (_, _, _, oc, _, _) \<Rightarrow> oc) = fst (snd (snd (snd s)))"
  by (cases s) auto
lemma case6_5th: "(case s of (_, _, _, _, ie, _) \<Rightarrow> ie) = fst (snd (snd (snd (snd s))))"
  by (cases s) auto
lemma case6_6th: "(case s of (_, _, _, _, _, ic) \<Rightarrow> ic) = snd (snd (snd (snd (snd s))))"
  by (cases s) auto

subsubsection \<open>Every free-edge CSR slot holds a real edge id\<close>

lemma passA_step_oe_shape:
  "fst (snd (snd (passA_step fl e s))) = fst (snd (snd s))
   \<or> (\<exists>k. fst (snd (snd (passA_step fl e s))) = (fst (snd (snd s)))[k := e])"
  by (cases s) (auto simp: passA_step_def Let_def)

lemma passA_step_ie_shape:
  "fst (snd (snd (snd (snd (passA_step fl e s))))) = fst (snd (snd (snd (snd s))))
   \<or> (\<exists>k. fst (snd (snd (snd (snd (passA_step fl e s))))) = (fst (snd (snd (snd (snd s)))))[k := e])"
  by (cases s) (auto simp: passA_step_def Let_def)

lemma passA_step_oe_set:
  assumes "e < m" and "\<forall>x \<in> set (fst (snd (snd s))). x < m"
  shows "\<forall>x \<in> set (fst (snd (snd (passA_step fl e s)))). x < m"
  using passA_step_oe_shape[of fl e s] assms set_update_subset_insert[of "fst (snd (snd s))"] by fastforce

lemma passA_step_ie_set:
  assumes "e < m" and "\<forall>x \<in> set (fst (snd (snd (snd (snd s))))). x < m"
  shows "\<forall>x \<in> set (fst (snd (snd (snd (snd (passA_step fl e s)))))). x < m"
  using passA_step_ie_shape[of fl e s] assms set_update_subset_insert[of "fst (snd (snd (snd (snd s))))"] by fastforce

lemma passA_fold_oe_set:
  assumes "\<forall>e\<in>set xs. e < m" "\<forall>x \<in> set (fst (snd (snd s))). x < m"
  shows "\<forall>x \<in> set (fst (snd (snd (fold (passA_step fl) xs s)))). x < m"
  using assms
proof (induct xs arbitrary: s)
  case Nil thus ?case by simp
next
  case (Cons a xs)
  have a: "a < m" and rest: "\<forall>e\<in>set xs. e < m" using Cons.prems(1) by auto
  from Cons.hyps[OF rest passA_step_oe_set[OF a Cons.prems(2)]]
  show ?case by simp
qed

lemma passA_fold_ie_set:
  assumes "\<forall>e\<in>set xs. e < m" "\<forall>x \<in> set (fst (snd (snd (snd (snd s))))). x < m"
  shows "\<forall>x \<in> set (fst (snd (snd (snd (snd (fold (passA_step fl) xs s)))))). x < m"
  using assms
proof (induct xs arbitrary: s)
  case Nil thus ?case by simp
next
  case (Cons a xs)
  have a: "a < m" and rest: "\<forall>e\<in>set xs. e < m" using Cons.prems(1) by auto
  from Cons.hyps[OF rest passA_step_ie_set[OF a Cons.prems(2)]]
  show ?case by simp
qed

lemma free_out_edges_set: "\<forall>x \<in> set (free_out_edges fl). x < m"
proof -
  have init: "\<forall>x \<in> set (csr_edges out_csr). x < m"
    using set_concat_csr_groups_sub[of vcount "nth fst_list" "[0..<m]"]
    by (auto simp: out_csr_eq scatter_edges_eq_concat[OF keys_fst_lt])
  have "\<forall>x \<in> set (fst (snd (snd (fold (passA_step fl) [0..<m]
      (replicate m InL, replicate (Suc vcount) (0::'n), csr_edges out_csr, out_lo, csr_edges in_csr, in_lo))))). x < m"
    by (rule passA_fold_oe_set) (use init in auto)
  thus ?thesis by (simp add: free_out_edges_def case6_3rd passA_def)
qed

lemma free_in_edges_set: "\<forall>x \<in> set (free_in_edges fl). x < m"
proof -
  have init: "\<forall>x \<in> set (csr_edges in_csr). x < m"
    using set_concat_csr_groups_sub[of vcount "nth snd_list" "[0..<m]"]
    by (auto simp: in_csr_eq scatter_edges_eq_concat[OF keys_snd_lt])
  have "\<forall>x \<in> set (fst (snd (snd (snd (snd (fold (passA_step fl) [0..<m]
      (replicate m InL, replicate (Suc vcount) (0::'n), csr_edges out_csr, out_lo, csr_edges in_csr, in_lo))))))). x < m"
    by (rule passA_fold_ie_set) (use init in auto)
  thus ?thesis by (simp add: free_in_edges_def case6_5th passA_def)
qed

subsubsection \<open>Every scanned cursor stays within the array\<close>

lemma passA_step_oc:
  "fst (snd (snd (snd (passA_step fl e s))))
     = (if classify fl e = InTree
        then (fst (snd (snd (snd s))))[fst_list ! e := fst (snd (snd (snd s))) ! (fst_list ! e) + 1]
        else fst (snd (snd (snd s))))"
  by (cases s) (auto simp: passA_step_def classify_def Let_def)

lemma passA_step_ic:
  "snd (snd (snd (snd (snd (passA_step fl e s)))))
     = (if classify fl e = InTree
        then (snd (snd (snd (snd (snd s)))))[snd_list ! e := snd (snd (snd (snd (snd s)))) ! (snd_list ! e) + 1]
        else snd (snd (snd (snd (snd s)))))"
  by (cases s) (auto simp: passA_step_def classify_def Let_def)

lemma length_filter_conj_le: "length (filter (\<lambda>x. P x \<and> Q x) xs) \<le> length (filter Q xs)"
  by (induct xs) auto

lemma passA_fold_oc_count:
  assumes "sized s" "v < vcount"
  shows "fst (snd (snd (snd (fold (passA_step fl) xs s)))) ! v
           = fst (snd (snd (snd s))) ! v + length (filter (\<lambda>e. classify fl e = InTree \<and> fst_list ! e = v) xs)"
  using assms
proof (induct xs arbitrary: s)
  case Nil thus ?case by simp
next
  case (Cons a xs)
  have sz: "sized (passA_step fl a s)" using Cons.prems(1) by (rule passA_step_sized)
  have len: "length (fst (snd (snd (snd s)))) = vcount" using Cons.prems(1) by (cases s) (simp add: sized_def)
  have step: "fst (snd (snd (snd (passA_step fl a s)))) ! v
              = fst (snd (snd (snd s))) ! v + (if classify fl a = InTree \<and> fst_list ! a = v then 1 else 0)"
    using len Cons.prems(2) by (simp add: passA_step_oc nth_list_update)
  show ?case using Cons.hyps[OF sz Cons.prems(2)] step by simp
qed

lemma passA_fold_ic_count:
  assumes "sized s" "v < vcount"
  shows "snd (snd (snd (snd (snd (fold (passA_step fl) xs s))))) ! v
           = snd (snd (snd (snd (snd s)))) ! v + length (filter (\<lambda>e. classify fl e = InTree \<and> snd_list ! e = v) xs)"
  using assms
proof (induct xs arbitrary: s)
  case Nil thus ?case by simp
next
  case (Cons a xs)
  have sz: "sized (passA_step fl a s)" using Cons.prems(1) by (rule passA_step_sized)
  have len: "length (snd (snd (snd (snd (snd s))))) = vcount" using Cons.prems(1) by (cases s) (simp add: sized_def)
  have step: "snd (snd (snd (snd (snd (passA_step fl a s))))) ! v
              = snd (snd (snd (snd (snd s)))) ! v + (if classify fl a = InTree \<and> snd_list ! a = v then 1 else 0)"
    using len Cons.prems(2) by (simp add: passA_step_ic nth_list_update)
  show ?case using Cons.hyps[OF sz Cons.prems(2)] step by simp
qed

lemma free_out_hi_count:
  assumes v: "v < vcount"
  shows "free_out_hi fl ! v = out_lo ! v + length (filter (\<lambda>e. classify fl e = InTree \<and> fst_list ! e = v) [0..<m])"
proof -
  have sz0: "sized (replicate m InL, replicate (Suc vcount) (0::'n), csr_edges out_csr, out_lo,
                csr_edges in_csr, in_lo)"
    by (simp add: sized_def length_out_lo length_in_lo out_csr_eq in_csr_eq)
  show ?thesis
    using passA_fold_oc_count[OF sz0 v, where xs = "[0..<m]"]
    by (simp add: free_out_hi_def case6_4th passA_def)
qed

lemma free_in_hi_count:
  assumes v: "v < vcount"
  shows "free_in_hi fl ! v = in_lo ! v + length (filter (\<lambda>e. classify fl e = InTree \<and> snd_list ! e = v) [0..<m])"
proof -
  have sz0: "sized (replicate m InL, replicate (Suc vcount) (0::'n), csr_edges out_csr, out_lo,
                csr_edges in_csr, in_lo)"
    by (simp add: sized_def length_out_lo length_in_lo out_csr_eq in_csr_eq)
  show ?thesis
    using passA_fold_ic_count[OF sz0 v, where xs = "[0..<m]"]
    by (simp add: free_in_hi_def case6_6th passA_def)
qed

lemma filter2_le_ct:
  assumes v: "v < vcount"
  shows "length (filter (\<lambda>e. classify fl e = InTree \<and> fst_list ! e = v) [0..<m]) \<le> ct vcount (nth fst_list) [0..<m] ! v"
  using length_filter_conj_le[of "\<lambda>e. classify fl e = InTree" "\<lambda>e. fst_list ! e = v" "[0..<m]"] v
  by (simp add: ct_nth)

lemma filter2_le_ct_snd:
  assumes v: "v < vcount"
  shows "length (filter (\<lambda>e. classify fl e = InTree \<and> snd_list ! e = v) [0..<m]) \<le> ct vcount (nth snd_list) [0..<m] ! v"
  using length_filter_conj_le[of "\<lambda>e. classify fl e = InTree" "\<lambda>e. snd_list ! e = v" "[0..<m]"] v
  by (simp add: ct_nth)

lemma out_lo_sum_take:
  assumes v: "v < vcount"
  shows "out_lo ! v = sum_list (take v (ct vcount (nth fst_list) [0..<m]))"
proof -
  let ?cts = "ct vcount (nth fst_list) [0..<m]"
  have "out_lo ! v = butlast (psums 0 ?cts) ! v" by (simp add: out_lo_def out_csr_eq)
  also have "\<dots> = psums 0 ?cts ! v" using v by (simp add: nth_butlast psums_length)
  also have "\<dots> = sum_list (take v ?cts)" using v by (simp add: psums_nth)
  finally show ?thesis .
qed

lemma in_lo_sum_take:
  assumes v: "v < vcount"
  shows "in_lo ! v = sum_list (take v (ct vcount (nth snd_list) [0..<m]))"
proof -
  let ?cts = "ct vcount (nth snd_list) [0..<m]"
  have "in_lo ! v = butlast (psums 0 ?cts) ! v" by (simp add: in_lo_def in_csr_eq)
  also have "\<dots> = psums 0 ?cts ! v" using v by (simp add: nth_butlast psums_length)
  also have "\<dots> = sum_list (take v ?cts)" using v by (simp add: psums_nth)
  finally show ?thesis .
qed

lemma free_out_hi_le_m:
  assumes v: "v < vcount"
  shows "free_out_hi fl ! v \<le> m"
proof -
  let ?cts = "ct vcount (nth fst_list) [0..<m]"
  have "free_out_hi fl ! v \<le> sum_list (take v ?cts) + ?cts ! v"
    using free_out_hi_count[OF v] filter2_le_ct[OF v] out_lo_sum_take[OF v] by simp
  also have "\<dots> = sum_list (take (Suc v) ?cts)" using v by (simp add: take_Suc_conv_app_nth)
  also have "\<dots> \<le> sum_list ?cts" by (rule sum_list_take_le)
  also have "\<dots> = m" using keys_fst_lt by (simp add: sum_ct)
  finally show ?thesis .
qed

lemma free_in_hi_le_m:
  assumes v: "v < vcount"
  shows "free_in_hi fl ! v \<le> m"
proof -
  let ?cts = "ct vcount (nth snd_list) [0..<m]"
  have "free_in_hi fl ! v \<le> sum_list (take v ?cts) + ?cts ! v"
    using free_in_hi_count[OF v] filter2_le_ct_snd[OF v] in_lo_sum_take[OF v] by simp
  also have "\<dots> = sum_list (take (Suc v) ?cts)" using v by (simp add: take_Suc_conv_app_nth)
  also have "\<dots> \<le> sum_list ?cts" by (rule sum_list_take_le)
  also have "\<dots> = m" using keys_snd_lt by (simp add: sum_ct)
  finally show ?thesis .
qed

subsubsection \<open>The edge-validity hypotheses, hence unconditional termination on well-formed states\<close>

lemma Hout_valid:
  assumes "v < vcount" "out_lo ! v \<le> j" "j < free_out_hi fl ! v"
  shows "snd_list ! (free_out_edges fl ! j) < vcount"
proof -
  have jm: "j < m" using assms(3) free_out_hi_le_m[OF assms(1)] by (meson order_less_le_trans)
  hence "free_out_edges fl ! j \<in> set (free_out_edges fl)" by (metis length_free_out_edges nth_mem)
  hence m: "free_out_edges fl ! j < m" using free_out_edges_set by blast
  show ?thesis by (rule vs_less_vcount[OF snd_list_nth_vertex[OF m]])
qed

lemma Hin_valid:
  assumes "v < vcount" "in_lo ! v \<le> j" "j < free_in_hi fl ! v"
  shows "fst_list ! (free_in_edges fl ! j) < vcount"
proof -
  have jm: "j < m" using assms(3) free_in_hi_le_m[OF assms(1)] by (meson order_less_le_trans)
  hence "free_in_edges fl ! j \<in> set (free_in_edges fl)" by (metis length_free_in_edges nth_mem)
  hence m: "free_in_edges fl ! j < m" using free_in_edges_set by blast
  show ?thesis by (rule vs_less_vcount[OF fst_list_nth_vertex[OF m]])
qed

subsubsection \<open>The holed-scatter block characterisation (I3's linchpin)\<close>

text \<open>Pass A scatters every \<^emph>\<open>free\<close> edge into the front of its owner's CSR block, keyed on the tail
      (outgoing) resp.\ head (ingoing) --- the holes are the non-free tail of the old block. The two
      lemmas below characterise the resulting blocks: every slot of @{term \<open>free_out_edges fl\<close>} in
      @{term v}'s block \<open>[out_lo ! v ..< free_out_hi fl ! v)\<close> holds a free edge whose \<^emph>\<open>tail\<close> is
      @{term v}, and dually for @{term \<open>free_in_edges fl\<close>} keyed on the head. This is exactly the fact
      design-notes I3 needs to know that a vertex discovered in @{term v}'s out-scan is joined to
      @{term v} by that scanned edge (with the right orientation). The proof reuses the scatter
      block-disjointness @{thm sc_block_disj} via @{thm out_lo_sum_take}, decoupled from
      @{const scatter_edges} because Pass A skips the non-free edges.\<close>

lemma passA_step_oe:
  "fst (snd (snd (passA_step fl e s)))
     = (if classify fl e = InTree
        then (fst (snd (snd s)))[fst (snd (snd (snd s))) ! (fst_list ! e) := e]
        else fst (snd (snd s)))"
  by (cases s) (auto simp: passA_step_def classify_def Let_def)

lemma passA_step_ie:
  "fst (snd (snd (snd (snd (passA_step fl e s)))))
     = (if classify fl e = InTree
        then (fst (snd (snd (snd (snd s)))))[snd (snd (snd (snd (snd s)))) ! (snd_list ! e) := e]
        else fst (snd (snd (snd (snd s)))))"
  by (cases s) (auto simp: passA_step_def classify_def Let_def)

lemma out_lo_eq_sc_lo:
  "v < vcount \<Longrightarrow> out_lo ! v = sc_lo vcount (nth fst_list) [0..<m] v"
  by (simp add: out_lo_sum_take sc_lo_def)

lemma in_lo_eq_sc_lo:
  "v < vcount \<Longrightarrow> in_lo ! v = sc_lo vcount (nth snd_list) [0..<m] v"
  by (simp add: in_lo_sum_take sc_lo_def)

definition scW_out ::
  "'n list \<Rightarrow> nat list \<Rightarrow> edge_tag list \<times> 'n list \<times> nat list \<times> nat list \<times> nat list \<times> nat list \<Rightarrow> bool" where
  "scW_out fl dn s \<longleftrightarrow>
     (\<forall>v<vcount. fst (snd (snd (snd s))) ! v
          = out_lo ! v + length (filter (\<lambda>e. classify fl e = InTree \<and> fst_list ! e = v) dn)) \<and>
     (\<forall>v<vcount. \<forall>j. out_lo ! v \<le> j \<longrightarrow> j < fst (snd (snd (snd s))) ! v \<longrightarrow>
          fst_list ! (fst (snd (snd s)) ! j) = v \<and> classify fl (fst (snd (snd s)) ! j) = InTree)"

lemma scW_out_step:
  assumes split: "[0..<m] = dn @ e # rest" and sz: "sized s" and inv: "scW_out fl dn s"
  shows "scW_out fl (dn @ [e]) (passA_step fl e s)"
proof (cases "classify fl e = InTree")
  case notfree: False
  have oc': "fst (snd (snd (snd (passA_step fl e s)))) = fst (snd (snd (snd s)))"
    by (simp add: passA_step_oc notfree)
  have oe': "fst (snd (snd (passA_step fl e s))) = fst (snd (snd s))"
    by (simp add: passA_step_oe notfree)
  show ?thesis using inv unfolding scW_out_def oc' oe' by (simp add: notfree)
next
  case free: True
  define x where "x = fst_list ! e"
  have es: "e \<in> set [0..<m]" using split by simp
  hence em: "e < m" by simp
  have xlt: "x < vcount" using es keys_fst_lt x_def by blast
  have loc: "length (fst (snd (snd (snd s)))) = vcount" using sz by (cases s) (simp add: sized_def)
  have loe: "length (fst (snd (snd s))) = m" using sz by (cases s) (simp add: sized_def)
  define W where "W = fst (snd (snd (snd s))) ! x"
  have oc': "fst (snd (snd (snd (passA_step fl e s)))) = (fst (snd (snd (snd s))))[x := W + 1]"
    using free by (simp add: passA_step_oc x_def W_def)
  have oe': "fst (snd (snd (passA_step fl e s))) = (fst (snd (snd s)))[W := e]"
    using free by (simp add: passA_step_oe x_def W_def)
  have countI: "\<And>v. v < vcount \<Longrightarrow> fst (snd (snd (snd s))) ! v
        = out_lo ! v + length (filter (\<lambda>y. classify fl y = InTree \<and> fst_list ! y = v) dn)"
    using inv by (simp add: scW_out_def)
  have contI: "\<And>v j. v < vcount \<Longrightarrow> out_lo ! v \<le> j \<Longrightarrow> j < fst (snd (snd (snd s))) ! v \<Longrightarrow>
        fst_list ! (fst (snd (snd s)) ! j) = v \<and> classify fl (fst (snd (snd s)) ! j) = InTree"
    using inv by (simp add: scW_out_def)
  have Wval: "W = out_lo ! x + length (filter (\<lambda>y. classify fl y = InTree \<and> fst_list ! y = x) dn)"
    using countI[OF xlt] W_def by simp
  have dnlt: "length (filter (\<lambda>y. fst_list ! y = x) dn) < length (filter (\<lambda>y. fst_list ! y = x) [0..<m])"
    using split x_def by simp
  have cntx_lt: "length (filter (\<lambda>y. classify fl y = InTree \<and> fst_list ! y = x) dn)
                   < ct vcount (nth fst_list) [0..<m] ! x"
  proof -
    have "length (filter (\<lambda>y. classify fl y = InTree \<and> fst_list ! y = x) dn)
            \<le> length (filter (\<lambda>y. fst_list ! y = x) dn)" by (rule length_filter_conj_le)
    thus ?thesis using dnlt xlt by (simp add: ct_nth)
  qed
  have Wm: "W < m"
  proof -
    have "W = out_lo ! x + length (filter (\<lambda>y. classify fl y = InTree \<and> fst_list ! y = x) dn)" by (rule Wval)
    also have "\<dots> < out_lo ! x + ct vcount (nth fst_list) [0..<m] ! x" using cntx_lt by simp
    also have "\<dots> = sc_lo vcount (nth fst_list) [0..<m] (Suc x)"
      using xlt by (simp add: out_lo_eq_sc_lo sc_lo_Suc)
    also have "\<dots> \<le> length [0..<m]"
      using xlt sc_lo_le_length[OF keys_fst_lt, of "Suc x"] by simp
    finally show ?thesis by simp
  qed
  show ?thesis unfolding scW_out_def oc' oe'
  proof (intro conjI; intro allI impI)
    fix v assume v: "v < vcount"
    show "(fst (snd (snd (snd s))))[x := W + 1] ! v
            = out_lo ! v + length (filter (\<lambda>y. classify fl y = InTree \<and> fst_list ! y = v) (dn @ [e]))"
    proof (cases "v = x")
      case True
      have "(fst (snd (snd (snd s))))[x := W + 1] ! v = W + 1"
        using True loc xlt by (simp add: nth_list_update_eq)
      also have "\<dots> = out_lo ! v + length (filter (\<lambda>y. classify fl y = InTree \<and> fst_list ! y = x) dn) + 1"
        using Wval True by simp
      also have "\<dots> = out_lo ! v + length (filter (\<lambda>y. classify fl y = InTree \<and> fst_list ! y = v) (dn @ [e]))"
        using True free x_def by simp
      finally show ?thesis .
    next
      case False
      have "(fst (snd (snd (snd s))))[x := W + 1] ! v = fst (snd (snd (snd s))) ! v"
        using False by (simp add: nth_list_update_neq)
      also have "\<dots> = out_lo ! v + length (filter (\<lambda>y. classify fl y = InTree \<and> fst_list ! y = v) dn)"
        by (rule countI[OF v])
      also have "\<dots> = out_lo ! v + length (filter (\<lambda>y. classify fl y = InTree \<and> fst_list ! y = v) (dn @ [e]))"
        using False x_def by simp
      finally show ?thesis .
    qed
  next
    fix v j assume v: "v < vcount" and lo: "out_lo ! v \<le> j"
      and jlt: "j < (fst (snd (snd (snd s))))[x := W + 1] ! v"
    show "fst_list ! ((fst (snd (snd s)))[W := e] ! j) = v
            \<and> classify fl ((fst (snd (snd s)))[W := e] ! j) = InTree"
    proof (cases "j = W")
      case jW: True
      have oej: "(fst (snd (snd s)))[W := e] ! j = e"
        using jW Wm loe by (simp add: nth_list_update_eq)
      have "v = x"
      proof (rule ccontr)
        assume vne: "v \<noteq> x"
        have ocv: "(fst (snd (snd (snd s))))[x := W + 1] ! v = fst (snd (snd (snd s))) ! v"
          using vne by (simp add: nth_list_update_neq)
        have javlt: "j - out_lo ! v < length (filter (\<lambda>y. classify fl y = InTree \<and> fst_list ! y = v) dn)"
          using jlt ocv countI[OF v] lo by simp
        have avct: "j - out_lo ! v < ct vcount (nth fst_list) [0..<m] ! v"
        proof -
          have "length (filter (\<lambda>y. classify fl y = InTree \<and> fst_list ! y = v) dn)
                  \<le> length (filter (\<lambda>y. fst_list ! y = v) dn)" by (rule length_filter_conj_le)
          also have "\<dots> \<le> length (filter (\<lambda>y. fst_list ! y = v) [0..<m])" using split by simp
          finally have le: "length (filter (\<lambda>y. classify fl y = InTree \<and> fst_list ! y = v) dn)
                  \<le> length (filter (\<lambda>y. fst_list ! y = v) [0..<m])" .
          show ?thesis using javlt le v by (simp add: ct_nth)
        qed
        have "sc_lo vcount (nth fst_list) [0..<m] x
                + length (filter (\<lambda>y. classify fl y = InTree \<and> fst_list ! y = x) dn)
              \<noteq> sc_lo vcount (nth fst_list) [0..<m] v + (j - out_lo ! v)"
          by (rule sc_block_disj[OF xlt v vne cntx_lt avct])
        moreover have "sc_lo vcount (nth fst_list) [0..<m] x
                + length (filter (\<lambda>y. classify fl y = InTree \<and> fst_list ! y = x) dn) = j"
          using Wval jW out_lo_eq_sc_lo[OF xlt] by simp
        moreover have "sc_lo vcount (nth fst_list) [0..<m] v + (j - out_lo ! v) = j"
          using out_lo_eq_sc_lo[OF v] lo by simp
        ultimately show False by simp
      qed
      thus ?thesis using oej x_def free by simp
    next
      case jW: False
      have oej: "(fst (snd (snd s)))[W := e] ! j = fst (snd (snd s)) ! j"
        using jW by (simp add: nth_list_update_neq)
      have jocv: "j < fst (snd (snd (snd s))) ! v"
      proof (cases "v = x")
        case True
        have jW1: "j < W + 1" using jlt True loc xlt by (simp add: nth_list_update_eq)
        show ?thesis using jW1 jW True W_def by auto
      next
        case False
        have "(fst (snd (snd (snd s))))[x := W + 1] ! v = fst (snd (snd (snd s))) ! v"
          using False by (simp add: nth_list_update_neq)
        thus ?thesis using jlt by simp
      qed
      show ?thesis using contI[OF v lo jocv] oej by simp
    qed
  qed
qed

lemma scW_out_fold:
  assumes "[0..<m] = dn @ rest" "sized s" "scW_out fl dn s"
  shows "scW_out fl [0..<m] (fold (passA_step fl) rest s)"
  using assms
proof (induction rest arbitrary: dn s)
  case Nil thus ?case by simp
next
  case (Cons e rest)
  have split: "[0..<m] = dn @ e # rest" using Cons.prems(1) by simp
  have split': "[0..<m] = (dn @ [e]) @ rest" using Cons.prems(1) by simp
  have step: "scW_out fl (dn @ [e]) (passA_step fl e s)"
    by (rule scW_out_step[OF split Cons.prems(2) Cons.prems(3)])
  have sz': "sized (passA_step fl e s)" using Cons.prems(2) by (rule passA_step_sized)
  show ?case using Cons.IH[OF split' sz' step] by simp
qed

lemma scW_out_init:
  "scW_out fl [] (replicate m InL, replicate (Suc vcount) (0::'n), csr_edges out_csr, out_lo,
               csr_edges in_csr, in_lo)"
  by (simp add: scW_out_def)

lemma scW_out_passA: "scW_out fl [0..<m] (passA fl)"
proof -
  have sz0: "sized (replicate m InL, replicate (Suc vcount) (0::'n), csr_edges out_csr, out_lo,
                csr_edges in_csr, in_lo)"
    by (simp add: sized_def length_out_lo length_in_lo out_csr_eq in_csr_eq)
  have "scW_out fl [0..<m] (fold (passA_step fl) [0..<m]
          (replicate m InL, replicate (Suc vcount) (0::'n), csr_edges out_csr, out_lo,
           csr_edges in_csr, in_lo))"
    by (rule scW_out_fold[OF _ sz0 scW_out_init]) simp
  thus ?thesis by (simp add: passA_def)
qed

lemma free_out_edges_block:
  assumes "v < vcount" "out_lo ! v \<le> j" "j < free_out_hi fl ! v"
  shows "fst_list ! (free_out_edges fl ! j) = v \<and> classify fl (free_out_edges fl ! j) = InTree"
proof -
  have hi: "j < fst (snd (snd (snd (passA fl)))) ! v" using assms(3) by (simp add: free_out_hi_def case6_4th)
  have allf: "\<forall>v<vcount. \<forall>j. out_lo ! v \<le> j \<longrightarrow> j < fst (snd (snd (snd (passA fl)))) ! v \<longrightarrow>
          fst_list ! (fst (snd (snd (passA fl))) ! j) = v \<and> classify fl (fst (snd (snd (passA fl))) ! j) = InTree"
    using scW_out_passA by (simp add: scW_out_def)
  show ?thesis using allf assms(1,2) hi by (simp add: free_out_edges_def case6_3rd)
qed

definition scW_in ::
  "'n list \<Rightarrow> nat list \<Rightarrow> edge_tag list \<times> 'n list \<times> nat list \<times> nat list \<times> nat list \<times> nat list \<Rightarrow> bool" where
  "scW_in fl dn s \<longleftrightarrow>
     (\<forall>v<vcount. snd (snd (snd (snd (snd s)))) ! v
          = in_lo ! v + length (filter (\<lambda>e. classify fl e = InTree \<and> snd_list ! e = v) dn)) \<and>
     (\<forall>v<vcount. \<forall>j. in_lo ! v \<le> j \<longrightarrow> j < snd (snd (snd (snd (snd s)))) ! v \<longrightarrow>
          snd_list ! (fst (snd (snd (snd (snd s)))) ! j) = v
          \<and> classify fl (fst (snd (snd (snd (snd s)))) ! j) = InTree)"

lemma scW_in_step:
  assumes split: "[0..<m] = dn @ e # rest" and sz: "sized s" and inv: "scW_in fl dn s"
  shows "scW_in fl (dn @ [e]) (passA_step fl e s)"
proof (cases "classify fl e = InTree")
  case notfree: False
  have oc': "snd (snd (snd (snd (snd (passA_step fl e s))))) = snd (snd (snd (snd (snd s))))"
    by (simp add: passA_step_ic notfree)
  have oe': "fst (snd (snd (snd (snd (passA_step fl e s))))) = fst (snd (snd (snd (snd s))))"
    by (simp add: passA_step_ie notfree)
  show ?thesis using inv unfolding scW_in_def oc' oe' by (simp add: notfree)
next
  case free: True
  define x where "x = snd_list ! e"
  have es: "e \<in> set [0..<m]" using split by simp
  hence em: "e < m" by simp
  have xlt: "x < vcount" using es keys_snd_lt x_def by blast
  have loc: "length (snd (snd (snd (snd (snd s))))) = vcount" using sz by (cases s) (simp add: sized_def)
  have loe: "length (fst (snd (snd (snd (snd s))))) = m" using sz by (cases s) (simp add: sized_def)
  define W where "W = snd (snd (snd (snd (snd s)))) ! x"
  have oc': "snd (snd (snd (snd (snd (passA_step fl e s))))) = (snd (snd (snd (snd (snd s)))))[x := W + 1]"
    using free by (simp add: passA_step_ic x_def W_def)
  have oe': "fst (snd (snd (snd (snd (passA_step fl e s))))) = (fst (snd (snd (snd (snd s)))))[W := e]"
    using free by (simp add: passA_step_ie x_def W_def)
  have countI: "\<And>v. v < vcount \<Longrightarrow> snd (snd (snd (snd (snd s)))) ! v
        = in_lo ! v + length (filter (\<lambda>y. classify fl y = InTree \<and> snd_list ! y = v) dn)"
    using inv by (simp add: scW_in_def)
  have contI: "\<And>v j. v < vcount \<Longrightarrow> in_lo ! v \<le> j \<Longrightarrow> j < snd (snd (snd (snd (snd s)))) ! v \<Longrightarrow>
        snd_list ! (fst (snd (snd (snd (snd s)))) ! j) = v \<and> classify fl (fst (snd (snd (snd (snd s)))) ! j) = InTree"
    using inv by (simp add: scW_in_def)
  have Wval: "W = in_lo ! x + length (filter (\<lambda>y. classify fl y = InTree \<and> snd_list ! y = x) dn)"
    using countI[OF xlt] W_def by simp
  have dnlt: "length (filter (\<lambda>y. snd_list ! y = x) dn) < length (filter (\<lambda>y. snd_list ! y = x) [0..<m])"
    using split x_def by simp
  have cntx_lt: "length (filter (\<lambda>y. classify fl y = InTree \<and> snd_list ! y = x) dn)
                   < ct vcount (nth snd_list) [0..<m] ! x"
  proof -
    have "length (filter (\<lambda>y. classify fl y = InTree \<and> snd_list ! y = x) dn)
            \<le> length (filter (\<lambda>y. snd_list ! y = x) dn)" by (rule length_filter_conj_le)
    thus ?thesis using dnlt xlt by (simp add: ct_nth)
  qed
  have Wm: "W < m"
  proof -
    have "W = in_lo ! x + length (filter (\<lambda>y. classify fl y = InTree \<and> snd_list ! y = x) dn)" by (rule Wval)
    also have "\<dots> < in_lo ! x + ct vcount (nth snd_list) [0..<m] ! x" using cntx_lt by simp
    also have "\<dots> = sc_lo vcount (nth snd_list) [0..<m] (Suc x)"
      using xlt by (simp add: in_lo_eq_sc_lo sc_lo_Suc)
    also have "\<dots> \<le> length [0..<m]"
      using xlt sc_lo_le_length[OF keys_snd_lt, of "Suc x"] by simp
    finally show ?thesis by simp
  qed
  show ?thesis unfolding scW_in_def oc' oe'
  proof (intro conjI; intro allI impI)
    fix v assume v: "v < vcount"
    show "(snd (snd (snd (snd (snd s)))))[x := W + 1] ! v
            = in_lo ! v + length (filter (\<lambda>y. classify fl y = InTree \<and> snd_list ! y = v) (dn @ [e]))"
    proof (cases "v = x")
      case True
      have "(snd (snd (snd (snd (snd s)))))[x := W + 1] ! v = W + 1"
        using True loc xlt by (simp add: nth_list_update_eq)
      also have "\<dots> = in_lo ! v + length (filter (\<lambda>y. classify fl y = InTree \<and> snd_list ! y = x) dn) + 1"
        using Wval True by simp
      also have "\<dots> = in_lo ! v + length (filter (\<lambda>y. classify fl y = InTree \<and> snd_list ! y = v) (dn @ [e]))"
        using True free x_def by simp
      finally show ?thesis .
    next
      case False
      have "(snd (snd (snd (snd (snd s)))))[x := W + 1] ! v = snd (snd (snd (snd (snd s)))) ! v"
        using False by (simp add: nth_list_update_neq)
      also have "\<dots> = in_lo ! v + length (filter (\<lambda>y. classify fl y = InTree \<and> snd_list ! y = v) dn)"
        by (rule countI[OF v])
      also have "\<dots> = in_lo ! v + length (filter (\<lambda>y. classify fl y = InTree \<and> snd_list ! y = v) (dn @ [e]))"
        using False x_def by simp
      finally show ?thesis .
    qed
  next
    fix v j assume v: "v < vcount" and lo: "in_lo ! v \<le> j"
      and jlt: "j < (snd (snd (snd (snd (snd s)))))[x := W + 1] ! v"
    show "snd_list ! ((fst (snd (snd (snd (snd s)))))[W := e] ! j) = v
            \<and> classify fl ((fst (snd (snd (snd (snd s)))))[W := e] ! j) = InTree"
    proof (cases "j = W")
      case jW: True
      have oej: "(fst (snd (snd (snd (snd s)))))[W := e] ! j = e"
        using jW Wm loe by (simp add: nth_list_update_eq)
      have "v = x"
      proof (rule ccontr)
        assume vne: "v \<noteq> x"
        have ocv: "(snd (snd (snd (snd (snd s)))))[x := W + 1] ! v = snd (snd (snd (snd (snd s)))) ! v"
          using vne by (simp add: nth_list_update_neq)
        have javlt: "j - in_lo ! v < length (filter (\<lambda>y. classify fl y = InTree \<and> snd_list ! y = v) dn)"
          using jlt ocv countI[OF v] lo by simp
        have avct: "j - in_lo ! v < ct vcount (nth snd_list) [0..<m] ! v"
        proof -
          have "length (filter (\<lambda>y. classify fl y = InTree \<and> snd_list ! y = v) dn)
                  \<le> length (filter (\<lambda>y. snd_list ! y = v) dn)" by (rule length_filter_conj_le)
          also have "\<dots> \<le> length (filter (\<lambda>y. snd_list ! y = v) [0..<m])" using split by simp
          finally have le: "length (filter (\<lambda>y. classify fl y = InTree \<and> snd_list ! y = v) dn)
                  \<le> length (filter (\<lambda>y. snd_list ! y = v) [0..<m])" .
          show ?thesis using javlt le v by (simp add: ct_nth)
        qed
        have "sc_lo vcount (nth snd_list) [0..<m] x
                + length (filter (\<lambda>y. classify fl y = InTree \<and> snd_list ! y = x) dn)
              \<noteq> sc_lo vcount (nth snd_list) [0..<m] v + (j - in_lo ! v)"
          by (rule sc_block_disj[OF xlt v vne cntx_lt avct])
        moreover have "sc_lo vcount (nth snd_list) [0..<m] x
                + length (filter (\<lambda>y. classify fl y = InTree \<and> snd_list ! y = x) dn) = j"
          using Wval jW in_lo_eq_sc_lo[OF xlt] by simp
        moreover have "sc_lo vcount (nth snd_list) [0..<m] v + (j - in_lo ! v) = j"
          using in_lo_eq_sc_lo[OF v] lo by simp
        ultimately show False by simp
      qed
      thus ?thesis using oej x_def free by simp
    next
      case jW: False
      have oej: "(fst (snd (snd (snd (snd s)))))[W := e] ! j = fst (snd (snd (snd (snd s)))) ! j"
        using jW by (simp add: nth_list_update_neq)
      have jocv: "j < snd (snd (snd (snd (snd s)))) ! v"
      proof (cases "v = x")
        case True
        have jW1: "j < W + 1" using jlt True loc xlt by (simp add: nth_list_update_eq)
        show ?thesis using jW1 jW True W_def by auto
      next
        case False
        have "(snd (snd (snd (snd (snd s)))))[x := W + 1] ! v = snd (snd (snd (snd (snd s)))) ! v"
          using False by (simp add: nth_list_update_neq)
        thus ?thesis using jlt by simp
      qed
      show ?thesis using contI[OF v lo jocv] oej by simp
    qed
  qed
qed

lemma scW_in_fold:
  assumes "[0..<m] = dn @ rest" "sized s" "scW_in fl dn s"
  shows "scW_in fl [0..<m] (fold (passA_step fl) rest s)"
  using assms
proof (induction rest arbitrary: dn s)
  case Nil thus ?case by simp
next
  case (Cons e rest)
  have split: "[0..<m] = dn @ e # rest" using Cons.prems(1) by simp
  have split': "[0..<m] = (dn @ [e]) @ rest" using Cons.prems(1) by simp
  have step: "scW_in fl (dn @ [e]) (passA_step fl e s)"
    by (rule scW_in_step[OF split Cons.prems(2) Cons.prems(3)])
  have sz': "sized (passA_step fl e s)" using Cons.prems(2) by (rule passA_step_sized)
  show ?case using Cons.IH[OF split' sz' step] by simp
qed

lemma scW_in_init:
  "scW_in fl [] (replicate m InL, replicate (Suc vcount) (0::'n), csr_edges out_csr, out_lo,
              csr_edges in_csr, in_lo)"
  by (simp add: scW_in_def)

lemma scW_in_passA: "scW_in fl [0..<m] (passA fl)"
proof -
  have sz0: "sized (replicate m InL, replicate (Suc vcount) (0::'n), csr_edges out_csr, out_lo,
                csr_edges in_csr, in_lo)"
    by (simp add: sized_def length_out_lo length_in_lo out_csr_eq in_csr_eq)
  have "scW_in fl [0..<m] (fold (passA_step fl) [0..<m]
          (replicate m InL, replicate (Suc vcount) (0::'n), csr_edges out_csr, out_lo,
           csr_edges in_csr, in_lo))"
    by (rule scW_in_fold[OF _ sz0 scW_in_init]) simp
  thus ?thesis by (simp add: passA_def)
qed

lemma free_in_edges_block:
  assumes "v < vcount" "in_lo ! v \<le> j" "j < free_in_hi fl ! v"
  shows "snd_list ! (free_in_edges fl ! j) = v \<and> classify fl (free_in_edges fl ! j) = InTree"
proof -
  have hi: "j < snd (snd (snd (snd (snd (passA fl))))) ! v" using assms(3) by (simp add: free_in_hi_def case6_6th)
  have allf: "\<forall>v<vcount. \<forall>j. in_lo ! v \<le> j \<longrightarrow> j < snd (snd (snd (snd (snd (passA fl))))) ! v \<longrightarrow>
          snd_list ! (fst (snd (snd (snd (snd (passA fl))))) ! j) = v
          \<and> classify fl (fst (snd (snd (snd (snd (passA fl))))) ! j) = InTree"
    using scW_in_passA by (simp add: scW_in_def)
  show ?thesis using allf assms(1,2) hi by (simp add: free_in_edges_def case6_5th)
qed

text \<open>Packaging the block characterisation for a scanned edge: a slot in @{term v}'s free out-block
      is a real free edge whose tail is @{term v} (and dually the in-block, head @{term v}).\<close>

lemma free_out_edge_fst:
  assumes "v < vcount" "out_lo ! v \<le> oc" "oc < free_out_hi fl ! v"
  shows "fst_list ! (free_out_edges fl ! oc) = v \<and> is_free fl (free_out_edges fl ! oc) \<and> free_out_edges fl ! oc < m"
proof -
  have ocm: "oc < m" using assms(3) free_out_hi_le_m[OF assms(1)] by (meson order_less_le_trans)
  have em: "free_out_edges fl ! oc < m"
    using ocm free_out_edges_set by (metis length_free_out_edges nth_mem)
  have blk: "fst_list ! (free_out_edges fl ! oc) = v \<and> classify fl (free_out_edges fl ! oc) = InTree"
    using free_out_edges_block[OF assms] .
  have "is_free fl (free_out_edges fl ! oc)" using blk em by (simp add: is_free_def edge_state_nth)
  thus ?thesis using blk em by simp
qed

lemma free_in_edge_snd:
  assumes "v < vcount" "in_lo ! v \<le> ic" "ic < free_in_hi fl ! v"
  shows "snd_list ! (free_in_edges fl ! ic) = v \<and> is_free fl (free_in_edges fl ! ic) \<and> free_in_edges fl ! ic < m"
proof -
  have icm: "ic < m" using assms(3) free_in_hi_le_m[OF assms(1)] by (meson order_less_le_trans)
  have em: "free_in_edges fl ! ic < m"
    using icm free_in_edges_set by (metis length_free_in_edges nth_mem)
  have blk: "snd_list ! (free_in_edges fl ! ic) = v \<and> classify fl (free_in_edges fl ! ic) = InTree"
    using free_in_edges_block[OF assms] .
  have "is_free fl (free_in_edges fl ! ic)" using blk em by (simp add: is_free_def edge_state_nth)
  thus ?thesis using blk em by simp
qed

lemma build_dfs_dom_wf':
  assumes "dfs_wf s"
  shows "build_dfs_dom (fl, s)"
  using build_dfs_dom_wf[OF Hout_valid Hin_valid assms] .

subsection \<open>The whole builder is total and length-preserving\<close>

text \<open>Opening a component seeds the stack with a single frame at a real vertex \<open>c < vcount\<close> and
      leaves the visited array's length untouched, so its pre-@{const build_dfs} state is well-formed;
      hence the internal traversal terminates and preserves @{const dfs_sized}. The two phase scans and
      the final root \<open>lsuc\<close> write then carry @{const dfs_sized} all the way to @{const build_tree}.\<close>

lemma open_tree_component_sized:
  assumes sz: "dfs_sized s" and c: "c < vcount"
  shows "dfs_sized (open_tree_component fl s c)"
  unfolding open_tree_component_def Let_def
  apply (rule build_dfs_sized)
   apply (rule build_dfs_dom_wf')
   apply (auto simp: dfs_wf_def c sz[unfolded dfs_sized_def])[1]
  apply (auto simp: dfs_sized_def sz[unfolded dfs_sized_def])[1]
  done

lemma phase1_step_sized:
  assumes "v < vcount" "dfs_sized s"
  shows "dfs_sized (phase1_step fl v s)"
  using assms open_tree_component_sized[OF assms(2) assms(1)] emit_U_edge_sized[OF assms(2)]
  by (auto simp: phase1_step_def)

lemma phase2_step_sized:
  assumes "v < vcount" "dfs_sized s"
  shows "dfs_sized (phase2_step fl v s)"
  using assms open_tree_component_sized[OF assms(2) assms(1)]
  by (auto simp: phase2_step_def)

lemma phase1_sized:
  assumes "dfs_sized s" shows "dfs_sized (phase1 fl s)"
  unfolding phase1_def
  apply (rule fold_invariant[where Q = "\<lambda>v. v < vcount"])
    apply (simp add: vs_less_vcount)
   apply (rule assms)
  apply (erule (1) phase1_step_sized)
  done

lemma phase2_sized:
  assumes "dfs_sized s" shows "dfs_sized (phase2 fl s)"
  unfolding phase2_def
  apply (rule fold_invariant[where Q = "\<lambda>v. v < vcount"])
    apply (simp add: vs_less_vcount)
   apply (rule assms)
  apply (erule (1) phase2_step_sized)
  done

lemma build_tree_sized: "dfs_sized (build_tree fl)"
  unfolding build_tree_def Let_def
  using phase2_sized[OF phase1_sized[OF dfs_init_sized]]
  by (simp add: dfs_sized_def)

section \<open>The structural builder invariant (I1/I2 core)\<close>

text \<open>The first tree-shaped invariant maintained by the whole builder: the artificial root
      @{term vcount} is never marked visited, every vertex currently on the DFS stack is visited, and
      every visited real vertex's parent is either the root or another visited vertex. Together with
      the fact that a parent is fixed (when a vertex is first discovered) to a vertex already visited,
      this is the rooted-forest-towards-@{term vcount} skeleton underlying @{term arb_invar} (design
      notes I1/I2). We carry it bundled with @{const dfs_wf} and @{const dfs_sized}, since maintaining
      the parent clause across a discovery needs both the discovered vertex's range (\<open>dfs_wf\<close>, via the
      holed-scatter) and the parent array's length (\<open>dfs_sized\<close>).\<close>

definition tree_seen_inv :: "'n dfs_state \<Rightarrow> bool" where
  "tree_seen_inv s \<longleftrightarrow>
     \<not> ds_seen s ! vcount \<and>
     (\<forall>(v,oc,ic)\<in>set (ds_stk s). ds_seen s ! v) \<and>
     (\<forall>w. w < vcount \<longrightarrow> ds_seen s ! w \<longrightarrow>
        ds_prnt s ! w = vcount \<or> (ds_prnt s ! w < vcount \<and> ds_seen s ! (ds_prnt s ! w)))"

subsection \<open>Maintenance across the three recursive calls\<close>

lemma bd_upd1_tsi:
  assumes Hout: "\<And>u j. u < vcount \<Longrightarrow> out_lo ! u \<le> j \<Longrightarrow> j < free_out_hi fl ! u \<Longrightarrow> snd_list ! (free_out_edges fl ! j) < vcount"
      and wf: "dfs_wf s" and sz: "dfs_sized s" and tsi: "tree_seen_inv s" and c: "bd_call1_conds fl s"
  shows "tree_seen_inv (bd_upd1 fl s)"
proof -
  from c obtain v oc ic rest where stk: "ds_stk s = (v, oc, ic) # rest" and oclt: "oc < free_out_hi fl ! v"
    by (auto simp: bd_call1_conds_def split: list.splits prod.splits)
  from wf stk have vlt: "v < vcount" and olo: "out_lo ! v \<le> oc" and len: "length (ds_seen s) = Suc vcount"
    by (auto simp: dfs_wf_def)
  have lenp: "length (ds_prnt s) = Suc vcount" using sz by (simp add: dfs_sized_def)
  let ?w = "snd_list ! (free_out_edges fl ! oc)"
  have wlt: "?w < vcount" using Hout[OF vlt olo oclt] .
  from tsi have root: "\<not> ds_seen s ! vcount"
    and sseen: "\<forall>(v',oc',ic')\<in>set (ds_stk s). ds_seen s ! v'"
    and par: "\<forall>w<vcount. ds_seen s ! w \<longrightarrow> ds_prnt s ! w = vcount \<or> (ds_prnt s ! w < vcount \<and> ds_seen s ! (ds_prnt s ! w))"
    by (auto simp: tree_seen_inv_def)
  have vseen: "ds_seen s ! v" using sseen stk by auto
  have restseen: "\<forall>(a,b,c)\<in>set rest. ds_seen s ! a" using sseen stk by auto
  show ?thesis
  proof (cases "ds_seen s ! ?w")
    case True
    have "bd_upd1 fl s = s\<lparr>ds_stk := (v, Suc oc, ic) # rest\<rparr>" using stk True by (simp add: bd_upd1_def Let_def)
    thus ?thesis using root sseen par stk by (auto simp: tree_seen_inv_def)
  next
    case False
    have up: "bd_upd1 fl s = dfs_discover (s\<lparr>ds_stk := (v, Suc oc, ic) # rest\<rparr>) v ?w (free_out_edges fl ! oc)"
      using stk False by (simp add: bd_upd1_def Let_def)
    have neq: "\<And>v'. ds_seen s ! v' \<Longrightarrow> v' \<noteq> ?w" using False by auto
    show ?thesis
      unfolding up tree_seen_inv_def
      using root par vseen wlt vlt False neq len lenp restseen
      by (auto simp: dfs_discover_def Let_def nth_list_update)
  qed
qed

lemma bd_upd2_tsi:
  assumes Hin: "\<And>u j. u < vcount \<Longrightarrow> in_lo ! u \<le> j \<Longrightarrow> j < free_in_hi fl ! u \<Longrightarrow> fst_list ! (free_in_edges fl ! j) < vcount"
      and wf: "dfs_wf s" and sz: "dfs_sized s" and tsi: "tree_seen_inv s" and c: "bd_call2_conds fl s"
  shows "tree_seen_inv (bd_upd2 fl s)"
proof -
  from c obtain v oc ic rest where stk: "ds_stk s = (v, oc, ic) # rest"
      and noc: "\<not> oc < free_out_hi fl ! v" and iclt: "ic < free_in_hi fl ! v"
    by (auto simp: bd_call2_conds_def split: list.splits prod.splits)
  from wf stk have vlt: "v < vcount" and ilo: "in_lo ! v \<le> ic" and len: "length (ds_seen s) = Suc vcount"
    by (auto simp: dfs_wf_def)
  have lenp: "length (ds_prnt s) = Suc vcount" using sz by (simp add: dfs_sized_def)
  let ?w = "fst_list ! (free_in_edges fl ! ic)"
  have wlt: "?w < vcount" using Hin[OF vlt ilo iclt] .
  from tsi have root: "\<not> ds_seen s ! vcount"
    and sseen: "\<forall>(v',oc',ic')\<in>set (ds_stk s). ds_seen s ! v'"
    and par: "\<forall>w<vcount. ds_seen s ! w \<longrightarrow> ds_prnt s ! w = vcount \<or> (ds_prnt s ! w < vcount \<and> ds_seen s ! (ds_prnt s ! w))"
    by (auto simp: tree_seen_inv_def)
  have vseen: "ds_seen s ! v" using sseen stk by auto
  have restseen: "\<forall>(a,b,c)\<in>set rest. ds_seen s ! a" using sseen stk by auto
  show ?thesis
  proof (cases "ds_seen s ! ?w")
    case True
    have "bd_upd2 fl s = s\<lparr>ds_stk := (v, oc, Suc ic) # rest\<rparr>" using stk True by (simp add: bd_upd2_def Let_def)
    thus ?thesis using root sseen par stk by (auto simp: tree_seen_inv_def)
  next
    case False
    have up: "bd_upd2 fl s = dfs_discover (s\<lparr>ds_stk := (v, oc, Suc ic) # rest\<rparr>) v ?w (free_in_edges fl ! ic)"
      using stk False by (simp add: bd_upd2_def Let_def)
    have neq: "\<And>v'. ds_seen s ! v' \<Longrightarrow> v' \<noteq> ?w" using False by auto
    show ?thesis
      unfolding up tree_seen_inv_def
      using root par vseen wlt vlt False neq len lenp restseen
      by (auto simp: dfs_discover_def Let_def nth_list_update)
  qed
qed

lemma bd_upd3_tsi:
  assumes tsi: "tree_seen_inv s" and c: "bd_call3_conds fl s"
  shows "tree_seen_inv (bd_upd3 s)"
proof -
  from c obtain v oc ic rest where stk: "ds_stk s = (v, oc, ic) # rest"
    by (auto simp: bd_call3_conds_def split: list.splits prod.splits)
  have "bd_upd3 s = dfs_finish s v rest" using stk by (simp add: bd_upd3_def)
  thus ?thesis using tsi stk by (auto simp: tree_seen_inv_def dfs_finish_def Let_def)
qed

section \<open>The thread invariant (I5)\<close>

text \<open>The builder threads every emitted vertex into a singly-linked list in emission order: at each
      discovery / component-opening it links the fresh vertex \<open>w\<close> after the last emitted vertex
      \<open>ds_prev s\<close> (setting \<open>ds_thrd s ! (ds_prev s)\<close> to \<open>w\<close> and \<open>ds_rvth s ! w\<close> to \<open>ds_prev s\<close>) and
      makes \<open>w\<close> the new last, the root @{term vcount} being the first emitted vertex. The following
      invariant records that @{const ds_thrd} and @{const ds_rvth} are \<^emph>\<open>mutual inverses\<close> on the emitted
      vertices (\<open>rvth \<circ> thrd = id\<close> away from the last, \<open>thrd \<circ> rvth = id\<close> away from the root), that the
      last-emitted vertex has no successor and the root no predecessor, that all links out of a
      not-yet-emitted vertex are still the null sentinel \<open>0\<close>, and that vertex \<open>0\<close> itself is never
      emitted (\<open>no_zero_node\<close> makes \<open>0\<close> a pure sentinel --- no real vertex collides with it, which is
      exactly what lets the backward inverse go through). A vertex is \<^emph>\<open>emitted\<close> exactly when it is the
      root or is visited. This is design-notes clause I5; it feeds \<open>parent_spec\<close> of the thread and
      reverse-thread maps and the mutual-inverse clauses of \<open>arb_invar\<close>. It touches only the thread
      fields, so it needs neither the free-edge scatter characterisation nor the parent map.\<close>

definition thread_inv :: "'n dfs_state \<Rightarrow> bool" where
  "thread_inv s \<longleftrightarrow>
     ds_prev s < Suc vcount \<and>
     (ds_prev s = vcount \<or> ds_seen s ! (ds_prev s)) \<and>
     ds_thrd s ! (ds_prev s) = 0 \<and>
     ds_rvth s ! vcount = 0 \<and>
     \<not> ds_seen s ! 0 \<and>
     (\<forall>x < Suc vcount. \<not> (x = vcount \<or> ds_seen s ! x) \<longrightarrow> ds_thrd s ! x = 0 \<and> ds_rvth s ! x = 0) \<and>
     (\<forall>x < Suc vcount. (x = vcount \<or> ds_seen s ! x) \<longrightarrow> x \<noteq> ds_prev s \<longrightarrow>
         ds_thrd s ! x < Suc vcount \<and> (ds_thrd s ! x = vcount \<or> ds_seen s ! (ds_thrd s ! x))
         \<and> ds_rvth s ! (ds_thrd s ! x) = x) \<and>
     (\<forall>x < Suc vcount. (x = vcount \<or> ds_seen s ! x) \<longrightarrow> x \<noteq> vcount \<longrightarrow>
         ds_rvth s ! x < Suc vcount \<and> (ds_rvth s ! x = vcount \<or> ds_seen s ! (ds_rvth s ! x))
         \<and> ds_thrd s ! (ds_rvth s ! x) = x)"

text \<open>Small helpers used throughout: writing @{term True} into a boolean array preserves the entries
      already set; and (mirroring \<open>Hout_valid\<close> / \<open>Hin_valid\<close>) a free incident edge's other endpoint is
      a genuine vertex, hence never the reserved sentinel \<open>0\<close> (by \<open>no_zero_node\<close>).\<close>

lemma nth_update_True_mono: "xs ! x \<Longrightarrow> (xs[i := True]) ! x"
  by (cases "i = x"; cases "i < length xs") (auto simp: nth_list_update_neq nth_list_update_eq list_update_beyond)

lemma Hout_nz:
  assumes "v < vcount" "out_lo ! v \<le> j" "j < free_out_hi fl ! v"
  shows "snd_list ! (free_out_edges fl ! j) \<noteq> 0"
proof -
  have jm: "j < m" using assms(3) free_out_hi_le_m[OF assms(1)] by (meson order_less_le_trans)
  hence "free_out_edges fl ! j \<in> set (free_out_edges fl)" by (metis length_free_out_edges nth_mem)
  hence em: "free_out_edges fl ! j < m" using free_out_edges_set by blast
  show ?thesis using snd_list_nth_vertex[OF em] no_zero_node by (metis)
qed

lemma Hin_nz:
  assumes "v < vcount" "in_lo ! v \<le> j" "j < free_in_hi fl ! v"
  shows "fst_list ! (free_in_edges fl ! j) \<noteq> 0"
proof -
  have jm: "j < m" using assms(3) free_in_hi_le_m[OF assms(1)] by (meson order_less_le_trans)
  hence "free_in_edges fl ! j \<in> set (free_in_edges fl)" by (metis length_free_in_edges nth_mem)
  hence em: "free_in_edges fl ! j < m" using free_in_edges_set by blast
  show ?thesis using fst_list_nth_vertex[OF em] no_zero_node by (metis)
qed

text \<open>The generic maintenance step: any state @{term t} whose four thread-relevant fields are the
      emission update of @{term s} at a fresh real vertex @{term w} (mark @{term w} visited, link it
      after @{term \<open>ds_prev s\<close>}, make it the new last) preserves @{const thread_inv}. Both the
      free-edge discovery @{const dfs_discover} and the component opening @{const open_tree_component}
      are instances.\<close>

lemma thread_inv_upd:
  assumes thi: "thread_inv s"
      and wlt: "w < vcount"
      and wnz: "w \<noteq> 0"
      and unseen: "\<not> ds_seen s ! w"
      and lseen: "length (ds_seen s) = Suc vcount"
      and lthrd: "length (ds_thrd s) = Suc vcount"
      and lrvth: "length (ds_rvth s) = Suc vcount"
      and P_prev: "ds_prev t = w"
      and P_seen: "ds_seen t = (ds_seen s)[w := True]"
      and P_thrd: "ds_thrd t = (ds_thrd s)[ds_prev s := w]"
      and P_rvth: "ds_rvth t = (ds_rvth s)[w := ds_prev s]"
  shows "thread_inv t"
proof -
  define pv where "pv = ds_prev s"
  from thi have pv_lt: "pv < Suc vcount"
    and pv_em: "pv = vcount \<or> ds_seen s ! pv"
    and thrd_pv0: "ds_thrd s ! pv = 0"
    and rvth_r0: "ds_rvth s ! vcount = 0"
    and zunseen: "\<not> ds_seen s ! 0"
    and unem: "\<And>x. x < Suc vcount \<Longrightarrow> \<not> (x = vcount \<or> ds_seen s ! x) \<Longrightarrow> ds_thrd s ! x = 0 \<and> ds_rvth s ! x = 0"
    and fwd: "\<And>x. x < Suc vcount \<Longrightarrow> (x = vcount \<or> ds_seen s ! x) \<Longrightarrow> x \<noteq> pv \<Longrightarrow>
                 ds_thrd s ! x < Suc vcount \<and> (ds_thrd s ! x = vcount \<or> ds_seen s ! (ds_thrd s ! x))
                 \<and> ds_rvth s ! (ds_thrd s ! x) = x"
    and bwd: "\<And>x. x < Suc vcount \<Longrightarrow> (x = vcount \<or> ds_seen s ! x) \<Longrightarrow> x \<noteq> vcount \<Longrightarrow>
                 ds_rvth s ! x < Suc vcount \<and> (ds_rvth s ! x = vcount \<or> ds_seen s ! (ds_rvth s ! x))
                 \<and> ds_thrd s ! (ds_rvth s ! x) = x"
    unfolding thread_inv_def pv_def by auto
  have wnv: "w \<noteq> vcount" using wlt by auto
  have pvw: "pv \<noteq> w" using pv_em wnv unseen by auto
  have wunem: "ds_thrd s ! w = 0 \<and> ds_rvth s ! w = 0"
    using unem[of w] wlt wnv unseen by auto
  have e_prev: "ds_prev t = w" using P_prev .
  have e_seen: "ds_seen t = (ds_seen s)[w := True]" using P_seen .
  have e_thrd: "ds_thrd t = (ds_thrd s)[pv := w]" using P_thrd pv_def by simp
  have e_rvth: "ds_rvth t = (ds_rvth s)[w := pv]" using P_rvth pv_def by simp
  show ?thesis
    unfolding thread_inv_def
  proof (intro conjI)
    show "ds_prev t < Suc vcount" using wlt e_prev by simp
  next
    show "ds_prev t = vcount \<or> ds_seen t ! (ds_prev t)"
      using e_prev e_seen lseen wlt by simp
  next
    show "ds_thrd t ! (ds_prev t) = 0"
      using e_prev e_thrd pvw wunem by (simp add: nth_list_update)
  next
    show "ds_rvth t ! vcount = 0"
      using e_rvth wnv rvth_r0 by (simp add: nth_list_update)
  next
    show "\<not> ds_seen t ! 0"
      using e_seen wnz zunseen by (simp add: nth_list_update)
  next
    show "\<forall>x < Suc vcount. \<not> (x = vcount \<or> ds_seen t ! x) \<longrightarrow> ds_thrd t ! x = 0 \<and> ds_rvth t ! x = 0"
    proof (intro allI impI)
      fix x assume xlt: "x < Suc vcount" and xun: "\<not> (x = vcount \<or> ds_seen t ! x)"
      have xw: "x \<noteq> w" using xun e_seen lseen wlt by (auto simp: nth_list_update)
      have xun': "\<not> (x = vcount \<or> ds_seen s ! x)" using xun e_seen xw by (simp add: nth_list_update)
      have xpv: "x \<noteq> pv" using xun' pv_em by auto
      have "ds_thrd s ! x = 0 \<and> ds_rvth s ! x = 0" using unem[OF xlt xun'] .
      thus "ds_thrd t ! x = 0 \<and> ds_rvth t ! x = 0"
        using e_thrd e_rvth xpv xw by (simp add: nth_list_update)
    qed
  next
    show "\<forall>x < Suc vcount. (x = vcount \<or> ds_seen t ! x) \<longrightarrow> x \<noteq> ds_prev t \<longrightarrow>
            ds_thrd t ! x < Suc vcount \<and> (ds_thrd t ! x = vcount \<or> ds_seen t ! (ds_thrd t ! x))
            \<and> ds_rvth t ! (ds_thrd t ! x) = x"
    proof (intro allI impI)
      fix x assume xlt: "x < Suc vcount" and xem: "x = vcount \<or> ds_seen t ! x" and xnw: "x \<noteq> ds_prev t"
      have xw: "x \<noteq> w" using xnw e_prev by simp
      have xem': "x = vcount \<or> ds_seen s ! x" using xem e_seen xw by (simp add: nth_list_update)
      show "ds_thrd t ! x < Suc vcount \<and> (ds_thrd t ! x = vcount \<or> ds_seen t ! (ds_thrd t ! x))
            \<and> ds_rvth t ! (ds_thrd t ! x) = x"
      proof (cases "x = pv")
        case True
        have t1: "ds_thrd t ! x = w" using e_thrd True pv_lt lthrd by (simp add: nth_list_update)
        show ?thesis using t1 wlt e_seen e_rvth True pv_def lseen lrvth
          by (simp add: nth_list_update)
      next
        case False
        from fwd[OF xlt xem' False] have y_lt: "ds_thrd s ! x < Suc vcount"
          and y_em: "ds_thrd s ! x = vcount \<or> ds_seen s ! (ds_thrd s ! x)"
          and y_rv: "ds_rvth s ! (ds_thrd s ! x) = x" by auto
        have t1: "ds_thrd t ! x = ds_thrd s ! x" using e_thrd False by (simp add: nth_list_update)
        have yw: "ds_thrd s ! x \<noteq> w" using y_em unseen wnv by auto
        show ?thesis
          using t1 y_lt y_em y_rv yw e_seen e_rvth lseen wlt
          by (simp add: nth_list_update)
      qed
    qed
  next
    show "\<forall>x < Suc vcount. (x = vcount \<or> ds_seen t ! x) \<longrightarrow> x \<noteq> vcount \<longrightarrow>
            ds_rvth t ! x < Suc vcount \<and> (ds_rvth t ! x = vcount \<or> ds_seen t ! (ds_rvth t ! x))
            \<and> ds_thrd t ! (ds_rvth t ! x) = x"
    proof (intro allI impI)
      fix x assume xlt: "x < Suc vcount" and xem: "x = vcount \<or> ds_seen t ! x" and xnr: "x \<noteq> vcount"
      have seenx: "ds_seen t ! x" using xem xnr by auto
      show "ds_rvth t ! x < Suc vcount \<and> (ds_rvth t ! x = vcount \<or> ds_seen t ! (ds_rvth t ! x))
            \<and> ds_thrd t ! (ds_rvth t ! x) = x"
      proof (cases "x = w")
        case True
        have r1: "ds_rvth t ! x = pv" using e_rvth True wlt lrvth by (simp add: nth_list_update)
        show ?thesis
        proof (intro conjI)
          show "ds_rvth t ! x < Suc vcount" using r1 pv_lt by simp
        next
          show "ds_rvth t ! x = vcount \<or> ds_seen t ! (ds_rvth t ! x)"
            using r1 pv_em e_seen nth_update_True_mono by auto
        next
          show "ds_thrd t ! (ds_rvth t ! x) = x"
            using r1 True e_thrd pv_lt lthrd by (simp add: nth_list_update)
        qed
      next
        case False
        have seenx_s: "ds_seen s ! x" using seenx e_seen False by (simp add: nth_list_update)
        have xem': "x = vcount \<or> ds_seen s ! x" using seenx_s by simp
        from bwd[OF xlt xem' xnr] have z_lt: "ds_rvth s ! x < Suc vcount"
          and z_em: "ds_rvth s ! x = vcount \<or> ds_seen s ! (ds_rvth s ! x)"
          and z_th: "ds_thrd s ! (ds_rvth s ! x) = x" by auto
        have r1: "ds_rvth t ! x = ds_rvth s ! x" using e_rvth False by (simp add: nth_list_update)
        have xnz: "x \<noteq> 0"
        proof
          assume "x = 0"
          thus False using seenx_s zunseen by simp
        qed
        have znpv: "ds_rvth s ! x \<noteq> pv"
        proof
          assume "ds_rvth s ! x = pv"
          hence "ds_thrd s ! pv = x" using z_th by simp
          thus False using thrd_pv0 xnz by simp
        qed
        show ?thesis
        proof (intro conjI)
          show "ds_rvth t ! x < Suc vcount" using r1 z_lt by simp
        next
          show "ds_rvth t ! x = vcount \<or> ds_seen t ! (ds_rvth t ! x)"
            using r1 z_em e_seen nth_update_True_mono by auto
        next
          show "ds_thrd t ! (ds_rvth t ! x) = x"
            using r1 z_th znpv e_thrd by (simp add: nth_list_update)
        qed
      qed
    qed
  qed
qed

lemma dfs_discover_thi:
  assumes thi: "thread_inv s" and wlt: "w < vcount" and wnz: "w \<noteq> 0" and unseen: "\<not> ds_seen s ! w"
      and lseen: "length (ds_seen s) = Suc vcount"
      and lthrd: "length (ds_thrd s) = Suc vcount"
      and lrvth: "length (ds_rvth s) = Suc vcount"
  shows "thread_inv (dfs_discover s v w e)"
  apply (rule thread_inv_upd[OF thi wlt wnz unseen lseen lthrd lrvth])
  by (simp_all add: dfs_discover_def Let_def)

subsection \<open>Maintenance of @{const thread_inv} across the three recursive calls\<close>

lemma bd_upd1_thi:
  assumes Hout: "\<And>u j. u < vcount \<Longrightarrow> out_lo ! u \<le> j \<Longrightarrow> j < free_out_hi fl ! u \<Longrightarrow> snd_list ! (free_out_edges fl ! j) < vcount"
      and wf: "dfs_wf s" and sz: "dfs_sized s" and thi: "thread_inv s" and c: "bd_call1_conds fl s"
  shows "thread_inv (bd_upd1 fl s)"
proof -
  from c obtain v oc ic rest where stk: "ds_stk s = (v, oc, ic) # rest" and oclt: "oc < free_out_hi fl ! v"
    by (auto simp: bd_call1_conds_def split: list.splits prod.splits)
  from wf stk have vlt: "v < vcount" and olo: "out_lo ! v \<le> oc" by (auto simp: dfs_wf_def)
  have lseen: "length (ds_seen s) = Suc vcount" and lthrd: "length (ds_thrd s) = Suc vcount"
       and lrvth: "length (ds_rvth s) = Suc vcount" using sz by (auto simp: dfs_sized_def)
  let ?w = "snd_list ! (free_out_edges fl ! oc)"
  have wlt: "?w < vcount" using Hout[OF vlt olo oclt] .
  have wnz: "?w \<noteq> 0" using Hout_nz[OF vlt olo oclt] .
  show ?thesis
  proof (cases "ds_seen s ! ?w")
    case True
    have "bd_upd1 fl s = s\<lparr>ds_stk := (v, Suc oc, ic) # rest\<rparr>" using stk True by (simp add: bd_upd1_def Let_def)
    thus ?thesis using thi by (simp add: thread_inv_def)
  next
    case False
    let ?s1 = "s\<lparr>ds_stk := (v, Suc oc, ic) # rest\<rparr>"
    have up: "bd_upd1 fl s = dfs_discover ?s1 v ?w (free_out_edges fl ! oc)"
      using stk False by (simp add: bd_upd1_def Let_def)
    have "thread_inv (dfs_discover ?s1 v ?w (free_out_edges fl ! oc))"
      using thi wlt wnz False lseen lthrd lrvth
      by (intro dfs_discover_thi) (simp_all add: thread_inv_def)
    thus ?thesis using up by simp
  qed
qed

lemma bd_upd2_thi:
  assumes Hin: "\<And>u j. u < vcount \<Longrightarrow> in_lo ! u \<le> j \<Longrightarrow> j < free_in_hi fl ! u \<Longrightarrow> fst_list ! (free_in_edges fl ! j) < vcount"
      and wf: "dfs_wf s" and sz: "dfs_sized s" and thi: "thread_inv s" and c: "bd_call2_conds fl s"
  shows "thread_inv (bd_upd2 fl s)"
proof -
  from c obtain v oc ic rest where stk: "ds_stk s = (v, oc, ic) # rest"
      and noc: "\<not> oc < free_out_hi fl ! v" and iclt: "ic < free_in_hi fl ! v"
    by (auto simp: bd_call2_conds_def split: list.splits prod.splits)
  from wf stk have vlt: "v < vcount" and ilo: "in_lo ! v \<le> ic" by (auto simp: dfs_wf_def)
  have lseen: "length (ds_seen s) = Suc vcount" and lthrd: "length (ds_thrd s) = Suc vcount"
       and lrvth: "length (ds_rvth s) = Suc vcount" using sz by (auto simp: dfs_sized_def)
  let ?w = "fst_list ! (free_in_edges fl ! ic)"
  have wlt: "?w < vcount" using Hin[OF vlt ilo iclt] .
  have wnz: "?w \<noteq> 0" using Hin_nz[OF vlt ilo iclt] .
  show ?thesis
  proof (cases "ds_seen s ! ?w")
    case True
    have "bd_upd2 fl s = s\<lparr>ds_stk := (v, oc, Suc ic) # rest\<rparr>" using stk True by (simp add: bd_upd2_def Let_def)
    thus ?thesis using thi by (simp add: thread_inv_def)
  next
    case False
    let ?s1 = "s\<lparr>ds_stk := (v, oc, Suc ic) # rest\<rparr>"
    have up: "bd_upd2 fl s = dfs_discover ?s1 v ?w (free_in_edges fl ! ic)"
      using stk False by (simp add: bd_upd2_def Let_def)
    have "thread_inv (dfs_discover ?s1 v ?w (free_in_edges fl ! ic))"
      using thi wlt wnz False lseen lthrd lrvth
      by (intro dfs_discover_thi) (simp_all add: thread_inv_def)
    thus ?thesis using up by simp
  qed
qed

lemma bd_upd3_thi:
  assumes thi: "thread_inv s" and c: "bd_call3_conds fl s"
  shows "thread_inv (bd_upd3 s)"
proof -
  from c obtain v oc ic rest where stk: "ds_stk s = (v, oc, ic) # rest"
    by (auto simp: bd_call3_conds_def split: list.splits prod.splits)
  have "bd_upd3 s = dfs_finish s v rest" using stk by (simp add: bd_upd3_def)
  thus ?thesis using thi by (simp add: thread_inv_def dfs_finish_def Let_def)
qed

text \<open>The two non-recursive emitters: a saturated @{term U} edge changes no thread field; the initial
      state has the root as sole emitted vertex with all links null.\<close>

lemma emit_U_edge_thi: "thread_inv s \<Longrightarrow> thread_inv (emit_U_edge s v)"
  by (simp add: thread_inv_def emit_U_edge_def Let_def)

lemma dfs_init_thi: "thread_inv dfs_init"
  by (auto simp add: thread_inv_def dfs_init_def simp del: replicate_Suc)

subsection \<open>The bundled invariant and its propagation to @{const build_tree}\<close>

section \<open>The parent-edge invariant (I3)\<close>

text \<open>Design-notes clause I3, for the \<^emph>\<open>interior\<close> tree edges. Every visited non-root vertex @{term w}
      whose parent @{term \<open>ds_prnt s ! w\<close>} is itself a real vertex (\<open>< vcount\<close>, i.e.\ @{term w} was
      discovered inside a component, not opened as a component root) has @{term \<open>ds_par s ! w\<close>} equal
      to the free real edge across which it was discovered: that edge is \<open>< m\<close> (real), free,
      and its endpoints are exactly @{term \<open>{w, ds_prnt s ! w}\<close>}, oriented so that
      @{term \<open>ds_dir s ! w = (fst_list ! (ds_par s ! w) = w)\<close>} (\<open>True\<close> iff the edge points \<open>w \<rightarrow> parent\<close>,
      up toward the root). The linchpin is the holed-scatter block characterisation
      (@{thm free_out_edge_fst} / @{thm free_in_edge_snd}): a vertex discovered in @{term v}'s out-scan
      is joined to @{term v} by an edge whose tail is @{term v}, and dually in-scan by an edge whose
      head is @{term v}. Component roots (\<open>prnt = vcount\<close>) carry an \<^emph>\<open>artificial\<close> edge and are excluded
      here; they are handled by the augmented-array assembly. This clause feeds \<open>H1\<close> parent-edge
      injectivity and the \<open>init_tree_corr\<close> orientation obligation.\<close>

definition par_edge_inv :: "'n list \<Rightarrow> 'n dfs_state \<Rightarrow> bool" where
  "par_edge_inv fl s \<longleftrightarrow>
     (\<forall>w<vcount. ds_seen s ! w \<longrightarrow> ds_prnt s ! w < vcount \<longrightarrow>
        ds_par s ! w < m \<and> is_free fl (ds_par s ! w)
        \<and> ds_dir s ! w = (fst_list ! (ds_par s ! w) = w)
        \<and> fst_list ! (ds_par s ! w) = (if ds_dir s ! w then w else ds_prnt s ! w)
        \<and> snd_list ! (ds_par s ! w) = (if ds_dir s ! w then ds_prnt s ! w else w))"

lemma bd_upd3_pei:
  assumes pei: "par_edge_inv fl s" and c: "bd_call3_conds fl s"
  shows "par_edge_inv fl (bd_upd3 s)"
proof -
  from c obtain v oc ic rest where stk: "ds_stk s = (v, oc, ic) # rest"
    by (auto simp: bd_call3_conds_def split: list.splits prod.splits)
  have "bd_upd3 s = dfs_finish s v rest" using stk by (simp add: bd_upd3_def)
  thus ?thesis using pei by (auto simp: par_edge_inv_def dfs_finish_def Let_def)
qed

lemma bd_upd1_pei:
  assumes wf: "dfs_wf s" and sz: "dfs_sized s" and tsi: "tree_seen_inv s"
      and pei: "par_edge_inv fl s" and c: "bd_call1_conds fl s"
  shows "par_edge_inv fl (bd_upd1 fl s)"
proof -
  from c obtain v oc ic rest where stk: "ds_stk s = (v, oc, ic) # rest" and oclt: "oc < free_out_hi fl ! v"
    by (auto simp: bd_call1_conds_def split: list.splits prod.splits)
  from wf stk have vlt: "v < vcount" and olo: "out_lo ! v \<le> oc"
    by (auto simp: dfs_wf_def)
  let ?e = "free_out_edges fl ! oc"
  let ?w = "snd_list ! ?e"
  have realise: "fst_list ! ?e = v \<and> is_free fl ?e \<and> ?e < m" using free_out_edge_fst[OF vlt olo oclt] .
  have wlt: "?w < vcount" using Hout_valid[OF vlt olo oclt] .
  have lens: "length (ds_seen s) = Suc vcount" "length (ds_prnt s) = Suc vcount"
             "length (ds_par s) = Suc vcount" "length (ds_dir s) = Suc vcount"
    using sz by (auto simp: dfs_sized_def)
  from tsi have sseen: "\<forall>(v',oc',ic')\<in>set (ds_stk s). ds_seen s ! v'" by (auto simp: tree_seen_inv_def)
  have vseen: "ds_seen s ! v" using sseen stk by auto
  from pei have peiC: "\<forall>w<vcount. ds_seen s ! w \<longrightarrow> ds_prnt s ! w < vcount \<longrightarrow>
        ds_par s ! w < m \<and> is_free fl (ds_par s ! w) \<and> ds_dir s ! w = (fst_list ! (ds_par s ! w) = w)
        \<and> fst_list ! (ds_par s ! w) = (if ds_dir s ! w then w else ds_prnt s ! w)
        \<and> snd_list ! (ds_par s ! w) = (if ds_dir s ! w then ds_prnt s ! w else w)"
    by (simp add: par_edge_inv_def)
  show ?thesis
  proof (cases "ds_seen s ! ?w")
    case True
    have "bd_upd1 fl s = s\<lparr>ds_stk := (v, Suc oc, ic) # rest\<rparr>" using stk True by (simp add: bd_upd1_def Let_def)
    thus ?thesis using pei by (simp add: par_edge_inv_def)
  next
    case False
    have up: "bd_upd1 fl s = dfs_discover (s\<lparr>ds_stk := (v, Suc oc, ic) # rest\<rparr>) v ?w ?e"
      using stk False by (simp add: bd_upd1_def Let_def)
    have neq: "v \<noteq> ?w" using vseen False by auto
    have dirw: "(fst_list ! ?e = ?w) = False" using realise neq by auto
    show ?thesis
      unfolding up par_edge_inv_def
      using peiC realise wlt neq dirw False vlt lens
      by (auto simp: dfs_discover_def Let_def nth_list_update)
  qed
qed

lemma bd_upd2_pei:
  assumes wf: "dfs_wf s" and sz: "dfs_sized s" and tsi: "tree_seen_inv s"
      and pei: "par_edge_inv fl s" and c: "bd_call2_conds fl s"
  shows "par_edge_inv fl (bd_upd2 fl s)"
proof -
  from c obtain v oc ic rest where stk: "ds_stk s = (v, oc, ic) # rest"
      and noc: "\<not> oc < free_out_hi fl ! v" and iclt: "ic < free_in_hi fl ! v"
    by (auto simp: bd_call2_conds_def split: list.splits prod.splits)
  from wf stk have vlt: "v < vcount" and ilo: "in_lo ! v \<le> ic"
    by (auto simp: dfs_wf_def)
  let ?e = "free_in_edges fl ! ic"
  let ?w = "fst_list ! ?e"
  have realise: "snd_list ! ?e = v \<and> is_free fl ?e \<and> ?e < m" using free_in_edge_snd[OF vlt ilo iclt] .
  have wlt: "?w < vcount" using Hin_valid[OF vlt ilo iclt] .
  have lens: "length (ds_seen s) = Suc vcount" "length (ds_prnt s) = Suc vcount"
             "length (ds_par s) = Suc vcount" "length (ds_dir s) = Suc vcount"
    using sz by (auto simp: dfs_sized_def)
  from tsi have sseen: "\<forall>(v',oc',ic')\<in>set (ds_stk s). ds_seen s ! v'" by (auto simp: tree_seen_inv_def)
  have vseen: "ds_seen s ! v" using sseen stk by auto
  from pei have peiC: "\<forall>w<vcount. ds_seen s ! w \<longrightarrow> ds_prnt s ! w < vcount \<longrightarrow>
        ds_par s ! w < m \<and> is_free fl (ds_par s ! w) \<and> ds_dir s ! w = (fst_list ! (ds_par s ! w) = w)
        \<and> fst_list ! (ds_par s ! w) = (if ds_dir s ! w then w else ds_prnt s ! w)
        \<and> snd_list ! (ds_par s ! w) = (if ds_dir s ! w then ds_prnt s ! w else w)"
    by (simp add: par_edge_inv_def)
  show ?thesis
  proof (cases "ds_seen s ! ?w")
    case True
    have "bd_upd2 fl s = s\<lparr>ds_stk := (v, oc, Suc ic) # rest\<rparr>" using stk True by (simp add: bd_upd2_def Let_def)
    thus ?thesis using pei by (simp add: par_edge_inv_def)
  next
    case False
    have up: "bd_upd2 fl s = dfs_discover (s\<lparr>ds_stk := (v, oc, Suc ic) # rest\<rparr>) v ?w ?e"
      using stk False by (simp add: bd_upd2_def Let_def)
    have neq: "v \<noteq> ?w" using vseen False by auto
    show ?thesis
      unfolding up par_edge_inv_def
      using peiC realise wlt neq False vlt lens
      by (auto simp: dfs_discover_def Let_def nth_list_update)
  qed
qed

section \<open>The potential invariant (I4)\<close>

text \<open>Design-notes clause I4, at the tagged-pair (\<open>pval\<close>) level for the interior tree edges. Every
      visited non-root vertex @{term w} with an interior parent (\<open>prnt < vcount\<close>) has its potential
      obtained from its parent's by adding an \<open>M_0\<close>-tagged \<open>\<plusminus> cost_list ! (ds_par s ! w)\<close>, the sign
      chosen so the tree edge \<open>ds_par s ! w\<close> has zero reduced cost: \<open>+ cost\<close> when @{term w}'s parent
      is the edge's tail, \<open>- cost\<close> otherwise. This is exactly the update @{const dfs_discover}
      performs (its \<open>sgn\<close> formula is syntactically this one, with \<open>v = ds_prnt s ! w\<close> and
      \<open>e = ds_par s ! w\<close>), and potentials are never rewritten, so the equation persists. The
      \<open>pval_abstract\<close>-level zero-reduced-cost \<open>c-pi (ds_par s ! w) = 0\<close> follows once the faithful
      decomposition (\<open>good_pot_val\<close>) is available at \<open>arb_invar\<close> assembly. Component roots
      (\<open>prnt = vcount\<close>) are excluded; their potential is seeded to a big-\<open>M\<close> tagged value.\<close>

definition pot_inv :: "'n dfs_state \<Rightarrow> bool" where
  "pot_inv s \<longleftrightarrow>
     (\<forall>w<vcount. ds_seen s ! w \<longrightarrow> ds_prnt s ! w < vcount \<longrightarrow>
        ds_pot s ! w = pval_plus (ds_pot s ! (ds_prnt s ! w))
           (M_0, if ds_prnt s ! w = fst_list ! (ds_par s ! w)
                 then cost_list ! (ds_par s ! w) else - cost_list ! (ds_par s ! w)))"

lemma bd_upd3_pot:
  assumes poti: "pot_inv s" and c: "bd_call3_conds fl s"
  shows "pot_inv (bd_upd3 s)"
proof -
  from c obtain v oc ic rest where stk: "ds_stk s = (v, oc, ic) # rest"
    by (auto simp: bd_call3_conds_def split: list.splits prod.splits)
  have "bd_upd3 s = dfs_finish s v rest" using stk by (simp add: bd_upd3_def)
  thus ?thesis using poti by (auto simp: pot_inv_def dfs_finish_def Let_def)
qed

lemma bd_upd1_pot:
  assumes wf: "dfs_wf s" and sz: "dfs_sized s" and tsi: "tree_seen_inv s"
      and poti: "pot_inv s" and c: "bd_call1_conds fl s"
  shows "pot_inv (bd_upd1 fl s)"
proof -
  from c obtain v oc ic rest where stk: "ds_stk s = (v, oc, ic) # rest" and oclt: "oc < free_out_hi fl ! v"
    by (auto simp: bd_call1_conds_def split: list.splits prod.splits)
  from wf stk have vlt: "v < vcount" and olo: "out_lo ! v \<le> oc"
    by (auto simp: dfs_wf_def)
  let ?e = "free_out_edges fl ! oc"
  let ?w = "snd_list ! ?e"
  have wlt: "?w < vcount" using Hout_valid[OF vlt olo oclt] .
  have lens: "length (ds_seen s) = Suc vcount" "length (ds_prnt s) = Suc vcount"
             "length (ds_par s) = Suc vcount" "length (ds_pot s) = Suc vcount"
    using sz by (auto simp: dfs_sized_def)
  from tsi have sseen: "\<forall>(v',oc',ic')\<in>set (ds_stk s). ds_seen s ! v'"
    and par: "\<forall>w<vcount. ds_seen s ! w \<longrightarrow> ds_prnt s ! w = vcount \<or> (ds_prnt s ! w < vcount \<and> ds_seen s ! (ds_prnt s ! w))"
    by (auto simp: tree_seen_inv_def)
  have vseen: "ds_seen s ! v" using sseen stk by auto
  from poti have potC: "\<forall>w<vcount. ds_seen s ! w \<longrightarrow> ds_prnt s ! w < vcount \<longrightarrow>
        ds_pot s ! w = pval_plus (ds_pot s ! (ds_prnt s ! w))
           (M_0, if ds_prnt s ! w = fst_list ! (ds_par s ! w)
                 then cost_list ! (ds_par s ! w) else - cost_list ! (ds_par s ! w))"
    by (simp add: pot_inv_def)
  show ?thesis
  proof (cases "ds_seen s ! ?w")
    case True
    have "bd_upd1 fl s = s\<lparr>ds_stk := (v, Suc oc, ic) # rest\<rparr>" using stk True by (simp add: bd_upd1_def Let_def)
    thus ?thesis using poti by (simp add: pot_inv_def)
  next
    case False
    define t where "t = dfs_discover (s\<lparr>ds_stk := (v, Suc oc, ic) # rest\<rparr>) v ?w ?e"
    have up: "bd_upd1 fl s = t" using stk False t_def by (simp add: bd_upd1_def Let_def)
    have vne: "v \<noteq> ?w" using vseen False by auto
    have neq: "\<And>w'. ds_seen s ! w' \<Longrightarrow> w' \<noteq> ?w" using False by auto
    have pne: "\<And>w. w < vcount \<Longrightarrow> ds_seen s ! w \<Longrightarrow> ds_prnt s ! w < vcount \<Longrightarrow> ds_prnt s ! w \<noteq> ?w"
      using par neq by fastforce
    have e_seen: "ds_seen t = (ds_seen s)[?w := True]" by (simp add: t_def dfs_discover_def Let_def)
    have e_prnt: "ds_prnt t = (ds_prnt s)[?w := v]" by (simp add: t_def dfs_discover_def Let_def)
    have e_par:  "ds_par t = (ds_par s)[?w := ?e]" by (simp add: t_def dfs_discover_def Let_def)
    have e_pot:  "ds_pot t = (ds_pot s)[?w := pval_plus (ds_pot s ! v)
                    (M_0, if v = fst_list ! ?e then cost_list ! ?e else - cost_list ! ?e)]"
      by (simp add: t_def dfs_discover_def Let_def)
    show ?thesis
      unfolding up pot_inv_def
    proof (intro allI impI)
      fix w assume wv: "w < vcount" and ws: "ds_seen t ! w" and wp: "ds_prnt t ! w < vcount"
      show "ds_pot t ! w = pval_plus (ds_pot t ! (ds_prnt t ! w))
              (M_0, if ds_prnt t ! w = fst_list ! (ds_par t ! w)
                    then cost_list ! (ds_par t ! w) else - cost_list ! (ds_par t ! w))"
      proof (cases "w = ?w")
        case True
        have p1: "ds_prnt t ! w = v" using True e_prnt wlt lens by (simp add: nth_list_update)
        have p2: "ds_par t ! w = ?e" using True e_par wlt lens by (simp add: nth_list_update)
        have p3: "ds_pot t ! w = pval_plus (ds_pot s ! v)
                    (M_0, if v = fst_list ! ?e then cost_list ! ?e else - cost_list ! ?e)"
          using True e_pot wlt lens by (simp add: nth_list_update)
        have p4: "ds_pot t ! v = ds_pot s ! v" using vne e_pot by (simp add: nth_list_update)
        show ?thesis using p1 p2 p3 p4 by simp
      next
        case ww: False
        have s_ws: "ds_seen s ! w" using ws e_seen ww by (simp add: nth_list_update)
        have p1: "ds_prnt t ! w = ds_prnt s ! w" using ww e_prnt by (simp add: nth_list_update)
        have p2: "ds_par t ! w = ds_par s ! w" using ww e_par by (simp add: nth_list_update)
        have p3: "ds_pot t ! w = ds_pot s ! w" using ww e_pot by (simp add: nth_list_update)
        have wps: "ds_prnt s ! w < vcount" using wp p1 by simp
        have prntne: "ds_prnt s ! w \<noteq> ?w" using pne wv s_ws wps by simp
        have p4: "ds_pot t ! (ds_prnt s ! w) = ds_pot s ! (ds_prnt s ! w)"
          using prntne e_pot by (simp add: nth_list_update)
        have "ds_pot s ! w = pval_plus (ds_pot s ! (ds_prnt s ! w))
                (M_0, if ds_prnt s ! w = fst_list ! (ds_par s ! w)
                      then cost_list ! (ds_par s ! w) else - cost_list ! (ds_par s ! w))"
          using potC wv s_ws wps by simp
        thus ?thesis using p1 p2 p3 p4 by simp
      qed
    qed
  qed
qed

lemma bd_upd2_pot:
  assumes wf: "dfs_wf s" and sz: "dfs_sized s" and tsi: "tree_seen_inv s"
      and poti: "pot_inv s" and c: "bd_call2_conds fl s"
  shows "pot_inv (bd_upd2 fl s)"
proof -
  from c obtain v oc ic rest where stk: "ds_stk s = (v, oc, ic) # rest"
      and noc: "\<not> oc < free_out_hi fl ! v" and iclt: "ic < free_in_hi fl ! v"
    by (auto simp: bd_call2_conds_def split: list.splits prod.splits)
  from wf stk have vlt: "v < vcount" and ilo: "in_lo ! v \<le> ic"
    by (auto simp: dfs_wf_def)
  let ?e = "free_in_edges fl ! ic"
  let ?w = "fst_list ! ?e"
  have wlt: "?w < vcount" using Hin_valid[OF vlt ilo iclt] .
  have lens: "length (ds_seen s) = Suc vcount" "length (ds_prnt s) = Suc vcount"
             "length (ds_par s) = Suc vcount" "length (ds_pot s) = Suc vcount"
    using sz by (auto simp: dfs_sized_def)
  from tsi have sseen: "\<forall>(v',oc',ic')\<in>set (ds_stk s). ds_seen s ! v'"
    and par: "\<forall>w<vcount. ds_seen s ! w \<longrightarrow> ds_prnt s ! w = vcount \<or> (ds_prnt s ! w < vcount \<and> ds_seen s ! (ds_prnt s ! w))"
    by (auto simp: tree_seen_inv_def)
  have vseen: "ds_seen s ! v" using sseen stk by auto
  from poti have potC: "\<forall>w<vcount. ds_seen s ! w \<longrightarrow> ds_prnt s ! w < vcount \<longrightarrow>
        ds_pot s ! w = pval_plus (ds_pot s ! (ds_prnt s ! w))
           (M_0, if ds_prnt s ! w = fst_list ! (ds_par s ! w)
                 then cost_list ! (ds_par s ! w) else - cost_list ! (ds_par s ! w))"
    by (simp add: pot_inv_def)
  show ?thesis
  proof (cases "ds_seen s ! ?w")
    case True
    have "bd_upd2 fl s = s\<lparr>ds_stk := (v, oc, Suc ic) # rest\<rparr>" using stk True by (simp add: bd_upd2_def Let_def)
    thus ?thesis using poti by (simp add: pot_inv_def)
  next
    case False
    define t where "t = dfs_discover (s\<lparr>ds_stk := (v, oc, Suc ic) # rest\<rparr>) v ?w ?e"
    have up: "bd_upd2 fl s = t" using stk False t_def by (simp add: bd_upd2_def Let_def)
    have vne: "v \<noteq> ?w" using vseen False by auto
    have neq: "\<And>w'. ds_seen s ! w' \<Longrightarrow> w' \<noteq> ?w" using False by auto
    have pne: "\<And>w. w < vcount \<Longrightarrow> ds_seen s ! w \<Longrightarrow> ds_prnt s ! w < vcount \<Longrightarrow> ds_prnt s ! w \<noteq> ?w"
      using par neq by fastforce
    have e_seen: "ds_seen t = (ds_seen s)[?w := True]" by (simp add: t_def dfs_discover_def Let_def)
    have e_prnt: "ds_prnt t = (ds_prnt s)[?w := v]" by (simp add: t_def dfs_discover_def Let_def)
    have e_par:  "ds_par t = (ds_par s)[?w := ?e]" by (simp add: t_def dfs_discover_def Let_def)
    have e_pot:  "ds_pot t = (ds_pot s)[?w := pval_plus (ds_pot s ! v)
                    (M_0, if v = fst_list ! ?e then cost_list ! ?e else - cost_list ! ?e)]"
      by (simp add: t_def dfs_discover_def Let_def)
    show ?thesis
      unfolding up pot_inv_def
    proof (intro allI impI)
      fix w assume wv: "w < vcount" and ws: "ds_seen t ! w" and wp: "ds_prnt t ! w < vcount"
      show "ds_pot t ! w = pval_plus (ds_pot t ! (ds_prnt t ! w))
              (M_0, if ds_prnt t ! w = fst_list ! (ds_par t ! w)
                    then cost_list ! (ds_par t ! w) else - cost_list ! (ds_par t ! w))"
      proof (cases "w = ?w")
        case True
        have p1: "ds_prnt t ! w = v" using True e_prnt wlt lens by (simp add: nth_list_update)
        have p2: "ds_par t ! w = ?e" using True e_par wlt lens by (simp add: nth_list_update)
        have p3: "ds_pot t ! w = pval_plus (ds_pot s ! v)
                    (M_0, if v = fst_list ! ?e then cost_list ! ?e else - cost_list ! ?e)"
          using True e_pot wlt lens by (simp add: nth_list_update)
        have p4: "ds_pot t ! v = ds_pot s ! v" using vne e_pot by (simp add: nth_list_update)
        show ?thesis using p1 p2 p3 p4 by simp
      next
        case ww: False
        have s_ws: "ds_seen s ! w" using ws e_seen ww by (simp add: nth_list_update)
        have p1: "ds_prnt t ! w = ds_prnt s ! w" using ww e_prnt by (simp add: nth_list_update)
        have p2: "ds_par t ! w = ds_par s ! w" using ww e_par by (simp add: nth_list_update)
        have p3: "ds_pot t ! w = ds_pot s ! w" using ww e_pot by (simp add: nth_list_update)
        have wps: "ds_prnt s ! w < vcount" using wp p1 by simp
        have prntne: "ds_prnt s ! w \<noteq> ?w" using pne wv s_ws wps by simp
        have p4: "ds_pot t ! (ds_prnt s ! w) = ds_pot s ! (ds_prnt s ! w)"
          using prntne e_pot by (simp add: nth_list_update)
        have "ds_pot s ! w = pval_plus (ds_pot s ! (ds_prnt s ! w))
                (M_0, if ds_prnt s ! w = fst_list ! (ds_par s ! w)
                      then cost_list ! (ds_par s ! w) else - cost_list ! (ds_par s ! w))"
          using potC wv s_ws wps by simp
        thus ?thesis using p1 p2 p3 p4 by simp
      qed
    qed
  qed
qed

text \<open>The potential invariant is preserved by opening a component at an unseen @{term c}: only the
      single fresh slot @{term c} is written (its parent becomes the root, so it is excluded), and no
      previously-emitted vertex's parent is @{term c}, so every earlier equation survives.\<close>

lemma pot_inv_seed:
  assumes poti: "pot_inv s" and tsi: "tree_seen_inv s"
      and c: "c < vcount" and unseen: "\<not> ds_seen s ! c"
      and t_prnt_c: "ds_prnt t ! c = vcount"
      and agree_seen: "\<And>i. i \<noteq> c \<Longrightarrow> ds_seen t ! i = ds_seen s ! i"
      and agree_prnt: "\<And>i. i \<noteq> c \<Longrightarrow> ds_prnt t ! i = ds_prnt s ! i"
      and agree_par:  "\<And>i. i \<noteq> c \<Longrightarrow> ds_par t ! i = ds_par s ! i"
      and agree_pot:  "\<And>i. i \<noteq> c \<Longrightarrow> ds_pot t ! i = ds_pot s ! i"
    shows "pot_inv t"
proof -
  from tsi have par: "\<forall>w<vcount. ds_seen s ! w \<longrightarrow> ds_prnt s ! w = vcount \<or> (ds_prnt s ! w < vcount \<and> ds_seen s ! (ds_prnt s ! w))"
    by (auto simp: tree_seen_inv_def)
  have neq: "\<And>w'. ds_seen s ! w' \<Longrightarrow> w' \<noteq> c" using unseen by auto
  have pne: "\<And>w. w < vcount \<Longrightarrow> ds_seen s ! w \<Longrightarrow> ds_prnt s ! w < vcount \<Longrightarrow> ds_prnt s ! w \<noteq> c"
    using par neq by fastforce
  from poti have potC: "\<forall>w<vcount. ds_seen s ! w \<longrightarrow> ds_prnt s ! w < vcount \<longrightarrow>
        ds_pot s ! w = pval_plus (ds_pot s ! (ds_prnt s ! w))
           (M_0, if ds_prnt s ! w = fst_list ! (ds_par s ! w)
                 then cost_list ! (ds_par s ! w) else - cost_list ! (ds_par s ! w))"
    by (simp add: pot_inv_def)
  show ?thesis
    unfolding pot_inv_def
  proof (intro allI impI)
    fix w assume wv: "w < vcount" and ws: "ds_seen t ! w" and wp: "ds_prnt t ! w < vcount"
    show "ds_pot t ! w = pval_plus (ds_pot t ! (ds_prnt t ! w))
            (M_0, if ds_prnt t ! w = fst_list ! (ds_par t ! w)
                  then cost_list ! (ds_par t ! w) else - cost_list ! (ds_par t ! w))"
    proof (cases "w = c")
      case True
      thus ?thesis using wp t_prnt_c by simp
    next
      case wc: False
      have s_ws: "ds_seen s ! w" using ws agree_seen wc by simp
      have p1: "ds_prnt t ! w = ds_prnt s ! w" using wc agree_prnt by simp
      have p2: "ds_par t ! w = ds_par s ! w" using wc agree_par by simp
      have p3: "ds_pot t ! w = ds_pot s ! w" using wc agree_pot by simp
      have wps: "ds_prnt s ! w < vcount" using wp p1 by simp
      have prntne: "ds_prnt s ! w \<noteq> c" using pne wv s_ws wps by simp
      have p4: "ds_pot t ! (ds_prnt s ! w) = ds_pot s ! (ds_prnt s ! w)"
        using prntne agree_pot by simp
      have "ds_pot s ! w = pval_plus (ds_pot s ! (ds_prnt s ! w))
              (M_0, if ds_prnt s ! w = fst_list ! (ds_par s ! w)
                    then cost_list ! (ds_par s ! w) else - cost_list ! (ds_par s ! w))"
        using potC wv s_ws wps by simp
      thus ?thesis using p1 p2 p3 p4 by simp
    qed
  qed
qed

section \<open>The root-potential invariant (I1)\<close>

text \<open>Design-notes clause I1 for the root: @{term \<open>ds_pot s ! vcount = pval_zero\<close>}. The root is seeded
      with zero potential by @{const dfs_init} and every state transformer writes @{const ds_pot} only
      at real vertices (\<open>< vcount\<close>) --- discovery at the fresh child, component-opening at the new root
      @{term c} --- or not at all, so the root potential is never disturbed. This discharges the
      @{term \<open>\<pi> r = 0\<close>} half of \<open>init_pot_fits\<close>.\<close>

definition root_pot_inv :: "'n dfs_state \<Rightarrow> bool" where
  "root_pot_inv s \<longleftrightarrow> ds_pot s ! vcount = pval_zero"

lemma bd_upd1_rpi:
  assumes wf: "dfs_wf s" and rpi: "root_pot_inv s" and c: "bd_call1_conds fl s"
  shows "root_pot_inv (bd_upd1 fl s)"
proof -
  from c obtain v oc ic rest where stk: "ds_stk s = (v, oc, ic) # rest" and oclt: "oc < free_out_hi fl ! v"
    by (auto simp: bd_call1_conds_def split: list.splits prod.splits)
  from wf stk have vlt: "v < vcount" and olo: "out_lo ! v \<le> oc" by (auto simp: dfs_wf_def)
  let ?e = "free_out_edges fl ! oc"
  let ?w = "snd_list ! ?e"
  have wlt: "?w < vcount" using Hout_valid[OF vlt olo oclt] .
  show ?thesis
  proof (cases "ds_seen s ! ?w")
    case True
    have "bd_upd1 fl s = s\<lparr>ds_stk := (v, Suc oc, ic) # rest\<rparr>" using stk True by (simp add: bd_upd1_def Let_def)
    thus ?thesis using rpi by (simp add: root_pot_inv_def)
  next
    case False
    have up: "bd_upd1 fl s = dfs_discover (s\<lparr>ds_stk := (v, Suc oc, ic) # rest\<rparr>) v ?w ?e"
      using stk False by (simp add: bd_upd1_def Let_def)
    have "ds_pot (dfs_discover (s\<lparr>ds_stk := (v, Suc oc, ic) # rest\<rparr>) v ?w ?e) ! vcount = ds_pot s ! vcount"
      using wlt by (simp add: dfs_discover_def Let_def nth_list_update)
    thus ?thesis using rpi up by (simp add: root_pot_inv_def)
  qed
qed

lemma bd_upd2_rpi:
  assumes wf: "dfs_wf s" and rpi: "root_pot_inv s" and c: "bd_call2_conds fl s"
  shows "root_pot_inv (bd_upd2 fl s)"
proof -
  from c obtain v oc ic rest where stk: "ds_stk s = (v, oc, ic) # rest"
      and noc: "\<not> oc < free_out_hi fl ! v" and iclt: "ic < free_in_hi fl ! v"
    by (auto simp: bd_call2_conds_def split: list.splits prod.splits)
  from wf stk have vlt: "v < vcount" and ilo: "in_lo ! v \<le> ic" by (auto simp: dfs_wf_def)
  let ?e = "free_in_edges fl ! ic"
  let ?w = "fst_list ! ?e"
  have wlt: "?w < vcount" using Hin_valid[OF vlt ilo iclt] .
  show ?thesis
  proof (cases "ds_seen s ! ?w")
    case True
    have "bd_upd2 fl s = s\<lparr>ds_stk := (v, oc, Suc ic) # rest\<rparr>" using stk True by (simp add: bd_upd2_def Let_def)
    thus ?thesis using rpi by (simp add: root_pot_inv_def)
  next
    case False
    have up: "bd_upd2 fl s = dfs_discover (s\<lparr>ds_stk := (v, oc, Suc ic) # rest\<rparr>) v ?w ?e"
      using stk False by (simp add: bd_upd2_def Let_def)
    have "ds_pot (dfs_discover (s\<lparr>ds_stk := (v, oc, Suc ic) # rest\<rparr>) v ?w ?e) ! vcount = ds_pot s ! vcount"
      using wlt by (simp add: dfs_discover_def Let_def nth_list_update)
    thus ?thesis using rpi up by (simp add: root_pot_inv_def)
  qed
qed

lemma bd_upd3_rpi:
  assumes rpi: "root_pot_inv s" and c: "bd_call3_conds fl s"
  shows "root_pot_inv (bd_upd3 s)"
proof -
  from c obtain v oc ic rest where stk: "ds_stk s = (v, oc, ic) # rest"
    by (auto simp: bd_call3_conds_def split: list.splits prod.splits)
  have "bd_upd3 s = dfs_finish s v rest" using stk by (simp add: bd_upd3_def)
  thus ?thesis using rpi by (simp add: root_pot_inv_def dfs_finish_def Let_def)
qed

section \<open>The stack-chain invariant (structural core of I6)\<close>

text \<open>The explicit DFS stack is, read top-to-bottom, exactly a @{const ds_prnt}-chain ending at the
      root: the parent of each frame's vertex is the vertex of the frame below it, and the bottom
      frame's vertex (a component root) has the root @{term vcount} as parent. This is the array-level
      heart of the DFS-preorder step (design-notes I6): when a vertex is discovered from the stack top
      @{term v} its parent is set to @{term v}, and @{term v} is an ancestor of the last-emitted vertex;
      when a component is opened its parent is the root, which every root-path reaches. The full
      preorder step / clause J then follows at \<open>arb_invar\<close> assembly, where the emission order (thread)
      and the abstract root-path (\<open>follow\<close>) are available. The stack is empty at @{const build_tree}, so
      this invariant is a \<^emph>\<open>traversal\<close> invariant (it constrains intermediate states, not the finished
      tree directly).\<close>

fun vchain :: "nat list \<Rightarrow> nat list \<Rightarrow> bool" where
  "vchain P [] = True"
| "vchain P [v] = (P ! v = vcount)"
| "vchain P (v # u # rest) = (P ! v = u \<and> vchain P (u # rest))"

lemma vchain_cong: "(\<And>x. x \<in> set xs \<Longrightarrow> P ! x = Q ! x) \<Longrightarrow> vchain P xs = vchain Q xs"
  by (induct xs rule: vchain.induct) auto

lemma vchain_tl: "vchain P (v # vs) \<Longrightarrow> vchain P vs"
  by (cases vs) auto

definition stk_prnt_inv :: "'n dfs_state \<Rightarrow> bool" where
  "stk_prnt_inv s \<longleftrightarrow> vchain (ds_prnt s) (map (\<lambda>(v,oc,ic). v) (ds_stk s))"

lemma bd_upd3_spi:
  assumes spi: "stk_prnt_inv s" and c: "bd_call3_conds fl s"
  shows "stk_prnt_inv (bd_upd3 s)"
proof -
  from c obtain v oc ic rest where stk: "ds_stk s = (v, oc, ic) # rest"
    by (auto simp: bd_call3_conds_def split: list.splits prod.splits)
  have bu: "bd_upd3 s = dfs_finish s v rest" using stk by (simp add: bd_upd3_def)
  have "vchain (ds_prnt s) (v # map (\<lambda>(v,oc,ic). v) rest)" using spi stk by (simp add: stk_prnt_inv_def)
  hence "vchain (ds_prnt s) (map (\<lambda>(v,oc,ic). v) rest)" by (rule vchain_tl)
  thus ?thesis using bu by (simp add: stk_prnt_inv_def dfs_finish_def Let_def)
qed

lemma bd_upd1_spi:
  assumes wf: "dfs_wf s" and sz: "dfs_sized s" and tsi: "tree_seen_inv s"
      and spi: "stk_prnt_inv s" and c: "bd_call1_conds fl s"
  shows "stk_prnt_inv (bd_upd1 fl s)"
proof -
  from c obtain v oc ic rest where stk: "ds_stk s = (v, oc, ic) # rest" and oclt: "oc < free_out_hi fl ! v"
    by (auto simp: bd_call1_conds_def split: list.splits prod.splits)
  from wf stk have vlt: "v < vcount" and olo: "out_lo ! v \<le> oc" by (auto simp: dfs_wf_def)
  have lenp: "length (ds_prnt s) = Suc vcount" using sz by (simp add: dfs_sized_def)
  let ?e = "free_out_edges fl ! oc"
  let ?w = "snd_list ! ?e"
  have wlt: "?w < vcount" using Hout_valid[OF vlt olo oclt] .
  from tsi have sseen: "\<forall>(v',oc',ic')\<in>set (ds_stk s). ds_seen s ! v'" by (auto simp: tree_seen_inv_def)
  have vseen: "ds_seen s ! v" using sseen stk by auto
  have chain0: "vchain (ds_prnt s) (v # map (\<lambda>(v,oc,ic). v) rest)" using spi stk by (simp add: stk_prnt_inv_def)
  show ?thesis
  proof (cases "ds_seen s ! ?w")
    case True
    have "bd_upd1 fl s = s\<lparr>ds_stk := (v, Suc oc, ic) # rest\<rparr>" using stk True by (simp add: bd_upd1_def Let_def)
    thus ?thesis using chain0 by (simp add: stk_prnt_inv_def)
  next
    case False
    have up: "bd_upd1 fl s = dfs_discover (s\<lparr>ds_stk := (v, Suc oc, ic) # rest\<rparr>) v ?w ?e"
      using stk False by (simp add: bd_upd1_def Let_def)
    have vnw: "?w \<noteq> v" using vseen False by auto
    have rnw: "\<And>a b cc. (a, b, cc) \<in> set rest \<Longrightarrow> ?w \<noteq> a" using sseen stk False by fastforce
    have cong: "vchain ((ds_prnt s)[?w := v]) (v # map (\<lambda>(v,oc,ic). v) rest)
                 = vchain (ds_prnt s) (v # map (\<lambda>(v,oc,ic). v) rest)"
      by (rule vchain_cong) (auto simp: nth_list_update_neq vnw rnw)
    have "vchain ((ds_prnt s)[?w := v]) (?w # v # map (\<lambda>(v,oc,ic). v) rest)"
      using wlt lenp cong chain0 by (simp add: nth_list_update)
    thus ?thesis using up by (simp add: stk_prnt_inv_def dfs_discover_def Let_def)
  qed
qed

lemma bd_upd2_spi:
  assumes wf: "dfs_wf s" and sz: "dfs_sized s" and tsi: "tree_seen_inv s"
      and spi: "stk_prnt_inv s" and c: "bd_call2_conds fl s"
  shows "stk_prnt_inv (bd_upd2 fl s)"
proof -
  from c obtain v oc ic rest where stk: "ds_stk s = (v, oc, ic) # rest"
      and noc: "\<not> oc < free_out_hi fl ! v" and iclt: "ic < free_in_hi fl ! v"
    by (auto simp: bd_call2_conds_def split: list.splits prod.splits)
  from wf stk have vlt: "v < vcount" and ilo: "in_lo ! v \<le> ic" by (auto simp: dfs_wf_def)
  have lenp: "length (ds_prnt s) = Suc vcount" using sz by (simp add: dfs_sized_def)
  let ?e = "free_in_edges fl ! ic"
  let ?w = "fst_list ! ?e"
  have wlt: "?w < vcount" using Hin_valid[OF vlt ilo iclt] .
  from tsi have sseen: "\<forall>(v',oc',ic')\<in>set (ds_stk s). ds_seen s ! v'" by (auto simp: tree_seen_inv_def)
  have vseen: "ds_seen s ! v" using sseen stk by auto
  have chain0: "vchain (ds_prnt s) (v # map (\<lambda>(v,oc,ic). v) rest)" using spi stk by (simp add: stk_prnt_inv_def)
  show ?thesis
  proof (cases "ds_seen s ! ?w")
    case True
    have "bd_upd2 fl s = s\<lparr>ds_stk := (v, oc, Suc ic) # rest\<rparr>" using stk True by (simp add: bd_upd2_def Let_def)
    thus ?thesis using chain0 by (simp add: stk_prnt_inv_def)
  next
    case False
    have up: "bd_upd2 fl s = dfs_discover (s\<lparr>ds_stk := (v, oc, Suc ic) # rest\<rparr>) v ?w ?e"
      using stk False by (simp add: bd_upd2_def Let_def)
    have vnw: "?w \<noteq> v" using vseen False by auto
    have rnw: "\<And>a b cc. (a, b, cc) \<in> set rest \<Longrightarrow> ?w \<noteq> a" using sseen stk False by fastforce
    have cong: "vchain ((ds_prnt s)[?w := v]) (v # map (\<lambda>(v,oc,ic). v) rest)
                 = vchain (ds_prnt s) (v # map (\<lambda>(v,oc,ic). v) rest)"
      by (rule vchain_cong) (auto simp: nth_list_update_neq vnw rnw)
    have "vchain ((ds_prnt s)[?w := v]) (?w # v # map (\<lambda>(v,oc,ic). v) rest)"
      using wlt lenp cong chain0 by (simp add: nth_list_update)
    thus ?thesis using up by (simp add: stk_prnt_inv_def dfs_discover_def Let_def)
  qed
qed

section \<open>Emission-order invariant (I6, full DFS step)\<close>

text \<open>The full design-notes clause I6 (the preorder DFS step of \<open>preorder_contiguous\<close>): the abstract
      parent of every emitted vertex is an \<^emph>\<open>ancestor\<close> of its thread-predecessor. We phrase ancestry
      via the parent-step relation @{term pstep} --- the child{\isasymrightarrow}parent edges of the currently emitted
      vertices --- whose reflexive-transitive closure is exactly the root-path (\<open>follow\<close>) once the
      abstract tree is assembled. The relation only ever \<^emph>\<open>grows\<close> (one edge per emission), so old
      ancestry facts persist; the emission-order pair is discharged at each discovery by the fact
      that the stack top is an ancestor of the last-emitted vertex.

      The bundled invariant @{term emit_ord_inv} carries three clauses: every emitted vertex reaches
      the root @{term vcount} (reaches-root); the stack top is an ancestor of @{const ds_prev}
      (stack-descends); and the target @{term \<open>(ds_rvth s ! w, ds_prnt s ! w) \<in> (pstep s)\<^sup>*\<close>}
      (emission-order). The three are proved together because their maintenance steps feed one
      another (a discovery uses stack-descends for the new pair and reaches-root of the parent for
      the new reaches-root fact).\<close>

definition pstep :: "'n dfs_state \<Rightarrow> (nat \<times> nat) set" where
  "pstep s = {(x, ds_prnt s ! x) |x. x < vcount \<and> ds_seen s ! x}"

lemma pstep_upd:
  assumes "ds_prnt t = (ds_prnt s)[w := v]" and "ds_seen t = (ds_seen s)[w := True]"
      and "w < vcount" and "\<not> ds_seen s ! w"
      and "length (ds_seen s) = Suc vcount" and "length (ds_prnt s) = Suc vcount"
  shows "pstep t = insert (w, v) (pstep s)"
proof -
  have wl: "w < length (ds_seen s)" "w < length (ds_prnt s)" using assms(3,5,6) by auto
  show ?thesis
    using assms wl by (auto simp: pstep_def nth_list_update split: if_splits)
qed

lemma pstep_cong: "ds_prnt s = ds_prnt t \<Longrightarrow> ds_seen s = ds_seen t \<Longrightarrow> pstep s = pstep t"
  by (simp add: pstep_def)

definition emit_ord_inv :: "'n dfs_state \<Rightarrow> bool" where
  "emit_ord_inv s \<longleftrightarrow>
     (\<forall>x < vcount. ds_seen s ! x \<longrightarrow> (x, vcount) \<in> (pstep s)\<^sup>*)
   \<and> (ds_stk s \<noteq> [] \<longrightarrow> (ds_prev s, fst (hd (ds_stk s))) \<in> (pstep s)\<^sup>*)
   \<and> (\<forall>w < vcount. ds_seen s ! w \<longrightarrow> (ds_rvth s ! w, ds_prnt s ! w) \<in> (pstep s)\<^sup>*)"

lemma bd_upd3_eoi:
  assumes wf: "dfs_wf s" and tsi: "tree_seen_inv s" and spi: "stk_prnt_inv s"
      and eoi: "emit_ord_inv s" and c: "bd_call3_conds fl s"
  shows "emit_ord_inv (bd_upd3 s)"
proof -
  from c obtain v oc ic rest where stk: "ds_stk s = (v, oc, ic) # rest"
    by (auto simp: bd_call3_conds_def split: list.splits prod.splits)
  have bu: "bd_upd3 s = dfs_finish s v rest" using stk by (simp add: bd_upd3_def)
  have eprnt: "ds_prnt (bd_upd3 s) = ds_prnt s" and eseen: "ds_seen (bd_upd3 s) = ds_seen s"
    and ervth: "ds_rvth (bd_upd3 s) = ds_rvth s" and eprev: "ds_prev (bd_upd3 s) = ds_prev s"
    and estk: "ds_stk (bd_upd3 s) = rest"
    by (simp_all add: bu dfs_finish_def Let_def)
  have ps: "pstep (bd_upd3 s) = pstep s" using eprnt eseen by (rule pstep_cong)
  from wf stk have vlt: "v < vcount" by (auto simp: dfs_wf_def)
  from tsi have sseen: "\<forall>(v',oc',ic')\<in>set (ds_stk s). ds_seen s ! v'" by (auto simp: tree_seen_inv_def)
  have vseen: "ds_seen s ! v" using sseen stk by auto
  from eoi have RR: "\<forall>x < vcount. ds_seen s ! x \<longrightarrow> (x, vcount) \<in> (pstep s)\<^sup>*"
    and SD: "ds_stk s \<noteq> [] \<longrightarrow> (ds_prev s, fst (hd (ds_stk s))) \<in> (pstep s)\<^sup>*"
    and EO: "\<forall>w < vcount. ds_seen s ! w \<longrightarrow> (ds_rvth s ! w, ds_prnt s ! w) \<in> (pstep s)\<^sup>*"
    by (auto simp: emit_ord_inv_def)
  show ?thesis
    unfolding emit_ord_inv_def
  proof (intro conjI)
    show "\<forall>x < vcount. ds_seen (bd_upd3 s) ! x \<longrightarrow> (x, vcount) \<in> (pstep (bd_upd3 s))\<^sup>*"
      using RR ps eseen by simp
    show "\<forall>w < vcount. ds_seen (bd_upd3 s) ! w \<longrightarrow> (ds_rvth (bd_upd3 s) ! w, ds_prnt (bd_upd3 s) ! w) \<in> (pstep (bd_upd3 s))\<^sup>*"
      using EO ps eseen ervth eprnt by simp
    show "ds_stk (bd_upd3 s) \<noteq> [] \<longrightarrow> (ds_prev (bd_upd3 s), fst (hd (ds_stk (bd_upd3 s)))) \<in> (pstep (bd_upd3 s))\<^sup>*"
    proof (cases rest)
      case Nil thus ?thesis using estk by simp
    next
      case (Cons f fs)
      obtain u ou iu where f: "f = (u, ou, iu)" by (cases f) auto
      have topv: "(ds_prev s, v) \<in> (pstep s)\<^sup>*" using SD stk by simp
      have prv: "ds_prnt s ! v = u"
        using spi stk Cons f by (simp add: stk_prnt_inv_def)
      have "(v, u) \<in> pstep s" using vlt vseen prv by (auto simp: pstep_def)
      hence "(ds_prev s, u) \<in> (pstep s)\<^sup>*" using topv by (simp add: rtrancl_into_rtrancl)
      thus ?thesis using estk eprev ps Cons f by simp
    qed
  qed
qed

lemma bd_upd1_eoi:
  assumes wf: "dfs_wf s" and sz: "dfs_sized s" and tsi: "tree_seen_inv s"
      and eoi: "emit_ord_inv s" and c: "bd_call1_conds fl s"
  shows "emit_ord_inv (bd_upd1 fl s)"
proof -
  from c obtain v oc ic rest where stk: "ds_stk s = (v, oc, ic) # rest" and oclt: "oc < free_out_hi fl ! v"
    by (auto simp: bd_call1_conds_def split: list.splits prod.splits)
  from wf stk have vlt: "v < vcount" and olo: "out_lo ! v \<le> oc" by (auto simp: dfs_wf_def)
  have lens: "length (ds_seen s) = Suc vcount" "length (ds_prnt s) = Suc vcount"
       "length (ds_rvth s) = Suc vcount"
    using sz by (simp_all add: dfs_sized_def)
  let ?e = "free_out_edges fl ! oc"
  let ?w = "snd_list ! ?e"
  have wlt: "?w < vcount" using Hout_valid[OF vlt olo oclt] .
  from tsi have sseen: "\<forall>(v',oc',ic')\<in>set (ds_stk s). ds_seen s ! v'" by (auto simp: tree_seen_inv_def)
  have vseen: "ds_seen s ! v" using sseen stk by auto
  from eoi have RR: "\<forall>x < vcount. ds_seen s ! x \<longrightarrow> (x, vcount) \<in> (pstep s)\<^sup>*"
    and SD: "ds_stk s \<noteq> [] \<longrightarrow> (ds_prev s, fst (hd (ds_stk s))) \<in> (pstep s)\<^sup>*"
    and EO: "\<forall>w < vcount. ds_seen s ! w \<longrightarrow> (ds_rvth s ! w, ds_prnt s ! w) \<in> (pstep s)\<^sup>*"
    by (auto simp: emit_ord_inv_def)
  show ?thesis
  proof (cases "ds_seen s ! ?w")
    case True
    have "bd_upd1 fl s = s\<lparr>ds_stk := (v, Suc oc, ic) # rest\<rparr>" using stk True by (simp add: bd_upd1_def Let_def)
    hence ef: "ds_prnt (bd_upd1 fl s) = ds_prnt s" "ds_seen (bd_upd1 fl s) = ds_seen s"
       "ds_rvth (bd_upd1 fl s) = ds_rvth s" "ds_prev (bd_upd1 fl s) = ds_prev s"
       "ds_stk (bd_upd1 fl s) = (v, Suc oc, ic) # rest" by simp_all
    have ps: "pstep (bd_upd1 fl s) = pstep s" using ef(1,2) by (rule pstep_cong)
    show ?thesis unfolding emit_ord_inv_def using RR SD EO ef ps stk by auto
  next
    case False
    have up: "bd_upd1 fl s = dfs_discover (s\<lparr>ds_stk := (v, Suc oc, ic) # rest\<rparr>) v ?w ?e"
      using stk False by (simp add: bd_upd1_def Let_def)
    have ef: "ds_prnt (bd_upd1 fl s) = (ds_prnt s)[?w := v]"
       "ds_seen (bd_upd1 fl s) = (ds_seen s)[?w := True]"
       "ds_rvth (bd_upd1 fl s) = (ds_rvth s)[?w := ds_prev s]"
       "ds_prev (bd_upd1 fl s) = ?w"
       "ds_stk (bd_upd1 fl s) = (?w, out_lo ! ?w, in_lo ! ?w) # (v, Suc oc, ic) # rest"
      by (simp_all add: up dfs_discover_def Let_def)
    have pe: "pstep (bd_upd1 fl s) = insert (?w, v) (pstep s)"
      using pstep_upd[OF ef(1) ef(2) wlt False lens(1,2)] by simp
    have sub: "pstep s \<subseteq> pstep (bd_upd1 fl s)" using pe by auto
    have wvP: "(?w, v) \<in> pstep (bd_upd1 fl s)" using pe by simp
    have topv: "(ds_prev s, v) \<in> (pstep s)\<^sup>*" using SD stk by simp
    show ?thesis
      unfolding emit_ord_inv_def
    proof (intro conjI)
      show "\<forall>x < vcount. ds_seen (bd_upd1 fl s) ! x \<longrightarrow> (x, vcount) \<in> (pstep (bd_upd1 fl s))\<^sup>*"
      proof (intro allI impI)
        fix x assume xlt: "x < vcount" and xseen: "ds_seen (bd_upd1 fl s) ! x"
        show "(x, vcount) \<in> (pstep (bd_upd1 fl s))\<^sup>*"
        proof (cases "x = ?w")
          case True
          have "(v, vcount) \<in> (pstep s)\<^sup>*" using RR vlt vseen by simp
          hence "(v, vcount) \<in> (pstep (bd_upd1 fl s))\<^sup>*" using rtrancl_mono[OF sub] by auto
          thus ?thesis using wvP True by (simp add: converse_rtrancl_into_rtrancl)
        next
          case False
          have "ds_seen s ! x" using xseen ef(2) False lens by (simp add: nth_list_update)
          hence "(x, vcount) \<in> (pstep s)\<^sup>*" using RR xlt by simp
          thus ?thesis using rtrancl_mono[OF sub] by auto
        qed
      qed
    next
      show "ds_stk (bd_upd1 fl s) \<noteq> [] \<longrightarrow> (ds_prev (bd_upd1 fl s), fst (hd (ds_stk (bd_upd1 fl s)))) \<in> (pstep (bd_upd1 fl s))\<^sup>*"
        using ef(4,5) by simp
    next
      show "\<forall>w < vcount. ds_seen (bd_upd1 fl s) ! w \<longrightarrow> (ds_rvth (bd_upd1 fl s) ! w, ds_prnt (bd_upd1 fl s) ! w) \<in> (pstep (bd_upd1 fl s))\<^sup>*"
      proof (intro allI impI)
        fix x assume xlt: "x < vcount" and xseen: "ds_seen (bd_upd1 fl s) ! x"
        show "(ds_rvth (bd_upd1 fl s) ! x, ds_prnt (bd_upd1 fl s) ! x) \<in> (pstep (bd_upd1 fl s))\<^sup>*"
        proof (cases "x = ?w")
          case True
          have "ds_rvth (bd_upd1 fl s) ! x = ds_prev s" using ef(3) True wlt lens by (simp add: nth_list_update)
          moreover have "ds_prnt (bd_upd1 fl s) ! x = v" using ef(1) True wlt lens by (simp add: nth_list_update)
          ultimately show ?thesis using topv rtrancl_mono[OF sub] by auto
        next
          case False
          have "ds_seen s ! x" using xseen ef(2) False lens by (simp add: nth_list_update)
          hence "(ds_rvth s ! x, ds_prnt s ! x) \<in> (pstep s)\<^sup>*" using EO xlt by simp
          moreover have "ds_rvth (bd_upd1 fl s) ! x = ds_rvth s ! x" using ef(3) False by (simp add: nth_list_update)
          moreover have "ds_prnt (bd_upd1 fl s) ! x = ds_prnt s ! x" using ef(1) False by (simp add: nth_list_update)
          ultimately show ?thesis using rtrancl_mono[OF sub] by auto
        qed
      qed
    qed
  qed
qed

lemma bd_upd2_eoi:
  assumes wf: "dfs_wf s" and sz: "dfs_sized s" and tsi: "tree_seen_inv s"
      and eoi: "emit_ord_inv s" and c: "bd_call2_conds fl s"
  shows "emit_ord_inv (bd_upd2 fl s)"
proof -
  from c obtain v oc ic rest where stk: "ds_stk s = (v, oc, ic) # rest"
      and noc: "\<not> oc < free_out_hi fl ! v" and iclt: "ic < free_in_hi fl ! v"
    by (auto simp: bd_call2_conds_def split: list.splits prod.splits)
  from wf stk have vlt: "v < vcount" and ilo: "in_lo ! v \<le> ic" by (auto simp: dfs_wf_def)
  have lens: "length (ds_seen s) = Suc vcount" "length (ds_prnt s) = Suc vcount"
       "length (ds_rvth s) = Suc vcount"
    using sz by (simp_all add: dfs_sized_def)
  let ?e = "free_in_edges fl ! ic"
  let ?w = "fst_list ! ?e"
  have wlt: "?w < vcount" using Hin_valid[OF vlt ilo iclt] .
  from tsi have sseen: "\<forall>(v',oc',ic')\<in>set (ds_stk s). ds_seen s ! v'" by (auto simp: tree_seen_inv_def)
  have vseen: "ds_seen s ! v" using sseen stk by auto
  from eoi have RR: "\<forall>x < vcount. ds_seen s ! x \<longrightarrow> (x, vcount) \<in> (pstep s)\<^sup>*"
    and SD: "ds_stk s \<noteq> [] \<longrightarrow> (ds_prev s, fst (hd (ds_stk s))) \<in> (pstep s)\<^sup>*"
    and EO: "\<forall>w < vcount. ds_seen s ! w \<longrightarrow> (ds_rvth s ! w, ds_prnt s ! w) \<in> (pstep s)\<^sup>*"
    by (auto simp: emit_ord_inv_def)
  show ?thesis
  proof (cases "ds_seen s ! ?w")
    case True
    have "bd_upd2 fl s = s\<lparr>ds_stk := (v, oc, Suc ic) # rest\<rparr>" using stk True by (simp add: bd_upd2_def Let_def)
    hence ef: "ds_prnt (bd_upd2 fl s) = ds_prnt s" "ds_seen (bd_upd2 fl s) = ds_seen s"
       "ds_rvth (bd_upd2 fl s) = ds_rvth s" "ds_prev (bd_upd2 fl s) = ds_prev s"
       "ds_stk (bd_upd2 fl s) = (v, oc, Suc ic) # rest" by simp_all
    have ps: "pstep (bd_upd2 fl s) = pstep s" using ef(1,2) by (rule pstep_cong)
    show ?thesis unfolding emit_ord_inv_def using RR SD EO ef ps stk by auto
  next
    case False
    have up: "bd_upd2 fl s = dfs_discover (s\<lparr>ds_stk := (v, oc, Suc ic) # rest\<rparr>) v ?w ?e"
      using stk False by (simp add: bd_upd2_def Let_def)
    have ef: "ds_prnt (bd_upd2 fl s) = (ds_prnt s)[?w := v]"
       "ds_seen (bd_upd2 fl s) = (ds_seen s)[?w := True]"
       "ds_rvth (bd_upd2 fl s) = (ds_rvth s)[?w := ds_prev s]"
       "ds_prev (bd_upd2 fl s) = ?w"
       "ds_stk (bd_upd2 fl s) = (?w, out_lo ! ?w, in_lo ! ?w) # (v, oc, Suc ic) # rest"
      by (simp_all add: up dfs_discover_def Let_def)
    have pe: "pstep (bd_upd2 fl s) = insert (?w, v) (pstep s)"
      using pstep_upd[OF ef(1) ef(2) wlt False lens(1,2)] by simp
    have sub: "pstep s \<subseteq> pstep (bd_upd2 fl s)" using pe by auto
    have wvP: "(?w, v) \<in> pstep (bd_upd2 fl s)" using pe by simp
    have topv: "(ds_prev s, v) \<in> (pstep s)\<^sup>*" using SD stk by simp
    show ?thesis
      unfolding emit_ord_inv_def
    proof (intro conjI)
      show "\<forall>x < vcount. ds_seen (bd_upd2 fl s) ! x \<longrightarrow> (x, vcount) \<in> (pstep (bd_upd2 fl s))\<^sup>*"
      proof (intro allI impI)
        fix x assume xlt: "x < vcount" and xseen: "ds_seen (bd_upd2 fl s) ! x"
        show "(x, vcount) \<in> (pstep (bd_upd2 fl s))\<^sup>*"
        proof (cases "x = ?w")
          case True
          have "(v, vcount) \<in> (pstep s)\<^sup>*" using RR vlt vseen by simp
          hence "(v, vcount) \<in> (pstep (bd_upd2 fl s))\<^sup>*" using rtrancl_mono[OF sub] by auto
          thus ?thesis using wvP True by (simp add: converse_rtrancl_into_rtrancl)
        next
          case False
          have "ds_seen s ! x" using xseen ef(2) False lens by (simp add: nth_list_update)
          hence "(x, vcount) \<in> (pstep s)\<^sup>*" using RR xlt by simp
          thus ?thesis using rtrancl_mono[OF sub] by auto
        qed
      qed
    next
      show "ds_stk (bd_upd2 fl s) \<noteq> [] \<longrightarrow> (ds_prev (bd_upd2 fl s), fst (hd (ds_stk (bd_upd2 fl s)))) \<in> (pstep (bd_upd2 fl s))\<^sup>*"
        using ef(4,5) by simp
    next
      show "\<forall>w < vcount. ds_seen (bd_upd2 fl s) ! w \<longrightarrow> (ds_rvth (bd_upd2 fl s) ! w, ds_prnt (bd_upd2 fl s) ! w) \<in> (pstep (bd_upd2 fl s))\<^sup>*"
      proof (intro allI impI)
        fix x assume xlt: "x < vcount" and xseen: "ds_seen (bd_upd2 fl s) ! x"
        show "(ds_rvth (bd_upd2 fl s) ! x, ds_prnt (bd_upd2 fl s) ! x) \<in> (pstep (bd_upd2 fl s))\<^sup>*"
        proof (cases "x = ?w")
          case True
          have "ds_rvth (bd_upd2 fl s) ! x = ds_prev s" using ef(3) True wlt lens by (simp add: nth_list_update)
          moreover have "ds_prnt (bd_upd2 fl s) ! x = v" using ef(1) True wlt lens by (simp add: nth_list_update)
          ultimately show ?thesis using topv rtrancl_mono[OF sub] by auto
        next
          case False
          have "ds_seen s ! x" using xseen ef(2) False lens by (simp add: nth_list_update)
          hence "(ds_rvth s ! x, ds_prnt s ! x) \<in> (pstep s)\<^sup>*" using EO xlt by simp
          moreover have "ds_rvth (bd_upd2 fl s) ! x = ds_rvth s ! x" using ef(3) False by (simp add: nth_list_update)
          moreover have "ds_prnt (bd_upd2 fl s) ! x = ds_prnt s ! x" using ef(1) False by (simp add: nth_list_update)
          ultimately show ?thesis using rtrancl_mono[OF sub] by auto
        qed
      qed
    qed
  qed
qed

lemma emit_ord_inv_seed:
  assumes eoi: "emit_ord_inv s" and thi: "thread_inv s"
      and c: "c < vcount" and unseen: "\<not> ds_seen s ! c"
      and lens: "length (ds_seen s) = Suc vcount" "length (ds_prnt s) = Suc vcount"
                "length (ds_rvth s) = Suc vcount"
      and eprnt: "ds_prnt t = (ds_prnt s)[c := vcount]"
      and eseen: "ds_seen t = (ds_seen s)[c := True]"
      and ervth: "ds_rvth t = (ds_rvth s)[c := ds_prev s]"
      and eprev: "ds_prev t = c"
      and estk:  "ds_stk t = [(c, out_lo ! c, in_lo ! c)]"
  shows "emit_ord_inv t"
proof -
  from eoi have RR: "\<forall>x < vcount. ds_seen s ! x \<longrightarrow> (x, vcount) \<in> (pstep s)\<^sup>*"
    and EO: "\<forall>w < vcount. ds_seen s ! w \<longrightarrow> (ds_rvth s ! w, ds_prnt s ! w) \<in> (pstep s)\<^sup>*"
    by (auto simp: emit_ord_inv_def)
  from thi have prevlt: "ds_prev s < Suc vcount"
    and prevem: "ds_prev s = vcount \<or> ds_seen s ! (ds_prev s)" by (auto simp: thread_inv_def)
  have pe: "pstep t = insert (c, vcount) (pstep s)"
    using pstep_upd[OF eprnt eseen c unseen lens(1,2)] by simp
  have sub: "pstep s \<subseteq> pstep t" using pe by auto
  have cvP: "(c, vcount) \<in> pstep t" using pe by simp
  have prevroot: "(ds_prev s, vcount) \<in> (pstep t)\<^sup>*"
  proof (cases "ds_prev s = vcount")
    case True thus ?thesis by simp
  next
    case False
    hence "ds_prev s < vcount" using prevlt by simp
    moreover have "ds_seen s ! (ds_prev s)" using prevem False by simp
    ultimately have "(ds_prev s, vcount) \<in> (pstep s)\<^sup>*" using RR by simp
    thus ?thesis using rtrancl_mono[OF sub] by auto
  qed
  show ?thesis
    unfolding emit_ord_inv_def
  proof (intro conjI)
    show "\<forall>x < vcount. ds_seen t ! x \<longrightarrow> (x, vcount) \<in> (pstep t)\<^sup>*"
    proof (intro allI impI)
      fix x assume xlt: "x < vcount" and xseen: "ds_seen t ! x"
      show "(x, vcount) \<in> (pstep t)\<^sup>*"
      proof (cases "x = c")
        case True thus ?thesis using cvP by auto
      next
        case False
        have "ds_seen s ! x" using xseen eseen False lens by (simp add: nth_list_update)
        thus ?thesis using RR xlt rtrancl_mono[OF sub] by auto
      qed
    qed
  next
    show "ds_stk t \<noteq> [] \<longrightarrow> (ds_prev t, fst (hd (ds_stk t))) \<in> (pstep t)\<^sup>*"
      using estk eprev by simp
  next
    show "\<forall>w < vcount. ds_seen t ! w \<longrightarrow> (ds_rvth t ! w, ds_prnt t ! w) \<in> (pstep t)\<^sup>*"
    proof (intro allI impI)
      fix x assume xlt: "x < vcount" and xseen: "ds_seen t ! x"
      show "(ds_rvth t ! x, ds_prnt t ! x) \<in> (pstep t)\<^sup>*"
      proof (cases "x = c")
        case True
        have "ds_rvth t ! x = ds_prev s" using ervth True c lens by (simp add: nth_list_update)
        moreover have "ds_prnt t ! x = vcount" using eprnt True c lens by (simp add: nth_list_update)
        ultimately show ?thesis using prevroot by simp
      next
        case False
        have "ds_seen s ! x" using xseen eseen False lens by (simp add: nth_list_update)
        hence "(ds_rvth s ! x, ds_prnt s ! x) \<in> (pstep s)\<^sup>*" using EO xlt by simp
        moreover have "ds_rvth t ! x = ds_rvth s ! x" using ervth False by (simp add: nth_list_update)
        moreover have "ds_prnt t ! x = ds_prnt s ! x" using eprnt False by (simp add: nth_list_update)
        ultimately show ?thesis using rtrancl_mono[OF sub] by auto
      qed
    qed
  qed
qed

lemma emit_U_edge_eoi: "emit_ord_inv s \<Longrightarrow> emit_ord_inv (emit_U_edge s v)"
  by (auto simp: emit_ord_inv_def pstep_def emit_U_edge_def Let_def)

lemma dfs_init_eoi: "emit_ord_inv dfs_init"
proof -
  have s: "ds_seen dfs_init ! x = False" if "x < vcount" for x
    using that by (simp add: dfs_init_def del: replicate_Suc)
  have st: "ds_stk dfs_init = []" by (simp add: dfs_init_def)
  show ?thesis using s st by (auto simp: emit_ord_inv_def)
qed

section \<open>Subtree bookkeeping (I7): descendant sets and subtree sizes\<close>

text \<open>Design-notes clause I7: when a vertex @{term v} finishes, @{term \<open>ds_snum s ! v\<close>} is the size of
      its subtree and @{term \<open>ds_lsuc s ! v\<close>} its last preorder descendant. We phrase the subtree as the
      set @{term \<open>desc s v\<close>} of emitted @{const pstep}-descendants (the array counterpart of the abstract
      @{text children}). @{const ds_snum} is established \<^emph>\<open>at finish\<close>: it is seeded to @{term 1} on
      discovery and accumulates a child's subtree size into its parent when the child pops. The proof
      threads two facts over the DFS stack: a finished vertex's @{const ds_snum} equals its descendant
      count, and --- telescoping down the stack (\<open>snchk\<close>) --- every frame's descendant count equals the
      running sum of @{const ds_snum} over it and the frames above it. A discovery adds the fresh vertex to
      exactly the descendant sets of the current stack vertices (its ancestors), so each frame's count
      rises by one; a finish reads the top frame's count off the telescoping base and credits it upward.\<close>

definition desc :: "'n dfs_state \<Rightarrow> nat \<Rightarrow> nat set" where
  "desc s v = {u. u < vcount \<and> ds_seen s ! u \<and> (u, v) \<in> (pstep s)\<^sup>*}"

definition dcard :: "'n dfs_state \<Rightarrow> nat \<Rightarrow> nat" where
  "dcard s v = card (desc s v)"

definition stkverts :: "'n dfs_state \<Rightarrow> nat set" where
  "stkverts s = set (map (\<lambda>(v,oc,ic). v) (ds_stk s))"

lemma desc_finite: "finite (desc s v)"
  by (rule finite_subset[of _ "{0..<vcount}"]) (auto simp: desc_def)

lemma desc_sub: "desc s v \<subseteq> {0..<vcount}"
  by (auto simp: desc_def)

lemma pstep_single_valued: "single_valued (pstep s)"
  by (auto simp: single_valued_def pstep_def)

lemma pstep_no_in:
  assumes tsi: "tree_seen_inv s" and wlt: "w < vcount" and wns: "\<not> ds_seen s ! w"
  shows "(a, w) \<notin> pstep s"
  using tsi wlt wns by (auto simp: pstep_def tree_seen_inv_def)

lemma pstep_to_w:
  assumes noin: "\<And>a. (a, w) \<notin> pstep s" and reach: "(u, w) \<in> (pstep s)\<^sup>*"
  shows "u = w"
  using reach by (cases rule: rtranclE) (auto simp: noin)

lemma pstep_reach_avoid_w:
  assumes noin: "\<And>a. (a, w) \<notin> pstep s"
      and P': "P' = insert (w, v0) (pstep s)"
      and reach: "(u, x) \<in> P'\<^sup>*" and une: "u \<noteq> w"
  shows "(u, x) \<in> (pstep s)\<^sup>*"
  using reach une
proof (induct rule: rtrancl_induct)
  case base thus ?case by simp
next
  case (step y z)
  have uy: "(u, y) \<in> (pstep s)\<^sup>*" using step.hyps(3) step.prems by simp
  from step.hyps(2) P' have "(y, z) \<in> pstep s \<or> (y, z) = (w, v0)" by auto
  thus ?case
  proof
    assume "(y, z) \<in> pstep s"
    thus ?thesis using uy by (simp add: rtrancl_into_rtrancl)
  next
    assume "(y, z) = (w, v0)"
    hence "y = w" by simp
    hence "u = w" using uy pstep_to_w[OF noin] by simp
    thus ?thesis using step.prems by simp
  qed
qed

lemma pstep_from_root:
  assumes "(vcount, x) \<in> (pstep s)\<^sup>*" shows "x = vcount"
  using assms
proof (cases rule: converse_rtranclE)
  case base thus ?thesis by simp
next
  case (step y) thus ?thesis by (auto simp: pstep_def)
qed

lemma vchain_parent_step:
  "vchain P xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> P ! y \<in> set xs \<or> P ! y = vcount"
proof (induct P xs rule: vchain.induct)
  case (1 P) thus ?case by simp
next
  case (2 P v)
  have "P ! v = vcount" using "2.prems"(1) by simp
  thus ?case using "2.prems"(2) by simp
next
  case (3 P v u rest)
  from "3.prems"(1) have pv: "P ! v = u" and rec: "vchain P (u # rest)" by auto
  show ?case
  proof (cases "y = v")
    case True thus ?thesis using pv by simp
  next
    case False
    hence "y \<in> set (u # rest)" using "3.prems"(2) by auto
    thus ?thesis using "3.hyps"[OF rec] by auto
  qed
qed

lemma stkverts_parent:
  assumes "stk_prnt_inv s" "y \<in> stkverts s"
  shows "ds_prnt s ! y \<in> stkverts s \<or> ds_prnt s ! y = vcount"
  using vchain_parent_step[of "ds_prnt s" "map (\<lambda>(v,oc,ic). v) (ds_stk s)" y] assms
  by (simp add: stk_prnt_inv_def stkverts_def)

lemma pstep_anc_on_stk:
  assumes spi: "stk_prnt_inv s" and v0: "v0 \<in> stkverts s" and reach: "(v0, x) \<in> (pstep s)\<^sup>*"
  shows "x \<in> stkverts s \<or> x = vcount"
  using reach
proof (induct rule: rtrancl_induct)
  case base thus ?case using v0 by simp
next
  case (step y z)
  have "y < vcount" and pz: "z = ds_prnt s ! y" using step.hyps(2) by (auto simp: pstep_def)
  hence "y \<in> stkverts s" using step.hyps(3) by auto
  thus ?case using stkverts_parent[OF spi] pz by auto
qed

lemma vchain_hd_reaches:
  "vchain (ds_prnt s) (a # xs) \<Longrightarrow> (\<And>y. y \<in> set (a # xs) \<Longrightarrow> y < vcount \<and> ds_seen s ! y) \<Longrightarrow>
   x \<in> set (a # xs) \<Longrightarrow> (a, x) \<in> (pstep s)\<^sup>*"
proof (induct xs arbitrary: a)
  case Nil
  hence "x = a" by simp
  thus ?case by simp
next
  case (Cons u us)
  from Cons.prems(1) have pa: "ds_prnt s ! a = u" and rec: "vchain (ds_prnt s) (u # us)" by auto
  have aprop: "a < vcount \<and> ds_seen s ! a" using Cons.prems(2) by simp
  have step: "(a, u) \<in> pstep s" using aprop pa by (auto simp: pstep_def)
  show ?case
  proof (cases "x = a")
    case True thus ?thesis by simp
  next
    case False
    hence xin: "x \<in> set (u # us)" using Cons.prems(3) by auto
    have "(u, x) \<in> (pstep s)\<^sup>*"
      using Cons.hyps[OF rec _ xin] Cons.prems(2) by auto
    thus ?thesis using step by (simp add: converse_rtrancl_into_rtrancl)
  qed
qed

lemma stkverts_props:
  assumes wf: "dfs_wf s" and tsi: "tree_seen_inv s" and y: "y \<in> stkverts s"
  shows "y < vcount \<and> ds_seen s ! y"
proof -
  from y obtain oc ic where mem: "(y, oc, ic) \<in> set (ds_stk s)" by (auto simp: stkverts_def)
  have "y < vcount" using wf mem by (auto simp: dfs_wf_def)
  moreover have "ds_seen s ! y" using tsi mem by (auto simp: tree_seen_inv_def)
  ultimately show ?thesis by simp
qed

lemma stk_top_reaches:
  assumes spi: "stk_prnt_inv s" and wf: "dfs_wf s" and tsi: "tree_seen_inv s"
      and stk: "ds_stk s = (v0, oc, ic) # rest" and x: "x \<in> stkverts s"
  shows "(v0, x) \<in> (pstep s)\<^sup>*"
proof -
  have xs_eq: "map (\<lambda>(v,oc,ic). v) (ds_stk s) = v0 # map (\<lambda>(v,oc,ic). v) rest" using stk by simp
  have vc: "vchain (ds_prnt s) (v0 # map (\<lambda>(v,oc,ic). v) rest)"
    using spi xs_eq by (simp add: stk_prnt_inv_def)
  have xin: "x \<in> set (v0 # map (\<lambda>(v,oc,ic). v) rest)" using x xs_eq by (simp add: stkverts_def)
  have props: "\<And>y. y \<in> set (v0 # map (\<lambda>(v,oc,ic). v) rest) \<Longrightarrow> y < vcount \<and> ds_seen s ! y"
    using stkverts_props[OF wf tsi] xs_eq by (simp add: stkverts_def)
  show ?thesis using vchain_hd_reaches[OF vc props xin] .
qed

text \<open>How @{const desc} changes on a discovery from stack top @{term v0} to fresh @{term w}: the fresh
      vertex is added to exactly the descendant sets of @{term w}'s ancestors (@{term w} itself and every
      vertex @{term v0} reaches), and nothing else.\<close>

lemma desc_discover:
  assumes tsi: "tree_seen_inv s" and wlt: "w < vcount" and wns: "\<not> ds_seen s ! w"
      and vne: "v0 \<noteq> w"
      and lens: "length (ds_seen s) = Suc vcount" "length (ds_prnt s) = Suc vcount"
      and eprnt: "ds_prnt s' = (ds_prnt s)[w := v0]"
      and eseen: "ds_seen s' = (ds_seen s)[w := True]"
  shows "desc s' x = (if x = w \<or> (v0, x) \<in> (pstep s)\<^sup>* then insert w (desc s x) else desc s x)"
proof -
  have pe: "pstep s' = insert (w, v0) (pstep s)" using pstep_upd[OF eprnt eseen wlt wns lens] .
  have sub: "pstep s \<subseteq> pstep s'" using pe by auto
  have noin: "\<And>a. (a, w) \<notin> pstep s" using pstep_no_in[OF tsi wlt wns] .
  have wout: "\<And>y. (w, y) \<notin> pstep s" using wns by (auto simp: pstep_def)
  have wnd: "w \<notin> desc s x" using wns by (auto simp: desc_def)
  have wreach: "(w, x) \<in> (pstep s')\<^sup>* \<longleftrightarrow> (x = w \<or> (v0, x) \<in> (pstep s)\<^sup>*)"
  proof
    assume "(w, x) \<in> (pstep s')\<^sup>*"
    thus "x = w \<or> (v0, x) \<in> (pstep s)\<^sup>*"
    proof (cases rule: converse_rtranclE)
      case base thus ?thesis by simp
    next
      case (step y)
      have "(w, y) \<in> pstep s'" using step(1) .
      hence "y = v0" using pe wout by auto
      hence "(v0, x) \<in> (pstep s')\<^sup>*" using step(2) by simp
      thus ?thesis using pstep_reach_avoid_w[OF noin pe] vne by auto
    qed
  next
    assume "x = w \<or> (v0, x) \<in> (pstep s)\<^sup>*"
    thus "(w, x) \<in> (pstep s')\<^sup>*"
    proof
      assume "x = w" thus ?thesis by simp
    next
      assume "(v0, x) \<in> (pstep s)\<^sup>*"
      hence "(v0, x) \<in> (pstep s')\<^sup>*" using rtrancl_mono[OF sub] by auto
      moreover have "(w, v0) \<in> pstep s'" using pe by simp
      ultimately show ?thesis by (simp add: converse_rtrancl_into_rtrancl)
    qed
  qed
  show ?thesis
  proof (rule set_eqI)
    fix u
    show "u \<in> desc s' x \<longleftrightarrow> u \<in> (if x = w \<or> (v0, x) \<in> (pstep s)\<^sup>* then insert w (desc s x) else desc s x)"
    proof (cases "u = w")
      case True
      have "u \<in> desc s' x \<longleftrightarrow> (w, x) \<in> (pstep s')\<^sup>*"
        using True wlt eseen lens by (auto simp: desc_def nth_list_update)
      thus ?thesis using True wreach wnd by (auto simp: desc_def)
    next
      case False
      have su: "ds_seen s' ! u = ds_seen s ! u" if "u < vcount"
        using False eseen that lens by (simp add: nth_list_update)
      have "u \<in> desc s' x \<longleftrightarrow> (u < vcount \<and> ds_seen s ! u \<and> (u, x) \<in> (pstep s)\<^sup>*)"
        using False su pe pstep_reach_avoid_w[OF noin pe] rtrancl_mono[OF sub]
        by (auto simp: desc_def)
      thus ?thesis using False by (auto simp: desc_def)
    qed
  qed
qed

lemma desc_fresh_empty:
  assumes tsi: "tree_seen_inv s" and wlt: "w < vcount" and wns: "\<not> ds_seen s ! w"
  shows "desc s w = {}"
proof -
  have noin: "\<And>a. (a, w) \<notin> pstep s" using pstep_no_in[OF tsi wlt wns] .
  show ?thesis
  proof (rule ccontr)
    assume "desc s w \<noteq> {}"
    then obtain u where "u \<in> desc s w" by auto
    hence "ds_seen s ! u" and "(u, w) \<in> (pstep s)\<^sup>*" by (auto simp: desc_def)
    hence "u = w" using pstep_to_w[OF noin] by simp
    thus False using \<open>ds_seen s ! u\<close> wns by simp
  qed
qed

fun snchk :: "'n dfs_state \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> bool" where
  "snchk s acc [] = True"
| "snchk s acc (v # rest) = (dcard s v = ds_snum s ! v + acc \<and> snchk s (dcard s v) rest)"

lemma snchk_cong:
  assumes "\<And>v. v \<in> set xs \<Longrightarrow> dcard s' v = dcard s v \<and> ds_snum s' ! v = ds_snum s ! v"
  shows "snchk s' acc xs = snchk s acc xs"
  using assms
proof (induct xs arbitrary: acc)
  case Nil thus ?case by simp
next
  case (Cons v rest)
  have dv: "dcard s' v = dcard s v" and sv: "ds_snum s' ! v = ds_snum s ! v" using Cons.prems by auto
  have "snchk s' (dcard s' v) rest = snchk s (dcard s v) rest"
    using Cons.hyps[of "dcard s v"] Cons.prems dv by auto
  thus ?case using dv sv by simp
qed

lemma snchk_incr:
  assumes "\<And>v. v \<in> set xs \<Longrightarrow> dcard s' v = Suc (dcard s v) \<and> ds_snum s' ! v = ds_snum s ! v"
  shows "snchk s' (Suc acc) xs = snchk s acc xs"
  using assms
proof (induct xs arbitrary: acc)
  case Nil thus ?case by simp
next
  case (Cons v rest)
  have dv: "dcard s' v = Suc (dcard s v)" and sv: "ds_snum s' ! v = ds_snum s ! v" using Cons.prems by auto
  have "snchk s' (dcard s' v) rest = snchk s (dcard s v) rest"
    using Cons.hyps[of "dcard s v"] Cons.prems dv by auto
  thus ?case using dv sv by simp
qed

definition snum_inv :: "'n dfs_state \<Rightarrow> bool" where
  "snum_inv s \<longleftrightarrow>
     distinct (map (\<lambda>(v,oc,ic). v) (ds_stk s))
   \<and> (\<forall>v < vcount. ds_seen s ! v \<longrightarrow> v \<notin> stkverts s \<longrightarrow> ds_snum s ! v = dcard s v)
   \<and> snchk s 0 (map (\<lambda>(v,oc,ic). v) (ds_stk s))"

lemma bd_upd1_sni:
  assumes wf: "dfs_wf s" and sz: "dfs_sized s" and tsi: "tree_seen_inv s"
      and spi: "stk_prnt_inv s" and sni: "snum_inv s" and c: "bd_call1_conds fl s"
  shows "snum_inv (bd_upd1 fl s)"
proof -
  from c obtain v oc ic rest where stk: "ds_stk s = (v, oc, ic) # rest" and oclt: "oc < free_out_hi fl ! v"
    by (auto simp: bd_call1_conds_def split: list.splits prod.splits)
  from wf stk have vlt: "v < vcount" and olo: "out_lo ! v \<le> oc" by (auto simp: dfs_wf_def)
  have lens: "length (ds_seen s) = Suc vcount" "length (ds_prnt s) = Suc vcount"
       "length (ds_snum s) = Suc vcount"
    using sz by (simp_all add: dfs_sized_def)
  let ?e = "free_out_edges fl ! oc"
  let ?w = "snd_list ! ?e"
  have wlt: "?w < vcount" using Hout_valid[OF vlt olo oclt] .
  have vin: "v \<in> stkverts s" using stk by (auto simp: stkverts_def)
  from sni have dist0: "distinct (map (\<lambda>(v,oc,ic). v) (ds_stk s))"
    and sn1_0: "\<forall>x < vcount. ds_seen s ! x \<longrightarrow> x \<notin> stkverts s \<longrightarrow> ds_snum s ! x = dcard s x"
    and sn2_0: "snchk s 0 (map (\<lambda>(v,oc,ic). v) (ds_stk s))"
    by (auto simp: snum_inv_def)
  show ?thesis
  proof (cases "ds_seen s ! ?w")
    case True
    have eqf: "bd_upd1 fl s = s\<lparr>ds_stk := (v, Suc oc, ic) # rest\<rparr>" using stk True by (simp add: bd_upd1_def Let_def)
    have ef: "ds_prnt (bd_upd1 fl s) = ds_prnt s" "ds_seen (bd_upd1 fl s) = ds_seen s"
       "ds_snum (bd_upd1 fl s) = ds_snum s"
       "map (\<lambda>(v,oc,ic). v) (ds_stk (bd_upd1 fl s)) = map (\<lambda>(v,oc,ic). v) (ds_stk s)"
      by (simp_all add: eqf stk)
    have dd: "\<And>x. desc (bd_upd1 fl s) x = desc s x"
      using pstep_cong[OF ef(1) ef(2)] by (simp add: desc_def ef(2))
    have sc: "snchk (bd_upd1 fl s) 0 (map (\<lambda>(v,oc,ic). v) (ds_stk s)) = snchk s 0 (map (\<lambda>(v,oc,ic). v) (ds_stk s))"
      by (rule snchk_cong) (simp add: dd dcard_def ef(3))
    show ?thesis
      unfolding snum_inv_def
    proof (intro conjI)
      show "distinct (map (\<lambda>(v,oc,ic). v) (ds_stk (bd_upd1 fl s)))" using dist0 ef(4) by simp
    next
      show "\<forall>x < vcount. ds_seen (bd_upd1 fl s) ! x \<longrightarrow> x \<notin> stkverts (bd_upd1 fl s) \<longrightarrow> ds_snum (bd_upd1 fl s) ! x = dcard (bd_upd1 fl s) x"
        using sn1_0 ef dd by (simp add: stkverts_def dcard_def)
    next
      show "snchk (bd_upd1 fl s) 0 (map (\<lambda>(v,oc,ic). v) (ds_stk (bd_upd1 fl s)))"
        using sc sn2_0 ef(4) by simp
    qed
  next
    case False
    have vseen: "ds_seen s ! v" using tsi stk by (auto simp: tree_seen_inv_def)
    have vne: "v \<noteq> ?w" using vseen False by auto
    have wnstk: "?w \<notin> stkverts s" using False stkverts_props[OF wf tsi] by auto
    have up: "bd_upd1 fl s = dfs_discover (s\<lparr>ds_stk := (v, Suc oc, ic) # rest\<rparr>) v ?w ?e"
      using stk False by (simp add: bd_upd1_def Let_def)
    have ef: "ds_prnt (bd_upd1 fl s) = (ds_prnt s)[?w := v]"
       "ds_seen (bd_upd1 fl s) = (ds_seen s)[?w := True]"
       "ds_snum (bd_upd1 fl s) = (ds_snum s)[?w := 1]"
       "map (\<lambda>(v,oc,ic). v) (ds_stk (bd_upd1 fl s)) = ?w # map (\<lambda>(v,oc,ic). v) (ds_stk s)"
      by (simp_all add: up dfs_discover_def Let_def stk)
    have stkv': "stkverts (bd_upd1 fl s) = insert ?w (stkverts s)" using ef(4) by (simp add: stkverts_def)
    have DD: "\<And>x. desc (bd_upd1 fl s) x
                = (if x = ?w \<or> (v, x) \<in> (pstep s)\<^sup>* then insert ?w (desc s x) else desc s x)"
      using desc_discover[OF tsi wlt False vne lens(1,2) ef(1) ef(2)] .
    have descw: "desc (bd_upd1 fl s) ?w = {?w}"
      using DD[of ?w] desc_fresh_empty[OF tsi wlt False] by simp
    have wnd: "\<And>x. ?w \<notin> desc s x" using False by (auto simp: desc_def)
    have incr: "\<And>x. x \<in> stkverts s \<Longrightarrow> dcard (bd_upd1 fl s) x = Suc (dcard s x) \<and> ds_snum (bd_upd1 fl s) ! x = ds_snum s ! x"
    proof -
      fix x assume xin: "x \<in> stkverts s"
      have reach: "(v, x) \<in> (pstep s)\<^sup>*" using stk_top_reaches[OF spi wf tsi stk xin] .
      have "desc (bd_upd1 fl s) x = insert ?w (desc s x)" using DD[of x] reach by simp
      hence "dcard (bd_upd1 fl s) x = Suc (dcard s x)" using wnd[of x] desc_finite by (simp add: dcard_def)
      moreover have "x \<noteq> ?w" using xin wnstk by auto
      hence "ds_snum (bd_upd1 fl s) ! x = ds_snum s ! x" using ef(3) by (simp add: nth_list_update)
      ultimately show "dcard (bd_upd1 fl s) x = Suc (dcard s x) \<and> ds_snum (bd_upd1 fl s) ! x = ds_snum s ! x" by simp
    qed
    show ?thesis
      unfolding snum_inv_def
    proof (intro conjI)
      show "distinct (map (\<lambda>(v,oc,ic). v) (ds_stk (bd_upd1 fl s)))"
        using ef(4) dist0 wnstk by (simp add: stkverts_def)
    next
      show "\<forall>x < vcount. ds_seen (bd_upd1 fl s) ! x \<longrightarrow> x \<notin> stkverts (bd_upd1 fl s) \<longrightarrow> ds_snum (bd_upd1 fl s) ! x = dcard (bd_upd1 fl s) x"
      proof (intro allI impI)
        fix x assume xlt: "x < vcount" and xseen: "ds_seen (bd_upd1 fl s) ! x" and xns: "x \<notin> stkverts (bd_upd1 fl s)"
        have xnw: "x \<noteq> ?w" and xnstk: "x \<notin> stkverts s" using xns stkv' by auto
        have "ds_seen s ! x" using xseen ef(2) xnw lens by (simp add: nth_list_update)
        hence sn: "ds_snum s ! x = dcard s x" using sn1_0 xlt xnstk by simp
        have "\<not> ((v, x) \<in> (pstep s)\<^sup>*)" using pstep_anc_on_stk[OF spi vin] xlt xnstk by auto
        hence "desc (bd_upd1 fl s) x = desc s x" using DD[of x] xnw by simp
        thus "ds_snum (bd_upd1 fl s) ! x = dcard (bd_upd1 fl s) x"
          using sn ef(3) xnw by (simp add: nth_list_update dcard_def)
      qed
    next
      have dcw: "dcard (bd_upd1 fl s) ?w = 1" using descw by (simp add: dcard_def)
      have snw: "ds_snum (bd_upd1 fl s) ! ?w = 1" using ef(3) wlt lens by (simp add: nth_list_update)
      have "snchk (bd_upd1 fl s) (Suc 0) (map (\<lambda>(v,oc,ic). v) (ds_stk s)) = snchk s 0 (map (\<lambda>(v,oc,ic). v) (ds_stk s))"
        by (rule snchk_incr) (auto simp: incr stkverts_def)
      hence sc1: "snchk (bd_upd1 fl s) (Suc 0) (map (\<lambda>(v,oc,ic). v) (ds_stk s))" using sn2_0 by simp
      show "snchk (bd_upd1 fl s) 0 (map (\<lambda>(v,oc,ic). v) (ds_stk (bd_upd1 fl s)))"
        using ef(4) dcw snw sc1 by simp
    qed
  qed
qed

lemma bd_upd2_sni:
  assumes wf: "dfs_wf s" and sz: "dfs_sized s" and tsi: "tree_seen_inv s"
      and spi: "stk_prnt_inv s" and sni: "snum_inv s" and c: "bd_call2_conds fl s"
  shows "snum_inv (bd_upd2 fl s)"
proof -
  from c obtain v oc ic rest where stk: "ds_stk s = (v, oc, ic) # rest"
      and noc: "\<not> oc < free_out_hi fl ! v" and iclt: "ic < free_in_hi fl ! v"
    by (auto simp: bd_call2_conds_def split: list.splits prod.splits)
  from wf stk have vlt: "v < vcount" and ilo: "in_lo ! v \<le> ic" by (auto simp: dfs_wf_def)
  have lens: "length (ds_seen s) = Suc vcount" "length (ds_prnt s) = Suc vcount"
       "length (ds_snum s) = Suc vcount"
    using sz by (simp_all add: dfs_sized_def)
  let ?e = "free_in_edges fl ! ic"
  let ?w = "fst_list ! ?e"
  have wlt: "?w < vcount" using Hin_valid[OF vlt ilo iclt] .
  have vin: "v \<in> stkverts s" using stk by (auto simp: stkverts_def)
  from sni have dist0: "distinct (map (\<lambda>(v,oc,ic). v) (ds_stk s))"
    and sn1_0: "\<forall>x < vcount. ds_seen s ! x \<longrightarrow> x \<notin> stkverts s \<longrightarrow> ds_snum s ! x = dcard s x"
    and sn2_0: "snchk s 0 (map (\<lambda>(v,oc,ic). v) (ds_stk s))"
    by (auto simp: snum_inv_def)
  show ?thesis
  proof (cases "ds_seen s ! ?w")
    case True
    have eqf: "bd_upd2 fl s = s\<lparr>ds_stk := (v, oc, Suc ic) # rest\<rparr>" using stk True by (simp add: bd_upd2_def Let_def)
    have ef: "ds_prnt (bd_upd2 fl s) = ds_prnt s" "ds_seen (bd_upd2 fl s) = ds_seen s"
       "ds_snum (bd_upd2 fl s) = ds_snum s"
       "map (\<lambda>(v,oc,ic). v) (ds_stk (bd_upd2 fl s)) = map (\<lambda>(v,oc,ic). v) (ds_stk s)"
      by (simp_all add: eqf stk)
    have dd: "\<And>x. desc (bd_upd2 fl s) x = desc s x"
      using pstep_cong[OF ef(1) ef(2)] by (simp add: desc_def ef(2))
    have sc: "snchk (bd_upd2 fl s) 0 (map (\<lambda>(v,oc,ic). v) (ds_stk s)) = snchk s 0 (map (\<lambda>(v,oc,ic). v) (ds_stk s))"
      by (rule snchk_cong) (simp add: dd dcard_def ef(3))
    show ?thesis
      unfolding snum_inv_def
    proof (intro conjI)
      show "distinct (map (\<lambda>(v,oc,ic). v) (ds_stk (bd_upd2 fl s)))" using dist0 ef(4) by simp
    next
      show "\<forall>x < vcount. ds_seen (bd_upd2 fl s) ! x \<longrightarrow> x \<notin> stkverts (bd_upd2 fl s) \<longrightarrow> ds_snum (bd_upd2 fl s) ! x = dcard (bd_upd2 fl s) x"
        using sn1_0 ef dd by (simp add: stkverts_def dcard_def)
    next
      show "snchk (bd_upd2 fl s) 0 (map (\<lambda>(v,oc,ic). v) (ds_stk (bd_upd2 fl s)))"
        using sc sn2_0 ef(4) by simp
    qed
  next
    case False
    have vseen: "ds_seen s ! v" using tsi stk by (auto simp: tree_seen_inv_def)
    have vne: "v \<noteq> ?w" using vseen False by auto
    have wnstk: "?w \<notin> stkverts s" using False stkverts_props[OF wf tsi] by auto
    have up: "bd_upd2 fl s = dfs_discover (s\<lparr>ds_stk := (v, oc, Suc ic) # rest\<rparr>) v ?w ?e"
      using stk False by (simp add: bd_upd2_def Let_def)
    have ef: "ds_prnt (bd_upd2 fl s) = (ds_prnt s)[?w := v]"
       "ds_seen (bd_upd2 fl s) = (ds_seen s)[?w := True]"
       "ds_snum (bd_upd2 fl s) = (ds_snum s)[?w := 1]"
       "map (\<lambda>(v,oc,ic). v) (ds_stk (bd_upd2 fl s)) = ?w # map (\<lambda>(v,oc,ic). v) (ds_stk s)"
      by (simp_all add: up dfs_discover_def Let_def stk)
    have stkv': "stkverts (bd_upd2 fl s) = insert ?w (stkverts s)" using ef(4) by (simp add: stkverts_def)
    have DD: "\<And>x. desc (bd_upd2 fl s) x
                = (if x = ?w \<or> (v, x) \<in> (pstep s)\<^sup>* then insert ?w (desc s x) else desc s x)"
      using desc_discover[OF tsi wlt False vne lens(1,2) ef(1) ef(2)] .
    have descw: "desc (bd_upd2 fl s) ?w = {?w}"
      using DD[of ?w] desc_fresh_empty[OF tsi wlt False] by simp
    have wnd: "\<And>x. ?w \<notin> desc s x" using False by (auto simp: desc_def)
    have incr: "\<And>x. x \<in> stkverts s \<Longrightarrow> dcard (bd_upd2 fl s) x = Suc (dcard s x) \<and> ds_snum (bd_upd2 fl s) ! x = ds_snum s ! x"
    proof -
      fix x assume xin: "x \<in> stkverts s"
      have reach: "(v, x) \<in> (pstep s)\<^sup>*" using stk_top_reaches[OF spi wf tsi stk xin] .
      have "desc (bd_upd2 fl s) x = insert ?w (desc s x)" using DD[of x] reach by simp
      hence "dcard (bd_upd2 fl s) x = Suc (dcard s x)" using wnd[of x] desc_finite by (simp add: dcard_def)
      moreover have "x \<noteq> ?w" using xin wnstk by auto
      hence "ds_snum (bd_upd2 fl s) ! x = ds_snum s ! x" using ef(3) by (simp add: nth_list_update)
      ultimately show "dcard (bd_upd2 fl s) x = Suc (dcard s x) \<and> ds_snum (bd_upd2 fl s) ! x = ds_snum s ! x" by simp
    qed
    show ?thesis
      unfolding snum_inv_def
    proof (intro conjI)
      show "distinct (map (\<lambda>(v,oc,ic). v) (ds_stk (bd_upd2 fl s)))"
        using ef(4) dist0 wnstk by (simp add: stkverts_def)
    next
      show "\<forall>x < vcount. ds_seen (bd_upd2 fl s) ! x \<longrightarrow> x \<notin> stkverts (bd_upd2 fl s) \<longrightarrow> ds_snum (bd_upd2 fl s) ! x = dcard (bd_upd2 fl s) x"
      proof (intro allI impI)
        fix x assume xlt: "x < vcount" and xseen: "ds_seen (bd_upd2 fl s) ! x" and xns: "x \<notin> stkverts (bd_upd2 fl s)"
        have xnw: "x \<noteq> ?w" and xnstk: "x \<notin> stkverts s" using xns stkv' by auto
        have "ds_seen s ! x" using xseen ef(2) xnw lens by (simp add: nth_list_update)
        hence sn: "ds_snum s ! x = dcard s x" using sn1_0 xlt xnstk by simp
        have "\<not> ((v, x) \<in> (pstep s)\<^sup>*)" using pstep_anc_on_stk[OF spi vin] xlt xnstk by auto
        hence "desc (bd_upd2 fl s) x = desc s x" using DD[of x] xnw by simp
        thus "ds_snum (bd_upd2 fl s) ! x = dcard (bd_upd2 fl s) x"
          using sn ef(3) xnw by (simp add: nth_list_update dcard_def)
      qed
    next
      have dcw: "dcard (bd_upd2 fl s) ?w = 1" using descw by (simp add: dcard_def)
      have snw: "ds_snum (bd_upd2 fl s) ! ?w = 1" using ef(3) wlt lens by (simp add: nth_list_update)
      have "snchk (bd_upd2 fl s) (Suc 0) (map (\<lambda>(v,oc,ic). v) (ds_stk s)) = snchk s 0 (map (\<lambda>(v,oc,ic). v) (ds_stk s))"
        by (rule snchk_incr) (auto simp: incr stkverts_def)
      hence sc1: "snchk (bd_upd2 fl s) (Suc 0) (map (\<lambda>(v,oc,ic). v) (ds_stk s))" using sn2_0 by simp
      show "snchk (bd_upd2 fl s) 0 (map (\<lambda>(v,oc,ic). v) (ds_stk (bd_upd2 fl s)))"
        using ef(4) dcw snw sc1 by simp
    qed
  qed
qed

lemma bd_upd3_sni:
  assumes wf: "dfs_wf s" and sz: "dfs_sized s" and tsi: "tree_seen_inv s"
      and spi: "stk_prnt_inv s" and sni: "snum_inv s" and c: "bd_call3_conds fl s"
  shows "snum_inv (bd_upd3 s)"
proof -
  from c obtain v oc ic rest where stk: "ds_stk s = (v, oc, ic) # rest"
    by (auto simp: bd_call3_conds_def split: list.splits prod.splits)
  from wf stk have vlt: "v < vcount" by (auto simp: dfs_wf_def)
  have lsnum: "length (ds_snum s) = Suc vcount" using sz by (simp add: dfs_sized_def)
  let ?pp = "ds_prnt s ! v"
  have bu: "bd_upd3 s = dfs_finish s v rest" using stk by (simp add: bd_upd3_def)
  have ef: "ds_prnt (bd_upd3 s) = ds_prnt s" "ds_seen (bd_upd3 s) = ds_seen s"
     "ds_snum (bd_upd3 s) = (ds_snum s)[?pp := ds_snum s ! ?pp + ds_snum s ! v]"
     "map (\<lambda>(v,oc,ic). v) (ds_stk (bd_upd3 s)) = map (\<lambda>(v,oc,ic). v) rest"
    by (simp_all add: bu dfs_finish_def Let_def)
  have dd: "\<And>x. desc (bd_upd3 s) x = desc s x" using pstep_cong[OF ef(1) ef(2)] by (simp add: desc_def ef(2))
  have ddc: "\<And>x. dcard (bd_upd3 s) x = dcard s x" by (simp add: dcard_def dd)
  have mapstk: "map (\<lambda>(v,oc,ic). v) (ds_stk s) = v # map (\<lambda>(v,oc,ic). v) rest" using stk by simp
  have vc: "vchain (ds_prnt s) (v # map (\<lambda>(v,oc,ic). v) rest)" using spi mapstk by (simp add: stk_prnt_inv_def)
  from sni have dist0: "distinct (v # map (\<lambda>(v,oc,ic). v) rest)"
    and sn1_0: "\<forall>x < vcount. ds_seen s ! x \<longrightarrow> x \<notin> stkverts s \<longrightarrow> ds_snum s ! x = dcard s x"
    and sn2_0: "snchk s 0 (v # map (\<lambda>(v,oc,ic). v) rest)"
    using mapstk by (auto simp: snum_inv_def)
  have snv: "dcard s v = ds_snum s ! v" using sn2_0 by simp
  have sn2_tail: "snchk s (ds_snum s ! v) (map (\<lambda>(v,oc,ic). v) rest)" using sn2_0 snv by simp
  show ?thesis
    unfolding snum_inv_def
  proof (intro conjI)
    show "distinct (map (\<lambda>(v,oc,ic). v) (ds_stk (bd_upd3 s)))" using dist0 ef(4) by simp
  next
    show "\<forall>x < vcount. ds_seen (bd_upd3 s) ! x \<longrightarrow> x \<notin> stkverts (bd_upd3 s) \<longrightarrow> ds_snum (bd_upd3 s) ! x = dcard (bd_upd3 s) x"
    proof (intro allI impI)
      fix x assume xlt: "x < vcount" and xseen: "ds_seen (bd_upd3 s) ! x" and xns: "x \<notin> stkverts (bd_upd3 s)"
      have xnrest: "x \<notin> set (map (\<lambda>(v,oc,ic). v) rest)" using xns ef(4) by (simp add: stkverts_def)
      show "ds_snum (bd_upd3 s) ! x = dcard (bd_upd3 s) x"
      proof (cases "x = v")
        case True
        have "?pp \<noteq> v" using vc dist0 vlt by (cases "map (\<lambda>(v,oc,ic). v) rest") auto
        hence "ds_snum (bd_upd3 s) ! x = ds_snum s ! v" using ef(3) True by (simp add: nth_list_update_neq)
        thus ?thesis using snv True ddc by simp
      next
        case False
        have xnstk: "x \<notin> stkverts s" using xnrest False mapstk by (simp add: stkverts_def)
        have xseen': "ds_seen s ! x" using xseen ef(2) by simp
        have sn: "ds_snum s ! x = dcard s x" using sn1_0 xlt xseen' xnstk by simp
        have "x \<noteq> ?pp"
        proof (cases "map (\<lambda>(v,oc,ic). v) rest")
          case Nil hence "?pp = vcount" using vc by simp
          thus ?thesis using xlt by auto
        next
          case (Cons g gs) hence "?pp = g" using vc by simp
          thus ?thesis using xnrest Cons by auto
        qed
        hence "ds_snum (bd_upd3 s) ! x = ds_snum s ! x" using ef(3) by (simp add: nth_list_update_neq)
        thus ?thesis using sn ddc by simp
      qed
    qed
  next
    show "snchk (bd_upd3 s) 0 (map (\<lambda>(v,oc,ic). v) (ds_stk (bd_upd3 s)))"
    proof (cases "map (\<lambda>(v,oc,ic). v) rest")
      case Nil thus ?thesis using ef(4) by simp
    next
      case (Cons g gs)
      have gin: "g \<in> stkverts s" using Cons mapstk by (auto simp: stkverts_def)
      have glt: "g < length (ds_snum s)" using stkverts_props[OF wf tsi gin] lsnum by simp
      have pg: "?pp = g" using vc Cons by simp
      have gdist: "g \<notin> set gs" using dist0 Cons by simp
      note tlu = sn2_tail[unfolded Cons snchk.simps(2)]
      have dg: "dcard s g = ds_snum s ! g + ds_snum s ! v" using tlu by (rule conjunct1)
      have sgs: "snchk s (dcard s g) gs" using tlu by (rule conjunct2)
      have snumg: "ds_snum (bd_upd3 s) ! g = ds_snum s ! g + ds_snum s ! v"
        using ef(3) pg glt by (simp add: nth_list_update)
      have snumgs: "\<And>x. x \<in> set gs \<Longrightarrow> ds_snum (bd_upd3 s) ! x = ds_snum s ! x"
      proof -
        fix x assume xg: "x \<in> set gs"
        hence "?pp \<noteq> x" using gdist pg by auto
        thus "ds_snum (bd_upd3 s) ! x = ds_snum s ! x" using ef(3) by (simp add: nth_list_update_neq)
      qed
      have head: "dcard s g = ds_snum (bd_upd3 s) ! g + 0" using dg snumg by simp
      have cong_prem: "\<And>x. x \<in> set gs \<Longrightarrow> dcard (bd_upd3 s) x = dcard s x \<and> ds_snum (bd_upd3 s) ! x = ds_snum s ! x"
        using ddc snumgs by simp
      have sc2: "snchk (bd_upd3 s) (dcard s g) gs" using sgs snchk_cong[OF cong_prem] by simp
      have "snchk (bd_upd3 s) 0 (g # gs)"
        unfolding snchk.simps(2) ddc using head sc2 by (rule conjI)
      thus ?thesis unfolding ef(4) Cons .
    qed
  qed
qed

lemma emit_U_edge_sni: "snum_inv s \<Longrightarrow> snum_inv (emit_U_edge s v)"
proof -
  assume sni: "snum_inv s"
  have e: "ds_prnt (emit_U_edge s v) = ds_prnt s" "ds_seen (emit_U_edge s v) = ds_seen s"
     "ds_snum (emit_U_edge s v) = ds_snum s" "ds_stk (emit_U_edge s v) = ds_stk s"
    by (simp_all add: emit_U_edge_def Let_def)
  have "\<And>x. desc (emit_U_edge s v) x = desc s x" using pstep_cong[OF e(1) e(2)] by (simp add: desc_def e(2))
  hence dc: "\<And>x. dcard (emit_U_edge s v) x = dcard s x" by (simp add: dcard_def)
  have "snchk (emit_U_edge s v) 0 (map (\<lambda>(v,oc,ic). v) (ds_stk s)) = snchk s 0 (map (\<lambda>(v,oc,ic). v) (ds_stk s))"
    by (rule snchk_cong) (simp add: dc e(3))
  thus ?thesis using sni e dc by (auto simp: snum_inv_def stkverts_def)
qed

lemma dfs_init_sni: "snum_inv dfs_init"
proof -
  have s: "\<And>x. x < vcount \<Longrightarrow> ds_seen dfs_init ! x = False" by (simp add: dfs_init_def del: replicate_Suc)
  have st: "ds_stk dfs_init = []" by (simp add: dfs_init_def)
  show ?thesis using s st by (auto simp: snum_inv_def stkverts_def)
qed

lemma snum_inv_seed:
  assumes sni: "snum_inv s" and tsi: "tree_seen_inv s"
      and c: "c < vcount" and unseen: "\<not> ds_seen s ! c" and stkempty: "ds_stk s = []"
      and lens: "length (ds_seen s) = Suc vcount" "length (ds_prnt s) = Suc vcount"
                "length (ds_snum s) = Suc vcount"
      and eprnt: "ds_prnt t = (ds_prnt s)[c := vcount]"
      and eseen: "ds_seen t = (ds_seen s)[c := True]"
      and esnum: "ds_snum t = (ds_snum s)[c := 1]"
      and estk:  "ds_stk t = [(c, out_lo ! c, in_lo ! c)]"
  shows "snum_inv t"
proof -
  have vne: "vcount \<noteq> c" using c by simp
  from sni have sn1_0: "\<forall>v < vcount. ds_seen s ! v \<longrightarrow> ds_snum s ! v = dcard s v"
    using stkempty by (auto simp: snum_inv_def stkverts_def)
  have DD: "\<And>x. desc t x = (if x = c \<or> (vcount, x) \<in> (pstep s)\<^sup>* then insert c (desc s x) else desc s x)"
    using desc_discover[OF tsi c unseen vne lens(1,2) eprnt eseen] .
  have descc: "desc t c = {c}" using DD[of c] desc_fresh_empty[OF tsi c unseen] by simp
  have stkt: "stkverts t = {c}" using estk by (simp add: stkverts_def)
  show ?thesis
    unfolding snum_inv_def
  proof (intro conjI)
    show "distinct (map (\<lambda>(v,oc,ic). v) (ds_stk t))" using estk by simp
  next
    show "\<forall>v < vcount. ds_seen t ! v \<longrightarrow> v \<notin> stkverts t \<longrightarrow> ds_snum t ! v = dcard t v"
    proof (intro allI impI)
      fix v assume vlt: "v < vcount" and vseen: "ds_seen t ! v" and vns: "v \<notin> stkverts t"
      have vnc: "v \<noteq> c" using vns stkt by simp
      have "ds_seen s ! v" using vseen eseen vnc lens by (simp add: nth_list_update)
      hence sn: "ds_snum s ! v = dcard s v" using sn1_0 vlt by simp
      have "\<not> (v = c \<or> (vcount, v) \<in> (pstep s)\<^sup>*)" using vnc pstep_from_root vlt by auto
      hence "desc t v = desc s v" using DD[of v] by simp
      thus "ds_snum t ! v = dcard t v" using sn esnum vnc by (simp add: nth_list_update dcard_def)
    qed
  next
    have "dcard t c = 1" using descc by (simp add: dcard_def)
    moreover have "ds_snum t ! c = 1" using esnum c lens by (simp add: nth_list_update)
    ultimately show "snchk t 0 (map (\<lambda>(v,oc,ic). v) (ds_stk t))" using estk by simp
  qed
qed

lemma snum_inv_lsuc: "snum_inv s \<Longrightarrow> snum_inv (s\<lparr>ds_lsuc := L\<rparr>)"
proof -
  assume sni: "snum_inv s"
  let ?t = "s\<lparr>ds_lsuc := L\<rparr>"
  have d: "\<And>x. desc ?t x = desc s x" by (simp add: desc_def pstep_def)
  hence dc: "\<And>x. dcard ?t x = dcard s x" by (simp add: dcard_def)
  have "snchk ?t 0 (map (\<lambda>(v,oc,ic). v) (ds_stk s)) = snchk s 0 (map (\<lambda>(v,oc,ic). v) (ds_stk s))"
    by (rule snchk_cong) (simp add: dc)
  thus ?thesis using sni d dc by (auto simp: snum_inv_def stkverts_def)
qed

text \<open>Design-notes clause I7 for @{const ds_lsuc}: when a vertex @{term v} finishes, @{term \<open>ds_lsuc s ! v\<close>}
      is the \<^emph>\<open>last\<close> vertex emitted inside @{term v}'s subtree (the rightmost descendant in the thread ---
      the block-last for clause J). We phrase it at the array level via @{const desc}: for every finished
      @{term v}, @{term \<open>ds_lsuc s ! v\<close>} is a descendant of @{term v} whose thread-successor \<^emph>\<open>leaves\<close>
      the subtree. It is set at finish to @{const ds_prev} --- which the emission-order stack-descends clause
      (I6) pins as a descendant of the finishing top, and whose thread-successor is @{term 0} (I5) hence
      outside every subtree. As emission continues, that successor is overwritten with a vertex of a sibling
      subtree --- still outside --- so the property is stable. With I6's contiguity (assembly phase) this makes
      @{term \<open>ds_lsuc s ! v\<close>} exactly the last element of @{term v}'s thread-block.\<close>

definition lsuc_inv :: "'n dfs_state \<Rightarrow> bool" where
  "lsuc_inv s \<longleftrightarrow> (\<forall>v < vcount. ds_seen s ! v \<longrightarrow> v \<notin> stkverts s \<longrightarrow>
      ds_lsuc s ! v \<in> desc s v \<and> ds_thrd s ! (ds_lsuc s ! v) \<notin> desc s v)"

lemma bd_upd3_lsi:
  assumes wf: "dfs_wf s" and sz: "dfs_sized s" and spi: "stk_prnt_inv s"
      and thi: "thread_inv s" and eoi: "emit_ord_inv s" and sni: "snum_inv s"
      and lsi: "lsuc_inv s" and c: "bd_call3_conds fl s"
  shows "lsuc_inv (bd_upd3 s)"
proof -
  from c obtain v0 oc ic rest where stk: "ds_stk s = (v0, oc, ic) # rest"
    by (auto simp: bd_call3_conds_def split: list.splits prod.splits)
  from wf stk have v0lt: "v0 < vcount" by (auto simp: dfs_wf_def)
  have llen: "length (ds_lsuc s) = Suc vcount" using sz by (simp add: dfs_sized_def)
  have bu: "bd_upd3 s = dfs_finish s v0 rest" using stk by (simp add: bd_upd3_def)
  have ef: "ds_lsuc (bd_upd3 s) = (ds_lsuc s)[v0 := ds_prev s]"
     "ds_thrd (bd_upd3 s) = ds_thrd s" "ds_prnt (bd_upd3 s) = ds_prnt s"
     "ds_seen (bd_upd3 s) = ds_seen s"
     "map (\<lambda>(v,oc,ic). v) (ds_stk (bd_upd3 s)) = map (\<lambda>(v,oc,ic). v) rest"
    by (simp_all add: bu dfs_finish_def Let_def)
  have dd: "\<And>x. desc (bd_upd3 s) x = desc s x" using pstep_cong[OF ef(3) ef(4)] by (simp add: desc_def ef(4))
  have stkv': "stkverts (bd_upd3 s) = set (map (\<lambda>(v,oc,ic). v) rest)" using ef(5) by (simp add: stkverts_def)
  have mapstk: "map (\<lambda>(v,oc,ic). v) (ds_stk s) = v0 # map (\<lambda>(v,oc,ic). v) rest" using stk by simp
  have dist0: "distinct (v0 # map (\<lambda>(v,oc,ic). v) rest)" using sni mapstk by (auto simp: snum_inv_def)
  from eoi have "ds_stk s \<noteq> [] \<longrightarrow> (ds_prev s, fst (hd (ds_stk s))) \<in> (pstep s)\<^sup>*" by (auto simp: emit_ord_inv_def)
  hence sd: "(ds_prev s, v0) \<in> (pstep s)\<^sup>*" using stk by simp
  from thi have prevem: "ds_prev s = vcount \<or> ds_seen s ! (ds_prev s)"
    and thrdpv: "ds_thrd s ! (ds_prev s) = 0"
    and prevlt: "ds_prev s < Suc vcount"
    and zerouns: "\<not> ds_seen s ! 0" by (auto simp: thread_inv_def)
  have prevnv: "ds_prev s \<noteq> vcount"
  proof
    assume "ds_prev s = vcount"
    hence "(vcount, v0) \<in> (pstep s)\<^sup>*" using sd by simp
    hence "v0 = vcount" by (rule pstep_from_root)
    thus False using v0lt by simp
  qed
  have prevlt2: "ds_prev s < vcount" using prevlt prevnv by simp
  have prevseen: "ds_seen s ! (ds_prev s)" using prevem prevnv by simp
  have prevdesc: "ds_prev s \<in> desc s v0" using prevlt2 prevseen sd by (simp add: desc_def)
  have zero_nd: "\<And>x. (0::nat) \<notin> desc s x" using zerouns by (auto simp: desc_def)
  show ?thesis
    unfolding lsuc_inv_def
  proof (intro allI impI)
    fix u assume ult: "u < vcount" and useen: "ds_seen (bd_upd3 s) ! u" and uns: "u \<notin> stkverts (bd_upd3 s)"
    have useen': "ds_seen s ! u" using useen ef(4) by simp
    have unrest: "u \<notin> set (map (\<lambda>(v,oc,ic). v) rest)" using uns stkv' by simp
    show "ds_lsuc (bd_upd3 s) ! u \<in> desc (bd_upd3 s) u \<and> ds_thrd (bd_upd3 s) ! (ds_lsuc (bd_upd3 s) ! u) \<notin> desc (bd_upd3 s) u"
    proof (cases "u = v0")
      case True
      have l1: "ds_lsuc (bd_upd3 s) ! u = ds_prev s" using ef(1) True v0lt llen by (simp add: nth_list_update)
      have "ds_lsuc (bd_upd3 s) ! u \<in> desc (bd_upd3 s) u" using l1 True prevdesc dd by simp
      moreover have "ds_thrd (bd_upd3 s) ! (ds_lsuc (bd_upd3 s) ! u) = 0" using ef(2) l1 thrdpv by simp
      hence "ds_thrd (bd_upd3 s) ! (ds_lsuc (bd_upd3 s) ! u) \<notin> desc (bd_upd3 s) u" using zero_nd dd by simp
      ultimately show ?thesis by simp
    next
      case False
      have unstk: "u \<notin> stkverts s" using unrest False mapstk by (auto simp: stkverts_def)
      have leq: "ds_lsuc (bd_upd3 s) ! u = ds_lsuc s ! u" using ef(1) False by (simp add: nth_list_update)
      from lsi have "ds_lsuc s ! u \<in> desc s u \<and> ds_thrd s ! (ds_lsuc s ! u) \<notin> desc s u"
        using ult useen' unstk by (auto simp: lsuc_inv_def)
      thus ?thesis using leq ef(2) dd by simp
    qed
  qed
qed

lemma bd_upd1_lsi:
  assumes wf: "dfs_wf s" and sz: "dfs_sized s" and tsi: "tree_seen_inv s"
      and spi: "stk_prnt_inv s" and thi: "thread_inv s" and lsi: "lsuc_inv s" and c: "bd_call1_conds fl s"
  shows "lsuc_inv (bd_upd1 fl s)"
proof -
  from c obtain v oc ic rest where stk: "ds_stk s = (v, oc, ic) # rest" and oclt: "oc < free_out_hi fl ! v"
    by (auto simp: bd_call1_conds_def split: list.splits prod.splits)
  from wf stk have vlt: "v < vcount" and olo: "out_lo ! v \<le> oc" by (auto simp: dfs_wf_def)
  have lens: "length (ds_seen s) = Suc vcount" "length (ds_prnt s) = Suc vcount" "length (ds_thrd s) = Suc vcount"
    using sz by (simp_all add: dfs_sized_def)
  have prevlt: "ds_prev s < Suc vcount" using thi by (simp add: thread_inv_def)
  let ?e = "free_out_edges fl ! oc"
  let ?w = "snd_list ! ?e"
  have wlt: "?w < vcount" using Hout_valid[OF vlt olo oclt] .
  have vin: "v \<in> stkverts s" using stk by (auto simp: stkverts_def)
  show ?thesis
  proof (cases "ds_seen s ! ?w")
    case True
    have eqf: "bd_upd1 fl s = s\<lparr>ds_stk := (v, Suc oc, ic) # rest\<rparr>" using stk True by (simp add: bd_upd1_def Let_def)
    have ef: "ds_lsuc (bd_upd1 fl s) = ds_lsuc s" "ds_thrd (bd_upd1 fl s) = ds_thrd s"
       "ds_prnt (bd_upd1 fl s) = ds_prnt s" "ds_seen (bd_upd1 fl s) = ds_seen s"
       "map (\<lambda>(v,oc,ic). v) (ds_stk (bd_upd1 fl s)) = map (\<lambda>(v,oc,ic). v) (ds_stk s)"
      by (simp_all add: eqf stk)
    have dd: "\<And>x. desc (bd_upd1 fl s) x = desc s x" using pstep_cong[OF ef(3) ef(4)] by (simp add: desc_def ef(4))
    have "stkverts (bd_upd1 fl s) = stkverts s" using ef(5) by (simp add: stkverts_def)
    thus ?thesis using lsi ef dd by (auto simp: lsuc_inv_def)
  next
    case False
    have wns: "\<not> ds_seen s ! ?w" using False .
    have vseen: "ds_seen s ! v" using tsi stk by (auto simp: tree_seen_inv_def)
    have vne: "v \<noteq> ?w" using vseen wns by auto
    have up: "bd_upd1 fl s = dfs_discover (s\<lparr>ds_stk := (v, Suc oc, ic) # rest\<rparr>) v ?w ?e"
      using stk False by (simp add: bd_upd1_def Let_def)
    have ef: "ds_lsuc (bd_upd1 fl s) = ds_lsuc s"
       "ds_thrd (bd_upd1 fl s) = (ds_thrd s)[ds_prev s := ?w]"
       "ds_prnt (bd_upd1 fl s) = (ds_prnt s)[?w := v]"
       "ds_seen (bd_upd1 fl s) = (ds_seen s)[?w := True]"
       "map (\<lambda>(v,oc,ic). v) (ds_stk (bd_upd1 fl s)) = ?w # map (\<lambda>(v,oc,ic). v) (ds_stk s)"
      by (simp_all add: up dfs_discover_def Let_def stk)
    have stkv': "stkverts (bd_upd1 fl s) = insert ?w (stkverts s)" using ef(5) by (simp add: stkverts_def)
    have DD: "\<And>x. desc (bd_upd1 fl s) x
                = (if x = ?w \<or> (v, x) \<in> (pstep s)\<^sup>* then insert ?w (desc s x) else desc s x)"
      using desc_discover[OF tsi wlt wns vne lens(1,2) ef(3) ef(4)] .
    have wnd: "\<And>x. ?w \<notin> desc s x" using wns by (auto simp: desc_def)
    show ?thesis
      unfolding lsuc_inv_def
    proof (intro allI impI)
      fix u assume ult: "u < vcount" and useen: "ds_seen (bd_upd1 fl s) ! u" and uns: "u \<notin> stkverts (bd_upd1 fl s)"
      have unw: "u \<noteq> ?w" and unstk: "u \<notin> stkverts s" using uns stkv' by auto
      have useen': "ds_seen s ! u" using useen ef(4) unw lens by (simp add: nth_list_update)
      have notanc: "\<not> ((v, u) \<in> (pstep s)\<^sup>*)" using pstep_anc_on_stk[OF spi vin] ult unstk by auto
      have descu: "desc (bd_upd1 fl s) u = desc s u" using DD[of u] unw notanc by simp
      from lsi have LSu: "ds_lsuc s ! u \<in> desc s u" and LSt: "ds_thrd s ! (ds_lsuc s ! u) \<notin> desc s u"
        using ult useen' unstk by (auto simp: lsuc_inv_def)
      have "ds_lsuc (bd_upd1 fl s) ! u \<in> desc (bd_upd1 fl s) u" using ef(1) LSu descu by simp
      moreover have "ds_thrd (bd_upd1 fl s) ! (ds_lsuc s ! u) \<notin> desc (bd_upd1 fl s) u"
      proof (cases "ds_lsuc s ! u = ds_prev s")
        case True
        have "ds_thrd (bd_upd1 fl s) ! (ds_lsuc s ! u) = ?w" using ef(2) True prevlt lens by (simp add: nth_list_update)
        thus ?thesis using wnd descu by simp
      next
        case False
        have "ds_thrd (bd_upd1 fl s) ! (ds_lsuc s ! u) = ds_thrd s ! (ds_lsuc s ! u)"
          using ef(2) False by (simp add: nth_list_update)
        thus ?thesis using LSt descu by simp
      qed
      ultimately show "ds_lsuc (bd_upd1 fl s) ! u \<in> desc (bd_upd1 fl s) u
              \<and> ds_thrd (bd_upd1 fl s) ! (ds_lsuc (bd_upd1 fl s) ! u) \<notin> desc (bd_upd1 fl s) u"
        using ef(1) by simp
    qed
  qed
qed

lemma bd_upd2_lsi:
  assumes wf: "dfs_wf s" and sz: "dfs_sized s" and tsi: "tree_seen_inv s"
      and spi: "stk_prnt_inv s" and thi: "thread_inv s" and lsi: "lsuc_inv s" and c: "bd_call2_conds fl s"
  shows "lsuc_inv (bd_upd2 fl s)"
proof -
  from c obtain v oc ic rest where stk: "ds_stk s = (v, oc, ic) # rest"
      and noc: "\<not> oc < free_out_hi fl ! v" and iclt: "ic < free_in_hi fl ! v"
    by (auto simp: bd_call2_conds_def split: list.splits prod.splits)
  from wf stk have vlt: "v < vcount" and ilo: "in_lo ! v \<le> ic" by (auto simp: dfs_wf_def)
  have lens: "length (ds_seen s) = Suc vcount" "length (ds_prnt s) = Suc vcount" "length (ds_thrd s) = Suc vcount"
    using sz by (simp_all add: dfs_sized_def)
  have prevlt: "ds_prev s < Suc vcount" using thi by (simp add: thread_inv_def)
  let ?e = "free_in_edges fl ! ic"
  let ?w = "fst_list ! ?e"
  have wlt: "?w < vcount" using Hin_valid[OF vlt ilo iclt] .
  have vin: "v \<in> stkverts s" using stk by (auto simp: stkverts_def)
  show ?thesis
  proof (cases "ds_seen s ! ?w")
    case True
    have eqf: "bd_upd2 fl s = s\<lparr>ds_stk := (v, oc, Suc ic) # rest\<rparr>" using stk True by (simp add: bd_upd2_def Let_def)
    have ef: "ds_lsuc (bd_upd2 fl s) = ds_lsuc s" "ds_thrd (bd_upd2 fl s) = ds_thrd s"
       "ds_prnt (bd_upd2 fl s) = ds_prnt s" "ds_seen (bd_upd2 fl s) = ds_seen s"
       "map (\<lambda>(v,oc,ic). v) (ds_stk (bd_upd2 fl s)) = map (\<lambda>(v,oc,ic). v) (ds_stk s)"
      by (simp_all add: eqf stk)
    have dd: "\<And>x. desc (bd_upd2 fl s) x = desc s x" using pstep_cong[OF ef(3) ef(4)] by (simp add: desc_def ef(4))
    have "stkverts (bd_upd2 fl s) = stkverts s" using ef(5) by (simp add: stkverts_def)
    thus ?thesis using lsi ef dd by (auto simp: lsuc_inv_def)
  next
    case False
    have wns: "\<not> ds_seen s ! ?w" using False .
    have vseen: "ds_seen s ! v" using tsi stk by (auto simp: tree_seen_inv_def)
    have vne: "v \<noteq> ?w" using vseen wns by auto
    have up: "bd_upd2 fl s = dfs_discover (s\<lparr>ds_stk := (v, oc, Suc ic) # rest\<rparr>) v ?w ?e"
      using stk False by (simp add: bd_upd2_def Let_def)
    have ef: "ds_lsuc (bd_upd2 fl s) = ds_lsuc s"
       "ds_thrd (bd_upd2 fl s) = (ds_thrd s)[ds_prev s := ?w]"
       "ds_prnt (bd_upd2 fl s) = (ds_prnt s)[?w := v]"
       "ds_seen (bd_upd2 fl s) = (ds_seen s)[?w := True]"
       "map (\<lambda>(v,oc,ic). v) (ds_stk (bd_upd2 fl s)) = ?w # map (\<lambda>(v,oc,ic). v) (ds_stk s)"
      by (simp_all add: up dfs_discover_def Let_def stk)
    have stkv': "stkverts (bd_upd2 fl s) = insert ?w (stkverts s)" using ef(5) by (simp add: stkverts_def)
    have DD: "\<And>x. desc (bd_upd2 fl s) x
                = (if x = ?w \<or> (v, x) \<in> (pstep s)\<^sup>* then insert ?w (desc s x) else desc s x)"
      using desc_discover[OF tsi wlt wns vne lens(1,2) ef(3) ef(4)] .
    have wnd: "\<And>x. ?w \<notin> desc s x" using wns by (auto simp: desc_def)
    show ?thesis
      unfolding lsuc_inv_def
    proof (intro allI impI)
      fix u assume ult: "u < vcount" and useen: "ds_seen (bd_upd2 fl s) ! u" and uns: "u \<notin> stkverts (bd_upd2 fl s)"
      have unw: "u \<noteq> ?w" and unstk: "u \<notin> stkverts s" using uns stkv' by auto
      have useen': "ds_seen s ! u" using useen ef(4) unw lens by (simp add: nth_list_update)
      have notanc: "\<not> ((v, u) \<in> (pstep s)\<^sup>*)" using pstep_anc_on_stk[OF spi vin] ult unstk by auto
      have descu: "desc (bd_upd2 fl s) u = desc s u" using DD[of u] unw notanc by simp
      from lsi have LSu: "ds_lsuc s ! u \<in> desc s u" and LSt: "ds_thrd s ! (ds_lsuc s ! u) \<notin> desc s u"
        using ult useen' unstk by (auto simp: lsuc_inv_def)
      have "ds_lsuc (bd_upd2 fl s) ! u \<in> desc (bd_upd2 fl s) u" using ef(1) LSu descu by simp
      moreover have "ds_thrd (bd_upd2 fl s) ! (ds_lsuc s ! u) \<notin> desc (bd_upd2 fl s) u"
      proof (cases "ds_lsuc s ! u = ds_prev s")
        case True
        have "ds_thrd (bd_upd2 fl s) ! (ds_lsuc s ! u) = ?w" using ef(2) True prevlt lens by (simp add: nth_list_update)
        thus ?thesis using wnd descu by simp
      next
        case False
        have "ds_thrd (bd_upd2 fl s) ! (ds_lsuc s ! u) = ds_thrd s ! (ds_lsuc s ! u)"
          using ef(2) False by (simp add: nth_list_update)
        thus ?thesis using LSt descu by simp
      qed
      ultimately show "ds_lsuc (bd_upd2 fl s) ! u \<in> desc (bd_upd2 fl s) u
              \<and> ds_thrd (bd_upd2 fl s) ! (ds_lsuc (bd_upd2 fl s) ! u) \<notin> desc (bd_upd2 fl s) u"
        using ef(1) by simp
    qed
  qed
qed

lemma lsuc_inv_seed:
  assumes lsi: "lsuc_inv s" and tsi: "tree_seen_inv s" and thi: "thread_inv s"
      and c: "c < vcount" and unseen: "\<not> ds_seen s ! c" and stkempty: "ds_stk s = []"
      and lens: "length (ds_seen s) = Suc vcount" "length (ds_prnt s) = Suc vcount"
                "length (ds_thrd s) = Suc vcount"
      and elsuc: "ds_lsuc t = ds_lsuc s"
      and eprnt: "ds_prnt t = (ds_prnt s)[c := vcount]"
      and eseen: "ds_seen t = (ds_seen s)[c := True]"
      and ethrd: "ds_thrd t = (ds_thrd s)[ds_prev s := c]"
      and estk:  "ds_stk t = [(c, out_lo ! c, in_lo ! c)]"
  shows "lsuc_inv t"
proof -
  have vne: "vcount \<noteq> c" using c by simp
  have prevlt: "ds_prev s < Suc vcount" using thi by (simp add: thread_inv_def)
  from lsi have LS0: "\<forall>u < vcount. ds_seen s ! u \<longrightarrow> ds_lsuc s ! u \<in> desc s u \<and> ds_thrd s ! (ds_lsuc s ! u) \<notin> desc s u"
    using stkempty by (auto simp: lsuc_inv_def stkverts_def)
  have DD: "\<And>x. desc t x = (if x = c \<or> (vcount, x) \<in> (pstep s)\<^sup>* then insert c (desc s x) else desc s x)"
    using desc_discover[OF tsi c unseen vne lens(1,2) eprnt eseen] .
  have cnd: "\<And>x. c \<notin> desc s x" using unseen by (auto simp: desc_def)
  have stkt: "stkverts t = {c}" using estk by (simp add: stkverts_def)
  show ?thesis
    unfolding lsuc_inv_def
  proof (intro allI impI)
    fix u assume ult: "u < vcount" and useen: "ds_seen t ! u" and uns: "u \<notin> stkverts t"
    have unc: "u \<noteq> c" using uns stkt by simp
    have useen': "ds_seen s ! u" using useen eseen unc lens by (simp add: nth_list_update)
    have descu: "desc t u = desc s u"
      using DD[of u] unc pstep_from_root ult by auto
    from LS0 have LSu: "ds_lsuc s ! u \<in> desc s u" and LSt: "ds_thrd s ! (ds_lsuc s ! u) \<notin> desc s u"
      using ult useen' by auto
    have "ds_lsuc t ! u \<in> desc t u" using elsuc LSu descu by simp
    moreover have "ds_thrd t ! (ds_lsuc s ! u) \<notin> desc t u"
    proof (cases "ds_lsuc s ! u = ds_prev s")
      case True
      have "ds_thrd t ! (ds_lsuc s ! u) = c" using ethrd True prevlt lens by (simp add: nth_list_update)
      thus ?thesis using cnd descu by simp
    next
      case False
      have "ds_thrd t ! (ds_lsuc s ! u) = ds_thrd s ! (ds_lsuc s ! u)"
        using ethrd False by (simp add: nth_list_update)
      thus ?thesis using LSt descu by simp
    qed
    ultimately show "ds_lsuc t ! u \<in> desc t u \<and> ds_thrd t ! (ds_lsuc t ! u) \<notin> desc t u"
      using elsuc by simp
  qed
qed

lemma emit_U_edge_lsi: "lsuc_inv s \<Longrightarrow> lsuc_inv (emit_U_edge s v)"
proof -
  assume lsi: "lsuc_inv s"
  have e: "ds_lsuc (emit_U_edge s v) = ds_lsuc s" "ds_thrd (emit_U_edge s v) = ds_thrd s"
     "ds_prnt (emit_U_edge s v) = ds_prnt s" "ds_seen (emit_U_edge s v) = ds_seen s"
     "ds_stk (emit_U_edge s v) = ds_stk s"
    by (simp_all add: emit_U_edge_def Let_def)
  have "\<And>x. desc (emit_U_edge s v) x = desc s x" using pstep_cong[OF e(3) e(4)] by (simp add: desc_def e(4))
  thus ?thesis using lsi e by (auto simp: lsuc_inv_def stkverts_def)
qed

lemma dfs_init_lsi: "lsuc_inv dfs_init"
proof -
  have s: "\<And>x. x < vcount \<Longrightarrow> ds_seen dfs_init ! x = False" by (simp add: dfs_init_def del: replicate_Suc)
  show ?thesis using s by (auto simp: lsuc_inv_def)
qed

lemma lsuc_inv_root_wrap: "lsuc_inv s \<Longrightarrow> lsuc_inv (s\<lparr>ds_lsuc := (ds_lsuc s)[vcount := L]\<rparr>)"
proof -
  assume lsi: "lsuc_inv s"
  let ?t = "s\<lparr>ds_lsuc := (ds_lsuc s)[vcount := L]\<rparr>"
  have d: "\<And>x. desc ?t x = desc s x" by (simp add: desc_def pstep_def)
  have lu: "\<And>v. v < vcount \<Longrightarrow> ds_lsuc ?t ! v = ds_lsuc s ! v" using nth_list_update_neq by fastforce
  show ?thesis
    unfolding lsuc_inv_def
  proof (intro allI impI)
    fix v assume vlt: "v < vcount" and vseen: "ds_seen ?t ! v" and vns: "v \<notin> stkverts ?t"
    have "ds_seen s ! v" using vseen by simp
    moreover have "v \<notin> stkverts s" using vns by (simp add: stkverts_def)
    ultimately have "ds_lsuc s ! v \<in> desc s v \<and> ds_thrd s ! (ds_lsuc s ! v) \<notin> desc s v"
      using lsi vlt by (auto simp: lsuc_inv_def)
    thus "ds_lsuc ?t ! v \<in> desc ?t v \<and> ds_thrd ?t ! (ds_lsuc ?t ! v) \<notin> desc ?t v"
      using lu[OF vlt] d by simp
  qed
qed

definition dfs_inv :: "'n list \<Rightarrow> 'n dfs_state \<Rightarrow> bool" where
  "dfs_inv fl s \<longleftrightarrow> dfs_wf s \<and> dfs_sized s \<and> tree_seen_inv s \<and> thread_inv s \<and> par_edge_inv fl s \<and> pot_inv s
     \<and> root_pot_inv s \<and> stk_prnt_inv s \<and> emit_ord_inv s \<and> snum_inv s \<and> lsuc_inv s"

lemma bd_upd1_inv:
  assumes "dfs_inv fl s" "bd_call1_conds fl s"
  shows "dfs_inv fl (bd_upd1 fl s)"
  using assms bd_upd1_wf[OF Hout_valid] bd_upd1_sized bd_upd1_tsi[OF Hout_valid]
        bd_upd1_thi[OF Hout_valid] bd_upd1_pei bd_upd1_pot bd_upd1_rpi bd_upd1_spi bd_upd1_eoi
        bd_upd1_sni bd_upd1_lsi
  by (auto simp: dfs_inv_def)

lemma bd_upd2_inv:
  assumes "dfs_inv fl s" "bd_call2_conds fl s"
  shows "dfs_inv fl (bd_upd2 fl s)"
  using assms bd_upd2_wf[OF Hin_valid] bd_upd2_sized bd_upd2_tsi[OF Hin_valid]
        bd_upd2_thi[OF Hin_valid] bd_upd2_pei bd_upd2_pot bd_upd2_rpi bd_upd2_spi bd_upd2_eoi
        bd_upd2_sni bd_upd2_lsi
  by (auto simp: dfs_inv_def)

lemma bd_upd3_inv:
  assumes "dfs_inv fl s" "bd_call3_conds fl s"
  shows "dfs_inv fl (bd_upd3 s)"
  using assms bd_upd3_wf bd_upd3_sized bd_upd3_tsi bd_upd3_thi bd_upd3_pei bd_upd3_pot
        bd_upd3_rpi bd_upd3_spi bd_upd3_eoi bd_upd3_sni bd_upd3_lsi
  by (auto simp: dfs_inv_def)

lemma build_dfs_inv:
  assumes "build_dfs_dom (fl, s)" "dfs_inv fl s"
  shows "dfs_inv fl (build_dfs fl s)"
  using assms(2)
proof (induct rule: bd_induct[OF assms(1)])
  case IH: (1 fl s)
  show ?case
    apply (rule bd_cases[where s = s and fl = fl])
    by (auto intro!: IH(2-4) bd_upd1_inv bd_upd2_inv bd_upd3_inv IH(5)
             simp: bd_simps[OF IH(1)])
qed

lemma build_dfs_inv':
  assumes "dfs_inv fl s" shows "dfs_inv fl (build_dfs fl s)"
proof -
  have dom: "build_dfs_dom (fl, s)" using assms by (simp add: dfs_inv_def build_dfs_dom_wf')
  show ?thesis by (rule build_dfs_inv[OF dom assms])
qed

text \<open>@{const build_dfs} runs until its stack is empty, so every component opened by
      @{const open_tree_component} leaves the stack empty again --- the property that lets the phase folds
      hand each @{const open_tree_component} a between-components state (empty stack), which the subtree
      bookkeeping (I7) needs for its finished-vertex clause.\<close>

lemma build_dfs_stk_empty:
  assumes "build_dfs_dom (fl, s)" shows "ds_stk (build_dfs fl s) = []"
proof (induct rule: bd_induct[OF assms])
  case IH: (1 fl s)
  show ?case
    apply (rule bd_cases[where s = s and fl = fl])
    by (auto intro!: IH(2-4) simp: bd_simps[OF IH(1)] bd_ret_conds_def)
qed

lemma open_tree_component_stk_empty:
  assumes wf: "dfs_wf s" and c: "c < vcount"
  shows "ds_stk (open_tree_component fl s c) = []"
  unfolding open_tree_component_def Let_def
  apply (rule build_dfs_stk_empty)
  apply (rule build_dfs_dom_wf')
  using wf c by (auto simp: dfs_wf_def)

lemma open_tree_component_inv:
  assumes inv: "dfs_inv fl s" and c: "c < vcount" and unseen: "\<not> ds_seen s ! c" and cnz: "c \<noteq> 0"
      and stke: "ds_stk s = []"
  shows "dfs_inv fl (open_tree_component fl s c)"
  unfolding open_tree_component_def Let_def
  apply (rule build_dfs_inv')
  unfolding dfs_inv_def
  apply (intro conjI)
  subgoal using inv c by (auto simp: dfs_inv_def dfs_wf_def dfs_sized_def tree_seen_inv_def nth_list_update)
  subgoal using inv c by (auto simp: dfs_inv_def dfs_wf_def dfs_sized_def tree_seen_inv_def nth_list_update)
  subgoal using inv c by (auto simp: dfs_inv_def dfs_wf_def dfs_sized_def tree_seen_inv_def nth_list_update)
  subgoal
    apply (rule thread_inv_upd[where s = s and w = c])
    using inv c unseen cnz by (auto simp: dfs_inv_def dfs_sized_def)
  subgoal using inv c by (auto simp: dfs_inv_def dfs_sized_def par_edge_inv_def nth_list_update)
  subgoal
    apply (rule pot_inv_seed[where s = s and c = c])
    using inv c unseen by (auto simp: dfs_inv_def dfs_sized_def nth_list_update)
  subgoal using inv c by (auto simp: dfs_inv_def dfs_sized_def root_pot_inv_def nth_list_update)
  subgoal using inv c by (auto simp: dfs_inv_def dfs_sized_def stk_prnt_inv_def nth_list_update)
  subgoal
    apply (rule emit_ord_inv_seed[where s = s and c = c])
    using inv c unseen by (auto simp: dfs_inv_def dfs_sized_def)
  subgoal
    apply (rule snum_inv_seed[where s = s and c = c])
    using inv c unseen stke by (auto simp: dfs_inv_def dfs_sized_def)
  subgoal
    apply (rule lsuc_inv_seed[where s = s and c = c])
    using inv c unseen stke by (auto simp: dfs_inv_def dfs_sized_def)
  done

lemma emit_U_edge_inv: "dfs_inv fl s \<Longrightarrow> dfs_inv fl (emit_U_edge s v)"
  using emit_U_edge_thi emit_U_edge_eoi emit_U_edge_sni emit_U_edge_lsi
  by (auto simp: dfs_inv_def dfs_wf_def dfs_sized_def tree_seen_inv_def par_edge_inv_def
                 pot_inv_def root_pot_inv_def stk_prnt_inv_def emit_U_edge_def Let_def)

lemma phase1_step_inv:
  assumes "v \<in> set vs_list" and pre: "dfs_inv fl s \<and> ds_stk s = []"
  shows "dfs_inv fl (phase1_step fl v s) \<and> ds_stk (phase1_step fl v s) = []"
proof -
  have inv: "dfs_inv fl s" and stke: "ds_stk s = []" using pre by auto
  show ?thesis
  proof (cases "imbalance ! v = 0")
    case True thus ?thesis using inv stke by (simp add: phase1_step_def)
  next
    case nz: False
    show ?thesis
    proof (cases "ds_seen s ! v")
      case True
      have "ds_stk (emit_U_edge s v) = []" using stke by (simp add: emit_U_edge_def Let_def)
      thus ?thesis using nz True emit_U_edge_inv[OF inv] by (simp add: phase1_step_def)
    next
      case False
      have vlt: "v < vcount" using vs_less_vcount[OF assms(1)] .
      have vnz: "v \<noteq> 0" using assms(1) no_zero_node by (metis)
      have wf: "dfs_wf s" using inv by (simp add: dfs_inv_def)
      have "ds_stk (open_tree_component fl s v) = []" using open_tree_component_stk_empty[OF wf vlt] .
      thus ?thesis using nz False open_tree_component_inv[OF inv vlt False vnz stke]
        by (simp add: phase1_step_def)
    qed
  qed
qed

lemma phase2_step_inv:
  assumes "v \<in> set vs_list" and pre: "dfs_inv fl s \<and> ds_stk s = []"
  shows "dfs_inv fl (phase2_step fl v s) \<and> ds_stk (phase2_step fl v s) = []"
proof -
  have inv: "dfs_inv fl s" and stke: "ds_stk s = []" using pre by auto
  show ?thesis
  proof (cases "ds_seen s ! v")
    case True thus ?thesis using inv stke by (simp add: phase2_step_def)
  next
    case False
    note ns = this
    have vlt: "v < vcount" using vs_less_vcount[OF assms(1)] .
    show ?thesis
    proof (cases "is_lonely v")
      case True \<comment> \<open>edge-less vertex: the guard fires, the state is unchanged\<close>
      thus ?thesis using inv stke by (simp add: phase2_step_def)
    next
      case False \<comment> \<open>a real vertex: the component is opened exactly as before\<close>
      note nl = this
      have vnz: "v \<noteq> 0" using assms(1) no_zero_node by (metis)
      have wf: "dfs_wf s" using inv by (simp add: dfs_inv_def)
      have stkeq: "ds_stk (open_tree_component fl s v) = []" using open_tree_component_stk_empty[OF wf vlt] .
      have eq: "phase2_step fl v s = open_tree_component fl s v" by (simp add: phase2_step_def ns nl)
      show ?thesis using eq stkeq open_tree_component_inv[OF inv vlt ns vnz stke] by simp
    qed
  qed
qed

lemma dfs_init_inv: "dfs_inv fl dfs_init"
  unfolding dfs_inv_def
proof (intro conjI)
  show "dfs_wf dfs_init" by (simp add: dfs_wf_def dfs_init_def)
  show "dfs_sized dfs_init" by (rule dfs_init_sized)
  show "tree_seen_inv dfs_init" by (simp add: tree_seen_inv_def dfs_init_def del: replicate_Suc)
  show "thread_inv dfs_init" by (rule dfs_init_thi)
  show "par_edge_inv fl dfs_init" by (simp add: par_edge_inv_def dfs_init_def del: replicate_Suc)
  show "pot_inv dfs_init" by (simp add: pot_inv_def dfs_init_def del: replicate_Suc)
  show "root_pot_inv dfs_init" by (simp add: root_pot_inv_def dfs_init_def del: replicate_Suc)
  show "stk_prnt_inv dfs_init" by (simp add: stk_prnt_inv_def dfs_init_def)
  show "emit_ord_inv dfs_init" by (rule dfs_init_eoi)
  show "snum_inv dfs_init" by (rule dfs_init_sni)
  show "lsuc_inv dfs_init" by (rule dfs_init_lsi)
qed

lemma phase1_inv:
  assumes "dfs_inv fl s \<and> ds_stk s = []" shows "dfs_inv fl (phase1 fl s) \<and> ds_stk (phase1 fl s) = []"
  unfolding phase1_def
  apply (rule fold_invariant[where Q = "\<lambda>v. v \<in> set vs_list" and P = "\<lambda>s. dfs_inv fl s \<and> ds_stk s = []"])
    apply simp
   apply (rule assms)
  apply (erule (1) phase1_step_inv)
  done

lemma phase2_inv:
  assumes "dfs_inv fl s \<and> ds_stk s = []" shows "dfs_inv fl (phase2 fl s) \<and> ds_stk (phase2 fl s) = []"
  unfolding phase2_def
  apply (rule fold_invariant[where Q = "\<lambda>v. v \<in> set vs_list" and P = "\<lambda>s. dfs_inv fl s \<and> ds_stk s = []"])
    apply simp
   apply (rule assms)
  apply (erule (1) phase2_step_inv)
  done

lemma build_tree_inv: "dfs_inv fl (build_tree fl)"
proof -
  have i0: "dfs_inv fl dfs_init \<and> ds_stk dfs_init = []" using dfs_init_inv by (simp add: dfs_init_def)
  have "dfs_inv fl (phase2 fl (phase1 fl dfs_init)) \<and> ds_stk (phase2 fl (phase1 fl dfs_init)) = []"
    using phase2_inv[OF phase1_inv[OF i0]] .
  hence inv: "dfs_inv fl (phase2 fl (phase1 fl dfs_init))" by simp
  show ?thesis
    unfolding build_tree_def Let_def
    using inv snum_inv_lsuc[of "phase2 fl (phase1 fl dfs_init)"] lsuc_inv_root_wrap[of "phase2 fl (phase1 fl dfs_init)"]
    by (auto simp: dfs_inv_def dfs_wf_def dfs_sized_def tree_seen_inv_def thread_inv_def
                   par_edge_inv_def pot_inv_def root_pot_inv_def stk_prnt_inv_def
                   emit_ord_inv_def pstep_def)
qed

text \<open>The two consequences the arborescence proof will consume: the root is outside the visited set,
      and the parent map on the visited vertices is a forest directed towards @{term vcount}.\<close>

lemma build_tree_root_unseen: "\<not> ds_seen (build_tree fl) ! vcount"
  using build_tree_inv by (auto simp: dfs_inv_def tree_seen_inv_def)

lemma build_tree_parent_in_seen:
  assumes "w < vcount" "ds_seen (build_tree fl) ! w"
  shows "ds_prnt (build_tree fl) ! w = vcount \<or> (ds_prnt (build_tree fl) ! w < vcount \<and> ds_seen (build_tree fl) ! (ds_prnt (build_tree fl) ! w))"
  using build_tree_inv assms by (auto simp: dfs_inv_def tree_seen_inv_def)

text \<open>Design-notes I3 for the finished tree: every interior tree vertex's stored parent edge is a real
      free edge realising the link to its parent, with the recorded orientation. (Component roots,
      \<open>prnt = vcount\<close>, are excluded --- their parent edge is the artificial one.)\<close>

lemma build_tree_par_edge:
  assumes "w < vcount" "ds_seen (build_tree fl) ! w" "ds_prnt (build_tree fl) ! w < vcount"
  shows "ds_par (build_tree fl) ! w < m \<and> is_free fl (ds_par (build_tree fl) ! w)
         \<and> ds_dir (build_tree fl) ! w = (fst_list ! (ds_par (build_tree fl) ! w) = w)
         \<and> fst_list ! (ds_par (build_tree fl) ! w) = (if ds_dir (build_tree fl) ! w then w else ds_prnt (build_tree fl) ! w)
         \<and> snd_list ! (ds_par (build_tree fl) ! w) = (if ds_dir (build_tree fl) ! w then ds_prnt (build_tree fl) ! w else w)"
  using build_tree_inv assms by (auto simp: dfs_inv_def par_edge_inv_def)

text \<open>Design-notes I4 for the finished tree: every interior tree vertex's potential is its parent's
      plus the @{term \<open>M_0\<close>}-tagged signed cost of its tree edge --- zero reduced cost on that edge
      (abstract-level once \<open>good_pot_val\<close> is available at assembly).\<close>

lemma build_tree_pot:
  assumes "w < vcount" "ds_seen (build_tree fl) ! w" "ds_prnt (build_tree fl) ! w < vcount"
  shows "ds_pot (build_tree fl) ! w = pval_plus (ds_pot (build_tree fl) ! (ds_prnt (build_tree fl) ! w))
           (M_0, if ds_prnt (build_tree fl) ! w = fst_list ! (ds_par (build_tree fl) ! w)
                 then cost_list ! (ds_par (build_tree fl) ! w) else - cost_list ! (ds_par (build_tree fl) ! w))"
  using build_tree_inv assms by (auto simp: dfs_inv_def pot_inv_def)

text \<open>Design-notes I1 for the root: the finished tree gives the artificial root zero potential
      (\<open>\<pi> r = 0\<close>, consumed by \<open>init_pot_fits\<close>).\<close>

lemma build_tree_root_pot: "ds_pot (build_tree fl) ! vcount = pval_zero"
  using build_tree_inv by (simp add: dfs_inv_def root_pot_inv_def)

text \<open>Design-notes I6 for the finished tree (the full preorder DFS step of \<open>preorder_contiguous\<close>):
      the parent of every emitted vertex is an ancestor --- in the parent-step closure @{term \<open>(pstep (build_tree fl))\<^sup>*\<close>}
      --- of its thread-predecessor @{const ds_rvth}. Together with the thread mutual-inverse (I5) this is
      exactly the \<open>dfs\<close> premise of \<open>preorder_contiguous\<close>, restated over the arrays; the array{\isasymrightarrow}abstract
      \<open>follow\<close>/\<open>parent_spec\<close> bridge that turns @{term pstep} closure into an abstract root-path is set up
      at \<open>arb_invar\<close> assembly.\<close>

lemma build_tree_emit_order:
  assumes "w < vcount" "ds_seen (build_tree fl) ! w"
  shows "(ds_rvth (build_tree fl) ! w, ds_prnt (build_tree fl) ! w) \<in> (pstep (build_tree fl))\<^sup>*"
  using build_tree_inv assms by (auto simp: dfs_inv_def emit_ord_inv_def)

text \<open>Every emitted vertex reaches the artificial root through the parent-step closure --- the array
      counterpart of \<open>follow T v\<close> terminating at the root, and the ingredient that makes the abstract
      parent map a genuine forest rooted at @{term vcount}.\<close>

lemma build_tree_reaches_root:
  assumes "w < vcount" "ds_seen (build_tree fl) ! w"
  shows "(w, vcount) \<in> (pstep (build_tree fl))\<^sup>*"
  using build_tree_inv assms by (auto simp: dfs_inv_def emit_ord_inv_def)

text \<open>Design-notes I7 for the finished tree: @{term \<open>ds_snum (build_tree fl) ! w\<close>} is the size of @{term w}'s
      subtree --- where the subtree is the array set @{term \<open>desc (build_tree fl) w\<close>} of emitted
      @{const pstep}-descendants, the counterpart of the abstract @{text \<open>children (prnt S) w\<close>}. The whole
      DFS stack is empty at @{const build_tree}, so every emitted vertex is finished and the
      finished-vertex clause of @{const snum_inv} applies to all of them.\<close>

lemma build_tree_stk_empty: "ds_stk (build_tree fl) = []"
proof -
  have i0: "dfs_inv fl dfs_init \<and> ds_stk dfs_init = []" using dfs_init_inv by (simp add: dfs_init_def)
  have "ds_stk (phase2 fl (phase1 fl dfs_init)) = []" using phase2_inv[OF phase1_inv[OF i0]] by simp
  thus ?thesis unfolding build_tree_def Let_def by simp
qed

lemma build_tree_snum:
  assumes "w < vcount" "ds_seen (build_tree fl) ! w"
  shows "ds_snum (build_tree fl) ! w = dcard (build_tree fl) w"
proof -
  have "snum_inv (build_tree fl)" using build_tree_inv by (simp add: dfs_inv_def)
  moreover have "w \<notin> stkverts (build_tree fl)" using build_tree_stk_empty by (simp add: stkverts_def)
  ultimately show ?thesis using assms by (auto simp: snum_inv_def)
qed

text \<open>Design-notes I7 for @{const ds_lsuc} on the finished tree: every tree vertex's stored last-successor
      is a descendant of it whose thread-successor leaves its subtree --- the array form of "\<open>lsuc S v\<close>
      is the last vertex of @{term v}'s subtree block", which with I6's contiguity gives clause J's
      \<open>last pre = lsuc S v\<close> at \<open>arb_invar\<close> assembly.\<close>

lemma build_tree_lsuc:
  assumes "w < vcount" "ds_seen (build_tree fl) ! w"
  shows "ds_lsuc (build_tree fl) ! w \<in> desc (build_tree fl) w
         \<and> ds_thrd (build_tree fl) ! (ds_lsuc (build_tree fl) ! w) \<notin> desc (build_tree fl) w"
proof -
  have "lsuc_inv (build_tree fl)" using build_tree_inv by (simp add: dfs_inv_def)
  moreover have "w \<notin> stkverts (build_tree fl)" using build_tree_stk_empty by (simp add: stkverts_def)
  ultimately show ?thesis using assms by (auto simp: lsuc_inv_def)
qed

text \<open>The thread consequences (design notes I5): @{const ds_rvth} recovers the @{const ds_thrd}
      source of every emitted, non-last vertex, the root has no thread predecessor, and each thread
      successor of an emitted non-last vertex is itself an emitted vertex --- the raw material for
      \<open>parent_spec\<close> of the thread and reverse-thread maps and the mutual-inverse clauses of
      \<open>arb_invar\<close>.\<close>

lemma build_tree_thread_inv: "thread_inv (build_tree fl)"
  using build_tree_inv by (simp add: dfs_inv_def)

lemma build_tree_root_no_pred: "ds_rvth (build_tree fl) ! vcount = 0"
  using build_tree_thread_inv by (simp add: thread_inv_def)

lemma build_tree_thread_inverse:
  assumes "x < Suc vcount" "x = vcount \<or> ds_seen (build_tree fl) ! x" "x \<noteq> ds_prev (build_tree fl)"
  shows "ds_thrd (build_tree fl) ! x < Suc vcount"
    and "ds_thrd (build_tree fl) ! x = vcount \<or> ds_seen (build_tree fl) ! (ds_thrd (build_tree fl) ! x)"
    and "ds_rvth (build_tree fl) ! (ds_thrd (build_tree fl) ! x) = x"
  using build_tree_thread_inv assms by (auto simp: thread_inv_def)

lemma build_tree_rev_thread_inverse:
  assumes "x < Suc vcount" "x = vcount \<or> ds_seen (build_tree fl) ! x" "x \<noteq> vcount"
  shows "ds_rvth (build_tree fl) ! x < Suc vcount"
    and "ds_rvth (build_tree fl) ! x = vcount \<or> ds_seen (build_tree fl) ! (ds_rvth (build_tree fl) ! x)"
    and "ds_thrd (build_tree fl) ! (ds_rvth (build_tree fl) ! x) = x"
  using build_tree_thread_inv assms by (auto simp: thread_inv_def)

section \<open>Spanning: every vertex is visited by @{const build_tree}\<close>

text \<open>Phase 2 opens every still-unseen vertex, so after the whole build every vertex of @{term vs_list}
      is visited. The proof rests on \<^emph>\<open>monotonicity\<close>: once a vertex is marked, no later step unmarks it
      (@{const dfs_discover} only ever writes @{term True} into @{const ds_seen}, and @{const dfs_finish}
      leaves it untouched). Together with the parent skeleton (design notes I2) this gives the L2
      ingredient @{term \<open>dom T = V - {r}\<close>}: every real vertex has its parent edge in the tree.\<close>

lemma bd_upd1_seen_mono: "bd_call1_conds fl s \<Longrightarrow> ds_seen s ! x \<Longrightarrow> ds_seen (bd_upd1 fl s) ! x"
  by (auto simp: bd_call1_conds_def bd_upd1_def dfs_discover_def Let_def nth_update_True_mono split: list.splits prod.splits if_splits)

lemma bd_upd2_seen_mono: "bd_call2_conds fl s \<Longrightarrow> ds_seen s ! x \<Longrightarrow> ds_seen (bd_upd2 fl s) ! x"
  by (auto simp: bd_call2_conds_def bd_upd2_def dfs_discover_def Let_def nth_update_True_mono split: list.splits prod.splits if_splits)

lemma bd_upd3_seen_mono: "bd_call3_conds fl s \<Longrightarrow> ds_seen s ! x \<Longrightarrow> ds_seen (bd_upd3 s) ! x"
  by (auto simp: bd_call3_conds_def bd_upd3_def dfs_finish_def Let_def split: list.splits prod.splits)

lemma build_dfs_seen_mono:
  assumes "build_dfs_dom (fl, s)" "ds_seen s ! x"
  shows "ds_seen (build_dfs fl s) ! x"
  using assms(2)
proof (induct rule: bd_induct[OF assms(1)])
  case IH: (1 fl s)
  show ?case
    apply (rule bd_cases[where s = s and fl = fl])
    by (auto intro!: IH(2-4) bd_upd1_seen_mono bd_upd2_seen_mono bd_upd3_seen_mono IH(5)
             simp: bd_simps[OF IH(1)])
qed

lemma open_tree_component_marks:
  assumes inv: "dfs_inv fl s" and c: "c < vcount"
  shows "ds_seen (open_tree_component fl s c) ! c"
proof -
  have lseen: "length (ds_seen s) = Suc vcount" using inv by (simp add: dfs_inv_def dfs_sized_def)
  show ?thesis
    unfolding open_tree_component_def Let_def
    apply (rule build_dfs_seen_mono)
     apply (rule build_dfs_dom_wf')
     apply (insert c lseen)
     apply (auto simp: dfs_wf_def)[1]
    apply (simp add: nth_list_update)
    done
qed

lemma open_tree_component_seen_mono:
  assumes inv: "dfs_inv fl s" and c: "c < vcount" and seen: "ds_seen s ! x"
  shows "ds_seen (open_tree_component fl s c) ! x"
proof -
  have lseen: "length (ds_seen s) = Suc vcount" using inv by (simp add: dfs_inv_def dfs_sized_def)
  show ?thesis
    unfolding open_tree_component_def Let_def
    apply (rule build_dfs_seen_mono)
     apply (rule build_dfs_dom_wf')
     apply (insert c lseen seen)
     apply (auto simp: dfs_wf_def)[1]
    apply (simp add: nth_update_True_mono)
    done
qed

lemma phase2_step_marks:
  assumes "dfs_inv fl s" "v < vcount" "\<not> is_lonely v"
  shows "ds_seen (phase2_step fl v s) ! v"
proof (cases "ds_seen s ! v")
  case True thus ?thesis by (simp add: phase2_step_def)
next
  case False thus ?thesis using open_tree_component_marks[OF assms(1) assms(2)] assms(3) by (simp add: phase2_step_def)
qed

lemma phase2_step_seen_mono:
  assumes "dfs_inv fl s" "v < vcount" "ds_seen s ! x"
  shows "ds_seen (phase2_step fl v s) ! x"
proof (cases "ds_seen s ! v")
  case True thus ?thesis using assms(3) by (simp add: phase2_step_def)
next
  case False thus ?thesis using open_tree_component_seen_mono[OF assms(1) assms(2) assms(3)] assms(3) by (simp add: phase2_step_def)
qed

lemma fold_phase2_seen_mono:
  assumes "set us \<subseteq> set vs_list" "dfs_inv fl s \<and> ds_stk s = []" "ds_seen s ! x"
  shows "ds_seen (fold (phase2_step fl) us s) ! x"
  using assms
proof (induct us arbitrary: s)
  case Nil thus ?case by simp
next
  case (Cons u us)
  have u_in: "u \<in> set vs_list" using Cons.prems(1) by auto
  have u_lt: "u < vcount" using vs_less_vcount[OF u_in] .
  have tail: "set us \<subseteq> set vs_list" using Cons.prems(1) by auto
  have inv': "dfs_inv fl (phase2_step fl u s) \<and> ds_stk (phase2_step fl u s) = []"
    using phase2_step_inv[OF u_in Cons.prems(2)] .
  have seen': "ds_seen (phase2_step fl u s) ! x"
    using phase2_step_seen_mono[OF conjunct1[OF Cons.prems(2)] u_lt Cons.prems(3)] .
  have "ds_seen (fold (phase2_step fl) us (phase2_step fl u s)) ! x"
    using Cons.hyps[OF tail inv' seen'] by simp
  thus ?case by simp
qed

lemma fold_phase2_marks:
  assumes "set us \<subseteq> set vs_list" "dfs_inv fl s \<and> ds_stk s = []" "v \<in> set us" "\<not> is_lonely v"
  shows "ds_seen (fold (phase2_step fl) us s) ! v"
  using assms
proof (induct us arbitrary: s)
  case Nil thus ?case by simp
next
  case (Cons u us)
  have u_in: "u \<in> set vs_list" using Cons.prems(1) by auto
  have u_lt: "u < vcount" using vs_less_vcount[OF u_in] .
  have tail: "set us \<subseteq> set vs_list" using Cons.prems(1) by auto
  have inv': "dfs_inv fl (phase2_step fl u s) \<and> ds_stk (phase2_step fl u s) = []"
    using phase2_step_inv[OF u_in Cons.prems(2)] .
  show ?case
  proof (cases "v = u")
    case True
    hence lu: "\<not> is_lonely u" using Cons.prems(4) by simp
    have "ds_seen (phase2_step fl u s) ! v"
      using phase2_step_marks[OF conjunct1[OF Cons.prems(2)] u_lt lu] True by simp
    hence "ds_seen (fold (phase2_step fl) us (phase2_step fl u s)) ! v"
      using fold_phase2_seen_mono[OF tail inv'] by simp
    thus ?thesis by simp
  next
    case False
    have vus: "v \<in> set us" using Cons.prems(3) False by simp
    thus ?thesis using Cons.hyps[OF tail inv' vus Cons.prems(4)] by simp
  qed
qed

text \<open>The tree spans exactly the \<^emph>\<open>edged\<close> vertices: a lonely name of @{term vs_list} is skipped by the
      guard and so is never marked seen.  The non-lonely hypothesis is the one supplied at every use
      site through @{thm edged_not_lonely} / @{const edged_vs_list}.\<close>

lemma build_tree_spans:
  assumes "v \<in> set vs_list" "\<not> is_lonely v"
  shows "ds_seen (build_tree fl) ! v"
proof -
  have i0: "dfs_inv fl dfs_init \<and> ds_stk dfs_init = []" using dfs_init_inv by (simp add: dfs_init_def)
  have inv1: "dfs_inv fl (phase1 fl dfs_init) \<and> ds_stk (phase1 fl dfs_init) = []" using phase1_inv[OF i0] .
  have "ds_seen (phase2 fl (phase1 fl dfs_init)) ! v"
    unfolding phase2_def using fold_phase2_marks[OF subset_refl inv1 assms(1) assms(2)] .
  thus ?thesis by (simp add: build_tree_def Let_def)
qed

text \<open>L2 skeleton: every real vertex sits in the parent map with its parent either the root or another
      visited vertex --- i.e.\ @{term \<open>dom T = V - {r}\<close>} together with \<open>build_tree_root_unseen\<close>.\<close>

lemma build_tree_vertex_parent:
  assumes "v \<in> set vs_list" "\<not> is_lonely v"
  shows "ds_prnt (build_tree fl) ! v = vcount \<or> (ds_prnt (build_tree fl) ! v < vcount \<and> ds_seen (build_tree fl) ! (ds_prnt (build_tree fl) ! v))"
  using build_tree_inv vs_less_vcount[OF assms(1)] build_tree_spans[OF assms(1) assms(2)]
  by (auto simp: dfs_inv_def tree_seen_inv_def)

section \<open>Free-edge coverage: every free edge is a tree edge (needs acyclicity)\<close>

text \<open>The tree edges are exactly the free real edges plus the artificial component-root edges. One
      direction --- parent edges are @{term InTree} --- holds unconditionally (design-notes I3 for interior
      vertices, the component-root emission for roots). The converse --- every \<^emph>\<open>free\<close> real edge is a
      parent edge (so @{term \<open>\<E> = T \<union> U \<union> L\<close>} in \<open>spanning_tree_partition\<close>) --- is the
      forest property: an uncovered free edge would be a back edge of the depth-first spanning forest,
      closing a cycle of free arcs, which the acyclicity of @{term flow_list} forbids.

      We localise the acyclicity hypothesis to a lightweight @{command context} block rather than
      burdening the outer locale: @{term \<open>original_network.acyclic_flow (h \<circ> nth flow_list)\<close>} is precisely what
      @{thm make_acyclic_correct_unconditional_bflow} delivers on the branch where the acyclifying
      procedure returns @{term Some} (a @{term None} answer means a negative infinite-capacity cycle,
      i.e.\ the instance is unbounded and no tree is built).\<close>

text \<open>The correctness lemmas that need the input flow to be capacity-complying and acyclic live in
      this \<open>fl\<close>-fixing context: the strongly-feasible tree is built from an arbitrary acyclic,
      capacity-complying flow \<open>fl\<close> (the acyclifier's output). The pipeline enters this context with
      \<open>fl\<close> instantiated to that output, discharging the three assumptions from the acyclifier's
      correctness.\<close>

context
  fixes fl :: "'n list"
  assumes fl_nonneg: "\<And>e. e < m \<Longrightarrow> 0 \<le> fl ! e"
      and fl_le_cap: "\<And>e. e < m \<Longrightarrow> capacity_list ! e \<noteq> - 1 \<Longrightarrow> fl ! e \<le> capacity_list ! e"
begin

text \<open>The edge classification reads back exactly the residual bounds. This needs only \<open>fl\<close>'s
      \<^emph>\<open>capacity-compliance\<close>, not its acyclicity --- which is why these two live outside the \<open>acyc\<close>
      context nested below: whether an edge is free is a statement about the two residual bounds
      alone. The initial tree's strong feasibility is a consequence of them, so it must not be made
      to depend on the acyclifier's verdict.\<close>

lemma edge_state_InTree_iff:
  assumes "e < m"
  shows "edge_state fl ! e = InTree \<longleftrightarrow>
           0 < fl ! e \<and> (capacity_list ! e = - 1 \<or> fl ! e < capacity_list ! e)"
  using fl_nonneg[OF assms] fl_le_cap[OF assms] edge_state_nth[OF assms]
  by (force simp: classify_def)

lemma is_free_iff:
  assumes "e < m"
  shows "is_free fl e \<longleftrightarrow> 0 < fl ! e \<and> (capacity_list ! e = - 1 \<or> fl ! e < capacity_list ! e)"
  by (simp add: is_free_def edge_state_InTree_iff[OF assms])

context
  assumes acyc: "original_network.acyclic_flow (h \<circ> nth fl)"
begin

text \<open>The concrete consequence used throughout this section: \<open>fl\<close> carries no closed
      residual pre-path of pairwise-distinct free arcs.\<close>

lemma flow_no_free_cycle:
  "\<nexists>C. original_network.prepath C \<and> (\<forall>e\<in>set C. af_arc_free fl (original_network.oedge e)) 
       \<and> distinct (map original_network.oedge C)
       \<and> original_network.fstv (hd C) = original_network.sndv (last C) \<and> set C \<subseteq> original_network.\<EE>"
  by (rule acyclic_flow_no_free_cycle[OF acyc])

end

end

end

end
