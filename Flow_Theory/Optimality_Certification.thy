theory Optimality_Certification
  imports Cost_Optimality Directed_Set_Graphs.Multigraph_Potentials
begin

context 
  cost_flow_network
begin



lemma optimality_from_potentials:
  assumes "f is b flow"
    "\<And> e. \<lbrakk> e \<in> \<E>; f e = 0; \<u> e \<noteq> 0\<rbrakk> \<Longrightarrow> \<c> e + \<pi> (fst e) - \<pi> (snd e) \<ge> 0"
    "\<And> e. \<lbrakk> e \<in> \<E>; f e = \<u> e; \<u> e \<noteq> 0\<rbrakk> \<Longrightarrow> \<c> e + \<pi> (fst e) - \<pi> (snd e) \<le> 0"
    "\<And> e. \<lbrakk> e \<in> \<E>; f e > 0; f e < \<u> e\<rbrakk> \<Longrightarrow> \<c> e + \<pi> (fst e) - \<pi> (snd e) = 0"
  shows "is_Opt b f"
proof(rule ccontr, goal_cases)
  case 1
  then have ex_augcycle: "\<exists> C. augcycle f C"
    using assms(1) is_opt_iff_no_augcycle by blast
  then obtain C where augC: "augcycle f C" by blast

  have CC_neg: "\<CC> C < 0"
    and augpath_C: "augpath f C"
    and cycle_C: "fstv (hd C) = sndv (last C)"
    and distinct_C: "distinct C"
    and setC_EE: "set C \<subseteq> \<EE>"
    using augC unfolding augcycle_def by auto

  have prepath_C: "prepath C" using augpath_C unfolding augpath_def by simp
  have isuflow_f: "isuflow f" using assms(1) isbflow_def by blast

  have telescope: "(\<Sum> e \<leftarrow> C. (\<pi> (fstv e) - \<pi> (sndv e))) = \<pi> (fstv (hd C)) - \<pi> (sndv (last C))"
    using prepath_C
  proof (induction rule: prepath_induct[OF prepath_C])
    case (1 e) show ?case by simp
  next
    case (2 e d es)
    then show ?case by simp
  qed

  have pi_list_zero: "(\<Sum> e \<leftarrow> C. (\<pi> (fstv e) - \<pi> (sndv e))) = 0"
    using telescope cycle_C by simp

  have pi_set_zero: "(\<Sum> e \<in> set C. (\<pi> (fstv e) - \<pi> (sndv e))) = 0"
    using distinct_C pi_list_zero
    by (simp add: sum.distinct_set_conv_list)

  have test3: "\<And> (a :: ereal) (b :: real). (0 :: ereal) < a - ereal b \<Longrightarrow> ereal b < a"
  proof -
    fix a :: ereal and b :: real
    assume h: "0 < a - ereal b"
    show "ereal b < a"
    proof (cases a)
      case (real r) then show ?thesis using h by simp
    next
      case PInf then show ?thesis by simp
    next
      case MInf then show ?thesis using h by simp
    qed
  qed

  have redcost_nonneg: "\<forall> e \<in> set C. \<cc> e + \<pi> (fstv e) - \<pi> (sndv e) \<ge> 0"
  proof
    fix e assume he: "e \<in> set C"
    have rcap_pos: "0 < \<uu>\<^bsub>f\<^esub>e"
      using augpath_rcap_pos_strict'[OF augpath_C he] by simp
    have hE: "e \<in> \<EE>" using setC_EE he by blast
    show "\<cc> e + \<pi> (fstv e) - \<pi> (sndv e) \<ge> 0"
    proof (cases e)
      case (F d)
      then have hdE: "d \<in> \<E>" using hE \<EE>_def by auto
      have hflt: "ereal (f d) < \<u> d"
        using test3[of "\<u> d" "f d"] rcap_pos F by simp
      have hfge: "0 \<le> f d" using isuflow_f isuflow_def hdE by auto
      show ?thesis
      proof (cases "f d = 0")
        case True
        then show ?thesis using assms(2) hdE F hflt 
          by(auto simp add: zero_ereal_def)
      next
        case False
        then have hfgt: "f d > 0" using hfge by simp
        have eq: "\<c> d + \<pi> (fst d) - \<pi> (snd d) = 0"
          using assms(4) hdE hfgt hflt by simp
        then show ?thesis using F by simp
      qed
    next
      case (B d)
      then have hdE: "d \<in> \<E>" using hE \<EE>_def by auto
      have hfgt: "0 < f d" using rcap_pos B by (simp add: ereal_less(2))
      have hfle: "ereal (f d) \<le> \<u> d" using isuflow_f isuflow_def hdE by auto
      show ?thesis
      proof (cases "ereal (f d) = \<u> d")
        case True
        have le: "\<c> d + \<pi> (fst d) - \<pi> (snd d) \<le> 0"
          using assms(3) hdE True hfgt by fastforce
        then show ?thesis using B by simp
      next
        case False
        then have hflt: "ereal (f d) < \<u> d" using hfle le_less by blast
        have eq: "\<c> d + \<pi> (fst d) - \<pi> (snd d) = 0"
          using assms(4) hdE hfgt hflt by simp
        then show ?thesis using B by simp
      qed
    qed
  qed

  have sum_nonneg: "(\<Sum> e \<in> set C. \<cc> e + \<pi> (fstv e) - \<pi> (sndv e)) \<ge> 0"
    by (rule sum_nonneg) (use redcost_nonneg in auto)

  have sum_split: "(\<Sum> e \<in> set C. \<cc> e + \<pi> (fstv e) - \<pi> (sndv e)) =
      (\<Sum> e \<in> set C. \<cc> e) + (\<Sum> e \<in> set C. \<pi> (fstv e) - \<pi> (sndv e))"
    by (simp only: sum.distrib sum_subtractf algebra_simps)

  have CC_nonneg: "\<CC> C \<ge> 0"
    using sum_split sum_nonneg pi_set_zero \<CC>_def by simp

  show False using CC_neg CC_nonneg by simp
qed

text \<open>Re-established here for local use: \<open>interpretation\<close> inside a locale \<open>context\<close> block is visible
      only within that same block, so \<open>Cost_Optimality.thy\<close>'s own \<open>residual_flow\<close> (declared inside
      its own reopening of this locale) does not carry over into this file's reopening, even though
      this theory imports it. Same interpretation, same proof, as \<open>Cost_Optimality.thy\<close>.\<close>

interpretation residual_flow: cost_flow_network where
  fst = fstv and snd = sndv and create_edge = create_edge_residual and
  \<E> = \<EE> and \<c> = \<cc>   and \<u> = "\<lambda> _. PInfty"
  using  make_pair create_edge  E_not_empty oedge_on_\<EE>
  by(auto simp add: finite_\<EE> make_pair[OF refl refl] create_edge cost_flow_network_def flow_network_axioms_def flow_network_def multigraph_def)

text \<open>An \<^emph>\<open>M-scaled\<close> relaxation of \<open>optimality_from_potentials\<close>, in the following sense: instead of
      requiring the reduced cost of \<^emph>\<open>every\<close> residual arc to sit in the exact three-way trichotomy
      (empty \<longrightarrow> \<ge>0, saturated \<longrightarrow> \<le>0, interior \<longrightarrow> =0), it only requires \<open>M \<sqdot> (reduced cost) \<ge> -1\<close> on every
      residual arc that is still present, for a single global integer \<open>M\<close> exceeding the vertex count.
      This is deliberately weaker and cheaper to produce --- a cost-scaling oracle's own potentials
      already satisfy it at its last phase, with no correction pass --- and it is still enough to
      certify optimality, \<^emph>\<open>provided\<close> arc costs are integers.

      \<^emph>\<open>Proof sketch, informally first.\<close> Suppose \<open>f\<close> were not optimal. By the standard negative-cycle
      characterisation, its residual graph then contains a simple augmenting cycle \<open>C\<close> of strictly
      negative cost, and being simple it has at most as many arcs as there are vertices, say \<open>k \<le> n\<close>.
      Sum the scaled inequality over the arcs of \<open>C\<close>: the potential terms telescope to zero going
      around the cycle (exactly as in \<open>optimality_from_potentials\<close>), leaving \<open>M \<sqdot> cost(C) \<ge> -k \<ge> -n\<close>.
      Separately, \<open>cost(C)\<close> is a negative integer (arc costs are integers, so the cycle's total is
      too), hence \<open>cost(C) \<le> -1\<close>, and multiplying through by the positive \<open>M\<close> gives
      \<open>M \<sqdot> cost(C) \<le> -M\<close>. Combining the two bounds forces \<open>M \<le> n\<close>, contradicting \<open>n < M\<close>. So no
      negative cycle exists, and \<open>f\<close> is optimal after all.

      \<^emph>\<open>Where this differs from \<open>optimality_from_potentials\<close>, and why each difference matters.\<close>

      \<^item> \<^emph>\<open>The criterion moves from edge-local to a genuine sum-over-a-cycle argument.\<close> In the exact
        proof, every single residual arc individually contributes a non-negative reduced cost to any
        would-be augmenting cycle, so summing over the cycle's arcs is really just summing zeros ---
        the argument never needs to know \<^emph>\<open>how many\<close> arcs the cycle has. Here an individual arc's
        slack can be as bad as \<open>-1/M\<close>, so the sum over the cycle only stays non-negative if the
        \<^emph>\<open>number of arcs\<close> is bounded. That bound is the one genuinely new piece of mathematics this
        proof needs beyond \<open>optimality_from_potentials\<close>'s own telescoping step.

      \<^item> \<^emph>\<open>The cycle has to be vertex-simple, and that is not free from \<open>augcycle\<close>'s own definition.\<close>
        \<open>augcycle\<close> only requires \<open>distinct cs\<close> --- the \<^emph>\<open>arcs\<close> are pairwise distinct --- which in a
        multigraph does \<^emph>\<open>not\<close> bound a closed walk's length by the vertex count, only by the (usually
        much larger) arc count. Getting a bound by vertex count needs a witness cycle that revisits no
        vertex, which the decomposition machinery in \<open>Decomposition.thy\<close> already builds internally
        (\<open>find_flow_cycle_in_circ\<close>'s \<open>\<forall> v. ... visited at most once\<close> conjunct) but does not expose
        through the public statement of \<open>flowcycle_decomposition\<close>, since the latter's own conclusion
        only needs to reconstruct the circulation as a weighted sum of cycles, not bound any one
        cycle's length. \<open>exists_short_neg_augcycle\<close> below re-derives the needed existence fact directly
        from \<open>find_flow_cycle_in_circ\<close>, carrying the vertex-simple property all the way through instead
        of reconstructing the full decomposition.

      \<^item> \<^emph>\<open>Costs must be integers; potentials need not be.\<close> Turning \<open>cost(C) < 0\<close> into \<open>cost(C) \<le> -1\<close> is
        a discrete fact with no continuous analogue, so it is folded in as an explicit hypothesis on
        \<open>\<c>\<close> rather than derived. The potentials \<open>\<pi>\<close> are unconstrained reals throughout, exactly as in
        \<open>optimality_from_potentials\<close> --- the telescoping step that cancels them around the cycle never
        uses integrality on their side.

      \<^item> \<^emph>\<open>Additive, not a replacement.\<close> Nothing about \<open>optimality_from_potentials\<close> changes; this is a
        new, independent theorem for a differently-shaped certificate.\<close>

lemma residual_V_eq: "residual_flow.\<V> = \<V>"
proof(intro subset_antisym subsetI)
  fix v assume "v \<in> residual_flow.\<V>"
  then obtain e where e_mem: "e \<in> \<EE>" and v_disj: "v = fstv e \<or> v = sndv e"
    unfolding dVs_def residual_flow_make_pair by fastforce
  obtain d where d: "d \<in> \<E>" "e = F d \<or> e = B d" using e_mem unfolding \<EE>_def by auto
  thus "v \<in> \<V>" using v_disj fst_E_V snd_E_V by (cases "e = F d") auto
next
  fix v assume "v \<in> \<V>"
  then obtain d where d: "d \<in> \<E>" "v = fst d \<or> v = snd d"
    unfolding dVs_def make_pair_def by fastforce
  have Fd: "F d \<in> \<EE>" using d unfolding \<EE>_def by auto
  have pair_in: "(fst d, snd d) \<in> make_pair_residual ` \<EE>"
    using Fd by (auto intro: image_eqI[of _ make_pair_residual "F d"])
  have "fst d \<in> dVs (make_pair_residual ` \<EE>)" using pair_in dVsI(1) by blast
  moreover have "snd d \<in> dVs (make_pair_residual ` \<EE>)" using pair_in dVsI(2) by blast
  ultimately show "v \<in> residual_flow.\<V>" using d unfolding residual_flow_make_pair by auto
qed

text \<open>A cycle whose every vertex has at most one participating outgoing and one incoming arc ---
      exactly \<open>find_flow_cycle_in_circ\<close>'s own guarantee --- cannot be longer than the vertex count:
      the map from arcs to their tails is injective on such a cycle, into a set of size \<open>card \<V>\<close>.\<close>

lemma vertex_simple_bound:
  assumes sub: "set es \<subseteq> \<EE>"
    and dist: "distinct es"
    and deg: "\<And>v. v \<in> residual_flow.\<V> \<Longrightarrow>
                (\<exists> eov eiv. residual_flow.delta_plus v \<inter> set es = {eov} \<and>
                             residual_flow.delta_minus v \<inter> set es = {eiv}) \<or>
                (residual_flow.delta_plus v \<inter> set es = {} \<and> residual_flow.delta_minus v \<inter> set es = {})"
  shows "length es \<le> card \<V>"
proof -
  have inj: "inj_on fstv (set es)"
  proof(rule inj_onI)
    fix e1 e2 assume e1: "e1 \<in> set es" and e2: "e2 \<in> set es" and eq: "fstv e1 = fstv e2"
    define v where "v = fstv e1"
    have e1E: "e1 \<in> \<EE>" and e2E: "e2 \<in> \<EE>" using sub e1 e2 by auto
    have vV: "v \<in> residual_flow.\<V>" using residual_flow.fst_E_V[OF e1E] v_def by simp
    have m1: "e1 \<in> residual_flow.delta_plus v \<inter> set es"
      using e1 e1E v_def by (simp add: residual_flow.delta_plus_def)
    have m2: "e2 \<in> residual_flow.delta_plus v \<inter> set es"
      using e2 e2E v_def eq by (simp add: residual_flow.delta_plus_def)
    obtain eov eiv where "residual_flow.delta_plus v \<inter> set es = {eov}"
      using deg[OF vV] m1 by blast
    thus "e1 = e2" using m1 m2 by auto
  qed
  have img: "fstv ` set es \<subseteq> \<V>" using sub residual_flow.fst_E_V residual_V_eq by auto
  have "length es = card (set es)" using dist by (simp add: distinct_card)
  also have "\<dots> = card (fstv ` set es)" using inj by (simp add: card_image)
  also have "\<dots> \<le> card \<V>" using img \<V>_finite by (simp add: card_mono)
  finally show ?thesis .
qed

text \<open>The bottleneck value on a cycle, and its three elementary properties, phrased via \<open>Min\<close> over
      the (finite, non-empty) set of arc values rather than via a fold --- the same content as the
      inline construction \<open>flowcycle_decomposition\<close> uses, pulled out because it is needed twice below.\<close>

lemma gamma_facts:
  assumes fc: "residual_flow.flowcycle g es"
  shows "es \<noteq> []"
    and "\<And>e. e \<in> set es \<Longrightarrow> Min (g ` set es) \<le> g e"
    and "\<exists>e\<in>set es. g e = Min (g ` set es)"
    and "Min (g ` set es) > 0"
proof -
  show e_ne: "es \<noteq> []" 
    using fc by(simp add: residual_flow.flowcycle_def)
  have fin: "finite (g ` set es)" by simp
  have ne: "g ` set es \<noteq> {}" using e_ne by simp
  show "\<And>e. e \<in> set es \<Longrightarrow> Min (g ` set es) \<le> g e" using fin by (simp add: Min_le)
  show "\<exists>e\<in>set es. g e = Min (g ` set es)" using Min_in[OF fin ne] by auto
  have fp: "residual_flow.flowpath g es" using fc unfolding residual_flow.flowcycle_def by simp
  have pos: "\<forall>e\<in>set es. 0 < g e" using residual_flow.flowpath_es_non_neg[OF fp] by simp
  show "Min (g ` set es) > 0" using Min_in[OF fin ne] pos by auto
qed

text \<open>A constant value \<open>\<gamma>\<close> placed on exactly the arcs of a cycle, and zero elsewhere, is itself a
      circulation --- at every active vertex the one in-arc and the one out-arc both carry \<open>\<gamma>\<close>, and
      an inactive vertex carries nothing on either side.\<close>

lemma cycle_indicator_is_circ:
  assumes fc: "residual_flow.flowcycle g es" and dist: "distinct es" and es_sub: "set es \<subseteq> \<EE>"
    and deg: "\<forall>v\<in>\<V>. (\<exists> eov eiv. residual_flow.delta_plus v \<inter> set es = {eov} \<and>
                                    residual_flow.delta_minus v \<inter> set es = {eiv}) \<or>
                       (residual_flow.delta_plus v \<inter> set es = {} \<and> residual_flow.delta_minus v \<inter> set es = {})"
  shows "residual_flow.is_circ (\<lambda>e. if e \<in> set es then \<gamma> else 0)"
  unfolding residual_flow.is_circ_def
proof
  fix v assume vV: "v \<in> residual_flow.\<V>"
  hence vV': "v \<in> \<V>" using residual_V_eq by simp
  let ?h = "\<lambda>e. if e \<in> set es then \<gamma> else (0::real)"
  show "residual_flow.ex ?h v = 0"
    unfolding residual_flow.ex_def
  proof(cases "residual_flow.delta_plus v \<inter> set es = {} \<and> residual_flow.delta_minus v \<inter> set es = {}")
    case True
    have "sum ?h (residual_flow.delta_minus v) = 0" by (rule sum.neutral) (use True in auto)
    moreover have "sum ?h (residual_flow.delta_plus v) = 0" by (rule sum.neutral) (use True in auto)
    ultimately show "sum ?h (residual_flow.delta_minus v) - sum ?h (residual_flow.delta_plus v) = 0"
      by simp
  next
    case False
    then obtain eov eiv where eov: "residual_flow.delta_plus v \<inter> set es = {eov}"
                          and eiv: "residual_flow.delta_minus v \<inter> set es = {eiv}"
      using deg[rule_format, OF vV'] by blast
    have eiv_mem: "eiv \<in> residual_flow.delta_minus v" using eiv by auto
    have split_minus: "residual_flow.delta_minus v = (residual_flow.delta_minus v - {eiv}) \<union> {eiv}"
      using eiv_mem by auto
    have "sum ?h (residual_flow.delta_minus v)
          = sum ?h (residual_flow.delta_minus v - {eiv}) + ?h eiv"
      using residual_flow.delta_minus_finite by (subst split_minus, subst sum.union_disjoint) auto
    also have "\<dots> = 0 + \<gamma>"
    proof -
      have "sum ?h (residual_flow.delta_minus v - {eiv}) = 0" by (rule sum.neutral) (use eiv in auto)
      moreover have "?h eiv = \<gamma>" using eiv by auto
      ultimately show ?thesis by simp
    qed
    finally have min_eq: "sum ?h (residual_flow.delta_minus v) = \<gamma>" by simp
    have eov_mem: "eov \<in> residual_flow.delta_plus v" using eov by auto
    have split_plus: "residual_flow.delta_plus v = (residual_flow.delta_plus v - {eov}) \<union> {eov}"
      using eov_mem by auto
    have "sum ?h (residual_flow.delta_plus v)
          = sum ?h (residual_flow.delta_plus v - {eov}) + ?h eov"
      using residual_flow.delta_plus_finite by (subst split_plus, subst sum.union_disjoint) auto
    also have "\<dots> = 0 + \<gamma>"
    proof -
      have "sum ?h (residual_flow.delta_plus v - {eov}) = 0" by (rule sum.neutral) (use eov in auto)
      moreover have "?h eov = \<gamma>" using eov by auto
      ultimately show ?thesis by simp
    qed
    finally have plus_eq: "sum ?h (residual_flow.delta_plus v) = \<gamma>" by simp
    show "sum ?h (residual_flow.delta_minus v) - sum ?h (residual_flow.delta_plus v) = 0"
      using min_eq plus_eq by simp
  qed
qed

text \<open>Circulations are closed under (pointwise) subtraction --- excess is linear in the flow.\<close>

lemma is_circ_diff:
  assumes "residual_flow.is_circ g1" "residual_flow.is_circ g2"
  shows "residual_flow.is_circ (\<lambda>e. g1 e - g2 e)"
  unfolding residual_flow.is_circ_def residual_flow.ex_def
proof
  fix v assume vV: "v \<in> residual_flow.\<V>"
  have g1z: "sum g1 (residual_flow.delta_minus v) - sum g1 (residual_flow.delta_plus v) = 0"
    using assms(1) vV unfolding residual_flow.is_circ_def residual_flow.ex_def by auto
  have g2z: "sum g2 (residual_flow.delta_minus v) - sum g2 (residual_flow.delta_plus v) = 0"
    using assms(2) vV unfolding residual_flow.is_circ_def residual_flow.ex_def by auto
  have s1: "sum (\<lambda>e. g1 e - g2 e) (residual_flow.delta_minus v)
            = sum g1 (residual_flow.delta_minus v) - sum g2 (residual_flow.delta_minus v)"
    using residual_flow.delta_minus_finite by (simp add: sum_subtractf)
  have s2: "sum (\<lambda>e. g1 e - g2 e) (residual_flow.delta_plus v)
            = sum g1 (residual_flow.delta_plus v) - sum g2 (residual_flow.delta_plus v)"
    using residual_flow.delta_plus_finite by (simp add: sum_subtractf)
  show "sum (\<lambda>e. g1 e - g2 e) (residual_flow.delta_minus v)
        - sum (\<lambda>e. g1 e - g2 e) (residual_flow.delta_plus v) = 0"
    using g1z g2z s1 s2 by simp
qed

text \<open>The existence fact this whole development is built around: a non-negative, non-zero,
      negative-cost circulation contains a \<^emph>\<open>vertex-simple\<close> negative-cost cycle --- not merely \<^emph>\<open>some\<close>
      negative cycle, which \<open>flowcycle_decomposition\<close> already gives via \<open>no_augcycle_min_cost_flow\<close>,
      but one of length at most \<open>card \<V>\<close>. The proof repeats \<open>flowcycle_decomposition\<close>'s own
      peel-one-cycle-and-recurse strategy (via \<open>find_flow_cycle_in_circ\<close>, strong induction on the
      shrinking support), but stops the first time the peeled cycle itself has negative cost, rather
      than reconstructing the full weighted decomposition --- since a telescoping-cost argument shows
      the remaining circulation's cost only gets \<^emph>\<open>more\<close> negative while every peeled cycle is
      non-negative, this must happen before the support empties out.\<close>

lemma exists_short_neg_augcycle:
  assumes "n = card (residual_flow.support g)"
    and "residual_flow.flow_non_neg g" and "residual_flow.is_circ g" and "residual_flow.\<C> g < 0"
  shows "\<exists> es. residual_flow.flowcycle g es \<and> set es \<subseteq> residual_flow.support g \<and> distinct es \<and>
               length es \<le> card \<V> \<and> (\<Sum> e \<in> set es. \<cc> e) < 0"
  using assms
proof(induction n arbitrary: g rule: less_induct)
  case (less n)
  have supp_sub: "residual_flow.support g \<subseteq> \<EE>" unfolding residual_flow.support_def by auto
  have fin_supp: "finite (residual_flow.support g)" using supp_sub finite_\<EE> finite_subset by blast
  have supp_ne: "residual_flow.support g \<noteq> {}"
  proof
    assume supp0: "residual_flow.support g = {}"
    have "\<And>e. e \<in> \<EE> \<Longrightarrow> g e = 0"
    proof -
      fix e assume eE: "e \<in> \<EE>"
      have "\<not> (0 < g e)" using supp0 eE unfolding residual_flow.support_def by auto
      moreover have "0 \<le> g e" using less.prems(2) eE unfolding residual_flow.flow_non_neg_def by auto
      ultimately show "g e = 0" by simp
    qed
    hence "residual_flow.\<C> g = 0" unfolding residual_flow.\<C>_def by simp
    thus False using less.prems(4) by simp
  qed
  have abs_pos: "residual_flow.Abs g > 0"
    unfolding residual_flow.Abs_def
  proof -
    from supp_ne obtain e0 where e0: "e0 \<in> residual_flow.support g" by auto
    have e0E: "e0 \<in> \<EE>" using e0 supp_sub by auto
    have e0pos: "0 < g e0" using e0 unfolding residual_flow.support_def by auto
    have allpos: "\<And>i. i \<in> \<EE> \<Longrightarrow> 0 \<le> g i"
      using less.prems(2) unfolding residual_flow.flow_non_neg_def by auto
    show "0 < sum g \<EE>"
      by (intro sum_pos2[of \<EE> e0]) (auto simp add: finite_\<EE> e0E e0pos allpos)
  qed
  obtain es where es_Def: "residual_flow.flowcycle g es" "set es \<subseteq> residual_flow.support g"
                          "distinct es"
                          "\<forall>v\<in>residual_flow.\<V>.
                            (\<exists> eov eiv. residual_flow.delta_plus v \<inter> set es = {eov} \<and>
                                        residual_flow.delta_minus v \<inter> set es = {eiv}) \<or>
                            (residual_flow.delta_plus v \<inter> set es = {} \<and> residual_flow.delta_minus v \<inter> set es = {})"
    using residual_flow.find_flow_cycle_in_circ[OF less.prems(2) abs_pos less.prems(3)]
    by blast
  have es_sub_EE: "set es \<subseteq> \<EE>" using es_Def(2) supp_sub by auto
  have deg_rf: "\<And>v. v \<in> residual_flow.\<V> \<Longrightarrow>
                  (\<exists> eov eiv. residual_flow.delta_plus v \<inter> set es = {eov} \<and>
                              residual_flow.delta_minus v \<inter> set es = {eiv}) \<or>
                  (residual_flow.delta_plus v \<inter> set es = {} \<and> residual_flow.delta_minus v \<inter> set es = {})"
    using es_Def(4) by blast
  have deg': "\<forall>v\<in>\<V>. (\<exists> eov eiv. residual_flow.delta_plus v \<inter> set es = {eov} \<and>
                                    residual_flow.delta_minus v \<inter> set es = {eiv}) \<or>
                       (residual_flow.delta_plus v \<inter> set es = {} \<and> residual_flow.delta_minus v \<inter> set es = {})"
    using es_Def(4) residual_V_eq by simp
  have len_bound: "length es \<le> card \<V>" using vertex_simple_bound[OF es_sub_EE es_Def(3) deg_rf] by simp
  define \<gamma> where "\<gamma> = Min (g ` set es)"
  have gfacts2: "\<And>e. e \<in> set es \<Longrightarrow> \<gamma> \<le> g e" "\<exists>e\<in>set es. g e = \<gamma>" "\<gamma> > 0"
    using gamma_facts[OF es_Def(1)] unfolding \<gamma>_def by auto
  define g' where "g' = (\<lambda>e. if e \<in> set es then g e - \<gamma> else g e)"
  define h where "h = (\<lambda>e. if e \<in> set es then \<gamma> else (0::real))"
  have g'_eq: "\<And>e. g' e = g e - h e" unfolding g'_def h_def by simp
  have h_circ: "residual_flow.is_circ h"
    using cycle_indicator_is_circ[OF es_Def(1) es_Def(3) es_sub_EE deg'] unfolding h_def \<gamma>_def by simp
  have g'_circ: "residual_flow.is_circ g'"
    using is_circ_diff[OF less.prems(3) h_circ] g'_eq by presburger
  have g'_nonneg: "residual_flow.flow_non_neg g'"
    unfolding residual_flow.flow_non_neg_def
  proof
    fix e assume eE: "e \<in> \<EE>"
    show "0 \<le> g' e"
    proof(cases "e \<in> set es")
      case True thus ?thesis using gfacts2(1)[OF True] unfolding g'_def by simp
    next
      case False thus ?thesis using less.prems(2) eE unfolding g'_def residual_flow.flow_non_neg_def by simp
    qed
  qed
  have g'_le_g: "\<And>e. g' e \<le> g e" unfolding g'_def using gfacts2(3) by simp
  have cost_split: "residual_flow.\<C> g = residual_flow.\<C> g' + \<gamma> * (\<Sum> e \<in> set es. \<cc> e)"
  proof -
    have "residual_flow.\<C> g = (\<Sum> e \<in> \<EE>. g e * \<cc> e)" unfolding residual_flow.\<C>_def by simp
    also have "\<dots> = (\<Sum> e \<in> \<EE>. (g' e + h e) * \<cc> e)" using g'_eq by simp
    also have "\<dots> = (\<Sum> e \<in> \<EE>. g' e * \<cc> e) + (\<Sum> e \<in> \<EE>. h e * \<cc> e)"
      by (simp add: algebra_simps sum.distrib)
    also have "\<dots> = residual_flow.\<C> g' + (\<Sum> e \<in> \<EE>. h e * \<cc> e)" unfolding residual_flow.\<C>_def by simp
    also have "(\<Sum> e \<in> \<EE>. h e * \<cc> e) = (\<Sum> e \<in> set es. h e * \<cc> e)"
      using es_sub_EE unfolding h_def by (intro sum.mono_neutral_right) (auto simp add: finite_\<EE>)
    also have "\<dots> = \<gamma> * (\<Sum> e \<in> set es. \<cc> e)" unfolding h_def by (simp add: sum_distrib_left)
    finally show ?thesis by simp
  qed
  show ?case
  proof(cases "(\<Sum> e \<in> set es. \<cc> e) < 0")
    case True
    thus ?thesis using es_Def(1,2,3) len_bound by auto
  next
    case False
    hence nonneg_sum: "(\<Sum> e \<in> set es. \<cc> e) \<ge> 0" by simp
    have gs_nonneg: "\<gamma> * (\<Sum> e \<in> set es. \<cc> e) \<ge> 0" using gfacts2(3) nonneg_sum by simp
    have g'_neg: "residual_flow.\<C> g' < 0" using cost_split less.prems(4) gs_nonneg by linarith
    obtain e_wit where e_wit: "e_wit \<in> set es" "g e_wit = \<gamma>" using gfacts2(2) by auto
    have e_wit_in_supp: "e_wit \<in> residual_flow.support g"
      using e_wit gfacts2(3) es_sub_EE unfolding residual_flow.support_def by auto
    have e_wit_notin_supp': "e_wit \<notin> residual_flow.support g'"
      unfolding residual_flow.support_def g'_def using e_wit by simp
    have supp_g'_sub: "residual_flow.support g' \<subseteq> residual_flow.support g"
      using g'_le_g unfolding residual_flow.support_def by (smt (verit) Collect_mono_iff)
    have supp_strict: "residual_flow.support g' \<subset> residual_flow.support g"
      using supp_g'_sub e_wit_in_supp e_wit_notin_supp' by auto
    have card_lt: "card (residual_flow.support g') < n"
      using psubset_card_mono[OF fin_supp supp_strict] less.prems(1) by simp
    obtain es' where es'_Def: "residual_flow.flowcycle g' es'" "set es' \<subseteq> residual_flow.support g'"
                     "distinct es'" "length es' \<le> card \<V>" "(\<Sum> e \<in> set es'. \<cc> e) < 0"
      using less.IH[OF card_lt refl g'_nonneg g'_circ g'_neg] by blast
    have lift: "residual_flow.flowcycle g es'"
      using residual_flow.flow_cyc_mono[OF es'_Def(1)] g'_le_g by blast
    have supp_lift: "set es' \<subseteq> residual_flow.support g" using es'_Def(2) supp_g'_sub by blast
    show ?thesis using lift supp_lift es'_Def(3,4,5) by blast
  qed
qed

text \<open>Repackaged in the vocabulary the main theorem needs: a non-optimal \<open>b\<close>-flow has a genuine
      \<open>augcycle\<close> --- so the checks already proved sound for \<open>optimality_from_potentials\<close> apply to it
      unchanged --- of length at most the vertex count. This mirrors \<open>no_augcycle_min_cost_flow\<close>'s own
      opening (the difference of \<open>f\<close> and a strictly cheaper flow \<open>f'\<close> is a residual circulation of
      negative cost), but finishes with \<open>exists_short_neg_augcycle\<close> in place of the full
      \<open>flowcycle_decomposition\<close>, since only one bounded witness cycle is needed here, not a
      reconstruction of the whole circulation.\<close>

lemma short_augcycle_from_not_opt:
  assumes bflow: "f is b flow" and not_opt: "\<not> is_Opt b f"
  shows "\<exists>es. augcycle f es \<and> length es \<le> card \<V>"
proof -
  obtain f' where f'_Def: "\<C> f' < \<C> f \<and> f' is b flow"
    using bflow not_opt unfolding is_Opt_def by force
  hence f_f'_diff_neg: "\<C> f' - \<C> f < 0" by simp
  define g where "g = difference f' f"
  have R_cost_g: "residual_flow.\<C> g = \<C> f' - \<C> f" by (simp add: g_def rcost_difference)
  have isuflow_f: "isuflow f" using bflow isbflow_def by blast
  have isuflow_f': "isuflow f'" using f'_Def isbflow_def by blast
  have g_nonneg: "residual_flow.flow_non_neg g"
    using difference_flow_pos[OF isuflow_f isuflow_f'] g_def by simp
  have g_circ: "residual_flow.is_circ g" using diff_is_res_circ[OF bflow] f'_Def g_def by simp
  have g_neg: "residual_flow.\<C> g < 0" using R_cost_g f_f'_diff_neg by simp
  obtain es where es_Def: "residual_flow.flowcycle g es" "set es \<subseteq> residual_flow.support g"
                          "distinct es" "length es \<le> card \<V>" "(\<Sum> e \<in> set es. \<cc> e) < 0"
    using exists_short_neg_augcycle[OF refl g_nonneg g_circ g_neg] by blast
  have es_ne: "es \<noteq> []" using es_Def(1) unfolding residual_flow.flowcycle_def by simp
  have supp_sub_EE: "residual_flow.support g \<subseteq> \<EE>" unfolding residual_flow.support_def by auto
  have es_sub_EE: "set es \<subseteq> \<EE>" using es_Def(2) supp_sub_EE by auto
  have inf: "e \<in> residual_flow.support g \<Longrightarrow> rcap f e > 0" for e
    using difference_less_rcap[of f f' e] bflow f'_Def g_def isbflow_def pos_difference_pos_rcap
    by (force simp add: residual_flow.support_def)
  hence rcap_pos: "\<forall> e \<in> set es. rcap f e > 0" using es_Def(2) by blast
  have flowpath_es: "residual_flow.flowpath g es" using es_Def(1) unfolding residual_flow.flowcycle_def by simp
  have augpath_f: "augpath f es"
    using flowpath_es rcap_pos es_ne ext[of to_vertex_pair make_pair_residual]
          Min_gr_iff[of "rcap f ` (set es)"]
    by (auto simp add: augpath_def prepath_def residual_flow.flowpath_def
                        to_vertex_pair_fst_snd residual_flow.multigraph_path_def Rcap_def)
  have cyc_close: "fstv (hd es) = sndv (last es)"
    using es_Def(1) unfolding residual_flow.flowcycle_def by simp
  have CC_neg: "\<CC> es < 0" unfolding \<CC>_def using es_Def(3,5) by (simp add: sum.distinct_set_conv_list)
  have "augcycle f es"
    using CC_neg augpath_f cyc_close es_Def(3) es_sub_EE by (auto simp add: augcycle_def)
  thus ?thesis using es_Def(4) by blast
qed

(* --- 2026-08-13 session, first attempt at the eps-optimality chain, superseded below ---

text \<open>\<^emph>\<open>The general, real-valued criterion.\<close> A primal-dual pair \<open>(f, \<pi>)\<close> satisfies \<open>\<epsilon>\<close>-complementary
      slackness if no residual arc's reduced cost falls more than \<open>\<epsilon>\<close> below zero --- the standard
      relaxation of exact complementary slackness (\<open>optimality_from_potentials\<close> above is the \<open>\<epsilon> = 0\<close>
      case, checked pointwise rather than via this predicate). \<open>\<epsilon>\<close> and \<open>\<pi>\<close> are genuine reals here, not
      tied to any scaling factor or numeric type --- the M-scaled criterion below is one instance of
      this, not the general case. This is a \<^emph>\<open>dual/residual-graph\<close> notion: it says nothing directly
      about how close \<open>f\<close>'s cost is to the optimum --- \<open>eps_cost_optimal\<close> further below is the
      \<^emph>\<open>primal cost-distance\<close> notion, and \<open>eps_complementary_slack_imp_eps_cost_optimal\<close> is the bridge
      from this to that.\<close>

definition eps_complementary_slack :: "real \<Rightarrow> ('edge \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> bool" where
  "eps_complementary_slack \<epsilon> f \<pi> \<longleftrightarrow>
     (\<forall> e \<in> \<EE>. \<uu>\<^bsub>f\<^esub>e > 0 \<longrightarrow> \<cc> e + \<pi> (fstv e) - \<pi> (sndv e) \<ge> - \<epsilon>)"

text \<open>\<^emph>\<open>\<epsilon>-optimality certifies optimality once \<epsilon> is small enough, given integer costs.\<close> The proof is
      exactly \<open>optimality_from_potentials\<close>'s: assume not, obtain a short augmenting cycle from
      \<open>short_augcycle_from_not_opt\<close>, and telescope the criterion over it. What used to be a
      multiplication by an integer \<open>M\<close> is now a plain real bound \<open>n\<epsilon> < 1\<close>, and every step after the
      telescoping runs in reals throughout --- no \<open>of_nat\<close>, no bridging between a numeric type and
      \<open>real\<close>, since there was never anything but \<open>real\<close> here to begin with. Integrality is still
      essential and still enters exactly once, turning the cycle's negative real total cost into
      \<open>\<le> -1\<close>; nothing in this proof removes that, only the parameterisation changes.\<close>

theorem optimality_from_eps_potentials:
  fixes \<epsilon> :: real
  assumes bflow: "f is b flow"
    and eps_pos: "0 < \<epsilon>"
    and n_bound: "real (card \<V>) * \<epsilon> < 1"
    and cost_int: "\<And>e. e \<in> \<EE> \<Longrightarrow> \<cc> e \<in> \<int>"
    and eps_opt: "eps_complementary_slack \<epsilon> f \<pi>"
  shows "is_Opt b f"
proof(rule ccontr)
  assume not_opt: "\<not> is_Opt b f"
  obtain es where augC: "augcycle f es" and len_bound: "length es \<le> card \<V>"
    using short_augcycle_from_not_opt[OF bflow not_opt] by blast
  have CC_neg: "\<CC> es < 0" and augpath_C: "augpath f es"
    and cycle_C: "fstv (hd es) = sndv (last es)" and distinct_C: "distinct es"
    and setC_EE: "set es \<subseteq> \<EE>"
    using augC unfolding augcycle_def by auto
  have prepath_C: "prepath es" using augpath_C unfolding augpath_def by simp
  have telescope: "(\<Sum> e \<leftarrow> es. (\<pi> (fstv e) - \<pi> (sndv e))) = \<pi> (fstv (hd es)) - \<pi> (sndv (last es))"
    using prepath_C
  proof (induction rule: prepath_induct[OF prepath_C])
    case (1 e) show ?case by simp
  next
    case (2 e d es) then show ?case by simp
  qed
  have pi_list_zero: "(\<Sum> e \<leftarrow> es. (\<pi> (fstv e) - \<pi> (sndv e))) = 0" using telescope cycle_C by simp
  have pi_set_zero: "(\<Sum> e \<in> set es. (\<pi> (fstv e) - \<pi> (sndv e))) = 0"
    using distinct_C pi_list_zero by (simp add: sum.distinct_set_conv_list)
  have eps_edge: "\<And>e. e \<in> set es \<Longrightarrow> \<cc> e + \<pi> (fstv e) - \<pi> (sndv e) \<ge> - \<epsilon>"
  proof -
    fix e assume he: "e \<in> set es"
    have hE: "e \<in> \<EE>" using setC_EE he by blast
    have "0 < \<uu>\<^bsub>f\<^esub>e" using augpath_rcap_pos_strict'[OF augpath_C he] by simp
    thus "\<cc> e + \<pi> (fstv e) - \<pi> (sndv e) \<ge> - \<epsilon>"
      using eps_opt hE unfolding eps_complementary_slack_def by simp
  qed
  have sum_ge: "(\<Sum> e \<in> set es. \<cc> e + \<pi> (fstv e) - \<pi> (sndv e)) \<ge> (\<Sum> e \<in> set es. (- \<epsilon>))"
    by (rule sum_mono) (use eps_edge in blast)
  have card_len: "(\<Sum> e \<in> set es. (- \<epsilon>)) = - \<epsilon> * real (length es)"
    using distinct_C by (simp add: distinct_card)
  have sum_split: "(\<Sum> e \<in> set es. \<cc> e + \<pi> (fstv e) - \<pi> (sndv e))
      = (\<Sum> e \<in> set es. \<cc> e) + (\<Sum> e \<in> set es. (\<pi> (fstv e) - \<pi> (sndv e)))"
    by (simp add: sum.distrib sum_subtractf algebra_simps)
  have key: "\<CC> es \<ge> - \<epsilon> * real (length es)"
    unfolding \<CC>_def using sum_ge card_len sum_split pi_set_zero by linarith
  have ge_card: "- \<epsilon> * real (length es) \<ge> - \<epsilon> * real (card \<V>)"
    using len_bound eps_pos by (simp add: mult_left_mono)
  have lb: "\<CC> es \<ge> - \<epsilon> * real (card \<V>)" using key ge_card by linarith
  have cc_int: "\<CC> es \<in> \<int>" unfolding \<CC>_def using cost_int setC_EE by (intro Ints_sum) blast
  obtain k where k_def: "\<CC> es = of_int k" using cc_int Ints_cases by blast
  have k_neg: "k < 0" using CC_neg k_def by simp
  hence k_le: "k \<le> -1" by simp
  have cc_le: "\<CC> es \<le> -1" using k_def k_le by (simp add: of_int_le_iff[symmetric])
  have "- \<epsilon> * real (card \<V>) \<le> -1" using lb cc_le by linarith
  hence "1 \<le> \<epsilon> * real (card \<V>)" by simp
  thus False using n_bound by (simp add: mult.commute)
qed

text \<open>\<^emph>\<open>Kept as it stood.\<close> The \<open>M\<close>-scaled criterion of the certificate checker is the \<open>\<epsilon> = 1/M\<close>
      instance of the theorem above, with \<open>\<pi>\<close> rescaled the same way --- multiplying
      \<open>M \<cdot> \<cc> e + \<pi>(u) - \<pi>(v) \<ge> -1\<close> through by \<open>1/M\<close> gives exactly \<open>eps_cost_optimal (1/M) f (\<lambda>v. \<pi> v /
      M)\<close>, and \<open>card \<V> < M\<close> becomes exactly \<open>n\<epsilon> < 1\<close> the same way. Name and statement are unchanged
      from before, so nothing downstream --- \<open>check_optimum_eps_sound\<close> in particular --- needs to
      change; only the proof is now three lines instead of the argument this file used to carry
      twice.\<close>

corollary optimality_from_scaled_potentials:
  fixes M :: nat
  assumes bflow: "f is b flow"
    and M_gt: "card \<V> < M"
    and cost_int: "\<And>e. e \<in> \<EE> \<Longrightarrow> \<cc> e \<in> \<int>"
    and scaled_opt: "\<And>e. e \<in> \<EE> \<Longrightarrow> \<uu>\<^bsub>f\<^esub>e > 0 \<Longrightarrow>
                      real M * \<cc> e + \<pi> (fstv e) - \<pi> (sndv e) \<ge> -1"
  shows "is_Opt b f"
proof -
  have Mpos: "(0::real) < real M" using M_gt by simp
  have eps_pos: "0 < 1 / real M" using Mpos by simp
  have n_bound: "real (card \<V>) * (1 / real M) < 1"
    using M_gt Mpos by (simp add: field_simps)
  have eps_opt: "eps_complementary_slack (1 / real M) f (\<lambda>v. \<pi> v / real M)"
    unfolding eps_complementary_slack_def
  proof
    fix e assume he: "e \<in> \<EE>"
    show "\<uu>\<^bsub>f\<^esub>e > 0 \<longrightarrow> \<cc> e + \<pi> (fstv e) / real M - \<pi> (sndv e) / real M \<ge> - (1 / real M)"
    proof
      assume "\<uu>\<^bsub>f\<^esub>e > 0"
      hence ineq: "real M * \<cc> e + \<pi> (fstv e) - \<pi> (sndv e) \<ge> -1" using scaled_opt[OF he] by simp
      have step1: "(-1::real) / real M \<le> (real M * \<cc> e + \<pi> (fstv e) - \<pi> (sndv e)) / real M"
        by (rule divide_right_mono[OF ineq]) (use Mpos in simp)
      have split: "(real M * \<cc> e + \<pi> (fstv e) - \<pi> (sndv e)) / real M
                   = \<cc> e + \<pi> (fstv e) / real M - \<pi> (sndv e) / real M"
        using Mpos by (simp add: add_divide_distrib diff_divide_distrib)
      show "\<cc> e + \<pi> (fstv e) / real M - \<pi> (sndv e) / real M \<ge> - (1 / real M)"
        using step1 split by simp
    qed
  qed
  show ?thesis
    by (rule optimality_from_eps_potentials[OF bflow eps_pos n_bound cost_int eps_opt])
qed

--- end of superseded attempt --- *)

text \<open>\<^emph>\<open>The eps-optimality chain, take three.\<close> Two \<^emph>\<open>parallel\<close> consequences of the same \<open>\<epsilon>\<close>-complementary
      slackness certificate --- not a chain where one feeds the other. The literature backs this shape
      directly: the classical result (Tardos 1985; Bertsekas 1986; Goldberg--Tarjan 1989/1990) is that
      for integral costs, \<open>1/(n+1)\<close>-complementary slackness already forces \<^emph>\<open>exact\<close> optimality, proved
      straight from the certificate via the negative-cycle-cost bound --- no flow integrality anywhere.
      The aggregate \<open>\<delta>\<close>-additive/relative approximation guarantee (Goldberg--Tarjan's own
      successive-approximation framework) is a separate, weaker kind of statement. There is no route in
      the literature --- and, as the counterexample discussed above shows (an idle edge's reduced cost
      is otherwise unbounded above), no route here either --- from the \<^emph>\<open>aggregate\<close> cost-distance number
      back to exactness without assuming the flow itself is integral. So exactness is kept on its own
      direct path from the certificate, exactly as \<open>optimality_from_eps_potentials\<close> already established
      earlier in this file, and is \<^emph>\<open>not\<close> re-derived from \<open>eps_cost_optimal\<close>.

      \<^item> \<^emph>\<open>Theorem 1\<close> (below): the certificate --- stated inline, no named wrapper, since it is used in
        exactly one place here --- guarantees \<open>f\<close> is relatively \<open>\<delta>\<close>-cost-optimal for \<open>\<delta> = \<epsilon>\<close> times the
        network's total finite capacity, \<^emph>\<open>with no integrality assumption at all\<close>.

      \<^item> \<^emph>\<open>Theorem "old"\<close> (restored below, unchanged from earlier in this file): the \<^emph>\<open>same\<close> certificate,
        together with \<^emph>\<open>only\<close> cost integrality and \<open>n\<sqdot>\<epsilon> < 1\<close>, forces \<open>f\<close> to be \<^emph>\<open>exactly\<close> optimal. This
        is \<open>optimality_from_eps_potentials\<close> plus its \<open>M\<close>-scaled corollary \<open>optimality_from_scaled_
        potentials\<close> --- both restored here with their original (already verified) proofs, dual condition
        inlined to match Theorem 1's style instead of going through a named wrapper. Downstream
        (\<open>check_optimum_eps_sound\<close>) keeps working unchanged, since the name and statement of
        \<open>optimality_from_scaled_potentials\<close> are exactly as before.\<close>

definition eps_cost_optimal :: "real \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('edge \<Rightarrow> real) \<Rightarrow> bool" where
  "eps_cost_optimal \<delta> b f \<longleftrightarrow>
     (\<exists> fstar. is_Opt b fstar \<and> \<bar>\<C> f - \<C> fstar\<bar> / (1 + \<bar>\<C> fstar\<bar>) \<le> \<delta>)"

theorem eps_dual_slack_imp_eps_cost_optimal:
  fixes \<epsilon> :: real
  assumes bflow: "f is b flow"
    and eps_nonneg: "0 \<le> \<epsilon>"
    and fin_cap: "\<forall> e \<in> \<E>. \<u> e \<noteq> \<infinity>"
    and slack: "\<forall> e \<in> \<EE>. \<uu>\<^bsub>f\<^esub>e > 0 \<longrightarrow> \<cc> e + \<pi> (fstv e) - \<pi> (sndv e) \<ge> - \<epsilon>"
    and opt: "is_Opt b fstar"
  shows "eps_cost_optimal (\<epsilon> * (\<Sum> e \<in> \<E>. real_of_ereal (\<u> e))) b f"
  unfolding eps_cost_optimal_def
proof (intro exI conjI)
  show "is_Opt b fstar" by (rule opt)
  have hfstar_flow: "fstar is b flow" using opt is_Opt_def by blast
  have hf_ge_fstar: "\<C> fstar \<le> \<C> f" using opt is_Opt_def bflow by blast
  have Ucap_nonneg: "0 \<le> (\<Sum> e \<in> \<E>. real_of_ereal (\<u> e))"
  proof (rule sum_nonneg)
    fix e assume "e \<in> \<E>"
    then show "0 \<le> real_of_ereal (\<u> e)" using u_non_neg[of e] by (cases "\<u> e") auto
  qed
  have hb_gen: "\<And>g e. g is b flow \<Longrightarrow> e \<in> \<E> \<Longrightarrow> 0 \<le> g e \<and> g e \<le> real_of_ereal (\<u> e)"
  proof -
    fix g e assume hg: "g is b flow" and he: "e \<in> \<E>"
    have hisuflow: "isuflow g" using hg isbflow_def by blast
    have hge: "0 \<le> g e" using hisuflow isuflow_def he by blast
    have hle_ereal: "ereal (g e) \<le> \<u> e" using hisuflow isuflow_def he by blast
    obtain r where hr: "\<u> e = ereal r" using hle_ereal fin_cap he by (cases "\<u> e") auto
    have hle: "g e \<le> real_of_ereal (\<u> e)" using hle_ereal hr by (auto simp: real_le_ereal_iff)
    show "0 \<le> g e \<and> g e \<le> real_of_ereal (\<u> e)" using hge hle by blast
  qed
  have hb_gen_fstar: "\<And>e. e \<in> \<E> \<Longrightarrow> 0 \<le> fstar e \<and> fstar e \<le> real_of_ereal (\<u> e)"
    using hb_gen[of fstar] hfstar_flow by blast
  have hb_gen_f: "\<And>e. e \<in> \<E> \<Longrightarrow> 0 \<le> f e \<and> f e \<le> real_of_ereal (\<u> e)"
    using hb_gen[of f] bflow by blast
  have telescope_gen: "\<And>g. g is b flow \<Longrightarrow>
      \<C> g = (\<Sum> e \<in> \<E>. (\<c> e + \<pi> (fst e) - \<pi> (snd e)) * g e) - (\<Sum> v \<in> \<V>. \<pi> v * b v)"
  proof -
    fix g assume hg: "g is b flow"
    have hisuflow: "isuflow g" using hg isbflow_def by blast
    have hbv: "\<forall> v \<in> \<V>. b v = sum g (delta_plus v) - sum g (delta_minus v)"
    proof
      fix v assume hv: "v \<in> \<V>"
      have "- ex g v = b v" using hg isbflow_def hv by blast
      then show "b v = sum g (delta_plus v) - sum g (delta_minus v)"
        by (simp add: ex_def delta_plus_def delta_minus_def)
    qed
    have union_plus: "(Union (delta_plus ` \<V>)) = \<E>" by (auto simp add: delta_plus_def fst_E_V)
    have union_minus: "(Union (delta_minus ` \<V>)) = \<E>" by (auto simp add: delta_minus_def snd_E_V)
    have disj_plus: "\<forall> v1 \<in> \<V>. \<forall> v2 \<in> \<V>. v1 \<noteq> v2 \<longrightarrow> delta_plus v1 \<inter> delta_plus v2 = {}"
      by (auto simp add: delta_plus_def)
    have disj_minus: "\<forall> v1 \<in> \<V>. \<forall> v2 \<in> \<V>. v1 \<noteq> v2 \<longrightarrow> delta_minus v1 \<inter> delta_minus v2 = {}"
      by (auto simp add: delta_minus_def)
    have regroup_fst: "sum (\<lambda> e. \<pi> (fst e) * g e) \<E> = (\<Sum> v \<in> \<V>. \<pi> v * sum g (delta_plus v))"
    proof -
      have h1: "sum (\<lambda> e. \<pi> (fst e) * g e) (Union (delta_plus ` \<V>))
                = (\<Sum> v \<in> \<V>. \<Sum> e \<in> delta_plus v. \<pi> (fst e) * g e)"
        by (rule sum.UNION_disjoint) (use \<V>_finite delta_plus_finite disj_plus in auto)
      have h2: "(\<Sum> v \<in> \<V>. \<Sum> e \<in> delta_plus v. \<pi> (fst e) * g e) = (\<Sum> v \<in> \<V>. \<pi> v * sum g (delta_plus v))"
        by (rule sum.cong, rule refl) (auto simp add: delta_plus_def sum_distrib_left)
      show ?thesis using h1 h2 by (simp add: union_plus)
    qed
    have regroup_snd: "sum (\<lambda> e. \<pi> (snd e) * g e) \<E> = (\<Sum> v \<in> \<V>. \<pi> v * sum g (delta_minus v))"
    proof -
      have h1: "sum (\<lambda> e. \<pi> (snd e) * g e) (Union (delta_minus ` \<V>))
                = (\<Sum> v \<in> \<V>. \<Sum> e \<in> delta_minus v. \<pi> (snd e) * g e)"
        by (rule sum.UNION_disjoint) (use \<V>_finite delta_minus_finite disj_minus in auto)
      have h2: "(\<Sum> v \<in> \<V>. \<Sum> e \<in> delta_minus v. \<pi> (snd e) * g e) = (\<Sum> v \<in> \<V>. \<pi> v * sum g (delta_minus v))"
        by (rule sum.cong, rule refl) (auto simp add: delta_minus_def sum_distrib_left)
      show ?thesis using h1 h2 by (simp add: union_minus)
    qed
    have pivot: "(\<Sum> e \<in> \<E>. (\<pi> (fst e) - \<pi> (snd e)) * g e) = (\<Sum> v \<in> \<V>. \<pi> v * b v)"
    proof -
      have "(\<Sum> e \<in> \<E>. (\<pi> (fst e) - \<pi> (snd e)) * g e)
            = (\<Sum> e \<in> \<E>. \<pi> (fst e) * g e) - (\<Sum> e \<in> \<E>. \<pi> (snd e) * g e)"
        by (simp add: ring_distribs sum_subtractf)
      also have "... = (\<Sum> v \<in> \<V>. \<pi> v * sum g (delta_plus v)) - (\<Sum> v \<in> \<V>. \<pi> v * sum g (delta_minus v))"
        by (simp add: regroup_fst regroup_snd)
      also have "... = (\<Sum> v \<in> \<V>. \<pi> v * (sum g (delta_plus v) - sum g (delta_minus v)))"
        by (simp add: sum_subtractf ring_distribs)
      also have "... = (\<Sum> v \<in> \<V>. \<pi> v * b v)" by (rule sum.cong, rule refl) (use hbv in auto)
      finally show ?thesis .
    qed
    show "\<C> g = (\<Sum> e \<in> \<E>. (\<c> e + \<pi> (fst e) - \<pi> (snd e)) * g e) - (\<Sum> v \<in> \<V>. \<pi> v * b v)"
    proof -
      have "(\<Sum> e \<in> \<E>. (\<c> e + \<pi> (fst e) - \<pi> (snd e)) * g e)
            = (\<Sum> e \<in> \<E>. \<c> e * g e) + (\<Sum> e \<in> \<E>. (\<pi> (fst e) - \<pi> (snd e)) * g e)"
        by (simp add: ring_distribs sum.distrib sum_subtractf)
      also have "... = \<C> g + (\<Sum> v \<in> \<V>. \<pi> v * b v)" using pivot by (simp add: \<C>_def mult.commute)
      finally show ?thesis by linarith
    qed
  qed
  define L where "L = (\<Sum> e \<in> \<E>. min 0 (\<c> e + \<pi> (fst e) - \<pi> (snd e)) * real_of_ereal (\<u> e))
                       - (\<Sum> v \<in> \<V>. \<pi> v * b v)"
  have hL_le_fstar: "L \<le> \<C> fstar"
  proof -
    have telescope_fstar: "\<C> fstar = (\<Sum> e \<in> \<E>. (\<c> e + \<pi> (fst e) - \<pi> (snd e)) * fstar e) - (\<Sum> v \<in> \<V>. \<pi> v * b v)"
      using telescope_gen[OF hfstar_flow] .
    have edge_lb: "\<And>e. e \<in> \<E> \<Longrightarrow>
        min 0 (\<c> e + \<pi> (fst e) - \<pi> (snd e)) * real_of_ereal (\<u> e) \<le> (\<c> e + \<pi> (fst e) - \<pi> (snd e)) * fstar e"
    proof -
      fix e assume he: "e \<in> \<E>"
      have hb: "0 \<le> fstar e \<and> fstar e \<le> real_of_ereal (\<u> e)" using hb_gen_fstar he by blast
      let ?c = "\<c> e + \<pi> (fst e) - \<pi> (snd e)"
      show "min 0 ?c * real_of_ereal (\<u> e) \<le> ?c * fstar e"
      proof (cases "?c \<ge> 0")
        case True then show ?thesis using hb by (simp add: mult_nonneg_nonneg)
      next
        case False
        then have h: "?c < 0" by linarith
        then have "min 0 ?c = ?c" by simp
        then show ?thesis using h hb by (simp add: mult_left_mono_neg)
      qed
    qed
    have "(\<Sum> e \<in> \<E>. min 0 (\<c> e + \<pi> (fst e) - \<pi> (snd e)) * real_of_ereal (\<u> e))
          \<le> (\<Sum> e \<in> \<E>. (\<c> e + \<pi> (fst e) - \<pi> (snd e)) * fstar e)"
      by (rule sum_mono) (use edge_lb in blast)
    then show ?thesis using telescope_fstar L_def by linarith
  qed
  have telescope_f: "\<C> f = (\<Sum> e \<in> \<E>. (\<c> e + \<pi> (fst e) - \<pi> (snd e)) * f e) - (\<Sum> v \<in> \<V>. \<pi> v * b v)"
    using telescope_gen[OF bflow] .
  have Fb: "\<And>e. e \<in> \<E> \<Longrightarrow> f e < real_of_ereal (\<u> e) \<Longrightarrow> \<c> e + \<pi> (fst e) - \<pi> (snd e) \<ge> -\<epsilon>"
  proof -
    fix e assume he: "e \<in> \<E>" and hlt: "f e < real_of_ereal (\<u> e)"
    have hFE: "F e \<in> \<EE>" using he \<EE>_def by auto
    obtain r where hr: "\<u> e = ereal r" using fin_cap he u_non_neg[of e] by (cases "\<u> e") auto
    have hpos: "\<uu>\<^bsub>f\<^esub>(F e) > 0" using hr hlt by simp
    show "\<c> e + \<pi> (fst e) - \<pi> (snd e) \<ge> -\<epsilon>"
      using slack hFE hpos by auto
  qed
  have Bb: "\<And>e. e \<in> \<E> \<Longrightarrow> f e > 0 \<Longrightarrow> \<c> e + \<pi> (fst e) - \<pi> (snd e) \<le> \<epsilon>"
  proof -
    fix e assume he: "e \<in> \<E>" and hgt: "f e > 0"
    have hBE: "B e \<in> \<EE>" using he \<EE>_def by auto
    have hpos: "\<uu>\<^bsub>f\<^esub>(B e) > 0" using hgt by simp
    have hge: "\<cc> (B e) + \<pi> (fstv (B e)) - \<pi> (sndv (B e)) \<ge> -\<epsilon>"
      using slack hBE hpos by auto
    then show "\<c> e + \<pi> (fst e) - \<pi> (snd e) \<le> \<epsilon>" by simp
  qed
  have edge_eps: "\<And>e. e \<in> \<E> \<Longrightarrow>
      (\<c> e + \<pi> (fst e) - \<pi> (snd e)) * f e - min 0 (\<c> e + \<pi> (fst e) - \<pi> (snd e)) * real_of_ereal (\<u> e)
      \<le> \<epsilon> * real_of_ereal (\<u> e)"
  proof -
    fix e assume he: "e \<in> \<E>"
    let ?c = "\<c> e + \<pi> (fst e) - \<pi> (snd e)"
    let ?u = "real_of_ereal (\<u> e)"
    have hb: "0 \<le> f e \<and> f e \<le> ?u" using hb_gen_f he by blast
    have hu_nonneg: "0 \<le> ?u" using hb by linarith
    show "?c * f e - min 0 ?c * ?u \<le> \<epsilon> * ?u"
    proof (cases "?c \<ge> 0")
      case True
      then have hmin0: "min 0 ?c = 0" by simp
      show ?thesis
      proof (cases "f e = 0")
        case True2: True
        show ?thesis using hmin0 True2 eps_nonneg hu_nonneg by (simp add: mult_nonneg_nonneg)
      next
        case False2: False
        then have hgt: "f e > 0" using hb by linarith
        have hBbound: "?c \<le> \<epsilon>" using Bb he hgt by simp
        have step1: "?c * f e \<le> \<epsilon> * f e" using hBbound hb by (simp add: mult_right_mono)
        have step2: "\<epsilon> * f e \<le> \<epsilon> * ?u" using hb eps_nonneg by (simp add: mult_left_mono)
        show ?thesis unfolding hmin0 using step1 step2 by linarith
      qed
    next
      case False
      then have hltc: "?c < 0" by linarith
      then have hmin0: "min 0 ?c = ?c" by simp
      show ?thesis
      proof (cases "f e = ?u")
        case True3: True
        show ?thesis using hmin0 True3 eps_nonneg hu_nonneg by (simp add: mult_nonneg_nonneg)
      next
        case False3: False
        then have hlt: "f e < ?u" using hb by linarith
        have hFbound: "?c \<ge> -\<epsilon>" using Fb he hlt by simp
        have hprod: "?c * (f e - ?u) \<le> (-\<epsilon>) * (f e - ?u)"
        proof (rule mult_right_mono_neg)
          show "-\<epsilon> \<le> ?c" using hFbound by simp
          show "f e - ?u \<le> 0" using hlt by simp
        qed
        have step2: "(-\<epsilon>) * (f e - ?u) \<le> \<epsilon> * ?u"
          using hb eps_nonneg by (simp add: right_diff_distrib)
        have expand: "?c * f e - ?c * ?u = ?c * (f e - ?u)" by (simp add: right_diff_distrib)
        show ?thesis unfolding hmin0 using hprod step2 expand by linarith
      qed
    qed
  qed
  have hCf_L: "\<C> f - L \<le> \<epsilon> * (\<Sum> e \<in> \<E>. real_of_ereal (\<u> e))"
  proof -
    have hsum: "(\<Sum> e \<in> \<E>. (\<c> e + \<pi> (fst e) - \<pi> (snd e)) * f e - min 0 (\<c> e + \<pi> (fst e) - \<pi> (snd e)) * real_of_ereal (\<u> e))
          \<le> (\<Sum> e \<in> \<E>. \<epsilon> * real_of_ereal (\<u> e))"
      by (rule sum_mono) (use edge_eps in blast)
    have hlhs: "(\<Sum> e \<in> \<E>. (\<c> e + \<pi> (fst e) - \<pi> (snd e)) * f e - min 0 (\<c> e + \<pi> (fst e) - \<pi> (snd e)) * real_of_ereal (\<u> e))
          = (\<Sum> e \<in> \<E>. (\<c> e + \<pi> (fst e) - \<pi> (snd e)) * f e) - (\<Sum> e \<in> \<E>. min 0 (\<c> e + \<pi> (fst e) - \<pi> (snd e)) * real_of_ereal (\<u> e))"
      by (simp add: sum_subtractf)
    have hrhs: "(\<Sum> e \<in> \<E>. \<epsilon> * real_of_ereal (\<u> e)) = \<epsilon> * (\<Sum> e \<in> \<E>. real_of_ereal (\<u> e))"
      by (simp add: sum_distrib_left)
    show ?thesis using hsum hlhs hrhs telescope_f L_def by linarith
  qed
  have hCf_Cfstar: "\<C> f - \<C> fstar \<le> \<epsilon> * (\<Sum> e \<in> \<E>. real_of_ereal (\<u> e))" using hCf_L hL_le_fstar by linarith
  have hnonneg: "0 \<le> \<C> f - \<C> fstar" using hf_ge_fstar by linarith
  have habs: "\<bar>\<C> f - \<C> fstar\<bar> = \<C> f - \<C> fstar" using hnonneg by simp
  have hden: "1 \<le> 1 + \<bar>\<C> fstar\<bar>" by simp
  have hden_pos: "0 < 1 + \<bar>\<C> fstar\<bar>" by simp
  have step1: "(\<C> f - \<C> fstar) / (1 + \<bar>\<C> fstar\<bar>) \<le> \<C> f - \<C> fstar"
  proof -
    have "(\<C> f - \<C> fstar) \<le> (\<C> f - \<C> fstar) * (1 + \<bar>\<C> fstar\<bar>)"
      using hnonneg hden mult_le_cancel_left1[of "\<C> f - \<C> fstar" "1 + \<bar>\<C> fstar\<bar>"]
      by (cases "\<C> f - \<C> fstar = 0") auto
    then show ?thesis using hden_pos by (simp add: divide_le_eq mult.commute)
  qed
  show "\<bar>\<C> f - \<C> fstar\<bar> / (1 + \<bar>\<C> fstar\<bar>) \<le> \<epsilon> * (\<Sum> e \<in> \<E>. real_of_ereal (\<u> e))"
    using habs step1 hCf_Cfstar by linarith
qed

theorem optimality_from_eps_potentials:
  fixes \<epsilon> :: real
  assumes bflow: "f is b flow"
    and eps_pos: "0 < \<epsilon>"
    and n_bound: "real (card \<V>) * \<epsilon> < 1"
    and cost_int: "\<And>e. e \<in> \<EE> \<Longrightarrow> \<cc> e \<in> \<int>"
    and eps_opt: "\<forall> e \<in> \<EE>. \<uu>\<^bsub>f\<^esub>e > 0 \<longrightarrow> \<cc> e + \<pi> (fstv e) - \<pi> (sndv e) \<ge> - \<epsilon>"
  shows "is_Opt b f"
proof(rule ccontr)
  assume not_opt: "\<not> is_Opt b f"
  obtain es where augC: "augcycle f es" and len_bound: "length es \<le> card \<V>"
    using short_augcycle_from_not_opt[OF bflow not_opt] by blast
  have CC_neg: "\<CC> es < 0" and augpath_C: "augpath f es"
    and cycle_C: "fstv (hd es) = sndv (last es)" and distinct_C: "distinct es"
    and setC_EE: "set es \<subseteq> \<EE>"
    using augC unfolding augcycle_def by auto
  have prepath_C: "prepath es" using augpath_C unfolding augpath_def by simp
  have telescope: "(\<Sum> e \<leftarrow> es. (\<pi> (fstv e) - \<pi> (sndv e))) = \<pi> (fstv (hd es)) - \<pi> (sndv (last es))"
    using prepath_C
  proof (induction rule: prepath_induct[OF prepath_C])
    case (1 e) show ?case by simp
  next
    case (2 e d es) then show ?case by simp
  qed
  have pi_list_zero: "(\<Sum> e \<leftarrow> es. (\<pi> (fstv e) - \<pi> (sndv e))) = 0" using telescope cycle_C by simp
  have pi_set_zero: "(\<Sum> e \<in> set es. (\<pi> (fstv e) - \<pi> (sndv e))) = 0"
    using distinct_C pi_list_zero by (simp add: sum.distinct_set_conv_list)
  have eps_edge: "\<And>e. e \<in> set es \<Longrightarrow> \<cc> e + \<pi> (fstv e) - \<pi> (sndv e) \<ge> - \<epsilon>"
  proof -
    fix e assume he: "e \<in> set es"
    have hE: "e \<in> \<EE>" using setC_EE he by blast
    have "0 < \<uu>\<^bsub>f\<^esub>e" using augpath_rcap_pos_strict'[OF augpath_C he] by simp
    thus "\<cc> e + \<pi> (fstv e) - \<pi> (sndv e) \<ge> - \<epsilon>"
      using eps_opt hE by simp
  qed
  have sum_ge: "(\<Sum> e \<in> set es. \<cc> e + \<pi> (fstv e) - \<pi> (sndv e)) \<ge> (\<Sum> e \<in> set es. (- \<epsilon>))"
    by (rule sum_mono) (use eps_edge in blast)
  have card_len: "(\<Sum> e \<in> set es. (- \<epsilon>)) = - \<epsilon> * real (length es)"
    using distinct_C by (simp add: distinct_card)
  have sum_split: "(\<Sum> e \<in> set es. \<cc> e + \<pi> (fstv e) - \<pi> (sndv e))
      = (\<Sum> e \<in> set es. \<cc> e) + (\<Sum> e \<in> set es. (\<pi> (fstv e) - \<pi> (sndv e)))"
    by (simp add: sum.distrib sum_subtractf algebra_simps)
  have key: "\<CC> es \<ge> - \<epsilon> * real (length es)"
    unfolding \<CC>_def using sum_ge card_len sum_split pi_set_zero by linarith
  have ge_card: "- \<epsilon> * real (length es) \<ge> - \<epsilon> * real (card \<V>)"
    using len_bound eps_pos by (simp add: mult_left_mono)
  have lb: "\<CC> es \<ge> - \<epsilon> * real (card \<V>)" using key ge_card by linarith
  have cc_int: "\<CC> es \<in> \<int>" unfolding \<CC>_def using cost_int setC_EE by (intro Ints_sum) blast
  obtain k where k_def: "\<CC> es = of_int k" using cc_int Ints_cases by blast
  have k_neg: "k < 0" using CC_neg k_def by simp
  hence k_le: "k \<le> -1" by simp
  have cc_le: "\<CC> es \<le> -1" using k_def k_le by (simp add: of_int_le_iff[symmetric])
  have "- \<epsilon> * real (card \<V>) \<le> -1" using lb cc_le by linarith
  hence "1 \<le> \<epsilon> * real (card \<V>)" by simp
  thus False using n_bound by (simp add: mult.commute)
qed

corollary optimality_from_scaled_potentials:
  fixes M :: nat
  assumes bflow: "f is b flow"
    and M_gt: "card \<V> < M"
    and cost_int: "\<And>e. e \<in> \<EE> \<Longrightarrow> \<cc> e \<in> \<int>"
    and scaled_opt: "\<And>e. e \<in> \<EE> \<Longrightarrow> \<uu>\<^bsub>f\<^esub>e > 0 \<Longrightarrow>
                      real M * \<cc> e + \<pi> (fstv e) - \<pi> (sndv e) \<ge> -1"
  shows "is_Opt b f"
proof -
  have Mpos: "(0::real) < real M" using M_gt by simp
  have eps_pos: "0 < 1 / real M" using Mpos by simp
  have n_bound: "real (card \<V>) * (1 / real M) < 1"
    using M_gt Mpos by (simp add: field_simps)
  have eps_opt: "\<forall> e \<in> \<EE>. \<uu>\<^bsub>f\<^esub>e > 0 \<longrightarrow> \<cc> e + \<pi> (fstv e) / real M - \<pi> (sndv e) / real M \<ge> - (1 / real M)"
  proof
    fix e assume he: "e \<in> \<EE>"
    show "\<uu>\<^bsub>f\<^esub>e > 0 \<longrightarrow> \<cc> e + \<pi> (fstv e) / real M - \<pi> (sndv e) / real M \<ge> - (1 / real M)"
    proof
      assume "\<uu>\<^bsub>f\<^esub>e > 0"
      hence ineq: "real M * \<cc> e + \<pi> (fstv e) - \<pi> (sndv e) \<ge> -1" using scaled_opt[OF he] by simp
      have step1: "(-1::real) / real M \<le> (real M * \<cc> e + \<pi> (fstv e) - \<pi> (sndv e)) / real M"
        by (rule divide_right_mono[OF ineq]) (use Mpos in simp)
      have split: "(real M * \<cc> e + \<pi> (fstv e) - \<pi> (sndv e)) / real M
                   = \<cc> e + \<pi> (fstv e) / real M - \<pi> (sndv e) / real M"
        using Mpos by (simp add: add_divide_distrib diff_divide_distrib)
      show "\<cc> e + \<pi> (fstv e) / real M - \<pi> (sndv e) / real M \<ge> - (1 / real M)"
        using step1 split by simp
    qed
  qed
  show ?thesis
    by (rule optimality_from_eps_potentials[OF bflow eps_pos n_bound cost_int eps_opt])
qed

text \<open>\<^emph>\<open>The converse direction: actual optimality gives a slack-based certificate too.\<close> Needed for a
      \<^emph>\<open>temporary weakening\<close>: while the solver's \<open>\<epsilon>\<close>-mode doesn't yet have a genuinely approximate
      algorithm behind it, its output is always exactly optimal, and this lemma lets that exact output
      satisfy whatever \<open>\<epsilon>\<close>-optimality obligation the mode's public contract asserts. Two pieces:

      \<^item> \<^emph>\<open>Monotonicity\<close> (below, proved): \<open>\<epsilon>\<close>-complementary slackness only gets easier to satisfy as \<open>\<epsilon>\<close>
        grows, so any certificate valid at a smaller \<open>\<epsilon>\<close> is automatically valid at every larger one.
        Pure arithmetic, no existence argument.

      \<^item> \<^emph>\<open>Existence\<close> (below, \<open>sorry\<close>): \<open>is_Opt b f\<close> gives a negative-cycle-free residual graph
        (\<open>min_cost_flow_no_augcycle\<close>, already in \<open>Cost_Optimality.thy\<close>); the standard construction adds
        a virtual source with \<open>0\<close>-cost edges to every vertex and takes \<open>\<pi>\<close> to be shortest-path distances
        from it (\<open>Bellman_Ford.thy\<close>'s \<open>Bellman_Equation\<close> is negative-weight-capable and already used
        this way elsewhere in the Orlin's-algorithm development) --- no negative cycle reachable from the
        source keeps every distance finite, and shortest-path optimality forces every edge's reduced
        cost to be \<open>\<ge> 0\<close>, i.e. exact (\<open>\<epsilon> = 0\<close>) complementary slackness. Genuinely new assembly, not
        currently formalised anywhere in this codebase (checked); parked here as a stated obligation.

      The two combine to give the general statement at the bottom, \<open>is_Opt_imp_eps_complementary_slack\<close>,
      for any \<open>\<epsilon> \<ge> 0\<close> --- not just \<open>\<epsilon> = 0\<close>.\<close>

lemma eps_complementary_slack_mono:
  assumes "\<forall> e \<in> \<EE>. \<uu>\<^bsub>f\<^esub>e > 0 \<longrightarrow> \<cc> e + \<pi> (fstv e) - \<pi> (sndv e) \<ge> - \<epsilon>" and "\<epsilon> \<le> \<epsilon>'"
  shows "\<forall> e \<in> \<EE>. \<uu>\<^bsub>f\<^esub>e > 0 \<longrightarrow> \<cc> e + \<pi> (fstv e) - \<pi> (sndv e) \<ge> - \<epsilon>'"
  using assms by fastforce

theorem is_Opt_imp_exact_complementary_slack:
  assumes bflow: "f is b flow"
    and opt: "is_Opt b f"
  shows "\<exists>\<pi>. \<forall> e \<in> \<EE>. \<uu>\<^bsub>f\<^esub>e > 0 \<longrightarrow> \<cc> e + \<pi> (fstv e) - \<pi> (sndv e) \<ge> 0"
proof (cases "{e \<in> \<EE>. \<uu>\<^bsub>f\<^esub>e > 0} = {}")
  case True
  then show ?thesis by (intro exI[of _ "\<lambda>_. 0"]) auto
next
  case False
  interpret EF: multigraph where
    \<E> = "{e \<in> \<EE>. \<uu>\<^bsub>f\<^esub>e > 0}" and fst = fstv and snd = sndv and create_edge = create_edge_residual
  proof
    show "\<And>x y. fstv (create_edge_residual x y) = x" using residual_flow.fst_create_edge .
    show "\<And>x y. sndv (create_edge_residual x y) = y" using residual_flow.snd_create_edge .
    show "finite {e \<in> \<EE>. \<uu>\<^bsub>f\<^esub>e > 0}" using finite_\<EE> by auto
    show "{e \<in> \<EE>. \<uu>\<^bsub>f\<^esub>e > 0} \<noteq> {}" using False .
  qed
  have noaug: "\<not> (\<exists> cs. augcycle f cs)" using min_cost_flow_no_augcycle[OF opt] .
  have conserv: "EF.conservative \<cc>"
  proof (rule EF.conservative_of_simple)
    fix es v assume es_ne: "es \<noteq> []" and pb: "EF.path_bet es v v" and dis: "distinct es"
    show "EF.weight \<cc> es \<ge> 0"
    proof (rule ccontr)
      assume neg: "\<not> EF.weight \<cc> es \<ge> 0"
      have subE: "set es \<subseteq> {e \<in> \<EE>. \<uu>\<^bsub>f\<^esub>e > 0}" using EF.path_bet_edges_subset[OF pb] .
      have subEE: "set es \<subseteq> \<EE>" using subE by auto
      have mp: "EF.multigraph_path es" using EF.path_bet_multigraph_path[OF pb] .
      have awalk_raw: "awalk UNIV (fstv (hd es)) (map EF.make_pair es) (sndv (last es))"
        using mp es_ne unfolding EF.multigraph_path_def by auto
      have makepair_eq: "EF.make_pair = to_vertex_pair"
        using EF.make_pair_function to_vertex_pair_fst_snd by simp
      have awalk_es: "awalk UNIV (fstv (hd es)) (map to_vertex_pair es) (sndv (last es))"
        using awalk_raw makepair_eq by simp
      have prep: "prepath es" using awalk_es es_ne by (simp add: prepath_def)
      have finset: "finite (set es)" by simp
      have nonempt: "set es \<noteq> {}" using es_ne by simp
      have rcpos: "\<And>e. e \<in> set es \<Longrightarrow> \<uu>\<^bsub>f\<^esub>e > 0" using subE by auto
      have rcap_pos: "Rcap f (set es) > 0" using Rcap_strictI[OF finset nonempt rcpos] .
      have augp: "augpath f es" unfolding augpath_def using prep rcap_pos by blast
      have closed: "fstv (hd es) = sndv (last es)"
        using EF.path_bet_hd[OF pb es_ne] EF.path_bet_last[OF pb es_ne] by simp
      have costeq: "\<CC> es = EF.weight \<cc> es"
        using dis unfolding \<CC>_def EF.weight_def by (simp add: sum_list_distinct_conv_sum_set)
      have costneg: "\<CC> es < 0" using costeq neg by simp
      have "augcycle f es" unfolding augcycle_def using costneg augp closed dis subEE by blast
      then show False using noaug by blast
    qed
  qed
  obtain \<pi> where hpi: "\<forall> e \<in> {e \<in> \<EE>. \<uu>\<^bsub>f\<^esub>e > 0}. \<cc> e + \<pi> (fstv e) - \<pi> (sndv e) \<ge> 0"
    using EF.potential_of_conservative[OF conserv] by blast
  then show ?thesis by auto
qed

theorem is_Opt_imp_eps_complementary_slack:
  assumes bflow: "f is b flow"
    and opt: "is_Opt b f"
    and eps_nonneg: "0 \<le> \<epsilon>"
  shows "\<exists>\<pi>. \<forall> e \<in> \<EE>. \<uu>\<^bsub>f\<^esub>e > 0 \<longrightarrow> \<cc> e + \<pi> (fstv e) - \<pi> (sndv e) \<ge> - \<epsilon>"
proof -
  obtain \<pi> where hpi: "\<forall> e \<in> \<EE>. \<uu>\<^bsub>f\<^esub>e > 0 \<longrightarrow> \<cc> e + \<pi> (fstv e) - \<pi> (sndv e) \<ge> 0"
    using is_Opt_imp_exact_complementary_slack[OF bflow opt] by blast
  have "\<forall> e \<in> \<EE>. \<uu>\<^bsub>f\<^esub>e > 0 \<longrightarrow> \<cc> e + \<pi> (fstv e) - \<pi> (sndv e) \<ge> - \<epsilon>"
    using hpi eps_nonneg by fastforce
  thus ?thesis by blast
qed

text \<open>\<^emph>\<open>Rejected: exactness via \<open>eps_cost_optimal\<close> plus flow integrality.\<close> An earlier version of this
      section tried to derive exact optimality from \<open>eps_cost_optimal\<close> (the aggregate real-number
      distance) together with integrality of \<open>f\<close> itself, an integral optimum, and a \<open>\<delta>\<close>-bound in terms
      of \<open>C f\<close>. Rejected because it demands \<^emph>\<open>flow\<close> integrality on top of cost integrality, which
      \<open>optimality_from_eps_potentials\<close> above never needed and the literature never needs either --- the
      statement it would have had:

      \<open>theorem eps_cost_optimal_integral_imp_opt:
         fixes \<delta> :: real
         assumes bflow: "f is b flow"
           and flow_int: "\<And>e. e \<in> \<E> \<Longrightarrow> f e \<in> \<int>"
           and cost_int: "\<And>e. e \<in> \<E> \<Longrightarrow> \<c> e \<in> \<int>"
           and opt_int: "\<exists> fstar. is_Opt b fstar \<and> \<C> fstar \<in> \<int>"
           and eps_opt: "eps_cost_optimal \<delta> b f"
           and delta_bound: "\<delta> * (2 + \<bar>\<C> f\<bar>) < 1"
         shows "is_Opt b f"\<close>\<close>

  text \<open>\section*{1. Setup and Definitions}
Let $G = (V,E)$ be a directed graph. 
\begin{itemize}
    \item \textbf{Edge variables:} For any edge $e = (u,v)$, let $c(e)$ be its cost, $u(e)$ its capacity, and $f(e)$ the flow across it.
    \item \textbf{Node variables:} For any node $v$, let $b(v)$ be its required net flow (outflow minus inflow). Let $b_f(v)$ be the \textit{actual} net flow generated by a pseudoflow $f$.
    \item \textbf{Potentials:} Let $\pi(v)$ be an arbitrary real number assigned to each node. We define the modified edge cost as $c^\pi(e) = c(e) + \pi(u) - \pi(v)$.
\end{itemize}

\subsection*{The Computable Bounds}
Calculate the following three values using the pseudoflow $f$ and potentials $\pi$:
\begin{align}
    \text{Pseudoflow Cost:} \quad c(f) &= \sum_{e \in E} c(e)f(e) \\[1ex]
    \text{Lower Bound:} \quad L(\pi) &= \sum_{e \in E} \min(0, c^\pi(e))u(e) - \sum_{v \in V} \pi(v)b(v) \\[1ex]
    \text{Upper Bound:} \quad U(\pi) &= \sum_{e \in E} \max(0, c^\pi(e))u(e) - \sum_{v \in V} \pi(v)b(v)
\end{align}

\vspace{0.5cm}
\hrule
\vspace{0.5cm}

\section*{2. The Required Constraint}

To guarantee that the pseudoflow $f$ is within a relative error threshold $\delta$ of the true, unknown optimal flow $f^*$, evaluate this single computable inequality:

\begin{equation}
    \frac{\max\Big( |c(f) - L(\pi)|, \; |c(f) - U(\pi)| \Big)}{1 + M_{\min}} < \delta
\end{equation}

Where $M_{\min}$ is the minimum possible absolute value in the interval $[L(\pi), U(\pi)]$, defined strictly as:
\begin{align*}
    M_{\min} &= 0 \quad &&\text{if } L(\pi) \le 0 \le U(\pi) \\
    M_{\min} &= L(\pi) \quad &&\text{if } L(\pi) > 0 \\
    M_{\min} &= -U(\pi) \quad &&\text{if } U(\pi) < 0
\end{align*}

\pagebreak

\section*{3. Algebraic Proof of Sufficiency}

We must prove that evaluating the computable fraction in (4) guarantees the true relative error is bounded: $\frac{|c(f) - c(f^*)|}{1 + |c(f^*)|} < \delta$.

\subsection*{Step A: The Telescoping Sum Identity}
For any flow assignment $x$, we can expand its total cost by adding and subtracting node potentials. By grouping the terms by nodes, the potentials telescope against the net flow $b_x(v)$:
\begin{align*}
    c(x) &= \sum_{(u,v) \in E} c(u,v)x(u,v) \\
    &= \sum_{(u,v) \in E} \Big(c^\pi(u,v) - \pi(u) + \pi(v)\Big)x(u,v) \\
    &= \sum_{e \in E} c^\pi(e)x(e) - \sum_{v \in V} \pi(v)b_x(v)
\end{align*}

\subsection*{Step B: Trapping the Optimal Cost $c(f^*)$}
By definition, the true optimal flow $f^*$ is physically valid. This guarantees:
\begin{enumerate}
    \item It perfectly satisfies node balances: $b_{f^*}(v) = b(v)$.
    \item It strictly obeys capacity bounds: $0 \le f^*(e) \le u(e)$.
\end{enumerate}

Applying the telescoping identity to the optimal flow:
\begin{equation*}
    c(f^*) = \sum_{e \in E} c^\pi(e)f^*(e) - \sum_{v \in V} \pi(v)b(v)
\end{equation*}

Because $f^*(e)$ is bounded between $0$ and $u(e)$, the term $c^\pi(e)f^*(e)$ has absolute mathematical limits. Its minimum possible value is $\min(0, c^\pi(e))u(e)$, and its maximum is $\max(0, c^\pi(e))u(e)$. By substituting these extremes into the equation, we guarantee that the optimal cost $c(f^*)$ is perfectly trapped between our computable bounds $L(\pi)$ and $U(\pi)$:
\begin{equation*}
    L(\pi) \le c(f^*) \le U(\pi)
\end{equation*}

\subsection*{Step C: Bounding the Numerator and Denominator}
We now bound the components of the target fraction $\frac{|c(f) - c(f^*)|}{1 + |c(f^*)|}$.

\paragraph{1. Bounding the Numerator:}
We know $c(f^*)$ exists somewhere within the interval $[L(\pi), U(\pi)]$. The maximum possible distance from the pseudoflow's cost $c(f)$ to \textit{any} point in that interval is the distance to the furthest endpoint. Therefore, the absolute error is strictly bounded from above:
\begin{equation*}
    |c(f) - c(f^*)| \le \max\Big( |c(f) - L(\pi)|, \; |c(f) - U(\pi)| \Big)
\end{equation*}

\paragraph{2. Bounding the Denominator:}
Because $c(f^*)$ lies in $[L(\pi), U(\pi)]$, its absolute value $|c(f^*)|$ cannot be smaller than the absolute value of the number closest to $0$ in that interval. We defined this minimum absolute value as $M_{\min}$. Therefore, the denominator is strictly bounded from below:
\begin{equation*}
    1 + |c(f^*)| \ge 1 + M_{\min}
\end{equation*}

\subsection*{Conclusion}
By replacing the true numerator with our strictly larger maximum distance, and the true denominator with our strictly smaller minimum value, we mathematically force our computable fraction to be larger than or equal to the true relative error:
\begin{equation*}
    \frac{|c(f) - c(f^*)|}{1 + |c(f^*)|} \le \frac{\max\Big( |c(f) - L(\pi)|, \; |c(f) - U(\pi)| \Big)}{1 + M_{\min}}
\end{equation*}

Therefore, if the computable fraction on the right evaluates to less than $\delta$, it is algebraically guaranteed that the true relative error on the left is also less than $\delta$. \qed\<close>

lemma cost_optimality_relative_bound:
  assumes
    opt: "is_Opt b \<f>"
    and fin_cap: "\<forall> e \<in> \<E>. \<u> e \<noteq> \<infinity>"
    and L_def: "L = (\<Sum> e \<in> \<E>. min 0 (\<c> e + \<pi> (fst e) - \<pi> (snd e)) * real_of_ereal (\<u> e))
                     - (\<Sum> v \<in> \<V>. \<pi> v * b v)"
    and U_def: "U = (\<Sum> e \<in> \<E>. max 0 (\<c> e + \<pi> (fst e) - \<pi> (snd e)) * real_of_ereal (\<u> e))
                     - (\<Sum> v \<in> \<V>. \<pi> v * b v)"
    and M_min_def: "M_min = (if L \<le> 0 \<and> 0 \<le> U then 0 else if 0 < L then L else -U)"
    and bound: "max (\<bar>\<C> f - L\<bar>) (\<bar>\<C> f - U\<bar>) / (1 + M_min) < \<delta>"
  shows
    "\<bar>\<C> f - \<C> \<f>\<bar> / (1 + \<bar>\<C> \<f>\<bar>) < \<delta>"
proof -
  have hflow: "\<f> is b flow" using opt is_Opt_def by blast
  have hisuflow: "isuflow \<f>" using hflow isbflow_def by blast
  have hfge: "\<forall> e \<in> \<E>. 0 \<le> \<f> e" using hisuflow isuflow_def by blast
  have hfle_ereal: "\<forall> e \<in> \<E>. ereal (\<f> e) \<le> \<u> e" using hisuflow isuflow_def by blast
  have hfle_real: "\<forall> e \<in> \<E>. \<f> e \<le> real_of_ereal (\<u> e)"
  proof
    fix e assume he: "e \<in> \<E>"
    obtain r where hr: "\<u> e = ereal r"
      using hfle_ereal he fin_cap by (cases "\<u> e") auto
    show "\<f> e \<le> real_of_ereal (\<u> e)"
      using hfle_ereal he hr by (auto simp: real_le_ereal_iff)
  qed
  have hbv: "\<forall> v \<in> \<V>. b v = sum \<f> (delta_plus v) - sum \<f> (delta_minus v)"
  proof
    fix v assume hv: "v \<in> \<V>"
    have "- ex \<f> v = b v" using hflow isbflow_def hv by blast
    then show "b v = sum \<f> (delta_plus v) - sum \<f> (delta_minus v)"
      by (simp add: ex_def delta_plus_def delta_minus_def)
  qed
  have union_plus: "(Union (delta_plus ` \<V>)) = \<E>"
    by (auto simp add: delta_plus_def fst_E_V)
  have union_minus: "(Union (delta_minus ` \<V>)) = \<E>"
    by (auto simp add: delta_minus_def snd_E_V)
  have disj_plus: "\<forall> v1 \<in> \<V>. \<forall> v2 \<in> \<V>. v1 \<noteq> v2 \<longrightarrow> delta_plus v1 \<inter> delta_plus v2 = {}"
    by (auto simp add: delta_plus_def)
  have disj_minus: "\<forall> v1 \<in> \<V>. \<forall> v2 \<in> \<V>. v1 \<noteq> v2 \<longrightarrow> delta_minus v1 \<inter> delta_minus v2 = {}"
    by (auto simp add: delta_minus_def)
  have regroup_fst: "sum (\<lambda> e. \<pi> (fst e) * \<f> e) \<E> = (\<Sum> v \<in> \<V>. \<pi> v * sum \<f> (delta_plus v))"
  proof -
    have h1: "sum (\<lambda> e. \<pi> (fst e) * \<f> e) (Union (delta_plus ` \<V>))
              = (\<Sum> v \<in> \<V>. \<Sum> e \<in> delta_plus v. \<pi> (fst e) * \<f> e)"
      by (rule sum.UNION_disjoint) (use \<V>_finite delta_plus_finite disj_plus in auto)
    have h2: "(\<Sum> v \<in> \<V>. \<Sum> e \<in> delta_plus v. \<pi> (fst e) * \<f> e)
              = (\<Sum> v \<in> \<V>. \<pi> v * sum \<f> (delta_plus v))"
      by (rule sum.cong, rule refl) (auto simp add: delta_plus_def sum_distrib_left)
    show ?thesis using h1 h2 by (simp add: union_plus)
  qed
  have regroup_snd: "sum (\<lambda> e. \<pi> (snd e) * \<f> e) \<E> = (\<Sum> v \<in> \<V>. \<pi> v * sum \<f> (delta_minus v))"
  proof -
    have h1: "sum (\<lambda> e. \<pi> (snd e) * \<f> e) (Union (delta_minus ` \<V>))
              = (\<Sum> v \<in> \<V>. \<Sum> e \<in> delta_minus v. \<pi> (snd e) * \<f> e)"
      by (rule sum.UNION_disjoint) (use \<V>_finite delta_minus_finite disj_minus in auto)
    have h2: "(\<Sum> v \<in> \<V>. \<Sum> e \<in> delta_minus v. \<pi> (snd e) * \<f> e)
              = (\<Sum> v \<in> \<V>. \<pi> v * sum \<f> (delta_minus v))"
      by (rule sum.cong, rule refl) (auto simp add: delta_minus_def sum_distrib_left)
    show ?thesis using h1 h2 by (simp add: union_minus)
  qed
  have pivot: "(\<Sum> e \<in> \<E>. (\<pi> (fst e) - \<pi> (snd e)) * \<f> e) = (\<Sum> v \<in> \<V>. \<pi> v * b v)"
  proof -
    have "(\<Sum> e \<in> \<E>. (\<pi> (fst e) - \<pi> (snd e)) * \<f> e)
          = (\<Sum> e \<in> \<E>. \<pi> (fst e) * \<f> e) - (\<Sum> e \<in> \<E>. \<pi> (snd e) * \<f> e)"
      by (simp add: ring_distribs sum_subtractf)
    also have "... = (\<Sum> v \<in> \<V>. \<pi> v * sum \<f> (delta_plus v)) - (\<Sum> v \<in> \<V>. \<pi> v * sum \<f> (delta_minus v))"
      by (simp add: regroup_fst regroup_snd)
    also have "... = (\<Sum> v \<in> \<V>. \<pi> v * (sum \<f> (delta_plus v) - sum \<f> (delta_minus v)))"
      by (simp add: sum_subtractf ring_distribs)
    also have "... = (\<Sum> v \<in> \<V>. \<pi> v * b v)"
      by (rule sum.cong, rule refl) (use hbv in auto)
    finally show ?thesis .
  qed
  have telescope: "\<C> \<f> = (\<Sum> e \<in> \<E>. (\<c> e + \<pi> (fst e) - \<pi> (snd e)) * \<f> e) - (\<Sum> v \<in> \<V>. \<pi> v * b v)"
  proof -
    have "(\<Sum> e \<in> \<E>. (\<c> e + \<pi> (fst e) - \<pi> (snd e)) * \<f> e)
          = (\<Sum> e \<in> \<E>. \<c> e * \<f> e) + (\<Sum> e \<in> \<E>. (\<pi> (fst e) - \<pi> (snd e)) * \<f> e)"
      by (simp add: ring_distribs sum.distrib sum_subtractf)
    also have "... = \<C> \<f> + (\<Sum> v \<in> \<V>. \<pi> v * b v)"
      using pivot by (simp add: \<C>_def mult.commute)
    finally show ?thesis by linarith
  qed
  have edge_lb: "\<forall> e \<in> \<E>. min 0 (\<c> e + \<pi> (fst e) - \<pi> (snd e)) * real_of_ereal (\<u> e)
                            \<le> (\<c> e + \<pi> (fst e) - \<pi> (snd e)) * \<f> e"
  proof
    fix e assume he: "e \<in> \<E>"
    let ?c = "\<c> e + \<pi> (fst e) - \<pi> (snd e)"
    have hge: "0 \<le> \<f> e" using hfge he by blast
    have hle: "\<f> e \<le> real_of_ereal (\<u> e)" using hfle_real he by blast
    show "min 0 ?c * real_of_ereal (\<u> e) \<le> ?c * \<f> e"
    proof (cases "?c \<ge> 0")
      case True then show ?thesis by (simp add: mult_nonneg_nonneg hge)
    next
      case False
      then have h: "?c < 0" by linarith
      then have "min 0 ?c = ?c" by simp
      then show ?thesis using h hle by (simp add: mult_left_mono_neg)
    qed
  qed
  have edge_ub: "\<forall> e \<in> \<E>. (\<c> e + \<pi> (fst e) - \<pi> (snd e)) * \<f> e
                            \<le> max 0 (\<c> e + \<pi> (fst e) - \<pi> (snd e)) * real_of_ereal (\<u> e)"
  proof
    fix e assume he: "e \<in> \<E>"
    let ?c = "\<c> e + \<pi> (fst e) - \<pi> (snd e)"
    have hge: "0 \<le> \<f> e" using hfge he by blast
    have hle: "\<f> e \<le> real_of_ereal (\<u> e)" using hfle_real he by blast
    show "?c * \<f> e \<le> max 0 ?c * real_of_ereal (\<u> e)"
    proof (cases "?c \<ge> 0")
      case True
      then have "max 0 ?c = ?c" by simp
      then show ?thesis using True hle by (simp add: mult_left_mono)
    next
      case False
      then have h: "?c < 0" by linarith
      then have "max 0 ?c = 0" by simp
      then show ?thesis using h hge by (simp add: mult_nonpos_nonneg)
    qed
  qed
  have hL: "L \<le> \<C> \<f>"
  proof -
    have "(\<Sum> e \<in> \<E>. min 0 (\<c> e + \<pi> (fst e) - \<pi> (snd e)) * real_of_ereal (\<u> e))
          \<le> (\<Sum> e \<in> \<E>. (\<c> e + \<pi> (fst e) - \<pi> (snd e)) * \<f> e)"
      by (rule sum_mono) (use edge_lb in blast)
    then show ?thesis using telescope L_def by linarith
  qed
  have hU: "\<C> \<f> \<le> U"
  proof -
    have "(\<Sum> e \<in> \<E>. (\<c> e + \<pi> (fst e) - \<pi> (snd e)) * \<f> e)
          \<le> (\<Sum> e \<in> \<E>. max 0 (\<c> e + \<pi> (fst e) - \<pi> (snd e)) * real_of_ereal (\<u> e))"
      by (rule sum_mono) (use edge_ub in blast)
    then show ?thesis using telescope U_def by linarith
  qed
  have hLU: "L \<le> U" using hL hU by linarith
  have hMmin_nonneg: "0 \<le> M_min"
  proof (cases "L \<le> 0 \<and> 0 \<le> U")
    case True then show ?thesis by (simp add: M_min_def)
  next
    case False
    show ?thesis
    proof (cases "0 < L")
      case True then show ?thesis by (simp add: M_min_def False)
    next
      case False2: False
      then have "U < 0" using hLU False by linarith
      then show ?thesis by (simp add: M_min_def False False2)
    qed
  qed
  have hMmin_abs: "M_min \<le> \<bar>\<C> \<f>\<bar>"
  proof (cases "L \<le> 0 \<and> 0 \<le> U")
    case True then show ?thesis by (simp add: M_min_def)
  next
    case False
    show ?thesis
    proof (cases "0 < L")
      case True
      then have "M_min = L" using M_min_def False by simp
      then show ?thesis using hL True by linarith
    next
      case False2: False
      then have "U < 0" using hLU \<open>\<not> (L \<le> 0 \<and> 0 \<le> U)\<close> by linarith
      then have "M_min = - U" using M_min_def \<open>\<not> (L \<le> 0 \<and> 0 \<le> U)\<close> False2 by simp
      then show ?thesis using hU \<open>U < 0\<close> by linarith
    qed
  qed
  have hnum: "\<bar>\<C> f - \<C> \<f>\<bar> \<le> max \<bar>\<C> f - L\<bar> \<bar>\<C> f - U\<bar>"
    using hL hU unfolding abs_real_def max_def by simp
  have hden: "1 + M_min \<le> 1 + \<bar>\<C> \<f>\<bar>" using hMmin_abs by linarith
  have hnum_nonneg: "0 \<le> max (\<bar>\<C> f - L\<bar>) (\<bar>\<C> f - U\<bar>)" by simp
  have hden_pos: "0 < 1 + M_min" using hMmin_nonneg by linarith
  have hden2_pos: "0 < 1 + \<bar>\<C> \<f>\<bar>" by simp
  show "\<bar>\<C> f - \<C> \<f>\<bar> / (1 + \<bar>\<C> \<f>\<bar>) < \<delta>"
  proof -
    have step1: "\<bar>\<C> f - \<C> \<f>\<bar> / (1 + \<bar>\<C> \<f>\<bar>) \<le>
                 max (\<bar>\<C> f - L\<bar>) (\<bar>\<C> f - U\<bar>) / (1 + \<bar>\<C> \<f>\<bar>)"
      by (rule divide_right_mono) (use hnum hden2_pos in linarith)+
    have step2: "max (\<bar>\<C> f - L\<bar>) (\<bar>\<C> f - U\<bar>) / (1 + \<bar>\<C> \<f>\<bar>) \<le>
                 max (\<bar>\<C> f - L\<bar>) (\<bar>\<C> f - U\<bar>) / (1 + M_min)"
    proof (rule divide_left_mono)
      show "1 + M_min \<le> 1 + \<bar>\<C> \<f>\<bar>" using hden .
      show "0 \<le> max (\<bar>\<C> f - L\<bar>) (\<bar>\<C> f - U\<bar>)" using hnum_nonneg .
      have "0 < (1 + M_min) * (1 + \<bar>\<C> \<f>\<bar>)"
        by (rule mult_pos_pos) (use hden_pos hden2_pos in linarith)+
      then show "0 < (1 + \<bar>\<C> \<f>\<bar>) * (1 + M_min)" by (simp add: mult.commute)
    qed
    show ?thesis
      using step1 step2 bound by linarith
  qed
qed

end
end