theory Spanning_Tree_Flow
  imports Flow_Theory.Cost_Optimality Spanning_Trees.Arborescense
begin

context
cost_flow_network
begin


definition "spanning_tree_partition r T L U =
    (\<E> = T \<union> U \<union> L \<and> T \<inter> U = {} \<and> T \<inter> L = {} \<and> L \<inter> U = {} \<and>
      graph_abs.arborescence ((\<lambda> e. {fst e, snd e} ) ` T) r ((\<lambda> e. {fst e, snd e})  ` T)
      \<and>  graph_abs ((\<lambda> e. {fst e, snd e} ) ` T) \<and>
      (\<forall> e e'. {e, e'} \<subseteq> T \<and> {fst e, snd e} = {fst e', snd e'} \<longrightarrow> e = e') \<and>
      dVs (make_pair ` T) = \<V> )"

definition "flow_fits_spanning_tree_partition T L U f =
    ((\<forall> e \<in> L. f e = 0) \<and> (\<forall> e \<in> U. ereal (f e) = \<u> e))"

definition "potential_fits_spanning_tree_partition r T \<pi> =
       (\<pi> r = 0 \<and> (\<forall> e \<in> T. \<c> e + \<pi> (fst e) - \<pi> (snd e) = 0))"

text \<open>At a fixed vertex @{term a}, the excess of a flow is a signed sum of the flow values on the
      edges incident to @{term a}. If two flows agree on all incident edges but one, and they have
      the same excess at @{term a}, then they must also agree on that last edge.\<close>

lemma excess_determines_edge:
  assumes e0E: "e0 \<in> \<E>" and ain: "a = fst e0 \<or> a = snd e0" and dist: "fst e0 \<noteq> snd e0"
    and agp: "\<And> e. \<lbrakk>e \<in> \<E>; e \<noteq> e0; fst e = a\<rbrakk> \<Longrightarrow> f e = f' e"
    and agm: "\<And> e. \<lbrakk>e \<in> \<E>; e \<noteq> e0; snd e = a\<rbrakk> \<Longrightarrow> f e = f' e"
    and exeq: "(ex\<^bsub>f\<^esub> a) = (ex\<^bsub>f'\<^esub> a)"
  shows "f e0 = f' e0"
proof -
  have finE: "finite \<E>" using finite_E by simp
  have finp: "finite (\<delta>\<^sup>+ a)" using finE by (auto simp add: delta_plus_def)
  have finm: "finite (\<delta>\<^sup>- a)" using finE by (auto simp add: delta_minus_def)
  have sump: "(\<Sum> e\<in>\<delta>\<^sup>+ a. f e - f' e) = (\<Sum> e\<in>\<delta>\<^sup>+ a \<inter> {e0}. f e - f' e)"
    using agp finp by (intro sum.mono_neutral_right) (auto simp add: delta_plus_def)
  have summ: "(\<Sum> e\<in>\<delta>\<^sup>- a. f e - f' e) = (\<Sum> e\<in>\<delta>\<^sup>- a \<inter> {e0}. f e - f' e)"
    using agm finm by (intro sum.mono_neutral_right) (auto simp add: delta_minus_def)
  have exdiff: "(ex\<^bsub>f\<^esub> a) - (ex\<^bsub>f'\<^esub> a) = (\<Sum> e\<in>\<delta>\<^sup>- a. f e - f' e) - (\<Sum> e\<in>\<delta>\<^sup>+ a. f e - f' e)"
    by (simp add: ex_def sum_subtractf)
  show "f e0 = f' e0"
    using ain
  proof
    assume af: "a = fst e0"
    hence e0p: "\<delta>\<^sup>+ a \<inter> {e0} = {e0}" using e0E by (auto simp add: delta_plus_def)
    have e0m: "\<delta>\<^sup>- a \<inter> {e0} = {}" using dist af by (auto simp add: delta_minus_def)
    have "(ex\<^bsub>f\<^esub> a) - (ex\<^bsub>f'\<^esub> a) = - (f e0 - f' e0)"
      using exdiff sump summ e0p e0m by simp
    thus "f e0 = f' e0" using exeq by simp
  next
    assume as: "a = snd e0"
    hence e0m: "\<delta>\<^sup>- a \<inter> {e0} = {e0}" using e0E by (auto simp add: delta_minus_def)
    have e0p: "\<delta>\<^sup>+ a \<inter> {e0} = {}" using dist as by (auto simp add: delta_plus_def)
    have "(ex\<^bsub>f\<^esub> a) - (ex\<^bsub>f'\<^esub> a) = (f e0 - f' e0)"
      using exdiff sump summ e0p e0m by simp
    thus "f e0 = f' e0" using exeq by simp
  qed
qed

text \<open>Given a spanning-tree partition, the flow on the tree edges is uniquely determined by the
      balance @{term b}. We prove this by peeling off leaves of the (sub-)forest one at a time: a
      non-empty forest has a leaf @{term a}, all edges incident to @{term a} except its unique tree
      edge already agree, and the balance constraint at @{term a} then pins down the last one via
      @{thm [source] excess_determines_edge}.  The induction runs over arbitrary sub-forests, so no
      root bookkeeping is needed; instantiating it with \<open>S = T\<close> settles all tree edges at once.\<close>

lemma spanning_flow_unique:
  assumes "f is b flow" "f' is b flow"
          "spanning_tree_partition r T L U"
          "flow_fits_spanning_tree_partition T L U f"
          "flow_fits_spanning_tree_partition T L U f'"
    shows "\<And> e. e \<in> \<E> \<Longrightarrow> f e = f' e"
proof -
  define GT where "GT = (\<lambda> e. {fst e, snd e}) ` T"
  have EE: "\<E> = T \<union> U \<union> L" and gaT: "graph_abs GT"
   and arbT: "graph_abs.arborescence GT r GT"
   and injT: "\<And> e e'. \<lbrakk>e \<in> T; e' \<in> T; {fst e, snd e} = {fst e', snd e'}\<rbrakk> \<Longrightarrow> e = e'"
   and VsGT: "dVs (make_pair ` T) = \<V>"
    using assms(3) by(auto simp add: spanning_tree_partition_def GT_def)
  have LUf: "\<And> e. e \<in> L \<Longrightarrow> f e = 0" "\<And> e. e \<in> U \<Longrightarrow> f e = \<u> e"
   and LUf': "\<And> e. e \<in> L \<Longrightarrow> f' e = 0" "\<And> e. e \<in> U \<Longrightarrow> f' e = \<u> e"
    using assms(4,5) by(auto simp add: flow_fits_spanning_tree_partition_def)
  have hncT: "graph_abs.has_no_cycle GT GT"
    using graph_abs.arborescenceD(1)[OF gaT arbT] by simp
  have TE: "T \<subseteq> \<E>" using EE by auto
  have bal: "\<And> v. v \<in> \<V> \<Longrightarrow> (ex\<^bsub>f\<^esub> v) = (ex\<^bsub>f'\<^esub> v)"
  proof -
    fix v assume vV: "v \<in> \<V>"
    have "- (ex\<^bsub>f\<^esub> v) = b v" using assms(1) vV by(auto elim!: isbflowE)
    moreover have "- (ex\<^bsub>f'\<^esub> v) = b v" using assms(2) vV by(auto elim!: isbflowE)
    ultimately show "(ex\<^bsub>f\<^esub> v) = (ex\<^bsub>f'\<^esub> v)" by simp
  qed
  have VsGTeq: "Vs GT = \<V>"
  proof -
    have "Vs GT = \<Union> {{fst e, snd e} | e. e \<in> T}"
      by (auto simp add: GT_def Vs_def)
    also have "\<dots> = dVs (make_pair ` T)"
      by (auto simp add: dVs_def make_pair_def)
    finally show ?thesis using VsGT by simp
  qed
  have key: "\<And> S. S \<subseteq> T \<Longrightarrow> (\<forall> x \<in> \<E>. x \<notin> S \<longrightarrow> f x = f' x) \<Longrightarrow> (\<forall> e \<in> S. f e = f' e)"
  proof -
    fix S
    show "\<lbrakk>S \<subseteq> T; \<forall> x \<in> \<E>. x \<notin> S \<longrightarrow> f x = f' x\<rbrakk> \<Longrightarrow> (\<forall> e \<in> S. f e = f' e)"
    proof(induct "card S" arbitrary: S rule: less_induct)
      case (less S)
      show ?case
      proof(cases "S = {}")
        case True
        thus ?thesis by simp
      next
        case False
        have ST: "S \<subseteq> T" using less.prems by blast
        have out: "\<And> x. \<lbrakk>x \<in> \<E>; x \<notin> S\<rbrakk> \<Longrightarrow> f x = f' x" using less.prems by blast
        have finT: "finite T" using finite_subset[OF TE finite_E] by simp
        have finS: "finite S" using finite_subset[OF ST finT] by simp
        have imgS_sub: "(\<lambda> e. {fst e, snd e}) ` S \<subseteq> GT" using ST by(auto simp add: GT_def)
        have hncS: "graph_abs.has_no_cycle GT ((\<lambda> e. {fst e, snd e}) ` S)"
          using graph_abs.has_no_cycle_indep_subset[OF gaT hncT imgS_sub] by simp
        have imgS_ne: "(\<lambda> e. {fst e, snd e}) ` S \<noteq> {}" using \<open>S \<noteq> {}\<close> by simp
        obtain a where aVs: "a \<in> Vs ((\<lambda> e. {fst e, snd e}) ` S)"
                   and adeg: "degree ((\<lambda> e. {fst e, snd e}) ` S) a = 1"
          using graph_abs.tree_has_leaf[OF gaT hncS imgS_ne] by auto
        from degree_one_unique[OF adeg]
        obtain Ea where EaS: "Ea \<in> (\<lambda> e. {fst e, snd e}) ` S" and aEa: "a \<in> Ea"
          and Ea_uniq: "\<And> E'. E' \<in> (\<lambda> e. {fst e, snd e}) ` S \<Longrightarrow> a \<in> E' \<Longrightarrow> E' = Ea"
          by (auto elim!: ex1E)
        obtain ea where eaS: "ea \<in> S" and Eaea: "Ea = {fst ea, snd ea}" using EaS by auto
        have a_in_ea: "a \<in> {fst ea, snd ea}" using aEa Eaea by simp
        have Ea_GT: "Ea \<in> GT" using EaS imgS_sub by auto
        have dist_ea: "fst ea \<noteq> snd ea"
          using graph_invar_edgeD[OF graph_abs.graph[OF gaT]] Ea_GT Eaea by auto
        have aV: "a \<in> \<V>" using aVs Vs_subset[OF imgS_sub] VsGTeq by auto
        have agree_other: "\<And> e. \<lbrakk>e \<in> \<E>; e \<noteq> ea; a \<in> {fst e, snd e}\<rbrakk> \<Longrightarrow> f e = f' e"
        proof -
          fix e assume eE: "e \<in> \<E>" and ene: "e \<noteq> ea" and ain: "a \<in> {fst e, snd e}"
          show "f e = f' e"
          proof(cases "e \<in> S")
            case True
            hence eT: "e \<in> T" using ST by auto
            have "{fst e, snd e} \<in> (\<lambda> e. {fst e, snd e}) ` S" using True by auto
            hence "{fst e, snd e} = Ea" using Ea_uniq ain by auto
            hence "{fst e, snd e} = {fst ea, snd ea}" using Eaea by simp
            hence "e = ea" using injT[OF eT] eaS ST by auto
            thus ?thesis using ene by simp
          next
            case False
            thus ?thesis using out eE by simp
          qed
        qed
        have agp: "\<And> e. \<lbrakk>e \<in> \<E>; e \<noteq> ea; fst e = a\<rbrakk> \<Longrightarrow> f e = f' e"
          by (metis agree_other insert_iff)
        have agm: "\<And> e. \<lbrakk>e \<in> \<E>; e \<noteq> ea; snd e = a\<rbrakk> \<Longrightarrow> f e = f' e"
          by (metis agree_other insert_iff)
        have eaE: "ea \<in> \<E>" using eaS ST TE by auto
        have ain_ea: "a = fst ea \<or> a = snd ea" using a_in_ea by auto
        have exeq_a: "(ex\<^bsub>f\<^esub> a) = (ex\<^bsub>f'\<^esub> a)" using bal[OF aV] by blast
        have fea: "f ea = f' ea"
          by (rule excess_determines_edge[OF eaE ain_ea dist_ea agp agm exeq_a])
        have subS: "S - {ea} \<subseteq> T" using ST by auto
        have cardlt: "card (S - {ea}) < card S" using card_Diff1_less[OF finS eaS] by simp
        have out': "\<forall> x \<in> \<E>. x \<notin> S - {ea} \<longrightarrow> f x = f' x" using out fea by auto
        have "\<forall> e \<in> S - {ea}. f e = f' e" using less.hyps[OF cardlt subS out'] by simp
        thus "\<forall> e \<in> S. f e = f' e" using fea by auto
      qed
    qed
  qed
  have outT: "\<forall> x \<in> \<E>. x \<notin> T \<longrightarrow> f x = f' x"
  proof(intro ballI impI)
    fix x assume xE: "x \<in> \<E>" and xnT: "x \<notin> T"
    from xE xnT EE have "x \<in> U \<or> x \<in> L" by auto
    thus "f x = f' x"
    proof
      assume "x \<in> U"
      thus ?thesis using LUf(2) LUf'(2) by (metis ereal.inject)
    next
      assume "x \<in> L"
      thus ?thesis using LUf(1) LUf'(1) by simp
    qed
  qed
  have onT: "\<forall> e \<in> T. f e = f' e" using key[OF subset_refl outT] by simp
  show "\<And> e. e \<in> \<E> \<Longrightarrow> f e = f' e" using onT outT by blast
qed

text \<open>The vertex potentials are unique, too. Consider the set of vertices on which the two
      potentials \<open>\<pi>\<close> and \<open>\<pi>'\<close> agree. The root r belongs to it, since both potentials vanish at r. This
      set is closed along the tree edges: subtracting the two reduced-cost constraints
      \<open>\<c> e + \<pi> (fst e) + \<pi> (snd e) = 0\<close> and \<open>\<c> e + \<pi>' (fst e) + \<pi>' (snd e) = 0\<close> of a tree edge e
      shows that the potential differences at its two endpoints are negatives of one another, so
      whenever one endpoint agrees the other must agree as well. Since the tree is a spanning
      arborescence around r, every vertex of \<open>\<V>\<close> is joined to r by a walk in the tree; propagating
      agreement edge by edge along that walk shows the two potentials coincide at the vertex.\<close>

lemma spanning_potential_unqiue:
  assumes "spanning_tree_partition r T L U"
      "potential_fits_spanning_tree_partition r T \<pi>" 
      "potential_fits_spanning_tree_partition r T \<pi>'"
    shows "\<And> v. v \<in> \<V> \<Longrightarrow> \<pi> v = \<pi>' v"
proof -
  define GT where "GT = (\<lambda> e. {fst e, snd e}) ` T"
  have gaT: "graph_abs GT" and arbT: "graph_abs.arborescence GT r GT"
   and VsGT: "dVs (make_pair ` T) = \<V>"
    using assms(1) by(auto simp add: spanning_tree_partition_def GT_def)
  have piR: "\<pi> r = 0" and edgeqA: "\<And> e. e \<in> T \<Longrightarrow> \<c> e + \<pi> (fst e) - \<pi> (snd e) = 0"
    using assms(2) by(auto simp add: potential_fits_spanning_tree_partition_def)
  have piR': "\<pi>' r = 0" and edgeqB: "\<And> e. e \<in> T \<Longrightarrow> \<c> e + \<pi>' (fst e) - \<pi>' (snd e) = 0"
    using assms(3) by(auto simp add: potential_fits_spanning_tree_partition_def)
  have VsGTeq: "Vs GT = \<V>"
  proof -
    have "Vs GT = \<Union> {{fst e, snd e} | e. e \<in> T}"
      by (auto simp add: GT_def Vs_def)
    also have "\<dots> = dVs (make_pair ` T)"
      by (auto simp add: dVs_def make_pair_def)
    finally show ?thesis using VsGT by simp
  qed
  define W where "W = {x. \<pi> x = \<pi>' x}"
  have rW: "r \<in> W" using piR piR' by(simp add: W_def)
  have closed: "\<And> x y. \<lbrakk>{x, y} \<in> GT; x \<in> W\<rbrakk> \<Longrightarrow> y \<in> W"
  proof -
    fix x y assume xy: "{x, y} \<in> GT" and xW: "x \<in> W"
    from xy obtain e where eT: "e \<in> T" and exy: "{fst e, snd e} = {x, y}"
      by(auto simp add: GT_def)
    have px: "\<pi> x = \<pi>' x" using xW by(simp add: W_def)
    have keyeq: "(\<pi> (fst e) - \<pi>' (fst e)) - (\<pi> (snd e) - \<pi>' (snd e)) = 0"
      using edgeqA[OF eT] edgeqB[OF eT] by auto
    from exy have "fst e = x \<and> snd e = y \<or> fst e = y \<and> snd e = x"
      by (metis doubleton_eq_iff)
    thus "y \<in> W"
    proof
      assume "fst e = x \<and> snd e = y"
      hence "(\<pi> x - \<pi>' x) - (\<pi> y - \<pi>' y) = 0" using keyeq by simp
      thus ?thesis using px by(simp add: W_def)
    next
      assume "fst e = y \<and> snd e = x"
      hence "(\<pi> y - \<pi>' y) - (\<pi> x - \<pi>' x) = 0" using keyeq by simp
      thus ?thesis using px by(simp add: W_def)
    qed
  qed
  show "\<And> v. v \<in> \<V> \<Longrightarrow> \<pi> v = \<pi>' v"
  proof -
    fix v assume vV: "v \<in> \<V>"
    have GTne: "GT \<noteq> {}" using vV VsGTeq by(auto simp add: Vs_def)
    have VsGT_arb: "Vs GT = connected_component GT r"
      using graph_abs.arborescenceD(2)[OF gaT arbT GTne] by simp
    have rVs: "r \<in> Vs GT" using VsGT_arb in_own_connected_component by auto
    have vcc: "v \<in> connected_component GT r" using vV VsGTeq VsGT_arb by simp
    obtain p where walk: "walk_betw GT r p v"
      by (rule in_connected_component_has_walk[OF vcc rVs])
    have "r \<in> W \<longrightarrow> v \<in> W" using walk
    proof(induct rule: induct_walk_betw)
      case (path1 u)
      thus ?case by simp
    next
      case (path2 u u' vs b)
      show ?case
      proof
        assume "u \<in> W"
        hence "u' \<in> W" using closed "path2.hyps"(1) by blast
        thus "b \<in> W" using "path2.hyps"(3) by simp
      qed
    qed
    hence "v \<in> W" using rW by simp
    thus "\<pi> v = \<pi>' v" by(simp add: W_def)
  qed
qed
end
end