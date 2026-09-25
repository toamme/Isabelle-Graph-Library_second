theory Spanning_Tree_Flow
  imports Flow_Theory.Cost_Optimality Spanning_Trees.Arborescense
begin

context graph_abs
begin

text ‹Any finite non-empty acyclic (undirected) graph, i.e. a non-empty forest, contains a
      vertex of degree one, a so-called leaf. The proof is a counting argument: by the
      handshaking lemma the degrees sum up to twice the number of edges, while a forest has
      strictly more vertices than edges. Hence not every vertex can have degree ≥ 2.›

lemma tree_has_leaf:
  assumes "has_no_cycle T" "T ≠ {}"
  shows "∃ v. v ∈ Vs T ∧ degree T v = 1"
proof(rule ccontr)
  assume contr: "∄ v. v ∈ Vs T ∧ degree T v = 1"
  have TsubG: "T ⊆ G" using assms(1) has_no_cycle_indep_subset_carrier by simp
  have giT: "graph_invar T" using graph_invar_subset[OF graph TsubG] by simp
  have dblT: "⋀ e. e ∈ T ⟹ ∃u v. e = {u, v} ∧ u ≠ v"
    using giT by (auto simp add: dblton_graph_def dest: graph_invar_dblton)
  have finVsT: "finite (Vs T)" using giT graph_invar_finite_Vs by simp
  have hs: "sum (degree T) (Vs T) = enat (2 * card T)"
    using bigraph_handshaking_lemma[OF giT] by simp
  have cc: "card (Vs T) = card T + card (connected_components T)"
    using connected_components_card[OF assms(1) dblT] by simp
  have VsT_ne: "Vs T ≠ {}" using card_of_non_empty_graph_geq_2[OF giT assms(2)] by auto
  have enat_ge2: "⋀ x::enat. 1 ≤ x ⟹ x ≠ 1 ⟹ 2 ≤ x"
  proof -
    fix x :: enat assume a1: "1 ≤ x" and a2: "x ≠ 1"
    show "2 ≤ x"
    proof(cases x)
      case (enat n)
      from a1 enat have n1: "1 ≤ n" by (metis one_enat_def enat_ord_simps(1))
      from a2 enat have "n ≠ 1" by (metis one_enat_def)
      with n1 have "2 ≤ n" by simp
      thus "2 ≤ x" using enat by (metis numeral_eq_enat enat_ord_simps(1))
    next
      case infinity
      thus "2 ≤ x" by simp
    qed
  qed
  have deg2: "⋀ v. v ∈ Vs T ⟹ (2::enat) ≤ degree T v"
  proof -
    fix v assume v: "v ∈ Vs T"
    show "(2::enat) ≤ degree T v"
      using degree_Vs[OF v] contr v enat_ge2 by blast
  qed
  have consum: "sum (λ v. (2::enat)) (Vs T) = enat (2 * card (Vs T))"
    using finVsT by (simp add: numeral_eq_enat of_nat_eq_enat mult.commute)
  have "enat (2 * card (Vs T)) = sum (λ v. (2::enat)) (Vs T)" using consum by simp
  also have "… ≤ sum (degree T) (Vs T)" by (intro sum_mono deg2)
  also have "… = enat (2 * card T)" using hs by simp
  finally have le: "card (Vs T) ≤ card T" by (simp add: enat_ord_simps)
  have "connected_components T ≠ {}"
  proof -
    obtain v0 where "v0 ∈ Vs T" using VsT_ne by auto
    hence "connected_component T v0 ∈ connected_components T"
      by (auto simp add: connected_components_def)
    thus ?thesis by auto
  qed
  hence "card (connected_components T) ≥ 1"
    using finite_con_comps[OF finVsT] by (simp add: card_gt_0_iff Suc_leI)
  thus False using cc le by simp
qed

end

context
cost_flow_network
begin


definition "spanning_tree_partition r T L U =
    (ℰ = T ∪ U ∪ L ∧ T ∩ U = {} ∧ T ∩ L = {} ∧ L ∩ U = {} ∧
      graph_abs.arborescence ((λ e. {fst e, snd e} ) ` T) r ((λ e. {fst e, snd e})  ` T)
      ∧  graph_abs ((λ e. {fst e, snd e} ) ` T) ∧
      (∀ e e'. {e, e'} ⊆ T ∧ {fst e, snd e} = {fst e', snd e'} ⟶ e = e') ∧
      dVs (make_pair ` T) = 𝒱 )"

definition "flow_fits_spanning_tree_partition T L U f =
    ((∀ e ∈ L. f e = 0) ∧ (∀ e ∈ U. ereal (f e) = 𝗎 e))"

definition "potential_fits_spanning_tree_partition r T π =
       (π r = 0 ∧ (∀ e ∈ T. 𝖼 e + π (fst e) - π (snd e) = 0))"

text ‹At a fixed vertex @{term a}, the excess of a flow is a signed sum of the flow values on the
      edges incident to @{term a}. If two flows agree on all incident edges but one, and they have
      the same excess at @{term a}, then they must also agree on that last edge.›

lemma excess_determines_edge:
  assumes e0E: "e0 ∈ ℰ" and ain: "a = fst e0 ∨ a = snd e0" and dist: "fst e0 ≠ snd e0"
    and agp: "⋀ e. e ∈ ℰ ⟹ e ≠ e0 ⟹ fst e = a ⟹ f e = f' e"
    and agm: "⋀ e. e ∈ ℰ ⟹ e ≠ e0 ⟹ snd e = a ⟹ f e = f' e"
    and exeq: "(ex⇘f⇙ a) = (ex⇘f'⇙ a)"
  shows "f e0 = f' e0"
proof -
  have finE: "finite ℰ" using finite_E by simp
  have finp: "finite (δ⇧+ a)" using finE by (auto simp add: delta_plus_def)
  have finm: "finite (δ⇧- a)" using finE by (auto simp add: delta_minus_def)
  have sump: "(∑ e∈δ⇧+ a. f e - f' e) = (∑ e∈δ⇧+ a ∩ {e0}. f e - f' e)"
    using agp finp by (intro sum.mono_neutral_right) (auto simp add: delta_plus_def)
  have summ: "(∑ e∈δ⇧- a. f e - f' e) = (∑ e∈δ⇧- a ∩ {e0}. f e - f' e)"
    using agm finm by (intro sum.mono_neutral_right) (auto simp add: delta_minus_def)
  have exdiff: "(ex⇘f⇙ a) - (ex⇘f'⇙ a) = (∑ e∈δ⇧- a. f e - f' e) - (∑ e∈δ⇧+ a. f e - f' e)"
    by (simp add: ex_def sum_subtractf)
  show "f e0 = f' e0"
    using ain
  proof
    assume af: "a = fst e0"
    hence e0p: "δ⇧+ a ∩ {e0} = {e0}" using e0E by (auto simp add: delta_plus_def)
    have e0m: "δ⇧- a ∩ {e0} = {}" using dist af by (auto simp add: delta_minus_def)
    have "(ex⇘f⇙ a) - (ex⇘f'⇙ a) = - (f e0 - f' e0)"
      using exdiff sump summ e0p e0m by simp
    thus "f e0 = f' e0" using exeq by simp
  next
    assume as: "a = snd e0"
    hence e0m: "δ⇧- a ∩ {e0} = {e0}" using e0E by (auto simp add: delta_minus_def)
    have e0p: "δ⇧+ a ∩ {e0} = {}" using dist as by (auto simp add: delta_plus_def)
    have "(ex⇘f⇙ a) - (ex⇘f'⇙ a) = (f e0 - f' e0)"
      using exdiff sump summ e0p e0m by simp
    thus "f e0 = f' e0" using exeq by simp
  qed
qed

text ‹Given a spanning-tree partition, the flow on the tree edges is uniquely determined by the
      balance @{term b}. We prove this by peeling off leaves of the (sub-)forest one at a time: a
      non-empty forest has a leaf @{term a}, all edges incident to @{term a} except its unique tree
      edge already agree, and the balance constraint at @{term a} then pins down the last one via
      @{thm [source] excess_determines_edge}.  The induction runs over arbitrary sub-forests, so no
      root bookkeeping is needed; instantiating it with ‹S = T› settles all tree edges at once.›

lemma spanning_flow_unique:
  assumes "f is b flow" "f' is b flow"
          "spanning_tree_partition r T L U"
          "flow_fits_spanning_tree_partition T L U f"
          "flow_fits_spanning_tree_partition T L U f'"
    shows "⋀ e. e ∈ ℰ ⟹ f e = f' e"
proof -
  define GT where "GT = (λ e. {fst e, snd e}) ` T"
  have EE: "ℰ = T ∪ U ∪ L" and gaT: "graph_abs GT"
   and arbT: "graph_abs.arborescence GT r GT"
   and injT: "⋀ e e'. e ∈ T ⟹ e' ∈ T ⟹ {fst e, snd e} = {fst e', snd e'} ⟹ e = e'"
   and VsGT: "dVs (make_pair ` T) = 𝒱"
    using assms(3) by(auto simp add: spanning_tree_partition_def GT_def)
  have LUf: "⋀ e. e ∈ L ⟹ f e = 0" "⋀ e. e ∈ U ⟹ f e = 𝗎 e"
   and LUf': "⋀ e. e ∈ L ⟹ f' e = 0" "⋀ e. e ∈ U ⟹ f' e = 𝗎 e"
    using assms(4,5) by(auto simp add: flow_fits_spanning_tree_partition_def)
  have hncT: "graph_abs.has_no_cycle GT GT"
    using graph_abs.arborescenceD(1)[OF gaT arbT] by simp
  have TE: "T ⊆ ℰ" using EE by auto
  have bal: "⋀ v. v ∈ 𝒱 ⟹ (ex⇘f⇙ v) = (ex⇘f'⇙ v)"
  proof -
    fix v assume vV: "v ∈ 𝒱"
    have "- (ex⇘f⇙ v) = b v" using assms(1) vV by(auto elim!: isbflowE)
    moreover have "- (ex⇘f'⇙ v) = b v" using assms(2) vV by(auto elim!: isbflowE)
    ultimately show "(ex⇘f⇙ v) = (ex⇘f'⇙ v)" by simp
  qed
  have VsGTeq: "Vs GT = 𝒱"
  proof -
    have "Vs GT = ⋃ {{fst e, snd e} | e. e ∈ T}"
      by (auto simp add: GT_def Vs_def)
    also have "… = dVs (make_pair ` T)"
      by (auto simp add: dVs_def make_pair_def)
    finally show ?thesis using VsGT by simp
  qed
  have key: "⋀ S. S ⊆ T ⟹ (∀ x ∈ ℰ. x ∉ S ⟶ f x = f' x) ⟹ (∀ e ∈ S. f e = f' e)"
  proof -
    fix S
    show "S ⊆ T ⟹ (∀ x ∈ ℰ. x ∉ S ⟶ f x = f' x) ⟹ (∀ e ∈ S. f e = f' e)"
    proof(induct "card S" arbitrary: S rule: less_induct)
      case (less S)
      show ?case
      proof(cases "S = {}")
        case True
        thus ?thesis by simp
      next
        case False
        have ST: "S ⊆ T" using less.prems by blast
        have out: "⋀ x. x ∈ ℰ ⟹ x ∉ S ⟹ f x = f' x" using less.prems by blast
        have finT: "finite T" using finite_subset[OF TE finite_E] by simp
        have finS: "finite S" using finite_subset[OF ST finT] by simp
        have imgS_sub: "(λ e. {fst e, snd e}) ` S ⊆ GT" using ST by(auto simp add: GT_def)
        have hncS: "graph_abs.has_no_cycle GT ((λ e. {fst e, snd e}) ` S)"
          using graph_abs.has_no_cycle_indep_subset[OF gaT hncT imgS_sub] by simp
        have imgS_ne: "(λ e. {fst e, snd e}) ` S ≠ {}" using ‹S ≠ {}› by simp
        obtain a where aVs: "a ∈ Vs ((λ e. {fst e, snd e}) ` S)"
                   and adeg: "degree ((λ e. {fst e, snd e}) ` S) a = 1"
          using graph_abs.tree_has_leaf[OF gaT hncS imgS_ne] by auto
        from degree_one_unique[OF adeg]
        obtain Ea where EaS: "Ea ∈ (λ e. {fst e, snd e}) ` S" and aEa: "a ∈ Ea"
          and Ea_uniq: "⋀ E'. E' ∈ (λ e. {fst e, snd e}) ` S ⟹ a ∈ E' ⟹ E' = Ea"
          by (auto elim!: ex1E)
        obtain ea where eaS: "ea ∈ S" and Eaea: "Ea = {fst ea, snd ea}" using EaS by auto
        have a_in_ea: "a ∈ {fst ea, snd ea}" using aEa Eaea by simp
        have Ea_GT: "Ea ∈ GT" using EaS imgS_sub by auto
        have dist_ea: "fst ea ≠ snd ea"
          using graph_invar_edgeD[OF graph_abs.graph[OF gaT]] Ea_GT Eaea by auto
        have aV: "a ∈ 𝒱" using aVs Vs_subset[OF imgS_sub] VsGTeq by auto
        have agree_other: "⋀ e. e ∈ ℰ ⟹ e ≠ ea ⟹ a ∈ {fst e, snd e} ⟹ f e = f' e"
        proof -
          fix e assume eE: "e ∈ ℰ" and ene: "e ≠ ea" and ain: "a ∈ {fst e, snd e}"
          show "f e = f' e"
          proof(cases "e ∈ S")
            case True
            hence eT: "e ∈ T" using ST by auto
            have "{fst e, snd e} ∈ (λ e. {fst e, snd e}) ` S" using True by auto
            hence "{fst e, snd e} = Ea" using Ea_uniq ain by auto
            hence "{fst e, snd e} = {fst ea, snd ea}" using Eaea by simp
            hence "e = ea" using injT[OF eT] eaS ST by auto
            thus ?thesis using ene by simp
          next
            case False
            thus ?thesis using out eE by simp
          qed
        qed
        have agp: "⋀ e. e ∈ ℰ ⟹ e ≠ ea ⟹ fst e = a ⟹ f e = f' e"
          by (metis agree_other insert_iff)
        have agm: "⋀ e. e ∈ ℰ ⟹ e ≠ ea ⟹ snd e = a ⟹ f e = f' e"
          by (metis agree_other insert_iff)
        have eaE: "ea ∈ ℰ" using eaS ST TE by auto
        have ain_ea: "a = fst ea ∨ a = snd ea" using a_in_ea by auto
        have exeq_a: "(ex⇘f⇙ a) = (ex⇘f'⇙ a)" using bal[OF aV] by blast
        have fea: "f ea = f' ea"
          by (rule excess_determines_edge[OF eaE ain_ea dist_ea agp agm exeq_a])
        have subS: "S - {ea} ⊆ T" using ST by auto
        have cardlt: "card (S - {ea}) < card S" using card_Diff1_less[OF finS eaS] by simp
        have out': "∀ x ∈ ℰ. x ∉ S - {ea} ⟶ f x = f' x" using out fea by auto
        have "∀ e ∈ S - {ea}. f e = f' e" using less.hyps[OF cardlt subS out'] by simp
        thus "∀ e ∈ S. f e = f' e" using fea by auto
      qed
    qed
  qed
  have outT: "∀ x ∈ ℰ. x ∉ T ⟶ f x = f' x"
  proof(intro ballI impI)
    fix x assume xE: "x ∈ ℰ" and xnT: "x ∉ T"
    from xE xnT EE have "x ∈ U ∨ x ∈ L" by auto
    thus "f x = f' x"
    proof
      assume "x ∈ U"
      thus ?thesis using LUf(2) LUf'(2) by (metis ereal.inject)
    next
      assume "x ∈ L"
      thus ?thesis using LUf(1) LUf'(1) by simp
    qed
  qed
  have onT: "∀ e ∈ T. f e = f' e" using key[OF subset_refl outT] by simp
  show "⋀ e. e ∈ ℰ ⟹ f e = f' e" using onT outT by blast
qed

text ‹The vertex potentials are unique, too. Consider the set of vertices on which the two
      potentials π and π' agree. The root r belongs to it, since both potentials vanish at r. This
      set is closed along the tree edges: subtracting the two reduced-cost constraints
      ‹𝖼 e + π (fst e) + π (snd e) = 0› and ‹𝖼 e + π' (fst e) + π' (snd e) = 0› of a tree edge e
      shows that the potential differences at its two endpoints are negatives of one another, so
      whenever one endpoint agrees the other must agree as well. Since the tree is a spanning
      arborescence around r, every vertex of 𝒱 is joined to r by a walk in the tree; propagating
      agreement edge by edge along that walk shows the two potentials coincide at the vertex.›

lemma spanning_potential_unqiue:
  assumes "spanning_tree_partition r T L U"
      "potential_fits_spanning_tree_partition r T π" 
      "potential_fits_spanning_tree_partition r T π'"
    shows "⋀ v. v ∈ 𝒱 ⟹ π v = π' v"
proof -
  define GT where "GT = (λ e. {fst e, snd e}) ` T"
  have gaT: "graph_abs GT" and arbT: "graph_abs.arborescence GT r GT"
   and VsGT: "dVs (make_pair ` T) = 𝒱"
    using assms(1) by(auto simp add: spanning_tree_partition_def GT_def)
  have piR: "π r = 0" and edgeqA: "⋀ e. e ∈ T ⟹ 𝖼 e + π (fst e) - π (snd e) = 0"
    using assms(2) by(auto simp add: potential_fits_spanning_tree_partition_def)
  have piR': "π' r = 0" and edgeqB: "⋀ e. e ∈ T ⟹ 𝖼 e + π' (fst e) - π' (snd e) = 0"
    using assms(3) by(auto simp add: potential_fits_spanning_tree_partition_def)
  have VsGTeq: "Vs GT = 𝒱"
  proof -
    have "Vs GT = ⋃ {{fst e, snd e} | e. e ∈ T}"
      by (auto simp add: GT_def Vs_def)
    also have "… = dVs (make_pair ` T)"
      by (auto simp add: dVs_def make_pair_def)
    finally show ?thesis using VsGT by simp
  qed
  define W where "W = {x. π x = π' x}"
  have rW: "r ∈ W" using piR piR' by(simp add: W_def)
  have closed: "⋀ x y. {x, y} ∈ GT ⟹ x ∈ W ⟹ y ∈ W"
  proof -
    fix x y assume xy: "{x, y} ∈ GT" and xW: "x ∈ W"
    from xy obtain e where eT: "e ∈ T" and exy: "{fst e, snd e} = {x, y}"
      by(auto simp add: GT_def)
    have px: "π x = π' x" using xW by(simp add: W_def)
    have keyeq: "(π (fst e) - π' (fst e)) - (π (snd e) - π' (snd e)) = 0"
      using edgeqA[OF eT] edgeqB[OF eT] by auto
    from exy have "fst e = x ∧ snd e = y ∨ fst e = y ∧ snd e = x"
      by (metis doubleton_eq_iff)
    thus "y ∈ W"
    proof
      assume "fst e = x ∧ snd e = y"
      hence "(π x - π' x) - (π y - π' y) = 0" using keyeq by simp
      thus ?thesis using px by(simp add: W_def)
    next
      assume "fst e = y ∧ snd e = x"
      hence "(π y - π' y) - (π x - π' x) = 0" using keyeq by simp
      thus ?thesis using px by(simp add: W_def)
    qed
  qed
  show "⋀ v. v ∈ 𝒱 ⟹ π v = π' v"
  proof -
    fix v assume vV: "v ∈ 𝒱"
    have GTne: "GT ≠ {}" using vV VsGTeq by(auto simp add: Vs_def)
    have VsGT_arb: "Vs GT = connected_component GT r"
      using graph_abs.arborescenceD(2)[OF gaT arbT GTne] by simp
    have rVs: "r ∈ Vs GT" using VsGT_arb in_own_connected_component by auto
    have vcc: "v ∈ connected_component GT r" using vV VsGTeq VsGT_arb by simp
    obtain p where walk: "walk_betw GT r p v"
      by (rule in_connected_component_has_walk[OF vcc rVs])
    have "r ∈ W ⟶ v ∈ W" using walk
    proof(induct rule: induct_walk_betw)
      case (path1 u)
      thus ?case by simp
    next
      case (path2 u u' vs b)
      show ?case
      proof
        assume "u ∈ W"
        hence "u' ∈ W" using closed "path2.hyps"(1) by blast
        thus "b ∈ W" using "path2.hyps"(3) by simp
      qed
    qed
    hence "v ∈ W" using rW by simp
    thus "π v = π' v" by(simp add: W_def)
  qed
qed
end
end