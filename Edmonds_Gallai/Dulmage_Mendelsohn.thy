theory Dulmage_Mendelsohn
  imports Edmonds_Gallai
begin

provenance ai_human

section \<open>Bipartite specialization of Edmonds--Gallai\<close>

text \<open>We retain the inessential vertices and their neighbourhood from
  Edmonds--Gallai. Factor-criticality is expressed by near-perfect matchings,
  as in that decomposition. In a bipartite graph its odd components are
  singletons.\<close>

lemma bipartite_factor_critical_singleton:
  assumes "finite X" "bipartite G L R" "r \<in> X"
    "\<And>x. x \<in> X \<Longrightarrow> \<exists>M. graph_matching G M \<and> Vs M = X - {x}"
  shows "X = {r}"
proof-
  have balance: "card ((X - {x}) \<inter> L) = card ((X - {x}) \<inter> R)" if "x \<in> X" for x
    using assms(4)[of x] that
    by (auto dest: bipartite_same_matcheds_on_both_sides[OF assms(2) conjI])
  have "X \<inter> L = {} \<or> X \<inter> R = {}"
  proof(rule ccontr)
    assume "\<not> (X \<inter> L = {} \<or> X \<inter> R = {})"
    then obtain u v where "u \<in> X" "u \<in> L" "v \<in> X" "v \<in> R"
      by blast
    hence "card (X \<inter> L) - 1 = card (X \<inter> R)"
      "card (X \<inter> L) = card (X \<inter> R) - 1"
      using bipartite_disjointD[of G L R] bipartite_disjointD[of G R L]
        bipartite_commute[of G L R] assms(2) balance[of u] balance[of v]
        \<open>u \<in> X\<close> \<open>u \<in> L\<close>
        \<open>v \<in> X\<close> \<open>v \<in> R\<close>
      by (auto simp: Diff_Int_distrib2 card_Diff_singleton_if disjoint_iff)+
    moreover have "0 < card (X \<inter> L)"
      using assms(1) \<open>u \<in> X\<close> \<open>u \<in> L\<close>
      by (auto simp: card_gt_0_iff)
    ultimately show False
      by arith
  qed
  obtain M where "matching M" "M \<subseteq> G" "Vs M = X - {r}"
    using assms(3,4)
    by blast
  have "M = {}"
  proof(rule ccontr)
    assume "M \<noteq> {}"
    then obtain u v where "{u,v} \<in> M" "u \<in> L" "v \<in> R"
      using bipartite_subgraph[OF assms(2) \<open>M \<subseteq> G\<close>]
      by (fastforce simp only: bipartite_def)
    thus False
      using \<open>Vs M = X - {r}\<close> \<open>X \<inter> L = {} \<or> X \<inter> R = {}\<close>
      by (auto simp: Vs_def)
  qed
  thus ?thesis
    using \<open>Vs M = X - {r}\<close> assms(3)
    by (auto simp: Vs_def)
qed

lemma bipartite_edmonds_gallai_component:
  assumes "graph_invar G" "bipartite G L R" "D \<in> \<oo>\<cc> G (\<A> G)" "x \<in> D"
  shows "D = {x}"
  using assms edmonds_gallai_decomposition_general(1)[of G D]
    diff_odd_compoenent_has_odd_card[of D G "\<A> G"]
    bipartite_subgraph[OF assms(2) graph_inter_Vs_subset(1), of D]
  by (intro bipartite_factor_critical_singleton[where G = "G \<lbrakk>D\<rbrakk>" and L = L and R = R])
    (auto dest: card.infinite)

lemma bipartite_edmonds_gallai_singleton:
  assumes "graph_invar G" "bipartite G L R"
  shows "{x} \<in> \<oo>\<cc> G (\<A> G) \<longleftrightarrow> x \<in> \<I> G"
  using assms edmonds_gallai_decomposition_general(5)[of G]
  by (blast dest: bipartite_edmonds_gallai_component[OF assms, where x = x])

lemma bipartite_edmonds_gallai_components:
  assumes "graph_invar G" "bipartite G L R"
  shows "\<oo>\<cc> G (\<A> G) = (\<lambda>x. {x}) ` \<I> G"
proof-
  have "\<exists>x. D = {x}" if "D \<in> \<oo>\<cc> G (\<A> G)" for D
    using assms that bipartite_edmonds_gallai_component[where G = G and L = L and R = R and D = D]
      diff_odd_compoenent_has_odd_card[of D G "\<A> G"]
    by (cases "D = {}") auto
  thus ?thesis
    using assms
    by (force simp: bipartite_edmonds_gallai_singleton[where L = L and R = R])
qed

lemma bipartite_inessentials_edge:
  assumes "graph_invar G" "bipartite G L R" "{x,y} \<in> G" "x \<in> \<I> G"
  shows "y \<in> \<A> G"
  using assms adj_inessentials_disjoint[of G]
  by (elim edmonds_gallai_decomposition_general(6)[OF assms(1)];
    auto simp: bipartite_edmonds_gallai_components[OF assms(1,2)]
      doubleton_eq_iff dblton_graph_def; blast)

lemma bipartite_max_matching_edge:
  assumes "graph_invar G" "bipartite G L R" "max_card_matching G M" "{x,y} \<in> M"
  shows "(x \<in> \<A> G \<and> y \<in> \<I> G) \<or> (y \<in> \<A> G \<and> x \<in> \<I> G) \<or>
    {x,y} \<subseteq> Vs G - \<I> G - \<A> G"
  using assms(1,4) max_card_matchingDs(1)[OF assms(3)]
  by (elim edmonds_gallai_decomposition_all(7)[OF assms(1,3)]; auto
    simp: bipartite_edmonds_gallai_components[OF assms(1,2)]
      doubleton_eq_iff dblton_graph_def; fastforce)

lemma bipartite_max_matching_remainder:
  assumes "graph_invar G" "bipartite G L R" "max_card_matching G M"
  shows "Vs (M \<lbrakk>Vs G - \<I> G - \<A> G\<rbrakk>) = Vs G - \<I> G - \<A> G"
proof-
  have "x \<in> Vs (M \<lbrakk>Vs G - \<I> G - \<A> G\<rbrakk>)"
    if "x \<in> Vs G - \<I> G - \<A> G" for x
  proof-
    have "x \<in> Vs M"
      using that assms(3)
      by (auto simp: inessentials_def inessential_def)
    then obtain y where "{x,y} \<in> M"
      using assms(1) max_card_matchingDs(1)[OF assms(3)]
      by (auto elim: graph_invar_vertex_edgeE[OF graph_invar_subset[OF assms(1)]])
    thus ?thesis
      using that bipartite_max_matching_edge[OF assms, of x y]
      by (auto simp: Vs_def graph_inter_Vs_def)
  qed
  thus ?thesis
    using graph_inter_Vs_subset(2)[of M "Vs G - \<I> G - \<A> G"]
    by blast
qed

lemma bipartite_remainder_vertices:
  assumes "graph_invar G" "bipartite G L R"
  shows "Vs (G \<lbrakk>Vs G - \<I> G - \<A> G\<rbrakk>) = Vs G - \<I> G - \<A> G"
proof-
  obtain M where "max_card_matching G M"
    using assms(1)
    by (auto dest: finite_Vs_then_finite elim!: max_card_matching_exists)
  thus ?thesis
    using bipartite_max_matching_remainder[OF assms, of M]
      graph_inter_Vs_subset(2)[of G "Vs G - \<I> G - \<A> G"]
      max_card_matchingDs(1)[THEN graph_inter_subset, THEN Vs_subset, of G M "Vs G - \<I> G - \<A> G"]
    by blast
qed

lemma bipartite_remainder_perfect_matching:
  assumes "graph_invar G" "bipartite G L R" "max_card_matching G M"
  shows "perfect_matching (G \<lbrakk>Vs G - \<I> G - \<A> G\<rbrakk>)
    (M \<lbrakk>Vs G - \<I> G - \<A> G\<rbrakk>)"
proof-
  have "H \<lbrakk>Vs G - \<I> G - \<A> G\<rbrakk> = H \<setminus> (\<I> G \<union> \<A> G)"
    if "H \<subseteq> G" for H
    using that
    by (auto simp: graph_inter_Vs_def remove_vertices_graph_def Vs_def)
  thus ?thesis
    using assms edmonds_gallai_decomposition_all(3,8)[of G M]
    by (simp add: max_card_matchingDs(1))
qed

lemma bipartite_remainder_balanced:
  assumes "graph_invar G" "bipartite G L R"
  shows "card ((Vs G - \<I> G - \<A> G) \<inter> L) =
    card ((Vs G - \<I> G - \<A> G) \<inter> R)"
proof-
  obtain M where "max_card_matching G M"
    using assms(1)
    by (auto dest: finite_Vs_then_finite elim!: max_card_matching_exists)
  have "graph_matching G (M \<lbrakk>Vs G - \<I> G - \<A> G\<rbrakk>)"
    using \<open>max_card_matching G M\<close>
    by (auto simp: graph_inter_Vs_def intro: matching_subgraph dest: max_card_matchingDs(1,2))
  thus ?thesis
    using assms \<open>max_card_matching G M\<close>
      bipartite_same_matcheds_on_both_sides[of G L R "M \<lbrakk>Vs G - \<I> G - \<A> G\<rbrakk>"]
    by (simp add: bipartite_max_matching_remainder)
qed

section \<open>Coarse decomposition\<close>

lemma bipartite_inessential_region_matching:
  assumes "graph_invar G" "bipartite G L R" "max_card_matching G M"
  shows "cover_matching (G \<lbrakk>(\<I> G \<inter> L) \<union> (\<A> G \<inter> R)\<rbrakk>)
    (M \<lbrakk>(\<I> G \<inter> L) \<union> (\<A> G \<inter> R)\<rbrakk>) (\<A> G \<inter> R)"
proof-
  obtain m where "image m (\<A> G) \<subseteq> \<I> G" "\<forall>x\<in>\<A> G. {x,m x} \<in> M"
    using assms edmonds_gallai_decomposition_all(5,8)[of G M]
    by auto
  hence "\<A> G \<inter> R \<subseteq> Vs (M \<lbrakk>(\<I> G \<inter> L) \<union> (\<A> G \<inter> R)\<rbrakk>)"
    using assms(2,3) max_card_matchingDs(1)[of G M]
    by (fastforce simp: Vs_def graph_inter_Vs_def dest: bipartite_edgeD(2))
  thus ?thesis
    using graph_matching_inter_Vs[where G = G and M = M] assms(3)
    by (auto simp: cover_matching_def dest: max_card_matchingDs(1,2))
qed

lemma dulmage_mendelsohn_coarse_partition:
  fixes G :: "'a graph" and L R I C D_L D_R :: "'a set"
  assumes "bipartite G L R"
  defines "I \<equiv> {x \<in> L \<union> R. inessential G x}"
    and "C \<equiv> L \<union> R - I - \<A> G"
    and "D_L \<equiv> (I \<inter> L) \<union> (\<A> G \<inter> R)"
    and "D_R \<equiv> (I \<inter> R) \<union> (\<A> G \<inter> L)"
  shows "D_L \<union> D_R \<union> C = L \<union> R"
    "D_L \<inter> D_R = {}" "D_L \<inter> C = {}" "D_R \<inter> C = {}"
    "D_L \<inter> L = I \<inter> L" "D_L \<inter> R = \<A> G \<inter> R"
    "D_R \<inter> R = I \<inter> R" "D_R \<inter> L = \<A> G \<inter> L"
  using assms(1) bipartite_vs_subset[of G L R] adj_inessentialsin_G[of G]
  by (auto simp: I_def C_def D_L_def D_R_def bipartite_def
    adj_inessentials_def Neighbourhood_def inessentials_def)

theorem dulmage_mendelsohn_max_matching:
  fixes G M :: "'a graph" and L R I C D_L D_R :: "'a set"
  assumes "finite L" "finite R" "bipartite G L R" "max_card_matching G M"
  defines "I \<equiv> {x \<in> L \<union> R. inessential G x}"
    and "C \<equiv> L \<union> R - I - \<A> G"
    and "D_L \<equiv> (I \<inter> L) \<union> (\<A> G \<inter> R)"
    and "D_R \<equiv> (I \<inter> R) \<union> (\<A> G \<inter> L)"
  shows "cover_matching (G \<lbrakk>D_L\<rbrakk>) (M \<lbrakk>D_L\<rbrakk>) (\<A> G \<inter> R)"
    "cover_matching (G \<lbrakk>D_R\<rbrakk>) (M \<lbrakk>D_R\<rbrakk>) (\<A> G \<inter> L)"
    "perfect_matching (G \<lbrakk>C\<rbrakk>) (M \<lbrakk>C\<rbrakk>)"
    "Vs (M \<lbrakk>C\<rbrakk>) = C"
    "card (C \<inter> L) = card (C \<inter> R)"
  using assms(1-4) finite_parts_bipartite_graph_invar[of L R G]
    bipartite_vs_subset[of G L R] max_card_matchingDs(1)[of G M]
    bipartite_commute[of G L R] bipartite_inessential_region_matching[of G L R M]
    bipartite_inessential_region_matching[of G R L M]
    bipartite_remainder_perfect_matching[of G L R M]
    bipartite_max_matching_remainder[of G L R M] bipartite_remainder_balanced[of G L R]
  by (auto simp only: I_def C_def D_L_def D_R_def inessential_region_graph_in_universe
    edmonds_gallai_remainder_in_universe finite_Vs_then_finite subset_refl)

lemma bipartite_matching_number:
  assumes "graph_invar G" "bipartite G L R"
  shows "\<nu> G = card (\<A> G) + card ((Vs G - \<I> G - \<A> G) \<inter> L)"
proof-
  let ?C = "Vs G - \<I> G - \<A> G"
  have "finite (\<I> G)" "finite (\<A> G)" "finite ?C"
    using assms(1) adj_inessentialsin_G[of G]
    by (auto simp: inessentials_def intro: finite_subset)
  have "(\<I> G \<union> \<A> G) \<union> ?C = Vs G"
    "\<I> G \<inter> \<A> G = {}" "(\<I> G \<union> \<A> G) \<inter> ?C = {}"
    using adj_inessentialsin_G[of G] adj_inessentials_disjoint[of G]
    by (auto simp: inessentials_def)
  hence "card (Vs G) = card (\<I> G) + card (\<A> G) + card ?C"
    using \<open>finite (\<I> G)\<close> \<open>finite (\<A> G)\<close> \<open>finite ?C\<close>
      card_Un_disjoint[of "\<I> G" "\<A> G"]
      card_Un_disjoint[of "\<I> G \<union> \<A> G" ?C]
    by simp
  moreover have "(?C \<inter> L) \<union> (?C \<inter> R) = ?C"
    "(?C \<inter> L) \<inter> (?C \<inter> R) = {}"
    using assms(2) bipartite_vs_subset[of G L R] bipartite_disjointD[of G L R]
    by auto
  hence "card ?C = 2 * card (?C \<inter> L)"
    using assms \<open>finite ?C\<close> bipartite_remainder_balanced[of G L R]
      card_Un_disjoint[of "?C \<inter> L" "?C \<inter> R"]
    by simp
  moreover have "card (\<oo>\<cc> G (\<A> G)) = card (\<I> G)"
    using assms
    by (simp add: bipartite_edmonds_gallai_components card_image inj_on_def)
  ultimately show ?thesis
    using assms(1) edmonds_gallai_decomposition_general(4)[of G]
    by (auto; linarith)
qed

lemma bipartite_inessentials_strict_hall:
  assumes "graph_invar G" "bipartite G L R" "X \<subseteq> \<A> G" "X \<noteq> {}"
  shows "card X < card (Neighbourhood G X \<inter> \<I> G)"
proof-
  have "{D. D \<in> image (\<lambda>x. {x}) (\<I> G) \<and> connected_set_of_vertices X G D} =
    image (\<lambda>x. {x}) (Neighbourhood G X \<inter> \<I> G)"
    using assms(3) adj_inessentials_disjoint[of G]
    by (auto simp: connected_set_of_vertices_def Neighbourhood_def; blast)
  moreover have "inj_on (\<lambda>x. {x}) (Neighbourhood G X \<inter> \<I> G)"
    by (auto simp: inj_on_def)
  ultimately show ?thesis
    using assms edmonds_gallai_decomposition_general(3)[of G X]
    by (simp add: bipartite_edmonds_gallai_components card_image)
qed

lemma bipartite_inessential_region_delete:
  assumes "graph_invar G" "bipartite G L R" "inessential G x"
  shows "\<exists>M. cover_matching
    ((G \<lbrakk>(\<I> G \<inter> L) \<union> (\<A> G \<inter> R)\<rbrakk>) \<setminus> {x})
    M (\<A> G \<inter> R)"
proof-
  obtain M where "max_card_matching G M" "x \<notin> Vs M"
    using assms(3)
    by (elim inessentialE)
  thus ?thesis
    using bipartite_inessential_region_matching[OF assms(1,2), of M]
    by (intro exI[of _ "M \<lbrakk>(\<I> G \<inter> L) \<union> (\<A> G \<inter> R)\<rbrakk>"])
      (auto simp: cover_matching_def remove_vertices_graph_def graph_inter_Vs_def Vs_def)
qed

section \<open>Possible maximum-matching edges and canonical components\<close>

text \<open>Possible maximum-matching edges occur in a maximum cardinality matching. The explicit
  vertex universe retains isolated vertices as singleton components.\<close>

definition max_match_components where
  "max_match_components G V = connected_components' V (possible_max_matching_edges G)"

lemma max_match_components_cover:
  "\<lbrakk>dblton_graph G; Vs G \<subseteq> V\<rbrakk> \<Longrightarrow>
    \<Union>(max_match_components G V) = V"
  using possible_max_matching_edges_subset[of G]
  by (auto simp: max_match_components_def Vs_def intro!: union_connected_components'; blast)

lemma dulmage_mendelsohn_component_nonempty:
  "C \<in> max_match_components G V \<Longrightarrow> C \<noteq> {}"
  by (simp add: max_match_components_def connected_component'_nonempty)

lemma max_match_components_disjoint:
  "\<lbrakk>C \<in> max_match_components G V;
    D \<in> max_match_components G V; C \<noteq> D\<rbrakk>
    \<Longrightarrow> C \<inter> D = {}"
  by (simp add: max_match_components_def connected_components'_disj)

lemma dulmage_mendelsohn_isolated_vertex:
  "x \<in> V - Vs G \<Longrightarrow> {x} \<in> max_match_components G V"
  using possible_max_matching_edges_subset[THEN Vs_subset, of G]
  by (auto simp: max_match_components_def connected_components'_def)

lemma dulmage_mendelsohn_empty_graph:
  "max_match_components {} V = (\<lambda>x. {x}) ` V"
  by (simp add: max_match_components_def connected_components'_def
    possible_max_matching_edges_empty connected_components_def comps_def)

lemma bipartite_inessential_edge_possible:
  assumes "graph_invar G" "bipartite G L R" "{x,y} \<in> G" "inessential G x"
  shows "{x,y} \<in> possible_max_matching_edges G"
proof-
  obtain M where "max_card_matching G M" "x \<notin> Vs M"
    using assms(4)
    by (elim inessentialE)
  have "y \<in> \<A> G"
    using assms
    by (intro bipartite_inessentials_edge[of G L R x y])
      (auto simp: inessentials_def intro: edges_are_Vs)
  hence "y \<in> Vs M"
    using \<open>max_card_matching G M\<close> adj_inessentialsin_G[of G]
      adj_inessentials_disjoint[of G]
    by (auto simp: inessentials_def inessential_def)
  then obtain e where "e \<in> M" "y \<in> e"
    by (auto simp: Vs_def)
  have "matching M" "M \<subseteq> G" "finite M"
    using \<open>max_card_matching G M\<close> assms(1)
    by (auto dest: max_card_matchingDs(1,2) finite_Vs_then_finite
      intro: finite_subset)
  have "graph_matching G (insert {x,y} (M - {e}))"
    using \<open>matching M\<close> \<open>M \<subseteq> G\<close> \<open>e \<in> M\<close>
      \<open>y \<in> e\<close> \<open>x \<notin> Vs M\<close> assms(3)
    by (auto intro!: matching_insert intro: matching_delete simp: remove_matching_edge_Vs)
  moreover have "{x,y} \<notin> M" "0 < card M"
    using \<open>x \<notin> Vs M\<close> \<open>finite M\<close> \<open>e \<in> M\<close>
    by (auto simp: card_gt_0_iff dest: edges_are_Vs)
  moreover have "card M = card (insert {x,y} (M - {e}))"
    using \<open>finite M\<close> \<open>e \<in> M\<close>
      \<open>{x,y} \<notin> M\<close> \<open>0 < card M\<close>
    by (simp add: card_Diff_singleton_if)
  ultimately have "max_card_matching G (insert {x,y} (M - {e}))"
    using \<open>max_card_matching G M\<close>
    by (blast intro: max_matching_if_same_card)
  thus ?thesis
    by (auto simp: possible_max_matching_edges_iff)
qed

lemma bipartite_possible_max_matching_edge:
  assumes "graph_invar G" "bipartite G L R" "{x,y} \<in> possible_max_matching_edges G"
  shows "(x \<in> \<A> G \<and> y \<in> \<I> G) \<or> (y \<in> \<A> G \<and> x \<in> \<I> G) \<or>
    {x,y} \<subseteq> Vs G - \<I> G - \<A> G"
  using assms(3)
  by (auto simp: possible_max_matching_edges_iff dest: bipartite_max_matching_edge[OF assms(1,2)])

lemma bipartite_inessential_region_possible:
  assumes "graph_invar G" "bipartite G L R"
  shows "(possible_max_matching_edges G
      \<lbrakk>(\<I> G \<inter> L) \<union> (\<A> G \<inter> R)\<rbrakk>) =
    (G \<lbrakk>(\<I> G \<inter> L) \<union> (\<A> G \<inter> R)\<rbrakk>)"
  using possible_max_matching_edges_subset[of G] assms(2)
  by (fastforce simp: graph_inter_Vs_def bipartite_def inessentials_def
    intro: bipartite_inessential_edge_possible[OF assms])

lemma max_match_components_possible_edges:
  "finite G \<Longrightarrow> max_match_components (possible_max_matching_edges G) V =
    max_match_components G V"
  by (simp add: max_match_components_def possible_max_matching_edges_idempotent)

lemma bipartite_possible_max_matching_delta:
  assumes "graph_invar G" "bipartite G L R"
  shows "Delta (possible_max_matching_edges G) ((\<I> G \<inter> L) \<union> (\<A> G \<inter> R)) = {}"
    "Delta (possible_max_matching_edges G) (Vs G - \<I> G - \<A> G) = {}"
  using assms(2) possible_max_matching_edges_subset[of G] adj_inessentials_disjoint[of G]
  by (auto simp: Delta_def
    dest: bipartite_possible_max_matching_edge[OF assms]
      bipartite_edgeD(1,2)[OF _ assms(2)])

theorem dulmage_mendelsohn_component_regions:
  fixes G :: "'a graph" and L R I C D_L D_R D :: "'a set"
  assumes "graph_invar G" "bipartite G L R"
    "D \<in> max_match_components G (L \<union> R)"
  defines "I \<equiv> {x \<in> L \<union> R. inessential G x}"
    and "C \<equiv> L \<union> R - I - \<A> G"
    and "D_L \<equiv> (I \<inter> L) \<union> (\<A> G \<inter> R)"
    and "D_R \<equiv> (I \<inter> R) \<union> (\<A> G \<inter> L)"
  shows "D \<subseteq> D_L \<or> D \<subseteq> D_R \<or> D \<subseteq> C"
proof-
  let ?E = "possible_max_matching_edges G"
  have "Vs ?E \<subseteq> L \<union> R"
    using possible_max_matching_edges_subset[THEN Vs_subset, of G]
      bipartite_vs_subset[of G L R] assms(2)
    by blast
  obtain x where "x \<in> L \<union> R" "D = connected_component ?E x"
    using assms(3) \<open>Vs ?E \<subseteq> L \<union> R\<close>
    by (auto simp: max_match_components_def connected_components'_aux_def comps_def)
  have "dblton_graph ?E"
    using assms(1) possible_max_matching_edges_subset[of G]
    by auto
  note deltas = bipartite_possible_max_matching_delta[OF assms(1)]
  have inessential: "u \<in> I \<longleftrightarrow> u \<in> \<I> G"
    "v \<in> I \<longleftrightarrow> v \<in> \<I> G" if "{u,v} \<in> ?E" for u v
    using that \<open>Vs ?E \<subseteq> L \<union> R\<close>
      possible_max_matching_edges_subset[THEN Vs_subset, of G]
    by (auto simp: I_def inessentials_def dest: edges_are_Vs edges_are_Vs_2)
  have "Delta ?E D_L = {}" "Delta ?E D_R = {}"
    using assms(2) deltas(1)[of L R] deltas(1)[of R L] bipartite_commute[of G L R]
    by (auto simp: D_L_def D_R_def Delta_def; blast dest: inessential)+
  moreover have "C = Vs G - \<I> G - \<A> G"
    using assms(1,2) bipartite_vs_subset[of G L R]
    unfolding C_def I_def
    by (intro edmonds_gallai_remainder_in_universe) (auto dest: finite_Vs_then_finite)
  hence "Delta ?E C = {}"
    using assms(2) deltas(2)[of L R]
    by simp
  moreover have "x \<in> D_L \<union> D_R \<union> C"
    using assms(2) dulmage_mendelsohn_coarse_partition(1)[of G L R]
      \<open>x \<in> L \<union> R\<close>
    by (simp add: I_def C_def D_L_def D_R_def)
  ultimately show ?thesis
    using \<open>D = connected_component ?E x\<close> \<open>dblton_graph ?E\<close>
      empty_delta_component_confined[of ?E D_L x]
      empty_delta_component_confined[of ?E D_R x]
      empty_delta_component_confined[of ?E C x]
    by auto
qed

lemma dulmage_mendelsohn_component_delta:
  "D \<in> max_match_components G V \<Longrightarrow>
    Delta (possible_max_matching_edges G) D = {}"
  by (auto simp: max_match_components_def
    connected_components'_aux_def comps_def component_Delta_empty)

lemma dulmage_mendelsohn_matching_vertices:
  assumes "dblton_graph G" "D \<in> max_match_components G V"
    "max_card_matching G M"
  shows "Vs (M \<lbrakk>D\<rbrakk>) = Vs M \<inter> D"
  using assms max_matching_subset_possible_edges[of G M]
    dblton_graph_subset[OF assms(1) possible_max_matching_edges_subset]
  by (intro subgraph_component_vertices[where G = "possible_max_matching_edges G" and V = V])
    (auto simp: max_match_components_def)

lemma dulmage_mendelsohn_component_matching:
  assumes "graph_invar G" "D \<in> max_match_components G V"
    "max_card_matching G M"
  shows "max_card_matching (G \<lbrakk>D\<rbrakk>) (M \<lbrakk>D\<rbrakk>)"
  using assms dulmage_mendelsohn_matching_vertices[of G D V M]
  by (intro max_card_matching_restrict) (auto dest: finite_Vs_then_finite)

lemma dulmage_mendelsohn_component_exchange:
  assumes "graph_invar G" "D \<in> max_match_components G V"
    "max_card_matching G M" "max_card_matching (G \<lbrakk>D\<rbrakk>) N"
  shows "max_card_matching G ((M - (M \<lbrakk>D\<rbrakk>)) \<union> N)"
  using assms dulmage_mendelsohn_matching_vertices[of G D V M]
  by (intro max_card_matching_exchange) (auto dest: finite_Vs_then_finite)

lemma possible_max_matching_edges_restrict:
  assumes "graph_invar G" "D \<in> max_match_components G V"
  shows "possible_max_matching_edges (G \<lbrakk>D\<rbrakk>) =
    (possible_max_matching_edges G \<lbrakk>D\<rbrakk>)"
proof-
  obtain M where "max_card_matching G M"
    using assms(1)
    by (auto dest: finite_Vs_then_finite elim!: max_card_matching_exists)
  have "e \<in> possible_max_matching_edges G" if "max_card_matching (G \<lbrakk>D\<rbrakk>) N" "e \<in> N" for e N
    using assms \<open>max_card_matching G M\<close> that
      dulmage_mendelsohn_component_exchange[of G D V M N]
    by (auto simp: possible_max_matching_edges_iff)
  thus ?thesis
    using assms possible_max_matching_edges_subset[of "G \<lbrakk>D\<rbrakk>"]
    by (auto simp: possible_max_matching_edges_iff graph_inter_Vs_def
      dest!: dulmage_mendelsohn_component_matching[OF assms])
qed

lemma dulmage_mendelsohn_matching_partition:
  assumes "dblton_graph G" "max_card_matching G M"
  shows "M = (\<Union>D \<in> max_match_components G V. (M \<lbrakk>D\<rbrakk>))"
  using assms max_matching_subset_possible_edges[of G M] max_card_matchingDs(1)[of G M]
  by (auto simp: graph_inter_Vs_def max_match_components_def connected_components'_def;
    fastforce simp: dblton_graph_def dest: edge_in_component[where G = "possible_max_matching_edges G"])

lemma dulmage_mendelsohn_matching_card:
  assumes "graph_invar G" "finite V" "H \<subseteq> G"
  shows "card (\<Union>D \<in> max_match_components G V. (H \<lbrakk>D\<rbrakk>)) =
    (\<Sum>D \<in> max_match_components G V. card (H \<lbrakk>D\<rbrakk>))"
proof-
  have "finite G" "finite H" "{} \<notin> H"
    using assms(1,3)
    by (auto dest: finite_Vs_then_finite intro: finite_subset)
  have "finite (Vs (possible_max_matching_edges G))"
    using assms(1) possible_max_matching_edges_subset[THEN Vs_subset, of G]
    by (auto intro: finite_subset)
  hence "finite (max_match_components G V)"
    using assms(2)
    by (simp add: max_match_components_def connected_components'_aux_def comps_def)
  moreover have "(H \<lbrakk>D\<rbrakk>) \<inter> (H \<lbrakk>E\<rbrakk>) = {}"
    if "D \<in> max_match_components G V"
      "E \<in> max_match_components G V" "D \<noteq> E" for D E
  proof-
    have "(H \<lbrakk>D\<rbrakk>) \<inter> (H \<lbrakk>E\<rbrakk>) = (H \<lbrakk>D \<inter> E\<rbrakk>)"
      by (auto simp: graph_inter_Vs_def)
    thus ?thesis
      using max_match_components_disjoint[OF that] \<open>{} \<notin> H\<close>
      by (simp add: graph_inter_Vs_def)
  qed
  ultimately show ?thesis
    using \<open>finite H\<close>
    by (intro card_UN_disjoint) (auto simp: graph_inter_Vs_def)
qed

theorem dulmage_mendelsohn_matching_number:
  assumes "graph_invar G" "finite V"
  shows "\<nu> G = (\<Sum>D \<in> max_match_components G V. \<nu> (G \<lbrakk>D\<rbrakk>))"
proof-
  have "finite G"
    using assms(1)
    by (auto dest: finite_Vs_then_finite)
  then obtain M where "max_card_matching G M" "card M = \<nu> G"
    by (elim obtain_max_card_matching_\<nu>) auto
  have "card (M \<lbrakk>D\<rbrakk>) = \<nu> (G \<lbrakk>D\<rbrakk>)"
    if "D \<in> max_match_components G V" for D
    using dulmage_mendelsohn_component_matching[OF assms(1) that \<open>max_card_matching G M\<close>]
      \<open>finite G\<close>
    by (intro max_matching_is_\<nu>) (auto simp: graph_inter_Vs_def)
  thus ?thesis
    using assms \<open>max_card_matching G M\<close> \<open>card M = \<nu> G\<close>
      dulmage_mendelsohn_matching_card[of G V M] dulmage_mendelsohn_matching_partition[of G M V]
    by (simp add: max_card_matchingDs(1))
qed

theorem dulmage_mendelsohn_max_matching_iff:
  assumes "graph_invar G" "finite V"
  shows "max_card_matching G M \<longleftrightarrow>
    graph_matching G M \<and> (\<forall>D \<in> max_match_components G V.
      max_card_matching (G \<lbrakk>D\<rbrakk>) (M \<lbrakk>D\<rbrakk>))"
proof(intro iffI, goal_cases)
  case 1
  thus ?case
    using assms(1)
    by (auto dest: max_card_matchingDs(1,2)
      intro: dulmage_mendelsohn_component_matching[OF assms(1)])
next
  case 2
  have "graph_matching G M"
    and local_maximum: "\<forall>D \<in> max_match_components G V.
      max_card_matching (G \<lbrakk>D\<rbrakk>) (M \<lbrakk>D\<rbrakk>)"
    using 2
    by auto
  have "finite G"
    using assms(1)
    by (auto dest: finite_Vs_then_finite)
  hence "finite M"
    using \<open>graph_matching G M\<close>
    by (auto intro: finite_subset)
  have "card (M \<lbrakk>D\<rbrakk>) = \<nu> (G \<lbrakk>D\<rbrakk>)"
    if "D \<in> max_match_components G V" for D
    using local_maximum that \<open>finite G\<close>
    by (intro max_matching_is_\<nu>) (auto simp: graph_inter_Vs_def)
  hence "\<nu> G = card (\<Union>D \<in> max_match_components G V. (M \<lbrakk>D\<rbrakk>))"
    using assms \<open>graph_matching G M\<close>
      dulmage_mendelsohn_matching_card[of G V M]
      dulmage_mendelsohn_matching_number[of G V]
    by simp
  also have "... \<le> card M"
    using \<open>finite M\<close>
    by (intro card_mono) (auto simp: graph_inter_Vs_def)
  finally have "\<nu> G \<le> card M" .
  obtain N where "max_card_matching G N" "card N = \<nu> G"
    using \<open>finite G\<close>
    by (elim obtain_max_card_matching_\<nu>) auto
  thus ?case
    using \<open>\<nu> G \<le> card M\<close> \<open>graph_matching G M\<close>
    by (intro max_card_matchingI; auto dest: max_card_matchingDs(3); linarith)
qed

theorem dulmage_mendelsohn_assemble:
  fixes F :: "'a set \<Rightarrow> 'a graph"
  assumes "graph_invar G" "finite V"
    "\<And>D. D \<in> max_match_components G V \<Longrightarrow>
      max_card_matching (G \<lbrakk>D\<rbrakk>) (F D)"
  defines "M \<equiv> \<Union>D \<in> max_match_components G V. F D"
  shows "max_card_matching G M"
    "\<And>D. D \<in> max_match_components G V \<Longrightarrow> (M \<lbrakk>D\<rbrakk>) = F D"
proof-
  have local_matching: "matching (F D)" "F D \<subseteq> G" "Vs (F D) \<subseteq> D"
    if "D \<in> max_match_components G V" for D
    using assms(3)[OF that]
    by (auto simp: graph_inter_Vs_def Vs_def dest: max_card_matchingDs(1,2))
  have "Vs (F D) \<inter> Vs (F E) = {}"
    if "D \<in> max_match_components G V"
      "E \<in> max_match_components G V" "D \<noteq> E" for D E
    using that local_matching(3)[of D] local_matching(3)[of E]
      max_match_components_disjoint[OF that]
    by blast
  hence "matching M"
    using local_matching(1)
    unfolding M_def matching_def Vs_def
    by blast
  moreover have "M \<subseteq> G"
    using local_matching(2)
    by (auto simp: M_def)
  moreover show "(M \<lbrakk>D\<rbrakk>) = F D" if "D \<in> max_match_components G V" for D
  proof-
    have "E = D" if "E \<in> max_match_components G V"
      "e \<in> F E" "e \<subseteq> D" for E e
    proof-
      have "e \<noteq> {}" "e \<subseteq> E"
        using assms(1) local_matching(2,3)[of E] that(1,2)
        by (auto simp: Vs_def)
      thus ?thesis
        using that \<open>D \<in> max_match_components G V\<close>
        by (blast dest: max_match_components_disjoint)
    qed
    thus ?thesis
      using that local_matching(3)[of D]
      by (auto simp: M_def graph_inter_Vs_def Vs_def; blast)
  qed
  ultimately show "max_card_matching G M"
    using assms(1-3)
    by (auto simp: dulmage_mendelsohn_max_matching_iff)
qed

lemma dulmage_mendelsohn_inessential:
  assumes "graph_invar G" "D \<in> max_match_components G V" "x \<in> D"
  shows "inessential (G \<lbrakk>D\<rbrakk>) x \<longleftrightarrow> inessential G x"
proof((intro iffI; elim inessentialE), goal_cases)
  case (1 N)
  obtain M where "max_card_matching G M"
    using assms(1)
    by (auto dest: finite_Vs_then_finite elim!: max_card_matching_exists)
  have "max_card_matching G ((M - (M \<lbrakk>D\<rbrakk>)) \<union> N)"
    using assms(1,2) \<open>max_card_matching G M\<close> \<open>max_card_matching (G \<lbrakk>D\<rbrakk>) N\<close>
    by (rule dulmage_mendelsohn_component_exchange)
  moreover have "x \<notin> Vs ((M - (M \<lbrakk>D\<rbrakk>)) \<union> N)"
    using assms \<open>x \<notin> Vs N\<close> \<open>max_card_matching G M\<close>
      dulmage_mendelsohn_matching_vertices[of G D V M]
      remove_matching_edges_Vs[of M "M \<lbrakk>D\<rbrakk>"]
      graph_inter_Vs_subset(1)[of M D]
    by (auto dest: max_card_matchingDs(2) simp: vs_union)
  ultimately show ?case
    by (auto intro: inessentialI)
next
  case (2 M)
  have "max_card_matching (G \<lbrakk>D\<rbrakk>) (M \<lbrakk>D\<rbrakk>)"
    using assms(1,2) \<open>max_card_matching G M\<close>
    by (rule dulmage_mendelsohn_component_matching)
  thus "inessential (G \<lbrakk>D\<rbrakk>) x"
    using \<open>x \<notin> Vs M\<close>
    by (auto intro!: inessentialI simp: Vs_def graph_inter_Vs_def)
qed

lemma dulmage_mendelsohn_component_saturation:
  assumes "graph_invar G" "D \<in> max_match_components G V"
    "max_card_matching (G \<lbrakk>D\<rbrakk>) M"
  shows "D - {x \<in> D. inessential G x} \<subseteq> Vs M"
  using assms inessential_complement_matched[of "G \<lbrakk>D\<rbrakk>" M D]
  by (auto simp: dulmage_mendelsohn_inessential[of G D V])

lemma dulmage_mendelsohn_balanced_component:
  assumes "graph_invar G" "D \<in> max_match_components G V"
    "D \<subseteq> V - {x \<in> V. inessential G x}"
    "max_card_matching (G \<lbrakk>D\<rbrakk>) M"
  shows "Vs M = D" "perfect_matching (G \<lbrakk>D\<rbrakk>) M"
  using assms dulmage_mendelsohn_component_saturation[of G D V M]
    max_card_matchingDs(1,2)[of "G \<lbrakk>D\<rbrakk>" M]
  by (auto simp: perfect_matching_def Vs_def graph_inter_Vs_def)

section \<open>Decomposition theorems\<close>

text \<open>The following results collect the coarse partition and the
  maximum-matching structure of the canonical components.\<close>

theorem dulmage_mendelsohn_decomposition_all:
  fixes G M N :: "'a graph" and L R I C D_L D_R :: "'a set"
    and K :: "'a set set" and F :: "'a set \<Rightarrow> 'a graph"
  assumes "finite L" "finite R" "bipartite G L R" "max_card_matching G M"
  defines "I \<equiv> {x \<in> L \<union> R. inessential G x}"
    and "C \<equiv> L \<union> R - I - \<A> G"
    and "D_L \<equiv> (I \<inter> L) \<union> (\<A> G \<inter> R)"
    and "D_R \<equiv> (I \<inter> R) \<union> (\<A> G \<inter> L)"
    and "K \<equiv> max_match_components G (L \<union> R)"
  shows "D_L \<union> D_R \<union> C = L \<union> R"
    "D_L \<inter> D_R = {} \<and> D_L \<inter> C = {} \<and> D_R \<inter> C = {}"
    "\<Union>K = L \<union> R"
    "D \<in> K \<Longrightarrow> D \<noteq> {} \<and> D \<subseteq> L \<union> R"
    "\<lbrakk>D \<in> K; E \<in> K; D \<noteq> E\<rbrakk> \<Longrightarrow> D \<inter> E = {}"
    "D \<in> K \<Longrightarrow> D \<subseteq> D_L \<or> D \<subseteq> D_R \<or> D \<subseteq> C"
    "cover_matching (G \<lbrakk>D_L\<rbrakk>) (M \<lbrakk>D_L\<rbrakk>) (\<A> G \<inter> R)"
    "cover_matching (G \<lbrakk>D_R\<rbrakk>) (M \<lbrakk>D_R\<rbrakk>) (\<A> G \<inter> L)"
    "perfect_matching (G \<lbrakk>C\<rbrakk>) (M \<lbrakk>C\<rbrakk>) \<and> Vs (M \<lbrakk>C\<rbrakk>) = C"
    "card (C \<inter> L) = card (C \<inter> R)"
    "\<nu> G = card (\<A> G) + card (C \<inter> L)"
    "\<nu> G = (\<Sum>D \<in> K. \<nu> (G \<lbrakk>D\<rbrakk>))"
    "M = (\<Union>D \<in> K. (M \<lbrakk>D\<rbrakk>))"
    "D \<in> K \<Longrightarrow> max_card_matching (G \<lbrakk>D\<rbrakk>) (M \<lbrakk>D\<rbrakk>)"
    "D \<in> K \<Longrightarrow> Vs (M \<lbrakk>D\<rbrakk>) = Vs M \<inter> D"
    "D \<in> K \<Longrightarrow> possible_max_matching_edges (G \<lbrakk>D\<rbrakk>) = (possible_max_matching_edges G \<lbrakk>D\<rbrakk>)"
    "\<lbrakk>D \<in> K; x \<in> D\<rbrakk> \<Longrightarrow>
      inessential (G \<lbrakk>D\<rbrakk>) x \<longleftrightarrow> inessential G x"
    "max_card_matching G N \<longleftrightarrow> graph_matching G N \<and>
      (\<forall>D \<in> K. max_card_matching (G \<lbrakk>D\<rbrakk>) (N \<lbrakk>D\<rbrakk>))"
    "(\<And>D. D \<in> K \<Longrightarrow> max_card_matching (G \<lbrakk>D\<rbrakk>) (F D)) \<Longrightarrow>
      max_card_matching G (\<Union>D \<in> K. F D) \<and>
      (\<forall>D \<in> K. ((\<Union>E \<in> K. F E) \<lbrakk>D\<rbrakk>) = F D)"
    "\<lbrakk>X \<subseteq> \<A> G; X \<noteq> {}\<rbrakk> \<Longrightarrow> card X < card (Neighbourhood G X \<inter> I)"
    "\<lbrakk>{x,y} \<in> G; inessential G x\<rbrakk> \<Longrightarrow> {x,y} \<in> possible_max_matching_edges G"
    "x \<in> L \<union> R - Vs G \<Longrightarrow> {x} \<in> K"
proof-
  have "graph_invar G" "Vs G \<subseteq> L \<union> R" "finite (L \<union> R)"
    using assms(1-3) finite_parts_bipartite_graph_invar[of L R G] bipartite_vs_subset[of G L R]
    by auto
  have remainder: "C = Vs G - \<I> G - \<A> G"
    using \<open>graph_invar G\<close> \<open>Vs G \<subseteq> L \<union> R\<close>
    unfolding C_def I_def
    by (intro edmonds_gallai_remainder_in_universe) (auto dest: finite_Vs_then_finite)
  show "D_L \<union> D_R \<union> C = L \<union> R"
    "D_L \<inter> D_R = {} \<and> D_L \<inter> C = {} \<and> D_R \<inter> C = {}"
    using dulmage_mendelsohn_coarse_partition[OF assms(3)]
    by (auto simp: I_def C_def D_L_def D_R_def)
  show "\<Union>K = L \<union> R"
    using \<open>graph_invar G\<close> \<open>Vs G \<subseteq> L \<union> R\<close>
    unfolding K_def
    by (intro max_match_components_cover) auto
  show "D \<in> K \<Longrightarrow> D \<noteq> {} \<and> D \<subseteq> L \<union> R"
    using \<open>\<Union>K = L \<union> R\<close> dulmage_mendelsohn_component_nonempty[of D G "L \<union> R"]
    by (auto simp: K_def)
  show "\<lbrakk>D \<in> K; E \<in> K; D \<noteq> E\<rbrakk> \<Longrightarrow> D \<inter> E = {}"
    by (auto simp: K_def max_match_components_disjoint)
  show "D \<in> K \<Longrightarrow> D \<subseteq> D_L \<or> D \<subseteq> D_R \<or> D \<subseteq> C"
    using dulmage_mendelsohn_component_regions[OF \<open>graph_invar G\<close> assms(3), of D]
    by (auto simp: K_def I_def C_def D_L_def D_R_def)
  show "cover_matching (G \<lbrakk>D_L\<rbrakk>) (M \<lbrakk>D_L\<rbrakk>) (\<A> G \<inter> R)"
    "cover_matching (G \<lbrakk>D_R\<rbrakk>) (M \<lbrakk>D_R\<rbrakk>) (\<A> G \<inter> L)"
    "perfect_matching (G \<lbrakk>C\<rbrakk>) (M \<lbrakk>C\<rbrakk>) \<and> Vs (M \<lbrakk>C\<rbrakk>) = C"
    "card (C \<inter> L) = card (C \<inter> R)"
    using dulmage_mendelsohn_max_matching[OF assms(1-4)]
    by (auto simp: I_def C_def D_L_def D_R_def)
  show "\<nu> G = card (\<A> G) + card (C \<inter> L)"
    "\<nu> G = (\<Sum>D \<in> K. \<nu> (G \<lbrakk>D\<rbrakk>))"
    "M = (\<Union>D \<in> K. (M \<lbrakk>D\<rbrakk>))"
    using \<open>graph_invar G\<close> \<open>finite (L \<union> R)\<close> assms(3,4)
    by (auto simp: K_def remainder intro!: bipartite_matching_number[where R = R]
      dulmage_mendelsohn_matching_number dulmage_mendelsohn_matching_partition[where G = G])
  show "D \<in> K \<Longrightarrow> max_card_matching (G \<lbrakk>D\<rbrakk>) (M \<lbrakk>D\<rbrakk>)"
    "D \<in> K \<Longrightarrow> Vs (M \<lbrakk>D\<rbrakk>) = Vs M \<inter> D"
    "D \<in> K \<Longrightarrow> possible_max_matching_edges (G \<lbrakk>D\<rbrakk>) = (possible_max_matching_edges G \<lbrakk>D\<rbrakk>)"
    "\<lbrakk>D \<in> K; x \<in> D\<rbrakk> \<Longrightarrow>
      inessential (G \<lbrakk>D\<rbrakk>) x \<longleftrightarrow> inessential G x"
    using \<open>graph_invar G\<close> assms(4)
    by (auto simp: K_def
      dulmage_mendelsohn_matching_vertices[where G = G and V = "L \<union> R"]
      dulmage_mendelsohn_inessential[where V = "L \<union> R"]
      intro!: dulmage_mendelsohn_component_matching[where G = G] possible_max_matching_edges_restrict)
  show "max_card_matching G N \<longleftrightarrow> graph_matching G N \<and>
      (\<forall>D \<in> K. max_card_matching (G \<lbrakk>D\<rbrakk>) (N \<lbrakk>D\<rbrakk>))"
    by (simp add: K_def dulmage_mendelsohn_max_matching_iff[
      OF \<open>graph_invar G\<close> \<open>finite (L \<union> R)\<close>])
  show "(\<And>D. D \<in> K \<Longrightarrow> max_card_matching (G \<lbrakk>D\<rbrakk>) (F D)) \<Longrightarrow>
      max_card_matching G (\<Union>D \<in> K. F D) \<and>
      (\<forall>D \<in> K. ((\<Union>E \<in> K. F E) \<lbrakk>D\<rbrakk>) = F D)"
    using dulmage_mendelsohn_assemble[OF \<open>graph_invar G\<close> \<open>finite (L \<union> R)\<close>,
      where F = F]
    by (auto simp: K_def)
  have "Neighbourhood G X \<inter> I = Neighbourhood G X \<inter> \<I> G"
    using Neighbourhood_in_G[of G X] \<open>Vs G \<subseteq> L \<union> R\<close>
    by (auto simp: I_def inessentials_def)
  show "\<lbrakk>X \<subseteq> \<A> G; X \<noteq> {}\<rbrakk> \<Longrightarrow> card X < card (Neighbourhood G X \<inter> I)"
    unfolding \<open>Neighbourhood G X \<inter> I = Neighbourhood G X \<inter> \<I> G\<close>
    by (intro bipartite_inessentials_strict_hall[OF \<open>graph_invar G\<close> assms(3)]) auto
  show "\<lbrakk>{x,y} \<in> G; inessential G x\<rbrakk> \<Longrightarrow> {x,y} \<in> possible_max_matching_edges G"
    by (intro bipartite_inessential_edge_possible[OF \<open>graph_invar G\<close> assms(3)]) auto
  show "x \<in> L \<union> R - Vs G \<Longrightarrow> {x} \<in> K"
    by (simp add: K_def dulmage_mendelsohn_isolated_vertex)
qed

lemmas dulmage_mendelsohn_decomposition_max_matching_specific =
  dulmage_mendelsohn_decomposition_all(7-9,13-15)

theorem dulmage_mendelsohn_decomposition_general:
  fixes G N :: "'a graph" and L R I C D_L D_R :: "'a set"
    and K :: "'a set set" and F :: "'a set \<Rightarrow> 'a graph"
  assumes "finite L" "finite R" "bipartite G L R"
  defines "I \<equiv> {x \<in> L \<union> R. inessential G x}"
    and "C \<equiv> L \<union> R - I - \<A> G"
    and "D_L \<equiv> (I \<inter> L) \<union> (\<A> G \<inter> R)"
    and "D_R \<equiv> (I \<inter> R) \<union> (\<A> G \<inter> L)"
    and "K \<equiv> max_match_components G (L \<union> R)"
  shows "D_L \<union> D_R \<union> C = L \<union> R"
    "D_L \<inter> D_R = {} \<and> D_L \<inter> C = {} \<and> D_R \<inter> C = {}"
    "\<Union>K = L \<union> R"
    "D \<in> K \<Longrightarrow> D \<noteq> {} \<and> D \<subseteq> L \<union> R"
    "\<lbrakk>D \<in> K; E \<in> K; D \<noteq> E\<rbrakk> \<Longrightarrow> D \<inter> E = {}"
    "D \<in> K \<Longrightarrow> D \<subseteq> D_L \<or> D \<subseteq> D_R \<or> D \<subseteq> C"
    "card (C \<inter> L) = card (C \<inter> R)"
    "\<nu> G = card (\<A> G) + card (C \<inter> L)"
    "\<nu> G = (\<Sum>D \<in> K. \<nu> (G \<lbrakk>D\<rbrakk>))"
    "D \<in> K \<Longrightarrow> possible_max_matching_edges (G \<lbrakk>D\<rbrakk>) = (possible_max_matching_edges G \<lbrakk>D\<rbrakk>)"
    "\<lbrakk>D \<in> K; x \<in> D\<rbrakk> \<Longrightarrow>
      inessential (G \<lbrakk>D\<rbrakk>) x \<longleftrightarrow> inessential G x"
    "max_card_matching G N \<longleftrightarrow> graph_matching G N \<and>
      (\<forall>D \<in> K. max_card_matching (G \<lbrakk>D\<rbrakk>) (N \<lbrakk>D\<rbrakk>))"
    "(\<And>D. D \<in> K \<Longrightarrow> max_card_matching (G \<lbrakk>D\<rbrakk>) (F D)) \<Longrightarrow>
      max_card_matching G (\<Union>D \<in> K. F D) \<and>
      (\<forall>D \<in> K. ((\<Union>E \<in> K. F E) \<lbrakk>D\<rbrakk>) = F D)"
    "\<lbrakk>X \<subseteq> \<A> G; X \<noteq> {}\<rbrakk> \<Longrightarrow> card X < card (Neighbourhood G X \<inter> I)"
    "\<lbrakk>{x,y} \<in> G; inessential G x\<rbrakk> \<Longrightarrow> {x,y} \<in> possible_max_matching_edges G"
    "x \<in> L \<union> R - Vs G \<Longrightarrow> {x} \<in> K"
    "\<exists>M. max_card_matching G M \<and>
      cover_matching (G \<lbrakk>D_L\<rbrakk>) (M \<lbrakk>D_L\<rbrakk>) (\<A> G \<inter> R) \<and>
      cover_matching (G \<lbrakk>D_R\<rbrakk>) (M \<lbrakk>D_R\<rbrakk>) (\<A> G \<inter> L) \<and>
      perfect_matching (G \<lbrakk>C\<rbrakk>) (M \<lbrakk>C\<rbrakk>) \<and> Vs (M \<lbrakk>C\<rbrakk>) = C"
proof-
  obtain M where "max_card_matching G M"
    using finite_parts_bipartite_graph_invar[OF assms(1-3)]
    by (auto dest: finite_Vs_then_finite elim!: max_card_matching_exists)
  note decomposition = dulmage_mendelsohn_decomposition_all[
    OF assms(1-3) \<open>max_card_matching G M\<close>, folded I_def C_def D_L_def D_R_def K_def]
  show "D_L \<union> D_R \<union> C = L \<union> R"
    "D_L \<inter> D_R = {} \<and> D_L \<inter> C = {} \<and> D_R \<inter> C = {}"
    "\<Union>K = L \<union> R"
    "D \<in> K \<Longrightarrow> D \<noteq> {} \<and> D \<subseteq> L \<union> R"
    "\<lbrakk>D \<in> K; E \<in> K; D \<noteq> E\<rbrakk> \<Longrightarrow> D \<inter> E = {}"
    "D \<in> K \<Longrightarrow> D \<subseteq> D_L \<or> D \<subseteq> D_R \<or> D \<subseteq> C"
    using decomposition(1-6)
    by auto
  show "card (C \<inter> L) = card (C \<inter> R)"
    "\<nu> G = card (\<A> G) + card (C \<inter> L)"
    "\<nu> G = (\<Sum>D \<in> K. \<nu> (G \<lbrakk>D\<rbrakk>))"
    using decomposition(10-12)
    by auto
  show "D \<in> K \<Longrightarrow> possible_max_matching_edges (G \<lbrakk>D\<rbrakk>) = (possible_max_matching_edges G \<lbrakk>D\<rbrakk>)"
    "\<lbrakk>D \<in> K; x \<in> D\<rbrakk> \<Longrightarrow>
      inessential (G \<lbrakk>D\<rbrakk>) x \<longleftrightarrow> inessential G x"
    "max_card_matching G N \<longleftrightarrow> graph_matching G N \<and>
      (\<forall>D \<in> K. max_card_matching (G \<lbrakk>D\<rbrakk>) (N \<lbrakk>D\<rbrakk>))"
    "\<lbrakk>X \<subseteq> \<A> G; X \<noteq> {}\<rbrakk> \<Longrightarrow> card X < card (Neighbourhood G X \<inter> I)"
    "\<lbrakk>{x,y} \<in> G; inessential G x\<rbrakk> \<Longrightarrow> {x,y} \<in> possible_max_matching_edges G"
    "x \<in> L \<union> R - Vs G \<Longrightarrow> {x} \<in> K"
    using decomposition(16-18,20-22)
    by auto
  show "(\<And>D. D \<in> K \<Longrightarrow> max_card_matching (G \<lbrakk>D\<rbrakk>) (F D)) \<Longrightarrow>
      max_card_matching G (\<Union>D \<in> K. F D) \<and>
      (\<forall>D \<in> K. ((\<Union>E \<in> K. F E) \<lbrakk>D\<rbrakk>) = F D)"
    by (fact decomposition(19))
  show "\<exists>M. max_card_matching G M \<and>
      cover_matching (G \<lbrakk>D_L\<rbrakk>) (M \<lbrakk>D_L\<rbrakk>) (\<A> G \<inter> R) \<and>
      cover_matching (G \<lbrakk>D_R\<rbrakk>) (M \<lbrakk>D_R\<rbrakk>) (\<A> G \<inter> L) \<and>
      perfect_matching (G \<lbrakk>C\<rbrakk>) (M \<lbrakk>C\<rbrakk>) \<and> Vs (M \<lbrakk>C\<rbrakk>) = C"
    using decomposition(7-9) \<open>max_card_matching G M\<close>
    by auto
qed

end

