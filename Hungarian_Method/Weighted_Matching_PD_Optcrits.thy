theory Weighted_Matching_PD_Optcrits
  imports  RANKING.More_Graph Berge_Lemma.Berge
begin

no_translations
  "_Collect p P"      <= "{p. P}"
  "_Collect p P"      <= "{p|xs. P}"
  "_CollectIn p A P"  <= "{p : A. P}"

(*TODO MOVE*)
lemma matching_graph_mono: "graph_matching G M \<Longrightarrow> G \<subseteq> G' \<Longrightarrow> graph_matching G' M"
  by(auto simp add: matching_def)

lemma perfect_matchingE:
"perfect_matching G M \<Longrightarrow> (M \<subseteq> G \<Longrightarrow> matching M \<Longrightarrow> Vs G = Vs M \<Longrightarrow> P) \<Longrightarrow> P"
  by(auto simp add: perfect_matching_def)
(*TODO MOVE*)
definition "Neighbourhood G V = {v | v u. {u, v} \<in> G \<and> u \<in> V \<and> v \<notin> V}"

lemma not_in_NeighbourhoodE: "v \<notin> Neighbourhood G V \<Longrightarrow>
                ((\<And> u. {u, v} \<in> G \<Longrightarrow> u \<in> V \<Longrightarrow> v \<notin> V \<Longrightarrow> False) \<Longrightarrow> P) \<Longrightarrow> P"
  by(auto simp add: Neighbourhood_def)

lemma self_not_in_Neighbourhood:
"x \<in> V \<Longrightarrow> x \<notin> Neighbourhood G V"
  by(auto simp add: Neighbourhood_def)

lemma Neighbourhood_neighbourhood_union_inter:
 "Neighbourhood G V = \<Union> (neighbourhood G ` V) - V"
  by(auto simp add: Neighbourhood_def neighbourhood_def  insert_commute)

lemma Neighbourhood_bipartite:
  assumes"bipartite G X Y" "V \<subseteq> X \<or> V \<subseteq> Y"
  shows  "Neighbourhood G V = \<Union> (neighbourhood G ` V)"
proof(rule, all \<open>rule\<close>, goal_cases)
  case (1 u)
  then obtain v where uv:"{v, u} \<in> G" "v \<in> V"
    by(auto simp add: Neighbourhood_def)
  hence "u \<in> neighbourhood G v"
    by(auto simp add: neighbourhood_def edge_commute) 
  then show ?case 
    using uv(2) by auto
next
  case (2 u)
  then obtain v where v: "u \<in> neighbourhood G v" "v \<in> V" by auto
  hence uv:"{u, v} \<in> G"
    by(auto simp add: neighbourhood_def)
  hence "u \<notin> V"
    using v(2) assms by(fastforce simp add: bipartite_def)
  then show ?case 
    using edge_commute[OF uv] v(2)
    by(auto simp add: Neighbourhood_def) 
qed

lemma Neighbourhood_bipartite_left:
  assumes"bipartite G X Y" "V \<subseteq> X"
  shows  "Neighbourhood G V \<subseteq> Y"
  using assms
  by(auto simp add: doubleton_eq_iff bipartite_def Neighbourhood_def dest: bipartite_edgeD(1))

lemma Neighbourhood_bipartite_mono:
  assumes"bipartite G X Y" "G' \<subseteq> G"
  shows  "Neighbourhood G' X \<subseteq> Neighbourhood G X"
  using assms
  by (auto simp add: doubleton_eq_iff bipartite_def Neighbourhood_def)

lemma Neighbourhood_bipartite_right:
  assumes"bipartite G X Y" "V \<subseteq> Y"
  shows  "Neighbourhood G V \<subseteq> X"
  using assms
  by (auto simp add: doubleton_eq_iff bipartite_def Neighbourhood_def dest: bipartite_edgeD(2))

lemma bipartite_alternation:
  assumes "bipartite G X Y" "walk_betw G s p t"
  shows   "s \<in> X \<Longrightarrow> alt_list (\<lambda> x. x \<in> X) (\<lambda> x. x \<in> Y) p"
          "s \<in> Y \<Longrightarrow> alt_list (\<lambda> x. x \<in> Y) (\<lambda> x. x \<in> X) p"
  using assms(2)
proof(induction rule: induct_walk_betw , goal_cases)
  case (1 s)
  then show ?case 
    by (simp add: alt_list.intros(1,2))
next
  case (2 s)
  then show ?case
    by (simp add: alt_list.intros(1,2))
next
  case (3 x y p t)
  have XY: "x \<in> X" "y \<in> Y"
    using  3(1,5) assms(1) bipartite_edgeD(1) by fastforce+
  show ?case 
    by(auto intro!: 3(4) intro:  alt_list.intros(2) simp add: XY)
next
  case (4 x y p t)
  have XY: "x \<in> Y" "y \<in> X"
    using  4(1,5) assms(1) bipartite_edgeD(2) by fastforce+
  show ?case 
    by(auto intro!: 4(3) intro:  alt_list.intros(2) simp add: XY)
qed

lemma bipartite_ends_and_lengths:
  assumes "bipartite G X Y" "walk_betw G s p t"
  shows   "s \<in> X \<Longrightarrow> even (length p) \<Longrightarrow> t \<in> Y"
          "s \<in> X \<Longrightarrow> odd (length p) \<Longrightarrow> t \<in> X"
          "s \<in> Y \<Longrightarrow> even (length p) \<Longrightarrow> t \<in> X"
          "s \<in> Y \<Longrightarrow> odd (length p) \<Longrightarrow> t \<in> Y"
          "s \<in> X \<Longrightarrow> t \<in> Y \<Longrightarrow> even (length p)"
          "s \<in> X \<Longrightarrow> t \<in> X \<Longrightarrow> odd (length p)"
          "s \<in> Y \<Longrightarrow> t \<in> X \<Longrightarrow> even (length p)"
          "s \<in> Y \<Longrightarrow> t \<in> Y \<Longrightarrow> odd (length p)"
  using bipartite_alternation[OF assms]
        alternating_list_odd_last[of _ _ p]
        alternating_list_even_last[of _ _ p] assms(2)
        bipartite_vertex(1)[OF walk_endpoints(1) assms(1)] walk_symmetric[OF assms(2)] 
  by (fastforce simp add: walk_between_nonempty_pathD(4)[OF assms(2)])+

section \<open>Duality-Based Optimality Criteria for Weighted Matchings\<close>

text \<open>In both cases, we show weak duality in form of an inequality. 
This implies optimality for pairs of primal and dual solutions that satisfy the inequality with equality.\<close>

subsection \<open>Maximum Weight Matchings\<close>

definition "feasible_max_dual V E w (y::'v \<Rightarrow> real) = 
 ((\<forall> v \<in> V. y v \<ge> 0) \<and> 
(\<forall> e \<in> E. \<forall> u v. e ={u, v} \<longrightarrow> y u +  y v \<ge> w e) \<and> 
Vs E \<subseteq> V \<and> finite V)"

lemma feasible_max_dualI:
"(\<And> v. v \<in> V \<Longrightarrow> y v \<ge> 0) \<Longrightarrow>
(\<And> e u v. e \<in> E \<Longrightarrow> e ={u, v} \<Longrightarrow> y u +  y v \<ge> w e)
\<Longrightarrow> Vs E \<subseteq> V \<Longrightarrow> finite V
\<Longrightarrow> feasible_max_dual V E w y"
and feasible_max_dualE:
"feasible_max_dual V E w y \<Longrightarrow>((\<And> v. v \<in> V \<Longrightarrow> y v \<ge> 0) \<Longrightarrow>
(\<And> e u v. e \<in> E \<Longrightarrow> e ={u, v} \<Longrightarrow> y u +  y v \<ge> w e)
\<Longrightarrow> Vs E \<subseteq> V \<Longrightarrow> finite V \<Longrightarrow> P) \<Longrightarrow> P"
and feasible_max_dualD:
"feasible_max_dual V E w y \<Longrightarrow> v \<in> V \<Longrightarrow> y v \<ge> 0"
"feasible_max_dual V E w y \<Longrightarrow> e \<in> E \<Longrightarrow> e ={u, v} \<Longrightarrow> y u +  y v \<ge> w e"
"feasible_max_dual V E w y \<Longrightarrow>  Vs E \<subseteq> V"
"feasible_max_dual V E w y \<Longrightarrow>  finite V"
  by(auto simp add: feasible_max_dual_def)

definition "min_feasible_max_dual V E w y =
 (feasible_max_dual V E w y \<and>
 (\<forall> y'. feasible_max_dual V E w y' \<longrightarrow> sum y V \<le> sum y' V))"

lemma min_feasible_max_dualE:
"min_feasible_max_dual V E w y \<Longrightarrow>
(feasible_max_dual V E w y \<Longrightarrow>
(\<And> y'. feasible_max_dual V E w y' \<Longrightarrow> sum y V \<le> sum y' V) \<Longrightarrow> P)
\<Longrightarrow> P"
and min_feasible_max_dualI:
"feasible_max_dual V E w y \<Longrightarrow>
(\<And> y'. feasible_max_dual V E w y' \<Longrightarrow> sum y V \<le> sum y' V) \<Longrightarrow> 
min_feasible_max_dual V E w y"
and min_feasible_max_dualD:
"min_feasible_max_dual V E w y \<Longrightarrow>feasible_max_dual V E w y"
"min_feasible_max_dual V E w y \<Longrightarrow> feasible_max_dual V E w y' \<Longrightarrow> sum y V \<le> sum y' V"
  by(auto simp add: min_feasible_max_dual_def)

definition "max_weight_matching E w M =
  (graph_matching E M \<and> (\<forall> M'. graph_matching E M' \<longrightarrow> sum w M' \<le> sum w M))"

lemma max_weight_matchingI:
"graph_matching E M \<Longrightarrow> (\<And> M'. graph_matching E M' \<Longrightarrow> sum w M' \<le> sum w M)
\<Longrightarrow> max_weight_matching E w M"
and max_weight_matchingE:
"max_weight_matching E w M \<Longrightarrow> 
(graph_matching E M \<Longrightarrow> (\<And> M'. graph_matching E M' \<Longrightarrow> sum w M' \<le> sum w M) \<Longrightarrow> P)
\<Longrightarrow> P"
and max_weight_matchingD:
"max_weight_matching E w M \<Longrightarrow> graph_matching E M"
"max_weight_matching E w M \<Longrightarrow> graph_matching E M' \<Longrightarrow> sum w M' \<le> sum w M"
  by(auto simp add: max_weight_matching_def)
(*Do we have something like that already?*)
definition "pick_one e = (SOME v. v \<in> e)"
definition "pick_another e = (SOME v. v \<in> e \<and> v \<noteq> pick_one e)"

lemma pick_one_and_another_props:
  assumes "\<exists> u v. e = {u, v} \<and> u \<noteq> v" 
  shows   "pick_one e \<in> e" "pick_another e \<in> e"
          "e = {pick_one e, pick_another e}"
proof-
  obtain u v where uv: "e = {u, v}" "u \<noteq> v" using assms by auto
  have "pick_one e = u \<or> pick_one e = v"
    using uv 
    by (metis empty_iff insert_iff pick_one_def some_in_eq)
  moreover have "pick_one e = u \<Longrightarrow> pick_another e = v"
    using uv 
    by (metis (mono_tags, lifting) insert_iff pick_another_def singletonD someI_ex)
  moreover have "pick_one e = v \<Longrightarrow> pick_another e = u"
    using uv 
    by (metis (mono_tags, lifting) insert_iff pick_another_def singletonD someI_ex)
  ultimately show  "pick_one e \<in> e" "pick_another e \<in> e" "e = {pick_one e, pick_another e}"
    using uv by auto
qed

lemma max_matching_weak_duality:
  assumes "feasible_max_dual V E w y" "graph_matching E M"
          "graph_invar E"
  shows   "sum w M \<le> sum y V"
proof-
  have graph_invar_M: "graph_invar M"
    using assms(2,3) graph_invar_subset by auto
  have Ms_finite: "Ball M finite"
    using graph_invar_M by blast
  have Ms_disjoint: "\<forall>A\<in>M. \<forall>B\<in>M. A \<noteq> B \<longrightarrow> A \<inter> B = {}" 
    using  assms(2) by (auto elim!: matchingE)
  have "sum w M \<le> ((sum \<circ> sum) y M)"
    using assms(2) 
    by (force intro: ordered_comm_monoid_add_class.sum_mono
                     dblton_graphE[OF graph_invar_dblton[OF graph_invar_M]] 
                     feasible_max_dualD(2)[OF assms(1)])
  also have "... = sum y (\<Union> M)"
    by(auto simp add:Vs_def comm_monoid_add_class.sum.Union_disjoint[OF Ms_finite Ms_disjoint])
  also have "... \<le> sum y V"
    using assms(2)  feasible_max_dualD[OF assms(1)] 
    by (fastforce intro!: ordered_comm_monoid_add_class.sum_mono2)
  finally show ?thesis by simp
qed

corollary max_matching_pd_optimality:
  assumes "feasible_max_dual V E w y" "graph_matching E M"
          "graph_invar E"  "sum w M = sum y V"
    shows "max_weight_matching E w M" "min_feasible_max_dual V E w y"
  using assms max_matching_weak_duality
  by(force intro!: max_weight_matchingI min_feasible_max_dualI)+

definition "tight_subgraph E w y = {{u, v} | u v. {u, v} \<in> E \<and> w {u, v} = y u + y v}"

lemma in_tight_subgraphI:
"e = {u, v} \<Longrightarrow> {u, v} \<in> E \<Longrightarrow> w {u, v} = y u + y v \<Longrightarrow> e \<in> tight_subgraph E w y"
and in_tight_subgraphE:
" e \<in> tight_subgraph E w y \<Longrightarrow>
 (\<And> u v. e = {u, v} \<Longrightarrow> {u, v} \<in> E \<Longrightarrow> w {u, v} = y u + y v \<Longrightarrow> P) \<Longrightarrow> P"
and in_tight_subgraphD:
" e \<in> tight_subgraph E w y \<Longrightarrow> e = {u, v}  \<Longrightarrow> w {u, v} = (y::'v \<Rightarrow> real) u + y v"
  by(auto simp add: tight_subgraph_def doubleton_eq_iff insert_commute)

definition "non_zero_vertices V y = {v | v. v \<in> V \<and> y v \<noteq> 0}"

lemma in_non_zero_verticesI:
"v \<in> V \<Longrightarrow> y v \<noteq> 0 \<Longrightarrow> v \<in> non_zero_vertices V y"
and in_non_zero_verticesE:
"v \<in> non_zero_vertices V y \<Longrightarrow> 
(v \<in> V \<Longrightarrow> y v \<noteq> 0 \<Longrightarrow> P) \<Longrightarrow> P"
  by(auto simp add:  non_zero_vertices_def)

lemma equality_if_tight_matching_covers_bads:
  assumes "feasible_max_dual V E w y" "graph_matching E M"
          "graph_invar E" "M \<subseteq> tight_subgraph E w y"
          "non_zero_vertices V y \<subseteq> Vs M"
  shows   "sum w M = sum y V"
proof-
  have graph_invar_M: "graph_invar M"
    using assms(2,3) graph_invar_subset by auto
  have Ms_finite: "Ball M finite"
    using graph_invar_M by blast
  have Ms_disjoint: "\<forall>A\<in>M. \<forall>B\<in>M. A \<noteq> B \<longrightarrow> A \<inter> B = {}" 
    using  assms(2) by (auto elim!: matchingE)
  have "sum w M = ((sum \<circ> sum) y M)"
    using assms(2,4)
    by(force intro!: comm_monoid_add_class.sum.cong in_tight_subgraphD[of _ E w y]
               elim: dblton_graphE[OF graph_invar_dblton[OF graph_invar_M]])
  also have "... = sum y (\<Union> M)"
    by(auto simp add:Vs_def comm_monoid_add_class.sum.Union_disjoint[OF Ms_finite Ms_disjoint])
  also have "... = sum y V - sum y (V - \<Union> M)"
    using graph_invar_M assms(1,2) feasible_max_dualD(3)[OF assms(1)]
    by(force simp add: Vs_def comm_monoid_add_class.sum.union_disjoint[symmetric] algebra_simps 
                 dest: feasible_max_dualD(4)
               intro: arg_cong[of _ _ "sum y"])
  also have "... = sum y V"
    using assms(5) in_non_zero_verticesI subsetD 
    by(fastforce intro!: comm_monoid_add_class.sum.neutral simp add: vs_member)
  finally show ?thesis by simp
qed

corollary max_weight_if_tight_matching_covers_bads:
  assumes "feasible_max_dual V E w y" "graph_matching E M"
          "graph_invar E" "M \<subseteq> tight_subgraph E w y"
          "non_zero_vertices V y \<subseteq> Vs M"
    shows "max_weight_matching E w M" "min_feasible_max_dual V E w y"
  using assms
  by(auto intro: max_matching_pd_optimality equality_if_tight_matching_covers_bads)

definition "feasible_min_perfect_dual E w (y::'v \<Rightarrow> real) = 
 ((\<forall> e \<in> E. \<forall> u v. e ={u, v} \<longrightarrow> y u +  y v \<le> w e) )"

lemma feasible_min_perfect_dualI:
"(\<And> e u v. e \<in> E \<Longrightarrow> e ={u, v} \<Longrightarrow> y u +  y v \<le> w e)
\<Longrightarrow> feasible_min_perfect_dual E w y"
and feasible_min_perfect_dualE:
"feasible_min_perfect_dual E w y \<Longrightarrow>(
(\<And> e u v. e \<in> E \<Longrightarrow> e ={u, v} \<Longrightarrow> y u +  y v \<le> w e)
 \<Longrightarrow> P) \<Longrightarrow> P"
and feasible_min_perfect_dualD:
"feasible_min_perfect_dual E w y \<Longrightarrow> e \<in> E \<Longrightarrow> e ={u, v} \<Longrightarrow> y u +  y v \<le> w e"
  by(auto simp add: feasible_min_perfect_dual_def)

definition "max_feasible_min_perfect_dual E w y =
 (feasible_min_perfect_dual E w y \<and>
 (\<forall> y'. feasible_min_perfect_dual E w y' \<longrightarrow> sum y (Vs E) \<ge> sum y' (Vs E)))"

lemma max_feasible_min_perfect_dualE:
"max_feasible_min_perfect_dual  E w y \<Longrightarrow>
(feasible_min_perfect_dual  E w y \<Longrightarrow>
(\<And> y'. feasible_min_perfect_dual  E w y' \<Longrightarrow> sum y (Vs E) \<ge> sum y' (Vs E)) \<Longrightarrow> P)
\<Longrightarrow> P"
and max_feasible_min_perfect_dualI:
"feasible_min_perfect_dual E w y \<Longrightarrow>
(\<And> y'. feasible_min_perfect_dual E w y' \<Longrightarrow> sum y (Vs E) \<ge> sum y' (Vs E)) \<Longrightarrow> 
max_feasible_min_perfect_dual E w y"
and max_feasible_min_perfect_dualD:
"max_feasible_min_perfect_dual E w y \<Longrightarrow>feasible_min_perfect_dual E w y"
"max_feasible_min_perfect_dual E w y \<Longrightarrow> feasible_min_perfect_dual E w y'
 \<Longrightarrow> sum y (Vs E) \<ge> sum y' (Vs E)"
  by(auto simp add: max_feasible_min_perfect_dual_def)

definition "min_weight_perfect_matching E w M =
  (perfect_matching E M \<and> (\<forall> M'. perfect_matching E M' \<longrightarrow> sum w M' \<ge> sum w M))"

lemma min_weight_perfect_matchingI:
"perfect_matching E M \<Longrightarrow> (\<And> M'. perfect_matching E M' \<Longrightarrow> sum w M' \<ge> sum w M)
\<Longrightarrow> min_weight_perfect_matching E w M"
and min_weight_perfect_matchingE:
"min_weight_perfect_matching E w M \<Longrightarrow> 
(perfect_matching E M \<Longrightarrow> (\<And> M'. perfect_matching E M' \<Longrightarrow> sum w M' \<ge> sum w M) \<Longrightarrow> P)
\<Longrightarrow> P"
and min_weight_perfect_matchingD:
"min_weight_perfect_matching E w M \<Longrightarrow> perfect_matching E M"
"min_weight_perfect_matching E w M \<Longrightarrow> perfect_matching E M' \<Longrightarrow> sum w M' \<ge> sum w M"
  by(auto simp add: min_weight_perfect_matching_def)

lemma min_perfect_matching_weak_duality:
  assumes "feasible_min_perfect_dual E w y" "perfect_matching E M"
          "graph_invar E"                                  
  shows   "sum w M \<ge> sum y (Vs E)"
proof-
  have graph_invar_M: "graph_invar M"
    using assms(2,3) graph_invar_subset 
    by(auto dest!: perfect_matchingD(1))
  have Ms_finite: "Ball M finite"
    using graph_invar_M by blast
  have Ms_disjoint: "\<forall>A\<in>M. \<forall>B\<in>M. A \<noteq> B \<longrightarrow> A \<inter> B = {}" 
    using  assms(2) 
    by (simp add: matching_def perfect_matching_def)
  have "sum w M \<ge> ((sum \<circ> sum) y M)"
    using assms(1,2)  graph_invar_M 
    by(fastforce intro!: ordered_comm_monoid_add_class.sum_mono 
                   dest: feasible_min_perfect_dualD(1) perfect_matching_subgraphD)
  moreover have "((sum \<circ> sum) y M) = sum y (\<Union> M)"
    by(auto simp add:Vs_def comm_monoid_add_class.sum.Union_disjoint[OF Ms_finite Ms_disjoint])
  moreover have "sum y (\<Union> M) = sum y (Vs E)" 
    using   assms(1,2) 
    by(auto simp add: Vs_def 
               elim!: feasible_min_perfect_dualE perfect_matchingE)
  ultimately show ?thesis by simp
qed

corollary min_perfect_matching_pd_optimality:
  assumes "feasible_min_perfect_dual E w y" "perfect_matching E M"
          "graph_invar E"  "sum w M = sum y (Vs E)"
    shows "min_weight_perfect_matching E w M" "max_feasible_min_perfect_dual E w y"
  using assms min_perfect_matching_weak_duality
  by(force intro!: min_weight_perfect_matchingI max_feasible_min_perfect_dualI)+

lemma equality_if_tight_perfect_matching:
  assumes "feasible_min_perfect_dual E w y" "perfect_matching E M"
          "graph_invar E"  "M \<subseteq> tight_subgraph E w y"                                 
  shows   "sum w M = sum y (Vs E)"
proof-
  have graph_invar_M: "graph_invar M"
    using assms(2,3) graph_invar_subset 
    by(auto dest!: perfect_matchingD(1))
  have Ms_finite: "Ball M finite"
    using graph_invar_M by blast
  have Ms_disjoint: "\<forall>A\<in>M. \<forall>B\<in>M. A \<noteq> B \<longrightarrow> A \<inter> B = {}" 
    using  assms(2) 
    by (simp add: matching_def perfect_matching_def)
  have "sum w M = ((sum \<circ> sum) y M)"
    using assms(4) 
    by (fastforce intro: comm_monoid_add_class.sum.cong in_tight_subgraphD[of _ E w y]
         elim:  dblton_graphE[OF graph_invar_dblton[OF graph_invar_M]])+
  moreover have "((sum \<circ> sum) y M) = sum y (\<Union> M)"
    by(auto simp add:Vs_def comm_monoid_add_class.sum.Union_disjoint[OF Ms_finite Ms_disjoint])
  moreover have "sum y (\<Union> M) = sum y (Vs E)" 
    using   assms(1,2) 
    by(auto simp add: Vs_def 
               elim!: feasible_min_perfect_dualE perfect_matchingE)
  ultimately show ?thesis by simp
qed

corollary min_weight_perfect_if_tight:
  assumes "feasible_min_perfect_dual E w y" "perfect_matching E M"
          "graph_invar E"  "M \<subseteq> tight_subgraph E w y"
    shows "min_weight_perfect_matching E w M" "max_feasible_min_perfect_dual E w y"
  using assms
  by(auto intro: min_perfect_matching_pd_optimality
                 max_matching_pd_optimality equality_if_tight_perfect_matching)

end