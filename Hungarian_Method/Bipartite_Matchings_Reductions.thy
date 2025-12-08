theory Bipartite_Matchings_Reductions
  imports Primal_Dual_Bipartite_Matching.Matching_LP  Hungarian_Method_Top_Loop
begin

lemma max_card_matchingE:
  "max_card_matching G M \<Longrightarrow>
 (\<lbrakk> M \<subseteq> G; matching M; \<And> M'. \<lbrakk>M' \<subseteq> G; matching M'\<rbrakk> \<Longrightarrow> card M' \<le> card M\<rbrakk> \<Longrightarrow> P)
\<Longrightarrow> P"
  by(auto simp add: max_card_matching_def)

section \<open>Variants of Weighted Matching\<close>

subsection \<open>Definitions\<close>

thm max_weight_matching_def
thm min_weight_perfect_matching_def

definition "min_weight_matching E w M =
  (graph_matching E M \<and> (\<forall> M'. graph_matching E M' \<longrightarrow> ((sum w M')::real) \<ge> sum w M))"

lemma min_weight_matchingI:
  "graph_matching E M \<Longrightarrow> (\<And> M'. graph_matching E M' \<Longrightarrow> sum w M' \<ge> sum w M)
\<Longrightarrow> min_weight_matching E w M"
  and min_weight_matchingE:
  "min_weight_matching E w M \<Longrightarrow> 
(graph_matching E M \<Longrightarrow> (\<And> M'. graph_matching E M' \<Longrightarrow> sum w M' \<ge> sum w M) \<Longrightarrow> P)
\<Longrightarrow> P"
  and min_weight_matchingD:
  "min_weight_matching E w M \<Longrightarrow> graph_matching E M"
  "min_weight_matching E w M \<Longrightarrow> graph_matching E M' \<Longrightarrow> sum w M' \<ge> sum w M"
  by(auto simp add: min_weight_matching_def)

lemma min_weight_matching_only_negs:
  "\<lbrakk>min_weight_matching G w M; finite M;e \<in> M\<rbrakk> \<Longrightarrow> w e \<le> 0"
proof(rule ccontr, goal_cases)
  case 1
  have "graph_matching G (M - {e})"
    using "1"(1) min_weight_matchingD(1)
    by(auto intro!:  matching_delete)
  moreover have "sum w (M - {e}) < sum w M"
    using 1(3,4)
    by(auto simp add: sum_diff1[OF 1(2)])
  ultimately show False
    using 1(1)
    by(auto elim!: min_weight_matchingE)
qed

definition "max_weight_perfect_matching E w M =
  (perfect_matching E M \<and> (\<forall> M'. perfect_matching E M' \<longrightarrow> (sum w M'::real) \<le> sum w M))"

lemma max_weight_perfect_matchingI:
  "perfect_matching E M \<Longrightarrow> (\<And> M'. perfect_matching E M' \<Longrightarrow> sum w M' \<le> sum w M)
\<Longrightarrow> max_weight_perfect_matching E w M"
  and max_weight_perfect_matchingE:
  "max_weight_perfect_matching E w M \<Longrightarrow> 
(perfect_matching E M \<Longrightarrow> (\<And> M'. perfect_matching E M' \<Longrightarrow> sum w M' \<le> sum w M) \<Longrightarrow> P)
\<Longrightarrow> P"
  and max_weight_perfect_matchingD:
  "max_weight_perfect_matching E w M \<Longrightarrow> perfect_matching E M"
  "max_weight_perfect_matching E w M \<Longrightarrow> perfect_matching E M' \<Longrightarrow> sum w M' \<le> sum w M"
  by(auto simp add: max_weight_perfect_matching_def)

lemma max_weight_matching_only_negs:
  "\<lbrakk>max_weight_matching G w M; finite M;e \<in> M\<rbrakk> \<Longrightarrow> w e \<ge> 0"
proof(rule ccontr, goal_cases)
  case 1
  have "graph_matching G (M - {e})"
    using "1"(1) max_weight_matchingD(1)
    by(auto intro!:  matching_delete)
  moreover have "sum w (M - {e}) > sum w M"
    using 1(3,4)
    by(auto simp add: sum_diff1[OF 1(2)])
  ultimately show False
    using 1(1)
    by(auto elim!: max_weight_matchingE)
qed

definition "max_weight_max_card_matching E w M =
  (max_card_matching E M \<and> (\<forall> M'. max_card_matching E M' \<longrightarrow> (sum w M'::real) \<le> sum w M))"

lemma max_weight_max_card_matchingI:
  "max_card_matching E M \<Longrightarrow> (\<And> M'. max_card_matching E M' \<Longrightarrow> sum w M' \<le> sum w M)
\<Longrightarrow> max_weight_max_card_matching E w M"
  and max_weight_max_card_matchingE:
  "max_weight_max_card_matching E w M \<Longrightarrow> 
(max_card_matching E M \<Longrightarrow> (\<And> M'. max_card_matching E M' \<Longrightarrow> sum w M' \<le> sum w M) \<Longrightarrow> P)
\<Longrightarrow> P"
  and max_weight_max_card_matchingD:
  "max_weight_max_card_matching E w M \<Longrightarrow> max_card_matching E M"
  "max_weight_max_card_matching E w M \<Longrightarrow> max_card_matching E M' \<Longrightarrow> sum w M' \<le> sum w M"
  by(auto simp add: max_weight_max_card_matching_def)

definition "min_weight_max_card_matching E w M =
  (max_card_matching E M \<and> (\<forall> M'. max_card_matching E M' \<longrightarrow> (sum w M'::real) \<ge> sum w M))"

lemma min_weight_max_card_matchingI:
  "max_card_matching E M \<Longrightarrow> (\<And> M'. max_card_matching E M' \<Longrightarrow> sum w M' \<ge> sum w M)
\<Longrightarrow> min_weight_max_card_matching E w M"
  and min_weight_max_card_matchingE:
  "min_weight_max_card_matching E w M \<Longrightarrow> 
(max_card_matching E M \<Longrightarrow> (\<And> M'. max_card_matching E M' \<Longrightarrow> sum w M' \<ge> sum w M) \<Longrightarrow> P)
\<Longrightarrow> P"
  and min_weight_max_card_matchingD:
  "min_weight_max_card_matching E w M \<Longrightarrow> max_card_matching E M"
  "min_weight_max_card_matching E w M \<Longrightarrow> max_card_matching E M' \<Longrightarrow> sum w M' \<ge> sum w M"
  by(auto simp add: min_weight_max_card_matching_def)

lemma 
  assumes "finite G"
  shows finite_number_of_matchings: "finite (Collect (graph_matching G))"
    and finite_number_of_perfect_matchings: "finite (Collect (perfect_matching G))"
    and finite_number_of_max_card_matchings: "finite (Collect (max_card_matching G))"
  using assms
  by(auto intro!: finite_subset[of _ "Pow G"] simp add: perfect_matching_def max_card_matching_def)

lemma empty_is_graph_matching: "graph_matching G {}"
  using matching_empty by blast

(*TODO MOVE*)
lemma minimiser_of_function_nempty_finite:
  assumes "finite X" "X \<noteq> {}"
  obtains x where "x \<in> X" "\<And> y. y \<in> X \<Longrightarrow> ((f x)::'a::linorder) \<le> f y"
proof(goal_cases)
  case 1
  define MX where "MX = {f x | x. x \<in> X}"
  have "Min MX \<in> MX"
    using assms
    by(intro linorder_class.Min_in) (auto simp add: MX_def)
  then obtain x where x: "f x = Min MX" "x \<in> X"
    by(auto simp add: MX_def)
  hence "\<And> y. y \<in> X \<Longrightarrow> ((f x)::'a::linorder) \<le> f y"
    using assms
    by(auto intro!: linorder_class.Min.coboundedI 
        simp add: MX_def)
  thus thesis
    using 1 x by auto
qed

lemma maximiser_of_function_nempty_finite:
  assumes "finite X" "X \<noteq> {}"
  obtains x where "x \<in> X" "\<And> y. y \<in> X \<Longrightarrow> ((f x)::'a::linorder) \<ge> f y"
proof(goal_cases)
  case 1
  define MX where "MX = {f x | x. x \<in> X}"
  have "Max MX \<in> MX"
    using assms
    by(intro linorder_class.Max_in) (auto simp add: MX_def)
  then obtain x where x: "f x = Max MX" "x \<in> X"
    by(auto simp add: MX_def)
  hence "\<And> y. y \<in> X \<Longrightarrow> ((f x)::'a::linorder) \<ge> f y"
    using assms
    by(auto intro!:  linorder_class.Max.coboundedI 
        simp add: MX_def)
  thus thesis
    using 1 x by auto
qed

lemma min_matching_exists:
  assumes "finite G"
  obtains M' where "min_weight_matching G w M'"
  apply(rule  minimiser_of_function_nempty_finite[of "Collect (graph_matching G)" "sum w"])
  using finite_number_of_matchings[OF assms(1)] 
  by(auto intro!: exI[of _ "{}"] simp add: min_weight_matching_def)

lemma max_card_matching_exists:
  assumes "finite G"
  obtains M' where "max_card_matching G M'"
  apply(rule  maximiser_of_function_nempty_finite[of "Collect (graph_matching G)" card])
  using finite_number_of_matchings[OF assms(1)] 
  by(auto intro!: exI[of _ "{}"] simp add: max_card_matching_def)

lemma min_perfect_matching_exists:
  assumes "finite G" "perfect_matching G M"
  obtains M' where "min_weight_perfect_matching G w M'"
  apply(rule  minimiser_of_function_nempty_finite[of "Collect (perfect_matching G)" "sum w"])
  using finite_number_of_perfect_matchings[OF assms(1)] assms(2)
  by(auto simp add: min_weight_perfect_matching_def)

lemma min_weight_max_card_matching_exists:
  assumes "finite G"
  obtains M' where "min_weight_max_card_matching G w M'"
  apply(rule  minimiser_of_function_nempty_finite[of "Collect (max_card_matching G)" "sum w"])
  using finite_number_of_max_card_matchings[OF assms(1)]
  by(auto simp add: min_weight_max_card_matching_def 
      intro: max_card_matching_exists[OF assms(1)])

lemma max_matching_exists:
  assumes "finite G"
  obtains M' where "max_weight_matching G w M'"
  apply(rule  maximiser_of_function_nempty_finite[of "Collect (graph_matching G)" "sum w"])
  using finite_number_of_matchings[OF assms(1)]
  by(auto simp add: max_weight_matching_def 
      intro: exI[of _ "{}"])

lemma max_perfect_matching_exists:
  assumes "finite G" "perfect_matching G M"
  obtains M' where "max_weight_perfect_matching G w M'"
  apply(rule  maximiser_of_function_nempty_finite[of "Collect (perfect_matching G)" "sum w"])
  using finite_number_of_perfect_matchings[OF assms(1)] assms(2)
  by(auto simp add: max_weight_perfect_matching_def)

lemma max_weight_max_card_matching_exists:
  assumes "finite G"
  obtains M' where "max_weight_max_card_matching G w M'"
  apply(rule  maximiser_of_function_nempty_finite[of "Collect (max_card_matching G)" "sum w"])
  using finite_number_of_max_card_matchings[OF assms(1)]
  by(auto simp add: max_weight_max_card_matching_def
      intro: max_card_matching_exists[OF assms(1)])

lemma perfect_matching_card:
  assumes "perfect_matching G M" "graph_abs G"
  shows "2* card M = card (Vs G)" 
  using assms
  by(subst graph_abs.matching_card_vs)
    (auto intro: graph_abs_mono 
      simp add: perfect_matching_def)

lemma perfect_matchings_same_card:
  "\<lbrakk>perfect_matching G M; perfect_matching G M'; graph_abs G\<rbrakk> \<Longrightarrow> card M = card M'"
  by(auto intro!: max_card_matchings_same_size graph_abs.perfect_matching_is_max_card_matching)

lemma perfect_matching_card':  
  assumes "perfect_matching G M" "graph_abs G"
  shows "card M = card (Vs G) div 2"
  using  perfect_matching_card assms by fastforce

subsection \<open>Reductions\<close>
  (*max weight    max weight max card
     |                |
     v                v
   min weight   min weight max card
     |                |
     v                v
     min weight perfect <-- max weight perfect
*)
subsubsection \<open>Relationships between Weight Minimisation, Weight Maximisation 
               and Cardinality Maximisation\<close>

lemma min_and_max_matching:
  "min_weight_matching G w M \<longleftrightarrow> max_weight_matching G (- w) M"
  by(auto intro!: min_weight_matchingI max_weight_matchingI
      elim!:  min_weight_matchingE max_weight_matchingE
      simp add: sum_negf)

lemma min_perfect_and_max_perfect_matching:
  "min_weight_perfect_matching G w M \<longleftrightarrow> max_weight_perfect_matching G (- w) M"
  by(auto intro!: min_weight_perfect_matchingI max_weight_perfect_matchingI
      elim!:  min_weight_perfect_matchingE max_weight_perfect_matchingE
      simp add: sum_negf)

lemma min_max_card_and_max_max_card_matching:
  "min_weight_max_card_matching G w M \<longleftrightarrow> max_weight_max_card_matching G (- w) M"
  by(auto intro!: min_weight_max_card_matchingI max_weight_max_card_matchingI
      elim!:  min_weight_max_card_matchingE max_weight_max_card_matchingE
      simp add: sum_negf)

lemma max_unit_weight_max_card_matching:
  "max_weight_matching G (\<lambda> e. 1) M \<longleftrightarrow> max_card_matching G M"
  by(auto elim!: max_weight_matchingE max_card_matchingE
         intro!: max_weight_matchingI max_card_matchingI)

subsubsection \<open>Maximum Weight (Maximum Cardinality) to Minimum Weight Perfect (Bipartite)\<close>

datatype 'v bp_vertex_wrapper = old_vertex (the_vertex: 'v) | new_vertex nat

definition "bp_perfected_G G L R= 
  {{old_vertex u, old_vertex v} | u v. u \<in> L \<and> v \<in> R} \<union>
   {{new_vertex i, old_vertex v} | i v. i < card R - card L \<and> v \<in> R} \<union>
   {{old_vertex u, new_vertex i} | i u. i < card L - card R \<and> u \<in> L}"

definition "bp_perfected_L L R= 
  old_vertex ` L \<union> {new_vertex i | i . i < card R - card L }"

definition "bp_perfected_R L R= 
  old_vertex ` R \<union> {new_vertex i | i . i < card L - card R}"

definition "complete_bipartite G L R = 
   (bipartite G L R \<and> (\<forall> u \<in> L. \<forall> v \<in> R. {u, v} \<in> G))"

lemma complete_bipartiteE:
  "complete_bipartite G L R \<Longrightarrow>
  (\<lbrakk>bipartite G L R; \<And> u v. \<lbrakk>u \<in> L; v \<in> R\<rbrakk> \<Longrightarrow> {u, v} \<in> G\<rbrakk> \<Longrightarrow> P)
  \<Longrightarrow> P"
  and complete_bipartiteI:
  "\<lbrakk>bipartite G L R; \<And> u v. \<lbrakk>u \<in> L; v \<in> R\<rbrakk> \<Longrightarrow> {u, v} \<in> G\<rbrakk> \<Longrightarrow> complete_bipartite G L R"
  and complete_bipartiteD:
  "complete_bipartite G L R \<Longrightarrow> bipartite G L R"
  "\<lbrakk>complete_bipartite G L R; u \<in> L; v \<in> R\<rbrakk> \<Longrightarrow> {u, v} \<in> G"
  by(auto simp add: complete_bipartite_def)

lemma complete_bipartite_Vs:
  assumes "complete_bipartite G L R" "dblton_graph G" "L = {} \<longleftrightarrow> R = {}"
  shows "Vs G = L \<union> R"
  using assms
  by(auto elim!: complete_bipartiteE bipartite_edgeE 
      intro: bipartite_vertex(3) 
      dest!: edges_are_Vs) blast

definition "balanced_complete_bipartite G L R = 
  (complete_bipartite G L R \<and> card L = card R)"

lemma balanced_complete_bipartiteE:
  "balanced_complete_bipartite G L R \<Longrightarrow>
 (\<lbrakk>complete_bipartite G L R; card L = card R\<rbrakk> \<Longrightarrow> P)
 \<Longrightarrow> P"
  and balanced_complete_bipartiteI:
  "\<lbrakk>complete_bipartite G L R; card L = card R\<rbrakk> \<Longrightarrow> balanced_complete_bipartite G L R"
  and balanced_complete_bipartiteD:
  "balanced_complete_bipartite G L R \<Longrightarrow> complete_bipartite G L R"
  "balanced_complete_bipartite G L R \<Longrightarrow> card L = card R"
  by(auto simp add: balanced_complete_bipartite_def)
    (*TODO MOVE*)
lemma set_of_f_up_to_n_image:"{f i |i. i < n} = f ` {0..<n::nat}" 
  by auto

lemma perfected_vertices_empty_same:
  "\<lbrakk> finite L; finite R\<rbrakk> \<Longrightarrow> (bp_perfected_L L R) = {} \<longleftrightarrow>  (bp_perfected_R L R) = {}"
  using card_gt_0_iff by(force simp add: bp_perfected_L_def bp_perfected_R_def)

lemma balanced_complete_bipartite_perfected:
  assumes "bipartite G L R" "finite L" "finite R"
  shows "balanced_complete_bipartite (bp_perfected_G G L R)
              (bp_perfected_L L R)  (bp_perfected_R L R)" (is ?th1)
    and balanced_complete_bipartite_perfected_side_cards:
    "card (bp_perfected_L L R) = max (card L) (card R)"
    "card (bp_perfected_R L R) = max (card L) (card R)"
proof-
  have card_hleper:  
    "card (old_vertex ` L \<union> {new_vertex i |i. i < card R - card L}) =
    card (old_vertex ` R \<union> {new_vertex i |i. i < card L - card R})"
    using assms(2,3)
    apply(subst card_Un_disjoint, simp, simp, force)
    apply(subst card_Un_disjoint)
    by(auto simp add: set_of_f_up_to_n_image card_image inj_on_def)
  show ?th1
    using assms
    by(auto intro!: balanced_complete_bipartiteI complete_bipartiteI 
        simp add: bp_perfected_G_def bp_perfected_R_def 
        bp_perfected_L_def bipartite_def card_hleper)+
  have "card L < card R 
    \<Longrightarrow> card (old_vertex ` L \<union> {new_vertex i |i. i < card R - card L}) = card R"
    using assms(2,3)
    by(subst card_Un_disjoint)
      (auto simp add: set_of_f_up_to_n_image card_image inj_on_def)
  thus  "card (bp_perfected_L L R) = max (card L) (card R)"
    by(cases "card L < card R")
      (auto simp add: bp_perfected_L_def bp_perfected_R_def inj_on_def intro!: card_image)
  have "\<not> card L < card R \<Longrightarrow> card (old_vertex ` R \<union> {new_vertex i |i. i < card L - card R}) = card L"
    using assms(2,3)
    by(subst card_Un_disjoint)
      (auto simp add: set_of_f_up_to_n_image card_image inj_on_def)
  thus   "card (bp_perfected_R L R) = max (card L) (card R)"
    by(cases "card L < card R")
      (auto simp add: bp_perfected_L_def bp_perfected_R_def inj_on_def intro!: card_image)
qed

lemma bipartite_to_graph_abs:
  "\<lbrakk>bipartite G L R; finite G\<rbrakk> \<Longrightarrow> graph_abs G"
  by(fastforce simp add: bipartite_def graph_abs_def dblton_graph_def disjoint_iff
      intro!: finite_dbl_finite_verts) 

lemma bipartite_L_R_matched_perfect:
  assumes "bipartite G L R" "finite G" "finite L" "finite R"
    "graph_matching G M"
    "2*card M = card L + card R"
  shows "perfect_matching G M"
proof(rule ccontr, goal_cases)
  case 1
  then obtain u where u: "u \<in> Vs G" "u \<notin> Vs M" 
    using assms(5) 
    by(auto simp add: perfect_matching_def dest: Vs_subset)
  have Vs_M_L_R:"Vs M = Vs M \<inter> L \<union> Vs M \<inter> R"
    using assms(5)  bipartite_vs_subset[OF assms(1)] assms(1)
    by (auto dest!: bipartite_vertex(4)[OF _ bipartite_subgraph])
  have "2*card M = card (Vs M)"
    using assms(1,2,5)
    by(auto intro!: graph_abs.matching_card_vs graph_abs_mono[OF bipartite_to_graph_abs, of G L R M])
  also have "... = card (Vs M \<inter> L) + card (Vs M \<inter> R)"
    apply(subst card_Un_disjoint[symmetric])
    using assms(1,2,5) graph_abs.finite_Vs[OF graph_abs_mono[of G M] ]
      bipartite_to_graph_abs[OF assms(1)] bipartite_disjointD Vs_M_L_R 
    by auto
  also have "... < card L + card R"
  proof(cases "u \<in> L")
    case True
    have "card (Vs M \<inter> L) + card (Vs M \<inter> R) \<le>card (Vs M \<inter> L) + card R"
      by (auto intro!: card_mono assms(4))
    moreover have "... < card L + card R"
      using True u(2)
      by (auto intro!: psubset_card_mono assms(3))
    ultimately show ?thesis 
      by simp
  next
    case False
    hence False: "u \<in> R" 
      using assms(1)  u(1)
      by(auto intro: bipartite_vertex(3))
    have "card (Vs M \<inter> L) + card (Vs M \<inter> R) \<le> card (Vs M \<inter> R) + card L"
      by (auto intro!: card_mono assms(3))
    moreover have "... < card L + card R"
      using False u(2)
      by (auto intro!: psubset_card_mono assms(4))
    ultimately show ?thesis 
      by simp
  qed
  finally have "2*card M < card L + card R"
    by simp
  thus False
    using assms(6) by simp
qed

lemma extending_perfect_matching_in_balanced_complete_bipartite:
  assumes "balanced_complete_bipartite G L R"
    "graph_matching G M" "finite G"
  shows "\<exists> M'. perfect_matching G M' \<and> M' \<supseteq> M"
proof-
  define unmatched where "unmatched = card G - card M"
  note G_props = complete_bipartiteD[OF balanced_complete_bipartiteD(1)[OF assms(1)]]
    balanced_complete_bipartiteD(2)[OF assms(1)]
  show ?thesis
    using assms(2) unmatched_def
  proof(induction unmatched arbitrary: M rule: less_induct)
    case (less unmatched)
    note IH = this
    show ?case 
    proof(cases "perfect_matching G M")
      case True
      then show ?thesis by auto
    next
      case False
      then obtain a where a: "a \<notin> Vs M" "a \<in> Vs G" 
        using less.prems(1)  subgraph_vs_subset_eq [of G M]
        by(auto simp add: perfect_matching_def dest: Vs_subset) 
      obtain u where u: "u \<in> L" "u \<notin> Vs M" 
      proof(rule ccontr, goal_cases)
        case 1
        hence "L \<subseteq> Vs M" by blast
        moreover hence "L \<noteq> {} \<Longrightarrow> card L > 0" 
          using a  G_props(1) assms(3) less.prems(1)
            graph_invar_subset[OF finite_bipartite_graph_invar[OF assms(3) G_props(1)], of M]       
          by (auto simp add: finite_subset card_gt_0_iff)
        moreover hence "finite R"
          using G_props(1, 3) a(2) bipartite_empty_part_iff_empty[of G R] by force
        ultimately have "perfect_matching G M" 
          using G_props IH(2)
          by(auto intro!: all_left_matched_perfect[of G L R M])
        thus False
          using False by simp
      qed
      obtain v where v: "v \<in> R" "v \<notin> Vs M" 
      proof(rule ccontr, goal_cases)
        case 1
        hence "R \<subseteq> Vs M" by blast
        moreover hence "L \<noteq> {} \<Longrightarrow> card L > 0" 
          using a  bipartite_commute[OF G_props(1)] assms(3) less.prems(1) G_props(3) 
            graph_invar_subset[OF finite_bipartite_graph_invar[OF assms(3) G_props(1)], of M]       
          by (auto simp add: finite_subset card_gt_0_iff vs_member elim!: bipartite_edgeE)
        moreover hence "finite L"
          using G_props(1, 3) a(2) bipartite_empty_part_iff_empty[of G R] by force
        ultimately have "perfect_matching G M" 
          using G_props IH(2)
          by(auto intro!: all_right_matched_perfect[of G L R M])    
        thus False
          using False by simp
      qed
      have uv: "{u, v} \<notin> M" "{u, v} \<in> G"
        using edges_are_Vs[of u v] u(2) G_props(2) u(1) v(1) by auto
      hence uvG:"{u, v} \<in> G"
        using G_props(2) by blast 
      have finiteM: "finite M"
        using assms(3) less.prems(1) rev_finite_subset by blast
      have "card (insert {u, v} M) \<le> card G"
        by (simp add: assms(3) card_mono less.prems(1) uvG)
      hence "card G - card (insert {u, v} M) < unmatched"
        using finiteM uv(1) by(auto simp add: IH(3))
      moreover have "graph_matching G ({{u, v}} \<union> M)"
        using uv IH(2) u(2) v(2) 
        by (auto intro!: matching_insert)
      ultimately obtain M' where "perfect_matching G M'" "insert {u, v} M \<subseteq> M'"
        using IH(1)[OF _ _ refl] by force
      thus ?thesis 
        by auto
    qed
  qed
qed

corollary perfect_matching_in_balanced_complete_bipartite:
  assumes "balanced_complete_bipartite G L R" "finite G"
  shows "\<exists> M. perfect_matching G M"
  using extending_perfect_matching_in_balanced_complete_bipartite[where M = empty] assms
  by auto

definition "penalty G w = (card (Vs G) / 2) * Max (insert 0 { \<bar>w e \<bar> | e. e \<in> G}) + 1"

lemma penalty_cost_neagation:"penalty G (-w) = penalty G w"
  by(auto simp add: penalty_def)

(*TODO MOVE*)

lemma card_of_non_empty_graph_geq_2:
  assumes "graph_invar G"  "G \<noteq> {}"
  shows "card (Vs G) \<ge> 2"
proof-
  obtain e where e_in_G:"e \<in> G"
    using assms(2) by auto
  then obtain u v where "e = {u, v}" "u \<noteq> v"
    using assms(1) by blast
  hence "card e = 2" by simp
  moreover have "card (Vs G) \<ge> card e"
    using e_in_G assms(1)
    by(auto intro!: card_mono)
  ultimately show ?thesis 
    by simp
qed

lemma penalty_gtr_0: 
  assumes"finite G" 
  shows  "penalty G w > 0"
proof-
  have "0 \<le> Max ({0} \<union> { \<bar>w e\<bar> |e. e \<in> G})"
    using assms by(auto simp add: Max_ge_iff)
  hence "0 \<le> real (card (Vs G)) * Max ({0} \<union> { \<bar>w e\<bar> |e. e \<in> G}) / 2" 
    by auto
  then show ?thesis
    by(auto simp add: penalty_def)
qed

lemma edge_weight_less_thatn_penalty:
  assumes "graph_invar G" "e \<in> G"
  shows "w e < penalty G w" 
proof-
  have "w e \<le> Max (insert 0 { \<bar>w e \<bar> | e. e \<in> G})"
    using graph_invar_finite[OF assms(1)] assms(2)
    by(auto simp add: Max_ge_iff)
  moreover have "... \<le> (card (Vs G) / 2) * Max (insert 0 { \<bar>w e\<bar> | e. e \<in> G})"
    using assms graph_invar_finite[OF assms(1)]
    by(intro ordered_semiring_class.mult_right_mono[of 1 "(card (Vs G) / 2)", simplified mult_1])
      (auto simp add: less_eq_Suc_le[symmetric] card_gt_0_iff intro!: card_of_non_empty_graph_geq_2)
  moreover have "... < penalty G w"
    by(auto simp add: penalty_def)
  ultimately show  "w e < penalty G w" 
    by simp+
qed

(*TODO MOVE*)
lemma (in graph_abs) matching_card_vs':
  assumes "matching G"
  shows "card G = card (Vs G) / 2"
  using assms by(simp add: matching_card_vs[symmetric])

lemma weight_of_matching_less_penalty:
  assumes "graph_invar G" "graph_matching G M"
  shows "sum w M < penalty G w"
proof-
  have zero_leq_Max: "0 \<le> Max ({0} \<union> { \<bar>w e\<bar> |e. e \<in> G})" and
    we_leq_Max: "e \<in> G \<Longrightarrow> w e \<le> Max ({0} \<union> { \<bar>w e\<bar> |e. e \<in> G})" for e
    using assms graph_invar_finite[OF assms(1)]
    by(auto simp add: Max_ge_iff)
  have "sum w M \<le> real (card M) * Max (insert 0 { \<bar>w e\<bar> | e. e \<in> G})"
    apply(subst semiring_1_class.sum_constant[of  "_::real", symmetric])
    apply(rule ordered_comm_monoid_add_class.sum_mono)
    using assms(2) we_leq_Max 
    by auto
  moreover have "... \<le> card (Vs G) / 2 * Max (insert 0 { \<bar>w e \<bar> | e. e \<in> G})"
    apply(rule ordered_semiring_class.mult_right_mono)
     apply(subst graph_abs.matching_card_vs')
    using assms(1,2) graph_abs.intro graph_abs_mono zero_leq_Max
    by (auto intro!: card_mono dest: subsetD[OF Vs_subset])
  moreover have "... < penalty G w"
    by(auto simp add: penalty_def)
  ultimately show ?thesis
    by simp
qed

lemma weight_of_matching_gtr_negated_penalty:
  assumes "graph_invar G" "graph_matching G M"
  shows "sum w M > -penalty G w"
proof-
  have "- sum w M < penalty G w"
    using weight_of_matching_less_penalty[OF assms, of "- w"]
    by(simp add: sum_negf[of w M, symmetric] penalty_cost_neagation[of G w, symmetric])
  thus ?thesis
    by simp
qed

lemma weight_of_matching_abs_less:
  assumes "graph_invar G" "graph_matching G M"
  shows "\<bar>sum w M\<bar> < penalty G w"
  using weight_of_matching_gtr_negated_penalty[OF assms, of w]
    weight_of_matching_less_penalty[OF assms, of w] 
  by(auto simp add: linordered_idom_class.abs_less_iff)

lemma weight_diff_of_matchings_less_than_2_penalties:
  assumes "graph_invar G" "graph_matching G M" "graph_matching G M'"
  shows "\<bar> sum w M - sum w M' \<bar> < 2*penalty G w"
  using weight_of_matching_abs_less[OF assms(1,2), of w]
    weight_of_matching_abs_less[OF assms(1,3), of w]
  by auto

definition "min_costs_to_min_perfect_costs G (w::'a set \<Rightarrow> real) =
            (\<lambda> e. if \<exists> i. new_vertex i \<in> e then 0
                  else if (the_vertex ` e) \<notin> G then 0
                  else min 0 (w (the_vertex ` e)))"

definition "min_max_card_costs_to_min_perfect_costs G (w::'a set \<Rightarrow> real) =
            (\<lambda> e. if \<exists> i. new_vertex i \<in> e then 2*penalty G w
                  else if (the_vertex ` e) \<notin> G then 2*penalty G w
                  else w (the_vertex ` e))"

lemma no_new_vertex_old_vertex_new_vertex_inverse:
  assumes "(\<And> i. new_vertex i \<noteq> x)" 
  shows"old_vertex ( the_vertex  x) = x"
  using assms
  by(cases x) auto

lemma no_new_vertex_old_vertex_new_vertex_image_inverse:
  assumes "(\<And> i. new_vertex i \<notin> e)" 
  shows"old_vertex ` the_vertex ` e = e"
proof(rule, all \<open>rule\<close>, goal_cases)
  case (1 x)
  then obtain x' where x': "x' \<in> the_vertex ` e" "x = old_vertex x'" by blast
  moreover then obtain x'' where x'': "x'' \<in> e" "x' = the_vertex x''" by auto
  ultimately have "x = x''"
    using assms by(cases x'') auto
  then show ?case 
    using x'' by blast
next
  case (2 x)
  then obtain x' where "x = old_vertex x'" "the_vertex x = x'"
    using assms 
    by(cases x) auto
  then show ?case 
    using 2
    by (auto intro!: image_eqI)
qed

lemma old_vertex_of_the_vertex_contained:
  "\<lbrakk>\<And>i. new_vertex i \<notin> x; xc \<in> x\<rbrakk> \<Longrightarrow> old_vertex (the_vertex xc) \<in> x"
  using no_new_vertex_old_vertex_new_vertex_image_inverse by blast

lemma no_new_vertex_new_vertex_old_vertex_image_inverse:
  "the_vertex ` old_vertex ` e = e"
  by (auto intro!: image_eqI)

lemma "min_costs_to_min_perfect_costs G w e < 0 
        \<Longrightarrow> \<exists> e'. e = old_vertex ` e' \<and> w e' < 0 \<and> e' \<in> G"
  by(auto simp add: min_costs_to_min_perfect_costs_def if_split[of "\<lambda> x. 0 > x"]
      no_new_vertex_old_vertex_new_vertex_image_inverse[of e] 
      intro!: exI[of _ "the_vertex ` e"] | 
      subst no_new_vertex_old_vertex_new_vertex_inverse)+

definition "min_w_perfect_to_max_w_matching M w = {e | e. e \<in> M \<and> w e > 0}"
  (*TODO MOVE*)

lemma matchingI:
  "(\<And>e1 e2. \<lbrakk>e1 \<in> M; e2 \<in> M; e1 \<noteq> e2\<rbrakk> \<Longrightarrow> e1 \<inter> e2 = {}) \<Longrightarrow> matching M"
  by (auto simp: matching_def)

lemma max_weight_matching_unused_edges:
  assumes "max_weight_matching G w M" "e \<in> G" 
    "e \<inter> Vs M = {}" "e \<noteq> {}" "finite M"
  shows "w e \<le> 0"
proof(rule ccontr, goal_cases)
  case 1
  hence "sum w (insert e M) > sum w M"
    using assms
    by(subst comm_monoid_add_class.sum.insert) auto
  moreover have "graph_matching G (insert e M)"
    using assms 
    by(auto elim!: max_weight_matchingE intro: matchingI
        dest: matching_unique_match)
  ultimately show False
    using assms(1)
    by(auto elim!:  max_weight_matchingE)
qed

lemma min_weight_matching_unused_edges:
  assumes "min_weight_matching G w M" "e \<in> G" 
    "e \<inter> Vs M = {}" "e \<noteq> {}" "finite M"
  shows "w e \<ge> 0"
proof(rule ccontr, goal_cases)
  case 1
  hence "sum w (insert e M) < sum w M"
    using assms
    by(subst comm_monoid_add_class.sum.insert) auto
  moreover have "graph_matching G (insert e M)"
    using assms 
    by(auto elim!: min_weight_matchingE intro: matchingI
        dest: matching_unique_match)
  ultimately show False
    using assms(1)
    by(auto elim!: min_weight_matchingE)
qed

lemma matching_on_old_vertices:
  "matching M \<longleftrightarrow> matching ((image old_vertex )` M)"
  by(auto intro!: matchingI elim!: matchingE) blast+

lemma inj_image_rev_mono:"\<lbrakk>inj f; f `A \<subseteq> f `B\<rbrakk> \<Longrightarrow> A \<subseteq> B"
  by (auto simp add: in_mono inj_image_subset_iff)

lemma old_vertex_rev_mono: 
  "(image old_vertex)` G \<subseteq> (image old_vertex)` G' \<Longrightarrow> G \<subseteq> G'"
  by(rule inj_image_rev_mono)
    (auto intro!: inj_on_image simp add: inj_def)

lemma graph_matching_on_old_vertices:
  "graph_matching G M \<longleftrightarrow> graph_matching ((image old_vertex )` G) ((image old_vertex )` M)"
  using matching_on_old_vertices 
  by (auto dest!: old_vertex_rev_mono)

definition "project_to_old G = {the_vertex ` e | e. e\<in> G \<and> (\<nexists> i. new_vertex i \<in> e)}"

lemma project_to_old_mono:
  "G \<subseteq> G' \<Longrightarrow> project_to_old G \<subseteq> project_to_old G'"
  by(auto simp add: project_to_old_def)

lemma matching_on_project_to_old:
  "matching M \<Longrightarrow> matching (project_to_old M)"
proof(rule matchingI, goal_cases)
  case (1 e1 e2)
  then obtain e1' e2' where e1e2:"e1 = the_vertex ` e1'" "e2 = the_vertex ` e2'"
    "e1' \<in> M" "e2' \<in> M" "(\<nexists> i. new_vertex i \<in> e1')" "(\<nexists> i. new_vertex i \<in> e2')"
    by(auto simp add: project_to_old_def)
  hence "e1' \<inter> e2' = {}" 
    using  "1"(1,4) 
    by(elim matchingE)blast
  moreover have "e1' = old_vertex ` e1" 
    using e1e2(1,5) no_new_vertex_old_vertex_new_vertex_image_inverse 
    by blast
  moreover have "e2' = old_vertex ` e2" 
    using e1e2(2,6) no_new_vertex_old_vertex_new_vertex_image_inverse 
    by blast
  ultimately show ?case
    by auto
qed

lemma graph_matching_on_project_to_old:
  "graph_matching G M \<Longrightarrow> graph_matching (project_to_old G) (project_to_old M)"
  using matching_on_project_to_old project_to_old_mono by auto

lemma the_vertex_inj:
  "\<lbrakk>\<nexists> i. x = new_vertex i; \<nexists> i. y = new_vertex i; the_vertex x = the_vertex y\<rbrakk> \<Longrightarrow> x = y"
  by(cases x, all \<open>cases y\<close>) auto

lemma the_vertex_image_inj:
  "\<lbrakk>\<nexists> i. new_vertex i \<in> x; \<nexists> i. new_vertex i \<in> y; the_vertex ` x = the_vertex ` y\<rbrakk> \<Longrightarrow> x = y"
  by (metis no_new_vertex_old_vertex_new_vertex_image_inverse)

lemma graph_matching_bigger_graph:
  "\<lbrakk>graph_matching G M; G \<subseteq> G'\<rbrakk> \<Longrightarrow> graph_matching G' M"
  by auto

lemma finite_G_finite_completion:
  "\<lbrakk>finite G; finite L; finite R\<rbrakk> \<Longrightarrow> finite (bp_perfected_G G L R)"
proof(unfold bp_perfected_G_def, rule finite_UnI, rule finite_UnI, goal_cases)
  case 1
  thus ?case
    by (auto simp add: image_iff 
        intro!: finite_surj[of "L \<times> R" _  "\<lambda> x. {old_vertex (fst x), old_vertex (snd x)}"] 
        bexI)
next
  case 2
  thus ?case
    by (auto simp add: image_iff 
        intro!: finite_surj[of "R \<times> {0..< card R - card L}" _  
          "\<lambda> x. {old_vertex (fst x), new_vertex (snd x)}"] bexI)
next
  case 3
  thus ?case
    by (auto  intro!:  finite_surj[of "L \<times> {0..< card L - card R}" _  
          "\<lambda> x. {old_vertex (fst x), new_vertex (snd x)}"] bexI
        simp add: image_iff)
qed

lemma finite_L_finite_completion:
  "\<lbrakk>finite L\<rbrakk> \<Longrightarrow> finite (bp_perfected_L L R)"
  by(auto simp add: bp_perfected_L_def)

lemma finite_R_finite_completion:
  "\<lbrakk>finite R\<rbrakk> \<Longrightarrow> finite (bp_perfected_R L R)"
  by(auto simp add: bp_perfected_R_def)

lemma bp_perfected_L_R_disjnt:
  "R \<inter>  L = {} \<Longrightarrow> (bp_perfected_L L R) \<inter> (bp_perfected_R L R) = {}"
  by(auto simp add: bp_perfected_L_def bp_perfected_R_def)



context
  fixes G::"'a set set" and L R and w::"'a set \<Rightarrow> real"
  assumes bipartite_G: "bipartite G L R" 
    and finite_L: "finite L"
    and finite_R: "finite R"
begin

lemma finite_G: "finite G" 
  using bipartite_G finite_L finite_R finite_Vs_then_finite finite_parts_bipartite_graph_invar
  by auto

abbreviation "G' \<equiv> bp_perfected_G G L R"
abbreviation "L' \<equiv> bp_perfected_L L R"
abbreviation "R' \<equiv> bp_perfected_R L R"
abbreviation "w' \<equiv> min_costs_to_min_perfect_costs G w"

lemma old_vertex_of_G_in_G': "(image old_vertex) ` G \<subseteq> G'"
  using bipartite_G
  by(auto simp add: bp_perfected_G_def elim!: bipartite_edgeE)

lemma sum_on_new_is_sum_on_project_old:
  assumes "finite E"
  shows "sum w' E = sum w (project_to_old E \<inter> {e | e. w e < 0} \<inter> G)"
proof-
  have "sum w' E = sum w' {e | e. e \<in> E \<and> (\<nexists> i. new_vertex i \<in> e)} 
                + sum w' {e | e i. e \<in> E \<and> new_vertex i \<in> e}"
    using assms(1) 
    by (subst comm_monoid_add_class.sum.union_disjoint[symmetric]) 
      (auto intro!: arg_cong[of  _ _ "sum w'"])
  also have "... = sum w' {e | e. e \<in> E \<and> (\<nexists> i. new_vertex i \<in> e)}"
    by (auto simp add: min_costs_to_min_perfect_costs_def)
  also have "... = sum w' {e | e. e \<in> E \<and> (\<nexists> i. new_vertex i \<in> e) \<and> w' e < 0} +
                   sum w' {e | e. e \<in> E \<and> (\<nexists> i. new_vertex i \<in> e) \<and> w' e \<ge> 0}"
    using assms(1)
    by (subst comm_monoid_add_class.sum.union_disjoint[symmetric]) 
      (auto intro!: arg_cong[of  _ _ "sum w'"])
  also have "... =  sum w' {e | e. e \<in> E \<and> (\<nexists> i. new_vertex i \<in> e) \<and> w' e < 0}"
    by(auto simp add: min_costs_to_min_perfect_costs_def
        intro!: comm_monoid_add_class.sum.neutral)
  also have "... = sum w (project_to_old E \<inter> {e | e. w e < 0} \<inter> G)"
  proof-
    have pto_is:"project_to_old E \<inter> {e | e. w e < 0} \<inter> G = 
          (image the_vertex) ` {e |e. e \<in> E \<and> (\<nexists>i. new_vertex i \<in> e) \<and> local.w' e < 0}"
      by (auto simp add: project_to_old_def min_costs_to_min_perfect_costs_def)
    have inj: "inj_on ((`) the_vertex) {e |e. e \<in> E \<and> (\<nexists>i. new_vertex i \<in> e) \<and> local.w' e < 0}"
      by(auto simp add: inj_on_def  the_vertex_image_inj)
    show ?thesis
      apply(subst pto_is)
      apply(subst comm_monoid_add_class.sum.reindex[OF inj])
      by (auto intro: comm_monoid_add_class.sum.cong 
          simp add: min_costs_to_min_perfect_costs_def)
  qed
  finally show ?thesis
    by simp
qed

lemma project_to_old_of_negs_two_ways:
  "project_to_old (E \<inter> {e | e. w' e < 0}) \<inter> G =
       project_to_old E \<inter> {e | e. w e < 0} \<inter> G"
  by(auto simp add:  project_to_old_def min_costs_to_min_perfect_costs_def)

lemma finite_G':"finite G'"
  by(auto intro!: finite_G_finite_completion
      simp add: finite_L finite_R finite_G)

lemma e_in_project_to_old_L_times_R:
  "e \<in> project_to_old G' \<Longrightarrow> e \<in> {{u, v} | u v. u \<in> L \<and> v \<in> R}"
  by(auto simp add: bp_perfected_G_def project_to_old_def)

lemma min_weight_implies_min_weight_perfect:
  assumes "min_weight_matching G w M"
  obtains M' where "min_weight_perfect_matching G' w' M'"
    "sum w' M' = sum w M"  "((image old_vertex) ` M) \<subseteq> M'"
proof-
  note M_props = min_weight_matchingD[OF assms(1)]
  have "graph_matching G' ((image old_vertex) ` M)"
    apply(rule graph_matching_bigger_graph)
     apply(rule iffD1[OF graph_matching_on_old_vertices])
    using assms(1) old_vertex_of_G_in_G'
    by(auto elim!: min_weight_matchingE intro!: perfect_matchingD)
  hence "\<exists>M'. perfect_matching local.G' M' \<and> ((image old_vertex) ` M) \<subseteq> M'"
    by(auto intro!: extending_perfect_matching_in_balanced_complete_bipartite[
          OF balanced_complete_bipartite_perfected(1)[OF bipartite_G]]
        simp add: finite_L finite_R finite_G')
  then obtain M' where M': "perfect_matching local.G' M'" "((image old_vertex) ` M) \<subseteq> M'"
    by auto
  have finite_M': "finite M'" and matching_M': "matching M'" and M'_in_G': "M' \<subseteq> G'"
    using  M'(1) finite_G' 
    by(auto simp add: perfect_matching_def intro: rev_finite_subset) 
  have finite_M: "finite M" 
    using  M_props(1) finite_G rev_finite_subset by blast
  have M'_neg_olds_in_M: "project_to_old (M' \<inter> {e. local.w' e < 0}) \<inter> G \<subseteq> M"
  proof(rule ccontr, goal_cases)
    case 1
    then obtain e where e: "e \<in> project_to_old (M' \<inter> {e. local.w' e < 0})" "e \<notin> M" by auto
    hence "e \<in> {{u, v} | u v. u \<in> L \<and> v \<in> R}"
      using perfect_matchingD[OF M'(1)]  
      apply (intro e_in_project_to_old_L_times_R)
      apply(rule subsetD[OF project_to_old_mono])
      by auto
    hence e_props:"e \<in> G" "old_vertex ` e \<in> M'" "w' (old_vertex ` e) < 0" "w e < 0"
      using e
      by(auto simp add: project_to_old_def min_costs_to_min_perfect_costs_def
          if_split[of "\<lambda> x. x < 0"] no_new_vertex_old_vertex_new_vertex_image_inverse)
    moreover have "matching (insert e M)"
      apply(subst matching_on_old_vertices)
      apply(rule matching_subgraph[OF matching_M'])
      using M'(2) e_props(2) by blast
    moreover have "insert e M \<subseteq> G"
      by (simp add: M_props(1) e_props(1))
    ultimately have "graph_matching G (insert e M)" 
      by simp
    moreover have "sum w (insert e M) < sum w M"
      by(simp add: comm_monoid_add_class.sum.insert[OF finite_M e(2)] e_props(4))
    ultimately show False
      using assms 
      by(auto dest: min_weight_matchingD)
  qed
  have in_M_but_not_in_project_zero_weight:
    "\<lbrakk>e\<in>M; e\<notin>  project_to_old (M' \<inter> {e. local.w' e < 0}) \<inter> G\<rbrakk> \<Longrightarrow> w e = 0" for e
  proof(goal_cases)
    case 1
    hence "old_vertex ` e \<in> M'"
      using M'(2) by blast
    moreover have e_in_G:"e \<in> G" 
      using "1"(1) M_props(1) by blast
    ultimately have "w' (old_vertex ` e) \<ge> 0"
      using 1(2)
      by(auto simp add: project_to_old_def min_costs_to_min_perfect_costs_def
          if_split[of "\<lambda> x. x < 0"]) force
    hence "w e \<ge> 0" 
      by (simp add: e_in_G image_iff min_costs_to_min_perfect_costs_def
          no_new_vertex_new_vertex_old_vertex_image_inverse)
    thus ?case
      using "1"(1) assms finite_M min_weight_matching_only_negs by fastforce
  qed
  have M'_M_same_costs:"sum w' M' = sum  w M"
  proof-
    have "sum w (project_to_old (M' \<inter> {e. w' e < 0}) \<inter> G) = sum w M"
      using in_M_but_not_in_project_zero_weight finite_M M'_neg_olds_in_M
      by(auto intro!: comm_monoid_add_class.sum.mono_neutral_left)
    thus ?thesis
      using M' project_to_old_of_negs_two_ways[of M']
      by(auto simp add: sum_on_new_is_sum_on_project_old[OF finite_M'] )
  qed
  have M'_opt:"min_weight_perfect_matching G' w' M'"
  proof(rule ccontr,goal_cases)
    case 1
    then obtain M'' where M'': "perfect_matching G' M''" "sum w' M'' < sum w' M'"
      using M'(1) by(auto simp add: min_weight_perfect_matching_def)
    hence "sum w' M'' < sum w M" 
      using M'_M_same_costs by linarith
    moreover have "sum w (project_to_old M'' \<inter> {e |e. w e < 0} \<inter> G) = sum w' M''" 
      using M''(1) finite_G' 
      by(subst sum_on_new_is_sum_on_project_old)
        (auto dest: perfect_matchingD(1) intro: rev_finite_subset)
    moreover have "graph_matching G (project_to_old M'' \<inter> {e |e. w e < 0} \<inter> G)"
      using M''(1) matching_subgraph[OF matching_on_project_to_old, of M'']
      by(auto dest: perfect_matchingD(2) simp add: inf.coboundedI1)
    ultimately have "\<not> min_weight_matching G w M" 
      by(auto simp add:  min_weight_matching_def)
    thus False
      using assms(1)
      by simp
  qed
  show thesis
    using M'_M_same_costs M'_opt that M'(2) by blast
qed

lemma min_weight_perfect_implies_min_weight:
  assumes "min_weight_perfect_matching G' w' M"
  shows "min_weight_matching G w (project_to_old M \<inter> {e |e. w e < 0} \<inter> G)"
    "sum w' M = sum w (project_to_old M \<inter> {e |e. w e < 0} \<inter> G)"
proof-
  show same_sum:"sum w' M = sum w (project_to_old M \<inter> {e |e. w e < 0} \<inter> G)"
    using assms finite_G' finite_subset
    by(intro sum_on_new_is_sum_on_project_old)
      (auto dest!: min_weight_perfect_matchingD(1) perfect_matchingD(1))
  have graph_match: "graph_matching G (project_to_old M \<inter> {e |e. w e < 0} \<inter> G)"
    using assms
    by(auto intro!: matching_subgraph[OF matching_on_project_to_old, of M]
        intro: perfect_matchingD
        elim!: min_weight_perfect_matchingE)
  show "min_weight_matching G w (project_to_old M \<inter> {e |e. w e < 0} \<inter> G)"
  proof(rule ccontr, goal_cases)
    case 1
    obtain M' where M': "min_weight_matching G w M'"
      using  min_matching_exists[OF finite_G] by blast
    hence M'_props: "graph_matching G M'" 
      "sum w M' < sum w (project_to_old M \<inter> {e |e. w e < 0} \<inter> G)"
      using 1 graph_match
      by (auto simp add: min_weight_matching_def)
    obtain M'' where "min_weight_perfect_matching G' w' M''" "sum w' M'' =  sum w M'"
      using M' min_weight_implies_min_weight_perfect by blast
    hence "perfect_matching G' M''" "sum w' M'' < sum w' M" 
      using min_weight_perfect_matchingD(1)  M'_props(2)  same_sum 
      by auto
    hence "\<not> min_weight_perfect_matching G' w' M" 
      using same_sum min_weight_perfect_matchingD(1)[OF assms] 
      by(auto simp add: min_weight_perfect_matching_def)
    thus False
      using assms(1) by simp
  qed
qed

abbreviation "w'' \<equiv> min_max_card_costs_to_min_perfect_costs G w"

lemma not_in_imageE:
  "y \<notin> f ` X \<Longrightarrow> ((\<And> x. x \<in> X \<Longrightarrow> y = f x \<Longrightarrow> False) \<Longrightarrow> P) \<Longrightarrow> P"
  and not_in_imageD:
  "y \<notin> f ` X \<Longrightarrow>  x \<in> X \<Longrightarrow> y = f x \<Longrightarrow> False"
  by blast+

(*TODO MOVE*)
lemma same_sum_card_prod:
  "\<lbrakk>\<And> x. x \<in> X \<Longrightarrow> f x = (c::real); finite X \<rbrakk> \<Longrightarrow> sum f X = real (card X) * c"
  by simp

lemma sum_on_new_is_sum_on_project_old':
  assumes "finite E"
  shows "sum w'' E = sum w (project_to_old E \<inter> G) +
                       (real (card E) - real (card (project_to_old E \<inter> G))) * 2*penalty G w"
proof-
  define pnty where "pnty = 2*penalty G w"
  have "sum w'' E = sum w'' {e | e. e \<in> E \<and> (\<nexists> i. new_vertex i \<in> e)} 
                + sum w'' {e | e i. e \<in> E \<and> new_vertex i \<in> e}"
    using assms(1) 
    by (subst comm_monoid_add_class.sum.union_disjoint[symmetric]) 
      (auto intro!: arg_cong[of  _ _ "sum w''"])
  moreover have "... = sum w'' {e | e. e \<in> E \<and> (\<nexists> i. new_vertex i \<in> e)} +
                  card {e | e i. e \<in> E \<and> new_vertex i \<in> e} * pnty"
    by (auto simp add: min_max_card_costs_to_min_perfect_costs_def pnty_def)
  moreover have "... = sum w'' {e | e. e \<in> E \<and> (\<nexists> i. new_vertex i \<in> e) \<and> the_vertex ` e \<in> G} +
                   sum w'' {e | e. e \<in> E \<and> (\<nexists> i. new_vertex i \<in> e) \<and> the_vertex ` e \<notin> G} +
                  card {e | e i. e \<in> E \<and> new_vertex i \<in> e} * pnty"
    using assms(1)
    by (subst comm_monoid_add_class.sum.union_disjoint[symmetric]) 
      (auto intro!: arg_cong[of  _ _ "sum w''"])
  moreover have "sum w'' {e | e. e \<in> E \<and> (\<nexists> i. new_vertex i \<in> e) \<and> the_vertex ` e \<in> G}
                  = sum w (project_to_old E \<inter> G)"
  proof-
    have pto_is:"project_to_old E  \<inter> G = 
          (image the_vertex) ` {e |e. e \<in> E \<and> (\<nexists>i. new_vertex i \<in> e) \<and> the_vertex ` e \<in> G}"
      by (auto simp add: project_to_old_def min_costs_to_min_perfect_costs_def)
    have inj: "inj_on ((`) the_vertex) {e |e. e \<in> E \<and> (\<nexists>i. new_vertex i \<in> e) \<and> the_vertex ` e \<in> G}"
      by(auto simp add: inj_on_def  the_vertex_image_inj)
    show ?thesis
      apply(subst pto_is)
      apply(subst comm_monoid_add_class.sum.reindex[OF inj])
      by (auto intro: comm_monoid_add_class.sum.cong 
          simp add: min_max_card_costs_to_min_perfect_costs_def)
  qed
  moreover have "sum w'' {e | e. e \<in> E \<and> (\<nexists> i. new_vertex i \<in> e) \<and> the_vertex ` e \<notin> G} +
                  card {e | e i. e \<in> E \<and> new_vertex i \<in> e} * pnty = 
                (real (card E) - real (card (project_to_old E \<inter> G))) * pnty"
  proof-
    have "sum w'' {e | e. e \<in> E \<and> (\<nexists> i. new_vertex i \<in> e) \<and> the_vertex ` e \<notin> G} =
          card {e | e. e \<in> E \<and> (\<nexists> i. new_vertex i \<in> e) \<and> the_vertex ` e \<notin> G} * pnty"
      by(auto intro!: same_sum_card_prod
          simp add: penalty_def min_max_card_costs_to_min_perfect_costs_def pnty_def)
    moreover have "card {e | e i. e \<in> E \<and> new_vertex i \<in> e} +
            card {e | e. e \<in> E \<and> (\<nexists> i. new_vertex i \<in> e) \<and> the_vertex ` e \<notin> G}
           = real (card E) - card (project_to_old E \<inter> G)"
    proof(subst card_Un_disjoint[symmetric], goal_cases)
      case 4
      show ?case 
      proof(subst card_image[symmetric, of "image old_vertex" "_ \<inter> _"], goal_cases)
        case 1
        show ?case
          using inj_on_def by blast
      next
        case 2
        have "card E \<ge> card ((`) old_vertex ` (project_to_old E \<inter> G))"
          by(auto intro!: card_mono[OF assms(1)] simp add: project_to_old_def
              no_new_vertex_old_vertex_new_vertex_image_inverse)
        hence subst_help: "real (card E) - real (card ((`) old_vertex ` (project_to_old E \<inter> G)))
              = card E -card ((`) old_vertex ` (project_to_old E \<inter> G))"
          by simp
        show ?case     
        proof(subst subst_help, subst card_Diff_subset[symmetric], goal_cases)
          case 1
          show ?case
            using finite_G by blast
        next
          case 2
          show ?case
            by(auto simp add: project_to_old_def
                no_new_vertex_old_vertex_new_vertex_image_inverse)
        next
          case 3
          show ?case
            by (auto intro!: arg_cong[of _ _ card] old_vertex_of_the_vertex_contained
                simp add: project_to_old_def 
                no_new_vertex_old_vertex_new_vertex_image_inverse
                dest!: not_in_imageD)
        qed
      qed
    qed(insert assms, auto)
    ultimately show ?thesis 
      by(auto simp add: algebra_simps distrib_left[symmetric] simp del: distrib_left)
  qed
  ultimately show ?thesis
    by (auto simp add: pnty_def)
qed

lemma int_minus_leq:"a \<le> b \<Longrightarrow> int b - int a = int ( b- a)"
  by auto

lemma G'_bipartite: "bipartite G' L' R'"
  by (simp add: balanced_complete_bipartiteD(1) balanced_complete_bipartite_perfected bipartite_G
      complete_bipartiteD(1) finite_L finite_R)

lemma graph_abs_G': "graph_abs G'"
  by(auto intro!: bipartite_to_graph_abs G'_bipartite finite_G')

lemma complete_bipartite_G': "complete_bipartite G' L' R'"
  by (simp add: balanced_complete_bipartiteD(1) balanced_complete_bipartite_perfected(1)
      bipartite_G finite_L finite_R)

lemma L'_R'_same_empty:"L' = {} \<longleftrightarrow> R' = {}"
  by (simp add: finite_L finite_R perfected_vertices_empty_same)

lemma finite_L': "finite L'"
  by (simp add: finite_L finite_L_finite_completion)

lemma finite_R': "finite R'"
  by (simp add: finite_R finite_R_finite_completion)

lemma L'_R'_disjoint: "L' \<inter> R' = {}"
  using G'_bipartite bipartite_disjointD by blast

lemma card_Vs_G': "card (Vs G') = 2* max (card L) (card R)"
  by (simp add: complete_bipartite_Vs[OF complete_bipartite_G' _ L'_R'_same_empty]
      graph_abs.dblton_E graph_abs_G' card_Un_disjoint finite_L' finite_R' 
      L'_R'_disjoint
      balanced_complete_bipartite_perfected_side_cards[OF bipartite_G finite_L finite_R])

lemma perfect_in_G'_max_L_R_edges:
  "perfect_matching G' M \<Longrightarrow> card M = max (card L) (card R)"
  by(auto simp add: perfect_matching_card'[OF _ graph_abs_G'] card_Vs_G')

lemma max_card_matching_in_perfect_matching:
  assumes "perfect_matching G' M'" "(image old_vertex) ` M \<subseteq> M'"
    "max_card_matching G M"
  shows "project_to_old M' \<inter> G = M"
proof-
  have M'_matching:"graph_matching G' M'" "matching M'"
    using assms(1) perfect_matchingD(1,2) by blast+
  have finite_M: "finite M" 
    using assms(3) finite_G 
    by(auto dest!: max_card_matchingD intro: rev_finite_subset) 
  show ?thesis
  proof(rule, rule ccontr, goal_cases)
    case 1
    then obtain e where e: "e \<in> project_to_old M'" "e \<notin> M" "e \<in> G" by auto
    hence "e \<in> {{u, v} | u v. u \<in> L \<and> v \<in> R}"
      using M'_matching(1)  
      apply (intro e_in_project_to_old_L_times_R)
      apply(rule subsetD[OF project_to_old_mono])
      by auto
    hence e_props:"e \<in> G" "old_vertex ` e \<in> M'" 
      using e
      by(auto simp add: project_to_old_def min_costs_to_min_perfect_costs_def
          if_split[of "\<lambda> x. x < 0"] no_new_vertex_old_vertex_new_vertex_image_inverse)
    moreover have "matching (insert e M)"
      apply(subst matching_on_old_vertices)
      apply(rule matching_subgraph[OF M'_matching(2)])
      using assms(2) e_props(2) by blast
    moreover have "insert e M \<subseteq> G"
      by (simp add: assms(3) e_props(1) max_card_matchingD)
    ultimately have "graph_matching G (insert e M)" 
      by simp
    moreover have "card (insert e M) > card M"
      by (simp add: e(2) finite_M)
    ultimately show False 
      using linorder_not_le  max_card_matchingD[OF assms(3)]
      by blast
  next 
    case 2
    have "\<lbrakk>(`) old_vertex ` M \<subseteq> M'; M \<subseteq> G; x \<in> M\<rbrakk>
           \<Longrightarrow> \<exists>e. x = the_vertex ` e \<and> e \<in> M' \<and> (\<forall>i. new_vertex i \<notin> e)" for x
      apply(rule  exI[of _ "(image old_vertex) _"])
      apply rule
       apply(rule no_new_vertex_new_vertex_old_vertex_image_inverse[symmetric])
      by auto
    thus ?case
      using assms(1,2) conjunct1[OF max_card_matchingD[OF assms(3)]]
      by(auto simp add: project_to_old_def)
  qed
qed

lemma graph_invarG: "graph_invar G"
  using bipartite_G finite_G finite_bipartite_graph_invar by auto

lemma "(a::real)*b - a* c = a*(b-c)"
  by (simp add: right_diff_distrib)

lemma min_weight_perfect_fives_min_weight_max_card_matching:
  assumes "min_weight_perfect_matching G' w'' M"
  shows  "min_weight_max_card_matching G w (project_to_old M \<inter> G)"
proof-
  note M_props = perfect_matchingD[OF min_weight_perfect_matchingD(1)[OF assms]]
    min_weight_perfect_matchingD[OF assms]
  have finite_M: "finite M"
    using M_props(1) finite_G' rev_finite_subset by blast
  have graph_matching_M:"graph_matching G (project_to_old M \<inter> G)" 
    using M_props(2) 
    by(auto intro: matching_subgraph[OF matching_on_project_to_old, of _ "_ \<inter> G"])
  have costs_of_M: "sum w'' M = sum w (project_to_old M \<inter> G)
           + (real (card M) - real (card (project_to_old M \<inter> G))) * 2*penalty G w"
    using sum_on_new_is_sum_on_project_old'[OF finite_M]  by simp
  have False
    if  "\<not> min_weight_max_card_matching G w (project_to_old M \<inter> G)"
  proof-
    have how_not_opt:
      "\<not> max_card_matching G (project_to_old M \<inter> G) \<or> 
           (max_card_matching G (project_to_old M \<inter> G) \<and>
            (\<exists> M'. max_card_matching G M' \<and> sum w M' < sum w (project_to_old M \<inter> G)))"
      using that 
      by(auto simp add: min_weight_max_card_matching_def)
    obtain M' where M': "min_weight_max_card_matching G w M'" 
      using finite_G min_weight_max_card_matching_exists by blast
    note M'_props = min_weight_max_card_matchingD[OF M']
    hence M_projected_non_opt_cases: "card M' > card (project_to_old M \<inter> G)
             \<or> (card M' = card  (project_to_old M \<inter> G) \<and> sum w M' < sum w (project_to_old M \<inter> G))"
    proof(cases rule: context_disjE[OF how_not_opt], goal_cases)
      case 1
      thus ?case 
        using graph_matching_M 
        by(auto dest!: min_weight_max_card_matchingD(1)
            simp add: max_card_matching_def order_less_le)
    next
      case 2
      then obtain M'' where "max_card_matching G M''" "sum w M'' < sum w (project_to_old M \<inter> G)"
        by auto
      moreover hence "sum w M'' \<ge> sum w M'"
        using M' min_weight_max_card_matching_def by blast
      moreover have "card M' =  card  (project_to_old M \<inter> G)" 
        using 2 M'_props(1)
        by(auto  intro: max_card_matchings_same_size)
      ultimately show ?case
        by simp
    qed
    have graph_matching_M': "graph_matching G M'"
      using M' max_card_matchingD min_weight_max_card_matchingD(1) by blast
    note that = graph_matching_M' M_projected_non_opt_cases
    have "\<exists>M''. perfect_matching G' M'' \<and> ((image old_vertex) ` M') \<subseteq> M''"
      using that(1) graph_matching_on_old_vertices old_vertex_of_G_in_G'
      by(auto intro!: extending_perfect_matching_in_balanced_complete_bipartite[
            OF balanced_complete_bipartite_perfected(1)[OF bipartite_G]]
          rev_image_eqI
          simp add: finite_L finite_R finite_G')
    then obtain M'' where M'': 
      "perfect_matching G' M''" "((image old_vertex) ` M') \<subseteq> M''" by auto
    have M''_props: "matching M''" "graph_matching G' M''" "finite M''"  
      using M''(1) finite_G' by(auto simp add: perfect_matching_def finite_subset)
    have M''_sum_is: "sum w'' M'' = sum w (project_to_old M'' \<inter> G) +
       (real (card M'') - real (card (project_to_old M'' \<inter> G))) * 2 * penalty G w"
      using sum_on_new_is_sum_on_project_old'[OF M''_props(3)] by simp
    have M''_costs_M: "sum w'' M'' \<ge> sum w'' M"
      using M''(1) M_props(5) by blast
    have M_M''_card:"card M'' = card M" 
      using  M''(1) M_props(4) graph_abs_G' 
      by(auto intro!: perfect_matchings_same_card)
    have project_M''_is: "project_to_old M'' \<inter> G = M'" 
      using  M''(1,2) M'_props(1)
      by(intro max_card_matching_in_perfect_matching) 
    have "sum w'' M > sum w'' M''"
    proof(cases rule: disjE[OF M_projected_non_opt_cases], goal_cases)
      case 1
      have "\<bar>sum w M' - sum w (project_to_old M \<inter> G)\<bar> < 2* penalty G w  "
        using graph_matching_M'  graph_matching_M
        by(auto intro!: weight_diff_of_matchings_less_than_2_penalties simp add: graph_invarG)
      moreover have "penalty G w * (real (card M') * 2) -
           penalty G w * (2 * real (card (project_to_old M \<inter> G))) \<ge> 2 * penalty G w"
        apply(subst right_diff_distrib[symmetric])
        apply(subst ab_semigroup_mult_class.mult.commute[of 2 "penalty G w"])
        apply(subst linordered_ring_strict_class.mult_le_cancel_left_pos)
        using 1 
        by (auto simp add: finite_G penalty_gtr_0 algebra_simps)
      ultimately show ?case
        by(auto simp add: costs_of_M M''_sum_is M_M''_card project_M''_is algebra_simps)
    next
      case 2
      thus ?case
        by(auto simp add: 2(1) costs_of_M M''_sum_is M_M''_card project_M''_is algebra_simps)
    qed
    thus False
      using M''_costs_M by argo
  qed
  thus ?thesis
    by auto
qed
end

end