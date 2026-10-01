theory Matching_Certificate_Spec
  imports Matching_LPs.Matching_LP Basic_Matching.Weighted_Matchings_Reductions
          Tutte_Theorem.Bipartite_Matchings_Existence 
          Data_Structures.Real_Embedding
begin

section \<open>Certificate Checkers for Extremal Bipartite Matchings: Specification\<close>

text \<open>A checker that is independent of any solver. It receives an instance, a candidate matching
      and a certificate, and decides whether the candidate is a minimum or maximum weight
      (perfect) matching, or whether a certificate shows that there is no perfect matching.

      The instance consists of a finite set @{term E} of edge names, enumerated by
      @{term elist}, with the left endpoint @{term efst}, the right endpoint @{term esnd} and the
      weight @{term ew} of every edge, and of the lists @{term ls} and @{term rs} of the left and
      the right vertices, all below @{term n}. The candidate matching is a list of edge names,
      the optimality certificate a list of potentials (one for every vertex), and the
      infeasibility certificate a list of left vertices violating Hall's condition.

      For @{term neg}, the problem is to minimise the weights negated if @{term neg} holds.
      The certificate is always a dual of the minimisation problem.\<close>

definition sgn_c :: "bool \<Rightarrow> 'a::uminus \<Rightarrow> 'a" where
  "sgn_c b x = (if b then - x else x)"

subsection \<open>The Checks\<close>

locale matching_cert_spec =
  fixes E :: "'e set"
    and elist :: "'e list"
    and efst :: "'e \<Rightarrow> nat"
    and esnd :: "'e \<Rightarrow> nat"
    and ew :: "'e \<Rightarrow> 'n::linordered_idom"
    and n :: nat
    and ls :: "nat list"
    and rs :: "nat list"
begin

abbreviation "L \<equiv> set ls"
abbreviation "R \<equiv> set rs"

text \<open>The checks are for the weights shifted by @{term "- t"}: the dual constraint of an edge
      @{term e} is @{term "ys ! efst e + ys ! esnd e + t \<le> sgn_c neg (ew e)"}. The shift is
      @{term 0} except for the maximum cardinality variants.\<close>

definition "feas_ok neg t ys e = (ys ! efst e + ys ! esnd e + t \<le> sgn_c neg (ew e))"

definition "tight_ok neg t ys e = (ys ! efst e + ys ! esnd e + t = sgn_c neg (ew e))"

text \<open>The matching: every name is an edge, no vertex is used twice, and every edge is tight.
      The set @{term U} collects the matched vertices.\<close>

fun match_list :: "bool \<Rightarrow> 'n \<Rightarrow> 'n list \<Rightarrow> nat set \<Rightarrow> 'e list \<Rightarrow> nat set \<times> bool" where
  "match_list neg t ys U [] = (U, True)"
| "match_list neg t ys U (e # es) =
     (if e \<in> E \<and> efst e \<notin> U \<and> esnd e \<notin> U \<and> tight_ok neg t ys e
      then match_list neg t ys (insert (esnd e) (insert (efst e) U)) es else (U, False))"

text \<open>Non-perfect variants: potentials are non-positive and vanish on unmatched vertices.\<close>

definition "vert_ok ys U x = (ys ! x \<le> 0 \<and> (ys ! x \<noteq> 0 \<longrightarrow> x \<in> U))"

definition certify_sh :: "bool \<Rightarrow> bool \<Rightarrow> 'n \<Rightarrow> 'e list \<Rightarrow> 'n list \<Rightarrow> bool" where
  "certify_sh neg perfect t ms ys =
     (n \<le> length ys \<and> list_all (feas_ok neg t ys) elist \<and>
      (case match_list neg t ys {} ms of (U, ok) \<Rightarrow> ok \<and>
         (if perfect then length ms = length ls \<and> length ls = length rs
          else list_all (vert_ok ys U) ls \<and> list_all (vert_ok ys U) rs)))"

definition certify :: "bool \<Rightarrow> bool \<Rightarrow> 'e list \<Rightarrow> 'n list \<Rightarrow> bool" where
  "certify neg perfect = certify_sh neg perfect 0"

text \<open>Hall violators: the distinct elements of @{term S} are counted, duplicates are skipped.\<close>

fun hall_S :: "nat set \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat set \<times> nat \<times> bool" where
  "hall_S Sm k [] = (Sm, k, True)"
| "hall_S Sm k (x # xs) =
     (if x \<in> L then if x \<in> Sm then hall_S Sm k xs else hall_S (insert x Sm) (Suc k) xs
      else (Sm, k, False))"

fun hall_N :: "nat set \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> 'e list \<Rightarrow> nat set \<times> nat" where
  "hall_N Sm Nm k [] = (Nm, k)"
| "hall_N Sm Nm k (e # es) =
     (if efst e \<in> Sm \<and> esnd e \<notin> Nm then hall_N Sm (insert (esnd e) Nm) (Suc k) es
      else hall_N Sm Nm k es)"

definition hall_check :: "nat list \<Rightarrow> bool" where
  "hall_check S =
     (length ls \<noteq> length rs \<or>
      (case hall_S {} 0 S of (Sm, k, ok) \<Rightarrow>
         ok \<and> (case hall_N Sm {} 0 elist of (Nm, nb) \<Rightarrow> nb < k)))"

text \<open>Maximum cardinality: a set @{term S} of left vertices with
      @{text "|L| - |S| + |N(S)| \<le> |ms|"}, and a dual for the shifted weights.\<close>

definition defic_ok :: "'e list \<Rightarrow> nat list \<Rightarrow> bool" where
  "defic_ok ms S =
     (case hall_S {} 0 S of (Sm, k, ok) \<Rightarrow>
        ok \<and> (case hall_N Sm {} 0 elist of (Nm, nb) \<Rightarrow> length ls + nb \<le> length ms + k))"

definition certify_mc :: "bool \<Rightarrow> 'e list \<Rightarrow> 'n list \<Rightarrow> 'n \<Rightarrow> nat list \<Rightarrow> bool" where
  "certify_mc neg ms ys t S = (certify_sh neg False t ms ys \<and> defic_ok ms S)"

end

subsection \<open>Shifted Weights and Maximum Cardinality\<close>

lemma shift_max_card:
  assumes "min_weight_matching G (\<lambda>d. w d - c) M" "max_card_matching G M"
  shows "min_weight_max_card_matching G w M"
proof (rule min_weight_max_card_matchingI[OF assms(2)])
  fix M' assume M': "max_card_matching G M'"
  have "card M' = card M" using max_card_matchings_same_size[OF M' assms(2)] .
  moreover have "sum (\<lambda>d. w d - c) M \<le> sum (\<lambda>d. w d - c) M'"
    using assms(1) M' by (auto simp: min_weight_matching_def max_card_matching_def)
  ultimately show "sum w M \<le> sum w M'" by (simp add: sum_subtractf)
qed

subsection \<open>Soundness\<close>

locale matching_cert = matching_cert_spec E elist efst esnd ew n ls rs + real_embedding h
  for E :: "'e set" and elist efst esnd and ew :: "'e \<Rightarrow> 'n::linordered_idom" and n ls rs
    and h :: "'n \<Rightarrow> real" +
  assumes elist_E: "set elist = E"
    and fst_L: "efst ` E = L"
    and snd_R: "esnd ` E = R"
    and ls_distinct: "distinct ls"
    and rs_distinct: "distinct rs"
    and sides_disjoint: "L \<inter> R = {}"
    and verts_below: "L \<union> R \<subseteq> {..<n}"
    and no_parallel: "inj_on (\<lambda>e. (efst e, esnd e)) E"
begin

definition "cedge e = {efst e, esnd e}"

definition "G = cedge ` E"

definition "wG d = h (ew (THE e. e \<in> E \<and> cedge e = d))"

definition "wt neg d = sgn_c neg (wG d)"

definition "wt_sh neg t = (\<lambda>d. wt neg d - h t)"

lemma wt_sh_0 [simp]: "wt_sh neg 0 = wt neg"
  by (simp add: wt_sh_def)

definition "pot ys v = h (ys ! v)"

definition "Mat ms = cedge ` set ms"

lemma fst_in: "e \<in> E \<Longrightarrow> efst e \<in> L" and snd_in: "e \<in> E \<Longrightarrow> esnd e \<in> R"
  using fst_L snd_R by blast+

lemma fst_snd_neq: "e \<in> E \<Longrightarrow> efst e \<noteq> esnd e"
proof -
  assume e: "e \<in> E"
  have "efst e \<in> L" "esnd e \<in> R" using fst_in[OF e] snd_in[OF e] .
  thus ?thesis using sides_disjoint by (metis IntI empty_iff)
qed

lemma finite_E: "finite E"
  using elist_E by blast

lemma cedge_eq: "\<lbrakk>e \<in> E; e' \<in> E; cedge e = cedge e'\<rbrakk> \<Longrightarrow> e = e'"
proof -
  assume e: "e \<in> E" "e' \<in> E" "cedge e = cedge e'"
  have "efst e = efst e' \<and> esnd e = esnd e'"
    using e fst_in[of e] snd_in[of e] fst_in[of e'] snd_in[of e'] sides_disjoint
    by (auto simp: cedge_def doubleton_eq_iff)
  thus "e = e'" using inj_onD[OF no_parallel _ e(1,2)] by simp
qed

lemma wG_edge: "e \<in> E \<Longrightarrow> wG (cedge e) = h (ew e)"
  unfolding wG_def by (rule arg_cong[where f = "\<lambda>x. h (ew x)"], rule the_equality) (auto dest: cedge_eq)

lemma h_sgn: "h (sgn_c b x) = sgn_c b (h x)"
  by (simp add: sgn_c_def)

lemma Vs_cedge: "Vs (cedge ` S) = efst ` S \<union> esnd ` S"
  by (auto simp: Vs_def cedge_def)

lemma Vs_G: "Vs G = L \<union> R"
  using fst_L snd_R by (simp add: G_def Vs_cedge)

lemma G_edgeE:
  assumes "d \<in> G"
  obtains e where "e \<in> E" "d = cedge e"
  using assms by (auto simp: G_def)

lemma graph_invar_G: "graph_invar G"
proof
  show "dblton_graph G" unfolding dblton_graph_def
  proof
    fix d assume "d \<in> G"
    then obtain e where e: "e \<in> E" "d = cedge e" by (rule G_edgeE)
    show "\<exists>u v. d = {u, v} \<and> u \<noteq> v"
      using e fst_snd_neq by (intro exI[of _ "efst e"] exI[of _ "esnd e"]) (simp add: cedge_def)
  qed
  show "finite (Vs G)" using Vs_G by simp
qed

lemma bipartite_G: "bipartite G L R"
  unfolding bipartite_def
proof (intro conjI ballI)
  show "L \<inter> R = {}" by (rule sides_disjoint)
  fix d assume "d \<in> G"
  then obtain e where e: "e \<in> E" "d = cedge e" by (rule G_edgeE)
  show "\<exists>u v. d = {u, v} \<and> u \<in> L \<and> v \<in> R"
    using e fst_in snd_in by (intro exI[of _ "efst e"] exI[of _ "esnd e"]) (simp add: cedge_def)
qed

subsubsection \<open>Feasibility and Tightness\<close>

lemma cedge_doubleton:
  assumes "e \<in> E" "cedge e = {u, v}"
  shows "pot ys u + pot ys v = h (ys ! efst e + ys ! esnd e)"
  using assms by (auto simp: cedge_def doubleton_eq_iff pot_def h_add)

lemma feasible:
  assumes "list_all (feas_ok neg t ys) elist"
  shows "feasible_min_perfect_dual G (wt_sh neg t) (pot ys)"
proof (rule feasible_min_perfect_dualI)
  fix d u v assume d: "d \<in> G" "d = {u, v}"
  then obtain e where e: "e \<in> E" "d = cedge e" by (elim G_edgeE)
  have "feas_ok neg t ys e" using assms e(1) elist_E by (simp add: list_all_iff)
  hence le: "h (ys ! efst e + ys ! esnd e) + h t \<le> h (sgn_c neg (ew e))"
    by (simp add: feas_ok_def flip: h_add)
  have w: "wt_sh neg t d = h (sgn_c neg (ew e)) - h t"
    using wG_edge[OF e(1)] e(2) by (simp add: wt_sh_def wt_def h_sgn)
  show "pot ys u + pot ys v \<le> wt_sh neg t d"
    using le w cedge_doubleton[OF e(1), of u v ys] d(2) e(2) by simp
qed

lemma tight:
  assumes "e \<in> E" "tight_ok neg t ys e"
  shows "cedge e \<in> tight_subgraph G (wt_sh neg t) (pot ys)"
proof (rule in_tight_subgraphI)
  show "cedge e = {efst e, esnd e}" by (simp add: cedge_def)
  show "{efst e, esnd e} \<in> G" using assms(1) by (auto simp: G_def cedge_def)
  have "h (ys ! efst e) + h (ys ! esnd e) + h t = h (sgn_c neg (ew e))"
    using assms(2) by (simp add: tight_ok_def flip: h_add)
  hence "h (ys ! efst e) + h (ys ! esnd e) = sgn_c neg (h (ew e)) - h t" by (simp add: h_sgn)
  thus "wt_sh neg t {efst e, esnd e} = pot ys (efst e) + pot ys (esnd e)"
    using wG_edge[OF assms(1)] by (simp add: cedge_def wt_sh_def wt_def pot_def)
qed

subsubsection \<open>The Matching\<close>

lemma match_list_props:
  "match_list neg t ys U0 xs = (U, True) \<Longrightarrow>
   set xs \<subseteq> E \<and> list_all (tight_ok neg t ys) xs \<and> U = U0 \<union> efst ` set xs \<union> esnd ` set xs \<and>
   (efst ` set xs \<union> esnd ` set xs) \<inter> U0 = {} \<and> distinct (map efst xs) \<and> distinct (map esnd xs)"
proof (induction xs arbitrary: U0)
  case (Cons e xs)
  have c: "e \<in> E" "efst e \<notin> U0" "esnd e \<notin> U0" "tight_ok neg t ys e"
    and r: "match_list neg t ys (insert (esnd e) (insert (efst e) U0)) xs = (U, True)"
    using Cons.prems by (simp_all split: if_splits)
  note ih = Cons.IH[OF r]
  have "efst e \<notin> efst ` set xs" "esnd e \<notin> esnd ` set xs" using ih by blast+
  thus ?case using ih c by auto
qed simp

lemma matching_Mat:
  assumes "set ms \<subseteq> E" "distinct (map efst ms)" "distinct (map esnd ms)"
  shows "matching (Mat ms)"
  unfolding matching_def Mat_def
proof (intro ballI impI)
  fix d1 d2 assume d: "d1 \<in> cedge ` set ms" "d2 \<in> cedge ` set ms" "d1 \<noteq> d2"
  then obtain a b where ab: "a \<in> set ms" "b \<in> set ms" "d1 = cedge a" "d2 = cedge b" by blast
  hence "a \<noteq> b" using d(3) by blast
  hence "efst a \<noteq> efst b" "esnd a \<noteq> esnd b"
    using ab(1,2) assms(2,3) by (auto simp: distinct_map inj_on_def)
  moreover have "efst a \<noteq> esnd b" "esnd a \<noteq> efst b"
    using ab(1,2) assms(1) fst_in snd_in sides_disjoint by (metis IntI empty_iff subsetD)+
  ultimately show "d1 \<inter> d2 = {}" using ab(3,4) by (auto simp: cedge_def)
qed

lemma Mat_props:
  assumes "match_list neg t ys {} ms = (U, True)"
  shows "graph_matching G (Mat ms)" "Vs (Mat ms) = U"
        "Mat ms \<subseteq> tight_subgraph G (wt_sh neg t) (pot ys)"
        "distinct (map efst ms)" "distinct (map esnd ms)" "set ms \<subseteq> E"
proof -
  note P = match_list_props[OF assms]
  show "set ms \<subseteq> E" "distinct (map efst ms)" "distinct (map esnd ms)" using P by simp_all
  show "graph_matching G (Mat ms)" using P matching_Mat by (auto simp: Mat_def G_def)
  show "Vs (Mat ms) = U" using P by (simp add: Mat_def Vs_cedge)
  show "Mat ms \<subseteq> tight_subgraph G (wt_sh neg t) (pot ys)"
    using P tight by (auto simp: Mat_def list_all_iff)
qed

subsubsection \<open>Perfect Variants\<close>

lemma covers:
  assumes "set ms \<subseteq> E" "distinct (map f ms)" "f ` E = X" "distinct xs" "set xs = X"
          "length ms = length xs"
  shows "f ` set ms = X"
proof (rule card_subset_eq)
  show "finite X" using assms(5) by blast
  show "f ` set ms \<subseteq> X" using assms(1,3) by blast
  have "card (f ` set ms) = length ms" using assms(2) distinct_card[of "map f ms"] by simp
  thus "card (f ` set ms) = card X" using assms(4,5,6) distinct_card[of xs] by simp
qed

theorem certify_perfect_sound:
  assumes "certify_sh neg True t ms ys"
  shows "min_weight_perfect_matching G (wt_sh neg t) (Mat ms)"
proof -
  obtain U where m: "match_list neg t ys {} ms = (U, True)"
    and len: "length ms = length ls" "length ls = length rs"
    and f: "list_all (feas_ok neg t ys) elist"
    using assms by (cases "match_list neg t ys {} ms") (auto simp: certify_sh_def)
  note M = Mat_props[OF m]
  have "efst ` set ms = L" "esnd ` set ms = R"
    using covers[OF M(6,4) fst_L ls_distinct refl] covers[OF M(6,5) snd_R rs_distinct refl] len
    by simp_all
  hence "Vs G = Vs (Mat ms)" using Vs_G by (simp add: Mat_def Vs_cedge)
  hence "perfect_matching G (Mat ms)" using M(1) by (simp add: perfect_matching_def)
  thus ?thesis
    using min_weight_perfect_if_tight(1)[OF feasible[OF f] _ graph_invar_G M(3)] by simp
qed

subsubsection \<open>Non-Perfect Variants\<close>

theorem certify_matching_sound:
  assumes "certify_sh neg False t ms ys"
  shows "min_weight_matching G (wt_sh neg t) (Mat ms)"
proof -
  obtain U where m: "match_list neg t ys {} ms = (U, True)"
    and f: "list_all (feas_ok neg t ys) elist"
    and v: "list_all (vert_ok ys U) ls" "list_all (vert_ok ys U) rs"
    using assms by (cases "match_list neg t ys {} ms") (auto simp: certify_sh_def)
  note M = Mat_props[OF m]
  have vx: "ys ! x \<le> 0" "ys ! x \<noteq> 0 \<Longrightarrow> x \<in> Vs (Mat ms)" if "x \<in> L \<union> R" for x
    using v that M(2) by (auto simp: list_all_iff vert_ok_def)
  have fd: "feasible_min_perfect_dual G (wt_sh neg t) (pot ys)" by (rule feasible[OF f])
  have "feasible_max_dual (L \<union> R) G (- wt_sh neg t) (- pot ys)"
  proof (rule feasible_max_dualI)
    show "0 \<le> (- pot ys) v" if "v \<in> L \<union> R" for v using vx(1)[OF that] by (simp add: pot_def)
    show "(- wt_sh neg t) d \<le> (- pot ys) u + (- pot ys) v" if "d \<in> G" "d = {u, v}" for d u v
      using feasible_min_perfect_dualD[OF fd that] by simp
    show "Vs G \<subseteq> L \<union> R" "finite (L \<union> R)" using Vs_G by simp_all
  qed
  moreover have "Mat ms \<subseteq> tight_subgraph G (- wt_sh neg t) (- pot ys)"
  proof
    fix d assume "d \<in> Mat ms"
    hence "d \<in> tight_subgraph G (wt_sh neg t) (pot ys)" using M(3) by blast
    then obtain u v where uv: "d = {u, v}" "{u, v} \<in> G" "wt_sh neg t {u, v} = pot ys u + pot ys v"
      by (elim in_tight_subgraphE)
    show "d \<in> tight_subgraph G (- wt_sh neg t) (- pot ys)"
      by (rule in_tight_subgraphI[OF uv(1)]) (simp_all add: uv(2,3))
  qed
  moreover have "non_zero_vertices (L \<union> R) (- pot ys) \<subseteq> Vs (Mat ms)"
    using vx(2) by (auto simp: non_zero_vertices_def pot_def)
  ultimately have "max_weight_matching G (- wt_sh neg t) (Mat ms)"
    using max_weight_if_tight_matching_covers_bads(1)[OF _ M(1) graph_invar_G] by blast
  thus ?thesis using min_and_max_matching[of G "wt_sh neg t"] by simp
qed

subsubsection \<open>The Four Variants\<close>

lemma wt_False: "wt False = wG" and wt_True: "wt True = - wG" and neg_neg_wG: "- (- wG) = wG"
  by (auto simp: wt_def sgn_c_def)

corollary min_weight_perfect_certified:
  "certify False True ms ys \<Longrightarrow> min_weight_perfect_matching G wG (Mat ms)"
  using certify_perfect_sound[of False 0] by (simp add: certify_def wt_False)

corollary max_weight_perfect_certified:
  "certify True True ms ys \<Longrightarrow> max_weight_perfect_matching G wG (Mat ms)"
  using certify_perfect_sound[of True 0] min_perfect_and_max_perfect_matching[of G "- wG"]
  by (simp add: certify_def wt_True neg_neg_wG)

corollary min_weight_matching_certified:
  "certify False False ms ys \<Longrightarrow> min_weight_matching G wG (Mat ms)"
  using certify_matching_sound[of False 0] by (simp add: certify_def wt_False)

corollary max_weight_matching_certified:
  "certify True False ms ys \<Longrightarrow> max_weight_matching G wG (Mat ms)"
  using certify_matching_sound[of True 0] min_and_max_matching[of G "- wG"]
  by (simp add: certify_def wt_True neg_neg_wG)

subsubsection \<open>Hall Violators\<close>

lemma hall_S_props:
  "\<lbrakk>hall_S Sm0 k0 xs = (Sm, k, True); finite Sm0; k0 = card Sm0\<rbrakk>
   \<Longrightarrow> Sm = Sm0 \<union> set xs \<and> k = card Sm \<and> set xs \<subseteq> L"
proof (induction xs arbitrary: Sm0 k0)
  case (Cons x xs)
  have x: "x \<in> L" using Cons.prems(1) by (simp split: if_splits)
  show ?case
  proof (cases "x \<in> Sm0")
    case True
    hence "hall_S Sm0 k0 xs = (Sm, k, True)" using Cons.prems(1) x by simp
    thus ?thesis using Cons.IH[OF _ Cons.prems(2,3)] x True by auto
  next
    case False
    hence "hall_S (insert x Sm0) (Suc k0) xs = (Sm, k, True)" using Cons.prems(1) x by simp
    moreover have "Suc k0 = card (insert x Sm0)" using False Cons.prems(2,3) by simp
    ultimately show ?thesis using Cons.IH[of "insert x Sm0" "Suc k0"] Cons.prems(2) x by auto
  qed
qed simp

lemma hall_N_props:
  "\<lbrakk>hall_N Sm Nm0 k0 xs = (Nm, k); finite Nm0; k0 = card Nm0\<rbrakk>
   \<Longrightarrow> Nm = Nm0 \<union> esnd ` {e \<in> set xs. efst e \<in> Sm} \<and> k = card Nm"
proof (induction xs arbitrary: Nm0 k0)
  case (Cons e xs)
  show ?case
  proof (cases "efst e \<in> Sm \<and> esnd e \<notin> Nm0")
    case True
    hence "hall_N Sm (insert (esnd e) Nm0) (Suc k0) xs = (Nm, k)" using Cons.prems(1) by simp
    moreover have "Suc k0 = card (insert (esnd e) Nm0)" using True Cons.prems(2,3) by simp
    ultimately have "Nm = insert (esnd e) Nm0 \<union> esnd ` {e \<in> set xs. efst e \<in> Sm}" "k = card Nm"
      using Cons.IH[of "insert (esnd e) Nm0" "Suc k0"] Cons.prems(2) by auto
    thus ?thesis using True by auto
  next
    case False
    hence "hall_N Sm Nm0 k0 xs = (Nm, k)" using Cons.prems(1) by (auto split: if_splits)
    hence "Nm = Nm0 \<union> esnd ` {e \<in> set xs. efst e \<in> Sm}" "k = card Nm"
      using Cons.IH[OF _ Cons.prems(2,3)] by auto
    thus ?thesis using False by auto
  qed
qed simp

lemma neighbourhood_left:
  assumes "X \<subseteq> L"
  shows "Neighbourhood G X = esnd ` {e \<in> E. efst e \<in> X}"
proof
  show "Neighbourhood G X \<subseteq> esnd ` {e \<in> E. efst e \<in> X}"
  proof
    fix v assume "v \<in> Neighbourhood G X"
    then obtain u where uv: "{u, v} \<in> G" "u \<in> X" by (auto simp: Neighbourhood_def)
    then obtain e where e: "e \<in> E" "{u, v} = cedge e" by (elim G_edgeE)
    have "u \<noteq> esnd e" using uv(2) assms snd_in[OF e(1)] sides_disjoint by (metis IntI empty_iff subsetD)
    hence "u = efst e" "v = esnd e" using e(2) by (auto simp: cedge_def doubleton_eq_iff)
    thus "v \<in> esnd ` {e \<in> E. efst e \<in> X}" using e(1) uv(2) by blast
  qed
  show "esnd ` {e \<in> E. efst e \<in> X} \<subseteq> Neighbourhood G X"
  proof
    fix v assume "v \<in> esnd ` {e \<in> E. efst e \<in> X}"
    then obtain e where e: "e \<in> E" "efst e \<in> X" "v = esnd e" by blast
    have "v \<notin> X" using e(1,3) assms snd_in[OF e(1)] sides_disjoint by (metis IntI empty_iff subsetD)
    moreover have "{efst e, v} \<in> G" using e by (auto simp: G_def cedge_def)
    ultimately show "v \<in> Neighbourhood G X" using e(2) by (auto simp: Neighbourhood_def)
  qed
qed

theorem hall_sound:
  assumes "hall_check S"
  shows "\<nexists>M. perfect_matching G M"
proof -
  have LG: "L \<inter> Vs G = L" "R \<inter> Vs G = R" using Vs_G by auto
  note fb = frobenius_standard_bipartite[OF bipartite_G graph_invar_G, unfolded LG]
  show ?thesis
  proof (cases "length ls = length rs")
    case False
    hence "card L \<noteq> card R" using distinct_card[OF ls_distinct] distinct_card[OF rs_distinct] by simp
    thus ?thesis using fb by blast
  next
    case True
    obtain Sm k ok where s: "hall_S {} 0 S = (Sm, k, ok)" by (cases "hall_S {} 0 S") auto
    obtain Nm nb where nn: "hall_N Sm {} 0 elist = (Nm, nb)" by (cases "hall_N Sm {} 0 elist") auto
    have ok: "ok" and lt: "nb < k" using assms True s nn by (simp_all add: hall_check_def)
    have S: "Sm = set S" "k = card Sm" "set S \<subseteq> L" using hall_S_props[of "{}" 0 S Sm k] s ok by simp_all
    have "Nm = esnd ` {e \<in> E. efst e \<in> set S}" "nb = card Nm"
      using hall_N_props[OF nn] S(1) elist_E by simp_all
    hence "card (Neighbourhood G (set S)) < card (set S)" using neighbourhood_left[OF S(3)] lt S(1,2) by simp
    hence "\<not> (\<forall>X \<subseteq> L. card X \<le> card (Neighbourhood G X))" using S(3) by (meson not_le)
    thus ?thesis using fb by blast
  qed
qed

corollary hall_complete:
  assumes "\<nexists>M. perfect_matching G M" "length ls = length rs"
  shows "\<exists>X \<subseteq> L. card (Neighbourhood G X) < card X"
proof -
  have LG: "L \<inter> Vs G = L" "R \<inter> Vs G = R" using Vs_G by auto
  have "card L = card R" using assms(2) distinct_card[OF ls_distinct] distinct_card[OF rs_distinct] by simp
  thus ?thesis using assms(1) frobenius_standard_bipartite[OF bipartite_G graph_invar_G, unfolded LG]
    by (meson not_le)
qed

subsubsection \<open>Extremal Weight Maximum Cardinality Matchings\<close>

text \<open>Every matching has at most @{text "|L - S| + |N(S)|"} edges: map each edge to its right
      endpoint if its left endpoint is in @{term S}, and to its left endpoint otherwise.\<close>

lemma defic_bound:
  assumes "graph_matching G M'" "Sset \<subseteq> L"
  shows "card M' \<le> card (L - Sset) + card (esnd ` {e \<in> E. efst e \<in> Sset})"
proof -
  define Nset where "Nset = esnd ` {e \<in> E. efst e \<in> Sset}"
  define f where "f d = (if d \<inter> Sset = {} then the_elem (d \<inter> L) else the_elem (d \<inter> R))" for d
  have fe: "f (cedge e) = (if efst e \<in> Sset then esnd e else efst e)" if "e \<in> E" for e
  proof -
    have "cedge e \<inter> L = {efst e}" "cedge e \<inter> R = {esnd e}"
      using fst_in[OF that] snd_in[OF that] sides_disjoint by (auto simp: cedge_def)
    moreover have "cedge e \<inter> Sset = {} \<longleftrightarrow> efst e \<notin> Sset"
      using snd_in[OF that] sides_disjoint assms(2) by (auto simp: cedge_def)
    ultimately show ?thesis by (simp add: f_def)
  qed
  have fin: "f d \<in> d \<and> f d \<in> (L - Sset) \<union> Nset" if d: "d \<in> G" for d
  proof -
    obtain e where e: "e \<in> E" "d = cedge e" using d by (rule G_edgeE)
    show ?thesis using fe[OF e(1)] e fst_in[OF e(1)] by (auto simp: cedge_def Nset_def)
  qed
  have "inj_on f M'"
  proof (rule inj_onI)
    fix d1 d2 assume d: "d1 \<in> M'" "d2 \<in> M'" "f d1 = f d2"
    have "d1 \<in> G" "d2 \<in> G" using d(1,2) assms(1) by auto
    hence "f d1 \<in> d1" "f d2 \<in> d2" using fin by blast+
    hence "f d1 \<in> d1 \<inter> d2" using d(3) by simp
    thus "d1 = d2" using assms(1) d(1,2) by (auto simp: matching_def)
  qed
  moreover have "f ` M' \<subseteq> (L - Sset) \<union> Nset" using fin assms(1) by auto
  moreover have "finite ((L - Sset) \<union> Nset)" using finite_E by (simp add: Nset_def)
  ultimately have "card M' \<le> card ((L - Sset) \<union> Nset)" by (rule card_inj_on_le)
  also have "\<dots> \<le> card (L - Sset) + card Nset" by (rule card_Un_le)
  finally show ?thesis by (simp add: Nset_def)
qed

lemma card_Mat: "\<lbrakk>set ms \<subseteq> E; distinct (map efst ms)\<rbrakk> \<Longrightarrow> card (Mat ms) = length ms"
proof -
  assume a: "set ms \<subseteq> E" "distinct (map efst ms)"
  have "inj_on cedge (set ms)" using a(1) cedge_eq by (meson inj_onI subsetD)
  moreover have "distinct ms" using a(2) distinct_map by blast
  ultimately show ?thesis by (simp add: Mat_def card_image distinct_card)
qed

theorem certify_mc_sound:
  assumes "certify_mc neg ms ys t S"
  shows "min_weight_max_card_matching G (wt neg) (Mat ms)"
proof -
  have c: "certify_sh neg False t ms ys" and d: "defic_ok ms S"
    using assms by (simp_all add: certify_mc_def)
  obtain U where m: "match_list neg t ys {} ms = (U, True)"
    using c by (cases "match_list neg t ys {} ms") (auto simp: certify_sh_def)
  note M = Mat_props[OF m]
  obtain Sm k ok where s: "hall_S {} 0 S = (Sm, k, ok)" by (cases "hall_S {} 0 S") auto
  obtain Nm nb where nn: "hall_N Sm {} 0 elist = (Nm, nb)" by (cases "hall_N Sm {} 0 elist") auto
  have ok: "ok" and le: "length ls + nb \<le> length ms + k" using d s nn by (simp_all add: defic_ok_def)
  have S: "Sm = set S" "k = card Sm" "set S \<subseteq> L" using hall_S_props[of "{}" 0 S Sm k] s ok by simp_all
  have N: "nb = card (esnd ` {e \<in> E. efst e \<in> set S})"
    using hall_N_props[OF nn] S(1) elist_E by simp
  have cS: "card (L - set S) = length ls - k" "k \<le> length ls"
    using card_Diff_subset[OF _ S(3)] card_mono[OF _ S(3)] S(1,2) distinct_card[OF ls_distinct]
    by simp_all
  have "max_card_matching G (Mat ms)"
  proof (rule max_card_matchingI')
    show "graph_matching G (Mat ms)" by (rule M(1))
    fix M' assume "graph_matching G M'"
    hence "card M' \<le> length ls - k + nb" using defic_bound[OF _ S(3)] N cS(1) by simp
    thus "card M' \<le> card (Mat ms)" using le cS(2) card_Mat[OF M(6,4)] by simp
  qed
  thus ?thesis using shift_max_card[OF certify_matching_sound[OF c, unfolded wt_sh_def]] by blast
qed

corollary min_weight_max_card_certified:
  "certify_mc False ms ys t S \<Longrightarrow> min_weight_max_card_matching G wG (Mat ms)"
  using certify_mc_sound[of False] by (simp add: wt_False)

corollary max_weight_max_card_certified:
  "certify_mc True ms ys t S \<Longrightarrow> max_weight_max_card_matching G wG (Mat ms)"
  using certify_mc_sound[of True] min_max_card_and_max_max_card_matching[of G "- wG"]
  by (simp add: wt_True neg_neg_wG)

end

end
