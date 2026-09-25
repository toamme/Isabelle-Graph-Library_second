theory Multigraph_Potentials
  imports Multigraph_Weighted_Paths
begin

section ‹Potentials on Weighted Multigraphs›

text ‹A real weight function on a finite directed multigraph is ‹conservative› when no closed walk
      has negative total weight. This is the classical hypothesis under which a potential function
      exists: a real-valued function on vertices making every edge's ‹reduced cost›
      ‹w e + π (tail e) - π (head e)› non-negative. The characterisation theorem below proves both
      directions, purely in terms of ‹multigraph›, ‹weight›, ‹path_bet› and ‹distance_set›, with no
      reference to flows, capacities or costs.›

context multigraph
begin

subsection ‹Conservative Weight Functions›

definition conservative :: "('edge ⇒ real) ⇒ bool" where
  "conservative w ⟷ (∀ es v. es ≠ [] ⟶ path_bet es v v ⟶ weight w es ≥ 0)"

lemma conservativeI:
  "(⋀ es v. es ≠ [] ⟹ path_bet es v v ⟹ weight w es ≥ 0) ⟹ conservative w"
  by (auto simp: conservative_def)

lemma conservativeD:
  "conservative w ⟹ es ≠ [] ⟹ path_bet es v v ⟹ weight w es ≥ 0"
  by (auto simp: conservative_def)

subsection ‹A Potential Forces Conservativity›

lemma path_bet_telescope:
  fixes π :: "'a ⇒ real"
  assumes "path_bet es u v"
  shows "(∑ e ← es. π (fst e) - π (snd e)) = π u - π v"
using assms proof (induction es arbitrary: u)
  case Nil
  then show ?case by simp
next
  case (Cons e es)
  from Cons.prems have eE: "e ∈ ℰ" and fu: "fst e = u" and rest: "path_bet es (snd e) v"
    by (auto elim: path_bet_ConsE)
  have IHes: "(∑ e ← es. π (fst e) - π (snd e)) = π (snd e) - π v"
    using Cons.IH rest by blast
  show ?case using IHes fu by simp
qed

lemma conservative_of_potential:
  assumes "∀ e ∈ ℰ. w e + π (fst e) - π (snd e) ≥ 0"
  shows "conservative w"
proof (rule conservativeI)
  fix es v assume es: "es ≠ []" and pb: "path_bet es v v"
  have sub: "set es ⊆ ℰ" using path_bet_edges_subset[OF pb] .
  have tel: "(∑ e ← es. π (fst e) - π (snd e)) = 0"
    using path_bet_telescope[OF pb] by simp
  have mono: "(∑ e ← es. - (π (fst e) - π (snd e))) ≤ (∑ e ← es. w e)"
  proof (rule sum_list_mono)
    fix e assume "e ∈ set es"
    then have "e ∈ ℰ" using sub by blast
    then show "- (π (fst e) - π (snd e)) ≤ w e" using assms by fastforce
  qed
  have neg: "(∑ e ← es. - (π (fst e) - π (snd e))) = - (∑ e ← es. π (fst e) - π (snd e))"
    by (induction es) simp_all
  show "weight w es ≥ 0" using mono neg tel by (simp add: weight_def)
qed

subsection ‹Conservativity Yields a Potential, via Distance from the Vertex Set›

lemma conservative_shortcut:
  assumes "conservative w"
  shows "path_bet es u v ⟹ ∃ es'. path_bet es' u v ∧ distinct es' ∧ weight w es' ≤ weight w es"
proof(induction "length es" arbitrary: es u v rule: less_induct)
  case less
  show ?case
  proof(cases "distinct es")
    case True
    then show ?thesis using less.prems by blast
  next
    case False
    from not_distinct_decomp[OF False] obtain p1 x p2 p3
      where dec0: "es = p1 @ [x] @ p2 @ [x] @ p3" by blast
    have dec: "es = p1 @ x # p2 @ x # p3" using dec0 by simp
    have "path_bet (p1 @ (x # p2 @ x # p3)) u v" using less.prems dec by simp
    then obtain m1 where p1p: "path_bet p1 u m1" and rest1: "path_bet (x # p2 @ x # p3) m1 v"
      by (auto elim: path_bet_appendE)
    from rest1 have xE: "x ∈ ℰ" and m1: "fst x = m1" and rest2: "path_bet (p2 @ x # p3) (snd x) v"
      by (auto elim: path_bet_ConsE)
    from rest2 obtain m2 where p2p: "path_bet p2 (snd x) m2" and rest3: "path_bet (x # p3) m2 v"
      by (auto elim: path_bet_appendE)
    from rest3 have m2: "fst x = m2" and p3p: "path_bet p3 (snd x) v"
      by (auto elim: path_bet_ConsE)
    have m1': "path_bet p1 u (fst x)" using p1p m1 by simp
    have p2': "path_bet p2 (snd x) (fst x)" using p2p m2 by simp
    have xp3: "path_bet (x # p3) (fst x) v" using xE p3p by (rule path_bet_ConsI)
    have xp2: "path_bet (x # p2) (fst x) (fst x)" using xE p2' by (rule path_bet_ConsI)
    have shortpath: "path_bet (p1 @ x # p3) u v" using path_bet_append[OF m1' xp3] by simp
    have shortlen: "length (p1 @ x # p3) < length es" using dec by simp
    have nonneg0: "weight w (x # p2) ≥ 0" using conservativeD[OF assms] xp2 by fastforce
    have weq: "weight w es = weight w (p1 @ x # p3) + weight w (x # p2)" using dec by simp
    have shortwt: "weight w (p1 @ x # p3) ≤ weight w es" using weq nonneg0 by simp
    then obtain es' where "path_bet es' u v" "distinct es'" "weight w es' ≤ weight w (p1 @ x # p3)"
      using less.hyps[OF shortlen shortpath] by blast
    then show ?thesis using shortwt by fastforce
  qed
qed

lemma distance_neq_minf: "distance w a b ≠ - ∞"
proof (cases "reachable a b")
  case True
  then obtain es where "is_shortest_path w es a b" by (rule is_shortest_path_exists)
  then show ?thesis using is_shortest_path_dist by fastforce
next
  case False
  then show ?thesis using unreachable_dist by simp
qed

lemma conservative_distance_set_finite:
  assumes "v ∈ 𝒱"
  shows "distance_set w 𝒱 v ≠ ∞" "distance_set w 𝒱 v ≠ - ∞"
proof -
  have "distance_set w 𝒱 v ≤ distance w v v" using dist_set_mem[OF assms] .
  moreover have "distance w v v < ∞" using reachable_dist[OF reachable_refl] .
  ultimately show "distance_set w 𝒱 v ≠ ∞" by auto
next
  obtain u where eq: "distance_set w 𝒱 v = distance w u v"
    using distance_set_wit[OF 𝒱_finite V_non_empt] by blast
  then show "distance_set w 𝒱 v ≠ - ∞" using distance_neq_minf by simp
qed

lemma conservative_distance_set_triangle:
  assumes "conservative w" "e ∈ ℰ"
  shows "distance_set w 𝒱 (snd e) ≤ distance_set w 𝒱 (fst e) + ereal (w e)"
proof -
  have uV: "fst e ∈ 𝒱" using fst_E_V[OF assms(2)] .
  have fin: "distance_set w 𝒱 (fst e) < ∞"
    using conservative_distance_set_finite(1)[OF uV] by simp
  obtain es s where sV: "s ∈ 𝒱" and short: "is_shortest_path w es s (fst e)"
                and eqd: "distance w s (fst e) = distance_set w 𝒱 (fst e)"
    using dist_set_less_infty_get_path[OF 𝒱_finite fin] by blast
  have pbes: "path_bet es s (fst e)" using short by (rule is_shortest_path_path_bet)
  have esw: "ereal (weight w es) = distance_set w 𝒱 (fst e)"
    using is_shortest_path_dist[OF short] eqd by simp
  have pbe: "path_bet (es @ [e]) s (snd e)" using path_bet_snocI[OF pbes assms(2)] .
  obtain es' where pbes': "path_bet es' s (snd e)" and dises': "distinct es'"
               and wtes': "weight w es' ≤ weight w (es @ [e])"
    using conservative_shortcut[OF assms(1) pbe] by blast
  have "distance_set w 𝒱 (snd e) ≤ ereal (weight w es')"
    using distance_set_le_path[OF sV pbes' dises'] .
  also have "... ≤ ereal (weight w (es @ [e]))" using wtes' by simp
  also have "... = ereal (weight w es) + ereal (w e)" by simp
  also have "... = distance_set w 𝒱 (fst e) + ereal (w e)" using esw by simp
  finally show ?thesis .
qed

lemma potential_of_conservative:
  assumes "conservative w"
  shows "∃ π. ∀ e ∈ ℰ. w e + π (fst e) - π (snd e) ≥ 0"
proof -
  define π where "π = (λ v. real_of_ereal (distance_set w 𝒱 v))"
  have "w e + π (fst e) - π (snd e) ≥ 0" if eE: "e ∈ ℰ" for e
  proof -
    have fV: "fst e ∈ 𝒱" and sV: "snd e ∈ 𝒱" using fst_E_V[OF eE] snd_E_V[OF eE] by auto
    obtain rf where rf: "distance_set w 𝒱 (fst e) = ereal rf"
      using conservative_distance_set_finite[OF fV] by (cases "distance_set w 𝒱 (fst e)") auto
    obtain rs where rs: "distance_set w 𝒱 (snd e) = ereal rs"
      using conservative_distance_set_finite[OF sV] by (cases "distance_set w 𝒱 (snd e)") auto
    have "distance_set w 𝒱 (snd e) ≤ distance_set w 𝒱 (fst e) + ereal (w e)"
      using conservative_distance_set_triangle[OF assms eE] .
    then have "rs ≤ rf + w e" using rf rs by simp
    then show ?thesis using rf rs by (simp add: π_def)
  qed
  then show ?thesis by blast
qed

subsection ‹No Negative Simple Cycle Already Suffices›

text ‹A checkable strengthening of ‹conservative›'s hypothesis side: it is enough to rule out
      negative-weight simple (distinct) closed walks, since any closed walk shortens, without
      increasing weight, to one that is simple --- the same decomposition used by
      ‹conservative_shortcut›, but run here as the base case of the bootstrap instead of relying on
      it.›

lemma closed_walk_nonneg_of_simple:
  assumes simp_hyp: "⋀ es v. es ≠ [] ⟹ path_bet es v v ⟹ distinct es ⟹ weight w es ≥ 0"
  shows "path_bet es v v ⟹ es ≠ [] ⟹ weight w es ≥ 0"
proof(induction "length es" arbitrary: es v rule: less_induct)
  case less
  show ?case
  proof(cases "distinct es")
    case True
    then show ?thesis using less.prems simp_hyp by blast
  next
    case False
    from not_distinct_decomp[OF False] obtain p1 x p2 p3
      where dec0: "es = p1 @ [x] @ p2 @ [x] @ p3" by blast
    have dec: "es = p1 @ x # p2 @ x # p3" using dec0 by simp
    have "path_bet (p1 @ (x # p2 @ x # p3)) v v" using less.prems dec by simp
    then obtain m1 where p1p: "path_bet p1 v m1" and rest1: "path_bet (x # p2 @ x # p3) m1 v"
      by (auto elim: path_bet_appendE)
    from rest1 have xE: "x ∈ ℰ" and m1: "fst x = m1" and rest2: "path_bet (p2 @ x # p3) (snd x) v"
      by (auto elim: path_bet_ConsE)
    from rest2 obtain m2 where p2p: "path_bet p2 (snd x) m2" and rest3: "path_bet (x # p3) m2 v"
      by (auto elim: path_bet_appendE)
    from rest3 have m2: "fst x = m2" and p3p: "path_bet p3 (snd x) v"
      by (auto elim: path_bet_ConsE)
    have m1': "path_bet p1 v (fst x)" using p1p m1 by simp
    have p2': "path_bet p2 (snd x) (fst x)" using p2p m2 by simp
    have xp3: "path_bet (x # p3) (fst x) v" using xE p3p by (rule path_bet_ConsI)
    have xp2: "path_bet (x # p2) (fst x) (fst x)" using xE p2' by (rule path_bet_ConsI)
    have shortpath: "path_bet (p1 @ x # p3) v v" using path_bet_append[OF m1' xp3] by simp
    have shortlen: "length (p1 @ x # p3) < length es" using dec by simp
    have looplen: "length (x # p2) < length es" using dec by simp
    have loopnn: "weight w (x # p2) ≥ 0" using less.hyps[OF looplen xp2] by simp
    have shortnn: "weight w (p1 @ x # p3) ≥ 0" using less.hyps[OF shortlen shortpath] by simp
    have weq: "weight w es = weight w (p1 @ x # p3) + weight w (x # p2)" using dec by simp
    show ?thesis using weq loopnn shortnn by simp
  qed
qed

lemma conservative_of_simple:
  assumes "⋀ es v. es ≠ [] ⟹ path_bet es v v ⟹ distinct es ⟹ weight w es ≥ 0"
  shows "conservative w"
proof (rule conservativeI)
  fix es v assume "es ≠ []" "path_bet es v v"
  then show "weight w es ≥ 0" using assms closed_walk_nonneg_of_simple by blast
qed

subsection ‹The Characterisation Theorem›

theorem ex_potential_iff_conservative:
  "(∃ π. ∀ e ∈ \<E>. w e + π (fst e) - π (snd e) ≥ 0) ⟷ conservative w"
  using conservative_of_potential potential_of_conservative by blast

end
end
