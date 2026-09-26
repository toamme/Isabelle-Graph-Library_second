theory Network_Simplex_Preservation
  imports Network_Simplex
begin

text \<open>\<^bold>\<open>Unique-path characterisation of an arborescence.\<close> A finite graph in which every vertex is
      joined to the designated root @{term r} by \<^emph>\<open>exactly one\<close> simple (vertex-disjoint) path --- more
      precisely, any two vertices are joined by a unique distinct walk --- is a rooted spanning
      arborescence. This is the bridge from the \<open>arborescense_adt\<close> axioms (which supply exactly
      the unique-distinct-walk property, \<open>general(3)\<close>) to the graph-library predicate
      \<open>graph_abs.arborescence\<close> used by \<open>spanning_tree_partition\<close>. Connectivity of the
      root component follows from existence of the walks; acyclicity follows from uniqueness, via
      \<open>graph_abs.decycle_edge_path\<close>: a cycle through an edge \<open>{a,b}\<close> yields a second
      distinct \<open>b\<close>--\<open>a\<close> walk avoiding that edge, contradicting the unique walk given by the edge.\<close>

lemma unique_walks_arborescence:
  assumes gi: "graph_invar G"
    and rVs: "r \<in> Vs G"
    and uniq: "\<And>x y. x \<in> Vs G \<Longrightarrow> y \<in> Vs G \<Longrightarrow> \<exists>!p. walk_betw G x p y \<and> distinct p"
  shows "graph_abs.arborescence G r G"
proof -
  have gaG: "graph_abs G" using gi by (simp add: graph_abs_def)
  have reach_r: "\<And>x. x \<in> Vs G \<Longrightarrow> reachable G r x"
  proof -
    fix x assume xVs: "x \<in> Vs G"
    obtain p where wp: "walk_betw G x p r" using uniq[OF xVs rVs] by blast
    have "walk_betw G r (rev p) x" using wp by (rule walk_symmetric)
    thus "reachable G r x" by (auto simp: reachable_def)
  qed
  have reach_Vs: "\<And>x. reachable G r x \<Longrightarrow> x \<in> Vs G"
    by (auto simp: reachable_def dest: walk_endpoints(2))
  have vscc: "connected_component G r = Vs G"
    by (rule connected_component_set[OF rVs reach_r reach_Vs])
  have nocyc: "\<nexists>u c. decycle G u c"
  proof (rule notI, elim exE)
    fix u c assume dc: "decycle G u c"
    have ep: "epath G u c u" and lc: "2 < length c" and dic: "distinct c"
      using dc by (auto simp: decycle_def)
    have csub: "set c \<subseteq> G" using ep by (rule epath_edges_subset)
    have cne: "c \<noteq> []" using lc by auto
    have e1: "hd c \<in> G" using csub cne by (meson hd_in_set subset_iff)
    obtain a b where eab: "hd c = {a, b}" and abne: "a \<noteq> b"
      using dblton_graphE[OF graph_invar_dblton[OF gi] e1] by metis
    have abG: "{a, b} \<in> G" using e1 eab by simp
    have insEq: "insert {a, b} (G - {{a, b}}) = G" using abG by auto
    have memc: "{a, b} \<in> set c" using eab hd_in_set[OF cne] by simp
    have "\<exists>q. walk_betw (G - {{a, b}}) b q a"
      using graph_abs.decycle_edge_path[OF gaG, of a b "G - {{a, b}}" u c]
            insEq abG dc memc by simp
    then obtain q where wq: "walk_betw (G - {{a, b}}) b q a" by blast
    obtain D where wD: "walk_betw (G - {{a, b}}) b D a" and dD: "distinct D"
      using walk_betw_different_verts_to_ditinct[OF wq abne[symmetric] refl] by blast
    have wDG: "walk_betw G b D a" using wD walk_subset by (metis Diff_subset)
    have wedge: "walk_betw G b [b, a] a" using abG by (simp add: insert_commute edges_are_walks)
    have aVs: "a \<in> Vs G" using abG by (auto simp: Vs_def)
    have bVs: "b \<in> Vs G" using abG by (auto simp: Vs_def)
    have Q1: "walk_betw G b D a \<and> distinct D" using wDG dD by simp
    have Q2: "walk_betw G b [b, a] a \<and> distinct [b, a]" using wedge abne by simp
    have "D = [b, a]" using uniq[OF bVs aVs] Q1 Q2 by blast
    hence "walk_betw (G - {{a, b}}) b [b, a] a" using wD by simp
    hence "{b, a} \<in> G - {{a, b}}" by (auto simp: walk_betw_def path_2)
    thus False by (simp add: insert_commute)
  qed
  have hnc: "graph_abs.has_no_cycle G G"
    using nocyc by (simp add: graph_abs.has_no_cycle_def[OF gaG])
  show "graph_abs.arborescence G r G"
    using gaG hnc vscc by (auto intro!: graph_abs.arborescenceI)
qed

section \<open>Preservation of the loop invariants and the termination measure\<close>

text \<open>For each of the two \<^emph>\<open>recursive\<close> branches of @{const network_simplex_spec.ns_loop} --- the
      degenerate flip @{const network_simplex_spec.ns_flip} (@{term \<open>leaving = None\<close>}, KV's
      @{term \<open>e = e0\<close>}) and the full pivot @{const network_simplex_spec.ns_pivot} --- we prove that the
      loop invariant @{const network_simplex.ns_invar} is preserved and that a lexicographic
      termination measure strictly decreases. The two terminal branches
      (@{const network_simplex_spec.ns_optimal}, @{const network_simplex_spec.ns_unbounded_upd}) only
      set the return flag, so they preserve every invariant trivially and never recurse.

      The two recursive-case proofs are \<^emph>\<open>conditional\<close> on a family of auxiliary facts about the helper
      functions. Following the design notes, each auxiliary function has a \<^emph>\<open>single\<close> bundled lemma
      stating all the properties its callers consume under one shared set of hypotheses, so the
      recursive-case proofs can reuse the whole lemma context in one step. The informal arguments these
      lemmas discharge are \S{}0--\S{}4 of \<open>Network_Simplex_Design_Notes.md\<close>; the lexicographic measure is
      that file's ``Termination'' section.\<close>

context network_simplex
begin

subsection \<open>Destructor/intro bundle for @{const spanning_tree_partition}\<close>

text \<open>Feeding the eight conjuncts of @{const spanning_tree_partition} inline via @{text "dest:"}
      instead of hand-counted @{text "THEN conjunctN"} chains.\<close>

lemma spanning_tree_partitionD:
  "spanning_tree_partition r T L U \<Longrightarrow> \<E> = T \<union> U \<union> L"
  "spanning_tree_partition r T L U \<Longrightarrow> T \<inter> U = {}"
  "spanning_tree_partition r T L U \<Longrightarrow> T \<inter> L = {}"
  "spanning_tree_partition r T L U \<Longrightarrow> L \<inter> U = {}"
  "spanning_tree_partition r T L U \<Longrightarrow>
     graph_abs.arborescence ((\<lambda>e. {fst e, snd e}) ` T) r ((\<lambda>e. {fst e, snd e}) ` T)"
  "spanning_tree_partition r T L U \<Longrightarrow> graph_abs ((\<lambda>e. {fst e, snd e}) ` T)"
  "spanning_tree_partition r T L U \<Longrightarrow>
     (\<forall>e e'. {e, e'} \<subseteq> T \<and> {fst e, snd e} = {fst e', snd e'} \<longrightarrow> e = e')"
  "spanning_tree_partition r T L U \<Longrightarrow> dVs (make_pair ` T) = \<V>"
  by (simp_all add: spanning_tree_partition_def)

lemma spanning_tree_partitionI:
  "\<lbrakk>\<E> = T \<union> U \<union> L; T \<inter> U = {}; T \<inter> L = {}; L \<inter> U = {};
    graph_abs.arborescence ((\<lambda>e. {fst e, snd e}) ` T) r ((\<lambda>e. {fst e, snd e}) ` T);
    graph_abs ((\<lambda>e. {fst e, snd e}) ` T);
    \<forall>e e'. {e, e'} \<subseteq> T \<and> {fst e, snd e} = {fst e', snd e'} \<longrightarrow> e = e';
    dVs (make_pair ` T) = \<V>\<rbrakk> \<Longrightarrow> spanning_tree_partition r T L U"
  unfolding spanning_tree_partition_def by blast

subsection \<open>Structural helpers (H1, H2)\<close>

text \<open>\<^bold>\<open>(H1)\<close> @{const par_edge} is injective on the non-root vertices. If two vertices shared a parent
      edge, the child endpoint would be ambiguous and one vertex's simple walk to the root would begin
      with a repeat, contradicting the walk conjunct of @{const ns_invar_tree} and the uniqueness of
      simple walks.\<close>

lemma singleton_not_dblton: "dblton_graph G \<Longrightarrow> {x} \<notin> G"
  by (auto simp: dblton_graph_def)

lemma par_edge_inj:
  assumes "ns_invar s" "v \<in> \<V> - {r}" "v' \<in> \<V> - {r}" "par_edge s v = par_edge s v'"
  shows "v = v'"
proof -
  note tree = ns_invarD(7)[OF assms(1)]
  have e0E: "par_edge s v \<in> \<E>" using ns_invar_tree_edgeD[OF tree assms(2)] .
  have nsl: "fst (par_edge s v) \<noteq> snd (par_edge s v)"
  proof
    assume sl: "fst (par_edge s v) = snd (par_edge s v)"
    have et: "par_edge s v \<in> ns_tree_edges s" using assms(2) by (auto simp: par_edge_def)
    have ga: "graph_abs ((\<lambda>e. {fst e, snd e}) ` ns_tree_edges s)"
      using spanning_tree_partitionD(6)[OF ns_invar_partitionD[OF ns_invarD(3)[OF assms(1)]]] .
    have dbl: "dblton_graph ((\<lambda>e. {fst e, snd e}) ` ns_tree_edges s)" using graph_abs.dblton_E[OF ga] .
    have "{fst (par_edge s v)} \<in> (\<lambda>e. {fst e, snd e}) ` ns_tree_edges s" using et sl by force
    thus False using singleton_not_dblton[OF dbl] by blast
  qed
  have dv: "if par_up s v then fst (par_edge s v) = v else snd (par_edge s v) = v"
    using ns_invar_tree_dirD[OF tree assms(2)] .
  have dv': "if par_up s v' then fst (par_edge s v') = v' else snd (par_edge s v') = v'"
    using ns_invar_tree_dirD[OF tree assms(3)] .
  have setv: "{v, par_vx s v} = {fst (par_edge s v), snd (par_edge s v)}"
    using dv by (auto simp: par_vx_def split: if_splits)
  have setv': "{v', par_vx s v'} = {fst (par_edge s v), snd (par_edge s v)}"
    using dv' by (auto simp: par_vx_def assms(4)[symmetric] split: if_splits)
  show "v = v'"
  proof (rule ccontr)
    assume ne: "v \<noteq> v'"
    have sets_eq: "{v, par_vx s v} = {v', par_vx s v'}" using setv setv' by simp
    have m1: "v' \<in> {v, par_vx s v}" using sets_eq by auto
    have m2: "v \<in> {v', par_vx s v'}" using sets_eq by auto
    have pv: "par_vx s v = v'" using m1 ne by auto
    have pv': "par_vx s v' = v" using m2 ne by auto
    obtain q where q: "distinct (v # v' # q)
                     \<and> walk_betw (abstract_arborescense (spanning_tree s)) v (v # v' # q) r"
      using ns_invar_tree_walkD[OF tree assms(2)] unfolding pv by blast
    obtain q' where q': "distinct (v' # v # q')
                       \<and> walk_betw (abstract_arborescense (spanning_tree s)) v' (v' # v # q') r"
      using ns_invar_tree_walkD[OF tree assms(3)] unfolding pv' by blast
    have wv: "walk_betw (abstract_arborescense (spanning_tree s)) v (v # v' # q) r" using q by simp
    have tail: "walk_betw (abstract_arborescense (spanning_tree s)) v' (v' # q) r"
      using wv by (metis walk_betw_cons)
    have dtail: "distinct (v' # q)" using q by simp
    have arb: "arborescense_invar (spanning_tree s)"
      using ns_invar_implD(7)[OF ns_invarD(1)[OF assms(1)]] .
    have rV: "r \<in> \<V>" using general(1) .
    have v'V: "v' \<in> \<V>" using assms(3) by simp
    have uniq: "\<exists>!p. walk_betw (abstract_arborescense (spanning_tree s)) v' p r \<and> distinct p"
      using general(3)[OF arb rV v'V] .
    have eq: "v' # q = v' # v # q'" using uniq tail dtail q' by (metis (mono_tags, lifting))
    have "q = v # q'" using eq by simp
    then have "distinct (v # v' # v # q')" using q by simp
    thus False by simp
  qed
qed

text \<open>\<^bold>\<open>(H2)\<close> @{const par_vx} is the successor of @{term v} on its unique simple walk to the root: that
      walk starts \<open>v # par_vx s v # \<dots>\<close>.\<close>

lemma par_vx_walk_succ:
  assumes "ns_invar s" "v \<in> \<V> - {r}"
  shows "\<exists> q. distinct (v # par_vx s v # q)
             \<and> walk_betw (abstract_arborescense (spanning_tree s)) v (v # par_vx s v # q) r"
  using ns_invar_tree_walkD[OF ns_invarD(7)[OF assms(1)] assms(2)] .

subsection \<open>Scan helpers\<close>

text \<open>The vertex returned by a bottleneck scan is always a member of the scanned path. Both scans fold
      an accumulator @{term \<open>(m, best)\<close>} over the path; the second component is only ever set to a
      vertex taken from the list, so on a @{term \<open>Some v\<close>} result @{term v} lies on the path. Proved by
      induction on the path from the right (the accumulator is generalised).\<close>

lemma scan_up_snd_mem: "scan_up s p = (m, v) \<Longrightarrow> m \<noteq> - 1 \<Longrightarrow> v \<in> set p"
proof (induct p arbitrary: m v rule: rev_induct)
  case Nil thus ?case by (simp add: scan_up_def)
next
  case (snoc x p)
  obtain m' b' where mb: "scan_up s p = (m', b')" by (cases "scan_up s p")
  have "scan_up s (p @ [x]) =
        (let rr = res_up s x in if rr = - 1 then (m', b')
         else if m' = - 1 then (rr, x) else if rr \<le> m' then (rr, x) else (m', b'))"
    using mb by (simp add: scan_up_def)
  thus ?case using snoc.hyps mb snoc.prems by (auto simp: Let_def split: if_splits)
qed

lemma scan_down_snd_mem: "scan_down s p = (m, v) \<Longrightarrow> m \<noteq> - 1 \<Longrightarrow> v \<in> set p"
proof (induct p arbitrary: m v rule: rev_induct)
  case Nil thus ?case by (simp add: scan_down_def)
next
  case (snoc x p)
  obtain m' b' where mb: "scan_down s p = (m', b')" by (cases "scan_down s p")
  have "scan_down s (p @ [x]) =
        (let rr = res_down s x in if rr = - 1 then (m', b')
         else if m' = - 1 then (rr, x) else if rr < m' then (rr, x) else (m', b'))"
    using mb by (simp add: scan_down_def)
  thus ?case using snoc.hyps mb snoc.prems by (auto simp: Let_def split: if_splits)
qed

text \<open>The value component a scan returns is the residual at the returned vertex whenever a vertex was
      recorded (i.e.\ @{term \<open>m \<noteq> - 1\<close>}).\<close>

lemma scan_up_val_at: "scan_up s p = (m, v0) \<Longrightarrow> m \<noteq> - 1 \<Longrightarrow> res_up s v0 = m"
proof (induct p arbitrary: m v0 rule: rev_induct)
  case Nil thus ?case by (simp add: scan_up_def)
next
  case (snoc x p)
  obtain m' b' where mb: "scan_up s p = (m', b')" by (cases "scan_up s p")
  have "scan_up s (p @ [x]) =
        (let rr = res_up s x in if rr = - 1 then (m', b')
         else if m' = - 1 then (rr, x) else if rr \<le> m' then (rr, x) else (m', b'))"
    using mb by (simp add: scan_up_def)
  thus ?case using snoc.hyps mb snoc.prems by (auto simp: Let_def split: if_splits)
qed

lemma scan_down_val_at: "scan_down s p = (m, v0) \<Longrightarrow> m \<noteq> - 1 \<Longrightarrow> res_down s v0 = m"
proof (induct p arbitrary: m v0 rule: rev_induct)
  case Nil thus ?case by (simp add: scan_down_def)
next
  case (snoc x p)
  obtain m' b' where mb: "scan_down s p = (m', b')" by (cases "scan_down s p")
  have "scan_down s (p @ [x]) =
        (let rr = res_down s x in if rr = - 1 then (m', b')
         else if m' = - 1 then (rr, x) else if rr < m' then (rr, x) else (m', b'))"
    using mb by (simp add: scan_down_def)
  thus ?case using snoc.hyps mb snoc.prems by (auto simp: Let_def split: if_splits)
qed

subsection \<open>Residual signs (\S{}0)\<close>

text \<open>Under @{const ns_invar} every residual is non-negative or the @{term \<open>- 1\<close>} infinity sentinel:
      the backward residual is the (non-negative) flow, and the forward residual is \<open>cap - f \<ge> 0\<close>
      whenever it is finite (using @{thm cap_nonneg} to complete the sentinel encoding). On the strict
      side, an \<^emph>\<open>upward-traversed\<close> parent edge has a \<^emph>\<open>strictly positive\<close> residual (KV strong feasibility).\<close>

lemma res_bwd_nonneg:
  assumes "ns_invar s" "e \<in> \<E>"
  shows "0 \<le> res_bwd s e"
proof -
  have "isuflow (ns_flow_of s)"
    using ns_invar_bflowD[OF ns_invarD(2)[OF assms(1)]] by (simp add: isbflow_def)
  thus ?thesis using assms(2) by (auto simp: isuflow_def res_bwd_def)
qed

lemma res_fwd_sign:
  assumes "ns_invar s" "e \<in> \<E>"
  shows "0 \<le> res_fwd s e \<or> res_fwd s e = - 1"
proof (cases "cap e = - 1")
  case True thus ?thesis by (simp add: res_fwd_def)
next
  case False
  hence cnn: "0 \<le> cap e" using cap_nonneg[OF assms(2)] by simp
  have ue: "\<u> e = ereal (h (cap e))" using cap_finite[OF assms(2) cnn] .
  have "isuflow (ns_flow_of s)"
    using ns_invar_bflowD[OF ns_invarD(2)[OF assms(1)]] by (simp add: isbflow_def)
  hence "ereal (ns_flow_of s e) \<le> \<u> e" using assms(2) by (auto simp: isuflow_def)
  hence "ns_flow_of s e \<le> h (cap e)" using ue by simp
  hence "flow_lookup (current_flow s) e \<le> cap e" by (simp add: comp_def)
  thus ?thesis using False by (simp add: res_fwd_def)
qed

lemma res_down_sign:
  assumes "ns_invar s" "v \<in> \<V> - {r}"
  shows "0 \<le> res_down s v \<or> res_down s v = - 1"
proof -
  have pe: "par_edge s v \<in> \<E>" using ns_invar_tree_edgeD[OF ns_invarD(7)[OF assms(1)] assms(2)] .
  show ?thesis
  proof (cases "par_up s v")
    case True thus ?thesis using res_bwd_nonneg[OF assms(1) pe] by (simp add: res_down_def)
  next
    case False thus ?thesis using res_fwd_sign[OF assms(1) pe] by (simp add: res_down_def)
  qed
qed

lemma res_up_pos:
  assumes "ns_invar s" "v \<in> \<V> - {r}"
  shows "0 < res_up s v \<or> res_up s v = - 1"
proof -
  have pe: "par_edge s v \<in> \<E>" using ns_invar_tree_edgeD[OF ns_invarD(7)[OF assms(1)] assms(2)] .
  have strict: "ns_invar_strict s" using ns_invarD(6)[OF assms(1)] .
  show ?thesis
  proof (cases "par_up s v")
    case up: True
    show ?thesis
    proof (cases "cap (par_edge s v) = - 1")
      case True thus ?thesis by (simp add: res_up_def up res_fwd_def)
    next
      case False
      hence cnn: "0 \<le> cap (par_edge s v)" using cap_nonneg[OF pe] by simp
      have ue: "\<u> (par_edge s v) = ereal (h (cap (par_edge s v)))" using cap_finite[OF pe cnn] .
      have "ereal (h (flow_lookup (current_flow s) (par_edge s v))) < \<u> (par_edge s v)"
        using ns_invar_strict_upD[OF strict assms(2) up] .
      hence "flow_lookup (current_flow s) (par_edge s v) < cap (par_edge s v)" using ue by simp
      thus ?thesis using up False by (simp add: res_up_def res_fwd_def)
    qed
  next
    case False
    have "flow_lookup (current_flow s) (par_edge s v) > 0"
      using ns_invar_strict_downD[OF strict assms(2) False] .
    thus ?thesis using False by (simp add: res_up_def res_bwd_def)
  qed
qed

lemma mininf_sign:
  assumes "0 \<le> x \<or> x = - 1" "0 \<le> y \<or> y = - 1"
  shows "0 \<le> mininf x y \<or> mininf x y = - 1"
  using assms by (auto simp: mininf_def)

text \<open>Lifting the residual signs through a scan: if every scanned vertex is a non-root vertex, the
      scan's value component is again non-negative or @{term \<open>- 1\<close>}.\<close>

lemma scan_up_val_sign:
  assumes "ns_invar s" "set p \<subseteq> \<V> - {r}" "scan_up s p = (m, v0)"
  shows "0 \<le> m \<or> m = - 1"
proof (cases "m = - 1")
  case True thus ?thesis by simp
next
  case False
  have vm: "res_up s v0 = m" using scan_up_val_at[OF assms(3) False] .
  have mem: "v0 \<in> \<V> - {r}" using scan_up_snd_mem[OF assms(3) False] assms(2) by blast
  show ?thesis using res_up_pos[OF assms(1) mem] vm by auto
qed

lemma scan_down_val_sign:
  assumes "ns_invar s" "set p \<subseteq> \<V> - {r}" "scan_down s p = (m, v0)"
  shows "0 \<le> m \<or> m = - 1"
proof (cases "m = - 1")
  case True thus ?thesis by simp
next
  case False
  have vm: "res_down s v0 = m" using scan_down_val_at[OF assms(3) False] .
  have mem: "v0 \<in> \<V> - {r}" using scan_down_snd_mem[OF assms(3) False] assms(2) by blast
  show ?thesis using res_down_sign[OF assms(1) mem] vm by auto
qed

subsection \<open>Path vertices and selector facts\<close>

text \<open>Both tree paths returned by \<open>get_path_pair\<close> consist of non-root vertices: their vertices
      lie on a simple walk to @{term r} inside the arborescence, so they are in @{term \<open>\<V>\<close>}, and @{term r}
      (the walk's endpoint) cannot repeat inside a prefix by distinctness.\<close>

lemma get_path_pair_verts:
  assumes inv: "ns_invar s" and eE: "e \<in> \<E>" and neq: "fst e \<noteq> snd e"
    and pp: "get_path_pair (spanning_tree s) (fst e) (snd e) = (p1, p2)"
  shows "set p1 \<subseteq> \<V> - {r}" and "set p2 \<subseteq> \<V> - {r}"
proof -
  have arb: "arborescense_invar (spanning_tree s)" using ns_invar_implD(7)[OF ns_invarD(1)[OF inv]] .
  have fV: "fst e \<in> \<V>" using fst_E_V[OF eE] .
  have sV: "snd e \<in> \<V>" using snd_E_V[OF eE] .
  obtain a p3 where
    w1: "walk_betw (abstract_arborescense (spanning_tree s)) (fst e) (p1 @ a # p3) r" and
    w2: "walk_betw (abstract_arborescense (spanning_tree s)) (snd e) (p2 @ a # p3) r" and
    d1: "distinct (p1 @ a # p3)" and d2: "distinct (p2 @ a # p3)"
    using get_path_pair(1)[OF arb pp neq fV sV] by blast
  have VsV: "Vs (abstract_arborescense (spanning_tree s)) = \<V>" using general(4)[OF arb] .
  have "last (a # p3) = r" using w1 unfolding walk_betw_def by simp
  hence rin: "r \<in> set (a # p3)" by (metis last_in_set list.distinct(1))
  show "set p1 \<subseteq> \<V> - {r}"
  proof
    fix z assume z: "z \<in> set p1"
    have "z \<in> \<V>" using z walk_in_Vs[OF w1] VsV by auto
    moreover have "z \<noteq> r" using z rin d1 by auto
    ultimately show "z \<in> \<V> - {r}" by simp
  qed
  show "set p2 \<subseteq> \<V> - {r}"
  proof
    fix z assume z: "z \<in> set p2"
    have "z \<in> \<V>" using z walk_in_Vs[OF w2] VsV by auto
    moreover have "z \<noteq> r" using z rin d2 by auto
    ultimately show "z \<in> \<V> - {r}" by simp
  qed
qed

text \<open>When the selector fires, the entering edge is a real @{term L}/@{term U} edge --- hence a graph edge
      that is not (yet) a tree edge.\<close>

lemma ns_select_SomeD:
  assumes "ns_invar s" "ns_select s = Some (e, in_U, \<gamma>, sel')"
  shows "e \<in> ns_L_of s \<union> ns_U_of s" and "e \<in> \<E>" and "e \<notin> ns_tree_edges s"
proof -
  have prec: "selection_precond (edge_sel s) (potentials s) (edge_state s)"
    using ns_invar_implD[OF ns_invarD(1)[OF assms(1)]] ns_invar_pot_fitsD[OF ns_invarD(5)[OF assms(1)]]
    by (simp add: selection_precond_def potential_fits_spanning_tree_partition_def)
  have seleq: "sel_select (edge_sel s) (potentials s) (edge_state s) = Some (e, in_U, \<gamma>, sel')"
    using assms(2) by (simp add: ns_select_def)
  from sel_select_SomeD(4)[OF prec seleq]
  have ent: "entering_edge (potentials s) (edge_state s) e in_U" .
  show eLU: "e \<in> ns_L_of s \<union> ns_U_of s"
    using ent by (auto simp: entering_edge_def ns_L_of_def ns_U_of_def split: if_splits)
  show "e \<in> \<E>"
    using ent by (auto simp: entering_edge_def split: if_splits)
  have part: "spanning_tree_partition r (ns_tree_edges s)
     (ns_L_of s \<union> ns_selfloops_L) (ns_U_of s \<union> ns_selfloops_U)"
    using ns_invar_partitionD[OF ns_invarD(3)[OF assms(1)]] .
  show "e \<notin> ns_tree_edges s"
    using eLU part[unfolded spanning_tree_partition_def] by blast
qed

text \<open>The entering edge is never a self-loop. Its reduced cost equals its plain cost (the potentials
      cancel when @{term \<open>fst e = snd e\<close>}), so an entering edge taken from @{term L} has @{term \<open>\<c> e < 0\<close>}
      and one from @{term U} has @{term \<open>\<c> e > 0\<close>}; either way the self-loop classification invariant
      @{const ns_invar_selfloop} would force the opposite membership, a contradiction. This replaces the
      former \<open>no_self_loop\<close> axiom at every entering-edge use.\<close>

lemma entering_not_selfloop:
  assumes inv: "ns_invar s" and sel: "ns_select s = Some (e, in_U, \<gamma>, sel')"
  shows "fst e \<noteq> snd e"
proof -
  have prec: "selection_precond (edge_sel s) (potentials s) (edge_state s)"
    using ns_invar_implD[OF ns_invarD(1)[OF inv]] ns_invar_pot_fitsD[OF ns_invarD(5)[OF inv]]
    by (simp add: selection_precond_def potential_fits_spanning_tree_partition_def)
  have seleq: "sel_select (edge_sel s) (potentials s) (edge_state s) = Some (e, in_U, \<gamma>, sel')"
    using sel by (simp add: ns_select_def)
  have ent: "entering_edge (potentials s) (edge_state s) e in_U" using sel_select_SomeD(4)[OF prec seleq] .
  thus "fst e \<noteq> snd e" by (auto simp: entering_edge_def split: if_splits)
qed

text \<open>A tree edge is never a self-loop: the spanning-tree partition keeps the tree edges a
      @{const graph_abs}, whose @{const dblton_graph} requirement rules out the singleton
      @{term \<open>{fst e, snd e}\<close>} of a self-loop.\<close>

lemma tree_edge_not_selfloop:
  assumes inv: "ns_invar s" and et: "e \<in> ns_tree_edges s"
  shows "fst e \<noteq> snd e"
proof
  assume sl: "fst e = snd e"
  have ga: "graph_abs ((\<lambda>e. {fst e, snd e}) ` ns_tree_edges s)"
    using spanning_tree_partitionD(6)[OF ns_invar_partitionD[OF ns_invarD(3)[OF inv]]] .
  have dbl: "dblton_graph ((\<lambda>e. {fst e, snd e}) ` ns_tree_edges s)" using graph_abs.dblton_E[OF ga] .
  have "{fst e} \<in> (\<lambda>e. {fst e, snd e}) ` ns_tree_edges s"
    by (rule image_eqI[OF _ et]) (simp add: sl)
  thus False using singleton_not_dblton[OF dbl] by blast
qed

subsection \<open>Auxiliary bundles (\S{}4)\<close>

text \<open>Throughout this subsection @{term s} is the pre-step state with @{term \<open>ns_invar s\<close>}, the
      selector has fired (@{term \<open>ns_select s = Some (e, in_U, \<gamma>, sel')\<close>}), and @{term p1}, @{term p2}
      are the two tree paths @{term \<open>get_path_pair (spanning_tree s) (fst e) (snd e) = (p1, p2)\<close>}.\<close>

text \<open>\<^bold>\<open>\S{}4.1 Path/array alignment\<close> --- the linchpin. The \<open>get_path_pair\<close> specification names an
      apex @{term a} and a shared tail @{term p3}; the consequence used downstream is that consecutive
      path vertices are parent-linked (@{const par_vx} of one is the next), that the two paths are
      disjoint, and that @{const par_edge} is injective on their union (H1). The degenerate case
      @{term \<open>p1 = []\<close>} / @{term \<open>p2 = []\<close>} (one endpoint of @{term e} is an ancestor of the other) is
      admitted.\<close>

lemma get_path_pair_align:
  assumes inv: "ns_invar s"
    and sel: "ns_select s = Some (e, in_U, \<gamma>, sel')"
    and pp:  "get_path_pair (spanning_tree s) (fst e) (snd e) = (p1, p2)"
  shows "\<exists> a p3.
           walk_betw (abstract_arborescense (spanning_tree s)) (fst e) (p1 @ a # p3) r \<and>
           walk_betw (abstract_arborescense (spanning_tree s)) (snd e) (p2 @ a # p3) r \<and>
           distinct (p1 @ a # p3) \<and> distinct (p2 @ a # p3) \<and> set p1 \<inter> set p2 = {}"
    and "\<And>i. Suc i < length p1 \<Longrightarrow> par_vx s (p1 ! i) = p1 ! Suc i"
    and "\<And>i. Suc i < length p2 \<Longrightarrow> par_vx s (p2 ! i) = p2 ! Suc i"
    and "set p1 \<inter> set p2 = {}"
    and "inj_on (par_edge s) (set p1 \<union> set p2)"
proof -
  let ?absT = "abstract_arborescense (spanning_tree s)"
  have eE: "e \<in> \<E>" using ns_select_SomeD(2)[OF inv sel] .
  have arb: "arborescense_invar (spanning_tree s)"
    using ns_invar_implD(7)[OF ns_invarD(1)[OF inv]] .
  have neq: "fst e \<noteq> snd e" using entering_not_selfloop[OF inv sel] .
  have fV: "fst e \<in> \<V>" using fst_E_V[OF eE] .
  have sV: "snd e \<in> \<V>" using snd_E_V[OF eE] .
  have rV: "r \<in> \<V>" using general(1) .
  obtain a p3 where
    w1: "walk_betw ?absT (fst e) (p1 @ a # p3) r" and
    w2: "walk_betw ?absT (snd e) (p2 @ a # p3) r" and
    d1: "distinct (p1 @ a # p3)" and d2: "distinct (p2 @ a # p3)" and
    disj: "set p1 \<inter> set p2 = {}"
    using get_path_pair(1)[OF arb pp neq fV sV] by blast
  have p1V: "set p1 \<subseteq> \<V> - {r}" and p2V: "set p2 \<subseteq> \<V> - {r}"
    using get_path_pair_verts[OF inv eE entering_not_selfloop[OF inv sel] pp] by auto
  have link: "\<And>q u i. distinct (q @ a # p3) \<Longrightarrow> set q \<subseteq> \<V> - {r} \<Longrightarrow>
                walk_betw ?absT u (q @ a # p3) r \<Longrightarrow> Suc i < length q \<Longrightarrow>
                par_vx s (q ! i) = q ! Suc i"
  proof -
    fix q u i
    assume dq: "distinct (q @ a # p3)" and qV: "set q \<subseteq> \<V> - {r}"
       and wq: "walk_betw ?absT u (q @ a # p3) r" and iL: "Suc i < length q"
    have iq: "i < length q" using iL by simp
    let ?x = "q ! i"
    let ?su = "drop (Suc i) q @ a # p3"
    have decomp: "q @ a # p3 = take i q @ [?x] @ ?su"
      using id_take_nth_drop[OF iq] by simp
    have wsuff: "walk_betw ?absT ?x (?x # ?su) r"
      using wq[unfolded decomp] by (rule walk_suff)
    have dsu: "distinct (?x # ?su)"
      using dq[unfolded decomp] by simp
    have xVr: "?x \<in> \<V> - {r}" using qV iq nth_mem by (metis subsetD)
    have xV: "?x \<in> \<V>" using xVr by simp
    obtain q'' where q'': "distinct (?x # par_vx s ?x # q'')
                        \<and> walk_betw ?absT ?x (?x # par_vx s ?x # q'') r"
      using par_vx_walk_succ[OF inv xVr] by blast
    have uniq: "\<exists>!p. walk_betw ?absT ?x p r \<and> distinct p"
      using general(3)[OF arb rV xV] .
    have eq: "?x # ?su = ?x # par_vx s ?x # q''"
      using uniq wsuff dsu q'' by (metis (mono_tags, lifting))
    hence "?su = par_vx s ?x # q''" by simp
    hence hsu: "hd ?su = par_vx s ?x" by simp
    have "hd ?su = q ! Suc i"
      using iL hd_drop_conv_nth[of "Suc i" q] by (simp add: hd_append)
    thus "par_vx s (q ! i) = q ! Suc i" using hsu by simp
  qed
  show "\<exists>a p3. walk_betw ?absT (fst e) (p1 @ a # p3) r \<and> walk_betw ?absT (snd e) (p2 @ a # p3) r \<and>
          distinct (p1 @ a # p3) \<and> distinct (p2 @ a # p3) \<and> set p1 \<inter> set p2 = {}"
    using w1 w2 d1 d2 disj by blast
  show "\<And>i. Suc i < length p1 \<Longrightarrow> par_vx s (p1 ! i) = p1 ! Suc i"
    using link[OF d1 p1V w1] by blast
  show "\<And>i. Suc i < length p2 \<Longrightarrow> par_vx s (p2 ! i) = p2 ! Suc i"
    using link[OF d2 p2V w2] by blast
  show "set p1 \<inter> set p2 = {}" by (rule disj)
  show "inj_on (par_edge s) (set p1 \<union> set p2)"
  proof (rule inj_onI)
    fix x y assume xin: "x \<in> set p1 \<union> set p2" and yin: "y \<in> set p1 \<union> set p2"
       and eqp: "par_edge s x = par_edge s y"
    have xV: "x \<in> \<V> - {r}" using xin p1V p2V by auto
    have yV: "y \<in> \<V> - {r}" using yin p1V p2V by auto
    show "x = y" using par_edge_inj[OF inv xV yV eqp] .
  qed
qed

text \<open>The general walk-successor fact used through \S{}4.1 and again in \S{}4.3/\S{}4.5: on \<^emph>\<open>any\<close> distinct walk
      to the root, the successor of a non-root vertex is its @{const par_vx}. Applied to a spine
      @{term \<open>P @ a # p3\<close>} it gives both the interior links (successor inside @{term P}) and the apex link
      @{term \<open>par_vx s (last P) = a\<close>}. Proof: the suffix from position @{term i} is, by @{thm general(3)},
      \<^emph>\<open>the\<close> unique distinct walk to @{term r}, so its second vertex is @{term \<open>par_vx s (W ! i)\<close>} (H2).\<close>

lemma walk_succ_is_par_vx:
  assumes inv: "ns_invar s"
    and w: "walk_betw (abstract_arborescense (spanning_tree s)) u W r"
    and d: "distinct W"
    and iL: "Suc i < length W"
    and vV: "W ! i \<in> \<V> - {r}"
  shows "par_vx s (W ! i) = W ! Suc i"
proof -
  let ?absT = "abstract_arborescense (spanning_tree s)"
  have arb: "arborescense_invar (spanning_tree s)"
    using ns_invar_implD(7)[OF ns_invarD(1)[OF inv]] .
  have rV: "r \<in> \<V>" using general(1) .
  have iq: "i < length W" using iL by simp
  let ?x = "W ! i"
  let ?su = "drop (Suc i) W"
  have decomp: "W = take i W @ [?x] @ ?su"
    using id_take_nth_drop[OF iq] by simp
  have wdec: "walk_betw ?absT u (take i W @ [?x] @ ?su) r"
    using w by (simp only: decomp[symmetric])
  have wsuff: "walk_betw ?absT ?x (?x # ?su) r"
    using wdec by (rule walk_suff)
  have dlong: "distinct (take i W @ [?x] @ ?su)"
    using d by (simp only: decomp[symmetric])
  have dsu: "distinct (?x # ?su)"
    using dlong by simp
  have xV: "?x \<in> \<V>" using vV by simp
  obtain q'' where q'': "distinct (?x # par_vx s ?x # q'')
                      \<and> walk_betw ?absT ?x (?x # par_vx s ?x # q'') r"
    using par_vx_walk_succ[OF inv vV] by blast
  have uniq: "\<exists>!p. walk_betw ?absT ?x p r \<and> distinct p"
    using general(3)[OF arb rV xV] .
  have eq: "?x # ?su = ?x # par_vx s ?x # q''"
    using uniq wsuff dsu q'' by (metis (mono_tags, lifting))
  hence "?su = par_vx s ?x # q''" by simp
  hence hsu: "hd ?su = par_vx s ?x" by simp
  have "hd ?su = W ! Suc i"
    using hd_drop_conv_nth[OF iL] by simp
  thus "par_vx s (W ! i) = W ! Suc i" using hsu by simp
qed

text \<open>\<^bold>\<open>\S{}4.6 @{const bottleneck}-return facts\<close> for the pivot branch: the leaving child @{term v} lies on
      the spine @{term P} it was scanned from, is a non-root vertex, its parent edge is the leaving
      tree edge @{term e0}, and the entering edge @{term e} is not yet a tree edge. The positivity fact
      from \S{}0 (no up-side residual is @{term 0}, so an up-side leaving edge forces @{term \<open>\<delta> > 0\<close>}) is
      bundled here too.\<close>

lemma mininf_snd_of_neq_fst: "mininf (x::'n) y \<noteq> x \<Longrightarrow> mininf x y = y"
  by (cases "x = - 1"; cases "y = - 1") (auto simp: mininf_def min_def)

lemma mininf_snd_attains:
  "mininf (x::'n) y \<noteq> - 1 \<Longrightarrow> \<not> (x \<noteq> - 1 \<and> x = mininf x y) \<Longrightarrow> y = mininf x y \<and> y \<noteq> - 1"
  by (cases "x = - 1"; cases "y = - 1") (auto simp: mininf_def min_def)

lemma bottleneck_pivot_facts:
  assumes inv: "ns_invar s"
    and sel: "ns_select s = Some (e, in_U, \<gamma>, sel')"
    and pp:  "get_path_pair (spanning_tree s) (fst e) (snd e) = (p1, p2)"
    and bn:  "bottleneck s e in_U p1 p2 = (\<delta>, False, v, e0fwd, up_side)"
  shows "v \<in> set (if in_U = up_side then p1 else p2)"
    and "v \<in> \<V> - {r}"
    and "par_edge s v \<in> ns_tree_edges s"
    and "e \<notin> ns_tree_edges s"
    and "\<delta> \<ge> 0"
    and "up_side \<Longrightarrow> \<delta> > 0"
proof -
  have eE: "e \<in> \<E>" using ns_select_SomeD(2)[OF inv sel] .
  have p1V: "set p1 \<subseteq> \<V> - {r}" and p2V: "set p2 \<subseteq> \<V> - {r}"
    using get_path_pair_verts[OF inv eE entering_not_selfloop[OF inv sel] pp] by auto
  have upV: "set (if in_U then p1 else p2) \<subseteq> \<V> - {r}" using p1V p2V by auto
  have dnV: "set (if in_U then p2 else p1) \<subseteq> \<V> - {r}" using p1V p2V by auto
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
  have dne: "?d \<noteq> - 1"
  proof
    assume "?d = - 1"
    hence "bottleneck s e in_U p1 p2 = (- 1, True, r, False, False)" using bform by simp
    thus False using bn by simp
  qed
  have dd: "\<delta> = ?d" using bn bform dne by (auto split: if_splits)
  have reS: "0 \<le> ?re \<or> ?re = - 1"
    using res_bwd_nonneg[OF inv eE] res_fwd_sign[OF inv eE] by auto
  have muS: "0 \<le> mu \<or> mu = - 1" using scan_up_val_sign[OF inv upV su] .
  have mdS: "0 \<le> md \<or> md = - 1" using scan_down_val_sign[OF inv dnV sd] .
  have dS: "0 \<le> ?d" using mininf_sign[OF reS mininf_sign[OF muS mdS]] dne by auto
  have arm: "(up_side \<and> mu \<noteq> - 1 \<and> mu = ?d \<and> vu = v) \<or> (\<not> up_side \<and> md = ?d \<and> md \<noteq> - 1 \<and> vd = v)"
  proof (cases "mu \<noteq> - 1 \<and> mu = ?d")
    case True
    have f1: "bottleneck s e in_U p1 p2 = (?d, False, vu, par_up s vu, True)"
      using bform True dne by simp
    have "up_side \<and> vu = v" using bn f1 by (metis Pair_inject)
    thus ?thesis using True by auto
  next
    case notup: False
    have rene: "?re \<noteq> ?d"
    proof
      assume "?re = ?d"
      hence "bottleneck s e in_U p1 p2 = (?d, True, r, False, False)"
        using bform notup dne by simp
      thus False using bn by simp
    qed
    have f2: "bottleneck s e in_U p1 p2 = (?d, False, vd, \<not> par_up s vd, False)"
      using bform notup rene dne by simp
    have vdv_nup: "vd = v \<and> \<not> up_side" using bn f2 by (metis Pair_inject)
    have dY: "?d = mininf mu md" using mininf_snd_of_neq_fst[of ?re "mininf mu md"] rene by simp
    have mdd: "md = ?d \<and> md \<noteq> - 1"
      using mininf_snd_attains[of mu md] dY dne notup by simp
    thus ?thesis using vdv_nup by auto
  qed
  show g1: "v \<in> set (if in_U = up_side then p1 else p2)"
  proof (cases up_side)
    case True
    hence A: "mu \<noteq> - 1 \<and> vu = v" using arm by auto
    hence "scan_up s (if in_U then p1 else p2) = (mu, v)" using su by simp
    hence "v \<in> set (if in_U then p1 else p2)" using scan_up_snd_mem A by blast
    thus ?thesis using True by (auto split: if_splits)
  next
    case False
    hence A: "md \<noteq> - 1 \<and> vd = v" using arm by auto
    hence "scan_down s (if in_U then p2 else p1) = (md, v)" using sd by simp
    hence "v \<in> set (if in_U then p2 else p1)" using scan_down_snd_mem A by blast
    thus ?thesis using False by (auto split: if_splits)
  qed
  show g2: "v \<in> \<V> - {r}" using g1 p1V p2V by (auto split: if_splits)
  show "par_edge s v \<in> ns_tree_edges s" using g2 by (auto simp: par_edge_def)
  show "e \<notin> ns_tree_edges s" using ns_select_SomeD(3)[OF inv sel] .
  show "0 \<le> \<delta>" using dd dS by simp
  { assume us: "up_side"
    from arm us have A: "mu \<noteq> - 1 \<and> mu = ?d \<and> vu = v" by auto
    hence sq: "scan_up s (if in_U then p1 else p2) = (mu, v)" using su by simp
    have "res_up s v = mu" using scan_up_val_at[OF sq] A by simp
    moreover have "0 < res_up s v \<or> res_up s v = - 1" using res_up_pos[OF inv g2] .
    ultimately have "0 < \<delta>" using A dd by auto }
  thus "up_side \<Longrightarrow> 0 < \<delta>" by blast
qed

text \<open>\<^bold>\<open>\S{}4.2 Conservation (circulation)\<close>. For @{term \<open>\<delta> > 0\<close>} the flow produced by
      @{const augment_flow} is a @{term \<delta>}-scaled unit circulation around the fundamental circuit: it
      leaves every vertex balance unchanged, hence stays a @{term b}-flow, and every circuit edge is
      pushed by at most its own residual so the capacity bounds are kept. This is the whole of
      @{const ns_invar_bflow} for both recursive branches.\<close>

definition "ns_flow_cost s = (\<C> (ns_flow_of s))"

text \<open>Conservation infrastructure: a single flow update shifts the excess of its two endpoints by
      opposite signed amounts, and folding such updates accumulates those shifts additively (no
      arc-distinctness needed for the excess, since each step is additive).\<close>

lemma sum_fun_upd_delta:
  assumes "finite S"
  shows "sum (g(a := g a + (\<delta>::real))) S = sum g S + (if a \<in> S then \<delta> else 0)"
proof (cases "a \<in> S")
  case True
  have "sum (g(a := g a + \<delta>)) S = (g a + \<delta>) + sum (g(a := g a + \<delta>)) (S - {a})"
    by (simp add: sum.remove[OF assms True])
  moreover have "sum (g(a := g a + \<delta>)) (S - {a}) = sum g (S - {a})"
    by (intro sum.cong) auto
  moreover have "sum g (S - {a}) = sum g S - g a"
    by (simp add: sum.remove[OF assms True])
  ultimately show ?thesis using True by simp
next
  case False
  hence "sum (g(a := g a + \<delta>)) S = sum g S" by (intro sum.cong) (auto simp: False)
  thus ?thesis using False by simp
qed

lemma flow_upd_ex:
  assumes fi: "flow_invar f" and ae: "a \<in> \<E>"
  shows "ex (h \<circ> flow_lookup (flow_upd f a (flow_lookup f a + c))) v
           = ex (h \<circ> flow_lookup f) v + h c * ((if snd a = v then 1 else 0) - (if fst a = v then 1 else 0))"
proof -
  let ?f' = "\<lambda>e. h (flow_lookup (flow_upd f a (flow_lookup f a + c)) e)"
  have fl'_eq: "?f' = (\<lambda>e. h (flow_lookup f e))(a := h (flow_lookup f a) + h c)"
    by (rule ext) (simp add: flow_arr.fixed_univ_map_upd[OF fi ae] h_add)
  have din: "(\<Sum>ee\<in>\<delta>\<^sup>- v. ?f' ee) = (\<Sum>ee\<in>\<delta>\<^sup>- v. h (flow_lookup f ee)) + (if a \<in> \<delta>\<^sup>- v then h c else 0)"
    unfolding fl'_eq by (rule sum_fun_upd_delta[OF delta_minus_finite])
  have dout: "(\<Sum>ee\<in>\<delta>\<^sup>+ v. ?f' ee) = (\<Sum>ee\<in>\<delta>\<^sup>+ v. h (flow_lookup f ee)) + (if a \<in> \<delta>\<^sup>+ v then h c else 0)"
    unfolding fl'_eq by (rule sum_fun_upd_delta[OF delta_plus_finite])
  have inm: "(a \<in> \<delta>\<^sup>- v) = (snd a = v)" using ae by (auto simp: delta_minus_def)
  have inp: "(a \<in> \<delta>\<^sup>+ v) = (fst a = v)" using ae by (auto simp: delta_plus_def)
  have "ex (h \<circ> flow_lookup (flow_upd f a (flow_lookup f a + c))) v
          = (\<Sum>ee\<in>\<delta>\<^sup>- v. ?f' ee) - (\<Sum>ee\<in>\<delta>\<^sup>+ v. ?f' ee)"
    by (simp only: ex_def comp_def)
  also have "... = ((\<Sum>ee\<in>\<delta>\<^sup>- v. h (flow_lookup f ee)) + (if a \<in> \<delta>\<^sup>- v then h c else 0))
                 - ((\<Sum>ee\<in>\<delta>\<^sup>+ v. h (flow_lookup f ee)) + (if a \<in> \<delta>\<^sup>+ v then h c else 0))"
    by (simp only: din dout)
  also have "... = ex (h \<circ> flow_lookup f) v
                     + h c * ((if snd a = v then 1 else 0) - (if fst a = v then 1 else 0))"
    by (simp add: ex_def comp_def inm inp algebra_simps split: if_split)
  finally show ?thesis .
qed

lemma fold_flow_upd_invar:
  "flow_invar f0 \<Longrightarrow> (\<forall>w\<in>set xs. par_edge s w \<in> \<E>) \<Longrightarrow> flow_invar (fold (\<lambda>v f. flow_upd f (par_edge s v) (flow_lookup f (par_edge s v) + g v)) xs f0)"
proof (induction xs arbitrary: f0)
  case Nil thus ?case by simp
next
  case (Cons w xs)
  have wE: "par_edge s w \<in> \<E>" using Cons.prems(2) by simp
  have restE: "\<forall>w'\<in>set xs. par_edge s w' \<in> \<E>" using Cons.prems(2) by simp
  have "flow_invar (flow_upd f0 (par_edge s w) (flow_lookup f0 (par_edge s w) + g w))"
    using Cons.prems(1) wE by (rule flow_arr.fixed_univ_map_upd_invar)
  thus ?case using Cons.IH[OF _ restE] by simp
qed

lemma fold_flow_upd_ex:
  "flow_invar f0 \<Longrightarrow> (\<forall>w\<in>set xs. par_edge s w \<in> \<E>) \<Longrightarrow>
   ex (h \<circ> flow_lookup (fold (\<lambda>v f. flow_upd f (par_edge s v) (flow_lookup f (par_edge s v) + g v)) xs f0)) v
     = ex (h \<circ> flow_lookup f0) v
       + (\<Sum>w\<leftarrow>xs. h (g w) * ((if snd (par_edge s w) = v then 1 else 0) - (if fst (par_edge s w) = v then 1 else 0)))"
proof (induction xs arbitrary: f0)
  case Nil thus ?case by simp
next
  case (Cons w xs)
  let ?f1 = "flow_upd f0 (par_edge s w) (flow_lookup f0 (par_edge s w) + g w)"
  have wE: "par_edge s w \<in> \<E>" using Cons.prems(2) by simp
  have fi1: "flow_invar ?f1" using Cons.prems(1) wE by (rule flow_arr.fixed_univ_map_upd_invar)
  have restE: "\<forall>w'\<in>set xs. par_edge s w' \<in> \<E>" using Cons.prems(2) by simp
  have step: "ex (h \<circ> flow_lookup ?f1) v = ex (h \<circ> flow_lookup f0) v
                + h (g w) * ((if snd (par_edge s w) = v then 1 else 0) - (if fst (par_edge s w) = v then 1 else 0))"
    using flow_upd_ex[OF Cons.prems(1) wE] .
  have "ex (h \<circ> flow_lookup (fold (\<lambda>v f. flow_upd f (par_edge s v) (flow_lookup f (par_edge s v) + g v)) (w # xs) f0)) v
      = ex (h \<circ> flow_lookup (fold (\<lambda>v f. flow_upd f (par_edge s v) (flow_lookup f (par_edge s v) + g v)) xs ?f1)) v"
    by simp
  also have "... = ex (h \<circ> flow_lookup ?f1) v
      + (\<Sum>w'\<leftarrow>xs. h (g w') * ((if snd (par_edge s w') = v then 1 else 0) - (if fst (par_edge s w') = v then 1 else 0)))"
    using Cons.IH[OF fi1 restE] .
  also have "... = ex (h \<circ> flow_lookup f0) v
      + (\<Sum>w'\<leftarrow>(w # xs). h (g w') * ((if snd (par_edge s w') = v then 1 else 0) - (if fst (par_edge s w') = v then 1 else 0)))"
    using step by simp
  finally show ?case .
qed

lemma up_contrib:
  assumes inv: "ns_invar s" and wV: "w \<in> \<V> - {r}"
  shows "(if par_up s w then \<delta> else - \<delta>) * ((if snd (par_edge s w) = v then 1 else 0) - (if fst (par_edge s w) = v then 1 else 0))
       = \<delta> * ((if par_vx s w = v then (1::real) else 0) - (if w = v then 1 else 0))"
proof -
  have dir: "if par_up s w then fst (par_edge s w) = w else snd (par_edge s w) = w"
    using ns_invar_tree_dirD[OF ns_invarD(7)[OF inv] wV] .
  show ?thesis using dir by (cases "par_up s w") (auto simp: par_vx_def)
qed

lemma down_contrib:
  assumes inv: "ns_invar s" and wV: "w \<in> \<V> - {r}"
  shows "(if par_up s w then - \<delta> else \<delta>) * ((if snd (par_edge s w) = v then 1 else 0) - (if fst (par_edge s w) = v then 1 else 0))
       = \<delta> * ((if w = v then (1::real) else 0) - (if par_vx s w = v then 1 else 0))"
proof -
  have dir: "if par_up s w then fst (par_edge s w) = w else snd (par_edge s w) = w"
    using ns_invar_tree_dirD[OF ns_invarD(7)[OF inv] wV] .
  show ?thesis using dir by (cases "par_up s w") (auto simp: par_vx_def)
qed

lemma telescope_succ:
  assumes succ: "\<And>i. Suc i < length ys \<Longrightarrow> f (ys ! i) = ys ! Suc i" and ne: "ys \<noteq> []"
  shows "(\<Sum>w\<leftarrow>butlast ys. (if f w = v then (1::real) else 0) - (if w = v then 1 else 0))
       = (if last ys = v then 1 else 0) - (if hd ys = v then 1 else 0)"
proof -
  let ?n = "length ys - 1"
  let ?g = "\<lambda>i. if ys ! i = v then (1::real) else 0"
  have lb: "length (butlast ys) = ?n" by simp
  have "(\<Sum>w\<leftarrow>butlast ys. (if f w = v then (1::real) else 0) - (if w = v then 1 else 0))
      = (\<Sum>i<?n. (if f (butlast ys ! i) = v then (1::real) else 0) - (if butlast ys ! i = v then 1 else 0))"
    by (simp add: sum_list_sum_nth lb atLeast0LessThan)
  also have "... = (\<Sum>i<?n. ?g (Suc i) - ?g i)"
  proof (rule sum.cong)
    fix i assume "i \<in> {..<?n}"
    hence iL: "i < ?n" by simp
    hence bi: "butlast ys ! i = ys ! i" by (simp add: nth_butlast)
    have "Suc i < length ys" using iL by simp
    hence "f (ys ! i) = ys ! Suc i" using succ by simp
    thus "(if f (butlast ys ! i) = v then (1::real) else 0) - (if butlast ys ! i = v then 1 else 0)
          = ?g (Suc i) - ?g i" using bi by simp
  qed simp
  also have "... = ?g ?n - ?g 0" by (rule sum_lessThan_telescope)
  also have "... = (if last ys = v then 1 else 0) - (if hd ys = v then 1 else 0)"
    using ne by (simp add: last_conv_nth hd_conv_nth)
  finally show ?thesis .
qed

lemma path_telescope:
  assumes inv: "ns_invar s"
    and w: "walk_betw (abstract_arborescense (spanning_tree s)) u (P @ a # p3) r"
    and d: "distinct (P @ a # p3)"
    and PV: "set P \<subseteq> \<V> - {r}"
  shows "(\<Sum>w\<leftarrow>P. (if par_vx s w = v then (1::real) else 0) - (if w = v then 1 else 0))
       = (if a = v then 1 else 0) - (if u = v then 1 else 0)"
proof -
  let ?ys = "P @ [a]"
  have ne: "?ys \<noteq> []" by simp
  have succ: "\<And>i. Suc i < length ?ys \<Longrightarrow> par_vx s (?ys ! i) = ?ys ! Suc i"
  proof -
    fix i assume iL: "Suc i < length ?ys"
    have iP: "i < length P" using iL by simp
    have SiW: "Suc i < length (P @ a # p3)" using iL by simp
    have wi: "?ys ! i = (P @ a # p3) ! i" using iP by (simp add: nth_append)
    have wsi: "?ys ! Suc i = (P @ a # p3) ! Suc i" using iL by (auto simp: nth_append)
    have Wi: "(P @ a # p3) ! i = P ! i" using iP by (simp add: nth_append)
    have WiV: "(P @ a # p3) ! i \<in> \<V> - {r}" using Wi iP PV nth_mem by (metis subsetD)
    have "par_vx s ((P @ a # p3) ! i) = (P @ a # p3) ! Suc i"
      using walk_succ_is_par_vx[OF inv w d SiW WiV] .
    thus "par_vx s (?ys ! i) = ?ys ! Suc i" using wi wsi by simp
  qed
  have hd_u: "hd ?ys = u"
  proof -
    have "hd (P @ a # p3) = u" using w by (simp add: walk_betw_def)
    thus ?thesis by (cases P) auto
  qed
  have tele: "(\<Sum>w\<leftarrow>butlast ?ys. (if par_vx s w = v then (1::real) else 0) - (if w = v then 1 else 0))
       = (if last ?ys = v then 1 else 0) - (if hd ?ys = v then 1 else 0)"
    using telescope_succ[OF succ ne] .
  show ?thesis using tele hd_u by simp
qed

lemma sum_list_scale: "(\<Sum>x\<leftarrow>xs. (c::real) * f x) = c * (\<Sum>x\<leftarrow>xs. f x)"
  by (induct xs) (auto simp: algebra_simps)

lemma sum_list_uminus: "(\<Sum>x\<leftarrow>xs. - f x) = - (\<Sum>x\<leftarrow>xs. (f x::real))"
  by (induct xs) auto

lemma up_sum:
  assumes inv: "ns_invar s"
    and w: "walk_betw (abstract_arborescense (spanning_tree s)) u (P @ a # p3) r"
    and d: "distinct (P @ a # p3)"
    and PV: "set P \<subseteq> \<V> - {r}"
  shows "(\<Sum>w\<leftarrow>P. (if par_up s w then \<delta> else - \<delta>) * ((if snd (par_edge s w) = v then (1::real) else 0) - (if fst (par_edge s w) = v then 1 else 0)))
       = \<delta> * ((if a = v then 1 else 0) - (if u = v then 1 else 0))"
proof -
  have "(\<Sum>w\<leftarrow>P. (if par_up s w then \<delta> else - \<delta>) * ((if snd (par_edge s w) = v then (1::real) else 0) - (if fst (par_edge s w) = v then 1 else 0)))
      = (\<Sum>w\<leftarrow>P. \<delta> * ((if par_vx s w = v then (1::real) else 0) - (if w = v then 1 else 0)))"
  proof (rule arg_cong[where f=sum_list], rule map_cong[OF refl])
    fix w assume "w \<in> set P"
    hence "w \<in> \<V> - {r}" using PV by auto
    thus "(if par_up s w then \<delta> else - \<delta>) * ((if snd (par_edge s w) = v then (1::real) else 0) - (if fst (par_edge s w) = v then 1 else 0))
          = \<delta> * ((if par_vx s w = v then (1::real) else 0) - (if w = v then 1 else 0))"
      by (rule up_contrib[OF inv])
  qed
  also have "... = \<delta> * (\<Sum>w\<leftarrow>P. (if par_vx s w = v then (1::real) else 0) - (if w = v then 1 else 0))"
    by (rule sum_list_scale)
  also have "... = \<delta> * ((if a = v then 1 else 0) - (if u = v then 1 else 0))"
    using path_telescope[OF inv w d PV] by simp
  finally show ?thesis .
qed

lemma down_sum:
  assumes inv: "ns_invar s"
    and w: "walk_betw (abstract_arborescense (spanning_tree s)) u (P @ a # p3) r"
    and d: "distinct (P @ a # p3)"
    and PV: "set P \<subseteq> \<V> - {r}"
  shows "(\<Sum>w\<leftarrow>P. (if par_up s w then - \<delta> else \<delta>) * ((if snd (par_edge s w) = v then (1::real) else 0) - (if fst (par_edge s w) = v then 1 else 0)))
       = \<delta> * ((if u = v then 1 else 0) - (if a = v then 1 else 0))"
proof -
  have "(\<Sum>w\<leftarrow>P. (if par_up s w then - \<delta> else \<delta>) * ((if snd (par_edge s w) = v then (1::real) else 0) - (if fst (par_edge s w) = v then 1 else 0)))
      = (\<Sum>w\<leftarrow>P. - ((if par_up s w then \<delta> else - \<delta>) * ((if snd (par_edge s w) = v then (1::real) else 0) - (if fst (par_edge s w) = v then 1 else 0))))"
    by (rule arg_cong[where f=sum_list], rule map_cong[OF refl]) (auto simp: algebra_simps)
  also have "... = - (\<Sum>w\<leftarrow>P. (if par_up s w then \<delta> else - \<delta>) * ((if snd (par_edge s w) = v then (1::real) else 0) - (if fst (par_edge s w) = v then 1 else 0)))"
    by (rule sum_list_uminus)
  also have "... = - (\<delta> * ((if a = v then 1 else 0) - (if u = v then 1 else 0)))"
    using up_sum[OF inv w d PV] by simp
  also have "... = \<delta> * ((if u = v then 1 else 0) - (if a = v then 1 else 0))" by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma up_sum_h:
  assumes inv: "ns_invar s"
    and w: "walk_betw (abstract_arborescense (spanning_tree s)) u (P @ a # p3) r"
    and d: "distinct (P @ a # p3)"
    and PV: "set P \<subseteq> \<V> - {r}"
  shows "(\<Sum>w\<leftarrow>P. h (if par_up s w then \<delta> else - \<delta>) * ((if snd (par_edge s w) = v then (1::real) else 0) - (if fst (par_edge s w) = v then 1 else 0)))
       = h \<delta> * ((if a = v then 1 else 0) - (if u = v then 1 else 0))"
proof -
  have "(\<Sum>w\<leftarrow>P. h (if par_up s w then \<delta> else - \<delta>) * ((if snd (par_edge s w) = v then (1::real) else 0) - (if fst (par_edge s w) = v then 1 else 0)))
      = (\<Sum>w\<leftarrow>P. (if par_up s w then h \<delta> else - h \<delta>) * ((if snd (par_edge s w) = v then (1::real) else 0) - (if fst (par_edge s w) = v then 1 else 0)))"
    by (rule arg_cong[where f=sum_list], rule map_cong[OF refl]) simp
  also have "... = h \<delta> * ((if a = v then 1 else 0) - (if u = v then 1 else 0))"
    using up_sum[OF inv w d PV] by simp
  finally show ?thesis .
qed

lemma down_sum_h:
  assumes inv: "ns_invar s"
    and w: "walk_betw (abstract_arborescense (spanning_tree s)) u (P @ a # p3) r"
    and d: "distinct (P @ a # p3)"
    and PV: "set P \<subseteq> \<V> - {r}"
  shows "(\<Sum>w\<leftarrow>P. h (if par_up s w then - \<delta> else \<delta>) * ((if snd (par_edge s w) = v then (1::real) else 0) - (if fst (par_edge s w) = v then 1 else 0)))
       = h \<delta> * ((if u = v then 1 else 0) - (if a = v then 1 else 0))"
proof -
  have "(\<Sum>w\<leftarrow>P. h (if par_up s w then - \<delta> else \<delta>) * ((if snd (par_edge s w) = v then (1::real) else 0) - (if fst (par_edge s w) = v then 1 else 0)))
      = (\<Sum>w\<leftarrow>P. (if par_up s w then - h \<delta> else h \<delta>) * ((if snd (par_edge s w) = v then (1::real) else 0) - (if fst (par_edge s w) = v then 1 else 0)))"
    by (rule arg_cong[where f=sum_list], rule map_cong[OF refl]) simp
  also have "... = h \<delta> * ((if u = v then 1 else 0) - (if a = v then 1 else 0))"
    using down_sum[OF inv w d PV] by simp
  finally show ?thesis .
qed

lemma augment_flow_ex:
  assumes inv: "ns_invar s"
    and sel: "ns_select s = Some (e, in_U, \<gamma>, sel')"
    and pp:  "get_path_pair (spanning_tree s) (fst e) (snd e) = (p1, p2)"
  shows "ex (h \<circ> flow_lookup (augment_flow s e in_U \<delta> p1 p2)) v = ex (h \<circ> flow_lookup (current_flow s)) v"
proof (cases "\<delta> \<le> 0")
  case True
  thus ?thesis by (simp add: augment_flow_def)
next
  case False
  have eE: "e \<in> \<E>" using ns_select_SomeD(2)[OF inv sel] .
  have neq: "fst e \<noteq> snd e" using entering_not_selfloop[OF inv sel] .
  have fV: "fst e \<in> \<V>" using fst_E_V[OF eE] .
  have sV: "snd e \<in> \<V>" using snd_E_V[OF eE] .
  have arb: "arborescense_invar (spanning_tree s)" using ns_invar_implD(7)[OF ns_invarD(1)[OF inv]] .
  have fiE: "flow_invar (current_flow s)" using ns_invar_implD(1)[OF ns_invarD(1)[OF inv]] .
  have tree: "ns_invar_tree s" using ns_invarD(7)[OF inv] .
  obtain a p3 where
    w1: "walk_betw (abstract_arborescense (spanning_tree s)) (fst e) (p1 @ a # p3) r" and
    w2: "walk_betw (abstract_arborescense (spanning_tree s)) (snd e) (p2 @ a # p3) r" and
    d1: "distinct (p1 @ a # p3)" and d2: "distinct (p2 @ a # p3)"
    using get_path_pair(1)[OF arb pp neq fV sV] by blast
  have p1V: "set p1 \<subseteq> \<V> - {r}" and p2V: "set p2 \<subseteq> \<V> - {r}"
    using get_path_pair_verts[OF inv eE entering_not_selfloop[OF inv sel] pp] by auto
  have p1E: "\<forall>w\<in>set p1. par_edge s w \<in> \<E>" using p1V ns_invar_tree_edgeD[OF tree] by auto
  have p2E: "\<forall>w\<in>set p2. par_edge s w \<in> \<E>" using p2V ns_invar_tree_edgeD[OF tree] by auto
  let ?ce = "if in_U then - \<delta> else \<delta>"
  let ?f0 = "flow_upd (current_flow s) e (flow_lookup (current_flow s) e + ?ce)"
  let ?up = "if in_U then p1 else p2"
  let ?dn = "if in_U then p2 else p1"
  let ?gup = "\<lambda>w. if par_up s w then \<delta> else - \<delta>"
  let ?gdn = "\<lambda>w. if par_up s w then - \<delta> else \<delta>"
  let ?f1 = "fold (\<lambda>w f. flow_upd f (par_edge s w) (flow_lookup f (par_edge s w) + ?gup w)) ?up ?f0"
  let ?f' = "fold (\<lambda>w f. flow_upd f (par_edge s w) (flow_lookup f (par_edge s w) + ?gdn w)) ?dn ?f1"
  let ?chi = "\<lambda>x. (if snd x = v then (1::real) else 0) - (if fst x = v then 1 else 0)"
  have augeq: "augment_flow s e in_U \<delta> p1 p2 = ?f'"
    using False by (simp add: augment_flow_def Let_def)
  have upE: "\<forall>w\<in>set ?up. par_edge s w \<in> \<E>" using p1E p2E by (cases in_U) auto
  have dnE: "\<forall>w\<in>set ?dn. par_edge s w \<in> \<E>" using p1E p2E by (cases in_U) auto
  have fi0: "flow_invar ?f0" using fiE eE by (rule flow_arr.fixed_univ_map_upd_invar)
  have fi1: "flow_invar ?f1" using fold_flow_upd_invar[OF fi0 upE] .
  have ex1: "ex (h \<circ> flow_lookup ?f') v = ex (h \<circ> flow_lookup ?f1) v + (\<Sum>w\<leftarrow>?dn. h (?gdn w) * ?chi (par_edge s w))"
    using fold_flow_upd_ex[OF fi1 dnE] .
  have ex2: "ex (h \<circ> flow_lookup ?f1) v = ex (h \<circ> flow_lookup ?f0) v + (\<Sum>w\<leftarrow>?up. h (?gup w) * ?chi (par_edge s w))"
    using fold_flow_upd_ex[OF fi0 upE] .
  have ex3: "ex (h \<circ> flow_lookup ?f0) v = ex (h \<circ> flow_lookup (current_flow s)) v + h ?ce * ?chi e"
    using flow_upd_ex[OF fiE eE] .
  have combined: "ex (h \<circ> flow_lookup ?f') v = ex (h \<circ> flow_lookup (current_flow s)) v + h ?ce * ?chi e
        + (\<Sum>w\<leftarrow>?up. h (?gup w) * ?chi (par_edge s w)) + (\<Sum>w\<leftarrow>?dn. h (?gdn w) * ?chi (par_edge s w))"
    using ex1 ex2 ex3 by simp
  show ?thesis
    unfolding augeq
  proof (cases in_U)
    case True
    have su: "(\<Sum>w\<leftarrow>?up. h (?gup w) * ?chi (par_edge s w)) = h \<delta> * ((if a = v then 1 else 0) - (if fst e = v then 1 else 0))"
      using up_sum_h[OF inv w1 d1 p1V] True by simp
    have sd: "(\<Sum>w\<leftarrow>?dn. h (?gdn w) * ?chi (par_edge s w)) = h \<delta> * ((if snd e = v then 1 else 0) - (if a = v then 1 else 0))"
      using down_sum_h[OF inv w2 d2 p2V] True by simp
    show "ex (h \<circ> flow_lookup ?f') v = ex (h \<circ> flow_lookup (current_flow s)) v"
      using combined su sd True by (simp add: algebra_simps)
  next
    case False
    have su: "(\<Sum>w\<leftarrow>?up. h (?gup w) * ?chi (par_edge s w)) = h \<delta> * ((if a = v then 1 else 0) - (if snd e = v then 1 else 0))"
      using up_sum_h[OF inv w2 d2 p2V] False by simp
    have sd: "(\<Sum>w\<leftarrow>?dn. h (?gdn w) * ?chi (par_edge s w)) = h \<delta> * ((if fst e = v then 1 else 0) - (if a = v then 1 else 0))"
      using down_sum_h[OF inv w1 d1 p1V] False by simp
    show "ex (h \<circ> flow_lookup ?f') v = ex (h \<circ> flow_lookup (current_flow s)) v"
      using combined su sd False by (simp add: algebra_simps)
  qed
qed

lemma augment_flow_flow_invar:
  assumes inv: "ns_invar s"
    and sel: "ns_select s = Some (e, in_U, \<gamma>, sel')"
    and pp:  "get_path_pair (spanning_tree s) (fst e) (snd e) = (p1, p2)"
  shows "flow_invar (augment_flow s e in_U \<delta> p1 p2)"
proof (cases "\<delta> \<le> 0")
  case True
  thus ?thesis using ns_invar_implD(1)[OF ns_invarD(1)[OF inv]] by (simp add: augment_flow_def)
next
  case False
  have eE: "e \<in> \<E>" using ns_select_SomeD(2)[OF inv sel] .
  have fiE: "flow_invar (current_flow s)" using ns_invar_implD(1)[OF ns_invarD(1)[OF inv]] .
  have tree: "ns_invar_tree s" using ns_invarD(7)[OF inv] .
  have p1V: "set p1 \<subseteq> \<V> - {r}" and p2V: "set p2 \<subseteq> \<V> - {r}"
    using get_path_pair_verts[OF inv eE entering_not_selfloop[OF inv sel] pp] by auto
  have upE: "\<forall>w\<in>set (if in_U then p1 else p2). par_edge s w \<in> \<E>"
    using p1V p2V ns_invar_tree_edgeD[OF tree] by (cases in_U) auto
  have dnE: "\<forall>w\<in>set (if in_U then p2 else p1). par_edge s w \<in> \<E>"
    using p1V p2V ns_invar_tree_edgeD[OF tree] by (cases in_U) auto
  let ?f0 = "flow_upd (current_flow s) e (flow_lookup (current_flow s) e + (if in_U then - \<delta> else \<delta>))"
  let ?f1 = "fold (\<lambda>w f. flow_upd f (par_edge s w) (flow_lookup f (par_edge s w) + (if par_up s w then \<delta> else - \<delta>))) (if in_U then p1 else p2) ?f0"
  have fi0: "flow_invar ?f0" using fiE eE by (rule flow_arr.fixed_univ_map_upd_invar)
  have fi1: "flow_invar ?f1" using fold_flow_upd_invar[OF fi0 upE] .
  have "flow_invar (fold (\<lambda>w f. flow_upd f (par_edge s w) (flow_lookup f (par_edge s w) + (if par_up s w then - \<delta> else \<delta>))) (if in_U then p2 else p1) ?f1)"
    using fold_flow_upd_invar[OF fi1 dnE] .
  thus ?thesis using False by (simp add: augment_flow_def Let_def)
qed

text \<open>Capacity infrastructure: the exact per-edge value after the fold (accumulation form, no
      distinctness), specialised --- via @{const par_edge} injectivity --- to ``touched once'' and
      ``untouched''.\<close>

lemma fold_flow_upd_lookup:
  "flow_invar f0 \<Longrightarrow> (\<forall>w\<in>set xs. par_edge s w \<in> \<E>) \<Longrightarrow>
   flow_lookup (fold (\<lambda>v f. flow_upd f (par_edge s v) (flow_lookup f (par_edge s v) + g v)) xs f0) a
     = flow_lookup f0 a + (\<Sum>w\<leftarrow>xs. if par_edge s w = a then g w else 0)"
proof (induction xs arbitrary: f0)
  case Nil thus ?case by simp
next
  case (Cons w xs)
  have wE: "par_edge s w \<in> \<E>" using Cons.prems(2) by simp
  have restE: "\<forall>w'\<in>set xs. par_edge s w' \<in> \<E>" using Cons.prems(2) by simp
  let ?f1 = "flow_upd f0 (par_edge s w) (flow_lookup f0 (par_edge s w) + g w)"
  have fi1: "flow_invar ?f1" using Cons.prems(1) wE by (rule flow_arr.fixed_univ_map_upd_invar)
  have l1: "flow_lookup ?f1 a = flow_lookup f0 a + (if par_edge s w = a then g w else 0)"
    using flow_arr.fixed_univ_map_upd[OF Cons.prems(1) wE] by (auto simp: fun_upd_def)
  have "flow_lookup (fold (\<lambda>v f. flow_upd f (par_edge s v) (flow_lookup f (par_edge s v) + g v)) (w # xs) f0) a
      = flow_lookup (fold (\<lambda>v f. flow_upd f (par_edge s v) (flow_lookup f (par_edge s v) + g v)) xs ?f1) a"
    by simp
  also have "... = flow_lookup ?f1 a + (\<Sum>w'\<leftarrow>xs. if par_edge s w' = a then g w' else 0)"
    using Cons.IH[OF fi1 restE] .
  also have "... = flow_lookup f0 a + (\<Sum>w'\<leftarrow>(w # xs). if par_edge s w' = a then g w' else 0)"
    using l1 by simp
  finally show ?case .
qed

lemma sum_list_if_eq_notin:
  "w0 \<notin> set xs \<Longrightarrow> (\<Sum>w\<leftarrow>xs. if w = w0 then g w else 0) = 0"
  by (induct xs) auto

lemma sum_list_if_eq_distinct:
  assumes "distinct xs" "w0 \<in> set xs"
  shows "(\<Sum>w\<leftarrow>xs. if w = w0 then g w else 0) = g w0"
  using assms
proof (induct xs)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases "x = w0")
    case True
    have "w0 \<notin> set xs" using Cons.prems(1) True by simp
    thus ?thesis using True by (simp add: sum_list_if_eq_notin)
  next
    case False
    hence "w0 \<in> set xs" using Cons.prems(2) by simp
    thus ?thesis using Cons.hyps Cons.prems False by simp
  qed
qed

lemma fold_lookup_notin:
  assumes fi: "flow_invar f0" and rE: "\<forall>w\<in>set xs. par_edge s w \<in> \<E>" and ni: "a \<notin> par_edge s ` set xs"
  shows "flow_lookup (fold (\<lambda>v f. flow_upd f (par_edge s v) (flow_lookup f (par_edge s v) + g v)) xs f0) a
       = flow_lookup f0 a"
proof -
  have z: "(\<Sum>w\<leftarrow>xs. if par_edge s w = a then g w else 0) = 0"
  proof -
    have "(\<Sum>w\<leftarrow>xs. if par_edge s w = a then g w else 0) = (\<Sum>w\<leftarrow>xs. 0)"
      by (rule arg_cong[where f=sum_list], rule map_cong[OF refl]) (use ni in auto)
    thus ?thesis by simp
  qed
  have "flow_lookup (fold (\<lambda>v f. flow_upd f (par_edge s v) (flow_lookup f (par_edge s v) + g v)) xs f0) a
      = flow_lookup f0 a + (\<Sum>w\<leftarrow>xs. if par_edge s w = a then g w else 0)"
    by (rule fold_flow_upd_lookup[OF fi rE])
  thus ?thesis using z by simp
qed

lemma fold_lookup_at:
  assumes fi: "flow_invar f0" and rE: "\<forall>w\<in>set xs. par_edge s w \<in> \<E>" and dist: "distinct xs"
    and inj: "inj_on (par_edge s) (set xs)" and w0: "w0 \<in> set xs"
  shows "flow_lookup (fold (\<lambda>v f. flow_upd f (par_edge s v) (flow_lookup f (par_edge s v) + g v)) xs f0) (par_edge s w0)
       = flow_lookup f0 (par_edge s w0) + g w0"
proof -
  have s: "(\<Sum>w\<leftarrow>xs. if par_edge s w = par_edge s w0 then g w else 0) = g w0"
  proof -
    have "(\<Sum>w\<leftarrow>xs. if par_edge s w = par_edge s w0 then g w else 0) = (\<Sum>w\<leftarrow>xs. if w = w0 then g w else 0)"
      by (rule arg_cong[where f=sum_list], rule map_cong[OF refl]) (use w0 in \<open>auto dest: inj_onD[OF inj]\<close>)
    also have "... = g w0" using sum_list_if_eq_distinct[OF dist w0] .
    finally show ?thesis .
  qed
  have "flow_lookup (fold (\<lambda>v f. flow_upd f (par_edge s v) (flow_lookup f (par_edge s v) + g v)) xs f0) (par_edge s w0)
      = flow_lookup f0 (par_edge s w0) + (\<Sum>w\<leftarrow>xs. if par_edge s w = par_edge s w0 then g w else 0)"
    by (rule fold_flow_upd_lookup[OF fi rE])
  thus ?thesis using s by simp
qed

text \<open>Bounds on the minimum-under-infinity and the scan minimum: the scanned value is the infinity
      sentinel or is below every finite residual on the path.\<close>

lemma mininf_le1: "x \<noteq> - 1 \<Longrightarrow> mininf x y \<le> x"
  by (auto simp: mininf_def)

lemma mininf_le2: "y \<noteq> - 1 \<Longrightarrow> mininf x y \<le> y"
  by (auto simp: mininf_def)

lemma mininf_nonneg: "0 \<le> x \<Longrightarrow> (0 \<le> y \<or> y = - 1) \<Longrightarrow> 0 \<le> mininf x y"
  by (auto simp: mininf_def)

lemma mininf_nonneg2: "(0 \<le> x \<or> x = - 1) \<Longrightarrow> 0 \<le> y \<Longrightarrow> 0 \<le> mininf x y"
  by (auto simp: mininf_def)

lemma scan_up_min:
  "scan_up s p = (m, best) \<Longrightarrow> w \<in> set p \<Longrightarrow> res_up s w \<noteq> - 1 \<Longrightarrow> m \<noteq> - 1 \<and> m \<le> res_up s w"
proof (induct p arbitrary: m best w rule: rev_induct)
  case Nil thus ?case by simp
next
  case (snoc x p)
  obtain m' b' where mb: "scan_up s p = (m', b')" by (cases "scan_up s p")
  have step: "scan_up s (p @ [x]) =
        (let rr = res_up s x in if rr = - 1 then (m', b')
         else if m' = - 1 then (rr, x) else if rr \<le> m' then (rr, x) else (m', b'))"
    using mb by (simp add: scan_up_def)
  show ?case
  proof (cases "w = x")
    case True
    thus ?thesis using snoc.prems step by (auto simp: Let_def split: if_splits)
  next
    case False
    hence winp: "w \<in> set p" using snoc.prems(2) by simp
    have ih: "res_up s w \<noteq> - 1 \<Longrightarrow> m' \<noteq> - 1 \<and> m' \<le> res_up s w" using snoc.hyps[OF mb winp] .
    thus ?thesis using snoc.prems step by (auto simp: Let_def split: if_splits)
  qed
qed

lemma scan_down_min:
  "scan_down s p = (m, best) \<Longrightarrow> w \<in> set p \<Longrightarrow> res_down s w \<noteq> - 1 \<Longrightarrow> m \<noteq> - 1 \<and> m \<le> res_down s w"
proof (induct p arbitrary: m best w rule: rev_induct)
  case Nil thus ?case by simp
next
  case (snoc x p)
  obtain m' b' where mb: "scan_down s p = (m', b')" by (cases "scan_down s p")
  have step: "scan_down s (p @ [x]) =
        (let rr = res_down s x in if rr = - 1 then (m', b')
         else if m' = - 1 then (rr, x) else if rr < m' then (rr, x) else (m', b'))"
    using mb by (simp add: scan_down_def)
  show ?case
  proof (cases "w = x")
    case True
    thus ?thesis using snoc.prems step by (auto simp: Let_def split: if_splits)
  next
    case False
    hence winp: "w \<in> set p" using snoc.prems(2) by simp
    have ih: "res_down s w \<noteq> - 1 \<Longrightarrow> m' \<noteq> - 1 \<and> m' \<le> res_down s w" using snoc.hyps[OF mb winp] .
    thus ?thesis using snoc.prems step by (auto simp: Let_def split: if_splits)
  qed
qed

lemma bottleneck_delta:
  assumes bn: "bottleneck s e in_U p1 p2 = (\<delta>, is_flip, v, e0fwd, up_side)"
    and dne0: "\<delta> \<noteq> - 1"
    and su: "scan_up s (if in_U then p1 else p2) = (mu, vu)"
    and sd: "scan_down s (if in_U then p2 else p1) = (md, vd)"
  shows "\<delta> = mininf (if in_U then res_bwd s e else res_fwd s e) (mininf mu md)"
proof -
  let ?re = "if in_U then res_bwd s e else res_fwd s e"
  let ?d = "mininf ?re (mininf mu md)"
  have bform: "bottleneck s e in_U p1 p2 =
     (if ?d = - 1 then (- 1, True, r, False, False)
      else if mu \<noteq> - 1 \<and> mu = ?d then (?d, False, vu, par_up s vu, True)
      else if ?re = ?d then (?d, True, r, False, False)
      else (?d, False, vd, \<not> par_up s vd, False))"
    unfolding bottleneck_def Let_def su sd by simp
  show ?thesis using bn dne0 unfolding bform by (auto split: if_splits)
qed

lemma bottleneck_delta_bounds:
  assumes inv: "ns_invar s"
    and sel: "ns_select s = Some (e, in_U, \<gamma>, sel')"
    and pp: "get_path_pair (spanning_tree s) (fst e) (snd e) = (p1, p2)"
    and bn: "bottleneck s e in_U p1 p2 = (\<delta>, isf, lv, lfw, lus)"
    and dne: "\<delta> \<noteq> - 1"
  shows "0 \<le> \<delta>"
    and "\<And>w. w \<in> set (if in_U then p1 else p2) \<Longrightarrow> res_up s w \<noteq> - 1 \<Longrightarrow> \<delta> \<le> res_up s w"
    and "\<And>w. w \<in> set (if in_U then p2 else p1) \<Longrightarrow> res_down s w \<noteq> - 1 \<Longrightarrow> \<delta> \<le> res_down s w"
    and "(if in_U then res_bwd s e else res_fwd s e) \<noteq> - 1 \<Longrightarrow> \<delta> \<le> (if in_U then res_bwd s e else res_fwd s e)"
proof -
  have eE: "e \<in> \<E>" using ns_select_SomeD(2)[OF inv sel] .
  have p1V: "set p1 \<subseteq> \<V> - {r}" and p2V: "set p2 \<subseteq> \<V> - {r}"
    using get_path_pair_verts[OF inv eE entering_not_selfloop[OF inv sel] pp] by auto
  have upV: "set (if in_U then p1 else p2) \<subseteq> \<V> - {r}" using p1V p2V by (cases in_U) auto
  have dnV: "set (if in_U then p2 else p1) \<subseteq> \<V> - {r}" using p1V p2V by (cases in_U) auto
  obtain mu vu where su: "scan_up s (if in_U then p1 else p2) = (mu, vu)"
    by (cases "scan_up s (if in_U then p1 else p2)")
  obtain md vd where sd: "scan_down s (if in_U then p2 else p1) = (md, vd)"
    by (cases "scan_down s (if in_U then p2 else p1)")
  let ?re = "if in_U then res_bwd s e else res_fwd s e"
  have deq: "\<delta> = mininf ?re (mininf mu md)"
    using bottleneck_delta[OF bn dne su sd] .
  have reS: "0 \<le> ?re \<or> ?re = - 1"
    using res_bwd_nonneg[OF inv eE] res_fwd_sign[OF inv eE] by (cases in_U) auto
  have muS: "0 \<le> mu \<or> mu = - 1" using scan_up_val_sign[OF inv upV su] .
  have mdS: "0 \<le> md \<or> md = - 1" using scan_down_val_sign[OF inv dnV sd] .
  show "0 \<le> \<delta>" using mininf_sign[OF reS mininf_sign[OF muS mdS]] dne deq by auto
  show "\<And>w. w \<in> set (if in_U then p1 else p2) \<Longrightarrow> res_up s w \<noteq> - 1 \<Longrightarrow> \<delta> \<le> res_up s w"
  proof -
    fix w assume winw: "w \<in> set (if in_U then p1 else p2)" and rw: "res_up s w \<noteq> - 1"
    have muw: "mu \<noteq> - 1 \<and> mu \<le> res_up s w" using scan_up_min[OF su winw rw] .
    hence muNe: "mu \<noteq> - 1" by simp
    hence muNN: "0 \<le> mu" using muS by simp
    have mmNe: "mininf mu md \<noteq> - 1" using mininf_nonneg[OF muNN mdS] by simp
    have "\<delta> \<le> mininf mu md" using deq mininf_le2[OF mmNe] by simp
    also have "... \<le> mu" using mininf_le1[OF muNe] .
    also have "... \<le> res_up s w" using muw by simp
    finally show "\<delta> \<le> res_up s w" .
  qed
  show "\<And>w. w \<in> set (if in_U then p2 else p1) \<Longrightarrow> res_down s w \<noteq> - 1 \<Longrightarrow> \<delta> \<le> res_down s w"
  proof -
    fix w assume winw: "w \<in> set (if in_U then p2 else p1)" and rw: "res_down s w \<noteq> - 1"
    have mdw: "md \<noteq> - 1 \<and> md \<le> res_down s w" using scan_down_min[OF sd winw rw] .
    hence mdNe: "md \<noteq> - 1" by simp
    hence mdNN: "0 \<le> md" using mdS by simp
    have mmNe: "mininf mu md \<noteq> - 1" using mininf_nonneg2[OF muS mdNN] by simp
    have "\<delta> \<le> mininf mu md" using deq mininf_le2[OF mmNe] by simp
    also have "... \<le> md" using mininf_le2[OF mdNe] .
    also have "... \<le> res_down s w" using mdw by simp
    finally show "\<delta> \<le> res_down s w" .
  qed
  show "?re \<noteq> - 1 \<Longrightarrow> \<delta> \<le> ?re"
  proof -
    assume rne: "?re \<noteq> - 1"
    show "\<delta> \<le> ?re" using deq mininf_le1[OF rne] by simp
  qed
qed

lemma push_fwd_bound:
  assumes inv: "ns_invar s" and aE: "a \<in> \<E>" and d0: "0 \<le> \<delta>"
    and dle: "res_fwd s a = - 1 \<or> \<delta> \<le> res_fwd s a"
  shows "0 \<le> flow_lookup (current_flow s) a + \<delta> \<and> ereal (h (flow_lookup (current_flow s) a + \<delta>)) \<le> \<u> a"
proof -
  have iu: "isuflow (ns_flow_of s)" using ns_invar_bflowD[OF ns_invarD(2)[OF inv]] by (simp add: isbflow_def)
  have cfnn: "0 \<le> flow_lookup (current_flow s) a" using iu aE by (auto simp: isuflow_def comp_def)
  show ?thesis
  proof (cases "cap a = - 1")
    case True
    hence "\<u> a = \<infinity>" using cap_infinite[OF aE] by simp
    thus ?thesis using cfnn d0 by simp
  next
    case False
    hence cnn: "0 \<le> cap a" using cap_nonneg[OF aE] by simp
    have ue: "\<u> a = ereal (h (cap a))" using cap_finite[OF aE cnn] .
    have cfle: "flow_lookup (current_flow s) a \<le> cap a" using iu aE ue by (auto simp: isuflow_def comp_def)
    have rf: "res_fwd s a = cap a - flow_lookup (current_flow s) a" using False by (simp add: res_fwd_def)
    have rfnn: "0 \<le> res_fwd s a" using rf cfle by simp
    have "\<delta> \<le> res_fwd s a" using dle rfnn by auto
    hence "flow_lookup (current_flow s) a + \<delta> \<le> cap a" using rf by simp
    thus ?thesis using cfnn d0 ue by simp
  qed
qed

lemma push_bwd_bound:
  assumes inv: "ns_invar s" and aE: "a \<in> \<E>" and d0: "0 \<le> \<delta>"
    and dle: "\<delta> \<le> res_bwd s a"
  shows "0 \<le> flow_lookup (current_flow s) a - \<delta> \<and> ereal (h (flow_lookup (current_flow s) a - \<delta>)) \<le> \<u> a"
proof -
  have iu: "isuflow (ns_flow_of s)" using ns_invar_bflowD[OF ns_invarD(2)[OF inv]] by (simp add: isbflow_def)
  have cfle: "ereal (h (flow_lookup (current_flow s) a)) \<le> \<u> a" using iu aE by (auto simp: isuflow_def comp_def)
  have low: "0 \<le> flow_lookup (current_flow s) a - \<delta>" using dle by (simp add: res_bwd_def)
  have "ereal (h (flow_lookup (current_flow s) a - \<delta>)) \<le> ereal (h (flow_lookup (current_flow s) a))" using d0 by simp
  also have "... \<le> \<u> a" using cfle .
  finally show ?thesis using low by simp
qed

text \<open>\<^bold>\<open>Capacity.\<close> Every circuit edge is pushed by at most its own residual, so the flow stays
      within its capacity bounds. Case split on where an edge lies (the entering edge, an up-path
      parent, a down-path parent, or untouched); the new value comes from the touched-once lookup lemmas.\<close>

lemma augment_flow_isuflow:
  assumes inv: "ns_invar s"
    and sel: "ns_select s = Some (e, in_U, \<gamma>, sel')"
    and pp: "get_path_pair (spanning_tree s) (fst e) (snd e) = (p1, p2)"
    and bn: "bottleneck s e in_U p1 p2 = (\<delta>, isf, lv, lfw, lus)"
    and dne: "\<delta> \<noteq> - 1"
  shows "isuflow (h \<circ> flow_lookup (augment_flow s e in_U \<delta> p1 p2))"
proof (cases "\<delta> \<le> 0")
  case True
  have "isuflow (ns_flow_of s)" using ns_invar_bflowD[OF ns_invarD(2)[OF inv]] by (simp add: isbflow_def)
  thus ?thesis using True by (simp add: augment_flow_def)
next
  case False
  have d0: "0 \<le> \<delta>" using bottleneck_delta_bounds(1)[OF inv sel pp bn dne] .
  have eE: "e \<in> \<E>" using ns_select_SomeD(2)[OF inv sel] .
  have neq: "fst e \<noteq> snd e" using entering_not_selfloop[OF inv sel] .
  have fV: "fst e \<in> \<V>" using fst_E_V[OF eE] .
  have sV: "snd e \<in> \<V>" using snd_E_V[OF eE] .
  have arb: "arborescense_invar (spanning_tree s)" using ns_invar_implD(7)[OF ns_invarD(1)[OF inv]] .
  have fiE: "flow_invar (current_flow s)" using ns_invar_implD(1)[OF ns_invarD(1)[OF inv]] .
  have tree: "ns_invar_tree s" using ns_invarD(7)[OF inv] .
  have p1V: "set p1 \<subseteq> \<V> - {r}" and p2V: "set p2 \<subseteq> \<V> - {r}"
    using get_path_pair_verts[OF inv eE entering_not_selfloop[OF inv sel] pp] by auto
  obtain a0 p3 where
    d1: "distinct (p1 @ a0 # p3)" and d2: "distinct (p2 @ a0 # p3)"
    using get_path_pair(1)[OF arb pp neq fV sV] by blast
  have injp: "inj_on (par_edge s) (set p1 \<union> set p2)"
    using get_path_pair_align(5)[OF inv sel pp] .
  have entree: "e \<notin> ns_tree_edges s" using ns_select_SomeD(3)[OF inv sel] .
  have e_ne: "\<And>w. w \<in> \<V> - {r} \<Longrightarrow> par_edge s w \<noteq> e"
  proof -
    fix w assume "w \<in> \<V> - {r}"
    hence "par_edge s w \<in> ns_tree_edges s" by (auto simp: par_edge_def)
    thus "par_edge s w \<noteq> e" using entree by blast
  qed
  have parE: "\<And>w. w \<in> \<V> - {r} \<Longrightarrow> par_edge s w \<in> \<E>" using ns_invar_tree_edgeD[OF tree] .
  let ?up = "if in_U then p1 else p2"
  let ?dn = "if in_U then p2 else p1"
  have upV: "set ?up \<subseteq> \<V> - {r}" using p1V p2V by (cases in_U) auto
  have dnV: "set ?dn \<subseteq> \<V> - {r}" using p1V p2V by (cases in_U) auto
  have upE: "\<forall>w\<in>set ?up. par_edge s w \<in> \<E>" using p1V p2V parE by (cases in_U) auto
  have dnE: "\<forall>w\<in>set ?dn. par_edge s w \<in> \<E>" using p1V p2V parE by (cases in_U) auto
  have updist: "distinct ?up" using d1 d2 by (cases in_U) auto
  have dndist: "distinct ?dn" using d1 d2 by (cases in_U) auto
  have upsub: "set ?up \<subseteq> set p1 \<union> set p2" by (cases in_U) auto
  have dnsub: "set ?dn \<subseteq> set p1 \<union> set p2" by (cases in_U) auto
  have injup: "inj_on (par_edge s) (set ?up)" using injp upsub by (rule inj_on_subset)
  have injdn: "inj_on (par_edge s) (set ?dn)" using injp dnsub by (rule inj_on_subset)
  have updisj: "set ?up \<inter> set ?dn = {}"
    using get_path_pair_align(4)[OF inv sel pp] by (cases in_U) auto
  let ?ce = "if in_U then - \<delta> else \<delta>"
  let ?gup = "\<lambda>w. if par_up s w then \<delta> else - \<delta>"
  let ?gdn = "\<lambda>w. if par_up s w then - \<delta> else \<delta>"
  let ?f0 = "flow_upd (current_flow s) e (flow_lookup (current_flow s) e + ?ce)"
  let ?f1 = "fold (\<lambda>w f. flow_upd f (par_edge s w) (flow_lookup f (par_edge s w) + ?gup w)) ?up ?f0"
  let ?f' = "fold (\<lambda>w f. flow_upd f (par_edge s w) (flow_lookup f (par_edge s w) + ?gdn w)) ?dn ?f1"
  have augeq: "augment_flow s e in_U \<delta> p1 p2 = ?f'"
    using False by (simp add: augment_flow_def Let_def)
  have fi0: "flow_invar ?f0" using fiE eE by (rule flow_arr.fixed_univ_map_upd_invar)
  have fi1: "flow_invar ?f1" using fold_flow_upd_invar[OF fi0 upE] .
  have f0val: "\<And>a. flow_lookup ?f0 a = (if a = e then flow_lookup (current_flow s) e + ?ce else flow_lookup (current_flow s) a)"
    using flow_arr.fixed_univ_map_upd[OF fiE eE] by (auto simp: fun_upd_def)
  have e_notin_up: "e \<notin> par_edge s ` set ?up"
  proof
    assume "e \<in> par_edge s ` set ?up"
    then obtain w where w: "w \<in> set ?up" and eq: "e = par_edge s w" by auto
    have wV: "w \<in> \<V> - {r}" using w upV by auto
    show False using e_ne[OF wV] eq by simp
  qed
  have e_notin_dn: "e \<notin> par_edge s ` set ?dn"
  proof
    assume "e \<in> par_edge s ` set ?dn"
    then obtain w where w: "w \<in> set ?dn" and eq: "e = par_edge s w" by auto
    have wV: "w \<in> \<V> - {r}" using w dnV by auto
    show False using e_ne[OF wV] eq by simp
  qed
  have up_notin_dn: "\<And>w0. w0 \<in> set ?up \<Longrightarrow> par_edge s w0 \<notin> par_edge s ` set ?dn"
  proof -
    fix w0 assume w0: "w0 \<in> set ?up"
    show "par_edge s w0 \<notin> par_edge s ` set ?dn"
    proof
      assume "par_edge s w0 \<in> par_edge s ` set ?dn"
      then obtain w1 where w1: "w1 \<in> set ?dn" and eq: "par_edge s w0 = par_edge s w1" by auto
      have "w0 \<in> set p1 \<union> set p2" using w0 upsub by auto
      moreover have "w1 \<in> set p1 \<union> set p2" using w1 dnsub by auto
      ultimately have "w0 = w1" using eq injp by (auto dest: inj_onD)
      thus False using w0 w1 updisj by auto
    qed
  qed
  have dn_notin_up: "\<And>w0. w0 \<in> set ?dn \<Longrightarrow> par_edge s w0 \<notin> par_edge s ` set ?up"
  proof -
    fix w0 assume w0: "w0 \<in> set ?dn"
    show "par_edge s w0 \<notin> par_edge s ` set ?up"
    proof
      assume "par_edge s w0 \<in> par_edge s ` set ?up"
      then obtain w1 where w1: "w1 \<in> set ?up" and eq: "par_edge s w0 = par_edge s w1" by auto
      have "w0 \<in> set p1 \<union> set p2" using w0 dnsub by auto
      moreover have "w1 \<in> set p1 \<union> set p2" using w1 upsub by auto
      ultimately have "w0 = w1" using eq injp by (auto dest: inj_onD)
      thus False using w0 w1 updisj by auto
    qed
  qed
  have bound: "\<And>a. a \<in> \<E> \<Longrightarrow> 0 \<le> flow_lookup ?f' a \<and> ereal (h (flow_lookup ?f' a)) \<le> \<u> a"
  proof -
    fix a assume aE: "a \<in> \<E>"
    consider (Up) w0 where "w0 \<in> set ?up" "a = par_edge s w0"
           | (Dn) w0 where "w0 \<in> set ?dn" "a = par_edge s w0"
           | (Other) "a \<notin> par_edge s ` set ?up" "a \<notin> par_edge s ` set ?dn"
      by auto
    then show "0 \<le> flow_lookup ?f' a \<and> ereal (h (flow_lookup ?f' a)) \<le> \<u> a"
    proof cases
      case (Up w0)
      have w0V: "w0 \<in> \<V> - {r}" using Up(1) upV by auto
      have aneE: "par_edge s w0 \<noteq> e" using e_ne[OF w0V] .
      have fdn: "flow_lookup ?f' a = flow_lookup ?f1 a"
        using fold_lookup_notin[OF fi1 dnE up_notin_dn[OF Up(1)]] Up(2) by simp
      have fup: "flow_lookup ?f1 (par_edge s w0) = flow_lookup ?f0 (par_edge s w0) + ?gup w0"
        using fold_lookup_at[OF fi0 upE updist injup Up(1)] .
      have f0a: "flow_lookup ?f0 (par_edge s w0) = flow_lookup (current_flow s) (par_edge s w0)"
        using f0val aneE by simp
      have val: "flow_lookup ?f' a = flow_lookup (current_flow s) a + ?gup w0"
        using fdn fup f0a Up(2) by simp
      show ?thesis
      proof (cases "par_up s w0")
        case up: True
        have resup: "res_up s w0 = res_fwd s a" using up Up(2) by (simp add: res_up_def)
        have dle: "res_fwd s a = - 1 \<or> \<delta> \<le> res_fwd s a"
          using bottleneck_delta_bounds(2)[OF inv sel pp bn dne Up(1)] resup by auto
        have "0 \<le> flow_lookup (current_flow s) a + \<delta> \<and> ereal (h (flow_lookup (current_flow s) a + \<delta>)) \<le> \<u> a"
          using push_fwd_bound[OF inv aE d0 dle] .
        thus ?thesis using val up by simp
      next
        case dn: False
        have resup: "res_up s w0 = res_bwd s a" using dn Up(2) by (simp add: res_up_def)
        have rbnn: "res_bwd s a \<noteq> - 1" using res_bwd_nonneg[OF inv aE] by simp
        have dle: "\<delta> \<le> res_bwd s a"
          using bottleneck_delta_bounds(2)[OF inv sel pp bn dne Up(1)] resup rbnn by auto
        have "0 \<le> flow_lookup (current_flow s) a - \<delta> \<and> ereal (h (flow_lookup (current_flow s) a - \<delta>)) \<le> \<u> a"
          using push_bwd_bound[OF inv aE d0 dle] .
        thus ?thesis using val dn by simp
      qed
    next
      case (Dn w0)
      have w0V: "w0 \<in> \<V> - {r}" using Dn(1) dnV by auto
      have aneE: "par_edge s w0 \<noteq> e" using e_ne[OF w0V] .
      have fdn: "flow_lookup ?f' a = flow_lookup ?f1 (par_edge s w0) + ?gdn w0"
        using fold_lookup_at[OF fi1 dnE dndist injdn Dn(1)] Dn(2) by simp
      have fup: "flow_lookup ?f1 (par_edge s w0) = flow_lookup ?f0 (par_edge s w0)"
        using fold_lookup_notin[OF fi0 upE dn_notin_up[OF Dn(1)]] .
      have f0a: "flow_lookup ?f0 (par_edge s w0) = flow_lookup (current_flow s) (par_edge s w0)"
        using f0val aneE by simp
      have val: "flow_lookup ?f' a = flow_lookup (current_flow s) a + ?gdn w0"
        using fdn fup f0a Dn(2) by simp
      show ?thesis
      proof (cases "par_up s w0")
        case up: True
        have resdn: "res_down s w0 = res_bwd s a" using up Dn(2) by (simp add: res_down_def)
        have rbnn: "res_bwd s a \<noteq> - 1" using res_bwd_nonneg[OF inv aE] by simp
        have dle: "\<delta> \<le> res_bwd s a"
          using bottleneck_delta_bounds(3)[OF inv sel pp bn dne Dn(1)] resdn rbnn by auto
        have "0 \<le> flow_lookup (current_flow s) a - \<delta> \<and> ereal (h (flow_lookup (current_flow s) a - \<delta>)) \<le> \<u> a"
          using push_bwd_bound[OF inv aE d0 dle] .
        thus ?thesis using val up by simp
      next
        case dn: False
        have resdn: "res_down s w0 = res_fwd s a" using dn Dn(2) by (simp add: res_down_def)
        have dle: "res_fwd s a = - 1 \<or> \<delta> \<le> res_fwd s a"
          using bottleneck_delta_bounds(3)[OF inv sel pp bn dne Dn(1)] resdn by auto
        have "0 \<le> flow_lookup (current_flow s) a + \<delta> \<and> ereal (h (flow_lookup (current_flow s) a + \<delta>)) \<le> \<u> a"
          using push_fwd_bound[OF inv aE d0 dle] .
        thus ?thesis using val dn by simp
      qed
    next
      case Other
      have f1a: "flow_lookup ?f1 a = flow_lookup ?f0 a"
        using fold_lookup_notin[OF fi0 upE Other(1)] .
      have fdn: "flow_lookup ?f' a = flow_lookup ?f1 a"
        using fold_lookup_notin[OF fi1 dnE Other(2)] .
      show ?thesis
      proof (cases "a = e")
        case ae: True
        have val: "flow_lookup ?f' a = flow_lookup (current_flow s) e + ?ce"
          using fdn f1a f0val ae by simp
        show ?thesis
        proof (cases in_U)
          case iu: True
          have rbnn: "res_bwd s e \<noteq> - 1" using res_bwd_nonneg[OF inv eE] by simp
          have dle: "\<delta> \<le> res_bwd s e"
            using bottleneck_delta_bounds(4)[OF inv sel pp bn dne] iu rbnn by simp
          have "0 \<le> flow_lookup (current_flow s) e - \<delta> \<and> ereal (h (flow_lookup (current_flow s) e - \<delta>)) \<le> \<u> e"
            using push_bwd_bound[OF inv eE d0 dle] .
          thus ?thesis using val ae iu by simp
        next
          case iu: False
          have dle: "res_fwd s e = - 1 \<or> \<delta> \<le> res_fwd s e"
            using bottleneck_delta_bounds(4)[OF inv sel pp bn dne] iu by auto
          have "0 \<le> flow_lookup (current_flow s) e + \<delta> \<and> ereal (h (flow_lookup (current_flow s) e + \<delta>)) \<le> \<u> e"
            using push_fwd_bound[OF inv eE d0 dle] .
          thus ?thesis using val ae iu by simp
        qed
      next
        case ae: False
        have val: "flow_lookup ?f' a = flow_lookup (current_flow s) a"
          using fdn f1a f0val ae by simp
        have iu: "isuflow (ns_flow_of s)" using ns_invar_bflowD[OF ns_invarD(2)[OF inv]] by (simp add: isbflow_def)
        show ?thesis using val iu aE by (auto simp: isuflow_def comp_def)
      qed
    qed
  qed
  show "isuflow (h \<circ> flow_lookup (augment_flow s e in_U \<delta> p1 p2))"
    unfolding augeq
  proof (rule isuflowI)
    fix aa assume "aa \<in> \<E>" thus "ereal ((h \<circ> flow_lookup ?f') aa) \<le> \<u> aa" using bound by (auto simp: comp_def)
  next
    fix aa assume "aa \<in> \<E>" thus "0 \<le> (h \<circ> flow_lookup ?f') aa" using bound by (auto simp: comp_def)
  qed
qed

text \<open>Conservation and capacity together: @{const augment_flow} stays a @{term b}-flow.\<close>

lemma augment_flow_bflow:
  assumes inv: "ns_invar s"
    and sel: "ns_select s = Some (e, in_U, \<gamma>, sel')"
    and pp: "get_path_pair (spanning_tree s) (fst e) (snd e) = (p1, p2)"
    and bn: "bottleneck s e in_U p1 p2 = (\<delta>, isf, lv, lfw, lus)"
    and dne: "\<delta> \<noteq> - 1"
  shows "(h \<circ> flow_lookup (augment_flow s e in_U \<delta> p1 p2)) is b flow"
proof (rule isbflowI)
  show "isuflow (h \<circ> flow_lookup (augment_flow s e in_U \<delta> p1 p2))"
    using augment_flow_isuflow[OF inv sel pp bn dne] .
next
  fix v assume vV: "v \<in> \<V>"
  have "ex (h \<circ> flow_lookup (augment_flow s e in_U \<delta> p1 p2)) v = ex (h \<circ> flow_lookup (current_flow s)) v"
    using augment_flow_ex[OF inv sel pp] .
  moreover have "- ex (ns_flow_of s) v = b v"
    using ns_invar_bflowD[OF ns_invarD(2)[OF inv]] vV by (auto elim!: isbflowE)
  ultimately show "- ex (h \<circ> flow_lookup (augment_flow s e in_U \<delta> p1 p2)) v = b v" by simp
qed

text \<open>\<^bold>\<open>Cost identity.\<close> The cost change telescopes exactly as conservation did, but weighted by the
      potentials: on tree edges the reduced cost is zero, so \<open>\<c> (par_edge s w) = \<pi> (snd) - \<pi> (fst)\<close>,
      and each leg's cost sum collapses to the boundary potentials. Combined with the entering edge the
      total change is the entering edge's reduced cost, times the signed flow change applied to it.\<close>

lemma telescope_succ_gen:
  assumes succ: "\<And>i. Suc i < length ys \<Longrightarrow> f (ys ! i) = ys ! Suc i" and ne: "ys \<noteq> []"
  shows "(\<Sum>w\<leftarrow>butlast ys. \<phi> (f w) - \<phi> w) = \<phi> (last ys) - (\<phi> (hd ys) :: real)"
proof -
  let ?n = "length ys - 1"
  let ?g = "\<lambda>i. (\<phi> (ys ! i) :: real)"
  have lb: "length (butlast ys) = ?n" by simp
  have "(\<Sum>w\<leftarrow>butlast ys. \<phi> (f w) - \<phi> w) = (\<Sum>i<?n. \<phi> (f (butlast ys ! i)) - \<phi> (butlast ys ! i))"
    by (simp add: sum_list_sum_nth lb atLeast0LessThan)
  also have "... = (\<Sum>i<?n. ?g (Suc i) - ?g i)"
  proof (rule sum.cong)
    fix i assume "i \<in> {..<?n}"
    hence iL: "i < ?n" by simp
    hence bi: "butlast ys ! i = ys ! i" by (simp add: nth_butlast)
    have "Suc i < length ys" using iL by simp
    hence "f (ys ! i) = ys ! Suc i" using succ by simp
    thus "\<phi> (f (butlast ys ! i)) - \<phi> (butlast ys ! i) = ?g (Suc i) - ?g i" using bi by simp
  qed simp
  also have "... = ?g ?n - ?g 0" by (rule sum_lessThan_telescope)
  also have "... = \<phi> (last ys) - \<phi> (hd ys)"
    using ne by (simp add: last_conv_nth hd_conv_nth)
  finally show ?thesis .
qed

lemma path_telescope_gen:
  assumes inv: "ns_invar s"
    and w: "walk_betw (abstract_arborescense (spanning_tree s)) u (P @ a # p3) r"
    and d: "distinct (P @ a # p3)"
    and PV: "set P \<subseteq> \<V> - {r}"
  shows "(\<Sum>w\<leftarrow>P. \<phi> (par_vx s w) - \<phi> w) = \<phi> a - (\<phi> u :: real)"
proof -
  let ?ys = "P @ [a]"
  have ne: "?ys \<noteq> []" by simp
  have succ: "\<And>i. Suc i < length ?ys \<Longrightarrow> par_vx s (?ys ! i) = ?ys ! Suc i"
  proof -
    fix i assume iL: "Suc i < length ?ys"
    have iP: "i < length P" using iL by simp
    have SiW: "Suc i < length (P @ a # p3)" using iL by simp
    have wi: "?ys ! i = (P @ a # p3) ! i" using iP by (simp add: nth_append)
    have wsi: "?ys ! Suc i = (P @ a # p3) ! Suc i" using iL by (auto simp: nth_append)
    have Wi: "(P @ a # p3) ! i = P ! i" using iP by (simp add: nth_append)
    have WiV: "(P @ a # p3) ! i \<in> \<V> - {r}" using Wi iP PV nth_mem by (metis subsetD)
    have "par_vx s ((P @ a # p3) ! i) = (P @ a # p3) ! Suc i"
      using walk_succ_is_par_vx[OF inv w d SiW WiV] .
    thus "par_vx s (?ys ! i) = ?ys ! Suc i" using wi wsi by simp
  qed
  have hd_u: "hd ?ys = u"
  proof -
    have "hd (P @ a # p3) = u" using w by (simp add: walk_betw_def)
    thus ?thesis by (cases P) auto
  qed
  have "(\<Sum>w\<leftarrow>butlast ?ys. \<phi> (par_vx s w) - \<phi> w) = \<phi> (last ?ys) - \<phi> (hd ?ys)"
    using telescope_succ_gen[OF succ ne] .
  thus ?thesis using hd_u by simp
qed

lemma cval_lemma:
  assumes inv: "ns_invar s" and wV: "w \<in> \<V> - {r}"
  shows "\<c> (par_edge s w) = (if par_up s w then ns_pot_of s (par_vx s w) - ns_pot_of s w
                                          else ns_pot_of s w - ns_pot_of s (par_vx s w))"
proof -
  have pe: "par_edge s w \<in> ns_tree_edges s" using wV by (auto simp: par_edge_def)
  have allrc: "\<forall>ee\<in>ns_tree_edges s. \<c> ee + ns_pot_of s (fst ee) - ns_pot_of s (snd ee) = 0"
    using ns_invar_pot_fitsD[OF ns_invarD(5)[OF inv]] unfolding potential_fits_spanning_tree_partition_def by simp
  have rc0: "\<c> (par_edge s w) + ns_pot_of s (fst (par_edge s w)) - ns_pot_of s (snd (par_edge s w)) = 0"
    using bspec[OF allrc pe] .
  have dir: "if par_up s w then fst (par_edge s w) = w else snd (par_edge s w) = w"
    using ns_invar_tree_dirD[OF ns_invarD(7)[OF inv] wV] .
  show ?thesis using rc0 dir by (cases "par_up s w") (auto simp: par_vx_def)
qed

lemma up_cost_contrib:
  assumes inv: "ns_invar s" and wV: "w \<in> \<V> - {r}"
  shows "\<c> (par_edge s w) * (if par_up s w then \<delta> else - \<delta>)
       = \<delta> * (ns_pot_of s (par_vx s w) - ns_pot_of s w)"
  unfolding cval_lemma[OF inv wV] by (cases "par_up s w") (simp_all add: algebra_simps)

lemma down_cost_contrib:
  assumes inv: "ns_invar s" and wV: "w \<in> \<V> - {r}"
  shows "\<c> (par_edge s w) * (if par_up s w then - \<delta> else \<delta>)
       = \<delta> * (ns_pot_of s w - ns_pot_of s (par_vx s w))"
  unfolding cval_lemma[OF inv wV] by (cases "par_up s w") (simp_all add: algebra_simps)

lemma sum_list_mult_right: "(\<Sum>x\<leftarrow>xs. f x) * (c::real) = (\<Sum>x\<leftarrow>xs. f x * c)"
  by (induct xs) (auto simp: algebra_simps)

lemma sum_sum_list_swap:
  "finite A \<Longrightarrow> (\<Sum>a\<in>A. (\<Sum>w\<leftarrow>xs. hf a w)) = (\<Sum>w\<leftarrow>xs. (\<Sum>a\<in>A. hf a w))"
proof (induct xs)
  case Nil thus ?case by simp
next
  case (Cons w xs)
  have "(\<Sum>a\<in>A. (\<Sum>w'\<leftarrow>(w # xs). hf a w')) = (\<Sum>a\<in>A. (hf a w + (\<Sum>w'\<leftarrow>xs. hf a w')))" by simp
  also have "... = (\<Sum>a\<in>A. hf a w) + (\<Sum>a\<in>A. (\<Sum>w'\<leftarrow>xs. hf a w'))" by (rule sum.distrib)
  also have "... = (\<Sum>a\<in>A. hf a w) + (\<Sum>w'\<leftarrow>xs. (\<Sum>a\<in>A. hf a w'))" using Cons by simp
  finally show ?case by simp
qed

lemma up_cost_sum:
  assumes inv: "ns_invar s"
    and w: "walk_betw (abstract_arborescense (spanning_tree s)) u (P @ a # p3) r"
    and d: "distinct (P @ a # p3)"
    and PV: "set P \<subseteq> \<V> - {r}"
  shows "(\<Sum>w\<leftarrow>P. \<c> (par_edge s w) * (if par_up s w then \<delta> else - \<delta>))
       = \<delta> * (ns_pot_of s a - ns_pot_of s u)"
proof -
  have "(\<Sum>w\<leftarrow>P. \<c> (par_edge s w) * (if par_up s w then \<delta> else - \<delta>))
      = (\<Sum>w\<leftarrow>P. \<delta> * (ns_pot_of s (par_vx s w) - ns_pot_of s w))"
  proof (rule arg_cong[where f=sum_list], rule map_cong[OF refl])
    fix w assume "w \<in> set P"
    hence "w \<in> \<V> - {r}" using PV by auto
    thus "\<c> (par_edge s w) * (if par_up s w then \<delta> else - \<delta>) = \<delta> * (ns_pot_of s (par_vx s w) - ns_pot_of s w)"
      by (rule up_cost_contrib[OF inv])
  qed
  also have "... = \<delta> * (\<Sum>w\<leftarrow>P. ns_pot_of s (par_vx s w) - ns_pot_of s w)"
    by (rule sum_list_scale)
  also have "... = \<delta> * (ns_pot_of s a - ns_pot_of s u)"
    using path_telescope_gen[OF inv w d PV, of "ns_pot_of s"] by simp
  finally show ?thesis .
qed

lemma down_cost_sum:
  assumes inv: "ns_invar s"
    and w: "walk_betw (abstract_arborescense (spanning_tree s)) u (P @ a # p3) r"
    and d: "distinct (P @ a # p3)"
    and PV: "set P \<subseteq> \<V> - {r}"
  shows "(\<Sum>w\<leftarrow>P. \<c> (par_edge s w) * (if par_up s w then - \<delta> else \<delta>))
       = \<delta> * (ns_pot_of s u - ns_pot_of s a)"
proof -
  have "(\<Sum>w\<leftarrow>P. \<c> (par_edge s w) * (if par_up s w then - \<delta> else \<delta>))
      = (\<Sum>w\<leftarrow>P. \<delta> * (ns_pot_of s w - ns_pot_of s (par_vx s w)))"
  proof (rule arg_cong[where f=sum_list], rule map_cong[OF refl])
    fix w assume "w \<in> set P"
    hence "w \<in> \<V> - {r}" using PV by auto
    thus "\<c> (par_edge s w) * (if par_up s w then - \<delta> else \<delta>) = \<delta> * (ns_pot_of s w - ns_pot_of s (par_vx s w))"
      by (rule down_cost_contrib[OF inv])
  qed
  also have "... = \<delta> * (\<Sum>w\<leftarrow>P. ns_pot_of s w - ns_pot_of s (par_vx s w))"
    by (rule sum_list_scale)
  also have "... = \<delta> * (- (ns_pot_of s a - ns_pot_of s u))"
    using path_telescope_gen[OF inv w d PV, of "ns_pot_of s"] by (simp add: sum_list_subtractf)
  also have "... = \<delta> * (ns_pot_of s u - ns_pot_of s a)" by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma h_sum_list: "h (\<Sum>w\<leftarrow>xs. g w) = (\<Sum>w\<leftarrow>xs. h (g w))"
  by (induct xs) (auto simp: h_add)

lemma h_if0: "h (if c then (x::'n) else 0) = (if c then h x else 0)"
  by (simp add: if_distrib[where f=h])

lemma up_cost_sum_h:
  assumes inv: "ns_invar s"
    and w: "walk_betw (abstract_arborescense (spanning_tree s)) u (P @ a # p3) r"
    and d: "distinct (P @ a # p3)"
    and PV: "set P \<subseteq> \<V> - {r}"
  shows "(\<Sum>w\<leftarrow>P. \<c> (par_edge s w) * h (if par_up s w then \<delta> else - \<delta>))
       = h \<delta> * (ns_pot_of s a - ns_pot_of s u)"
proof -
  have "(\<Sum>w\<leftarrow>P. \<c> (par_edge s w) * h (if par_up s w then \<delta> else - \<delta>))
      = (\<Sum>w\<leftarrow>P. \<c> (par_edge s w) * (if par_up s w then h \<delta> else - h \<delta>))"
    by (rule arg_cong[where f=sum_list], rule map_cong[OF refl]) (simp add: if_distrib[where f=h])
  also have "... = h \<delta> * (ns_pot_of s a - ns_pot_of s u)"
    using up_cost_sum[OF inv w d PV] by simp
  finally show ?thesis .
qed

lemma down_cost_sum_h:
  assumes inv: "ns_invar s"
    and w: "walk_betw (abstract_arborescense (spanning_tree s)) u (P @ a # p3) r"
    and d: "distinct (P @ a # p3)"
    and PV: "set P \<subseteq> \<V> - {r}"
  shows "(\<Sum>w\<leftarrow>P. \<c> (par_edge s w) * h (if par_up s w then - \<delta> else \<delta>))
       = h \<delta> * (ns_pot_of s u - ns_pot_of s a)"
proof -
  have "(\<Sum>w\<leftarrow>P. \<c> (par_edge s w) * h (if par_up s w then - \<delta> else \<delta>))
      = (\<Sum>w\<leftarrow>P. \<c> (par_edge s w) * (if par_up s w then - h \<delta> else h \<delta>))"
    by (rule arg_cong[where f=sum_list], rule map_cong[OF refl]) (simp add: if_distrib[where f=h])
  also have "... = h \<delta> * (ns_pot_of s u - ns_pot_of s a)"
    using down_cost_sum[OF inv w d PV] by simp
  finally show ?thesis .
qed

lemma augment_flow_cost:
  assumes inv: "ns_invar s"
    and sel: "ns_select s = Some (e, in_U, \<gamma>, sel')"
    and pp: "get_path_pair (spanning_tree s) (fst e) (snd e) = (p1, p2)"
    and bn: "bottleneck s e in_U p1 p2 = (\<delta>, isf, lv, lfw, lus)"
    and dne: "\<delta> \<noteq> - 1"
  shows "\<C> (h \<circ> flow_lookup (augment_flow s e in_U \<delta> p1 p2))
       = ns_flow_cost s + (if in_U then - h \<delta> else h \<delta>) * reduced_cost (potentials s) e"
proof (cases "\<delta> \<le> 0")
  case True
  have "0 \<le> \<delta>" using bottleneck_delta_bounds(1)[OF inv sel pp bn dne] .
  hence d0: "\<delta> = 0" using True by simp
  have "augment_flow s e in_U \<delta> p1 p2 = current_flow s" using True by (simp add: augment_flow_def)
  thus ?thesis using d0 by (simp add: ns_flow_cost_def)
next
  case False
  have eE: "e \<in> \<E>" using ns_select_SomeD(2)[OF inv sel] .
  have neq: "fst e \<noteq> snd e" using entering_not_selfloop[OF inv sel] .
  have fV: "fst e \<in> \<V>" using fst_E_V[OF eE] .
  have sV: "snd e \<in> \<V>" using snd_E_V[OF eE] .
  have arb: "arborescense_invar (spanning_tree s)" using ns_invar_implD(7)[OF ns_invarD(1)[OF inv]] .
  have fiE: "flow_invar (current_flow s)" using ns_invar_implD(1)[OF ns_invarD(1)[OF inv]] .
  have tree: "ns_invar_tree s" using ns_invarD(7)[OF inv] .
  obtain a0 p3 where
    w1: "walk_betw (abstract_arborescense (spanning_tree s)) (fst e) (p1 @ a0 # p3) r" and
    w2: "walk_betw (abstract_arborescense (spanning_tree s)) (snd e) (p2 @ a0 # p3) r" and
    d1: "distinct (p1 @ a0 # p3)" and d2: "distinct (p2 @ a0 # p3)"
    using get_path_pair(1)[OF arb pp neq fV sV] by blast
  have p1V: "set p1 \<subseteq> \<V> - {r}" and p2V: "set p2 \<subseteq> \<V> - {r}"
    using get_path_pair_verts[OF inv eE entering_not_selfloop[OF inv sel] pp] by auto
  let ?ce = "if in_U then - \<delta> else \<delta>"
  let ?gup = "\<lambda>w. if par_up s w then \<delta> else - \<delta>"
  let ?gdn = "\<lambda>w. if par_up s w then - \<delta> else \<delta>"
  let ?f0 = "flow_upd (current_flow s) e (flow_lookup (current_flow s) e + ?ce)"
  let ?up = "if in_U then p1 else p2"
  let ?dn = "if in_U then p2 else p1"
  have upEf: "\<forall>w\<in>set ?up. par_edge s w \<in> \<E>" using p1V p2V ns_invar_tree_edgeD[OF tree] by (cases in_U) auto
  have dnEf: "\<forall>w\<in>set ?dn. par_edge s w \<in> \<E>" using p1V p2V ns_invar_tree_edgeD[OF tree] by (cases in_U) auto
  let ?f1 = "fold (\<lambda>w f. flow_upd f (par_edge s w) (flow_lookup f (par_edge s w) + ?gup w)) ?up ?f0"
  let ?f' = "fold (\<lambda>w f. flow_upd f (par_edge s w) (flow_lookup f (par_edge s w) + ?gdn w)) ?dn ?f1"
  have augeq: "augment_flow s e in_U \<delta> p1 p2 = ?f'"
    using False by (simp add: augment_flow_def Let_def)
  have fi0: "flow_invar ?f0" using fiE eE by (rule flow_arr.fixed_univ_map_upd_invar)
  have fi1: "flow_invar ?f1" using fold_flow_upd_invar[OF fi0 upEf] .
  have f0val: "\<And>a. flow_lookup ?f0 a = (if a = e then flow_lookup (current_flow s) e + ?ce else flow_lookup (current_flow s) a)"
    using flow_arr.fixed_univ_map_upd[OF fiE eE] by (auto simp: fun_upd_def)
  have fval: "\<And>a. flow_lookup ?f' a = flow_lookup (current_flow s) a + (if a = e then ?ce else 0)
        + (\<Sum>w\<leftarrow>?up. if par_edge s w = a then ?gup w else 0)
        + (\<Sum>w\<leftarrow>?dn. if par_edge s w = a then ?gdn w else 0)"
  proof -
    fix a
    have d': "flow_lookup ?f' a = flow_lookup ?f1 a + (\<Sum>w\<leftarrow>?dn. if par_edge s w = a then ?gdn w else 0)"
      by (rule fold_flow_upd_lookup[OF fi1 dnEf])
    have d1': "flow_lookup ?f1 a = flow_lookup ?f0 a + (\<Sum>w\<leftarrow>?up. if par_edge s w = a then ?gup w else 0)"
      by (rule fold_flow_upd_lookup[OF fi0 upEf])
    have d0': "flow_lookup ?f0 a = flow_lookup (current_flow s) a + (if a = e then ?ce else 0)"
      using f0val by simp
    show "flow_lookup ?f' a = flow_lookup (current_flow s) a + (if a = e then ?ce else 0)
        + (\<Sum>w\<leftarrow>?up. if par_edge s w = a then ?gup w else 0)
        + (\<Sum>w\<leftarrow>?dn. if par_edge s w = a then ?gdn w else 0)"
      using d' d1' d0' by simp
  qed
  have hfval: "\<And>a. h (flow_lookup ?f' a) = h (flow_lookup (current_flow s) a) + (if a = e then h ?ce else 0)
        + (\<Sum>w\<leftarrow>?up. if par_edge s w = a then h (?gup w) else 0)
        + (\<Sum>w\<leftarrow>?dn. if par_edge s w = a then h (?gdn w) else 0)"
    by (simp add: fval h_add h_sum_list h_if0)
  have upV: "set ?up \<subseteq> \<V> - {r}" using p1V p2V by (cases in_U) auto
  have dnV: "set ?dn \<subseteq> \<V> - {r}" using p1V p2V by (cases in_U) auto
  have upE: "\<And>w. w \<in> set ?up \<Longrightarrow> par_edge s w \<in> \<E>" using upV ns_invar_tree_edgeD[OF tree] by auto
  have dnE: "\<And>w. w \<in> set ?dn \<Longrightarrow> par_edge s w \<in> \<E>" using dnV ns_invar_tree_edgeD[OF tree] by auto
  have Tcf: "(\<Sum>a\<in>\<E>. h (flow_lookup (current_flow s) a) * \<c> a) = ns_flow_cost s"
    by (simp add: ns_flow_cost_def \<C>_def comp_def)
  have Te: "(\<Sum>a\<in>\<E>. (if a = e then h ?ce else 0) * \<c> a) = h ?ce * \<c> e"
  proof -
    have "(\<Sum>a\<in>\<E>. (if a = e then h ?ce else 0) * \<c> a) = (\<Sum>a\<in>\<E>. if a = e then h ?ce * \<c> e else 0)"
      by (rule sum.cong) auto
    also have "... = h ?ce * \<c> e" using finite_E eE by (simp add: sum.delta)
    finally show ?thesis .
  qed
  have Tup: "(\<Sum>a\<in>\<E>. (\<Sum>w\<leftarrow>?up. if par_edge s w = a then h (?gup w) else 0) * \<c> a)
           = (\<Sum>w\<leftarrow>?up. \<c> (par_edge s w) * h (?gup w))"
  proof -
    have "(\<Sum>a\<in>\<E>. (\<Sum>w\<leftarrow>?up. if par_edge s w = a then h (?gup w) else 0) * \<c> a)
        = (\<Sum>a\<in>\<E>. (\<Sum>w\<leftarrow>?up. (if par_edge s w = a then h (?gup w) else 0) * \<c> a))"
      by (simp add: sum_list_mult_right)
    also have "... = (\<Sum>w\<leftarrow>?up. (\<Sum>a\<in>\<E>. (if par_edge s w = a then h (?gup w) else 0) * \<c> a))"
      by (rule sum_sum_list_swap[OF finite_E])
    also have "... = (\<Sum>w\<leftarrow>?up. \<c> (par_edge s w) * h (?gup w))"
    proof (rule arg_cong[where f=sum_list], rule map_cong[OF refl])
      fix w assume winup: "w \<in> set ?up"
      have peE: "par_edge s w \<in> \<E>" using winup upE by simp
      have "(\<Sum>a\<in>\<E>. (if par_edge s w = a then h (?gup w) else 0) * \<c> a)
          = (\<Sum>a\<in>\<E>. if a = par_edge s w then h (?gup w) * \<c> (par_edge s w) else 0)"
        by (rule sum.cong) auto
      also have "... = h (?gup w) * \<c> (par_edge s w)" using finite_E peE by (simp add: sum.delta)
      finally show "(\<Sum>a\<in>\<E>. (if par_edge s w = a then h (?gup w) else 0) * \<c> a) = \<c> (par_edge s w) * h (?gup w)"
        by (simp add: mult.commute)
    qed
    finally show ?thesis .
  qed
  have Tdn: "(\<Sum>a\<in>\<E>. (\<Sum>w\<leftarrow>?dn. if par_edge s w = a then h (?gdn w) else 0) * \<c> a)
           = (\<Sum>w\<leftarrow>?dn. \<c> (par_edge s w) * h (?gdn w))"
  proof -
    have "(\<Sum>a\<in>\<E>. (\<Sum>w\<leftarrow>?dn. if par_edge s w = a then h (?gdn w) else 0) * \<c> a)
        = (\<Sum>a\<in>\<E>. (\<Sum>w\<leftarrow>?dn. (if par_edge s w = a then h (?gdn w) else 0) * \<c> a))"
      by (simp add: sum_list_mult_right)
    also have "... = (\<Sum>w\<leftarrow>?dn. (\<Sum>a\<in>\<E>. (if par_edge s w = a then h (?gdn w) else 0) * \<c> a))"
      by (rule sum_sum_list_swap[OF finite_E])
    also have "... = (\<Sum>w\<leftarrow>?dn. \<c> (par_edge s w) * h (?gdn w))"
    proof (rule arg_cong[where f=sum_list], rule map_cong[OF refl])
      fix w assume windn: "w \<in> set ?dn"
      have peE: "par_edge s w \<in> \<E>" using windn dnE by simp
      have "(\<Sum>a\<in>\<E>. (if par_edge s w = a then h (?gdn w) else 0) * \<c> a)
          = (\<Sum>a\<in>\<E>. if a = par_edge s w then h (?gdn w) * \<c> (par_edge s w) else 0)"
        by (rule sum.cong) auto
      also have "... = h (?gdn w) * \<c> (par_edge s w)" using finite_E peE by (simp add: sum.delta)
      finally show "(\<Sum>a\<in>\<E>. (if par_edge s w = a then h (?gdn w) else 0) * \<c> a) = \<c> (par_edge s w) * h (?gdn w)"
        by (simp add: mult.commute)
    qed
    finally show ?thesis .
  qed
  have Csplit: "\<C> (h \<circ> flow_lookup ?f') = ns_flow_cost s + h ?ce * \<c> e
      + (\<Sum>w\<leftarrow>?up. \<c> (par_edge s w) * h (?gup w)) + (\<Sum>w\<leftarrow>?dn. \<c> (par_edge s w) * h (?gdn w))"
  proof -
    have "\<C> (h \<circ> flow_lookup ?f') = (\<Sum>a\<in>\<E>. h (flow_lookup ?f' a) * \<c> a)" by (simp add: \<C>_def comp_def)
    also have "... = (\<Sum>a\<in>\<E>. (h (flow_lookup (current_flow s) a) + (if a = e then h ?ce else 0)
          + (\<Sum>w\<leftarrow>?up. if par_edge s w = a then h (?gup w) else 0)
          + (\<Sum>w\<leftarrow>?dn. if par_edge s w = a then h (?gdn w) else 0)) * \<c> a)"
      using hfval by simp
    also have "... = (\<Sum>a\<in>\<E>. h (flow_lookup (current_flow s) a) * \<c> a)
        + (\<Sum>a\<in>\<E>. (if a = e then h ?ce else 0) * \<c> a)
        + (\<Sum>a\<in>\<E>. (\<Sum>w\<leftarrow>?up. if par_edge s w = a then h (?gup w) else 0) * \<c> a)
        + (\<Sum>a\<in>\<E>. (\<Sum>w\<leftarrow>?dn. if par_edge s w = a then h (?gdn w) else 0) * \<c> a)"
      by (simp add: sum.distrib distrib_right)
    also have "... = ns_flow_cost s + h ?ce * \<c> e
        + (\<Sum>w\<leftarrow>?up. \<c> (par_edge s w) * h (?gup w)) + (\<Sum>w\<leftarrow>?dn. \<c> (par_edge s w) * h (?gdn w))"
      using Tcf Te Tup Tdn by simp
    finally show ?thesis .
  qed
  show ?thesis
    unfolding augeq
  proof (cases in_U)
    case True
    have su: "(\<Sum>w\<leftarrow>?up. \<c> (par_edge s w) * h (?gup w)) = h \<delta> * (ns_pot_of s a0 - ns_pot_of s (fst e))"
      using up_cost_sum_h[OF inv w1 d1 p1V] True by simp
    have sd: "(\<Sum>w\<leftarrow>?dn. \<c> (par_edge s w) * h (?gdn w)) = h \<delta> * (ns_pot_of s (snd e) - ns_pot_of s a0)"
      using down_cost_sum_h[OF inv w2 d2 p2V] True by simp
    show "\<C> (h \<circ> flow_lookup ?f') = ns_flow_cost s + (if in_U then - h \<delta> else h \<delta>) * reduced_cost (potentials s) e"
      using Csplit su sd True by (simp add: reduced_cost_def algebra_simps)
  next
    case False
    have su: "(\<Sum>w\<leftarrow>?up. \<c> (par_edge s w) * h (?gup w)) = h \<delta> * (ns_pot_of s a0 - ns_pot_of s (snd e))"
      using up_cost_sum_h[OF inv w2 d2 p2V] False by simp
    have sd: "(\<Sum>w\<leftarrow>?dn. \<c> (par_edge s w) * h (?gdn w)) = h \<delta> * (ns_pot_of s (fst e) - ns_pot_of s a0)"
      using down_cost_sum_h[OF inv w1 d1 p1V] False by simp
    show "\<C> (h \<circ> flow_lookup ?f') = ns_flow_cost s + (if in_U then - h \<delta> else h \<delta>) * reduced_cost (potentials s) e"
      using Csplit su sd False by (simp add: reduced_cost_def algebra_simps)
  qed
qed

lemma augment_flow_props:
  assumes inv: "ns_invar s"
    and sel: "ns_select s = Some (e, in_U, \<gamma>, sel')"
    and pp:  "get_path_pair (spanning_tree s) (fst e) (snd e) = (p1, p2)"
    and bn:  "bottleneck s e in_U p1 p2 = (\<delta>, isf, lv, lfw, lus)"
    and dne: "\<delta> \<noteq> - 1"
  shows "flow_invar (augment_flow s e in_U \<delta> p1 p2)"
    and "(h \<circ> flow_lookup (augment_flow s e in_U \<delta> p1 p2)) is b flow"
    and "\<C> (h \<circ> flow_lookup (augment_flow s e in_U \<delta> p1 p2)) =
         ns_flow_cost s + (if in_U then - h \<delta> else h \<delta>) * reduced_cost (potentials s) e"
proof -
  show "flow_invar (augment_flow s e in_U \<delta> p1 p2)"
    using augment_flow_flow_invar[OF inv sel pp] .
  show "(h \<circ> flow_lookup (augment_flow s e in_U \<delta> p1 p2)) is b flow"
    using augment_flow_bflow[OF inv sel pp bn dne] .
  show "\<C> (h \<circ> flow_lookup (augment_flow s e in_U \<delta> p1 p2)) =
         ns_flow_cost s + (if in_U then - h \<delta> else h \<delta>) * reduced_cost (potentials s) e"
    using augment_flow_cost[OF inv sel pp bn dne] .
qed

text \<open>\<^bold>\<open>\S{}4.4 Shift set and cut\<close>. @{term shift_pot} adds @{term \<gamma>} (signed) over exactly the moved
      subtree \<open>S\<close> --- the component of @{term v} in \<open>(V, T - {e0})\<close>, which excludes @{term r}. Every tree
      edge other than \<open>e0\<close> has both ends on one side of the cut (its reduced cost is unchanged), \<open>e0\<close> is
      the unique old crossing edge, and @{term e} is the new crossing edge whose reduced cost the shift
      zeroes. Together with \<open>\<pi> r = 0\<close> preserved this is @{const ns_invar_pot_fits} for the pivot.\<close>

definition "ns_pot_sum s = (\<Sum> v \<in> \<V>. ns_pot_of s v)"

text \<open>Shift-set infrastructure: @{term shift_pot} folds @{term pot_upd} over the moved subtree \<open>S\<close>
      (via the @{term iterate_root_opposed} axiom), so it adds \<open>\<plusminus>\<gamma>\<close> to each vertex of \<open>S\<close> and leaves
      the rest untouched; membership of \<open>S\<close> is characterised by whether the pivot lies on a vertex's
      distinct walk to the root, which yields the cut property.\<close>

lemma foldr_pot_upd_invar:
  "(\<forall>x\<in>set xs. x \<in> \<V>) \<Longrightarrow> pot_invar acc \<Longrightarrow> pot_invar (foldr (\<lambda>x a. pot_upd a x (val a x)) xs acc)"
proof (induct xs)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  have xV: "x \<in> \<V>" using Cons.prems(1) by simp
  have restV: "\<forall>y\<in>set xs. y \<in> \<V>" using Cons.prems(1) by simp
  have "pot_invar (foldr (\<lambda>x a. pot_upd a x (val a x)) xs acc)"
    using Cons.hyps[OF restV Cons.prems(2)] .
  thus ?case using xV by (simp add: pot_arr.fixed_univ_map_upd_invar)
qed

lemma foldr_pot_upd_lookup:
  "distinct xs \<Longrightarrow> (\<forall>x\<in>set xs. x \<in> \<V>) \<Longrightarrow> pot_invar acc \<Longrightarrow>
   pot_lookup (foldr (\<lambda>x a. pot_upd a x (hop (pot_lookup a x))) xs acc)
     = (\<lambda>u. if u \<in> set xs then hop (pot_lookup acc u) else pot_lookup acc u)"
proof (induct xs)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  let ?f = "\<lambda>x a. pot_upd a x (hop (pot_lookup a x))"
  let ?a' = "foldr ?f xs acc"
  have dxs: "distinct xs" using Cons.prems(1) by simp
  have xni: "x \<notin> set xs" using Cons.prems(1) by simp
  have xV: "x \<in> \<V>" using Cons.prems(2) by simp
  have restV: "\<forall>y\<in>set xs. y \<in> \<V>" using Cons.prems(2) by simp
  have inv': "pot_invar ?a'" using restV Cons.prems(3) by (rule foldr_pot_upd_invar)
  have look_a': "pot_lookup ?a' = (\<lambda>u. if u \<in> set xs then hop (pot_lookup acc u) else pot_lookup acc u)"
    using Cons.hyps[OF dxs restV Cons.prems(3)] .
  have "pot_lookup (foldr ?f (x # xs) acc) = pot_lookup (pot_upd ?a' x (hop (pot_lookup ?a' x)))" by simp
  also have "... = (pot_lookup ?a')(x := hop (pot_lookup ?a' x))" using pot_arr.fixed_univ_map_upd[OF inv' xV] .
  also have "... = (\<lambda>u. if u \<in> set (x # xs) then hop (pot_lookup acc u) else pot_lookup acc u)"
    using look_a' xni by (auto simp: fun_eq_iff)
  finally show ?case .
qed

text \<open>Bridging rules: the conditional descriptor axioms, with the guard stated as @{const good_pot_val}.\<close>

lemma pot_plus_good:
  assumes "pot_value_invar p" "rcost_invar g"
    and "good_pot_val (pot_value_abstract p + rcost_abstract g)"
  shows "pot_value_abstract (pot_value_plus p g) = pot_value_abstract p + rcost_abstract g"
    and "pot_value_invar (pot_value_plus p g)"
  using pot_value_plus_spec[OF assms(1,2)] assms(3) by (auto simp: good_pot_val_def)

lemma pot_minus_good:
  assumes "pot_value_invar p" "rcost_invar g"
    and "good_pot_val (pot_value_abstract p - rcost_abstract g)"
  shows "pot_value_abstract (pot_value_minus p g) = pot_value_abstract p - rcost_abstract g"
    and "pot_value_invar (pot_value_minus p g)"
  using pot_value_minus_spec[OF assms(1,2)] assms(3) by (auto simp: good_pot_val_def)

lemma shift_pot_abstract:
  assumes inv: "ns_invar s" and vV: "v \<in> \<V>" and gi: "rcost_invar \<gamma>"
    and gd: "\<And>u. u \<in> {x. \<exists>p. walk_betw (abstract_arborescense (spanning_tree s)) x p r \<and> distinct p \<and> v \<in> set p}
              \<Longrightarrow> good_pot_val (if up then ns_pot_of s u + rcost_abstract \<gamma> else ns_pot_of s u - rcost_abstract \<gamma>)"
  shows "abstract_pot (shift_pot (spanning_tree s) v (potentials s) \<gamma> up) u
       = (if u \<in> {x. \<exists>p. walk_betw (abstract_arborescense (spanning_tree s)) x p r \<and> distinct p \<and> v \<in> set p}
          then (if up then ns_pot_of s u + rcost_abstract \<gamma> else ns_pot_of s u - rcost_abstract \<gamma>)
          else ns_pot_of s u)"
proof -
  let ?absT = "abstract_arborescense (spanning_tree s)"
  let ?S = "{x. \<exists>p. walk_betw ?absT x p r \<and> distinct p \<and> v \<in> set p}"
  let ?op = "if up then pot_value_plus else pot_value_minus"
  let ?h = "\<lambda>rr. ?op rr \<gamma>"
  let ?f = "\<lambda>x acc. pot_upd acc x (?h (pot_lookup acc x))"
  have arb: "arborescense_invar (spanning_tree s)" using ns_invar_implD(7)[OF ns_invarD(1)[OF inv]] .
  have potv: "pot_valid (potentials s)" using ns_invar_implD(2)[OF ns_invarD(1)[OF inv]] .
  have pinv: "pot_invar (potentials s)" using potv by (simp add: pot_valid_def)
  have vinvs: "\<And>u. u \<in> \<V> \<Longrightarrow> pot_value_invar (pot_lookup (potentials s) u)" using potv by (simp add: pot_valid_def)
  obtain xs where Sxs: "set xs = ?S" and dxs: "distinct xs"
    and foldeq: "shift_pot (spanning_tree s) v (potentials s) \<gamma> up = foldr ?f xs (potentials s)"
    using shift_pot_spec[OF arb vV pinv vinvs] by blast
  have SsubV: "?S \<subseteq> \<V>"
  proof
    fix x assume "x \<in> ?S"
    then obtain p where wp: "walk_betw ?absT x p r" by auto
    hence "x \<in> Vs ?absT" by (metis hd_in_set subsetD walk_betw_def walk_in_Vs)
    thus "x \<in> \<V>" using general(4)[OF arb] by simp
  qed
  have xsV: "\<forall>x\<in>set xs. x \<in> \<V>" using Sxs SsubV by auto
  have look: "pot_lookup (foldr ?f xs (potentials s))
       = (\<lambda>u. if u \<in> set xs then ?h (pot_lookup (potentials s) u) else pot_lookup (potentials s) u)"
    using foldr_pot_upd_lookup[OF dxs xsV pinv] .
  show ?thesis
  proof (cases "u \<in> ?S")
    case True
    hence uxs: "u \<in> set xs" using Sxs by simp
    have uV: "u \<in> \<V>" using True SsubV by auto
    have uvi: "pot_value_invar (pot_lookup (potentials s) u)" using potv uV by (simp add: pot_valid_def)
    have gdu: "good_pot_val (if up then ns_pot_of s u + rcost_abstract \<gamma> else ns_pot_of s u - rcost_abstract \<gamma>)"
      using gd[OF True] .
    have step: "pot_value_abstract (?h (pot_lookup (potentials s) u))
        = (if up then ns_pot_of s u + rcost_abstract \<gamma> else ns_pot_of s u - rcost_abstract \<gamma>)"
    proof (cases up)
      case True
      have g: "good_pot_val (pot_value_abstract (pot_lookup (potentials s) u) + rcost_abstract \<gamma>)"
        using gdu True by simp
      have "pot_value_abstract (pot_value_plus (pot_lookup (potentials s) u) \<gamma>)
          = pot_value_abstract (pot_lookup (potentials s) u) + rcost_abstract \<gamma>"
        using pot_plus_good(1)[OF uvi gi g] .
      thus ?thesis using True by simp
    next
      case False
      have g: "good_pot_val (pot_value_abstract (pot_lookup (potentials s) u) - rcost_abstract \<gamma>)"
        using gdu False by simp
      have "pot_value_abstract (pot_value_minus (pot_lookup (potentials s) u) \<gamma>)
          = pot_value_abstract (pot_lookup (potentials s) u) - rcost_abstract \<gamma>"
        using pot_minus_good(1)[OF uvi gi g] .
      thus ?thesis using False by simp
    qed
    have hu: "abstract_pot (shift_pot (spanning_tree s) v (potentials s) \<gamma> up) u
        = (if up then ns_pot_of s u + rcost_abstract \<gamma> else ns_pot_of s u - rcost_abstract \<gamma>)"
      unfolding foldeq by (simp add: look uxs step)
    show ?thesis unfolding if_P[OF True] by (rule hu)
  next
    case False
    hence uxs: "u \<notin> set xs" using Sxs by simp
    have hu: "abstract_pot (shift_pot (spanning_tree s) v (potentials s) \<gamma> up) u = ns_pot_of s u"
      unfolding foldeq by (simp add: look uxs)
    show ?thesis unfolding if_not_P[OF False] by (rule hu)
  qed
qed

lemma shift_pot_valid:
  assumes inv: "ns_invar s" and vV: "v \<in> \<V>" and gi: "rcost_invar \<gamma>"
    and gd: "\<And>u. u \<in> {x. \<exists>p. walk_betw (abstract_arborescense (spanning_tree s)) x p r \<and> distinct p \<and> v \<in> set p}
              \<Longrightarrow> good_pot_val (if up then ns_pot_of s u + rcost_abstract \<gamma> else ns_pot_of s u - rcost_abstract \<gamma>)"
  shows "pot_valid (shift_pot (spanning_tree s) v (potentials s) \<gamma> up)"
proof -
  let ?op = "if up then pot_value_plus else pot_value_minus"
  let ?h = "\<lambda>rr. ?op rr \<gamma>"
  let ?f = "\<lambda>x acc. pot_upd acc x (?h (pot_lookup acc x))"
  have arb: "arborescense_invar (spanning_tree s)" using ns_invar_implD(7)[OF ns_invarD(1)[OF inv]] .
  have potv: "pot_valid (potentials s)" using ns_invar_implD(2)[OF ns_invarD(1)[OF inv]] .
  have pinv: "pot_invar (potentials s)" using potv by (simp add: pot_valid_def)
  have vinvs: "\<And>u. u \<in> \<V> \<Longrightarrow> pot_value_invar (pot_lookup (potentials s) u)" using potv by (simp add: pot_valid_def)
  obtain xs where Sxs: "set xs = {x. \<exists>p. walk_betw (abstract_arborescense (spanning_tree s)) x p r \<and> distinct p \<and> v \<in> set p}"
    and dxs: "distinct xs"
    and foldeq: "shift_pot (spanning_tree s) v (potentials s) \<gamma> up = foldr ?f xs (potentials s)"
    using shift_pot_spec[OF arb vV pinv vinvs] by blast
  have xsV: "\<forall>x\<in>set xs. x \<in> \<V>"
  proof
    fix x assume "x \<in> set xs"
    then obtain p where wp: "walk_betw (abstract_arborescense (spanning_tree s)) x p r" using Sxs by auto
    hence "x \<in> Vs (abstract_arborescense (spanning_tree s))" by (metis hd_in_set subsetD walk_betw_def walk_in_Vs)
    thus "x \<in> \<V>" using general(4)[OF arb] by simp
  qed
  have pinv': "pot_invar (shift_pot (spanning_tree s) v (potentials s) \<gamma> up)" unfolding foldeq using xsV pinv by (rule foldr_pot_upd_invar)
  have look: "pot_lookup (foldr ?f xs (potentials s))
       = (\<lambda>u. if u \<in> set xs then ?h (pot_lookup (potentials s) u) else pot_lookup (potentials s) u)"
    using foldr_pot_upd_lookup[OF dxs xsV pinv] .
  have vinv: "\<forall>u\<in>\<V>. pot_value_invar (pot_lookup (shift_pot (spanning_tree s) v (potentials s) \<gamma> up) u)"
  proof
    fix u assume uV: "u \<in> \<V>"
    have uvi: "pot_value_invar (pot_lookup (potentials s) u)" using potv uV by (simp add: pot_valid_def)
    have look_u: "pot_lookup (shift_pot (spanning_tree s) v (potentials s) \<gamma> up) u = (if u \<in> set xs then ?h (pot_lookup (potentials s) u) else pot_lookup (potentials s) u)"
      unfolding foldeq using look by simp
    show "pot_value_invar (pot_lookup (shift_pot (spanning_tree s) v (potentials s) \<gamma> up) u)"
    proof (cases "u \<in> set xs")
      case notin: False
      show ?thesis using look_u notin uvi by simp
    next
      case isin: True
      hence uS: "u \<in> {x. \<exists>p. walk_betw (abstract_arborescense (spanning_tree s)) x p r \<and> distinct p \<and> v \<in> set p}"
        using Sxs by simp
      have gdu: "good_pot_val (if up then ns_pot_of s u + rcost_abstract \<gamma> else ns_pot_of s u - rcost_abstract \<gamma>)"
        using gd[OF uS] .
      have hinv: "pot_value_invar (?h (pot_lookup (potentials s) u))"
      proof (cases up)
        case True
        have g: "good_pot_val (pot_value_abstract (pot_lookup (potentials s) u) + rcost_abstract \<gamma>)"
          using gdu True by simp
        show ?thesis using pot_plus_good(2)[OF uvi gi g] True by simp
      next
        case False
        have g: "good_pot_val (pot_value_abstract (pot_lookup (potentials s) u) - rcost_abstract \<gamma>)"
          using gdu False by simp
        show ?thesis using pot_minus_good(2)[OF uvi gi g] False by simp
      qed
      show ?thesis using look_u isin hinv by simp
    qed
  qed
  show ?thesis using pinv' vinv by (simp add: pot_valid_def)
qed

lemma S_via_walk:
  assumes inv: "ns_invar s"
    and wx: "walk_betw (abstract_arborescense (spanning_tree s)) x W r"
    and dW: "distinct W"
  shows "(x \<in> {y. \<exists>p. walk_betw (abstract_arborescense (spanning_tree s)) y p r \<and> distinct p \<and> v \<in> set p})
         \<longleftrightarrow> v \<in> set W"
proof
  let ?absT = "abstract_arborescense (spanning_tree s)"
  have arb: "arborescense_invar (spanning_tree s)" using ns_invar_implD(7)[OF ns_invarD(1)[OF inv]] .
  have rV: "r \<in> \<V>" using general(1) .
  have xV: "x \<in> \<V>" using wx general(4)[OF arb] by (metis hd_in_set subsetD walk_betw_def walk_in_Vs)
  assume "x \<in> {y. \<exists>p. walk_betw ?absT y p r \<and> distinct p \<and> v \<in> set p}"
  then obtain p where wp: "walk_betw ?absT x p r" and dp: "distinct p" and vp: "v \<in> set p" by auto
  have "\<exists>!q. walk_betw ?absT x q r \<and> distinct q" using general(3)[OF arb rV xV] .
  hence "p = W" using wp dp wx dW by (metis (mono_tags, lifting))
  thus "v \<in> set W" using vp by simp
next
  let ?absT = "abstract_arborescense (spanning_tree s)"
  assume "v \<in> set W"
  thus "x \<in> {y. \<exists>p. walk_betw ?absT y p r \<and> distinct p \<and> v \<in> set p}"
    using wx dW by auto
qed

lemma cut_4c:
  assumes inv: "ns_invar s" and wV: "w \<in> \<V> - {r}" and wne: "w \<noteq> v"
  shows "(w \<in> {y. \<exists>p. walk_betw (abstract_arborescense (spanning_tree s)) y p r \<and> distinct p \<and> v \<in> set p})
       = (par_vx s w \<in> {y. \<exists>p. walk_betw (abstract_arborescense (spanning_tree s)) y p r \<and> distinct p \<and> v \<in> set p})"
proof -
  let ?absT = "abstract_arborescense (spanning_tree s)"
  let ?S = "{y. \<exists>p. walk_betw ?absT y p r \<and> distinct p \<and> v \<in> set p}"
  have tree: "ns_invar_tree s" using ns_invarD(7)[OF inv] .
  obtain q where q: "distinct (w # par_vx s w # q) \<and> walk_betw ?absT w (w # par_vx s w # q) r"
    using ns_invar_tree_walkD[OF tree wV] by blast
  have ww: "walk_betw ?absT w (w # par_vx s w # q) r" using q by simp
  have dw: "distinct (w # par_vx s w # q)" using q by simp
  have tailw: "walk_betw ?absT (par_vx s w) (par_vx s w # q) r" using ww by (metis walk_betw_cons)
  have dtail: "distinct (par_vx s w # q)" using dw by simp
  have "(w \<in> ?S) = (v \<in> set (w # par_vx s w # q))" using S_via_walk[OF inv ww dw] .
  also have "... = (v \<in> set (par_vx s w # q))" using wne by auto
  also have "... = (par_vx s w \<in> ?S)" using S_via_walk[OF inv tailw dtail] by simp
  finally show ?thesis .
qed

text \<open>A signed edge-cost sum given by two \<^emph>\<open>distinct\<close> edge lists (with at most one root edge across
      both) is admissible --- the packaging rule for @{const good_pot_val}.\<close>

lemma good_pot_valI_list:
  assumes "set Al \<subseteq> \<E>" "set Dl \<subseteq> \<E>" "distinct Al" "distinct Dl"
    and "card {e \<in> set Al \<union> set Dl. fst e = r \<or> snd e = r} \<le> 1"
    and "x = (\<Sum> e \<leftarrow> Al. \<c> e) - (\<Sum> e \<leftarrow> Dl. \<c> e)"
  shows "good_pot_val x"
  unfolding good_pot_val_def using assms
  by (intro exI[of _ "set Al"] exI[of _ "set Dl"]) (simp add: sum_list_distinct_conv_sum_set)


text \<open>\<^bold>\<open>\S{}4.3 \<open>swap_edge\<close> basis exchange\<close>. Instantiating the ADT axiom through \S{}4.1 and \S{}4.6:
      swapping the leaving edge @{term \<open>e0 = par_edge s v\<close>} for the entering edge @{term e} preserves
      \<open>arborescense_invar\<close> and realises the abstract exchange \<open>absT - {e0} \<union> {e}\<close>.\<close>

lemma swap_edge_pivot:
  assumes inv: "ns_invar s"
    and sel: "ns_select s = Some (e, in_U, \<gamma>, sel')"
    and pp:  "get_path_pair (spanning_tree s) (fst e) (snd e) = (p1, p2)"
    and bn:  "bottleneck s e in_U p1 p2 = (\<delta>, False, v, e0fwd, up_side)"
    and dne: "\<delta> \<noteq> - 1"
  shows "arborescense_invar
           (swap_edge (spanning_tree s) v
              (if in_U = up_side then fst e else snd e)
              (if in_U = up_side then snd e else fst e))"
    and "abstract_arborescense
           (swap_edge (spanning_tree s) v
              (if in_U = up_side then fst e else snd e)
              (if in_U = up_side then snd e else fst e))
         = abstract_arborescense (spanning_tree s)
             - {{fst (par_edge s v), snd (par_edge s v)}} \<union> {{fst e, snd e}}"
proof -
  let ?absT = "abstract_arborescense (spanning_tree s)"
  let ?u = "if in_U = up_side then fst e else snd e"
  let ?vax = "if in_U = up_side then snd e else fst e"
  let ?P = "if in_U = up_side then p1 else p2"
  have eE: "e \<in> \<E>" using ns_select_SomeD(2)[OF inv sel] .
  have arb: "arborescense_invar (spanning_tree s)"
    using ns_invar_implD(7)[OF ns_invarD(1)[OF inv]] .
  have neq: "fst e \<noteq> snd e" using entering_not_selfloop[OF inv sel] .
  have fV: "fst e \<in> \<V>" using fst_E_V[OF eE] .
  have sV: "snd e \<in> \<V>" using snd_E_V[OF eE] .
  have tree: "ns_invar_tree s" using ns_invarD(7)[OF inv] .
  obtain a p3 where
    w1: "walk_betw ?absT (fst e) (p1 @ a # p3) r" and
    w2: "walk_betw ?absT (snd e) (p2 @ a # p3) r" and
    d1: "distinct (p1 @ a # p3)" and d2: "distinct (p2 @ a # p3)" and
    disj: "set p1 \<inter> set p2 = {}"
    using get_path_pair(1)[OF arb pp neq fV sV] by blast
  have vP: "v \<in> set ?P" using bottleneck_pivot_facts(1)[OF inv sel pp bn] .
  have vVr: "v \<in> \<V> - {r}" using bottleneck_pivot_facts(2)[OF inv sel pp bn] .
  have wP: "walk_betw ?absT ?u (?P @ a # p3) r" using w1 w2 by (cases "in_U = up_side") simp_all
  have dP: "distinct (?P @ a # p3)" using d1 d2 by (cases "in_U = up_side") simp_all
  have remE: "{fst (par_edge s v), snd (par_edge s v)} = {v, par_vx s v}"
    using ns_invar_tree_dirD[OF tree vVr]
    by (cases "par_up s v") (auto simp add: par_vx_def)
  obtain j where jlen: "j < length ?P" and Pj: "?P ! j = v"
    using vP by (metis in_set_conv_nth)
  have SjW: "Suc j < length (?P @ a # p3)" using jlen by simp
  have Wj: "(?P @ a # p3) ! j = v" using jlen Pj by (simp add: nth_append)
  have Wjr: "(?P @ a # p3) ! j \<in> \<V> - {r}" using Wj vVr by simp
  have pv_succ: "par_vx s v = (?P @ a # p3) ! Suc j"
    using walk_succ_is_par_vx[OF inv wP dP SjW Wjr] Wj by simp
  have qlen: "Suc j < length (?P @ [a])" using jlen by simp
  have qj: "(?P @ [a]) ! j = v" using jlen Pj by (simp add: nth_append)
  have qcat: "?P @ a # p3 = (?P @ [a]) @ p3" by simp
  have qsucc: "(?P @ [a]) ! Suc j = par_vx s v"
    using pv_succ qlen by (metis nth_append qcat)
  have eidx: "edges_of_vwalk (?P @ [a]) ! j = (v, par_vx s v)"
    using edges_of_vwalk_index[OF qlen] qj qsucc by simp
  have jelen: "j < length (edges_of_vwalk (?P @ [a]))"
    using jlen by (simp add: edges_of_vwalk_length)
  have edgemem: "(v, par_vx s v) \<in> set (edges_of_vwalk (?P @ [a]))"
    using nth_mem[OF jelen] eidx by simp
  have GP: "get_path_pair (spanning_tree s) ?u ?vax = (?P, if in_U = up_side then p2 else p1)"
    using pp get_path_pair(2)[OF arb pp neq fV sV] by (cases "in_U = up_side") simp_all
  have neq': "?u \<noteq> ?vax" using neq by (cases "in_U = up_side") simp_all
  have uV: "?u \<in> \<V>" using fV sV by (cases "in_U = up_side") simp_all
  have vaxV: "?vax \<in> \<V>" using fV sV by (cases "in_U = up_side") simp_all
  have swap1: "arborescense_invar (swap_edge (spanning_tree s) v ?u ?vax)"
    using swap_edge(1)[OF arb GP neq' wP dP edgemem uV vaxV] .
  have swap2: "abstract_arborescense (swap_edge (spanning_tree s) v ?u ?vax) =
      abstract_arborescense (spanning_tree s) - {{v, par_vx s v}} \<union> {{?u, ?vax}}"
    using swap_edge(2)[OF arb GP neq' wP dP edgemem uV vaxV] .
  have uvaxE: "{?u, ?vax} = {fst e, snd e}" by (cases "in_U = up_side") auto
  show "arborescense_invar (swap_edge (spanning_tree s) v ?u ?vax)" using swap1 .
  show "abstract_arborescense (swap_edge (spanning_tree s) v ?u ?vax) =
      abstract_arborescense (spanning_tree s) - {{fst (par_edge s v), snd (par_edge s v)}} \<union> {{fst e, snd e}}"
    using swap2 by (simp only: remE uvaxE)
qed

text \<open>\<^bold>\<open>\S{}4.5 \<open>reparent\<close> correctness\<close>. Re-parenting reverses the spine \<open>hd P \<dots> v\<close>: off-spine
      vertices keep their parent data, spine vertices inherit their predecessor's old edge with flipped
      orientation, and the resulting parent/direction arrays project onto the new tree \<open>swap_edge \<dots>\<close>.
      Presented (with the result pair bound to @{term parr}, @{term darr}) as the two array invariants
      plus the global projection.\<close>

lemma reparent_walk_invar:
  "set ws \<subseteq> \<V> - {r} \<Longrightarrow>
   (case pd of (p0, d0) \<Rightarrow> parent_invar p0 \<and> dir_invar d0)
   \<Longrightarrow> (case reparent_walk s e v first pe pup ws pd of (p, d) \<Rightarrow> parent_invar p \<and> dir_invar d)"
proof (induction ws arbitrary: first pe pup pd)
  case Nil
  then show ?case by simp
next
  case (Cons w ws)
  have wV: "w \<in> \<V> - {r}" using Cons.prems(1) by simp
  have wsV: "set ws \<subseteq> \<V> - {r}" using Cons.prems(1) by simp
  obtain parr darr where pd: "pd = (parr, darr)" by (cases pd)
  from Cons.prems(2) pd have inv0: "parent_invar parr" "dir_invar darr" by auto
  show ?case
  proof (cases "w = v")
    case wv: True
    show ?thesis
    proof (cases first)
      case True
      have "reparent_walk s e v first pe pup (w # ws) pd = (parent_upd parr w e, dir_upd darr w (w = fst_exec e))"
        using pd True wv by simp
      then show ?thesis using inv0 wV
        by (simp add: parent_arr.fixed_univ_map_upd_invar dir_arr.fixed_univ_map_upd_invar)
    next
      case False
      have "reparent_walk s e v first pe pup (w # ws) pd
              = (parent_upd parr w pe, dir_upd darr w (\<not> pup))"
        using pd False wv by simp
      then show ?thesis using inv0 wV
        by (simp add: parent_arr.fixed_univ_map_upd_invar dir_arr.fixed_univ_map_upd_invar)
    qed
  next
    case wv: False
    show ?thesis
    proof (cases first)
      case True
      have rw: "reparent_walk s e v first pe pup (w # ws) pd
                  = reparent_walk s e v False (par_edge s w) (par_up s w) ws (parent_upd parr w e, dir_upd darr w (w = fst_exec e))"
        using pd True wv by simp
      have inv': "parent_invar (parent_upd parr w e) \<and> dir_invar (dir_upd darr w (w = fst_exec e))"
        using inv0 wV by (simp add: parent_arr.fixed_univ_map_upd_invar dir_arr.fixed_univ_map_upd_invar)
      show ?thesis
        using Cons.IH[OF wsV, of "(parent_upd parr w e, dir_upd darr w (w = fst_exec e))" False "par_edge s w" "par_up s w"] inv' rw by simp
    next
      case False
      have rw: "reparent_walk s e v first pe pup (w # ws) pd
                  = reparent_walk s e v False (par_edge s w) (par_up s w) ws (parent_upd parr w pe, dir_upd darr w (\<not> pup))"
        using pd False wv by simp
      have inv': "parent_invar (parent_upd parr w pe) \<and> dir_invar (dir_upd darr w (\<not> pup))"
        using inv0 wV by (simp add: parent_arr.fixed_univ_map_upd_invar dir_arr.fixed_univ_map_upd_invar)
      show ?thesis
        using Cons.IH[OF wsV, of "(parent_upd parr w pe, dir_upd darr w (\<not> pup))" False "par_edge s w" "par_up s w"] inv' rw by simp
    qed
  qed
qed

text \<open>\<^bold>\<open>Tree-edge injectivity.\<close> Distinct non-root vertices carry distinct undirected parent edges: the
      parent edge of @{term w} is @{term \<open>{w, par_vx s w}\<close>}, so a coincidence would force a two-cycle
      @{term \<open>w = par_vx s w'\<close>}, @{term \<open>w' = par_vx s w\<close>}, contradicting the uniqueness of simple walks.\<close>

lemma tree_edge_inj:
  assumes inv: "ns_invar s"
  shows "inj_on (\<lambda>w. {fst (par_edge s w), snd (par_edge s w)}) (\<V> - {r})"
proof (rule inj_onI)
  fix w w'
  assume wV: "w \<in> \<V> - {r}" and w'V: "w' \<in> \<V> - {r}"
    and eq: "{fst (par_edge s w), snd (par_edge s w)} = {fst (par_edge s w'), snd (par_edge s w')}"
  note tree = ns_invarD(7)[OF inv]
  have dirw: "if par_up s w then fst (par_edge s w) = w else snd (par_edge s w) = w"
    using ns_invar_tree_dirD[OF tree wV] .
  have dirw': "if par_up s w' then fst (par_edge s w') = w' else snd (par_edge s w') = w'"
    using ns_invar_tree_dirD[OF tree w'V] .
  have setw: "{fst (par_edge s w), snd (par_edge s w)} = {w, par_vx s w}"
    using dirw by (auto simp: par_vx_def split: if_splits)
  have setw': "{fst (par_edge s w'), snd (par_edge s w')} = {w', par_vx s w'}"
    using dirw' by (auto simp: par_vx_def split: if_splits)
  show "w = w'"
  proof (rule ccontr)
    assume ne: "w \<noteq> w'"
    have sets_eq: "{w, par_vx s w} = {w', par_vx s w'}" using eq setw setw' by simp
    have m1: "w' \<in> {w, par_vx s w}" using sets_eq by auto
    have pv: "par_vx s w = w'" using m1 ne by auto
    have m2: "w \<in> {w', par_vx s w'}" using sets_eq by auto
    have pv': "par_vx s w' = w" using m2 ne by auto
    obtain q where q: "distinct (w # w' # q)
                     \<and> walk_betw (abstract_arborescense (spanning_tree s)) w (w # w' # q) r"
      using ns_invar_tree_walkD[OF tree wV] unfolding pv by blast
    obtain q' where q': "distinct (w' # w # q')
                       \<and> walk_betw (abstract_arborescense (spanning_tree s)) w' (w' # w # q') r"
      using ns_invar_tree_walkD[OF tree w'V] unfolding pv' by blast
    have tail: "walk_betw (abstract_arborescense (spanning_tree s)) w' (w' # q) r"
      using q by (metis walk_betw_cons)
    have dtail: "distinct (w' # q)" using q by simp
    have arb: "arborescense_invar (spanning_tree s)"
      using ns_invar_implD(7)[OF ns_invarD(1)[OF inv]] .
    have rV: "r \<in> \<V>" using general(1) .
    have w'VV: "w' \<in> \<V>" using w'V by simp
    have uniq: "\<exists>!p. walk_betw (abstract_arborescense (spanning_tree s)) w' p r \<and> distinct p"
      using general(3)[OF arb rV w'VV] .
    have eqp: "w' # q = w' # w # q'" using uniq tail dtail q' by (metis (mono_tags, lifting))
    have "q = w # q'" using eqp by simp
    then have "distinct (w # w' # w # q')" using q by simp
    thus False by simp
  qed
qed

text \<open>\<^bold>\<open>\S{}4.5 pointwise re-parenting.\<close> Walking the spine, @{const reparent_walk} rewrites exactly the
      prefix up to @{term v}: off-spine parents are untouched, and the undirected edges over the spine
      collapse to the entering edge @{term e} (or the predecessor's edge) plus the predecessors' old
      edges --- the ownership shift by one vertex. Proved by induction on the walked list.\<close>

lemma reparent_walk_char:
  "\<lbrakk>distinct ws; v \<in> set ws; parent_invar parr0; set ws \<subseteq> \<V> - {r}\<rbrakk>
   \<Longrightarrow> (case reparent_walk s e v first pe pup ws (parr0, darr0) of (parr, darr) \<Rightarrow>
        (\<forall>x. x \<notin> insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ws)) \<longrightarrow> parent_lookup parr x = parent_lookup parr0 x)
       \<and> (\<lambda>w. {fst (parent_lookup parr w), snd (parent_lookup parr w)}) ` insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ws))
          = insert (if first then {fst e, snd e} else {fst pe, snd pe})
               ((\<lambda>w. {fst (par_edge s w), snd (par_edge s w)}) ` set (takeWhile (\<lambda>y. y \<noteq> v) ws)))"
proof (induction ws arbitrary: first pe pup parr0 darr0)
  case Nil
  then show ?case by simp
next
  case (Cons w ws')
  have dw: "distinct (w # ws')" and vin: "v \<in> set (w # ws')" and pinv: "parent_invar parr0"
    using Cons.prems by auto
  have wV: "w \<in> \<V> - {r}" using Cons.prems(4) by simp
  have wsV': "set ws' \<subseteq> \<V> - {r}" using Cons.prems(4) by simp
  define val_w where "val_w = (if first then e else pe)"
  define dval_w where "dval_w = (if first then (w = fst_exec e) else (\<not> pup))"
  have pinv': "parent_invar (parent_upd parr0 w val_w)"
    using pinv wV by (rule parent_arr.fixed_univ_map_upd_invar)
  have look_upd: "parent_lookup (parent_upd parr0 w val_w) = (parent_lookup parr0)(w := val_w)"
    using pinv wV by (rule parent_arr.fixed_univ_map_upd)
  have headval: "{fst val_w, snd val_w}
      = (if first then {fst e, snd e} else {fst pe, snd pe})"
    by (cases first) (simp_all add: val_w_def)
  show ?case
  proof (cases "w = v")
    case True
    have res: "reparent_walk s e v first pe pup (w # ws') (parr0, darr0) = (parent_upd parr0 w val_w, dir_upd darr0 w dval_w)"
      using True by (cases first) (simp_all add: val_w_def dval_w_def)
    have ins: "insert v (set (takeWhile (\<lambda>y. y \<noteq> v) (w # ws'))) = {v}" using True by simp
    have tw0: "set (takeWhile (\<lambda>y. y \<noteq> v) (w # ws')) = {}" using True by simp
    show ?thesis
      unfolding res prod.case
    proof (intro conjI allI impI)
      fix x assume "x \<notin> insert v (set (takeWhile (\<lambda>y. y \<noteq> v) (w # ws')))"
      hence "x \<noteq> v" using ins by simp
      thus "parent_lookup (parent_upd parr0 w val_w) x = parent_lookup parr0 x"
        using True look_upd by simp
    next
      show "(\<lambda>w'. {fst (parent_lookup (parent_upd parr0 w val_w) w'), snd (parent_lookup (parent_upd parr0 w val_w) w')}) ` insert v (set (takeWhile (\<lambda>y. y \<noteq> v) (w # ws')))
            = insert (if first then {fst e, snd e} else {fst pe, snd pe})
                 ((\<lambda>w'. {fst (par_edge s w'), snd (par_edge s w')}) ` set (takeWhile (\<lambda>y. y \<noteq> v) (w # ws')))"
        using True look_upd ins tw0 headval by simp
    qed
  next
    case False
    have res: "reparent_walk s e v first pe pup (w # ws') (parr0, darr0)
                 = reparent_walk s e v False (par_edge s w) (par_up s w) ws' (parent_upd parr0 w val_w, dir_upd darr0 w dval_w)"
      using False by (cases first) (simp_all add: val_w_def dval_w_def)
    have vin': "v \<in> set ws'" using vin False by simp
    have dw': "distinct ws'" using dw by simp
    have wns: "w \<notin> set ws'" using dw by simp
    have tw: "set (takeWhile (\<lambda>y. y \<noteq> v) (w # ws')) = insert w (set (takeWhile (\<lambda>y. y \<noteq> v) ws'))"
      using False by simp
    have twsub: "set (takeWhile (\<lambda>y. y \<noteq> v) ws') \<subseteq> set ws'" by (auto dest: set_takeWhileD)
    have wnotin: "w \<notin> insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ws'))"
      using wns twsub False by auto
    obtain parr darr where res2:
      "reparent_walk s e v False (par_edge s w) (par_up s w) ws' (parent_upd parr0 w val_w, dir_upd darr0 w dval_w) = (parr, darr)"
      by (cases "reparent_walk s e v False (par_edge s w) (par_up s w) ws' (parent_upd parr0 w val_w, dir_upd darr0 w dval_w)")
    have IH: "(\<forall>x. x \<notin> insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ws')) \<longrightarrow> parent_lookup parr x = parent_lookup (parent_upd parr0 w val_w) x)
            \<and> (\<lambda>w'. {fst (parent_lookup parr w'), snd (parent_lookup parr w')}) ` insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ws'))
               = insert {fst (par_edge s w), snd (par_edge s w)}
                    ((\<lambda>w'. {fst (par_edge s w'), snd (par_edge s w')}) ` set (takeWhile (\<lambda>y. y \<noteq> v) ws'))"
      using Cons.IH[OF dw' vin' pinv' wsV', of False "par_edge s w" "par_up s w" "dir_upd darr0 w dval_w"]
      unfolding res2 prod.case by simp
    have IH1: "\<forall>x. x \<notin> insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ws')) \<longrightarrow> parent_lookup parr x = parent_lookup (parent_upd parr0 w val_w) x"
      using IH by (rule conjunct1)
    have IH2: "(\<lambda>w'. {fst (parent_lookup parr w'), snd (parent_lookup parr w')}) ` insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ws'))
               = insert {fst (par_edge s w), snd (par_edge s w)}
                    ((\<lambda>w'. {fst (par_edge s w'), snd (par_edge s w')}) ` set (takeWhile (\<lambda>y. y \<noteq> v) ws'))"
      using IH by (rule conjunct2)
    have plw: "parent_lookup parr w = val_w"
      using IH1[rule_format, OF wnotin] look_upd by simp
    show ?thesis
      unfolding res res2 prod.case
    proof (intro conjI allI impI)
      fix x assume A: "x \<notin> insert v (set (takeWhile (\<lambda>y. y \<noteq> v) (w # ws')))"
      have A2: "x \<notin> insert v (insert w (set (takeWhile (\<lambda>y. y \<noteq> v) ws')))" using A[unfolded tw] .
      have xw: "x \<noteq> w" using A2 by simp
      have xni: "x \<notin> insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ws'))" using A2 by simp
      have "parent_lookup parr x = parent_lookup (parent_upd parr0 w val_w) x"
        using IH1[rule_format, OF xni] .
      thus "parent_lookup parr x = parent_lookup parr0 x" using xw look_upd by simp
    next
      have "(\<lambda>w'. {fst (parent_lookup parr w'), snd (parent_lookup parr w')}) ` insert v (set (takeWhile (\<lambda>y. y \<noteq> v) (w # ws')))
          = (\<lambda>w'. {fst (parent_lookup parr w'), snd (parent_lookup parr w')}) ` insert w (insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ws')))"
        by (simp only: tw insert_commute)
      also have "... = insert {fst (parent_lookup parr w), snd (parent_lookup parr w)}
               ((\<lambda>w'. {fst (parent_lookup parr w'), snd (parent_lookup parr w')}) ` insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ws')))"
        by (simp only: image_insert)
      also have "... = insert {fst val_w, snd val_w}
               (insert {fst (par_edge s w), snd (par_edge s w)}
                  ((\<lambda>w'. {fst (par_edge s w'), snd (par_edge s w')}) ` set (takeWhile (\<lambda>y. y \<noteq> v) ws')))"
        by (simp only: plw IH2)
      also have "... = insert (if first then {fst e, snd e} else {fst pe, snd pe})
               ((\<lambda>w'. {fst (par_edge s w'), snd (par_edge s w')}) ` set (takeWhile (\<lambda>y. y \<noteq> v) (w # ws')))"
        by (simp only: headval tw image_insert)
      finally show "(\<lambda>w. {fst (parent_lookup parr w), snd (parent_lookup parr w)}) ` insert v (set (takeWhile (\<lambda>y. y \<noteq> v) (w # ws')))
          = insert (if first then {fst e, snd e} else {fst pe, snd pe})
               ((\<lambda>w. {fst (par_edge s w), snd (par_edge s w)}) ` set (takeWhile (\<lambda>y. y \<noteq> v) (w # ws')))" .
    qed
  qed
qed

text \<open>\<^bold>\<open>Abstract admissibility (\S{}4.4b).\<close> The reusable core, purely on the abstract layer (edge set
      \<open>T\<close>, real potential \<open>\<pi>\<close>): for \<^emph>\<open>any\<close> spanning-tree partition and any potential fitting it, every
      vertex potential \<open>\<pi> v\<close> is the signed cost-sum along \<open>v\<close>'s (distinct) tree path to \<open>r\<close> --- telescoped
      via \<open>zt\<close> over the walk's consecutive pairs, each mapped to its unique directed tree edge (\<open>de\<close>) ---
      and the only path edge touching \<open>r\<close> is the first, so \<open>\<pi> v\<close> is @{const good_pot_val}.\<close>

lemma potential_fits_imp_good:
  assumes Tsub: "T \<subseteq> \<E>"
    and gaT0: "graph_abs ((\<lambda> e. {fst e, snd e}) ` T)"
    and arbT0: "graph_abs.arborescence ((\<lambda> e. {fst e, snd e}) ` T) r ((\<lambda> e. {fst e, snd e}) ` T)"
    and VsGT: "dVs (make_pair ` T) = \<V>"
    and fit: "potential_fits_spanning_tree_partition r T \<pi>" and vV: "v \<in> \<V>"
  shows "good_pot_val (\<pi> v)"
proof -
  define GT where "GT = (\<lambda> e. {fst e, snd e}) ` T"
  have gaT: "graph_abs GT" using gaT0 by (simp add: GT_def)
  have arbT: "graph_abs.arborescence GT r GT" using arbT0 by (simp add: GT_def)
  have piR: "\<pi> r = 0" and edgeq: "\<And>e. e \<in> T \<Longrightarrow> \<c> e + \<pi> (fst e) - \<pi> (snd e) = 0"
    using fit by (auto simp add: potential_fits_spanning_tree_partition_def)
  have VsGTeq: "Vs GT = \<V>"
  proof -
    have "Vs GT = \<Union> {{fst e, snd e} | e. e \<in> T}" by (auto simp add: GT_def Vs_def)
    also have "\<dots> = dVs (make_pair ` T)" by (auto simp add: dVs_def make_pair_def)
    finally show ?thesis using VsGT by simp
  qed
  have GTne: "GT \<noteq> {}" using vV VsGTeq by (auto simp add: Vs_def)
  have VsGT_arb: "Vs GT = connected_component GT r" using graph_abs.arborescenceD(2)[OF gaT arbT GTne] by simp
  have rVs: "r \<in> Vs GT" using VsGT_arb in_own_connected_component by auto
  have vcc: "v \<in> connected_component GT r" using vV VsGTeq VsGT_arb by simp
  show ?thesis
  proof (cases "v = r")
    case True
    show ?thesis using piR True by (intro good_pot_valI_list[where Al="[]" and Dl="[]"]) auto
  next
    case False
    have rneqv: "r \<noteq> v" using False by simp
    obtain p0 where walk0: "walk_betw GT r p0 v" using in_connected_component_has_walk[OF vcc rVs] by blast
    obtain p where walkp: "walk_betw GT r p v" and dp: "distinct p"
      using walk_betw_different_verts_to_ditinct[OF walk0 rneqv] by blast
    have zt: "(\<Sum> (x,y)\<leftarrow>zip xs (tl xs). \<pi> y - \<pi> x) = (if xs = [] then 0 else \<pi> (last xs) - \<pi> (hd xs))" for xs
    proof (induct xs rule: induct_list012)
      case nil show ?case by simp
    next
      case (single x) show ?case by simp
    next
      case (sucsuc x y zs)
      have "(\<Sum> (a,b)\<leftarrow>zip (x # y # zs) (tl (x # y # zs)). \<pi> b - \<pi> a) = (\<pi> y - \<pi> x) + (\<Sum> (a,b)\<leftarrow>zip (y # zs) (tl (y # zs)). \<pi> b - \<pi> a)" by simp
      also have "... = (\<pi> y - \<pi> x) + (\<pi> (last (y # zs)) - \<pi> (hd (y # zs)))" using sucsuc by simp
      also have "... = \<pi> (last (x # y # zs)) - \<pi> (hd (x # y # zs))" by simp
      finally show ?case by simp
    qed
    have pne: "p \<noteq> []" using walkp by (auto simp: walk_betw_def)
    have hd_p: "hd p = r" using walkp by (simp add: walk_betw_def)
    have last_p: "last p = v" using walkp by (simp add: walk_betw_def)
    have sumpi: "(\<Sum> (x,y)\<leftarrow>zip p (tl p). \<pi> y - \<pi> x) = \<pi> v" using zt[of p] pne hd_p last_p piR by simp
    have pathp: "path GT p" using walkp by (simp add: walk_between_nonempty_pathD(1))
    have edgesGT: "set (edges_of_path p) \<subseteq> GT" using pathp by (rule path_edges_subset)
    have zip_eop: "(a,b) \<in> set (zip ys (tl ys)) \<Longrightarrow> {a, b} \<in> set (edges_of_path ys)" for a b ys
    proof (induct ys rule: edges_of_path.induct)
      case 1 then show ?case by simp
    next
      case (2 x) then show ?case by simp
    next
      case (3 x y zs) thus ?case by auto
    qed
    have keypair: "\<And>x y. (x,y) \<in> set (zip p (tl p)) \<Longrightarrow> \<exists>e. e \<in> T \<and> {fst e, snd e} = {x,y} \<and> \<pi> y - \<pi> x = (if fst e = x then \<c> e else - \<c> e)"
    proof -
      fix x y assume mem: "(x,y) \<in> set (zip p (tl p))"
      have xyGT: "{x,y} \<in> GT" using zip_eop[OF mem] edgesGT by auto
      then obtain e where eT: "e \<in> T" and exy: "{fst e, snd e} = {x,y}" by (auto simp: GT_def)
      have eE: "e \<in> \<E>" using eT Tsub by auto
      have rc: "\<c> e + \<pi> (fst e) - \<pi> (snd e) = 0" using edgeq[OF eT] .
      have neq: "fst e \<noteq> snd e"
      proof
        assume sl2: "fst e = snd e"
        have "{fst e} \<in> (\<lambda>e. {fst e, snd e}) ` T"
          by (rule image_eqI[OF _ eT]) (simp add: sl2)
        thus False using singleton_not_dblton[OF graph_abs.dblton_E[OF gaT0]] by blast
      qed
      have cases2: "(fst e = x \<and> snd e = y) \<or> (fst e = y \<and> snd e = x)" using exy by (metis doubleton_eq_iff)
      show "\<exists>e. e \<in> T \<and> {fst e, snd e} = {x,y} \<and> \<pi> y - \<pi> x = (if fst e = x then \<c> e else - \<c> e)"
        using cases2 eT exy rc neq by (elim disjE) auto
    qed
    define de where "de = (\<lambda>x y. SOME e. e \<in> T \<and> {fst e, snd e} = {x,y} \<and> \<pi> y - \<pi> x = (if fst e = x then \<c> e else - \<c> e))"
    have deP: "\<And>x y. (x,y) \<in> set (zip p (tl p)) \<Longrightarrow> de x y \<in> T \<and> {fst (de x y), snd (de x y)} = {x,y} \<and> \<pi> y - \<pi> x = (if fst (de x y) = x then \<c> (de x y) else - \<c> (de x y))"
    proof -
      fix x y assume "(x,y) \<in> set (zip p (tl p))"
      from someI_ex[OF keypair[OF this]] show "de x y \<in> T \<and> {fst (de x y), snd (de x y)} = {x,y} \<and> \<pi> y - \<pi> x = (if fst (de x y) = x then \<c> (de x y) else - \<c> (de x y))" unfolding de_def .
    qed
    define pairs where "pairs = zip p (tl p)"
    define Al where "Al = map (\<lambda>(x,y). de x y) (filter (\<lambda>(x,y). fst (de x y) = x) pairs)"
    define Dl where "Dl = map (\<lambda>(x,y). de x y) (filter (\<lambda>(x,y). fst (de x y) \<noteq> x) pairs)"
    have gs: "(\<Sum>(x,y)\<leftarrow>zs. (if fst (de x y) = x then \<c> (de x y) else - \<c> (de x y))) = (\<Sum>(x,y)\<leftarrow>filter (\<lambda>(x,y). fst (de x y) = x) zs. \<c> (de x y)) - (\<Sum>(x,y)\<leftarrow>filter (\<lambda>(x,y). fst (de x y) \<noteq> x) zs. \<c> (de x y))" for zs
      by (induct zs) (auto simp: algebra_simps split: prod.split)
    have sum_rw: "(\<Sum>(x,y)\<leftarrow>pairs. (\<pi> y - \<pi> x)) = (\<Sum>(x,y)\<leftarrow>pairs. (if fst (de x y) = x then \<c> (de x y) else - \<c> (de x y)))"
      by (intro arg_cong[where f=sum_list] map_cong[OF refl]) (auto simp: pairs_def split: prod.split dest: deP)
    have pv_pairs: "\<pi> v = (\<Sum>(x,y)\<leftarrow>pairs. (\<pi> y - \<pi> x))" using sumpi by (simp add: pairs_def)
    have Al_sum: "(\<Sum> e\<leftarrow>Al. \<c> e) = (\<Sum>(x,y)\<leftarrow>filter (\<lambda>(x,y). fst (de x y) = x) pairs. \<c> (de x y))" unfolding Al_def by (simp add: comp_def split_def)
    have Dl_sum: "(\<Sum> e\<leftarrow>Dl. \<c> e) = (\<Sum>(x,y)\<leftarrow>filter (\<lambda>(x,y). fst (de x y) \<noteq> x) pairs. \<c> (de x y))" unfolding Dl_def by (simp add: comp_def split_def)
    have eq1: "\<pi> v = (\<Sum> e\<leftarrow>Al. \<c> e) - (\<Sum> e\<leftarrow>Dl. \<c> e)" using pv_pairs sum_rw gs[of pairs] Al_sum Dl_sum by simp
    have de_T: "\<And>x y. (x,y) \<in> set pairs \<Longrightarrow> de x y \<in> T" using deP by (auto simp: pairs_def)
    have Al_E: "set Al \<subseteq> \<E>" unfolding Al_def using de_T Tsub by (auto simp: split_def)
    have Dl_E: "set Dl \<subseteq> \<E>" unfolding Dl_def using de_T Tsub by (auto simp: split_def)
    have dpairs: "distinct pairs" unfolding pairs_def using dp by (rule distinct_zipI1)
    have de_inj: "\<And>x y x' y'. (x,y) \<in> set pairs \<Longrightarrow> (x',y') \<in> set pairs \<Longrightarrow> de x y = de x' y' \<Longrightarrow> {x,y} = {x',y'}"
    proof -
      fix x y x' y' assume a1: "(x,y) \<in> set pairs" and a2: "(x',y') \<in> set pairs" and a3: "de x y = de x' y'"
      have "{fst (de x y), snd (de x y)} = {x,y}" using deP[OF a1[unfolded pairs_def]] by simp
      moreover have "{fst (de x' y'), snd (de x' y')} = {x',y'}" using deP[OF a2[unfolded pairs_def]] by simp
      ultimately show "{x,y} = {x',y'}" using a3 by simp
    qed
    have dedp: "distinct (edges_of_path p)" using dp by (rule distinct_edges_of_vpath)
    have eop_gen: "edges_of_path xs = map (\<lambda>(x,y). {x,y}) (zip xs (tl xs))" for xs by (induct xs rule: edges_of_path.induct) auto
    have eop_map: "edges_of_path p = map (\<lambda>(x,y). {x,y}) pairs" using eop_gen[of p] by (simp add: pairs_def)
    have pairs_inj: "inj_on (\<lambda>(x,y). {x,y}) (set pairs)" using dedp[unfolded eop_map] by (simp add: distinct_map)
    have de_map_inj: "inj_on (\<lambda>(x,y). de x y) (set pairs)"
    proof (rule inj_onI)
      fix z z' assume A1: "z \<in> set pairs" and A2: "z' \<in> set pairs" and A3: "(case z of (x,y) \<Rightarrow> de x y) = (case z' of (x,y) \<Rightarrow> de x y)"
      obtain x y where z: "z = (x,y)" by fastforce
      obtain x' y' where z': "z' = (x',y')" by fastforce
      have deq: "de x y = de x' y'" using A3 z z' by simp
      hence "{x,y} = {x',y'}" using de_inj[OF A1[unfolded z] A2[unfolded z']] by simp
      hence "(\<lambda>(x,y). {x,y}) z = (\<lambda>(x,y). {x,y}) z'" using z z' by simp
      thus "z = z'" using pairs_inj A1 A2 by (auto simp: inj_on_def)
    qed
    have s_fil_A: "set (filter (\<lambda>(x,y). fst (de x y) = x) pairs) \<subseteq> set pairs" by auto
    have s_fil_D: "set (filter (\<lambda>(x,y). fst (de x y) \<noteq> x) pairs) \<subseteq> set pairs" by auto
    have dAl: "distinct Al" unfolding Al_def using dpairs inj_on_subset[OF de_map_inj s_fil_A] by (simp add: distinct_map distinct_filter)
    have dDl: "distinct Dl" unfolding Dl_def using dpairs inj_on_subset[OF de_map_inj s_fil_D] by (simp add: distinct_map distinct_filter)
    have hdp0: "p ! 0 = r" using hd_p pne by (simp add: hd_conv_nth)
    have rootpair: "\<And>x y. (x,y) \<in> set pairs \<Longrightarrow> r \<in> {x,y} \<Longrightarrow> (x,y) = (hd p, hd (tl p))"
    proof -
      fix x y assume mem: "(x,y) \<in> set pairs" and rxy: "r \<in> {x,y}"
      from mem[unfolded pairs_def] obtain i where iP: "i < length p" and itl: "i < length (tl p)" and xi: "p ! i = x" and yi: "tl p ! i = y" by (auto simp: in_set_zip)
      have yi': "p ! Suc i = y" using yi itl by (simp add: nth_tl)
      have SiP: "Suc i < length p" using itl by simp
      have plen: "0 < length p" using pne by auto
      have tlne: "tl p \<noteq> []" using itl by (cases p) auto
      from rxy have "x = r \<or> y = r" by auto
      thus "(x,y) = (hd p, hd (tl p))"
      proof
        assume "x = r"
        hence "p ! i = p ! 0" using xi hdp0 by simp
        hence i0: "i = 0" using dp iP plen nth_eq_iff_index_eq by blast
        have "x = hd p" using xi i0 hdp0 hd_p by simp
        moreover have "y = hd (tl p)" using yi' i0 tlne by (metis One_nat_def hd_conv_nth length_greater_0_conv nth_tl)
        ultimately show ?thesis by simp
      next
        assume "y = r"
        hence "p ! Suc i = p ! 0" using yi' hdp0 by simp
        hence "Suc i = 0" using dp SiP plen nth_eq_iff_index_eq by blast
        thus ?thesis by simp
      qed
    qed
    have AlDlU: "set Al \<union> set Dl = (\<lambda>(x,y). de x y) ` set pairs" unfolding Al_def Dl_def by (auto simp: split_def)
    have rootedges: "{e \<in> set Al \<union> set Dl. fst e = r \<or> snd e = r} \<subseteq> {de (hd p) (hd (tl p))}"
    proof
      fix e assume "e \<in> {e \<in> set Al \<union> set Dl. fst e = r \<or> snd e = r}"
      hence eU: "e \<in> set Al \<union> set Dl" and rte: "fst e = r \<or> snd e = r" by auto
      obtain x y where mem: "(x,y) \<in> set pairs" and eeq: "e = de x y" using eU AlDlU by auto
      have "{fst (de x y), snd (de x y)} = {x,y}" using deP[OF mem[unfolded pairs_def]] by simp
      hence "r \<in> {x,y}" using rte eeq by auto
      hence "(x,y) = (hd p, hd (tl p))" using rootpair[OF mem] by simp
      thus "e \<in> {de (hd p) (hd (tl p))}" using eeq by auto
    qed
    have cardle: "card {e \<in> set Al \<union> set Dl. fst e = r \<or> snd e = r} \<le> 1"
    proof -
      have "card {e \<in> set Al \<union> set Dl. fst e = r \<or> snd e = r} \<le> card {de (hd p) (hd (tl p))}" by (rule card_mono[OF _ rootedges]) simp
      also have "... = 1" by simp
      finally show ?thesis .
    qed
    show ?thesis using good_pot_valI_list[OF Al_E Dl_E dAl dDl cardle eq1] .
  qed
qed

text \<open>\<^bold>\<open>New potential fits the new tree (\S{}4.4c, abstract).\<close> The \<^emph>\<open>explicit real\<close> potential
      \<open>\<lambda>u. ns_pot_of s u + (if u\<in>S then \<plusminus>\<gamma> else 0)\<close> fits the pivoted tree \<open>T - {e0} \<union> {e}\<close> --- this is the
      \<open>shift_pot_props\<close> cut argument (\<open>cut_4c\<close>, \<open>crosse\<close>) on the plain mathematical function, so
      the \<open>abschar\<close> step is definitional and no \<open>shift_pot\<close> / descriptor is involved.\<close>

lemma expl_fits:
  assumes inv: "ns_invar s" and sel: "ns_select s = Some (e, in_U, \<gamma>, sel')" and pp: "get_path_pair (spanning_tree s) (fst e) (snd e) = (p1, p2)" and bn: "bottleneck s e in_U p1 p2 = (\<delta>, False, v, e0fwd, up_side)" and dne: "\<delta> \<noteq> - 1"
  shows "potential_fits_spanning_tree_partition r (ns_tree_edges s - {par_edge s v} \<union> {e}) (\<lambda>u. ns_pot_of s u + (if u \<in> {x. \<exists>p. walk_betw (abstract_arborescense (spanning_tree s)) x p r \<and> distinct p \<and> v \<in> set p} then (if in_U \<noteq> up_side then rcost_abstract \<gamma> else - rcost_abstract \<gamma>) else 0))"
proof -
  let ?absT = "abstract_arborescense (spanning_tree s)"
  let ?S = "{x. \<exists>p. walk_betw ?absT x p r \<and> distinct p \<and> v \<in> set p}"
  let ?up = "in_U \<noteq> up_side"
  let ?pv = "rcost_abstract \<gamma>"
  let ?dp = "if in_U \<noteq> up_side then ?pv else - ?pv"
  let ?pi = "\<lambda>u. ns_pot_of s u + (if u \<in> ?S then ?dp else 0)"
  have eE: "e \<in> \<E>" using ns_select_SomeD(2)[OF inv sel] .
  have neq: "fst e \<noteq> snd e" using entering_not_selfloop[OF inv sel] .
  have fV: "fst e \<in> \<V>" using fst_E_V[OF eE] .
  have sV: "snd e \<in> \<V>" using snd_E_V[OF eE] .
  have arb: "arborescense_invar (spanning_tree s)" using ns_invar_implD(7)[OF ns_invarD(1)[OF inv]] .
  have tree: "ns_invar_tree s" using ns_invarD(7)[OF inv] .
  have vVr: "v \<in> \<V> - {r}" using bottleneck_pivot_facts(2)[OF inv sel pp bn] .
  have vV: "v \<in> \<V>" using vVr by simp
  have vP: "v \<in> set (if in_U = up_side then p1 else p2)" using bottleneck_pivot_facts(1)[OF inv sel pp bn] .
  have precond: "selection_precond (edge_sel s) (potentials s) (edge_state s)"
    using ns_invar_implD(6)[OF ns_invarD(1)[OF inv]] ns_invar_implD(2)[OF ns_invarD(1)[OF inv]] ns_invar_implD(5)[OF ns_invarD(1)[OF inv]]
          ns_invar_pot_fitsD[OF ns_invarD(5)[OF inv]]
    by (simp add: selection_precond_def potential_fits_spanning_tree_partition_def)
  have selS: "sel_select (edge_sel s) (potentials s) (edge_state s) = Some (e, in_U, \<gamma>, sel')" using sel by (simp add: ns_select_def)
  have gi: "rcost_invar \<gamma>" using sel_select_SomeD(2)[OF precond selS] .
  have rc_eq: "?pv = reduced_cost (potentials s) e" using sel_select_SomeD(3)[OF precond selS] .
  have pf: "potential_fits_spanning_tree_partition r (ns_tree_edges s) (ns_pot_of s)" using ns_invar_pot_fitsD[OF ns_invarD(5)[OF inv]] .
  have pir0: "ns_pot_of s r = 0" using pf by (simp add: potential_fits_spanning_tree_partition_def)
  have treerc: "\<And>t. t \<in> ns_tree_edges s \<Longrightarrow> \<c> t + ns_pot_of s (fst t) - ns_pot_of s (snd t) = 0" using pf by (auto simp: potential_fits_spanning_tree_partition_def)
  obtain a p3 where w1: "walk_betw ?absT (fst e) (p1 @ a # p3) r" and w2: "walk_betw ?absT (snd e) (p2 @ a # p3) r" and d1: "distinct (p1 @ a # p3)" and d2: "distinct (p2 @ a # p3)" and disj: "set p1 \<inter> set p2 = {}"
    using get_path_pair(1)[OF arb pp neq fV sV] by blast
  have rV: "r \<in> \<V>" using general(1) .
  have rinVs: "r \<in> Vs ?absT" using rV general(4)[OF arb] by simp
  have rwalk: "walk_betw ?absT r [r] r" using rinVs by (rule walk_reflexive)
  have rnotS: "r \<notin> ?S"
  proof
    assume "r \<in> ?S"
    then obtain p where wp: "walk_betw ?absT r p r" and dp: "distinct p" and vp: "v \<in> set p" by auto
    have "\<exists>!q. walk_betw ?absT r q r \<and> distinct q" using general(3)[OF arb rV rV] .
    hence "p = [r]" using wp dp rwalk by (metis (mono_tags, lifting) distinct_singleton)
    thus False using vp vVr by simp
  qed
  have vp1: "(v \<in> set (p1 @ a # p3)) = (in_U = up_side)"
  proof (cases "in_U = up_side")
    case True hence "v \<in> set p1" using vP by simp thus ?thesis using True by simp
  next
    case False hence vin2: "v \<in> set p2" using vP by simp
    have "v \<notin> set p1" using vin2 disj by auto
    moreover have "v \<notin> set (a # p3)" using vin2 d2 by (auto simp: distinct_append)
    ultimately show ?thesis using False by auto
  qed
  have vp2: "(v \<in> set (p2 @ a # p3)) = (in_U \<noteq> up_side)"
  proof (cases "in_U = up_side")
    case True hence vin1: "v \<in> set p1" using vP by simp
    have "v \<notin> set p2" using vin1 disj by auto
    moreover have "v \<notin> set (a # p3)" using vin1 d1 by (auto simp: distinct_append)
    ultimately show ?thesis using True by auto
  next
    case False hence "v \<in> set p2" using vP by simp thus ?thesis using False by simp
  qed
  have fstS: "(fst e \<in> ?S) = (in_U = up_side)" using S_via_walk[OF inv w1 d1] vp1 by simp
  have sndS: "(snd e \<in> ?S) = (in_U \<noteq> up_side)" using S_via_walk[OF inv w2 d2] vp2 by simp
  have crosse: "(if fst e \<in> ?S then ?dp else 0) - (if snd e \<in> ?S then ?dp else 0) = - ?pv"
    unfolding fstS sndS by (cases "in_U = up_side") simp_all
  have ifr0: "(if r \<in> ?S then ?dp else 0) = 0" by (rule if_not_P[OF rnotS])
  have pirE: "?pi r = 0" using ifr0 pir0 by simp
  define pd where "pd = ?pi"
  have abschar2: "\<And>u. pd u = ns_pot_of s u + (if u \<in> ?S then ?dp else 0)" by (simp add: pd_def)
  have pdrE: "pd r = 0" using pirE by (simp add: pd_def)
  have pdfits: "potential_fits_spanning_tree_partition r (ns_tree_edges s - {par_edge s v} \<union> {e}) pd"
    unfolding potential_fits_spanning_tree_partition_def
  proof (intro conjI ballI)
    show "pd r = 0" using pdrE .
  next
    fix t assume tin: "t \<in> ns_tree_edges s - {par_edge s v} \<union> {e}"
    consider (E) "t = e" | (T) "t \<in> ns_tree_edges s" "t \<noteq> par_edge s v" using tin by auto
    thus "\<c> t + pd (fst t) - pd (snd t) = 0"
    proof cases
      case E
      have "\<c> t + pd (fst t) - pd (snd t) = \<c> e + pd (fst e) - pd (snd e)" using E by simp
      also have "... = \<c> e + (ns_pot_of s (fst e) - ns_pot_of s (snd e)) + ((if fst e \<in> ?S then ?dp else 0) - (if snd e \<in> ?S then ?dp else 0))"
        unfolding abschar2[of "fst e"] abschar2[of "snd e"] by (simp add: algebra_simps split del: if_split)
      also have "... = \<c> e + (ns_pot_of s (fst e) - ns_pot_of s (snd e)) + (- ?pv)" by (simp only: crosse)
      also have "... = reduced_cost (potentials s) e - ?pv" by (simp add: reduced_cost_def)
      also have "... = 0" using rc_eq by simp
      finally show ?thesis .
    next
      case T
      obtain w where wV: "w \<in> \<V> - {r}" and tw: "t = par_edge s w" using T(1) by (auto simp: par_edge_def)
      have wne: "w \<noteq> v" using T(2) tw par_edge_inj[OF inv wV vVr] by blast
      have cut: "(w \<in> ?S) = (par_vx s w \<in> ?S)" using cut_4c[OF inv wV wne] .
      have dir: "if par_up s w then fst (par_edge s w) = w else snd (par_edge s w) = w" using ns_invar_tree_dirD[OF tree wV] .
      have chi0: "(if fst t \<in> ?S then ?dp else 0) - (if snd t \<in> ?S then ?dp else 0) = 0"
      proof (cases "par_up s w")
        case True
        have ft: "fst t = w" and st: "snd t = par_vx s w" using tw dir True by (auto simp: par_vx_def)
        show ?thesis unfolding ft st cut by simp
      next
        case False
        have ft: "fst t = par_vx s w" and st: "snd t = w" using tw dir False by (auto simp: par_vx_def)
        show ?thesis unfolding ft st cut by simp
      qed
      have trc: "\<c> t + ns_pot_of s (fst t) - ns_pot_of s (snd t) = 0" using treerc[OF T(1)] .
      have "\<c> t + pd (fst t) - pd (snd t) = (\<c> t + ns_pot_of s (fst t) - ns_pot_of s (snd t)) + ((if fst t \<in> ?S then ?dp else 0) - (if snd t \<in> ?S then ?dp else 0))"
        unfolding abschar2[of "fst t"] abschar2[of "snd t"] by (simp add: algebra_simps split del: if_split)
      also have "... = 0" using trc chi0 by simp
      finally show ?thesis .
    qed
  qed
  show "potential_fits_spanning_tree_partition r (ns_tree_edges s - {par_edge s v} \<union> {e}) ?pi" using pdfits by (simp add: pd_def)
qed

text \<open>\<^bold>\<open>Guard discharge (\S{}4.4a).\<close> For every vertex \<open>u\<close> of the moved subtree \<open>S\<close>, the shifted
      value \<open>ns_pot_of s u \<plusminus> reduced_cost e\<close> equals \<open>u\<close>'s tree-path cost sum in the swapped tree ---
      a signed edge-cost sum touching the root exactly once --- hence @{const good_pot_val}.
      This is exactly the precondition of the potential-descriptor axioms at each @{term shift_pot}
      application. The proof is the compose: the swapped tree \<open>T' = ns_tree_edges s - {e0} \<union> {e}\<close> is an
      arborescence (\<open>swap_edge_pivot\<close>, with \<open>L' = \<E> - T'\<close>, \<open>U' = {}\<close>), the explicit potential fits it
      (\<open>expl_fits\<close>), so \<open>potential_fits_imp_good\<close> gives \<open>good_pot_val (\<pi>'_expl u)\<close>, and \<open>\<pi>'_expl u = the
      shifted value\<close> for \<open>u \<in> S\<close>.\<close>

lemma shift_good:
  assumes inv: "ns_invar s"
    and sel: "ns_select s = Some (e, in_U, \<gamma>, sel')"
    and pp:  "get_path_pair (spanning_tree s) (fst e) (snd e) = (p1, p2)"
    and bn:  "bottleneck s e in_U p1 p2 = (\<delta>, False, v, e0fwd, up_side)"
    and dne: "\<delta> \<noteq> - 1"
    and uS:  "u \<in> {x. \<exists>p. walk_betw (abstract_arborescense (spanning_tree s)) x p r \<and> distinct p \<and> v \<in> set p}"
  shows "good_pot_val (if in_U \<noteq> up_side then ns_pot_of s u + rcost_abstract \<gamma>
                                          else ns_pot_of s u - rcost_abstract \<gamma>)"
proof -
  let ?absT = "abstract_arborescense (spanning_tree s)"
  let ?S = "{x. \<exists>p. walk_betw ?absT x p r \<and> distinct p \<and> v \<in> set p}"
  let ?e0 = "par_edge s v"
  let ?T' = "ns_tree_edges s - {?e0} \<union> {e}"
  let ?f = "\<lambda>ee. {fst ee, snd ee}"
  let ?sw = "swap_edge (spanning_tree s) v (if in_U = up_side then fst e else snd e) (if in_U = up_side then snd e else fst e)"
  have eE: "e \<in> \<E>" using ns_select_SomeD(2)[OF inv sel] .
  have tree: "ns_invar_tree s" using ns_invarD(7)[OF inv] .
  have arb: "arborescense_invar (spanning_tree s)" using ns_invar_implD(7)[OF ns_invarD(1)[OF inv]] .
  have vVr: "v \<in> \<V> - {r}" using bottleneck_pivot_facts(2)[OF inv sel pp bn] .
  have e0T: "?e0 \<in> ns_tree_edges s" using vVr by (auto simp: par_edge_def)
  have e0sub: "{?e0} \<subseteq> ns_tree_edges s" using e0T by simp
  have part: "spanning_tree_partition r (ns_tree_edges s) (ns_L_of s \<union> ns_selfloops_L) (ns_U_of s \<union> ns_selfloops_U)" using ns_invarD(3)[OF inv] by (simp add: ns_invar_partition_def)
  have TsubE: "?T' \<subseteq> \<E>" using spanning_tree_partitionD(1)[OF part] eE by auto
  have oldnm: "inj_on ?f (ns_tree_edges s)" unfolding inj_on_def using spanning_tree_partitionD(7)[OF part] by blast
  have fTeq: "?f ` (ns_tree_edges s) = ?absT" using ns_invar_tree_edgesD[OF tree] by (simp add: par_edge_def image_image)
  have absw: "abstract_arborescense ?sw = ?absT - {?f ?e0} \<union> {?f e}" using swap_edge_pivot(2)[OF inv sel pp bn dne] .
  have arbsw: "arborescense_invar ?sw" using swap_edge_pivot(1)[OF inv sel pp bn dne] .
  have fT'eq: "?f ` ?T' = abstract_arborescense ?sw"
  proof -
    have "?f ` ?T' = ?f ` (ns_tree_edges s - {?e0}) \<union> {?f e}" by (simp add: image_Un)
    also have "... = ?f ` (ns_tree_edges s) - {?f ?e0} \<union> {?f e}" using inj_on_image_set_diff[OF oldnm Diff_subset e0sub] by simp
    also have "... = ?absT - {?f ?e0} \<union> {?f e}" using fTeq by simp
    also have "... = abstract_arborescense ?sw" using absw by simp
    finally show ?thesis .
  qed
  have giT': "graph_invar (abstract_arborescense ?sw)" using general(2)[OF arbsw] .
  have VsT': "Vs (abstract_arborescense ?sw) = \<V>" using general(4)[OF arbsw] .
  have rV: "r \<in> \<V>" using general(1) .
  have rVsT': "r \<in> Vs (abstract_arborescense ?sw)" using rV VsT' by simp
  have uniqT': "\<And>x y. x \<in> Vs (abstract_arborescense ?sw) \<Longrightarrow> y \<in> Vs (abstract_arborescense ?sw) \<Longrightarrow> \<exists>!p. walk_betw (abstract_arborescense ?sw) x p y \<and> distinct p"
  proof -
    fix x y assume "x \<in> Vs (abstract_arborescense ?sw)" "y \<in> Vs (abstract_arborescense ?sw)"
    hence xy: "x\<in>\<V>" "y\<in>\<V>" using VsT' by auto
    show "\<exists>!p. walk_betw (abstract_arborescense ?sw) x p y \<and> distinct p" using general(3)[OF arbsw xy(2) xy(1)] .
  qed
  have arbsw2: "graph_abs.arborescence (abstract_arborescense ?sw) r (abstract_arborescense ?sw)" using unique_walks_arborescence[OF giT' rVsT' uniqT'] .
  have gaT0: "graph_abs (?f ` ?T')" using giT' unfolding fT'eq by (simp add: graph_abs_def)
  have arbT0: "graph_abs.arborescence (?f ` ?T') r (?f ` ?T')" using arbsw2 unfolding fT'eq .
  have dVsVs: "\<And>X. dVs (make_pair ` X) = Vs (?f ` X)" by (auto simp: dVs_def make_pair_def Vs_def)
  have VsGT': "dVs (make_pair ` ?T') = \<V>" using dVsVs[of ?T'] fT'eq VsT' by simp
  have uV: "u \<in> \<V>"
  proof -
    from uS obtain p where "walk_betw ?absT u p r" by auto
    hence "u \<in> Vs ?absT" by (metis hd_in_set subsetD walk_betw_def walk_in_Vs)
    thus ?thesis using general(4)[OF arb] by simp
  qed
  have fit: "potential_fits_spanning_tree_partition r ?T' (\<lambda>w. ns_pot_of s w + (if w \<in> ?S then (if in_U \<noteq> up_side then rcost_abstract \<gamma> else - rcost_abstract \<gamma>) else 0))" using expl_fits[OF inv sel pp bn dne] .
  have good: "good_pot_val ((\<lambda>w. ns_pot_of s w + (if w \<in> ?S then (if in_U \<noteq> up_side then rcost_abstract \<gamma> else - rcost_abstract \<gamma>) else 0)) u)" using potential_fits_imp_good[OF TsubE gaT0 arbT0 VsGT' fit uV] .
  have ifu: "(if u \<in> ?S then (if in_U \<noteq> up_side then rcost_abstract \<gamma> else - rcost_abstract \<gamma>) else 0) = (if in_U \<noteq> up_side then rcost_abstract \<gamma> else - rcost_abstract \<gamma>)" by (rule if_P[OF uS])
  have eqv: "ns_pot_of s u + (if u \<in> ?S then (if in_U \<noteq> up_side then rcost_abstract \<gamma> else - rcost_abstract \<gamma>) else 0) = (if in_U \<noteq> up_side then ns_pot_of s u + rcost_abstract \<gamma> else ns_pot_of s u - rcost_abstract \<gamma>)" using ifu by simp
  show ?thesis using good eqv by simp
qed

lemma shift_pot_props:
  assumes inv: "ns_invar s"
    and sel: "ns_select s = Some (e, in_U, \<gamma>, sel')"
    and pp:  "get_path_pair (spanning_tree s) (fst e) (snd e) = (p1, p2)"
    and bn:  "bottleneck s e in_U p1 p2 = (\<delta>, False, v, e0fwd, up_side)"
    and dne: "\<delta> \<noteq> - 1"
  shows "pot_valid (shift_pot (spanning_tree s) v (potentials s) \<gamma> (in_U \<noteq> up_side))"
    and "abstract_pot (shift_pot (spanning_tree s) v (potentials s) \<gamma> (in_U \<noteq> up_side)) r = 0"
    and "potential_fits_spanning_tree_partition r
           (ns_tree_edges s - {par_edge s v} \<union> {e})
           (abstract_pot (shift_pot (spanning_tree s) v (potentials s) \<gamma> (in_U \<noteq> up_side)))"
    and "(\<Sum> u \<in> \<V>. abstract_pot (shift_pot (spanning_tree s) v (potentials s) \<gamma> (in_U \<noteq> up_side)) u) =
         ns_pot_sum s
         + (if in_U \<noteq> up_side then rcost_abstract \<gamma> else - rcost_abstract \<gamma>)
           * card {x. \<exists>p. walk_betw (abstract_arborescense (spanning_tree s)) x p r
                           \<and> distinct p \<and> v \<in> set p}"
proof -
  let ?absT = "abstract_arborescense (spanning_tree s)"
  let ?S = "{x. \<exists>p. walk_betw ?absT x p r \<and> distinct p \<and> v \<in> set p}"
  let ?up = "in_U \<noteq> up_side"
  let ?pv = "rcost_abstract \<gamma>"
  let ?dp = "if in_U \<noteq> up_side then ?pv else - ?pv"
  let ?pi = "abstract_pot (shift_pot (spanning_tree s) v (potentials s) \<gamma> ?up)"
  have eE: "e \<in> \<E>" using ns_select_SomeD(2)[OF inv sel] .
  have neq: "fst e \<noteq> snd e" using entering_not_selfloop[OF inv sel] .
  have fV: "fst e \<in> \<V>" using fst_E_V[OF eE] .
  have sV: "snd e \<in> \<V>" using snd_E_V[OF eE] .
  have arb: "arborescense_invar (spanning_tree s)" using ns_invar_implD(7)[OF ns_invarD(1)[OF inv]] .
  have tree: "ns_invar_tree s" using ns_invarD(7)[OF inv] .
  have vVr: "v \<in> \<V> - {r}" using bottleneck_pivot_facts(2)[OF inv sel pp bn] .
  have vV: "v \<in> \<V>" using vVr by simp
  have vP: "v \<in> set (if in_U = up_side then p1 else p2)" using bottleneck_pivot_facts(1)[OF inv sel pp bn] .
  have precond: "selection_precond (edge_sel s) (potentials s) (edge_state s)"
    using ns_invar_implD(6)[OF ns_invarD(1)[OF inv]] ns_invar_implD(2)[OF ns_invarD(1)[OF inv]]
          ns_invar_implD(5)[OF ns_invarD(1)[OF inv]] ns_invar_pot_fitsD[OF ns_invarD(5)[OF inv]]
    by (simp add: selection_precond_def potential_fits_spanning_tree_partition_def)
  have selS: "sel_select (edge_sel s) (potentials s) (edge_state s) = Some (e, in_U, \<gamma>, sel')"
    using sel by (simp add: ns_select_def)
  have gi: "rcost_invar \<gamma>" using sel_select_SomeD(2)[OF precond selS] .
  have rc_eq: "?pv = reduced_cost (potentials s) e" using sel_select_SomeD(3)[OF precond selS] .
  have pf: "potential_fits_spanning_tree_partition r (ns_tree_edges s) (ns_pot_of s)"
    using ns_invar_pot_fitsD[OF ns_invarD(5)[OF inv]] .
  have pir0: "ns_pot_of s r = 0" using pf by (simp add: potential_fits_spanning_tree_partition_def)
  have treerc: "\<And>t. t \<in> ns_tree_edges s \<Longrightarrow> \<c> t + ns_pot_of s (fst t) - ns_pot_of s (snd t) = 0"
    using pf by (auto simp: potential_fits_spanning_tree_partition_def)
  obtain a p3 where
    w1: "walk_betw ?absT (fst e) (p1 @ a # p3) r" and
    w2: "walk_betw ?absT (snd e) (p2 @ a # p3) r" and
    d1: "distinct (p1 @ a # p3)" and d2: "distinct (p2 @ a # p3)" and
    disj: "set p1 \<inter> set p2 = {}"
    using get_path_pair(1)[OF arb pp neq fV sV] by blast
  have shg: "\<And>u. u \<in> ?S \<Longrightarrow> good_pot_val (if ?up then ns_pot_of s u + rcost_abstract \<gamma> else ns_pot_of s u - rcost_abstract \<gamma>)"
    using shift_good[OF inv sel pp bn dne] by blast
  have abschar: "\<And>u. ?pi u = ns_pot_of s u + (if u \<in> ?S then ?dp else 0)"
  proof -
    fix u
    consider (isin) "u \<in> ?S" | (out) "u \<notin> ?S" by blast
    thus "?pi u = ns_pot_of s u + (if u \<in> ?S then ?dp else 0)"
    proof cases
      case isin
      have "?pi u = (if ?up then ns_pot_of s u + ?pv else ns_pot_of s u - ?pv)"
        using shift_pot_abstract[OF inv vV gi shg, of u] unfolding if_P[OF isin] .
      thus ?thesis unfolding if_P[OF isin] by (cases ?up) simp_all
    next
      case out
      have "?pi u = ns_pot_of s u"
        using shift_pot_abstract[OF inv vV gi shg, of u] unfolding if_not_P[OF out] .
      thus ?thesis unfolding if_not_P[OF out] by simp
    qed
  qed
  have rV: "r \<in> \<V>" using general(1) .
  have rinVs: "r \<in> Vs ?absT" using rV general(4)[OF arb] by simp
  have rwalk: "walk_betw ?absT r [r] r" using rinVs by (rule walk_reflexive)
  have rnotS: "r \<notin> ?S"
  proof
    assume "r \<in> ?S"
    then obtain p where wp: "walk_betw ?absT r p r" and dp: "distinct p" and vp: "v \<in> set p" by auto
    have "\<exists>!q. walk_betw ?absT r q r \<and> distinct q" using general(3)[OF arb rV rV] .
    hence "p = [r]" using wp dp rwalk by (metis (mono_tags, lifting) distinct_singleton)
    thus False using vp vVr by simp
  qed
  have vp1: "(v \<in> set (p1 @ a # p3)) = (in_U = up_side)"
  proof (cases "in_U = up_side")
    case True
    hence "v \<in> set p1" using vP by simp
    thus ?thesis using True by simp
  next
    case False
    hence vin2: "v \<in> set p2" using vP by simp
    have "v \<notin> set p1" using vin2 disj by auto
    moreover have "v \<notin> set (a # p3)" using vin2 d2 by (auto simp: distinct_append)
    ultimately show ?thesis using False by auto
  qed
  have vp2: "(v \<in> set (p2 @ a # p3)) = (in_U \<noteq> up_side)"
  proof (cases "in_U = up_side")
    case True
    hence vin1: "v \<in> set p1" using vP by simp
    have "v \<notin> set p2" using vin1 disj by auto
    moreover have "v \<notin> set (a # p3)" using vin1 d1 by (auto simp: distinct_append)
    ultimately show ?thesis using True by auto
  next
    case False
    hence "v \<in> set p2" using vP by simp
    thus ?thesis using False by simp
  qed
  have fstS: "(fst e \<in> ?S) = (in_U = up_side)" using S_via_walk[OF inv w1 d1] vp1 by simp
  have sndS: "(snd e \<in> ?S) = (in_U \<noteq> up_side)" using S_via_walk[OF inv w2 d2] vp2 by simp
  have crosse: "(if fst e \<in> ?S then ?dp else 0) - (if snd e \<in> ?S then ?dp else 0) = - ?pv"
    unfolding fstS sndS by (cases "in_U = up_side") simp_all
  have piR0: "?pi r = 0"
  proof -
    have "?pi r = ns_pot_of s r + (if r \<in> ?S then ?dp else 0)" by (rule abschar)
    also have "... = ns_pot_of s r" unfolding if_not_P[OF rnotS] by simp
    also have "... = 0" using pir0 .
    finally show ?thesis .
  qed
  show "pot_valid (shift_pot (spanning_tree s) v (potentials s) \<gamma> (in_U \<noteq> up_side))" using shift_pot_valid[OF inv vV gi shg] .
  show "abstract_pot (shift_pot (spanning_tree s) v (potentials s) \<gamma> (in_U \<noteq> up_side)) r = 0" using piR0 .
  show "potential_fits_spanning_tree_partition r (ns_tree_edges s - {par_edge s v} \<union> {e}) ?pi"
    unfolding potential_fits_spanning_tree_partition_def
  proof (intro conjI ballI)
    show "?pi r = 0" using piR0 .
  next
    fix t assume tin: "t \<in> ns_tree_edges s - {par_edge s v} \<union> {e}"
    consider (E) "t = e" | (T) "t \<in> ns_tree_edges s" "t \<noteq> par_edge s v" using tin by auto
    thus "\<c> t + ?pi (fst t) - ?pi (snd t) = 0"
    proof cases
      case E
      have "\<c> t + ?pi (fst t) - ?pi (snd t) = \<c> e + ?pi (fst e) - ?pi (snd e)" using E by simp
      also have "... = \<c> e + (ns_pot_of s (fst e) - ns_pot_of s (snd e))
            + ((if fst e \<in> ?S then ?dp else 0) - (if snd e \<in> ?S then ?dp else 0))"
        unfolding abschar[of "fst e"] abschar[of "snd e"] by (simp add: algebra_simps split del: if_split)
      also have "... = \<c> e + (ns_pot_of s (fst e) - ns_pot_of s (snd e)) + (- ?pv)"
        by (simp only: crosse)
      also have "... = reduced_cost (potentials s) e - ?pv" by (simp add: reduced_cost_def)
      also have "... = 0" using rc_eq by simp
      finally show ?thesis .
    next
      case T
      obtain w where wV: "w \<in> \<V> - {r}" and tw: "t = par_edge s w"
        using T(1) by (auto simp: par_edge_def)
      have wne: "w \<noteq> v" using T(2) tw par_edge_inj[OF inv wV vVr] by blast
      have cut: "(w \<in> ?S) = (par_vx s w \<in> ?S)" using cut_4c[OF inv wV wne] .
      have dir: "if par_up s w then fst (par_edge s w) = w else snd (par_edge s w) = w"
        using ns_invar_tree_dirD[OF tree wV] .
      have chi0: "(if fst t \<in> ?S then ?dp else 0) - (if snd t \<in> ?S then ?dp else 0) = 0"
      proof (cases "par_up s w")
        case True
        have ft: "fst t = w" and st: "snd t = par_vx s w" using tw dir True by (auto simp: par_vx_def)
        show ?thesis unfolding ft st cut by simp
      next
        case False
        have ft: "fst t = par_vx s w" and st: "snd t = w" using tw dir False by (auto simp: par_vx_def)
        show ?thesis unfolding ft st cut by simp
      qed
      have trc: "\<c> t + ns_pot_of s (fst t) - ns_pot_of s (snd t) = 0" using treerc[OF T(1)] .
      have "\<c> t + ?pi (fst t) - ?pi (snd t)
          = (\<c> t + ns_pot_of s (fst t) - ns_pot_of s (snd t))
            + ((if fst t \<in> ?S then ?dp else 0) - (if snd t \<in> ?S then ?dp else 0))"
        unfolding abschar[of "fst t"] abschar[of "snd t"] by (simp add: algebra_simps split del: if_split)
      also have "... = 0" using trc chi0 by simp
      finally show ?thesis .
    qed
  qed
  have SsubV: "?S \<subseteq> \<V>"
  proof
    fix x assume "x \<in> ?S"
    then obtain p where "walk_betw ?absT x p r" by auto
    hence "x \<in> Vs ?absT" by (metis hd_in_set subsetD walk_betw_def walk_in_Vs)
    thus "x \<in> \<V>" using general(4)[OF arb] by simp
  qed
  have finV: "finite \<V>" using \<V>_finite .
  show "(\<Sum> u \<in> \<V>. abstract_pot (shift_pot (spanning_tree s) v (potentials s) \<gamma> (in_U \<noteq> up_side)) u) =
         ns_pot_sum s + (if in_U \<noteq> up_side then rcost_abstract \<gamma> else - rcost_abstract \<gamma>) * card ?S"
  proof -
    have sumpi: "sum ?pi \<V> = (\<Sum>u\<in>\<V>. ns_pot_of s u) + (\<Sum>u\<in>\<V>. (if u \<in> ?S then ?dp else 0))"
    proof -
      have "sum ?pi \<V> = (\<Sum>u\<in>\<V>. ns_pot_of s u + (if u \<in> ?S then ?dp else 0))"
        by (rule sum.cong[OF refl]) (simp only: abschar)
      thus ?thesis by (simp add: sum.distrib)
    qed
    have s1: "(\<Sum>u\<in>\<V>. ns_pot_of s u) = ns_pot_sum s" by (simp add: ns_pot_sum_def)
    have s2: "(\<Sum>u\<in>\<V>. (if u \<in> ?S then ?dp else 0)) = ?dp * real (card ?S)"
    proof -
      have "(\<Sum>u\<in>\<V>. (if u \<in> ?S then ?dp else 0)) = (\<Sum>u\<in>\<V> \<inter> ?S. ?dp)"
        by (rule sum.inter_restrict[OF finV, symmetric])
      also have "... = real (card (\<V> \<inter> ?S)) * ?dp" by simp
      also have "\<V> \<inter> ?S = ?S" using SsubV by blast
      finally show ?thesis by (simp add: mult.commute)
    qed
    show ?thesis using sumpi s1 s2 by simp
  qed
qed


lemma reparent_props:
  assumes inv: "ns_invar s"
    and sel: "ns_select s = Some (e, in_U, \<gamma>, sel')"
    and pp:  "get_path_pair (spanning_tree s) (fst e) (snd e) = (p1, p2)"
    and bn:  "bottleneck s e in_U p1 p2 = (\<delta>, False, v, e0fwd, up_side)"
    and dne: "\<delta> \<noteq> - 1"
    and rp:  "reparent s e (if in_U = up_side then p1 else p2) v = (parr, darr)"
  shows "parent_invar parr"
    and "dir_invar darr"
    and "(\<lambda> w. {fst (parent_lookup parr w), snd (parent_lookup parr w)}) ` (\<V> - {r})
         = abstract_arborescense
             (swap_edge (spanning_tree s) v
                (if in_U = up_side then fst e else snd e)
                (if in_U = up_side then snd e else fst e))"
proof -
  let ?P = "if in_U = up_side then p1 else p2"
  let ?absT = "abstract_arborescense (spanning_tree s)"
  have eE: "e \<in> \<E>" using ns_select_SomeD(2)[OF inv sel] .
  have neq: "fst e \<noteq> snd e" using entering_not_selfloop[OF inv sel] .
  have fV: "fst e \<in> \<V>" using fst_E_V[OF eE] .
  have sV: "snd e \<in> \<V>" using snd_E_V[OF eE] .
  have arb: "arborescense_invar (spanning_tree s)" using ns_invar_implD(7)[OF ns_invarD(1)[OF inv]] .
  have pinvE: "parent_invar (parent_edge s)" using ns_invar_implD(3)[OF ns_invarD(1)[OF inv]] .
  have dinvE: "dir_invar (edge_dir s)" using ns_invar_implD(4)[OF ns_invarD(1)[OF inv]] .
  obtain a p3 where d1: "distinct (p1 @ a # p3)" and d2: "distinct (p2 @ a # p3)"
    using get_path_pair(1)[OF arb pp neq fV sV] by blast
  have Pdist: "distinct ?P" using d1 d2 by (cases "in_U = up_side") auto
  have vP: "v \<in> set ?P" using bottleneck_pivot_facts(1)[OF inv sel pp bn] .
  have vVr: "v \<in> \<V> - {r}" using bottleneck_pivot_facts(2)[OF inv sel pp bn] .
  have PsubV: "set ?P \<subseteq> \<V> - {r}"
    using get_path_pair_verts[OF inv eE entering_not_selfloop[OF inv sel] pp] by (cases "in_U = up_side") auto
  have rpw: "reparent_walk s e v True e False ?P (parent_edge s, edge_dir s) = (parr, darr)"
    using rp by (simp add: reparent_def)
  have "case reparent_walk s e v True e False ?P (parent_edge s, edge_dir s) of (p, d) \<Rightarrow> parent_invar p \<and> dir_invar d"
    by (rule reparent_walk_invar[OF PsubV]) (simp add: pinvE dinvE)
  hence inv12: "parent_invar parr \<and> dir_invar darr" unfolding rpw prod.case .
  have chc: "case reparent_walk s e v True e False ?P (parent_edge s, edge_dir s) of (parr, darr) \<Rightarrow>
       (\<forall>x. x \<notin> insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ?P)) \<longrightarrow> parent_lookup parr x = parent_lookup (parent_edge s) x)
      \<and> (\<lambda>w. {fst (parent_lookup parr w), snd (parent_lookup parr w)}) ` insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ?P))
         = insert (if True then {fst e, snd e} else {fst e, snd e})
              ((\<lambda>w. {fst (par_edge s w), snd (par_edge s w)}) ` set (takeWhile (\<lambda>y. y \<noteq> v) ?P))"
    by (rule reparent_walk_char[OF Pdist vP pinvE PsubV])
  have char: "(\<forall>x. x \<notin> insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ?P)) \<longrightarrow> parent_lookup parr x = parent_lookup (parent_edge s) x)
      \<and> (\<lambda>w. {fst (parent_lookup parr w), snd (parent_lookup parr w)}) ` insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ?P))
         = insert {fst e, snd e} ((\<lambda>w. {fst (par_edge s w), snd (par_edge s w)}) ` set (takeWhile (\<lambda>y. y \<noteq> v) ?P))"
    using chc unfolding rpw prod.case by simp
  have off: "\<And>x. x \<notin> insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ?P)) \<Longrightarrow> parent_lookup parr x = par_edge s x"
    using char by (auto simp: par_edge_def)
  have spine: "(\<lambda>w. {fst (parent_lookup parr w), snd (parent_lookup parr w)}) ` insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ?P))
             = insert {fst e, snd e} ((\<lambda>w. {fst (par_edge s w), snd (par_edge s w)}) ` set (takeWhile (\<lambda>y. y \<noteq> v) ?P))"
    using char by (rule conjunct2)
  have vnotTW: "v \<notin> set (takeWhile (\<lambda>y. y \<noteq> v) ?P)" by (auto dest: set_takeWhileD)
  have TWsub: "set (takeWhile (\<lambda>y. y \<noteq> v) ?P) \<subseteq> set ?P" by (auto dest: set_takeWhileD)
  have VISsubV: "insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ?P)) \<subseteq> \<V> - {r}"
    using vVr TWsub PsubV by auto
  have setfact: "set (takeWhile (\<lambda>y. y \<noteq> v) ?P) \<union> ((\<V> - {r}) - insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ?P))) = (\<V> - {r}) - {v}"
    using TWsub PsubV vnotTW vVr by auto
  have gimg: "(\<lambda>w. {fst (par_edge s w), snd (par_edge s w)}) ` (\<V> - {r}) = ?absT"
    using ns_invar_tree_edgesD[OF ns_invarD(7)[OF inv]] by (simp add: par_edge_def image_image)
  have vsub: "{v} \<subseteq> \<V> - {r}" using vVr by simp
  have Dstep: "(\<lambda>w. {fst (par_edge s w), snd (par_edge s w)}) ` ((\<V> - {r}) - {v})
             = ?absT - {{fst (par_edge s v), snd (par_edge s v)}}"
    using inj_on_image_set_diff[OF tree_edge_inj[OF inv] Diff_subset vsub] gimg by simp
  have main: "(\<lambda>w. {fst (parent_lookup parr w), snd (parent_lookup parr w)}) ` (\<V> - {r})
            = insert {fst e, snd e} (?absT - {{fst (par_edge s v), snd (par_edge s v)}})"
  proof -
    have step1: "(\<lambda>w. {fst (parent_lookup parr w), snd (parent_lookup parr w)}) ` (\<V> - {r})
        = (\<lambda>w. {fst (parent_lookup parr w), snd (parent_lookup parr w)}) ` insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ?P))
          \<union> (\<lambda>w. {fst (parent_lookup parr w), snd (parent_lookup parr w)}) ` ((\<V> - {r}) - insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ?P)))"
      by (metis Diff_partition[OF VISsubV] image_Un)
    have step2: "(\<lambda>w. {fst (parent_lookup parr w), snd (parent_lookup parr w)}) ` ((\<V> - {r}) - insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ?P)))
        = (\<lambda>w. {fst (par_edge s w), snd (par_edge s w)}) ` ((\<V> - {r}) - insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ?P)))"
      by (rule image_cong[OF refl]) (simp add: off)
    have "(\<lambda>w. {fst (parent_lookup parr w), snd (parent_lookup parr w)}) ` (\<V> - {r})
        = insert {fst e, snd e} ((\<lambda>w. {fst (par_edge s w), snd (par_edge s w)}) ` set (takeWhile (\<lambda>y. y \<noteq> v) ?P))
          \<union> (\<lambda>w. {fst (par_edge s w), snd (par_edge s w)}) ` ((\<V> - {r}) - insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ?P)))"
      by (simp only: step1 spine step2)
    also have "... = insert {fst e, snd e} ((\<lambda>w. {fst (par_edge s w), snd (par_edge s w)}) ` set (takeWhile (\<lambda>y. y \<noteq> v) ?P)
          \<union> (\<lambda>w. {fst (par_edge s w), snd (par_edge s w)}) ` ((\<V> - {r}) - insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ?P))))"
      by simp
    also have "... = insert {fst e, snd e} ((\<lambda>w. {fst (par_edge s w), snd (par_edge s w)}) ` (set (takeWhile (\<lambda>y. y \<noteq> v) ?P)
          \<union> ((\<V> - {r}) - insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ?P)))))"
      by (simp add: image_Un)
    also have "... = insert {fst e, snd e} ((\<lambda>w. {fst (par_edge s w), snd (par_edge s w)}) ` ((\<V> - {r}) - {v}))"
      by (simp only: setfact)
    also have "... = insert {fst e, snd e} (?absT - {{fst (par_edge s v), snd (par_edge s v)}})"
      by (simp only: Dstep)
    finally show ?thesis .
  qed
  show "parent_invar parr" using inv12 by simp
  show "dir_invar darr" using inv12 by simp
  show "(\<lambda> w. {fst (parent_lookup parr w), snd (parent_lookup parr w)}) ` (\<V> - {r})
         = abstract_arborescense
             (swap_edge (spanning_tree s) v
                (if in_U = up_side then fst e else snd e)
                (if in_U = up_side then snd e else fst e))"
    using main swap_edge_pivot(2)[OF inv sel pp bn dne] by auto
qed

text \<open>\<^bold>\<open>Arc-level re-parenting.\<close> The undirected projection in \<open>reparent_props\<close> suffices for the
      tree bridge, but the partition and potential-fits invariants need the parent array's \<^emph>\<open>arc\<close> set.
      The arc-level twin of \<open>reparent_walk_char\<close> says the spine's new parent arcs are the
      entering edge together with each predecessor's old parent arc; assembling it over \<open>V - {r}\<close>
      yields the basis exchange \<open>T - {e0} \<union> {e}\<close> on the arc level.\<close>

lemma reparent_walk_char_arc:
  "\<lbrakk>distinct ws; v \<in> set ws; parent_invar parr0; set ws \<subseteq> \<V> - {r}\<rbrakk>
   \<Longrightarrow> (case reparent_walk s e v first pe pup ws (parr0, darr0) of (parr, darr) \<Rightarrow>
        (\<forall>x. x \<notin> insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ws)) \<longrightarrow> parent_lookup parr x = parent_lookup parr0 x)
       \<and> parent_lookup parr ` insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ws))
          = insert (if first then e else pe)
               (par_edge s ` set (takeWhile (\<lambda>y. y \<noteq> v) ws)))"
proof (induction ws arbitrary: first pe pup parr0 darr0)
  case Nil
  then show ?case by simp
next
  case (Cons w ws')
  have dw: "distinct (w # ws')" and vin: "v \<in> set (w # ws')" and pinv: "parent_invar parr0"
    using Cons.prems by auto
  have wV: "w \<in> \<V> - {r}" using Cons.prems(4) by simp
  have wsV': "set ws' \<subseteq> \<V> - {r}" using Cons.prems(4) by simp
  define val_w where "val_w = (if first then e else pe)"
  define dval_w where "dval_w = (if first then (w = fst_exec e) else (\<not> pup))"
  have pinv': "parent_invar (parent_upd parr0 w val_w)"
    using pinv wV by (rule parent_arr.fixed_univ_map_upd_invar)
  have look_upd: "parent_lookup (parent_upd parr0 w val_w) = (parent_lookup parr0)(w := val_w)"
    using pinv wV by (rule parent_arr.fixed_univ_map_upd)
  have headval: "val_w = (if first then e else pe)"
    by (simp add: val_w_def)
  show ?case
  proof (cases "w = v")
    case True
    have res: "reparent_walk s e v first pe pup (w # ws') (parr0, darr0) = (parent_upd parr0 w val_w, dir_upd darr0 w dval_w)"
      using True by (cases first) (simp_all add: val_w_def dval_w_def)
    have ins: "insert v (set (takeWhile (\<lambda>y. y \<noteq> v) (w # ws'))) = {v}" using True by simp
    have tw0: "set (takeWhile (\<lambda>y. y \<noteq> v) (w # ws')) = {}" using True by simp
    show ?thesis
      unfolding res prod.case
    proof (intro conjI allI impI)
      fix x assume "x \<notin> insert v (set (takeWhile (\<lambda>y. y \<noteq> v) (w # ws')))"
      hence "x \<noteq> v" using ins by simp
      thus "parent_lookup (parent_upd parr0 w val_w) x = parent_lookup parr0 x"
        using True look_upd by simp
    next
      show "parent_lookup (parent_upd parr0 w val_w) ` insert v (set (takeWhile (\<lambda>y. y \<noteq> v) (w # ws')))
            = insert (if first then e else pe)
                 (par_edge s ` set (takeWhile (\<lambda>y. y \<noteq> v) (w # ws')))"
        using True look_upd ins tw0 headval by simp
    qed
  next
    case False
    have res: "reparent_walk s e v first pe pup (w # ws') (parr0, darr0)
                 = reparent_walk s e v False (par_edge s w) (par_up s w) ws' (parent_upd parr0 w val_w, dir_upd darr0 w dval_w)"
      using False by (cases first) (simp_all add: val_w_def dval_w_def)
    have vin': "v \<in> set ws'" using vin False by simp
    have dw': "distinct ws'" using dw by simp
    have wns: "w \<notin> set ws'" using dw by simp
    have tw: "set (takeWhile (\<lambda>y. y \<noteq> v) (w # ws')) = insert w (set (takeWhile (\<lambda>y. y \<noteq> v) ws'))"
      using False by simp
    have twsub: "set (takeWhile (\<lambda>y. y \<noteq> v) ws') \<subseteq> set ws'" by (auto dest: set_takeWhileD)
    have wnotin: "w \<notin> insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ws'))"
      using wns twsub False by auto
    obtain parr darr where res2:
      "reparent_walk s e v False (par_edge s w) (par_up s w) ws' (parent_upd parr0 w val_w, dir_upd darr0 w dval_w) = (parr, darr)"
      by (cases "reparent_walk s e v False (par_edge s w) (par_up s w) ws' (parent_upd parr0 w val_w, dir_upd darr0 w dval_w)")
    have IH: "(\<forall>x. x \<notin> insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ws')) \<longrightarrow> parent_lookup parr x = parent_lookup (parent_upd parr0 w val_w) x)
            \<and> parent_lookup parr ` insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ws'))
               = insert (par_edge s w)
                    (par_edge s ` set (takeWhile (\<lambda>y. y \<noteq> v) ws'))"
      using Cons.IH[OF dw' vin' pinv' wsV', of False "par_edge s w" "par_up s w" "dir_upd darr0 w dval_w"]
      unfolding res2 prod.case by simp
    have IH1: "\<forall>x. x \<notin> insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ws')) \<longrightarrow> parent_lookup parr x = parent_lookup (parent_upd parr0 w val_w) x"
      using IH by (rule conjunct1)
    have IH2: "parent_lookup parr ` insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ws'))
               = insert (par_edge s w)
                    (par_edge s ` set (takeWhile (\<lambda>y. y \<noteq> v) ws'))"
      using IH by (rule conjunct2)
    have plw: "parent_lookup parr w = val_w"
      using IH1[rule_format, OF wnotin] look_upd by simp
    show ?thesis
      unfolding res res2 prod.case
    proof (intro conjI allI impI)
      fix x assume A: "x \<notin> insert v (set (takeWhile (\<lambda>y. y \<noteq> v) (w # ws')))"
      have A2: "x \<notin> insert v (insert w (set (takeWhile (\<lambda>y. y \<noteq> v) ws')))" using A[unfolded tw] .
      have xw: "x \<noteq> w" using A2 by simp
      have xni: "x \<notin> insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ws'))" using A2 by simp
      have "parent_lookup parr x = parent_lookup (parent_upd parr0 w val_w) x"
        using IH1[rule_format, OF xni] .
      thus "parent_lookup parr x = parent_lookup parr0 x" using xw look_upd by simp
    next
      have "parent_lookup parr ` insert v (set (takeWhile (\<lambda>y. y \<noteq> v) (w # ws')))
          = parent_lookup parr ` insert w (insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ws')))"
        by (simp only: tw insert_commute)
      also have "... = insert (parent_lookup parr w)
               (parent_lookup parr ` insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ws')))"
        by (simp only: image_insert)
      also have "... = insert val_w
               (insert (par_edge s w)
                  (par_edge s ` set (takeWhile (\<lambda>y. y \<noteq> v) ws')))"
        by (simp only: plw IH2)
      also have "... = insert (if first then e else pe)
               (par_edge s ` set (takeWhile (\<lambda>y. y \<noteq> v) (w # ws')))"
        by (simp only: headval tw image_insert par_edge_def)
      finally show "parent_lookup parr ` insert v (set (takeWhile (\<lambda>y. y \<noteq> v) (w # ws')))
          = insert (if first then e else pe)
               (par_edge s ` set (takeWhile (\<lambda>y. y \<noteq> v) (w # ws')))" .
    qed
  qed
qed

lemma par_edge_inj_on: "ns_invar s \<Longrightarrow> inj_on (par_edge s) (\<V> - {r})"
  by (rule inj_onI) (rule par_edge_inj)

text \<open>\<^bold>\<open>Pointwise re-parenting.\<close> The exact new parent edge \<^emph>\<open>and\<close> orientation flag of every vertex
      after @{const reparent_walk}: off the walked spine both are untouched; the spine head @{term \<open>hd ws\<close>}
      gets the entering edge @{term e} (flag @{term \<open>hd ws = fst e\<close>}, or the carried predecessor's edge);
      and each subsequent spine vertex @{term \<open>ws ! Suc i\<close>} inherits its predecessor @{term \<open>ws ! i\<close>}'s
      \<^emph>\<open>old\<close> parent edge with the orientation flipped. This is the per-vertex data (notes 4.5 (5b)) that
      the strong-feasibility and tree invariants consume.\<close>

lemma reparent_walk_full:
  "distinct ws \<Longrightarrow> v \<in> set ws \<Longrightarrow> parent_invar pp0 \<Longrightarrow> dir_invar dd0 \<Longrightarrow> set ws \<subseteq> \<V> - {r} \<Longrightarrow>
   (case reparent_walk s e v first pe pup ws (pp0, dd0) of (pr, dr) \<Rightarrow>
      (\<forall>x. x \<notin> insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ws)) \<longrightarrow>
           parent_lookup pr x = parent_lookup pp0 x \<and> dir_lookup dr x = dir_lookup dd0 x)
    \<and> parent_lookup pr (hd ws) = (if first then e else pe)
    \<and> dir_lookup dr (hd ws) = (if first then (hd ws = fst_exec e) else (\<not> pup))
    \<and> (\<forall>i. Suc i < length ws \<longrightarrow> ws ! i \<in> set (takeWhile (\<lambda>y. y \<noteq> v) ws) \<longrightarrow>
         parent_lookup pr (ws ! Suc i) = par_edge s (ws ! i)
       \<and> dir_lookup dr (ws ! Suc i) = (\<not> par_up s (ws ! i))))"
proof (induction ws arbitrary: first pe pup pp0 dd0)
  case Nil thus ?case by simp
next
  case (Cons w ws')
  have dw: "distinct (w # ws')" and vin: "v \<in> set (w # ws')"
    and pinv: "parent_invar pp0" and dinv: "dir_invar dd0" using Cons.prems by auto
  have wV: "w \<in> \<V> - {r}" using Cons.prems(5) by simp
  have wsV': "set ws' \<subseteq> \<V> - {r}" using Cons.prems(5) by simp
  define vw where "vw = (if first then e else pe)"
  define dvw where "dvw = (if first then (w = fst_exec e) else (\<not> pup))"
  have plu: "parent_lookup (parent_upd pp0 w vw) = (parent_lookup pp0)(w := vw)"
    using pinv wV by (rule parent_arr.fixed_univ_map_upd)
  have dlu: "dir_lookup (dir_upd dd0 w dvw) = (dir_lookup dd0)(w := dvw)"
    using dinv wV by (rule dir_arr.fixed_univ_map_upd)
  have pinv': "parent_invar (parent_upd pp0 w vw)" using pinv wV by (rule parent_arr.fixed_univ_map_upd_invar)
  have dinv': "dir_invar (dir_upd dd0 w dvw)" using dinv wV by (rule dir_arr.fixed_univ_map_upd_invar)
  show ?case
  proof (cases "w = v")
    case wv: True
    have res: "reparent_walk s e v first pe pup (w # ws') (pp0, dd0) = (parent_upd pp0 w vw, dir_upd dd0 w dvw)"
      using wv by (cases first) (simp_all add: vw_def dvw_def)
    have tw0: "set (takeWhile (\<lambda>y. y \<noteq> v) (w # ws')) = {}" using wv by simp
    have pluw: "parent_lookup (parent_upd pp0 w vw) w = vw" by (simp add: plu)
    have dluw: "dir_lookup (dir_upd dd0 w dvw) w = dvw" by (simp add: dlu)
    have hw: "hd (w # ws') = w" by simp
    show ?thesis unfolding res prod.case
    proof (intro conjI)
      show "\<forall>x. x \<notin> insert v (set (takeWhile (\<lambda>y. y \<noteq> v) (w # ws'))) \<longrightarrow> parent_lookup (parent_upd pp0 w vw) x = parent_lookup pp0 x \<and> dir_lookup (dir_upd dd0 w dvw) x = dir_lookup dd0 x"
        using wv plu dlu by auto
      show "parent_lookup (parent_upd pp0 w vw) (hd (w # ws')) = (if first then e else pe)"
        unfolding hw using pluw by (simp add: vw_def)
      show "dir_lookup (dir_upd dd0 w dvw) (hd (w # ws')) = (if first then (hd (w # ws') = fst_exec e) else (\<not> pup))"
        unfolding hw using dluw by (simp add: dvw_def)
      show "\<forall>i. Suc i < length (w # ws') \<longrightarrow> (w # ws') ! i \<in> set (takeWhile (\<lambda>y. y \<noteq> v) (w # ws')) \<longrightarrow>
             parent_lookup (parent_upd pp0 w vw) ((w # ws') ! Suc i) = par_edge s ((w # ws') ! i)
           \<and> dir_lookup (dir_upd dd0 w dvw) ((w # ws') ! Suc i) = (\<not> par_up s ((w # ws') ! i))"
        using tw0 by auto
    qed
  next
    case wnv: False
    have res: "reparent_walk s e v first pe pup (w # ws') (pp0, dd0)
                 = reparent_walk s e v False (par_edge s w) (par_up s w) ws' (parent_upd pp0 w vw, dir_upd dd0 w dvw)"
      using wnv by (cases first) (simp_all add: vw_def dvw_def)
    have tw: "set (takeWhile (\<lambda>y. y \<noteq> v) (w # ws')) = insert w (set (takeWhile (\<lambda>y. y \<noteq> v) ws'))"
      using wnv by simp
    have dw': "distinct ws'" using dw by simp
    have vin': "v \<in> set ws'" using vin wnv by simp
    have hw: "hd (w # ws') = w" by simp
    have wns: "w \<notin> set ws'" using dw by simp
    obtain pr dr where res2: "reparent_walk s e v False (par_edge s w) (par_up s w) ws' (parent_upd pp0 w vw, dir_upd dd0 w dvw) = (pr, dr)"
      by (cases "reparent_walk s e v False (par_edge s w) (par_up s w) ws' (parent_upd pp0 w vw, dir_upd dd0 w dvw)")
    note IH = Cons.IH[OF dw' vin' pinv' dinv' wsV', of False "par_edge s w" "par_up s w", unfolded res2 prod.case]
    have IHoff: "\<And>x. x \<notin> insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ws')) \<Longrightarrow> parent_lookup pr x = parent_lookup (parent_upd pp0 w vw) x \<and> dir_lookup dr x = dir_lookup (dir_upd dd0 w dvw) x"
      using IH by blast
    have IHhd: "parent_lookup pr (hd ws') = par_edge s w \<and> dir_lookup dr (hd ws') = (\<not> par_up s w)"
      using IH by simp
    have IHnth: "\<And>i. Suc i < length ws' \<Longrightarrow> ws' ! i \<in> set (takeWhile (\<lambda>y. y \<noteq> v) ws') \<Longrightarrow> parent_lookup pr (ws' ! Suc i) = par_edge s (ws' ! i) \<and> dir_lookup dr (ws' ! Suc i) = (\<not> par_up s (ws' ! i))"
      using IH by blast
    have hdws': "ws' \<noteq> []" using vin' by auto
    have wnotpre': "w \<notin> insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ws'))" using wns wnv by (auto dest: set_takeWhileD)
    have prw: "parent_lookup pr w = vw \<and> dir_lookup dr w = dvw"
      using IHoff[OF wnotpre'] plu dlu by simp
    show ?thesis unfolding res res2 prod.case
    proof (intro conjI)
      show "\<forall>x. x \<notin> insert v (set (takeWhile (\<lambda>y. y \<noteq> v) (w # ws'))) \<longrightarrow> parent_lookup pr x = parent_lookup pp0 x \<and> dir_lookup dr x = dir_lookup dd0 x"
      proof (intro allI impI)
        fix x assume A: "x \<notin> insert v (set (takeWhile (\<lambda>y. y \<noteq> v) (w # ws')))"
        have x1: "x \<notin> insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ws'))" using A tw by auto
        have x2: "x \<noteq> w" using A tw by auto
        show "parent_lookup pr x = parent_lookup pp0 x \<and> dir_lookup dr x = dir_lookup dd0 x"
          using IHoff[OF x1] plu dlu x2 by simp
      qed
    next
      show "parent_lookup pr (hd (w # ws')) = (if first then e else pe)"
        unfolding hw using prw by (simp add: vw_def)
    next
      show "dir_lookup dr (hd (w # ws')) = (if first then (hd (w # ws') = fst_exec e) else (\<not> pup))"
        unfolding hw using prw by (simp add: dvw_def)
    next
      show "\<forall>i. Suc i < length (w # ws') \<longrightarrow> (w # ws') ! i \<in> set (takeWhile (\<lambda>y. y \<noteq> v) (w # ws')) \<longrightarrow>
             parent_lookup pr ((w # ws') ! Suc i) = par_edge s ((w # ws') ! i)
           \<and> dir_lookup dr ((w # ws') ! Suc i) = (\<not> par_up s ((w # ws') ! i))"
      proof (intro allI impI)
        fix i assume iL: "Suc i < length (w # ws')" and imem: "(w # ws') ! i \<in> set (takeWhile (\<lambda>y. y \<noteq> v) (w # ws'))"
        show "parent_lookup pr ((w # ws') ! Suc i) = par_edge s ((w # ws') ! i)
           \<and> dir_lookup dr ((w # ws') ! Suc i) = (\<not> par_up s ((w # ws') ! i))"
        proof (cases i)
          case 0
          show ?thesis using IHhd hdws' unfolding 0 by (simp add: hd_conv_nth)
        next
          case (Suc j)
          have jl: "j < length ws'" using iL Suc by simp
          have sj: "Suc j < length ws'" using iL Suc by simp
          have jmem: "ws' ! j \<in> set ws'" using jl by (rule nth_mem)
          have jnw: "ws' ! j \<noteq> w" using jmem wns by auto
          have mem': "ws' ! j \<in> set (takeWhile (\<lambda>y. y \<noteq> v) ws')" using imem Suc tw jnw by auto
          show ?thesis using IHnth[OF sj mem'] Suc by simp
        qed
      qed
    qed
  qed
qed

lemma reparent_arc_set:
  assumes inv: "ns_invar s"
    and sel: "ns_select s = Some (e, in_U, \<gamma>, sel')"
    and pp:  "get_path_pair (spanning_tree s) (fst e) (snd e) = (p1, p2)"
    and bn:  "bottleneck s e in_U p1 p2 = (\<delta>, False, v, e0fwd, up_side)"
    and dne: "\<delta> \<noteq> - 1"
    and rp:  "reparent s e (if in_U = up_side then p1 else p2) v = (parr, darr)"
  shows "parent_lookup parr ` (\<V> - {r}) = ns_tree_edges s - {par_edge s v} \<union> {e}"
proof -
  let ?P = "if in_U = up_side then p1 else p2"
  have eE: "e \<in> \<E>" using ns_select_SomeD(2)[OF inv sel] .
  have neq: "fst e \<noteq> snd e" using entering_not_selfloop[OF inv sel] .
  have fV: "fst e \<in> \<V>" using fst_E_V[OF eE] .
  have sV: "snd e \<in> \<V>" using snd_E_V[OF eE] .
  have arb: "arborescense_invar (spanning_tree s)" using ns_invar_implD(7)[OF ns_invarD(1)[OF inv]] .
  have pinvE: "parent_invar (parent_edge s)" using ns_invar_implD(3)[OF ns_invarD(1)[OF inv]] .
  obtain a p3 where d1: "distinct (p1 @ a # p3)" and d2: "distinct (p2 @ a # p3)"
    using get_path_pair(1)[OF arb pp neq fV sV] by blast
  have Pdist: "distinct ?P" using d1 d2 by (cases "in_U = up_side") auto
  have vP: "v \<in> set ?P" using bottleneck_pivot_facts(1)[OF inv sel pp bn] .
  have vVr: "v \<in> \<V> - {r}" using bottleneck_pivot_facts(2)[OF inv sel pp bn] .
  have PsubV: "set ?P \<subseteq> \<V> - {r}"
    using get_path_pair_verts[OF inv eE entering_not_selfloop[OF inv sel] pp] by (cases "in_U = up_side") auto
  have rpw: "reparent_walk s e v True e False ?P (parent_edge s, edge_dir s) = (parr, darr)"
    using rp by (simp add: reparent_def)
  have chc: "case reparent_walk s e v True e False ?P (parent_edge s, edge_dir s) of (parr, darr) \<Rightarrow>
       (\<forall>x. x \<notin> insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ?P)) \<longrightarrow> parent_lookup parr x = parent_lookup (parent_edge s) x)
      \<and> parent_lookup parr ` insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ?P))
         = insert (if True then e else e)
              (par_edge s ` set (takeWhile (\<lambda>y. y \<noteq> v) ?P))"
    by (rule reparent_walk_char_arc[OF Pdist vP pinvE PsubV])
  have off: "\<And>x. x \<notin> insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ?P)) \<Longrightarrow> parent_lookup parr x = par_edge s x"
    using chc unfolding rpw prod.case by (auto simp: par_edge_def)
  have spine: "parent_lookup parr ` insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ?P))
             = insert e (par_edge s ` set (takeWhile (\<lambda>y. y \<noteq> v) ?P))"
    using chc unfolding rpw prod.case by simp
  have vnotTW: "v \<notin> set (takeWhile (\<lambda>y. y \<noteq> v) ?P)" by (auto dest: set_takeWhileD)
  have TWsub: "set (takeWhile (\<lambda>y. y \<noteq> v) ?P) \<subseteq> set ?P" by (auto dest: set_takeWhileD)
  have VISsubV: "insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ?P)) \<subseteq> \<V> - {r}"
    using vVr TWsub PsubV by auto
  have setfact: "set (takeWhile (\<lambda>y. y \<noteq> v) ?P) \<union> ((\<V> - {r}) - insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ?P))) = (\<V> - {r}) - {v}"
    using TWsub PsubV vnotTW vVr by auto
  have gimg: "par_edge s ` (\<V> - {r}) = ns_tree_edges s" by (simp add: par_edge_def)
  have vsub: "{v} \<subseteq> \<V> - {r}" using vVr by simp
  have Dstep: "par_edge s ` ((\<V> - {r}) - {v}) = ns_tree_edges s - {par_edge s v}"
    using inj_on_image_set_diff[OF par_edge_inj_on[OF inv] Diff_subset vsub] gimg by simp
  have "parent_lookup parr ` (\<V> - {r})
      = parent_lookup parr ` insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ?P))
        \<union> parent_lookup parr ` ((\<V> - {r}) - insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ?P)))"
    by (metis Diff_partition[OF VISsubV] image_Un)
  also have "... = insert e (par_edge s ` set (takeWhile (\<lambda>y. y \<noteq> v) ?P))
        \<union> par_edge s ` ((\<V> - {r}) - insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ?P)))"
    by (simp only: spine, rule arg_cong[where f="\<lambda>X. insert e (par_edge s ` set (takeWhile (\<lambda>y. y \<noteq> v) ?P)) \<union> X"],
        rule image_cong[OF refl], simp add: off)
  also have "... = insert e (par_edge s ` (set (takeWhile (\<lambda>y. y \<noteq> v) ?P)
        \<union> ((\<V> - {r}) - insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ?P)))))"
    by (simp add: image_Un)
  also have "... = insert e (par_edge s ` ((\<V> - {r}) - {v}))"
    by (simp only: setfact)
  also have "... = insert e (ns_tree_edges s - {par_edge s v})"
    by (simp only: Dstep)
  finally show ?thesis by auto
qed

subsection \<open>Termination measure (lexicographic)\<close>

text \<open>The measure follows the notes' two-level construction. The \<^emph>\<open>outer\<close> level is the pair
      (flow cost, @{term \<open>- \<Sum>\<pi>\<close>}): a genuine augment (@{term \<open>\<delta> > 0\<close>}) strictly decreases the flow
      cost; a degenerate non-flip pivot (@{term \<open>\<delta> = 0\<close>}, @{term \<open>e \<noteq> e0\<close>}) keeps the cost but strictly
      increases @{term \<open>\<Sum>\<pi>\<close>}. The \<^emph>\<open>inner\<close> level, reached only when both are flat (a degenerate flip
      with @{term \<open>u e = 0\<close>}), is the number of edges violating the optimality certificate, which
      strictly decreases. Well-foundedness of the outer level rests on the finiteness of spanning-tree
      structures (KV Prop 9.25) and is deferred; here we establish the per-step \<^emph>\<open>strict decrease\<close>
      relation defined below, which is what the two recursive cases must show.\<close>

definition "possible_trees s =
  {(T, L, U) | T L U f' \<pi>'.
       spanning_tree_partition r T L U \<and>
       flow_fits_spanning_tree_partition T L U f' \<and>
       potential_fits_spanning_tree_partition r T \<pi>' \<and>
       f' is b flow \<and>
       (\<C> f' < ns_flow_cost s
        \<or> (\<C> f' = ns_flow_cost s \<and> (\<Sum> v \<in> \<V>. \<pi>' v) \<ge> ns_pot_sum s))}"

definition "ns_violation s =
  card {e \<in> ns_L_of s. reduced_cost (potentials s) e < 0}
  + card {e \<in> ns_U_of s. reduced_cost (potentials s) e > 0}"

definition "ns_less s' s \<longleftrightarrow>
    (card (possible_trees s') < card (possible_trees s))
  \<or> (card (possible_trees s') = card (possible_trees s)
      \<and> ns_violation s' < ns_violation s)"

(*
definition "ns_less s' s \<longleftrightarrow>
  ns_flow_cost s' < ns_flow_cost s
  \<or> (ns_flow_cost s' = ns_flow_cost s \<and> ns_pot_sum s' > ns_pot_sum s)
  \<or> (ns_flow_cost s' = ns_flow_cost s \<and> ns_pot_sum s' = ns_pot_sum s
      \<and> ns_violation s' < ns_violation s)"
*)
subsection \<open>Recursive-case preservation and decrease\<close>

text \<open>\<^bold>\<open>Flip branch\<close> (\S{}2). @{const ns_flip} augments the flow along the whole circuit, toggles @{term e}
      between @{term L} and @{term U}, and leaves the tree, potentials and parent/direction arrays
      untouched. Every invariant survives; strong feasibility (\S{}2, the delicate part) holds because no
      edge changes orientation and the branch's strict @{term \<open>mu > \<delta>\<close>} protects the up-side. The
      measure drops via the flow cost when @{term \<open>\<delta> > 0\<close>} and via the violation count when
      @{term \<open>\<delta> = 0\<close>}.\<close>

text \<open>\<^bold>\<open>Shared flow-lookup characterisation.\<close> Both recursive branches augment the flow the same way,
      so the per-arc lookup formula for @{const augment_flow} is factored out here.\<close>

lemma augment_flow_lookup_char:
  assumes fiE: "flow_invar (current_flow s)" and d0ge: "0 \<le> \<delta>"
    and eE: "e \<in> \<E>"
    and upE: "\<forall>w\<in>set (if in_U then p1 else p2). par_edge s w \<in> \<E>"
    and dnE: "\<forall>w\<in>set (if in_U then p2 else p1). par_edge s w \<in> \<E>"
  shows "flow_lookup (augment_flow s e in_U \<delta> p1 p2) a =
           flow_lookup (current_flow s) a + (if a = e then (if in_U then - \<delta> else \<delta>) else 0)
         + (\<Sum>w\<leftarrow>(if in_U then p1 else p2). if par_edge s w = a then (if par_up s w then \<delta> else - \<delta>) else 0)
         + (\<Sum>w\<leftarrow>(if in_U then p2 else p1). if par_edge s w = a then (if par_up s w then - \<delta> else \<delta>) else 0)"
proof -
  let ?f' = "augment_flow s e in_U \<delta> p1 p2"
  let ?ce = "if in_U then - \<delta> else \<delta>"
  let ?gup = "\<lambda>w. if par_up s w then \<delta> else - \<delta>"
  let ?gdn = "\<lambda>w. if par_up s w then - \<delta> else \<delta>"
  let ?up = "if in_U then p1 else p2"
  let ?dn = "if in_U then p2 else p1"
  show "flow_lookup ?f' a = flow_lookup (current_flow s) a + (if a = e then ?ce else 0)
        + (\<Sum>w\<leftarrow>?up. if par_edge s w = a then ?gup w else 0)
        + (\<Sum>w\<leftarrow>?dn. if par_edge s w = a then ?gdn w else 0)"
  proof (cases "\<delta> \<le> 0")
    case True
    hence d0: "\<delta> = 0" using d0ge by simp
    have cf: "flow_lookup ?f' a = flow_lookup (current_flow s) a" using True by (simp add: augment_flow_def)
    have su0: "(\<Sum>w\<leftarrow>?up. if par_edge s w = a then ?gup w else 0) = 0"
    proof -
      have "(\<Sum>w\<leftarrow>?up. if par_edge s w = a then ?gup w else 0) = (\<Sum>w\<leftarrow>?up. 0)"
        by (rule arg_cong[where f=sum_list], rule map_cong[OF refl]) (simp add: d0)
      thus ?thesis by (simp add: sum_list_0)
    qed
    have sd0: "(\<Sum>w\<leftarrow>?dn. if par_edge s w = a then ?gdn w else 0) = 0"
    proof -
      have "(\<Sum>w\<leftarrow>?dn. if par_edge s w = a then ?gdn w else 0) = (\<Sum>w\<leftarrow>?dn. 0)"
        by (rule arg_cong[where f=sum_list], rule map_cong[OF refl]) (simp add: d0)
      thus ?thesis by (simp add: sum_list_0)
    qed
    show ?thesis using cf su0 sd0 d0 by simp
  next
    case False
    let ?f0 = "flow_upd (current_flow s) e (flow_lookup (current_flow s) e + ?ce)"
    let ?f1 = "fold (\<lambda>w f. flow_upd f (par_edge s w) (flow_lookup f (par_edge s w) + ?gup w)) ?up ?f0"
    have augeq: "?f' = fold (\<lambda>w f. flow_upd f (par_edge s w) (flow_lookup f (par_edge s w) + ?gdn w)) ?dn ?f1"
      using False by (simp add: augment_flow_def Let_def)
    have fi0: "flow_invar ?f0" using fiE eE by (rule flow_arr.fixed_univ_map_upd_invar)
    have fi1: "flow_invar ?f1" using fold_flow_upd_invar[OF fi0 upE] .
    have f0val: "flow_lookup ?f0 a = (if a = e then flow_lookup (current_flow s) e + ?ce else flow_lookup (current_flow s) a)"
      using flow_arr.fixed_univ_map_upd[OF fiE eE] by (auto simp: fun_upd_def)
    have A: "flow_lookup ?f' a = flow_lookup ?f1 a + (\<Sum>w\<leftarrow>?dn. if par_edge s w = a then ?gdn w else 0)"
      unfolding augeq by (rule fold_flow_upd_lookup[OF fi1 dnE])
    have B: "flow_lookup ?f1 a = flow_lookup ?f0 a + (\<Sum>w\<leftarrow>?up. if par_edge s w = a then ?gup w else 0)"
      by (rule fold_flow_upd_lookup[OF fi0 upE])
    show ?thesis using A B f0val by simp
  qed
qed

text \<open>A self-loop's flow is untouched by an augmentation: it is neither the entering edge
      (@{thm [source] entering_not_selfloop}) nor a parent/tree edge (@{thm [source] tree_edge_not_selfloop}),
      so none of the circuit arcs coincide with it and every term of the per-arc formula vanishes.\<close>

lemma augment_flow_selfloop:
  assumes inv: "ns_invar s"
    and sel: "ns_select s = Some (e, in_U, \<gamma>, sel')"
    and pp: "get_path_pair (spanning_tree s) (fst e) (snd e) = (p1, p2)"
    and d0ge: "0 \<le> \<delta>"
    and ee: "ee \<in> \<E>" and eesl: "fst ee = snd ee"
  shows "flow_lookup (augment_flow s e in_U \<delta> p1 p2) ee = flow_lookup (current_flow s) ee"
proof -
  have eE: "e \<in> \<E>" using ns_select_SomeD(2)[OF inv sel] .
  have fiE: "flow_invar (current_flow s)" using ns_invar_implD(1)[OF ns_invarD(1)[OF inv]] .
  have tree: "ns_invar_tree s" using ns_invarD(7)[OF inv] .
  have p1V: "set p1 \<subseteq> \<V> - {r}" and p2V: "set p2 \<subseteq> \<V> - {r}"
    using get_path_pair_verts[OF inv eE entering_not_selfloop[OF inv sel] pp] by auto
  have upE: "\<forall>w\<in>set (if in_U then p1 else p2). par_edge s w \<in> \<E>"
    using p1V p2V ns_invar_tree_edgeD[OF tree] by (cases in_U) auto
  have dnE: "\<forall>w\<in>set (if in_U then p2 else p1). par_edge s w \<in> \<E>"
    using p1V p2V ns_invar_tree_edgeD[OF tree] by (cases in_U) auto
  have ene: "ee \<noteq> e" using eesl entering_not_selfloop[OF inv sel] by auto
  have parne: "\<And>w. w \<in> set p1 \<union> set p2 \<Longrightarrow> par_edge s w \<noteq> ee"
  proof -
    fix w assume "w \<in> set p1 \<union> set p2"
    hence wV: "w \<in> \<V> - {r}" using p1V p2V by auto
    have "par_edge s w \<in> ns_tree_edges s" using wV by (auto simp: par_edge_def)
    hence "fst (par_edge s w) \<noteq> snd (par_edge s w)" using tree_edge_not_selfloop[OF inv] by simp
    thus "par_edge s w \<noteq> ee" using eesl by auto
  qed
  have zero_sum: "\<And>g xs. set xs \<subseteq> set p1 \<union> set p2 \<Longrightarrow>
                    (\<Sum>w\<leftarrow>xs. if par_edge s w = ee then (g w::'n) else 0) = 0"
  proof -
    fix g :: "'a \<Rightarrow> 'n" and xs assume sub: "set xs \<subseteq> set p1 \<union> set p2"
    have "(\<Sum>w\<leftarrow>xs. if par_edge s w = ee then g w else 0) = (\<Sum>w\<leftarrow>xs. (0::'n))"
    proof (rule arg_cong[where f=sum_list], rule map_cong[OF refl])
      fix w assume "w \<in> set xs"
      hence "par_edge s w \<noteq> ee" using parne sub by auto
      thus "(if par_edge s w = ee then g w else 0) = 0" by simp
    qed
    thus "(\<Sum>w\<leftarrow>xs. if par_edge s w = ee then g w else 0) = 0" by simp
  qed
  have s1: "(\<Sum>w\<leftarrow>(if in_U then p1 else p2). if par_edge s w = ee then (if par_up s w then \<delta> else - \<delta>) else 0) = 0"
    using zero_sum[of "if in_U then p1 else p2" "\<lambda>w. if par_up s w then \<delta> else - \<delta>"] by (cases in_U) auto
  have s2: "(\<Sum>w\<leftarrow>(if in_U then p2 else p1). if par_edge s w = ee then (if par_up s w then - \<delta> else \<delta>) else 0) = 0"
    using zero_sum[of "if in_U then p2 else p1" "\<lambda>w. if par_up s w then - \<delta> else \<delta>"] by (cases in_U) auto
  show ?thesis
    using augment_flow_lookup_char[OF fiE d0ge eE upE dnE] s1 s2 ene by simp
qed

text \<open>\<^bold>\<open>Vanishing of a parent-indexed sum.\<close> If @{term a} is not a tree edge, no vertex on a
      non-root list carries it as parent, so the signed contribution telescopes to zero.\<close>

lemma sum_par_vanish:
  assumes xs: "set xs \<subseteq> \<V> - {r}" and a: "a \<notin> ns_tree_edges s"
  shows "(\<Sum>w\<leftarrow>xs. if par_edge s w = a then g w else 0) = 0"
proof -
  have ne: "\<And>w. w \<in> set xs \<Longrightarrow> par_edge s w \<noteq> a"
  proof -
    fix w assume "w \<in> set xs"
    hence "par_edge s w \<in> ns_tree_edges s" using xs by (auto simp: par_edge_def)
    thus "par_edge s w \<noteq> a" using a by blast
  qed
  have "(\<Sum>w\<leftarrow>xs. if par_edge s w = a then g w else 0) = (\<Sum>w\<leftarrow>xs. 0)"
    by (rule arg_cong[where f=sum_list], rule map_cong[OF refl]) (simp add: ne)
  thus ?thesis by (simp add: sum_list_0)
qed

text \<open>\<^bold>\<open>Single-vertex pick.\<close> On a distinct non-root list the parent-indexed sum collapses to the
      single contribution of @{term v} (if present), by injectivity of @{const par_edge}.\<close>

lemma par_sum_pick:
  assumes inv: "ns_invar s" and dx: "distinct xs" and xsV: "set xs \<subseteq> \<V> - {r}" and vV: "v \<in> \<V> - {r}"
  shows "(\<Sum>w\<leftarrow>xs. if par_edge s w = par_edge s v then g w else 0) = (if v \<in> set xs then g v else 0)"
proof -
  have cond: "\<And>w. w \<in> set xs \<Longrightarrow> (par_edge s w = par_edge s v) = (w = v)"
    using par_edge_inj[OF inv] xsV vV by blast
  have "(\<Sum>w\<leftarrow>xs. if par_edge s w = par_edge s v then g w else 0) = (\<Sum>w\<leftarrow>xs. if w = v then g w else 0)"
    by (rule arg_cong[where f=sum_list], rule map_cong[OF refl]) (simp add: cond)
  also have "... = (if v \<in> set xs then g v else 0)"
  proof (cases "v \<in> set xs")
    case True thus ?thesis using sum_list_if_eq_distinct[OF dx True] by simp
  next
    case False thus ?thesis using sum_list_if_eq_notin[OF False] by simp
  qed
  finally show ?thesis .
qed

text \<open>\<^bold>\<open>Finiteness of the tree-structure search space.\<close> Every member of @{const possible_trees}
      partitions @{term \<E>}, so the set injects into @{term "Pow \<E> \<times> Pow \<E> \<times> Pow \<E>"}.\<close>

lemma finite_possible_trees: "finite (possible_trees x)"
proof -
  have "possible_trees x \<subseteq> Pow \<E> \<times> Pow \<E> \<times> Pow \<E>"
  proof (rule subsetI)
    fix z assume "z \<in> possible_trees x"
    then obtain T L U where z: "z = (T, L, U)" and stp: "spanning_tree_partition r T L U"
      unfolding possible_trees_def by blast
    thus "z \<in> Pow \<E> \<times> Pow \<E> \<times> Pow \<E>" using spanning_tree_partitionD(1)[OF stp] z by auto
  qed
  thus ?thesis by (rule finite_subset) (simp add: finite_E)
qed

lemma ns_flip_preservation:
  assumes inv: "ns_invar s" and cond: "ns_flip_cond s"
  shows "ns_invar (ns_flip_upd s)"
    and "ns_less (ns_flip_upd s) s"
proof -
  from cond obtain e in_U \<gamma> sel' p1 p2 \<delta> v e0fwd up_side where
    sel: "ns_select s = Some (e, in_U, \<gamma>, sel')" and
    ppx: "get_path_pair (spanning_tree s) (fst_exec e) (snd_exec e) = (p1, p2)" and
    bn: "bottleneck s e in_U p1 p2 = (\<delta>, True, v, e0fwd, up_side)" and
    dne: "\<delta> \<noteq> - 1"
    by (rule ns_flip_condE)
  let ?f' = "augment_flow s e in_U \<delta> p1 p2"
  let ?s' = "ns_flip s e in_U \<gamma> sel' \<delta> p1 p2"
  have flipeq: "ns_flip_upd s = ?s'" by (simp add: ns_flip_upd_def sel ppx bn)
  have pj_tree: "spanning_tree ?s' = spanning_tree s"
    and pj_pot: "potentials ?s' = potentials s"
    and pj_par: "parent_edge ?s' = parent_edge s"
    and pj_dir: "edge_dir ?s' = edge_dir s"
    and pj_flow: "current_flow ?s' = ?f'"
    and pj_state: "edge_state ?s' = es_upd (edge_state s) e (if in_U then InL else InU)"
    and pj_sel: "edge_sel ?s' = sel'"
    by (simp_all add: ns_flip_def)
  have eE: "e \<in> \<E>" and eLU: "e \<in> ns_L_of s \<union> ns_U_of s" and entree: "e \<notin> ns_tree_edges s"
    using ns_select_SomeD(2,1,3)[OF inv sel] by blast+
  note exbr[simp] = fst_exec_coincide[OF eE] snd_exec_coincide[OF eE]
  have pp: "get_path_pair (spanning_tree s) (fst e) (snd e) = (p1, p2)" using ppx by simp
  have implS: "ns_invar_impl s" using ns_invarD(1)[OF inv] .
  have tree_eq: "ns_tree_edges ?s' = ns_tree_edges s" by (simp add: pj_par)
  have pot_eq: "ns_pot_of ?s' = ns_pot_of s" by (simp add: pj_pot)
  have paredge_eq: "\<And>v. par_edge ?s' v = par_edge s v" by (simp add: par_edge_def pj_par)
  have parup_eq: "\<And>v. par_up ?s' v = par_up s v" by (simp add: par_up_def pj_dir)
  have precond: "selection_precond (edge_sel s) (potentials s) (edge_state s)"
    using ns_invar_implD(6)[OF implS] ns_invar_implD(2)[OF implS] ns_invar_implD(5)[OF implS]
          ns_invar_pot_fitsD[OF ns_invarD(5)[OF inv]]
    by (simp add: selection_precond_def potential_fits_spanning_tree_partition_def)
  have selS: "sel_select (edge_sel s) (potentials s) (edge_state s) = Some (e, in_U, \<gamma>, sel')"
    using sel by (simp add: ns_select_def)
  have selinv': "sel_invar sel'" using sel_select_SomeD(1)[OF precond selS] .
  have gi: "rcost_invar \<gamma>" using sel_select_SomeD(2)[OF precond selS] .
  have rc_eq: "rcost_abstract \<gamma> = reduced_cost (potentials s) e" using sel_select_SomeD(3)[OF precond selS] .
  have impl': "ns_invar_impl ?s'"
  using augment_flow_flow_invar[OF inv sel pp] ns_invar_implD(2,3,4,7)[OF implS]
        es_arr.fixed_univ_map_upd_invar[OF ns_invar_implD(5)[OF implS] eE] selinv' eE
  by (auto intro!: ns_invar_implI
      simp: pj_flow pj_pot pj_par pj_dir pj_state pj_sel pj_tree)
  have parvx_eq: "\<And>v. par_vx ?s' v = par_vx s v" by (simp add: par_vx_def parup_eq paredge_eq)
  have bflow': "ns_invar_bflow ?s'"
    using augment_flow_bflow[OF inv sel pp bn dne] by (simp add: ns_invar_bflow_def pj_flow)
  have potfits': "ns_invar_pot_fits ?s'"
    using ns_invarD(5)[OF inv] by (simp add: ns_invar_pot_fits_def tree_eq pot_eq)
  have tree': "ns_invar_tree ?s'"
    using ns_invarD(7)[OF inv] by (simp add: ns_invar_tree_def paredge_eq parup_eq parvx_eq pj_tree pj_par)
  have neqe: "fst e \<noteq> snd e" using entering_not_selfloop[OF inv sel] .
  have e_nsl: "e \<notin> ns_selfloops_L" "e \<notin> ns_selfloops_U"
    using neqe by (auto simp: ns_selfloops_L_def ns_selfloops_U_def)
  have esu: "es_lookup (edge_state ?s') = (es_lookup (edge_state s))(e := (if in_U then InL else InU))"
    unfolding pj_state using es_arr.fixed_univ_map_upd[OF ns_invar_implD(5)[OF implS] eE] by simp
  have Lab: "ns_L_of ?s' = (if in_U then insert e (ns_L_of s) else ns_L_of s - {e})"
    using esu eE neqe by (auto simp: ns_L_of_def split: if_splits)
  have Uab: "ns_U_of ?s' = (if in_U then ns_U_of s - {e} else insert e (ns_U_of s))"
    using esu eE neqe by (auto simp: ns_U_of_def split: if_splits)
  have ent: "entering_edge (potentials s) (edge_state s) e in_U"
    using sel_select_SomeD(4)[OF precond selS] .
  have eside: "if in_U then e \<in> ns_U_of s else e \<in> ns_L_of s"
    using ent by (auto simp: entering_edge_def ns_L_of_def ns_U_of_def)
  have partS: "spanning_tree_partition r (ns_tree_edges s) (ns_L_of s \<union> ns_selfloops_L) (ns_U_of s \<union> ns_selfloops_U)"
    using ns_invarD(3)[OF inv] by (simp add: ns_invar_partition_def)
  note Pd = spanning_tree_partitionD[OF partS]
  have dTU: "ns_tree_edges s \<inter> ns_U_of s = {}" using Pd(2) by blast
  have dTL: "ns_tree_edges s \<inter> ns_L_of s = {}" using Pd(3) by blast
  have partition': "ns_invar_partition ?s'"
    unfolding ns_invar_partition_def tree_eq Lab Uab
  proof (rule spanning_tree_partitionI)
    show "\<E> = ns_tree_edges s \<union> ((if in_U then ns_U_of s - {e} else insert e (ns_U_of s)) \<union> ns_selfloops_U)
            \<union> ((if in_U then insert e (ns_L_of s) else ns_L_of s - {e}) \<union> ns_selfloops_L)"
      using Pd(1) eside eE by (cases in_U) auto
    show "ns_tree_edges s \<inter> ((if in_U then ns_U_of s - {e} else insert e (ns_U_of s)) \<union> ns_selfloops_U) = {}"
      using dTU dTL entree Pd(2) by (cases in_U) auto
    show "ns_tree_edges s \<inter> ((if in_U then insert e (ns_L_of s) else ns_L_of s - {e}) \<union> ns_selfloops_L) = {}"
      using dTU dTL entree Pd(3) by (cases in_U) auto
    show "((if in_U then insert e (ns_L_of s) else ns_L_of s - {e}) \<union> ns_selfloops_L)
            \<inter> ((if in_U then ns_U_of s - {e} else insert e (ns_U_of s)) \<union> ns_selfloops_U) = {}"
      using Pd(4) eside e_nsl by (cases in_U) auto
    show "graph_abs.arborescence ((\<lambda>e. {fst e, snd e}) ` ns_tree_edges s) r ((\<lambda>e. {fst e, snd e}) ` ns_tree_edges s)"
      using Pd(5) .
    show "graph_abs ((\<lambda>e. {fst e, snd e}) ` ns_tree_edges s)" using Pd(6) .
    show "\<forall>ee ee'. {ee, ee'} \<subseteq> ns_tree_edges s \<and> {fst ee, snd ee} = {fst ee', snd ee'} \<longrightarrow> ee = ee'"
      using Pd(7) .
    show "dVs (make_pair ` ns_tree_edges s) = \<V>" using Pd(8) .
  qed
  have arbb: "arborescense_invar (spanning_tree s)" using ns_invar_implD(7)[OF implS] .
  have neq: "fst e \<noteq> snd e" using entering_not_selfloop[OF inv sel] .
  have fVe: "fst e \<in> \<V>" using fst_E_V[OF eE] .
  have sVe: "snd e \<in> \<V>" using snd_E_V[OF eE] .
  have fiE: "flow_invar (current_flow s)" using ns_invar_implD(1)[OF implS] .
  have treeinv: "ns_invar_tree s" using ns_invarD(7)[OF inv] .
  have d0ge: "0 \<le> \<delta>" using bottleneck_delta_bounds(1)[OF inv sel pp bn dne] .
  let ?ce = "if in_U then - \<delta> else \<delta>"
  let ?gup = "\<lambda>w. if par_up s w then \<delta> else - \<delta>"
  let ?gdn = "\<lambda>w. if par_up s w then - \<delta> else \<delta>"
  let ?up = "if in_U then p1 else p2"
  let ?dn = "if in_U then p2 else p1"
  have p1Vc: "set p1 \<subseteq> \<V> - {r}" and p2Vc: "set p2 \<subseteq> \<V> - {r}"
    using get_path_pair_verts[OF inv eE entering_not_selfloop[OF inv sel] pp] by auto
  have upEc: "\<forall>w\<in>set ?up. par_edge s w \<in> \<E>" using p1Vc p2Vc ns_invar_tree_edgeD[OF treeinv] by (cases in_U) auto
  have dnEc: "\<forall>w\<in>set ?dn. par_edge s w \<in> \<E>" using p1Vc p2Vc ns_invar_tree_edgeD[OF treeinv] by (cases in_U) auto
  have fval: "\<And>a. flow_lookup ?f' a = flow_lookup (current_flow s) a + (if a = e then ?ce else 0)
        + (\<Sum>w\<leftarrow>?up. if par_edge s w = a then ?gup w else 0)
        + (\<Sum>w\<leftarrow>?dn. if par_edge s w = a then ?gdn w else 0)"
    by (rule augment_flow_lookup_char[OF fiE d0ge eE upEc dnEc])
  obtain mu vu where su: "scan_up s ?up = (mu, vu)" by (cases "scan_up s ?up")
  obtain md vd where sd: "scan_down s ?dn = (md, vd)" by (cases "scan_down s ?dn")
  have p1V: "set p1 \<subseteq> \<V> - {r}" and p2V: "set p2 \<subseteq> \<V> - {r}"
    using get_path_pair_verts[OF inv eE entering_not_selfloop[OF inv sel] pp] by auto
  have upV: "set ?up \<subseteq> \<V> - {r}" using p1V p2V by (cases in_U) auto
  have dnV: "set ?dn \<subseteq> \<V> - {r}" using p1V p2V by (cases in_U) auto
  define re where "re = (if in_U then res_bwd s e else res_fwd s e)"
  define dd where "dd = mininf re (mininf mu md)"
  have bform: "bottleneck s e in_U p1 p2 =
     (if dd = - 1 then (- 1, True, r, False, False)
      else if mu \<noteq> - 1 \<and> mu = dd then (dd, False, vu, par_up s vu, True)
      else if re = dd then (dd, True, r, False, False)
      else (dd, False, vd, \<not> par_up s vd, False))"
    unfolding bottleneck_def Let_def su sd re_def dd_def by simp
  have flip_re: "re = \<delta>" and mu_alt: "mu = - 1 \<or> mu \<noteq> \<delta>" and deq: "\<delta> = dd"
    using bn dne unfolding bform by (auto split: if_splits)
  have muS: "0 \<le> mu \<or> mu = - 1" using scan_up_val_sign[OF inv upV su] .
  have mdS: "0 \<le> md \<or> md = - 1" using scan_down_val_sign[OF inv dnV sd] .
  have flip_mu: "mu \<noteq> - 1 \<Longrightarrow> \<delta> < mu"
  proof -
    assume muNe: "mu \<noteq> - 1"
    hence muNN: "0 \<le> mu" using muS by simp
    have mmNe: "mininf mu md \<noteq> - 1" using mininf_nonneg[OF muNN mdS] by simp
    have "\<delta> \<le> mininf mu md" using deq mininf_le2[OF mmNe] by (simp add: dd_def)
    also have "... \<le> mu" using mininf_le1[OF muNe] .
    finally have "\<delta> \<le> mu" .
    thus "\<delta> < mu" using mu_alt muNe by auto
  qed
  have parE: "\<And>w. w \<in> \<V> - {r} \<Longrightarrow> par_edge s w \<in> ns_tree_edges s" by (auto simp: par_edge_def)
  have sum_up_vanish: "\<And>a. a \<notin> ns_tree_edges s \<Longrightarrow> (\<Sum>w\<leftarrow>?up. if par_edge s w = a then ?gup w else 0) = 0"
    by (rule sum_par_vanish[OF upV])
  have sum_dn_vanish: "\<And>a. a \<notin> ns_tree_edges s \<Longrightarrow> (\<Sum>w\<leftarrow>?dn. if par_edge s w = a then ?gdn w else 0) = 0"
    by (rule sum_par_vanish[OF dnV])
  have e_flow: "flow_lookup ?f' e = flow_lookup (current_flow s) e + ?ce"
    using fval[of e] sum_up_vanish[OF entree] sum_dn_vanish[OF entree] by simp
  have notin_flow: "\<And>a. a \<notin> ns_tree_edges s \<Longrightarrow> a \<noteq> e \<Longrightarrow> flow_lookup ?f' a = flow_lookup (current_flow s) a"
    using fval sum_up_vanish sum_dn_vanish by simp
  have LUfit: "flow_fits_spanning_tree_partition (ns_tree_edges s) (ns_L_of s) (ns_U_of s) (ns_flow_of s)"
    using ns_invarD(4)[OF inv] by (simp add: ns_invar_flow_fits_def)
  have Lfit: "\<And>a. a \<in> ns_L_of s \<Longrightarrow> flow_lookup (current_flow s) a = 0"
    using LUfit by (simp add: flow_fits_spanning_tree_partition_def)
  have Ufit: "\<And>a. a \<in> ns_U_of s \<Longrightarrow> ereal (h (flow_lookup (current_flow s) a)) = \<u> a"
    using LUfit by (simp add: flow_fits_spanning_tree_partition_def)
  have Lnt: "\<And>a. a \<in> ns_L_of s \<Longrightarrow> a \<notin> ns_tree_edges s" using dTL by auto
  have Unt: "\<And>a. a \<in> ns_U_of s \<Longrightarrow> a \<notin> ns_tree_edges s" using dTU by auto
  have flow_eq: "ns_flow_of ?s' = h \<circ> flow_lookup ?f'" by (simp add: pj_flow)
  have e_flow_L: "in_U \<Longrightarrow> flow_lookup ?f' e = 0"
    using e_flow flip_re by (simp add: re_def res_bwd_def)
  have e_flow_U: "\<not> in_U \<Longrightarrow> ereal (h (flow_lookup ?f' e)) = \<u> e"
  proof -
    assume iu: "\<not> in_U"
    have cf0: "flow_lookup (current_flow s) e = 0" using Lfit eside iu by simp
    have capne: "cap e \<noteq> - 1" using flip_re dne iu by (auto simp: re_def res_fwd_def split: if_splits)
    hence "\<delta> = cap e" using flip_re cf0 iu by (simp add: re_def res_fwd_def)
    thus "ereal (h (flow_lookup ?f' e)) = \<u> e"
      using e_flow iu cf0 capne cap_nonneg[OF eE] cap_finite[OF eE] by simp
  qed
  have flowfits': "ns_invar_flow_fits ?s'"
    unfolding ns_invar_flow_fits_def tree_eq pj_flow Lab Uab flow_fits_spanning_tree_partition_def comp_def
  proof (intro conjI ballI)
    fix a assume aL: "a \<in> (if in_U then insert e (ns_L_of s) else ns_L_of s - {e})"
    show "h (flow_lookup ?f' a) = 0"
    proof (cases "a = e")
      case True
      have iu: "in_U" using aL True by (cases in_U) auto
      thus ?thesis using e_flow_L True by simp
    next
      case False
      have aLs: "a \<in> ns_L_of s" using aL False by (cases in_U) auto
      have "flow_lookup ?f' a = flow_lookup (current_flow s) a" using notin_flow[OF Lnt[OF aLs] False] .
      thus ?thesis using Lfit[OF aLs] by simp
    qed
  next
    fix a assume aU: "a \<in> (if in_U then ns_U_of s - {e} else insert e (ns_U_of s))"
    show "ereal (h (flow_lookup ?f' a)) = \<u> a"
    proof (cases "a = e")
      case True
      have iu: "\<not> in_U" using aU True by (cases in_U) auto
      thus ?thesis using e_flow_U True by simp
    next
      case False
      have aUs: "a \<in> ns_U_of s" using aU False by (cases in_U) auto
      have "flow_lookup ?f' a = flow_lookup (current_flow s) a" using notin_flow[OF Unt[OF aUs] False] .
      thus ?thesis using Ufit[OF aUs] by simp
    qed
  qed
  obtain a0 p3 where d1a: "distinct (p1 @ a0 # p3)" and d2a: "distinct (p2 @ a0 # p3)"
    using get_path_pair(1)[OF arbb pp neq fVe sVe] by blast
  have updist: "distinct ?up" using d1a d2a by (cases in_U) auto
  have dndist: "distinct ?dn" using d1a d2a by (cases in_U) auto
  have sumpick: "\<And>v xs g. distinct xs \<Longrightarrow> set xs \<subseteq> \<V> - {r} \<Longrightarrow> v \<in> \<V> - {r} \<Longrightarrow>
     (\<Sum>w\<leftarrow>xs. if par_edge s w = par_edge s v then (g w::'n) else 0) = (if v \<in> set xs then g v else 0)"
    using par_sum_pick[OF inv] by blast
  have treeval: "\<And>v. v \<in> \<V> - {r} \<Longrightarrow> flow_lookup ?f' (par_edge s v)
       = flow_lookup (current_flow s) (par_edge s v) + (if v \<in> set ?up then ?gup v else 0) + (if v \<in> set ?dn then ?gdn v else 0)"
  proof -
    fix v assume vV: "v \<in> \<V> - {r}"
    have pne: "par_edge s v \<noteq> e" using parE[OF vV] entree by blast
    have "flow_lookup ?f' (par_edge s v) = flow_lookup (current_flow s) (par_edge s v)
        + (if par_edge s v = e then ?ce else 0)
        + (\<Sum>w\<leftarrow>?up. if par_edge s w = par_edge s v then ?gup w else 0)
        + (\<Sum>w\<leftarrow>?dn. if par_edge s w = par_edge s v then ?gdn w else 0)"
      using fval[of "par_edge s v"] .
    thus "flow_lookup ?f' (par_edge s v)
       = flow_lookup (current_flow s) (par_edge s v) + (if v \<in> set ?up then ?gup v else 0) + (if v \<in> set ?dn then ?gdn v else 0)"
      using pne sumpick[OF updist upV vV] sumpick[OF dndist dnV vV] by simp
  qed
  have up_res: "\<And>v. v \<in> set ?up \<Longrightarrow> res_up s v = - 1 \<or> \<delta> < res_up s v"
  proof -
    fix v assume vup: "v \<in> set ?up"
    show "res_up s v = - 1 \<or> \<delta> < res_up s v"
    proof (cases "res_up s v = - 1")
      case True thus ?thesis by simp
    next
      case False
      have "mu \<noteq> - 1 \<and> mu \<le> res_up s v" using scan_up_min[OF su vup False] .
      thus ?thesis using flip_mu by auto
    qed
  qed
  have oldstrict: "\<And>v. v \<in> \<V> - {r} \<Longrightarrow> (if par_up s v then ereal (h (flow_lookup (current_flow s) (par_edge s v))) < \<u> (par_edge s v) else flow_lookup (current_flow s) (par_edge s v) > 0)"
    using ns_invarD(6)[OF inv] by (simp add: ns_invar_strict_def)
  have updisj: "set ?up \<inter> set ?dn = {}"
    using get_path_pair_align(4)[OF inv sel pp] by (cases in_U) auto
  have strict': "ns_invar_strict ?s'"
    unfolding ns_invar_strict_def
  proof (rule ballI)
    fix v assume vV: "v \<in> \<V> - {r}"
    have paredge_E: "par_edge s v \<in> \<E>" using ns_invar_tree_edgeD[OF treeinv vV] .
    have iu: "isuflow (ns_flow_of s)" using ns_invar_bflowD[OF ns_invarD(2)[OF inv]] by (simp add: isbflow_def)
    have cfnn: "0 \<le> flow_lookup (current_flow s) (par_edge s v)"
      using res_bwd_nonneg[OF inv paredge_E] by (simp add: res_bwd_def)
    have tv: "flow_lookup ?f' (par_edge s v) = flow_lookup (current_flow s) (par_edge s v)
         + (if v \<in> set ?up then ?gup v else 0) + (if v \<in> set ?dn then ?gdn v else 0)"
      using treeval[OF vV] .
    have base: "if par_up s v then ereal (h (flow_lookup ?f' (par_edge s v))) < \<u> (par_edge s v)
                else flow_lookup ?f' (par_edge s v) > 0"
    proof (cases "v \<in> set ?up")
      case inup: True
      hence vnd: "v \<notin> set ?dn" using updisj by auto
      have tv': "flow_lookup ?f' (par_edge s v) = flow_lookup (current_flow s) (par_edge s v) + ?gup v"
        using tv inup vnd by simp
      show ?thesis
      proof (cases "par_up s v")
        case pu: True
        have rue: "res_up s v = res_fwd s (par_edge s v)" using pu by (simp add: res_up_def)
        have "ereal (h (flow_lookup ?f' (par_edge s v))) < \<u> (par_edge s v)"
        proof (cases "cap (par_edge s v) = - 1")
          case True
          hence "\<u> (par_edge s v) = \<infinity>" using cap_infinite[OF paredge_E] by simp
          thus ?thesis by simp
        next
          case cfin: False
          hence cnn: "0 \<le> cap (par_edge s v)" using cap_nonneg[OF paredge_E] by simp
          have ue: "\<u> (par_edge s v) = ereal (h (cap (par_edge s v)))" using cap_finite[OF paredge_E cnn] .
          have cfle: "flow_lookup (current_flow s) (par_edge s v) \<le> cap (par_edge s v)"
            using iu paredge_E ue by (auto simp: isuflow_def comp_def)
          have rup: "res_up s v = cap (par_edge s v) - flow_lookup (current_flow s) (par_edge s v)"
            using rue cfin by (simp add: res_fwd_def)
          have "res_up s v \<noteq> - 1" using rup cfle by linarith
          hence "\<delta> < res_up s v" using up_res[OF inup] by simp
          hence "flow_lookup (current_flow s) (par_edge s v) + \<delta> < cap (par_edge s v)" using rup by simp
          thus ?thesis using tv' pu ue by simp
        qed
        thus ?thesis using pu by simp
      next
        case pd: False
        have rbv: "res_up s v = flow_lookup (current_flow s) (par_edge s v)"
          using pd by (simp add: res_up_def res_bwd_def)
        have "res_up s v \<noteq> - 1" using rbv cfnn by linarith
        hence "\<delta> < res_up s v" using up_res[OF inup] by simp
        hence "flow_lookup (current_flow s) (par_edge s v) - \<delta> > 0" using rbv by simp
        thus ?thesis using tv' pd by simp
      qed
    next
      case notup: False
      show ?thesis
      proof (cases "v \<in> set ?dn")
        case indn: True
        have tv': "flow_lookup ?f' (par_edge s v) = flow_lookup (current_flow s) (par_edge s v) + ?gdn v"
          using tv notup indn by simp
        show ?thesis
        proof (cases "par_up s v")
          case True
          have f'eq: "flow_lookup ?f' (par_edge s v) = flow_lookup (current_flow s) (par_edge s v) - \<delta>"
            using tv' True by simp
          have "ereal (h (flow_lookup ?f' (par_edge s v))) \<le> ereal (h (flow_lookup (current_flow s) (par_edge s v)))"
            using f'eq d0ge by simp
          also have "... < \<u> (par_edge s v)" using oldstrict[OF vV] True by simp
          finally show ?thesis using True by simp
        next
          case False
          have "flow_lookup ?f' (par_edge s v) = flow_lookup (current_flow s) (par_edge s v) + \<delta>"
            using tv' False by simp
          thus ?thesis using oldstrict[OF vV] False d0ge by simp
        qed
      next
        case notdn: False
        have "flow_lookup ?f' (par_edge s v) = flow_lookup (current_flow s) (par_edge s v)"
          using tv notup notdn by simp
        thus ?thesis using oldstrict[OF vV] by simp
      qed
    qed
    show "if par_up ?s' v then ereal (h (flow_lookup (current_flow ?s') (par_edge ?s' v))) < \<u> (par_edge ?s' v)
          else flow_lookup (current_flow ?s') (par_edge ?s' v) > 0"
      using base by (simp add: parup_eq paredge_eq pj_flow)
  qed
  have selfloop': "ns_invar_selfloop ?s'"
    unfolding ns_invar_selfloop_def
  proof (intro ballI impI)
    fix ee assume eeE: "ee \<in> \<E>" and eesl: "fst ee = snd ee"
    have "flow_lookup ?f' ee = flow_lookup (current_flow s) ee"
      using augment_flow_selfloop[OF inv sel pp d0ge eeE eesl] .
    hence feq: "ns_flow_of ?s' ee = ns_flow_of s ee" by (simp add: flow_eq)
    thus "(0 \<le> \<c> ee \<longrightarrow> ns_flow_of ?s' ee = 0) \<and> (\<c> ee < 0 \<longrightarrow> ereal (ns_flow_of ?s' ee) = \<u> ee)"
      using ns_invarD(8)[OF inv] eeE eesl by (simp add: ns_invar_selfloop_def)
  qed
  show "ns_invar (ns_flip_upd s)"
    unfolding flipeq
    using ns_invarI[OF impl' bflow' partition' flowfits' potfits' strict' tree' selfloop'] .
  have costeq: "ns_flow_cost (ns_flip_upd s)
       = ns_flow_cost s + (if in_U then - h \<delta> else h \<delta>) * reduced_cost (potentials s) e"
    using augment_flow_cost[OF inv sel pp bn dne] by (simp add: flipeq ns_flow_cost_def flow_eq)
  have poteq: "ns_pot_sum (ns_flip_upd s) = ns_pot_sum s"
    unfolding flipeq ns_pot_sum_def pot_eq by (rule refl)
  have rcpos: "in_U \<Longrightarrow> reduced_cost (potentials s) e > 0" using ent by (simp add: entering_edge_def)
  have rcneg: "\<not> in_U \<Longrightarrow> reduced_cost (potentials s) e < 0" using ent by (simp add: entering_edge_def)
  have chg_le: "(if in_U then - h \<delta> else h \<delta>) * reduced_cost (potentials s) e \<le> 0"
    using d0ge rcpos rcneg by (cases in_U) (auto simp: mult_le_0_iff)
  have chg_lt: "0 < \<delta> \<Longrightarrow> (if in_U then - h \<delta> else h \<delta>) * reduced_cost (potentials s) e < 0"
    using rcpos rcneg by (cases in_U) (auto simp: mult_less_0_iff)
  have cle: "ns_flow_cost (ns_flip_upd s) \<le> ns_flow_cost s" using costeq chg_le by simp
  have clt: "0 < \<delta> \<Longrightarrow> ns_flow_cost (ns_flip_upd s) < ns_flow_cost s" using costeq chg_lt by simp
  have stp_s: "spanning_tree_partition r (ns_tree_edges s) (ns_L_of s \<union> ns_selfloops_L) (ns_U_of s \<union> ns_selfloops_U)"
    using ns_invarD(3)[OF inv] by (simp add: ns_invar_partition_def)
  have ffit_s: "flow_fits_spanning_tree_partition (ns_tree_edges s) (ns_L_of s) (ns_U_of s) (ns_flow_of s)"
    using ns_invarD(4)[OF inv] by (simp add: ns_invar_flow_fits_def)
  have pfit_s: "potential_fits_spanning_tree_partition r (ns_tree_edges s) (ns_pot_of s)"
    using ns_invarD(5)[OF inv] by (simp add: ns_invar_pot_fits_def)
  have bflow_s: "(ns_flow_of s) is b flow" using ns_invar_bflowD[OF ns_invarD(2)[OF inv]] .
  have finPT: "\<And>x. finite (possible_trees x)" by (rule finite_possible_trees)
  have rcflip: "reduced_cost (potentials (ns_flip_upd s)) = reduced_cost (potentials s)"
    by (simp add: flipeq pj_pot)
  have Lflip: "ns_L_of (ns_flip_upd s) = (if in_U then insert e (ns_L_of s) else ns_L_of s - {e})"
    by (simp add: flipeq Lab)
  have Uflip: "ns_U_of (ns_flip_upd s) = (if in_U then ns_U_of s - {e} else insert e (ns_U_of s))"
    by (simp add: flipeq Uab)
  have LsubE: "ns_L_of s \<subseteq> \<E>" and UsubE: "ns_U_of s \<subseteq> \<E>"
    using stp_s by (auto simp: spanning_tree_partition_def)
  have finL: "finite (ns_L_of s)" using finite_subset[OF LsubE finite_E] .
  have finU: "finite (ns_U_of s)" using finite_subset[OF UsubE finite_E] .
  have violflip: "ns_violation (ns_flip_upd s)
    = card {e' \<in> (if in_U then insert e (ns_L_of s) else ns_L_of s - {e}). reduced_cost (potentials s) e' < 0}
    + card {e' \<in> (if in_U then ns_U_of s - {e} else insert e (ns_U_of s)). reduced_cost (potentials s) e' > 0}"
    by (simp only: ns_violation_def rcflip Lflip Uflip)
  show "ns_less (ns_flip_upd s) s"
  proof (cases "\<delta> = 0")
    case dz: True
    have c0: "ns_flow_cost (ns_flip_upd s) = ns_flow_cost s" using costeq dz by simp
    have pt_eq: "possible_trees (ns_flip_upd s) = possible_trees s"
      by (simp only: possible_trees_def c0 poteq)
    have cardeq: "card (possible_trees (ns_flip_upd s)) = card (possible_trees s)" using pt_eq by simp
    have "ns_violation (ns_flip_upd s) < ns_violation s"
    proof (cases in_U)
      case iu: True
      have eU: "e \<in> ns_U_of s" using eside iu by simp
      have rce: "reduced_cost (potentials s) e > 0" using rcpos iu by simp
      have Lviol: "{e' \<in> insert e (ns_L_of s). reduced_cost (potentials s) e' < 0}
                 = {e' \<in> ns_L_of s. reduced_cost (potentials s) e' < 0}"
        using rce by auto
      have Uviol: "{e' \<in> ns_U_of s - {e}. reduced_cost (potentials s) e' > 0}
                 = {e' \<in> ns_U_of s. reduced_cost (potentials s) e' > 0} - {e}" by auto
      have eUv: "e \<in> {e' \<in> ns_U_of s. reduced_cost (potentials s) e' > 0}" using eU rce by simp
      have finUv: "finite {e' \<in> ns_U_of s. reduced_cost (potentials s) e' > 0}" using finU by simp
      have cardU: "card {e' \<in> ns_U_of s - {e}. reduced_cost (potentials s) e' > 0}
                 = card {e' \<in> ns_U_of s. reduced_cost (potentials s) e' > 0} - 1"
        using Uviol eUv finUv by (simp add: card_Diff_singleton)
      have Bpos: "0 < card {e' \<in> ns_U_of s. reduced_cost (potentials s) e' > 0}"
        using eUv finUv card_gt_0_iff by blast
      have "ns_violation (ns_flip_upd s)
          = card {e' \<in> ns_L_of s. reduced_cost (potentials s) e' < 0}
          + (card {e' \<in> ns_U_of s. reduced_cost (potentials s) e' > 0} - 1)"
        unfolding violflip using iu Lviol cardU by simp
      thus ?thesis using Bpos by (simp add: ns_violation_def)
    next
      case iu: False
      have eL: "e \<in> ns_L_of s" using eside iu by simp
      have rce: "reduced_cost (potentials s) e < 0" using rcneg iu by simp
      have Uviol: "{e' \<in> insert e (ns_U_of s). reduced_cost (potentials s) e' > 0}
                 = {e' \<in> ns_U_of s. reduced_cost (potentials s) e' > 0}"
        using rce by auto
      have Lviol: "{e' \<in> ns_L_of s - {e}. reduced_cost (potentials s) e' < 0}
                 = {e' \<in> ns_L_of s. reduced_cost (potentials s) e' < 0} - {e}" by auto
      have eLv: "e \<in> {e' \<in> ns_L_of s. reduced_cost (potentials s) e' < 0}" using eL rce by simp
      have finLv: "finite {e' \<in> ns_L_of s. reduced_cost (potentials s) e' < 0}" using finL by simp
      have cardL: "card {e' \<in> ns_L_of s - {e}. reduced_cost (potentials s) e' < 0}
                 = card {e' \<in> ns_L_of s. reduced_cost (potentials s) e' < 0} - 1"
        using Lviol eLv finLv by (simp add: card_Diff_singleton)
      have Bpos: "0 < card {e' \<in> ns_L_of s. reduced_cost (potentials s) e' < 0}"
        using eLv finLv card_gt_0_iff by blast
      have "ns_violation (ns_flip_upd s)
          = (card {e' \<in> ns_L_of s. reduced_cost (potentials s) e' < 0} - 1)
          + card {e' \<in> ns_U_of s. reduced_cost (potentials s) e' > 0}"
        unfolding violflip using iu Uviol cardL by simp
      thus ?thesis using Bpos by (simp add: ns_violation_def)
    qed
    thus ?thesis unfolding ns_less_def using cardeq by simp
  next
    case dnz: False
    hence dpos: "0 < \<delta>" using d0ge by simp
    have sub: "possible_trees (ns_flip_upd s) \<subseteq> possible_trees s"
    proof
      fix z assume "z \<in> possible_trees (ns_flip_upd s)"
      then obtain T L U f' \<pi>' where z: "z = (T, L, U)"
        and A1: "spanning_tree_partition r T L U"
        and A2: "flow_fits_spanning_tree_partition T L U f'"
        and A3: "potential_fits_spanning_tree_partition r T \<pi>'"
        and A4: "f' is b flow"
        and A56: "\<C> f' < ns_flow_cost (ns_flip_upd s)
                  \<or> (\<C> f' = ns_flow_cost (ns_flip_upd s) \<and> (\<Sum>v\<in>\<V>. \<pi>' v) \<ge> ns_pot_sum (ns_flip_upd s))"
        unfolding possible_trees_def by blast
      have A5le: "\<C> f' \<le> ns_flow_cost (ns_flip_upd s)" using A56 by auto
      have B5: "\<C> f' < ns_flow_cost s" using le_less_trans[OF A5le clt[OF dpos]] .
      show "z \<in> possible_trees s"
        unfolding possible_trees_def using z A1 A2 A3 A4 B5 by blast
    qed
    have slinv: "ns_invar_selfloop s" using ns_invarD(8)[OF inv] .
    have ffit_aug: "flow_fits_spanning_tree_partition (ns_tree_edges s)
         (ns_L_of s \<union> ns_selfloops_L) (ns_U_of s \<union> ns_selfloops_U) (ns_flow_of s)"
      using ffit_s slinv
      by (auto simp: flow_fits_spanning_tree_partition_def ns_selfloops_L_def ns_selfloops_U_def
                     ns_invar_selfloop_def)
    have old_in: "(ns_tree_edges s, ns_L_of s \<union> ns_selfloops_L, ns_U_of s \<union> ns_selfloops_U) \<in> possible_trees s"
      unfolding possible_trees_def using stp_s ffit_aug pfit_s bflow_s
      by (auto simp: ns_flow_cost_def ns_pot_sum_def)
    have old_notin: "(ns_tree_edges s, ns_L_of s \<union> ns_selfloops_L, ns_U_of s \<union> ns_selfloops_U) \<notin> possible_trees (ns_flip_upd s)"
    proof
      assume "(ns_tree_edges s, ns_L_of s \<union> ns_selfloops_L, ns_U_of s \<union> ns_selfloops_U) \<in> possible_trees (ns_flip_upd s)"
      then obtain f' \<pi>' where
        B2: "flow_fits_spanning_tree_partition (ns_tree_edges s) (ns_L_of s \<union> ns_selfloops_L) (ns_U_of s \<union> ns_selfloops_U) f'"
        and B4: "f' is b flow"
        and B56: "\<C> f' < ns_flow_cost (ns_flip_upd s)
                  \<or> (\<C> f' = ns_flow_cost (ns_flip_upd s) \<and> (\<Sum>v\<in>\<V>. \<pi>' v) \<ge> ns_pot_sum (ns_flip_upd s))"
        by (auto simp: possible_trees_def)
      have B5: "\<C> f' \<le> ns_flow_cost (ns_flip_upd s)" using B56 by auto
      have unique: "\<And>a. a \<in> \<E> \<Longrightarrow> f' a = ns_flow_of s a"
        using spanning_flow_unique[OF B4 bflow_s stp_s B2 ffit_aug] by simp
      have "\<C> f' = \<C> (ns_flow_of s)"
        unfolding \<C>_def by (rule sum.cong[OF refl]) (simp add: unique)
      hence "ns_flow_cost s \<le> ns_flow_cost (ns_flip_upd s)" using B5 by (simp add: ns_flow_cost_def)
      thus False using clt[OF dpos] by simp
    qed
    have "possible_trees (ns_flip_upd s) \<subset> possible_trees s"
      using sub old_in old_notin by blast
    hence "card (possible_trees (ns_flip_upd s)) < card (possible_trees s)"
      by (rule psubset_card_mono[OF finPT])
    thus ?thesis unfolding ns_less_def by simp
  qed
qed

text \<open>\<^bold>\<open>Scan tie-break lemmas.\<close> The heart of strong-feasibility preservation. @{const scan_up} keeps the
      \<^emph>\<open>last\<close> minimiser (updates on \<open>\<le>\<close>), @{const scan_down} the \<^emph>\<open>first\<close> (updates on \<open><\<close>). Hence on the
      reversed spine there is \<^emph>\<open>no\<close> minimiser but the leaving vertex itself: everything strictly before a
      @{const scan_down} minimiser (resp. after a @{const scan_up} one) has a \<^emph>\<open>strictly larger\<close> residual.
      The proofs rest on a fold invariant: the running best changes only to the current element, so once
      the returned best is fixed, later (resp. earlier) elements could not have tied it.\<close>

lemma sd_fold_keep:
  fixes s
  defines "stp \<equiv> (\<lambda>x acc. case acc of (m, best) \<Rightarrow> let rr = res_down s x in if rr = - 1 then (m, best) else if m = - 1 then (rr, x) else if rr < m then (rr, x) else (m, best))"
  shows "fold stp post Y = (m, v) \<Longrightarrow> v \<notin> set post \<Longrightarrow> fold stp post Y = Y"
proof (induction post arbitrary: Y)
  case Nil thus ?case by simp
next
  case (Cons a post')
  have vna: "v \<noteq> a" and vnp: "v \<notin> set post'" using Cons.prems(2) by auto
  have res: "fold stp post' (stp a Y) = (m, v)" using Cons.prems(1) by simp
  have keepa: "stp a Y = Y"
  proof (rule ccontr)
    assume ne: "stp a Y \<noteq> Y"
    obtain m0 best0 where Y: "Y = (m0, best0)" by (cases Y)
    have stpa: "stp a Y = (res_down s a, a)"
      using ne unfolding stp_def Y by (auto simp: Let_def split: if_splits)
    have r2: "fold stp post' (res_down s a, a) = (m, v)" using res stpa by simp
    have "fold stp post' (res_down s a, a) = (res_down s a, a)"
      using Cons.IH[of "(res_down s a, a)"] r2 vnp by blast
    hence "(res_down s a, a) = (m, v)" using r2 by simp
    thus False using vna by simp
  qed
  have r3: "fold stp post' Y = (m, v)" using res keepa by simp
  have "fold stp post' Y = Y" using Cons.IH[of Y] r3 vnp by blast
  thus ?case using keepa by simp
qed

lemma scan_down_before:
  assumes sc: "scan_down s p = (m, v)" and mne: "m \<noteq> - 1" and dp: "distinct p"
    and win: "w \<in> set (takeWhile (\<lambda>y. y \<noteq> v) p)" and wne: "res_down s w \<noteq> - 1"
  shows "m < res_down s w"
proof -
  define stp where "stp = (\<lambda>x acc. case acc of (m, best) \<Rightarrow> let rr = res_down s x in if rr = - 1 then (m, best) else if m = - 1 then (rr, x) else if rr < m then (rr, x) else (m, best))"
  have sdfold: "\<And>q. scan_down s q = fold stp q (- 1, r)" by (simp add: scan_down_def stp_def)
  have vmem: "v \<in> set p" using sc mne scan_down_snd_mem by blast
  define pre where "pre = takeWhile (\<lambda>y. y \<noteq> v) p"
  define post where "post = tl (dropWhile (\<lambda>y. y \<noteq> v) p)"
  have dwne: "dropWhile (\<lambda>y. y \<noteq> v) p \<noteq> []" using vmem by (auto simp: dropWhile_eq_Nil_conv)
  have dwhd: "hd (dropWhile (\<lambda>y. y \<noteq> v) p) = v" using dwne by (metis (mono_tags, lifting) hd_dropWhile)
  have dwv: "dropWhile (\<lambda>y. y \<noteq> v) p = v # post" using hd_Cons_tl[OF dwne] dwhd by (simp add: post_def)
  have psplit: "p = pre @ v # post"
    using takeWhile_dropWhile_id[of "\<lambda>y. y \<noteq> v" p] dwv by (simp add: pre_def)
  have vpost: "v \<notin> set post" using dp psplit by auto
  have vpre: "v \<notin> set pre" by (auto simp: pre_def dest: set_takeWhileD)
  obtain mp bp where scpre: "scan_down s pre = (mp, bp)" by (cases "scan_down s pre")
  have foldpre: "fold stp pre (- 1, r) = (mp, bp)" using scpre by (simp add: sdfold)
  have decomp: "fold stp post (stp v (mp, bp)) = (m, v)"
    using sc unfolding sdfold psplit by (simp add: foldpre)
  have collapse: "stp v (mp, bp) = (m, v)"
  proof -
    have "fold stp post (stp v (mp, bp)) = stp v (mp, bp)"
      using sd_fold_keep[where s = s and post = post and Y = "stp v (mp, bp)" and m = m and v = v]
            decomp vpost by (simp add: stp_def)
    thus ?thesis using decomp by simp
  qed
  have bpne: "mp \<noteq> - 1 \<Longrightarrow> bp \<noteq> v"
  proof
    assume "mp \<noteq> - 1" and "bp = v"
    hence "v \<in> set pre" using scan_down_snd_mem[OF scpre] by simp
    thus False using vpre by simp
  qed
  have stpupd: "m = res_down s v \<and> (mp = - 1 \<or> res_down s v < mp)"
    using collapse bpne unfolding stp_def by (auto simp: Let_def split: if_splits)
  have wpre: "w \<in> set pre" using win by (simp add: pre_def)
  have wge: "mp \<noteq> - 1 \<and> mp \<le> res_down s w" using scan_down_min[OF scpre wpre wne] .
  show ?thesis using stpupd wge by auto
qed

lemma su_fold_keep:
  fixes s
  defines "stp \<equiv> (\<lambda>x acc. case acc of (m, best) \<Rightarrow> let rr = res_up s x in if rr = - 1 then (m, best) else if m = - 1 then (rr, x) else if rr \<le> m then (rr, x) else (m, best))"
  shows "fold stp post Y = (m, v) \<Longrightarrow> v \<notin> set post \<Longrightarrow> fold stp post Y = Y"
proof (induction post arbitrary: Y)
  case Nil thus ?case by simp
next
  case (Cons a post')
  have vna: "v \<noteq> a" and vnp: "v \<notin> set post'" using Cons.prems(2) by auto
  have res: "fold stp post' (stp a Y) = (m, v)" using Cons.prems(1) by simp
  have keepa: "stp a Y = Y"
  proof (rule ccontr)
    assume ne: "stp a Y \<noteq> Y"
    obtain m0 best0 where Y: "Y = (m0, best0)" by (cases Y)
    have stpa: "stp a Y = (res_up s a, a)"
      using ne unfolding stp_def Y by (auto simp: Let_def split: if_splits)
    have r2: "fold stp post' (res_up s a, a) = (m, v)" using res stpa by simp
    have "fold stp post' (res_up s a, a) = (res_up s a, a)"
      using Cons.IH[of "(res_up s a, a)"] r2 vnp by blast
    hence "(res_up s a, a) = (m, v)" using r2 by simp
    thus False using vna by simp
  qed
  have r3: "fold stp post' Y = (m, v)" using res keepa by simp
  have "fold stp post' Y = Y" using Cons.IH[of Y] r3 vnp by blast
  thus ?case using keepa by simp
qed

lemma su_fold_after:
  fixes s
  defines "stp \<equiv> (\<lambda>x acc. case acc of (m, best) \<Rightarrow> let rr = res_up s x in if rr = - 1 then (m, best) else if m = - 1 then (rr, x) else if rr \<le> m then (rr, x) else (m, best))"
  shows "fold stp post Y = (m, v) \<Longrightarrow> v \<notin> set post \<Longrightarrow> w \<in> set post \<Longrightarrow> res_up s w = - 1 \<or> m < res_up s w"
proof (induction post arbitrary: Y)
  case Nil thus ?case by simp
next
  case (Cons a post')
  have vna: "v \<noteq> a" and vnp: "v \<notin> set post'" using Cons.prems(2) by auto
  have res: "fold stp post' (stp a Y) = (m, v)" using Cons.prems(1) by simp
  have collapse: "stp a Y = (m, v)"
    using su_fold_keep[where s = s and post = post' and Y = "stp a Y" and m = m and v = v] res vnp
    by (simp add: stp_def)
  obtain m0 best0 where Y: "Y = (m0, best0)" by (cases Y)
  have Yeq: "Y = (m, v)" and aprop: "res_up s a = - 1 \<or> m < res_up s a"
    using collapse vna unfolding stp_def Y by (auto simp: Let_def split: if_splits)
  show ?case
  proof (cases "w = a")
    case True thus ?thesis using aprop by simp
  next
    case False
    have wp: "w \<in> set post'" using Cons.prems(3) False by simp
    have "fold stp post' Y = (m, v)" using res collapse Yeq by simp
    thus ?thesis using Cons.IH vnp wp by blast
  qed
qed

lemma scan_up_after:
  assumes sc: "scan_up s p = (m, v)" and mne: "m \<noteq> - 1" and dp: "distinct p"
    and win: "w \<in> set p" and wout: "w \<notin> insert v (set (takeWhile (\<lambda>y. y \<noteq> v) p))" and wne: "res_up s w \<noteq> - 1"
  shows "m < res_up s w"
proof -
  define stp where "stp = (\<lambda>x acc. case acc of (m, best) \<Rightarrow> let rr = res_up s x in if rr = - 1 then (m, best) else if m = - 1 then (rr, x) else if rr \<le> m then (rr, x) else (m, best))"
  have sufold: "\<And>q. scan_up s q = fold stp q (- 1, r)" by (simp add: scan_up_def stp_def)
  have vmem: "v \<in> set p" using sc mne scan_up_snd_mem by blast
  define pre where "pre = takeWhile (\<lambda>y. y \<noteq> v) p"
  define post where "post = tl (dropWhile (\<lambda>y. y \<noteq> v) p)"
  have dwne: "dropWhile (\<lambda>y. y \<noteq> v) p \<noteq> []" using vmem by (auto simp: dropWhile_eq_Nil_conv)
  have dwhd: "hd (dropWhile (\<lambda>y. y \<noteq> v) p) = v" using dwne by (metis (mono_tags, lifting) hd_dropWhile)
  have dwv: "dropWhile (\<lambda>y. y \<noteq> v) p = v # post" using hd_Cons_tl[OF dwne] dwhd by (simp add: post_def)
  have psplit: "p = pre @ v # post"
    using takeWhile_dropWhile_id[of "\<lambda>y. y \<noteq> v" p] dwv by (simp add: pre_def)
  have vpost: "v \<notin> set post" using dp psplit by auto
  have setp: "set p = insert v (set pre \<union> set post)" using psplit by auto
  have wpost: "w \<in> set post" using win wout setp by (auto simp: pre_def)
  obtain mp bp where scpre: "scan_up s pre = (mp, bp)" by (cases "scan_up s pre")
  have foldpre: "fold stp pre (- 1, r) = (mp, bp)" using scpre by (simp add: sufold)
  have decomp: "fold stp post (stp v (mp, bp)) = (m, v)"
    using sc unfolding sufold psplit by (simp add: foldpre)
  have "res_up s w = - 1 \<or> m < res_up s w"
    using su_fold_after[where s = s and post = post and Y = "stp v (mp, bp)" and m = m and v = v and w = w]
          decomp vpost wpost by (simp add: stp_def)
  thus ?thesis using wne by simp
qed

lemma ns_pivot_preservation:
  assumes inv: "ns_invar s" and cond: "ns_pivot_cond s"
  shows "ns_invar (ns_pivot_upd s)"
    and "ns_less (ns_pivot_upd s) s"
proof -
  from cond obtain e in_U \<gamma> sel' p1 p2 \<delta> v e0fwd up_side where
  sel: "ns_select s = Some (e, in_U, \<gamma>, sel')" and
  ppx: "get_path_pair (spanning_tree s) (fst_exec e) (snd_exec e) = (p1, p2)" and
  bn: "bottleneck s e in_U p1 p2 = (\<delta>, False, v, e0fwd, up_side)" and
  dne: "\<delta> \<noteq> - 1"
  by (rule ns_pivot_condE)
  have eE0: "e \<in> \<E>" using ns_select_SomeD(2)[OF inv sel] .
  note exbr[simp] = fst_exec_coincide[OF eE0] snd_exec_coincide[OF eE0]
  have pp: "get_path_pair (spanning_tree s) (fst e) (snd e) = (p1, p2)" using ppx by simp
  define P where "P = (if in_U = up_side then p1 else p2)"
  define e0 where "e0 = par_edge s v"
  obtain parr darr where rp: "reparent s e P v = (parr, darr)" by (cases "reparent s e P v")
  let ?f' = "augment_flow s e in_U \<delta> p1 p2"
  let ?pi' = "shift_pot (spanning_tree s) v (potentials s) \<gamma> (in_U \<noteq> up_side)"
  let ?T' = "swap_edge (spanning_tree s) v (if in_U = up_side then fst e else snd e) (if in_U = up_side then snd e else fst e)"
  let ?s' = "ns_pivot s e in_U \<gamma> sel' \<delta> v e0fwd up_side p1 p2"
  have pivoteq: "ns_pivot_upd s = ?s'" by (simp add: ns_pivot_upd_def sel pp bn)
  have pj_flow: "current_flow ?s' = ?f'"
    and pj_pot: "potentials ?s' = ?pi'"
    and pj_tree: "spanning_tree ?s' = ?T'"
    and pj_par: "parent_edge ?s' = parr"
    and pj_dir: "edge_dir ?s' = darr"
    and pj_sel: "edge_sel ?s' = sel'"
    and pj_state: "edge_state ?s' = es_upd (es_upd (edge_state s) e InTree) e0 (if e0fwd then InU else InL)"
  by (simp_all add: ns_pivot_def Let_def rp e0_def flip: P_def split: prod.split)
  have eE: "e \<in> \<E>" and eLU: "e \<in> ns_L_of s \<union> ns_U_of s" and entree: "e \<notin> ns_tree_edges s"
    using ns_select_SomeD(2,1,3)[OF inv sel] by blast+
  have implS: "ns_invar_impl s" using ns_invarD(1)[OF inv] .
  have treeinv: "ns_invar_tree s" using ns_invarD(7)[OF inv] .
  have arbb: "arborescense_invar (spanning_tree s)" using ns_invar_implD(7)[OF implS] .
  have neq: "fst e \<noteq> snd e" using entering_not_selfloop[OF inv sel] .
  have fVe: "fst e \<in> \<V>" using fst_E_V[OF eE] .
  have sVe: "snd e \<in> \<V>" using snd_E_V[OF eE] .
  have fiE: "flow_invar (current_flow s)" using ns_invar_implD(1)[OF implS] .
  have precond: "selection_precond (edge_sel s) (potentials s) (edge_state s)"
  using ns_invar_implD(6)[OF implS] ns_invar_implD(2)[OF implS] ns_invar_implD(5)[OF implS]
        ns_invar_pot_fitsD[OF ns_invarD(5)[OF inv]]
  by (simp add: selection_precond_def potential_fits_spanning_tree_partition_def)
  have selS: "sel_select (edge_sel s) (potentials s) (edge_state s) = Some (e, in_U, \<gamma>, sel')"
  using sel by (simp add: ns_select_def)
  have selinv': "sel_invar sel'" using sel_select_SomeD(1)[OF precond selS] .
  have gi: "rcost_invar \<gamma>" using sel_select_SomeD(2)[OF precond selS] .
  have rc_eq: "rcost_abstract \<gamma> = reduced_cost (potentials s) e" using sel_select_SomeD(3)[OF precond selS] .
  have ent: "entering_edge (potentials s) (edge_state s) e in_U"
  using sel_select_SomeD(4)[OF precond selS] .
  have eside: "if in_U then e \<in> ns_U_of s else e \<in> ns_L_of s"
  using ent by (auto simp: entering_edge_def ns_L_of_def ns_U_of_def)
  have vP: "v \<in> set (if in_U = up_side then p1 else p2)" and vVr: "v \<in> \<V> - {r}"
    and e0tree: "par_edge s v \<in> ns_tree_edges s" and d0ge: "0 \<le> \<delta>" and upside_dpos: "up_side \<Longrightarrow> 0 < \<delta>"
    using bottleneck_pivot_facts(1,2,3,5,6)[OF inv sel pp bn] by blast+
  have vPP: "v \<in> set P" using vP by (simp add: P_def)
  have PsubV: "set P \<subseteq> \<V> - {r}"
    using get_path_pair_verts[OF inv eE entering_not_selfloop[OF inv sel] pp] by (cases "in_U = up_side") (auto simp: P_def)
  have vV: "v \<in> \<V>" using vVr by simp
  have e0E: "e0 \<in> \<E>" using ns_invar_tree_edgeD[OF treeinv vVr] by (simp add: e0_def)
  have rp': "reparent s e (if in_U = up_side then p1 else p2) v = (parr, darr)" using rp by (simp add: P_def)
  note reppr = reparent_props[OF inv sel pp bn dne rp']
  note swpr = swap_edge_pivot[OF inv sel pp bn dne]
  note shpr = shift_pot_props[OF inv sel pp bn dne]
  note aupr = augment_flow_props[OF inv sel pp bn dne]
  note arcset = reparent_arc_set[OF inv sel pp bn dne rp']
  have inv5: "es_invar (edge_state s)" using ns_invar_implD(5)[OF implS] .
  have ene0: "e \<noteq> e0" using entree e0tree by (auto simp: e0_def)
  have esinv': "es_invar (edge_state ?s')"
  unfolding pj_state
  by (rule es_arr.fixed_univ_map_upd_invar[OF es_arr.fixed_univ_map_upd_invar[OF inv5 eE] e0E])
  have esu: "es_lookup (edge_state ?s')
             = ((es_lookup (edge_state s))(e := InTree))(e0 := (if e0fwd then InU else InL))"
  unfolding pj_state
  by (simp add: es_arr.fixed_univ_map_upd[OF es_arr.fixed_univ_map_upd_invar[OF inv5 eE] e0E]
                es_arr.fixed_univ_map_upd[OF inv5 eE])
  have impl': "ns_invar_impl ?s'"
  using aupr(1) shpr(1) reppr(1) reppr(2) esinv' selinv' swpr(1)
  by (auto intro!: ns_invar_implI simp: pj_flow pj_pot pj_par pj_dir pj_sel pj_tree)
  have bflow': "ns_invar_bflow ?s'"
  using aupr(2) by (simp add: ns_invar_bflow_def pj_flow)
  have tree_eq: "ns_tree_edges ?s' = ns_tree_edges s - {e0} \<union> {e}"
  using arcset by (simp add: pj_par e0_def)
  have pot_eq: "ns_pot_of ?s' = abstract_pot ?pi'" by (simp add: pj_pot)
  have partS: "spanning_tree_partition r (ns_tree_edges s) (ns_L_of s \<union> ns_selfloops_L) (ns_U_of s \<union> ns_selfloops_U)"
  using ns_invarD(3)[OF inv] by (simp add: ns_invar_partition_def)
  have e0nL: "e0 \<notin> ns_L_of s" and e0nU: "e0 \<notin> ns_U_of s"
  using spanning_tree_partitionD(2,3)[OF partS] e0tree by (auto simp: e0_def)
  have neq: "fst e \<noteq> snd e" using entering_not_selfloop[OF inv sel] .
  have neq0: "fst e0 \<noteq> snd e0" using tree_edge_not_selfloop[OF inv e0tree] by (auto simp: e0_def)
  have e_nsl: "e \<notin> ns_selfloops_L" "e \<notin> ns_selfloops_U"
    using neq by (auto simp: ns_selfloops_L_def ns_selfloops_U_def)
  have e0_nsl: "e0 \<notin> ns_selfloops_L" "e0 \<notin> ns_selfloops_U"
    using neq0 by (auto simp: ns_selfloops_L_def ns_selfloops_U_def)
  have Lab: "ns_L_of ?s' = (if e0fwd then (if in_U then ns_L_of s else ns_L_of s - {e}) else insert e0 (if in_U then ns_L_of s else ns_L_of s - {e}))"
  using esu eE e0E ene0 eside e0nL e0nU neq neq0 by (auto simp: ns_L_of_def ns_U_of_def split: if_splits)
  have Uab: "ns_U_of ?s' = (if e0fwd then insert e0 (if in_U then ns_U_of s - {e} else ns_U_of s) else (if in_U then ns_U_of s - {e} else ns_U_of s))"
  using esu eE e0E ene0 eside e0nL e0nU neq neq0 by (auto simp: ns_L_of_def ns_U_of_def split: if_splits)
  have potfits': "ns_invar_pot_fits ?s'"
  unfolding ns_invar_pot_fits_def tree_eq pot_eq e0_def
  using shpr(3) .
  have UWA: "\<And>H. graph_invar H \<Longrightarrow> r \<in> Vs H \<Longrightarrow> (\<And>x y. x \<in> Vs H \<Longrightarrow> y \<in> Vs H \<Longrightarrow> \<exists>!p. walk_betw H x p y \<and> distinct p) \<Longrightarrow> graph_abs.arborescence H r H"
  proof -
    fix H :: "'a set set"
    assume gi: "graph_invar H" and rVs: "r \<in> Vs H"
    and uniqH: "\<And>x y. x \<in> Vs H \<Longrightarrow> y \<in> Vs H \<Longrightarrow> \<exists>!p. walk_betw H x p y \<and> distinct p"
    have gaG: "graph_abs H" using gi
      by (simp add: graph_abs_def)
    have reach_r: "\<And>x. x \<in> Vs H \<Longrightarrow> Paths.reachable H r x"
    proof -
      fix x assume xVs: "x \<in> Vs H"
      obtain p where wp: "walk_betw H x p r" using uniqH[OF xVs rVs] by blast
      have "walk_betw H r (rev p) x" using wp by (rule walk_symmetric)
      thus "Paths.reachable H r x" by (auto simp: Paths.reachable_def)
    qed
    have reach_Vs: "\<And>x. Paths.reachable H r x \<Longrightarrow> x \<in> Vs H"
    by (auto simp: Paths.reachable_def dest: walk_endpoints(2))
    have vscc: "connected_component H r = Vs H"
    by (rule connected_component_set[OF rVs reach_r reach_Vs])
    have nocyc: "\<nexists>u c. decycle H u c"
    proof (rule notI, elim exE)
      fix u c assume dc: "decycle H u c"
      have ep: "epath H u c u" and lc: "2 < length c" and dic: "distinct c"
      using dc by (auto simp: decycle_def)
      have csub: "set c \<subseteq> H" using ep by (rule epath_edges_subset)
      have cne: "c \<noteq> []" using lc by auto
      have e1: "hd c \<in> H" using csub cne by (meson hd_in_set subset_iff)
      obtain a b where eab: "hd c = {a, b}" and abne: "a \<noteq> b"
      using dblton_graphE[OF graph_invar_dblton[OF gi] e1] by metis
      have abG: "{a, b} \<in> H" using e1 eab by simp
      have insEq: "insert {a, b} (H - {{a, b}}) = H" using abG by auto
      have memc: "{a, b} \<in> set c" using eab hd_in_set[OF cne] by simp
      have "\<exists>q. walk_betw (H - {{a, b}}) b q a"
      using graph_abs.decycle_edge_path[OF gaG, of a b "H - {{a, b}}" u c]
      insEq abG dc memc by simp
      then obtain q where wq: "walk_betw (H - {{a, b}}) b q a" by blast
      obtain D where wD: "walk_betw (H - {{a, b}}) b D a" and dD: "distinct D"
      using walk_betw_different_verts_to_ditinct[OF wq abne[symmetric] refl] by blast
      have wDG: "walk_betw H b D a" using wD walk_subset by (metis Diff_subset)
      have wedge: "walk_betw H b [b, a] a" using abG by (simp add: insert_commute edges_are_walks)
      have aVs: "a \<in> Vs H" using abG by (auto simp: Vs_def)
      have bVs: "b \<in> Vs H" using abG by (auto simp: Vs_def)
      have Q1: "walk_betw H b D a \<and> distinct D" using wDG dD by simp
      have Q2: "walk_betw H b [b, a] a \<and> distinct [b, a]" using wedge abne by simp
      have "D = [b, a]" using uniqH[OF bVs aVs] Q1 Q2 by blast
      hence "walk_betw (H - {{a, b}}) b [b, a] a" using wD by simp
      hence "{b, a} \<in> H - {{a, b}}" by (auto simp: walk_betw_def path_2)
      thus False by (simp add: insert_commute)
    qed
    have hnc: "graph_abs.has_no_cycle H H"
    using nocyc by (simp add: graph_abs.has_no_cycle_def[OF gaG])
    show "graph_abs.arborescence H r H"
    using gaG hnc vscc by (auto intro!: graph_abs.arborescenceI)
  qed
  have arbT'inv: "arborescense_invar ?T'" using swpr(1) .
  have giT': "graph_invar (abstract_arborescense ?T')" using general(2)[OF arbT'inv] .
  have VsT': "Vs (abstract_arborescense ?T') = \<V>" using general(4)[OF arbT'inv] .
  have rV: "r \<in> \<V>" using general(1) .
  have rVsT': "r \<in> Vs (abstract_arborescense ?T')" using rV VsT' by simp
  have uniqT': "\<And>x y. x \<in> Vs (abstract_arborescense ?T') \<Longrightarrow> y \<in> Vs (abstract_arborescense ?T') \<Longrightarrow> \<exists>!p. walk_betw (abstract_arborescense ?T') x p y \<and> distinct p"
  proof -
    fix x y assume "x \<in> Vs (abstract_arborescense ?T')" "y \<in> Vs (abstract_arborescense ?T')"
    hence xV: "x \<in> \<V>" and yV: "y \<in> \<V>" using VsT' by auto
    show "\<exists>!p. walk_betw (abstract_arborescense ?T') x p y \<and> distinct p"
    using general(3)[OF arbT'inv yV xV] .
  qed
  have arbT': "graph_abs.arborescence (abstract_arborescense ?T') r (abstract_arborescense ?T')"
  using UWA[OF giT' rVsT' uniqT'] .
  have projeq: "(\<lambda>ee. {fst ee, snd ee}) ` (ns_tree_edges ?s') = abstract_arborescense ?T'"
  using reppr(3) by (simp add: pj_par image_image)
  note Pold = spanning_tree_partitionD[OF partS]
  have Eeq: "\<E> = ns_tree_edges s \<union> (ns_U_of s \<union> ns_selfloops_U) \<union> (ns_L_of s \<union> ns_selfloops_L)" using Pold(1) .
  have dTU: "ns_tree_edges s \<inter> ns_U_of s = {}" using Pold(2) by blast
  have dTL: "ns_tree_edges s \<inter> ns_L_of s = {}" using Pold(3) by blast
  have dLU: "ns_L_of s \<inter> ns_U_of s = {}" using Pold(4) by blast
  have Tinj: "\<forall>ee ee'. {ee, ee'} \<subseteq> ns_tree_edges s \<and> {fst ee, snd ee} = {fst ee', snd ee'} \<longrightarrow> ee = ee'"
  using Pold(7) .
  have TdVs: "dVs (make_pair ` ns_tree_edges s) = \<V>" using Pold(8) .
  have LsubE: "ns_L_of s \<subseteq> \<E>" and UsubE: "ns_U_of s \<subseteq> \<E>" using Eeq by auto
  have eLU2: "if in_U then e \<in> ns_U_of s else e \<in> ns_L_of s" using eside .
  have e0T: "e0 \<in> ns_tree_edges s" using e0tree by (simp add: e0_def)
  have gaT': "graph_abs (abstract_arborescense ?T')" using giT' by (simp add: graph_abs_def)
  have hncT': "graph_abs.has_no_cycle (abstract_arborescense ?T') (abstract_arborescense ?T')"
  using graph_abs.arborescenceD(1)[OF gaT' arbT'] .
  have finabsT': "finite (abstract_arborescense ?T')" using graph_abs.finite_E[OF gaT'] .
  have absT'ne: "abstract_arborescense ?T' \<noteq> {}"
  proof
    assume "abstract_arborescense ?T' = {}"
    hence "Vs (abstract_arborescense ?T') = {}" by (simp add: Vs_def)
    thus False using VsT' rV by auto
  qed
  have VsccT': "Vs (abstract_arborescense ?T') = connected_component (abstract_arborescense ?T') r"
  using graph_abs.arborescenceD(2)[OF gaT' arbT' absT'ne] .
  have allc: "\<And>vv. vv \<in> Vs (abstract_arborescense ?T') \<Longrightarrow> connected_component (abstract_arborescense ?T') vv = \<V>"
  proof -
    fix vv assume "vv \<in> Vs (abstract_arborescense ?T')"
    hence "vv \<in> connected_component (abstract_arborescense ?T') r" using VsccT' by simp
    hence "connected_component (abstract_arborescense ?T') vv = connected_component (abstract_arborescense ?T') r"
    by (rule connected_components_member_eq)
    thus "connected_component (abstract_arborescense ?T') vv = \<V>" using VsccT' VsT' by simp
  qed
  define AbsT where AbsTdef: "AbsT = abstract_arborescense ?T'"
  have VsAbs: "Vs AbsT = \<V>" using VsT' by (simp add: AbsTdef)
  have giAbs: "graph_invar AbsT" using giT' by (simp add: AbsTdef)
  have gaAbs: "graph_abs AbsT" using gaT' by (simp add: AbsTdef)
  have hncAbs: "graph_abs.has_no_cycle AbsT AbsT" using hncT' by (simp add: AbsTdef)
  have finAbs: "finite AbsT" using finabsT' by (simp add: AbsTdef)
  have rVsA: "r \<in> Vs AbsT" using rVsT' by (simp add: AbsTdef)
  have allcA: "\<And>vv. vv \<in> Vs AbsT \<Longrightarrow> connected_component AbsT vv = \<V>" using allc by (simp add: AbsTdef)
  have projeqA: "(\<lambda>ee. {fst ee, snd ee}) ` (ns_tree_edges ?s') = AbsT" using projeq by (simp add: AbsTdef)
  have ccne: "connected_components AbsT \<noteq> {}"
  using rVsA by (auto simp: connected_components_def)
  have ccimg: "connected_components AbsT = connected_component AbsT ` Vs AbsT"
  by (simp add: connected_components_aux_def comps_def)
  have ccsub: "connected_components AbsT \<subseteq> {\<V>}"
  unfolding ccimg
  proof (rule image_subsetI)
    fix x assume "x \<in> Vs AbsT"
    thus "connected_component AbsT x \<in> {\<V>}" using allcA[of x] by simp
  qed
  have ccEq: "connected_components AbsT = {\<V>}" using ccsub ccne by (blast dest: subset_singletonD)
  have ccOne: "card (connected_components AbsT) = 1" using ccEq by simp
  have dbl: "\<And>ee. ee \<in> AbsT \<Longrightarrow> \<exists>u w. ee = {u, w} \<and> u \<noteq> w"
  proof -
    fix ee assume "ee \<in> AbsT"
    thus "\<exists>u w. ee = {u, w} \<and> u \<noteq> w"
    using dblton_graphE[OF graph_invar_dblton[OF giAbs]] by metis
  qed
  have cc_card: "card (Vs AbsT) = card AbsT + card (connected_components AbsT)"
  using graph_abs.connected_components_card[OF gaAbs hncAbs dbl] .
  have cardAbs: "card AbsT = card \<V> - 1" using cc_card VsAbs ccOne by simp
  have finV: "finite \<V>" using \<V>_finite .
  have tsimg: "ns_tree_edges s = par_edge s ` (\<V> - {r})" by (simp add: par_edge_def)
  have finTs: "finite (ns_tree_edges s)" using finV by (simp add: tsimg)
  have cardVr: "card (\<V> - {r}) = card \<V> - 1" using finV rV by (simp add: card_Diff_singleton)
  have cardTs: "card (ns_tree_edges s) = card \<V> - 1"
  using card_image[OF par_edge_inj_on[OF inv]] cardVr by (simp add: tsimg)
  have enotAe0: "e \<notin> ns_tree_edges s - {e0}" using entree by simp
  have tsne: "ns_tree_edges s \<noteq> {}" using e0T by blast
  have cardpos: "0 < card (ns_tree_edges s)" using finTs tsne by (simp add: card_gt_0_iff)
  have cardT': "card (ns_tree_edges ?s') = card (ns_tree_edges s)"
  proof -
    have "card (ns_tree_edges ?s') = Suc (card (ns_tree_edges s - {e0}))"
    using finTs enotAe0 by (simp add: tree_eq card_insert_disjoint)
    also have "... = Suc (card (ns_tree_edges s) - 1)" using e0T finTs by (simp add: card_Diff_singleton)
    also have "... = card (ns_tree_edges s)" using cardpos by simp
    finally show ?thesis .
  qed
  have finT': "finite (ns_tree_edges ?s')" using finTs by (simp add: tree_eq)
  have cardProj: "card ((\<lambda>ee. {fst ee, snd ee}) ` (ns_tree_edges ?s')) = card \<V> - 1"
  using projeqA cardAbs by simp
  have cardTeq: "card (ns_tree_edges ?s') = card \<V> - 1" using cardT' cardTs by simp
  have injproj: "inj_on (\<lambda>ee. {fst ee, snd ee}) (ns_tree_edges ?s')"
  using eq_card_imp_inj_on[OF finT'] cardProj cardTeq by simp
  have Tinj': "\<forall>ee ee'. {ee, ee'} \<subseteq> ns_tree_edges ?s' \<and> {fst ee, snd ee} = {fst ee', snd ee'} \<longrightarrow> ee = ee'"
  using injproj by (auto simp: inj_on_def)
  have dVsVs: "\<And>X. dVs (make_pair ` X) = Vs ((\<lambda>ee. {fst ee, snd ee}) ` X)"
  by (auto simp: dVs_def make_pair_def Vs_def)
  have dVsT': "dVs (make_pair ` ns_tree_edges ?s') = \<V>"
  using dVsVs[of "ns_tree_edges ?s'"] projeqA VsAbs by simp
  have arbA: "graph_abs.arborescence AbsT r AbsT" using arbT' by (simp add: AbsTdef)
  have eU_iff: "in_U \<Longrightarrow> e \<in> ns_U_of s" and eL_iff: "\<not> in_U \<Longrightarrow> e \<in> ns_L_of s" using eside by (auto split: if_splits)
  have unionT': "\<E> = ns_tree_edges ?s' \<union> (ns_U_of ?s' \<union> ns_selfloops_U) \<union> (ns_L_of ?s' \<union> ns_selfloops_L)"
  unfolding tree_eq Lab Uab
  using Eeq eside entree e0T e0nL e0nU eU_iff eL_iff
  by (cases in_U; cases e0fwd) auto
  have enU: "\<not> in_U \<Longrightarrow> e \<notin> ns_U_of s" using eL_iff dLU by auto
  have enL: "in_U \<Longrightarrow> e \<notin> ns_L_of s" using eU_iff dLU by auto
  have disjTU': "ns_tree_edges ?s' \<inter> (ns_U_of ?s' \<union> ns_selfloops_U) = {}"
  unfolding tree_eq Uab
  using dTU entree e0nU ene0 enU Pold(2) e_nsl(2) e0_nsl(2)
  by (cases in_U; cases e0fwd) (auto simp: disjoint_iff)
  have disjTL': "ns_tree_edges ?s' \<inter> (ns_L_of ?s' \<union> ns_selfloops_L) = {}"
  unfolding tree_eq Lab
  using dTL entree e0nL ene0 enL Pold(3) e_nsl(1) e0_nsl(1)
  by (cases in_U; cases e0fwd) (auto simp: disjoint_iff)
  have disjLU': "(ns_L_of ?s' \<union> ns_selfloops_L) \<inter> (ns_U_of ?s' \<union> ns_selfloops_U) = {}"
  unfolding Lab Uab
  using dLU e0nL e0nU Pold(4) e_nsl e0_nsl
  by (cases in_U; cases e0fwd) (auto simp: disjoint_iff)
  have partition': "ns_invar_partition ?s'"
  unfolding ns_invar_partition_def spanning_tree_partition_def
  proof (intro conjI)
    show "\<E> = ns_tree_edges ?s' \<union> (ns_U_of ?s' \<union> ns_selfloops_U) \<union> (ns_L_of ?s' \<union> ns_selfloops_L)" using unionT' .
    show "ns_tree_edges ?s' \<inter> (ns_U_of ?s' \<union> ns_selfloops_U) = {}" using disjTU' .
    show "ns_tree_edges ?s' \<inter> (ns_L_of ?s' \<union> ns_selfloops_L) = {}" using disjTL' .
    show "(ns_L_of ?s' \<union> ns_selfloops_L) \<inter> (ns_U_of ?s' \<union> ns_selfloops_U) = {}" using disjLU' .
    show "graph_abs.arborescence ((\<lambda>ee. {fst ee, snd ee}) ` ns_tree_edges ?s') r ((\<lambda>ee. {fst ee, snd ee}) ` ns_tree_edges ?s')"
    using arbA projeqA by simp
    show "graph_abs ((\<lambda>ee. {fst ee, snd ee}) ` ns_tree_edges ?s')" using gaAbs projeqA by simp
    show "\<forall>ee ee'. {ee, ee'} \<subseteq> ns_tree_edges ?s' \<and> {fst ee, snd ee} = {fst ee', snd ee'} \<longrightarrow> ee = ee'" using Tinj' .
    show "dVs (make_pair ` ns_tree_edges ?s') = \<V>" using dVsT' .
  qed
  let ?ce = "if in_U then - \<delta> else \<delta>"
  let ?gup = "\<lambda>w. if par_up s w then \<delta> else - \<delta>"
  let ?gdn = "\<lambda>w. if par_up s w then - \<delta> else \<delta>"
  let ?up = "if in_U then p1 else p2"
  let ?dn = "if in_U then p2 else p1"
  have p1V: "set p1 \<subseteq> \<V> - {r}" and p2V: "set p2 \<subseteq> \<V> - {r}"
  using get_path_pair_verts[OF inv eE entering_not_selfloop[OF inv sel] pp] by auto
  have upV: "set ?up \<subseteq> \<V> - {r}" using p1V p2V by (cases in_U) auto
  have dnV: "set ?dn \<subseteq> \<V> - {r}" using p1V p2V by (cases in_U) auto
  obtain a0 p3 where d1a: "distinct (p1 @ a0 # p3)" and d2a: "distinct (p2 @ a0 # p3)"
  using get_path_pair(1)[OF arbb pp neq fVe sVe] by meson
  have updist: "distinct ?up" using d1a d2a by (cases in_U) auto
  have dndist: "distinct ?dn" using d1a d2a by (cases in_U) auto
  have updisj: "set ?up \<inter> set ?dn = {}"
  using get_path_pair_align(4)[OF inv sel pp] by (cases in_U) auto
  have upEc: "\<forall>w\<in>set ?up. par_edge s w \<in> \<E>" using p1V p2V ns_invar_tree_edgeD[OF ns_invarD(7)[OF inv]] by (cases in_U) auto
  have dnEc: "\<forall>w\<in>set ?dn. par_edge s w \<in> \<E>" using p1V p2V ns_invar_tree_edgeD[OF ns_invarD(7)[OF inv]] by (cases in_U) auto
  have fval: "\<And>a. flow_lookup ?f' a = flow_lookup (current_flow s) a + (if a = e then ?ce else 0) + (\<Sum>w\<leftarrow>?up. if par_edge s w = a then ?gup w else 0) + (\<Sum>w\<leftarrow>?dn. if par_edge s w = a then ?gdn w else 0)"
    by (rule augment_flow_lookup_char[OF fiE d0ge eE upEc dnEc])
  have parE: "\<And>w. w \<in> \<V> - {r} \<Longrightarrow> par_edge s w \<in> ns_tree_edges s" by (auto simp: par_edge_def)
  have sum_up_vanish: "\<And>a. a \<notin> ns_tree_edges s \<Longrightarrow> (\<Sum>w\<leftarrow>?up. if par_edge s w = a then ?gup w else 0) = 0"
  proof -
    fix a assume a: "a \<notin> ns_tree_edges s"
    have ne: "\<And>w. w \<in> set ?up \<Longrightarrow> par_edge s w \<noteq> a" using upV parE a by blast
    have "(\<Sum>w\<leftarrow>?up. if par_edge s w = a then ?gup w else 0) = (\<Sum>w\<leftarrow>?up. 0)"
    by (rule arg_cong[where f=sum_list], rule map_cong[OF refl]) (simp add: ne)
    thus "(\<Sum>w\<leftarrow>?up. if par_edge s w = a then ?gup w else 0) = 0" by (simp add: sum_list_0)
  qed
  have sum_dn_vanish: "\<And>a. a \<notin> ns_tree_edges s \<Longrightarrow> (\<Sum>w\<leftarrow>?dn. if par_edge s w = a then ?gdn w else 0) = 0"
  proof -
    fix a assume a: "a \<notin> ns_tree_edges s"
    have ne: "\<And>w. w \<in> set ?dn \<Longrightarrow> par_edge s w \<noteq> a" using dnV parE a by blast
    have "(\<Sum>w\<leftarrow>?dn. if par_edge s w = a then ?gdn w else 0) = (\<Sum>w\<leftarrow>?dn. 0)"
    by (rule arg_cong[where f=sum_list], rule map_cong[OF refl]) (simp add: ne)
    thus "(\<Sum>w\<leftarrow>?dn. if par_edge s w = a then ?gdn w else 0) = 0" by (simp add: sum_list_0)
  qed
  have notin_flow: "\<And>a. a \<notin> ns_tree_edges s \<Longrightarrow> a \<noteq> e \<Longrightarrow> flow_lookup ?f' a = flow_lookup (current_flow s) a"
  using fval sum_up_vanish sum_dn_vanish by simp
  have LUfit: "flow_fits_spanning_tree_partition (ns_tree_edges s) (ns_L_of s) (ns_U_of s) (ns_flow_of s)"
  using ns_invarD(4)[OF inv] by (simp add: ns_invar_flow_fits_def)
  have Lfit: "\<And>a. a \<in> ns_L_of s \<Longrightarrow> flow_lookup (current_flow s) a = 0"
  using LUfit by (simp add: flow_fits_spanning_tree_partition_def)
  have Ufit: "\<And>a. a \<in> ns_U_of s \<Longrightarrow> ereal (h (flow_lookup (current_flow s) a)) = \<u> a"
  using LUfit by (simp add: flow_fits_spanning_tree_partition_def)
  have Lnt: "\<And>a. a \<in> ns_L_of s \<Longrightarrow> a \<notin> ns_tree_edges s" using dTL by auto
  have Unt: "\<And>a. a \<in> ns_U_of s \<Longrightarrow> a \<notin> ns_tree_edges s" using dTU by auto
  have sumpick: "\<And>v xs g. distinct xs \<Longrightarrow> set xs \<subseteq> \<V> - {r} \<Longrightarrow> v \<in> \<V> - {r} \<Longrightarrow> (\<Sum>w\<leftarrow>xs. if par_edge s w = par_edge s v then (g w::'n) else 0) = (if v \<in> set xs then g v else 0)"
    using par_sum_pick[OF inv] by blast
  have treeval: "\<And>w. w \<in> \<V> - {r} \<Longrightarrow> flow_lookup ?f' (par_edge s w) = flow_lookup (current_flow s) (par_edge s w) + (if w \<in> set ?up then ?gup w else 0) + (if w \<in> set ?dn then ?gdn w else 0)"
  proof -
    fix w assume wV: "w \<in> \<V> - {r}"
    have pne: "par_edge s w \<noteq> e" using parE[OF wV] entree by blast
    have "flow_lookup ?f' (par_edge s w) = flow_lookup (current_flow s) (par_edge s w) + (if par_edge s w = e then ?ce else 0) + (\<Sum>wa\<leftarrow>?up. if par_edge s wa = par_edge s w then ?gup wa else 0) + (\<Sum>wa\<leftarrow>?dn. if par_edge s wa = par_edge s w then ?gdn wa else 0)"
    using fval[of "par_edge s w"] .
    thus "flow_lookup ?f' (par_edge s w) = flow_lookup (current_flow s) (par_edge s w) + (if w \<in> set ?up then ?gup w else 0) + (if w \<in> set ?dn then ?gdn w else 0)"
    using pne sumpick[OF updist upV wV] sumpick[OF dndist dnV wV] by simp
  qed
  obtain mu vu where su: "scan_up s ?up = (mu, vu)" by (cases "scan_up s ?up")
  obtain md vd where sd: "scan_down s ?dn = (md, vd)" by (cases "scan_down s ?dn")
  define re where "re = (if in_U then res_bwd s e else res_fwd s e)"
  define dd where "dd = mininf re (mininf mu md)"
  have bform: "bottleneck s e in_U p1 p2 = (if dd = - 1 then (- 1, True, r, False, False) else if mu \<noteq> - 1 \<and> mu = dd then (dd, False, vu, par_up s vu, True) else if re = dd then (dd, True, r, False, False) else (dd, False, vd, \<not> par_up s vd, False))"
  unfolding bottleneck_def Let_def su sd re_def dd_def by simp
  have muS: "0 \<le> mu \<or> mu = - 1" using scan_up_val_sign[OF inv upV su] .
  have mdS: "0 \<le> md \<or> md = - 1" using scan_down_val_sign[OF inv dnV sd] .
  have reS: "0 \<le> re \<or> re = - 1"
  using res_bwd_nonneg[OF inv eE] res_fwd_sign[OF inv eE] by (auto simp: re_def)
  have dne_dd: "dd \<noteq> - 1"
  proof
    assume "dd = - 1"
    hence "bottleneck s e in_U p1 p2 = (- 1, True, r, False, False)" using bform by simp
    thus False using bn by simp
  qed
  have geomU: "up_side \<Longrightarrow> v \<in> set ?up \<and> e0fwd = par_up s v \<and> res_up s v = \<delta>"
  proof -
    assume us: up_side
    have arm: "mu \<noteq> - 1 \<and> mu = dd"
    proof (rule ccontr)
      assume nc: "\<not> (mu \<noteq> - 1 \<and> mu = dd)"
      have "bottleneck s e in_U p1 p2 = (if re = dd then (dd, True, r, False, False) else (dd, False, vd, \<not> par_up s vd, False))"
      using bform nc dne_dd by (auto split: if_splits)
      thus False using bn us by (auto split: if_splits)
    qed
    hence eqs: "(dd, False, vu, par_up s vu, True) = (\<delta>, False, v, e0fwd, up_side)"
    using bform bn dne_dd by simp
    from eqs have vv': "vu = v" and dv: "\<delta> = dd" by auto
    from eqs vv' have ef: "e0fwd = par_up s v" by auto
    have squ: "scan_up s ?up = (mu, v)" using su vv' by simp
    have vmem: "v \<in> set ?up" using scan_up_snd_mem[OF squ] arm by simp
    have rv: "res_up s v = mu" using scan_up_val_at[OF squ] arm by simp
    have "mu = dd" using arm by simp
    thus "v \<in> set ?up \<and> e0fwd = par_up s v \<and> res_up s v = \<delta>" using vmem ef rv dv by simp
  qed
  have geomD: "\<not> up_side \<Longrightarrow> v \<in> set ?dn \<and> e0fwd = (\<not> par_up s v) \<and> res_down s v = \<delta>"
  proof -
    assume us: "\<not> up_side"
    have narm: "\<not> (mu \<noteq> - 1 \<and> mu = dd)"
    proof (rule ccontr)
      assume "\<not> \<not> (mu \<noteq> - 1 \<and> mu = dd)"
      hence a: "mu \<noteq> - 1 \<and> mu = dd" by simp
      have "(dd, False, vu, par_up s vu, True) = (\<delta>, False, v, e0fwd, up_side)"
      using bform bn a dne_dd by simp
      thus False using us by simp
    qed
    have rne: "re \<noteq> dd"
    proof (rule ccontr)
      assume "\<not> re \<noteq> dd" hence "re = dd" by simp
      hence "bottleneck s e in_U p1 p2 = (dd, True, r, False, False)" using bform narm dne_dd by simp
      thus False using bn by simp
    qed
    have eqs: "(dd, False, vd, \<not> par_up s vd, False) = (\<delta>, False, v, e0fwd, up_side)"
    using bform bn narm rne dne_dd by simp
    from eqs have vv': "vd = v" and dv: "\<delta> = dd" by auto
    from eqs vv' have ef: "e0fwd = (\<not> par_up s v)" by auto
    have sqd: "scan_down s ?dn = (md, v)" using sd vv' by simp
    have ddY: "dd = mininf mu md" using mininf_snd_of_neq_fst[of re "mininf mu md"] rne by (simp add: dd_def)
    have ddmd: "dd = md \<and> md \<noteq> - 1" using mininf_snd_attains[of mu md] ddY dne_dd narm by simp
    have vmem: "v \<in> set ?dn" using scan_down_snd_mem[OF sqd] ddmd by simp
    have rv: "res_down s v = md" using scan_down_val_at[OF sqd] ddmd by simp
    thus "v \<in> set ?dn \<and> e0fwd = (\<not> par_up s v) \<and> res_down s v = \<delta>" using vmem ef rv dv ddmd by simp
  qed
  have tvv: "flow_lookup ?f' e0 = flow_lookup (current_flow s) e0 + (if v \<in> set ?up then ?gup v else 0) + (if v \<in> set ?dn then ?gdn v else 0)"
  using treeval[OF vVr] by (simp add: e0_def)
  have cfnn: "0 \<le> flow_lookup (current_flow s) e0" using res_bwd_nonneg[OF inv e0E] by (simp add: res_bwd_def)
  have capfin: "res_fwd s e0 = \<delta> \<Longrightarrow> cap e0 \<noteq> - 1"
  proof -
    assume "res_fwd s e0 = \<delta>"
    thus "cap e0 \<noteq> - 1" using d0ge by (auto simp: res_fwd_def Let_def split: if_splits)
  qed
  have ufwd: "res_fwd s e0 = \<delta> \<Longrightarrow> ereal (h (flow_lookup (current_flow s) e0 + \<delta>)) = \<u> e0"
  proof -
    assume rf: "res_fwd s e0 = \<delta>"
    have cfin: "cap e0 \<noteq> - 1" using capfin[OF rf] .
    hence cnn: "0 \<le> cap e0" using cap_nonneg[OF e0E] by simp
    have ue: "\<u> e0 = ereal (h (cap e0))" using cap_finite[OF e0E cnn] .
    have "res_fwd s e0 = cap e0 - flow_lookup (current_flow s) e0" using cfin by (simp add: res_fwd_def Let_def)
    hence "flow_lookup (current_flow s) e0 + \<delta> = cap e0" using rf by simp
    thus "ereal (h (flow_lookup (current_flow s) e0 + \<delta>)) = \<u> e0" using ue by simp
  qed
  have e0fit: "if e0fwd then ereal (h (flow_lookup ?f' e0)) = \<u> e0 else flow_lookup ?f' e0 = 0"
  proof (cases up_side)
    case True
    note g = geomU[OF True]
    have vup: "v \<in> set ?up" and ef: "e0fwd = par_up s v" and rud: "res_up s v = \<delta>" using g by auto
    have vndn: "v \<notin> set ?dn" using vup updisj by auto
    have tv': "flow_lookup ?f' e0 = flow_lookup (current_flow s) e0 + ?gup v" using tvv vup vndn by simp
    show ?thesis
    proof (cases "par_up s v")
      case pu: True
      have rf: "res_fwd s e0 = \<delta>" using rud pu by (simp add: res_up_def e0_def)
      have "flow_lookup ?f' e0 = flow_lookup (current_flow s) e0 + \<delta>" using tv' pu by simp
      thus ?thesis using ef pu ufwd[OF rf] by simp
    next
      case pd: False
      have rb: "flow_lookup (current_flow s) e0 = \<delta>" using rud pd by (simp add: res_up_def res_bwd_def e0_def)
      have "flow_lookup ?f' e0 = flow_lookup (current_flow s) e0 - \<delta>" using tv' pd by simp
      thus ?thesis using ef pd rb by simp
    qed
  next
    case False
    note g = geomD[OF False]
    have vdn: "v \<in> set ?dn" and ef: "e0fwd = (\<not> par_up s v)" and rdd: "res_down s v = \<delta>" using g by auto
    have vnup: "v \<notin> set ?up" using vdn updisj by auto
    have tv': "flow_lookup ?f' e0 = flow_lookup (current_flow s) e0 + ?gdn v" using tvv vdn vnup by simp
    show ?thesis
    proof (cases "par_up s v")
      case pu: True
      have rb: "flow_lookup (current_flow s) e0 = \<delta>" using rdd pu by (simp add: res_down_def res_bwd_def e0_def)
      have "flow_lookup ?f' e0 = flow_lookup (current_flow s) e0 - \<delta>" using tv' pu by simp
      thus ?thesis using ef pu rb by simp
    next
      case pd: False
      have rf: "res_fwd s e0 = \<delta>" using rdd pd by (simp add: res_down_def e0_def)
      have "flow_lookup ?f' e0 = flow_lookup (current_flow s) e0 + \<delta>" using tv' pd by simp
      thus ?thesis using ef pd ufwd[OF rf] by simp
    qed
  qed
  have flow_eq: "ns_flow_of ?s' = h \<circ> flow_lookup ?f'" by (simp add: pj_flow)
  have e0_emp: "\<not> e0fwd \<Longrightarrow> flow_lookup ?f' e0 = 0" using e0fit by (simp split: if_splits)
  have e0_sat: "e0fwd \<Longrightarrow> ereal (h (flow_lookup ?f' e0)) = \<u> e0" using e0fit by (simp split: if_splits)
  have flowfits': "ns_invar_flow_fits ?s'"
  unfolding ns_invar_flow_fits_def pj_flow Lab Uab flow_fits_spanning_tree_partition_def comp_def
  proof (intro conjI ballI)
    fix a assume aL: "a \<in> (if e0fwd then (if in_U then ns_L_of s else ns_L_of s - {e}) else insert e0 (if in_U then ns_L_of s else ns_L_of s - {e}))"
    show "h (flow_lookup ?f' a) = 0"
    proof (cases "a = e0")
      case True
      have nf: "\<not> e0fwd" using aL True e0nL by (cases e0fwd; cases in_U) auto
      thus ?thesis using e0_emp True by simp
    next
      case ane0: False
      have aLs: "a \<in> ns_L_of s" using aL ane0 by (cases e0fwd; cases in_U) auto
      have ane: "a \<noteq> e" using aL ane0 enL by (cases e0fwd; cases in_U) auto
      have "flow_lookup ?f' a = flow_lookup (current_flow s) a" using notin_flow[OF Lnt[OF aLs] ane] .
      thus ?thesis using Lfit[OF aLs] by simp
    qed
  next
    fix a assume aU: "a \<in> (if e0fwd then insert e0 (if in_U then ns_U_of s - {e} else ns_U_of s) else (if in_U then ns_U_of s - {e} else ns_U_of s))"
    show "ereal (h (flow_lookup ?f' a)) = \<u> a"
    proof (cases "a = e0")
      case True
      have ff: "e0fwd" using aU True e0nU by (cases e0fwd; cases in_U) auto
      thus ?thesis using e0_sat True by simp
    next
      case ane0: False
      have aUs: "a \<in> ns_U_of s" using aU ane0 by (cases e0fwd; cases in_U) auto
      have ane: "a \<noteq> e" using aU ane0 enU by (cases e0fwd; cases in_U) auto
      have "flow_lookup ?f' a = flow_lookup (current_flow s) a" using notin_flow[OF Unt[OF aUs] ane] .
      thus ?thesis using Ufit[OF aUs] by simp
    qed
  qed
  have rpfull: "\<And>ws first pe pup pp0 dd0. distinct ws \<Longrightarrow> v \<in> set ws \<Longrightarrow> parent_invar pp0 \<Longrightarrow> dir_invar dd0 \<Longrightarrow> set ws \<subseteq> \<V> - {r} \<Longrightarrow>
    (case reparent_walk s e v first pe pup ws (pp0, dd0) of (pr, dr) \<Rightarrow>
       (\<forall>x. x \<notin> insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ws)) \<longrightarrow> parent_lookup pr x = parent_lookup pp0 x \<and> dir_lookup dr x = dir_lookup dd0 x)
     \<and> parent_lookup pr (hd ws) = (if first then e else pe)
     \<and> dir_lookup dr (hd ws) = (if first then (hd ws = fst_exec e) else (\<not> pup))
     \<and> (\<forall>i. Suc i < length ws \<longrightarrow> ws ! i \<in> set (takeWhile (\<lambda>y. y \<noteq> v) ws) \<longrightarrow> parent_lookup pr (ws ! Suc i) = par_edge s (ws ! i) \<and> dir_lookup dr (ws ! Suc i) = (\<not> par_up s (ws ! i))))"
    by (fact reparent_walk_full)
  have Pdist: "distinct P" using d1a d2a by (cases "in_U = up_side") (auto simp: P_def)
  have pinvE: "parent_invar (parent_edge s)" using ns_invar_implD(3)[OF implS] .
  have dinvE: "dir_invar (edge_dir s)" using ns_invar_implD(4)[OF implS] .
  have rpw_eq: "reparent_walk s e v True e False P (parent_edge s, edge_dir s) = (parr, darr)"
  using rp by (simp add: reparent_def)
  note rpapp = rpfull[of P "parent_edge s" "edge_dir s" True e False, OF Pdist vPP pinvE dinvE PsubV, unfolded rpw_eq prod.case]
  have rp_off: "\<And>x. x \<notin> insert v (set (takeWhile (\<lambda>y. y \<noteq> v) P)) \<Longrightarrow> parent_lookup parr x = par_edge s x \<and> dir_lookup darr x = par_up s x"
  using rpapp by (auto simp: par_edge_def par_up_def)
  have rp_head: "parent_lookup parr (hd P) = e \<and> dir_lookup darr (hd P) = (hd P = fst e)"
  using rpapp by simp
  have rp_nth: "\<And>i. Suc i < length P \<Longrightarrow> P ! i \<in> set (takeWhile (\<lambda>y. y \<noteq> v) P) \<Longrightarrow> parent_lookup parr (P ! Suc i) = par_edge s (P ! i) \<and> dir_lookup darr (P ! Suc i) = (\<not> par_up s (P ! i))"
  using rpapp by blast
  have paredge'_eq: "\<And>x. par_edge ?s' x = parent_lookup parr x" by (simp add: par_edge_def pj_par)
  have parup'_eq: "\<And>x. par_up ?s' x = dir_lookup darr x" by (simp add: par_up_def pj_dir)
  have P_side: "P = (if up_side then ?up else ?dn)" by (cases up_side; cases in_U) (auto simp: P_def)
  have scan_down_before: "\<And>p m0 v0 w0. scan_down s p = (m0, v0) \<Longrightarrow> m0 \<noteq> - 1 \<Longrightarrow> distinct p \<Longrightarrow> w0 \<in> set (takeWhile (\<lambda>y. y \<noteq> v0) p) \<Longrightarrow> res_down s w0 \<noteq> - 1 \<Longrightarrow> m0 < res_down s w0"
    by (fact scan_down_before)
  have scan_up_after: "\<And>p m0 v0 w0. scan_up s p = (m0, v0) \<Longrightarrow> m0 \<noteq> - 1 \<Longrightarrow> distinct p \<Longrightarrow> w0 \<in> set p \<Longrightarrow> w0 \<notin> insert v0 (set (takeWhile (\<lambda>y. y \<noteq> v0) p)) \<Longrightarrow> res_up s w0 \<noteq> - 1 \<Longrightarrow> m0 < res_up s w0"
    by (fact scan_up_after)
  have oldstrict: "\<And>v'. v' \<in> \<V> - {r} \<Longrightarrow> (if par_up s v' then ereal (h (flow_lookup (current_flow s) (par_edge s v'))) < \<u> (par_edge s v') else flow_lookup (current_flow s) (par_edge s v') > 0)"
  using ns_invarD(6)[OF inv] by (simp add: ns_invar_strict_def)
  have iu: "isuflow (ns_flow_of s)" using ns_invar_bflowD[OF ns_invarD(2)[OF inv]] by (simp add: isbflow_def)
  have e_flow: "flow_lookup ?f' e = flow_lookup (current_flow s) e + ?ce"
  using fval[of e] sum_up_vanish[OF entree] sum_dn_vanish[OF entree] by simp
  have eL0: "\<not> in_U \<Longrightarrow> flow_lookup (current_flow s) e = 0" using eside Lfit by (cases in_U) auto
  have eUu: "in_U \<Longrightarrow> ereal (h (flow_lookup (current_flow s) e)) = \<u> e" using eside Ufit by (cases in_U) auto
  have scanU_v: "up_side \<Longrightarrow> scan_up s ?up = (\<delta>, v)"
  proof -
    assume us: up_side
    have arm: "mu \<noteq> - 1 \<and> mu = dd"
    proof (rule ccontr)
      assume nc: "\<not> (mu \<noteq> - 1 \<and> mu = dd)"
      have "bottleneck s e in_U p1 p2 = (if re = dd then (dd, True, r, False, False) else (dd, False, vd, \<not> par_up s vd, False))"
      using bform nc bn by (auto split: if_splits)
      thus False using bn us by (auto split: if_splits)
    qed
    have f1: "bottleneck s e in_U p1 p2 = (dd, False, vu, par_up s vu, True)"
      using bform arm bn by (auto split: if_splits)
    have "vu = v \<and> \<delta> = dd" using bn f1 by (metis Pair_inject)
    thus "scan_up s ?up = (\<delta>, v)" using su arm by auto
  qed
  have scanD_v: "\<not> up_side \<Longrightarrow> scan_down s ?dn = (\<delta>, v)"
  proof -
    assume us: "\<not> up_side"
    have narm: "\<not> (mu \<noteq> - 1 \<and> mu = dd)"
    proof (rule ccontr)
      assume "\<not> \<not> (mu \<noteq> - 1 \<and> mu = dd)"
      hence a: "mu \<noteq> - 1 \<and> mu = dd" by simp
      have f: "bottleneck s e in_U p1 p2 = (dd, False, vu, par_up s vu, True)"
      using bform a bn by (auto split: if_splits)
      have "up_side" using bn f by (metis Pair_inject)
      thus False using us by simp
    qed
    have rne: "re \<noteq> dd"
    proof (rule ccontr)
      assume "\<not> re \<noteq> dd" hence "re = dd" by simp
      hence "bottleneck s e in_U p1 p2 = (dd, True, r, False, False)" using bform narm bn by (auto split: if_splits)
      thus False using bn by simp
    qed
    have f2: "bottleneck s e in_U p1 p2 = (dd, False, vd, \<not> par_up s vd, False)"
      using bform narm rne bn by (auto split: if_splits)
    have vdv: "vd = v" and ddd: "\<delta> = dd" using bn f2 by (metis Pair_inject)+
    have ddne: "dd \<noteq> - 1" using ddd d0ge by auto
    have ddmu: "dd = mininf mu md" using mininf_snd_of_neq_fst[of re "mininf mu md"] rne by (simp add: dd_def)
    have ddmd: "dd = md" using mininf_snd_attains[of mu md] ddmu ddne narm by simp
    show "scan_down s ?dn = (\<delta>, v)" using sd vdv ddd ddmd by simp
  qed
  have deq: "\<delta> = dd" using bform bn by (auto split: if_splits)
  have dne: "\<delta> \<noteq> - 1"
  proof
    assume "\<delta> = - 1"
    hence "dd = - 1" using deq by simp
    hence "bottleneck s e in_U p1 p2 = (- 1, True, r, False, False)" using bform by simp
    thus False using bn by simp
  qed
  have mu_gt: "\<not> up_side \<Longrightarrow> mu = - 1 \<or> \<delta> < mu"
  proof -
    assume us: "\<not> up_side"
    have narm: "\<not> (mu \<noteq> - 1 \<and> mu = dd)"
    proof (rule ccontr)
      assume "\<not> \<not> (mu \<noteq> - 1 \<and> mu = dd)" hence a: "mu \<noteq> - 1 \<and> mu = dd" by simp
      have f: "bottleneck s e in_U p1 p2 = (dd, False, vu, par_up s vu, True)"
      using bform a bn by (auto split: if_splits)
      have "up_side" using bn f by (metis Pair_inject)
      thus False using us by simp
    qed
    show "mu = - 1 \<or> \<delta> < mu"
    proof (cases "mu = - 1")
      case True thus ?thesis by simp
    next
      case muf: False
      hence mune: "mu \<noteq> dd" using narm by simp
      have mmne: "mininf mu md \<noteq> - 1" using muf mdS by (auto simp: mininf_def)
      have "dd \<le> mininf mu md" using mininf_le2[OF mmne] by (simp add: dd_def)
      also have "... \<le> mu" using mininf_le1[OF muf] .
      finally have "dd \<le> mu" .
      thus ?thesis using deq mune by auto
    qed
  qed
  have upStrict: "\<And>w. \<not> up_side \<Longrightarrow> w \<in> set ?up \<Longrightarrow> res_up s w \<noteq> - 1 \<Longrightarrow> \<delta> < res_up s w"
  proof -
    fix w assume us: "\<not> up_side" and wup: "w \<in> set ?up" and wne: "res_up s w \<noteq> - 1"
    have "mu \<noteq> - 1 \<and> mu \<le> res_up s w" using scan_up_min[OF su wup wne] .
    thus "\<delta> < res_up s w" using mu_gt[OF us] by auto
  qed
  have regt: "\<not> up_side \<Longrightarrow> re = - 1 \<or> \<delta> < re"
  proof -
    assume us: "\<not> up_side"
    have rne: "re \<noteq> dd"
    proof (rule ccontr)
      assume "\<not> re \<noteq> dd" hence "re = dd" by simp
      have narm: "\<not> (mu \<noteq> - 1 \<and> mu = dd)"
      proof (rule ccontr)
        assume "\<not> \<not> (mu \<noteq> - 1 \<and> mu = dd)" hence a: "mu \<noteq> - 1 \<and> mu = dd" by simp
        have f: "bottleneck s e in_U p1 p2 = (dd, False, vu, par_up s vu, True)"
        using bform a bn by (auto split: if_splits)
        have "up_side" using bn f by (metis Pair_inject)
        thus False using us by simp
      qed
      have "bottleneck s e in_U p1 p2 = (dd, True, r, False, False)" using bform narm bn \<open>re = dd\<close> by (auto split: if_splits)
      thus False using bn by simp
    qed
    show "re = - 1 \<or> \<delta> < re"
    proof (cases "re = - 1")
      case True thus ?thesis by simp
    next
      case ref: False
      have "dd \<le> re" using mininf_le1[OF ref] by (simp add: dd_def)
      thus ?thesis using deq rne ref by auto
    qed
  qed
  obtain k where klen: "k < length P" and Pk: "P ! k = v" using vPP by (auto simp: in_set_conv_nth)
  have dropk: "drop k P = v # drop (Suc k) P" using Cons_nth_drop_Suc[OF klen] Pk by simp
  have allne: "\<And>x. x \<in> set (take k P) \<Longrightarrow> x \<noteq> v"
  proof -
    fix x assume xin: "x \<in> set (take k P)"
    obtain i where il: "i < length (take k P)" and xp: "take k P ! i = x" using xin by (metis in_set_conv_nth)
    have ik: "i < k" using il klen by simp
    have xPi: "x = P ! i" using xp ik by simp
    have iLP: "i < length P" using ik klen by simp
    have "P ! i \<noteq> P ! k" using nth_eq_iff_index_eq[OF Pdist iLP klen] ik by simp
    thus "x \<noteq> v" using xPi Pk by simp
  qed
  have tw_take: "takeWhile (\<lambda>y. y \<noteq> v) P = take k P"
  proof -
    have A: "takeWhile (\<lambda>y. y \<noteq> v) (take k P @ drop k P) = take k P @ takeWhile (\<lambda>y. y \<noteq> v) (drop k P)"
    by (rule takeWhile_append2[OF allne])
    have "takeWhile (\<lambda>y. y \<noteq> v) P = take k P @ takeWhile (\<lambda>y. y \<noteq> v) (drop k P)" using A by simp
    thus ?thesis using dropk by simp
  qed
  have Pne: "P \<noteq> []" using klen by auto
  have hdP: "hd P = P ! 0" using Pne by (simp add: hd_conv_nth)
  have memtk: "\<And>i. i < k \<Longrightarrow> P ! i \<in> set (takeWhile (\<lambda>y. y \<noteq> v) P)"
  proof -
    fix i assume ik: "i < k"
    have "take k P ! i = P ! i" using ik by simp
    moreover have "i < length (take k P)" using ik klen by simp
    ultimately show "P ! i \<in> set (takeWhile (\<lambda>y. y \<noteq> v) P)" using tw_take by (metis nth_mem)
  qed
  have spine_pred: "\<And>v'. v' \<in> insert v (set (takeWhile (\<lambda>y. y \<noteq> v) P)) \<Longrightarrow> v' \<noteq> hd P \<Longrightarrow> \<exists>i. Suc i < length P \<and> P ! Suc i = v' \<and> P ! i \<in> set (takeWhile (\<lambda>y. y \<noteq> v) P)"
  proof -
    fix v' assume vsp: "v' \<in> insert v (set (takeWhile (\<lambda>y. y \<noteq> v) P))" and vhd: "v' \<noteq> hd P"
    have vtk: "v' = v \<or> v' \<in> set (take k P)" using vsp tw_take by simp
    show "\<exists>i. Suc i < length P \<and> P ! Suc i = v' \<and> P ! i \<in> set (takeWhile (\<lambda>y. y \<noteq> v) P)"
    proof (cases "v' = v")
      case True
      have k0: "0 < k"
      proof (rule ccontr)
        assume "\<not> 0 < k" hence "k = 0" by simp
        hence "v' = hd P" using True Pk hdP by simp
        thus False using vhd by simp
      qed
      then obtain kk where kkk: "k = Suc kk" by (cases k) auto
      have "Suc kk < length P \<and> P ! Suc kk = v' \<and> P ! kk \<in> set (takeWhile (\<lambda>y. y \<noteq> v) P)"
      using kkk klen Pk True memtk[of kk] by simp
      thus ?thesis by blast
    next
      case False
      hence vin: "v' \<in> set (take k P)" using vtk by simp
      obtain j where jl: "j < length (take k P)" and vpj: "take k P ! j = v'" by (metis vin in_set_conv_nth)
      have jk: "j < k" using jl klen by simp
      have vPj: "P ! j = v'" using vpj jk by simp
      have j0: "0 < j"
      proof (rule ccontr)
        assume "\<not> 0 < j" hence "j = 0" by simp
        hence "v' = hd P" using vPj hdP by simp
        thus False using vhd by simp
      qed
      then obtain jj where jjj: "j = Suc jj" by (cases j) auto
      have "Suc jj < length P \<and> P ! Suc jj = v' \<and> P ! jj \<in> set (takeWhile (\<lambda>y. y \<noteq> v) P)"
      using jjj jk klen vPj memtk[of jj] by simp
      thus ?thesis by blast
    qed
  qed
  have PsubVr: "set P \<subseteq> \<V> - {r}" using P_side upV dnV by (cases up_side) auto
  have flowP: "\<And>w. w \<in> set P \<Longrightarrow> flow_lookup ?f' (par_edge s w) = flow_lookup (current_flow s) (par_edge s w) + (if up_side then ?gup w else ?gdn w)"
  proof -
    fix w assume wP: "w \<in> set P"
    have wVr: "w \<in> \<V> - {r}" using wP PsubVr by auto
    show "flow_lookup ?f' (par_edge s w) = flow_lookup (current_flow s) (par_edge s w) + (if up_side then ?gup w else ?gdn w)"
    proof (cases up_side)
      case True
      have wup: "w \<in> set ?up" using wP P_side True by simp
      have wndn: "w \<notin> set ?dn" using wup updisj by auto
      show ?thesis using treeval[OF wVr] wup wndn True by simp
    next
      case False
      have wdn: "w \<in> set ?dn" using wP P_side False by simp
      have wnup: "w \<notin> set ?up" using wdn updisj by auto
      show ?thesis using treeval[OF wVr] wdn wnup False by simp
    qed
  qed
  have fnn: "\<And>a. a \<in> \<E> \<Longrightarrow> 0 \<le> flow_lookup (current_flow s) a" using res_bwd_nonneg[OF inv] by (simp add: res_bwd_def)
  have fle_cap: "\<And>a. a \<in> \<E> \<Longrightarrow> cap a \<noteq> - 1 \<Longrightarrow> flow_lookup (current_flow s) a \<le> cap a"
  proof -
    fix a assume aE: "a \<in> \<E>" and cne: "cap a \<noteq> - 1"
    have cnn: "0 \<le> cap a" using cap_nonneg[OF aE] cne by simp
    have ue: "\<u> a = ereal (h (cap a))" using cap_finite[OF aE cnn] .
    show "flow_lookup (current_flow s) a \<le> cap a" using iu aE ue by (auto simp: isuflow_def comp_def)
  qed
  have capfin_res: "\<And>a. res_fwd s a \<noteq> - 1 \<Longrightarrow> cap a \<noteq> - 1"
  proof -
    fix a assume rne: "res_fwd s a \<noteq> - 1"
    show "cap a \<noteq> - 1"
    proof assume "cap a = - 1" hence "res_fwd s a = - 1" by (simp add: res_fwd_def) thus False using rne by simp
    qed
  qed
  have cap_fit: "\<And>a. a \<in> \<E> \<Longrightarrow> res_fwd s a \<noteq> - 1 \<Longrightarrow> \<delta> < res_fwd s a \<Longrightarrow> ereal (h (flow_lookup (current_flow s) a + \<delta>)) < \<u> a"
  proof -
    fix a assume aE: "a \<in> \<E>" and rne: "res_fwd s a \<noteq> - 1" and dlt: "\<delta> < res_fwd s a"
    have cfin: "cap a \<noteq> - 1" using capfin_res[OF rne] .
    hence cnn: "0 \<le> cap a" using cap_nonneg[OF aE] by simp
    have ue: "\<u> a = ereal (h (cap a))" using cap_finite[OF aE cnn] .
    have "res_fwd s a = cap a - flow_lookup (current_flow s) a" using cfin by (simp add: res_fwd_def)
    hence "flow_lookup (current_flow s) a + \<delta> < cap a" using dlt by simp
    thus "ereal (h (flow_lookup (current_flow s) a + \<delta>)) < \<u> a" using ue by simp
  qed
  have inf_fit: "\<And>a x. a \<in> \<E> \<Longrightarrow> res_fwd s a = - 1 \<Longrightarrow> ereal x < \<u> a"
  proof -
    fix a x assume aE: "a \<in> \<E>" and rf: "res_fwd s a = - 1"
    have capm1: "cap a = - 1"
    proof (rule ccontr)
      assume cne: "cap a \<noteq> - 1"
      have fc: "flow_lookup (current_flow s) a \<le> cap a" using fle_cap[OF aE cne] .
      have "res_fwd s a = cap a - flow_lookup (current_flow s) a" using cne by (simp add: res_fwd_def)
      hence "cap a - flow_lookup (current_flow s) a = - 1" using rf by simp
      thus False using fc by linarith
    qed
    hence "\<u> a = \<infinity>" using cap_infinite[OF aE] by simp
    thus "ereal x < \<u> a" by simp
  qed
  obtain a1 p31 where w1: "walk_betw (abstract_arborescense (spanning_tree s)) (fst e) (p1 @ a1 # p31) r"
  and w2: "walk_betw (abstract_arborescense (spanning_tree s)) (snd e) (p2 @ a1 # p31) r"
  using get_path_pair(1)[OF arbb pp neq fVe sVe] by meson
  have hdp1: "p1 \<noteq> [] \<Longrightarrow> hd p1 = fst e"
  proof - assume "p1 \<noteq> []"
    have "hd (p1 @ a1 # p31) = fst e" using w1 by (simp add: walk_betw_def)
    thus "hd p1 = fst e" using \<open>p1 \<noteq> []\<close> by simp
  qed
  have hdp2: "p2 \<noteq> [] \<Longrightarrow> hd p2 = snd e"
  proof - assume "p2 \<noteq> []"
    have "hd (p2 @ a1 # p31) = snd e" using w2 by (simp add: walk_betw_def)
    thus "hd p2 = snd e" using \<open>p2 \<noteq> []\<close> by simp
  qed
  have hdP_val: "hd P = (if up_side = in_U then fst e else snd e)"
  proof -
    have p1c: "P = p1 \<Longrightarrow> hd P = fst e" using hdp1 Pne by auto
    have p2c: "P = p2 \<Longrightarrow> hd P = snd e" using hdp2 Pne by auto
    show ?thesis using P_side p1c p2c by (cases up_side; cases in_U) auto
  qed
  have strict_v: "\<And>v'. v' \<in> \<V> - {r} \<Longrightarrow> (if par_up ?s' v' then ereal (h (flow_lookup (current_flow ?s') (par_edge ?s' v'))) < \<u> (par_edge ?s' v') else flow_lookup (current_flow ?s') (par_edge ?s' v') > 0)"
  proof -
    fix v' assume v'V: "v' \<in> \<V> - {r}"
    have paredgeE: "par_edge s v' \<in> \<E>" using ns_invar_tree_edgeD[OF treeinv v'V] .
    show "if par_up ?s' v' then ereal (h (flow_lookup (current_flow ?s') (par_edge ?s' v'))) < \<u> (par_edge ?s' v') else flow_lookup (current_flow ?s') (par_edge ?s' v') > 0"
    proof (cases "v' \<in> insert v (set (takeWhile (\<lambda>y. y \<noteq> v) P))")
      case offspine: False
      have off_pe: "parent_lookup parr v' = par_edge s v'" and off_pu: "dir_lookup darr v' = par_up s v'"
      using rp_off[OF offspine] by auto
      have tv: "flow_lookup ?f' (par_edge s v') = flow_lookup (current_flow s) (par_edge s v') + (if v' \<in> set ?up then ?gup v' else 0) + (if v' \<in> set ?dn then ?gdn v' else 0)"
      using treeval[OF v'V] .
      have main: "if par_up s v' then ereal (h (flow_lookup ?f' (par_edge s v'))) < \<u> (par_edge s v') else flow_lookup ?f' (par_edge s v') > 0"
      proof (cases "v' \<in> set ?up")
        case inup: True
        have vndn: "v' \<notin> set ?dn" using inup updisj by auto
        have tv': "flow_lookup ?f' (par_edge s v') = flow_lookup (current_flow s) (par_edge s v') + ?gup v'" using tv inup vndn by simp
        have rud: "res_up s v' = - 1 \<or> \<delta> < res_up s v'"
        proof (cases "res_up s v' = - 1")
          case True thus ?thesis by simp
        next
          case rne: False
          show ?thesis
          proof (cases up_side)
            case us: True
            have vout: "v' \<notin> insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ?up))" using offspine P_side us by simp
            thus ?thesis using scan_up_after[OF scanU_v[OF us] dne updist inup vout rne] by simp
          next
            case us: False
            thus ?thesis using upStrict[OF us inup rne] by simp
          qed
        qed
        show ?thesis
        proof (cases "par_up s v'")
          case pu: True
          have rue: "res_up s v' = res_fwd s (par_edge s v')" using pu by (simp add: res_up_def)
          have "ereal (h (flow_lookup ?f' (par_edge s v'))) < \<u> (par_edge s v')"
          proof (cases "res_fwd s (par_edge s v') = - 1")
            case True thus ?thesis using inf_fit[OF paredgeE True] tv' pu by simp
          next
            case rf: False
            have "\<delta> < res_fwd s (par_edge s v')" using rud rue rf by auto
            thus ?thesis using cap_fit[OF paredgeE rf] tv' pu by simp
          qed
          thus ?thesis using pu by simp
        next
          case pd: False
          have rue: "res_up s v' = flow_lookup (current_flow s) (par_edge s v')" using pd by (simp add: res_up_def res_bwd_def)
          have "res_up s v' \<noteq> - 1" using rue fnn[OF paredgeE] by simp
          hence "\<delta> < res_up s v'" using rud by simp
          thus ?thesis using tv' pd rue by simp
        qed
      next
        case notup: False
        have os: "if par_up s v' then ereal (h (flow_lookup (current_flow s) (par_edge s v'))) < \<u> (par_edge s v') else flow_lookup (current_flow s) (par_edge s v') > 0" using oldstrict[OF v'V] .
        show ?thesis
        proof (cases "v' \<in> set ?dn")
          case indn: True
          have tv': "flow_lookup ?f' (par_edge s v') = flow_lookup (current_flow s) (par_edge s v') + ?gdn v'" using tv notup indn by simp
          show ?thesis
          proof (cases "par_up s v'")
            case pu: True
            have "ereal (h (flow_lookup ?f' (par_edge s v'))) \<le> ereal (h (flow_lookup (current_flow s) (par_edge s v')))" using tv' pu d0ge by simp
            also have "... < \<u> (par_edge s v')" using os pu by simp
            finally show ?thesis using pu by simp
          next
            case pd: False
            have "flow_lookup ?f' (par_edge s v') = flow_lookup (current_flow s) (par_edge s v') + \<delta>" using tv' pd by simp
            thus ?thesis using os pd d0ge by simp
          qed
        next
          case notdn: False
          have "flow_lookup ?f' (par_edge s v') = flow_lookup (current_flow s) (par_edge s v')" using tv notup notdn by simp
          thus ?thesis using os by simp
        qed
      qed
      show "if par_up ?s' v' then ereal (h (flow_lookup (current_flow ?s') (par_edge ?s' v'))) < \<u> (par_edge ?s' v') else flow_lookup (current_flow ?s') (par_edge ?s' v') > 0"
      using main by (simp add: parup'_eq paredge'_eq pj_flow off_pe off_pu)
    next
      case onspine: True
      show "if par_up ?s' v' then ereal (h (flow_lookup (current_flow ?s') (par_edge ?s' v'))) < \<u> (par_edge ?s' v') else flow_lookup (current_flow ?s') (par_edge ?s' v') > 0"
      proof (cases "v' = hd P")
        case hdc: True
        have pe: "parent_lookup parr v' = e" and pu: "dir_lookup darr v' = (hd P = fst e)" using rp_head hdc by auto
        have ef: "flow_lookup ?f' e = flow_lookup (current_flow s) e + ?ce" using e_flow .
        have main: "if (hd P = fst e) then ereal (h (flow_lookup ?f' e)) < \<u> e else flow_lookup ?f' e > 0"
        proof (cases up_side)
          case us: True
          have dpos: "0 < \<delta>" using upside_dpos[OF us] .
          show ?thesis
          proof (cases in_U)
            case iu2: True
            have hdfst: "hd P = fst e" using hdP_val us iu2 by simp
            have "ereal (h (flow_lookup ?f' e)) < \<u> e" using ef dpos iu2 by (simp add: eUu[OF iu2, symmetric])
            thus ?thesis using hdfst by simp
          next
            case iu2: False
            have hdnfst: "hd P \<noteq> fst e" using hdP_val us iu2 neq by simp
            have "flow_lookup ?f' e > 0" using ef eL0[OF iu2] dpos iu2 by simp
            thus ?thesis using hdnfst by simp
          qed
        next
          case us: False
          show ?thesis
          proof (cases in_U)
            case iu2: True
            have hdnfst: "hd P \<noteq> fst e" using hdP_val us iu2 neq by simp
            have reb: "re = flow_lookup (current_flow s) e" using iu2 by (simp add: re_def res_bwd_def)
            have dlt: "\<delta> < flow_lookup (current_flow s) e" using regt[OF us] reb fnn[OF eE] by auto
            have "flow_lookup ?f' e > 0" using ef iu2 dlt by simp
            thus ?thesis using hdnfst by simp
          next
            case iu2: False
            have hdfst: "hd P = fst e" using hdP_val us iu2 by simp
            have ref: "re = res_fwd s e" using iu2 by (simp add: re_def)
            have fe0: "flow_lookup (current_flow s) e = 0" using eL0[OF iu2] .
            have "ereal (h (flow_lookup ?f' e)) < \<u> e"
            proof (cases "res_fwd s e = - 1")
              case True thus ?thesis using inf_fit[OF eE True] by simp
            next
              case rf: False
              have "\<delta> < res_fwd s e" using regt[OF us] ref rf by auto
              thus ?thesis using cap_fit[OF eE rf] ef fe0 iu2 by simp
            qed
            thus ?thesis using hdfst by simp
          qed
        qed
        show "if par_up ?s' v' then ereal (h (flow_lookup (current_flow ?s') (par_edge ?s' v'))) < \<u> (par_edge ?s' v') else flow_lookup (current_flow ?s') (par_edge ?s' v') > 0"
        using main by (simp add: parup'_eq paredge'_eq pj_flow pe pu)
      next
        case nothd: False
        obtain i where iL: "Suc i < length P" and Pi: "P ! Suc i = v'" and Pimem: "P ! i \<in> set (takeWhile (\<lambda>y. y \<noteq> v) P)"
        using spine_pred[OF onspine nothd] by blast
        have pe: "parent_lookup parr v' = par_edge s (P ! i)" and pu: "dir_lookup darr v' = (\<not> par_up s (P ! i))"
        using rp_nth[OF iL Pimem] Pi by auto
        have PiP: "P ! i \<in> set P" using Pimem by (auto dest: set_takeWhileD)
        have PiVr: "P ! i \<in> \<V> - {r}" using PiP PsubVr by auto
        have PieE: "par_edge s (P ! i) \<in> \<E>" using ns_invar_tree_edgeD[OF treeinv PiVr] .
        have PieE_cnn: "cap (par_edge s (P ! i)) \<noteq> - 1 \<Longrightarrow> 0 \<le> cap (par_edge s (P ! i))" using cap_nonneg[OF PieE] by simp
        have fl: "flow_lookup ?f' (par_edge s (P ! i)) = flow_lookup (current_flow s) (par_edge s (P ! i)) + (if up_side then ?gup (P ! i) else ?gdn (P ! i))" using flowP[OF PiP] .
        have main: "if (\<not> par_up s (P ! i)) then ereal (h (flow_lookup ?f' (par_edge s (P ! i)))) < \<u> (par_edge s (P ! i)) else flow_lookup ?f' (par_edge s (P ! i)) > 0"
        proof (cases up_side)
          case us: True
          have dpos: "0 < \<delta>" using upside_dpos[OF us] .
          show ?thesis
          proof (cases "par_up s (P ! i)")
            case pu2: True
            have "flow_lookup ?f' (par_edge s (P ! i)) = flow_lookup (current_flow s) (par_edge s (P ! i)) + \<delta>" using fl us pu2 by simp
            thus ?thesis using fnn[OF PieE] dpos pu2 by simp
          next
            case pd2: False
            have f'eq: "flow_lookup ?f' (par_edge s (P ! i)) = flow_lookup (current_flow s) (par_edge s (P ! i)) - \<delta>" using fl us pd2 by simp
            have "ereal (h (flow_lookup ?f' (par_edge s (P ! i)))) < \<u> (par_edge s (P ! i))"
            proof (cases "cap (par_edge s (P ! i)) = - 1")
              case True hence "\<u> (par_edge s (P ! i)) = \<infinity>" using cap_infinite[OF PieE] by simp
              thus ?thesis by simp
            next
              case cf: False
              have fc: "flow_lookup (current_flow s) (par_edge s (P ! i)) \<le> cap (par_edge s (P ! i))" using fle_cap[OF PieE cf] .
              have ue: "\<u> (par_edge s (P ! i)) = ereal (h (cap (par_edge s (P ! i))))" using cap_finite[OF PieE PieE_cnn[OF cf]] .
              have "flow_lookup (current_flow s) (par_edge s (P ! i)) - \<delta> < cap (par_edge s (P ! i))" using fc dpos by simp
              thus ?thesis using f'eq ue by (simp del: h_diff)
            qed
            thus ?thesis using pd2 by simp
          qed
        next
          case us: False
          have Pidn: "P ! i \<in> set (takeWhile (\<lambda>y. y \<noteq> v) ?dn)" using Pimem P_side us by simp
          have rdd: "res_down s (P ! i) = - 1 \<or> \<delta> < res_down s (P ! i)"
          proof (cases "res_down s (P ! i) = - 1")
            case True thus ?thesis by simp
          next
            case rne: False
            thus ?thesis using scan_down_before[OF scanD_v[OF us] dne dndist Pidn rne] by simp
          qed
          show ?thesis
          proof (cases "par_up s (P ! i)")
            case pu2: True
            have rud: "res_down s (P ! i) = flow_lookup (current_flow s) (par_edge s (P ! i))" using pu2 by (simp add: res_down_def res_bwd_def)
            have "res_down s (P ! i) \<noteq> - 1" using rud fnn[OF PieE] by simp
            hence dlt: "\<delta> < res_down s (P ! i)" using rdd by simp
            have "flow_lookup ?f' (par_edge s (P ! i)) = flow_lookup (current_flow s) (par_edge s (P ! i)) - \<delta>" using fl us pu2 by simp
            thus ?thesis using dlt rud pu2 by simp
          next
            case pd2: False
            have rud: "res_down s (P ! i) = res_fwd s (par_edge s (P ! i))" using pd2 by (simp add: res_down_def)
            have f'eq: "flow_lookup ?f' (par_edge s (P ! i)) = flow_lookup (current_flow s) (par_edge s (P ! i)) + \<delta>" using fl us pd2 by simp
            have "ereal (h (flow_lookup ?f' (par_edge s (P ! i)))) < \<u> (par_edge s (P ! i))"
            proof (cases "res_fwd s (par_edge s (P ! i)) = - 1")
              case True thus ?thesis using inf_fit[OF PieE True] f'eq by simp
            next
              case rf: False
              have "\<delta> < res_fwd s (par_edge s (P ! i))" using rdd rud rf by auto
              thus ?thesis using cap_fit[OF PieE rf] f'eq by simp
            qed
            thus ?thesis using pd2 by simp
          qed
        qed
        show "if par_up ?s' v' then ereal (h (flow_lookup (current_flow ?s') (par_edge ?s' v'))) < \<u> (par_edge ?s' v') else flow_lookup (current_flow ?s') (par_edge ?s' v') > 0"
        using main by (simp add: parup'_eq paredge'_eq pj_flow pe pu)
      qed
    qed
  qed
  have strict': "ns_invar_strict ?s'"
  unfolding ns_invar_strict_def by (rule ballI) (rule strict_v)
  have rV: "r \<in> \<V>" using general(1) .
  have arb: "arborescense_invar (spanning_tree s)"
  using ns_invar_implD(7)[OF ns_invarD(1)[OF inv]] .
  have succ_along: "\<And>W x j. walk_betw (abstract_arborescense (spanning_tree s)) x W r \<Longrightarrow> distinct W \<Longrightarrow> Suc j < length W \<Longrightarrow> W ! j \<in> \<V> - {r} \<Longrightarrow> par_vx s (W ! j) = W ! Suc j"
  proof -
    fix W x j
    assume wW: "walk_betw (abstract_arborescense (spanning_tree s)) x W r"
    and dW: "distinct W" and jl: "Suc j < length W" and jVr: "W ! j \<in> \<V> - {r}"
    have jlen: "j < length W" using jl by simp
    have decomp: "W = take j W @ [W ! j] @ drop (Suc j) W"
    using id_take_nth_drop[OF jlen] by simp
    have wsuff: "walk_betw (abstract_arborescense (spanning_tree s)) (W ! j) (W ! j # drop (Suc j) W) r"
    using walk_suff[of "abstract_arborescense (spanning_tree s)" x "take j W" "W ! j" "drop (Suc j) W" r]
    wW decomp by simp
    have dsuff: "distinct (W ! j # drop (Suc j) W)"
    using dW jlen by (metis Cons_nth_drop_Suc distinct_drop)
    obtain q where q: "distinct (W ! j # par_vx s (W ! j) # q) \<and> walk_betw (abstract_arborescense (spanning_tree s)) (W ! j) (W ! j # par_vx s (W ! j) # q) r"
    using par_vx_walk_succ[OF inv jVr] by blast
    have jV: "W ! j \<in> \<V>" using jVr by simp
    have uniqj: "\<exists>!p. walk_betw (abstract_arborescense (spanning_tree s)) (W ! j) p r \<and> distinct p"
    using general(3)[OF arb rV jV] .
    have eqw: "W ! j # drop (Suc j) W = W ! j # par_vx s (W ! j) # q"
    using uniqj wsuff dsuff q by (metis (mono_tags, lifting))
    hence "drop (Suc j) W = par_vx s (W ! j) # q" by simp
    hence "(drop (Suc j) W) ! 0 = par_vx s (W ! j)" by simp
    thus "par_vx s (W ! j) = W ! Suc j" using jl by simp
  qed
  have eE: "e \<in> \<E>" using ns_select_SomeD(2)[OF inv sel] .
  have neq: "fst e \<noteq> snd e" using entering_not_selfloop[OF inv sel] .
  have fV: "fst e \<in> \<V>" using fst_E_V[OF eE] .
  have sV: "snd e \<in> \<V>" using snd_E_V[OF eE] .
  obtain aa p3 where
  wa1: "walk_betw (abstract_arborescense (spanning_tree s)) (fst e) (p1 @ aa # p3) r" and
  wa2: "walk_betw (abstract_arborescense (spanning_tree s)) (snd e) (p2 @ aa # p3) r" and
  da1: "distinct (p1 @ aa # p3)" and da2: "distinct (p2 @ aa # p3)" and
  pdisj: "set p1 \<inter> set p2 = {}"
  using get_path_pair(1)[OF arb pp neq fV sV] by blast
  obtain xP where WPwalk: "walk_betw (abstract_arborescense (spanning_tree s)) xP (P @ aa # p3) r"
  and WPdist: "distinct (P @ aa # p3)"
  using wa1 wa2 da1 da2 by (cases "in_U = up_side") (auto simp: P_def)
  have spineGeo: "\<And>i. Suc i < length P \<Longrightarrow> par_vx s (P ! i) = P ! Suc i"
  proof -
    fix i assume iL: "Suc i < length P"
    have iP: "i < length P" using iL by simp
    have sucL: "Suc i < length (P @ aa # p3)" using iL by (simp add: nth_append)
    have e1: "(P @ aa # p3) ! i = P ! i" using iP by (simp add: nth_append)
    have e2: "(P @ aa # p3) ! Suc i = P ! Suc i" using iL by (simp add: nth_append)
    have Pimem: "P ! i \<in> set P" using iP by (simp add: nth_mem)
    have PiVr: "(P @ aa # p3) ! i \<in> \<V> - {r}" unfolding e1 by (rule subsetD[OF PsubVr Pimem])
    have "par_vx s ((P @ aa # p3) ! i) = (P @ aa # p3) ! Suc i"
    using succ_along[OF WPwalk WPdist sucL PiVr] .
    thus "par_vx s (P ! i) = P ! Suc i" using e1 e2 by simp
  qed
  have de_v: "\<And>v'. v' \<in> \<V> - {r} \<Longrightarrow> par_edge ?s' v' \<in> \<E> \<and> (if par_up ?s' v' then fst (par_edge ?s' v') = v' else snd (par_edge ?s' v') = v')"
  proof -
    fix v' assume v'Vr: "v' \<in> \<V> - {r}"
    have pe': "par_edge ?s' v' = parent_lookup parr v'" using paredge'_eq .
    have pu': "par_up ?s' v' = dir_lookup darr v'" using parup'_eq .
    show "par_edge ?s' v' \<in> \<E> \<and> (if par_up ?s' v' then fst (par_edge ?s' v') = v' else snd (par_edge ?s' v') = v')"
    proof (cases "v' \<in> insert v (set (takeWhile (\<lambda>y. y \<noteq> v) P))")
      case False
      have "parent_lookup parr v' = par_edge s v' \<and> dir_lookup darr v' = par_up s v'"
      using rp_off[OF False] .
      hence pev: "par_edge ?s' v' = par_edge s v'" and puv: "par_up ?s' v' = par_up s v'"
      using pe' pu' by simp_all
      have eE': "par_edge s v' \<in> \<E>" using ns_invar_tree_edgeD[OF treeinv v'Vr] .
      have dv: "if par_up s v' then fst (par_edge s v') = v' else snd (par_edge s v') = v'"
      using ns_invar_tree_dirD[OF treeinv v'Vr] .
      show ?thesis using eE' dv pev puv by simp
    next
      case True
      show ?thesis
      proof (cases "v' = hd P")
        case True
        have pev: "par_edge ?s' v' = e" using pe' rp_head True by simp
        have puv: "par_up ?s' v' = (v' = fst e)" using pu' rp_head True by simp
        have hdcase: "v' = fst e \<or> v' = snd e" using True hdP_val by auto
        show ?thesis using pev puv eE hdcase neq by auto
      next
        case False
        obtain i where iL: "Suc i < length P" and vi: "P ! Suc i = v'"
        and imem: "P ! i \<in> set (takeWhile (\<lambda>y. y \<noteq> v) P)"
        using spine_pred[OF True False] by blast
        have pev: "par_edge ?s' v' = par_edge s (P ! i)"
        using pe' rp_nth[OF iL imem] vi by simp
        have puv: "par_up ?s' v' = (\<not> par_up s (P ! i))"
        using pu' rp_nth[OF iL imem] vi by simp
        have PiP: "P ! i \<in> set P" using imem set_takeWhileD by fast
        have PiVr: "P ! i \<in> \<V> - {r}" using PsubVr PiP by blast
        have eE': "par_edge s (P ! i) \<in> \<E>" using ns_invar_tree_edgeD[OF treeinv PiVr] .
        have dvi: "if par_up s (P ! i) then fst (par_edge s (P ! i)) = P ! i else snd (par_edge s (P ! i)) = P ! i"
        using ns_invar_tree_dirD[OF treeinv PiVr] .
        have geo: "par_vx s (P ! i) = v'" using spineGeo[OF iL] vi by simp
        have other: "(if par_up s (P ! i) then snd (par_edge s (P ! i)) else fst (par_edge s (P ! i))) = v'"
        using geo by (simp add: par_vx_def)
        show ?thesis using eE' pev puv dvi other by (auto split: if_splits)
      qed
    qed
  qed
  have parwalk: "\<And>T g w0. arborescense_invar T \<Longrightarrow> abstract_arborescense T = (\<lambda>x. {x, g x}) ` (\<V> - {r}) \<Longrightarrow> w0 \<in> \<V> - {r} \<Longrightarrow> (\<exists>q. distinct (w0 # g w0 # q) \<and> walk_betw (abstract_arborescense T) w0 (w0 # g w0 # q) r)"
  proof -
    fix T g w00
    assume aiT: "arborescense_invar T"
    and echar: "abstract_arborescense T = (\<lambda>x. {x, g x}) ` (\<V> - {r})"
    and w00Vr: "w00 \<in> \<V> - {r}"
    have giT: "graph_invar (abstract_arborescense T)" using general(2)[OF aiT] .
    have uniqT: "\<And>x. x \<in> \<V> \<Longrightarrow> \<exists>!p. walk_betw (abstract_arborescense T) x p r \<and> distinct p"
    using general(3)[OF aiT rV] by simp
    have hilf: "\<And>n. \<forall>w p. length p = n \<longrightarrow> w \<in> \<V> - {r} \<longrightarrow> walk_betw (abstract_arborescense T) w p r \<longrightarrow> distinct p \<longrightarrow> (\<exists>q. distinct (w # g w # q) \<and> walk_betw (abstract_arborescense T) w (w # g w # q) r)"
    (is "\<And>n. ?Ph n")
    proof -
      fix n show "?Ph n"
      proof (induct n rule: less_induct)
        case (less n)
        show ?case
        proof (intro allI impI)
          fix w p assume lp: "length p = n" and wVr: "w \<in> \<V> - {r}"
          and wp: "walk_betw (abstract_arborescense T) w p r" and dp: "distinct p"
          have wne: "w \<noteq> r" using wVr by simp
          have hdp: "hd p = w" and lstp: "last p = r" and pne: "p \<noteq> []"
          using wp by (auto simp: walk_betw_def)
          obtain rest where prest: "p = w # rest" using hdp pne by (cases p) auto
          have restne: "rest \<noteq> []" using prest lstp wne by (cases rest) auto
          then obtain u p' where restdec: "rest = u # p'" by (cases rest) auto
          have pdec: "p = w # u # p'" using prest restdec by simp
          have wcons: "walk_betw (abstract_arborescense T) u (u # p') r \<and> walk_betw (abstract_arborescense T) w [w, u] u"
          using wp pdec walk_betw_cons by metis
          have restw: "walk_betw (abstract_arborescense T) u (u # p') r" using wcons by simp
          have edgwu: "{w, u} \<in> abstract_arborescense T"
          using wcons by (auto simp: walk_betw_def)
          have wu_ne: "w \<noteq> u" using dp pdec by simp
          obtain x where xVr: "x \<in> \<V> - {r}" and exwu: "{w, u} = {x, g x}"
          using edgwu echar by auto
          show "\<exists>q. distinct (w # g w # q) \<and> walk_betw (abstract_arborescense T) w (w # g w # q) r"
          proof (cases "x = w")
            case True
            have ugw: "u = g w" using exwu True wu_ne by (auto simp: doubleton_eq_iff)
            have pg: "p = w # g w # p'" using pdec ugw by simp
            show ?thesis using wp dp unfolding pg by blast
          next
            case False
            have wux: "w = g x \<and> u = x" using exwu False by (auto simp: doubleton_eq_iff)
            have wgx: "w = g x" and ux: "u = x" using wux by simp_all
            have dxp': "distinct (x # p')" using dp pdec ux by simp
            have lenlt: "length (x # p') < n" using lp pdec by simp
            have restx: "walk_betw (abstract_arborescense T) x (x # p') r" using restw ux by simp
            have Qx: "\<exists>q'. distinct (x # g x # q') \<and> walk_betw (abstract_arborescense T) x (x # g x # q') r"
            using less.hyps[OF lenlt] xVr restx dxp' by blast
            obtain q' where q'a: "distinct (x # g x # q')"
            and q'b: "walk_betw (abstract_arborescense T) x (x # g x # q') r" using Qx by blast
            have xV: "x \<in> \<V>" using xVr by simp
            have "x # p' = x # g x # q'"
            using uniqT[OF xV] restx dxp' q'a q'b by (metis (mono_tags, lifting))
            hence "p' = w # q'" using wgx by simp
            hence "p = w # x # w # q'" using pdec ux by simp
            thus ?thesis using dp by simp
          qed
        qed
      qed
    qed
    obtain p0 where p0: "walk_betw (abstract_arborescense T) w00 p0 r" "distinct p0"
    using uniqT[of w00] w00Vr by blast
    show "\<exists>q. distinct (w00 # g w00 # q) \<and> walk_betw (abstract_arborescense T) w00 (w00 # g w00 # q) r"
    using hilf[of "length p0"] w00Vr p0 by blast
  qed
  have setw: "\<And>w. w \<in> \<V> - {r} \<Longrightarrow> {fst (par_edge ?s' w), snd (par_edge ?s' w)} = {w, par_vx ?s' w}"
  proof -
    fix w assume w: "w \<in> \<V> - {r}"
    have "if par_up ?s' w then fst (par_edge ?s' w) = w else snd (par_edge ?s' w) = w"
    using de_v[OF w] by simp
    thus "{fst (par_edge ?s' w), snd (par_edge ?s' w)} = {w, par_vx ?s' w}"
    by (auto simp: par_vx_def split: if_splits)
  qed
  have edgechar: "abstract_arborescense ?T' = (\<lambda>w. {w, par_vx ?s' w}) ` (\<V> - {r})"
  proof -
    have "abstract_arborescense ?T' = (\<lambda>ee. {fst ee, snd ee}) ` (parent_lookup (parent_edge ?s') ` (\<V> - {r}))"
    using projeq by simp
    also have "... = (\<lambda>w. {fst (par_edge ?s' w), snd (par_edge ?s' w)}) ` (\<V> - {r})"
    by (simp add: image_image par_edge_def)
    also have "... = (\<lambda>w. {w, par_vx ?s' w}) ` (\<V> - {r})"
    using setw by (auto intro: image_cong)
    finally show ?thesis .
  qed
  have tree': "ns_invar_tree ?s'"
  unfolding ns_invar_tree_def
  proof (intro conjI)
    show "\<forall>v'\<in>\<V> - {r}. par_edge ?s' v' \<in> \<E> \<and> (if par_up ?s' v' then fst (par_edge ?s' v') = v' else snd (par_edge ?s' v') = v') \<and> (\<exists>q. distinct (v' # par_vx ?s' v' # q) \<and> walk_betw (abstract_arborescense (spanning_tree ?s')) v' (v' # par_vx ?s' v' # q) r)"
    proof (rule ballI)
      fix v' assume v'Vr: "v' \<in> \<V> - {r}"
      have w3: "\<exists>q. distinct (v' # par_vx ?s' v' # q) \<and> walk_betw (abstract_arborescense (spanning_tree ?s')) v' (v' # par_vx ?s' v' # q) r"
      using parwalk[OF arbT'inv edgechar v'Vr] unfolding pj_tree .
      show "par_edge ?s' v' \<in> \<E> \<and> (if par_up ?s' v' then fst (par_edge ?s' v') = v' else snd (par_edge ?s' v') = v') \<and> (\<exists>q. distinct (v' # par_vx ?s' v' # q) \<and> walk_betw (abstract_arborescense (spanning_tree ?s')) v' (v' # par_vx ?s' v' # q) r)"
      using de_v[OF v'Vr] w3 by simp
    qed
  next
    show "(\<lambda>e. {fst e, snd e}) ` ns_tree_edges ?s' = abstract_arborescense (spanning_tree ?s')"
    using projeq unfolding pj_tree .
  qed
  have selfloop': "ns_invar_selfloop ?s'"
    unfolding ns_invar_selfloop_def
  proof (intro ballI impI)
    fix ee assume eeE: "ee \<in> \<E>" and eesl: "fst ee = snd ee"
    have "flow_lookup ?f' ee = flow_lookup (current_flow s) ee"
      using augment_flow_selfloop[OF inv sel pp d0ge eeE eesl] .
    hence feq: "ns_flow_of ?s' ee = ns_flow_of s ee" by (simp add: flow_eq)
    thus "(0 \<le> \<c> ee \<longrightarrow> ns_flow_of ?s' ee = 0) \<and> (\<c> ee < 0 \<longrightarrow> ereal (ns_flow_of ?s' ee) = \<u> ee)"
      using ns_invarD(8)[OF inv] eeE eesl by (simp add: ns_invar_selfloop_def)
  qed
  show "ns_invar (ns_pivot_upd s)"
  unfolding pivoteq
  by (rule ns_invarI[OF impl' bflow' partition' flowfits' potfits' strict' tree' selfloop'])
  show "ns_less (ns_pivot_upd s) s"
  proof -
    have d0ge: "0 \<le> \<delta>" using bottleneck_delta_bounds(1)[OF inv sel pp bn dne] .
    have cunningham: "up_side \<Longrightarrow> 0 < \<delta>"
    proof -
      assume us: up_side
      have rv: "res_up s v = \<delta>" using geomU us by simp
      have "0 < res_up s v \<or> res_up s v = - 1" using res_up_pos[OF inv vVr] .
      thus "0 < \<delta>" using rv d0ge by auto
    qed
    have costeq: "ns_flow_cost ?s' = ns_flow_cost s + (if in_U then - h \<delta> else h \<delta>) * reduced_cost (potentials s) e"
      using augment_flow_props(3)[OF inv sel pp bn dne] by (simp add: ns_flow_cost_def pj_flow)
    have ent: "entering_edge (potentials s) (edge_state s) e in_U"
      using sel_select_SomeD(4)[OF precond selS] .
    have rcpos: "in_U \<Longrightarrow> reduced_cost (potentials s) e > 0" using ent by (simp add: entering_edge_def)
    have rcneg: "\<not> in_U \<Longrightarrow> reduced_cost (potentials s) e < 0" using ent by (simp add: entering_edge_def)
    have rc_eq: "rcost_abstract \<gamma> = reduced_cost (potentials s) e"
      using sel_select_SomeD(3)[OF precond selS] .
    have chg_lt: "0 < \<delta> \<Longrightarrow> (if in_U then - h \<delta> else h \<delta>) * reduced_cost (potentials s) e < 0"
      using rcpos rcneg by (cases in_U) (auto simp: mult_less_0_iff)
    have costlt: "0 < \<delta> \<Longrightarrow> ns_flow_cost ?s' < ns_flow_cost s" using costeq chg_lt by simp
    have costeq0: "\<delta> = 0 \<Longrightarrow> ns_flow_cost ?s' = ns_flow_cost s" using costeq by simp
    have potsumeq: "ns_pot_sum ?s' = ns_pot_sum s
          + (if in_U \<noteq> up_side then reduced_cost (potentials s) e else - reduced_cost (potentials s) e)
            * real (card {x. \<exists>p. walk_betw (abstract_arborescense (spanning_tree s)) x p r \<and> distinct p \<and> v \<in> set p})"
    proof -
      have "ns_pot_sum ?s' = sum (abstract_pot ?pi') \<V>"
        unfolding ns_pot_sum_def by (simp add: pj_pot)
      thus ?thesis using shift_pot_props(4)[OF inv sel pp bn dne] rc_eq by (simp add: ns_pot_sum_def)
    qed
    have vinS: "v \<in> {x. \<exists>p. walk_betw (abstract_arborescense (spanning_tree s)) x p r \<and> distinct p \<and> v \<in> set p}"
    proof -
      obtain q where q: "distinct (v # par_vx s v # q)
           \<and> walk_betw (abstract_arborescense (spanning_tree s)) v (v # par_vx s v # q) r"
        using par_vx_walk_succ[OF inv vVr] by blast
      show ?thesis using q by auto
    qed
    have Ssub: "{x. \<exists>p. walk_betw (abstract_arborescense (spanning_tree s)) x p r \<and> distinct p \<and> v \<in> set p} \<subseteq> \<V>"
    proof
      fix x assume "x \<in> {x. \<exists>p. walk_betw (abstract_arborescense (spanning_tree s)) x p r \<and> distinct p \<and> v \<in> set p}"
      then obtain p where "walk_betw (abstract_arborescense (spanning_tree s)) x p r" by auto
      hence "x \<in> Vs (abstract_arborescense (spanning_tree s))"
        by (metis hd_in_set subsetD walk_betw_def walk_in_Vs)
      thus "x \<in> \<V>" using general(4)[OF arb] by simp
    qed
    have cardS_pos: "0 < card {x. \<exists>p. walk_betw (abstract_arborescense (spanning_tree s)) x p r \<and> distinct p \<and> v \<in> set p}"
    proof -
      have "{x. \<exists>p. walk_betw (abstract_arborescense (spanning_tree s)) x p r \<and> distinct p \<and> v \<in> set p} \<noteq> {}"
      proof (rule notI)
        assume empt: "{x. \<exists>p. walk_betw (abstract_arborescense (spanning_tree s)) x p r \<and> distinct p \<and> v \<in> set p} = {}"
        from vinS empt show False by simp
      qed
      thus ?thesis using finite_subset[OF Ssub \<V>_finite] by (simp add: card_gt_0_iff)
    qed
    have potsum_gt: "\<delta> = 0 \<Longrightarrow> ns_pot_sum s < ns_pot_sum ?s'"
    proof -
      assume dz: "\<delta> = 0"
      have nus: "\<not> up_side" using cunningham dz by auto
      have dp_pos: "0 < (if in_U \<noteq> up_side then reduced_cost (potentials s) e else - reduced_cost (potentials s) e)"
        using rcpos rcneg nus by (cases in_U) auto
      have "0 < (if in_U \<noteq> up_side then reduced_cost (potentials s) e else - reduced_cost (potentials s) e)
                * real (card {x. \<exists>p. walk_betw (abstract_arborescense (spanning_tree s)) x p r \<and> distinct p \<and> v \<in> set p})"
        using dp_pos cardS_pos by simp
      thus "ns_pot_sum s < ns_pot_sum ?s'" using potsumeq by simp
    qed
    have chg_le: "(if in_U then - h \<delta> else h \<delta>) * reduced_cost (potentials s) e \<le> 0"
      using d0ge rcpos rcneg by (cases in_U) (auto simp: mult_le_0_iff)
    have costle: "ns_flow_cost ?s' \<le> ns_flow_cost s" using costeq chg_le by simp
    have rcne: "reduced_cost (potentials s) e \<noteq> 0" using rcpos rcneg by (cases in_U) auto
    have costeq_imp_dz: "ns_flow_cost ?s' = ns_flow_cost s \<Longrightarrow> \<delta> = 0"
    proof -
      assume "ns_flow_cost ?s' = ns_flow_cost s"
      hence "(if in_U then - h \<delta> else h \<delta>) * reduced_cost (potentials s) e = 0" using costeq by simp
      hence "(if in_U then - h \<delta> else h \<delta>) = 0" using rcne by simp
      thus "\<delta> = 0" by (simp split: if_splits)
    qed
    have stp_s: "spanning_tree_partition r (ns_tree_edges s) (ns_L_of s \<union> ns_selfloops_L) (ns_U_of s \<union> ns_selfloops_U)"
      using ns_invarD(3)[OF inv] by (simp add: ns_invar_partition_def)
    have ffit_s: "flow_fits_spanning_tree_partition (ns_tree_edges s) (ns_L_of s) (ns_U_of s) (ns_flow_of s)"
      using ns_invarD(4)[OF inv] by (simp add: ns_invar_flow_fits_def)
    have pfit_s: "potential_fits_spanning_tree_partition r (ns_tree_edges s) (ns_pot_of s)"
      using ns_invarD(5)[OF inv] by (simp add: ns_invar_pot_fits_def)
    have bflow_s: "(ns_flow_of s) is b flow" using ns_invar_bflowD[OF ns_invarD(2)[OF inv]] .
    have finPT: "\<And>x. finite (possible_trees x)" by (rule finite_possible_trees)
    have sub: "possible_trees ?s' \<subseteq> possible_trees s"
    proof
      fix z assume "z \<in> possible_trees ?s'"
      then obtain T L U f' \<pi>' where z: "z = (T, L, U)"
        and A1: "spanning_tree_partition r T L U"
        and A2: "flow_fits_spanning_tree_partition T L U f'"
        and A3: "potential_fits_spanning_tree_partition r T \<pi>'"
        and A4: "f' is b flow"
        and A56: "\<C> f' < ns_flow_cost ?s'
                  \<or> (\<C> f' = ns_flow_cost ?s' \<and> (\<Sum>v\<in>\<V>. \<pi>' v) \<ge> ns_pot_sum ?s')"
        unfolding possible_trees_def by blast
      have goal56: "\<C> f' < ns_flow_cost s \<or> (\<C> f' = ns_flow_cost s \<and> (\<Sum>v\<in>\<V>. \<pi>' v) \<ge> ns_pot_sum s)"
      proof (cases "\<C> f' < ns_flow_cost ?s'")
        case True
        have "\<C> f' < ns_flow_cost s" using True costle by simp
        thus ?thesis by simp
      next
        case False
        hence eq5: "\<C> f' = ns_flow_cost ?s'" and ge6: "(\<Sum>v\<in>\<V>. \<pi>' v) \<ge> ns_pot_sum ?s'" using A56 by auto
        show ?thesis
        proof (cases "ns_flow_cost ?s' = ns_flow_cost s")
          case cte: True
          have dz: "\<delta> = 0" using costeq_imp_dz cte by simp
          have "ns_pot_sum ?s' > ns_pot_sum s" using potsum_gt dz by simp
          hence "(\<Sum>v\<in>\<V>. \<pi>' v) \<ge> ns_pot_sum s" using ge6 by simp
          thus ?thesis using eq5 cte by simp
        next
          case False
          hence "ns_flow_cost ?s' < ns_flow_cost s" using costle by simp
          hence "\<C> f' < ns_flow_cost s" using eq5 by simp
          thus ?thesis by simp
        qed
      qed
      show "z \<in> possible_trees s"
        unfolding possible_trees_def using z A1 A2 A3 A4 goal56 by blast
    qed
    have slinv: "ns_invar_selfloop s" using ns_invarD(8)[OF inv] .
    have ffit_aug: "flow_fits_spanning_tree_partition (ns_tree_edges s)
         (ns_L_of s \<union> ns_selfloops_L) (ns_U_of s \<union> ns_selfloops_U) (ns_flow_of s)"
      using ffit_s slinv
      by (auto simp: flow_fits_spanning_tree_partition_def ns_selfloops_L_def ns_selfloops_U_def
                     ns_invar_selfloop_def)
    have old_in: "(ns_tree_edges s, ns_L_of s \<union> ns_selfloops_L, ns_U_of s \<union> ns_selfloops_U) \<in> possible_trees s"
      unfolding possible_trees_def using stp_s ffit_aug pfit_s bflow_s
      by (auto simp: ns_flow_cost_def ns_pot_sum_def)
    have old_notin: "(ns_tree_edges s, ns_L_of s \<union> ns_selfloops_L, ns_U_of s \<union> ns_selfloops_U) \<notin> possible_trees ?s'"
    proof
      assume "(ns_tree_edges s, ns_L_of s \<union> ns_selfloops_L, ns_U_of s \<union> ns_selfloops_U) \<in> possible_trees ?s'"
      then obtain T L U f' \<pi>' where teq: "(ns_tree_edges s, ns_L_of s \<union> ns_selfloops_L, ns_U_of s \<union> ns_selfloops_U) = (T, L, U)"
        and B2: "flow_fits_spanning_tree_partition T L U f'"
        and B3: "potential_fits_spanning_tree_partition r T \<pi>'"
        and B4: "f' is b flow"
        and B56: "\<C> f' < ns_flow_cost ?s'
                  \<or> (\<C> f' = ns_flow_cost ?s' \<and> (\<Sum>v\<in>\<V>. \<pi>' v) \<ge> ns_pot_sum ?s')"
        unfolding possible_trees_def by blast
      from teq have Te: "T = ns_tree_edges s" and Le: "L = ns_L_of s \<union> ns_selfloops_L" and Ue: "U = ns_U_of s \<union> ns_selfloops_U" by auto
      have unique: "\<And>a. a \<in> \<E> \<Longrightarrow> f' a = ns_flow_of s a"
        using spanning_flow_unique[OF B4 bflow_s stp_s B2[unfolded Te Le Ue] ffit_aug] by simp
      have "\<C> f' = \<C> (ns_flow_of s)"
        unfolding \<C>_def by (rule sum.cong[OF refl]) (simp add: unique)
      hence cf'eq: "\<C> f' = ns_flow_cost s" by (simp add: ns_flow_cost_def)
      have "\<C> f' \<le> ns_flow_cost ?s'" using B56 by auto
      hence "ns_flow_cost s \<le> ns_flow_cost ?s'" using cf'eq by simp
      hence cte: "ns_flow_cost ?s' = ns_flow_cost s" using costle by simp
      have dz: "\<delta> = 0" using costeq_imp_dz cte by simp
      have ge6: "(\<Sum>v\<in>\<V>. \<pi>' v) \<ge> ns_pot_sum ?s'" using B56 cf'eq cte by simp
      have piuniq: "\<And>u. u \<in> \<V> \<Longrightarrow> ns_pot_of s u = \<pi>' u"
        using spanning_potential_unqiue[OF stp_s pfit_s B3[unfolded Te]] .
      have "(\<Sum>v\<in>\<V>. \<pi>' v) = ns_pot_sum s"
        unfolding ns_pot_sum_def by (rule sum.cong[OF refl]) (simp add: piuniq)
      hence "ns_pot_sum s \<ge> ns_pot_sum ?s'" using ge6 by simp
      moreover have "ns_pot_sum ?s' > ns_pot_sum s" using potsum_gt dz by simp
      ultimately show False by simp
    qed
    have "possible_trees ?s' \<subset> possible_trees s" using sub old_in old_notin by blast
    hence "card (possible_trees ?s') < card (possible_trees s)"
      by (rule psubset_card_mono[OF finPT])
    thus "ns_less (ns_pivot_upd s) s" unfolding ns_less_def pivoteq by simp
  qed
qed

end
end