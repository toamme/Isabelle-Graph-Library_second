theory BFS_Instantiation
  imports BFS_Refinement Directed_Set_Graphs.CSR_Buildup_Simple
begin

section \<open>An Instantiation of the Imperative BFS\<close>

text \<open>The locale @{locale BFS_lists_instance} is instantiated with purely imperative data
      structures of fixed size, allocated once:

        \<^item> the visited set is a Boolean array over the vertices \<open>{..<n}\<close>,
        \<^item> distances and parents are arrays over the vertices,
        \<^item> the frontier is an array with a fill pointer and a buffer array of the same size, and
        \<^item> the graph is in compressed sparse row (CSR) form, built by
          @{theory Directed_Set_Graphs.CSR_Buildup_Simple}. The CSR holds the neighbours: an
          array of heads grouped by their tails, together with the first and last positions of the
          group of each vertex.\<close>


subsection \<open>The visited set as a Boolean array\<close>

definition bset_assn :: "nat set \<Rightarrow> nat set \<Rightarrow> bool array \<Rightarrow> assn" where
  "bset_assn U S a =
     (\<exists>\<^sub>A l. a \<mapsto>\<^sub>a l * \<up>((\<forall>u \<in> U. u < length l \<and> (l ! u \<longleftrightarrow> u \<in> S)) \<and> S \<subseteq> U))"

definition bset_empty :: "nat \<Rightarrow> bool array Heap" where
  "bset_empty n = Array.new n False"

definition bset_memb :: "nat \<Rightarrow> bool array \<Rightarrow> bool Heap" where
  "bset_memb v a = Array.nth a v"

definition bset_ins :: "nat \<Rightarrow> bool array \<Rightarrow> bool array Heap" where
  "bset_ins v a = Array.upd v True a"

lemma bset_only_in_univ: "bset_assn U S a = bset_assn U S a * \<up>(S \<subseteq> U)"
  unfolding bset_assn_def by (rule ent_iffI) sep_auto+

lemma bset_empty_rule: "U \<subseteq> {..<n} \<Longrightarrow> <emp> bset_empty n <bset_assn U {}>"
  unfolding bset_assn_def bset_empty_def by (sep_auto simp: subset_iff)

lemma bset_memb_rule:
  "<bset_assn U S a * \<up>(v \<in> U)> bset_memb v a <\<lambda>r. bset_assn U S a * \<up>(r \<longleftrightarrow> v \<in> S)>"
  unfolding bset_assn_def bset_memb_def by sep_auto

lemma bset_ins_rule:
  "<bset_assn U S a * \<up>(v \<in> U \<and> v \<notin> S)> bset_ins v a <bset_assn U (Set.insert v S)>"
  unfolding bset_assn_def bset_ins_def by (sep_auto simp: nth_list_update)

subsection \<open>The graph as a CSR of neighbours\<close>

text \<open>The graph handle is the triple of the array of neighbours and the arrays of the first and
      the last positions.\<close>

fun csr3_assn :: "(nat \<Rightarrow> nat list option) \<Rightarrow> nat array \<times> nat array \<times> nat array \<Rightarrow> assn" where
  "csr3_assn G (Ga, Si, Ei) = CSR_assn G Ga Si Ei"

fun bfs_nbs where
  "bfs_nbs (Ga, Si, Ei) = iterate_neighbourhood Ga Si Ei"

lemma bfs_nbs_rule:
  "(\<And> acc acci x vs. \<lbrakk>G v = Some vs; x \<in> set vs\<rbrakk> \<Longrightarrow>
       <acc_assn acc acci * F> fi v x acci <\<lambda> r. acc_assn (f v acc x) r * F>) \<Longrightarrow>
   <csr3_assn G Gi * acc_assn acc acci * F>
     bfs_nbs Gi v fi acci
   <\<lambda> r. csr3_assn G Gi * F * acc_assn (foldl (f v) acc (case G v of None \<Rightarrow> [] | Some vs \<Rightarrow> vs)) r>"
  by (cases Gi rule: prod_cases3) (simp add: iterate_neighbourhood_rule)

lemma BFS_subprocedures_lists_bset:
  "BFS_subprocedures_lists bset_assn bset_memb bset_ins bfs_nbs csr3_assn"
  by unfold_locales (rule bset_only_in_univ bset_memb_rule bset_ins_rule bfs_nbs_rule | assumption)+



section \<open>The Code\<close>

text \<open>The graph is given by the list of its edges \<open>(u, v)\<close>. The CSR of neighbours is built by
      @{const build_CSR} of \<open>CSR_Buildup_Simple\<close>: the heads are
      stored consecutively, grouped by their tails, together with the first and the last position
      of the neighbours of each vertex; a vertex without neighbours gets a first position larger
      than its last one.

      The global interpretations of the code locales only fix operations and have no
      assumptions.\<close>

global_interpretation bfs_sub_code: BFS_subprocedures_lists_code bset_memb bset_ins bfs_nbs
  defines bfs_inner_loop = bfs_sub_code.inner_loop
    and bfs_outer_loop = bfs_sub_code.outer_loop
    and bfs_src_to_cf = bfs_sub_code.imp_src_to_cf
    and bfs_cf_is_empty = bfs_sub_code.imp_cf_is_empty
    and bfs_set_srcs_visited = bfs_sub_code.set_srcs_visited
    and bfs_set_dists = bfs_sub_code.set_all_dists_in_front_imp
    and bfs_round = bfs_sub_code.next_frontier_current_parents_imp
  done

global_interpretation bfs_code: BFS_Imperative_spec bfs_src_to_cf bfs_set_srcs_visited
    "bfs_round Gi" bfs_cf_is_empty bset_memb bfs_set_dists Array.nth Array.nth
  for Gi :: "nat array \<times> nat array \<times> nat array"
  defines bfs_loop = bfs_code.BFS_par_imp
    and bfs_init = bfs_code.initial_state_imp
    and bfs_check_reachable = bfs_code.check_reachable
    and bfs_visited_dists_parents = bfs_code.visited_dists_parents_imp
    and bfs_path_rev = bfs_code.path_rev_imp
    and bfs_path = bfs_code.path_imp
  done

text \<open>Copying the sources into the first frontier array.\<close>

partial_function (heap) copy_prefix_imp :: "'a::heap array \<Rightarrow> 'a array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "copy_prefix_imp Sa Fa k i =
     (if i < k then do {
        x \<leftarrow> Array.nth Sa i;
        Array.upd i x Fa;
        copy_prefix_imp Sa Fa k (Suc i) }
      else return ())"

text \<open>The final program takes the number of vertices, the edge list and the array of distinct
      sources. It builds the CSR, allocates all other data structures and runs the BFS. The
      distance and the parent array are initialised with the identity. It returns the visited set,
      the distances and the parents.\<close>

definition bfs_csr_run :: "nat \<Rightarrow> (nat \<times> nat) list \<Rightarrow> nat array \<Rightarrow>
                            (bool array \<times> nat array \<times> nat array) Heap" where
  "bfs_csr_run n es Sa = do {
     Gi \<leftarrow> build_CSR es;
     k \<leftarrow> Array.len Sa;
     Fr \<leftarrow> Array.new (Suc n) 0;
     copy_prefix_imp Sa Fr k 0;
     Bf \<leftarrow> Array.new (Suc n) 0;
     Vi \<leftarrow> bset_empty n;
     Da \<leftarrow> Array.make n id;
     Pa \<leftarrow> Array.make n id;
     bfs_visited_dists_parents Gi Vi (Fr, k, Bf) Da Pa }"

declare copy_prefix_imp.simps[code] iterate_range_strict.simps[code] iterate_range.simps[code]
  fill_nha.simps[code] bfs_code.BFS_par_imp.simps[code] bfs_code.path_rev_imp.simps[code]

export_code bfs_csr_run bfs_path checking SML_imp



section \<open>Correctness\<close>

text \<open>The input: the number of vertices \<open>n\<close>, the edge list \<open>es\<close> with endpoints below \<open>n\<close>
      and the distinct list of sources \<open>ss\<close>, which are vertices of the graph.\<close>

lemma copy_prefix_imp_rule:
  "\<lbrakk>i \<le> length ss; length ss \<le> length fl; take i fl = take i ss\<rbrakk> \<Longrightarrow>
   <Sa \<mapsto>\<^sub>a ss * Fa \<mapsto>\<^sub>a fl> copy_prefix_imp Sa Fa (length ss) i
   <\<lambda>_. Sa \<mapsto>\<^sub>a ss * Fa \<mapsto>\<^sub>a (ss @ drop (length ss) fl)>"
proof(induction "length ss - i" arbitrary: i fl)
  case 0
  have i: "i = length ss"
    using 0 by simp
  have "ss @ drop (length ss) fl = fl"
    using 0(4) i append_take_drop_id[of "length ss" fl] by simp
  then show ?case
    using i by (subst copy_prefix_imp.simps) sep_auto
next
  case (Suc m)
  have i: "i < length ss"
    using Suc.hyps(2) by simp
  have m: "m = length ss - Suc i"
    using Suc.hyps(2) by simp
  have tk: "take (Suc i) (fl[i := ss ! i]) = take (Suc i) ss"
    using Suc.prems i by (simp add: take_Suc_conv_app_nth list_update_append)
  have dr: "drop (length ss) (fl[i := ss ! i]) = drop (length ss) fl"
    using i by (simp add: drop_update_cancel)
  show ?case
    using i Suc.prems(2)
    by (subst copy_prefix_imp.simps) (sep_auto heap: Suc.hyps(1)[OF m _ _ tk] simp: dr)
qed

locale bfs_csr =
  fixes n :: nat and es :: "(nat \<times> nat) list" and ss :: "nat list"
  assumes es_bound: "(u, v) \<in> set es \<Longrightarrow> u < n \<and> v < n"
    and ss_distinct: "distinct ss" and ss_nonempty: "ss \<noteq> []"
    and ss_in_graph: "set ss \<subseteq> dVs (set es)"
begin

text \<open>The graph described by the list of edges, and the set of sources.\<close>

definition \<E> :: "(nat \<times> nat) set" where
  "\<E> = set es"

definition \<S> :: "nat set" where
  "\<S> = set ss"

lemma Vs_build: "BFS_subprocedures_lists.Vs (build_nhlists es) = dVs \<E>"
proof-
  have key: "(\<exists>vs. build_nhlists es u = Some vs \<and> v \<in> set vs) \<longleftrightarrow> (u, v) \<in> set es" for u v
    by (auto simp: build_nhlists_def nbrs_def filter_empty_conv)
  show ?thesis
    unfolding BFS_subprocedures_lists.Vs_def[OF BFS_subprocedures_lists_bset] dVs_def \<E>_def
    by (simp add: key)
qed

lemma Vs_bound: "BFS_subprocedures_lists.Vs (build_nhlists es) \<subseteq> {..<n}"
  unfolding Vs_build dVs_def \<E>_def using es_bound by blast

interpretation inst: BFS_lists_instance where is_visited_set = bset_assn
  and visited_memb = bset_memb and distinct_ins = bset_ins and iterate_neighbourhood = bfs_nbs
  and graph_assn = csr3_assn and G = "build_nhlists es" and Gi = Gi and srcs = "rev ss" for Gi
  using BFS_subprocedures_lists_bset finite_subset[OF Vs_bound]
  by (auto intro!: BFS_lists_instance.intro BFS_lists_instance_axioms.intro)

lemma digraph_abs_build: "inst.Graph.digraph_abs (build_nhlists es) = \<E>"
proof-
  have nb: "set (case build_nhlists es u of None \<Rightarrow> [] | Some vs \<Rightarrow> vs) = set (nbrs es u)" for u
  proof(cases "nbrs es u = []")
    case True
    show ?thesis
      unfolding build_nhlists_def
      by (subst if_P[OF True], subst option.case(1), subst True) (rule refl)
  next
    case False
    show ?thesis
      unfolding build_nhlists_def
      by (subst if_not_P[OF False], subst option.case(2)) (rule refl)
  qed
  have key: "v \<in> set (case build_nhlists es u of None \<Rightarrow> [] | Some vs \<Rightarrow> vs) \<longleftrightarrow> (u, v) \<in> set es"
    for u v
  proof
    assume "v \<in> set (case build_nhlists es u of None \<Rightarrow> [] | Some vs \<Rightarrow> vs)"
    then obtain e where e: "e \<in> set es" "fst e = u" "v = snd e"
      unfolding nb nbrs_def set_map set_filter by blast
    show "(u, v) \<in> set es"
      using e(1) unfolding e(2)[symmetric] e(3) prod.collapse .
  next
    assume "(u, v) \<in> set es"
    then have "(u, v) \<in> {e \<in> set es. fst e = u}"
      unfolding mem_Collect_eq fst_conv by (rule conjI) (rule refl)
    then have "snd (u, v) \<in> snd ` {e \<in> set es. fst e = u}"
      by (rule imageI)
    then show "v \<in> set (case build_nhlists es u of None \<Rightarrow> [] | Some vs \<Rightarrow> vs)"
      unfolding nb nbrs_def set_map set_filter snd_conv .
  qed
  show ?thesis
    unfolding inst.Graph.digraph_abs_def inst.Graph.neighbourhood_def key \<E>_def
    by (rule set_eqI) (simp only: mem_Collect_eq case_prod_beta prod.collapse)
qed

lemma BFS_axiom: "inst.imp_bfs.BFS_axiom"
proof-
  have "{v. build_nhlists es v \<noteq> None} \<subseteq> fst ` set es"
    unfolding dom_def[symmetric] build_nhlists_dom nbrs_def map_is_Nil_conv filter_empty_conv
    by blast
  then have fin: "finite {v. build_nhlists es v \<noteq> None}"
    by (rule finite_subset) (rule finite_imageI[OF finite_set])
  have nbfin: "finite (neighbourhood (set es) u)" for u
    by (rule finite_subset[of _ "snd ` set es"]) (auto simp: neighbourhood_def)
  show ?thesis
    unfolding inst.imp_bfs.BFS_axiom_def digraph_abs_build \<E>_def inst.Graph.graph_inv_def
              inst.Graph.finite_graph_def inst.Graph.finite_vsets_def set_rev distinct_rev set_empty
    by (intro conjI allI impI TrueI finite_set fin nbfin ss_in_graph ss_nonempty ss_distinct)
qed

text \<open>The code constants are those of the instance.\<close>

lemma code_eqs:
  "inst.imp_bfs.visited_dists_parents_imp Gi = bfs_visited_dists_parents Gi"
  "inst.imp_bfs.path_imp = bfs_path"
  by (simp_all add: bfs_visited_dists_parents_def bfs_path_def bfs_src_to_cf_def
                    bfs_set_srcs_visited_def bfs_round_def bfs_cf_is_empty_def bfs_set_dists_def)

text \<open>The allocations of @{const bfs_csr_run} establish the precondition of the BFS on the
      instance.\<close>

lemma bfs_csr_run_rule:
  assumes Q: "\<And>Gi Vi S Da Pa.
     <bset_assn (BFS_subprocedures_lists.Vs (build_nhlists es)) (set []) Vi *
      inst.imp_src_assn (build_nhlists es) (rev ss) S *
      inst.imp_dist_assn (build_nhlists es) id Da * inst.imp_par_assn (build_nhlists es) id Pa *
      csr3_assn (build_nhlists es) Gi>
       bfs_visited_dists_parents Gi Vi S Da Pa <Q Gi>"
  shows "<Sa \<mapsto>\<^sub>a ss> bfs_csr_run n es Sa <\<lambda>r. (\<exists>\<^sub>A Gi. Q Gi r) * Sa \<mapsto>\<^sub>a ss * true>"
proof-
  let ?V = "BFS_subprocedures_lists.Vs (build_nhlists es)"
  let ?FL = "ss @ drop (length ss) (replicate (Suc n) (0::nat))"
  have cV: "card ?V \<le> n"
    using card_mono[OF finite_lessThan Vs_bound] by simp
  have cS: "length ss \<le> card ?V"
    using card_mono[OF finite_subset[OF Vs_bound finite_lessThan] ss_in_graph[folded \<E>_def, folded Vs_build]]
          distinct_card[OF ss_distinct] by simp
  have sV: "set ss \<subseteq> ?V"
    using ss_in_graph unfolding Vs_build \<E>_def .
  have lenF: "length ?FL = Suc n"
    using cV cS by simp
  have b: "card ?V < length ?FL" "card ?V < length (replicate (Suc n) (0::nat))"
          "length ss < length ?FL" "take (length ss) ?FL = ss"
    unfolding lenF length_replicate using cV cS by simp_all
  have ids: "\<forall>i \<in> ?V. i < length (map id [0..<n]) \<and> id i = map id [0..<n] ! i"
  proof
    fix i assume "i \<in> ?V"
    then have "i < n"
      by (rule lessThan_iff[THEN iffD1, OF subsetD[OF Vs_bound]])
    then show "i < length (map id [0..<n]) \<and> id i = map id [0..<n] ! i"
      unfolding list.map_id by simp
  qed
  have csr: "<emp> build_CSR es <csr3_assn (build_nhlists es)>"
    by (rule ht_cons_post[OF build_CSR_correct]) (sep_auto simp: CSR_assn_def)
  have main:
    "<bset_assn ?V {} Vi * (Fr \<mapsto>\<^sub>a ?FL * Bf \<mapsto>\<^sub>a replicate (Suc n) (0::nat)) *
      Da \<mapsto>\<^sub>a map id [0..<n] * Pa \<mapsto>\<^sub>a map id [0..<n] * csr3_assn (build_nhlists es) Gi * Sa \<mapsto>\<^sub>a ss>
       bfs_visited_dists_parents Gi Vi (Fr, length ss, Bf) Da Pa
     <\<lambda>r. (\<exists>\<^sub>A Gi. Q Gi r) * Sa \<mapsto>\<^sub>a ss * true>" for Gi Vi Fr Bf Da Pa
    by (rule ht_cons[OF _ _ ht_frame[OF Q[unfolded list.set(1)], where R = "Sa \<mapsto>\<^sub>a ss"]])
       (intro ent_star_mono ent_refl inst.imp_src_assn_intro[OF b sV]
              inst.imp_dist_assn_intro[OF ids] inst.imp_par_assn_intro[OF ids], sep_auto)
  show ?thesis
    unfolding bfs_csr_run_def
    using cV cS by (sep_auto heap: csr copy_prefix_imp_rule bset_empty_rule[OF Vs_bound] main)
qed

subsection \<open>The result of the BFS\<close>

text \<open>The arrays returned are correct if, for every vertex of the graph @{term \<E>}, the
      visited array says whether it is reachable from a source, the distance array holds its
      distance from the sources if it is reachable, and the parent array holds, for every reachable
      vertex that is not a source, a reachable vertex from which an edge leads to it and whose
      distance is one smaller.\<close>

definition bfs_arrays :: "bool list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool" where
  "bfs_arrays vs ds ps \<longleftrightarrow> (\<forall>x \<in> dVs \<E>.
     x < length vs \<and> x < length ds \<and> x < length ps \<and>
     (vs ! x \<longleftrightarrow> (\<exists>u \<in> \<S>. \<exists>q. vwalk_bet \<E> u q x)) \<and>
     (vs ! x \<longrightarrow> enat (ds ! x) = distance_set \<E> \<S> x) \<and>
     ((vs ! x \<and> x \<notin> \<S>) \<longrightarrow>
        vs ! (ps ! x) \<and> (ps ! x, x) \<in> \<E> \<and> distance_set \<E> \<S> x = distance_set \<E> \<S> (ps ! x) + 1))"

lemma bfs_arrays_intro:
  assumes V: "\<forall>u \<in> dVs \<E>. u < length l \<and> (l ! u \<longleftrightarrow> u \<in> set vis)"
    and D: "\<forall>i \<in> dVs \<E>. i < length dl \<and> d i = dl ! i"
    and P: "\<forall>i \<in> dVs \<E>. i < length pl \<and> p i = pl ! i"
    and c1: "\<forall>x. x \<in> set vis \<longleftrightarrow> (\<exists>u \<in> \<S>. \<exists>q. vwalk_bet \<E> u q x)"
    and c2: "\<forall>x \<in> set vis. enat (d x) = distance_set \<E> \<S> x"
    and c3: "\<forall>x \<in> set vis - \<S>. p x \<in> set vis \<and> (p x, x) \<in> \<E> \<and>
               distance_set \<E> \<S> x = distance_set \<E> \<S> (p x) + 1"
  shows "bfs_arrays l dl pl"
  unfolding bfs_arrays_def
proof
  fix x assume x: "x \<in> dVs \<E>"
  note lx = bspec[OF V x] and dx = bspec[OF D x] and px = bspec[OF P x]
  have xv: "x \<in> set vis" if "l ! x"
    using conjunct2[OF lx] that by (rule iffD1)
  have par: "l ! (pl ! x) \<and> (pl ! x, x) \<in> \<E> \<and> distance_set \<E> \<S> x = distance_set \<E> \<S> (pl ! x) + 1"
    if "l ! x" "x \<notin> \<S>"
  proof-
    have c: "p x \<in> set vis" "(p x, x) \<in> \<E>" "distance_set \<E> \<S> x = distance_set \<E> \<S> (p x) + 1"
      using bspec[OF c3 DiffI[OF xv[OF that(1)] that(2)]] by blast+
    show ?thesis
      unfolding conjunct2[OF px, symmetric] using c bspec[OF V dVsI(1)[OF c(2)]] by blast
  qed
  have "enat (dl ! x) = distance_set \<E> \<S> x" if "l ! x"
    unfolding conjunct2[OF dx, symmetric] by (rule bspec[OF c2 xv[OF that]])
  then show "x < length l \<and> x < length dl \<and> x < length pl \<and>
             (l ! x \<longleftrightarrow> (\<exists>u \<in> \<S>. \<exists>q. vwalk_bet \<E> u q x)) \<and>
             (l ! x \<longrightarrow> enat (dl ! x) = distance_set \<E> \<S> x) \<and>
             ((l ! x \<and> x \<notin> \<S>) \<longrightarrow>
                l ! (pl ! x) \<and> (pl ! x, x) \<in> \<E> \<and> distance_set \<E> \<S> x = distance_set \<E> \<S> (pl ! x) + 1)"
    using lx dx px c1 par by blast
qed

lemma arrays_ent:
  assumes "\<And>l dl pl. \<lbrakk>pv l; pd dl; pp pl\<rbrakk> \<Longrightarrow> res l dl pl"
  shows "F * (\<exists>\<^sub>A l. Vi \<mapsto>\<^sub>a l * \<up>(pv l)) * (\<exists>\<^sub>A dl. Da \<mapsto>\<^sub>a dl * \<up>(pd dl)) *
         (\<exists>\<^sub>A pl. Pa \<mapsto>\<^sub>a pl * \<up>(pp pl)) \<Longrightarrow>\<^sub>A
         \<exists>\<^sub>A vs ds ps. Vi \<mapsto>\<^sub>a vs * Da \<mapsto>\<^sub>a ds * Pa \<mapsto>\<^sub>a ps * \<up>(res vs ds ps) * true"
  using assms by sep_auto

lemma bfs_arrays_ent:
  assumes "\<forall>x. x \<in> set vis \<longleftrightarrow> (\<exists>u \<in> \<S>. \<exists>q. vwalk_bet \<E> u q x)"
    and "\<forall>x \<in> set vis. enat (d x) = distance_set \<E> \<S> x"
    and "\<forall>x \<in> set vis - \<S>. p x \<in> set vis \<and> (p x, x) \<in> \<E> \<and>
           distance_set \<E> \<S> x = distance_set \<E> \<S> (p x) + 1"
  shows "F * bset_assn (BFS_subprocedures_lists.Vs (build_nhlists es)) (set vis) Vi *
         inst.imp_dist_assn (build_nhlists es) d Da * inst.imp_par_assn (build_nhlists es) p Pa \<Longrightarrow>\<^sub>A
         \<exists>\<^sub>A vs ds ps. Vi \<mapsto>\<^sub>a vs * Da \<mapsto>\<^sub>a ds * Pa \<mapsto>\<^sub>a ps * \<up>(bfs_arrays vs ds ps) * true"
  unfolding bset_assn_def inst.imp_dist_assn_char inst.imp_par_assn_char Vs_build
  by (rule arrays_ent, rule bfs_arrays_intro[OF _ _ _ assms], erule conjunct1)

text \<open>The final correctness theorem: the program returns a visited, a distance and a parent
      array with these properties.\<close>

theorem bfs_csr_run_correct:
  "<Sa \<mapsto>\<^sub>a ss> bfs_csr_run n es Sa
   <\<lambda>(Vi, Da, Pa). \<exists>\<^sub>A vs ds ps. Vi \<mapsto>\<^sub>a vs * Da \<mapsto>\<^sub>a ds * Pa \<mapsto>\<^sub>a ps * \<up>(bfs_arrays vs ds ps) * true>"
proof (rule ht_cons[OF ent_refl _ bfs_csr_run_rule[OF inst.imp_bfs.visited_dists_parents_imp_correct[OF
         BFS_axiom, unfolded code_eqs digraph_abs_build set_rev, folded \<S>_def]]], goal_cases)
  case (1 r)
  obtain Vi Da Pa where r: "r = (Vi, Da, Pa)"
    by (cases r)
  show ?case
    unfolding r prod.case
    by (rule ent_true_drop(1), rule ent_true_drop(1), intro ent_ex_preI, unfold ent_pure_pre_iff,
        intro impI, elim conjE, rule ent_true_drop(2), rule bfs_arrays_ent)
qed

lemma run_then_path:
  assumes "<P> m <\<lambda>r. (\<exists>\<^sub>A g. (case r of (a, b, d) \<Rightarrow> X g a * DA b * PA d)) * F * true>"
    and "\<And>b d. <DA b * PA d * Ra \<mapsto>\<^sub>a r> m' b d <\<lambda>k. DA b * PA d * (\<exists>\<^sub>A ps. Ra \<mapsto>\<^sub>a ps * \<up>(q k ps))>"
    and "\<And>k ps. q k ps \<Longrightarrow> q' k ps"
  shows "<P * Ra \<mapsto>\<^sub>a r> do { (a, b, d) \<leftarrow> m; m' b d } <\<lambda>k. \<exists>\<^sub>A ps. Ra \<mapsto>\<^sub>a ps * \<up>(q' k ps) * true>"
  using assms(3) by (sep_auto heap: assms(1,2))

text \<open>Path reconstruction: after the BFS, @{const bfs_path} writes a shortest path from the
      sources to any reachable vertex @{term v}, reversed, into the first cells of an array with
      at least @{term n} cells and returns its length.\<close>

theorem bfs_csr_path_correct:
  assumes v: "\<exists>u \<in> \<S>. \<exists>q. vwalk_bet \<E> u q v" and r: "n \<le> length r"
  shows "<Sa \<mapsto>\<^sub>a ss * Ra \<mapsto>\<^sub>a r>
           do { (Vi, Da, Pa) \<leftarrow> bfs_csr_run n es Sa; bfs_path Da Pa Ra v }
         <\<lambda>k. \<exists>\<^sub>A ps. Ra \<mapsto>\<^sub>a ps * \<up>(length ps = length r \<and>
              (\<exists>u \<in> \<S>. vwalk_bet \<E> u (rev (take k ps)) v \<and> enat (k - 1) = distance_set \<E> \<S> v)) * true>"
proof-
  have vis: "v \<in> set (BFS_dist_state.visited (inst.imp_bfs.BFS_par_impl inst.imp_bfs.initial_par_state))"
    using v unfolding inst.imp_bfs.BFS_par_correct(1)[OF BFS_axiom refl] digraph_abs_build set_rev \<S>_def .
  have card: "card (dVs (inst.Graph.digraph_abs (build_nhlists es))) \<le> length r"
    using card_mono[OF finite_lessThan Vs_bound] r unfolding Vs_build digraph_abs_build by simp
  show ?thesis
    by (rule run_then_path[OF bfs_csr_run_rule[OF inst.imp_bfs.visited_dists_parents_imp_rule[unfolded code_eqs]]
                              inst.imp_bfs.path_imp_correct[OF BFS_axiom refl vis card, unfolded code_eqs
                                digraph_abs_build set_rev, folded \<S>_def]])
       (elim conjE, intro conjI)
qed

end

section \<open>Running the Code\<close>

text \<open>A test harness. \<open>bfs_prepare\<close> copies the source list into an array and runs the BFS.
      \<open>bfs_query\<close> asks the arrays for a vertex \<open>v\<close>: if it is visited, it returns its distance and
      writes its path, reversed, into the array \<open>Ra\<close> the caller provides, together with the path
      length; otherwise it returns @{const None}. The \<open>code\<close> antiquotation compiles both into the
      running ML session; applying a @{typ "'a Heap"} computation to \<open>()\<close> runs it.\<close>

definition bfs_prepare where
  "bfs_prepare n es sl = do {
     Sa \<leftarrow> Array.of_list sl;
     bfs_csr_run n es Sa }"

definition bfs_query where
  "bfs_query Vi Da Pa Ra v = do {
     b \<leftarrow> Array.nth Vi v;
     if b then do {
       d \<leftarrow> Array.nth Da v;
       k \<leftarrow> bfs_path Da Pa Ra v;
       return (Some (d, k)) }
     else return None }"

text \<open>A graph with the sources 0 and 5. A path is read from the first \<open>k\<close> entries of the path
      array and reversed, so it is printed from its source to the vertex. The path array is
      allocated once and reused for every query. Vertex 6 is unreachable: its query returns
      @{const None}.\<close>

ML_val \<open>
  let
    val nat = @{code nat_of_integer}
    val i = @{code integer_of_nat}
    val n = 7
    val es = [(0, 1), (0, 2), (1, 2), (2, 3), (1, 3), (5, 4), (4, 3), (3, 4), (6, 0)]
    val (vi, (da, pa)) =
      @{code bfs_prepare} (nat n) (map (fn (u, v) => (nat u, nat v)) es) (map nat [0, 5]) ()
    val ra = Array.array (n, nat 0)
    fun query v =
      (case @{code bfs_query} vi da pa ra (nat v) () of
         NONE => (v, NONE)
       | SOME (d, k) => (v, SOME (i d, rev (List.tabulate (i k, fn j => i (Array.sub (ra, j)))))))
  in
    map query [0, 1, 2, 3, 4, 5, 6]
  end
\<close>

end
