theory Rooted_Arborescense
  imports Rooted_Arborescense_Defs
begin

lemma rooted_arborescense_swap_parents:
  assumes "rooted_arborescense_invar r V T"
          "Some pu = T u"
          "u \<notin> set (follow T v)"
          "v \<in> V"
        shows "rooted_arborescense_invar r V (T(u \<mapsto> v))"
              "{(y, x) |x y. (Some x = (T(u \<mapsto> v)) y)} = {(y, x) |x y. (Some x = T y)} - {(u, pu)} \<union> {(u, v)}"
proof -
  have Tu: "T u = Some pu" using assms(2) by simp
  have inv: "parent_spec T" "r \<in> V" "dom T = V - {r}" "dVs {(y, x) |x y. Some x = T y} = V"
    using assms(1) unfolding rooted_arborescense_invar_def by auto+
  have dom_eq: "dom (T(u \<mapsto> v)) = V - {r}"
    using inv(3) Tu by auto
  have u_in_V: "u \<in> V" using inv(3) Tu by auto
  have mem_E: "(u, pu) \<in> {(y, x) |x y. Some x = T y}" using Tu by auto
  have E_rw: "{(y, x) |x y. Some x = (T(u \<mapsto> v)) y} =
              {(y, x) |x y. Some x = T y} - {(u, pu)} \<union> {(u, v)}"
    apply (auto simp: Tu fun_upd_def split: if_splits) 
    by (metis Tu option.inject)
  have wfR: "wf {(x, y) |x y. Some x = T y}"
    using inv(1) unfolding parent_spec_def by auto
  have fdom: "\<And> w. parent_spec_i.follow_dom T w"
    apply (rule parent_spec_i.wf_follow_rel)
    using wfR by (auto simp: parent_spec_i.follow_rel.simps eq_commute)
  have follow_hd: "\<And> w. w \<in> set (follow T w)"
    proof -
      fix w show "w \<in> set (follow T w)"
        using parent_spec_i.follow.psimps[OF fdom[of w]]
        by (cases "T w") auto
    qed
  have not_ancestor: "(u, v) \<notin> {(x, y) |x y. Some x = T y}^*"
    proof (rule notI)
      assume h: "(u, v) \<in> {(x, y) |x y. Some x = T y}^*"
      have "u \<in> set (follow T v)"
      proof (rule rtrancl_induct[OF h])
        show "u \<in> set (follow T u)" using follow_hd by auto
      next
        fix y z
        assume yz: "(y, z) \<in> {(x, y) |x y. Some x = T y}"
        assume "u \<in> set (follow T y)"
        from yz obtain "T z = Some y" by auto
        then have "follow T z = z # follow T y"
          using parent_spec_i.follow.psimps[OF fdom[of z]] by simp
        with \<open>u \<in> set (follow T y)\<close> show "u \<in> set (follow T z)" by auto
      qed
      with assms(3) show False by auto
    qed
  have E'_spec_eq: "{(x, y) |x y. Some x = (T(u \<mapsto> v)) y} =
                    insert (v, u) ({(x, y) |x y. Some x = T y} - {(pu, u)})"
    using Tu by auto
  have wf_new: "parent_spec (T(u \<mapsto> v))"
    proof -
      have sub: "(u, v) \<notin> ({(x, y) |x y. Some x = T y} - {(pu, u)})^*"
        using not_ancestor by (meson Diff_subset rtrancl_mono subsetD)
      have wf_sub: "wf ({(x, y) |x y. Some x = T y} - {(pu, u)})"
        using wfR by (rule wf_subset) blast
      show ?thesis
        unfolding parent_spec_def E'_spec_eq wf_insert
        using wf_sub sub by auto
    qed
  have pu_ne_u: "pu \<noteq> u"
    proof
      assume "pu = u"
      then have self: "(u, u) \<in> {(x, y) |x y. Some x = T y}" using Tu by auto
      then show False using asymD[OF wf_imp_asym[OF wfR] self] by auto
    qed
  have v'_in_V: "\<And> x x'. T x = Some x' \<Longrightarrow> x' \<in> V"
    proof -
      fix x x' assume Tx: "T x = Some x'"
      have "(x, x') \<in> {(y, z) |y z. Some z = T y}" using Tx by auto
      hence "x' \<in> dVs {(y, z) |y z. Some z = T y}"
        unfolding dVs_def by auto
      moreover have "{(y, z) |y z. Some z = T y} = {(y, x) |x y. Some x = T y}" by auto
      ultimately show "x' \<in> V" using inv(4) by auto
    qed
  have path_lemma: "\<And> w. w \<in> V \<Longrightarrow> w \<noteq> r \<Longrightarrow> \<exists> y \<in> set (follow T w). T y = Some r"
    proof -
      fix w
      show "w \<in> V \<Longrightarrow> w \<noteq> r \<Longrightarrow> \<exists> y \<in> set (follow T w). T y = Some r"
      proof (induction w rule: wf_induct_rule[OF wfR])
        case (1 x)
        then have "x \<in> dom T" using inv(3) by auto
        then obtain x' where Tx: "T x = Some x'" by auto
        have follow_x: "follow T x = x # follow T x'"
          using parent_spec_i.follow.psimps[OF fdom[of x]] Tx by simp
        have x'_in_V: "x' \<in> V" using v'_in_V Tx by auto
        show ?case
        proof (cases "x' = r")
          case True thus ?thesis using follow_x Tx by fastforce
        next
          case False
          have step: "(x', x) \<in> {(x, y) |x y. Some x = T y}" using Tx by auto
          from "1.IH"[OF step x'_in_V False]
          obtain y where "y \<in> set (follow T x')" "T y = Some r" by auto
          thus ?thesis using follow_x by auto
        qed
      qed
    qed
  have dVs_split: "{u, pu} \<union> dVs ({(y, x) |x y. Some x = T y} - {(u, pu)}) = V"
    proof -
      have ins: "{(y, x) |x y. Some x = T y} =
                 insert (u, pu) ({(y, x) |x y. Some x = T y} - {(u, pu)})"
        using mem_E by auto
      have "dVs {(y, x) |x y. Some x = T y} =
            {u, pu} \<union> dVs ({(y, x) |x y. Some x = T y} - {(u, pu)})"
        by (metis ins insert_edge_dVs)
      then show ?thesis using inv(4) by (simp add: insert_commute)
    qed
  have pu_in: "pu \<in> dVs ({(y, x) |x y. Some x = T y} - {(u, pu)}) \<union> {u, v}"
    proof (cases "pu = v")
      case True thus ?thesis by auto
    next
      case ne_v: False
      show ?thesis
      proof (cases "pu = r")
        case False
        then have "pu \<in> dom T"
          using dVs_split inv(3)
          by auto
        then obtain pu' where Tpu: "T pu = Some pu'" by auto
        have "(pu, pu') \<in> {(y, x) |x y. Some x = T y} - {(u, pu)}"
          using Tpu pu_ne_u by auto
        then show ?thesis unfolding dVs_def by auto
      next
        case True
        then have "v \<noteq> r" using ne_v by auto
        from path_lemma[OF assms(4) this]
        obtain y where "y \<in> set (follow T v)" "T y = Some r" by auto
        then have "y \<noteq> u" using assms(3) by auto
        then have "(y, r) \<in> {(y, x) |x y. Some x = T y} - {(u, pu)}"
          using \<open>T y = Some r\<close> True by auto
        then have "r \<in> dVs ({(y, x) |x y. Some x = T y} - {(u, pu)})"
          unfolding dVs_def by auto
        thus ?thesis using True by auto
      qed
    qed
  have dVs_new: "dVs {(y, x) |x y. Some x = (T(u \<mapsto> v)) y} = V"
    proof -
      have rw: "dVs {(y, x) |x y. Some x = (T(u \<mapsto> v)) y} =
                dVs ({(y, x) |x y. Some x = T y} - {(u, pu)}) \<union> {u, v}"
        apply (auto simp add: E_rw dVs_union_distr insert_edge_dVs dVs_def)
        by (metis Tu insertCI option.inject)
      show ?thesis
      proof
        show "dVs {(y, x) |x y. Some x = (T(u \<mapsto> v)) y} \<subseteq> V"
          using rw dVs_split u_in_V assms(4)
          by (auto simp: dVs_def) 
        show "V \<subseteq> dVs {(y, x) |x y. Some x = (T(u \<mapsto> v)) y}"
          using rw dVs_split pu_in by auto
      qed
    qed
  show "rooted_arborescense_invar r V (T(u \<mapsto> v))"
    unfolding rooted_arborescense_invar_def
    using wf_new inv(2) dom_eq dVs_new by auto
  show "{(y, x) |x y. Some x = (T(u \<mapsto> v)) y} = {(y, x) |x y. Some x = T y} - {(u, pu)} \<union> {(u, v)}"
    using E_rw by auto
qed

subsection \<open>Threaded tree with subtree sizes (the @{text last}/@{text size} representation)\<close>

text \<open>
  We replace the @{text fst_out} field of the old @{text thread_invar} by two fields:
  \<^item> @{text lst}: for each vertex, the \<^emph>\<open>rightmost descendant\<close> of its subtree in the thread
    (the last node of its contiguous block).  The old @{text fst_out} is now \<^emph>\<open>derived\<close>:
    @{text "fst_out v = nxt (lst v)"}.
  \<^item> @{text sz}: the size (node count) of each subtree.

  @{text lst} is what makes the thread surgery local (only branches, not whole subtrees,
  change), and @{text sz} lets us find the common ancestor by climbing the smaller subtree,
  with no @{text depth} field.
\<close>



subsection \<open>The edge swap (remove one tree edge, insert another, reversing a path)\<close>

text \<open>
  A network-simplex pivot inserts the edge @{term "(i, j)"} and removes the tree edge
  @{term "(p, the (prnt S p))"}.  Here @{term i} (LEMON's @{text u_in}) is the endpoint of the
  entering arc inside the detached subtree, @{term j} (@{text v_in}) is its new parent, @{term p}
  (@{text u_out}) is the top of the detached subtree (lower endpoint of the leaving arc), and
  @{term jn} (@{text join}) is the apex of the pivot cycle.  Rooted-wise this \<^emph>\<open>reverses the
  parent pointers along the path @{term i} {\isasymdots} @{term p}\<close> and re-attaches @{term i} below
  @{term j}.

  The thread surgery below is a direct port of LEMON's \<open>updateTreeStructure\<close>: every step is
  a constant-time pointer update on @{const thrd}/@{const rvth}/@{const prnt}/@{const lsuc}/
  @{const snum}.  A parent chain is walked \<^emph>\<open>only\<close> in the join computation.
\<close>

paragraph \<open>Path computation --- the only place a parent chain is walked.\<close>

text \<open>Executable root-path (ancestor list) \<open>[v, the (T v), ..., r]\<close>, the code-level counterpart
      of @{term "follow T v"}.  This is the one parent-chain walk allowed in the functions; it is
      tail-recursive (the chain length is not structurally bounded).\<close>
partial_function (tailrec) anc_list :: "('a \<rightharpoonup> 'a) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "anc_list T v acc = (case T v of None \<Rightarrow> rev (v # acc) | Some w \<Rightarrow> anc_list T w (v # acc))"

declare anc_list.simps[code]

definition ancestors :: "('a \<rightharpoonup> 'a) \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "ancestors T v = anc_list T v []"

text \<open>The executable ancestor walk @{const anc_list} / @{const ancestors} computes exactly the
      logical root-path @{const follow}.  This is the bridge that lets the geometry of the pivot
      (stated with @{const follow}) be discharged for the code-level  join\_of.\<close>

lemma anc_list_acc:
  assumes "parent_spec T"
  shows "anc_list T v acc = rev acc @ follow T v"
proof -
  have fdom: "\<And> w. parent_spec_i.follow_dom T w"
    apply (rule parent_spec_i.wf_follow_rel)
    using assms[unfolded parent_spec_def] by (auto simp: parent_spec_i.follow_rel.simps eq_commute)
  show ?thesis
    apply (induction arbitrary: acc rule: parent_spec_i.follow.pinduct[OF fdom[of v]])
    apply (subst anc_list.simps)
    by (auto simp add: parent_spec_i.follow.psimps[OF fdom] split: option.split)
qed

lemma ancestors_eq_follow:
  assumes "parent_spec T"
  shows "ancestors T v = follow T v"
  using anc_list_acc[OF assms, of v "[]"] by (simp add: ancestors_def)

text \<open>Reusable @{const follow} facts under @{const parent_spec} (the global interpretation makes
      @{term "follow_dom"} conditional on well-foundedness).\<close>
lemma follow_dom_ps: "parent_spec T \<Longrightarrow> parent_spec_i.follow_dom T w"
  apply (rule parent_spec_i.wf_follow_rel)
  by (auto simp: parent_spec_def parent_spec_i.follow_rel.simps eq_commute)

lemma follow_ps_simps:
  assumes "parent_spec T"
  shows "follow T v = (case T v of None \<Rightarrow> [v] | Some w \<Rightarrow> v # follow T w)"
  using parent_spec_i.follow.psimps[OF follow_dom_ps[OF assms]] by simp

lemma follow_ne_ps:
  assumes "parent_spec T" shows "follow T v \<noteq> []"
  by (subst follow_ps_simps[OF assms]) (simp split: option.splits)

lemma follow_distinct_ps:
  assumes ps: "parent_spec T" shows "distinct (follow T v)"
proof -
  interpret par_T: parent T "\<lambda>_ _. True" using ps by unfold_locales
  show ?thesis by (simp add: follow_def par_T.follow_distinct)
qed

lemma follow_hd_ps:
  assumes ps: "parent_spec T" shows "hd (follow T v) = v"
proof -
  interpret par_T: parent T "\<lambda>_ _. True" using ps by unfold_locales
  show ?thesis by (simp add: follow_def par_T.follow_hd)
qed

lemma follow_append_ps:
  assumes ps: "parent_spec T" and "follow T v = p @ u # p'" shows "follow T u = u # p'"
proof -
  interpret par_T: parent T "\<lambda>_ _. True" using ps by unfold_locales
  show ?thesis using assms(2) by (simp add: follow_def par_T.follow_append)
qed

text \<open>Two parent maps that agree on every node of one's root-path have the same root-path (the walk
      only ever reads pointers along that path).  Used to show the pivot leaves untouched-branch
      root-paths unchanged.\<close>
lemma follow_eq_on:
  assumes psT: "parent_spec T" and psT': "parent_spec T'"
  shows "(\<forall>y\<in>set (follow T v). T y = T' y) \<longrightarrow> follow T v = follow T' v"
proof (induction rule: parent_spec_i.follow.pinduct[OF follow_dom_ps[OF psT, of v]])
  case (1 v)
  show ?case
  proof
    assume agree: "\<forall>y\<in>set (follow T v). T y = T' y"
    have hd: "v \<in> set (follow T v)" using follow_hd_ps[OF psT, of v] follow_ne_ps[OF psT, of v] by (metis hd_in_set)
    show "follow T v = follow T' v"
    proof (cases "T v")
      case None
      hence "T' v = None" using agree hd by auto
      have "follow T v = [v]" using None by (subst follow_ps_simps[OF psT]) simp
      moreover have "follow T' v = [v]" using \<open>T' v = None\<close> by (subst follow_ps_simps[OF psT']) simp
      ultimately show ?thesis by simp
    next
      case (Some w)
      hence Tw': "T' v = Some w" using agree hd by auto
      have fTv: "follow T v = v # follow T w" using Some by (subst follow_ps_simps[OF psT]) simp
      have fT'v: "follow T' v = v # follow T' w" using Tw' by (subst follow_ps_simps[OF psT']) simp
      have aw: "\<forall>y\<in>set (follow T w). T y = T' y" using agree fTv by simp
      have "follow T w = follow T' w" using 1(2)[OF Some] aw by (rule mp)
      thus ?thesis using fTv fT'v by simp
    qed
  qed
qed

lemma takeWhile_holds: "x \<in> set (takeWhile P xs) \<Longrightarrow> P x"
  by (induction xs) (auto split: if_splits)

text \<open>Consecutive nodes of a root-path are parent-linked: in @{term "follow T v"} every node's
      successor is its parent.  This turns the root-path list into an explicit parent chain
     (s 0, s 1, {\isasymdots}) (the path @{text P} the stem induction ranges over).\<close>
lemma follow_nth_Suc:
  assumes ps: "parent_spec T" and lt: "Suc t < length (follow T v)"
  shows "T (follow T v ! t) = Some (follow T v ! Suc t)"
proof -
  define x where "x = follow T v ! t"
  have td: "follow T v = take t (follow T v) @ x # drop (Suc t) (follow T v)"
    using lt by (metis Suc_lessD id_take_nth_drop x_def)
  have fx: "follow T x = x # drop (Suc t) (follow T v)"
    using follow_append_ps[OF ps] td by metis
  have dne: "drop (Suc t) (follow T v) \<noteq> []" using lt by simp
  define y where "y = follow T v ! Suc t"
  have hd_y: "hd (drop (Suc t) (follow T v)) = y" using lt y_def by (simp add: hd_drop_conv_nth)
  have dy: "drop (Suc t) (follow T v) = y # tl (drop (Suc t) (follow T v))"
    using dne hd_y by (metis hd_Cons_tl)
  have fx2: "follow T x = x # y # tl (drop (Suc t) (follow T v))" using fx dy by simp
  show ?thesis
  proof (cases "T x")
    case None
    then have "follow T x = [x]" by (subst follow_ps_simps[OF ps]) simp
    then show ?thesis using fx2 by simp
  next
    case (Some w)
    then have "follow T x = x # follow T w" by (subst follow_ps_simps[OF ps]) simp
    hence "follow T w = y # tl (drop (Suc t) (follow T v))" using fx2 by simp
    hence "hd (follow T w) = y" by simp
    hence "w = y" using follow_hd_ps[OF ps] by simp
    then show ?thesis using Some x_def y_def by simp
  qed
qed

text \<open>Converse of @{thm follow_nth_Suc} (the {\isasymsection}15.2 "out-edge" engine): a @{const parent_spec}
      function that chains through a list (consecutive links) and is @{term None} at the last node
      realises that list as @{const follow} from its head.  Used to pin the final thread to its
      explicit preorder list.\<close>
lemma follow_eq_of_chain:
  assumes ps: "parent_spec T"
      and ne: "xs \<noteq> []"
      and link: "\<And>i. Suc i < length xs \<Longrightarrow> T (xs ! i) = Some (xs ! Suc i)"
      and lastN: "T (last xs) = None"
  shows "follow T (hd xs) = xs"
  using ne link lastN
proof (induction xs)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases "xs = []")
    case True
    hence "T x = None" using Cons.prems(3) by simp
    thus ?thesis using True by (subst follow_ps_simps[OF ps]) simp
  next
    case False
    have len2: "Suc 0 < length (x # xs)" using False by (cases xs) auto
    have Tx: "T x = Some (hd xs)"
      using Cons.prems(2)[OF len2] False by (simp add: hd_conv_nth)
    have link': "\<And>i. Suc i < length xs \<Longrightarrow> T (xs ! i) = Some (xs ! Suc i)"
    proof -
      fix i assume "Suc i < length xs"
      hence "Suc (Suc i) < length (x # xs)" by simp
      from Cons.prems(2)[OF this] show "T (xs ! i) = Some (xs ! Suc i)" by simp
    qed
    have last': "T (last xs) = None" using Cons.prems(3) False by simp
    have "follow T (hd xs) = xs" using Cons.IH[OF False link' last'] by auto
    thus ?thesis using Tx False by (subst follow_ps_simps[OF ps]) simp
  qed
qed

text \<open>Clause @{text B} engine: a map whose every edge is a forward step in a \<^emph>\<open>distinct\<close> list is a
      @{const parent_spec} (acyclic), because the list position strictly decreases along the reverse
      relation.  Combined with @{thm follow_eq_of_chain} this turns "the final thread realises the
      preorder list" into both @{const parent_spec} (B) and the @{const follow}-value (D/E).\<close>
lemma parent_spec_of_distinct_chain:
  assumes dist: "distinct xs"
      and link: "\<And>x y. T x = Some y \<Longrightarrow> \<exists>i. Suc i < length xs \<and> xs ! i = x \<and> xs ! Suc i = y"
  shows "parent_spec T"
proof -
  define pos where "pos = (\<lambda>z. THE n. n < length xs \<and> xs ! n = z)"
  have posid: "\<And>n. n < length xs \<Longrightarrow> pos (xs ! n) = n"
  proof -
    fix n assume n: "n < length xs"
    show "pos (xs ! n) = n" unfolding pos_def
    proof (rule the_equality)
      show "n < length xs \<and> xs ! n = xs ! n" using n by simp
    next
      fix m assume "m < length xs \<and> xs ! m = xs ! n"
      thus "m = n" using n dist by (metis nth_eq_iff_index_eq)
    qed
  qed
  have "{(x, y) |x y. Some x = T y} \<subseteq> measure (\<lambda>z. length xs - pos z)"
  proof
    fix e assume "e \<in> {(x, y) |x y. Some x = T y}"
    then obtain x y where e: "e = (x,y)" and Ty: "T y = Some x" by auto
    from link[OF Ty] obtain i where i: "Suc i < length xs" "xs ! i = y" "xs ! Suc i = x" by auto
    have "length xs - pos x < length xs - pos y" using i posid[of i] posid[of "Suc i"] by auto
    thus "e \<in> measure (\<lambda>z. length xs - pos z)" using e by simp
  qed
  thus ?thesis unfolding parent_spec_def by (rule wf_subset[OF wf_measure])
qed

text \<open>@{text P}/@{text D1} (the path the stem induction ranges over): if @{term p} lies on
      @{term i}'s root-path then there is an explicit injective parent chain
      (s 0 = i, {\isasymdots}, s k = p) whose nodes are exactly the prefix of @{term "follow T i"}
      up to @{term p}.\<close>
lemma follow_path:
  assumes ps: "parent_spec T" and pin: "p \<in> set (follow T i)"
  obtains s k where "s 0 = i" "s k = p"
    and "\<And>t. t < k \<Longrightarrow> T (s t) = Some (s (Suc t))"
    and "inj_on s {..k}"
    and "\<And>t. t \<le> k \<Longrightarrow> s t \<in> set (follow T i)"
proof -
  define L where "L = follow T i"
  have distL: "distinct L" unfolding L_def by (rule follow_distinct_ps[OF ps])
  have Lne: "L \<noteq> []" unfolding L_def by (rule follow_ne_ps[OF ps])
  define pref where "pref = takeWhile (\<lambda>x. x \<noteq> p) L @ [p]"
  have dw: "dropWhile (\<lambda>x. x \<noteq> p) L \<noteq> []"
    using pin unfolding L_def by (auto simp: dropWhile_eq_Nil_conv)
  have hddw: "hd (dropWhile (\<lambda>x. x \<noteq> p) L) = p" using hd_dropWhile[OF dw] by simp
  have Lsplit: "L = pref @ tl (dropWhile (\<lambda>x. x \<noteq> p) L)"
  proof -
    have "L = takeWhile (\<lambda>x. x \<noteq> p) L @ dropWhile (\<lambda>x. x \<noteq> p) L" by simp
    also have "dropWhile (\<lambda>x. x \<noteq> p) L = p # tl (dropWhile (\<lambda>x. x \<noteq> p) L)"
      using dw hddw by (metis hd_Cons_tl)
    finally show ?thesis unfolding pref_def by simp
  qed
  have prefne: "pref \<noteq> []" by (simp add: pref_def)
  have distpref: "distinct pref" using distL Lsplit by (metis distinct_append)
  have hdL: "hd L = i" unfolding L_def by (rule follow_hd_ps[OF ps])
  have hdpref: "hd pref = i" using Lsplit prefne hdL by (metis hd_append)
  have lastpref: "last pref = p" by (simp add: pref_def)
  have nthpref: "\<And>t. t < length pref \<Longrightarrow> L ! t = pref ! t"
    by (subst Lsplit) (simp add: nth_append)
  define s where "s = (\<lambda>t. pref ! t)"
  define k where "k = length pref - 1"
  have klen: "Suc k = length pref" using prefne k_def by (cases pref) auto
  have s0: "s 0 = i" using hdpref prefne by (simp add: s_def hd_conv_nth)
  have sk: "s k = p" using lastpref prefne by (simp add: s_def k_def last_conv_nth)
  have mem: "\<And>t. t \<le> k \<Longrightarrow> s t \<in> set (follow T i)"
  proof -
    fix t assume "t \<le> k"
    hence "t < length pref" using klen by simp
    hence "s t \<in> set pref" by (simp add: s_def)
    thus "s t \<in> set (follow T i)" using Lsplit L_def by (metis Un_iff set_append)
  qed
  obtain rest where Lr: "L = pref @ rest" using Lsplit by auto
  have lp: "length pref \<le> length L" using Lr by simp
  have step: "\<And>t. t < k \<Longrightarrow> T (s t) = Some (s (Suc t))"
  proof -
    fix t assume tk: "t < k"
    have st: "Suc t < length pref" using tk klen by simp
    have t1: "t < length pref" using st by simp
    have "Suc t < length L" using st lp by simp
    hence "Suc t < length (follow T i)" using L_def by simp
    hence "T (follow T i ! t) = Some (follow T i ! Suc t)" by (rule follow_nth_Suc[OF ps])
    hence "T (L ! t) = Some (L ! Suc t)" using L_def by simp
    thus "T (s t) = Some (s (Suc t))" using nthpref[OF t1] nthpref[OF st] by (simp add: s_def)
  qed
  have inj: "inj_on s {..k}"
  proof (rule inj_onI)
    fix a b assume "a \<in> {..k}" "b \<in> {..k}" "s a = s b"
    hence al: "a < length pref" and bl: "b < length pref" using klen by auto
    show "a = b" using \<open>s a = s b\<close> al bl distpref by (simp add: s_def nth_eq_iff_index_eq)
  qed
  show thesis by (rule that[OF s0 sk step inj mem])
qed

text \<open>The join (apex / lowest common ancestor) of @{term a} and @{term b}: the first node on
      @{term a}'s root-path that also lies on @{term b}'s root-path.\<close>
definition join_of :: "('a \<rightharpoonup> 'a) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "join_of T a b = hd (filter (\<lambda>x. x \<in> set (ancestors T b)) (ancestors T a))"

text \<open>Rephrase @{const join_of} via @{const follow} (the logical root-path) using
      @{thm ancestors_eq_follow}.\<close>
lemma join_of_follow:
  assumes "parent_spec T"
  shows "join_of T a b = hd (filter (\<lambda>x. x \<in> set (follow T b)) (follow T a))"
  by (simp add: join_of_def ancestors_eq_follow[OF assms])

text \<open>The join lies on both root-paths.  The hypothesis @{term "last (follow T a) = last (follow T b)"}
      says @{term a} and @{term b} reach the same root (so the filtered list is non-empty); in the
      pivot it holds because both endpoints are in @{term V} and @{term "dom T = V - {r}"}.\<close>
lemma join_of_mem:
  assumes "parent_spec T" "last (follow T a) = last (follow T b)"
  shows "join_of T a b \<in> set (follow T a)"
    and "join_of T a b \<in> set (follow T b)"
proof -
  let ?P = "\<lambda>x. x \<in> set (follow T b)"
  have ne: "follow T a \<noteq> []" "follow T b \<noteq> []" using follow_ne_ps[OF assms(1)] by auto
  have wit: "last (follow T a) \<in> set (follow T a) \<and> ?P (last (follow T a))"
    using ne assms(2) by (metis last_in_set)
  hence ne_filt: "filter ?P (follow T a) \<noteq> []" by (auto simp: filter_empty_conv)
  have key: "join_of T a b \<in> set (filter ?P (follow T a))"
    unfolding join_of_follow[OF assms(1)] by (rule hd_in_set[OF ne_filt])
  from key show "join_of T a b \<in> set (follow T a)" by (auto simp: set_filter)
  from key show "join_of T a b \<in> set (follow T b)" by (auto simp: set_filter)
qed

text \<open>The crux for the no-cycle property @{text N}: any common node of the two root-paths lies
      on the join's root-path (the join is the \<^emph>\<open>nearest\<close> common ancestor reached from @{term a}).\<close>
lemma join_of_first:
  assumes ps: "parent_spec T" and lst: "last (follow T a) = last (follow T b)"
      and xa: "x \<in> set (follow T a)" and xb: "x \<in> set (follow T b)"
    shows "x \<in> set (follow T (join_of T a b))"
proof -
  interpret par_T: parent T "\<lambda>_ _. True"
    using ps by unfold_locales
  define jn where "jn = join_of T a b"
  let ?P = "\<lambda>y. y \<in> set (follow T b)"
  have jn_a: "jn \<in> set (follow T a)" unfolding jn_def using join_of_mem(1)[OF ps lst] by auto
  then obtain p1 p2 where split: "follow T a = p1 @ jn # p2" by (meson split_list)
  have hd_eq: "jn = hd (filter ?P (follow T a))"
    unfolding jn_def by (rule join_of_follow[OF ps])
  have dist: "distinct (follow T a)"
    by (simp add: follow_def par_T.follow_distinct)
  have foll_jn: "follow T jn = jn # p2"
    using split by (simp add: follow_def par_T.follow_append)
  have jn_notin_p1: "jn \<notin> set p1" using dist split by auto
  have p1_noP: "filter ?P p1 = []"
  proof (rule ccontr)
    assume ne: "filter ?P p1 \<noteq> []"
    have "filter ?P (follow T a) = filter ?P p1 @ filter ?P (jn # p2)" using split by simp
    hence "hd (filter ?P (follow T a)) = hd (filter ?P p1)" using ne by (simp add: hd_append)
    moreover have "hd (filter ?P p1) \<in> set p1"
      using ne by (meson hd_in_set filter_is_subset subsetD)
    ultimately show False using hd_eq jn_notin_p1 by simp
  qed
  have x_notin_p1: "x \<notin> set p1" using p1_noP xb by (auto simp: filter_empty_conv)
  have "x \<in> set (jn # p2)" using xa split x_notin_p1 by auto
  thus ?thesis using foll_jn by (simp add: jn_def)
qed

text \<open>Antisymmetry of the ancestor order: if @{term u} is an ancestor of @{term v} and vice
      versa then they coincide.  This is acyclicity of the parent map (from @{const parent_spec}),
      and it is the second ingredient of the no-cycle property @{text N}.\<close>
lemma ancestor_antisym:
  assumes ps: "parent_spec T" and uv: "u \<in> set (follow T v)" and vu: "v \<in> set (follow T u)"
  shows "u = v"
proof -
  interpret par_T: parent T "\<lambda>_ _. True" using ps by unfold_locales
  from uv obtain p1 p2 where s1: "follow T v = p1 @ u # p2" by (meson split_list)
  from vu obtain q1 q2 where s2: "follow T u = q1 @ v # q2" by (meson split_list)
  have fu: "follow T u = u # p2" using s1 by (simp add: follow_def par_T.follow_append)
  have fv: "follow T v = v # q2" using s2 by (simp add: follow_def par_T.follow_append)
  have lv: "length (follow T v) = length p1 + length p2 + 1" using s1 by simp
  have lv2: "length (follow T v) = length q2 + 1" using fv by simp
  have lu: "length (follow T u) = length p2 + 1" using fu by simp
  have "p1 = []" using lv lv2 lu s2 by auto
  with s1 fv show "u = v" by simp
qed

text \<open>@{text N} (no-cycle / legality of the pivot): the new parent @{term j} of the path top is
      not in the subtree below @{term p}, i.e. @{term p} is not an ancestor of @{term j}.  This is
      what guarantees the reparenting does not create a cycle.  Here @{term jn} is the join of
      @{term i} and @{term j}, @{term jnp} says @{term jn} is a proper ancestor of @{term p} on the
      old path, and @{term pne} that @{term "p \<noteq> jn"}.\<close>
lemma no_cycle:
  assumes ps: "parent_spec T"
      and lst: "last (follow T i) = last (follow T j)"
      and pi: "p \<in> set (follow T i)"
      and jnp: "jn \<in> set (follow T p)" and jn_def: "jn = join_of T i j"
      and pne: "p \<noteq> jn"
  shows "p \<notin> set (follow T j)"
  using join_of_first[OF ps lst pi] ancestor_antisym[OF ps] jnp jn_def pne by auto

text \<open>@{text D2} ingredient: a node with a \<^emph>\<open>proper\<close> ancestor has a parent (its root-path is not
      the singleton @{term "[p]"}).\<close>
lemma follow_proper_ancestor_parent:
  assumes ps: "parent_spec T" and a: "a \<in> set (follow T p)" and ane: "a \<noteq> p"
  shows "T p \<noteq> None"
  using a ane by (auto simp: follow_ps_simps[OF ps] split: option.splits)

text \<open>@{text D2}: the path top @{term p} is not the root (it carries the leaving tree edge).
      Consumes a proper ancestor of @{term p} (in the pivot, @{term jn} with @{term "p \<noteq> jn"}).\<close>
lemma pivot_p_ne_r:
  assumes inv: "arb_invar r V S"
      and a: "a \<in> set (follow (prnt S) p)" and ane: "a \<noteq> p"
  shows "p \<noteq> r"
proof -
  have rinv: "rooted_arborescense_invar r V (prnt S)" using inv unfolding arb_invar_def by simp
  show "p \<noteq> r" using follow_proper_ancestor_parent[OF rooted_arborescense_invar_parent_spec[OF rinv] a ane] rooted_arborescense_invar_dom[OF rinv] by auto
qed

text \<open>A tree root-path stays inside @{term V}: every ancestor of a node in @{term V} is itself in
      @{term V} (the parent map's range is contained in @{term "dVs = V"}).  This lets the abstract
      path of @{thm follow_path} be located in @{term V} for  block\_nest/the stem setup.\<close>
lemma follow_subset_V:
  assumes rinv: "rooted_arborescense_invar r V T" and vV: "v \<in> V"
  shows "set (follow T v) \<subseteq> V"
proof -
  have ps: "parent_spec T" using rinv by (rule rooted_arborescense_invar_parent_spec)
  have rangeV: "\<And>w w'. T w = Some w' \<Longrightarrow> w' \<in> V"
  proof -
    fix w w' assume "T w = Some w'"
    hence "(w, w') \<in> {(y, x) |x y. Some x = T y}" by auto
    thus "w' \<in> V" using rooted_arborescense_invar_dVs[OF rinv] by (auto simp: dVs_def)
  qed
  have "v \<in> V \<longrightarrow> set (follow T v) \<subseteq> V"
  proof (induction rule: parent_spec_i.follow.pinduct[OF follow_dom_ps[OF ps, of v]])
    case (1 v)
    show ?case
    proof (intro impI)
      assume vV': "v \<in> V"
      show "set (follow T v) \<subseteq> V"
      proof (cases "T v")
        case None
        thus ?thesis using vV' by (subst follow_ps_simps[OF ps]) auto
      next
        case (Some w)
        have "set (follow T w) \<subseteq> V" using 1(2)[OF Some] rangeV Some by auto
        thus ?thesis using Some vV' by (subst follow_ps_simps[OF ps]) auto
      qed
    qed
  qed
  thus ?thesis using vV by simp
qed

subsection \<open>Blocks: the thread is a preorder of the tree (clause J as a contiguity statement)\<close>

text \<open>The \<^emph>\<open>block\<close> of @{term v} is the contiguous thread segment of @{term v}'s subtree: the
      prefix of @{term "follow (thrd S) v"} up to and including @{term "lsuc S v"}.  Under
      @{const arb_invar} (clause J) this prefix is exactly the clause-J witness @{text pre}, and
      its element set is the subtree @{term "children (prnt S) v"}.\<close>
definition block :: "'a ndtree \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "block S v = takeWhile (\<lambda>x. x \<noteq> lsuc S v) (follow (thrd S) v) @ [lsuc S v]"

text \<open>Pinning @{const block} to the clause-J witness: cut a distinct list at the first occurrence
      of the (unique) last element of a non-empty prefix recovers that prefix.\<close>
lemma takeWhile_block_aux:
  assumes "distinct xs" "xs = pre @ rest" "pre \<noteq> []" "last pre = L"
  shows "takeWhile (\<lambda>x. x \<noteq> L) xs @ [L] = pre"
proof -
  have pe: "pre = butlast pre @ [L]" using assms(3,4) by (metis append_butlast_last_id)
  hence xs2: "xs = butlast pre @ L # rest" using assms(2) by simp
  have "distinct (butlast pre @ L # rest)" using assms(1) xs2 by simp
  hence Lnotin: "\<forall>x\<in>set (butlast pre). x \<noteq> L" by auto
  have "takeWhile (\<lambda>x. x \<noteq> L) (butlast pre @ L # rest) = butlast pre"
    using Lnotin by (simp add: takeWhile_append2)
  thus ?thesis using xs2 pe by simp
qed

text \<open>The defining properties of @{const block} under the invariant (= clause J, made explicit).\<close>
lemma block_props:
  assumes inv: "arb_invar r V S" and vV: "v \<in> V"
  shows "follow (thrd S) v
            = block S v @ (case thrd S (lsuc S v) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd S) w)"
    and "block S v \<noteq> []"
    and "last (block S v) = lsuc S v"
    and "set (block S v) = children (prnt S) v"
    and "hd (block S v) = v"
proof -
  have pst: "parent_spec (thrd S)" using inv unfolding arb_invar_def by simp
  have "\<forall>v\<in>V. \<exists>pre. follow (thrd S) v
            = pre @ (case thrd S (lsuc S v) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd S) w)
          \<and> pre \<noteq> [] \<and> last pre = lsuc S v \<and> set pre = children (prnt S) v"
    using inv unfolding arb_invar_def by simp
  then obtain pre where
    P1: "follow (thrd S) v = pre @ (case thrd S (lsuc S v) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd S) w)"
    and P2: "pre \<noteq> []" and P3: "last pre = lsuc S v" and P4: "set pre = children (prnt S) v"
    using vV by auto
  have dist: "distinct (follow (thrd S) v)" by (rule follow_distinct_ps[OF pst])
  have beq: "block S v = pre"
    unfolding block_def using takeWhile_block_aux[OF dist P1 P2 P3] by auto
  show "follow (thrd S) v = block S v @ (case thrd S (lsuc S v) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd S) w)"
    using beq P1 by simp
  show "block S v \<noteq> []" using beq P2 by simp
  show "last (block S v) = lsuc S v" using beq P3 by simp
  show "set (block S v) = children (prnt S) v" using beq P4 by simp
  show "hd (block S v) = v" using beq P1 P2 follow_hd_ps[OF pst, of v] by (simp add: hd_append)
qed

text \<open>Two prefixes of a distinct list are comparable, and set-inclusion fixes which: if @{term as}
      and @{term bs} are both prefixes of a distinct @{term ys} and @{term "set as \<subseteq> set bs"} then
      @{term as} is a prefix of @{term bs}.  This turns "subtree @{term c} {\isasymsubseteq} subtree @{term v}"
      into "block @{term c} sits contiguously inside block @{term v}".\<close>
lemma prefix_mono_set:
  assumes dist: "distinct ys" and ea: "as @ as' = ys" and eb: "bs @ bs' = ys"
      and sub: "set as \<subseteq> set bs"
  shows "\<exists>cs. bs = as @ cs"
proof -
  have ta: "as = take (length as) ys" using ea by (metis append_eq_conv_conj)
  have tb: "bs = take (length bs) ys" using eb by (metis append_eq_conv_conj)
  show ?thesis
  proof (cases "length as \<le> length bs")
    case True
    then have "as = take (length as) bs" using ta tb by (metis min.absorb1 take_take)
    thus ?thesis by (metis append_take_drop_id)
  next
    case False
    hence le: "length bs \<le> length as" by simp
    have "take (length bs) as = take (length bs) (take (length as) ys)" using ta by simp
    also have "... = take (length bs) ys" using le by (simp add: take_take min.absorb1)
    also have "... = bs" using tb by simp
    finally have bsas: "bs = take (length bs) as" by simp
    then obtain d where asd: "as = bs @ d" by (metis append_take_drop_id)
    have disj: "set d \<inter> set bs = {}" using dist ea distinct_append asd by auto
    have subd: "set d \<subseteq> set bs" using sub asd by auto
    have "set d = set d \<inter> set bs" using subd by (simp add: Int_absorb2)
    with disj have "set d = {}" by simp
    hence "d = []" by simp
    thus ?thesis using asd by auto
  qed
qed

text \<open>Transitivity of the ancestor relation: if @{term c} is an ancestor of @{term u} and
      @{term v} an ancestor of @{term c} then @{term v} is an ancestor of @{term u}.\<close>
lemma follow_trans:
  assumes ps: "parent_spec T" and cu: "c \<in> set (follow T u)" and vc: "v \<in> set (follow T c)"
  shows "v \<in> set (follow T u)"
proof -
  from cu obtain a b where ab: "follow T u = a @ c # b" by (meson split_list)
  hence "follow T c = c # b" using follow_append_ps[OF ps] by auto
  with vc have "v \<in> set (c # b)" by simp
  with ab show ?thesis by auto
qed

text \<open>The subtree of a descendant is contained in the subtree: @{term "children T v"} is the set of
      nodes having @{term v} on their root-path (the subtree of @{term v}); it is monotone along
      descent.\<close>
lemma children_subset:
  assumes ps: "parent_spec T" and cv: "c \<in> children T v"
  shows "children T c \<subseteq> children T v"
  using cv follow_trans[OF ps] by (auto simp: children_def)

subsection \<open>Generic preorder-contiguity engine (surgery-free; clause J's contiguity half)\<close>

text \<open>The subtree rooted at an ancestor @{term a} of @{term x} is a suffix of @{term x}'s root-path:
      if @{term a} lies on @{term "follow T x"} then @{term "follow T a"} is contained in it.\<close>
lemma follow_sub_of_mem:
  assumes ps: "parent_spec T" and a: "a \<in> set (follow T x)"
  shows "set (follow T a) \<subseteq> set (follow T x)"
proof -
  from a obtain G H where "follow T x = G @ a # H" by (meson split_list)
  hence "follow T a = a # H" using follow_append_ps[OF ps] by auto
  moreover from \<open>follow T x = G @ a # H\<close> have "set (a # H) \<subseteq> set (follow T x)" by auto
  ultimately show ?thesis by simp
qed

text \<open>Preorder key fact 1 --- \<^emph>\<open>ancestors occur earlier\<close>: if @{term xs} is a DFS-preorder of tree
      @{term T} (root has no parent; each node's parent lies on the previous node's root-path), then
      every ancestor-or-self of @{term "xs!m"} occurs at some position \<open>\<le> m\<close> in @{term xs}.
      By strong induction on @{term m} using @{thm follow_sub_of_mem}.\<close>
lemma ancestors_earlier:
  assumes ps: "parent_spec T"
    and root0: "T (xs!0) = None"
    and dfs: "\<And>t. Suc t < length xs \<Longrightarrow> \<exists>a. T (xs!Suc t) = Some a \<and> a \<in> set (follow T (xs!t))"
    and m: "m < length xs"
  shows "\<forall>a \<in> set (follow T (xs!m)). \<exists>q \<le> m. xs!q = a"
  using m
proof (induction m rule: less_induct)
  case (less m)
  show ?case
  proof (cases m)
    case 0
    have "follow T (xs!m) = [xs!m]" using root0 0 by (subst follow_ps_simps[OF ps]) simp
    thus ?thesis using 0 by auto
  next
    case (Suc t)
    have tlen: "Suc t < length xs" using Suc less.prems by simp
    obtain a where Ta: "T (xs!Suc t) = Some a" and amem: "a \<in> set (follow T (xs!t))"
      using dfs[OF tlen] by auto
    have flw: "follow T (xs!m) = xs!m # follow T a" using Ta Suc by (subst follow_ps_simps[OF ps]) simp
    show ?thesis
    proof
      fix b assume "b \<in> set (follow T (xs!m))"
      then consider "b = xs!m" | "b \<in> set (follow T a)" using flw by auto
      thus "\<exists>q \<le> m. xs!q = b"
      proof cases
        case 1 thus ?thesis by auto
      next
        case 2
        have "b \<in> set (follow T (xs!t))" using follow_sub_of_mem[OF ps amem] 2 by auto
        moreover have "t < m" using Suc by simp
        ultimately obtain q where qt: "q \<le> t" and xqb: "xs!q = b" using less.IH[OF _] tlen by force
        have "q \<le> m" using qt Suc by simp
        thus ?thesis using xqb by auto
      qed
    qed
  qed
qed

text \<open>Preorder key fact 2 --- \<^emph>\<open>no return\<close>: once a node past the root @{term "v = ys!0"} fails to be a
      descendant of @{term v}, every later node also fails.  The DFS-step keeps the current parent on
      the previous node's path, so leaving @{term v}'s subtree is permanent.\<close>
lemma not_desc_propagates:
  assumes ps: "parent_spec T"
    and dist: "distinct ys"
    and v0: "v = ys!0"
    and yne: "ys \<noteq> []"
    and dfs: "\<And>t. Suc t < length ys \<Longrightarrow> \<exists>a. T (ys!Suc t) = Some a \<and> a \<in> set (follow T (ys!t))"
    and q: "0 < q" "q < length ys" "v \<notin> set (follow T (ys!q))"
  shows "\<And>d. q + d < length ys \<Longrightarrow> v \<notin> set (follow T (ys!(q+d)))"
proof -
  fix d assume "q + d < length ys"
  thus "v \<notin> set (follow T (ys!(q+d)))"
  proof (induction d)
    case 0 thus ?case using q by simp
  next
    case (Suc d)
    have ih: "v \<notin> set (follow T (ys!(q+d)))" using Suc.IH Suc.prems by auto
    have slen: "Suc (q+d) < length ys" using Suc.prems by simp
    obtain a where Ta: "T (ys!Suc (q+d)) = Some a" and amem: "a \<in> set (follow T (ys!(q+d)))"
      using dfs[OF slen] by auto
    have flw: "follow T (ys!(q+Suc d)) = ys!(q+Suc d) # follow T a"
      using Ta by (subst follow_ps_simps[OF ps]) simp
    have y0len: "0 < length ys" using yne by simp
    have idx: "(ys!0 = ys!(q+Suc d)) = (0 = q+Suc d)"
      by (rule nth_eq_iff_index_eq[OF dist y0len Suc.prems])
    have vne: "v \<noteq> ys!(q+Suc d)" using idx v0 by auto
    have "v \<notin> set (follow T a)"
    proof
      assume "v \<in> set (follow T a)"
      hence "v \<in> set (follow T (ys!(q+d)))" using follow_sub_of_mem[OF ps amem] by auto
      thus False using ih by simp
    qed
    thus ?case using flw vne by simp
  qed
qed

text \<open>The thread reaches @{term v} as a suffix: if @{term "follow F r0"} is the whole list @{term xs}
      and @{term "v = xs!pv"} then @{term "follow F v"} is @{term "drop pv xs"}.\<close>
lemma follow_thread_suffix:
  assumes psF: "parent_spec F" and xs: "follow F r0 = xs" and pv: "pv < length xs"
  shows "follow F (xs!pv) = drop pv xs"
  using xs follow_append_ps[OF psF] by (metis id_take_nth_drop Cons_nth_drop_Suc pv)

text \<open>\<^bold>\<open>Preorder contiguity engine\<close> (generic, surgery-free): if the thread @{term F} realises a list
      @{term xs} that is a DFS-preorder of the tree @{term T} (root @{term "xs!0"} has no parent; every
      node's @{term T}-parent lies on the previous node's @{term T}-root-path), then for every node
      @{term v} the subtree @{term "children T v"} is a non-empty contiguous prefix of @{term "follow F v"}
      headed by @{term v}.  This subsumes \<open>block_self_similar\<close> without assuming @{const arb_invar};
      it is the contiguity half of clause J for the post-pivot state.  Proof: @{thm ancestors_earlier}
      places descendants at-or-after @{term v} (so they lie in the suffix @{term "follow F v"}), and
      @{thm not_desc_propagates} shows no descendant survives past the first non-descendant, so the
      @{term takeWhile} of "is a descendant of @{term v}" is exactly @{term "children T v"}.\<close>
lemma preorder_contiguous:
  assumes psT: "parent_spec T" and psF: "parent_spec F"
    and xs: "follow F r0 = xs"
    and root0: "T (xs!0) = None"
    and dfs: "\<And>t. Suc t < length xs \<Longrightarrow> \<exists>a. T (xs!Suc t) = Some a \<and> a \<in> set (follow T (xs!t))"
    and vin: "v \<in> set xs"
    and subv: "children T v \<subseteq> set xs"
  shows "\<exists>pre suf. follow F v = pre @ suf \<and> set pre = children T v \<and> pre \<noteq> [] \<and> hd pre = v"
proof -
  have distxs: "distinct xs" using xs follow_distinct_ps[OF psF, of r0] by simp
  obtain pv where pvlt: "pv < length xs" and xpv: "xs!pv = v" using vin by (meson in_set_conv_nth)
  have pvle: "pv \<le> length xs" using pvlt by simp
  define ys where "ys = drop pv xs"
  have fFv: "follow F v = ys" using follow_thread_suffix[OF psF xs pvlt] xpv ys_def by simp
  have lenys: "length ys = length xs - pv" using ys_def by simp
  have ysne: "ys \<noteq> []" using pvlt lenys by auto
  have ys0: "ys!0 = v" using ys_def xpv nth_drop[OF pvle, of 0] by simp
  have distys: "distinct ys" using distxs ys_def by simp
  have yscons: "ys = v # tl ys" using ysne ys0 by (metis hd_conv_nth hd_Cons_tl)
  have dfsys: "\<And>t. Suc t < length ys \<Longrightarrow> \<exists>a. T (ys!Suc t) = Some a \<and> a \<in> set (follow T (ys!t))"
  proof -
    fix t assume tll: "Suc t < length ys"
    have h1: "Suc (pv + t) < length xs" using tll lenys by simp
    obtain a where A: "T (xs!Suc (pv+t)) = Some a \<and> a \<in> set (follow T (xs!(pv+t)))" using dfs[OF h1] by auto
    show "\<exists>a. T (ys!Suc t) = Some a \<and> a \<in> set (follow T (ys!t))" using A ys_def nth_drop[OF pvle, of "Suc t"] nth_drop[OF pvle, of t] by auto
  qed
  define Q where "Q = (\<lambda>u. v \<in> set (follow T u))"
  define pre where "pre = takeWhile Q ys"
  define suf where "suf = dropWhile Q ys"
  have decomp: "ys = pre @ suf" using pre_def suf_def by simp
  have vQ: "Q v" unfolding Q_def using follow_hd_ps[OF psT, of v] follow_ne_ps[OF psT, of v] by (metis hd_in_set)
  have preQ: "pre = v # takeWhile Q (tl ys)" unfolding pre_def using vQ by (subst yscons) simp
  have prene: "pre \<noteq> []" using preQ by simp
  have hdpre: "hd pre = v" using preQ by simp
  have subset1: "set pre \<subseteq> children T v"
  proof
    fix u assume "u \<in> set pre"
    hence "Q u" using pre_def by (metis set_takeWhileD)
    thus "u \<in> children T v" unfolding Q_def children_def by simp
  qed
  have subset2: "children T v \<subseteq> set pre"
  proof
    fix d assume dc: "d \<in> children T v"
    hence Qd: "v \<in> set (follow T d)" unfolding children_def by simp
    have dxs: "d \<in> set xs" using subv dc by auto
    then obtain pd where pdlt: "pd < length xs" and xpd: "xs!pd = d" by (meson in_set_conv_nth)
    obtain q where qpd: "q \<le> pd" and xqv: "xs!q = v"
      using ancestors_earlier[OF psT root0 dfs pdlt] Qd xpd by auto
    have qpv: "q = pv" using nth_eq_iff_index_eq[OF distxs] qpd pdlt pvlt xqv xpv by auto
    hence pvpd: "pv \<le> pd" using qpd by simp
    define idx where "idx = pd - pv"
    have idxlt: "idx < length ys" using idx_def lenys pdlt pvpd by simp
    have ysidx: "ys!idx = d" using idx_def ys_def nth_drop[OF pvle, of idx] pvpd xpd by simp
    have idxpre: "idx < length pre"
    proof (rule ccontr)
      assume "\<not> idx < length pre"
      hence ge: "length pre \<le> idx" by simp
      show False
      proof (cases "suf = []")
        case True
        hence "length pre = length ys" using decomp by simp
        thus False using ge idxlt by simp
      next
        case False
        have pelt: "length pre < length ys" using decomp False by auto
        have yseq: "ys = pre @ hd suf # tl suf" using decomp False by simp
        have yspe: "ys!(length pre) = hd suf" using yseq by (metis nth_append_length)
        have notQ: "\<not> Q (hd suf)" using suf_def False by (metis hd_dropWhile)
        have vnot: "v \<notin> set (follow T (ys!(length pre)))" using yspe notQ Q_def by simp
        have pepos: "0 < length pre" using prene by (simp add: less_le)
        have ndp: "\<And>dd. length pre + dd < length ys \<Longrightarrow> v \<notin> set (follow T (ys!(length pre + dd)))"
          using not_desc_propagates[OF psT distys ys0[symmetric] ysne dfsys pepos pelt vnot] by auto
        have lt: "length pre + (idx - length pre) < length ys" using idxlt ge by auto
        have "v \<notin> set (follow T (ys!idx))" using ndp[OF lt] ge by auto
        thus False using ysidx Qd by simp
      qed
    qed
    have "d = pre!idx" using ysidx decomp idxpre by (simp add: nth_append)
    thus "d \<in> set pre" using idxpre by simp
  qed
  show ?thesis using fFv decomp subset1 subset2 prene hdpre by auto
qed

text \<open>@{text "B\<star>"} (block self-similarity / recursive preorder): the block of a node @{term v}
      contains, as a contiguous infix, the block of any node @{term c} in its subtree.  This is the
      heavy geometric fact: it re-derives that clause J is a \<^emph>\<open>recursive\<close> preorder, and from it the
      disjointness/ordering facts (@{text D3}) used by the stem induction follow mechanically.\<close>
lemma block_self_similar:
  assumes inv: "arb_invar r V S" and vV: "v \<in> V" and cV: "c \<in> V"
      and cchild: "c \<in> children (prnt S) v" and cne: "c \<noteq> v"
  shows "\<exists>A B. block S v = A @ block S c @ B"
proof -
  have pst: "parent_spec (thrd S)" using inv unfolding arb_invar_def by simp
  have ppt: "parent_spec (prnt S)" using inv unfolding arb_invar_def
    by (simp add: rooted_arborescense_invar_def)
  define FU where "FU = follow (thrd S) v"
  have bv_eq: "FU = block S v @ (case thrd S (lsuc S v) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd S) w)"
    unfolding FU_def by (rule block_props(1)[OF inv vV])
  have bv_set: "set (block S v) = children (prnt S) v" by (rule block_props(4)[OF inv vV])
  have dist: "distinct FU" unfolding FU_def by (rule follow_distinct_ps[OF pst])
  have cblk: "c \<in> set (block S v)" using cchild bv_set by simp
  hence cFU: "c \<in> set FU" using bv_eq by simp
  then obtain G H where FUsplit: "FU = G @ c # H" by (meson split_list)
  have fc: "follow (thrd S) c = c # H" using FUsplit follow_append_ps[OF pst] unfolding FU_def by auto
  have bc_eq: "follow (thrd S) c = block S c @ (case thrd S (lsuc S c) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd S) w)"
    by (rule block_props(1)[OF inv cV])
  have bc_set: "set (block S c) = children (prnt S) c" by (rule block_props(4)[OF inv cV])
  define Rv where "Rv = (case thrd S (lsuc S v) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd S) w)"
  have cnotG: "c \<notin> set G" using dist FUsplit by auto
  have eqA: "G @ c # H = block S v @ Rv" using FUsplit bv_eq Rv_def by simp
  have raw: "(\<exists>us. G = block S v @ us \<and> us @ c # H = Rv) \<or> (\<exists>us. G @ us = block S v \<and> c # H = us @ Rv)"
    using eqA by (subst (asm) append_eq_append_conv2) blast
  have Gsub: "\<exists>us. block S v = G @ us"
  proof (rule disjE[OF raw])
    assume "\<exists>us. G = block S v @ us \<and> us @ c # H = Rv"
    then obtain us where "G = block S v @ us" by auto
    hence "c \<in> set G" using cblk by simp
    with cnotG show ?thesis by simp
  next
    assume "\<exists>us. G @ us = block S v \<and> c # H = us @ Rv"
    then obtain us where "G @ us = block S v" by auto
    thus ?thesis by metis
  qed
  define Rc where "Rc = (case thrd S (lsuc S c) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd S) w)"
  have ea: "(G @ block S c) @ Rc = FU" using bc_eq fc Rc_def FUsplit by auto
  have eb: "block S v @ Rv = FU" using eqA FUsplit by simp
  have setG: "set G \<subseteq> set (block S v)" using Gsub by auto
  have setc: "children (prnt S) c \<subseteq> set (block S v)"
    using children_subset[OF ppt cchild] bv_set by simp
  have sub: "set (G @ block S c) \<subseteq> set (block S v)" using setG setc bc_set by auto
  obtain cs where "block S v = (G @ block S c) @ cs"
    using prefix_mono_set[OF dist ea eb sub] by auto
  thus ?thesis by auto
qed

text \<open>The block-nesting in the shape consumed by the stem induction ({\isasymsection}14.3 @{text block_nest}): the
      block of @{term v} opens with @{term v} itself, then contains the whole block of a subtree
      node @{term c} contiguously.  @{term v} heads the block because @{term "hd (block S v) = v"}
      and @{term "v \<noteq> c = hd (block S c)"}.\<close>
lemma block_nest:
  assumes inv: "arb_invar r V S" and vV: "v \<in> V" and cV: "c \<in> V"
      and cchild: "c \<in> children (prnt S) v" and cne: "c \<noteq> v"
  shows "\<exists>P Q. block S v = v # P @ block S c @ Q"
proof -
  obtain A B where AB: "block S v = A @ block S c @ B"
    using block_self_similar[OF inv vV cV cchild cne] by auto
  have hdv: "hd (block S v) = v" by (rule block_props(5)[OF inv vV])
  have hdc: "hd (block S c) = c" by (rule block_props(5)[OF inv cV])
  have bcne: "block S c \<noteq> []" by (rule block_props(2)[OF inv cV])
  have Ane: "A \<noteq> []"
  proof
    assume "A = []"
    hence "hd (block S v) = c" using AB hdc bcne by simp
    thus False using hdv cne by simp
  qed
  hence "hd A = v" using AB hdv by (simp add: hd_append)
  hence "A = v # tl A" using Ane by (metis hd_Cons_tl)
  hence "block S v = v # tl A @ block S c @ B" using AB by simp
  thus ?thesis by auto
qed

text \<open>\<^bold>\<open>The thread is a DFS-preorder of the tree\<close> (converse geometry of @{thm block_props}): under
      @{const arb_invar}, if @{term y} is the thread-successor of @{term x} (@{term "thrd S x = Some y"})
      then @{term y}'s tree-parent is an ancestor-or-self of @{term x}, i.e.
      @{term "\<exists>g. prnt S y = Some g \<and> g \<in> set (follow (prnt S) x)"}.  This is exactly the DFS-step
      hypothesis consumed by @{thm preorder_contiguous}; instantiated at @{term S0} it yields the old
      thread's preorder step, the backbone of the surviving \<open>holed\<close> edges in the pivot output.
      Proof (reusing the block machinery): @{term y} lies in @{term "block S g"} past its head @{term g},
      so its thread-predecessor --- which is @{term x} by injectivity of the thread (clause G) --- also
      lies in @{term "block S g"} (the subtree of @{term g}); hence @{term g} is an ancestor of @{term x}.\<close>
lemma arb_dfs_step:
  assumes inv: "arb_invar rr VV (S :: 'a ndtree)" and xV: "x \<in> VV" and edge: "thrd S x = Some y"
  shows "\<exists>g. prnt S y = Some g \<and> g \<in> set (follow (prnt S) x)"
proof -
  have pst: "parent_spec (thrd S)" using inv unfolding arb_invar_def by simp
  have rinv: "rooted_arborescense_invar rr VV (prnt S)" using inv unfolding arb_invar_def by simp
  have ppt: "parent_spec (prnt S)" by (rule rooted_arborescense_invar_parent_spec[OF rinv])
  have G: "\<forall>v v'. thrd S v = Some v' \<longleftrightarrow> rvth S v' = Some v" using inv unfolding arb_invar_def by simp
  have setV: "set (follow (thrd S) rr) = VV" using inv unfolding arb_invar_def by simp
  have xr: "x \<in> set (follow (thrd S) rr)" using xV setV by simp
  then obtain A B where AB: "follow (thrd S) rr = A @ x # B" by (meson split_list)
  have fx: "follow (thrd S) x = x # B" using follow_append_ps[OF pst AB] by auto
  have fxy: "follow (thrd S) x = x # follow (thrd S) y" using edge by (subst follow_ps_simps[OF pst]) simp
  have yfollow: "y \<in> set (follow (thrd S) x)"
    using fxy follow_hd_ps[OF pst, of y] follow_ne_ps[OF pst, of y] by (metis list.set_intros(2) hd_in_set)
  have "set (follow (thrd S) x) \<subseteq> VV" using fx AB setV by auto
  hence yV: "y \<in> VV" using yfollow by auto
  have ynr: "y \<noteq> rr"
  proof
    assume "y = rr"
    hence "rvth S rr = Some x" using G edge by simp
    moreover have "dom (rvth S) = VV - {rr}" using inv unfolding arb_invar_def by simp
    ultimately show False by auto
  qed
  have "y \<in> dom (prnt S)" using rooted_arborescense_invar_dom[OF rinv] yV ynr by simp
  then obtain g where g: "prnt S y = Some g" by (blast dest: domD)
  have gfy: "follow (prnt S) y = y # follow (prnt S) g" using g by (subst follow_ps_simps[OF ppt]) simp
  have gin: "g \<in> set (follow (prnt S) y)"
    using gfy follow_hd_ps[OF ppt, of g] follow_ne_ps[OF ppt, of g] by (metis list.set_intros(2) hd_in_set)
  hence ychild: "y \<in> children (prnt S) g" unfolding children_def by simp
  have gV: "g \<in> VV" using gin follow_subset_V[OF rinv yV] by auto
  have yblk: "y \<in> set (block S g)" using ychild block_props(4)[OF inv gV] by simp
  have hdg: "hd (block S g) = g" by (rule block_props(5)[OF inv gV])
  have bne: "block S g \<noteq> []" by (rule block_props(2)[OF inv gV])
  have yneg: "y \<noteq> g"
  proof
    assume "y = g"
    hence "follow (prnt S) y = y # follow (prnt S) y" using gfy by simp
    thus False by (metis Suc_n_not_n length_Cons)
  qed
  obtain idx where idxlt: "idx < length (block S g)" and byidx: "block S g ! idx = y"
    using yblk by (meson in_set_conv_nth)
  have idxpos: "0 < idx"
  proof (rule ccontr)
    assume "\<not> 0 < idx" hence "idx = 0" by simp
    hence "y = hd (block S g)" using byidx bne by (simp add: hd_conv_nth)
    thus False using hdg yneg by simp
  qed
  have fg: "follow (thrd S) g = block S g @ (case thrd S (lsuc S g) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd S) w)"
    by (rule block_props(1)[OF inv gV])
  have b1: "idx - 1 < length (block S g)" using idxlt idxpos by simp
  have idxlt2: "Suc (idx - 1) < length (follow (thrd S) g)" using idxpos idxlt fg by auto
  have ed0: "thrd S (follow (thrd S) g ! (idx - 1)) = Some (follow (thrd S) g ! Suc (idx - 1))"
    by (rule follow_nth_Suc[OF pst idxlt2])
  have p1: "follow (thrd S) g ! (idx-1) = block S g ! (idx-1)" using fg b1 by (metis nth_append)
  have p2: "follow (thrd S) g ! Suc (idx-1) = block S g ! idx" 
    using fg  idxlt 
    by (simp add: idxpos nth_append_left)
  have edge2: "thrd S (block S g ! (idx-1)) = Some y" using ed0 p1 p2 byidx by simp
  have "rvth S y = Some x" using G edge by simp
  moreover have "rvth S y = Some (block S g ! (idx-1))" using G edge2 by simp
  ultimately have "x = block S g ! (idx-1)" by simp
  hence "x \<in> set (block S g)" using b1 by (metis nth_mem)
  hence "x \<in> children (prnt S) g" using block_props(4)[OF inv gV] by simp
  hence "g \<in> set (follow (prnt S) x)" unfolding children_def by simp
  thus ?thesis using g by auto
qed

paragraph \<open>The loops, as tail-recursive functions over the maps (they climb unbounded parent /
           thread chains, so they cannot be ordinary @{command fun} definitions).\<close>


text \<open>Base case of the stem loop: when the current stem node has reached @{term p} the loop returns
      its state unchanged.  This is the guard-hit equation the stem induction ({\isasymsection}13.5) terminates on;
      the recursive step is @{thm stem_loop.simps} with the guard taken false.\<close>

text \<open>Generic engine for the @{text thrd_inv} unfolding ({\isasymsection}13.4): an external @{const fun_upd}
      on a key not written by a fold of @{const fun_upd}s commutes inside the fold.\<close>
lemma fold_upd_commute:
  "x \<notin> (g ` set xs) \<Longrightarrow>
     (fold (\<lambda>a T. T(g a := h a)) xs Y)(x := v)
       = fold (\<lambda>a T. T(g a := h a)) xs (Y(x := v))"
proof (induction xs arbitrary: Y)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  have ne: "x \<noteq> g a" using Cons.prems by simp
  have notin: "x \<notin> g ` set as" using Cons.prems by simp
  have step: "(Y(g a := h a))(x := v) = (Y(x := v))(g a := h a)"
    using ne by (simp add: fun_upd_twist)
  show ?case
    by (simp only: fold_simps Cons.IH[OF notin] step)
qed

text \<open>Companion: the value of a @{const fun_upd}-fold at a key it never writes is the base value.\<close>
lemma fold_upd_other:
  "z \<notin> (g ` set xs) \<Longrightarrow> (fold (\<lambda>a T. T(g a := h a)) xs Y) z = Y z"
  by (induction xs arbitrary: Y) auto

text \<open>Appending a fresh key to an association list is the same as a @{const fun_upd} on its
      @{const map_of} (used to extend @{text REV}/@{text revBR} by their @{term "t = m"} term).\<close>
lemma map_of_snoc_upd:
  "c \<notin> fst ` set xs \<Longrightarrow> map_of (xs @ [(c, v)]) = (map_of xs)(c \<mapsto> v)"
proof -
  assume a: "c \<notin> fst ` set xs"
  hence dom: "c \<notin> dom (map_of xs)" by (simp add: dom_map_of_conv_image_fst)
  show ?thesis
  proof (rule ext)
    fix x
    show "map_of (xs @ [(c, v)]) x = ((map_of xs)(c \<mapsto> v)) x"
      using dom by (cases "x = c"; cases "map_of xs x")
                   (auto simp: map_of_append map_add_def)
  qed
qed


text \<open>@{const dirty_pass} edits only @{const rvth} (it terminates, being a @{const foldl}); the other
      four record fields pass through unchanged.  This pins @{term "thrd (St)"} (the final thread, {\isasymsection}15.2)
      to @{term "thrd Ss"} and leaves @{const prnt}/@{const lsuc}/@{const snum} as the decoration loops find them.\<close>
lemma dirty_pass_unchanged:
  "thrd (dirty_pass S drt) = thrd S
   \<and> prnt (dirty_pass S drt) = prnt S
   \<and> lsuc (dirty_pass S drt) = lsuc S
   \<and> snum (dirty_pass S drt) = snum S"
proof (induction drt arbitrary: S)
  case Nil show ?case by (simp add: dirty_pass_def)
next
  case (Cons u us)
  define S' where "S' = (case thrd S u of None \<Rightarrow> S | Some w \<Rightarrow> S\<lparr>rvth := (rvth S)(w \<mapsto> u)\<rparr>)"
  have step: "dirty_pass S (u # us) = dirty_pass S' us"
    by (simp add: dirty_pass_def S'_def)
  have flds: "thrd S' = thrd S \<and> prnt S' = prnt S \<and> lsuc S' = lsuc S \<and> snum S' = snum S"
    by (simp add: S'_def split: option.split)
  show ?case using Cons.IH[of S'] step flds by simp
qed

lemmas dirty_pass_thrd[simp] = dirty_pass_unchanged[THEN conjunct1]
lemmas dirty_pass_prnt[simp] = dirty_pass_unchanged[THEN conjunct2, THEN conjunct1]
lemmas dirty_pass_lsuc[simp] = dirty_pass_unchanged[THEN conjunct2, THEN conjunct2, THEN conjunct1]
lemmas dirty_pass_snum[simp] = dirty_pass_unchanged[THEN conjunct2, THEN conjunct2, THEN conjunct2]

text \<open>@{const dirty_pass} rebuilds @{const rvth} by a left fold over @{term ds}: each node @{term u}
      with @{term "thrd S u = Some w"} contributes term "w {\isasymmapsto} u" (last write wins).\<close>
lemma dirty_pass_rvth_fold:
  "rvth (dirty_pass S ds) = foldl (\<lambda>R u. case thrd S u of None \<Rightarrow> R | Some w \<Rightarrow> R(w \<mapsto> u)) (rvth S) ds"
proof (induction ds arbitrary: S)
  case Nil show ?case by (simp add: dirty_pass_def)
next
  case (Cons u us)
  define S' where "S' = (case thrd S u of None \<Rightarrow> S | Some w \<Rightarrow> S\<lparr>rvth := (rvth S)(w \<mapsto> u)\<rparr>)"
  have step: "dirty_pass S (u # us) = dirty_pass S' us"
    by (simp add: dirty_pass_def S'_def)
  have th: "thrd S' = thrd S" by (simp add: S'_def split: option.split)
  have rv: "rvth S' = (case thrd S u of None \<Rightarrow> rvth S | Some w \<Rightarrow> (rvth S)(w \<mapsto> u))"
    by (simp add: S'_def split: option.split)
  have "rvth (dirty_pass S (u # us)) = foldl (\<lambda>R u. case thrd S' u of None \<Rightarrow> R | Some w \<Rightarrow> R(w \<mapsto> u)) (rvth S') us"
    using step Cons.IH[of S'] by simp
  also have "\<dots> = foldl (\<lambda>R u. case thrd S u of None \<Rightarrow> R | Some w \<Rightarrow> R(w \<mapsto> u)) (rvth S') us"
    using th by simp
  also have "\<dots> = foldl (\<lambda>R u. case thrd S u of None \<Rightarrow> R | Some w \<Rightarrow> R(w \<mapsto> u)) (rvth S) (u # us)"
    using rv by simp
  finally show ?case .
qed

text \<open>Last-write-wins evaluation of such a reverse-rebuild fold: the value at @{term x} is the last
      @{term u} in @{term ds} whose @{term "f u = Some x"} (else the seed @{term "R0 x"}).\<close>
lemma foldl_upd_eval:
  "(foldl (\<lambda>R u. case f u of None \<Rightarrow> R | Some w \<Rightarrow> R(w \<mapsto> u)) R0 ds) x =
   (if (\<exists>u\<in>set ds. f u = Some x) then Some (last (filter (\<lambda>u. f u = Some x) ds)) else R0 x)"
proof (induction ds rule: rev_induct)
  case Nil show ?case by simp
next
  case (snoc u ds)
  show ?case
  proof (cases "f u")
    case None
    thus ?thesis using snoc by auto
  next
    case (Some w)
    show ?thesis
    proof (cases "x = w")
      case True thus ?thesis using Some by simp
    next
      case False thus ?thesis using Some snoc by auto
    qed
  qed
qed

lemma filter_eq_self_single: "distinct xs \<Longrightarrow> u \<in> set xs \<Longrightarrow> filter (\<lambda>x. x = u) xs = [u]"
  by (induction xs) (auto simp: filter_empty_conv)



lemmas [code] =
  stem_loop.simps stem_num_loop.simps last_vin_loop.simps
  last_vout_loop.simps succ_vin_loop.simps succ_vout_loop.simps

text \<open>The five decoration loops ({\isasymsection}15.4) each climb the \<^emph>\<open>fixed\<close> parent map @{term P} (they never
      touch @{const prnt}), so when @{term P} is a @{const parent_spec} they terminate, and each
      preserves every record field except the one it recomputes (@{const lsuc} resp. @{const snum}).
      In particular all five leave @{const thrd}, @{const prnt}, @{const rvth} unchanged --- this pins
      the final thread (and reverse-thread before @{const dirty_pass}) for the {\isasymsection}15.2 "out-edge" closed
      form.  The shared proof is well-founded induction along the parent chain from @{term u}
      (@{thm follow_dom_ps}), exactly as in  stem\_loop\_effect.\<close>
lemma stem_num_loop_fields:
  assumes ps: "parent_spec P"
  shows "prnt S = P \<longrightarrow>
           (prnt (stem_num_loop S sn0 u iv acc tls) = P
          \<and> thrd (stem_num_loop S sn0 u iv acc tls) = thrd S
          \<and> rvth (stem_num_loop S sn0 u iv acc tls) = rvth S)"
proof (induction arbitrary: S acc rule: parent_spec_i.follow.pinduct[OF follow_dom_ps[OF ps, of u]])
  case (1 u)
  show ?case
  proof (intro impI)
    assume pS: "prnt S = P"
    show "prnt (stem_num_loop S sn0 u iv acc tls) = P
        \<and> thrd (stem_num_loop S sn0 u iv acc tls) = thrd S
        \<and> rvth (stem_num_loop S sn0 u iv acc tls) = rvth S"
    proof (cases "u = iv")
      case True
      have "stem_num_loop S sn0 u iv acc tls = S" using True by (subst stem_num_loop.simps) simp
      thus ?thesis using pS by simp
    next
      case False
      show ?thesis
      proof (cases "P u")
        case None
        hence "prnt S u = None" using pS by simp
        hence "stem_num_loop S sn0 u iv acc tls = S" using False by (subst stem_num_loop.simps) simp
        thus ?thesis using pS by simp
      next
        case (Some par)
        hence pSu: "prnt S u = Some par" using pS by simp
        define acc' where "acc' = acc + (sn0 u - sn0 par)"
        define S' where "S' = S\<lparr>snum := (snum S)(u := acc'), lsuc := (lsuc S)(par := tls)\<rparr>"
        have rec: "stem_num_loop S sn0 u iv acc tls = stem_num_loop S' sn0 par iv acc' tls"
          using False pSu by (subst stem_num_loop.simps) (simp add: acc'_def S'_def Let_def)
        have pS': "prnt S' = P" using pS by (simp add: S'_def)
        have IH: "prnt (stem_num_loop S' sn0 par iv acc' tls) = P
                \<and> thrd (stem_num_loop S' sn0 par iv acc' tls) = thrd S'
                \<and> rvth (stem_num_loop S' sn0 par iv acc' tls) = rvth S'"
          using 1(2)[OF Some, of S' acc'] pS' by simp
        thus ?thesis using rec by (simp add: S'_def)
      qed
    qed
  qed
qed

lemma last_vin_loop_fields:
  assumes ps: "parent_spec P"
  shows "prnt S = P \<longrightarrow>
           (prnt (last_vin_loop S u jv lso) = P
          \<and> thrd (last_vin_loop S u jv lso) = thrd S
          \<and> rvth (last_vin_loop S u jv lso) = rvth S
          \<and> snum (last_vin_loop S u jv lso) = snum S)"
proof (induction arbitrary: S rule: parent_spec_i.follow.pinduct[OF follow_dom_ps[OF ps, of u]])
  case (1 u)
  show ?case
  proof (intro impI)
    assume pS: "prnt S = P"
    show "prnt (last_vin_loop S u jv lso) = P
        \<and> thrd (last_vin_loop S u jv lso) = thrd S
        \<and> rvth (last_vin_loop S u jv lso) = rvth S
        \<and> snum (last_vin_loop S u jv lso) = snum S"
    proof (cases "lsuc S u = jv")
      case False
      have "last_vin_loop S u jv lso = S" using False by (subst last_vin_loop.simps) simp
      thus ?thesis using pS by simp
    next
      case True
      define S' where "S' = S\<lparr>lsuc := (lsuc S)(u := lso)\<rparr>"
      have pS': "prnt S' = P" using pS by (simp add: S'_def)
      show ?thesis
      proof (cases "P u")
        case None
        hence "prnt S' u = None" using pS' by simp
        hence "last_vin_loop S u jv lso = S'"
          using True by (subst last_vin_loop.simps) (simp add: S'_def Let_def)
        thus ?thesis using pS' by (simp add: S'_def)
      next
        case (Some par)
        hence pSu': "prnt S' u = Some par" using pS' by simp
        have rec: "last_vin_loop S u jv lso = last_vin_loop S' par jv lso"
          using True pSu' by (subst last_vin_loop.simps) (simp add: S'_def Let_def)
        have IH: "prnt (last_vin_loop S' par jv lso) = P
                \<and> thrd (last_vin_loop S' par jv lso) = thrd S'
                \<and> rvth (last_vin_loop S' par jv lso) = rvth S'
                \<and> snum (last_vin_loop S' par jv lso) = snum S'"
          using 1(2)[OF Some, of S'] pS' by simp
        thus ?thesis using rec by (simp add: S'_def)
      qed
    qed
  qed
qed

lemma last_vout_loop_fields:
  assumes ps: "parent_spec P"
  shows "prnt S = P \<longrightarrow>
           (prnt (last_vout_loop S u stp gv sv) = P
          \<and> thrd (last_vout_loop S u stp gv sv) = thrd S
          \<and> rvth (last_vout_loop S u stp gv sv) = rvth S
          \<and> snum (last_vout_loop S u stp gv sv) = snum S)"
proof (induction arbitrary: S rule: parent_spec_i.follow.pinduct[OF follow_dom_ps[OF ps, of u]])
  case (1 u)
  show ?case
  proof (intro impI)
    assume pS: "prnt S = P"
    show "prnt (last_vout_loop S u stp gv sv) = P
        \<and> thrd (last_vout_loop S u stp gv sv) = thrd S
        \<and> rvth (last_vout_loop S u stp gv sv) = rvth S
        \<and> snum (last_vout_loop S u stp gv sv) = snum S"
    proof (cases "Some u = stp \<or> lsuc S u \<noteq> gv")
      case True
      have "last_vout_loop S u stp gv sv = S" using True by (subst last_vout_loop.simps) simp
      thus ?thesis using pS by simp
    next
      case False
      define S' where "S' = S\<lparr>lsuc := (lsuc S)(u := sv)\<rparr>"
      have pS': "prnt S' = P" using pS by (simp add: S'_def)
      show ?thesis
      proof (cases "P u")
        case None
        hence "prnt S' u = None" using pS' by simp
        hence "last_vout_loop S u stp gv sv = S'"
          using False by (subst last_vout_loop.simps) (simp add: S'_def Let_def)
        thus ?thesis using pS' by (simp add: S'_def)
      next
        case (Some par)
        hence pSu': "prnt S' u = Some par" using pS' by simp
        have rec: "last_vout_loop S u stp gv sv = last_vout_loop S' par stp gv sv"
          using False pSu' by (subst last_vout_loop.simps) (simp add: S'_def Let_def)
        have IH: "prnt (last_vout_loop S' par stp gv sv) = P
                \<and> thrd (last_vout_loop S' par stp gv sv) = thrd S'
                \<and> rvth (last_vout_loop S' par stp gv sv) = rvth S'
                \<and> snum (last_vout_loop S' par stp gv sv) = snum S'"
          using 1(2)[OF Some, of S'] pS' by simp
        thus ?thesis using rec by (simp add: S'_def)
      qed
    qed
  qed
qed

lemma succ_vin_loop_fields:
  assumes ps: "parent_spec P"
  shows "prnt S = P \<longrightarrow>
           (prnt (succ_vin_loop S u jn d) = P
          \<and> thrd (succ_vin_loop S u jn d) = thrd S
          \<and> rvth (succ_vin_loop S u jn d) = rvth S
          \<and> lsuc (succ_vin_loop S u jn d) = lsuc S)"
proof (induction arbitrary: S rule: parent_spec_i.follow.pinduct[OF follow_dom_ps[OF ps, of u]])
  case (1 u)
  show ?case
  proof (intro impI)
    assume pS: "prnt S = P"
    show "prnt (succ_vin_loop S u jn d) = P
        \<and> thrd (succ_vin_loop S u jn d) = thrd S
        \<and> rvth (succ_vin_loop S u jn d) = rvth S
        \<and> lsuc (succ_vin_loop S u jn d) = lsuc S"
    proof (cases "u = jn")
      case True
      have "succ_vin_loop S u jn d = S" using True by (subst succ_vin_loop.simps) simp
      thus ?thesis using pS by simp
    next
      case False
      define S' where "S' = S\<lparr>snum := (snum S)(u := snum S u + d)\<rparr>"
      have pS': "prnt S' = P" using pS by (simp add: S'_def)
      show ?thesis
      proof (cases "P u")
        case None
        hence "prnt S' u = None" using pS' by simp
        hence "succ_vin_loop S u jn d = S'"
          using False by (subst succ_vin_loop.simps) (simp add: S'_def Let_def)
        thus ?thesis using pS' by (simp add: S'_def)
      next
        case (Some par)
        hence pSu': "prnt S' u = Some par" using pS' by simp
        have rec: "succ_vin_loop S u jn d = succ_vin_loop S' par jn d"
          using False pSu' by (subst succ_vin_loop.simps) (simp add: S'_def Let_def)
        have IH: "prnt (succ_vin_loop S' par jn d) = P
                \<and> thrd (succ_vin_loop S' par jn d) = thrd S'
                \<and> rvth (succ_vin_loop S' par jn d) = rvth S'
                \<and> lsuc (succ_vin_loop S' par jn d) = lsuc S'"
          using 1(2)[OF Some, of S'] pS' by simp
        thus ?thesis using rec by (simp add: S'_def)
      qed
    qed
  qed
qed

lemma succ_vout_loop_fields:
  assumes ps: "parent_spec P"
  shows "prnt S = P \<longrightarrow>
           (prnt (succ_vout_loop S u jn d) = P
          \<and> thrd (succ_vout_loop S u jn d) = thrd S
          \<and> rvth (succ_vout_loop S u jn d) = rvth S
          \<and> lsuc (succ_vout_loop S u jn d) = lsuc S)"
proof (induction arbitrary: S rule: parent_spec_i.follow.pinduct[OF follow_dom_ps[OF ps, of u]])
  case (1 u)
  show ?case
  proof (intro impI)
    assume pS: "prnt S = P"
    show "prnt (succ_vout_loop S u jn d) = P
        \<and> thrd (succ_vout_loop S u jn d) = thrd S
        \<and> rvth (succ_vout_loop S u jn d) = rvth S
        \<and> lsuc (succ_vout_loop S u jn d) = lsuc S"
    proof (cases "u = jn")
      case True
      have "succ_vout_loop S u jn d = S" using True by (subst succ_vout_loop.simps) simp
      thus ?thesis using pS by simp
    next
      case False
      define S' where "S' = S\<lparr>snum := (snum S)(u := snum S u - d)\<rparr>"
      have pS': "prnt S' = P" using pS by (simp add: S'_def)
      show ?thesis
      proof (cases "P u")
        case None
        hence "prnt S' u = None" using pS' by simp
        hence "succ_vout_loop S u jn d = S'"
          using False by (subst succ_vout_loop.simps) (simp add: S'_def Let_def)
        thus ?thesis using pS' by (simp add: S'_def)
      next
        case (Some par)
        hence pSu': "prnt S' u = Some par" using pS' by simp
        have rec: "succ_vout_loop S u jn d = succ_vout_loop S' par jn d"
          using False pSu' by (subst succ_vout_loop.simps) (simp add: S'_def Let_def)
        have IH: "prnt (succ_vout_loop S' par jn d) = P
                \<and> thrd (succ_vout_loop S' par jn d) = thrd S'
                \<and> rvth (succ_vout_loop S' par jn d) = rvth S'
                \<and> lsuc (succ_vout_loop S' par jn d) = lsuc S'"
          using 1(2)[OF Some, of S'] pS' by simp
        thus ?thesis using rec by (simp add: S'_def)
      qed
    qed
  qed
qed

text \<open>The value each decoration loop computes: it overwrites its single field on exactly the
      maximal run of the parent-chain from @{term u} on which its guard holds (a @{const takeWhile}
      over @{term "follow P u"}), and leaves it elsewhere.  These are the same $\mu$-induction as the
      field lemmas above; together with them they pin @{const lsuc}/@{const snum} for clauses E/H/I/J.\<close>
lemma succ_vin_loop_snum:
  assumes ps: "parent_spec P"
  shows "prnt S = P \<longrightarrow>
    snum (succ_vin_loop S u jn d) =
      (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow P u)) then snum S x + d else snum S x)"
proof (induction arbitrary: S rule: parent_spec_i.follow.pinduct[OF follow_dom_ps[OF ps, of u]])
  case (1 u)
  show ?case
  proof (intro impI)
    assume pS: "prnt S = P"
    show "snum (succ_vin_loop S u jn d) =
      (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow P u)) then snum S x + d else snum S x)"
    proof (cases "u = jn")
      case True
      have "succ_vin_loop S u jn d = S" using True by (subst succ_vin_loop.simps) simp
      moreover have "takeWhile (\<lambda>y. y \<noteq> jn) (follow P jn) = []"
        by (subst follow_ps_simps[OF ps]) (simp split: option.splits)
      ultimately show ?thesis using True by (simp add: fun_eq_iff)
    next
      case False
      define S' where "S' = S\<lparr>snum := (snum S)(u := snum S u + d)\<rparr>"
      have pS': "prnt S' = P" using pS by (simp add: S'_def)
      show ?thesis
      proof (cases "P u")
        case None
        hence fu: "follow P u = [u]" by (subst follow_ps_simps[OF ps]) simp
        have "prnt S' u = None" using pS' None by simp
        hence "succ_vin_loop S u jn d = S'"
          using False by (subst succ_vin_loop.simps) (simp add: S'_def Let_def)
        thus ?thesis using False fu by (simp add: S'_def fun_eq_iff)
      next
        case (Some par)
        hence pSu': "prnt S' u = Some par" using pS' by simp
        have rec: "succ_vin_loop S u jn d = succ_vin_loop S' par jn d"
          using False pSu' by (subst succ_vin_loop.simps) (simp add: S'_def Let_def)
        have fu: "follow P u = u # follow P par"
          using Some by (subst follow_ps_simps[OF ps]) simp
        have unotin: "u \<notin> set (follow P par)"
          using follow_distinct_ps[OF ps, of u] fu by simp
        have unotinTW: "u \<notin> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow P par))"
          using unotin set_takeWhileD by fastforce
        have IH: "snum (succ_vin_loop S' par jn d) =
            (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow P par)) then snum S' x + d else snum S' x)"
          using 1(2)[OF Some, of S'] pS' by simp
        have tw: "set (takeWhile (\<lambda>y. y \<noteq> jn) (follow P u))
                  = insert u (set (takeWhile (\<lambda>y. y \<noteq> jn) (follow P par)))"
          using fu False by simp
        show ?thesis
        proof (rule ext)
          fix x
          show "snum (succ_vin_loop S u jn d) x =
            (if x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow P u)) then snum S x + d else snum S x)"
            using rec IH tw unotinTW
            by (auto simp: S'_def)
        qed
      qed
    qed
  qed
qed

lemma succ_vout_loop_snum:
  assumes ps: "parent_spec P"
  shows "prnt S = P \<longrightarrow>
    snum (succ_vout_loop S u jn d) =
      (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow P u)) then snum S x - d else snum S x)"
proof (induction arbitrary: S rule: parent_spec_i.follow.pinduct[OF follow_dom_ps[OF ps, of u]])
  case (1 u)
  show ?case
  proof (intro impI)
    assume pS: "prnt S = P"
    show "snum (succ_vout_loop S u jn d) =
      (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow P u)) then snum S x - d else snum S x)"
    proof (cases "u = jn")
      case True
      have "succ_vout_loop S u jn d = S" using True by (subst succ_vout_loop.simps) simp
      moreover have "takeWhile (\<lambda>y. y \<noteq> jn) (follow P jn) = []"
        by (subst follow_ps_simps[OF ps]) (simp split: option.splits)
      ultimately show ?thesis using True by (simp add: fun_eq_iff)
    next
      case False
      define S' where "S' = S\<lparr>snum := (snum S)(u := snum S u - d)\<rparr>"
      have pS': "prnt S' = P" using pS by (simp add: S'_def)
      show ?thesis
      proof (cases "P u")
        case None
        hence fu: "follow P u = [u]" by (subst follow_ps_simps[OF ps]) simp
        have "prnt S' u = None" using pS' None by simp
        hence "succ_vout_loop S u jn d = S'"
          using False by (subst succ_vout_loop.simps) (simp add: S'_def Let_def)
        thus ?thesis using False fu by (simp add: S'_def fun_eq_iff)
      next
        case (Some par)
        hence pSu': "prnt S' u = Some par" using pS' by simp
        have rec: "succ_vout_loop S u jn d = succ_vout_loop S' par jn d"
          using False pSu' by (subst succ_vout_loop.simps) (simp add: S'_def Let_def)
        have fu: "follow P u = u # follow P par"
          using Some by (subst follow_ps_simps[OF ps]) simp
        have unotin: "u \<notin> set (follow P par)"
          using follow_distinct_ps[OF ps, of u] fu by simp
        have unotinTW: "u \<notin> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow P par))"
          using unotin set_takeWhileD by fastforce
        have IH: "snum (succ_vout_loop S' par jn d) =
            (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow P par)) then snum S' x - d else snum S' x)"
          using 1(2)[OF Some, of S'] pS' by simp
        have tw: "set (takeWhile (\<lambda>y. y \<noteq> jn) (follow P u))
                  = insert u (set (takeWhile (\<lambda>y. y \<noteq> jn) (follow P par)))"
          using fu False by simp
        show ?thesis
        proof (rule ext)
          fix x
          show "snum (succ_vout_loop S u jn d) x =
            (if x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow P u)) then snum S x - d else snum S x)"
            using rec IH tw unotinTW
            by (auto simp: S'_def)
        qed
      qed
    qed
  qed
qed

lemma last_vin_loop_lsuc:
  assumes ps: "parent_spec P"
  shows "prnt S = P \<longrightarrow>
    lsuc (last_vin_loop S u jv lso) =
      (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. lsuc S y = jv) (follow P u)) then lso else lsuc S x)"
proof (induction arbitrary: S rule: parent_spec_i.follow.pinduct[OF follow_dom_ps[OF ps, of u]])
  case (1 u)
  show ?case
  proof (intro impI)
    assume pS: "prnt S = P"
    show "lsuc (last_vin_loop S u jv lso) =
      (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. lsuc S y = jv) (follow P u)) then lso else lsuc S x)"
    proof (cases "lsuc S u = jv")
      case False
      have "last_vin_loop S u jv lso = S" using False by (subst last_vin_loop.simps) simp
      moreover have "takeWhile (\<lambda>y. lsuc S y = jv) (follow P u) = []"
        using False by (subst follow_ps_simps[OF ps]) (simp split: option.splits)
      ultimately show ?thesis by (simp add: fun_eq_iff)
    next
      case True
      define S' where "S' = S\<lparr>lsuc := (lsuc S)(u := lso)\<rparr>"
      have pS': "prnt S' = P" using pS by (simp add: S'_def)
      show ?thesis
      proof (cases "P u")
        case None
        hence fu: "follow P u = [u]" by (subst follow_ps_simps[OF ps]) simp
        have "prnt S' u = None" using pS' None by simp
        hence "last_vin_loop S u jv lso = S'"
          using True by (subst last_vin_loop.simps) (simp add: S'_def Let_def)
        thus ?thesis using True fu by (simp add: S'_def fun_eq_iff)
      next
        case (Some par)
        hence pSu': "prnt S' u = Some par" using pS' by simp
        have rec: "last_vin_loop S u jv lso = last_vin_loop S' par jv lso"
          using True pSu' by (subst last_vin_loop.simps) (simp add: S'_def Let_def)
        have fu: "follow P u = u # follow P par"
          using Some by (subst follow_ps_simps[OF ps]) simp
        have unotin: "u \<notin> set (follow P par)"
          using follow_distinct_ps[OF ps, of u] fu by simp
        have IH: "lsuc (last_vin_loop S' par jv lso) =
            (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. lsuc S' y = jv) (follow P par)) then lso else lsuc S' x)"
          using 1(2)[OF Some, of S'] pS' by simp
        have TWeq: "takeWhile (\<lambda>y. lsuc S' y = jv) (follow P par)
                    = takeWhile (\<lambda>y. lsuc S y = jv) (follow P par)"
          by (rule takeWhile_cong[OF refl]) (use unotin in \<open>auto simp: S'_def\<close>)
        have unotinTW: "u \<notin> set (takeWhile (\<lambda>y. lsuc S y = jv) (follow P par))"
          using unotin set_takeWhileD by fastforce
        have tw: "set (takeWhile (\<lambda>y. lsuc S y = jv) (follow P u))
                  = insert u (set (takeWhile (\<lambda>y. lsuc S y = jv) (follow P par)))"
          using fu True by simp
        show ?thesis
        proof (rule ext)
          fix x
          show "lsuc (last_vin_loop S u jv lso) x =
            (if x \<in> set (takeWhile (\<lambda>y. lsuc S y = jv) (follow P u)) then lso else lsuc S x)"
            using rec IH TWeq tw unotinTW by (auto simp: S'_def)
        qed
      qed
    qed
  qed
qed

lemma last_vout_loop_lsuc:
  assumes ps: "parent_spec P"
  shows "prnt S = P \<longrightarrow>
    lsuc (last_vout_loop S u stp gv sv) =
      (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. Some y \<noteq> stp \<and> lsuc S y = gv) (follow P u)) then sv else lsuc S x)"
proof (induction arbitrary: S rule: parent_spec_i.follow.pinduct[OF follow_dom_ps[OF ps, of u]])
  case (1 u)
  show ?case
  proof (intro impI)
    assume pS: "prnt S = P"
    show "lsuc (last_vout_loop S u stp gv sv) =
      (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. Some y \<noteq> stp \<and> lsuc S y = gv) (follow P u)) then sv else lsuc S x)"
    proof (cases "Some u = stp \<or> lsuc S u \<noteq> gv")
      case True
      have "last_vout_loop S u stp gv sv = S" using True by (subst last_vout_loop.simps) simp
      moreover have "takeWhile (\<lambda>y. Some y \<noteq> stp \<and> lsuc S y = gv) (follow P u) = []"
        using True follow_hd_ps[OF ps, of u] follow_ne_ps[OF ps, of u]
        by (cases "follow P u") auto
      ultimately show ?thesis by (simp add: fun_eq_iff)
    next
      case False
      hence guard: "Some u \<noteq> stp \<and> lsuc S u = gv" by simp
      define S' where "S' = S\<lparr>lsuc := (lsuc S)(u := sv)\<rparr>"
      have pS': "prnt S' = P" using pS by (simp add: S'_def)
      show ?thesis
      proof (cases "P u")
        case None
        hence fu: "follow P u = [u]" by (subst follow_ps_simps[OF ps]) simp
        have "prnt S' u = None" using pS' None by simp
        hence "last_vout_loop S u stp gv sv = S'"
          using False by (subst last_vout_loop.simps) (simp add: S'_def Let_def)
        thus ?thesis using guard fu by (simp add: S'_def fun_eq_iff)
      next
        case (Some par)
        hence pSu': "prnt S' u = Some par" using pS' by simp
        have rec: "last_vout_loop S u stp gv sv = last_vout_loop S' par stp gv sv"
          using False pSu' by (subst last_vout_loop.simps) (simp add: S'_def Let_def)
        have fu: "follow P u = u # follow P par"
          using Some by (subst follow_ps_simps[OF ps]) simp
        have unotin: "u \<notin> set (follow P par)"
          using follow_distinct_ps[OF ps, of u] fu by simp
        have IH: "lsuc (last_vout_loop S' par stp gv sv) =
            (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. Some y \<noteq> stp \<and> lsuc S' y = gv) (follow P par)) then sv else lsuc S' x)"
          using 1(2)[OF Some, of S'] pS' by simp
        have TWeq: "takeWhile (\<lambda>y. Some y \<noteq> stp \<and> lsuc S' y = gv) (follow P par)
                    = takeWhile (\<lambda>y. Some y \<noteq> stp \<and> lsuc S y = gv) (follow P par)"
          by (rule takeWhile_cong[OF refl]) (use unotin in \<open>auto simp: S'_def\<close>)
        have unotinTW: "u \<notin> set (takeWhile (\<lambda>y. Some y \<noteq> stp \<and> lsuc S y = gv) (follow P par))"
          using unotin set_takeWhileD by fastforce
        have tw: "set (takeWhile (\<lambda>y. Some y \<noteq> stp \<and> lsuc S y = gv) (follow P u))
                  = insert u (set (takeWhile (\<lambda>y. Some y \<noteq> stp \<and> lsuc S y = gv) (follow P par)))"
          using fu guard by simp
        show ?thesis
        proof (rule ext)
          fix x
          show "lsuc (last_vout_loop S u stp gv sv) x =
            (if x \<in> set (takeWhile (\<lambda>y. Some y \<noteq> stp \<and> lsuc S y = gv) (follow P u)) then sv else lsuc S x)"
            using rec IH TWeq tw unotinTW by (auto simp: S'_def)
        qed
      qed
    qed
  qed
qed

text \<open>@{const stem_num_loop} recomputes both @{const snum} (a telescoping subtree size) and
      @{const lsuc} (set to @{term tls} on the parents of the walked stem).  Two helper facts:
      a parent along a root-path lands in the strict tail (so it is fresh), and every node strictly
      below a reachable @{term iv} still has a parent.\<close>
lemma follow_parent_in_tail:
  assumes ps: "parent_spec P" and xin: "x \<in> set (follow P u)" and Px: "P x = Some y"
  shows "y \<in> set (follow P u) \<and> y \<noteq> u"
proof -
  from xin obtain A B where AB: "follow P u = A @ x # B"
    by (metis split_list)
  have fx: "follow P x = x # B" using follow_append_ps[OF ps AB] by auto
  have "follow P x = x # follow P y" using Px by (subst follow_ps_simps[OF ps]) simp
  hence Bf: "B = follow P y" using fx by simp
  have yB: "y \<in> set B" using Bf follow_hd_ps[OF ps, of y] follow_ne_ps[OF ps, of y]
    by (metis hd_in_set)
  hence yin: "y \<in> set (follow P u)" using AB by simp
  have dist: "distinct (follow P u)" using follow_distinct_ps[OF ps] by auto
  have uhd: "u = hd (follow P u)" using follow_hd_ps[OF ps] by simp
  have "u \<in> set (A @ [x])"
  proof (cases A)
    case Nil thus ?thesis using uhd AB by simp
  next
    case (Cons a A') thus ?thesis using uhd AB by simp
  qed
  moreover have "set (A @ [x]) \<inter> set B = {}" using dist AB by auto
  ultimately have "u \<notin> set B" by auto
  hence "y \<noteq> u" using yB by auto
  thus ?thesis using yin by simp
qed

lemma takeWhile_iv_parent_defined:
  assumes ps: "parent_spec P" and ivin: "iv \<in> set (follow P u)"
      and w: "w \<in> set (takeWhile (\<lambda>y. y \<noteq> iv) (follow P u))"
  shows "P w \<noteq> None"
proof -
  have split: "follow P u = takeWhile (\<lambda>y. y \<noteq> iv) (follow P u) @ dropWhile (\<lambda>y. y \<noteq> iv) (follow P u)"
    by simp
  have dw: "dropWhile (\<lambda>y. y \<noteq> iv) (follow P u) \<noteq> []"
    using ivin by (simp add: dropWhile_eq_Nil_conv)
  from w obtain C E where CE: "takeWhile (\<lambda>y. y \<noteq> iv) (follow P u) = C @ w # E"
    by (metis split_list)
  have decomp: "follow P u = C @ w # (E @ dropWhile (\<lambda>y. y \<noteq> iv) (follow P u))"
    using split CE by simp
  have fw: "follow P w = w # (E @ dropWhile (\<lambda>y. y \<noteq> iv) (follow P u))"
    using follow_append_ps[OF ps decomp] by auto
  have "follow P w \<noteq> [w]" using fw dw by simp
  thus ?thesis by (subst (asm) follow_ps_simps[OF ps]) (auto split: option.splits)
qed

lemma stem_num_loop_lsuc:
  assumes ps: "parent_spec P"
  shows "prnt S = P \<longrightarrow> iv \<in> set (follow P u) \<longrightarrow>
    lsuc (stem_num_loop S sn0 u iv acc tls) =
      (\<lambda>x. if x \<in> (\<lambda>y. the (P y)) ` set (takeWhile (\<lambda>y. y \<noteq> iv) (follow P u)) then tls else lsuc S x)"
proof (induction arbitrary: S acc rule: parent_spec_i.follow.pinduct[OF follow_dom_ps[OF ps, of u]])
  case (1 u)
  show ?case
  proof (intro impI)
    assume pS: "prnt S = P" and ivin: "iv \<in> set (follow P u)"
    show "lsuc (stem_num_loop S sn0 u iv acc tls) =
      (\<lambda>x. if x \<in> (\<lambda>y. the (P y)) ` set (takeWhile (\<lambda>y. y \<noteq> iv) (follow P u)) then tls else lsuc S x)"
    proof (cases "u = iv")
      case True
      have "stem_num_loop S sn0 u iv acc tls = S" using True by (subst stem_num_loop.simps) simp
      moreover have "takeWhile (\<lambda>y. y \<noteq> iv) (follow P iv) = []"
        by (subst follow_ps_simps[OF ps]) (simp split: option.splits)
      ultimately show ?thesis using True by (simp add: fun_eq_iff)
    next
      case False
      have PuNN: "P u \<noteq> None"
      proof
        assume "P u = None"
        hence "follow P u = [u]" by (subst follow_ps_simps[OF ps]) simp
        thus False using ivin False by simp
      qed
      then obtain par where Pu: "P u = Some par" by auto
      have ivpar: "iv \<in> set (follow P par)"
        using ivin False Pu by (subst (asm) follow_ps_simps[OF ps]) simp
      define acc' where "acc' = acc + (sn0 u - sn0 par)"
      define S' where "S' = S\<lparr>snum := (snum S)(u := acc'), lsuc := (lsuc S)(par := tls)\<rparr>"
      have pSu: "prnt S u = Some par" using pS Pu by simp
      have pS': "prnt S' = P" using pS by (simp add: S'_def)
      have rec: "stem_num_loop S sn0 u iv acc tls = stem_num_loop S' sn0 par iv acc' tls"
        using False pSu by (subst stem_num_loop.simps) (simp add: acc'_def S'_def Let_def)
      have IH: "lsuc (stem_num_loop S' sn0 par iv acc' tls) =
          (\<lambda>x. if x \<in> (\<lambda>y. the (P y)) ` set (takeWhile (\<lambda>y. y \<noteq> iv) (follow P par)) then tls else lsuc S' x)"
        using 1(2)[OF Pu, of S' acc'] pS' ivpar by simp
      have fu: "follow P u = u # follow P par"
        using Pu by (subst follow_ps_simps[OF ps]) simp
      have img: "(\<lambda>y. the (P y)) ` set (takeWhile (\<lambda>y. y \<noteq> iv) (follow P u))
                 = insert par ((\<lambda>y. the (P y)) ` set (takeWhile (\<lambda>y. y \<noteq> iv) (follow P par)))"
        using fu False Pu by simp
      show ?thesis
      proof (rule ext)
        fix x
        show "lsuc (stem_num_loop S sn0 u iv acc tls) x =
          (if x \<in> (\<lambda>y. the (P y)) ` set (takeWhile (\<lambda>y. y \<noteq> iv) (follow P u)) then tls else lsuc S x)"
          using rec IH img by (auto simp: S'_def)
      qed
    qed
  qed
qed

lemma stem_num_loop_snum:
  assumes ps: "parent_spec P"
  shows "prnt S = P \<longrightarrow> iv \<in> set (follow P u)
    \<longrightarrow> (\<forall> y \<in> set (takeWhile (\<lambda>z. z \<noteq> iv) (follow P u)). P y \<noteq> None \<longrightarrow> sn0 (the (P y)) \<le> sn0 y)
    \<longrightarrow> snum (stem_num_loop S sn0 u iv acc tls) =
      (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. y \<noteq> iv) (follow P u))
           then acc + sn0 u - sn0 (the (P x)) else snum S x)"
proof (induction arbitrary: S acc rule: parent_spec_i.follow.pinduct[OF follow_dom_ps[OF ps, of u]])
  case (1 u)
  show ?case
  proof (intro impI)
    assume pS: "prnt S = P" and ivin: "iv \<in> set (follow P u)"
       and mono: "\<forall> y \<in> set (takeWhile (\<lambda>z. z \<noteq> iv) (follow P u)). P y \<noteq> None \<longrightarrow> sn0 (the (P y)) \<le> sn0 y"
    show "snum (stem_num_loop S sn0 u iv acc tls) =
      (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. y \<noteq> iv) (follow P u))
           then acc + sn0 u - sn0 (the (P x)) else snum S x)"
    proof (cases "u = iv")
      case True
      have "stem_num_loop S sn0 u iv acc tls = S" using True by (subst stem_num_loop.simps) simp
      moreover have "takeWhile (\<lambda>y. y \<noteq> iv) (follow P iv) = []"
        by (subst follow_ps_simps[OF ps]) (simp split: option.splits)
      ultimately show ?thesis using True by (simp add: fun_eq_iff)
    next
      case False
      have PuNN: "P u \<noteq> None"
      proof
        assume "P u = None"
        hence "follow P u = [u]" by (subst follow_ps_simps[OF ps]) simp
        thus False using ivin False by simp
      qed
      then obtain par where Pu: "P u = Some par" by auto
      have fu: "follow P u = u # follow P par"
        using Pu by (subst follow_ps_simps[OF ps]) simp
      have tw: "set (takeWhile (\<lambda>y. y \<noteq> iv) (follow P u))
                = insert u (set (takeWhile (\<lambda>y. y \<noteq> iv) (follow P par)))"
        using fu False by simp
      have monou: "sn0 par \<le> sn0 u" using mono tw Pu by auto
      have ivpar: "iv \<in> set (follow P par)"
        using ivin False Pu by (subst (asm) follow_ps_simps[OF ps]) simp
      have monopar: "\<forall> y \<in> set (takeWhile (\<lambda>z. z \<noteq> iv) (follow P par)). P y \<noteq> None \<longrightarrow> sn0 (the (P y)) \<le> sn0 y"
        using mono tw by simp
      have unotin: "u \<notin> set (follow P par)"
        using follow_distinct_ps[OF ps, of u] fu by simp
      define acc' where "acc' = acc + (sn0 u - sn0 par)"
      define S' where "S' = S\<lparr>snum := (snum S)(u := acc'), lsuc := (lsuc S)(par := tls)\<rparr>"
      have pSu: "prnt S u = Some par" using pS Pu by simp
      have pS': "prnt S' = P" using pS by (simp add: S'_def)
      have rec: "stem_num_loop S sn0 u iv acc tls = stem_num_loop S' sn0 par iv acc' tls"
        using False pSu by (subst stem_num_loop.simps) (simp add: acc'_def S'_def Let_def)
      have IH: "snum (stem_num_loop S' sn0 par iv acc' tls) =
          (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. y \<noteq> iv) (follow P par))
               then acc' + sn0 par - sn0 (the (P x)) else snum S' x)"
        using 1(2)[OF Pu, of S' acc'] pS' ivpar monopar by simp
      have accid: "acc' + sn0 par = acc + sn0 u" using acc'_def monou by simp
      have unotinTW: "u \<notin> set (takeWhile (\<lambda>y. y \<noteq> iv) (follow P par))"
        using unotin set_takeWhileD by fastforce
      show ?thesis
      proof (rule ext)
        fix x
        show "snum (stem_num_loop S sn0 u iv acc tls) x =
          (if x \<in> set (takeWhile (\<lambda>y. y \<noteq> iv) (follow P u))
           then acc + sn0 u - sn0 (the (P x)) else snum S x)"
          using rec IH accid tw unotinTW Pu by (auto simp: S'_def acc'_def monou)
      qed
    qed
  qed
qed


subsection \<open>Fused decoration loops: single-pass equivalents of the four fix-up loops\<close>

text \<open>@{const fused_vin_loop} and @{const fused_vout_loop} each traverse a parent chain once while
      touching both @{const lsuc} and @{const snum} (a cache-friendly single pass).  We show every
      field of the fused walk agrees with the composition of the two original loops, via the
      closed-form @{const takeWhile} value lemmas above, and conclude the equivalences
      \<open>fused_vin_loop_eq\<close> / \<open>fused_vout_loop_eq\<close>.  The one commutation
      \<open>svin_lvout_commute\<close> (moving @{const succ_vin_loop} past @{const last_vout_loop},
      disjoint fields) reconciles the fused ordering with the interleaved original ordering in
      \<open>update_tree_tail_eq\<close>.\<close>

lemma fused_vin_loop_lsuc:
  assumes ps: "parent_spec P"
  shows "prnt S = P \<longrightarrow> lsuc (fused_vin_loop S u jv jn lso d la sa) = (\<lambda>x. if la \<and> x \<in> set (takeWhile (\<lambda>y. lsuc S y = jv) (follow P u)) then lso else lsuc S x)"
proof (induction arbitrary: S la sa rule: parent_spec_i.follow.pinduct[OF follow_dom_ps[OF ps, of u]])
  case (1 u)
  show ?case
  proof (intro impI)
    assume pS: "prnt S = P"
    define la' where "la' = (la \<and> lsuc S u = jv)"
    define sa' where "sa' = (sa \<and> u \<noteq> jn)"
    define S' where "S' = S\<lparr>lsuc := (if la' then (lsuc S)(u := lso) else lsuc S), snum := (if sa' then (snum S)(u := snum S u + d) else snum S)\<rparr>"
    have pS': "prnt S' = P" using pS by (simp add: S'_def)
    have lsucS': "lsuc S' = (if la' then (lsuc S)(u := lso) else lsuc S)" by (simp add: S'_def)
    have unfold: "fused_vin_loop S u jv jn lso d la sa = (if \<not> la' \<and> \<not> sa' then S else (case prnt S' u of None \<Rightarrow> S' | Some par \<Rightarrow> fused_vin_loop S' par jv jn lso d la' sa'))" by (subst fused_vin_loop.simps) (simp only: la'_def sa'_def S'_def Let_def)
    show "lsuc (fused_vin_loop S u jv jn lso d la sa) = (\<lambda>x. if la \<and> x \<in> set (takeWhile (\<lambda>y. lsuc S y = jv) (follow P u)) then lso else lsuc S x)"
    proof (cases "\<not> la' \<and> \<not> sa'")
      case True
      have f: "fused_vin_loop S u jv jn lso d la sa = S" using unfold True by simp
      have empt: "la \<longrightarrow> takeWhile (\<lambda>y. lsuc S y = jv) (follow P u) = []"
      proof
        assume "la" hence "lsuc S u \<noteq> jv" using True by (auto simp: la'_def)
        thus "takeWhile (\<lambda>y. lsuc S y = jv) (follow P u) = []" using follow_hd_ps[OF ps, of u] follow_ne_ps[OF ps, of u] by (cases "follow P u") auto
      qed
      show ?thesis using f empt by (auto simp: fun_eq_iff)
    next
      case False
      hence notboth: "\<not> (\<not> la' \<and> \<not> sa')" by simp
      show ?thesis
      proof (cases "P u")
        case None
        hence fu: "follow P u = [u]" by (subst follow_ps_simps[OF ps]) simp
        have pS'u: "prnt S' u = None" using pS' None by simp
        have f: "fused_vin_loop S u jv jn lso d la sa = S'" using unfold notboth pS'u by simp
        show ?thesis using f fu lsucS' by (auto simp: la'_def fun_eq_iff)
      next
        case (Some par)
        have pS'u: "prnt S' u = Some par" using pS' Some by simp
        have f: "fused_vin_loop S u jv jn lso d la sa = fused_vin_loop S' par jv jn lso d la' sa'" using unfold notboth pS'u by simp
        have fu: "follow P u = u # follow P par" using Some by (subst follow_ps_simps[OF ps]) simp
        have unotin: "u \<notin> set (follow P par)" using follow_distinct_ps[OF ps, of u] fu by simp
        have IH: "lsuc (fused_vin_loop S' par jv jn lso d la' sa') = (\<lambda>x. if la' \<and> x \<in> set (takeWhile (\<lambda>y. lsuc S' y = jv) (follow P par)) then lso else lsuc S' x)" using 1(2)[OF Some, of S' la' sa'] pS' by simp
        have TWeq: "takeWhile (\<lambda>y. lsuc S' y = jv) (follow P par) = takeWhile (\<lambda>y. lsuc S y = jv) (follow P par)" by (rule takeWhile_cong[OF refl]) (use unotin lsucS' in \<open>auto simp: S'_def\<close>)
        have unotinTW: "u \<notin> set (takeWhile (\<lambda>y. lsuc S y = jv) (follow P par))" using unotin set_takeWhileD by fastforce
        have lsuc_eq: "lsuc (fused_vin_loop S u jv jn lso d la sa) = (\<lambda>x. if la' \<and> x \<in> set (takeWhile (\<lambda>y. lsuc S y = jv) (follow P par)) then lso else lsuc S' x)" using f IH TWeq by simp
        show ?thesis
        proof (cases la')
          case True
          hence laT: "la" and gvT: "lsuc S u = jv" by (auto simp: la'_def)
          have tw_u: "takeWhile (\<lambda>y. lsuc S y = jv) (follow P u) = u # takeWhile (\<lambda>y. lsuc S y = jv) (follow P par)" using fu gvT by simp
          have lS': "lsuc S' = (lsuc S)(u := lso)" using True lsucS' by simp
          show ?thesis using lsuc_eq True laT tw_u unotinTW lS' by (auto simp: fun_eq_iff)
        next
          case False
          hence lS': "lsuc S' = lsuc S" using lsucS' by simp
          have "la \<longrightarrow> lsuc S u \<noteq> jv" using False by (auto simp: la'_def)
          hence tw_empty: "la \<longrightarrow> takeWhile (\<lambda>y. lsuc S y = jv) (follow P u) = []" using fu by auto
          show ?thesis using lsuc_eq False lS' tw_empty by (auto simp: fun_eq_iff)
        qed
      qed
    qed
  qed
qed

lemma fused_vin_loop_snum:
  assumes ps: "parent_spec P"
  shows "prnt S = P \<longrightarrow> snum (fused_vin_loop S u jv jn lso d la sa) = (\<lambda>x. if sa \<and> x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow P u)) then snum S x + d else snum S x)"
proof (induction arbitrary: S la sa rule: parent_spec_i.follow.pinduct[OF follow_dom_ps[OF ps, of u]])
  case (1 u)
  show ?case
  proof (intro impI)
    assume pS: "prnt S = P"
    define la' where "la' = (la \<and> lsuc S u = jv)"
    define sa' where "sa' = (sa \<and> u \<noteq> jn)"
    define S' where "S' = S\<lparr>lsuc := (if la' then (lsuc S)(u := lso) else lsuc S), snum := (if sa' then (snum S)(u := snum S u + d) else snum S)\<rparr>"
    have pS': "prnt S' = P" using pS by (simp add: S'_def)
    have snumS': "snum S' = (if sa' then (snum S)(u := snum S u + d) else snum S)" by (simp add: S'_def)
    have unfold: "fused_vin_loop S u jv jn lso d la sa = (if \<not> la' \<and> \<not> sa' then S else (case prnt S' u of None \<Rightarrow> S' | Some par \<Rightarrow> fused_vin_loop S' par jv jn lso d la' sa'))" by (subst fused_vin_loop.simps) (simp only: la'_def sa'_def S'_def Let_def)
    show "snum (fused_vin_loop S u jv jn lso d la sa) = (\<lambda>x. if sa \<and> x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow P u)) then snum S x + d else snum S x)"
    proof (cases "\<not> la' \<and> \<not> sa'")
      case True
      have f: "fused_vin_loop S u jv jn lso d la sa = S" using unfold True by simp
      have empt: "sa \<longrightarrow> takeWhile (\<lambda>y. y \<noteq> jn) (follow P u) = []"
      proof
        assume "sa" hence "u = jn" using True by (auto simp: sa'_def)
        thus "takeWhile (\<lambda>y. y \<noteq> jn) (follow P u) = []" using follow_hd_ps[OF ps, of u] follow_ne_ps[OF ps, of u] by (cases "follow P u") auto
      qed
      show ?thesis using f empt by (auto simp: fun_eq_iff)
    next
      case False
      hence notboth: "\<not> (\<not> la' \<and> \<not> sa')" by simp
      show ?thesis
      proof (cases "P u")
        case None
        hence fu: "follow P u = [u]" by (subst follow_ps_simps[OF ps]) simp
        have pS'u: "prnt S' u = None" using pS' None by simp
        have f: "fused_vin_loop S u jv jn lso d la sa = S'" using unfold notboth pS'u by simp
        show ?thesis using f fu snumS' by (auto simp: sa'_def fun_eq_iff)
      next
        case (Some par)
        have pS'u: "prnt S' u = Some par" using pS' Some by simp
        have f: "fused_vin_loop S u jv jn lso d la sa = fused_vin_loop S' par jv jn lso d la' sa'" using unfold notboth pS'u by simp
        have fu: "follow P u = u # follow P par" using Some by (subst follow_ps_simps[OF ps]) simp
        have unotin: "u \<notin> set (follow P par)" using follow_distinct_ps[OF ps, of u] fu by simp
        have unotinTW: "u \<notin> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow P par))" using unotin set_takeWhileD by fastforce
        have IH: "snum (fused_vin_loop S' par jv jn lso d la' sa') = (\<lambda>x. if sa' \<and> x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow P par)) then snum S' x + d else snum S' x)" using 1(2)[OF Some, of S' la' sa'] pS' by simp
        have snum_eq: "snum (fused_vin_loop S u jv jn lso d la sa) = (\<lambda>x. if sa' \<and> x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow P par)) then snum S' x + d else snum S' x)" using f IH by simp
        show ?thesis
        proof (cases sa')
          case True
          hence saT: "sa" and une: "u \<noteq> jn" by (auto simp: sa'_def)
          have tw_u: "takeWhile (\<lambda>y. y \<noteq> jn) (follow P u) = u # takeWhile (\<lambda>y. y \<noteq> jn) (follow P par)" using fu une by simp
          have sS': "snum S' = (snum S)(u := snum S u + d)" using True snumS' by simp
          show ?thesis using snum_eq True saT tw_u unotinTW sS' by (auto simp: fun_eq_iff)
        next
          case False
          hence sS': "snum S' = snum S" using snumS' by simp
          have "sa \<longrightarrow> u = jn" using False by (auto simp: sa'_def)
          hence tw_empty: "sa \<longrightarrow> takeWhile (\<lambda>y. y \<noteq> jn) (follow P u) = []" using fu by auto
          show ?thesis using snum_eq False sS' tw_empty by (auto simp: fun_eq_iff)
        qed
      qed
    qed
  qed
qed

lemma fused_vin_loop_fields:
  assumes ps: "parent_spec P"
  shows "prnt S = P \<longrightarrow> (prnt (fused_vin_loop S u jv jn lso d la sa) = P \<and> thrd (fused_vin_loop S u jv jn lso d la sa) = thrd S \<and> rvth (fused_vin_loop S u jv jn lso d la sa) = rvth S)"
proof (induction arbitrary: S la sa rule: parent_spec_i.follow.pinduct[OF follow_dom_ps[OF ps, of u]])
  case (1 u)
  show ?case
  proof (intro impI)
    assume pS: "prnt S = P"
    define la' where "la' = (la \<and> lsuc S u = jv)"
    define sa' where "sa' = (sa \<and> u \<noteq> jn)"
    define S' where "S' = S\<lparr>lsuc := (if la' then (lsuc S)(u := lso) else lsuc S), snum := (if sa' then (snum S)(u := snum S u + d) else snum S)\<rparr>"
    have pS': "prnt S' = P" using pS by (simp add: S'_def)
    have thrdS': "thrd S' = thrd S" by (simp add: S'_def)
    have rvthS': "rvth S' = rvth S" by (simp add: S'_def)
    have unfold: "fused_vin_loop S u jv jn lso d la sa = (if \<not> la' \<and> \<not> sa' then S else (case prnt S' u of None \<Rightarrow> S' | Some par \<Rightarrow> fused_vin_loop S' par jv jn lso d la' sa'))" by (subst fused_vin_loop.simps) (simp only: la'_def sa'_def S'_def Let_def)
    show "prnt (fused_vin_loop S u jv jn lso d la sa) = P \<and> thrd (fused_vin_loop S u jv jn lso d la sa) = thrd S \<and> rvth (fused_vin_loop S u jv jn lso d la sa) = rvth S"
    proof (cases "\<not> la' \<and> \<not> sa'")
      case True
      have "fused_vin_loop S u jv jn lso d la sa = S" using unfold True by simp
      thus ?thesis using pS by simp
    next
      case False
      hence notboth: "\<not> (\<not> la' \<and> \<not> sa')" by simp
      show ?thesis
      proof (cases "P u")
        case None
        have pS'u: "prnt S' u = None" using pS' None by simp
        have "fused_vin_loop S u jv jn lso d la sa = S'" using unfold notboth pS'u by simp
        thus ?thesis using pS' thrdS' rvthS' by simp
      next
        case (Some par)
        have pS'u: "prnt S' u = Some par" using pS' Some by simp
        have f: "fused_vin_loop S u jv jn lso d la sa = fused_vin_loop S' par jv jn lso d la' sa'" using unfold notboth pS'u by simp
        have IH: "prnt (fused_vin_loop S' par jv jn lso d la' sa') = P \<and> thrd (fused_vin_loop S' par jv jn lso d la' sa') = thrd S' \<and> rvth (fused_vin_loop S' par jv jn lso d la' sa') = rvth S'" using 1(2)[OF Some, of S' la' sa'] pS' by simp
        show ?thesis using f IH thrdS' rvthS' by simp
      qed
    qed
  qed
qed

lemma fused_vin_loop_eq:
  assumes ps: "parent_spec (prnt S)"
  shows "fused_vin_loop S u jv jn lso d True True = succ_vin_loop (last_vin_loop S u jv lso) u jn d"
proof -
  have LF: "prnt (last_vin_loop S u jv lso) = prnt S \<and> thrd (last_vin_loop S u jv lso) = thrd S \<and> rvth (last_vin_loop S u jv lso) = rvth S \<and> snum (last_vin_loop S u jv lso) = snum S" using last_vin_loop_fields[OF ps, THEN mp, OF refl] by blast
  have snumL: "snum (last_vin_loop S u jv lso) = snum S" using LF by simp
  have LL: "lsuc (last_vin_loop S u jv lso) = (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. lsuc S y = jv) (follow (prnt S) u)) then lso else lsuc S x)" using last_vin_loop_lsuc[OF ps, THEN mp, OF refl] by blast
  have pL: "prnt (last_vin_loop S u jv lso) = prnt S" using LF by simp
  have RF: "prnt (succ_vin_loop (last_vin_loop S u jv lso) u jn d) = prnt S \<and> thrd (succ_vin_loop (last_vin_loop S u jv lso) u jn d) = thrd S \<and> rvth (succ_vin_loop (last_vin_loop S u jv lso) u jn d) = rvth S \<and> lsuc (succ_vin_loop (last_vin_loop S u jv lso) u jn d) = lsuc (last_vin_loop S u jv lso)" using succ_vin_loop_fields[OF ps, THEN mp, OF pL] LF by simp
  have RS: "snum (succ_vin_loop (last_vin_loop S u jv lso) u jn d) = (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow (prnt S) u)) then snum (last_vin_loop S u jv lso) x + d else snum (last_vin_loop S u jv lso) x)" using succ_vin_loop_snum[OF ps, THEN mp, OF pL] by blast
  have RS': "snum (succ_vin_loop (last_vin_loop S u jv lso) u jn d) = (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow (prnt S) u)) then snum S x + d else snum S x)" using RS snumL by (simp only:)
  have FF: "prnt (fused_vin_loop S u jv jn lso d True True) = prnt S \<and> thrd (fused_vin_loop S u jv jn lso d True True) = thrd S \<and> rvth (fused_vin_loop S u jv jn lso d True True) = rvth S" using fused_vin_loop_fields[OF ps, THEN mp, OF refl] by blast
  have FL: "lsuc (fused_vin_loop S u jv jn lso d True True) = (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. lsuc S y = jv) (follow (prnt S) u)) then lso else lsuc S x)" using fused_vin_loop_lsuc[OF ps, THEN mp, OF refl] by simp
  have FS: "snum (fused_vin_loop S u jv jn lso d True True) = (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow (prnt S) u)) then snum S x + d else snum S x)" using fused_vin_loop_snum[OF ps, THEN mp, OF refl] by simp
  show ?thesis
  proof (rule ndtree.equality)
    show "prnt (fused_vin_loop S u jv jn lso d True True) = prnt (succ_vin_loop (last_vin_loop S u jv lso) u jn d)" using FF RF by simp
    show "thrd (fused_vin_loop S u jv jn lso d True True) = thrd (succ_vin_loop (last_vin_loop S u jv lso) u jn d)" using FF RF by simp
    show "rvth (fused_vin_loop S u jv jn lso d True True) = rvth (succ_vin_loop (last_vin_loop S u jv lso) u jn d)" using FF RF by simp
    show "lsuc (fused_vin_loop S u jv jn lso d True True) = lsuc (succ_vin_loop (last_vin_loop S u jv lso) u jn d)" using FL RF LL by simp
    show "snum (fused_vin_loop S u jv jn lso d True True) = snum (succ_vin_loop (last_vin_loop S u jv lso) u jn d)" using FS RS' by simp
    show "ndtree.more (fused_vin_loop S u jv jn lso d True True) = ndtree.more (succ_vin_loop (last_vin_loop S u jv lso) u jn d)" by simp
  qed
qed

lemma fused_vout_loop_lsuc:
  assumes ps: "parent_spec P"
  shows "prnt S = P \<longrightarrow> lsuc (fused_vout_loop S u stp gv sv jn d la sa) = (\<lambda>x. if la \<and> x \<in> set (takeWhile (\<lambda>y. Some y \<noteq> stp \<and> lsuc S y = gv) (follow P u)) then sv else lsuc S x)"
proof (induction arbitrary: S la sa rule: parent_spec_i.follow.pinduct[OF follow_dom_ps[OF ps, of u]])
  case (1 u)
  show ?case
  proof (intro impI)
    assume pS: "prnt S = P"
    define la' where "la' = (la \<and> Some u \<noteq> stp \<and> lsuc S u = gv)"
    define sa' where "sa' = (sa \<and> u \<noteq> jn)"
    define S' where "S' = S\<lparr>lsuc := (if la' then (lsuc S)(u := sv) else lsuc S), snum := (if sa' then (snum S)(u := snum S u - d) else snum S)\<rparr>"
    have pS': "prnt S' = P" using pS by (simp add: S'_def)
    have lsucS': "lsuc S' = (if la' then (lsuc S)(u := sv) else lsuc S)" by (simp add: S'_def)
    have unfold: "fused_vout_loop S u stp gv sv jn d la sa = (if \<not> la' \<and> \<not> sa' then S else (case prnt S' u of None \<Rightarrow> S' | Some par \<Rightarrow> fused_vout_loop S' par stp gv sv jn d la' sa'))" by (subst fused_vout_loop.simps) (simp only: la'_def sa'_def S'_def Let_def)
    show "lsuc (fused_vout_loop S u stp gv sv jn d la sa) = (\<lambda>x. if la \<and> x \<in> set (takeWhile (\<lambda>y. Some y \<noteq> stp \<and> lsuc S y = gv) (follow P u)) then sv else lsuc S x)"
    proof (cases "\<not> la' \<and> \<not> sa'")
      case True
      have f: "fused_vout_loop S u stp gv sv jn d la sa = S" using unfold True by simp
      have empt: "la \<longrightarrow> takeWhile (\<lambda>y. Some y \<noteq> stp \<and> lsuc S y = gv) (follow P u) = []"
      proof
        assume "la" hence "Some u = stp \<or> lsuc S u \<noteq> gv" using True by (auto simp: la'_def)
        thus "takeWhile (\<lambda>y. Some y \<noteq> stp \<and> lsuc S y = gv) (follow P u) = []" using follow_hd_ps[OF ps, of u] follow_ne_ps[OF ps, of u] by (cases "follow P u") auto
      qed
      show ?thesis using f empt by (auto simp: fun_eq_iff)
    next
      case False
      hence notboth: "\<not> (\<not> la' \<and> \<not> sa')" by simp
      show ?thesis
      proof (cases "P u")
        case None
        hence fu: "follow P u = [u]" by (subst follow_ps_simps[OF ps]) simp
        have pS'u: "prnt S' u = None" using pS' None by simp
        have f: "fused_vout_loop S u stp gv sv jn d la sa = S'" using unfold notboth pS'u by simp
        show ?thesis using f fu lsucS' by (auto simp: la'_def fun_eq_iff)
      next
        case (Some par)
        have pS'u: "prnt S' u = Some par" using pS' Some by simp
        have f: "fused_vout_loop S u stp gv sv jn d la sa = fused_vout_loop S' par stp gv sv jn d la' sa'" using unfold notboth pS'u by simp
        have fu: "follow P u = u # follow P par" using Some by (subst follow_ps_simps[OF ps]) simp
        have unotin: "u \<notin> set (follow P par)" using follow_distinct_ps[OF ps, of u] fu by simp
        have IH: "lsuc (fused_vout_loop S' par stp gv sv jn d la' sa') = (\<lambda>x. if la' \<and> x \<in> set (takeWhile (\<lambda>y. Some y \<noteq> stp \<and> lsuc S' y = gv) (follow P par)) then sv else lsuc S' x)" using 1(2)[OF Some, of S' la' sa'] pS' by simp
        have TWeq: "takeWhile (\<lambda>y. Some y \<noteq> stp \<and> lsuc S' y = gv) (follow P par) = takeWhile (\<lambda>y. Some y \<noteq> stp \<and> lsuc S y = gv) (follow P par)" by (rule takeWhile_cong[OF refl]) (use unotin lsucS' in \<open>auto simp: S'_def\<close>)
        have unotinTW: "u \<notin> set (takeWhile (\<lambda>y. Some y \<noteq> stp \<and> lsuc S y = gv) (follow P par))" using unotin set_takeWhileD by fastforce
        have lsuc_eq: "lsuc (fused_vout_loop S u stp gv sv jn d la sa) = (\<lambda>x. if la' \<and> x \<in> set (takeWhile (\<lambda>y. Some y \<noteq> stp \<and> lsuc S y = gv) (follow P par)) then sv else lsuc S' x)" using f IH TWeq by simp
        show ?thesis
        proof (cases la')
          case True
          hence laT: "la" and gvT: "Some u \<noteq> stp \<and> lsuc S u = gv" by (auto simp: la'_def)
          have tw_u: "takeWhile (\<lambda>y. Some y \<noteq> stp \<and> lsuc S y = gv) (follow P u) = u # takeWhile (\<lambda>y. Some y \<noteq> stp \<and> lsuc S y = gv) (follow P par)" using fu gvT by simp
          have lS': "lsuc S' = (lsuc S)(u := sv)" using True lsucS' by simp
          show ?thesis using lsuc_eq True laT tw_u unotinTW lS' by (auto simp: fun_eq_iff)
        next
          case False
          hence lS': "lsuc S' = lsuc S" using lsucS' by simp
          have "la \<longrightarrow> (Some u = stp \<or> lsuc S u \<noteq> gv)" using False by (auto simp: la'_def)
          hence tw_empty: "la \<longrightarrow> takeWhile (\<lambda>y. Some y \<noteq> stp \<and> lsuc S y = gv) (follow P u) = []" using fu by auto
          show ?thesis using lsuc_eq False lS' tw_empty by (auto simp: fun_eq_iff)
        qed
      qed
    qed
  qed
qed

lemma fused_vout_loop_snum:
  assumes ps: "parent_spec P"
  shows "prnt S = P \<longrightarrow> snum (fused_vout_loop S u stp gv sv jn d la sa) = (\<lambda>x. if sa \<and> x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow P u)) then snum S x - d else snum S x)"
proof (induction arbitrary: S la sa rule: parent_spec_i.follow.pinduct[OF follow_dom_ps[OF ps, of u]])
  case (1 u)
  show ?case
  proof (intro impI)
    assume pS: "prnt S = P"
    define la' where "la' = (la \<and> Some u \<noteq> stp \<and> lsuc S u = gv)"
    define sa' where "sa' = (sa \<and> u \<noteq> jn)"
    define S' where "S' = S\<lparr>lsuc := (if la' then (lsuc S)(u := sv) else lsuc S), snum := (if sa' then (snum S)(u := snum S u - d) else snum S)\<rparr>"
    have pS': "prnt S' = P" using pS by (simp add: S'_def)
    have snumS': "snum S' = (if sa' then (snum S)(u := snum S u - d) else snum S)" by (simp add: S'_def)
    have unfold: "fused_vout_loop S u stp gv sv jn d la sa = (if \<not> la' \<and> \<not> sa' then S else (case prnt S' u of None \<Rightarrow> S' | Some par \<Rightarrow> fused_vout_loop S' par stp gv sv jn d la' sa'))" by (subst fused_vout_loop.simps) (simp only: la'_def sa'_def S'_def Let_def)
    show "snum (fused_vout_loop S u stp gv sv jn d la sa) = (\<lambda>x. if sa \<and> x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow P u)) then snum S x - d else snum S x)"
    proof (cases "\<not> la' \<and> \<not> sa'")
      case True
      have f: "fused_vout_loop S u stp gv sv jn d la sa = S" using unfold True by simp
      have empt: "sa \<longrightarrow> takeWhile (\<lambda>y. y \<noteq> jn) (follow P u) = []"
      proof
        assume "sa" hence "u = jn" using True by (auto simp: sa'_def)
        thus "takeWhile (\<lambda>y. y \<noteq> jn) (follow P u) = []" using follow_hd_ps[OF ps, of u] follow_ne_ps[OF ps, of u] by (cases "follow P u") auto
      qed
      show ?thesis using f empt by (auto simp: fun_eq_iff)
    next
      case False
      hence notboth: "\<not> (\<not> la' \<and> \<not> sa')" by simp
      show ?thesis
      proof (cases "P u")
        case None
        hence fu: "follow P u = [u]" by (subst follow_ps_simps[OF ps]) simp
        have pS'u: "prnt S' u = None" using pS' None by simp
        have f: "fused_vout_loop S u stp gv sv jn d la sa = S'" using unfold notboth pS'u by simp
        show ?thesis using f fu snumS' by (auto simp: sa'_def fun_eq_iff)
      next
        case (Some par)
        have pS'u: "prnt S' u = Some par" using pS' Some by simp
        have f: "fused_vout_loop S u stp gv sv jn d la sa = fused_vout_loop S' par stp gv sv jn d la' sa'" using unfold notboth pS'u by simp
        have fu: "follow P u = u # follow P par" using Some by (subst follow_ps_simps[OF ps]) simp
        have unotin: "u \<notin> set (follow P par)" using follow_distinct_ps[OF ps, of u] fu by simp
        have unotinTW: "u \<notin> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow P par))" using unotin set_takeWhileD by fastforce
        have IH: "snum (fused_vout_loop S' par stp gv sv jn d la' sa') = (\<lambda>x. if sa' \<and> x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow P par)) then snum S' x - d else snum S' x)" using 1(2)[OF Some, of S' la' sa'] pS' by simp
        have snum_eq: "snum (fused_vout_loop S u stp gv sv jn d la sa) = (\<lambda>x. if sa' \<and> x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow P par)) then snum S' x - d else snum S' x)" using f IH by simp
        show ?thesis
        proof (cases sa')
          case True
          hence saT: "sa" and une: "u \<noteq> jn" by (auto simp: sa'_def)
          have tw_u: "takeWhile (\<lambda>y. y \<noteq> jn) (follow P u) = u # takeWhile (\<lambda>y. y \<noteq> jn) (follow P par)" using fu une by simp
          have sS': "snum S' = (snum S)(u := snum S u - d)" using True snumS' by simp
          show ?thesis using snum_eq True saT tw_u unotinTW sS' by (auto simp: fun_eq_iff)
        next
          case False
          hence sS': "snum S' = snum S" using snumS' by simp
          have "sa \<longrightarrow> u = jn" using False by (auto simp: sa'_def)
          hence tw_empty: "sa \<longrightarrow> takeWhile (\<lambda>y. y \<noteq> jn) (follow P u) = []" using fu by auto
          show ?thesis using snum_eq False sS' tw_empty by (auto simp: fun_eq_iff)
        qed
      qed
    qed
  qed
qed

lemma fused_vout_loop_fields:
  assumes ps: "parent_spec P"
  shows "prnt S = P \<longrightarrow> (prnt (fused_vout_loop S u stp gv sv jn d la sa) = P \<and> thrd (fused_vout_loop S u stp gv sv jn d la sa) = thrd S \<and> rvth (fused_vout_loop S u stp gv sv jn d la sa) = rvth S)"
proof (induction arbitrary: S la sa rule: parent_spec_i.follow.pinduct[OF follow_dom_ps[OF ps, of u]])
  case (1 u)
  show ?case
  proof (intro impI)
    assume pS: "prnt S = P"
    define la' where "la' = (la \<and> Some u \<noteq> stp \<and> lsuc S u = gv)"
    define sa' where "sa' = (sa \<and> u \<noteq> jn)"
    define S' where "S' = S\<lparr>lsuc := (if la' then (lsuc S)(u := sv) else lsuc S), snum := (if sa' then (snum S)(u := snum S u - d) else snum S)\<rparr>"
    have pS': "prnt S' = P" using pS by (simp add: S'_def)
    have thrdS': "thrd S' = thrd S" by (simp add: S'_def)
    have rvthS': "rvth S' = rvth S" by (simp add: S'_def)
    have unfold: "fused_vout_loop S u stp gv sv jn d la sa = (if \<not> la' \<and> \<not> sa' then S else (case prnt S' u of None \<Rightarrow> S' | Some par \<Rightarrow> fused_vout_loop S' par stp gv sv jn d la' sa'))" by (subst fused_vout_loop.simps) (simp only: la'_def sa'_def S'_def Let_def)
    show "prnt (fused_vout_loop S u stp gv sv jn d la sa) = P \<and> thrd (fused_vout_loop S u stp gv sv jn d la sa) = thrd S \<and> rvth (fused_vout_loop S u stp gv sv jn d la sa) = rvth S"
    proof (cases "\<not> la' \<and> \<not> sa'")
      case True
      have "fused_vout_loop S u stp gv sv jn d la sa = S" using unfold True by simp
      thus ?thesis using pS by simp
    next
      case False
      hence notboth: "\<not> (\<not> la' \<and> \<not> sa')" by simp
      show ?thesis
      proof (cases "P u")
        case None
        have pS'u: "prnt S' u = None" using pS' None by simp
        have "fused_vout_loop S u stp gv sv jn d la sa = S'" using unfold notboth pS'u by simp
        thus ?thesis using pS' thrdS' rvthS' by simp
      next
        case (Some par)
        have pS'u: "prnt S' u = Some par" using pS' Some by simp
        have f: "fused_vout_loop S u stp gv sv jn d la sa = fused_vout_loop S' par stp gv sv jn d la' sa'" using unfold notboth pS'u by simp
        have IH: "prnt (fused_vout_loop S' par stp gv sv jn d la' sa') = P \<and> thrd (fused_vout_loop S' par stp gv sv jn d la' sa') = thrd S' \<and> rvth (fused_vout_loop S' par stp gv sv jn d la' sa') = rvth S'" using 1(2)[OF Some, of S' la' sa'] pS' by simp
        show ?thesis using f IH thrdS' rvthS' by simp
      qed
    qed
  qed
qed

lemma fused_vout_loop_eq:
  assumes ps: "parent_spec (prnt S)"
  shows "fused_vout_loop S u stp gv sv jn d True True = succ_vout_loop (last_vout_loop S u stp gv sv) u jn d"
proof -
  have LF: "prnt (last_vout_loop S u stp gv sv) = prnt S \<and> thrd (last_vout_loop S u stp gv sv) = thrd S \<and> rvth (last_vout_loop S u stp gv sv) = rvth S \<and> snum (last_vout_loop S u stp gv sv) = snum S" using last_vout_loop_fields[OF ps, THEN mp, OF refl] by blast
  have snumL: "snum (last_vout_loop S u stp gv sv) = snum S" using LF by simp
  have LL: "lsuc (last_vout_loop S u stp gv sv) = (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. Some y \<noteq> stp \<and> lsuc S y = gv) (follow (prnt S) u)) then sv else lsuc S x)" using last_vout_loop_lsuc[OF ps, THEN mp, OF refl] by blast
  have pL: "prnt (last_vout_loop S u stp gv sv) = prnt S" using LF by simp
  have RF: "prnt (succ_vout_loop (last_vout_loop S u stp gv sv) u jn d) = prnt S \<and> thrd (succ_vout_loop (last_vout_loop S u stp gv sv) u jn d) = thrd S \<and> rvth (succ_vout_loop (last_vout_loop S u stp gv sv) u jn d) = rvth S \<and> lsuc (succ_vout_loop (last_vout_loop S u stp gv sv) u jn d) = lsuc (last_vout_loop S u stp gv sv)" using succ_vout_loop_fields[OF ps, THEN mp, OF pL] LF by simp
  have RS: "snum (succ_vout_loop (last_vout_loop S u stp gv sv) u jn d) = (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow (prnt S) u)) then snum (last_vout_loop S u stp gv sv) x - d else snum (last_vout_loop S u stp gv sv) x)" using succ_vout_loop_snum[OF ps, THEN mp, OF pL] by blast
  have RS': "snum (succ_vout_loop (last_vout_loop S u stp gv sv) u jn d) = (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow (prnt S) u)) then snum S x - d else snum S x)" using RS snumL by (simp only:)
  have FF: "prnt (fused_vout_loop S u stp gv sv jn d True True) = prnt S \<and> thrd (fused_vout_loop S u stp gv sv jn d True True) = thrd S \<and> rvth (fused_vout_loop S u stp gv sv jn d True True) = rvth S" using fused_vout_loop_fields[OF ps, THEN mp, OF refl] by blast
  have FL: "lsuc (fused_vout_loop S u stp gv sv jn d True True) = (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. Some y \<noteq> stp \<and> lsuc S y = gv) (follow (prnt S) u)) then sv else lsuc S x)" using fused_vout_loop_lsuc[OF ps, THEN mp, OF refl] by simp
  have FS: "snum (fused_vout_loop S u stp gv sv jn d True True) = (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow (prnt S) u)) then snum S x - d else snum S x)" using fused_vout_loop_snum[OF ps, THEN mp, OF refl] by simp
  show ?thesis
  proof (rule ndtree.equality)
    show "prnt (fused_vout_loop S u stp gv sv jn d True True) = prnt (succ_vout_loop (last_vout_loop S u stp gv sv) u jn d)" using FF RF by simp
    show "thrd (fused_vout_loop S u stp gv sv jn d True True) = thrd (succ_vout_loop (last_vout_loop S u stp gv sv) u jn d)" using FF RF by simp
    show "rvth (fused_vout_loop S u stp gv sv jn d True True) = rvth (succ_vout_loop (last_vout_loop S u stp gv sv) u jn d)" using FF RF by simp
    show "lsuc (fused_vout_loop S u stp gv sv jn d True True) = lsuc (succ_vout_loop (last_vout_loop S u stp gv sv) u jn d)" using FL RF LL by simp
    show "snum (fused_vout_loop S u stp gv sv jn d True True) = snum (succ_vout_loop (last_vout_loop S u stp gv sv) u jn d)" using FS RS' by simp
    show "ndtree.more (fused_vout_loop S u stp gv sv jn d True True) = ndtree.more (succ_vout_loop (last_vout_loop S u stp gv sv) u jn d)" by simp
  qed
qed

lemma fused_vout_loop_eq_snum:
  assumes ps: "parent_spec (prnt S)"
  shows "fused_vout_loop S u stp gv sv jn d False True = succ_vout_loop S u jn d"
proof -
  have RF: "prnt (succ_vout_loop S u jn d) = prnt S \<and> thrd (succ_vout_loop S u jn d) = thrd S \<and> rvth (succ_vout_loop S u jn d) = rvth S \<and> lsuc (succ_vout_loop S u jn d) = lsuc S" using succ_vout_loop_fields[OF ps, THEN mp, OF refl] by blast
  have RS: "snum (succ_vout_loop S u jn d) = (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow (prnt S) u)) then snum S x - d else snum S x)" using succ_vout_loop_snum[OF ps, THEN mp, OF refl] by blast
  have FF: "prnt (fused_vout_loop S u stp gv sv jn d False True) = prnt S \<and> thrd (fused_vout_loop S u stp gv sv jn d False True) = thrd S \<and> rvth (fused_vout_loop S u stp gv sv jn d False True) = rvth S" using fused_vout_loop_fields[OF ps, THEN mp, OF refl] by blast
  have FL: "lsuc (fused_vout_loop S u stp gv sv jn d False True) = lsuc S" using fused_vout_loop_lsuc[OF ps, THEN mp, OF refl] by simp
  have FS: "snum (fused_vout_loop S u stp gv sv jn d False True) = (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow (prnt S) u)) then snum S x - d else snum S x)" using fused_vout_loop_snum[OF ps, THEN mp, OF refl] by simp
  show ?thesis
  proof (rule ndtree.equality)
    show "prnt (fused_vout_loop S u stp gv sv jn d False True) = prnt (succ_vout_loop S u jn d)" using FF RF by simp
    show "thrd (fused_vout_loop S u stp gv sv jn d False True) = thrd (succ_vout_loop S u jn d)" using FF RF by simp
    show "rvth (fused_vout_loop S u stp gv sv jn d False True) = rvth (succ_vout_loop S u jn d)" using FF RF by simp
    show "lsuc (fused_vout_loop S u stp gv sv jn d False True) = lsuc (succ_vout_loop S u jn d)" using FL RF by simp
    show "snum (fused_vout_loop S u stp gv sv jn d False True) = snum (succ_vout_loop S u jn d)" using FS RS by simp
    show "ndtree.more (fused_vout_loop S u stp gv sv jn d False True) = ndtree.more (succ_vout_loop S u jn d)" by simp
  qed
qed

lemma svin_lvout_commute:
  assumes ps: "parent_spec (prnt X)"
  shows "last_vout_loop (succ_vin_loop X a jn1 d1) u stp gv sv = succ_vin_loop (last_vout_loop X u stp gv sv) a jn1 d1"
proof -
  have svF: "prnt (succ_vin_loop X a jn1 d1) = prnt X \<and> thrd (succ_vin_loop X a jn1 d1) = thrd X \<and> rvth (succ_vin_loop X a jn1 d1) = rvth X \<and> lsuc (succ_vin_loop X a jn1 d1) = lsuc X" using succ_vin_loop_fields[OF ps, THEN mp, OF refl] by blast
  have psSV: "prnt (succ_vin_loop X a jn1 d1) = prnt X" using svF by simp
  have lsucSV: "lsuc (succ_vin_loop X a jn1 d1) = lsuc X" using svF by simp
  have lvF: "prnt (last_vout_loop X u stp gv sv) = prnt X \<and> thrd (last_vout_loop X u stp gv sv) = thrd X \<and> rvth (last_vout_loop X u stp gv sv) = rvth X \<and> snum (last_vout_loop X u stp gv sv) = snum X" using last_vout_loop_fields[OF ps, THEN mp, OF refl] by blast
  have psLV: "prnt (last_vout_loop X u stp gv sv) = prnt X" using lvF by simp
  have snumLV: "snum (last_vout_loop X u stp gv sv) = snum X" using lvF by simp
  have psSV': "parent_spec (prnt (succ_vin_loop X a jn1 d1))" using ps psSV by simp
  have psLV': "parent_spec (prnt (last_vout_loop X u stp gv sv))" using ps psLV by simp
  have L_lsuc: "lsuc (last_vout_loop (succ_vin_loop X a jn1 d1) u stp gv sv) = (\<lambda>z. if z \<in> set (takeWhile (\<lambda>y. Some y \<noteq> stp \<and> lsuc X y = gv) (follow (prnt X) u)) then sv else lsuc X z)" using last_vout_loop_lsuc[OF ps, THEN mp, OF psSV] lsucSV by (simp only:)
  have L_snum: "snum (last_vout_loop (succ_vin_loop X a jn1 d1) u stp gv sv) = snum (succ_vin_loop X a jn1 d1)" using last_vout_loop_fields[OF psSV', THEN mp, OF refl] by blast
  have SV_snum: "snum (succ_vin_loop X a jn1 d1) = (\<lambda>z. if z \<in> set (takeWhile (\<lambda>y. y \<noteq> jn1) (follow (prnt X) a)) then snum X z + d1 else snum X z)" using succ_vin_loop_snum[OF ps, THEN mp, OF refl] by blast
  have R_lsuc: "lsuc (succ_vin_loop (last_vout_loop X u stp gv sv) a jn1 d1) = lsuc (last_vout_loop X u stp gv sv)" using succ_vin_loop_fields[OF psLV', THEN mp, OF refl] by blast
  have R_lsuc2: "lsuc (last_vout_loop X u stp gv sv) = (\<lambda>z. if z \<in> set (takeWhile (\<lambda>y. Some y \<noteq> stp \<and> lsuc X y = gv) (follow (prnt X) u)) then sv else lsuc X z)" using last_vout_loop_lsuc[OF ps, THEN mp, OF refl] by blast
  have R_snum: "snum (succ_vin_loop (last_vout_loop X u stp gv sv) a jn1 d1) = (\<lambda>z. if z \<in> set (takeWhile (\<lambda>y. y \<noteq> jn1) (follow (prnt X) a)) then snum X z + d1 else snum X z)" using succ_vin_loop_snum[OF psLV', THEN mp, OF refl] psLV snumLV by (simp only:)
  have Lp: "prnt (last_vout_loop (succ_vin_loop X a jn1 d1) u stp gv sv) = prnt X \<and> thrd (last_vout_loop (succ_vin_loop X a jn1 d1) u stp gv sv) = thrd X \<and> rvth (last_vout_loop (succ_vin_loop X a jn1 d1) u stp gv sv) = rvth X" using last_vout_loop_fields[OF psSV', THEN mp, OF refl] svF by simp
  have Rp: "prnt (succ_vin_loop (last_vout_loop X u stp gv sv) a jn1 d1) = prnt X \<and> thrd (succ_vin_loop (last_vout_loop X u stp gv sv) a jn1 d1) = thrd X \<and> rvth (succ_vin_loop (last_vout_loop X u stp gv sv) a jn1 d1) = rvth X" using succ_vin_loop_fields[OF psLV', THEN mp, OF refl] lvF by simp
  show ?thesis
  proof (rule ndtree.equality)
    show "prnt (last_vout_loop (succ_vin_loop X a jn1 d1) u stp gv sv) = prnt (succ_vin_loop (last_vout_loop X u stp gv sv) a jn1 d1)" using Lp Rp by simp
    show "thrd (last_vout_loop (succ_vin_loop X a jn1 d1) u stp gv sv) = thrd (succ_vin_loop (last_vout_loop X u stp gv sv) a jn1 d1)" using Lp Rp by simp
    show "rvth (last_vout_loop (succ_vin_loop X a jn1 d1) u stp gv sv) = rvth (succ_vin_loop (last_vout_loop X u stp gv sv) a jn1 d1)" using Lp Rp by simp
    show "lsuc (last_vout_loop (succ_vin_loop X a jn1 d1) u stp gv sv) = lsuc (succ_vin_loop (last_vout_loop X u stp gv sv) a jn1 d1)" using L_lsuc R_lsuc R_lsuc2 by simp
    show "snum (last_vout_loop (succ_vin_loop X a jn1 d1) u stp gv sv) = snum (succ_vin_loop (last_vout_loop X u stp gv sv) a jn1 d1)" using L_snum SV_snum R_snum by simp
    show "ndtree.more (last_vout_loop (succ_vin_loop X a jn1 d1) u stp gv sv) = ndtree.more (succ_vin_loop (last_vout_loop X u stp gv sv) a jn1 d1)" by simp
  qed
qed

text \<open>Reconcile the fused ordering (one @{term j}-pass then one @{term v_out}-pass) with the
      interleaved four-loop ordering of the original @{const update_tree} tail.\<close>
lemma update_tree_tail_eq:
  assumes ps: "parent_spec (prnt S1)"
  shows "(if jn \<noteq> old_rev \<and> j \<noteq> old_rev then fused_vout_loop (fused_vin_loop S1 j j jn last_out old_num True True) v_out up_limit old_last old_rev jn old_num True True else if last_out \<noteq> old_last then fused_vout_loop (fused_vin_loop S1 j j jn last_out old_num True True) v_out up_limit old_last last_out jn old_num True True else fused_vout_loop (fused_vin_loop S1 j j jn last_out old_num True True) v_out up_limit old_last old_last jn old_num False True) = succ_vout_loop (succ_vin_loop (if jn \<noteq> old_rev \<and> j \<noteq> old_rev then last_vout_loop (last_vin_loop S1 j j last_out) v_out up_limit old_last old_rev else if last_out \<noteq> old_last then last_vout_loop (last_vin_loop S1 j j last_out) v_out up_limit old_last last_out else last_vin_loop S1 j j last_out) j jn old_num) v_out jn old_num"
proof -
  define S2 where "S2 = last_vin_loop S1 j j last_out"
  have pS2eq: "prnt S2 = prnt S1" using last_vin_loop_fields[OF ps, THEN mp, OF refl] by (simp add: S2_def)
  have psS2: "parent_spec (prnt S2)" using ps pS2eq by simp
  have fvin: "fused_vin_loop S1 j j jn last_out old_num True True = succ_vin_loop S2 j jn old_num" using fused_vin_loop_eq[OF ps] by (simp add: S2_def)
  have psSVeq: "prnt (succ_vin_loop S2 j jn old_num) = prnt S2" using succ_vin_loop_fields[OF psS2, THEN mp, OF refl] by blast
  have psSV: "parent_spec (prnt (succ_vin_loop S2 j jn old_num))" using psS2 psSVeq by simp
  have bT: "\<And>sv. fused_vout_loop (succ_vin_loop S2 j jn old_num) v_out up_limit old_last sv jn old_num True True = succ_vout_loop (succ_vin_loop (last_vout_loop S2 v_out up_limit old_last sv) j jn old_num) v_out jn old_num" using fused_vout_loop_eq[OF psSV] svin_lvout_commute[OF psS2] by simp
  have bF: "fused_vout_loop (succ_vin_loop S2 j jn old_num) v_out up_limit old_last old_last jn old_num False True = succ_vout_loop (succ_vin_loop S2 j jn old_num) v_out jn old_num" using fused_vout_loop_eq_snum[OF psSV] by simp
  show ?thesis
  proof (cases "jn \<noteq> old_rev \<and> j \<noteq> old_rev")
    case True
    have e1: "(jn \<noteq> old_rev \<and> j \<noteq> old_rev) = True" using True by simp
    show ?thesis using fvin bT by (simp add: S2_def e1)
  next
    case c1: False
    have e1: "(jn \<noteq> old_rev \<and> j \<noteq> old_rev) = False" using c1 by simp
    show ?thesis
    proof (cases "last_out \<noteq> old_last")
      case c2: True
      have e2: "(last_out \<noteq> old_last) = True" using c2 by simp
      show ?thesis using fvin bT by (simp add: S2_def e1 e2)
    next
      case c2: False
      have e2: "(last_out \<noteq> old_last) = False" using c2 by simp
      show ?thesis using fvin bF by (simp add: S2_def e1 e2)
    qed
  qed
qed


subsection \<open>The stem reversal as a closed-form invariant ({\isasymsection}13)\<close>

text \<open>The path-reversal loop @{const stem_loop} is a @{command partial_function}, so it has no
      generated induction rule.  We fix the pivot data in a locale and characterise the loop's
      effect by a well-founded induction on the variant @{term "k - m"} ({\isasymsection}13.5).  The state after
      @{term m} body iterations is pinned down field-by-field by @{term "Istem m"}: every map is
      @{term "S0"}'s map overlaid (@{text "++"}, highest priority last) with the edits made so far.\<close>

locale stem_setup =
  fixes S0 :: "'a ndtree" and r :: 'a and V :: "'a set"
    and i j p :: 'a and k :: nat and s :: "nat \<Rightarrow> 'a"
  assumes arb:   "arb_invar r V S0"
      and path0: "s 0 = i"
      and pathS: "\<And>t. t < k \<Longrightarrow> prnt S0 (s t) = Some (s (Suc t))"
      and pathk: "s k = p"
      and inj:   "inj_on s {..k}"
      and jnotp: "j \<notin> children (prnt S0) p"
      and pne_r: "p \<noteq> r"
      and iV:    "i \<in> V"
      and jV:    "j \<in> V"
begin

text \<open>The path predecessor (@{text pstm}), with the convention @{term "s_pred 0 = j"}.\<close>
definition s_pred :: "nat \<Rightarrow> 'a" where
  "s_pred m = (if m = 0 then j else s (m - 1))"

text \<open>@{term "out t"}: the thread-successor (in @{term S0}) of @{term "s t"}'s last descendant ---
      the node spliced out when @{term "s t"}'s block is detached.\<close>
definition out :: "nat \<Rightarrow> 'a option" where
  "out t = thrd S0 (lsuc S0 (s t))"

text \<open>@{term "lsx t"}: the loop's running @{text lsx} pointer at step @{term t} (the last node of
      the block already threaded), in closed form ({\isasymsection}12.0).\<close>
definition lsx :: "nat \<Rightarrow> 'a" where
  "lsx t = (if t = 0 then lsuc S0 i
            else if lsuc S0 (s t) = lsuc S0 (s (t-1)) then the (rvth S0 (s (t-1)))
            else lsuc S0 (s t))"

definition aftn :: "nat \<Rightarrow> 'a option" where "aftn t = out t"

text \<open>@{term "drt m"}: the deferred-reverse list accumulated after @{term m} iterations.\<close>
definition drt :: "nat \<Rightarrow> 'a list" where "drt m = j # map lsx [0..<m]"

text \<open>@{term "bef t"}: the thread-predecessor (in @{term S0}) of @{term "s t"}.\<close>
definition bef :: "nat \<Rightarrow> 'a" where "bef t = the (rvth S0 (s t))"

text \<open>The thread map after @{term m} iterations, as a fold of @{const fun_upd}s: the j {\isasymmapsto} i
      seam at the bottom, then the bridge (BR) links "bef t {\isasymmapsto} out t (a delete when
      @{term "out t = None"}), then the up-links (UP) "lsx t {\isasymmapsto} s (Suc t)" applied last so
      they win on the single colliding key ({\isasymsection}12.3a).\<close>
definition thrd_inv :: "nat \<Rightarrow> ('a \<rightharpoonup> 'a)" where
  "thrd_inv m =
     fold (\<lambda>t T. T(lsx t \<mapsto> s (Suc t))) [0..<m]
       (fold (\<lambda>t T. T(bef t := out t)) [0..<m]
         ((thrd S0)(j \<mapsto> s 0)))"

text \<open>The reverse-thread edits actually installed during the loop (the deferred UP reverses are
      handled later by @{const dirty_pass}); only steps with @{term "out t \<noteq> None"} contribute.
      The loop sets the reverse-thread of @{term "out t"} to @{term "bef t"} on each iteration, so on
      a colliding key (two stem nodes sharing a last-successor, hence the same @{term "out t"}) the
      later write wins.  We therefore reverse the association list before @{const map_of} (which keeps
      the first occurrence), making the closed form last-write-wins to match the loop ({\isasymsection}13.4).\<close>
definition revBR :: "nat \<Rightarrow> ('a \<rightharpoonup> 'a)" where
  "revBR m = map_of (rev (map (\<lambda>t. (the (out t), bef t)) (filter (\<lambda>t. out t \<noteq> None) [0..<m])))"

text \<open>The reversed parent links installed after @{term m} iterations.\<close>
definition REV :: "nat \<Rightarrow> ('a \<rightharpoonup> 'a)" where
  "REV m = map_of (map (\<lambda>t. (s t, s_pred t)) [0..<m])"

definition Istem :: "nat \<Rightarrow> 'a ndtree \<Rightarrow> bool" where
  "Istem m S \<longleftrightarrow> thrd S = thrd_inv m
              \<and> rvth S = rvth S0 ++ revBR m
              \<and> prnt S = prnt S0 ++ REV m
              \<and> lsuc S = lsuc S0 \<and> snum S = snum S0"

definition Sfin :: "'a ndtree" where
  "Sfin = \<lparr> prnt = prnt S0 ++ REV k, thrd = thrd_inv k,
            rvth = rvth S0 ++ revBR k, lsuc = lsuc S0, snum = snum S0 \<rparr>"

text \<open>@{term "Istem m S"} pins every field, so the state at @{term "m = k"} is unique ({\isasymsection}13.1).\<close>
lemma Istem_unique:
  assumes "Istem k S" shows "S = Sfin"
  using assms by (cases S) (simp add: Istem_def Sfin_def)

text \<open>The live parent edge: at the head @{term "s m"} the reversal has not yet fired, so the parent
      is still @{term S0}'s ({\isasymsection}13.2 @{text live_prnt}).\<close>
lemma live_prnt:
  assumes "m < k" "Istem m S" shows "prnt S (s m) = Some (s (Suc m))"
proof -
  have dom: "s m \<notin> dom (REV m)"
  proof
    assume "s m \<in> dom (REV m)"
    then obtain t where "t < m" "s t = s m"
      by (auto simp: REV_def dom_map_of_conv_image_fst)
    hence "m = t" using inj \<open>m < k\<close> by (auto simp: inj_on_eq_iff)
    with \<open>t < m\<close> show False by simp
  qed
  show ?thesis using \<open>Istem m S\<close> dom pathS[OF \<open>m < k\<close>] by (simp add: Istem_def map_add_dom_app_simps)
qed

lemma thrd_inv_0: "thrd_inv 0 = (thrd S0)(j \<mapsto> i)"
  by (simp add: thrd_inv_def path0)

lemma revBR_0: "revBR 0 = Map.empty" by (simp add: revBR_def)
lemma REV_0: "REV 0 = Map.empty" by (simp add: REV_def)

text \<open>Entry: after the initial j mapped to Some i thread edit, @{term "Istem 0"} holds ({\isasymsection}13.6).\<close>
lemma Istem_0: "Istem 0 (S0\<lparr>thrd := (thrd S0)(j \<mapsto> i)\<rparr>)"
  by (simp add: Istem_def thrd_inv_0 revBR_0 REV_0)

text \<open>@{const REV} gains exactly its @{term "t = m"} reversed link (key @{term "s m"} is fresh by
      path injectivity).\<close>
lemma REV_Suc:
  assumes "m < k" shows "REV (Suc m) = (REV m)(s m \<mapsto> s_pred m)"
proof -
  have dom: "s m \<notin> fst ` set (map (\<lambda>t. (s t, s_pred t)) [0..<m])"
  proof
    assume "s m \<in> fst ` set (map (\<lambda>t. (s t, s_pred t)) [0..<m])"
    then obtain t where "t < m" "s t = s m" by auto
    hence "m = t" using inj \<open>m < k\<close> by (auto simp: inj_on_eq_iff)
    with \<open>t < m\<close> show False by simp
  qed
  have "REV (Suc m) = map_of (map (\<lambda>t. (s t, s_pred t)) [0..<m] @ [(s m, s_pred m)])"
    by (simp add: REV_def)
  also have "\<dots> = (REV m)(s m \<mapsto> s_pred m)"
    using map_of_snoc_upd[OF dom] by (simp add: REV_def)
  finally show ?thesis .
qed

end

text \<open>The locality (geometry) facts the induction quotes directly ({\isasymsection}13.2/{\isasymsection}14): the out-nodes are
      disjoint from the stem, the bridge key is not an up-link key, the out-nodes are distinct, and
      a genuinely new last-successor is untouched by the edits.  Per {\isasymsection}14 these are consequences of
      @{const arb_invar} plus the pivot preconditions (clause J etc.); they are assumed here so the
      stem induction ({\isasymsection}13.3--13.6) can be developed in isolation.\<close>
locale stem_setup_geom = stem_setup +
  assumes out_notin_stem: "\<And>t. t < k \<Longrightarrow> out t \<noteq> None \<Longrightarrow> the (out t) \<notin> s ` {..k}"
      and bef_notin_lsx:  "\<And>m. m < k \<Longrightarrow> bef m \<notin> lsx ` {..m}"
      and outnode_fresh:  "\<And>m. m < k \<Longrightarrow> lsuc S0 (s (Suc m)) \<noteq> lsuc S0 (s m) \<Longrightarrow>
                             lsuc S0 (s (Suc m)) \<notin> lsx ` {..m}
                           \<and> lsuc S0 (s (Suc m)) \<notin> bef ` {..m}
                           \<and> lsuc S0 (s (Suc m)) \<noteq> j"
begin

text \<open>At the head @{term "s m"} the reverse thread still agrees with @{term S0} ({\isasymsection}13.2 @{text live_rvth}).\<close>
lemma live_rvth:
  assumes "m \<le> k" "Istem m S" shows "rvth S (s m) = rvth S0 (s m)"
proof -
  have dom: "s m \<notin> dom (revBR m)"
  proof
    assume "s m \<in> dom (revBR m)"
    then obtain t where t: "t < m" "out t \<noteq> None" "the (out t) = s m"
      by (auto simp: revBR_def dom_map_of_conv_image_fst)
    from t have "the (out t) \<notin> s ` {..k}" using out_notin_stem[of t] \<open>m \<le> k\<close> by simp
    moreover have "the (out t) = s m" using t by simp
    moreover have "s m \<in> s ` {..k}" using \<open>m \<le> k\<close> by auto
    ultimately show False by simp
  qed
  show ?thesis using \<open>Istem m S\<close> dom by (simp add: Istem_def map_add_dom_app_simps)
qed

text \<open>@{const revBR} extension by its @{term "t = m"} term (Some / None branches).\<close>
lemma revBR_Suc_None:
  assumes "out m = None" shows "revBR (Suc m) = revBR m"
  using assms by (simp add: revBR_def upt_Suc_append)

text \<open>With the last-write-wins reversal of @{const revBR}, the @{term "t = m"} bridge reverse always
      wins on its key, so no injectivity of @{const out} is needed (cf. the deleted @{text out_inj}):
      @{thm map_of.simps(2)} puts the new pair on top.\<close>
lemma revBR_Suc_Some:
  assumes "out m \<noteq> None"
  shows "revBR (Suc m) = (revBR m)(the (out m) \<mapsto> bef m)"
proof -
  let ?L = "map (\<lambda>t. (the (out t), bef t)) (filter (\<lambda>t. out t \<noteq> None) [0..<m])"
  show ?thesis using \<open>out m \<noteq> None\<close> by (simp add: revBR_def upt_Suc_append)
qed

lemma revBR_dom: "dom (revBR k) = (\<lambda>t. the (out t)) ` {t. t < k \<and> out t \<noteq> None}"
proof -
  have "dom (revBR k) = fst ` set (map (\<lambda>t. (the (out t), bef t)) (filter (\<lambda>t. out t \<noteq> None) [0..<k]))"
    unfolding revBR_def by (simp add: dom_map_of_conv_image_fst)
  also have "\<dots> = (\<lambda>t. the (out t)) ` set (filter (\<lambda>t. out t \<noteq> None) [0..<k])"
    by (simp add: image_image)
  also have "\<dots> = (\<lambda>t. the (out t)) ` {t. t < k \<and> out t \<noteq> None}"
    by auto
  finally show ?thesis .
qed

lemma revBR_eval_ex:
  assumes "revBR k w = Some v" shows "\<exists>t < k. out t = Some w \<and> bef t = v"
proof -
  have "(w, v) \<in> set (rev (map (\<lambda>t. (the (out t), bef t)) (filter (\<lambda>t. out t \<noteq> None) [0..<k])))"
    using assms unfolding revBR_def by (rule map_of_SomeD)
  hence "(w, v) \<in> set (map (\<lambda>t. (the (out t), bef t)) (filter (\<lambda>t. out t \<noteq> None) [0..<k]))" by simp
  then obtain t where "t \<in> set (filter (\<lambda>t. out t \<noteq> None) [0..<k])" and wv: "(w, v) = (the (out t), bef t)"
    by auto
  hence tk: "t < k" and tno: "out t \<noteq> None" by auto
  have "the (out t) = w" and bv: "bef t = v" using wv by auto
  hence "out t = Some w" using tno by auto
  thus ?thesis using tk bv by auto
qed

text \<open>Last-write-wins value of @{const revBR}: the recorded reverse @{term v} comes from the LARGEST
      index @{term t} whose @{term "out t = Some w"} (no later @{term t'} overrides it).\<close>
lemma revBR_eval_last:
  "revBR m w = Some v \<Longrightarrow> \<exists>t<m. out t = Some w \<and> bef t = v \<and> (\<forall>t'. t < t' \<longrightarrow> t' < m \<longrightarrow> out t' \<noteq> Some w)"
proof (induction m)
  case 0 thus ?case by (simp add: revBR_0)
next
  case (Suc m)
  show ?case
  proof (cases "out m")
    case None
    hence eq: "revBR (Suc m) = revBR m" by (rule revBR_Suc_None)
    then obtain t where tm: "t < m" and ot: "out t = Some w" and bt: "bef t = v"
      and hi: "\<forall>t'. t < t' \<longrightarrow> t' < m \<longrightarrow> out t' \<noteq> Some w"
      using Suc.IH Suc.prems by auto
    have ext: "\<forall>t'. t < t' \<longrightarrow> t' < Suc m \<longrightarrow> out t' \<noteq> Some w"
    proof (intro allI impI)
      fix t' assume a1: "t < t'" and a2: "t' < Suc m"
      show "out t' \<noteq> Some w"
      proof (cases "t' = m")
        case True thus ?thesis using None by simp
      next
        case False hence "t' < m" using a2 by simp
        thus ?thesis using hi a1 by simp
      qed
    qed
    have "t < Suc m" using tm by simp
    thus ?thesis using ot bt ext by auto
  next
    case (Some w')
    have onn: "out m \<noteq> None" using Some by simp
    have eq: "revBR (Suc m) = (revBR m)(the (out m) \<mapsto> bef m)" by (rule revBR_Suc_Some[OF onn])
    show ?thesis
    proof (cases "w = w'")
      case True
      hence "revBR (Suc m) w = Some (bef m)" using eq Some by simp
      hence vm: "v = bef m" using Suc.prems by simp
      have "out m = Some w" using Some True by simp
      moreover have "\<forall>t'. m < t' \<longrightarrow> t' < Suc m \<longrightarrow> out t' \<noteq> Some w" by simp
      ultimately show ?thesis using vm by auto
    next
      case False
      hence "revBR (Suc m) w = revBR m w" using eq Some by simp
      hence "revBR m w = Some v" using Suc.prems by simp
      then obtain t where tm: "t < m" and ot: "out t = Some w" and bt: "bef t = v"
        and hi: "\<forall>t'. t < t' \<longrightarrow> t' < m \<longrightarrow> out t' \<noteq> Some w"
        using Suc.IH by auto
      have ext: "\<forall>t'. t < t' \<longrightarrow> t' < Suc m \<longrightarrow> out t' \<noteq> Some w"
      proof (intro allI impI)
        fix t' assume a1: "t < t'" and a2: "t' < Suc m"
        show "out t' \<noteq> Some w"
        proof (cases "t' = m")
          case True thus ?thesis using Some False by simp
        next
          case False hence "t' < m" using a2 by simp
          thus ?thesis using hi a1 by simp
        qed
      qed
      have "t < Suc m" using tm by simp
      thus ?thesis using ot bt ext by auto
    qed
  qed
qed

text \<open>The thread map gains the up-link "lsx m {\isasymmapsto} s (Suc m)" and the bridge
     "bef m := out m"; this is exactly the two edits the loop body performs ({\isasymsection}13.4 thrd3).\<close>
lemma thrd_inv_Suc:
  assumes mk: "m < k"
  shows "thrd_inv (Suc m) = ((thrd_inv m)(lsx m \<mapsto> s (Suc m)))(bef m := out m)"
proof -
  have notin: "bef m \<notin> lsx ` set [0..<m]" using bef_notin_lsx[OF mk] by auto
  have ne: "bef m \<noteq> lsx m" using bef_notin_lsx[OF mk] by auto
  let ?base = "(thrd S0)(j \<mapsto> s 0)"
  let ?X = "fold (\<lambda>t T. T(bef t := out t)) [0..<m] ?base"
  have splitlist: "[0..<Suc m] = [0..<m] @ [m]" by (simp add: upt_Suc_append)
  have inner: "fold (\<lambda>t T. T(bef t := out t)) [0..<Suc m] ?base = ?X(bef m := out m)"
    by (simp add: splitlist)
  have "thrd_inv (Suc m)
          = fold (\<lambda>t T. T(lsx t \<mapsto> s (Suc t))) [0..<Suc m] (?X(bef m := out m))"
    unfolding thrd_inv_def using inner by simp
  also have "\<dots> = (fold (\<lambda>t T. T(lsx t \<mapsto> s (Suc t))) [0..<m] (?X(bef m := out m)))(lsx m \<mapsto> s (Suc m))"
    by (simp add: splitlist)
  also have "\<dots> = ((fold (\<lambda>t T. T(lsx t \<mapsto> s (Suc t))) [0..<m] ?X)(bef m := out m))(lsx m \<mapsto> s (Suc m))"
    using fold_upd_commute[OF notin, of "\<lambda>t. Some (s (Suc t))" ?X "out m"] by simp
  also have "\<dots> = ((thrd_inv m)(bef m := out m))(lsx m \<mapsto> s (Suc m))"
    by (simp add: thrd_inv_def)
  also have "\<dots> = ((thrd_inv m)(lsx m \<mapsto> s (Suc m)))(bef m := out m)"
    using ne by (simp add: fun_upd_twist)
  finally show ?thesis .
qed

text \<open>Value of @{const thrd_inv} at a key written by neither fold nor the seam: it is @{term S0}'s.\<close>
lemma thrd_inv_eval_fresh:
  assumes "q \<notin> lsx ` set [0..<n]" "q \<notin> bef ` set [0..<n]" "q \<noteq> j"
  shows "thrd_inv n q = thrd S0 q"
proof -
  have "thrd_inv n q
          = (fold (\<lambda>t T. T(bef t := out t)) [0..<n] ((thrd S0)(j \<mapsto> s 0))) q"
    unfolding thrd_inv_def
    using fold_upd_other[OF assms(1), of "\<lambda>t. Some (s (Suc t))"
            "fold (\<lambda>t T. T(bef t := out t)) [0..<n] ((thrd S0)(j \<mapsto> s 0))"] by simp
  also have "\<dots> = ((thrd S0)(j \<mapsto> s 0)) q"
    using fold_upd_other[OF assms(2), of out "(thrd S0)(j \<mapsto> s 0)"] by auto
  also have "\<dots> = thrd S0 q" using assms(3) by simp
  finally show ?thesis .
qed

text \<open>Seam/look-ahead ({\isasymsection}13.3 + the @{text aft'} computation): the body's next @{text aft} pointer
      @{term "thrd S3 (lsx (Suc m))"} reads off as @{term "out (Suc m)"}.  Two cases: a coinciding
      last-successor (the bridge edit reads it back) or a genuinely new one (untouched).\<close>
lemma aft_lookup:
  assumes mk: "m < k"
  shows "thrd_inv (Suc m) (lsx (Suc m)) = out (Suc m)"
proof (cases "lsuc S0 (s (Suc m)) = lsuc S0 (s m)")
  case True
  have lsxB: "lsx (Suc m) = bef m" using True by (simp add: lsx_def bef_def)
  have outB: "out (Suc m) = out m" using True by (simp add: out_def)
  have "thrd_inv (Suc m) (lsx (Suc m)) = out m"
    using thrd_inv_Suc[OF mk] lsxB by simp
  thus ?thesis using outB by simp
next
  case False
  let ?q = "lsuc S0 (s (Suc m))"
  have lsxA: "lsx (Suc m) = ?q" using False by (simp add: lsx_def)
  have outA: "out (Suc m) = thrd S0 ?q" by (simp add: out_def)
  have setm: "set [0..<Suc m] = {..m}" by auto
  have h1: "?q \<notin> lsx ` set [0..<Suc m]" using outnode_fresh[OF mk False] setm by simp
  have h2: "?q \<notin> bef ` set [0..<Suc m]" using outnode_fresh[OF mk False] setm by simp
  have h3: "?q \<noteq> j" using outnode_fresh[OF mk False] by simp
  have "thrd_inv (Suc m) ?q = thrd S0 ?q" using thrd_inv_eval_fresh[OF h1 h2 h3] by auto
  thus ?thesis using lsxA outA by simp
qed

text \<open>Lemma B ({\isasymsection}13.4): one body iteration takes @{term "Istem m"} to @{term "Istem (Suc m)"}.
      The three edits become the @{term "t = m"} terms of @{const thrd_inv}/@{const revBR}/@{const REV}.\<close>
lemma body_pres:
  assumes mk: "m < k" and IS: "Istem m S"
  defines "S1 \<equiv> S\<lparr>thrd := (thrd S)(lsx m \<mapsto> the (prnt S (s m)))\<rparr>"
  defines "S2 \<equiv> (case aftn m of None \<Rightarrow> S1\<lparr>thrd := (thrd S1)(the (rvth S1 (s m)) := None)\<rparr>
                  | Some a \<Rightarrow> S1\<lparr>thrd := (thrd S1)(the (rvth S1 (s m)) \<mapsto> a),
                                  rvth := (rvth S1)(a \<mapsto> the (rvth S1 (s m)))\<rparr>)"
  defines "S3 \<equiv> S2\<lparr>prnt := (prnt S2)(s m \<mapsto> s_pred m)\<rparr>"
  shows "Istem (Suc m) S3"
proof -
  have nxt: "the (prnt S (s m)) = s (Suc m)" using live_prnt[OF mk IS] by simp
  have rvthS1: "rvth S1 = rvth S" by (simp add: S1_def)
  have befv: "the (rvth S1 (s m)) = bef m"
    using live_rvth[OF less_imp_le[OF mk] IS] rvthS1 by (simp add: bef_def)
  have thrdS1: "thrd S1 = (thrd_inv m)(lsx m \<mapsto> s (Suc m))"
    using IS nxt by (simp add: S1_def Istem_def)
  have thrd3: "thrd S3 = thrd_inv (Suc m)"
  proof (cases "out m")
    case None
    have aftN: "aftn m = None" using None by (simp add: aftn_def)
    show ?thesis using None befv thrdS1 thrd_inv_Suc[OF mk] by (simp add: S3_def S2_def aftN)
  next
    case (Some a)
    have aftS: "aftn m = Some a" using Some by (simp add: aftn_def)
    show ?thesis using Some befv thrdS1 thrd_inv_Suc[OF mk] by (simp add: S3_def S2_def aftS)
  qed
  have rvth3: "rvth S3 = rvth S0 ++ revBR (Suc m)"
  proof (cases "out m")
    case None
    have aftN: "aftn m = None" using None by (simp add: aftn_def)
    show ?thesis using IS revBR_Suc_None[OF None] by (simp add: S3_def S2_def S1_def aftN Istem_def)
  next
    case (Some a)
    have aftS: "aftn m = Some a" using Some by (simp add: aftn_def)
    have outNN: "out m \<noteq> None" using Some by simp
    have "rvth S3 = (rvth S1)(a \<mapsto> the (rvth S1 (s m)))" by (simp add: S3_def S2_def aftS)
    also have "\<dots> = (rvth S0 ++ revBR m)(the (out m) \<mapsto> bef m)"
      using rvthS1 befv IS Some by (simp add: Istem_def)
    also have "\<dots> = rvth S0 ++ revBR (Suc m)"
      using revBR_Suc_Some[OF outNN] by simp
    finally show ?thesis .
  qed
  have prnt3: "prnt S3 = prnt S0 ++ REV (Suc m)"
  proof -
    have "prnt S3 = (prnt S0 ++ REV m)(s m \<mapsto> s_pred m)"
      using IS by (cases "out m") (simp_all add: S3_def S2_def aftn_def S1_def Istem_def)
    also have "\<dots> = prnt S0 ++ REV (Suc m)" using REV_Suc[OF mk] by simp
    finally show ?thesis .
  qed
  have lsnum3: "lsuc S3 = lsuc S0 \<and> snum S3 = snum S0"
    using IS by (cases "out m") (simp_all add: S3_def S2_def aftn_def S1_def Istem_def)
  show "Istem (Suc m) S3"
    using thrd3 rvth3 prnt3 lsnum3 by (simp add: Istem_def)
qed

text \<open>The reverse thread agrees with @{term S0} at any stem node, under @{term "Istem n"} for any
      @{term "n \<le> k"} (generalises @{thm live_rvth} to an independent invariant index).\<close>
lemma rvth_stem_eq:
  assumes "m' \<le> k" "n \<le> k" "Istem n S" shows "rvth S (s m') = rvth S0 (s m')"
proof -
  have dom: "s m' \<notin> dom (revBR n)"
  proof
    assume "s m' \<in> dom (revBR n)"
    then obtain t where t: "t < n" "out t \<noteq> None" "the (out t) = s m'"
      by (auto simp: revBR_def dom_map_of_conv_image_fst)
    from t \<open>n \<le> k\<close> have "t < k" by simp
    hence "the (out t) \<notin> s ` {..k}" using out_notin_stem[of t] t by simp
    moreover have "s m' \<in> s ` {..k}" using \<open>m' \<le> k\<close> by auto
    ultimately show False using t by simp
  qed
  show ?thesis using \<open>Istem n S\<close> dom by (simp add: Istem_def map_add_dom_app_simps)
qed

text \<open>One unfolding of the loop equation: from a head at @{term "s m"} (with @{term "Istem m"}) the
      body produces the canonical @{term "Suc m"} state @{term S3} (= @{thm body_pres}) and arguments,
      reducing the recursion to its tail ({\isasymsection}13.5 step).  Combines guard-false, the seam @{thm aft_lookup},
      and the @{text lsx'} computation.\<close>
lemma stem_loop_step:
  assumes mk: "m < k" and IS: "Istem m S"
  defines "S1 \<equiv> S\<lparr>thrd := (thrd S)(lsx m \<mapsto> the (prnt S (s m)))\<rparr>"
  defines "S2 \<equiv> (case aftn m of None \<Rightarrow> S1\<lparr>thrd := (thrd S1)(the (rvth S1 (s m)) := None)\<rparr>
                  | Some a \<Rightarrow> S1\<lparr>thrd := (thrd S1)(the (rvth S1 (s m)) \<mapsto> a),
                                  rvth := (rvth S1)(a \<mapsto> the (rvth S1 (s m)))\<rparr>)"
  defines "S3 \<equiv> S2\<lparr>prnt := (prnt S2)(s m \<mapsto> s_pred m)\<rparr>"
  shows "stem_loop S (s m) (s_pred m) (lsx m) (aftn m) (drt m) p
           = stem_loop S3 (s (Suc m)) (s_pred (Suc m)) (lsx (Suc m)) (aftn (Suc m)) (drt (Suc m)) p"
proof -
  have guard: "s m \<noteq> p"
  proof
    assume "s m = p"
    hence "s m = s k" using pathk by simp
    moreover have "m \<in> {..k}" "k \<in> {..k}" using mk by auto
    ultimately have "m = k" using inj by (auto dest: inj_onD)
    thus False using mk by simp
  qed
  have nxt: "the (prnt S (s m)) = s (Suc m)" using live_prnt[OF mk IS] by simp
  have IS3: "Istem (Suc m) S3"
    unfolding S1_def S2_def S3_def using body_pres[OF mk IS] by simp
  have lsucS3: "lsuc S3 = lsuc S0" using IS3 by (simp add: Istem_def)
  have thrdS3: "thrd S3 = thrd_inv (Suc m)" using IS3 by (simp add: Istem_def)
  have rvthS3: "the (rvth S3 (s m)) = bef m"
    using rvth_stem_eq[OF less_imp_le[OF mk] Suc_leI[OF mk] IS3] by (simp add: bef_def)
  let ?LSX = "if lsuc S3 (the (prnt S (s m))) = lsuc S3 (s m)
                then the (rvth S3 (s m)) else lsuc S3 (the (prnt S (s m)))"
  have key: "stem_loop S (s m) (s_pred m) (lsx m) (aftn m) (drt m) p
               = stem_loop S3 (the (prnt S (s m))) (s m) ?LSX (thrd S3 ?LSX) (drt m @ [lsx m]) p"
    apply (subst stem_loop.simps)
    apply (unfold Let_def S1_def S2_def S3_def)
    apply (simp add: guard)
    done
  have lsxeq: "?LSX = lsx (Suc m)"
    using lsucS3 rvthS3 nxt by (simp add: lsx_def bef_def)
  have afteq: "thrd S3 ?LSX = aftn (Suc m)"
    using lsxeq thrdS3 aft_lookup[OF mk] by (simp add: aftn_def)
  show ?thesis
    using key lsxeq afteq nxt by (simp add: s_pred_def drt_def)
qed

text \<open>The inductive lemma ({\isasymsection}13.5): from @{term "Istem m"}, the loop runs to the unique final state
      @{const Sfin} and returns the @{term "m = k"} pointers, by well-founded induction on @{term "k - m"}.\<close>
lemma stem_loop_effect:
  "m \<le> k \<Longrightarrow> Istem m S \<Longrightarrow>
     stem_loop S (s m) (s_pred m) (lsx m) (aftn m) (drt m) p
       = (Sfin, s_pred k, lsx k, aftn k, drt k)"
proof (induction "k - m" arbitrary: m S)
  case 0
  hence "m = k" by simp
  have g: "s m = p" using \<open>m = k\<close> pathk by simp
  have sf: "S = Sfin" using \<open>Istem m S\<close> \<open>m = k\<close> Istem_unique by simp
  show ?case
    using g sf \<open>m = k\<close> by (subst stem_loop.simps) simp
next
  case (Suc n)
  from Suc.hyps(2) have mk: "m < k" by auto
  have meas: "n = k - Suc m" using Suc.hyps(2) mk by auto
  have sk: "Suc m \<le> k" using mk by simp
  show ?case
    using stem_loop_step[OF mk Suc.prems(2)]
          Suc.hyps(1)[OF meas sk body_pres[OF mk Suc.prems(2)]]
    by simp
qed

text \<open>Entry/hand-off ({\isasymsection}13.6): instantiated at @{term "m = 0"} with the loop's initial arguments,
      matching the @{const update_tree} call.\<close>
corollary stem_loop_init:
  "stem_loop (S0\<lparr>thrd := (thrd S0)(j \<mapsto> i)\<rparr>) i j (lsuc S0 i) (thrd S0 (lsuc S0 i)) [j] p
     = (Sfin, s_pred k, lsx k, aftn k, drt k)"
  using stem_loop_effect[OF le0 Istem_0]
  by (simp add: path0 s_pred_def lsx_def aftn_def out_def drt_def)

end

text \<open>Discharging the @{locale stem_setup_geom} locality assumptions ({\isasymsection}14) inside the bare
      @{locale stem_setup}: the out-nodes/bridge keys really are off the stem and the up-link
      keys, as consequences of @{const arb_invar} and the path (clause J / block geometry).\<close>
context stem_setup begin

lemma pst: "parent_spec (thrd S0)" and ppt: "parent_spec (prnt S0)"
  using arb unfolding arb_invar_def by (auto simp: rooted_arborescense_invar_def)

text \<open>Every stem node lies in @{term V} (when the stem is non-trivial): interior nodes are in
      @{term "dom (prnt S0)"}, the top node @{term p} is a parent value, both "{\isasymsubseteq} V".\<close>
lemma sV:
  assumes tk: "t \<le> k" and k0: "0 < k" shows "s t \<in> V"
proof -
  have rinv: "rooted_arborescense_invar r V (prnt S0)" using arb unfolding arb_invar_def by simp
  have domeq: "dom (prnt S0) = V - {r}" by (rule rooted_arborescense_invar_dom[OF rinv])
  have dvseq: "dVs {(y, x) |x y. Some x = prnt S0 y} = V" by (rule rooted_arborescense_invar_dVs[OF rinv])
  show ?thesis
  proof (cases "t < k")
    case True
    hence "s t \<in> dom (prnt S0)" using pathS[OF True] by auto
    thus ?thesis using domeq by auto
  next
    case False
    hence tk2: "t = k" using tk by simp
    have "prnt S0 (s (k-1)) = Some (s k)" using pathS[of "k-1"] k0 by simp
    hence "(s (k-1), s k) \<in> {(y, x) |x y. Some x = prnt S0 y}" by auto
    hence "s k \<in> dVs {(y, x) |x y. Some x = prnt S0 y}" by (auto simp: dVs_def)
    thus ?thesis using dvseq tk2 by simp
  qed
qed

text \<open>A proper @{const prnt}-ancestor of a node is not in that node's thread-suffix: it heads the
      whole thread but @{const follow} of a descendant is a strict suffix (preorder: ancestor first).\<close>
lemma anc_notin_thread_suffix:
  assumes uV: "u \<in> V" and vchild: "v \<in> children (prnt S0) u" and uv: "u \<noteq> v"
  shows "u \<notin> set (follow (thrd S0) v)"
proof -
  have vblk: "v \<in> set (block S0 u)" using vchild block_props(4)[OF arb uV] by simp
  have FUeq: "follow (thrd S0) u = block S0 u @ (case thrd S0 (lsuc S0 u) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd S0) w)"
    by (rule block_props(1)[OF arb uV])
  have vFU: "v \<in> set (follow (thrd S0) u)" using vblk FUeq by simp
  then obtain G H where GH: "follow (thrd S0) u = G @ v # H" by (meson split_list)
  have fv: "follow (thrd S0) v = v # H" using GH follow_append_ps[OF pst] by auto
  have dist: "distinct (follow (thrd S0) u)" by (rule follow_distinct_ps[OF pst])
  have hd: "hd (follow (thrd S0) u) = u" by (rule follow_hd_ps[OF pst])
  have Gne: "G \<noteq> []"
  proof
    assume "G = []"
    hence "hd (follow (thrd S0) u) = v" using GH by simp
    thus False using hd uv by simp
  qed
  hence "hd G = u" using GH hd by (simp add: hd_append)
  hence uG: "u \<in> set G" using Gne by (metis hd_in_set)
  have "u \<notin> set (v # H)" using dist GH uG uv by auto
  thus ?thesis using fv by simp
qed

text \<open>The stem is a @{const prnt}-ancestor chain: @{term "s b"} is on the root-path of @{term "s a"}
      for "a {\isasymle} b {\isasymle} k".\<close>
lemma stem_chain: "b \<le> k \<Longrightarrow> a \<le> b \<Longrightarrow> s b \<in> set (follow (prnt S0) (s a))"
proof (induction "b - a" arbitrary: a)
  case 0
  hence "a = b" by simp
  thus ?case using follow_ne_ps[OF ppt] follow_hd_ps[OF ppt] by (metis hd_in_set)
next
  case (Suc d)
  have ab: "a < b" using Suc.hyps(2) by simp
  hence ak: "a < k" using Suc.prems(1) by simp
  have "follow (prnt S0) (s a) = s a # follow (prnt S0) (s (Suc a))"
    using pathS[OF ak] by (subst follow_ps_simps[OF ppt]) simp
  moreover have "s b \<in> set (follow (prnt S0) (s (Suc a)))"
    using Suc.hyps(1)[of "Suc a"] Suc.hyps(2) Suc.prems(1) ab by simp
  ultimately show ?case by simp
qed

text \<open>@{text out_notin_stem} ({\isasymsection}14): the out-node of @{term "s t"} (the thread node spliced out after
      its block) is not a stem node --- below @{term "s t"} it is outside the block; above it the
      ancestors precede @{term "s t"} in the thread.\<close>
lemma geom_out_notin_stem:
  assumes tk: "t < k" and outNN: "out t \<noteq> None"
  shows "the (out t) \<notin> s ` {..k}"
proof -
  have k0: "0 < k" using tk by simp
  have stV: "s t \<in> V" using sV tk by simp
  obtain w where outw: "out t = Some w" using outNN by auto
  have thrdw: "thrd S0 (lsuc S0 (s t)) = Some w" using outw by (simp add: out_def)
  have FUeq: "follow (thrd S0) (s t) = block S0 (s t) @ follow (thrd S0) w"
    using block_props(1)[OF arb stV] thrdw by simp
  have distFU: "distinct (follow (thrd S0) (s t))" by (rule follow_distinct_ps[OF pst])
  have wfollow: "w \<in> set (follow (thrd S0) w)"
    using follow_hd_ps[OF pst] follow_ne_ps[OF pst] by (metis hd_in_set)
  have wFU: "w \<in> set (follow (thrd S0) (s t))" using wfollow FUeq by simp
  have wnotblk: "w \<notin> set (block S0 (s t))" using distFU FUeq wfollow by auto
  have wval: "the (out t) = w" using outw by simp
  have "w \<notin> s ` {..k}"
  proof
    assume "w \<in> s ` {..k}"
    then obtain t' where t'k: "t' \<le> k" and wst': "w = s t'" by auto
    show False
    proof (cases "t' \<le> t")
      case True
      have "s t \<in> set (follow (prnt S0) (s t'))" using stem_chain[of t t'] tk True by simp
      hence "s t' \<in> children (prnt S0) (s t)" unfolding children_def by simp
      hence "s t' \<in> set (block S0 (s t))" using block_props(4)[OF arb stV] by simp
      thus False using wnotblk wst' by simp
    next
      case False
      hence tt': "t < t'" by simp
      have st'V: "s t' \<in> V" using sV t'k k0 by simp
      have "s t' \<in> set (follow (prnt S0) (s t))" using stem_chain[of t' t] t'k tt' by simp
      hence stchild: "s t \<in> children (prnt S0) (s t')" unfolding children_def by simp
      have ne: "s t' \<noteq> s t" using inj tt' t'k tk by (auto simp: inj_on_eq_iff)
      have "s t' \<notin> set (follow (thrd S0) (s t))" using anc_notin_thread_suffix[OF st'V stchild ne] by auto
      thus False using wFU wst' by simp
    qed
  qed
  thus ?thesis using wval by simp
qed

text \<open>@{term "bef m"} is the thread-predecessor of @{term "s m"} (an interior stem node, so
      "{\isasymnoteq} r" and threaded in @{term S0}).\<close>
lemma bef_pred:
  assumes mk: "m < k"
  shows "thrd S0 (bef m) = Some (s m)" and "s m \<noteq> r" and "bef m \<in> V" and "s m \<in> V"
proof -
  have smdom: "s m \<in> dom (prnt S0)" using pathS[OF mk] by auto
  have domp: "dom (prnt S0) = V - {r}" using arb unfolding arb_invar_def
    by (simp add: rooted_arborescense_invar_def)
  show smr: "s m \<noteq> r" using smdom domp by auto
  show smV: "s m \<in> V" using smdom domp by auto
  have domrv: "dom (rvth S0) = V - {r}" using arb unfolding arb_invar_def by simp
  have "s m \<in> dom (rvth S0)" using smV smr domrv by simp
  then obtain u where u: "rvth S0 (s m) = Some u" by auto
  hence befu: "bef m = u" by (simp add: bef_def)
  have iff: "\<forall>v v'. (thrd S0 v = Some v') = (rvth S0 v' = Some v)" using arb unfolding arb_invar_def by simp
  have thrdu: "thrd S0 u = Some (s m)" using iff u by auto
  show "thrd S0 (bef m) = Some (s m)" using thrdu befu by simp
  have domt: "dom (thrd S0) = V - {lsuc S0 r}" using arb unfolding arb_invar_def by simp
  have "u \<in> dom (thrd S0)" using thrdu by auto
  thus "bef m \<in> V" using domt befu by auto
qed

text \<open>@{term "bef m"} is not inside @{term "s m"}'s block: as a thread-predecessor it precedes
      @{term "s m"}, while the block is a thread-suffix from @{term "s m"}.\<close>
lemma bef_notin_block:
  assumes mk: "m < k" shows "bef m \<notin> set (block S0 (s m))"
proof -
  have thrdu: "thrd S0 (bef m) = Some (s m)" by (rule bef_pred(1)[OF mk])
  have smV: "s m \<in> V" by (rule bef_pred(4)[OF mk])
  have f: "follow (thrd S0) (bef m) = bef m # follow (thrd S0) (s m)"
    using thrdu by (subst follow_ps_simps[OF pst]) simp
  have dist: "distinct (follow (thrd S0) (bef m))" by (rule follow_distinct_ps[OF pst])
  have "bef m \<notin> set (follow (thrd S0) (s m))" using f dist by auto
  moreover have "set (block S0 (s m)) \<subseteq> set (follow (thrd S0) (s m))"
    using block_props(1)[OF arb smV] by (metis Un_iff set_append subsetI)
  ultimately show ?thesis by auto
qed

text \<open>@{const bef} is injective on the stem (thread-predecessors of distinct nodes are distinct).\<close>
lemma bef_inj:
  assumes ak: "a < k" and bk: "b < k" and ab: "a \<noteq> b" shows "bef a \<noteq> bef b"
  using bef_pred(1)[OF ak] bef_pred(1)[OF bk] inj ak bk ab by (auto simp: inj_on_eq_iff)

text \<open>@{text bef_notin_lsx} ({\isasymsection}14): the bridge key @{term "bef m"} is not an up-link key.  A non-colliding
      @{term "lsx t"} (@{term "t \<le> m"}) is @{term "lsuc S0 (s t)"}, inside @{term "s t"}'s block hence
      inside @{term "s m"}'s (subtree monotonicity) --- where @{term "bef m"} is not; a colliding one is
      @{term "bef (t-1)"}, distinct from @{term "bef m"} by injectivity.\<close>
lemma geom_bef_notin_lsx:
  assumes mk: "m < k" shows "bef m \<notin> lsx ` {..m}"
proof
  assume "bef m \<in> lsx ` {..m}"
  then obtain t where tm: "t \<le> m" and eq: "bef m = lsx t" by auto
  have tk: "t < k" using tm mk by simp
  have smV: "s m \<in> V" by (rule bef_pred(4)[OF mk])
  show False
  proof (cases "t \<noteq> 0 \<and> lsuc S0 (s t) = lsuc S0 (s (t-1))")
    case True
    hence t1: "t \<ge> 1" by simp
    from True have lsxv: "lsx t = bef (t-1)" by (auto simp: lsx_def bef_def)
    have t1k: "t - 1 < k" using tk t1 by auto
    have "bef m \<noteq> bef (t-1)" using bef_inj[OF mk t1k] tm t1 by auto
    thus False using eq lsxv by simp
  next
    case False
    have stV: "s t \<in> V" using sV tk by simp
    have lsxv: "lsx t = lsuc S0 (s t)"
    proof (cases "t = 0")
      case True thus ?thesis by (simp add: lsx_def path0)
    next
      case Fz: False
      with False have "lsuc S0 (s t) \<noteq> lsuc S0 (s (t-1))" by simp
      thus ?thesis using Fz by (simp add: lsx_def)
    qed
    have lblk: "lsuc S0 (s t) \<in> set (block S0 (s t))"
      using block_props(2)[OF arb stV] block_props(3)[OF arb stV] by (metis last_in_set)
    have smchild: "s t \<in> children (prnt S0) (s m)"
      using stem_chain[of m t] mk tm unfolding children_def by auto
    have "set (block S0 (s t)) \<subseteq> set (block S0 (s m))"
      using children_subset[OF ppt smchild] block_props(4)[OF arb stV] block_props(4)[OF arb smV] by simp
    hence "lsx t \<in> set (block S0 (s m))" using lblk lsxv by auto
    moreover have "bef m \<notin> set (block S0 (s m))" by (rule bef_notin_block[OF mk])
    ultimately show False using eq by simp
  qed
qed

text \<open>The out-node disjointness extended to the top of the stem (@{term "t \<le> k"}, including
      @{term "t = k"} where @{term "s k = p"}): the node after a subtree is outside the stem.  Used
      to keep the genuinely-new last-successor off the bridge/up-link keys in  geom\_outnode\_fresh.\<close>
lemma out_notin_stem_le:
  assumes tk: "t \<le> k" and k0: "0 < k" and outNN: "out t \<noteq> None"
  shows "the (out t) \<notin> s ` {..k}"
proof -
  have stV: "s t \<in> V" using sV tk k0 by simp
  obtain w where outw: "out t = Some w" using outNN by auto
  have thrdw: "thrd S0 (lsuc S0 (s t)) = Some w" using outw by (simp add: out_def)
  have FUeq: "follow (thrd S0) (s t) = block S0 (s t) @ follow (thrd S0) w"
    using block_props(1)[OF arb stV] thrdw by simp
  have distFU: "distinct (follow (thrd S0) (s t))" by (rule follow_distinct_ps[OF pst])
  have wfollow: "w \<in> set (follow (thrd S0) w)"
    using follow_hd_ps[OF pst] follow_ne_ps[OF pst] by (metis hd_in_set)
  have wFU: "w \<in> set (follow (thrd S0) (s t))" using wfollow FUeq by simp
  have wnotblk: "w \<notin> set (block S0 (s t))" using distFU FUeq wfollow by auto
  have wval: "the (out t) = w" using outw by simp
  have "w \<notin> s ` {..k}"
  proof
    assume "w \<in> s ` {..k}"
    then obtain t' where t'k: "t' \<le> k" and wst': "w = s t'" by auto
    show False
    proof (cases "t' \<le> t")
      case True
      have "s t \<in> set (follow (prnt S0) (s t'))" using stem_chain[of t t'] tk True by simp
      hence "s t' \<in> children (prnt S0) (s t)" unfolding children_def by simp
      hence "s t' \<in> set (block S0 (s t))" using block_props(4)[OF arb stV] by simp
      thus False using wnotblk wst' by simp
    next
      case False
      hence tt': "t < t'" by simp
      have st'V: "s t' \<in> V" using sV t'k k0 by simp
      have "s t' \<in> set (follow (prnt S0) (s t))" using stem_chain[of t' t] t'k tt' by simp
      hence stchild: "s t \<in> children (prnt S0) (s t')" unfolding children_def by simp
      have ne: "s t' \<noteq> s t" using inj tt' t'k tk by (auto simp: inj_on_eq_iff)
      have "s t' \<notin> set (follow (thrd S0) (s t))" using anc_notin_thread_suffix[OF st'V stchild ne] by auto
      thus False using wFU wst' by simp
    qed
  qed
  thus ?thesis using wval by simp
qed

text \<open>@{text outnode_fresh} ({\isasymsection}14): a genuinely new last-successor @{term "lsuc S0 (s (Suc m))"} (i.e.
      "{\isasymnoteq} lsuc S0 (s m)") is untouched by the edits so far --- not an up-link key
      (@{const lsx}), not a bridge key (@{const bef}), and not @{term j}.  The @{const bef}/collision
      cases use that its thread-successor would be a stem node (impossible by @{thm out_notin_stem_le});
      the new-block case uses @{thm block_nest} (it lies in the tail @{term Q} beyond @{term "s m"}'s
      block);  "{\isasymnoteq} j" uses the no-cycle precondition @{thm jnotp} (it is in @{term p}'s subtree).\<close>
lemma geom_outnode_fresh:
  assumes mk: "m < k" and fresh: "lsuc S0 (s (Suc m)) \<noteq> lsuc S0 (s m)"
  shows "lsuc S0 (s (Suc m)) \<notin> lsx ` {..m}
       \<and> lsuc S0 (s (Suc m)) \<notin> bef ` {..m}
       \<and> lsuc S0 (s (Suc m)) \<noteq> j"
proof -
  let ?q = "lsuc S0 (s (Suc m))"
  have k0: "0 < k" using mk by simp
  have ssmV: "s (Suc m) \<in> V" using sV mk k0 by auto
  have smV: "s m \<in> V" using sV mk k0 by simp
  have qout: "thrd S0 ?q = out (Suc m)" by (simp add: out_def)
  have outfresh: "\<And>x. thrd S0 ?q = Some x \<Longrightarrow> x \<notin> s ` {..k}"
  proof -
    fix x assume "thrd S0 ?q = Some x"
    hence ox: "out (Suc m) = Some x" using qout by simp
    thus "x \<notin> s ` {..k}" 
      using out_notin_stem_le
      by (metis k0 less_eq_Suc_le mk option.distinct(1) option.sel)
  qed
  have child_sm: "s m \<in> children (prnt S0) (s (Suc m))"
  proof -
    have e: "follow (prnt S0) (s m) = s m # follow (prnt S0) (s (Suc m))"
      using pathS[OF mk] by (subst follow_ps_simps[OF ppt]) simp
    have "s (Suc m) \<in> set (follow (prnt S0) (s (Suc m)))"
      using follow_hd_ps[OF ppt] follow_ne_ps[OF ppt] by (metis hd_in_set)
    hence "s (Suc m) \<in> set (follow (prnt S0) (s m))" using e by simp
    thus ?thesis unfolding children_def by simp
  qed
  have sm_ne: "s m \<noteq> s (Suc m)" using inj mk by (auto simp: inj_on_eq_iff)
  obtain P Q where blkdec: "block S0 (s (Suc m)) = s (Suc m) # P @ block S0 (s m) @ Q"
    using block_nest[OF arb ssmV smV child_sm sm_ne] by auto
  have distfollow: "distinct (follow (thrd S0) (s (Suc m)))" by (rule follow_distinct_ps[OF pst])
  have blkpre: "follow (thrd S0) (s (Suc m)) = block S0 (s (Suc m)) @ (case thrd S0 (lsuc S0 (s (Suc m))) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd S0) w)"
    by (rule block_props(1)[OF arb ssmV])
  have blkdist: "distinct (block S0 (s (Suc m)))" using distfollow blkpre by (metis distinct_append)
  have qlast: "?q = last (block S0 (s (Suc m)))" by (simp add: block_props(3)[OF arb ssmV])
  have bsmne: "block S0 (s m) \<noteq> []" by (rule block_props(2)[OF arb smV])
  have Qne: "Q \<noteq> []"
  proof
    assume Qe: "Q = []"
    have "?q = last (block S0 (s m))" using qlast blkdec Qe bsmne by simp
    also have "\<dots> = lsuc S0 (s m)" by (rule block_props(3)[OF arb smV])
    finally show False using fresh by simp
  qed
  have "?q = last Q" using qlast blkdec Qne by (simp add: last_append)
  hence qQ: "?q \<in> set Q" using Qne by simp
  have disj_smQ: "set (block S0 (s m)) \<inter> set Q = {}" using blkdist unfolding blkdec by auto
  have qchild_ssm: "?q \<in> children (prnt S0) (s (Suc m))"
  proof -
    have "last (block S0 (s (Suc m))) \<in> set (block S0 (s (Suc m)))"
      using block_props(2)[OF arb ssmV] by (rule last_in_set)
    hence "?q \<in> set (block S0 (s (Suc m)))" using qlast by simp
    thus ?thesis using block_props(4)[OF arb ssmV] by simp
  qed
  have ssm_child_p: "s (Suc m) \<in> children (prnt S0) p"
    using stem_chain[of k "Suc m"] 
pathk unfolding children_def 
    using pathk mk by fastforce
  have qchild_p: "?q \<in> children (prnt S0) p"
    using children_subset[OF ppt ssm_child_p] qchild_ssm by auto
  have qj: "?q \<noteq> j" using qchild_p jnotp by auto
  have qbef: "?q \<notin> bef ` {..m}"
  proof
    assume "?q \<in> bef ` {..m}"
    then obtain t where tm: "t \<le> m" and eq: "?q = bef t" by auto
    have tk': "t < k" using tm mk by simp
    have "thrd S0 ?q = Some (s t)" using eq bef_pred(1)[OF tk'] by simp
    hence "s t \<notin> s ` {..k}" using outfresh by simp
    moreover have "s t \<in> s ` {..k}" using tk' by auto
    ultimately show False by simp
  qed
  have qlsx: "?q \<notin> lsx ` {..m}"
  proof
    assume "?q \<in> lsx ` {..m}"
    then obtain t where tm: "t \<le> m" and eq: "?q = lsx t" by auto
    have tk': "t < k" using tm mk by simp
    show False
    proof (cases "t \<noteq> 0 \<and> lsuc S0 (s t) = lsuc S0 (s (t-1))")
      case True
      hence t1: "t \<ge> 1" by simp
      from True have "lsx t = bef (t-1)" by (auto simp: lsx_def bef_def)
      hence qb: "?q = bef (t-1)" using eq by simp
      have t1k: "t - 1 < k" using tk' t1 by auto
      have "thrd S0 ?q = Some (s (t-1))" using qb bef_pred(1)[OF t1k] by simp
      hence "s (t-1) \<notin> s ` {..k}" using outfresh by simp
      moreover have "s (t-1) \<in> s ` {..k}" using t1k by auto
      ultimately show False by simp
    next
      case False
      have stV: "s t \<in> V" using sV tk' k0 by simp
      have lsxv: "lsx t = lsuc S0 (s t)"
      proof (cases "t = 0")
        case True thus ?thesis by (simp add: lsx_def path0)
      next
        case Fz: False
        with False have "lsuc S0 (s t) \<noteq> lsuc S0 (s (t-1))" by simp
        thus ?thesis using Fz by (simp add: lsx_def)
      qed
      have lblk: "lsuc S0 (s t) \<in> set (block S0 (s t))"
        using block_props(2)[OF arb stV] block_props(3)[OF arb stV] by (metis last_in_set)
      have smchild: "s t \<in> children (prnt S0) (s m)"
        using stem_chain[of m t] mk tm unfolding children_def by auto
      have "set (block S0 (s t)) \<subseteq> set (block S0 (s m))"
        using children_subset[OF ppt smchild] block_props(4)[OF arb stV] block_props(4)[OF arb smV] by simp
      hence "lsx t \<in> set (block S0 (s m))" using lblk lsxv by auto
      hence "?q \<in> set (block S0 (s m))" using eq by simp
      thus False using disj_smQ qQ by auto
    qed
  qed
  show ?thesis using qlsx qbef qj by simp
qed

end

text \<open>Discharge: every @{locale stem_setup} is a @{locale stem_setup_geom}.  The three {\isasymsection}14 locality
      obligations now hold from @{const arb_invar}, the path, and the no-cycle precondition
      @{thm stem_setup.jnotp} alone, so the whole {\isasymsection}13 stem-loop development is available unconditionally.\<close>
sublocale stem_setup \<subseteq> stem_setup_geom
  using geom_out_notin_stem geom_bef_notin_lsx geom_outnode_fresh
  by unfold_locales blast+

subsection \<open>Clause A: the new parent map is a rooted arborescence (output side, {\isasymsection}15.5)\<close>

text \<open>The new parent map reverses the stem path  "i = s 0, {\isasymdots}, s k = p" to
       "p {\isasymrightarrow} s (k-1) {\isasymrightarrow} {\isasymdots} {\isasymrightarrow} s 0 = i {\isasymrightarrow} j", i.e. it is @{term "prnt S0"} overwritten with
      "s t {\isasymmapsto} s\_pred t" for every @{term "t \<le> k"} (= @{term "prnt S0 ++ REV k"} plus the
      top edit  "p {\isasymmapsto} s\_pred k").  Clause A is proved by replaying this as @{term "k+1"}
      single-edge swaps (@{thm rooted_arborescense_swap_parents}) \<^emph>\<open>bottom-up\<close> (@{term i} first):
      each step re-parents @{term "s m"} to @{term "s_pred m"}, which is legal because @{term "s m"}
      is never an ancestor of @{term "s_pred m"} in the partially-reversed tree.  The load-bearing
      geometric fact is that no stem node is an ancestor of @{term j} (else @{term j} would lie in
      @{term p}'s detached subtree, contradicting the no-cycle precondition @{thm stem_setup.jnotp}).\<close>

text \<open>Editing a key that does not lie on a node's root-path leaves that root-path unchanged: the
      @{const follow} climb never consults the edited key.  This is the engine that lets each
      bottom-up swap leave the already-reversed suffix of the path untouched.\<close>
lemma follow_upd_fresh:
  assumes ps: "parent_spec T" and ps': "parent_spec (T(x \<mapsto> y))"
  shows "x \<notin> set (follow T v) \<longrightarrow> follow (T(x \<mapsto> y)) v = follow T v"
proof (induction rule: parent_spec_i.follow.pinduct[OF follow_dom_ps[OF ps, of v]])
  case (1 v)
  show ?case
  proof (intro impI)
    assume xni: "x \<notin> set (follow T v)"
    have vin: "v \<in> set (follow T v)" using follow_hd_ps[OF ps] follow_ne_ps[OF ps] by (metis hd_in_set)
    with xni have vnx: "v \<noteq> x" by auto
    show "follow (T(x \<mapsto> y)) v = follow T v"
    proof (cases "T v")
      case None
      hence f1: "follow T v = [v]" by (subst follow_ps_simps[OF ps]) simp
      have "(T(x \<mapsto> y)) v = None" using None vnx by simp
      hence "follow (T(x \<mapsto> y)) v = [v]" by (subst follow_ps_simps[OF ps']) simp
      thus ?thesis using f1 by simp
    next
      case (Some w)
      hence fTv: "follow T v = v # follow T w" by (subst follow_ps_simps[OF ps]) simp
      have xnw: "x \<notin> set (follow T w)" using xni fTv by simp
      have IH: "follow (T(x \<mapsto> y)) w = follow T w" using 1(2)[OF Some] xnw by (rule mp)
      have "(T(x \<mapsto> y)) v = Some w" using Some vnx by simp
      hence "follow (T(x \<mapsto> y)) v = v # follow (T(x \<mapsto> y)) w" by (subst follow_ps_simps[OF ps']) simp
      thus ?thesis using IH fTv by simp
    qed
  qed
qed

text \<open>The root-path of any @{term V}-node ends at the root @{term r} (the unique node with no
      parent): walk up the parent chain, which stays in @{term V} and terminates at @{term r}.\<close>
lemma last_follow_root:
  assumes rinv: "rooted_arborescense_invar r V T" and vV: "v \<in> V"
  shows "last (follow T v) = r"
proof -
  have ps: "parent_spec T" using rinv by (rule rooted_arborescense_invar_parent_spec)
  have rangeV: "\<And>w w'. T w = Some w' \<Longrightarrow> w' \<in> V"
  proof -
    fix w w' assume "T w = Some w'"
    hence "(w, w') \<in> {(y, x) |x y. Some x = T y}" by auto
    thus "w' \<in> V" using rooted_arborescense_invar_dVs[OF rinv] by (auto simp: dVs_def)
  qed
  have domT: "dom T = V - {r}" by (rule rooted_arborescense_invar_dom[OF rinv])
  have "v \<in> V \<longrightarrow> last (follow T v) = r"
  proof (induction rule: parent_spec_i.follow.pinduct[OF follow_dom_ps[OF ps, of v]])
    case (1 v)
    show ?case
    proof (intro impI)
      assume vV': "v \<in> V"
      show "last (follow T v) = r"
      proof (cases "T v")
        case None
        hence "v \<notin> dom T" by auto
        hence "v = r" using vV' domT by auto
        thus ?thesis using None by (subst follow_ps_simps[OF ps]) simp
      next
        case (Some w)
        have wV: "w \<in> V" using rangeV Some by simp
        have IH: "last (follow T w) = r" using 1(2)[OF Some] wV by simp
        have ne: "follow T w \<noteq> []" using follow_ne_ps[OF ps] by simp
        show ?thesis using Some IH ne by (subst follow_ps_simps[OF ps]) simp
      qed
    qed
  qed
  thus ?thesis using vV by simp
qed

context stem_setup begin

lemma stem_notin_follow_j:
  assumes "m \<le> k" shows "s m \<notin> set (follow (prnt S0) j)"
proof
  assume "s m \<in> set (follow (prnt S0) j)"
  hence jchild: "j \<in> children (prnt S0) (s m)" unfolding children_def by simp
  have "p \<in> set (follow (prnt S0) (s m))" using stem_chain[of k m] assms pathk by simp
  hence smp: "s m \<in> children (prnt S0) p" unfolding children_def by simp
  have "children (prnt S0) (s m) \<subseteq> children (prnt S0) p"
    by (rule children_subset[OF ppt smp])
  hence "j \<in> children (prnt S0) p" using jchild by auto
  thus False using jnotp by simp
qed

text \<open>The bottom-up swap sequence: @{term "Wseq m"} is @{term "prnt S0"} after re-parenting
       "s 0, {\isasymdots}, s (m-1)" (each  "s t {\isasymmapsto} s\_pred t").  @{term "Wseq (Suc k)"} is the
      fully-reversed new parent map.\<close>
definition Wseq :: "nat \<Rightarrow> ('a \<rightharpoonup> 'a)" where
  "Wseq m = fold (\<lambda>t T. T(s t \<mapsto> s_pred t)) [0..<m] (prnt S0)"

lemma Wseq_0: "Wseq 0 = prnt S0" by (simp add: Wseq_def)

lemma Wseq_Suc: "Wseq (Suc m) = (Wseq m)(s m \<mapsto> s_pred m)"
  by (simp add: Wseq_def upt_Suc_append)

text \<open>Evaluation of @{const Wseq}: keys outside @{term "s ` {..<m}"} keep their @{term S0} parent; the
      re-parented keys @{term "s t"} (@{term "t < m"}) point to @{term "s_pred t"}.\<close>
lemma Wseq_fresh: "(\<And>t. t < m \<Longrightarrow> x \<noteq> s t) \<Longrightarrow> Wseq m x = prnt S0 x"
  by (induction m) (auto simp: Wseq_0 Wseq_Suc)

lemma Wseq_eval: "m \<le> Suc k \<Longrightarrow> t < m \<Longrightarrow> Wseq m (s t) = Some (s_pred t)"
proof (induction m)
  case 0 thus ?case by simp
next
  case (Suc m)
  hence mk: "m \<le> k" by simp
  show ?case
  proof (cases "t = m")
    case True thus ?thesis by (simp add: Wseq_Suc)
  next
    case False
    hence tm: "t < m" using Suc.prems(2) by simp
    have "s t \<noteq> s m" using tm mk inj by (auto simp: inj_on_eq_iff)
    thus ?thesis using mk tm Suc.IH by (simp add: Wseq_Suc)
  qed
qed

text \<open>@{term p} is a vertex (interior of the stem when @{term "0 < k"}; otherwise @{term "p = i"}).\<close>
lemma pV: "p \<in> V"
  by (cases "0 < k") (use sV[OF order_refl] pathk path0 iV in auto)

text \<open>Every stem node still has a parent in @{term S0} (the interior nodes by @{thm pathS}; the top
      @{term "p = s k"} because @{term "p \<noteq> r"} and @{term "p \<in> V"}).  This is the @{term "Some pu = T u"}
      side-condition of the bottom-up swap at each step.\<close>
lemma prnt_sm_ne_None:
  assumes "m \<le> k" shows "prnt S0 (s m) \<noteq> None"
proof (cases "m < k")
  case True thus ?thesis using pathS[OF True] by simp
next
  case False
  hence "m = k" using assms by simp
  hence smp: "s m = p" using pathk by simp
  have rinv: "rooted_arborescense_invar r V (prnt S0)" using arb unfolding arb_invar_def by simp
  have "dom (prnt S0) = V - {r}" by (rule rooted_arborescense_invar_dom[OF rinv])
  hence "p \<in> dom (prnt S0)" using pV pne_r by simp
  thus ?thesis using smp by auto
qed

text \<open>The swap target @{term "s_pred m"} is a vertex (@{term j} for @{term "m = 0"}; an interior stem
      node otherwise).\<close>
lemma s_pred_in_V:
  assumes "m \<le> k" shows "s_pred m \<in> V"
  by (cases "m = 0") (use jV sV[of "m-1"] assms in \<open>auto simp: s_pred_def\<close>)

text \<open>The heart of clause A: each bottom-up swap preserves the rooted-arborescence invariant, and the
      root-path of the just-attached node @{term "s_pred m"} is exactly the already-reversed prefix
      @{term "s ` {..<m}"} followed by @{term j}'s @{term S0}-root-path.  Proved by simultaneous
      induction: the invariant gives @{const parent_spec} for the legality check of the next swap
      (@{term "s m"} is fresh on the path: not among @{term "s ` {..<m}"} by injectivity, nor an
      ancestor of @{term j} by @{thm stem_notin_follow_j}); the path equation is maintained because
      the new edge "s m {\isasymmapsto} s\_pred m" does not touch the existing path (@{thm follow_upd_fresh}).\<close>
lemma Wseq_step:
  "m \<le> Suc k \<Longrightarrow>
     rooted_arborescense_invar r V (Wseq m)
   \<and> set (follow (Wseq m) (s_pred m)) = s ` {..<m} \<union> set (follow (prnt S0) j)"
proof (induction m)
  case 0
  have inv0: "rooted_arborescense_invar r V (Wseq 0)"
    using arb unfolding arb_invar_def by (simp add: Wseq_0)
  have "set (follow (Wseq 0) (s_pred 0)) = set (follow (prnt S0) j)"
    by (simp add: Wseq_0 s_pred_def)
  thus ?case using inv0 by simp
next
  case (Suc m)
  hence mk: "m \<le> k" by simp
  have IHinv: "rooted_arborescense_invar r V (Wseq m)" using Suc.IH mk by simp
  have IHset: "set (follow (Wseq m) (s_pred m)) = s ` {..<m} \<union> set (follow (prnt S0) j)"
    using Suc.IH mk by simp
  have psm: "parent_spec (Wseq m)" using IHinv by (rule rooted_arborescense_invar_parent_spec)
  have a: "s m \<notin> s ` {..<m}"
  proof
    assume "s m \<in> s ` {..<m}"
    then obtain t where tm: "t < m" "s t = s m" by auto
    hence "t = m" using inj mk by (auto simp: inj_on_eq_iff)
    with tm show False by simp
  qed
  have smnotin: "s m \<notin> set (follow (Wseq m) (s_pred m))"
    using IHset a stem_notin_follow_j[OF mk] by simp
  have sp_V: "s_pred m \<in> V" using s_pred_in_V[OF mk] by auto
  obtain pu where pu: "prnt S0 (s m) = Some pu" using prnt_sm_ne_None[OF mk] by auto
  have Wsm: "Wseq m (s m) = Some pu"
  proof -
    have "Wseq m (s m) = prnt S0 (s m)"
      by (rule Wseq_fresh) (use inj mk in \<open>auto simp: inj_on_eq_iff\<close>)
    thus ?thesis using pu by simp
  qed
  have invSuc: "rooted_arborescense_invar r V (Wseq (Suc m))"
    using rooted_arborescense_swap_parents(1)[OF IHinv Wsm[symmetric] smnotin sp_V]
    by (simp add: Wseq_Suc)
  have psSuc': "parent_spec ((Wseq m)(s m \<mapsto> s_pred m))"
    using invSuc rooted_arborescense_invar_parent_spec by (simp add: Wseq_Suc)
  have fresh: "follow ((Wseq m)(s m \<mapsto> s_pred m)) (s_pred m) = follow (Wseq m) (s_pred m)"
    using follow_upd_fresh[OF psm psSuc'] smnotin by (rule mp)
  have WsucSm: "Wseq (Suc m) (s m) = Some (s_pred m)" by (simp add: Wseq_Suc)
  have psSuc: "parent_spec (Wseq (Suc m))" using invSuc by (rule rooted_arborescense_invar_parent_spec)
  have listeq: "follow (Wseq (Suc m)) (s_pred (Suc m)) = s m # follow (Wseq m) (s_pred m)"
  proof -
    have "follow (Wseq (Suc m)) (s_pred (Suc m)) = follow (Wseq (Suc m)) (s m)"
      by (simp add: s_pred_def)
    also have "\<dots> = s m # follow (Wseq (Suc m)) (s_pred m)"
      using WsucSm by (subst follow_ps_simps[OF psSuc]) simp
    also have "\<dots> = s m # follow (Wseq m) (s_pred m)"
      using fresh by (simp add: Wseq_Suc)
    finally show ?thesis .
  qed
  have "set (follow (Wseq (Suc m)) (s_pred (Suc m))) = s ` {..<Suc m} \<union> set (follow (prnt S0) j)"
    using listeq IHset by (auto simp: lessThan_Suc)
  thus ?case using invSuc by simp
qed

text \<open>@{const REV} gains its top link too (the @{term "t = m"} key @{term "s m"} is fresh for
      @{term "m \<le> k"}, by injectivity); the @{term "m < k"} form is @{thm REV_Suc}.\<close>
lemma REV_Suc_le:
  assumes "m \<le> k" shows "REV (Suc m) = (REV m)(s m \<mapsto> s_pred m)"
proof -
  have dom: "s m \<notin> fst ` set (map (\<lambda>t. (s t, s_pred t)) [0..<m])"
  proof
    assume "s m \<in> fst ` set (map (\<lambda>t. (s t, s_pred t)) [0..<m])"
    then obtain t where "t < m" "s t = s m" by auto
    hence "m = t" using inj \<open>m \<le> k\<close> by (auto simp: inj_on_eq_iff)
    with \<open>t < m\<close> show False by simp
  qed
  have "REV (Suc m) = map_of (map (\<lambda>t. (s t, s_pred t)) [0..<m] @ [(s m, s_pred m)])"
    by (simp add: REV_def)
  also have "\<dots> = (REV m)(s m \<mapsto> s_pred m)"
    using map_of_snoc_upd[OF dom] by (simp add: REV_def)
  finally show ?thesis .
qed

text \<open>The bottom-up swap sequence is exactly the closed-form @{term "prnt S0 ++ REV m"} used by the
      stem invariant ({\isasymsection}13), so the two developments agree on the parent map.\<close>
lemma Wseq_eq_REV: "m \<le> Suc k \<Longrightarrow> Wseq m = prnt S0 ++ REV m"
proof (induction m)
  case 0 thus ?case by (simp add: Wseq_0 REV_0)
next
  case (Suc m)
  hence mk: "m \<le> k" by simp
  have "Wseq (Suc m) = (prnt S0 ++ REV m)(s m \<mapsto> s_pred m)"
    using Suc.IH mk by (simp add: Wseq_Suc)
  also have "\<dots> = prnt S0 ++ (REV m)(s m \<mapsto> s_pred m)" by simp
  also have "\<dots> = prnt S0 ++ REV (Suc m)" using REV_Suc_le[OF mk] by simp
  finally show ?case .
qed

text \<open>The fully-reversed new parent map (= @{term "prnt Sp"} in @{const update_tree}): the {\isasymsection}13 stem
      map @{term "prnt S0 ++ REV k"} with the top edit  "p {\isasymmapsto} s\_pred k".\<close>
lemma newprnt_eq: "Wseq (Suc k) = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)"
proof -
  show ?thesis using Wseq_eq_REV[of "Suc k"] REV_Suc_le[of k] pathk by simp
qed

text \<open>Clause A: the new parent map is a rooted arborescence on @{term V} rooted @{term r}.\<close>
lemma clauseA: "rooted_arborescense_invar r V ((prnt S0 ++ REV k)(p \<mapsto> s_pred k))"
  using Wseq_step[of "Suc k"] by (simp add: newprnt_eq)

text \<open>The reversed stem is a genuine new-parent path from @{term p} down to @{term i}: the
      @{const stem_num_loop} that recomputes @{const snum}/@{const lsuc} walks it, so it needs
      @{term i} reachable from @{term p} in the reversed parent map (walked by the num loop).\<close>
lemma i_in_follow_newprnt:
  shows "i \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) p)"
proof -
  have sp: "s_pred (Suc k) = p" using pathk by (simp add: s_pred_def)
  have step: "set (follow (Wseq (Suc k)) (s_pred (Suc k))) = s ` {..<Suc k} \<union> set (follow (prnt S0) j)"
    using Wseq_step[of "Suc k"] by simp
  have "i \<in> s ` {..<Suc k}" using path0 by (metis image_eqI lessThan_iff zero_less_Suc)
  hence "i \<in> set (follow (Wseq (Suc k)) (s_pred (Suc k)))" using step by simp
  thus ?thesis using sp newprnt_eq by simp
qed

text \<open>The pivot leaves @{term j}'s root-path unchanged: no stem node lies on it (@{thm stem_notin_follow_j}),
      and off the stem the reversed map agrees with @{term "prnt S0"} (@{thm Wseq_fresh}).\<close>
lemma follow_newprnt_j:
  shows "follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) j = follow (prnt S0) j"
proof -
  have psN: "parent_spec ((prnt S0 ++ REV k)(p \<mapsto> s_pred k))"
    using clauseA rooted_arborescense_invar_parent_spec by auto
  have agree: "\<forall>y\<in>set (follow (prnt S0) j). prnt S0 y = ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) y"
  proof
    fix y assume yin: "y \<in> set (follow (prnt S0) j)"
    have "\<And>t. t < Suc k \<Longrightarrow> y \<noteq> s t"
    proof -
      fix t assume "t < Suc k"
      hence "t \<le> k" by simp
      thus "y \<noteq> s t" using stem_notin_follow_j[of t] yin by auto
    qed
    hence "Wseq (Suc k) y = prnt S0 y" using Wseq_fresh[of "Suc k" y] by auto
    thus "prnt S0 y = ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) y" using newprnt_eq by simp
  qed
  have "follow (prnt S0) j = follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) j"
    using follow_eq_on[OF ppt psN, of j] agree by (rule mp)
  thus ?thesis by simp
qed

text \<open>The rightmost-spine lemma: if @{term w} is the last descendant of @{term a} and @{term b}
      lies on the path from @{term w} up to @{term a}, then @{term w} is also @{term b}'s last
      descendant (blocks nest as infixes; @{term w} being the global last of @{term a}'s block
      forces @{term b}'s block to end there).\<close>
lemma spine_lemma:
  assumes aw: "lsuc S0 a = w" and aV: "a \<in> V" and bV: "b \<in> V"
      and bw: "b \<in> set (follow (prnt S0) w)" and ab: "a \<in> set (follow (prnt S0) b)"
  shows "lsuc S0 b = w"
proof (cases "b = a")
  case True thus ?thesis using aw by simp
next
  case False
  have wchild: "w \<in> children (prnt S0) b" using bw unfolding children_def by simp
  have bchild: "b \<in> children (prnt S0) a" using ab unfolding children_def by simp
  have wblkb: "w \<in> set (block S0 b)" using block_props(4)[OF arb bV] wchild by simp
  obtain A B where AB: "block S0 a = A @ block S0 b @ B"
    using block_self_similar[OF arb aV bV bchild False] by auto
  have lasteq: "last (block S0 a) = w" using block_props(3)[OF arb aV] aw by simp
  have "follow (thrd S0) a = block S0 a @ (case thrd S0 (lsuc S0 a) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd S0) w)"
    using block_props(1)[OF arb aV] by auto
  hence "\<exists>C. follow (thrd S0) a = block S0 a @ C" by auto
  then obtain C where fC: "follow (thrd S0) a = block S0 a @ C" by auto
  have dist_a: "distinct (block S0 a)" using follow_distinct_ps[OF pst] fC by (metis distinct_append)
  have Bnil: "B = []"
  proof (rule ccontr)
    assume "B \<noteq> []"
    hence "last (block S0 a) = last B" using AB by simp
    hence wB: "w \<in> set B" using lasteq \<open>B \<noteq> []\<close> by (metis last_in_set)
    have "distinct (A @ block S0 b @ B)" using dist_a AB by simp
    hence "set (block S0 b) \<inter> set B = {}" by auto
    thus False using wblkb wB by auto
  qed
  have "last (block S0 a) = last (block S0 b)"
    using AB Bnil block_props(2)[OF arb bV] by simp
  thus ?thesis using lasteq block_props(3)[OF arb bV] by simp
qed

text \<open>No stem node lies on @{term "the (prnt S0 p)"}'s root-path: the stem is inside @{term p}'s
      subtree, while @{term "the (prnt S0 p)"}'s ancestors are all proper ancestors of @{term p}.\<close>
lemma stem_notin_follow_vout:
  assumes kpos: "0 < k" and mk: "m \<le> k"
  shows "s m \<notin> set (follow (prnt S0) (the (prnt S0 p)))"
proof
  assume asm: "s m \<in> set (follow (prnt S0) (the (prnt S0 p)))"
  have pV: "p \<in> V" using sV[of k] kpos pathk by simp
  have rinv: "rooted_arborescense_invar r V (prnt S0)" using arb unfolding arb_invar_def by simp
  have "dom (prnt S0) = V - {r}" by (rule rooted_arborescense_invar_dom[OF rinv])
  hence "p \<in> dom (prnt S0)" using pV pne_r by simp
  then obtain vo where vo: "prnt S0 p = Some vo" by auto
  have smvo: "s m \<in> set (follow (prnt S0) vo)" using asm vo by simp
  have chain: "p \<in> set (follow (prnt S0) (s m))" using stem_chain[of k m] mk pathk by simp
  have "p \<in> set (follow (prnt S0) vo)" using follow_trans[OF ppt smvo chain] by auto
  moreover have "follow (prnt S0) p = p # follow (prnt S0) vo" using vo by (subst follow_ps_simps[OF ppt]) simp
  ultimately show False using follow_distinct_ps[OF ppt, of p] by simp
qed

text \<open>Consequently the pivot leaves @{term "the (prnt S0 p)"}'s root-path unchanged too (cf.
      @{thm follow_newprnt_j}).\<close>
lemma follow_newprnt_vout:
  assumes kpos: "0 < k"
  shows "follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (the (prnt S0 p)) = follow (prnt S0) (the (prnt S0 p))"
proof -
  have psN: "parent_spec ((prnt S0 ++ REV k)(p \<mapsto> s_pred k))"
    using clauseA rooted_arborescense_invar_parent_spec by auto
  have agree: "\<forall>y\<in>set (follow (prnt S0) (the (prnt S0 p))). prnt S0 y = ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) y"
  proof
    fix y assume yin: "y \<in> set (follow (prnt S0) (the (prnt S0 p)))"
    have "\<And>t. t < Suc k \<Longrightarrow> y \<noteq> s t"
    proof -
      fix t assume "t < Suc k"
      hence "t \<le> k" by simp
      thus "y \<noteq> s t" using stem_notin_follow_vout[OF kpos, of t] yin by auto
    qed
    hence "Wseq (Suc k) y = prnt S0 y" using Wseq_fresh[of "Suc k" y] by auto
    thus "prnt S0 y = ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) y" using newprnt_eq by simp
  qed
  have "follow (prnt S0) (the (prnt S0 p)) = follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (the (prnt S0 p))"
    using follow_eq_on[OF ppt psN] agree by (rule mp)
  thus ?thesis by simp
qed

text \<open>General form (subsumes @{thm follow_newprnt_j}, @{thm follow_newprnt_vout}): any node whose old
      root-path contains no stem node keeps that root-path under the reversed parent map --- the
      structural input for clause I's descendant-set transformation.\<close>
lemma follow_newprnt_free:
  assumes free: "\<forall>m\<le>k. s m \<notin> set (follow (prnt S0) u)"
  shows "follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u = follow (prnt S0) u"
proof -
  have psN: "parent_spec ((prnt S0 ++ REV k)(p \<mapsto> s_pred k))"
    using clauseA rooted_arborescense_invar_parent_spec by auto
  have agree: "\<forall>y\<in>set (follow (prnt S0) u). prnt S0 y = ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) y"
  proof
    fix y assume yin: "y \<in> set (follow (prnt S0) u)"
    have "\<And>t. t < Suc k \<Longrightarrow> y \<noteq> s t"
    proof -
      fix t assume "t < Suc k"
      hence "t \<le> k" by simp
      thus "y \<noteq> s t" using free yin by auto
    qed
    hence "Wseq (Suc k) y = prnt S0 y" using Wseq_fresh[of "Suc k" y] by auto
    thus "prnt S0 y = ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) y" using newprnt_eq by simp
  qed
  have "follow (prnt S0) u = follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u"
    using follow_eq_on[OF ppt psN] agree by (rule mp)
  thus ?thesis by simp
qed

text \<open>The explicit list realised by the reversed parent chain from p: the reversed stem
      s k, ..., s 0 followed by j's old root-path.  Re-derives the list step
      (Wseq\_step only exposes the set) so the num loop's walk can be pinned to the stem.\<close>
lemma Wseq_follow_list:
  "m \<le> Suc k \<Longrightarrow> follow (Wseq m) (s_pred m) = map s (rev [0..<m]) @ follow (prnt S0) j"
proof (induction m)
  case 0
  show ?case by (simp add: Wseq_0 s_pred_def)
next
  case (Suc m)
  hence mk: "m \<le> k" by simp
  have inv_m: "rooted_arborescense_invar r V (Wseq m)" using Wseq_step[of m] mk by simp
  have ps_m: "parent_spec (Wseq m)" using inv_m by (rule rooted_arborescense_invar_parent_spec)
  have set_m: "set (follow (Wseq m) (s_pred m)) = s ` {..<m} \<union> set (follow (prnt S0) j)"
    using Wseq_step[of m] mk by simp
  have a: "s m \<notin> s ` {..<m}"
  proof
    assume "s m \<in> s ` {..<m}"
    then obtain t where "t < m" "s t = s m" by auto
    hence "t = m" using inj mk by (auto simp: inj_on_eq_iff)
    thus False using \<open>t < m\<close> by simp
  qed
  have smnotin: "s m \<notin> set (follow (Wseq m) (s_pred m))"
    using set_m a stem_notin_follow_j[OF mk] by simp
  have invSuc: "rooted_arborescense_invar r V (Wseq (Suc m))" using Wseq_step[of "Suc m"] Suc.prems by simp
  have ps_Suc: "parent_spec (Wseq (Suc m))" using invSuc by (rule rooted_arborescense_invar_parent_spec)
  have ps_Suc': "parent_spec ((Wseq m)(s m \<mapsto> s_pred m))" using ps_Suc by (simp add: Wseq_Suc)
  have WsucSm: "Wseq (Suc m) (s m) = Some (s_pred m)" by (simp add: Wseq_Suc)
  have fresh: "follow ((Wseq m)(s m \<mapsto> s_pred m)) (s_pred m) = follow (Wseq m) (s_pred m)"
    using follow_upd_fresh[OF ps_m ps_Suc'] smnotin by (rule mp)
  have "follow (Wseq (Suc m)) (s_pred (Suc m)) = follow (Wseq (Suc m)) (s m)"
    by (simp add: s_pred_def)
  also have "\<dots> = s m # follow (Wseq (Suc m)) (s_pred m)"
    using WsucSm by (subst follow_ps_simps[OF ps_Suc]) simp
  also have "\<dots> = s m # follow (Wseq m) (s_pred m)"
    using fresh by (simp add: Wseq_Suc)
  also have "\<dots> = s m # (map s (rev [0..<m]) @ follow (prnt S0) j)"
    using Suc.IH mk by simp
  also have "\<dots> = map s (rev [0..<Suc m]) @ follow (prnt S0) j"
    by simp
  finally show ?case .
qed

text \<open>Subtree-size monotonicity along the walked stem: for each stem node @{term "s t"} strictly
      above @{term i}, its new parent @{term "s (t-1)"} was an old child, so its old subtree is no
      larger.  This is exactly the hypothesis @{thm stem_num_loop_snum} needs (only on the walked
      @{const takeWhile} chain, which stops at @{term i}).\<close>
lemma stem_chain_snum_mono:
  "\<forall> y \<in> set (takeWhile (\<lambda>z. z \<noteq> i) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) p)).
      ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) y \<noteq> None
      \<longrightarrow> snum S0 (the (((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) y)) \<le> snum S0 y"
proof (intro ballI impI)
  fix y
  assume yin: "y \<in> set (takeWhile (\<lambda>z. z \<noteq> i) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) p))"
  have sp: "s_pred (Suc k) = p" using pathk by (simp add: s_pred_def)
  have fl: "follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) p = map s (rev [0..<Suc k]) @ follow (prnt S0) j"
    using Wseq_follow_list[of "Suc k"] sp newprnt_eq by simp
  have split: "map s (rev [0..<Suc k]) = map s (rev [1..<Suc k]) @ [s 0]"
    by (simp add: upt_rec)
  have setimg: "set (map s (rev [1..<Suc k])) = s ` {1..<Suc k}"
    by (simp only: set_map set_rev set_upt)
  have allne: "\<And>a. a \<in> set (map s (rev [1..<Suc k])) \<Longrightarrow> a \<noteq> i"
  proof -
    fix a assume "a \<in> set (map s (rev [1..<Suc k]))"
    hence "a \<in> s ` {1..<Suc k}" using setimg by simp
    then obtain x where xr: "x \<in> {1..<Suc k}" and ax: "a = s x" by auto
    have "x \<noteq> 0" using xr by auto
    moreover have "x \<in> {..k}" "(0::nat) \<in> {..k}" using xr by auto
    ultimately have "s x \<noteq> s 0" using inj by (auto simp: inj_on_eq_iff)
    thus "a \<noteq> i" using ax path0 by simp
  qed
  have flsplit: "follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) p
                 = map s (rev [1..<Suc k]) @ (i # follow (prnt S0) j)"
    using fl split path0 by simp
  have chain_eq: "takeWhile (\<lambda>z. z \<noteq> i) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) p)
                  = map s (rev [1..<Suc k])"
  proof -
    have "takeWhile (\<lambda>z. z \<noteq> i) (map s (rev [1..<Suc k]) @ (i # follow (prnt S0) j))
          = map s (rev [1..<Suc k]) @ takeWhile (\<lambda>z. z \<noteq> i) (i # follow (prnt S0) j)"
      by (rule takeWhile_append2) (use allne in auto)
    thus ?thesis using flsplit by simp
  qed
  from yin chain_eq have "y \<in> s ` {1..<Suc k}" using setimg by simp
  then obtain t where tt: "t \<in> {1..<Suc k}" and yt: "y = s t" by auto
  have t1: "1 \<le> t" and tk: "t \<le> k" using tt by auto
  have kpos: "0 < k" using t1 tk by simp
  have npv: "((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (s t) = Some (s_pred t)"
    using Wseq_eval[of "Suc k" t] tt newprnt_eq by simp
  have spt: "s_pred t = s (t - 1)" using t1 by (simp add: s_pred_def)
  have tm1k: "t - 1 < k" using t1 tk by simp
  have child: "prnt S0 (s (t - 1)) = Some (s t)"
    using pathS[OF tm1k] t1 by simp
  have stm1_child: "s (t - 1) \<in> children (prnt S0) (s t)"
  proof -
    have "follow (prnt S0) (s (t - 1)) = s (t - 1) # follow (prnt S0) (s t)"
      using child by (subst follow_ps_simps[OF ppt]) simp
    moreover have "s t \<in> set (follow (prnt S0) (s t))"
      using follow_hd_ps[OF ppt, of "s t"] follow_ne_ps[OF ppt, of "s t"] by (metis hd_in_set)
    ultimately have "s t \<in> set (follow (prnt S0) (s (t - 1)))" by simp
    thus ?thesis unfolding children_def by simp
  qed
  have sub: "children (prnt S0) (s (t - 1)) \<subseteq> children (prnt S0) (s t)"
    by (rule children_subset[OF ppt stm1_child])
  have stV: "s t \<in> V" using sV[of t] tk kpos by simp
  have stm1V: "s (t - 1) \<in> V" using sV[of "t - 1"] tm1k kpos by simp
  have finV: "finite V" using arb unfolding arb_invar_def by (metis List.finite_set)
  have rinv: "rooted_arborescense_invar r V (prnt S0)" using arb unfolding arb_invar_def by simp
  have domeq: "dom (prnt S0) = V - {r}" by (rule rooted_arborescense_invar_dom[OF rinv])
  have chsub: "children (prnt S0) (s t) \<subseteq> V"
  proof
    fix u assume "u \<in> children (prnt S0) (s t)"
    hence stf: "s t \<in> set (follow (prnt S0) u)" unfolding children_def by simp
    show "u \<in> V"
    proof (rule ccontr)
      assume "u \<notin> V"
      hence "prnt S0 u = None" using domeq by auto
      hence "follow (prnt S0) u = [u]" by (subst follow_ps_simps[OF ppt]) simp
      hence "s t = u" using stf by simp
      thus False using stV \<open>u \<notin> V\<close> by simp
    qed
  qed
  have finB: "finite (children (prnt S0) (s t))" using chsub finV by (rule finite_subset)
  have cardmono: "card (children (prnt S0) (s (t - 1))) \<le> card (children (prnt S0) (s t))"
    by (rule card_mono[OF finB sub])
  have I: "\<forall>v \<in> V. snum S0 v = card (children (prnt S0) v)" using arb unfolding arb_invar_def by simp
  have "snum S0 (s (t - 1)) = card (children (prnt S0) (s (t - 1)))" using I stm1V by simp
  moreover have "snum S0 (s t) = card (children (prnt S0) (s t))" using I stV by simp
  ultimately have "snum S0 (s (t - 1)) \<le> snum S0 (s t)" using cardmono by simp
  thus "snum S0 (the (((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) y)) \<le> snum S0 y"
    using yt npv spt by simp
qed

text \<open>Geometric facts for the clause-E root analysis: the root and the apex @{term jn} are not stem
      nodes; @{term jn} lies on @{term "the (prnt S0 p)"}'s root-path; and the walked stem-chain and
      its parent-image sit inside @{term "s ` {..k}"}.\<close>
lemma r_notin_stem:
  assumes kpos: "0 < k" shows "r \<notin> s ` {..k}"
proof
  assume "r \<in> s ` {..k}"
  then obtain m where mk: "m \<le> k" and rm: "r = s m" by auto
  have "p \<in> set (follow (prnt S0) (s m))" using stem_chain[of k m] mk pathk by simp
  hence pr: "p \<in> set (follow (prnt S0) r)" using rm by simp
  have rinv: "rooted_arborescense_invar r V (prnt S0)" using arb unfolding arb_invar_def by simp
  have "dom (prnt S0) = V - {r}" by (rule rooted_arborescense_invar_dom[OF rinv])
  hence "prnt S0 r = None" by auto
  hence "follow (prnt S0) r = [r]" by (subst follow_ps_simps[OF ppt]) simp
  thus False using pr pne_r by simp
qed

lemma jn_notin_stem:
  assumes jnp: "jn \<in> set (follow (prnt S0) p)" and pjn: "p \<noteq> jn" shows "jn \<notin> s ` {..k}"
proof
  assume "jn \<in> s ` {..k}"
  then obtain m where mk: "m \<le> k" and jm: "jn = s m" by auto
  have "p \<in> set (follow (prnt S0) (s m))" using stem_chain[of k m] mk pathk by simp
  hence "p \<in> set (follow (prnt S0) jn)" using jm by simp
  hence "jn = p" using ancestor_antisym[OF ppt] jnp by simp
  thus False using pjn by simp
qed

lemma jn_on_vout:
  assumes kpos: "0 < k" and jnp: "jn \<in> set (follow (prnt S0) p)" and pjn: "p \<noteq> jn"
  shows "jn \<in> set (follow (prnt S0) (the (prnt S0 p)))"
proof -
  have pV: "p \<in> V" using sV[of k] kpos pathk by simp
  have rinv: "rooted_arborescense_invar r V (prnt S0)" using arb unfolding arb_invar_def by simp
  have "dom (prnt S0) = V - {r}" by (rule rooted_arborescense_invar_dom[OF rinv])
  hence "p \<in> dom (prnt S0)" using pV pne_r by simp
  then obtain vo where vo: "prnt S0 p = Some vo" by auto
  have "follow (prnt S0) p = p # follow (prnt S0) vo" using vo by (subst follow_ps_simps[OF ppt]) simp
  hence "jn \<in> set (p # follow (prnt S0) vo)" using jnp by simp
  hence "jn \<in> set (follow (prnt S0) vo)" using pjn by auto
  thus ?thesis using vo by simp
qed

lemma chainStem_set:
  assumes kpos: "0 < k"
  shows "set (takeWhile (\<lambda>x. x \<noteq> i) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) p)) = s ` {1..<Suc k}"
proof -
  have sp: "s_pred (Suc k) = p" using pathk by (simp add: s_pred_def)
  have fl: "follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) p = map s (rev [0..<Suc k]) @ follow (prnt S0) j"
    using Wseq_follow_list[of "Suc k"] sp newprnt_eq by simp
  have split: "map s (rev [0..<Suc k]) = map s (rev [1..<Suc k]) @ [s 0]" by (simp add: upt_rec)
  have setimg: "set (map s (rev [1..<Suc k])) = s ` {1..<Suc k}" by (simp only: set_map set_rev set_upt)
  have allne: "\<And>a. a \<in> set (map s (rev [1..<Suc k])) \<Longrightarrow> a \<noteq> i"
  proof -
    fix a assume "a \<in> set (map s (rev [1..<Suc k]))"
    hence "a \<in> s ` {1..<Suc k}" using setimg by simp
    then obtain x where xr: "x \<in> {1..<Suc k}" and ax: "a = s x" by auto
    have "x \<noteq> 0" using xr by auto
    moreover have "x \<in> {..k}" "(0::nat) \<in> {..k}" using xr by auto
    ultimately have "s x \<noteq> s 0" using inj by (auto simp: inj_on_eq_iff)
    thus "a \<noteq> i" using ax path0 by simp
  qed
  have flsplit: "follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) p = map s (rev [1..<Suc k]) @ (i # follow (prnt S0) j)"
    using fl split path0 by simp
  have "takeWhile (\<lambda>x. x \<noteq> i) (map s (rev [1..<Suc k]) @ (i # follow (prnt S0) j)) = map s (rev [1..<Suc k])"
  proof -
    have "takeWhile (\<lambda>x. x \<noteq> i) (map s (rev [1..<Suc k]) @ (i # follow (prnt S0) j))
          = map s (rev [1..<Suc k]) @ takeWhile (\<lambda>x. x \<noteq> i) (i # follow (prnt S0) j)"
      by (rule takeWhile_append2) (use allne in auto)
    thus ?thesis by simp
  qed
  hence "takeWhile (\<lambda>x. x \<noteq> i) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) p) = map s (rev [1..<Suc k])"
    using flsplit by simp
  thus ?thesis using setimg by simp
qed

lemma imgStem_sub:
  assumes kpos: "0 < k"
  shows "(\<lambda>y. the (((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) y)) ` set (takeWhile (\<lambda>x. x \<noteq> i) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) p)) \<subseteq> s ` {..k}"
proof
  fix z assume "z \<in> (\<lambda>y. the (((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) y)) ` set (takeWhile (\<lambda>x. x \<noteq> i) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) p))"
  then obtain y where yin: "y \<in> set (takeWhile (\<lambda>x. x \<noteq> i) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) p))"
    and zy: "z = the (((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) y)" by auto
  have "y \<in> s ` {1..<Suc k}" using chainStem_set[OF kpos] yin by simp
  then obtain t where tt: "t \<in> {1..<Suc k}" and yt: "y = s t" by auto
  have "((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (s t) = Some (s_pred t)"
    using Wseq_eval[of "Suc k" t] tt newprnt_eq by simp
  hence "z = s_pred t" using zy yt by simp
  moreover have "s_pred t = s (t - 1)" using tt by (auto simp: s_pred_def)
  moreover have "t - 1 \<le> k" using tt by auto
  ultimately show "z \<in> s ` {..k}" by auto
qed

text \<open>In the genuine-reversal branch the stem is nontrivial, i.e. @{term "0 < k"}.\<close>
lemma inep_aux: assumes kpos: "0 < k" shows "i \<noteq> p"
  using path0 pathk inj kpos by (auto simp: inj_on_def)

text \<open>Closed form of the @{const prnt} field of @{const update_tree} in the reversal branch:
      the decoration loops and @{const dirty_pass} all leave @{const prnt} untouched (they climb the
      fixed parent map, a @{const parent_spec} by @{thm clauseA}), so the only edit is @{term Sp}'s
       "p {\isasymmapsto} s\_pred k".\<close>
lemma update_tree_prnt:
  assumes kpos: "0 < k"
  shows "prnt (update_tree S0 i j p jn) = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)"
proof -
  have inep: "i \<noteq> p" using inep_aux[OF kpos] by auto
  have psN: "parent_spec ((prnt S0 ++ REV k)(p \<mapsto> s_pred k))"
    using clauseA rooted_arborescense_invar_parent_spec by auto
  have prnt_Sfin: "prnt Sfin = prnt S0 ++ REV k" by (simp add: Sfin_def)
  define Sp where "Sp = Sfin\<lparr>prnt := (prnt Sfin)(p \<mapsto> s_pred k)\<rparr>"
  define Sq where "Sq = (case (if the (rvth S0 p) = j then thrd S0 (lsuc S0 p) else thrd S0 j) of
                           None \<Rightarrow> Sp\<lparr>thrd := (thrd Sp)(lsx k := None)\<rparr>
                         | Some a \<Rightarrow> Sp\<lparr>thrd := (thrd Sp)(lsx k \<mapsto> a), rvth := (rvth Sp)(a \<mapsto> lsx k)\<rparr>)"
  define Sr where "Sr = Sq\<lparr>lsuc := (lsuc Sq)(p := lsx k)\<rparr>"
  define Ss where "Ss = (if the (rvth S0 p) \<noteq> j
                         then (case aftn k of
                                 None \<Rightarrow> Sr\<lparr>thrd := (thrd Sr)(the (rvth S0 p) := None)\<rparr>
                               | Some a \<Rightarrow> Sr\<lparr>thrd := (thrd Sr)(the (rvth S0 p) \<mapsto> a), rvth := (rvth Sr)(a \<mapsto> the (rvth S0 p))\<rparr>)
                         else Sr)"
  define St where "St = dirty_pass Ss (drt k)"
  define Su where "Su = stem_num_loop St (snum S0) p i 0 (lsuc St p)"
  define Sv where "Sv = Su\<lparr>snum := (snum Su)(i := snum S0 p)\<rparr>"
  define S2 where "S2 = last_vin_loop Sv j j (lsuc Sv p)"
  define S3 where "S3 = (if jn \<noteq> the (rvth S0 p) \<and> j \<noteq> the (rvth S0 p)
                         then last_vout_loop S2 (the (prnt S0 p)) (if lsuc Sv jn = j then Some jn else None) (lsuc S0 p) (the (rvth S0 p))
                         else if lsuc Sv p \<noteq> lsuc S0 p
                              then last_vout_loop S2 (the (prnt S0 p)) (if lsuc Sv jn = j then Some jn else None) (lsuc S0 p) (lsuc Sv p)
                              else S2)"
  define S4 where "S4 = succ_vin_loop S3 j jn (snum S0 p)"
  define S5 where "S5 = succ_vout_loop S4 (the (prnt S0 p)) jn (snum S0 p)"
  have psSv: "parent_spec (prnt Sv)" using stem_num_loop_fields[OF psN, THEN mp] psN by (simp add: Sv_def Su_def St_def Ss_def Sr_def Sq_def Sp_def Sfin_def split: option.split)
  define Sa where "Sa = fused_vin_loop Sv j j jn (lsuc Sv p) (snum S0 p) True True"
  define Sb where "Sb = (if jn \<noteq> the (rvth S0 p) \<and> j \<noteq> the (rvth S0 p) then fused_vout_loop Sa (the (prnt S0 p)) (if lsuc Sv jn = j then Some jn else None) (lsuc S0 p) (the (rvth S0 p)) jn (snum S0 p) True True else if lsuc Sv p \<noteq> lsuc S0 p then fused_vout_loop Sa (the (prnt S0 p)) (if lsuc Sv jn = j then Some jn else None) (lsuc S0 p) (lsuc Sv p) jn (snum S0 p) True True else fused_vout_loop Sa (the (prnt S0 p)) (if lsuc Sv jn = j then Some jn else None) (lsuc S0 p) (lsuc S0 p) jn (snum S0 p) False True)"
  have UTb: "update_tree S0 i j p jn = Sb" by (simp only: update_tree_def Let_def inep if_False if_True stem_loop_init prod.case Sb_def Sa_def Sv_def Su_def St_def Ss_def Sr_def Sq_def Sp_def)
  have SbS5: "Sb = S5" using update_tree_tail_eq[OF psSv] by (simp only: Sb_def Sa_def S5_def S4_def S3_def S2_def)
  have UT: "update_tree S0 i j p jn = S5" using UTb SbS5 by simp
  have pSp: "prnt Sp = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)" by (simp add: Sp_def prnt_Sfin)
  have pSq: "prnt Sq = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)" using pSp by (simp add: Sq_def split: option.split)
  have pSr: "prnt Sr = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)" using pSq by (simp add: Sr_def)
  have pSs: "prnt Ss = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)" using pSr by (simp add: Ss_def split: option.split)
  have pSt: "prnt St = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)" using pSs by (simp add: St_def)
  have pSu: "prnt Su = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)"
    using stem_num_loop_fields[OF psN, THEN mp, OF pSt] by (simp add: Su_def)
  have pSv: "prnt Sv = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)" using pSu by (simp add: Sv_def)
  have pS2: "prnt S2 = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)"
    using last_vin_loop_fields[OF psN, THEN mp, OF pSv] by (simp add: S2_def)
  have lvout: "\<And>u stp gv sv. prnt (last_vout_loop S2 u stp gv sv) = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)"
    using last_vout_loop_fields[OF psN, THEN mp, OF pS2] by simp
  have pS3: "prnt S3 = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)"
    using lvout pS2 by (simp add: S3_def)
  have pS4: "prnt S4 = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)"
    using succ_vin_loop_fields[OF psN, THEN mp, OF pS3] by (simp add: S4_def)
  have pS5: "prnt S5 = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)"
    using succ_vout_loop_fields[OF psN, THEN mp, OF pS4] by (simp add: S5_def)
  show ?thesis using UT pS5 by simp
qed

text \<open>The explicit final thread map (reversal branch): start from @{term "thrd_inv k"} (the reversed
      stem produced by @{const stem_loop}), re-link @{term "lsx k"} to the continuation thread, and
      (when the old reverse-thread of @{term p} is not @{term j}) splice @{term "the (rvth S0 p)"}.\<close>
definition final_thrd where "final_thrd = (let tc = (if the (rvth S0 p) = j then thrd S0 (lsuc S0 p) else thrd S0 j); b1 = (case tc of None \<Rightarrow> (thrd_inv k)(lsx k := None) | Some a \<Rightarrow> (thrd_inv k)(lsx k \<mapsto> a)) in (if the (rvth S0 p) \<noteq> j then (case aftn k of None \<Rightarrow> b1(the (rvth S0 p) := None) | Some a \<Rightarrow> b1(the (rvth S0 p) \<mapsto> a)) else b1))"

text \<open>Closed form of the @{const thrd} field of @{const update_tree} in the reversal branch: the
      decoration loops and @{const dirty_pass} preserve @{const thrd}, so the result is exactly the
      two thread-splices @{term Sq}, @{term Ss} make on top of @{term "thrd_inv k"}, i.e.\ @{const final_thrd}.\<close>
lemma update_tree_thrd:
  assumes kpos: "0 < k"
  shows "thrd (update_tree S0 i j p jn) = final_thrd"
proof -
  have inep: "i \<noteq> p" using inep_aux[OF kpos] by auto
  have psN: "parent_spec ((prnt S0 ++ REV k)(p \<mapsto> s_pred k))"
    using clauseA rooted_arborescense_invar_parent_spec by auto
  define Sp where "Sp = Sfin\<lparr>prnt := (prnt Sfin)(p \<mapsto> s_pred k)\<rparr>"
  define Sq where "Sq = (case (if the (rvth S0 p) = j then thrd S0 (lsuc S0 p) else thrd S0 j) of
                           None \<Rightarrow> Sp\<lparr>thrd := (thrd Sp)(lsx k := None)\<rparr>
                         | Some a \<Rightarrow> Sp\<lparr>thrd := (thrd Sp)(lsx k \<mapsto> a), rvth := (rvth Sp)(a \<mapsto> lsx k)\<rparr>)"
  define Sr where "Sr = Sq\<lparr>lsuc := (lsuc Sq)(p := lsx k)\<rparr>"
  define Ss where "Ss = (if the (rvth S0 p) \<noteq> j
                         then (case aftn k of
                                 None \<Rightarrow> Sr\<lparr>thrd := (thrd Sr)(the (rvth S0 p) := None)\<rparr>
                               | Some a \<Rightarrow> Sr\<lparr>thrd := (thrd Sr)(the (rvth S0 p) \<mapsto> a), rvth := (rvth Sr)(a \<mapsto> the (rvth S0 p))\<rparr>)
                         else Sr)"
  define St where "St = dirty_pass Ss (drt k)"
  define Su where "Su = stem_num_loop St (snum S0) p i 0 (lsuc St p)"
  define Sv where "Sv = Su\<lparr>snum := (snum Su)(i := snum S0 p)\<rparr>"
  define S2 where "S2 = last_vin_loop Sv j j (lsuc Sv p)"
  define S3 where "S3 = (if jn \<noteq> the (rvth S0 p) \<and> j \<noteq> the (rvth S0 p)
                         then last_vout_loop S2 (the (prnt S0 p)) (if lsuc Sv jn = j then Some jn else None) (lsuc S0 p) (the (rvth S0 p))
                         else if lsuc Sv p \<noteq> lsuc S0 p
                              then last_vout_loop S2 (the (prnt S0 p)) (if lsuc Sv jn = j then Some jn else None) (lsuc S0 p) (lsuc Sv p)
                              else S2)"
  define S4 where "S4 = succ_vin_loop S3 j jn (snum S0 p)"
  define S5 where "S5 = succ_vout_loop S4 (the (prnt S0 p)) jn (snum S0 p)"
  have psSv: "parent_spec (prnt Sv)" using stem_num_loop_fields[OF psN, THEN mp] psN by (simp add: Sv_def Su_def St_def Ss_def Sr_def Sq_def Sp_def Sfin_def split: option.split)
  define Sa where "Sa = fused_vin_loop Sv j j jn (lsuc Sv p) (snum S0 p) True True"
  define Sb where "Sb = (if jn \<noteq> the (rvth S0 p) \<and> j \<noteq> the (rvth S0 p) then fused_vout_loop Sa (the (prnt S0 p)) (if lsuc Sv jn = j then Some jn else None) (lsuc S0 p) (the (rvth S0 p)) jn (snum S0 p) True True else if lsuc Sv p \<noteq> lsuc S0 p then fused_vout_loop Sa (the (prnt S0 p)) (if lsuc Sv jn = j then Some jn else None) (lsuc S0 p) (lsuc Sv p) jn (snum S0 p) True True else fused_vout_loop Sa (the (prnt S0 p)) (if lsuc Sv jn = j then Some jn else None) (lsuc S0 p) (lsuc S0 p) jn (snum S0 p) False True)"
  have UTb: "update_tree S0 i j p jn = Sb" by (simp only: update_tree_def Let_def inep if_False if_True stem_loop_init prod.case Sb_def Sa_def Sv_def Su_def St_def Ss_def Sr_def Sq_def Sp_def)
  have SbS5: "Sb = S5" using update_tree_tail_eq[OF psSv] by (simp only: Sb_def Sa_def S5_def S4_def S3_def S2_def)
  have UT: "update_tree S0 i j p jn = S5" using UTb SbS5 by simp
  have pSp: "prnt Sp = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)" by (simp add: Sp_def Sfin_def)
  have pSq: "prnt Sq = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)" using pSp by (simp add: Sq_def split: option.split)
  have pSr: "prnt Sr = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)" using pSq by (simp add: Sr_def)
  have pSs: "prnt Ss = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)" using pSr by (simp add: Ss_def split: option.split)
  have pSt: "prnt St = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)" using pSs by (simp add: St_def)
  have pSu: "prnt Su = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)"
    using stem_num_loop_fields[OF psN, THEN mp, OF pSt] by (simp add: Su_def)
  have pSv: "prnt Sv = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)" using pSu by (simp add: Sv_def)
  have pS2: "prnt S2 = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)"
    using last_vin_loop_fields[OF psN, THEN mp, OF pSv] by (simp add: S2_def)
  have pS3: "prnt S3 = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)"
    using last_vout_loop_fields[OF psN, THEN mp, OF pS2] pS2 by (simp add: S3_def)
  have pS4: "prnt S4 = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)"
    using succ_vin_loop_fields[OF psN, THEN mp, OF pS3] by (simp add: S4_def)
  have tSs: "thrd Ss = final_thrd"
    by (simp add: Ss_def Sr_def Sq_def Sp_def Sfin_def final_thrd_def Let_def split: option.split)
  have tSt: "thrd St = final_thrd" using tSs by (simp add: St_def)
  have tSu: "thrd Su = final_thrd"
    using stem_num_loop_fields[OF psN, THEN mp, OF pSt] tSt by (simp add: Su_def)
  have tSv: "thrd Sv = final_thrd" using tSu by (simp add: Sv_def)
  have tS2: "thrd S2 = final_thrd"
    using last_vin_loop_fields[OF psN, THEN mp, OF pSv] tSv by (simp add: S2_def)
  have tvout: "\<And>u stp gv sv. thrd (last_vout_loop S2 u stp gv sv) = final_thrd"
    using last_vout_loop_fields[OF psN, THEN mp, OF pS2] tS2 by simp
  have tS3: "thrd S3 = final_thrd"
    using tvout tS2 by (simp add: S3_def)
  have tS4: "thrd S4 = final_thrd"
    using succ_vin_loop_fields[OF psN, THEN mp, OF pS3] tS3 by (simp add: S4_def)
  have tS5: "thrd S5 = final_thrd"
    using succ_vout_loop_fields[OF psN, THEN mp, OF pS4] tS4 by (simp add: S5_def)
  show ?thesis using UT tS5 by simp
qed

text \<open>Closed form of the @{const rvth} field: the decoration loops preserve @{const rvth}, so it is
      @{const dirty_pass}'s left fold (rebuilding the reverse-thread from @{const final_thrd}) on top of
      the two @{term Sq}, @{term Ss} reverse-splices over @{term "rvth Sfin"}.\<close>
definition final_rvth where "final_rvth = (let tc = (if the (rvth S0 p) = j then thrd S0 (lsuc S0 p) else thrd S0 j); r1 = (case tc of None \<Rightarrow> rvth Sfin | Some a \<Rightarrow> (rvth Sfin)(a \<mapsto> lsx k)); r2 = (if the (rvth S0 p) \<noteq> j then (case aftn k of None \<Rightarrow> r1 | Some a \<Rightarrow> r1(a \<mapsto> the (rvth S0 p))) else r1) in foldl (\<lambda>R u. case final_thrd u of None \<Rightarrow> R | Some w \<Rightarrow> R(w \<mapsto> u)) r2 (drt k))"

lemma update_tree_rvth:
  assumes kpos: "0 < k"
  shows "rvth (update_tree S0 i j p jn) = final_rvth"
proof -
  have inep: "i \<noteq> p" using inep_aux[OF kpos] by auto
  have psN: "parent_spec ((prnt S0 ++ REV k)(p \<mapsto> s_pred k))"
    using clauseA rooted_arborescense_invar_parent_spec by auto
  define Sp where "Sp = Sfin\<lparr>prnt := (prnt Sfin)(p \<mapsto> s_pred k)\<rparr>"
  define Sq where "Sq = (case (if the (rvth S0 p) = j then thrd S0 (lsuc S0 p) else thrd S0 j) of
                           None \<Rightarrow> Sp\<lparr>thrd := (thrd Sp)(lsx k := None)\<rparr>
                         | Some a \<Rightarrow> Sp\<lparr>thrd := (thrd Sp)(lsx k \<mapsto> a), rvth := (rvth Sp)(a \<mapsto> lsx k)\<rparr>)"
  define Sr where "Sr = Sq\<lparr>lsuc := (lsuc Sq)(p := lsx k)\<rparr>"
  define Ss where "Ss = (if the (rvth S0 p) \<noteq> j
                         then (case aftn k of
                                 None \<Rightarrow> Sr\<lparr>thrd := (thrd Sr)(the (rvth S0 p) := None)\<rparr>
                               | Some a \<Rightarrow> Sr\<lparr>thrd := (thrd Sr)(the (rvth S0 p) \<mapsto> a), rvth := (rvth Sr)(a \<mapsto> the (rvth S0 p))\<rparr>)
                         else Sr)"
  define St where "St = dirty_pass Ss (drt k)"
  define Su where "Su = stem_num_loop St (snum S0) p i 0 (lsuc St p)"
  define Sv where "Sv = Su\<lparr>snum := (snum Su)(i := snum S0 p)\<rparr>"
  define S2 where "S2 = last_vin_loop Sv j j (lsuc Sv p)"
  define S3 where "S3 = (if jn \<noteq> the (rvth S0 p) \<and> j \<noteq> the (rvth S0 p)
                         then last_vout_loop S2 (the (prnt S0 p)) (if lsuc Sv jn = j then Some jn else None) (lsuc S0 p) (the (rvth S0 p))
                         else if lsuc Sv p \<noteq> lsuc S0 p
                              then last_vout_loop S2 (the (prnt S0 p)) (if lsuc Sv jn = j then Some jn else None) (lsuc S0 p) (lsuc Sv p)
                              else S2)"
  define S4 where "S4 = succ_vin_loop S3 j jn (snum S0 p)"
  define S5 where "S5 = succ_vout_loop S4 (the (prnt S0 p)) jn (snum S0 p)"
  have psSv: "parent_spec (prnt Sv)" using stem_num_loop_fields[OF psN, THEN mp] psN by (simp add: Sv_def Su_def St_def Ss_def Sr_def Sq_def Sp_def Sfin_def split: option.split)
  define Sa where "Sa = fused_vin_loop Sv j j jn (lsuc Sv p) (snum S0 p) True True"
  define Sb where "Sb = (if jn \<noteq> the (rvth S0 p) \<and> j \<noteq> the (rvth S0 p) then fused_vout_loop Sa (the (prnt S0 p)) (if lsuc Sv jn = j then Some jn else None) (lsuc S0 p) (the (rvth S0 p)) jn (snum S0 p) True True else if lsuc Sv p \<noteq> lsuc S0 p then fused_vout_loop Sa (the (prnt S0 p)) (if lsuc Sv jn = j then Some jn else None) (lsuc S0 p) (lsuc Sv p) jn (snum S0 p) True True else fused_vout_loop Sa (the (prnt S0 p)) (if lsuc Sv jn = j then Some jn else None) (lsuc S0 p) (lsuc S0 p) jn (snum S0 p) False True)"
  have UTb: "update_tree S0 i j p jn = Sb" by (simp only: update_tree_def Let_def inep if_False if_True stem_loop_init prod.case Sb_def Sa_def Sv_def Su_def St_def Ss_def Sr_def Sq_def Sp_def)
  have SbS5: "Sb = S5" using update_tree_tail_eq[OF psSv] by (simp only: Sb_def Sa_def S5_def S4_def S3_def S2_def)
  have UT: "update_tree S0 i j p jn = S5" using UTb SbS5 by simp
  have pSp: "prnt Sp = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)" by (simp add: Sp_def Sfin_def)
  have pSq: "prnt Sq = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)" using pSp by (simp add: Sq_def split: option.split)
  have pSr: "prnt Sr = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)" using pSq by (simp add: Sr_def)
  have pSs: "prnt Ss = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)" using pSr by (simp add: Ss_def split: option.split)
  have pSt: "prnt St = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)" using pSs by (simp add: St_def)
  have pSu: "prnt Su = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)"
    using stem_num_loop_fields[OF psN, THEN mp, OF pSt] by (simp add: Su_def)
  have pSv: "prnt Sv = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)" using pSu by (simp add: Sv_def)
  have pS2: "prnt S2 = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)"
    using last_vin_loop_fields[OF psN, THEN mp, OF pSv] by (simp add: S2_def)
  have pS3: "prnt S3 = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)"
    using last_vout_loop_fields[OF psN, THEN mp, OF pS2] pS2 by (simp add: S3_def)
  have pS4: "prnt S4 = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)"
    using succ_vin_loop_fields[OF psN, THEN mp, OF pS3] by (simp add: S4_def)
  have tSs: "thrd Ss = final_thrd"
    by (simp add: Ss_def Sr_def Sq_def Sp_def Sfin_def final_thrd_def Let_def split: option.split)
  have rSs2: "rvth Ss = (let tc = (if the (rvth S0 p) = j then thrd S0 (lsuc S0 p) else thrd S0 j); r1 = (case tc of None \<Rightarrow> rvth Sfin | Some a \<Rightarrow> (rvth Sfin)(a \<mapsto> lsx k)) in (if the (rvth S0 p) \<noteq> j then (case aftn k of None \<Rightarrow> r1 | Some a \<Rightarrow> r1(a \<mapsto> the (rvth S0 p))) else r1))"
    by (simp add: Ss_def Sr_def Sq_def Sp_def Let_def split: option.split)
  have rSt: "rvth St = foldl (\<lambda>R u. case final_thrd u of None \<Rightarrow> R | Some w \<Rightarrow> R(w \<mapsto> u)) (rvth Ss) (drt k)"
    using dirty_pass_rvth_fold[of Ss "drt k"] tSs by (simp add: St_def)
  have rSu: "rvth Su = rvth St"
    using stem_num_loop_fields[OF psN, THEN mp, OF pSt] by (simp add: Su_def)
  have rSv: "rvth Sv = rvth St" using rSu by (simp add: Sv_def)
  have rS2: "rvth S2 = rvth St"
    using last_vin_loop_fields[OF psN, THEN mp, OF pSv] rSv by (simp add: S2_def)
  have rvout: "\<And>u stp gv sv. rvth (last_vout_loop S2 u stp gv sv) = rvth St"
    using last_vout_loop_fields[OF psN, THEN mp, OF pS2] rS2 by simp
  have rS3: "rvth S3 = rvth St" using rvout rS2 by (simp add: S3_def)
  have rS4: "rvth S4 = rvth St"
    using succ_vin_loop_fields[OF psN, THEN mp, OF pS3] rS3 by (simp add: S4_def)
  have rS5: "rvth S5 = rvth St"
    using succ_vout_loop_fields[OF psN, THEN mp, OF pS4] rS4 by (simp add: S5_def)
  have FR: "final_rvth = foldl (\<lambda>R u. case final_thrd u of None \<Rightarrow> R | Some w \<Rightarrow> R(w \<mapsto> u)) (rvth Ss) (drt k)"
    by (simp add: final_rvth_def Let_def rSs2)
  show ?thesis using UT rS5 rSt FR by simp
qed

text \<open>Closed form of the @{const snum} field of @{const update_tree} in the reversal branch, obtained
      by pushing @{term "snum S0"} through the five decoration loops with their value lemmas: the stem
      @{const stem_num_loop} telescopes subtree sizes, @{term Sv} pins @{term i}, and the two
      @{const succ_vin_loop}/@{const succ_vout_loop} climbs add/subtract the moved subtree size
      @{term "snum S0 p"} on the in-/out-chains up to the join.  Depends on @{term jn}.\<close>
definition final_snum where "final_snum jn = (let P = (prnt S0 ++ REV k)(p \<mapsto> s_pred k); vout = the (prnt S0 p); on = snum S0 p; su = (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. y \<noteq> i) (follow P p)) then on - snum S0 (the (P x)) else snum S0 x); sv = (\<lambda>x. if x = i then on else su x); s4 = (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow P j)) then sv x + on else sv x) in (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow P vout)) then s4 x - on else s4 x))"

lemma update_tree_snum:
  assumes kpos: "0 < k"
  shows "snum (update_tree S0 i j p jn) = final_snum jn"
proof -
  have inep: "i \<noteq> p" using inep_aux[OF kpos] by auto
  have psN: "parent_spec ((prnt S0 ++ REV k)(p \<mapsto> s_pred k))"
    using clauseA rooted_arborescense_invar_parent_spec by auto
  define Sp where "Sp = Sfin\<lparr>prnt := (prnt Sfin)(p \<mapsto> s_pred k)\<rparr>"
  define Sq where "Sq = (case (if the (rvth S0 p) = j then thrd S0 (lsuc S0 p) else thrd S0 j) of
                           None \<Rightarrow> Sp\<lparr>thrd := (thrd Sp)(lsx k := None)\<rparr>
                         | Some a \<Rightarrow> Sp\<lparr>thrd := (thrd Sp)(lsx k \<mapsto> a), rvth := (rvth Sp)(a \<mapsto> lsx k)\<rparr>)"
  define Sr where "Sr = Sq\<lparr>lsuc := (lsuc Sq)(p := lsx k)\<rparr>"
  define Ss where "Ss = (if the (rvth S0 p) \<noteq> j
                         then (case aftn k of
                                 None \<Rightarrow> Sr\<lparr>thrd := (thrd Sr)(the (rvth S0 p) := None)\<rparr>
                               | Some a \<Rightarrow> Sr\<lparr>thrd := (thrd Sr)(the (rvth S0 p) \<mapsto> a), rvth := (rvth Sr)(a \<mapsto> the (rvth S0 p))\<rparr>)
                         else Sr)"
  define St where "St = dirty_pass Ss (drt k)"
  define Su where "Su = stem_num_loop St (snum S0) p i 0 (lsuc St p)"
  define Sv where "Sv = Su\<lparr>snum := (snum Su)(i := snum S0 p)\<rparr>"
  define S2 where "S2 = last_vin_loop Sv j j (lsuc Sv p)"
  define S3 where "S3 = (if jn \<noteq> the (rvth S0 p) \<and> j \<noteq> the (rvth S0 p)
                         then last_vout_loop S2 (the (prnt S0 p)) (if lsuc Sv jn = j then Some jn else None) (lsuc S0 p) (the (rvth S0 p))
                         else if lsuc Sv p \<noteq> lsuc S0 p
                              then last_vout_loop S2 (the (prnt S0 p)) (if lsuc Sv jn = j then Some jn else None) (lsuc S0 p) (lsuc Sv p)
                              else S2)"
  define S4 where "S4 = succ_vin_loop S3 j jn (snum S0 p)"
  define S5 where "S5 = succ_vout_loop S4 (the (prnt S0 p)) jn (snum S0 p)"
  have psSv: "parent_spec (prnt Sv)" using stem_num_loop_fields[OF psN, THEN mp] psN by (simp add: Sv_def Su_def St_def Ss_def Sr_def Sq_def Sp_def Sfin_def split: option.split)
  define Sa where "Sa = fused_vin_loop Sv j j jn (lsuc Sv p) (snum S0 p) True True"
  define Sb where "Sb = (if jn \<noteq> the (rvth S0 p) \<and> j \<noteq> the (rvth S0 p) then fused_vout_loop Sa (the (prnt S0 p)) (if lsuc Sv jn = j then Some jn else None) (lsuc S0 p) (the (rvth S0 p)) jn (snum S0 p) True True else if lsuc Sv p \<noteq> lsuc S0 p then fused_vout_loop Sa (the (prnt S0 p)) (if lsuc Sv jn = j then Some jn else None) (lsuc S0 p) (lsuc Sv p) jn (snum S0 p) True True else fused_vout_loop Sa (the (prnt S0 p)) (if lsuc Sv jn = j then Some jn else None) (lsuc S0 p) (lsuc S0 p) jn (snum S0 p) False True)"
  have UTb: "update_tree S0 i j p jn = Sb" by (simp only: update_tree_def Let_def inep if_False if_True stem_loop_init prod.case Sb_def Sa_def Sv_def Su_def St_def Ss_def Sr_def Sq_def Sp_def)
  have SbS5: "Sb = S5" using update_tree_tail_eq[OF psSv] by (simp only: Sb_def Sa_def S5_def S4_def S3_def S2_def)
  have UT: "update_tree S0 i j p jn = S5" using UTb SbS5 by simp
  have pSp: "prnt Sp = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)" by (simp add: Sp_def Sfin_def)
  have pSq: "prnt Sq = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)" using pSp by (simp add: Sq_def split: option.split)
  have pSr: "prnt Sr = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)" using pSq by (simp add: Sr_def)
  have pSs: "prnt Ss = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)" using pSr by (simp add: Ss_def split: option.split)
  have pSt: "prnt St = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)" using pSs by (simp add: St_def)
  have pSu: "prnt Su = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)"
    using stem_num_loop_fields[OF psN, THEN mp, OF pSt] by (simp add: Su_def)
  have pSv: "prnt Sv = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)" using pSu by (simp add: Sv_def)
  have pS2: "prnt S2 = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)"
    using last_vin_loop_fields[OF psN, THEN mp, OF pSv] by (simp add: S2_def)
  have pS3: "prnt S3 = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)"
    using last_vout_loop_fields[OF psN, THEN mp, OF pS2] pS2 by (simp add: S3_def)
  have pS4: "prnt S4 = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)"
    using succ_vin_loop_fields[OF psN, THEN mp, OF pS3] by (simp add: S4_def)
  have snSp: "snum Sp = snum S0" by (simp add: Sp_def Sfin_def)
  have snSq: "snum Sq = snum S0" using snSp by (simp add: Sq_def split: option.split)
  have snSr: "snum Sr = snum S0" using snSq by (simp add: Sr_def)
  have snSs: "snum Ss = snum S0" using snSr by (simp add: Ss_def split: option.split)
  have snSt: "snum St = snum S0" using snSs by (simp add: St_def)
  have snSu: "snum Su = (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. y \<noteq> i) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) p))
                              then snum S0 p - snum S0 (the (((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) x)) else snum S0 x)"
  proof -
    have step: "snum (stem_num_loop St (snum S0) p i 0 (lsuc St p)) =
          (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. y \<noteq> i) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) p))
               then 0 + snum S0 p - snum S0 (the (((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) x)) else snum St x)"
      using stem_num_loop_snum[OF psN, THEN mp, OF pSt, THEN mp, OF i_in_follow_newprnt, THEN mp, OF stem_chain_snum_mono] by auto
    have "snum Su = (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. y \<noteq> i) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) p))
               then 0 + snum S0 p - snum S0 (the (((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) x)) else snum St x)"
      using step by (simp add: Su_def)
    thus ?thesis by (simp add: snSt fun_eq_iff)
  qed
  have snSv: "snum Sv = (snum Su)(i := snum S0 p)" by (simp add: Sv_def)
  have snS2: "snum S2 = snum Sv"
    using last_vin_loop_fields[OF psN, THEN mp, OF pSv] by (simp add: S2_def)
  have snvout: "\<And>u stp gv sv. snum (last_vout_loop S2 u stp gv sv) = snum S2"
    using last_vout_loop_fields[OF psN, THEN mp, OF pS2] by simp
  have snS3: "snum S3 = snum Sv" using snvout snS2 by (simp add: S3_def)
  have snS4: "snum S4 = (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) j))
                             then snum S3 x + snum S0 p else snum S3 x)"
    using succ_vin_loop_snum[OF psN, THEN mp, OF pS3] by (simp add: S4_def)
  have snS5: "snum S5 = (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (the (prnt S0 p))))
                             then snum S4 x - snum S0 p else snum S4 x)"
    using succ_vout_loop_snum[OF psN, THEN mp, OF pS4] by (simp add: S5_def)
  show ?thesis
    unfolding UT final_snum_def Let_def
    using snS5 snS4 snS3 snSv snSu by (simp add: fun_eq_iff)
qed

text \<open>The pivot re-parents @{term i} to @{term j} (the second conclusion of the correctness theorem),
      in the reversal branch: the reversed stem map carries the base link from s 0 (= i) to s\_pred 0 (= j).\<close>
lemma update_tree_prnt_i:
  assumes kpos: "0 < k"
  shows "prnt (update_tree S0 i j p jn) i = Some j"
proof -
  have inep: "i \<noteq> p" using inep_aux[OF kpos] by auto
  have "prnt (update_tree S0 i j p jn) = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)"
    using update_tree_prnt[OF kpos] by auto
  hence "prnt (update_tree S0 i j p jn) i = ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) i" by simp
  also have "\<dots> = (prnt S0 ++ REV k) i" using inep by simp
  also have "\<dots> = Wseq (Suc k) i" using newprnt_eq inep by simp
  also have "\<dots> = Wseq (Suc k) (s 0)" using path0 by simp
  also have "\<dots> = Some (s_pred 0)" using Wseq_eval[of "Suc k" 0] by simp
  also have "\<dots> = Some j" by (simp add: s_pred_def)
  finally show ?thesis .
qed

text \<open>Clause-I foundations (the descendant-set transformation, {\isasymsection}17.7).  A node outside the moved
      block @{term "block S0 p"} keeps its old root-path (its old ancestors contain no stem node); the
      root @{term i} of the reversed block attaches to @{term j} (its new root-path is @{term i} then
      @{term j}'s old path); hence @{term i}'s new subtree is contained in the moved block.\<close>
lemma follow_newprnt_off_block:
  assumes kpos: "0 < k" and unb: "u \<notin> set (block S0 p)"
  shows "follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u = follow (prnt S0) u"
proof (rule follow_newprnt_free)
  show "\<forall>m\<le>k. s m \<notin> set (follow (prnt S0) u)"
  proof (intro allI impI)
    fix m assume mk: "m \<le> k"
    show "s m \<notin> set (follow (prnt S0) u)"
    proof
      assume "s m \<in> set (follow (prnt S0) u)"
      hence uch: "u \<in> children (prnt S0) (s m)" unfolding children_def by simp
      have "p \<in> set (follow (prnt S0) (s m))" using stem_chain[of k m] mk pathk by simp
      hence "s m \<in> children (prnt S0) p" unfolding children_def by simp
      hence "children (prnt S0) (s m) \<subseteq> children (prnt S0) p" by (rule children_subset[OF ppt])
      hence "u \<in> children (prnt S0) p" using uch by auto
      hence "u \<in> set (block S0 p)" using block_props(4)[OF arb pV] by simp
      thus False using unb by simp
    qed
  qed
qed

lemma follow_newprnt_i:
  assumes kpos: "0 < k"
  shows "follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) i = i # follow (prnt S0) j"
proof -
  have psN: "parent_spec ((prnt S0 ++ REV k)(p \<mapsto> s_pred k))"
    using clauseA rooted_arborescense_invar_parent_spec by auto
  have inep: "i \<noteq> p" using inep_aux[OF kpos] by auto
  have npi: "((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) i = Some j" using inep newprnt_eq inep path0 Wseq_eval[of "Suc k" 0] by (simp add: s_pred_def)
  have "follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) i = i # follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) j"
    using npi by (subst follow_ps_simps[OF psN]) simp
  thus ?thesis using follow_newprnt_j by simp
qed

lemma children_newprnt_i_sub:
  assumes kpos: "0 < k"
  shows "children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) i \<subseteq> set (block S0 p)"
proof
  fix u assume "u \<in> children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) i"
  hence iu: "i \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u)" unfolding children_def by simp
  show "u \<in> set (block S0 p)"
  proof (rule ccontr)
    assume unb: "u \<notin> set (block S0 p)"
    have "i \<in> set (follow (prnt S0) u)" using iu follow_newprnt_off_block[OF kpos unb] by simp
    hence "u \<in> children (prnt S0) i" unfolding children_def by simp
    hence uic: "u \<in> set (block S0 i)" using block_props(4)[OF arb iV] by simp
    have "p \<in> set (follow (prnt S0) i)" using stem_chain[of k 0] kpos pathk path0 by simp
    hence "i \<in> children (prnt S0) p" unfolding children_def by simp
    hence "children (prnt S0) i \<subseteq> children (prnt S0) p" by (rule children_subset[OF ppt])
    hence "set (block S0 i) \<subseteq> set (block S0 p)" using block_props(4)[OF arb iV] block_props(4)[OF arb pV] by simp
    thus False using uic unb by auto
  qed
qed

text \<open>The moved block re-roots at @{term i}: one non-root step of a block node stays in the block
      (@{term block_p_newprnt_step}); a @{const parent_spec}-induction then carries every block node up
      to @{term i}, giving @{term "children newprnt i = set (block S0 p)"} --- @{term i}'s new subtree
      is exactly the moved block (clause I at @{term i}, and the reattachment engine for IN-chain).\<close>
lemma block_p_newprnt_step:
  assumes kpos: "0 < k" and ub: "u \<in> set (block S0 p)" and uni: "u \<noteq> i"
  shows "\<exists>w. ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u = Some w \<and> w \<in> set (block S0 p)"
proof -
  have uch: "u \<in> children (prnt S0) p" using ub block_props(4)[OF arb pV] by simp
  hence pfu: "p \<in> set (follow (prnt S0) u)" unfolding children_def by simp
  have rinv: "rooted_arborescense_invar r V (prnt S0)" using arb unfolding arb_invar_def by simp
  have domS0: "dom (prnt S0) = V - {r}" by (rule rooted_arborescense_invar_dom[OF rinv])
  have uV: "u \<in> V"
  proof (rule ccontr)
    assume "u \<notin> V"
    hence "prnt S0 u = None" using domS0 by auto
    hence "follow (prnt S0) u = [u]" by (subst follow_ps_simps[OF ppt]) simp
    hence "p = u" using pfu by simp
    thus False using \<open>u \<notin> V\<close> pV by simp
  qed
  have une_r: "u \<noteq> r"
  proof
    assume "u = r"
    hence "prnt S0 u = None" using domS0 by auto
    hence "follow (prnt S0) u = [u]" by (subst follow_ps_simps[OF ppt]) simp
    hence "p = u" using pfu by simp
    thus False using \<open>u = r\<close> pne_r by simp
  qed
  have rinvN: "rooted_arborescense_invar r V ((prnt S0 ++ REV k)(p \<mapsto> s_pred k))" by (rule clauseA)
  have "u \<in> dom ((prnt S0 ++ REV k)(p \<mapsto> s_pred k))"
    using rooted_arborescense_invar_dom[OF rinvN] uV une_r by simp
  then obtain w where w: "((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u = Some w" by (blast dest: domD)
  have "w \<in> set (block S0 p)"
  proof (cases "u \<in> s ` {..k}")
    case True
    then obtain m where mk: "m \<le> k" and um: "u = s m" by auto
    have "m \<noteq> 0"
    proof
      assume "m = 0"
      hence "u = i" using um path0 by simp
      thus False using uni by simp
    qed
    hence m1: "1 \<le> m" by simp
    have "((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (s m) = Some (s_pred m)"
      using Wseq_eval[of "Suc k" m] mk newprnt_eq by simp
    hence "w = s_pred m" using w um by simp
    hence weq: "w = s (m - 1)" using m1 by (simp add: s_pred_def)
    have "p \<in> set (follow (prnt S0) (s (m - 1)))" using stem_chain[of k "m - 1"] mk pathk by simp
    hence "s (m - 1) \<in> children (prnt S0) p" unfolding children_def by simp
    thus ?thesis using weq block_props(4)[OF arb pV] by simp
  next
    case False
    hence "\<forall>t < Suc k. u \<noteq> s t" by auto
    hence "Wseq (Suc k) u = prnt S0 u" using Wseq_fresh[of "Suc k" u] by auto
    hence "((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u = prnt S0 u" using newprnt_eq by simp
    hence pu: "prnt S0 u = Some w" using w by simp
    have "p \<noteq> u" using False pathk by auto
    have "follow (prnt S0) u = u # follow (prnt S0) w" using pu by (subst follow_ps_simps[OF ppt]) simp
    hence "p \<in> set (follow (prnt S0) w)" using pfu \<open>p \<noteq> u\<close> by simp
    hence "w \<in> children (prnt S0) p" unfolding children_def by simp
    thus ?thesis using block_props(4)[OF arb pV] by simp
  qed
  thus ?thesis using w by auto
qed

lemma block_p_under_i:
  assumes kpos: "0 < k"
  shows "u \<in> set (block S0 p) \<longrightarrow> i \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u)"
proof -
  have psN: "parent_spec ((prnt S0 ++ REV k)(p \<mapsto> s_pred k))"
    using clauseA rooted_arborescense_invar_parent_spec by auto
  show ?thesis
  proof (induction rule: parent_spec_i.follow.pinduct[OF follow_dom_ps[OF psN, of u]])
    case (1 u)
    show ?case
    proof
      assume ub: "u \<in> set (block S0 p)"
      show "i \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u)"
      proof (cases "u = i")
        case True
        thus ?thesis
          using follow_hd_ps[OF psN, of i] follow_ne_ps[OF psN, of i] by (metis hd_in_set)
      next
        case False
        obtain w where w: "((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u = Some w" and wb: "w \<in> set (block S0 p)"
          using block_p_newprnt_step[OF kpos ub False] by auto
        have "follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u = u # follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) w"
          using w by (subst follow_ps_simps[OF psN]) simp
        moreover have "i \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) w)"
          using 1(2)[OF w] wb by (rule mp)
        ultimately show ?thesis by simp
      qed
    qed
  qed
qed

lemma children_newprnt_i:
  assumes kpos: "0 < k"
  shows "children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) i = set (block S0 p)"
proof
  show "children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) i \<subseteq> set (block S0 p)"
    by (rule children_newprnt_i_sub[OF kpos])
next
  show "set (block S0 p) \<subseteq> children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) i"
  proof
    fix u assume "u \<in> set (block S0 p)"
    hence "i \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u)"
      by (rule mp[OF block_p_under_i[OF kpos]])
    thus "u \<in> children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) i" unfolding children_def by simp
  qed
qed

lemma card_children_newprnt_i:
  assumes kpos: "0 < k"
  shows "card (children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) i) = snum S0 p"
proof -
  show ?thesis using children_newprnt_i[OF kpos] block_props(4)[OF arb pV] arb pV unfolding arb_invar_def by simp
qed

text \<open>The descendant-set transformation, general form: split @{const children} by whether a node is in
      the moved block (off-block nodes keep their old path).  On @{term j}'s root-path every block node
      becomes a descendant (they all sit under @{term i} under @{term j}), so the new subtree of such a
      node is its old subtree together with the moved block --- the engine for the IN-chain (+ on) and
      the ancestor-of-@{term jn} (unchanged) regions.\<close>
lemma children_newprnt_decomp:
  assumes kpos: "0 < k"
  shows "children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v =
         (children (prnt S0) v - set (block S0 p)) \<union> {u \<in> set (block S0 p). v \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u)}"
proof
  show "children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v \<subseteq> (children (prnt S0) v - set (block S0 p)) \<union> {u \<in> set (block S0 p). v \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u)}"
  proof
    fix u assume "u \<in> children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v"
    hence vu: "v \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u)" unfolding children_def by simp
    show "u \<in> (children (prnt S0) v - set (block S0 p)) \<union> {u \<in> set (block S0 p). v \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u)}"
    proof (cases "u \<in> set (block S0 p)")
      case True thus ?thesis using vu by auto
    next
      case False
      have "v \<in> set (follow (prnt S0) u)" using vu follow_newprnt_off_block[OF kpos False] by simp
      hence "u \<in> children (prnt S0) v" unfolding children_def by simp
      thus ?thesis using False by auto
    qed
  qed
next
  show "(children (prnt S0) v - set (block S0 p)) \<union> {u \<in> set (block S0 p). v \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u)} \<subseteq> children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v"
  proof
    fix u assume "u \<in> (children (prnt S0) v - set (block S0 p)) \<union> {u \<in> set (block S0 p). v \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u)}"
    thus "u \<in> children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v"
    proof
      assume "u \<in> children (prnt S0) v - set (block S0 p)"
      hence unb: "u \<notin> set (block S0 p)" and "v \<in> set (follow (prnt S0) u)" unfolding children_def by auto
      hence "v \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u)" using follow_newprnt_off_block[OF kpos unb] by simp
      thus ?thesis unfolding children_def by simp
    next
      assume "u \<in> {u \<in> set (block S0 p). v \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u)}"
      thus ?thesis unfolding children_def by simp
    qed
  qed
qed

lemma block_p_desc_of_j:
  assumes kpos: "0 < k" and vj: "v \<in> set (follow (prnt S0) j)" and ub: "u \<in> set (block S0 p)"
  shows "v \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u)"
proof -
  have psN: "parent_spec ((prnt S0 ++ REV k)(p \<mapsto> s_pred k))"
    using clauseA rooted_arborescense_invar_parent_spec by auto
  have iu: "i \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u)"
    using ub by (rule mp[OF block_p_under_i[OF kpos]])
  from iu obtain A B where AB: "follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u = A @ i # B" by (meson split_list)
  have "follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) i = i # B" using follow_append_ps[OF psN AB] by auto
  hence "follow (prnt S0) j = B" using follow_newprnt_i[OF kpos] by simp
  hence "v \<in> set B" using vj by simp
  thus ?thesis using AB by simp
qed

lemma children_newprnt_jpath:
  assumes kpos: "0 < k" and vj: "v \<in> set (follow (prnt S0) j)"
  shows "children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v = children (prnt S0) v \<union> set (block S0 p)"
proof -
  have "{u \<in> set (block S0 p). v \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u)} = set (block S0 p)"
    using block_p_desc_of_j[OF kpos vj] by auto
  hence "children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v = (children (prnt S0) v - set (block S0 p)) \<union> set (block S0 p)"
    using children_newprnt_decomp[OF kpos] by simp
  thus ?thesis by auto
qed

text \<open>A node strictly before @{term jn} on @{term j}'s root-path is a proper descendant of @{term jn}.
      For the IN-chain (, with @{term jn} the
      join of @{term i} and @{term j}), the moved block is disjoint from @{term v}'s old subtree:
      otherwise a common descendant would make @{term v} either an ancestor of @{term p} (so a common
      ancestor of @{term i}, @{term j}, hence @{term "v = jn"} --- contradiction) or a descendant of
      @{term p} (so  --- against @{thm jnotp}).\<close>
lemma below_jn:
  assumes vin: "v \<in> set (takeWhile (\<lambda>x. x \<noteq> jn) (follow (prnt S0) j))"
      and jnj: "jn \<in> set (follow (prnt S0) j)"
  shows "jn \<in> set (follow (prnt S0) v) \<and> v \<noteq> jn"
proof
  define L where "L = follow (prnt S0) j"
  define TW where "TW = takeWhile (\<lambda>x. x \<noteq> jn) L"
  define DW where "DW = dropWhile (\<lambda>x. x \<noteq> jn) L"
  have vinTW: "v \<in> set TW" using vin by (simp add: TW_def L_def)
  show "v \<noteq> jn" using takeWhile_holds[OF vinTW[unfolded TW_def]] by simp
  have TWd: "L = TW @ DW" by (simp add: TW_def DW_def)
  have dne: "DW \<noteq> []" using jnj by (simp add: DW_def L_def dropWhile_eq_Nil_conv)
  have "\<not> (hd DW \<noteq> jn)" using hd_dropWhile[OF dne[unfolded DW_def]] by (simp add: DW_def)
  hence hj: "hd DW = jn" by simp
  have dwform: "DW = jn # tl DW" using hd_Cons_tl[OF dne] hj by simp
  have Lform: "L = TW @ jn # tl DW" using TWd dwform by simp
  from vinTW obtain A B where AB: "TW = A @ v # B" by (meson split_list)
  have dec: "L = A @ v # (B @ jn # tl DW)" using Lform AB by simp
  have "follow (prnt S0) v = v # (B @ jn # tl DW)"
    by (rule follow_append_ps[OF ppt dec[unfolded L_def]])
  thus "jn \<in> set (follow (prnt S0) v)" by simp
qed

lemma inchain_block_disjoint:
  assumes kpos: "0 < k" and jneq: "jn = join_of (prnt S0) i j"
      and vin: "v \<in> set (takeWhile (\<lambda>x. x \<noteq> jn) (follow (prnt S0) j))"
      and jnj: "jn \<in> set (follow (prnt S0) j)"
  shows "children (prnt S0) v \<inter> set (block S0 p) = {}"
proof (rule ccontr)
  assume "children (prnt S0) v \<inter> set (block S0 p) \<noteq> {}"
  then obtain u where uv: "u \<in> children (prnt S0) v" and ub: "u \<in> set (block S0 p)" by auto
  have vu: "v \<in> set (follow (prnt S0) u)" using uv unfolding children_def by simp
  have pu: "p \<in> set (follow (prnt S0) u)" using ub block_props(4)[OF arb pV] unfolding children_def by simp
  from vu obtain X Y where XY: "follow (prnt S0) u = X @ v # Y" by (meson split_list)
  have fv: "follow (prnt S0) v = v # Y" using follow_append_ps[OF ppt XY] by auto
  have jnv: "jn \<in> set (follow (prnt S0) v)" and vnej: "v \<noteq> jn" using below_jn[OF vin jnj] by auto
  have rinv: "rooted_arborescense_invar r V (prnt S0)" using arb unfolding arb_invar_def by simp
  have vj: "v \<in> set (follow (prnt S0) j)" using vin set_takeWhileD by fastforce
  show False
  proof (cases "p \<in> set (v # Y)")
    case True
    hence "p \<in> set (follow (prnt S0) v)" using fv by simp
    hence vcp: "v \<in> children (prnt S0) p" unfolding children_def by simp
    have "j \<in> children (prnt S0) v" using vj unfolding children_def by simp
    moreover have "children (prnt S0) v \<subseteq> children (prnt S0) p" using vcp by (rule children_subset[OF ppt])
    ultimately have "j \<in> children (prnt S0) p" by auto
    thus False using jnotp by simp
  next
    case False
    hence "p \<in> set X" using pu XY by auto
    then obtain X1 X2 where "X = X1 @ p # X2" by (meson split_list)
    hence "follow (prnt S0) u = X1 @ p # (X2 @ v # Y)" using XY by simp
    hence "follow (prnt S0) p = p # (X2 @ v # Y)" by (rule follow_append_ps[OF ppt])
    hence vfp: "v \<in> set (follow (prnt S0) p)" by simp
    have pi: "p \<in> set (follow (prnt S0) i)" using stem_chain[of k 0] kpos pathk path0 by simp
    have vi: "v \<in> set (follow (prnt S0) i)" using follow_trans[OF ppt pi vfp] by auto
    have lst: "last (follow (prnt S0) i) = last (follow (prnt S0) j)"
      using last_follow_root[OF rinv iV] last_follow_root[OF rinv jV] by simp
    have "v \<in> set (follow (prnt S0) (join_of (prnt S0) i j))" using join_of_first[OF ppt lst vi vj] by auto
    hence vjn: "v \<in> set (follow (prnt S0) jn)" using jneq by simp
    have "v = jn" using ancestor_antisym[OF ppt vjn jnv] by auto
    thus False using vnej by simp
  qed
qed

text \<open>Clause-I region cards.  @{term on_card}: the moved block has @{term "snum S0 p"} nodes.  The
      IN-chain region (@{term v} strictly before @{term jn} on @{term j}'s path): the new subtree is the
      old subtree disjointly extended by the block, so @{term "snum S0 v + snum S0 p"}.  The dichotomy
      @{term newprnt_follow_dichotomy}: any node on a block node's new root-path is itself in the block
      or on @{term j}'s path --- so a node off both keeps its old subtree minus the block
      (@{term children_newprnt_off_jpath}), the engine for the OUT-chain and disjoint-branch regions.\<close>
lemma on_card: "card (set (block S0 p)) = snum S0 p"
proof -
  show ?thesis using block_props(4)[OF arb pV] arb pV unfolding arb_invar_def by simp
qed

lemma rinv0: "rooted_arborescense_invar r V (prnt S0)" using arb unfolding arb_invar_def by simp

lemma children_finite: "v \<in> V \<Longrightarrow> finite (children (prnt S0) v)"
  using block_props(4)[OF arb] by (metis List.finite_set)

lemma i_in_block: "i \<in> set (block S0 p)"
  using stem_chain[of k 0] pathk path0 block_props(4)[OF arb pV] by (cases "k = 0") (auto simp: children_def)

lemma card_children_newprnt_INchain:
  assumes kpos: "0 < k" and jneq: "jn = join_of (prnt S0) i j"
      and vin: "v \<in> set (takeWhile (\<lambda>x. x \<noteq> jn) (follow (prnt S0) j))"
      and jnj: "jn \<in> set (follow (prnt S0) j)"
  shows "card (children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v) = snum S0 v + snum S0 p"
proof -
  have vj: "v \<in> set (follow (prnt S0) j)" using vin set_takeWhileD by fastforce
  have vV: "v \<in> V" using follow_subset_V[OF rinv0 jV] vj by auto
  have chnp: "children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v = children (prnt S0) v \<union> set (block S0 p)"
    by (rule children_newprnt_jpath[OF kpos vj])
  have disj: "children (prnt S0) v \<inter> set (block S0 p) = {}"
    by (rule inchain_block_disjoint[OF kpos jneq vin jnj])
  have "card (children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v) = card (children (prnt S0) v) + card (set (block S0 p))"
    using chnp disj children_finite[OF vV] by (simp add: card_Un_disjoint)
  also have "\<dots> = snum S0 v + snum S0 p"
    using vV on_card arb unfolding arb_invar_def by simp
  finally show ?thesis .
qed

lemma newprnt_follow_dichotomy:
  assumes kpos: "0 < k" and ub: "u \<in> set (block S0 p)"
      and vu: "v \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u)"
  shows "v \<in> set (block S0 p) \<or> v \<in> set (follow (prnt S0) j)"
proof -
  have psN: "parent_spec ((prnt S0 ++ REV k)(p \<mapsto> s_pred k))"
    using clauseA rooted_arborescense_invar_parent_spec by auto
  have iu: "i \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u)"
    using ub by (rule mp[OF block_p_under_i[OF kpos]])
  from iu obtain A B where AB: "follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u = A @ i # B" by (meson split_list)
  have "follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) i = i # B" using follow_append_ps[OF psN AB] by auto
  hence Beq: "B = follow (prnt S0) j" using follow_newprnt_i[OF kpos] by simp
  from vu AB have "v \<in> set A \<or> v \<in> set (i # B)" by auto
  thus ?thesis
  proof
    assume "v \<in> set (i # B)"
    hence "v = i \<or> v \<in> set (follow (prnt S0) j)" using Beq by auto
    thus ?thesis using i_in_block by auto
  next
    assume vA: "v \<in> set A"
    then obtain A1 A2 where "A = A1 @ v # A2" by (meson split_list)
    hence "follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u = A1 @ v # (A2 @ i # B)" using AB by simp
    hence "follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v = v # (A2 @ i # B)" by (rule follow_append_ps[OF psN])
    hence "i \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v)" by simp
    hence "v \<in> children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) i" unfolding children_def by simp
    thus ?thesis using children_newprnt_i[OF kpos] by simp
  qed
qed

lemma children_newprnt_off_jpath:
  assumes kpos: "0 < k" and vnb: "v \<notin> set (block S0 p)" and vnj: "v \<notin> set (follow (prnt S0) j)"
  shows "children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v = children (prnt S0) v - set (block S0 p)"
proof -
  have emp: "{u \<in> set (block S0 p). v \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u)} = {}"
  proof -
    { fix u assume "u \<in> set (block S0 p)" and "v \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u)"
      hence "v \<in> set (block S0 p) \<or> v \<in> set (follow (prnt S0) j)"
        using newprnt_follow_dichotomy[OF kpos] by auto
      hence False using vnb vnj by simp }
    thus ?thesis by auto
  qed
  have "children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v =
        (children (prnt S0) v - set (block S0 p)) \<union> {u \<in> set (block S0 p). v \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u)}"
    by (rule children_newprnt_decomp[OF kpos])
  also have "\<dots> = children (prnt S0) v - set (block S0 p)" unfolding emp by simp
  finally show ?thesis .
qed

text \<open>OUT-chain region.  @{term below_jn_gen} generalises @{term below_jn} to any root-path.  For a
      node @{term v} strictly before @{term jn} on @{term "the (prnt S0 p)"}'s path (the OUT-chain,
      @{term v_out} being @{term p}'s old parent), @{term v} is off @{term j}'s path (else it would be a
      common ancestor of @{term i}, @{term j}, forcing @{term "v = jn"}) and off the block, yet still an
      ancestor of the whole block --- so its new subtree loses exactly the block: @{term "snum S0 v - snum S0 p"}.\<close>
lemma below_jn_gen:
  assumes vin: "v \<in> set (takeWhile (\<lambda>x. x \<noteq> jn) (follow (prnt S0) w))"
      and jnw: "jn \<in> set (follow (prnt S0) w)"
  shows "jn \<in> set (follow (prnt S0) v) \<and> v \<noteq> jn"
proof
  define L where "L = follow (prnt S0) w"
  define TW where "TW = takeWhile (\<lambda>x. x \<noteq> jn) L"
  define DW where "DW = dropWhile (\<lambda>x. x \<noteq> jn) L"
  have vinTW: "v \<in> set TW" using vin by (simp add: TW_def L_def)
  show "v \<noteq> jn" using takeWhile_holds[OF vinTW[unfolded TW_def]] by simp
  have TWd: "L = TW @ DW" by (simp add: TW_def DW_def)
  have dne: "DW \<noteq> []" using jnw by (simp add: DW_def L_def dropWhile_eq_Nil_conv)
  have "\<not> (hd DW \<noteq> jn)" using hd_dropWhile[OF dne[unfolded DW_def]] by (simp add: DW_def)
  hence hj: "hd DW = jn" by simp
  have dwform: "DW = jn # tl DW" using hd_Cons_tl[OF dne] hj by simp
  have Lform: "L = TW @ jn # tl DW" using TWd dwform by simp
  from vinTW obtain A B where AB: "TW = A @ v # B" by (meson split_list)
  have dec: "L = A @ v # (B @ jn # tl DW)" using Lform AB by simp
  have "follow (prnt S0) v = v # (B @ jn # tl DW)"
    by (rule follow_append_ps[OF ppt dec[unfolded L_def]])
  thus "jn \<in> set (follow (prnt S0) v)" by simp
qed

lemma card_children_newprnt_OUTchain:
  assumes kpos: "0 < k" and jneq: "jn = join_of (prnt S0) i j"
      and jnp: "jn \<in> set (follow (prnt S0) p)" and pjn: "p \<noteq> jn"
      and vin: "v \<in> set (takeWhile (\<lambda>x. x \<noteq> jn) (follow (prnt S0) (the (prnt S0 p))))"
  shows "card (children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v) = snum S0 v - snum S0 p"
proof -
  have "p \<in> dom (prnt S0)" using pV pne_r rooted_arborescense_invar_dom[OF rinv0] by simp
  then obtain vo where pvo: "prnt S0 p = Some vo" by auto
  have voeq: "the (prnt S0 p) = vo" using pvo by simp
  have fp: "follow (prnt S0) p = p # follow (prnt S0) vo" using pvo by (subst follow_ps_simps[OF ppt]) simp
  have vofv: "vo \<in> set (follow (prnt S0) vo)"
    using follow_hd_ps[OF ppt, of vo] follow_ne_ps[OF ppt, of vo] by (metis hd_in_set)
  have voap: "vo \<in> set (follow (prnt S0) p)" using fp vofv by simp
  have distp: "distinct (follow (prnt S0) p)" by (rule follow_distinct_ps[OF ppt])
  have pnvo: "p \<notin> set (follow (prnt S0) vo)" using distp fp by simp
  have pai: "p \<in> set (follow (prnt S0) i)" using stem_chain[of k 0] pathk path0 by simp
  have voai: "vo \<in> set (follow (prnt S0) i)" using follow_trans[OF ppt pai voap] by auto
  have jnvo: "jn \<in> set (follow (prnt S0) vo)" using jnp pjn fp by simp
  have vin': "v \<in> set (takeWhile (\<lambda>x. x \<noteq> jn) (follow (prnt S0) vo))" using vin voeq by simp
  have vvo: "v \<in> set (follow (prnt S0) vo)" using vin' set_takeWhileD by fastforce
  have jnv: "jn \<in> set (follow (prnt S0) v)" and vnej: "v \<noteq> jn" using below_jn_gen[OF vin' jnvo] by auto
  have voV: "vo \<in> V" using follow_subset_V[OF rinv0 pV] voap by auto
  have vV: "v \<in> V" using follow_subset_V[OF rinv0 voV] vvo by auto
  have vap: "v \<in> set (follow (prnt S0) p)" using follow_trans[OF ppt voap vvo] by auto
  have vnb: "v \<notin> set (block S0 p)"
  proof
    assume "v \<in> set (block S0 p)"
    hence pfv: "p \<in> set (follow (prnt S0) v)" using block_props(4)[OF arb pV] unfolding children_def by simp
    have "p \<in> set (follow (prnt S0) vo)" using follow_trans[OF ppt vvo pfv] by auto
    thus False using pnvo by simp
  qed
  have vnj: "v \<notin> set (follow (prnt S0) j)"
  proof
    assume vj: "v \<in> set (follow (prnt S0) j)"
    have vi: "v \<in> set (follow (prnt S0) i)" using follow_trans[OF ppt voai vvo] by auto
    have lst: "last (follow (prnt S0) i) = last (follow (prnt S0) j)"
      using last_follow_root[OF rinv0 iV] last_follow_root[OF rinv0 jV] by simp
    have "v \<in> set (follow (prnt S0) (join_of (prnt S0) i j))" using join_of_first[OF ppt lst vi vj] by auto
    hence vfjn: "v \<in> set (follow (prnt S0) jn)" using jneq by simp
    have "v = jn" using ancestor_antisym[OF ppt vfjn jnv] by auto
    thus False using vnej by simp
  qed
  have bsub: "set (block S0 p) \<subseteq> children (prnt S0) v"
  proof
    fix u assume "u \<in> set (block S0 p)"
    hence pfu: "p \<in> set (follow (prnt S0) u)" using block_props(4)[OF arb pV] unfolding children_def by simp
    have "v \<in> set (follow (prnt S0) u)" using follow_trans[OF ppt pfu vap] by auto
    thus "u \<in> children (prnt S0) v" unfolding children_def by simp
  qed
  have choff: "children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v = children (prnt S0) v - set (block S0 p)"
    by (rule children_newprnt_off_jpath[OF kpos vnb vnj])
  show ?thesis using choff card_Diff_subset[OF finite_set bsub] vV on_card arb unfolding arb_invar_def by simp
qed

text \<open>The unchanged regions.  On @{term j}'s path at or above @{term jn} the block was already inside
      @{term v}'s subtree, so the new subtree is unchanged; in a branch disjoint from the block the new
      subtree is unchanged too.  Both give @{term "snum S0 v"}.\<close>
lemma card_children_newprnt_jpath_above:
  assumes kpos: "0 < k" and vj: "v \<in> set (follow (prnt S0) j)"
      and bsub: "set (block S0 p) \<subseteq> children (prnt S0) v" and vV: "v \<in> V"
  shows "card (children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v) = snum S0 v"
proof -
  have "children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v = children (prnt S0) v \<union> set (block S0 p)"
    by (rule children_newprnt_jpath[OF kpos vj])
  also have "\<dots> = children (prnt S0) v" using bsub by auto
  finally have "children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v = children (prnt S0) v" .
  thus ?thesis using vV arb unfolding arb_invar_def by simp
qed

lemma card_children_newprnt_disjoint:
  assumes kpos: "0 < k" and vnb: "v \<notin> set (block S0 p)" and vnj: "v \<notin> set (follow (prnt S0) j)"
      and disj: "set (block S0 p) \<inter> children (prnt S0) v = {}" and vV: "v \<in> V"
  shows "card (children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v) = snum S0 v"
proof -
  have "children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v = children (prnt S0) v - set (block S0 p)"
    by (rule children_newprnt_off_jpath[OF kpos vnb vnj])
  also have "\<dots> = children (prnt S0) v" using disj by auto
  finally have "children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v = children (prnt S0) v" .
  thus ?thesis using vV arb unfolding arb_invar_def by simp
qed

text \<open>The reversed-block-internal region (the hard core of clause I).  Within the moved block the stem
      is reversed and the non-stem edges are kept, so for a block node @{term u} the stem nodes on its
      new root-path are exactly (up to its stem entry @{term "s M"}) while the
      stem nodes on its old path are .  Hence, for a stem target @{term "s t"},
      @{term "s t"} is on @{term u}'s new path iff @{term "s (t - 1)"} is off its old path
      (@{term newpath_stem_char}); a non-stem block target keeps the same membership on both paths
      (@{term newpath_nonstem_char}).  This gives 
      (@{term "snum S0 p - snum S0 (s (t-1))"}) and an unchanged subtree for non-stem block nodes.\<close>
lemma stem_follow_iff:
  assumes ak: "a \<le> k" and bk: "b \<le> k"
  shows "(s a \<in> set (follow (prnt S0) (s b))) = (b \<le> a)"
proof
  assume sab: "s a \<in> set (follow (prnt S0) (s b))"
  show "b \<le> a"
  proof (rule ccontr)
    assume "\<not> b \<le> a"
    hence ab: "a < b" by simp
    hence "s b \<in> set (follow (prnt S0) (s a))" using stem_chain[of b a] bk by simp
    hence "s a = s b" using ancestor_antisym[OF ppt sab] by simp
    hence "a = b" using inj ak bk by (auto simp: inj_on_eq_iff)
    thus False using ab by simp
  qed
next
  assume "b \<le> a"
  thus "s a \<in> set (follow (prnt S0) (s b))" using stem_chain[of a b] ak by simp
qed

lemma follow_stem_prefix:
  assumes ak: "a \<le> k"
  shows "follow (prnt S0) (s a) = map s [a..<Suc k] @ follow (prnt S0) (the (prnt S0 p))"
proof -
  have "p \<in> dom (prnt S0)" using pV pne_r rooted_arborescense_invar_dom[OF rinv0] by simp
  then obtain vo where pvo: "prnt S0 p = Some vo" by auto
  have vothe: "the (prnt S0 p) = vo" using pvo by simp
  show ?thesis using ak
  proof (induction rule: inc_induct)
    case base
    have "follow (prnt S0) p = p # follow (prnt S0) vo" using pvo by (subst follow_ps_simps[OF ppt]) simp
    thus ?case using pathk vothe by simp
  next
    case (step n)
    have "prnt S0 (s n) = Some (s (Suc n))" using pathS step.hyps(2) by simp
    hence "follow (prnt S0) (s n) = s n # follow (prnt S0) (s (Suc n))"
      by (subst follow_ps_simps[OF ppt]) simp
    also have "\<dots> = s n # (map s [Suc n..<Suc k] @ follow (prnt S0) (the (prnt S0 p)))" using step.IH by simp
    also have "\<dots> = map s [n..<Suc k] @ follow (prnt S0) (the (prnt S0 p))"
      using step.hyps(2) by (simp add: upt_conv_Cons)
    finally show ?case .
  qed
qed

lemma block_notin_follow_j:
  assumes wb: "w \<in> set (block S0 p)" shows "w \<notin> set (follow (prnt S0) j)"
  using wb block_props(4)[OF arb pV] children_subset[OF ppt] jnotp by (auto simp: children_def)

lemma block_notin_follow_i:
  assumes wb: "w \<in> set (block S0 p)" and wns: "w \<notin> s ` {..k}"
  shows "w \<notin> set (follow (prnt S0) i)"
proof
  assume wfi: "w \<in> set (follow (prnt S0) i)"
  have "p \<in> dom (prnt S0)" using pV pne_r rooted_arborescense_invar_dom[OF rinv0] by simp
  then obtain vo where pvo: "prnt S0 p = Some vo" by auto
  have fp: "follow (prnt S0) p = p # follow (prnt S0) vo" using pvo by (subst follow_ps_simps[OF ppt]) simp
  have pnvo: "p \<notin> set (follow (prnt S0) vo)" using follow_distinct_ps[OF ppt] fp by (metis distinct.simps(2))
  have flist: "follow (prnt S0) i = map s [0..<Suc k] @ follow (prnt S0) vo"
    using follow_stem_prefix[of 0] path0 pvo by simp
  have "set (map s [0..<Suc k]) = s ` {..k}" by (simp add: atMost_upto)
  hence "w \<in> s ` {..k} \<or> w \<in> set (follow (prnt S0) vo)" using wfi flist by auto
  hence wvout: "w \<in> set (follow (prnt S0) vo)" using wns by simp
  have pfw: "p \<in> set (follow (prnt S0) w)" using wb block_props(4)[OF arb pV] unfolding children_def by simp
  have "p \<in> set (follow (prnt S0) vo)" using follow_trans[OF ppt wvout pfw] by auto
  thus False using pnvo by simp
qed

lemma stem_notin_jpath:
  assumes jneq: "jn = join_of (prnt S0) i j" and jnp: "jn \<in> set (follow (prnt S0) p)"
      and pjn: "p \<noteq> jn" and tk: "t \<le> k"
  shows "s t \<notin> set (follow (prnt S0) j)"
proof
  assume sj: "s t \<in> set (follow (prnt S0) j)"
  have si: "s t \<in> set (follow (prnt S0) i)" using stem_chain[of t 0] tk path0 by simp
  have lst: "last (follow (prnt S0) i) = last (follow (prnt S0) j)"
    using last_follow_root[OF rinv0 iV] last_follow_root[OF rinv0 jV] by simp
  have "s t \<in> set (follow (prnt S0) (join_of (prnt S0) i j))" using join_of_first[OF ppt lst si sj] by auto
  hence stjn: "s t \<in> set (follow (prnt S0) jn)" using jneq by simp
  have pst: "p \<in> set (follow (prnt S0) (s t))" using stem_chain[of k t] tk pathk by simp
  have jnst: "jn \<in> set (follow (prnt S0) (s t))" using follow_trans[OF ppt pst jnp] by auto
  have "s t = jn" using ancestor_antisym[OF ppt stjn jnst] by auto
  hence "p \<in> set (follow (prnt S0) jn)" using pst by simp
  hence "p = jn" using ancestor_antisym[OF ppt _ jnp] by simp
  thus False using pjn by simp
qed

lemma newpath_stem_char:
  assumes kpos: "0 < k" and jneq: "jn = join_of (prnt S0) i j"
      and jnp: "jn \<in> set (follow (prnt S0) p)" and pjn: "p \<noteq> jn"
  shows "u \<in> set (block S0 p) \<longrightarrow>
         (\<forall>t. 1 \<le> t \<and> t \<le> k \<longrightarrow>
            (s t \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u)) =
            (s (t - 1) \<notin> set (follow (prnt S0) u)))"
proof -
  have psN: "parent_spec ((prnt S0 ++ REV k)(p \<mapsto> s_pred k))"
    using clauseA rooted_arborescense_invar_parent_spec by auto
  show ?thesis
  proof (induction rule: parent_spec_i.follow.pinduct[OF follow_dom_ps[OF psN, of u]])
    case (1 u)
    show ?case
    proof (intro impI allI)
      assume ub: "u \<in> set (block S0 p)"
      fix t assume tcond: "1 \<le> t \<and> t \<le> k"
      hence t1: "1 \<le> t" and tk: "t \<le> k" by auto
      have tm1k: "t - 1 \<le> k" using tk by simp
      show "(s t \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u)) = (s (t - 1) \<notin> set (follow (prnt S0) u))"
      proof (cases "u = i")
        case True
        have "s t \<noteq> i" using inj t1 tk path0 by (auto simp: inj_on_eq_iff)
        moreover have "s t \<notin> set (follow (prnt S0) j)" by (rule stem_notin_jpath[OF jneq jnp pjn tk])
        ultimately have Lf: "s t \<notin> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u)"
          using True follow_newprnt_i[OF kpos] by simp
        have "s (t - 1) \<in> set (follow (prnt S0) i)" using stem_chain[of "t - 1" 0] tm1k path0 by simp
        hence Rf: "\<not> (s (t - 1) \<notin> set (follow (prnt S0) u))" using True by simp
        show ?thesis using Lf Rf by simp
      next
        case False
        obtain w where w: "((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u = Some w" and wb: "w \<in> set (block S0 p)"
          using block_p_newprnt_step[OF kpos ub False] by auto
        have fnu: "follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u = u # follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) w"
          using w by (subst follow_ps_simps[OF psN]) simp
        have IHw: "(s t \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) w)) = (s (t - 1) \<notin> set (follow (prnt S0) w))"
          using 1(2)[OF w] wb t1 tk by blast
        show ?thesis
        proof (cases "u \<in> s ` {..k}")
          case True
          then obtain m where mk: "m \<le> k" and um: "u = s m" by auto
          have m1: "1 \<le> m" using um False path0 inj mk by (cases "m = 0") auto
          have "((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (s m) = Some (s_pred m)"
            using Wseq_eval[of "Suc k" m] mk newprnt_eq by simp
          hence "w = s_pred m" using w um by simp
          hence wsm: "w = s (m - 1)" using m1 by (simp add: s_pred_def)
          have mm1k: "m - 1 \<le> k" using mk by simp
          have Leq: "(s t \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u)) = (t \<le> m)"
          proof -
            have "(s t \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u)) = (s t = s m \<or> s t \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) w))"
              using fnu um by simp
            also have "\<dots> = (s t = s m \<or> s (t - 1) \<notin> set (follow (prnt S0) w))" using IHw by simp
            also have "\<dots> = (s t = s m \<or> \<not> (m - 1 \<le> t - 1))" using wsm stem_follow_iff[OF tm1k mm1k] by simp
            also have "\<dots> = (t = m \<or> \<not> (m - 1 \<le> t - 1))" using inj tk mk by (simp add: inj_on_eq_iff)
            also have "\<dots> = (t \<le> m)" using m1 t1 by presburger
            finally show ?thesis .
          qed
          have Req: "(s (t - 1) \<notin> set (follow (prnt S0) u)) = (t \<le> m)"
          proof -
            have "(s (t - 1) \<notin> set (follow (prnt S0) u)) = (\<not> (m \<le> t - 1))"
              using um stem_follow_iff[OF tm1k mk] by simp
            also have "\<dots> = (t \<le> m)" using m1 t1 by presburger
            finally show ?thesis .
          qed
          show ?thesis using Leq Req by simp
        next
          case False
          hence "\<forall>t' < Suc k. u \<noteq> s t'" by auto
          hence "Wseq (Suc k) u = prnt S0 u" using Wseq_fresh[of "Suc k" u] by auto
          hence "((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u = prnt S0 u" using newprnt_eq by simp
          hence wpu: "prnt S0 u = Some w" using w by simp
          have foldu: "follow (prnt S0) u = u # follow (prnt S0) w" using wpu by (subst follow_ps_simps[OF ppt]) simp
          have stnu: "s t \<noteq> u" using False tk by auto
          have stm1nu: "s (t - 1) \<noteq> u" using False tm1k by auto
          show ?thesis using fnu stnu IHw foldu stm1nu by simp
        qed
      qed
    qed
  qed
qed

lemma children_newprnt_stem:
  assumes kpos: "0 < k" and jneq: "jn = join_of (prnt S0) i j"
      and jnp: "jn \<in> set (follow (prnt S0) p)" and pjn: "p \<noteq> jn"
      and t1: "1 \<le> t" and tk: "t \<le> k"
  shows "children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (s t) = set (block S0 p) - set (block S0 (s (t - 1)))"
proof -
  have tm1k: "t - 1 \<le> k" using tk by simp
  have stm1V: "s (t - 1) \<in> V" using stem_chain[of "t - 1" 0] tm1k path0 follow_subset_V[OF rinv0 iV] by auto
  have blk_stm1: "set (block S0 (s (t - 1))) = children (prnt S0) (s (t - 1))" by (rule block_props(4)[OF arb stm1V])
  have blk_p: "set (block S0 p) = children (prnt S0) p" by (rule block_props(4)[OF arb pV])
  show ?thesis
  proof
    show "children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (s t) \<subseteq> set (block S0 p) - set (block S0 (s (t - 1)))"
    proof
      fix u assume "u \<in> children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (s t)"
      hence su: "s t \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u)" unfolding children_def by simp
      have ub: "u \<in> set (block S0 p)"
      proof (rule ccontr)
        assume unb: "u \<notin> set (block S0 p)"
        have "s t \<in> set (follow (prnt S0) u)" using su follow_newprnt_off_block[OF kpos unb] by simp
        hence ust: "u \<in> children (prnt S0) (s t)" unfolding children_def by simp
        have "p \<in> set (follow (prnt S0) (s t))" using stem_chain[of k t] tk pathk by simp
        hence "s t \<in> children (prnt S0) p" unfolding children_def by simp
        hence "children (prnt S0) (s t) \<subseteq> children (prnt S0) p" by (rule children_subset[OF ppt])
        hence "u \<in> children (prnt S0) p" using ust by auto
        thus False using unb blk_p by simp
      qed
      have bic: "(s t \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u)) = (s (t - 1) \<notin> set (follow (prnt S0) u))"
        using newpath_stem_char[OF kpos jneq jnp pjn] ub t1 tk by auto
      have "s (t - 1) \<notin> set (follow (prnt S0) u)" using su bic by simp
      hence "u \<notin> children (prnt S0) (s (t - 1))" unfolding children_def by simp
      hence "u \<notin> set (block S0 (s (t - 1)))" using blk_stm1 by simp
      thus "u \<in> set (block S0 p) - set (block S0 (s (t - 1)))" using ub by simp
    qed
  next
    show "set (block S0 p) - set (block S0 (s (t - 1))) \<subseteq> children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (s t)"
    proof
      fix u assume "u \<in> set (block S0 p) - set (block S0 (s (t - 1)))"
      hence ub: "u \<in> set (block S0 p)" and unb: "u \<notin> set (block S0 (s (t - 1)))" by auto
      have "u \<notin> children (prnt S0) (s (t - 1))" using unb blk_stm1 by simp
      hence "s (t - 1) \<notin> set (follow (prnt S0) u)" unfolding children_def by simp
      moreover have bic: "(s t \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u)) = (s (t - 1) \<notin> set (follow (prnt S0) u))"
        using newpath_stem_char[OF kpos jneq jnp pjn] ub t1 tk by auto
      ultimately have "s t \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u)" by simp
      thus "u \<in> children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (s t)" unfolding children_def by simp
    qed
  qed
qed

lemma card_children_newprnt_stem:
  assumes kpos: "0 < k" and jneq: "jn = join_of (prnt S0) i j"
      and jnp: "jn \<in> set (follow (prnt S0) p)" and pjn: "p \<noteq> jn"
      and t1: "1 \<le> t" and tk: "t \<le> k"
  shows "card (children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (s t)) = snum S0 p - snum S0 (s (t - 1))"
proof -
  have tm1k: "t - 1 \<le> k" using tk by simp
  have stm1V: "s (t - 1) \<in> V" using stem_chain[of "t - 1" 0] tm1k path0 follow_subset_V[OF rinv0 iV] by auto
  have blk_stm1: "set (block S0 (s (t - 1))) = children (prnt S0) (s (t - 1))" by (rule block_props(4)[OF arb stm1V])
  have blk_p: "set (block S0 p) = children (prnt S0) p" by (rule block_props(4)[OF arb pV])
  have "p \<in> set (follow (prnt S0) (s (t - 1)))" using stem_chain[of k "t - 1"] tk tm1k pathk by simp
  hence "s (t - 1) \<in> children (prnt S0) p" unfolding children_def by simp
  hence "children (prnt S0) (s (t - 1)) \<subseteq> children (prnt S0) p" by (rule children_subset[OF ppt])
  hence sub: "set (block S0 (s (t - 1))) \<subseteq> set (block S0 p)" using blk_stm1 blk_p by simp
  have "card (children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (s t)) = card (set (block S0 p) - set (block S0 (s (t - 1))))"
    using children_newprnt_stem[OF kpos jneq jnp pjn t1 tk] by simp
  also have "\<dots> = card (set (block S0 p)) - card (set (block S0 (s (t - 1))))"
    using card_Diff_subset[OF finite_set sub] by simp
  also have "\<dots> = snum S0 p - snum S0 (s (t - 1))"
    using on_card blk_stm1 stm1V arb unfolding arb_invar_def by simp
  finally show ?thesis .
qed

lemma newpath_nonstem_char:
  assumes kpos: "0 < k" and wb: "w \<in> set (block S0 p)" and wns: "w \<notin> s ` {..k}"
  shows "u \<in> set (block S0 p) \<longrightarrow>
         (w \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u)) = (w \<in> set (follow (prnt S0) u))"
proof -
  have psN: "parent_spec ((prnt S0 ++ REV k)(p \<mapsto> s_pred k))"
    using clauseA rooted_arborescense_invar_parent_spec by auto
  have iin: "i \<in> s ` {..k}" using path0 by auto
  show ?thesis
  proof (induction rule: parent_spec_i.follow.pinduct[OF follow_dom_ps[OF psN, of u]])
    case (1 u)
    show ?case
    proof
      assume ub: "u \<in> set (block S0 p)"
      show "(w \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u)) = (w \<in> set (follow (prnt S0) u))"
      proof (cases "u = i")
        case True
        have wni: "w \<notin> set (follow (prnt S0) i)" by (rule block_notin_follow_i[OF wb wns])
        have wnj: "w \<notin> set (follow (prnt S0) j)" by (rule block_notin_follow_j[OF wb])
        have "w \<noteq> i" using wns iin by auto
        hence "w \<notin> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) i)" using follow_newprnt_i[OF kpos] wnj by simp
        thus ?thesis using True wni by simp
      next
        case False
        obtain v' where v: "((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u = Some v'" and vb: "v' \<in> set (block S0 p)"
          using block_p_newprnt_step[OF kpos ub False] by auto
        have fnu: "follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u = u # follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v'"
          using v by (subst follow_ps_simps[OF psN]) simp
        have IHv: "(w \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v')) = (w \<in> set (follow (prnt S0) v'))"
          using 1(2)[OF v] vb by blast
        show ?thesis
        proof (cases "u \<in> s ` {..k}")
          case True
          then obtain m where mk: "m \<le> k" and um: "u = s m" by auto
          have m1: "1 \<le> m" using um False path0 inj mk by (cases "m = 0") auto
          have "((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (s m) = Some (s_pred m)"
            using Wseq_eval[of "Suc k" m] mk newprnt_eq by simp
          hence "v' = s_pred m" using v um by simp
          hence vsm: "v' = s (m - 1)" using m1 by (simp add: s_pred_def)
          have "m - 1 < k" using mk m1 by simp
          hence "prnt S0 (s (m - 1)) = Some (s m)" using pathS m1 by simp
          hence foldv: "follow (prnt S0) v' = s (m - 1) # follow (prnt S0) (s m)"
            using vsm by (subst follow_ps_simps[OF ppt]) simp
          have wnesm: "w \<noteq> s m" using wns mk by auto
          have wnesm1: "w \<noteq> s (m - 1)" using wns mk by auto
          show ?thesis using fnu um wnesm IHv foldv wnesm1 um by simp
        next
          case False
          hence "\<forall>t' < Suc k. u \<noteq> s t'" by auto
          hence "Wseq (Suc k) u = prnt S0 u" using Wseq_fresh[of "Suc k" u] by auto
          hence "((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u = prnt S0 u" using newprnt_eq by simp
          hence vpu: "prnt S0 u = Some v'" using v by simp
          have foldu: "follow (prnt S0) u = u # follow (prnt S0) v'" using vpu by (subst follow_ps_simps[OF ppt]) simp
          show ?thesis using fnu IHv foldu by simp
        qed
      qed
    qed
  qed
qed

lemma card_children_newprnt_nonstem_block:
  assumes kpos: "0 < k" and wb: "w \<in> set (block S0 p)" and wns: "w \<notin> s ` {..k}"
  shows "card (children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) w) = snum S0 w"
proof -
  have eq: "\<And>u. (w \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u)) = (w \<in> set (follow (prnt S0) u))"
  proof -
    fix u
    show "(w \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u)) = (w \<in> set (follow (prnt S0) u))"
    proof (cases "u \<in> set (block S0 p)")
      case True thus ?thesis using newpath_nonstem_char[OF kpos wb wns] by auto
    next
      case False thus ?thesis using follow_newprnt_off_block[OF kpos False] by simp
    qed
  qed
  have cheq: "children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) w = children (prnt S0) w"
    unfolding children_def using eq by auto
  have wV: "w \<in> V"
  proof (rule ccontr)
    assume "w \<notin> V"
    hence "prnt S0 w = None" using rooted_arborescense_invar_dom[OF rinv0] by auto
    hence "follow (prnt S0) w = [w]" by (subst follow_ps_simps[OF ppt]) simp
    moreover have "p \<in> set (follow (prnt S0) w)" using wb block_props(4)[OF arb pV] unfolding children_def by simp
    ultimately have "p = w" by simp
    thus False using \<open>w \<notin> V\<close> pV by simp
  qed
  show ?thesis using cheq wV arb unfolding arb_invar_def by simp
qed

text \<open>Clause I assembly.  @{term follow_dropWhile}/@{term follow_comparable} are generic root-path
      lemmas; @{term join_facts} derives from @{term "jn = join_of (prnt S0) i j"} that @{term jn} lies
      on both @{term j}'s and @{term p}'s root-paths and is a proper ancestor of @{term p};
      @{term in_out_disjoint} shows the IN- and OUT-chains do not overlap; @{term jpath_above_block_sub}
      / @{term disjoint_block_int} settle the two unchanged sub-regions of the else-branch.  The
      case-split @{term snum_card_match} then evaluates @{const final_snum} region by region, and
      @{term clauseI} combines it with @{thm update_tree_snum} and @{thm update_tree_prnt} to give the
      clause-I conjunct of @{const arb_invar} for @{term "update_tree S0 i j p jn"}.\<close>
lemma follow_dropWhile:
  assumes ps: "parent_spec T" and xw: "x \<in> set (follow T w)"
  shows "dropWhile (\<lambda>y. y \<noteq> x) (follow T w) = follow T x"
proof -
  from xw obtain A B where AB: "follow T w = A @ x # B" by (meson split_list)
  have dist: "distinct (follow T w)" by (rule follow_distinct_ps[OF ps])
  have xnA: "x \<notin> set A" using dist AB by auto
  have fx: "follow T x = x # B" using follow_append_ps[OF ps AB] by auto
  have allA: "\<forall>y \<in> set A. y \<noteq> x" using xnA by auto
  have "dropWhile (\<lambda>y. y \<noteq> x) (A @ (x # B)) = dropWhile (\<lambda>y. y \<noteq> x) (x # B)"
    using allA by (simp add: dropWhile_append2)
  also have "\<dots> = x # B" by simp
  finally show ?thesis using AB fx by simp
qed

lemma follow_comparable:
  assumes ps: "parent_spec T" and va: "v \<in> set (follow T a)" and wa: "w \<in> set (follow T a)"
  shows "v \<in> set (follow T w) \<or> w \<in> set (follow T v)"
proof -
  from va obtain X Y where XY: "follow T a = X @ v # Y" by (meson split_list)
  have fv: "follow T v = v # Y" using follow_append_ps[OF ps XY] by auto
  show ?thesis
  proof (cases "w \<in> set (v # Y)")
    case True
    hence "w \<in> set (follow T v)" using fv by simp
    thus ?thesis by simp
  next
    case False
    hence "w \<in> set X" using wa XY by auto
    then obtain X1 X2 where "X = X1 @ w # X2" by (meson split_list)
    hence "follow T a = X1 @ w # (X2 @ v # Y)" using XY by simp
    hence "follow T w = w # (X2 @ v # Y)" by (rule follow_append_ps[OF ps])
    hence "v \<in> set (follow T w)" by simp
    thus ?thesis by simp
  qed
qed

lemma jpath_above_block_sub:
  assumes vj: "v \<in> set (follow (prnt S0) j)"
      and vni: "v \<notin> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow (prnt S0) j))"
      and jnj: "jn \<in> set (follow (prnt S0) j)" and jnp: "jn \<in> set (follow (prnt S0) p)"
  shows "set (block S0 p) \<subseteq> children (prnt S0) v"
proof -
  have "v \<in> set (dropWhile (\<lambda>y. y \<noteq> jn) (follow (prnt S0) j))"
    using vj vni by (metis Un_iff set_append takeWhile_dropWhile_id)
  hence vjn: "v \<in> set (follow (prnt S0) jn)" using follow_dropWhile[OF ppt jnj] by simp
  have vp: "v \<in> set (follow (prnt S0) p)" using follow_trans[OF ppt jnp vjn] by auto
  show ?thesis
  proof
    fix u assume "u \<in> set (block S0 p)"
    hence "p \<in> set (follow (prnt S0) u)" using block_props(4)[OF arb pV] unfolding children_def by simp
    hence "v \<in> set (follow (prnt S0) u)" using follow_trans[OF ppt _ vp] by simp
    thus "u \<in> children (prnt S0) v" unfolding children_def by simp
  qed
qed

lemma disjoint_block_int:
  assumes vnj: "v \<notin> set (follow (prnt S0) j)"
      and vno: "v \<notin> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow (prnt S0) (the (prnt S0 p))))"
      and vnb: "v \<notin> set (block S0 p)" and jnj: "jn \<in> set (follow (prnt S0) j)"
      and jnp: "jn \<in> set (follow (prnt S0) p)" and pjn: "p \<noteq> jn"
  shows "set (block S0 p) \<inter> children (prnt S0) v = {}"
proof -
  have "p \<in> dom (prnt S0)" using pV pne_r rooted_arborescense_invar_dom[OF rinv0] by simp
  then obtain vo where pvo: "prnt S0 p = Some vo" by auto
  have voeq: "the (prnt S0 p) = vo" using pvo by simp
  have fp: "follow (prnt S0) p = p # follow (prnt S0) vo" using pvo by (subst follow_ps_simps[OF ppt]) simp
  have jnvo: "jn \<in> set (follow (prnt S0) vo)" using jnp pjn fp by simp
  have pblk: "p \<in> set (block S0 p)"
    using block_props(4)[OF arb pV] follow_hd_ps[OF ppt, of p] follow_ne_ps[OF ppt, of p]
    unfolding children_def by (metis hd_in_set mem_Collect_eq)
  have vnp: "v \<notin> set (follow (prnt S0) p)"
  proof
    assume "v \<in> set (follow (prnt S0) p)"
    hence "v \<in> set (p # follow (prnt S0) vo)" using fp by simp
    moreover have "v \<noteq> p" using vnb pblk by auto
    ultimately have "v \<in> set (follow (prnt S0) vo)" by simp
    hence "v \<in> set (dropWhile (\<lambda>y. y \<noteq> jn) (follow (prnt S0) vo))"
      using vno voeq by (metis Un_iff set_append takeWhile_dropWhile_id)
    hence "v \<in> set (follow (prnt S0) jn)" using follow_dropWhile[OF ppt jnvo] by simp
    hence "v \<in> set (follow (prnt S0) j)" using follow_trans[OF ppt jnj] by simp
    thus False using vnj by simp
  qed
  show ?thesis
  proof (rule ccontr)
    assume "set (block S0 p) \<inter> children (prnt S0) v \<noteq> {}"
    then obtain u where ub: "u \<in> set (block S0 p)" and uv: "u \<in> children (prnt S0) v" by auto
    have pu: "p \<in> set (follow (prnt S0) u)" using ub block_props(4)[OF arb pV] unfolding children_def by simp
    have vu: "v \<in> set (follow (prnt S0) u)" using uv unfolding children_def by simp
    from vu obtain X Y where XY: "follow (prnt S0) u = X @ v # Y" by (meson split_list)
    have fv: "follow (prnt S0) v = v # Y" using follow_append_ps[OF ppt XY] by auto
    show False
    proof (cases "p \<in> set (v # Y)")
      case True
      hence "p \<in> set (follow (prnt S0) v)" using fv by simp
      hence "v \<in> children (prnt S0) p" unfolding children_def by simp
      hence "v \<in> set (block S0 p)" using block_props(4)[OF arb pV] by simp
      thus False using vnb by simp
    next
      case False
      hence "p \<in> set X" using pu XY by auto
      then obtain X1 X2 where "X = X1 @ p # X2" by (meson split_list)
      hence "follow (prnt S0) u = X1 @ p # (X2 @ v # Y)" using XY by simp
      hence "follow (prnt S0) p = p # (X2 @ v # Y)" by (rule follow_append_ps[OF ppt])
      hence "v \<in> set (follow (prnt S0) p)" by simp
      thus False using vnp by simp
    qed
  qed
qed

lemma join_facts:
  assumes jneq: "jn = join_of (prnt S0) i j"
  shows "jn \<in> set (follow (prnt S0) j) \<and> jn \<in> set (follow (prnt S0) p) \<and> p \<noteq> jn"
proof -
  have lst: "last (follow (prnt S0) i) = last (follow (prnt S0) j)"
    using last_follow_root[OF rinv0 iV] last_follow_root[OF rinv0 jV] by simp
  have jni: "jn \<in> set (follow (prnt S0) i)" using join_of_mem(1)[OF ppt lst] jneq by simp
  have jnj: "jn \<in> set (follow (prnt S0) j)" using join_of_mem(2)[OF ppt lst] jneq by simp
  have pi: "p \<in> set (follow (prnt S0) i)" using stem_chain[of k 0] pathk path0 by simp
  have notpjn: "p \<notin> set (follow (prnt S0) jn)"
  proof
    assume "p \<in> set (follow (prnt S0) jn)"
    hence "jn \<in> children (prnt S0) p" unfolding children_def by simp
    hence "children (prnt S0) jn \<subseteq> children (prnt S0) p" by (rule children_subset[OF ppt])
    moreover have "j \<in> children (prnt S0) jn" using jnj unfolding children_def by simp
    ultimately have "j \<in> children (prnt S0) p" by auto
    thus False using jnotp by simp
  qed
  have jnp: "jn \<in> set (follow (prnt S0) p)" using follow_comparable[OF ppt jni pi] notpjn by simp
  have pjn: "p \<noteq> jn"
  proof
    assume "p = jn"
    hence "p \<in> set (follow (prnt S0) j)" using jnj by simp
    hence "j \<in> children (prnt S0) p" unfolding children_def by simp
    thus False using jnotp by simp
  qed
  show ?thesis using jnj jnp pjn by simp
qed

lemma in_out_disjoint:
  assumes jneq: "jn = join_of (prnt S0) i j"
      and vin: "v \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow (prnt S0) j))"
      and vout: "v \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow (prnt S0) (the (prnt S0 p))))"
  shows False
proof -
  have jnj: "jn \<in> set (follow (prnt S0) j)" using join_facts[OF jneq] by simp
  have vj: "v \<in> set (follow (prnt S0) j)" using vin set_takeWhileD by fastforce
  have jnv: "jn \<in> set (follow (prnt S0) v)" and vnej: "v \<noteq> jn" using below_jn[OF vin jnj] by auto
  have "p \<in> dom (prnt S0)" using pV pne_r rooted_arborescense_invar_dom[OF rinv0] by simp
  then obtain vo where pvo: "prnt S0 p = Some vo" by auto
  have voeq: "the (prnt S0 p) = vo" using pvo by simp
  have fp: "follow (prnt S0) p = p # follow (prnt S0) vo" using pvo by (subst follow_ps_simps[OF ppt]) simp
  have vofv: "vo \<in> set (follow (prnt S0) vo)"
    using follow_hd_ps[OF ppt, of vo] follow_ne_ps[OF ppt, of vo] by (metis hd_in_set)
  have voap: "vo \<in> set (follow (prnt S0) p)" using fp vofv by simp
  have pai: "p \<in> set (follow (prnt S0) i)" using stem_chain[of k 0] pathk path0 by simp
  have voai: "vo \<in> set (follow (prnt S0) i)" using follow_trans[OF ppt pai voap] by auto
  have vvo: "v \<in> set (follow (prnt S0) vo)" using vout voeq set_takeWhileD by fastforce
  have vi: "v \<in> set (follow (prnt S0) i)" using follow_trans[OF ppt voai vvo] by auto
  have lst: "last (follow (prnt S0) i) = last (follow (prnt S0) j)"
    using last_follow_root[OF rinv0 iV] last_follow_root[OF rinv0 jV] by simp
  have "v \<in> set (follow (prnt S0) (join_of (prnt S0) i j))" using join_of_first[OF ppt lst vi vj] by auto
  hence "v \<in> set (follow (prnt S0) jn)" using jneq by simp
  hence "v = jn" using ancestor_antisym[OF ppt _ jnv] by simp
  thus False using vnej by simp
qed

lemma snum_card_match:
  assumes kpos: "0 < k" and jneq: "jn = join_of (prnt S0) i j" and vV: "v \<in> V"
  shows "final_snum jn v = card (children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v)"
proof -
  have jnj: "jn \<in> set (follow (prnt S0) j)" and jnp: "jn \<in> set (follow (prnt S0) p)" and pjn: "p \<noteq> jn"
    using join_facts[OF jneq] by auto
  have fPj: "follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) j = follow (prnt S0) j" by (rule follow_newprnt_j)
  have fPvo: "follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (the (prnt S0 p)) = follow (prnt S0) (the (prnt S0 p))"
    by (rule follow_newprnt_vout[OF kpos])
  have chP: "set (takeWhile (\<lambda>y. y \<noteq> i) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) p)) = s ` {1..<Suc k}"
    by (rule chainStem_set[OF kpos])
  show ?thesis
  proof (cases "v = i")
    case True
    have iIN: "v \<notin> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) j))"
      using True follow_newprnt_j stem_notin_follow_j[OF le0] path0 by (metis set_takeWhileD)
    have iOUT: "v \<notin> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (the (prnt S0 p))))"
      using True follow_newprnt_vout[OF kpos] stem_notin_follow_vout[OF kpos le0] path0 by (metis set_takeWhileD)
    have "final_snum jn v = snum S0 p" unfolding final_snum_def Let_def using iIN iOUT True by simp
    thus ?thesis using True card_children_newprnt_i[OF kpos] by simp
  next
    case notI: False
    show ?thesis
    proof (cases "v \<in> s ` {1..<Suc k}")
      case True
      then obtain m where mm: "m \<in> {1..<Suc k}" and um: "v = s m" by auto
      have m1: "1 \<le> m" and mk: "m \<le> k" using mm by auto
      have vIN: "v \<notin> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) j))"
        using um follow_newprnt_j stem_notin_follow_j[OF mk] by (metis set_takeWhileD)
      have vOUT: "v \<notin> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (the (prnt S0 p))))"
        using um follow_newprnt_vout[OF kpos] stem_notin_follow_vout[OF kpos mk] by (metis set_takeWhileD)
      have vchP: "v \<in> set (takeWhile (\<lambda>y. y \<noteq> i) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) p))"
        using chP True by simp
      have theP: "the (((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v) = s (m - 1)"
        using um Wseq_eval[of "Suc k" m] mk newprnt_eq m1 by (simp add: s_pred_def)
      have "final_snum jn v = snum S0 p - snum S0 (s (m - 1))"
        unfolding final_snum_def Let_def using vIN vOUT vchP theP notI by simp
      thus ?thesis using um card_children_newprnt_stem[OF kpos jneq jnp pjn m1 mk] by simp
    next
      case notStem: False
      have vchPF: "v \<notin> set (takeWhile (\<lambda>y. y \<noteq> i) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) p))"
        using chP notStem by simp
      show ?thesis
      proof (cases "v \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) j))")
        case True
        have vinj: "v \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow (prnt S0) j))" using True fPj by simp
        have vOUT: "v \<notin> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (the (prnt S0 p))))"
          using in_out_disjoint[OF jneq vinj] fPvo by auto
        have "final_snum jn v = snum S0 v + snum S0 p"
          unfolding final_snum_def Let_def using True vOUT notI vchPF by simp
        thus ?thesis using card_children_newprnt_INchain[OF kpos jneq vinj jnj] by simp
      next
        case notIN: False
        show ?thesis
        proof (cases "v \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (the (prnt S0 p))))")
          case True
          have voutj: "v \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow (prnt S0) (the (prnt S0 p))))" using True fPvo by simp
          have "final_snum jn v = snum S0 v - snum S0 p"
            unfolding final_snum_def Let_def using True notIN notI vchPF by simp
          thus ?thesis using card_children_newprnt_OUTchain[OF kpos jneq jnp pjn voutj] by simp
        next
          case notOUT: False
          have fin: "final_snum jn v = snum S0 v"
            unfolding final_snum_def Let_def using notIN notOUT notI vchPF by simp
          have vnji: "v \<notin> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow (prnt S0) j))" using notIN fPj by simp
          have vnjo: "v \<notin> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow (prnt S0) (the (prnt S0 p))))" using notOUT fPvo by simp
          show ?thesis
          proof (cases "v \<in> set (block S0 p)")
            case True
            have "v \<notin> s ` {..k}"
            proof
              assume "v \<in> s ` {..k}"
              then obtain m where mk: "m \<le> k" and um: "v = s m" by auto
              have "m = 0" using notStem um mk by (cases "m = 0") auto
              thus False using um notI path0 by simp
            qed
            hence "card (children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v) = snum S0 v"
              by (rule card_children_newprnt_nonstem_block[OF kpos True])
            thus ?thesis using fin by simp
          next
            case notBlk: False
            show ?thesis
            proof (cases "v \<in> set (follow (prnt S0) j)")
              case True
              have "set (block S0 p) \<subseteq> children (prnt S0) v"
                by (rule jpath_above_block_sub[OF True vnji jnj jnp])
              hence "card (children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v) = snum S0 v"
                by (rule card_children_newprnt_jpath_above[OF kpos True _ vV])
              thus ?thesis using fin by simp
            next
              case False
              have "set (block S0 p) \<inter> children (prnt S0) v = {}"
                by (rule disjoint_block_int[OF False vnjo notBlk jnj jnp pjn])
              hence "card (children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v) = snum S0 v"
                by (rule card_children_newprnt_disjoint[OF kpos notBlk False _ vV])
              thus ?thesis using fin by simp
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma clauseI:
  assumes kpos: "0 < k" and jneq: "jn = join_of (prnt S0) i j"
  shows "\<forall>v\<in>V. snum (update_tree S0 i j p jn) v = card (children (prnt (update_tree S0 i j p jn)) v)"
proof
  fix v assume vV: "v \<in> V"
  show "snum (update_tree S0 i j p jn) v = card (children (prnt (update_tree S0 i j p jn)) v)" using update_tree_snum[OF kpos] snum_card_match[OF kpos jneq vV] update_tree_prnt[OF kpos] by simp
qed

text \<open>Untouched-edge fact (the backbone of the {\isasymsection}15.2 out-edge case table): at any key outside the
      override set @{term "lsx ` {..k} \<union> bef ` {..<k} \<union> {j, the (rvth S0 p)}"} the final thread
      agrees with @{term "thrd S0"} --- the @{const thrd_inv} folds and the two splices touch only
      those keys.\<close>
lemma final_thrd_fresh:
  assumes ql: "q \<notin> lsx ` {..k}" and qb: "q \<notin> bef ` set [0..<k]"
      and qj: "q \<noteq> j" and qr: "q \<noteq> the (rvth S0 p)"
  shows "final_thrd q = thrd S0 q"
proof -
  have qlk: "q \<noteq> lsx k" using ql by auto
  have ql': "q \<notin> lsx ` set [0..<k]" using ql by auto
  have tik: "thrd_inv k q = thrd S0 q" using thrd_inv_eval_fresh[OF ql' qb qj] by auto
  show ?thesis
    using qlk qr tik by (simp add: final_thrd_def Let_def split: option.split)
qed

end

subsection \<open>OUT-edge ({\isasymsection}15.2): the final thread realises the new preorder list\<close>

text \<open>The out-edge analysis re-opens @{locale stem_setup} (now with @{thm last_follow_root} in scope)
      to characterise final\_thrd as the successor map of an explicit list edit of the old
      thread @{term "follow (thrd S0) r"}.\<close>
context stem_setup begin

text \<open>The detached subtree of @{term p} sits as a contiguous block inside the whole thread: the root
      block @{term "block S0 r"} is the entire thread, and @{thm block_self_similar} excises
      @{term "block S0 p"} from it.\<close>
lemma oldlist_block_p: "\<exists>A B. follow (thrd S0) r = A @ block S0 p @ B"
proof -
  have rinv: "rooted_arborescense_invar r V (prnt S0)" using arb unfolding arb_invar_def by simp
  have rV: "r \<in> V" using rinv by (rule rooted_arborescense_invar_r_in_V)
  have psp: "parent_spec (prnt S0)" by (rule rooted_arborescense_invar_parent_spec[OF rinv])
  have lastr: "last (follow (prnt S0) p) = r" by (rule last_follow_root[OF rinv pV])
  have ne: "follow (prnt S0) p \<noteq> []" using follow_ne_ps[OF psp] by simp
  have "r \<in> set (follow (prnt S0) p)" using lastr ne by (metis last_in_set)
  hence pchild: "p \<in> children (prnt S0) r" unfolding children_def by simp
  have domt: "dom (thrd S0) = V - {lsuc S0 r}" using arb unfolding arb_invar_def by simp
  hence "thrd S0 (lsuc S0 r) = None" by auto
  hence blockr: "follow (thrd S0) r = block S0 r" using block_props(1)[OF arb rV] by simp
  show ?thesis using block_self_similar[OF arb rV pV pchild pne_r] blockr by simp
qed

text \<open>@{term j} lies outside the detached subtree (no-cycle @{thm jnotp}): the insertion site is
      disjoint from the block being moved.\<close>
lemma j_notin_block_p: "j \<notin> set (block S0 p)"
  using block_props(4)[OF arb pV] jnotp by simp

text \<open>Consecutive nodes of a root-path are thread-linked: if @{term x} is immediately followed by
      @{term y} in @{term "follow T v"} then @{term "T x = Some y"}.\<close>
lemma thread_link:
  assumes ps: "parent_spec T" and eq: "follow T v = G @ x # y # H" shows "T x = Some y"
proof -
  have fx: "follow T x = x # y # H" using follow_append_ps[OF ps] eq by (metis append.assoc append_Cons append_Nil)
  show ?thesis using fx follow_ps_simps[OF ps, of x] follow_hd_ps[OF ps, of "the (T x)"]
    by (cases "T x") auto
qed

text \<open>The thread neighbours of the detached block: the node just before @{term "block S0 p"} is its
      thread-predecessor @{term "the (rvth S0 p)"} (@{text old_rev}), and the node just after is the
      thread-successor of the block's last node @{term "lsuc S0 p"} (@{text "out_S0 p"}).\<close>
lemma block_p_split:
  obtains A B where "follow (thrd S0) r = A @ block S0 p @ B"
    and "A \<noteq> [] \<Longrightarrow> the (rvth S0 p) = last A"
    and "B \<noteq> [] \<Longrightarrow> thrd S0 (lsuc S0 p) = Some (hd B)"
proof -
  have pst: "parent_spec (thrd S0)" using arb unfolding arb_invar_def by simp
  have G: "\<forall>v v'. thrd S0 v = Some v' \<longleftrightarrow> rvth S0 v' = Some v" using arb unfolding arb_invar_def by simp
  obtain A B where AB: "follow (thrd S0) r = A @ block S0 p @ B" using oldlist_block_p by auto
  have hdp: "hd (block S0 p) = p" by (rule block_props(5)[OF arb pV])
  have lastp: "last (block S0 p) = lsuc S0 p" by (rule block_props(3)[OF arb pV])
  have bne: "block S0 p \<noteq> []" by (rule block_props(2)[OF arb pV])
  have predA: "A \<noteq> [] \<Longrightarrow> the (rvth S0 p) = last A"
  proof -
    assume Ane: "A \<noteq> []"
    obtain A' a where Asplit: "A = A' @ [a]" using Ane by (metis append_butlast_last_id)
    have bp: "block S0 p = p # tl (block S0 p)" using bne hdp by (metis hd_Cons_tl)
    have "follow (thrd S0) r = A' @ a # p # (tl (block S0 p) @ B)"
      using AB Asplit bp by simp
    hence "thrd S0 a = Some p" by (rule thread_link[OF pst])
    hence "rvth S0 p = Some a" using G by auto
    thus "the (rvth S0 p) = last A" using Asplit by simp
  qed
  have succB: "B \<noteq> [] \<Longrightarrow> thrd S0 (lsuc S0 p) = Some (hd B)"
  proof -
    assume Bne: "B \<noteq> []"
    obtain b B' where Bsplit: "B = b # B'" using Bne by (cases B) auto
    have bp: "block S0 p = butlast (block S0 p) @ [lsuc S0 p]" using bne lastp by (metis append_butlast_last_id)
    have "follow (thrd S0) r = (A @ butlast (block S0 p)) @ (lsuc S0 p) # b # B'"
      using AB Bsplit bp by simp
    hence "thrd S0 (lsuc S0 p) = Some b" by (rule thread_link[OF pst])
    thus "thrd S0 (lsuc S0 p) = Some (hd B)" using Bsplit by simp
  qed
  show ?thesis using that[OF AB predA succB] by auto
qed

subsubsection \<open>The new preorder block \<open>newblock\<close> ({\isasymsection}15.1)\<close>

text \<open>Along the stem the blocks nest ({\isasymsection}1): @{term "block S0 (s (Suc m))"} contains @{term "block S0
      (s m)"} contiguously, framed by the "side" children-blocks @{text P}/@{text Q}.\<close>
lemma block_stem_decomp_ex:
  assumes "m < k"
  shows "\<exists>P Q. block S0 (s (Suc m)) = s (Suc m) # P @ block S0 (s m) @ Q"
proof -
  have smV: "s m \<in> V" using sV assms by simp
  have sSmV: "s (Suc m) \<in> V" using sV assms by simp
  have step: "prnt S0 (s m) = Some (s (Suc m))" using pathS[OF assms] by auto
  have "follow (prnt S0) (s m) = s m # follow (prnt S0) (s (Suc m))"
    using follow_ps_simps[OF ppt, of "s m"] step by simp
  hence "s (Suc m) \<in> set (follow (prnt S0) (s m))"
    using follow_hd_ps[OF ppt, of "s (Suc m)"] follow_ne_ps[OF ppt, of "s (Suc m)"]
    by (metis hd_in_set list.set_intros(2))
  hence child: "s m \<in> children (prnt S0) (s (Suc m))" unfolding children_def by simp
  have ne: "s m \<noteq> s (Suc m)" using inj assms by (auto simp: inj_on_eq_iff)
  show ?thesis using block_nest[OF arb sSmV smV child ne] by auto
qed

text \<open>The framing side-blocks @{term "defP m"} (before the nested stem block) and @{term "defQ m"}
      (after it), pinned by Hilbert choice to the nesting decomposition.\<close>
definition defP :: "nat \<Rightarrow> 'a list" where "defP m = (SOME P. \<exists>Q. block S0 (s (Suc m)) = s (Suc m) # P @ block S0 (s m) @ Q)"
definition defQ :: "nat \<Rightarrow> 'a list" where "defQ m = (SOME Q. block S0 (s (Suc m)) = s (Suc m) # defP m @ block S0 (s m) @ Q)"

lemma block_decomp:
  assumes "m < k"
  shows "block S0 (s (Suc m)) = s (Suc m) # defP m @ block S0 (s m) @ defQ m"
proof -
  have exP: "\<exists>P. \<exists>Q. block S0 (s (Suc m)) = s (Suc m) # P @ block S0 (s m) @ Q"
    using block_stem_decomp_ex[OF assms] by auto
  have "\<exists>Q. block S0 (s (Suc m)) = s (Suc m) # defP m @ block S0 (s m) @ Q"
    unfolding defP_def by (rule someI_ex[OF exP])
  thus ?thesis unfolding defQ_def by (rule someI_ex)
qed

text \<open>The contribution of a stem node ({\isasymsection}1): @{term "contrib 0 = block S0 i"} (the bottom subtree, kept
      whole); for @{term "m \<ge> 1"} the node @{term "s m"} followed by its side-blocks @{term "defP
      (m-1) @ defQ (m-1)"} (its nested stem child @{term "s (m-1)"} excised).   newblock is
      the new preorder of the detached set: the contributions concatenated bottom-up.\<close>
definition contrib :: "nat \<Rightarrow> 'a list" where "contrib m = (if m = 0 then block S0 i else s m # defP (m-1) @ defQ (m-1))"
definition newblock :: "'a list" where "newblock = concat (map contrib [0..<Suc k])"

text \<open>Unrolling: the first @{term "Suc m"} contributions cover exactly @{term "block S0 (s m)"} (as a
      set / by length), so @{const newblock} is a reordering of @{term "block S0 p"}.\<close>
lemma contrib_set_unroll:
  assumes "m \<le> k"
  shows "set (concat (map contrib [0..<Suc m])) = set (block S0 (s m))"
  using assms
proof (induction m)
  case 0
  show ?case by (simp add: contrib_def path0)
next
  case (Suc m)
  have mk: "m < k" using Suc.prems by simp
  have IH: "set (concat (map contrib [0..<Suc m])) = set (block S0 (s m))" using Suc.IH mk by simp
  have dec: "block S0 (s (Suc m)) = s (Suc m) # defP m @ block S0 (s m) @ defQ m"
    by (rule block_decomp[OF mk])
  have c: "contrib (Suc m) = s (Suc m) # defP m @ defQ m" by (simp add: contrib_def)
  have split: "concat (map contrib [0..<Suc (Suc m)]) = concat (map contrib [0..<Suc m]) @ contrib (Suc m)"
    by (simp add: upt_Suc_append)
  show ?case using split IH c dec by auto
qed

lemma newblock_set: "set newblock = set (block S0 p)"
  using contrib_set_unroll[of k] by (simp add: newblock_def pathk)

lemma contrib_len_unroll:
  assumes "m \<le> k"
  shows "length (concat (map contrib [0..<Suc m])) = length (block S0 (s m))"
  using assms
proof (induction m)
  case 0
  show ?case by (simp add: contrib_def path0)
next
  case (Suc m)
  have mk: "m < k" using Suc.prems by simp
  have IH: "length (concat (map contrib [0..<Suc m])) = length (block S0 (s m))" using Suc.IH mk by simp
  have dec: "block S0 (s (Suc m)) = s (Suc m) # defP m @ block S0 (s m) @ defQ m"
    by (rule block_decomp[OF mk])
  have c: "contrib (Suc m) = s (Suc m) # defP m @ defQ m" by (simp add: contrib_def)
  have split: "concat (map contrib [0..<Suc (Suc m)]) = concat (map contrib [0..<Suc m]) @ contrib (Suc m)"
    by (simp add: upt_Suc_append)
  show ?case using split IH c dec by simp
qed

lemma newblock_len: "length newblock = length (block S0 p)"
  using contrib_len_unroll[of k] by (simp add: newblock_def pathk)

lemma block_p_distinct: "distinct (block S0 p)"
proof -
  have pst: "parent_spec (thrd S0)" using arb unfolding arb_invar_def by simp
  obtain A B where AB: "follow (thrd S0) r = A @ block S0 p @ B" using oldlist_block_p by auto
  have "distinct (follow (thrd S0) r)" by (rule follow_distinct_ps[OF pst])
  thus ?thesis using AB by simp
qed

text \<open>@{const newblock} is distinct: same length as @{term "block S0 p"} and same (distinct) set.\<close>
lemma newblock_distinct: "distinct newblock"
  using newblock_set block_p_distinct newblock_len by (simp add: distinct_card card_distinct)

subsubsection \<open>The target list \<open>newlist\<close> as an explicit list edit ({\isasymsection}15.2)\<close>

text \<open>Pin the detached block as a concrete contiguous slice of the old thread: @{term alpha} is the
      prefix before @{term p}, @{term beta} the suffix after @{term "block S0 p"}.\<close>
definition alpha :: "'a list" where "alpha = takeWhile (\<lambda>x. x \<noteq> p) (follow (thrd S0) r)"
definition beta :: "'a list" where "beta = drop (length (block S0 p)) (dropWhile (\<lambda>x. x \<noteq> p) (follow (thrd S0) r))"

lemma oldlist_split_eq: "follow (thrd S0) r = alpha @ block S0 p @ beta"
proof -
  have pst: "parent_spec (thrd S0)" using arb unfolding arb_invar_def by simp
  obtain A B where AB: "follow (thrd S0) r = A @ block S0 p @ B" using oldlist_block_p by auto
  have dist: "distinct (follow (thrd S0) r)" by (rule follow_distinct_ps[OF pst])
  have hdp: "hd (block S0 p) = p" by (rule block_props(5)[OF arb pV])
  have bne: "block S0 p \<noteq> []" by (rule block_props(2)[OF arb pV])
  obtain rest where bp: "block S0 p = p # rest" using bne hdp by (metis hd_Cons_tl)
  have distA: "distinct (A @ p # rest @ B)" using dist AB bp by simp
  have allA: "\<forall>x\<in>set A. x \<noteq> p" using distA by auto
  have tw: "takeWhile (\<lambda>x. x \<noteq> p) (follow (thrd S0) r) = A"
    using AB bp allA by (simp add: takeWhile_append2)
  have dw: "dropWhile (\<lambda>x. x \<noteq> p) (follow (thrd S0) r) = block S0 p @ B"
    using AB bp allA by (simp add: dropWhile_append2)
  have "alpha = A" unfolding alpha_def using tw by auto
  moreover have "beta = B" unfolding beta_def using dw by simp
  ultimately show ?thesis using AB by simp
qed

text \<open>@{term holed} is the old thread with the detached block excised;  newlist re-inserts
      @{const newblock} immediately after @{term j} (its new parent).\<close>
definition holed :: "'a list" where "holed = alpha @ beta"
definition newlist :: "'a list" where "newlist = takeWhile (\<lambda>x. x \<noteq> j) holed @ j # newblock @ tl (dropWhile (\<lambda>x. x \<noteq> j) holed)"

lemma oldlist_distinct: "distinct (follow (thrd S0) r)"
  using arb[unfolded arb_invar_def] by (auto intro: follow_distinct_ps)

lemma oldlist_set_V: "set (follow (thrd S0) r) = V"
  using arb unfolding arb_invar_def by simp

lemma holed_distinct: "distinct holed"
  using oldlist_distinct oldlist_split_eq by (auto simp: holed_def)

lemma holed_set: "set holed = V - set (block S0 p)"
  using oldlist_distinct oldlist_split_eq oldlist_set_V by (auto simp: holed_def)

lemma j_in_holed: "j \<in> set holed"
  using holed_set jV j_notin_block_p by simp

text \<open>The insertion seam: @{term holed} splits around its (unique) occurrence of @{term j}.\<close>
lemma holed_split: "holed = takeWhile (\<lambda>x. x \<noteq> j) holed @ j # tl (dropWhile (\<lambda>x. x \<noteq> j) holed)"
proof -
  have dwne: "dropWhile (\<lambda>x. x \<noteq> j) holed \<noteq> []"
  proof
    assume "dropWhile (\<lambda>x. x \<noteq> j) holed = []"
    hence "\<forall>x\<in>set holed. x \<noteq> j" by (simp add: dropWhile_eq_Nil_conv)
    thus False using j_in_holed by auto
  qed
  have hdj: "hd (dropWhile (\<lambda>x. x \<noteq> j) holed) = j" using hd_dropWhile[OF dwne] by simp
  have eq2: "dropWhile (\<lambda>x. x \<noteq> j) holed = j # tl (dropWhile (\<lambda>x. x \<noteq> j) holed)"
    using dwne hdj by (cases "dropWhile (\<lambda>x. x \<noteq> j) holed") auto
  show ?thesis by (subst eq2[symmetric]) simp
qed

lemma block_p_subset_V: "set (block S0 p) \<subseteq> V"
  using oldlist_split_eq oldlist_set_V by auto

lemma set_holed_split: "set holed = set (takeWhile (\<lambda>x. x \<noteq> j) holed) \<union> {j} \<union> set (tl (dropWhile (\<lambda>x. x \<noteq> j) holed))"
  by (subst holed_split) auto

text \<open>@{const newlist} spans exactly @{term V} (clause D) and is distinct (the engine input for B/E).\<close>
lemma set_newlist: "set newlist = V"
proof -
  have nl: "set newlist = (set (takeWhile (\<lambda>x. x \<noteq> j) holed) \<union> {j} \<union> set (tl (dropWhile (\<lambda>x. x \<noteq> j) holed))) \<union> set newblock"
    unfolding newlist_def by auto
  show ?thesis using nl set_holed_split holed_set newblock_set block_p_subset_V by auto
qed

lemma distinct_newlist: "distinct newlist"
proof -
  have dh: "distinct (takeWhile (\<lambda>x. x \<noteq> j) holed @ j # tl (dropWhile (\<lambda>x. x \<noteq> j) holed))"
    using holed_distinct holed_split by simp
  have disj: "set newblock \<inter> set holed = {}"
    using newblock_set holed_set block_p_subset_V by auto
  have subTW: "set (takeWhile (\<lambda>x. x \<noteq> j) holed) \<subseteq> set holed"
    using set_holed_split by auto
  have subTL: "set (tl (dropWhile (\<lambda>x. x \<noteq> j) holed)) \<subseteq> set holed"
    using set_holed_split by auto
  have jh: "j \<in> set holed" by (rule j_in_holed)
  have nbTW: "set newblock \<inter> set (takeWhile (\<lambda>x. x \<noteq> j) holed) = {}" using disj subTW by auto
  have nbTL: "set newblock \<inter> set (tl (dropWhile (\<lambda>x. x \<noteq> j) holed)) = {}" using disj subTL by auto
  have jnb: "j \<notin> set newblock" using disj jh by auto
  show ?thesis unfolding newlist_def
    using dh newblock_distinct nbTW nbTL jnb by (auto simp: distinct_append)
qed

text \<open>@{const newlist} starts at the root @{term r}: the old thread does, and the surgery only edits
      the interior.\<close>
lemma hd_holed: "hd holed = r"
proof -
  have pst: "parent_spec (thrd S0)" using arb unfolding arb_invar_def by simp
  have hr: "hd (follow (thrd S0) r) = r" by (rule follow_hd_ps[OF pst])
  have ne: "follow (thrd S0) r \<noteq> []" by (rule follow_ne_ps[OF pst])
  obtain z zs where z: "follow (thrd S0) r = z # zs" using ne by (cases "follow (thrd S0) r") auto
  have zr: "z = r" using hr z by simp
  have "alpha = takeWhile (\<lambda>x. x \<noteq> p) (z # zs)" unfolding alpha_def using z by simp
  hence "alpha = r # takeWhile (\<lambda>x. x \<noteq> p) zs" using zr pne_r by simp
  thus ?thesis unfolding holed_def by simp
qed

lemma hd_newlist: "hd newlist = r"
proof -
  have jh: "j \<in> set holed" by (rule j_in_holed)
  obtain z zs where hz: "holed = z # zs" using jh by (cases holed) auto
  have zr: "z = r" using hd_holed hz by simp
  show ?thesis
  proof (cases "z = j")
    case True
    hence "takeWhile (\<lambda>x. x \<noteq> j) holed = []" using hz by simp
    thus ?thesis unfolding newlist_def using zr True by simp
  next
    case False
    hence "takeWhile (\<lambda>x. x \<noteq> j) holed = z # takeWhile (\<lambda>x. x \<noteq> j) zs" using hz by simp
    thus ?thesis unfolding newlist_def using zr by simp
  qed
qed

lemma newlist_ne: "newlist \<noteq> []"
  unfolding newlist_def by simp

subsubsection \<open>The override keys lie inside the detached block (D3 disjointness)\<close>

text \<open>Along the stem the blocks nest monotonically; in particular every @{term "block S0 (s a)"}
      (@{term "a \<le> k"}) is contained in @{term "block S0 p"}.\<close>
lemma block_step_mono:
  assumes "m < k" shows "set (block S0 (s m)) \<subseteq> set (block S0 (s (Suc m)))"
  using block_decomp[OF assms] by auto

lemma block_mono:
  assumes "a \<le> b" "b \<le> k" shows "set (block S0 (s a)) \<subseteq> set (block S0 (s b))"
  using assms
proof (induction b)
  case 0 thus ?case by simp
next
  case (Suc b)
  show ?case
  proof (cases "a = Suc b")
    case True thus ?thesis by simp
  next
    case False
    hence ab: "a \<le> b" using Suc.prems(1) by simp
    have bk: "b < k" using Suc.prems(2) by simp
    show ?thesis using Suc.IH ab bk block_step_mono[OF bk] by simp
  qed
qed

lemma block_in_p:
  assumes "a \<le> k" shows "set (block S0 (s a)) \<subseteq> set (block S0 p)"
  using block_mono[OF assms] pathk by simp

text \<open>The last successor of any stem node lies in @{term "block S0 p"} (it is the last element of that
      stem node's block, which nests into @{term "block S0 p"}).\<close>
lemma lsuc_in_block_p:
  assumes "t \<le> k" and kpos: "0 < k" shows "lsuc S0 (s t) \<in> set (block S0 p)"
proof -
  have stV: "s t \<in> V" using sV[OF assms] by auto
  have "lsuc S0 (s t) = last (block S0 (s t))" using block_props(3)[OF arb stV] by simp
  moreover have "last (block S0 (s t)) \<in> set (block S0 (s t))"
    using block_props(2)[OF arb stV] by simp
  ultimately show ?thesis using block_in_p[OF assms(1)] by auto
qed

text \<open>The thread-predecessor @{term "bef m"} of a stem node also lies in @{term "block S0 p"}: it is
      the node just before @{term "s m"} inside the parent block @{term "block S0 (s (Suc m))"}.\<close>
lemma bef_in_block_p:
  assumes mk: "m < k" shows "bef m \<in> set (block S0 p)"
proof -
  have pst: "parent_spec (thrd S0)" using arb unfolding arb_invar_def by simp
  have smV: "s m \<in> V" using sV[of m] mk by simp
  have sSmV: "s (Suc m) \<in> V" using sV[of "Suc m"] mk by simp
  have G: "\<forall>v v'. thrd S0 v = Some v' \<longleftrightarrow> rvth S0 v' = Some v" using arb unfolding arb_invar_def by simp
  have dec: "block S0 (s (Suc m)) = (s (Suc m) # defP m) @ block S0 (s m) @ defQ m"
    using block_decomp[OF mk] by simp
  obtain Rv where bf: "follow (thrd S0) (s (Suc m)) = block S0 (s (Suc m)) @ Rv"
    using block_props(1)[OF arb sSmV] by metis
  have bmne: "block S0 (s m) \<noteq> []" using block_props(2)[OF arb smV] by simp
  have bmhd: "hd (block S0 (s m)) = s m" using block_props(5)[OF arb smV] by simp
  obtain rest where bm: "block S0 (s m) = s m # rest" using bmne bmhd by (metis hd_Cons_tl)
  define pre where "pre = s (Suc m) # defP m"
  have preP: "pre \<noteq> []" unfolding pre_def by simp
  obtain G' x where pre2: "pre = G' @ [x]" using preP by (metis append_butlast_last_id)
  have "follow (thrd S0) (s (Suc m)) = G' @ x # s m # (rest @ defQ m @ Rv)"
    using bf dec bm pre_def pre2 by simp
  hence thx: "thrd S0 x = Some (s m)" by (rule thread_link[OF pst])
  have thbef: "thrd S0 (bef m) = Some (s m)" by (rule bef_pred(1)[OF mk])
  have "rvth S0 (s m) = Some x" using thx G by auto
  moreover have "rvth S0 (s m) = Some (bef m)" using thbef G by auto
  ultimately have "x = bef m" by simp
  hence "bef m \<in> set pre" using pre2 by auto
  hence "bef m \<in> set (block S0 (s (Suc m)))" using dec pre_def by auto
  thus ?thesis using block_in_p[of "Suc m"] mk by auto
qed

text \<open>Hence every @{const lsx} key lies in @{term "block S0 p"} (it is either a @{const lsuc} or a
      @{const bef}, by the closed form).\<close>
lemma lsx_in_block_p:
  assumes tk: "t \<le> k" and kpos: "0 < k" shows "lsx t \<in> set (block S0 p)"
proof (cases "t = 0")
  case True
  have "lsx t = lsuc S0 (s 0)" using True by (simp add: lsx_def path0)
  thus ?thesis using lsuc_in_block_p[of 0] kpos by simp
next
  case False
  then obtain t' where t': "t = Suc t'" using not0_implies_Suc by auto
  have t'k: "t' < k" using tk t' by simp
  show ?thesis
  proof (cases "lsuc S0 (s t) = lsuc S0 (s (t-1))")
    case True
    have "lsx t = the (rvth S0 (s (t-1)))" using False True by (simp add: lsx_def)
    also have "\<dots> = bef (t-1)" by (simp add: bef_def)
    finally show ?thesis using bef_in_block_p[of "t-1"] t' t'k by simp
  next
    case False
    have "lsx t = lsuc S0 (s t)" using \<open>t \<noteq> 0\<close> False by (simp add: lsx_def)
    thus ?thesis using lsuc_in_block_p[OF tk kpos] by simp
  qed
qed

text \<open>@{term "lsx k"}, the last-successor written onto the whole reversed stem, is a vertex:
      it lies in @{term "block S0 p"}, hence in @{term V}.\<close>
lemma lsx_k_in_V:
  assumes kpos: "0 < k" shows "lsx k \<in> V"
proof -
  have pV: "p \<in> V" using sV[of k] kpos pathk by simp
  have lkblk: "lsx k \<in> set (block S0 p)" using lsx_in_block_p[of k] kpos by simp
  have "set (block S0 p) = children (prnt S0) p" using block_props(4)[OF arb pV] by simp
  hence lkch: "p \<in> set (follow (prnt S0) (lsx k))" using lkblk unfolding children_def by simp
  have rinv: "rooted_arborescense_invar r V (prnt S0)" using arb unfolding arb_invar_def by simp
  have domeq: "dom (prnt S0) = V - {r}" by (rule rooted_arborescense_invar_dom[OF rinv])
  show ?thesis
  proof (rule ccontr)
    assume "lsx k \<notin> V"
    hence "prnt S0 (lsx k) = None" using domeq by auto
    hence "follow (prnt S0) (lsx k) = [lsx k]" by (subst follow_ps_simps[OF ppt]) simp
    hence "p = lsx k" using lkch by simp
    thus False using pV \<open>lsx k \<notin> V\<close> by simp
  qed
qed

text \<open>Clause H for the reversal branch: every @{const lsuc} value stays in @{term V}.  The five
      decoration loops overwrite @{const lsuc} only with values already in @{term V} (@{term "lsx k"},
      @{term "the (rvth S0 p)"}, or an existing in-@{term V} entry), and the base @{term "lsuc S0"}
      is in @{term V}, so membership is preserved along the whole pipeline.\<close>
lemma update_tree_lsuc_in_V:
  assumes kpos: "0 < k"
  shows "\<forall>v\<in>V. lsuc (update_tree S0 i j p jn) v \<in> V"
proof -
  have inep: "i \<noteq> p" using inep_aux[OF kpos] by auto
  have psN: "parent_spec ((prnt S0 ++ REV k)(p \<mapsto> s_pred k))"
    using clauseA rooted_arborescense_invar_parent_spec by auto
  have pV: "p \<in> V" using sV[of k] kpos pathk by simp
  have HS0: "\<forall>v\<in>V. lsuc S0 v \<in> V" using arb unfolding arb_invar_def by simp
  have lkV: "lsx k \<in> V" using lsx_k_in_V[OF kpos] by auto
  have orV: "the (rvth S0 p) \<in> V"
  proof -
    have pdom: "p \<in> dom (rvth S0)" using arb pV pne_r unfolding arb_invar_def by auto
    then obtain w where w: "rvth S0 p = Some w" by auto
    hence "thrd S0 w = Some p" using arb unfolding arb_invar_def by auto
    hence "w \<in> dom (thrd S0)" by auto
    moreover have "dom (thrd S0) = V - {lsuc S0 r}" using arb unfolding arb_invar_def by simp
    ultimately have "w \<in> V" by auto
    thus ?thesis using w by simp
  qed
  define Sp where "Sp = Sfin\<lparr>prnt := (prnt Sfin)(p \<mapsto> s_pred k)\<rparr>"
  define Sq where "Sq = (case (if the (rvth S0 p) = j then thrd S0 (lsuc S0 p) else thrd S0 j) of
                           None \<Rightarrow> Sp\<lparr>thrd := (thrd Sp)(lsx k := None)\<rparr>
                         | Some a \<Rightarrow> Sp\<lparr>thrd := (thrd Sp)(lsx k \<mapsto> a), rvth := (rvth Sp)(a \<mapsto> lsx k)\<rparr>)"
  define Sr where "Sr = Sq\<lparr>lsuc := (lsuc Sq)(p := lsx k)\<rparr>"
  define Ss where "Ss = (if the (rvth S0 p) \<noteq> j
                         then (case aftn k of
                                 None \<Rightarrow> Sr\<lparr>thrd := (thrd Sr)(the (rvth S0 p) := None)\<rparr>
                               | Some a \<Rightarrow> Sr\<lparr>thrd := (thrd Sr)(the (rvth S0 p) \<mapsto> a), rvth := (rvth Sr)(a \<mapsto> the (rvth S0 p))\<rparr>)
                         else Sr)"
  define St where "St = dirty_pass Ss (drt k)"
  define Su where "Su = stem_num_loop St (snum S0) p i 0 (lsuc St p)"
  define Sv where "Sv = Su\<lparr>snum := (snum Su)(i := snum S0 p)\<rparr>"
  define S2 where "S2 = last_vin_loop Sv j j (lsuc Sv p)"
  define S3 where "S3 = (if jn \<noteq> the (rvth S0 p) \<and> j \<noteq> the (rvth S0 p)
                         then last_vout_loop S2 (the (prnt S0 p)) (if lsuc Sv jn = j then Some jn else None) (lsuc S0 p) (the (rvth S0 p))
                         else if lsuc Sv p \<noteq> lsuc S0 p
                              then last_vout_loop S2 (the (prnt S0 p)) (if lsuc Sv jn = j then Some jn else None) (lsuc S0 p) (lsuc Sv p)
                              else S2)"
  define S4 where "S4 = succ_vin_loop S3 j jn (snum S0 p)"
  define S5 where "S5 = succ_vout_loop S4 (the (prnt S0 p)) jn (snum S0 p)"
  have psSv: "parent_spec (prnt Sv)" using stem_num_loop_fields[OF psN, THEN mp] psN by (simp add: Sv_def Su_def St_def Ss_def Sr_def Sq_def Sp_def Sfin_def split: option.split)
  define Sa where "Sa = fused_vin_loop Sv j j jn (lsuc Sv p) (snum S0 p) True True"
  define Sb where "Sb = (if jn \<noteq> the (rvth S0 p) \<and> j \<noteq> the (rvth S0 p) then fused_vout_loop Sa (the (prnt S0 p)) (if lsuc Sv jn = j then Some jn else None) (lsuc S0 p) (the (rvth S0 p)) jn (snum S0 p) True True else if lsuc Sv p \<noteq> lsuc S0 p then fused_vout_loop Sa (the (prnt S0 p)) (if lsuc Sv jn = j then Some jn else None) (lsuc S0 p) (lsuc Sv p) jn (snum S0 p) True True else fused_vout_loop Sa (the (prnt S0 p)) (if lsuc Sv jn = j then Some jn else None) (lsuc S0 p) (lsuc S0 p) jn (snum S0 p) False True)"
  have UTb: "update_tree S0 i j p jn = Sb" by (simp only: update_tree_def Let_def inep if_False if_True stem_loop_init prod.case Sb_def Sa_def Sv_def Su_def St_def Ss_def Sr_def Sq_def Sp_def)
  have SbS5: "Sb = S5" using update_tree_tail_eq[OF psSv] by (simp only: Sb_def Sa_def S5_def S4_def S3_def S2_def)
  have UT: "update_tree S0 i j p jn = S5" using UTb SbS5 by simp
  have pSp: "prnt Sp = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)" by (simp add: Sp_def Sfin_def)
  have pSq: "prnt Sq = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)" using pSp by (simp add: Sq_def split: option.split)
  have pSr: "prnt Sr = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)" using pSq by (simp add: Sr_def)
  have pSs: "prnt Ss = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)" using pSr by (simp add: Ss_def split: option.split)
  have pSt: "prnt St = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)" using pSs by (simp add: St_def)
  have pSu: "prnt Su = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)"
    using stem_num_loop_fields[OF psN, THEN mp, OF pSt] by (simp add: Su_def)
  have pSv: "prnt Sv = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)" using pSu by (simp add: Sv_def)
  have pS2: "prnt S2 = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)"
    using last_vin_loop_fields[OF psN, THEN mp, OF pSv] by (simp add: S2_def)
  have pS3: "prnt S3 = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)"
    using last_vout_loop_fields[OF psN, THEN mp, OF pS2] pS2 by (simp add: S3_def)
  have pS4: "prnt S4 = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)"
    using succ_vin_loop_fields[OF psN, THEN mp, OF pS3] by (simp add: S4_def)
  have lsSp: "lsuc Sp = lsuc S0" by (simp add: Sp_def Sfin_def)
  have lsSq: "lsuc Sq = lsuc S0" using lsSp by (simp add: Sq_def split: option.split)
  have lsSr: "lsuc Sr = (lsuc S0)(p := lsx k)" using lsSq by (simp add: Sr_def)
  have lsSs: "lsuc Ss = (lsuc S0)(p := lsx k)" using lsSr by (simp add: Ss_def split: option.split)
  have lsSt: "lsuc St = (lsuc S0)(p := lsx k)" using lsSs by (simp add: St_def)
  have QSt: "\<forall>v\<in>V. lsuc St v \<in> V" using lsSt lkV HS0 by auto
  have QSu: "\<forall>v\<in>V. lsuc Su v \<in> V"
  proof -
    have "lsuc Su = (\<lambda>x. if x \<in> (\<lambda>y. the (((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) y)) ` set (takeWhile (\<lambda>z. z \<noteq> i) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) p)) then lsuc St p else lsuc St x)"
      using stem_num_loop_lsuc[OF psN, THEN mp, OF pSt, THEN mp, OF i_in_follow_newprnt] by (simp add: Su_def)
    thus ?thesis using QSt pV by auto
  qed
  have lsSvSu: "lsuc Sv = lsuc Su" by (simp add: Sv_def)
  have QSv: "\<forall>v\<in>V. lsuc Sv v \<in> V" using QSu lsSvSu by simp
  have lsvpV: "lsuc Sv p \<in> V" using QSv pV by simp
  have QS2: "\<forall>v\<in>V. lsuc S2 v \<in> V"
  proof -
    have "lsuc S2 = (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. lsuc Sv y = j) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) j)) then lsuc Sv p else lsuc Sv x)"
      using last_vin_loop_lsuc[OF psN, THEN mp, OF pSv] by (simp add: S2_def)
    thus ?thesis using QSv lsvpV by auto
  qed
  have Qvout: "\<And>u stp gv sv. sv \<in> V \<Longrightarrow> \<forall>v\<in>V. lsuc (last_vout_loop S2 u stp gv sv) v \<in> V"
  proof -
    fix u stp gv sv assume svV: "sv \<in> V"
    have "lsuc (last_vout_loop S2 u stp gv sv) = (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. Some y \<noteq> stp \<and> lsuc S2 y = gv) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u)) then sv else lsuc S2 x)"
      using last_vout_loop_lsuc[OF psN, THEN mp, OF pS2] by simp
    thus "\<forall>v\<in>V. lsuc (last_vout_loop S2 u stp gv sv) v \<in> V" using svV QS2 by auto
  qed
  have QS3: "\<forall>v\<in>V. lsuc S3 v \<in> V"
  proof (cases "jn \<noteq> the (rvth S0 p) \<and> j \<noteq> the (rvth S0 p)")
    case True
    have "S3 = last_vout_loop S2 (the (prnt S0 p)) (if lsuc Sv jn = j then Some jn else None) (lsuc S0 p) (the (rvth S0 p))"
      unfolding S3_def by (rule if_P[OF True])
    thus ?thesis by (simp add: Qvout[OF orV])
  next
    case c1: False
    have S3red: "S3 = (if lsuc Sv p \<noteq> lsuc S0 p
                       then last_vout_loop S2 (the (prnt S0 p)) (if lsuc Sv jn = j then Some jn else None) (lsuc S0 p) (lsuc Sv p)
                       else S2)"
      unfolding S3_def by (rule if_not_P[OF c1])
    show ?thesis
    proof (cases "lsuc Sv p \<noteq> lsuc S0 p")
      case True
      have "S3 = last_vout_loop S2 (the (prnt S0 p)) (if lsuc Sv jn = j then Some jn else None) (lsuc S0 p) (lsuc Sv p)"
        using S3red by (simp add: True)
      thus ?thesis by (simp add: Qvout[OF lsvpV])
    next
      case False
      have "S3 = S2" using S3red by (simp add: False)
      thus ?thesis using QS2 by simp
    qed
  qed
  have QS5: "\<forall>v\<in>V. lsuc S5 v \<in> V"
  proof -
    have "lsuc S4 = lsuc S3" using succ_vin_loop_fields[OF psN, THEN mp, OF pS3] by (simp add: S4_def)
    moreover have "lsuc S5 = lsuc S4" using succ_vout_loop_fields[OF psN, THEN mp, OF pS4] by (simp add: S5_def)
    ultimately show ?thesis using QS3 by simp
  qed
  show ?thesis using UT QS5 by simp
qed


text \<open>The untouched-edge fact specialised to @{const holed}: every node of @{const holed} other than
      the two splice seams @{term j} and @{term "the (rvth S0 p)"} keeps its old thread successor.
      (The @{const thrd_inv}/splice override keys all live in @{term "block S0 p"}, disjoint from
      @{const holed}.)\<close>
lemma holed_fresh:
  assumes vh: "v \<in> set holed" and vj: "v \<noteq> j" and vr: "v \<noteq> the (rvth S0 p)" and kpos: "0 < k"
  shows "final_thrd v = thrd S0 v"
proof -
  have vnb: "v \<notin> set (block S0 p)" using vh holed_set by simp
  have vlsx: "v \<notin> lsx ` {..k}"
  proof
    assume "v \<in> lsx ` {..k}"
    then obtain t where "t \<le> k" "v = lsx t" by auto
    thus False using lsx_in_block_p[of t] kpos vnb by simp
  qed
  have vbef: "v \<notin> bef ` set [0..<k]"
  proof
    assume "v \<in> bef ` set [0..<k]"
    then obtain m where "m < k" "v = bef m" by auto
    thus False using bef_in_block_p[of m] vnb by simp
  qed
  show ?thesis using final_thrd_fresh[OF vlsx vbef vj vr] by auto
qed

subsubsection \<open>The \<open>j \<rightarrow> i\<close> insertion seam\<close>

lemma j_notin_lsx_img: "0 < k \<Longrightarrow> j \<notin> lsx ` set [0..<k]"
proof
  assume kpos: "0 < k" and "j \<in> lsx ` set [0..<k]"
  then obtain t where "t < k" "j = lsx t" by auto
  thus False using lsx_in_block_p[of t] kpos j_notin_block_p by simp
qed

lemma j_notin_bef_img: "j \<notin> bef ` set [0..<k]"
proof
  assume "j \<in> bef ` set [0..<k]"
  then obtain m where "m < k" "j = bef m" by auto
  thus False using bef_in_block_p[of m] j_notin_block_p by simp
qed

text \<open>The base  "j {\isasymmapsto} i" thread edit survives both @{const thrd_inv} folds (their keys @{const
      lsx}/@{const bef} avoid @{term j}), so @{term "thrd_inv k j = Some i"}.\<close>
lemma thrd_inv_j:
  assumes kpos: "0 < k" shows "thrd_inv k j = Some i"
proof -
  have jlsx: "j \<notin> lsx ` set [0..<k]" using j_notin_lsx_img kpos by simp
  have jbef: "j \<notin> bef ` set [0..<k]" using j_notin_bef_img by simp
  have "thrd_inv k j = (fold (\<lambda>t T. T(bef t := out t)) [0..<k] ((thrd S0)(j \<mapsto> s 0))) j"
    unfolding thrd_inv_def using jlsx by (rule fold_upd_other)
  also have "\<dots> = ((thrd S0)(j \<mapsto> s 0)) j" using jbef by (rule fold_upd_other)
  also have "\<dots> = Some i" using path0 by simp
  finally show ?thesis .
qed

text \<open>The two final splices (@{text Sq} at @{const lsx} @{term k}, @{text Ss} at @{term "the (rvth S0
      p)"}) miss @{term j}, so @{term "final_thrd j = Some i"} --- the new first child of @{term j} is
      @{term i}, the head of @{const newblock}.\<close>
lemma final_thrd_j:
  assumes kpos: "0 < k" shows "final_thrd j = Some i"
proof -
  have lk: "lsx k \<noteq> j" using lsx_in_block_p[of k] kpos j_notin_block_p by auto
  have "final_thrd j = thrd_inv k j"
    using lk by (simp add: final_thrd_def Let_def split: option.split)
  thus ?thesis using thrd_inv_j[OF kpos] by simp
qed

lemma hd_newblock: "hd newblock = i"
proof -
  have c0: "contrib 0 = block S0 i" by (simp add: contrib_def)
  have ne: "block S0 i \<noteq> []" by (rule block_props(2)[OF arb iV])
  have hdi: "hd (block S0 i) = i" by (rule block_props(5)[OF arb iV])
  have lst: "[0..<Suc k] = 0 # [1..<Suc k]" by (simp add: upt_conv_Cons)
  have "newblock = contrib 0 @ concat (map contrib [1..<Suc k])"
    unfolding newblock_def by (subst lst) simp
  thus ?thesis using c0 ne hdi by (simp add: hd_append)
qed

text \<open>Consecutive nodes of the old thread are @{const thrd}-linked (the {\isasymsection}15.2 out-edge engine
      applied to @{term S0}); the base for reading off the surviving edges in @{const holed}.\<close>
lemma oldlist_link:
  assumes "Suc t < length (follow (thrd S0) r)"
  shows "thrd S0 (follow (thrd S0) r ! t) = Some (follow (thrd S0) r ! Suc t)"
  by (rule follow_nth_Suc[OF _ assms]) (use arb in \<open>simp add: arb_invar_def\<close>)

text \<open>@{const alpha} is a prefix of the old thread, so its internal edges are old-thread edges.\<close>
lemma alpha_link:
  assumes "Suc t < length alpha"
  shows "thrd S0 (alpha ! t) = Some (alpha ! Suc t)"
proof -
  have la: "length alpha \<le> length (follow (thrd S0) r)"
    using oldlist_split_eq by simp
  have e1: "follow (thrd S0) r ! t = alpha ! t"
    using assms oldlist_split_eq by (simp add: nth_append)
  have e2: "follow (thrd S0) r ! Suc t = alpha ! Suc t"
    using assms oldlist_split_eq by (simp add: nth_append)
  have lt: "Suc t < length (follow (thrd S0) r)" using assms la by simp
  show ?thesis using oldlist_link[OF lt] e1 e2 by simp
qed

text \<open>@{const beta} is a suffix of the old thread, so its internal edges are old-thread edges.\<close>
lemma beta_link:
  assumes "Suc t < length beta"
  shows "thrd S0 (beta ! t) = Some (beta ! Suc t)"
proof -
  have split: "follow (thrd S0) r = (alpha @ block S0 p) @ beta"
    using oldlist_split_eq by simp
  have e1: "follow (thrd S0) r ! (length (alpha @ block S0 p) + t) = beta ! t"
    using split by (simp add: nth_append)
  have e2: "follow (thrd S0) r ! (length (alpha @ block S0 p) + Suc t) = beta ! Suc t"
    using split by (simp add: nth_append)
  have lt: "Suc (length (alpha @ block S0 p) + t) < length (follow (thrd S0) r)"
    using assms split by simp
  have "thrd S0 (follow (thrd S0) r ! (length (alpha @ block S0 p) + t))
        = Some (follow (thrd S0) r ! Suc (length (alpha @ block S0 p) + t))"
    by (rule oldlist_link[OF lt])
  thus ?thesis using e1 e2 by simp
qed

text \<open>@{const alpha} is nonempty (it starts with the root @{term r}).\<close>
lemma alpha_ne: "alpha \<noteq> []"
proof -
  have pst: "parent_spec (thrd S0)" using arb unfolding arb_invar_def by simp
  have hr: "hd (follow (thrd S0) r) = r" by (rule follow_hd_ps[OF pst])
  have ne: "follow (thrd S0) r \<noteq> []" by (rule follow_ne_ps[OF pst])
  obtain z zs where z: "follow (thrd S0) r = z # zs" using ne by (cases "follow (thrd S0) r") auto
  have zr: "z = r" using hr z by simp
  have "alpha = takeWhile (\<lambda>x. x \<noteq> p) (z # zs)" unfolding alpha_def using z by simp
  hence "alpha = r # takeWhile (\<lambda>x. x \<noteq> p) zs" using zr pne_r by simp
  thus ?thesis by simp
qed

text \<open>The spliced-out reverse of @{term p} is the last node of @{const alpha} (the node just before
      the detached block in the old thread).\<close>
lemma old_rev_last_alpha: "the (rvth S0 p) = last alpha"
proof -
  obtain A B where AB: "follow (thrd S0) r = A @ block S0 p @ B"
      and pA: "A \<noteq> [] \<Longrightarrow> the (rvth S0 p) = last A"
      and pB: "B \<noteq> [] \<Longrightarrow> thrd S0 (lsuc S0 p) = Some (hd B)"
    using block_p_split by auto
  have pst: "parent_spec (thrd S0)" using arb unfolding arb_invar_def by simp
  have dist: "distinct (follow (thrd S0) r)" by (rule follow_distinct_ps[OF pst])
  have hdp: "hd (block S0 p) = p" by (rule block_props(5)[OF arb pV])
  have bne: "block S0 p \<noteq> []" by (rule block_props(2)[OF arb pV])
  obtain rest where bp: "block S0 p = p # rest" using bne hdp by (metis hd_Cons_tl)
  have distA: "distinct (A @ p # rest @ B)" using dist AB bp by simp
  have allA: "\<forall>x\<in>set A. x \<noteq> p" using distA by auto
  have "alpha = A" unfolding alpha_def using AB bp allA by (simp add: takeWhile_append2)
  moreover have "A \<noteq> []" using alpha_ne \<open>alpha = A\<close> by simp
  ultimately show ?thesis using pA by simp
qed

text \<open>Every surviving @{const holed} edge (all but the junction at @{term "the (rvth S0 p)"}) is an
      old-thread edge.\<close>
lemma holed_old_adj:
  assumes lt: "Suc t < length holed" and nj: "holed ! t \<noteq> the (rvth S0 p)"
  shows "thrd S0 (holed ! t) = Some (holed ! Suc t)"
proof -
  have hd: "holed = alpha @ beta" unfolding holed_def by simp
  have lh: "length holed = length alpha + length beta" using hd by simp
  show ?thesis
  proof (cases "Suc t < length alpha")
    case True
    have e1: "holed ! t = alpha ! t" using hd True by (simp add: nth_append)
    have e2: "holed ! Suc t = alpha ! Suc t" using hd True by (simp add: nth_append)
    show ?thesis using alpha_link[OF True] e1 e2 by simp
  next
    case False
    show ?thesis
    proof (cases "t < length alpha")
      case True
      have "Suc t = length alpha" using True False by simp
      hence "t = length alpha - 1" by simp
      hence "alpha ! t = last alpha" using alpha_ne True by (simp add: last_conv_nth)
      hence "holed ! t = the (rvth S0 p)" using hd True old_rev_last_alpha by (simp add: nth_append)
      thus ?thesis using nj by simp
    next
      case False
      hence lat: "length alpha \<le> t" by simp
      obtain d where d: "t = length alpha + d" using le_Suc_ex[OF lat] by auto
      have db: "Suc d < length beta" using lt lh d by simp
      have e1: "holed ! t = beta ! d" using hd d by (simp add: nth_append)
      have e2: "holed ! Suc t = beta ! Suc d" using hd d by (simp add: nth_append)
      show ?thesis using beta_link[OF db] e1 e2 by simp
    qed
  qed
qed

text \<open>At the junction @{term "the (rvth S0 p)"} (when it is not @{term j}) the final thread points to
      @{term "aftn k"} --- the @{term Ss} splice.\<close>
lemma final_thrd_oldrev:
  assumes "the (rvth S0 p) \<noteq> j"
  shows "final_thrd (the (rvth S0 p)) = aftn k"
  using assms by (simp add: final_thrd_def Let_def split: option.split)

text \<open>@{term "aftn k"} is the old thread-successor of @{term p}'s last descendant, i.e. @{term "hd beta"}.\<close>
lemma beta_out:
  assumes bne: "beta \<noteq> []"
  shows "aftn k = Some (hd beta)"
proof -
  obtain A B where AB: "follow (thrd S0) r = A @ block S0 p @ B"
      and pA: "A \<noteq> [] \<Longrightarrow> the (rvth S0 p) = last A"
      and pB: "B \<noteq> [] \<Longrightarrow> thrd S0 (lsuc S0 p) = Some (hd B)"
    using block_p_split by auto
  have pst: "parent_spec (thrd S0)" using arb unfolding arb_invar_def by simp
  have dist: "distinct (follow (thrd S0) r)" by (rule follow_distinct_ps[OF pst])
  have hdp: "hd (block S0 p) = p" by (rule block_props(5)[OF arb pV])
  have bne0: "block S0 p \<noteq> []" by (rule block_props(2)[OF arb pV])
  obtain rest where bp: "block S0 p = p # rest" using bne0 hdp by (metis hd_Cons_tl)
  have distA: "distinct (A @ p # rest @ B)" using dist AB bp by simp
  have allA: "\<forall>x\<in>set A. x \<noteq> p" using distA by auto
  have aA: "alpha = A" unfolding alpha_def using AB bp allA by (simp add: takeWhile_append2)
  have "alpha @ block S0 p @ beta = A @ block S0 p @ B" using oldlist_split_eq AB by simp
  hence "beta = B" using aA by simp
  hence "thrd S0 (lsuc S0 p) = Some (hd beta)" using pB bne by simp
  thus ?thesis by (simp add: aftn_def out_def pathk)
qed

text \<open>The TW/TL regions of @{const newlist}: every consecutive @{const holed} pair (whose source is not
      @{term j}) is realised by @{const final_thrd} --- surviving edges via @{thm holed_fresh}, the
      junction via the @{term Ss} splice.\<close>
lemma holed_adj_final:
  assumes lt: "Suc t < length holed" and nj: "holed ! t \<noteq> j" and kpos: "0 < k"
  shows "final_thrd (holed ! t) = Some (holed ! Suc t)"
proof (cases "holed ! t = the (rvth S0 p)")
  case True
  have hd: "holed = alpha @ beta" unfolding holed_def by simp
  have lh: "length holed = length alpha + length beta" using hd by simp
  have la1: "length alpha - 1 < length holed"
    using alpha_ne lh by (cases "length alpha") auto
  have idx_or: "alpha ! (length alpha - 1) = last alpha"
    using alpha_ne by (simp add: last_conv_nth)
  have hor: "holed ! (length alpha - 1) = the (rvth S0 p)"
    using hd alpha_ne old_rev_last_alpha idx_or by (simp add: nth_append)
  have "holed ! t = holed ! (length alpha - 1)" using True hor by simp
  hence teq: "t = length alpha - 1"
    using holed_distinct lt la1 by (metis Suc_lessD nth_eq_iff_index_eq)
  have Suct: "Suc t = length alpha" using teq alpha_ne by simp
  have bne: "beta \<noteq> []" using lt lh Suct by (cases beta) auto
  have "holed ! Suc t = beta ! 0" using hd Suct by (simp add: nth_append)
  hence hb: "holed ! Suc t = hd beta" using bne by (simp add: hd_conv_nth)
  have "final_thrd (holed ! t) = aftn k" using True nj final_thrd_oldrev by simp
  also have "\<dots> = Some (hd beta)" using beta_out[OF bne] by auto
  finally show ?thesis using hb by simp
next
  case False
  have mem: "holed ! t \<in> set holed" using lt by (simp add: nth_mem)
  show ?thesis using holed_fresh[OF mem nj False kpos] holed_old_adj[OF lt] False by simp
qed

text \<open>@{term "block S0 v"} inherits distinctness from the (distinct) old thread it prefixes.\<close>
lemma block_distinct_V:
  assumes "v \<in> V" shows "distinct (block S0 v)"
proof -
  have pst: "parent_spec (thrd S0)" using arb unfolding arb_invar_def by simp
  obtain C where "follow (thrd S0) v = block S0 v @ C" using block_props(1)[OF arb assms] by metis
  moreover have "distinct (follow (thrd S0) v)" by (rule follow_distinct_ps[OF pst])
  ultimately show ?thesis by simp
qed

text \<open>Endpoint of the left side-part @{term "defP m"} (nodes before @{term "block S0 (s m)"} inside
      @{term "block S0 (s (Suc m))"}): its last node is @{term "bef m"}, the thread-predecessor of
      @{term "s m"}.\<close>
lemma defP_last:
  assumes mk: "m < k" and ne: "defP m \<noteq> []"
  shows "last (defP m) = bef m"
proof -
  have pst: "parent_spec (thrd S0)" using arb unfolding arb_invar_def by simp
  have G: "\<forall>v v'. thrd S0 v = Some v' \<longleftrightarrow> rvth S0 v' = Some v" using arb unfolding arb_invar_def by simp
  have smV: "s m \<in> V" using sV[of m] mk by simp
  have sSmV: "s (Suc m) \<in> V" using sV[of "Suc m"] mk by simp
  have dec: "block S0 (s (Suc m)) = s (Suc m) # defP m @ block S0 (s m) @ defQ m"
    using block_decomp[OF mk] by auto
  obtain C where bf: "follow (thrd S0) (s (Suc m)) = block S0 (s (Suc m)) @ C"
    using block_props(1)[OF arb sSmV] by metis
  have bmne: "block S0 (s m) \<noteq> []" using block_props(2)[OF arb smV] by simp
  have bmhd: "hd (block S0 (s m)) = s m" using block_props(5)[OF arb smV] by simp
  obtain rest where bm: "block S0 (s m) = s m # rest" using bmne bmhd by (metis hd_Cons_tl)
  obtain P' a where Psplit: "defP m = P' @ [a]" using ne by (metis append_butlast_last_id)
  have "follow (thrd S0) (s (Suc m)) = (s (Suc m) # P') @ a # s m # (rest @ defQ m @ C)"
    using bf dec bm Psplit by simp
  hence "thrd S0 a = Some (s m)" by (rule thread_link[OF pst])
  hence "rvth S0 (s m) = Some a" using G by auto
  hence "bef m = a" by (simp add: bef_def)
  thus ?thesis using Psplit by simp
qed

text \<open>When the left side-part is empty, @{term "bef m = s (Suc m)"} (the stem node itself is
      @{term "s m"}'s predecessor).\<close>
lemma defP_empty:
  assumes mk: "m < k" and ne: "defP m = []"
  shows "bef m = s (Suc m)"
proof -
  have pst: "parent_spec (thrd S0)" using arb unfolding arb_invar_def by simp
  have G: "\<forall>v v'. thrd S0 v = Some v' \<longleftrightarrow> rvth S0 v' = Some v" using arb unfolding arb_invar_def by simp
  have smV: "s m \<in> V" using sV[of m] mk by simp
  have sSmV: "s (Suc m) \<in> V" using sV[of "Suc m"] mk by simp
  have dec: "block S0 (s (Suc m)) = s (Suc m) # block S0 (s m) @ defQ m"
    using block_decomp[OF mk] ne by simp
  obtain C where bf: "follow (thrd S0) (s (Suc m)) = block S0 (s (Suc m)) @ C"
    using block_props(1)[OF arb sSmV] by metis
  have bmne: "block S0 (s m) \<noteq> []" using block_props(2)[OF arb smV] by simp
  have bmhd: "hd (block S0 (s m)) = s m" using block_props(5)[OF arb smV] by simp
  obtain rest where bm: "block S0 (s m) = s m # rest" using bmne bmhd by (metis hd_Cons_tl)
  have "follow (thrd S0) (s (Suc m)) = [] @ s (Suc m) # s m # (rest @ defQ m @ C)"
    using bf dec bm by simp
  hence "thrd S0 (s (Suc m)) = Some (s m)" by (rule thread_link[OF pst])
  hence "rvth S0 (s m) = Some (s (Suc m))" using G by auto
  thus ?thesis by (simp add: bef_def)
qed

text \<open>Endpoint of the right side-part @{term "defQ m"}: its last node is @{term "lsuc S0 (s (Suc m))"}
      (the last descendant of @{term "s (Suc m)"}).\<close>
lemma defQ_last:
  assumes mk: "m < k" and ne: "defQ m \<noteq> []"
  shows "last (defQ m) = lsuc S0 (s (Suc m))"
proof -
  have sSmV: "s (Suc m) \<in> V" using sV[of "Suc m"] mk by simp
  have dec: "block S0 (s (Suc m)) = (s (Suc m) # defP m @ block S0 (s m)) @ defQ m"
    using block_decomp[OF mk] by simp
  have "last (block S0 (s (Suc m))) = last (defQ m)" using dec ne by simp
  moreover have "last (block S0 (s (Suc m))) = lsuc S0 (s (Suc m))"
    by (rule block_props(3)[OF arb sSmV])
  ultimately show ?thesis by simp
qed

text \<open>When the right side-part is empty, @{term "s m"} and @{term "s (Suc m)"} share a last successor.\<close>
lemma defQ_empty:
  assumes mk: "m < k" and ne: "defQ m = []"
  shows "lsuc S0 (s m) = lsuc S0 (s (Suc m))"
proof -
  have smV: "s m \<in> V" using sV[of m] mk by simp
  have sSmV: "s (Suc m) \<in> V" using sV[of "Suc m"] mk by simp
  have bmne: "block S0 (s m) \<noteq> []" using block_props(2)[OF arb smV] by simp
  have dec: "block S0 (s (Suc m)) = (s (Suc m) # defP m) @ block S0 (s m)"
    using block_decomp[OF mk] ne by simp
  have "last (block S0 (s (Suc m))) = last (block S0 (s m))" using dec bmne by simp
  moreover have "last (block S0 (s (Suc m))) = lsuc S0 (s (Suc m))"
    by (rule block_props(3)[OF arb sSmV])
  moreover have "last (block S0 (s m)) = lsuc S0 (s m)"
    by (rule block_props(3)[OF arb smV])
  ultimately show ?thesis by simp
qed

text \<open>Converse geometry: a nonempty right side-part forces distinct last-successors (the last
      descendant of @{term "s (Suc m)"} lies strictly after @{term "s m"}'s block).\<close>
lemma defQ_ne_lsuc:
  assumes mk: "m < k" and ne: "defQ m \<noteq> []"
  shows "lsuc S0 (s (Suc m)) \<noteq> lsuc S0 (s m)"
proof
  assume eq: "lsuc S0 (s (Suc m)) = lsuc S0 (s m)"
  have smV: "s m \<in> V" using sV[of m] mk by simp
  have sSmV: "s (Suc m) \<in> V" using sV[of "Suc m"] mk by simp
  have dec: "block S0 (s (Suc m)) = (s (Suc m) # defP m) @ block S0 (s m) @ defQ m"
    using block_decomp[OF mk] by simp
  have dist: "distinct (block S0 (s (Suc m)))" by (rule block_distinct_V[OF sSmV])
  have qlast: "last (defQ m) = lsuc S0 (s (Suc m))" by (rule defQ_last[OF mk ne])
  have qin: "lsuc S0 (s (Suc m)) \<in> set (defQ m)" using qlast ne by (metis last_in_set)
  have blast': "last (block S0 (s m)) = lsuc S0 (s m)" by (rule block_props(3)[OF arb smV])
  have bmne: "block S0 (s m) \<noteq> []" by (rule block_props(2)[OF arb smV])
  have bin: "lsuc S0 (s m) \<in> set (block S0 (s m))" using blast' bmne by (metis last_in_set)
  have "set (block S0 (s m)) \<inter> set (defQ m) = {}" using dist dec by auto
  thus False using qin bin eq by auto
qed

text \<open>Seam-source identification ({\isasymsection}12.0): the loop's up-link pointer @{term "lsx t"} is exactly the
      last node of contribution @{term t}, so the up-links "lsx t {\isasymmapsto} s (Suc t)" are precisely
      the @{const contrib}-boundary edges of @{const newblock}.\<close>
lemma lsx_last_contrib:
  assumes "t \<le> k" shows "lsx t = last (contrib t)"
proof (cases t)
  case 0
  have "contrib 0 = block S0 i" by (simp add: contrib_def)
  moreover have "last (block S0 i) = lsuc S0 i" by (rule block_props(3)[OF arb iV])
  ultimately show ?thesis using 0 by (simp add: lsx_def path0)
next
  case (Suc m)
  have mk: "m < k" using assms Suc by simp
  have cc: "contrib (Suc m) = s (Suc m) # defP m @ defQ m" by (simp add: contrib_def)
  show ?thesis
  proof (cases "defQ m = []")
    case False
    have lc: "last (contrib (Suc m)) = lsuc S0 (s (Suc m))"
      using cc False defQ_last[OF mk False] by simp
    have "lsuc S0 (s (Suc m)) \<noteq> lsuc S0 (s m)" by (rule defQ_ne_lsuc[OF mk False])
    hence "lsx (Suc m) = lsuc S0 (s (Suc m))" by (simp add: lsx_def)
    thus ?thesis using Suc lc by simp
  next
    case True
    have eq: "lsuc S0 (s m) = lsuc S0 (s (Suc m))" by (rule defQ_empty[OF mk True])
    hence lsxv: "lsx (Suc m) = bef m" by (simp add: lsx_def bef_def)
    show ?thesis
    proof (cases "defP m = []")
      case True
      have "contrib (Suc m) = [s (Suc m)]" using cc True \<open>defQ m = []\<close> by simp
      hence "last (contrib (Suc m)) = s (Suc m)" by simp
      moreover have "bef m = s (Suc m)" by (rule defP_empty[OF mk True])
      ultimately show ?thesis using Suc lsxv by simp
    next
      case False
      have "last (contrib (Suc m)) = last (defP m)" using cc False \<open>defQ m = []\<close> by simp
      moreover have "last (defP m) = bef m" by (rule defP_last[OF mk False])
      ultimately show ?thesis using Suc lsxv by simp
    qed
  qed
qed

text \<open>Splitting an upper range at an interior point (list utility for the @{const contrib} segments).\<close>
lemma upt_split0: assumes "b \<le> n" shows "[0..<n] = [0..<b] @ [b..<n]"
  using assms upt_add_eq_append[of 0 b "n - b"] by simp

text \<open>Every contribution is nonempty.\<close>
lemma contrib_ne: "contrib t \<noteq> []"
  by (cases t) (auto simp: contrib_def block_props(2)[OF arb iV])

text \<open>Distinct contributions are set-disjoint (they are disjoint segments of the distinct
      @{const newblock}).\<close>
lemma contrib_seg_disjoint:
  assumes ab: "a < b" and bk: "b \<le> k"
  shows "set (contrib a) \<inter> set (contrib b) = {}"
proof -
  have sp: "[0..<Suc k] = [0..<b] @ b # [Suc b..<Suc k]"
    using bk by (subst upt_split0[of b "Suc k"]) (auto simp: upt_conv_Cons)
  have nb: "newblock = concat (map contrib [0..<b]) @ contrib b @ concat (map contrib [Suc b..<Suc k])"
    unfolding newblock_def by (subst sp) simp
  have dist: "distinct newblock" by (rule newblock_distinct)
  have disj: "set (concat (map contrib [0..<b])) \<inter> set (contrib b) = {}"
    using dist nb by (auto simp: distinct_append)
  have amem: "set (contrib a) \<subseteq> set (concat (map contrib [0..<b]))"
    using ab by auto
  show ?thesis using amem disj by auto
qed

text \<open>@{const lsx} is injective on @{term "{..k}"} (its values are the distinct last nodes of the
      distinct contributions).\<close>
lemma lsx_inj_le:
  assumes ak: "a \<le> k" and bk: "b \<le> k" and ab: "a \<noteq> b"
  shows "lsx a \<noteq> lsx b"
proof -
  have "\<And>x y. x < y \<Longrightarrow> y \<le> k \<Longrightarrow> lsx x \<noteq> lsx y"
  proof -
    fix x y assume xy: "x < y" and yk: "y \<le> k"
    have "lsx x = last (contrib x)" using lsx_last_contrib[of x] xy yk by simp
    moreover have "lsx y = last (contrib y)" using lsx_last_contrib[of y] yk by simp
    moreover have "last (contrib x) \<in> set (contrib x)" using contrib_ne by (metis last_in_set)
    moreover have "last (contrib y) \<in> set (contrib y)" using contrib_ne by (metis last_in_set)
    ultimately show "lsx x \<noteq> lsx y" using contrib_seg_disjoint[OF xy yk] by auto
  qed
  thus ?thesis using ak bk ab by (metis linorder_neqE_nat)
qed

text \<open>The up-links survive to step @{term k}: the edge term "lsx t {\isasymmapsto} s (Suc t)" installed at
      step @{term t} is never overwritten by a later up-link (@{thm lsx_inj_le}) or bridge
      (@{thm bef_notin_lsx}).\<close>
lemma thrd_inv_up_aux:
  assumes "t < n" and "n \<le> k"
  shows "thrd_inv n (lsx t) = Some (s (Suc t))"
  using assms
proof (induction n)
  case 0 thus ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases "t = n")
    case True
    have nk: "n < k" using Suc.prems by simp
    have bne: "bef n \<noteq> lsx n" using bef_notin_lsx[OF nk] by auto
    have "thrd_inv (Suc n) = ((thrd_inv n)(lsx n \<mapsto> s (Suc n)))(bef n := out n)"
      by (rule thrd_inv_Suc[OF nk])
    thus ?thesis using True bne by simp
  next
    case False
    hence tn: "t < n" using Suc.prems by simp
    have nk: "n < k" using Suc.prems by simp
    have IH: "thrd_inv n (lsx t) = Some (s (Suc t))" using Suc.IH tn nk by simp
    have ne1: "lsx t \<noteq> lsx n" using lsx_inj_le[of t n] tn nk False by simp
    have tmem: "lsx t \<in> lsx ` {..n}" using tn by auto
    have ne2: "lsx t \<noteq> bef n"
    proof
      assume "lsx t = bef n"
      thus False using bef_notin_lsx[OF nk] tmem by simp
    qed
    have "thrd_inv (Suc n) = ((thrd_inv n)(lsx n \<mapsto> s (Suc n)))(bef n := out n)"
      by (rule thrd_inv_Suc[OF nk])
    thus ?thesis using IH ne1 ne2 by simp
  qed
qed

text \<open>The @{const contrib}-boundary (seam) edges of @{const newblock}: @{term "lsx t"} (= last node of
      contribution @{term t}) threads to @{term "s (Suc t)"} (= head of contribution @{term "Suc t"}).\<close>
lemma thrd_inv_up:
  assumes "t < k" shows "thrd_inv k (lsx t) = Some (s (Suc t))"
  by (rule thrd_inv_up_aux[OF assms order.refl])

text \<open>No stem node is the root (interior stem nodes have parents; term "s k = p {\isasymnoteq} r").\<close>

text \<open>Each contribution is distinct (a segment of the distinct @{const newblock}).\<close>
lemma contrib_distinct: assumes "t \<le> k" shows "distinct (contrib t)"
proof -
  have sp: "[0..<Suc k] = [0..<t] @ t # [Suc t..<Suc k]"
    using assms by (subst upt_split0[of t "Suc k"]) (auto simp: upt_conv_Cons)
  have nb: "newblock = concat (map contrib [0..<t]) @ contrib t @ concat (map contrib [Suc t..<Suc k])"
    unfolding newblock_def by (subst sp) simp
  have "distinct newblock" by (rule newblock_distinct)
  thus ?thesis using nb by (simp add: distinct_append)
qed

text \<open>@{term "bef m"} lies in contribution @{term "Suc m"} (as @{term "last (defP m)"}, or as
      @{term "s (Suc m)"} when @{term "defP m"} is empty).\<close>
lemma bef_in_contrib_Suc: assumes mk: "m < k" shows "bef m \<in> set (contrib (Suc m))"
proof (cases "defP m = []")
  case True
  have "bef m = s (Suc m)" by (rule defP_empty[OF mk True])
  thus ?thesis by (simp add: contrib_def)
next
  case False
  have "last (defP m) = bef m" by (rule defP_last[OF mk False])
  hence "bef m \<in> set (defP m)" using False by (metis last_in_set)
  thus ?thesis by (simp add: contrib_def)
qed

text \<open>When the right side-part is nonempty, @{term "bef m"} is a strict interior node of contribution
      @{term "Suc m"} (it precedes the nonempty @{term "defQ m"}), hence not its last node.\<close>
lemma bef_ne_last_contrib_Suc:
  assumes mk: "m < k" and ne: "defQ m \<noteq> []"
  shows "bef m \<noteq> last (contrib (Suc m))"
proof -
  have cc: "contrib (Suc m) = (s (Suc m) # defP m) @ defQ m" by (simp add: contrib_def)
  have dist: "distinct (contrib (Suc m))" using contrib_distinct[of "Suc m"] mk by simp
  have lc: "last (contrib (Suc m)) = last (defQ m)" using cc ne by simp
  have qin: "last (defQ m) \<in> set (defQ m)" using ne by (metis last_in_set)
  have befin: "bef m \<in> set (s (Suc m) # defP m)"
  proof (cases "defP m = []")
    case True thus ?thesis using defP_empty[OF mk True] by simp
  next
    case False
    have "last (defP m) = bef m" by (rule defP_last[OF mk False])
    hence "bef m \<in> set (defP m)" using False by (metis last_in_set)
    thus ?thesis by simp
  qed
  have "set (s (Suc m) # defP m) \<inter> set (defQ m) = {}" using dist cc by (auto simp: distinct_append)
  thus ?thesis using lc qin befin by auto
qed

text \<open>A genuine hole source @{term "bef m"} (with @{term "defQ m \<noteq> []"}) is never an up-link key:
      as a contribution interior node it differs from every @{term "lsx t = last (contrib t)"}.\<close>
lemma bef_notin_lsx_all:
  assumes mk: "m < k" and ne: "defQ m \<noteq> []"
  shows "bef m \<notin> lsx ` {..k}"
proof
  assume "bef m \<in> lsx ` {..k}"
  then obtain t where tk: "t \<le> k" and eq: "bef m = lsx t" by auto
  show False
  proof (cases "t = Suc m")
    case True
    have "lsx (Suc m) = last (contrib (Suc m))" using lsx_last_contrib[of "Suc m"] mk by simp
    thus False using eq True bef_ne_last_contrib_Suc[OF mk ne] by simp
  next
    case False
    have lc: "lsx t = last (contrib t)" using lsx_last_contrib[OF tk] by auto
    have "last (contrib t) \<in> set (contrib t)" using contrib_ne by (metis last_in_set)
    hence tin: "bef m \<in> set (contrib t)" using eq lc by simp
    have bin: "bef m \<in> set (contrib (Suc m))" by (rule bef_in_contrib_Suc[OF mk])
    have Smk: "Suc m \<le> k" using mk by simp
    have "set (contrib t) \<inter> set (contrib (Suc m)) = {}"
    proof (cases "t < Suc m")
      case True thus ?thesis using contrib_seg_disjoint[OF True Smk] by simp
    next
      case False hence "Suc m < t" using \<open>t \<noteq> Suc m\<close> by simp
      thus ?thesis using contrib_seg_disjoint[OF _ tk] by auto
    qed
    thus False using tin bin by auto
  qed
qed

text \<open>The bridge (hole) edges survive to step @{term k}: the edge  "bef m {\isasymmapsto} out m" installed
      at step @{term m} is never overwritten by a later up-link (@{thm bef_notin_lsx_all}) or bridge
      (@{thm bef_inj}).\<close>
lemma thrd_inv_br_aux:
  assumes "m < n" and "n \<le> k" and ne: "defQ m \<noteq> []"
  shows "thrd_inv n (bef m) = out m"
  using assms(1,2)
proof (induction n)
  case 0 thus ?case by simp
next
  case (Suc n)
  have mk: "m < k" using Suc.prems by simp
  show ?case
  proof (cases "m = n")
    case True
    have nk: "n < k" using Suc.prems True by simp
    have "thrd_inv (Suc n) = ((thrd_inv n)(lsx n \<mapsto> s (Suc n)))(bef n := out n)"
      by (rule thrd_inv_Suc[OF nk])
    thus ?thesis using True by simp
  next
    case False
    hence mn: "m < n" using Suc.prems by simp
    have nk: "n < k" using Suc.prems by simp
    have IH: "thrd_inv n (bef m) = out m" using Suc.IH mn nk by simp
    have ne1: "bef m \<noteq> lsx n" using bef_notin_lsx_all[OF mk ne] nk by auto
    have ne2: "bef m \<noteq> bef n" using bef_inj[OF mk nk] False by simp
    have "thrd_inv (Suc n) = ((thrd_inv n)(lsx n \<mapsto> s (Suc n)))(bef n := out n)"
      by (rule thrd_inv_Suc[OF nk])
    thus ?thesis using IH ne1 ne2 by simp
  qed
qed

text \<open>The @{term defP}/@{term defQ} junction (hole) edge of @{const newblock}: @{term "bef m"}
      (= @{term "last (defP m)"}) threads to @{term "out m"} (= head of @{term "defQ m"}).\<close>
lemma thrd_inv_br:
  assumes mk: "m < k" and ne: "defQ m \<noteq> []"
  shows "thrd_inv k (bef m) = out m"
  by (rule thrd_inv_br_aux[OF mk order.refl ne])

text \<open>@{const final_thrd} agrees with @{term "thrd_inv k"} off the two top-level splice keys
      @{term "lsx k"} (@{term Sq}) and @{term "the (rvth S0 p)"} (@{term Ss}).  This is the bridge
      that turns the @{term "thrd_inv k"} edge lemmas into @{const final_thrd} edges.\<close>
lemma final_thrd_off:
  assumes "x \<noteq> lsx k" and "x \<noteq> the (rvth S0 p)"
  shows "final_thrd x = thrd_inv k x"
  using assms by (simp add: final_thrd_def Let_def split: option.split)

text \<open>Stem/block characterisation: @{term "s t"} lies in @{term "s n"}'s block iff @{term "t \<le> n"}
      (a stem node is a descendant of @{term "s n"} exactly when it is at or below @{term n} on the
      path).  Built from @{thm stem_chain} (ancestor chain) and @{thm anc_notin_thread_suffix}.\<close>
lemma s_in_block_iff:
  assumes tk: "t \<le> k" and nk: "n \<le> k" and k0: "0 < k"
  shows "(s t \<in> set (block S0 (s n))) \<longleftrightarrow> t \<le> n"
proof
  assume "s t \<in> set (block S0 (s n))"
  show "t \<le> n"
  proof (rule ccontr)
    assume "\<not> t \<le> n"
    hence nt: "n < t" by simp
    have snV: "s n \<in> V" using sV nk k0 by simp
    have stV: "s t \<in> V" using sV tk k0 by simp
    have "s t \<in> set (follow (prnt S0) (s n))" using stem_chain[of t n] tk nt by simp
    hence snchild: "s n \<in> children (prnt S0) (s t)" unfolding children_def by simp
    have ne: "s t \<noteq> s n" using inj nt tk nk by (auto simp: inj_on_eq_iff)
    have "s t \<notin> set (follow (thrd S0) (s n))"
      using anc_notin_thread_suffix[OF stV snchild ne] by auto
    moreover have "set (block S0 (s n)) \<subseteq> set (follow (thrd S0) (s n))"
      using block_props(1)[OF arb snV] by (metis Un_iff set_append subsetI)
    ultimately show False using \<open>s t \<in> set (block S0 (s n))\<close> by auto
  qed
next
  assume tn: "t \<le> n"
  have snV: "s n \<in> V" using sV nk k0 by simp
  have "s n \<in> set (follow (prnt S0) (s t))" using stem_chain[of n t] nk tn by simp
  hence "s t \<in> children (prnt S0) (s n)" unfolding children_def by simp
  thus "s t \<in> set (block S0 (s n))" using block_props(4)[OF arb snV] by simp
qed

text \<open>The left side-part @{term "defP m"} contains no stem node (it sits strictly between
      @{term "s (Suc m)"} and @{term "block S0 (s m)"}).\<close>

text \<open>The right side-part @{term "defQ m"} contains no stem node.\<close>
lemma defQ_no_stem:
  assumes mk: "m < k" and tk: "t \<le> k" shows "s t \<notin> set (defQ m)"
proof
  assume asm: "s t \<in> set (defQ m)"
  have k0: "0 < k" using mk by simp
  have sSmV: "s (Suc m) \<in> V" using sV[of "Suc m"] mk by simp
  have dec: "block S0 (s (Suc m)) = s (Suc m) # defP m @ block S0 (s m) @ defQ m"
    using block_decomp[OF mk] by auto
  have dist: "distinct (block S0 (s (Suc m)))" by (rule block_distinct_V[OF sSmV])
  have inblk: "s t \<in> set (block S0 (s (Suc m)))" using asm dec by simp
  have tSm: "t \<le> Suc m" using s_in_block_iff[of t "Suc m"] tk mk inblk k0 by simp
  have "s t \<notin> set (block S0 (s m))" using dist dec asm by auto
  hence "\<not> t \<le> m" using s_in_block_iff[of t m] tk mk inblk k0 by auto
  hence "t = Suc m" using tSm by simp
  hence "s t = s (Suc m)" by simp
  moreover have "s (Suc m) \<notin> set (defQ m)" using dist dec by auto
  ultimately show False using asm by simp
qed

text \<open>A node whose old thread-successor is not a stem node is not a bridge key (@{const bef}): the
      unlock for interior-edge freshness.\<close>

text \<open>Assembly engine (pure list): a map @{term f} that links every internal edge of each nonempty
      segment and every segment-boundary (seam) realises the whole @{const concat} as a forward chain.
      Applied to @{term "map contrib [0..<Suc k]"} it threads @{const newblock}, and to
      @{term "[TW, [j], newblock, TL]"} it threads @{const newlist}.\<close>
lemma concat_linked:
  assumes ne: "\<And>ys. ys \<in> set xss \<Longrightarrow> ys \<noteq> []"
    and internal: "\<And>ys q. ys \<in> set xss \<Longrightarrow> Suc q < length ys \<Longrightarrow> f (ys ! q) = Some (ys ! Suc q)"
    and seam: "\<And>i. Suc i < length xss \<Longrightarrow> f (last (xss ! i)) = Some (hd (xss ! Suc i))"
    and lt: "Suc t < length (concat xss)"
  shows "f (concat xss ! t) = Some (concat xss ! Suc t)"
  using ne internal seam lt
proof (induction xss arbitrary: t)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  have xne: "x \<noteq> []" using Cons.prems(1) by simp
  let ?n = "length x"
  show ?case
  proof (cases "Suc t < ?n")
    case True
    have "f (x ! t) = Some (x ! Suc t)" using Cons.prems(2)[of x t] True by simp
    moreover have "(x @ concat xs) ! t = x ! t" using True by (simp add: nth_append)
    moreover have "(x @ concat xs) ! Suc t = x ! Suc t" using True by (simp add: nth_append)
    ultimately show ?thesis by simp
  next
    case False
    show ?thesis
    proof (cases "t < ?n")
      case True
      have tn: "Suc t = ?n" using True False by simp
      have te: "length x - 1 = t" using tn by simp
      have xsne: "concat xs \<noteq> []" using Cons.prems(4) tn by simp
      then obtain y ys' where xs2: "xs = y # ys'" and yne: "y \<noteq> []"
        using Cons.prems(1) by (cases xs) auto
      have s0: "f (last x) = Some (hd (xs ! 0))"
        using Cons.prems(3)[of 0] xs2 by simp
      have lastx: "(x @ concat xs) ! t = last x"
        using True te xne by (simp add: nth_append last_conv_nth)
      have hdc: "(x @ concat xs) ! Suc t = hd (concat xs)"
        using tn xsne by (simp add: nth_append hd_conv_nth)
      have "hd (concat xs) = hd (xs ! 0)" using xs2 yne by simp
      thus ?thesis using lastx hdc s0 by simp
    next
      case False
      hence nt: "?n \<le> t" by simp
      obtain d where d: "t = ?n + d" using nt le_Suc_ex by auto
      have e1: "(x @ concat xs) ! t = concat xs ! d" using d by (simp add: nth_append)
      have e2: "(x @ concat xs) ! Suc t = concat xs ! Suc d" using d by (simp add: nth_append)
      have ltd: "Suc d < length (concat xs)" using Cons.prems(4) d by simp
      have IH: "f (concat xs ! d) = Some (concat xs ! Suc d)"
      proof (rule Cons.IH)
        show "\<And>ys. ys \<in> set xs \<Longrightarrow> ys \<noteq> []" using Cons.prems(1) by simp
        show "\<And>ys q. ys \<in> set xs \<Longrightarrow> Suc q < length ys \<Longrightarrow> f (ys ! q) = Some (ys ! Suc q)"
          using Cons.prems(2) by simp
        fix i assume "Suc i < length xs"
        thus "f (last (xs ! i)) = Some (hd (xs ! Suc i))"
          using Cons.prems(3)[of "Suc i"] by simp
      next
        show "Suc d < length (concat xs)" using ltd by auto
      qed
      show ?thesis using e1 e2 IH by simp
    qed
  qed
qed

lemma contrib_subset_nb:
  assumes "t \<le> k" shows "set (contrib t) \<subseteq> set newblock"
proof -
  have "t \<in> set [0..<Suc k]" using assms by fastforce
  hence "contrib t \<in> set (map contrib [0..<Suc k])" by force
  thus ?thesis unfolding newblock_def by (auto simp: set_concat)
qed

lemma block_link:
  assumes vV: "v \<in> V" and lt: "Suc q < length (block S0 v)"
  shows "thrd S0 (block S0 v ! q) = Some (block S0 v ! Suc q)"
proof -
  have pst: "parent_spec (thrd S0)" using arb unfolding arb_invar_def by simp
  obtain C where bf: "follow (thrd S0) v = block S0 v @ C" using block_props(1)[OF arb vV] by metis
  have e1: "follow (thrd S0) v ! q = block S0 v ! q" using lt bf by (simp add: nth_append)
  have e2: "follow (thrd S0) v ! Suc q = block S0 v ! Suc q" using lt bf by (simp add: nth_append)
  have lt2: "Suc q < length (follow (thrd S0) v)" using lt bf by simp
  show ?thesis using follow_nth_Suc[OF pst lt2] e1 e2 by simp
qed

lemma old_rev_notin_block_p: "the (rvth S0 p) \<notin> set (block S0 p)"
  using oldlist_distinct oldlist_split_eq old_rev_last_alpha alpha_ne last_in_set by auto

lemma out_eq_hd_defQ:
  assumes mk: "m < k" and ne: "defQ m \<noteq> []"
  shows "out m = Some (hd (defQ m))"
proof -
  have smV: "s m \<in> V" using sV[of m] mk by simp
  have sSmV: "s (Suc m) \<in> V" using sV[of "Suc m"] mk by simp
  define pre where "pre = s (Suc m) # defP m"
  have dec: "block S0 (s (Suc m)) = pre @ block S0 (s m) @ defQ m"
    using block_decomp[OF mk] pre_def by simp
  have bmne: "block S0 (s m) \<noteq> []" by (rule block_props(2)[OF arb smV])
  let ?lp = "length pre"
  let ?lb = "length (block S0 (s m))"
  let ?q = "?lp + ?lb - 1"
  have qpos: "?lp + ?lb - 1 = ?lp + (?lb - 1)" using bmne by (cases "block S0 (s m)") auto
  have idx1: "block S0 (s (Suc m)) ! ?q = last (block S0 (s m))"
    using dec qpos bmne by (simp add: nth_append last_conv_nth)
  have idx2: "block S0 (s (Suc m)) ! Suc ?q = hd (defQ m)"
  proof -
    have sq: "Suc ?q = ?lp + ?lb" using bmne by (cases "block S0 (s m)") auto
    have "block S0 (s (Suc m)) ! Suc ?q = defQ m ! 0" using dec sq by (simp add: nth_append)
    thus ?thesis using ne by (simp add: hd_conv_nth)
  qed
  have ltq: "Suc ?q < length (block S0 (s (Suc m)))"
    using dec ne bmne by (cases "block S0 (s m)") auto
  have "thrd S0 (block S0 (s (Suc m)) ! ?q) = Some (block S0 (s (Suc m)) ! Suc ?q)"
    by (rule block_link[OF sSmV ltq])
  hence "thrd S0 (last (block S0 (s m))) = Some (hd (defQ m))" using idx1 idx2 by simp
  moreover have "last (block S0 (s m)) = lsuc S0 (s m)" by (rule block_props(3)[OF arb smV])
  ultimately show ?thesis by (simp add: out_def)
qed

lemma contrib_seam:
  assumes tk: "t < k"
  shows "final_thrd (last (contrib t)) = Some (hd (contrib (Suc t)))"
proof -
  have k0: "0 < k" using tk by simp
  have lc: "last (contrib t) = lsx t" using lsx_last_contrib[of t] tk by simp
  have hc: "hd (contrib (Suc t)) = s (Suc t)" by (simp add: contrib_def)
  have ne_k: "lsx t \<noteq> lsx k" using lsx_inj_le[of t k] tk by simp
  have inblk: "lsx t \<in> set (block S0 p)" using lsx_in_block_p[of t] tk k0 by simp
  have ne_or: "lsx t \<noteq> the (rvth S0 p)" using inblk old_rev_notin_block_p by auto
  have "final_thrd (lsx t) = thrd_inv k (lsx t)" using final_thrd_off[OF ne_k ne_or] by auto
  also have "\<dots> = Some (s (Suc t))" by (rule thrd_inv_up[OF tk])
  finally show ?thesis using lc hc by simp
qed

lemma contrib_fresh:
  assumes xin: "x \<in> set (contrib t)" and tk: "t \<le> k"
    and xlsx: "x \<notin> lsx ` {..k}" and xbef: "x \<notin> bef ` set [0..<k]"
  shows "final_thrd x = thrd S0 x"
  using final_thrd_fresh[OF xlsx xbef] contrib_subset_nb[OF tk] xin newblock_set j_notin_block_p old_rev_notin_block_p by auto

lemma contrib_disj_sym:
  assumes ak: "a \<le> k" and bk: "b \<le> k" and ab: "a \<noteq> b"
  shows "set (contrib a) \<inter> set (contrib b) = {}"
proof (cases "a < b")
  case True from contrib_seg_disjoint[OF True bk] show ?thesis .
next
  case False hence ba: "b < a" using ab by simp
  from contrib_seg_disjoint[OF ba ak] show ?thesis by auto
qed

lemma interior_notin_lsx:
  assumes xin: "x \<in> set (contrib t)" and tk: "t \<le> k" and xne: "x \<noteq> last (contrib t)"
  shows "x \<notin> lsx ` {..k}"
proof
  assume "x \<in> lsx ` {..k}"
  then obtain t' where t'k: "t' \<le> k" and xeq: "x = lsx t'" by auto
  have lc: "lsx t' = last (contrib t')" using lsx_last_contrib[OF t'k] by auto
  show False
  proof (cases "t' = t")
    case True thus False using xeq lc xne by simp
  next
    case False
    have "last (contrib t') \<in> set (contrib t')" using contrib_ne by (metis last_in_set)
    hence "x \<in> set (contrib t')" using xeq lc by simp
    thus False using xin contrib_disj_sym[OF tk t'k] False by auto
  qed
qed

lemma interior_notin_bef:
  assumes xin: "x \<in> set (contrib t)" and tk: "t \<le> k"
    and hole: "\<And>m. m < k \<Longrightarrow> t = Suc m \<Longrightarrow> x \<noteq> bef m"
  shows "x \<notin> bef ` set [0..<k]"
proof
  assume "x \<in> bef ` set [0..<k]"
  then obtain m where mk: "m < k" and xeq: "x = bef m" by auto
  have bin: "bef m \<in> set (contrib (Suc m))" by (rule bef_in_contrib_Suc[OF mk])
  show False
  proof (cases "t = Suc m")
    case True thus False using hole[OF mk] xeq by simp
  next
    case False
    have Smk: "Suc m \<le> k" using mk by simp
    have "set (contrib t) \<inter> set (contrib (Suc m)) = {}"
      using contrib_disj_sym[OF tk Smk False] by auto
    thus False using xin xeq bin by auto
  qed
qed

lemma contrib0_link:
  assumes lt: "Suc q < length (contrib 0)"
  shows "final_thrd (contrib 0 ! q) = Some (contrib 0 ! Suc q)"
proof -
  have c0: "contrib 0 = block S0 i" by (simp add: contrib_def)
  have ltc: "Suc q < length (block S0 i)" using lt c0 by simp
  have bne: "block S0 i \<noteq> []" by (rule block_props(2)[OF arb iV])
  have dist: "distinct (block S0 i)" by (rule block_distinct_V[OF iV])
  have thr: "thrd S0 (block S0 i ! q) = Some (block S0 i ! Suc q)" by (rule block_link[OF iV ltc])
  define x where "x = contrib 0 ! q"
  have xin: "x \<in> set (contrib 0)" using x_def lt by (simp add: nth_mem)
  have xne: "x \<noteq> last (contrib 0)"
  proof -
    have lst: "last (contrib 0) = block S0 i ! (length (block S0 i) - 1)"
      using c0 bne by (simp add: last_conv_nth)
    have qne: "q \<noteq> length (block S0 i) - 1" using ltc by simp
    have i1: "q < length (block S0 i)" using ltc by simp
    have i2: "length (block S0 i) - 1 < length (block S0 i)" using bne by (cases "block S0 i") auto
    have "block S0 i ! q \<noteq> block S0 i ! (length (block S0 i) - 1)"
      using dist i1 i2 qne by (simp add: nth_eq_iff_index_eq)
    thus ?thesis using lst x_def c0 by simp
  qed
  have xlsx: "x \<notin> lsx ` {..k}" by (rule interior_notin_lsx[OF xin le0 xne])
  have xbef: "x \<notin> bef ` set [0..<k]" by (rule interior_notin_bef[OF xin le0]) simp
  have "final_thrd x = thrd S0 x" by (rule contrib_fresh[OF xin le0 xlsx xbef])
  thus ?thesis using x_def c0 thr by simp
qed

lemma final_thrd_bef:
  assumes mk: "m < k" and defQne: "defQ m \<noteq> []"
  shows "final_thrd (bef m) = Some (hd (defQ m))"
proof -
  have bne_k: "bef m \<notin> lsx ` {..k}" by (rule bef_notin_lsx_all[OF mk defQne])
  have bne_lsxk: "bef m \<noteq> lsx k" using bne_k by auto
  have bne_or: "bef m \<noteq> the (rvth S0 p)" using bef_in_block_p[OF mk] old_rev_notin_block_p by auto
  have "final_thrd (bef m) = thrd_inv k (bef m)" using final_thrd_off[OF bne_lsxk bne_or] by auto
  also have "\<dots> = out m" by (rule thrd_inv_br[OF mk defQne])
  also have "\<dots> = Some (hd (defQ m))" by (rule out_eq_hd_defQ[OF mk defQne])
  finally show ?thesis .
qed

lemma contribS_nth1:
  assumes mk: "m < k" and a: "a < Suc (length (defP m))"
  shows "contrib (Suc m) ! a = block S0 (s (Suc m)) ! a"
proof -
  have cc: "contrib (Suc m) = s (Suc m) # (defP m @ defQ m)" by (simp add: contrib_def)
  have dec: "block S0 (s (Suc m)) = s (Suc m) # (defP m @ block S0 (s m) @ defQ m)"
    using block_decomp[OF mk] by simp
  show ?thesis
  proof (cases a)
    case 0 thus ?thesis using cc dec by simp
  next
    case (Suc a')
    have a': "a' < length (defP m)" using a Suc by simp
    show ?thesis using cc Suc a' a' dec Suc by (simp add: nth_append)
  qed
qed

lemma contribS_nth2:
  assumes mk: "m < k" and a1: "Suc (length (defP m)) \<le> a"
    and a2: "a < Suc (length (defP m)) + length (defQ m)"
  shows "contrib (Suc m) ! a = block S0 (s (Suc m)) ! (a + length (block S0 (s m)))"
proof -
  define pre where "pre = s (Suc m) # defP m"
  have cc: "contrib (Suc m) = pre @ defQ m" by (simp add: contrib_def pre_def)
  have dec: "block S0 (s (Suc m)) = pre @ block S0 (s m) @ defQ m"
    using block_decomp[OF mk] pre_def by simp
  let ?lb = "length (block S0 (s m))"
  have lpe: "length pre = Suc (length (defP m))" by (simp add: pre_def)
  have geq: "length pre \<le> a" using a1 lpe by simp
  have "contrib (Suc m) ! a = defQ m ! (a - length pre)" using cc geq by (simp add: nth_append)
  moreover have "block S0 (s (Suc m)) ! (a + ?lb) = (block S0 (s m) @ defQ m) ! (a + ?lb - length pre)"
    using dec geq by (simp add: nth_append)
  moreover have "a + ?lb - length pre = ?lb + (a - length pre)" using geq by simp
  moreover have "(block S0 (s m) @ defQ m) ! (?lb + (a - length pre)) = defQ m ! (a - length pre)"
    by (simp add: nth_append)
  ultimately show ?thesis by simp
qed

lemma bef_eq_contrib_junction:
  assumes mk: "m < k" shows "bef m = contrib (Suc m) ! (length (defP m))"
proof -
  define pre where "pre = s (Suc m) # defP m"
  have cc: "contrib (Suc m) = pre @ defQ m" by (simp add: contrib_def pre_def)
  have lp: "length (defP m) < length pre" by (simp add: pre_def)
  have "contrib (Suc m) ! (length (defP m)) = pre ! (length (defP m))"
    using cc lp by (simp add: nth_append)
  also have "\<dots> = last pre" using lp by (simp add: last_conv_nth pre_def)
  also have "last pre = bef m"
  proof (cases "defP m = []")
    case True thus ?thesis using defP_empty[OF mk True] by (simp add: pre_def)
  next
    case False
    have "last pre = last (defP m)" using False by (simp add: pre_def)
    thus ?thesis using defP_last[OF mk False] by simp
  qed
  finally show ?thesis by simp
qed

lemma junction_index_ge:
  assumes F: "\<not> Suc q < Suc (length (defP m))" and nj: "Suc q \<noteq> Suc (length (defP m))"
  shows "Suc (length (defP m)) \<le> q"
  using F nj by simp

lemma contribS_defQ_block_bound:
  assumes mk: "m < k" and Sqlt: "Suc q < Suc (length (defP m)) + length (defQ m)"
  shows "Suc (q + length (block S0 (s m))) < length (block S0 (s (Suc m)))"
  using block_decomp[OF mk] Sqlt by simp

lemma thrd_step_transfer:
  assumes e1: "contrib (Suc m) ! q = block S0 (s (Suc m)) ! (q + length (block S0 (s m)))"
    and e2: "contrib (Suc m) ! Suc q = block S0 (s (Suc m)) ! (Suc q + length (block S0 (s m)))"
    and bl: "thrd S0 (block S0 (s (Suc m)) ! (q + length (block S0 (s m))))
        = Some (block S0 (s (Suc m)) ! Suc (q + length (block S0 (s m))))"
  shows "thrd S0 (contrib (Suc m) ! q) = Some (contrib (Suc m) ! Suc q)"
proof -
  have "Suc (q + length (block S0 (s m))) = Suc q + length (block S0 (s m))" by simp
  thus ?thesis using bl e1 e2 by simp
qed

lemma contribS_edge_pre:
  assumes mk: "m < k" and T: "Suc q < Suc (length (defP m))"
  shows "thrd S0 (contrib (Suc m) ! q) = Some (contrib (Suc m) ! Suc q)"
proof -
  have sSmV: "s (Suc m) \<in> V" using sV[of "Suc m"] mk by simp
  have e1: "contrib (Suc m) ! q = block S0 (s (Suc m)) ! q" using contribS_nth1[OF mk] T by simp
  have e2: "contrib (Suc m) ! Suc q = block S0 (s (Suc m)) ! Suc q" using contribS_nth1[OF mk] T by simp
  have lb2: "Suc q < length (block S0 (s (Suc m)))" using block_decomp[OF mk] T by simp
  show ?thesis using block_link[OF sSmV lb2] e1 e2 by simp
qed

lemma contrib_nth_ne_last:
  assumes mk: "m < k" and lt: "Suc q < length (contrib (Suc m))"
  shows "contrib (Suc m) ! q \<noteq> last (contrib (Suc m))"
proof -
  have distc: "distinct (contrib (Suc m))" using contrib_distinct[of "Suc m"] mk by simp
  have lst: "last (contrib (Suc m)) = contrib (Suc m) ! (length (contrib (Suc m)) - 1)"
    using contrib_ne by (simp add: last_conv_nth)
  have i1: "q < length (contrib (Suc m))" using lt by simp
  have i2: "length (contrib (Suc m)) - 1 < length (contrib (Suc m))"
    using contrib_ne by (cases "contrib (Suc m)") auto
  have "q \<noteq> length (contrib (Suc m)) - 1" using lt by simp
  thus ?thesis using nth_eq_iff_index_eq[OF distc i1 i2] lst by simp
qed

lemma contrib_nth_ne_bef:
  assumes mk: "m < k" and lt: "Suc q < length (contrib (Suc m))" and qnj: "q \<noteq> length (defP m)"
  shows "contrib (Suc m) ! q \<noteq> bef m"
proof -
  have distc: "distinct (contrib (Suc m))" using contrib_distinct[of "Suc m"] mk by simp
  have lenC: "length (contrib (Suc m)) = Suc (length (defP m)) + length (defQ m)" by (simp add: contrib_def)
  have befj: "bef m = contrib (Suc m) ! (length (defP m))" by (rule bef_eq_contrib_junction[OF mk])
  have i1: "q < length (contrib (Suc m))" using lt by simp
  have i2: "length (defP m) < length (contrib (Suc m))" using lenC by simp
  have "contrib (Suc m) ! q \<noteq> contrib (Suc m) ! (length (defP m))"
    using nth_eq_iff_index_eq[OF distc i1 i2] qnj by simp
  thus ?thesis using befj by simp
qed

lemma contribS_false:
  assumes mk: "m < k" and lt: "Suc q < length (contrib (Suc m))"
    and F: "\<not> Suc q < Suc (length (defP m))" and nj: "Suc q \<noteq> Suc (length (defP m))"
  shows "thrd S0 (contrib (Suc m) ! q) = Some (contrib (Suc m) ! Suc q)"
proof -
  have sSmV: "s (Suc m) \<in> V" using sV[of "Suc m"] mk by simp
  have lenC: "length (contrib (Suc m)) = Suc (length (defP m)) + length (defQ m)" by (simp add: contrib_def)
  have qlp: "Suc (length (defP m)) \<le> q" using junction_index_ge[OF F nj] by auto
  have Sqlt: "Suc q < Suc (length (defP m)) + length (defQ m)" using lt[unfolded lenC] by auto
  have e1: "contrib (Suc m) ! q = block S0 (s (Suc m)) ! (q + length (block S0 (s m)))"
    using contribS_nth2 mk qlp Sqlt by auto
  have qlp': "Suc (length (defP m)) \<le> Suc q" using qlp by simp
  have e2: "contrib (Suc m) ! Suc q = block S0 (s (Suc m)) ! (Suc q + length (block S0 (s m)))"
    by (rule contribS_nth2[OF mk qlp' Sqlt])
  have lb2: "Suc (q + length (block S0 (s m))) < length (block S0 (s (Suc m)))"
    by (rule contribS_defQ_block_bound[OF mk Sqlt])
  have bl: "thrd S0 (block S0 (s (Suc m)) ! (q + length (block S0 (s m))))
        = Some (block S0 (s (Suc m)) ! Suc (q + length (block S0 (s m))))"
    by (rule block_link[OF sSmV lb2])
  show ?thesis by (rule thrd_step_transfer[OF e1 e2 bl])
qed

lemma contribS_edge:
  assumes mk: "m < k" and lt: "Suc q < length (contrib (Suc m))"
    and nj: "Suc q \<noteq> Suc (length (defP m))"
  shows "thrd S0 (contrib (Suc m) ! q) = Some (contrib (Suc m) ! Suc q)"
proof (cases "Suc q < Suc (length (defP m))")
  case True
  show ?thesis by (rule contribS_edge_pre[OF mk True])
next
  case False
  show ?thesis by (rule contribS_false[OF mk lt False nj])
qed

lemma contribS_link_fresh:
  assumes mk: "m < k" and lt: "Suc q < length (contrib (Suc m))"
    and nj: "Suc q \<noteq> Suc (length (defP m))"
  shows "final_thrd (contrib (Suc m) ! q) = Some (contrib (Suc m) ! Suc q)"
proof -
  have Smk: "Suc m \<le> k" using mk by simp
  have qnj: "q \<noteq> length (defP m)" using nj by simp
  define x where "x = contrib (Suc m) ! q"
  have xin: "x \<in> set (contrib (Suc m))" using x_def lt by (simp add: nth_mem)
  have xne: "x \<noteq> last (contrib (Suc m))" using contrib_nth_ne_last[OF mk lt] x_def by simp
  have xnb: "x \<noteq> bef m" using contrib_nth_ne_bef[OF mk lt qnj] x_def by simp
  have xlsx: "x \<notin> lsx ` {..k}" by (rule interior_notin_lsx[OF xin Smk xne])
  have xbef: "x \<notin> bef ` set [0..<k]"
  proof (rule interior_notin_bef[OF xin Smk])
    fix m' assume "m' < k" and "Suc m = Suc m'"
    hence "m' = m" by simp
    thus "x \<noteq> bef m'" using xnb by simp
  qed
  have fr: "final_thrd x = thrd S0 x" by (rule contrib_fresh[OF xin Smk xlsx xbef])
  have edge: "thrd S0 x = Some (contrib (Suc m) ! Suc q)" using contribS_edge[OF mk lt nj] x_def by simp
  show ?thesis using fr edge x_def by simp
qed

lemma contribS_link_hole:
  assumes mk: "m < k" and hj: "Suc q = Suc (length (defP m))"
    and lt: "Suc q < length (contrib (Suc m))"
  shows "final_thrd (contrib (Suc m) ! q) = Some (contrib (Suc m) ! Suc q)"
proof -
  have lenC: "length (contrib (Suc m)) = Suc (length (defP m)) + length (defQ m)" by (simp add: contrib_def)
  have defQne: "defQ m \<noteq> []" using lt lenC hj by simp
  have qh: "q = length (defP m)" using hj by simp
  have src: "contrib (Suc m) ! q = bef m" using bef_eq_contrib_junction[OF mk] qh by simp
  have cc: "contrib (Suc m) = (s (Suc m) # defP m) @ defQ m" by (simp add: contrib_def)
  have tgt: "contrib (Suc m) ! Suc q = hd (defQ m)"
    using cc hj defQne by (simp add: nth_append hd_conv_nth)
  have "final_thrd (bef m) = Some (hd (defQ m))" by (rule final_thrd_bef[OF mk defQne])
  thus ?thesis using src tgt by simp
qed

lemma contrib_internal_link:
  assumes tk: "t \<le> k" and lt: "Suc q < length (contrib t)"
  shows "final_thrd (contrib t ! q) = Some (contrib t ! Suc q)"
proof (cases t)
  case 0
  show ?thesis using contrib0_link[of q] lt 0 by simp
next
  case (Suc m)
  have mk: "m < k" using tk Suc by simp
  have lt': "Suc q < length (contrib (Suc m))" using lt Suc by simp
  show ?thesis
  proof (cases "Suc q = Suc (length (defP m))")
    case True
    show ?thesis using contribS_link_hole[OF mk True lt'] Suc by simp
  next
    case False
    show ?thesis using contribS_link_fresh[OF mk lt' False] Suc by simp
  qed
qed

lemma newblock_link:
  assumes lt: "Suc t < length newblock"
  shows "final_thrd (newblock ! t) = Some (newblock ! Suc t)"
proof -
  let ?xss = "map contrib [0..<Suc k]"
  have nb: "newblock = concat ?xss" by (simp add: newblock_def)
  have img: "set ?xss = contrib ` set [0..<Suc k]" by (simp only: set_map)
  have xssnth: "\<And>j. j < Suc k \<Longrightarrow> ?xss ! j = contrib j" by (simp add: nth_map del: upt_Suc)
  have ne: "\<And>ys. ys \<in> set ?xss \<Longrightarrow> ys \<noteq> []"
  proof -
    fix ys assume "ys \<in> set ?xss"
    then obtain t' where "ys = contrib t'" using img by auto
    thus "ys \<noteq> []" using contrib_ne by simp
  qed
  have internal: "\<And>ys q. ys \<in> set ?xss \<Longrightarrow> Suc q < length ys \<Longrightarrow> final_thrd (ys ! q) = Some (ys ! Suc q)"
  proof -
    fix ys q assume yin: "ys \<in> set ?xss" and ylt: "Suc q < length ys"
    from yin obtain t' where t'in: "t' \<in> set [0..<Suc k]" and yeq: "ys = contrib t'" using img by blast
    have t'k: "t' \<le> k" using t'in by auto
    show "final_thrd (ys ! q) = Some (ys ! Suc q)" using contrib_internal_link[OF t'k] ylt yeq by simp
  qed
  have seam: "\<And>i. Suc i < length ?xss \<Longrightarrow> final_thrd (last (?xss ! i)) = Some (hd (?xss ! Suc i))"
  proof -
    fix i assume "Suc i < length ?xss"
    hence ik: "i < k" by simp
    have e1: "?xss ! i = contrib i" using xssnth ik by simp
    have e2: "?xss ! Suc i = contrib (Suc i)" using xssnth ik by simp
    show "final_thrd (last (?xss ! i)) = Some (hd (?xss ! Suc i))"
      using contrib_seam[OF ik] e1 e2 by simp
  qed
  have lt2: "Suc t < length (concat ?xss)" using lt nb by simp
  have "final_thrd (concat ?xss ! t) = Some (concat ?xss ! Suc t)"
    by (rule concat_linked[OF ne internal seam lt2])
  thus ?thesis using nb by simp
qed

subsubsection \<open>Tree (\<open>newtree\<close>) parents of @{const newblock}: towards the DFS-step (clause J)\<close>

text \<open>Off the stem the pivot leaves the parent untouched: @{term "u \<notin> s ` {..k}"} keeps its old
      parent @{term "prnt S0 u"} (the reversal @{const REV} and the \<open>p \<mapsto> s_pred k\<close> override
      only touch stem nodes).\<close>
lemma newtree_off_stem:
  assumes "u \<notin> s ` {..k}"
  shows "((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u = prnt S0 u"
proof -
  have "\<forall>t < Suc k. u \<noteq> s t" using assms by auto
  hence "Wseq (Suc k) u = prnt S0 u" using Wseq_fresh[of "Suc k" u] by auto
  thus ?thesis using newprnt_eq by simp
qed

text \<open>On the stem the parent is reversed: for \<open>0 < t \<le> k\<close> the new parent of @{term "s t"} is
      @{term "s (t-1)"} (one step \<^emph>\<open>down\<close> the old stem), covering both the @{const REV} interior and the
      top override at @{term "p = s k"}.\<close>
lemma newtree_stem_par:
  assumes t1: "0 < t" and tk: "t \<le> k"
  shows "((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (s t) = Some (s (t-1))"
proof (cases "t = k")
  case True
  have "((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (s t) = Some (s_pred k)" using True pathk by simp
  thus ?thesis using True t1 by (simp add: s_pred_def)
next
  case False
  hence tk': "t < k" using tk by simp
  have "s t \<noteq> p" using False pathk inj tk by (metis atMost_iff order_refl inj_onD nat_less_le)
  show ?thesis using newprnt_eq \<open>s t \<noteq> p\<close> Wseq_eval[of "Suc k" t] tk t1 by (simp add: s_pred_def)
qed

text \<open>Block monotonicity along the stem: @{term "s t"} is a descendant of @{term p} (via
      @{thm stem_chain}), so its subtree sits inside @{term p}'s.\<close>
lemma block_st_sub_p:
  assumes kpos: "0 < k" and tk: "t \<le> k"
  shows "set (block S0 (s t)) \<subseteq> set (block S0 p)"
proof -
  have stV: "s t \<in> V" using sV[OF tk kpos] by auto
  have "p \<in> set (follow (prnt S0) (s t))" using stem_chain[of k t] tk pathk by simp
  hence "s t \<in> children (prnt S0) p" unfolding children_def by simp
  hence "children (prnt S0) (s t) \<subseteq> children (prnt S0) p" by (rule children_subset[OF ppt])
  thus ?thesis using block_props(4)[OF arb stV] block_props(4)[OF arb pV] by simp
qed

text \<open>The @{term t}-th contribution sits inside @{term "s t"}'s \<^emph>\<open>new\<close> subtree: every node of
      @{term "contrib t"} lies in @{term "block S0 (s t)"} but not in @{term "block S0 (s (t-1))"}
      (segment-disjointness of @{const newblock}), which is exactly @{term "s t"}'s new children-set
      (@{thm children_newprnt_i} / @{thm children_newprnt_stem}).  Hence @{term "s t"} is a new-tree
      ancestor of every @{const contrib}-@{term t} node --- the engine for the reversed-stem seams.\<close>
lemma contrib_sub_children_stem:
  assumes kpos: "0 < k" and jneq: "jn = join_of (prnt S0) i j"
    and jnp: "jn \<in> set (follow (prnt S0) p)" and pjn: "p \<noteq> jn" and tk: "t \<le> k"
  shows "set (contrib t) \<subseteq> children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (s t)"
proof
  fix u assume ut: "u \<in> set (contrib t)"
  have splitc: "concat (map contrib [0..<Suc t]) = concat (map contrib [0..<t]) @ contrib t" by simp
  have subc: "set (contrib t) \<subseteq> set (concat (map contrib [0..<Suc t]))" using splitc by auto
  have ublk_t: "u \<in> set (block S0 (s t))" using ut subc contrib_set_unroll[OF tk] by auto
  show "u \<in> children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (s t)"
  proof (cases t)
    case 0
    have "u \<in> set (block S0 p)" using ublk_t 0 block_st_sub_p[OF kpos tk] by auto
    thus ?thesis using children_newprnt_i[OF kpos] 0 path0 by simp
  next
    case (Suc t')
    have t1: "1 \<le> t" using Suc by simp
    have unotprev: "u \<notin> set (block S0 (s (t-1)))"
    proof
      assume uprev: "u \<in> set (block S0 (s (t-1)))"
      have "set (block S0 (s (t-1))) = set (concat (map contrib [0..<Suc (t-1)]))"
        using contrib_set_unroll[of "t-1"] tk by simp
      moreover have "Suc (t-1) = t" using t1 by simp
      ultimately have "u \<in> set (concat (map contrib [0..<t]))" using uprev by simp
      then obtain a where a: "a \<in> set [0..<t]" and ua: "u \<in> set (contrib a)" by auto
      have alt: "a < t" using a by simp
      have "set (contrib a) \<inter> set (contrib t) = {}" using contrib_seg_disjoint[OF alt tk] by auto
      thus False using ua ut by auto
    qed
    have "u \<in> set (block S0 p)" using ublk_t block_st_sub_p[OF kpos tk] by auto
    moreover have "children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (s t) = set (block S0 p) - set (block S0 (s (t-1)))"
      by (rule children_newprnt_stem[OF kpos jneq jnp pjn t1 tk])
    ultimately show ?thesis using unotprev by simp
  qed
qed

text \<open>The @{const newblock} \<^emph>\<open>seam\<close> DFS-step: at the junction \<open>last (contrib m) \<rightarrow> s (Suc m)\<close> the
      successor's new parent @{term "s m"} (@{thm newtree_stem_par}) is a new-tree ancestor of
      @{term "last (contrib m)"} (@{thm contrib_sub_children_stem}).  This is the reversed-stem case of
      the @{const newblock} contribution to the clause-J DFS-step.\<close>
lemma newblock_seam_dfs:
  assumes kpos: "0 < k" and jneq: "jn = join_of (prnt S0) i j"
    and jnp: "jn \<in> set (follow (prnt S0) p)" and pjn: "p \<noteq> jn" and mk: "m < k"
  shows "\<exists>a. ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (hd (contrib (Suc m))) = Some a
             \<and> a \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (last (contrib m)))"
proof -
  have hd: "hd (contrib (Suc m)) = s (Suc m)" by (simp add: contrib_def)
  have par: "((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (s (Suc m)) = Some (s m)"
    using newtree_stem_par[of "Suc m"] mk by simp
  have lastin: "last (contrib m) \<in> set (contrib m)" by (metis contrib_ne last_in_set)
  have "set (contrib m) \<subseteq> children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (s m)"
    using contrib_sub_children_stem[OF kpos jneq jnp pjn less_imp_le[OF mk]] by auto
  hence "last (contrib m) \<in> children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (s m)" using lastin by auto
  hence "s m \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (last (contrib m)))" unfolding children_def by simp
  thus ?thesis using hd par by auto
qed

text \<open>\<^bold>\<open>Off-stem ancestors are preserved by the reversal\<close>: if @{term g} is an old-tree ancestor of
      @{term x} and every node strictly between @{term x} and @{term g} on @{term x}'s old root-path is
      off the stem, then @{term g} is still a \<open>newtree\<close>-ancestor of @{term x}.  Proof: walk the old
      path from @{term x} up to @{term g}; each step is off-stem so @{thm newtree_off_stem} keeps the same
      parent, and @{const follow} rebuilds identically until @{term g}.  This is the rewiring lemma that
      transports old ancestry \<^emph>\<open>within a stem layer\<close> to the reversed tree (the internal-@{const contrib}
      case of the clause-J DFS-step, where the reversal only flips the stem spine, not the side-blocks).\<close>
lemma follow_newtree_offstem_prefix:
  shows "g \<in> set (follow (prnt S0) x) \<longrightarrow>
         (\<forall>w. w \<in> set (follow (prnt S0) x) \<longrightarrow> g \<in> set (follow (prnt S0) w) \<longrightarrow> w \<noteq> g \<longrightarrow> w \<notin> s ` {..k}) \<longrightarrow>
         g \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) x)"
proof (induction rule: parent_spec_i.follow.pinduct[OF follow_dom_ps[OF ppt, of x]])
  case (1 x)
  have psN: "parent_spec ((prnt S0 ++ REV k)(p \<mapsto> s_pred k))"
    using clauseA rooted_arborescense_invar_parent_spec by auto
  show ?case
  proof (intro impI)
    assume gx: "g \<in> set (follow (prnt S0) x)"
      and off: "\<forall>w. w \<in> set (follow (prnt S0) x) \<longrightarrow> g \<in> set (follow (prnt S0) w) \<longrightarrow> w \<noteq> g \<longrightarrow> w \<notin> s ` {..k}"
    show "g \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) x)"
    proof (cases "g = x")
      case True
      thus ?thesis using follow_hd_ps[OF psN, of x] follow_ne_ps[OF psN, of x] by (metis hd_in_set)
    next
      case False
      have xin: "x \<in> set (follow (prnt S0) x)" using follow_hd_ps[OF ppt] follow_ne_ps[OF ppt] by (metis hd_in_set)
      have xoff: "x \<notin> s ` {..k}" using off xin gx False by auto
      have "prnt S0 x \<noteq> None"
      proof
        assume "prnt S0 x = None"
        hence "follow (prnt S0) x = [x]" by (subst follow_ps_simps[OF ppt]) simp
        thus False using gx False by simp
      qed
      then obtain x' where px: "prnt S0 x = Some x'" by auto
      have fxc: "follow (prnt S0) x = x # follow (prnt S0) x'" using px by (subst follow_ps_simps[OF ppt]) simp
      have gx': "g \<in> set (follow (prnt S0) x')" using gx fxc False by simp
      have ntx: "((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) x = Some x'" using newtree_off_stem[OF xoff] px by simp
      have fNTx: "follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) x = x # follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) x'"
        using ntx by (subst follow_ps_simps[OF psN]) simp
      have offx': "\<forall>w. w \<in> set (follow (prnt S0) x') \<longrightarrow> g \<in> set (follow (prnt S0) w) \<longrightarrow> w \<noteq> g \<longrightarrow> w \<notin> s ` {..k}"
        using off fxc by auto
      have "g \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) x')"
        using 1(2)[OF px] gx' offx' by blast
      thus ?thesis using fNTx by simp
    qed
  qed
qed


text \<open>Stem ancestry orders the indices: if @{term "s a"} is an ancestor of @{term "s b"} then
      @{term "b \<le> a"} (higher stem index = higher up the old tree).\<close>
lemma stem_anc_ge:
  assumes kpos: "0 < k" and mem: "s a \<in> set (follow (prnt S0) (s b))" and ak: "a \<le> k" and bk: "b \<le> k"
  shows "b \<le> a"
proof (rule ccontr)
  assume "\<not> b \<le> a"
  hence ab: "a < b" by simp
  have "s b \<in> set (follow (prnt S0) (s a))" using stem_chain[of b a] bk ab by simp
  hence "s a = s b" using ancestor_antisym[OF ppt mem] by simp
  hence "a = b" using inj ak bk by (auto simp: inj_on_eq_iff)
  thus False using ab by simp
qed

text \<open>@{const contrib}-@{term t} nodes lie in @{term "s t"}'s subtree.\<close>
lemma contrib_in_block:
  assumes tk: "t \<le> k" and ut: "u \<in> set (contrib t)"
  shows "u \<in> set (block S0 (s t))"
proof -
  have splitc: "concat (map contrib [0..<Suc t]) = concat (map contrib [0..<t]) @ contrib t" by simp
  have "set (contrib t) \<subseteq> set (concat (map contrib [0..<Suc t]))" using splitc by auto
  thus ?thesis using ut contrib_set_unroll[OF tk] by auto
qed

text \<open>...and (for @{term "t \<ge> 1"}) not in the previous stem block --- @{const newblock} segments are
      disjoint, so each @{const contrib} sits exactly in its own stem \<^emph>\<open>layer\<close>.\<close>
lemma contrib_notin_prev:
  assumes tk: "t \<le> k" and t1: "1 \<le> t" and ut: "u \<in> set (contrib t)"
  shows "u \<notin> set (block S0 (s (t-1)))"
proof
  assume uprev: "u \<in> set (block S0 (s (t-1)))"
  have "set (block S0 (s (t-1))) = set (concat (map contrib [0..<Suc (t-1)]))"
    using contrib_set_unroll[of "t-1"] tk by simp
  moreover have "Suc (t-1) = t" using t1 by simp
  ultimately have "u \<in> set (concat (map contrib [0..<t]))" using uprev by simp
  then obtain a where a: "a \<in> set [0..<t]" and ua: "u \<in> set (contrib a)" by auto
  have alt: "a < t" using a by simp
  have "set (contrib a) \<inter> set (contrib t) = {}" using contrib_seg_disjoint[OF alt tk] by auto
  thus False using ua ut by auto
qed

text \<open>\<^bold>\<open>Internal-@{const contrib} DFS-step (fresh/old edges)\<close>: for an \<^emph>\<open>old-thread\<close> edge
      @{term "thrd S0 x = Some y"} inside one @{const contrib} (so @{term y} is off-stem), the successor's
      new parent \<open>g = prnt S0 y\<close> is a \<open>newtree\<close>-ancestor of @{term x}.  Either \<open>g = s t\<close>
      (a direct child of the stem node --- discharged by @{thm contrib_sub_children_stem}) or @{term g} is
      off-stem in the same layer, in which case the whole old path @{term "x \<dots> g"} is off-stem
      (@{thm stem_anc_ge}, @{thm block_mono}, @{thm contrib_notin_prev}) and
      @{thm follow_newtree_offstem_prefix} transports the ancestry to the reversed tree.\<close>
lemma newblock_internal_oldedge_dfs:
  assumes kpos: "0 < k" and jneq: "jn = join_of (prnt S0) i j"
    and jnp: "jn \<in> set (follow (prnt S0) p)" and pjn: "p \<noteq> jn"
    and tk: "t \<le> k" and xt: "x \<in> set (contrib t)" and yt: "y \<in> set (contrib t)"
    and yoff: "y \<notin> s ` {..k}" and edge: "thrd S0 x = Some y"
  shows "\<exists>a. ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) y = Some a
             \<and> a \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) x)"
proof -
  have stV: "s t \<in> V" using sV[OF tk kpos] by auto
  have xblk: "x \<in> set (block S0 (s t))" using contrib_in_block[OF tk xt] by auto
  have xV: "x \<in> V" using xblk block_st_sub_p[OF kpos tk] block_p_subset_V by auto
  obtain g where g: "prnt S0 y = Some g" and gfx: "g \<in> set (follow (prnt S0) x)"
    using arb_dfs_step[OF arb xV edge] by auto
  have nty: "((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) y = Some g" using newtree_off_stem[OF yoff] g by simp
  have yblk: "y \<in> set (block S0 (s t))" using contrib_in_block[OF tk yt] by auto
  have ynst: "y \<noteq> s t" using yoff tk by (metis atMost_iff imageI)
  have yfg: "follow (prnt S0) y = y # follow (prnt S0) g" using g by (subst follow_ps_simps[OF ppt]) simp
  have gfy: "g \<in> set (follow (prnt S0) y)"
    using yfg follow_hd_ps[OF ppt, of g] follow_ne_ps[OF ppt, of g] by (metis hd_in_set list.set_intros(2))
  have ychild: "y \<in> children (prnt S0) (s t)" using yblk block_props(4)[OF arb stV] by simp
  have gblk: "g \<in> set (block S0 (s t))"
  proof -
    have "s t \<in> set (follow (prnt S0) y)" using ychild unfolding children_def by simp
    hence "s t \<in> set (follow (prnt S0) g)" using yfg ynst by simp
    hence "g \<in> children (prnt S0) (s t)" unfolding children_def by simp
    thus ?thesis using block_props(4)[OF arb stV] by simp
  qed
  have gchild_st: "g \<in> children (prnt S0) (s t)" using gblk block_props(4)[OF arb stV] by simp
  show ?thesis
  proof (cases "g \<in> s ` {..k}")
    case True
    then obtain t'' where t''k: "t'' \<le> k" and gst: "g = s t''" by auto
    have mem1: "s t \<in> set (follow (prnt S0) (s t''))" using gchild_st gst unfolding children_def by simp
    have t''t: "t'' \<le> t" using stem_anc_ge[OF kpos mem1 tk t''k] by auto
    have tt'': "t \<le> t''"
    proof (rule ccontr)
      assume "\<not> t \<le> t''" hence lt: "t'' < t" by simp
      hence t1: "1 \<le> t" by simp
      have "t'' \<le> t - 1" using lt by simp
      moreover have "t - 1 \<le> k" using tk by simp
      ultimately have sub: "set (block S0 (s t'')) \<subseteq> set (block S0 (s (t-1)))" using block_mono by simp
      have "y \<in> children (prnt S0) (s t'')" using gfy gst unfolding children_def by simp
      hence "y \<in> set (block S0 (s t''))" using block_props(4)[OF arb sV[OF t''k kpos]] by simp
      hence "y \<in> set (block S0 (s (t-1)))" using sub by auto
      thus False using contrib_notin_prev[OF tk t1 yt] by simp
    qed
    have "g = s t" using gst t''t tt'' by simp
    moreover have "x \<in> children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (s t)"
      using contrib_sub_children_stem[OF kpos jneq jnp pjn tk] xt by auto
    ultimately have "g \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) x)" unfolding children_def by simp
    thus ?thesis using nty by auto
  next
    case False
    have offcond: "\<forall>w. w \<in> set (follow (prnt S0) x) \<longrightarrow> g \<in> set (follow (prnt S0) w) \<longrightarrow> w \<noteq> g \<longrightarrow> w \<notin> s ` {..k}"
    proof (intro allI impI)
      fix w assume wx: "w \<in> set (follow (prnt S0) x)" and gw: "g \<in> set (follow (prnt S0) w)" and wg: "w \<noteq> g"
      show "w \<notin> s ` {..k}"
      proof
        assume "w \<in> s ` {..k}"
        then obtain t'' where t''k: "t'' \<le> k" and wst: "w = s t''" by auto
        have wcg: "w \<in> children (prnt S0) g" using gw unfolding children_def by simp
        have "children (prnt S0) g \<subseteq> children (prnt S0) (s t)" by (rule children_subset[OF ppt gchild_st])
        hence "w \<in> set (block S0 (s t))" using wcg block_props(4)[OF arb stV] by auto
        hence "s t'' \<in> children (prnt S0) (s t)" using wst block_props(4)[OF arb stV] by simp
        hence mem2: "s t \<in> set (follow (prnt S0) (s t''))" unfolding children_def by simp
        have t''t: "t'' \<le> t" using stem_anc_ge[OF kpos mem2 tk t''k] by auto
        have xcw: "x \<in> children (prnt S0) w" using wx unfolding children_def by simp
        have tt'': "t \<le> t''"
        proof (rule ccontr)
          assume "\<not> t \<le> t''" hence lt: "t'' < t" by simp
          hence t1: "1 \<le> t" by simp
          have "t'' \<le> t - 1" using lt by simp
          moreover have "t - 1 \<le> k" using tk by simp
          ultimately have sub: "set (block S0 (s t'')) \<subseteq> set (block S0 (s (t-1)))" using block_mono by simp
          have "x \<in> set (block S0 (s t''))" using xcw wst block_props(4)[OF arb sV[OF t''k kpos]] by simp
          hence "x \<in> set (block S0 (s (t-1)))" using sub by auto
          thus False using contrib_notin_prev[OF tk t1 xt] by simp
        qed
        have wst2: "w = s t" using wst t''t tt'' by simp
        have "s t \<in> children (prnt S0) g" using wcg wst2 by simp
        hence mem3: "g \<in> set (follow (prnt S0) (s t))" unfolding children_def by simp
        have mem4: "s t \<in> set (follow (prnt S0) g)" using gchild_st unfolding children_def by simp
        have "g = s t" using ancestor_antisym[OF ppt mem3 mem4] by auto
        thus False using False tk by (metis atMost_iff imageI)
      qed
    qed
    have "g \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) x)"
      using follow_newtree_offstem_prefix[of g x] gfx offcond by auto
    thus ?thesis using nty by auto
  qed
qed

text \<open>Two ancestors of a node are comparable (a root-path is a linear order).\<close>
lemma follow_linear:
  assumes ps: "parent_spec T" and a: "a \<in> set (follow T v)" and b: "b \<in> set (follow T v)"
  shows "a \<in> set (follow T b) \<or> b \<in> set (follow T a)"
proof -
  from a obtain G H where GH: "follow T v = G @ a # H" by (meson split_list)
  have fa: "follow T a = a # H" using follow_append_ps[OF ps GH] by auto
  show ?thesis
  proof (cases "b \<in> set (a # H)")
    case True thus ?thesis using fa by simp
  next
    case False
    hence "b \<in> set G" using b GH by auto
    then obtain G1 G2 where "G = G1 @ b # G2" by (meson split_list)
    hence "follow T v = G1 @ b # (G2 @ a # H)" using GH by simp
    hence "follow T b = b # (G2 @ a # H)" using follow_append_ps[OF ps] by auto
    thus ?thesis by simp
  qed
qed

text \<open>The head of @{term "defQ m"} is a \<^emph>\<open>direct child\<close> of the stem node @{term "s (Suc m)"}: in the old
      preorder the node after @{term "s m"}'s finished block @{term "block S0 (s m)"} is the next child of
      @{term "s (Suc m)"}.  Proved via @{thm arb_dfs_step} on the old edge @{term "thrd S0 (lsuc S0 (s m))"}
      = @{term "Some (hd (defQ m))"} (@{thm out_eq_hd_defQ}): the resulting parent lies above @{term "s m"}
      but inside @{term "s (Suc m)"}'s subtree, hence equals @{term "s (Suc m)"} (@{thm ancestor_antisym}).\<close>
lemma defQ_hd_parent:
  assumes mk: "m < k" and ne: "defQ m \<noteq> []"
  shows "prnt S0 (hd (defQ m)) = Some (s (Suc m))"
proof -
  have kpos: "0 < k" using mk by simp
  have smk: "m \<le> k" using mk by simp
  have Smk: "Suc m \<le> k" using mk by simp
  have smV: "s m \<in> V" using sV[OF smk kpos] by auto
  have sSmV: "s (Suc m) \<in> V" using sV[OF Smk kpos] by auto
  define lsm where "lsm = lsuc S0 (s m)"
  have bsmne: "block S0 (s m) \<noteq> []" by (rule block_props(2)[OF arb smV])
  have lsmin: "lsm \<in> set (block S0 (s m))"
    using lsm_def block_props(3)[OF arb smV] bsmne by (metis last_in_set)
  have lsmV: "lsm \<in> V" using lsmin block_st_sub_p[OF kpos smk] block_p_subset_V by auto
  have edge: "thrd S0 lsm = Some (hd (defQ m))"
    using out_eq_hd_defQ[OF mk ne] by (simp add: out_def lsm_def)
  obtain g' where g': "prnt S0 (hd (defQ m)) = Some g'" and g'anc: "g' \<in> set (follow (prnt S0) lsm)"
    using arb_dfs_step[OF arb lsmV edge] by auto
  have dec: "block S0 (s (Suc m)) = s (Suc m) # defP m @ block S0 (s m) @ defQ m" by (rule block_decomp[OF mk])
  have hdin: "hd (defQ m) \<in> set (defQ m)" using ne by simp
  have hdSm: "hd (defQ m) \<in> set (block S0 (s (Suc m)))" using dec hdin by simp
  have distSm: "distinct (block S0 (s (Suc m)))" by (rule block_distinct_V[OF sSmV])
  have hdnotsm: "hd (defQ m) \<notin> set (block S0 (s m))" using dec distSm hdin by auto
  have fhd: "follow (prnt S0) (hd (defQ m)) = hd (defQ m) # follow (prnt S0) g'"
    using g' by (subst follow_ps_simps[OF ppt]) simp
  have hdneSm: "s (Suc m) \<noteq> hd (defQ m)" using defQ_no_stem[OF mk Smk] hdin by auto
  have g'infhd: "g' \<in> set (follow (prnt S0) (hd (defQ m)))"
    using fhd follow_hd_ps[OF ppt, of g'] follow_ne_ps[OF ppt, of g'] by (metis hd_in_set list.set_intros(2))
  have hdchild_g': "hd (defQ m) \<in> children (prnt S0) g'" using g'infhd unfolding children_def by simp
  have g'Smblk: "g' \<in> set (block S0 (s (Suc m)))"
  proof -
    have "hd (defQ m) \<in> children (prnt S0) (s (Suc m))" using hdSm block_props(4)[OF arb sSmV] by simp
    hence "s (Suc m) \<in> set (follow (prnt S0) (hd (defQ m)))" unfolding children_def by simp
    hence "s (Suc m) \<in> set (follow (prnt S0) g')" using fhd hdneSm by simp
    hence "g' \<in> children (prnt S0) (s (Suc m))" unfolding children_def by simp
    thus ?thesis using block_props(4)[OF arb sSmV] by simp
  qed
  have g'notsm: "g' \<notin> set (block S0 (s m))"
  proof
    assume "g' \<in> set (block S0 (s m))"
    hence "g' \<in> children (prnt S0) (s m)" using block_props(4)[OF arb smV] by simp
    hence "children (prnt S0) g' \<subseteq> children (prnt S0) (s m)" by (rule children_subset[OF ppt])
    hence "hd (defQ m) \<in> children (prnt S0) (s m)" using hdchild_g' by auto
    hence "hd (defQ m) \<in> set (block S0 (s m))" using block_props(4)[OF arb smV] by simp
    thus False using hdnotsm by simp
  qed
  have smanc: "s m \<in> set (follow (prnt S0) lsm)"
    using lsmin block_props(4)[OF arb smV] unfolding children_def by simp
  have smnotg': "s m \<notin> set (follow (prnt S0) g')"
  proof
    assume "s m \<in> set (follow (prnt S0) g')"
    hence "g' \<in> children (prnt S0) (s m)" unfolding children_def by simp
    hence "g' \<in> set (block S0 (s m))" using block_props(4)[OF arb smV] by simp
    thus False using g'notsm by simp
  qed
  have g'insm: "g' \<in> set (follow (prnt S0) (s m))" using follow_linear[OF ppt g'anc smanc] smnotg' by simp
  have fsm: "follow (prnt S0) (s m) = s m # follow (prnt S0) (s (Suc m))"
    using pathS[OF mk] by (subst follow_ps_simps[OF ppt]) simp
  have "s m \<in> set (block S0 (s m))" using block_props(5)[OF arb smV] bsmne by (metis hd_in_set)
  hence "g' \<noteq> s m" using g'notsm by auto
  hence g'inSsm: "g' \<in> set (follow (prnt S0) (s (Suc m)))" using g'insm fsm by simp
  have "s (Suc m) \<in> set (follow (prnt S0) g')"
    using g'Smblk block_props(4)[OF arb sSmV] unfolding children_def by simp
  hence "g' = s (Suc m)" using ancestor_antisym[OF ppt g'inSsm] by simp
  thus ?thesis using g' by simp
qed

text \<open>\<^bold>\<open>Hole-edge DFS-step\<close> (the one spliced @{const contrib} edge \<open>bef m \<rightarrow> hd (defQ m)\<close>, where the
      nested block @{term "block S0 (s m)"} was excised): the successor's new parent @{term "s (Suc m)"}
      (@{thm defQ_hd_parent}, off-stem so unchanged) is a new-tree ancestor of @{term "bef m"}
      (@{thm contrib_sub_children_stem}, since @{term "bef m \<in> set (contrib (Suc m))"}).\<close>
lemma newblock_hole_dfs:
  assumes kpos: "0 < k" and jneq: "jn = join_of (prnt S0) i j"
    and jnp: "jn \<in> set (follow (prnt S0) p)" and pjn: "p \<noteq> jn"
    and mk: "m < k" and ne: "defQ m \<noteq> []"
  shows "\<exists>a. ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (hd (defQ m)) = Some a
             \<and> a \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (bef m))"
proof -
  have Smk: "Suc m \<le> k" using mk by simp
  have hdin: "hd (defQ m) \<in> set (defQ m)" using ne by simp
  have hdoff: "hd (defQ m) \<notin> s ` {..k}"
  proof
    assume "hd (defQ m) \<in> s ` {..k}"
    then obtain t where tk: "t \<le> k" and "hd (defQ m) = s t" by auto
    thus False using defQ_no_stem[OF mk tk] hdin by simp
  qed
  have nty: "((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (hd (defQ m)) = Some (s (Suc m))"
    using newtree_off_stem[OF hdoff] defQ_hd_parent[OF mk ne] by simp
  have befin: "bef m \<in> set (contrib (Suc m))" by (rule bef_in_contrib_Suc[OF mk])
  have "bef m \<in> children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (s (Suc m))"
    using contrib_sub_children_stem[OF kpos jneq jnp pjn Smk] befin by auto
  hence "s (Suc m) \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (bef m))" unfolding children_def by simp
  thus ?thesis using nty by auto
qed

text \<open>The head of each @{const contrib} is the stem node @{term "s t"}.\<close>
lemma contrib_hd: assumes tk: "t \<le> k" shows "contrib t ! 0 = s t"
proof (cases t)
  case 0
  have c0: "contrib 0 = block S0 i" by (simp add: contrib_def)
  have "block S0 i \<noteq> []" by (rule block_props(2)[OF arb iV])
  hence "contrib 0 ! 0 = i" using c0 block_props(5)[OF arb iV] by (metis hd_conv_nth)
  thus ?thesis using 0 path0 by simp
next
  case (Suc m) thus ?thesis by (simp add: contrib_def)
qed

text \<open>The \<^emph>\<open>interior\<close> of a @{const contrib} is off the stem: the only stem node in @{term "contrib t"}
      is its head @{term "s t"} (layer argument), so any node at index @{term "0 < q"} is off-stem ---
      hence the target of any internal @{const contrib} edge is off-stem.\<close>
lemma contrib_interior_offstem:
  assumes kpos: "0 < k" and tk: "t \<le> k" and q0: "0 < q" and qlt: "q < length (contrib t)"
  shows "contrib t ! q \<notin> s ` {..k}"
proof
  assume "contrib t ! q \<in> s ` {..k}"
  then obtain t'' where t''k: "t'' \<le> k" and eq: "contrib t ! q = s t''" by auto
  have mem: "contrib t ! q \<in> set (contrib t)" using qlt by (simp add: nth_mem)
  have stt''in: "s t'' \<in> set (contrib t)" using mem eq by simp
  have inblk: "s t'' \<in> set (block S0 (s t))" using contrib_in_block[OF tk stt''in] by auto
  have stV: "s t \<in> V" using sV[OF tk kpos] by auto
  have st''V: "s t'' \<in> V" using sV[OF t''k kpos] by auto
  have "s t'' \<in> children (prnt S0) (s t)" using inblk block_props(4)[OF arb stV] by simp
  hence memf: "s t \<in> set (follow (prnt S0) (s t''))" unfolding children_def by simp
  have t''t: "t'' \<le> t" using stem_anc_ge[OF kpos memf tk t''k] by auto
  have tt'': "t \<le> t''"
  proof (cases "t = 0")
    case True thus ?thesis by simp
  next
    case False hence t1: "1 \<le> t" by simp
    show ?thesis
    proof (rule ccontr)
      assume "\<not> t \<le> t''" hence lt: "t'' < t" by simp
      have "t'' \<le> t - 1" using lt by simp
      moreover have "t - 1 \<le> k" using tk by simp
      ultimately have "set (block S0 (s t'')) \<subseteq> set (block S0 (s (t-1)))" using block_mono by simp
      moreover have "s t'' \<in> set (block S0 (s t''))"
        using block_props(5)[OF arb st''V] block_props(2)[OF arb st''V] by (metis hd_in_set)
      ultimately have "s t'' \<in> set (block S0 (s (t-1)))" by auto
      thus False using contrib_notin_prev[OF tk t1 stt''in] by simp
    qed
  qed
  have "t'' = t" using t''t tt'' by simp
  hence eq0: "contrib t ! q = contrib t ! 0" using eq contrib_hd[OF tk] by simp
  have "0 < length (contrib t)" using contrib_ne by simp
  hence "q = 0" using eq0 contrib_distinct[OF tk] qlt by (metis nth_eq_iff_index_eq)
  thus False using q0 by simp
qed

text \<open>\<^bold>\<open>Internal-@{const contrib} DFS-step\<close> (all edges inside one @{const contrib}): mirrors
      @{thm contrib_internal_link} --- the @{term "t = 0"} block and the fresh @{term "Suc m"} edges are
      old-thread edges (@{thm block_link} / @{thm contribS_edge}) discharged by
      @{thm newblock_internal_oldedge_dfs}, and the single hole edge by @{thm newblock_hole_dfs}.\<close>
lemma contrib_internal_dfs:
  assumes kpos: "0 < k" and jneq: "jn = join_of (prnt S0) i j"
    and jnp: "jn \<in> set (follow (prnt S0) p)" and pjn: "p \<noteq> jn"
    and tk: "t \<le> k" and lt: "Suc q < length (contrib t)"
  shows "\<exists>a. ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (contrib t ! Suc q) = Some a
             \<and> a \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (contrib t ! q))"
proof -
  have srcin: "contrib t ! q \<in> set (contrib t)" using lt by (simp add: nth_mem)
  have tgtin: "contrib t ! Suc q \<in> set (contrib t)" using lt by (simp add: nth_mem)
  have tgtoff: "contrib t ! Suc q \<notin> s ` {..k}" using contrib_interior_offstem[OF kpos tk zero_less_Suc lt] by auto
  show ?thesis
  proof (cases t)
    case 0
    have c0: "contrib 0 = block S0 i" by (simp add: contrib_def)
    have ltb: "Suc q < length (block S0 i)" using lt 0 c0 by simp
    have edge: "thrd S0 (contrib t ! q) = Some (contrib t ! Suc q)"
      using block_link[OF iV ltb] c0 0 by simp
    show ?thesis by (rule newblock_internal_oldedge_dfs[OF kpos jneq jnp pjn tk srcin tgtin tgtoff edge])
  next
    case (Suc m)
    have mk: "m < k" using tk Suc by simp
    have lt': "Suc q < length (contrib (Suc m))" using lt Suc by simp
    show ?thesis
    proof (cases "Suc q = Suc (length (defP m))")
      case True
      have lenC: "length (contrib (Suc m)) = Suc (length (defP m)) + length (defQ m)" by (simp add: contrib_def)
      have defQne: "defQ m \<noteq> []" using lt' lenC True by simp
      have qh: "q = length (defP m)" using True by simp
      have src: "contrib t ! q = bef m" using Suc bef_eq_contrib_junction[OF mk] qh by simp
      have cc: "contrib (Suc m) = (s (Suc m) # defP m) @ defQ m" by (simp add: contrib_def)
      have tgt: "contrib t ! Suc q = hd (defQ m)"
      proof -
        have "contrib (Suc m) ! Suc q = ((s (Suc m) # defP m) @ defQ m) ! (length (s (Suc m) # defP m))"
          using cc True by simp
        also have "\<dots> = defQ m ! 0" by (simp add: nth_append)
        also have "\<dots> = hd (defQ m)" using defQne by (simp add: hd_conv_nth)
        finally show ?thesis using Suc by simp
      qed
      show ?thesis using newblock_hole_dfs[OF kpos jneq jnp pjn mk defQne] src tgt by simp
    next
      case False
      have edge: "thrd S0 (contrib (Suc m) ! q) = Some (contrib (Suc m) ! Suc q)"
        using contribS_edge[OF mk lt' False] by auto
      have tk': "Suc m \<le> k" using mk by simp
      have edge2: "thrd S0 (contrib t ! q) = Some (contrib t ! Suc q)" using edge Suc by simp
      show ?thesis by (rule newblock_internal_oldedge_dfs[OF kpos jneq jnp pjn tk srcin tgtin tgtoff edge2])
    qed
  qed
qed

text \<open>Generic assembly (the DFS-step twin of @{thm concat_linked}): a per-list internal DFS-step plus a
      per-junction seam DFS-step give the DFS-step of the whole @{const concat}.  Same induction as
      @{thm concat_linked}.\<close>
lemma concat_dfs:
  assumes ne: "\<And>ys. ys \<in> set xss \<Longrightarrow> ys \<noteq> []"
    and internal: "\<And>ys q. ys \<in> set xss \<Longrightarrow> Suc q < length ys \<Longrightarrow>
        \<exists>a. F (ys ! Suc q) = Some a \<and> a \<in> set (follow F (ys ! q))"
    and seam: "\<And>i. Suc i < length xss \<Longrightarrow>
        \<exists>a. F (hd (xss ! Suc i)) = Some a \<and> a \<in> set (follow F (last (xss ! i)))"
    and lt: "Suc t < length (concat xss)"
  shows "\<exists>a. F (concat xss ! Suc t) = Some a \<and> a \<in> set (follow F (concat xss ! t))"
  using ne internal seam lt
proof (induction xss arbitrary: t)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  have xne: "x \<noteq> []" using Cons.prems(1) by simp
  let ?n = "length x"
  show ?case
  proof (cases "Suc t < ?n")
    case True
    have "\<exists>a. F (x ! Suc t) = Some a \<and> a \<in> set (follow F (x ! t))"
      using Cons.prems(2)[of x t] True by simp
    moreover have "(x @ concat xs) ! t = x ! t" using True by (simp add: nth_append)
    moreover have "(x @ concat xs) ! Suc t = x ! Suc t" using True by (simp add: nth_append)
    ultimately show ?thesis by simp
  next
    case False
    show ?thesis
    proof (cases "t < ?n")
      case True
      have tn: "Suc t = ?n" using True False by simp
      have te: "length x - 1 = t" using tn by simp
      have xsne: "concat xs \<noteq> []" using Cons.prems(4) tn by simp
      then obtain y ys' where xs2: "xs = y # ys'" and yne: "y \<noteq> []"
        using Cons.prems(1) by (cases xs) auto
      have s0: "\<exists>a. F (hd (xs ! 0)) = Some a \<and> a \<in> set (follow F (last x))"
        using Cons.prems(3)[of 0] xs2 by simp
      have lastx: "(x @ concat xs) ! t = last x"
        using True te xne by (simp add: nth_append last_conv_nth)
      have hdc: "(x @ concat xs) ! Suc t = hd (concat xs)"
        using tn xsne by (simp add: nth_append hd_conv_nth)
      have "hd (concat xs) = hd (xs ! 0)" using xs2 yne by simp
      thus ?thesis using lastx hdc s0 by simp
    next
      case False
      hence nt: "?n \<le> t" by simp
      obtain d where d: "t = ?n + d" using nt le_Suc_ex by auto
      have e1: "(x @ concat xs) ! t = concat xs ! d" using d by (simp add: nth_append)
      have e2: "(x @ concat xs) ! Suc t = concat xs ! Suc d" using d by (simp add: nth_append)
      have ltd: "Suc d < length (concat xs)" using Cons.prems(4) d by simp
      have IH: "\<exists>a. F (concat xs ! Suc d) = Some a \<and> a \<in> set (follow F (concat xs ! d))"
      proof (rule Cons.IH)
        show "\<And>ys. ys \<in> set xs \<Longrightarrow> ys \<noteq> []" using Cons.prems(1) by simp
        show "\<And>ys q. ys \<in> set xs \<Longrightarrow> Suc q < length ys \<Longrightarrow> \<exists>a. F (ys ! Suc q) = Some a \<and> a \<in> set (follow F (ys ! q))"
          using Cons.prems(2) by simp
        fix i assume "Suc i < length xs"
        thus "\<exists>a. F (hd (xs ! Suc i)) = Some a \<and> a \<in> set (follow F (last (xs ! i)))"
          using Cons.prems(3)[of "Suc i"] by simp
      next
        show "Suc d < length (concat xs)" using ltd by auto
      qed
      show ?thesis using e1 e2 IH by simp
    qed
  qed
qed

text \<open>\<^bold>\<open>The @{const newblock} DFS-step\<close>: every internal @{const newblock} edge realises the DFS-step of
      the new tree \<open>newtree\<close> (the reversed-stem block is a preorder of @{term i}'s new subtree).  Assembles the
      per-@{const contrib} internal step (@{thm contrib_internal_dfs}) and the reversed-stem seams
      (@{thm newblock_seam_dfs}) via @{thm concat_dfs}.\<close>
lemma newblock_dfs:
  assumes kpos: "0 < k" and jneq: "jn = join_of (prnt S0) i j"
    and jnp: "jn \<in> set (follow (prnt S0) p)" and pjn: "p \<noteq> jn"
    and lt: "Suc t < length newblock"
  shows "\<exists>a. ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (newblock ! Suc t) = Some a
             \<and> a \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (newblock ! t))"
proof -
  let ?xss = "map contrib [0..<Suc k]"
  have nb: "newblock = concat ?xss" by (simp add: newblock_def)
  have xssnth: "\<And>idx. idx < Suc k \<Longrightarrow> ?xss ! idx = contrib idx" by (simp add: nth_map del: upt_Suc)
  have lenxss: "length ?xss = Suc k" by simp
  have ne: "\<And>ys. ys \<in> set ?xss \<Longrightarrow> ys \<noteq> []"
  proof -
    fix ys assume "ys \<in> set ?xss"
    then obtain idx where idxlt: "idx < length ?xss" and yeq2: "?xss ! idx = ys" by (metis in_set_conv_nth)
    have "ys = contrib idx" using yeq2 idxlt lenxss xssnth by simp
    thus "ys \<noteq> []" using contrib_ne by simp
  qed
  have internal: "\<And>ys q. ys \<in> set ?xss \<Longrightarrow> Suc q < length ys \<Longrightarrow>
      \<exists>a. ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (ys ! Suc q) = Some a
        \<and> a \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (ys ! q))"
  proof -
    fix ys q assume yin: "ys \<in> set ?xss" and lq: "Suc q < length ys"
    from yin obtain idx where idxlt: "idx < length ?xss" and yeq2: "?xss ! idx = ys" by (metis in_set_conv_nth)
    have idxk: "idx \<le> k" using idxlt lenxss by simp
    have yeq: "ys = contrib idx" using yeq2 idxlt lenxss xssnth by simp
    show "\<exists>a. ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (ys ! Suc q) = Some a
        \<and> a \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (ys ! q))"
      using contrib_internal_dfs[OF kpos jneq jnp pjn idxk] lq yeq by simp
  qed
  have seam: "\<And>i. Suc i < length ?xss \<Longrightarrow>
      \<exists>a. ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (hd (?xss ! Suc i)) = Some a
        \<and> a \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (last (?xss ! i)))"
  proof -
    fix i assume "Suc i < length ?xss"
    hence ik: "i < k" using lenxss by simp
    have e1: "?xss ! i = contrib i" using ik xssnth by simp
    have e2: "?xss ! Suc i = contrib (Suc i)" using ik xssnth by simp
    show "\<exists>a. ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (hd (?xss ! Suc i)) = Some a
        \<and> a \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (last (?xss ! i)))"
      using newblock_seam_dfs[OF kpos jneq jnp pjn ik] e1 e2 by simp
  qed
  have lt2: "Suc t < length (concat ?xss)" using lt nb by simp
  show ?thesis unfolding nb by (rule concat_dfs[OF ne internal seam lt2])
qed

text \<open>Engine hypotheses for clause J: the new tree's root has no parent, and every subtree stays in V.\<close>
lemma newtree_r_None:
  assumes kpos: "0 < k"
  shows "((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) r = None"
proof -
  have rns: "r \<notin> s ` {..k}" by (rule r_notin_stem[OF kpos])
  have "((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) r = prnt S0 r" by (rule newtree_off_stem[OF rns])
  moreover have "rooted_arborescense_invar r V (prnt S0)" using arb unfolding arb_invar_def by simp
  hence "dom (prnt S0) = V - {r}" by (rule rooted_arborescense_invar_dom)
  hence "prnt S0 r = None" by auto
  ultimately show ?thesis by simp
qed

lemma children_newtree_subset_V:
  assumes vV: "v \<in> V"
  shows "children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v \<subseteq> V"
proof
  fix u assume "u \<in> children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v"
  hence vfu: "v \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u)" unfolding children_def by simp
  have rinvN: "rooted_arborescense_invar r V ((prnt S0 ++ REV k)(p \<mapsto> s_pred k))" by (rule clauseA)
  have psN: "parent_spec ((prnt S0 ++ REV k)(p \<mapsto> s_pred k))" using rinvN rooted_arborescense_invar_parent_spec by auto
  show "u \<in> V"
  proof (rule ccontr)
    assume "u \<notin> V"
    hence "u \<notin> dom ((prnt S0 ++ REV k)(p \<mapsto> s_pred k))" using rooted_arborescense_invar_dom[OF rinvN] by auto
    hence "((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u = None" by auto
    hence "follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u = [u]" by (subst follow_ps_simps[OF psN]) simp
    hence "v = u" using vfu by simp
    thus False using vV \<open>u \<notin> V\<close> by simp
  qed
qed

lemma follow_last_None:
  assumes ps: "parent_spec T" shows "T (last (follow T v)) = None"
proof -
  have ne: "follow T v \<noteq> []" by (rule follow_ne_ps[OF ps])
  obtain pfx where fv: "follow T v = pfx @ last (follow T v) # []"
    using ne by (metis append_butlast_last_id)
  have "follow T (last (follow T v)) = last (follow T v) # []"
    by (rule follow_append_ps[OF ps fv])
  moreover have "follow T (last (follow T v))
    = (case T (last (follow T v)) of None \<Rightarrow> [last (follow T v)] | Some w \<Rightarrow> last (follow T v) # follow T w)"
    by (rule follow_ps_simps[OF ps])
  ultimately have "(case T (last (follow T v)) of None \<Rightarrow> [last (follow T v)] | Some w \<Rightarrow> last (follow T v) # follow T w) = [last (follow T v)]"
    by simp
  thus ?thesis using follow_ne_ps[OF ps] by (auto split: option.splits)
qed

lemma final_thrd_lsx_k:
  assumes kpos: "0 < k"
  shows "final_thrd (lsx k) = (if the (rvth S0 p) = j then thrd S0 (lsuc S0 p) else thrd S0 j)"
proof -
  have inblk: "lsx k \<in> set (block S0 p)" using lsx_in_block_p[of k] kpos by simp
  have ne_or: "lsx k \<noteq> the (rvth S0 p)" using inblk old_rev_notin_block_p by auto
  show ?thesis
    unfolding final_thrd_def Let_def
    using ne_or by (auto split: option.split)
qed

lemma tail_seam:
  assumes kpos: "0 < k" and TLne: "tl (dropWhile (\<lambda>x. x \<noteq> j) holed) \<noteq> []"
  shows "final_thrd (lsx k) = Some (hd (tl (dropWhile (\<lambda>x. x \<noteq> j) holed)))"
proof -
  define TW where "TW = takeWhile (\<lambda>x. x \<noteq> j) holed"
  define TL where "TL = tl (dropWhile (\<lambda>x. x \<noteq> j) holed)"
  have hsplit: "holed = TW @ j # TL" using holed_split TW_def TL_def by simp
  have TLne': "TL \<noteq> []" using TLne TL_def by simp
  have idxj: "holed ! (length TW) = j" using hsplit by (simp add: nth_append)
  have idxT: "holed ! Suc (length TW) = hd TL" using hsplit TLne' by (simp add: nth_append hd_conv_nth)
  have lenlt: "Suc (length TW) < length holed" using hsplit TLne' by simp
  have main: "final_thrd (lsx k) = Some (hd TL)"
  proof (cases "the (rvth S0 p) = j")
    case True
    have fj: "final_thrd (lsx k) = thrd S0 (lsuc S0 p)" using final_thrd_lsx_k[OF kpos] True by simp
    have jla: "j = last alpha" using old_rev_last_alpha True by simp
    have alne: "alpha \<noteq> []" by (rule alpha_ne)
    have aform: "alpha = butlast alpha @ [j]" using jla alne by (metis append_butlast_last_id)
    have distH: "distinct holed" by (rule holed_distinct)
    have hform: "holed = butlast alpha @ [j] @ beta" using holed_def aform by simp
    have allbl: "\<forall>x\<in>set (butlast alpha). x \<noteq> j"
    proof -
      have "distinct (butlast alpha @ [j] @ beta)" using distH hform by simp
      thus ?thesis by auto
    qed
    have dw: "dropWhile (\<lambda>x. x \<noteq> j) holed = j # beta"
      using hform allbl by (simp add: dropWhile_append2)
    have TLb: "TL = beta" using TL_def dw by simp
    have bne: "beta \<noteq> []" using TLne' TLb by simp
    have bhd: "aftn k = Some (hd beta)" by (rule beta_out[OF bne])
    have "thrd S0 (lsuc S0 p) = Some (hd beta)" using bhd by (simp add: aftn_def out_def pathk)
    thus ?thesis using fj TLb by simp
  next
    case False
    have fj: "final_thrd (lsx k) = thrd S0 j" using final_thrd_lsx_k[OF kpos] False by simp
    have "thrd S0 (holed ! (length TW)) = Some (holed ! Suc (length TW))"
      using holed_old_adj[OF lenlt] idxj False by simp
    thus ?thesis using fj idxj idxT by simp
  qed
  show ?thesis using main by (simp add: TL_def)
qed

lemma newblock_split_last: "newblock = concat (map contrib [0..<k]) @ contrib k"
proof -
  have sp: "[0..<Suc k] = [0..<k] @ [k]" by simp
  show ?thesis by (simp add: newblock_def sp)
qed

lemma newblock_ne: "newblock \<noteq> []"
  using newblock_split_last contrib_ne by (metis append_is_Nil_conv)

lemma last_newblock: "last newblock = lsx k"
proof -
  have "last newblock = last (contrib k)" using newblock_split_last contrib_ne by simp
  thus ?thesis using lsx_last_contrib[of k] by simp
qed

lemma nl_len: "length newlist = length (takeWhile (\<lambda>x. x \<noteq> j) holed) + 1 + length newblock + length (tl (dropWhile (\<lambda>x. x \<noteq> j) holed))"
  by (simp add: newlist_def)

lemma holed_len: "length holed = length (takeWhile (\<lambda>x. x \<noteq> j) holed) + 1 + length (tl (dropWhile (\<lambda>x. x \<noteq> j) holed))"
proof -
  have "length holed = length (takeWhile (\<lambda>x. x \<noteq> j) holed @ j # tl (dropWhile (\<lambda>x. x \<noteq> j) holed))"
    using holed_split by simp
  thus ?thesis by simp
qed

lemma nl_hd_region:
  assumes "a < length (takeWhile (\<lambda>x. x \<noteq> j) holed)"
  shows "newlist ! a = holed ! a"
proof -
  have "newlist ! a = takeWhile (\<lambda>x. x \<noteq> j) holed ! a" using assms by (simp add: newlist_def nth_append)
  moreover have "holed ! a = takeWhile (\<lambda>x. x \<noteq> j) holed ! a"
    using assms by (subst holed_split) (simp add: nth_append)
  ultimately show ?thesis by simp
qed

lemma nl_j: "newlist ! (length (takeWhile (\<lambda>x. x \<noteq> j) holed)) = j"
  by (simp add: newlist_def nth_append)

lemma nl_nb:
  assumes "d < length newblock"
  shows "newlist ! (length (takeWhile (\<lambda>x. x \<noteq> j) holed) + 1 + d) = newblock ! d"
  using assms by (simp add: newlist_def nth_append)

lemma nl_tl:
  assumes "c < length (tl (dropWhile (\<lambda>x. x \<noteq> j) holed))"
  shows "newlist ! (length (takeWhile (\<lambda>x. x \<noteq> j) holed) + 1 + length newblock + c) = holed ! (length (takeWhile (\<lambda>x. x \<noteq> j) holed) + 1 + c)"
proof -
  have "newlist ! (length (takeWhile (\<lambda>x. x \<noteq> j) holed) + 1 + length newblock + c) = tl (dropWhile (\<lambda>x. x \<noteq> j) holed) ! c"
    using assms by (simp add: newlist_def nth_append)
  moreover have "holed ! (length (takeWhile (\<lambda>x. x \<noteq> j) holed) + 1 + c) = tl (dropWhile (\<lambda>x. x \<noteq> j) holed) ! c"
    using assms by (subst holed_split) (simp add: nth_append)
  ultimately show ?thesis by simp
qed

lemma holed_j_pos: "holed ! (length (takeWhile (\<lambda>x. x \<noteq> j) holed)) = j"
  by (subst holed_split) (simp add: nth_append)

lemma holed_ne_j_off:
  assumes lt: "t < length holed" and off: "t \<noteq> length (takeWhile (\<lambda>x. x \<noteq> j) holed)"
  shows "holed ! t \<noteq> j"
proof
  assume "holed ! t = j"
  hence "holed ! t = holed ! (length (takeWhile (\<lambda>x. x \<noteq> j) holed))" using holed_j_pos by simp
  moreover have "length (takeWhile (\<lambda>x. x \<noteq> j) holed) < length holed" using holed_len by simp
  ultimately have "t = length (takeWhile (\<lambda>x. x \<noteq> j) holed)"
    using holed_distinct lt by (simp add: nth_eq_iff_index_eq)
  thus False using off by simp
qed

lemma nl_le_n1:
  assumes "a \<le> length (takeWhile (\<lambda>x. x \<noteq> j) holed)"
  shows "newlist ! a = holed ! a"
proof (cases "a < length (takeWhile (\<lambda>x. x \<noteq> j) holed)")
  case True thus ?thesis by (rule nl_hd_region)
next
  case False
  hence "a = length (takeWhile (\<lambda>x. x \<noteq> j) holed)" using assms by simp
  thus ?thesis using nl_j holed_j_pos by simp
qed

lemma holed_TL_nth:
  assumes "c < length (tl (dropWhile (\<lambda>x. x \<noteq> j) holed))"
  shows "holed ! (length (takeWhile (\<lambda>x. x \<noteq> j) holed) + 1 + c) = tl (dropWhile (\<lambda>x. x \<noteq> j) holed) ! c"
  using assms by (subst holed_split) (simp add: nth_append)

lemma newlist_link:
  assumes kpos: "0 < k" and lt: "Suc t < length newlist"
  shows "final_thrd (newlist ! t) = Some (newlist ! Suc t)"
proof -
  let ?n1 = "length (takeWhile (\<lambda>x. x \<noteq> j) holed)"
  let ?nb = "length newblock"
  let ?TL = "tl (dropWhile (\<lambda>x. x \<noteq> j) holed)"
  have hlen: "length holed = ?n1 + 1 + length ?TL" by (rule holed_len)
  have nllen: "length newlist = ?n1 + 1 + ?nb + length ?TL" by (rule nl_len)
  have nbpos: "0 < ?nb" using newblock_ne by auto
  consider (TW) "t < ?n1" | (J) "t = ?n1" | (NB) "?n1 < t" "t < ?n1 + ?nb"
    | (SEAM) "t = ?n1 + ?nb" | (TL) "?n1 + ?nb < t"
    by linarith
  then show ?thesis
  proof cases
    case TW
    have s: "newlist ! t = holed ! t" using nl_le_n1 TW by simp
    have tgt: "newlist ! Suc t = holed ! Suc t" using nl_le_n1 TW by simp
    have sjt: "Suc t < length holed" using TW hlen by simp
    have nej: "holed ! t \<noteq> j" using holed_ne_j_off TW hlen by simp
    show ?thesis using holed_adj_final[OF sjt nej kpos] s tgt by simp
  next
    case J
    have s: "newlist ! t = j" using nl_j J by simp
    have tgt: "newlist ! Suc t = i" using J nl_nb[of 0] nbpos newblock_ne hd_newblock by (simp add: hd_conv_nth)
    have lk: "lsx k \<noteq> j" using lsx_in_block_p[of k] kpos j_notin_block_p by auto
    have "final_thrd j = thrd_inv k j" using lk by (simp add: final_thrd_def Let_def split: option.split)
    also have "\<dots> = Some i" using thrd_inv_j[OF kpos] by auto
    finally show ?thesis using s tgt by simp
  next
    case NB
    obtain d where td: "t = ?n1 + 1 + d" using NB(1) less_imp_Suc_add by fastforce
    have dnb: "Suc d < ?nb" using NB(2) td by simp
    have s: "newlist ! t = newblock ! d" using nl_nb[of d] dnb td by simp
    have tgt: "newlist ! Suc t = newblock ! Suc d" using td nl_nb[of "Suc d"] dnb by simp
    show ?thesis using newblock_link[of d] dnb s tgt by simp
  next
    case SEAM
    have TLpos: "0 < length ?TL" using lt nllen SEAM by linarith
    have TLne: "?TL \<noteq> []" using TLpos by (cases "?TL") auto
    obtain nb' where nbeq: "?nb = Suc nb'" using newblock_ne by (cases "?nb") auto
    have td: "t = ?n1 + 1 + nb'" using SEAM nbeq by simp
    have s: "newlist ! t = lsx k"
    proof -
      have "newlist ! t = newblock ! nb'" using nl_nb[of nb'] nbeq td by simp
      also have "\<dots> = last newblock" using nbeq newblock_ne by (simp add: last_conv_nth)
      also have "\<dots> = lsx k" by (rule last_newblock)
      finally show ?thesis .
    qed
    have E1: "newlist ! Suc t = newlist ! (?n1 + 1 + ?nb + 0)" using SEAM by simp
    have E2: "newlist ! (?n1 + 1 + ?nb + 0) = holed ! (?n1 + 1 + 0)" by (rule nl_tl[OF TLpos])
    have E3: "holed ! (?n1 + 1 + 0) = ?TL ! 0" by (rule holed_TL_nth[OF TLpos])
    have E4: "?TL ! 0 = hd ?TL" using TLne by (simp add: hd_conv_nth)
    have tgt: "newlist ! Suc t = hd ?TL" using E1 E2 E3 E4 by simp
    show ?thesis using tail_seam[OF kpos TLne] s tgt by simp
  next
    case TL
    define c where "c = t - (?n1 + 1 + ?nb)"
    have tc: "t = ?n1 + 1 + ?nb + c" using TL c_def by simp
    have clt: "c < length ?TL" using lt nllen tc by linarith
    have c1lt: "Suc c < length ?TL" using lt nllen tc by linarith
    have s: "newlist ! t = holed ! (?n1 + 1 + c)" using nl_tl[OF clt] tc by simp
    have E1: "newlist ! Suc t = newlist ! (?n1 + 1 + ?nb + Suc c)" using tc by simp
    have E2: "newlist ! (?n1 + 1 + ?nb + Suc c) = holed ! (?n1 + 1 + Suc c)" by (rule nl_tl[OF c1lt])
    have tgt: "newlist ! Suc t = holed ! Suc (?n1 + 1 + c)" using E1 E2 by simp
    have idxlt: "?n1 + 1 + c < length holed" using hlen clt by simp
    have sjt: "Suc (?n1 + 1 + c) < length holed" using hlen c1lt by simp
    have off: "?n1 + 1 + c \<noteq> ?n1" by simp
    have nej: "holed ! (?n1 + 1 + c) \<noteq> j" by (rule holed_ne_j_off[OF idxlt off])
    show ?thesis using holed_adj_final[OF sjt nej kpos] s tgt by simp
  qed
qed

lemma last_follow_thrd0_None: "thrd S0 (last (follow (thrd S0) r)) = None"
proof -
  have pst: "parent_spec (thrd S0)" using arb unfolding arb_invar_def by simp
  show ?thesis by (rule follow_last_None[OF pst])
qed

lemma thrd_lsuc_p_None_of_beta_nil:
  assumes "beta = []" shows "thrd S0 (lsuc S0 p) = None"
proof -
  have "follow (thrd S0) r = alpha @ block S0 p" using oldlist_split_eq assms by simp
  hence "last (follow (thrd S0) r) = last (block S0 p)" using block_props(2)[OF arb pV] by simp
  also have "\<dots> = lsuc S0 p" using block_props(3)[OF arb pV] by simp
  finally have "last (follow (thrd S0) r) = lsuc S0 p" .
  thus ?thesis using last_follow_thrd0_None by simp
qed

lemma thrd_last_beta_None:
  assumes bne: "beta \<noteq> []" shows "thrd S0 (last beta) = None"
proof -
  have "follow (thrd S0) r = (alpha @ block S0 p) @ beta" using oldlist_split_eq by simp
  hence "last (follow (thrd S0) r) = last beta" using bne by simp
  thus ?thesis using last_follow_thrd0_None by simp
qed

lemma last_newlist_nil:
  assumes "tl (dropWhile (\<lambda>x. x \<noteq> j) holed) = []"
  shows "last newlist = lsx k"
proof -
  have "newlist = takeWhile (\<lambda>x. x \<noteq> j) holed @ j # newblock" using assms by (simp add: newlist_def)
  hence "last newlist = last (j # newblock)" by simp
  also have "\<dots> = last newblock" using newblock_ne by simp
  finally show ?thesis using last_newblock by simp
qed

lemma last_newlist_TL:
  assumes TLne: "tl (dropWhile (\<lambda>x. x \<noteq> j) holed) \<noteq> []"
  shows "last newlist = last holed"
proof -
  have "last newlist = last (tl (dropWhile (\<lambda>x. x \<noteq> j) holed))" using TLne by (simp add: newlist_def)
  moreover have "last holed = last (tl (dropWhile (\<lambda>x. x \<noteq> j) holed))" using TLne by (subst holed_split) simp
  ultimately show ?thesis by simp
qed

lemma last_holed_nil: "tl (dropWhile (\<lambda>x. x \<noteq> j) holed) = [] \<Longrightarrow> last holed = j"
  by (subst holed_split) simp

lemma last_holed_ne_j:
  assumes TLne: "tl (dropWhile (\<lambda>x. x \<noteq> j) holed) \<noteq> []"
  shows "last holed \<noteq> j"
proof -
  have hne: "holed \<noteq> []" using holed_split by (metis Nil_is_append_conv list.distinct(1))
  have lidx: "last holed = holed ! (length holed - 1)" using hne by (simp add: last_conv_nth)
  have "length (takeWhile (\<lambda>x. x \<noteq> j) holed) < length holed - 1"
    using holed_len TLne by (cases "tl (dropWhile (\<lambda>x. x \<noteq> j) holed)") auto
  hence off: "length holed - 1 \<noteq> length (takeWhile (\<lambda>x. x \<noteq> j) holed)" by simp
  have lt: "length holed - 1 < length holed" using hne by (cases holed) auto
  show ?thesis using holed_ne_j_off[OF lt off] lidx by simp
qed

lemma last_holed_beta: "beta \<noteq> [] \<Longrightarrow> last holed = last beta"
  by (simp add: holed_def)

lemma last_holed_old_rev: "beta = [] \<Longrightarrow> last holed = the (rvth S0 p)"
  using old_rev_last_alpha alpha_ne by (simp add: holed_def)

lemma aftn_eq_thrd_lsuc_p: "aftn k = thrd S0 (lsuc S0 p)"
  by (simp add: aftn_def out_def pathk)

lemma alpha_beta_disjoint: "set alpha \<inter> set beta = {}"
proof -
  have "distinct (alpha @ block S0 p @ beta)" using oldlist_distinct oldlist_split_eq by simp
  thus ?thesis by auto
qed

lemma set_beta_holed: "set beta \<subseteq> set holed"
  by (simp add: holed_def)

lemma newlist_last_None:
  assumes kpos: "0 < k"
  shows "final_thrd (last newlist) = None"
proof (cases "tl (dropWhile (\<lambda>x. x \<noteq> j) holed) = []")
  case True
  have lnl: "last newlist = lsx k" by (rule last_newlist_nil[OF True])
  have jlast: "last holed = j" by (rule last_holed_nil[OF True])
  have tc: "final_thrd (lsx k) = (if the (rvth S0 p) = j then thrd S0 (lsuc S0 p) else thrd S0 j)"
    by (rule final_thrd_lsx_k[OF kpos])
  show ?thesis
  proof (cases "beta = []")
    case True
    have "the (rvth S0 p) = j" using last_holed_old_rev[OF True] jlast by simp
    hence "final_thrd (lsx k) = thrd S0 (lsuc S0 p)" using tc by simp
    also have "\<dots> = None" using thrd_lsuc_p_None_of_beta_nil[OF True] by simp
    finally show ?thesis using lnl by simp
  next
    case False
    have jb: "j = last beta" using last_holed_beta[OF False] jlast by simp
    have orne: "the (rvth S0 p) \<noteq> j"
    proof
      assume "the (rvth S0 p) = j"
      hence "j = last alpha" using old_rev_last_alpha by simp
      hence "j \<in> set alpha" using alpha_ne by (metis last_in_set)
      moreover have "j \<in> set beta" using jb False by (metis last_in_set)
      ultimately show False using alpha_beta_disjoint by auto
    qed
    have "final_thrd (lsx k) = thrd S0 j" using tc orne by simp
    also have "\<dots> = thrd S0 (last beta)" using jb by simp
    also have "\<dots> = None" using thrd_last_beta_None[OF False] by simp
    finally show ?thesis using lnl by simp
  qed
next
  case False
  have lnl: "last newlist = last holed" by (rule last_newlist_TL[OF False])
  have znej: "last holed \<noteq> j" by (rule last_holed_ne_j[OF False])
  show ?thesis
  proof (cases "beta = []")
    case True
    have zor: "last holed = the (rvth S0 p)" by (rule last_holed_old_rev[OF True])
    have orne: "the (rvth S0 p) \<noteq> j" using zor znej by simp
    have "final_thrd (the (rvth S0 p)) = aftn k" by (rule final_thrd_oldrev[OF orne])
    also have "\<dots> = thrd S0 (lsuc S0 p)" by (rule aftn_eq_thrd_lsuc_p)
    also have "\<dots> = None" using thrd_lsuc_p_None_of_beta_nil[OF True] by simp
    finally show ?thesis using lnl zor by simp
  next
    case False
    have zb: "last holed = last beta" by (rule last_holed_beta[OF False])
    have zin: "last holed \<in> set holed" using zb set_beta_holed False by (metis last_in_set subsetD)
    have zor: "last holed \<noteq> the (rvth S0 p)"
    proof -
      have "the (rvth S0 p) = last alpha" by (rule old_rev_last_alpha)
      hence "the (rvth S0 p) \<in> set alpha" using alpha_ne by (metis last_in_set)
      moreover have "last holed \<in> set beta" using zb False by (metis last_in_set)
      ultimately show ?thesis using alpha_beta_disjoint by auto
    qed
    have "final_thrd (last holed) = thrd S0 (last holed)" by (rule holed_fresh[OF zin znej zor kpos])
    also have "\<dots> = thrd S0 (last beta)" using zb by simp
    also have "\<dots> = None" using thrd_last_beta_None[OF False] by simp
    finally show ?thesis using lnl by simp
  qed
qed

lemma old_rev_in_V: "the (rvth S0 p) \<in> V"
proof -
  have "the (rvth S0 p) = last alpha" by (rule old_rev_last_alpha)
  moreover have "last alpha \<in> set alpha" using alpha_ne by (metis last_in_set)
  ultimately have "the (rvth S0 p) \<in> set alpha" by simp
  moreover have "set alpha \<subseteq> V" using oldlist_split_eq oldlist_set_V by auto
  ultimately show ?thesis by auto
qed

lemma final_thrd_dom_V:
  assumes kpos: "0 < k" and xnV: "x \<notin> V" shows "final_thrd x = None"
proof -
  have xlk: "x \<noteq> lsx k" using lsx_in_block_p[of k] kpos block_p_subset_V xnV by auto
  have xor: "x \<noteq> the (rvth S0 p)" using old_rev_in_V xnV by auto
  have e1: "final_thrd x = thrd_inv k x" using final_thrd_off[OF xlk xor] by auto
  have xlsx: "x \<notin> lsx ` set [0..<k]"
  proof
    assume "x \<in> lsx ` set [0..<k]"
    then obtain t where "t < k" "x = lsx t" by auto
    thus False using lsx_in_block_p[of t] kpos block_p_subset_V xnV by auto
  qed
  have xbef: "x \<notin> bef ` set [0..<k]"
  proof
    assume "x \<in> bef ` set [0..<k]"
    then obtain t where "t < k" "x = bef t" by auto
    thus False using bef_in_block_p[of t] block_p_subset_V xnV by auto
  qed
  have xj: "x \<noteq> j" using jV xnV by auto
  have e2: "thrd_inv k x = thrd S0 x" using thrd_inv_eval_fresh[OF xlsx xbef xj] by auto
  have "dom (thrd S0) = V - {lsuc S0 r}" using arb unfolding arb_invar_def by simp
  hence "x \<notin> dom (thrd S0)" using xnV by auto
  hence "thrd S0 x = None" by auto
  thus ?thesis using e1 e2 by simp
qed

lemma final_thrd_reverse_chain:
  assumes kpos: "0 < k" and xy: "final_thrd x = Some y"
  shows "\<exists>i. Suc i < length newlist \<and> newlist ! i = x \<and> newlist ! Suc i = y"
proof -
  have xV: "x \<in> V" using final_thrd_dom_V[OF kpos] xy by (cases "x \<in> V") auto
  have "x \<in> set newlist" using xV set_newlist by simp
  then obtain i where ile: "i < length newlist" and xi: "newlist ! i = x" by (metis in_set_conv_nth)
  show ?thesis
  proof (cases "Suc i < length newlist")
    case True
    have "final_thrd (newlist ! i) = Some (newlist ! Suc i)" by (rule newlist_link[OF kpos True])
    hence "y = newlist ! Suc i" using xi xy by simp
    thus ?thesis using True xi by auto
  next
    case False
    hence "i = length newlist - 1" using ile by simp
    hence "newlist ! i = last newlist" using newlist_ne ile by (simp add: last_conv_nth)
    hence "final_thrd x = None" using xi newlist_last_None[OF kpos] by simp
    thus ?thesis using xy by simp
  qed
qed

lemma parent_spec_final_thrd:
  assumes kpos: "0 < k" shows "parent_spec final_thrd"
proof (rule parent_spec_of_distinct_chain[OF distinct_newlist])
  fix x y assume "final_thrd x = Some y"
  thus "\<exists>i. Suc i < length newlist \<and> newlist ! i = x \<and> newlist ! Suc i = y"
    by (rule final_thrd_reverse_chain[OF kpos])
qed

text \<open>Clause B of @{const arb_invar} for @{const update_tree}: the new thread is a
      valid parent map (well-founded / acyclic).  Immediate from @{thm update_tree_thrd}
      rewriting @{term "thrd (update_tree S0 i j p jn)"} to @{const final_thrd} and
      @{thm parent_spec_final_thrd}.\<close>
lemma clauseB:
  assumes kpos: "0 < k"
  shows "parent_spec (thrd (update_tree S0 i j p jn))"
  using update_tree_thrd[OF kpos] parent_spec_final_thrd[OF kpos] by simp

lemma out_edge:
  assumes kpos: "0 < k" shows "follow final_thrd r = newlist"
proof -
  have ps: "parent_spec final_thrd" by (rule parent_spec_final_thrd[OF kpos])
  have "follow final_thrd (hd newlist) = newlist"
    by (rule follow_eq_of_chain[OF ps newlist_ne newlist_link[OF kpos] newlist_last_None[OF kpos]])
  thus ?thesis using hd_newlist by simp
qed

subsubsection \<open>The @{const newlist} DFS-step and the contiguity half of clause J\<close>

lemma stem_in_block:
  assumes kpos: "0 < k" and tk: "t \<le> k" shows "s t \<in> set (block S0 p)"
proof -
  have "p \<in> set (follow (prnt S0) (s t))" using stem_chain[of k t] tk pathk by simp
  hence "s t \<in> children (prnt S0) p" unfolding children_def by simp
  thus ?thesis using block_props(4)[OF arb pV] by simp
qed

lemma off_block_off_stem:
  assumes kpos: "0 < k" and unb: "u \<notin> set (block S0 p)" shows "u \<notin> s ` {..k}"
proof
  assume "u \<in> s ` {..k}"
  then obtain t where tk: "t \<le> k" and "u = s t" by auto
  thus False using stem_in_block[OF kpos tk] unb by auto
qed

text \<open>The excision splice: @{term "hd beta"}'s new parent is an ancestor of the block's thread-predecessor
      @{term "the (rvth S0 p)"}.  Two @{thm arb_dfs_step} applications + @{thm follow_linear} + @{thm follow_sub_of_mem}.\<close>
lemma splice_dfs:
  assumes bne: "beta \<noteq> []"
  shows "\<exists>g. prnt S0 (hd beta) = Some g \<and> g \<in> set (follow (prnt S0) (the (rvth S0 p)))"
proof -
  have G: "\<forall>v v'. thrd S0 v = Some v' \<longleftrightarrow> rvth S0 v' = Some v" using arb unfolding arb_invar_def by simp
  have domrv: "dom (rvth S0) = V - {r}" using arb unfolding arb_invar_def by simp
  have lspin: "lsuc S0 p \<in> set (block S0 p)"
    using block_props(3)[OF arb pV] block_props(2)[OF arb pV] by (metis last_in_set)
  have lspV: "lsuc S0 p \<in> V" using lspin block_p_subset_V by auto
  have edge1: "thrd S0 (lsuc S0 p) = Some (hd beta)" using beta_out[OF bne] by (simp add: aftn_def out_def pathk)
  obtain g where g: "prnt S0 (hd beta) = Some g" and gfl: "g \<in> set (follow (prnt S0) (lsuc S0 p))"
    using arb_dfs_step[OF arb lspV edge1] by auto
  have fhb: "follow (prnt S0) (hd beta) = hd beta # follow (prnt S0) g" using g by (subst follow_ps_simps[OF ppt]) simp
  have gselfp: "g \<in> set (follow (prnt S0) g)" using follow_hd_ps[OF ppt, of g] follow_ne_ps[OF ppt, of g] by (metis hd_in_set)
  have hbcg: "hd beta \<in> children (prnt S0) g" using gselfp fhb unfolding children_def by simp
  have hbin: "hd beta \<in> set beta" using bne by simp
  have hbnb: "hd beta \<notin> set (block S0 p)" using hbin set_beta_holed holed_set by auto
  have gnb: "g \<notin> set (block S0 p)"
  proof
    assume "g \<in> set (block S0 p)"
    hence "g \<in> children (prnt S0) p" using block_props(4)[OF arb pV] by simp
    hence "children (prnt S0) g \<subseteq> children (prnt S0) p" by (rule children_subset[OF ppt])
    hence "hd beta \<in> children (prnt S0) p" using hbcg by auto
    hence "hd beta \<in> set (block S0 p)" using block_props(4)[OF arb pV] by simp
    thus False using hbnb by simp
  qed
  have pfl: "p \<in> set (follow (prnt S0) (lsuc S0 p))" using lspin block_props(4)[OF arb pV] unfolding children_def by simp
  have gfp: "g \<in> set (follow (prnt S0) p)"
  proof -
    have "g \<in> set (follow (prnt S0) p) \<or> p \<in> set (follow (prnt S0) g)"
      using follow_linear[OF ppt gfl pfl] by auto
    moreover have "p \<notin> set (follow (prnt S0) g)"
    proof
      assume "p \<in> set (follow (prnt S0) g)"
      hence "g \<in> children (prnt S0) p" unfolding children_def by simp
      hence "g \<in> set (block S0 p)" using block_props(4)[OF arb pV] by simp
      thus False using gnb by simp
    qed
    ultimately show ?thesis by simp
  qed
  have gnep: "g \<noteq> p" using gnb block_props(5)[OF arb pV] block_props(2)[OF arb pV] by (metis hd_in_set)
  obtain pp where pp: "prnt S0 p = Some pp" and ppfl: "pp \<in> set (follow (prnt S0) (the (rvth S0 p)))"
  proof -
    have pdom: "p \<in> dom (rvth S0)" using domrv pV pne_r by simp
    then obtain w where w: "rvth S0 p = Some w" by auto
    hence wthe: "the (rvth S0 p) = w" by simp
    have edge2: "thrd S0 w = Some p" using G w by auto
    have wV: "w \<in> V" using w wthe old_rev_in_V by simp
    obtain pp where "prnt S0 p = Some pp" and "pp \<in> set (follow (prnt S0) w)"
      using arb_dfs_step[OF arb wV edge2] by auto
    thus ?thesis using that wthe by simp
  qed
  have "g \<in> set (follow (prnt S0) pp)" using gfp pp gnep by (subst (asm) follow_ps_simps[OF ppt, of p]) simp
  hence "g \<in> set (follow (prnt S0) (the (rvth S0 p)))" using follow_sub_of_mem[OF ppt ppfl] by auto
  thus ?thesis using g by auto
qed

text \<open>DFS-step for consecutive @{const holed} nodes (both off-block): old-thread edges via
      @{thm holed_old_adj}+@{thm arb_dfs_step}; the junction via @{thm splice_dfs}.\<close>
lemma holed_dfs:
  assumes kpos: "0 < k" and lt: "Suc t' < length holed"
  shows "\<exists>a. ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (holed ! Suc t') = Some a
             \<and> a \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (holed ! t'))"
proof -
  have srcin: "holed ! t' \<in> set holed" using lt by (simp add: nth_mem)
  have tgtin: "holed ! Suc t' \<in> set holed" using lt by (simp add: nth_mem)
  have srcnb: "holed ! t' \<notin> set (block S0 p)" using srcin holed_set by auto
  have tgtnb: "holed ! Suc t' \<notin> set (block S0 p)" using tgtin holed_set by auto
  have tgtoff: "holed ! Suc t' \<notin> s ` {..k}" using tgtnb off_block_off_stem[OF kpos] by simp
  have ntt: "((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (holed ! Suc t') = prnt S0 (holed ! Suc t')"
    by (rule newtree_off_stem[OF tgtoff])
  have flsrc: "follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (holed ! t') = follow (prnt S0) (holed ! t')"
    by (rule follow_newprnt_off_block[OF kpos srcnb])
  show ?thesis
  proof (cases "holed ! t' = the (rvth S0 p)")
    case False
    have edge: "thrd S0 (holed ! t') = Some (holed ! Suc t')" using holed_old_adj[OF lt] False by simp
    have srcV: "holed ! t' \<in> V" using srcin holed_set by auto
    obtain a where a: "prnt S0 (holed ! Suc t') = Some a" and afl: "a \<in> set (follow (prnt S0) (holed ! t'))"
      using arb_dfs_step[OF arb srcV edge] by auto
    show ?thesis using ntt a afl flsrc by auto
  next
    case True
    have hd: "holed = alpha @ beta" unfolding holed_def by simp
    have lh: "length holed = length alpha + length beta" using hd by simp
    have la1: "length alpha - 1 < length holed" using alpha_ne lh by (cases "length alpha") auto
    have idx_or: "alpha ! (length alpha - 1) = last alpha" using alpha_ne by (simp add: last_conv_nth)
    have hor: "holed ! (length alpha - 1) = the (rvth S0 p)" using hd alpha_ne old_rev_last_alpha idx_or by (simp add: nth_append)
    have "holed ! t' = holed ! (length alpha - 1)" using True hor by simp
    hence teq: "t' = length alpha - 1" using holed_distinct lt la1 by (metis Suc_lessD nth_eq_iff_index_eq)
    have Suct: "Suc t' = length alpha" using teq alpha_ne by simp
    have bne: "beta \<noteq> []" using lt lh Suct by (cases beta) auto
    have "holed ! Suc t' = beta ! 0" using hd Suct by (simp add: nth_append)
    hence hb: "holed ! Suc t' = hd beta" using bne by (simp add: hd_conv_nth)
    obtain g where g: "prnt S0 (hd beta) = Some g" and gfl: "g \<in> set (follow (prnt S0) (the (rvth S0 p)))"
      using splice_dfs[OF bne] by auto
    show ?thesis using ntt hb g gfl flsrc True by auto
  qed
qed

lemma newtree_i:
  assumes kpos: "0 < k"
  shows "((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) i = Some j"
proof -
  have inep: "i \<noteq> p" using inep_aux[OF kpos] by auto
  show ?thesis using inep newprnt_eq inep path0 Wseq_eval[of "Suc k" 0] by (simp add: s_pred_def)
qed

text \<open>@{term j} lies on @{term "lsx k"}'s new root-path (through @{term i}): the SEAM node's parent lands here.\<close>
lemma j_in_follow_newtree_lsxk:
  assumes kpos: "0 < k"
  shows "j \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (lsx k))"
proof -
  have lsxblk: "lsx k \<in> set (block S0 p)" using lsx_in_block_p[of k] kpos by simp
  have psN: "parent_spec ((prnt S0 ++ REV k)(p \<mapsto> s_pred k))" using clauseA rooted_arborescense_invar_parent_spec by auto
  have ifl: "i \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (lsx k))"
    using block_p_under_i[OF kpos] lsxblk by auto
  have "follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) i = i # follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) j"
    using newtree_i[OF kpos] by (subst follow_ps_simps[OF psN]) simp
  hence "j \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) i)"
    using follow_hd_ps[OF psN, of j] follow_ne_ps[OF psN, of j] by (metis hd_in_set list.set_intros(2))
  moreover have "set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) i) \<subseteq> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (lsx k))"
    using follow_sub_of_mem[OF psN ifl] by auto
  ultimately show ?thesis by auto
qed

text \<open>\<^bold>\<open>The @{const newlist} DFS-step\<close>: the whole pivot output list is a preorder of the new tree.  Five
      regions (mirror @{thm newlist_link}): TW/TL via @{thm holed_dfs}, J via @{thm newtree_i}, NB via
      @{thm newblock_dfs}, SEAM via @{thm holed_dfs}+@{thm j_in_follow_newtree_lsxk}.\<close>
lemma newlist_dfs:
  assumes kpos: "0 < k" and jneq: "jn = join_of (prnt S0) i j"
    and jnp: "jn \<in> set (follow (prnt S0) p)" and pjn: "p \<noteq> jn"
    and lt: "Suc t < length newlist"
  shows "\<exists>a. ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (newlist ! Suc t) = Some a
             \<and> a \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (newlist ! t))"
proof -
  let ?n1 = "length (takeWhile (\<lambda>x. x \<noteq> j) holed)"
  let ?nb = "length newblock"
  let ?TL = "tl (dropWhile (\<lambda>x. x \<noteq> j) holed)"
  have psN: "parent_spec ((prnt S0 ++ REV k)(p \<mapsto> s_pred k))" using clauseA rooted_arborescense_invar_parent_spec by auto
  have hlen: "length holed = ?n1 + 1 + length ?TL" by (rule holed_len)
  have nllen: "length newlist = ?n1 + 1 + ?nb + length ?TL" by (rule nl_len)
  have nbpos: "0 < ?nb" using newblock_ne by auto
  consider (TW) "t < ?n1" | (J) "t = ?n1" | (NB) "?n1 < t" "t < ?n1 + ?nb"
    | (SEAM) "t = ?n1 + ?nb" | (TL) "?n1 + ?nb < t" by linarith
  then show ?thesis
  proof cases
    case TW
    have s: "newlist ! t = holed ! t" using nl_le_n1 TW by simp
    have tgt: "newlist ! Suc t = holed ! Suc t" using nl_le_n1 TW by simp
    have sjt: "Suc t < length holed" using TW hlen by simp
    show ?thesis using holed_dfs[OF kpos sjt] s tgt by simp
  next
    case J
    have s: "newlist ! t = j" using nl_j J by simp
    have tgt: "newlist ! Suc t = i" using J nl_nb[of 0] nbpos newblock_ne hd_newblock by (simp add: hd_conv_nth)
    have jfollow: "j \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) j)"
      using follow_hd_ps[OF psN, of j] follow_ne_ps[OF psN, of j] by (metis hd_in_set)
    show ?thesis using newtree_i[OF kpos] jfollow s tgt by auto
  next
    case NB
    obtain d where td: "t = ?n1 + 1 + d" using NB(1) less_imp_Suc_add by fastforce
    have dnb: "Suc d < ?nb" using NB(2) td by simp
    have s: "newlist ! t = newblock ! d" using nl_nb[of d] dnb td by simp
    have tgt: "newlist ! Suc t = newblock ! Suc d" using td nl_nb[of "Suc d"] dnb by simp
    show ?thesis using newblock_dfs[OF kpos jneq jnp pjn dnb] s tgt by simp
  next
    case SEAM
    have TLpos: "0 < length ?TL" using lt nllen SEAM by linarith
    have TLne: "?TL \<noteq> []" using TLpos by (cases "?TL") auto
    obtain nb' where nbeq: "?nb = Suc nb'" using newblock_ne by (cases "?nb") auto
    have td: "t = ?n1 + 1 + nb'" using SEAM nbeq by simp
    have s: "newlist ! t = lsx k"
    proof -
      have "newlist ! t = newblock ! nb'" using nl_nb[of nb'] nbeq td by simp
      also have "\<dots> = last newblock" using nbeq newblock_ne by (simp add: last_conv_nth)
      also have "\<dots> = lsx k" by (rule last_newblock)
      finally show ?thesis .
    qed
    have E1: "newlist ! Suc t = newlist ! (?n1 + 1 + ?nb + 0)" using SEAM by simp
    have E2: "newlist ! (?n1 + 1 + ?nb + 0) = holed ! (?n1 + 1 + 0)" by (rule nl_tl[OF TLpos])
    have E3: "holed ! (?n1 + 1 + 0) = ?TL ! 0" by (rule holed_TL_nth[OF TLpos])
    have E4: "?TL ! 0 = hd ?TL" using TLne by (simp add: hd_conv_nth)
    have tgt: "newlist ! Suc t = hd ?TL" using E1 E2 E3 E4 by simp
    have jpos: "holed ! ?n1 = j" by (rule holed_j_pos)
    have holedhdTL: "holed ! Suc ?n1 = hd ?TL"
    proof -
      have "holed ! Suc ?n1 = holed ! (?n1 + 1 + 0)" by simp
      also have "\<dots> = ?TL ! 0" by (rule holed_TL_nth[OF TLpos])
      also have "\<dots> = hd ?TL" using E4 by simp
      finally show ?thesis .
    qed
    have sjt: "Suc ?n1 < length holed" using hlen TLpos by simp
    obtain a where a: "((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (holed ! Suc ?n1) = Some a"
      and afl: "a \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (holed ! ?n1))"
      using holed_dfs[OF kpos sjt] by auto
    have "a \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) j)" using afl jpos by simp
    moreover have "set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) j) \<subseteq> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (lsx k))"
      using follow_sub_of_mem[OF psN j_in_follow_newtree_lsxk[OF kpos]] by auto
    ultimately have afl2: "a \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (lsx k))" by auto
    show ?thesis using a holedhdTL tgt s afl2 by auto
  next
    case TL
    define c where "c = t - (?n1 + 1 + ?nb)"
    have tc: "t = ?n1 + 1 + ?nb + c" using TL c_def by simp
    have clt: "c < length ?TL" using lt nllen tc by linarith
    have c1lt: "Suc c < length ?TL" using lt nllen tc by linarith
    have s: "newlist ! t = holed ! (?n1 + 1 + c)" using nl_tl[OF clt] tc by simp
    have E1: "newlist ! Suc t = newlist ! (?n1 + 1 + ?nb + Suc c)" using tc by simp
    have E2: "newlist ! (?n1 + 1 + ?nb + Suc c) = holed ! (?n1 + 1 + Suc c)" by (rule nl_tl[OF c1lt])
    have tgt: "newlist ! Suc t = holed ! Suc (?n1 + 1 + c)" using E1 E2 by simp
    have sjt: "Suc (?n1 + 1 + c) < length holed" using hlen c1lt by simp
    show ?thesis using holed_dfs[OF kpos sjt] s tgt by simp
  qed
qed

text \<open>\<^bold>\<open>Clause J, contiguity half\<close>: for every @{term "v \<in> V"} the new thread reaches @{term v}'s new
      subtree as a non-empty contiguous prefix headed by @{term v}.  Immediate from @{thm preorder_contiguous}
      once its hypotheses are discharged (@{thm parent_spec_final_thrd}, @{thm out_edge}, @{thm newtree_r_None},
      @{thm newlist_dfs}, @{thm set_newlist}, @{thm children_newtree_subset_V}).\<close>
lemma clauseJ_contig:
  assumes kpos: "0 < k" and jneq: "jn = join_of (prnt S0) i j"
    and jnp: "jn \<in> set (follow (prnt S0) p)" and pjn: "p \<noteq> jn" and vV: "v \<in> V"
  shows "\<exists>pre suf. follow (thrd (update_tree S0 i j p jn)) v = pre @ suf
           \<and> set pre = children (prnt (update_tree S0 i j p jn)) v \<and> pre \<noteq> [] \<and> hd pre = v"
proof -
  have psN: "parent_spec ((prnt S0 ++ REV k)(p \<mapsto> s_pred k))" using clauseA rooted_arborescense_invar_parent_spec by auto
  have psF: "parent_spec final_thrd" by (rule parent_spec_final_thrd[OF kpos])
  have oe: "follow final_thrd r = newlist" by (rule out_edge[OF kpos])
  have root0: "((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (newlist ! 0) = None"
  proof -
    have "newlist ! 0 = r" using hd_newlist newlist_ne by (simp add: hd_conv_nth)
    thus ?thesis using newtree_r_None[OF kpos] by simp
  qed
  have dfs: "\<And>t. Suc t < length newlist \<Longrightarrow> \<exists>a. ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (newlist ! Suc t) = Some a \<and> a \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (newlist ! t))"
    using newlist_dfs[OF kpos jneq jnp pjn] by auto
  have vin: "v \<in> set newlist" using vV set_newlist by simp
  have subv: "children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v \<subseteq> set newlist"
    using children_newtree_subset_V[OF vV] set_newlist by simp
  obtain pre suf where
    P1: "follow final_thrd v = pre @ suf"
    and P2: "set pre = children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v"
    and P3: "pre \<noteq> []" and P4: "hd pre = v"
    using preorder_contiguous[OF psN psF oe root0 dfs vin subv] by auto
  have ft: "thrd (update_tree S0 i j p jn) = final_thrd" by (rule update_tree_thrd[OF kpos])
  have pt: "prnt (update_tree S0 i j p jn) = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)" by (rule update_tree_prnt[OF kpos])
  show ?thesis using P1 P2 P3 P4 by (auto simp: ft pt)
qed

text \<open>\<^bold>\<open>Clause J assembly\<close>: the full clause J follows from the contiguity half
      (@{thm clauseJ_contig}) and the pointwise \<open>lsuc = last block\<close> property (hypothesis @{text lsuc_last}).
      The continuation matches because @{term "follow (thrd (update_tree S0 i j p jn)) v = pre @ suf"} is a
      thread chain: if @{term "suf = []"} then @{thm follow_last_None} gives @{text "thrd (last pre) = None"},
      else @{thm thread_link} gives @{text "thrd (last pre) = Some (hd suf)"} and @{thm follow_append_ps}
      that @{term suf} is the follow-list of @{term "hd suf"}.  Reduces clause J to the single remaining
      obligation @{text lsuc_last}.\<close>
lemma clauseJ_from_lsuc:
  assumes kpos: "0 < k" and jneq: "jn = join_of (prnt S0) i j"
    and jnp: "jn \<in> set (follow (prnt S0) p)" and pjn: "p \<noteq> jn"
    and lsuc_last: "\<And>v pre suf. v \<in> V \<Longrightarrow> follow (thrd (update_tree S0 i j p jn)) v = pre @ suf
        \<Longrightarrow> set pre = children (prnt (update_tree S0 i j p jn)) v \<Longrightarrow> pre \<noteq> [] \<Longrightarrow> hd pre = v
        \<Longrightarrow> lsuc (update_tree S0 i j p jn) v = last pre"
  shows "\<forall>v\<in>V. \<exists>pre. follow (thrd (update_tree S0 i j p jn)) v
           = pre @ (case thrd (update_tree S0 i j p jn) (lsuc (update_tree S0 i j p jn) v) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd (update_tree S0 i j p jn)) w)
           \<and> pre \<noteq> [] \<and> last pre = lsuc (update_tree S0 i j p jn) v \<and> set pre = children (prnt (update_tree S0 i j p jn)) v"
proof -
  define S5 where S5d: "S5 = update_tree S0 i j p jn"
  have psF: "parent_spec (thrd S5)" unfolding S5d by (rule clauseB[OF kpos])
  have contig: "\<And>v. v \<in> V \<Longrightarrow> \<exists>pre suf. follow (thrd S5) v = pre @ suf \<and> set pre = children (prnt S5) v \<and> pre \<noteq> [] \<and> hd pre = v"
    unfolding S5d using clauseJ_contig[OF kpos jneq jnp pjn] by auto
  have lsl0: "\<And>v pre suf. v \<in> V \<Longrightarrow> follow (thrd S5) v = pre @ suf \<Longrightarrow> set pre = children (prnt S5) v \<Longrightarrow> pre \<noteq> [] \<Longrightarrow> hd pre = v \<Longrightarrow> lsuc S5 v = last pre"
    unfolding S5d using lsuc_last by auto
  have main: "\<forall>v\<in>V. \<exists>pre. follow (thrd S5) v = pre @ (case thrd S5 (lsuc S5 v) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd S5) w)
             \<and> pre \<noteq> [] \<and> last pre = lsuc S5 v \<and> set pre = children (prnt S5) v"
  proof
    fix v assume vV: "v \<in> V"
    obtain pre suf where P1: "follow (thrd S5) v = pre @ suf" and P2: "set pre = children (prnt S5) v"
      and P3: "pre \<noteq> []" and P4: "hd pre = v" using contig[OF vV] by blast
    have lsl: "lsuc S5 v = last pre" using lsl0[OF vV P1 P2 P3 P4] by auto
    have cont: "(case thrd S5 (lsuc S5 v) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd S5) w) = suf"
    proof (cases suf)
      case Nil
      have fv: "follow (thrd S5) v = pre" using P1 Nil by simp
      have "thrd S5 (last pre) = None" using follow_last_None[OF psF, of v] fv by simp
      thus ?thesis using lsl Nil by simp
    next
      case (Cons y ys)
      have P1c: "follow (thrd S5) v = pre @ y # ys" using P1 Cons by simp
      have pe: "pre = butlast pre @ [last pre]" using append_butlast_last_id[OF P3] by simp
      have "pre @ y # ys = butlast pre @ last pre # y # ys" by (subst pe) simp
      hence split: "follow (thrd S5) v = butlast pre @ last pre # y # ys" using P1c by simp
      have edge: "thrd S5 (last pre) = Some y" using thread_link[OF psF split] by auto
      have "follow (thrd S5) y = y # ys" by (rule follow_append_ps[OF psF P1c])
      hence "follow (thrd S5) y = suf" using Cons by simp
      thus ?thesis using edge lsl by simp
    qed
    have g1: "follow (thrd S5) v = pre @ (case thrd S5 (lsuc S5 v) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd S5) w)" using P1 cont by simp
    show "\<exists>pre. follow (thrd S5) v = pre @ (case thrd S5 (lsuc S5 v) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd S5) w)
             \<and> pre \<noteq> [] \<and> last pre = lsuc S5 v \<and> set pre = children (prnt S5) v"
    proof (intro exI[of _ pre] conjI)
      show "follow (thrd S5) v = pre @ (case thrd S5 (lsuc S5 v) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd S5) w)" by (rule g1)
      show "pre \<noteq> []" by (rule P3)
      show "last pre = lsuc S5 v" by (rule lsl[symmetric])
      show "set pre = children (prnt S5) v" by (rule P2)
    qed
  qed
  show ?thesis by (rule main[unfolded S5d])
qed

text \<open>Clause D of @{const arb_invar} for @{const update_tree}: following the new thread from the root
      enumerates all of @{term V}.  @{thm update_tree_thrd} rewrites to @{const final_thrd},
      @{thm out_edge} gives @{term "follow final_thrd r = newlist"}, and @{thm set_newlist} that its
      set is @{term V}.\<close>
lemma clauseD:
  assumes kpos: "0 < k"
  shows "set (follow (thrd (update_tree S0 i j p jn)) r) = V"
  using update_tree_thrd[OF kpos] out_edge[OF kpos] set_newlist by simp

lemma dom_final_thrd:
  assumes kpos: "0 < k" shows "dom final_thrd = V - {last newlist}"
proof
  show "dom final_thrd \<subseteq> V - {last newlist}"
  proof
    fix x assume "x \<in> dom final_thrd"
    then obtain y where xy: "final_thrd x = Some y" by auto
    have xV: "x \<in> V" using final_thrd_dom_V[OF kpos] xy by (cases "x \<in> V") auto
    moreover have "x \<noteq> last newlist" using xy newlist_last_None[OF kpos] by auto
    ultimately show "x \<in> V - {last newlist}" by simp
  qed
next
  show "V - {last newlist} \<subseteq> dom final_thrd"
  proof
    fix x assume "x \<in> V - {last newlist}"
    hence xV: "x \<in> V" and xne: "x \<noteq> last newlist" by auto
    have "x \<in> set newlist" using xV set_newlist by simp
    then obtain i where ile: "i < length newlist" and xi: "newlist ! i = x"
      by (metis in_set_conv_nth)
    have "Suc i < length newlist"
    proof (rule ccontr)
      assume "\<not> Suc i < length newlist"
      hence "i = length newlist - 1" using ile by simp
      hence "x = last newlist" using xi newlist_ne ile by (simp add: last_conv_nth)
      thus False using xne by simp
    qed
    hence "final_thrd (newlist ! i) = Some (newlist ! Suc i)" by (rule newlist_link[OF kpos])
    thus "x \<in> dom final_thrd" using xi by auto
  qed
qed

text \<open>Domain of the new thread as a corollary for @{const update_tree} (clause E up to identifying
      @{term "lsuc (update_tree S0 i j p jn) r"} with @{term "last newlist"}).\<close>
lemma dom_thrd_update_tree:
  assumes kpos: "0 < k"
  shows "dom (thrd (update_tree S0 i j p jn)) = V - {last newlist}"
  using update_tree_thrd[OF kpos] dom_final_thrd[OF kpos] by simp

text \<open>The root sits on the IN-chain (the run of ancestors of @{term j} whose old last descendant is
      @{term j}) iff @{term j} was the root's old last descendant --- the rightmost-spine
      characterisation (@{thm spine_lemma}), the entry point of the clause-E case split.\<close>
lemma r_in_INchain_iff:
  "(r \<in> set (takeWhile (\<lambda>y. lsuc S0 y = j) (follow (prnt S0) j))) = (lsuc S0 r = j)"
proof
  assume "r \<in> set (takeWhile (\<lambda>y. lsuc S0 y = j) (follow (prnt S0) j))"
  thus "lsuc S0 r = j" using takeWhile_holds by fastforce
next
  assume L0j: "lsuc S0 r = j"
  have rinv: "rooted_arborescense_invar r V (prnt S0)" using arb unfolding arb_invar_def by simp
  have rV: "r \<in> V"
  proof -
    have "set (follow (thrd S0) r) = V" using arb unfolding arb_invar_def by simp
    moreover have "r \<in> set (follow (thrd S0) r)"
      using follow_hd_ps[OF pst, of r] follow_ne_ps[OF pst, of r] by (metis hd_in_set)
    ultimately show ?thesis by simp
  qed
  have rlast: "last (follow (prnt S0) j) = r" by (rule last_follow_root[OF rinv jV])
  have jne: "follow (prnt S0) j \<noteq> []" using follow_ne_ps[OF ppt] by auto
  have all: "\<forall>y\<in>set (follow (prnt S0) j). lsuc S0 y = j"
  proof
    fix y assume yin: "y \<in> set (follow (prnt S0) j)"
    have yV: "y \<in> V" using follow_subset_V[OF rinv jV] yin by auto
    have ry: "r \<in> set (follow (prnt S0) y)"
      using last_follow_root[OF rinv yV] follow_ne_ps[OF ppt, of y] by (metis last_in_set)
    show "lsuc S0 y = j" using spine_lemma[OF L0j rV yV yin ry] by simp
  qed
  hence "takeWhile (\<lambda>y. lsuc S0 y = j) (follow (prnt S0) j) = follow (prnt S0) j"
    by (simp add: takeWhile_eq_all_conv)
  thus "r \<in> set (takeWhile (\<lambda>y. lsuc S0 y = j) (follow (prnt S0) j))"
    using rlast jne by (metis last_in_set)
qed

lemma rV: "r \<in> V"
proof -
  have "set (follow (thrd S0) r) = V" using arb unfolding arb_invar_def by simp
  moreover have "r \<in> set (follow (thrd S0) r)"
    using follow_hd_ps[OF pst, of r] follow_ne_ps[OF pst, of r] by (metis hd_in_set)
  ultimately show ?thesis by simp
qed

text \<open>The root's old last descendant is the last node of the old thread.\<close>
lemma L0_char: "lsuc S0 r = last (follow (thrd S0) r)"
proof -
  have E: "dom (thrd S0) = V - {lsuc S0 r}" using arb unfolding arb_invar_def by simp
  hence "thrd S0 (lsuc S0 r) = None" by auto
  hence "follow (thrd S0) r = block S0 r"
    using block_props(1)[OF arb rV] by simp
  thus ?thesis using block_props(3)[OF arb rV] by simp
qed

text \<open>The three newlist-side matchings for clause E (@{term "L0 = lsuc S0 r"} = the root's old last
      descendant): if it was @{term j} the new last is @{term "lsx k"}; if it survives outside the
      moved block it is unchanged; if it was inside the moved block it becomes @{term "the (rvth S0 p)"}
      (or @{term "lsx k"} in the degenerate @{term "j = the (rvth S0 p)"} adjacency).\<close>
lemma caseA_match:
  assumes L0j: "lsuc S0 r = j"
  shows "last newlist = lsx k"
proof -
  have lastold: "last (follow (thrd S0) r) = j" using L0_char L0j by simp
  have split: "follow (thrd S0) r = alpha @ block S0 p @ beta" by (rule oldlist_split_eq)
  have bne: "block S0 p \<noteq> []" by (rule block_props(2)[OF arb pV])
  have betane: "beta \<noteq> []"
  proof
    assume "beta = []"
    hence "last (follow (thrd S0) r) = last (block S0 p)" using split bne by simp
    hence "j \<in> set (block S0 p)" using lastold bne by (metis last_in_set)
    thus False using j_notin_block_p by simp
  qed
  have lastholed: "last holed = j" using lastold split betane by (simp add: holed_def)
  have hne: "holed \<noteq> []" using holed_split by (metis Nil_is_append_conv list.distinct(1))
  have hbl: "holed = butlast holed @ [j]" using lastholed hne by (metis append_butlast_last_id)
  have jnotbl: "j \<notin> set (butlast holed)"
  proof - have "distinct (butlast holed @ [j])" using holed_distinct hbl by simp
    thus ?thesis by auto qed
  have allne: "\<forall>x\<in>set (butlast holed). x \<noteq> j" using jnotbl by auto
  have d1: "dropWhile (\<lambda>x. x \<noteq> j) holed = dropWhile (\<lambda>x. x \<noteq> j) (butlast holed @ [j])" by (rule arg_cong[OF hbl])
  have d2: "dropWhile (\<lambda>x. x \<noteq> j) (butlast holed @ [j]) = [j]" using allne by (simp add: dropWhile_append2)
  have "tl (dropWhile (\<lambda>x. x \<noteq> j) holed) = []" using d1 d2 by simp
  thus ?thesis by (rule last_newlist_nil)
qed

lemma caseB_match:
  assumes L0j: "lsuc S0 r \<noteq> j" and L0nb: "lsuc S0 r \<notin> set (block S0 p)"
  shows "last newlist = lsuc S0 r"
proof -
  have lastold: "last (follow (thrd S0) r) = lsuc S0 r" using L0_char by simp
  have split: "follow (thrd S0) r = alpha @ block S0 p @ beta" by (rule oldlist_split_eq)
  have bne: "block S0 p \<noteq> []" by (rule block_props(2)[OF arb pV])
  have betane: "beta \<noteq> []"
  proof
    assume "beta = []"
    hence "last (follow (thrd S0) r) = last (block S0 p)" using split bne by simp
    hence "lsuc S0 r \<in> set (block S0 p)" using lastold bne by (metis last_in_set)
    thus False using L0nb by simp
  qed
  have lastholed: "last holed = lsuc S0 r" using lastold split betane by (simp add: holed_def)
  have TLne: "tl (dropWhile (\<lambda>x. x \<noteq> j) holed) \<noteq> []"
  proof
    assume "tl (dropWhile (\<lambda>x. x \<noteq> j) holed) = []"
    hence "last holed = j" by (rule last_holed_nil)
    thus False using lastholed L0j by simp
  qed
  have "last newlist = last holed" by (rule last_newlist_TL[OF TLne])
  thus ?thesis using lastholed by simp
qed

lemma caseC_match:
  assumes L0b: "lsuc S0 r \<in> set (block S0 p)"
  shows "(j = the (rvth S0 p) \<and> last newlist = lsx k) \<or> (j \<noteq> the (rvth S0 p) \<and> last newlist = the (rvth S0 p))"
proof -
  have lastold: "last (follow (thrd S0) r) = lsuc S0 r" using L0_char by simp
  have split: "follow (thrd S0) r = alpha @ block S0 p @ beta" by (rule oldlist_split_eq)
  have dist: "distinct (alpha @ block S0 p @ beta)" using oldlist_distinct split by simp
  have betanil: "beta = []"
  proof (rule ccontr)
    assume bne': "beta \<noteq> []"
    have "last (follow (thrd S0) r) = last beta" using split bne' by simp
    hence "lsuc S0 r = last beta" using lastold by simp
    moreover have "last beta \<in> set beta" using bne' by simp
    moreover have "set beta \<inter> set (block S0 p) = {}" using dist by auto
    ultimately show False using L0b by auto
  qed
  have lastholed: "last holed = the (rvth S0 p)" by (rule last_holed_old_rev[OF betanil])
  show ?thesis
  proof (cases "j = the (rvth S0 p)")
    case True
    hence lhj: "last holed = j" using lastholed by simp
    have hne: "holed \<noteq> []" using holed_split by (metis Nil_is_append_conv list.distinct(1))
    have hbl: "holed = butlast holed @ [j]" using lhj hne by (metis append_butlast_last_id)
    have jnotbl: "j \<notin> set (butlast holed)"
    proof - have "distinct (butlast holed @ [j])" using holed_distinct hbl by simp
      thus ?thesis by auto qed
    have allne: "\<forall>x\<in>set (butlast holed). x \<noteq> j" using jnotbl by auto
    have d1: "dropWhile (\<lambda>x. x \<noteq> j) holed = dropWhile (\<lambda>x. x \<noteq> j) (butlast holed @ [j])" by (rule arg_cong[OF hbl])
    have d2: "dropWhile (\<lambda>x. x \<noteq> j) (butlast holed @ [j]) = [j]" using allne by (simp add: dropWhile_append2)
    have "tl (dropWhile (\<lambda>x. x \<noteq> j) holed) = []" using d1 d2 by simp
    hence "last newlist = lsx k" by (rule last_newlist_nil)
    thus ?thesis using True by simp
  next
    case False
    hence lhne: "last holed \<noteq> j" using lastholed by simp
    have TLne: "tl (dropWhile (\<lambda>x. x \<noteq> j) holed) \<noteq> []"
    proof
      assume "tl (dropWhile (\<lambda>x. x \<noteq> j) holed) = []"
      hence "last holed = j" by (rule last_holed_nil)
      thus False using lhne by simp
    qed
    have "last newlist = last holed" by (rule last_newlist_TL[OF TLne])
    thus ?thesis using lastholed False by simp
  qed
qed

text \<open>In case C (the root's old last descendant is inside the moved block), the apex @{term jn} is not
      the reverse-thread predecessor @{term "the (rvth S0 p)"} of @{term p}: otherwise
      @{term "thrd S0 jn = Some p"} would make @{term p} the @{term jn}-first-child and push @{term j}
      after @{term "block S0 p"}, contradicting @{term "beta = []"}.  This picks the @{term S3} arm-1.\<close>
lemma jn_ne_old_rev_C:
  assumes L0b: "lsuc S0 r \<in> set (block S0 p)" and jnj: "jn \<in> set (follow (prnt S0) j)"
      and jne: "j \<noteq> the (rvth S0 p)"
  shows "jn \<noteq> the (rvth S0 p)"
proof
  assume jeq: "jn = the (rvth S0 p)"
  have jnej: "j \<noteq> jn" using jne jeq by simp
  have rinv: "rooted_arborescense_invar r V (prnt S0)" using arb unfolding arb_invar_def by simp
  have lastold: "last (follow (thrd S0) r) = lsuc S0 r" using L0_char by simp
  have split: "follow (thrd S0) r = alpha @ block S0 p @ beta" by (rule oldlist_split_eq)
  have dist: "distinct (alpha @ block S0 p @ beta)" using oldlist_distinct split by simp
  have betanil: "beta = []"
  proof (rule ccontr)
    assume bne': "beta \<noteq> []"
    have "last (follow (thrd S0) r) = last beta" using split bne' by simp
    hence "lsuc S0 r = last beta" using lastold by simp
    moreover have "last beta \<in> set beta" using bne' by simp
    moreover have "set beta \<inter> set (block S0 p) = {}" using dist by auto
    ultimately show False using L0b by auto
  qed
  have pdom: "p \<in> dom (rvth S0)" using arb pV pne_r unfolding arb_invar_def by auto
  then obtain w where w: "rvth S0 p = Some w" by auto
  hence orw: "the (rvth S0 p) = w" by simp
  have "thrd S0 w = Some p" using w arb unfolding arb_invar_def by auto
  hence thrdjn: "thrd S0 jn = Some p" using jeq orw by simp
  have jnla: "jn = last alpha" using jeq old_rev_last_alpha by simp
  have alphabl: "alpha = butlast alpha @ [jn]" using jnla alpha_ne by (metis append_butlast_last_id)
  have oldform: "follow (thrd S0) r = butlast alpha @ jn # block S0 p"
    using split betanil alphabl by simp
  have fjn: "follow (thrd S0) jn = jn # block S0 p" using follow_append_ps[OF pst oldform] by auto
  have jnV: "jn \<in> V" using follow_subset_V[OF rinv jV] jnj by auto
  have "follow (thrd S0) jn = block S0 jn @ (case thrd S0 (lsuc S0 jn) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd S0) w)"
    using block_props(1)[OF arb jnV] by auto
  hence "set (block S0 jn) \<subseteq> set (follow (thrd S0) jn)" by (metis Un_iff set_append subsetI)
  hence blksub: "set (block S0 jn) \<subseteq> {jn} \<union> set (block S0 p)" using fjn by simp
  have jchild: "j \<in> children (prnt S0) jn" using jnj unfolding children_def by simp
  have "j \<in> set (block S0 jn)" using block_props(4)[OF arb jnV] jchild by simp
  hence "j \<in> {jn} \<union> set (block S0 p)" using blksub by auto
  thus False using jnej j_notin_block_p by auto
qed

text \<open>Clause E, hard half: the root's new last-descendant @{term "lsuc (update_tree S0 i j p jn) r"}
      equals @{term "last newlist"}.  Pipeline @{term "lsuc S5 r = lsuc S3 r"}; @{term "lsuc S2 r"} is
      @{term "lsx k"} iff @{term j} was the old last (@{thm r_in_INchain_iff}); then a 3-way split on
      the root's old last descendant, matched by @{thm caseA_match}/@{thm caseB_match}/@{thm caseC_match}.\<close>
lemma lsuc_update_tree_r:
  assumes kpos: "0 < k" and jnp: "jn \<in> set (follow (prnt S0) p)" and pjn: "p \<noteq> jn"
      and jnj: "jn \<in> set (follow (prnt S0) j)"
  shows "lsuc (update_tree S0 i j p jn) r = last newlist"
proof -
  have inep: "i \<noteq> p" using inep_aux[OF kpos] by auto
  have psN: "parent_spec ((prnt S0 ++ REV k)(p \<mapsto> s_pred k))"
    using clauseA rooted_arborescense_invar_parent_spec by auto
  have rinv: "rooted_arborescense_invar r V (prnt S0)" using arb unfolding arb_invar_def by simp
  define Sp where "Sp = Sfin\<lparr>prnt := (prnt Sfin)(p \<mapsto> s_pred k)\<rparr>"
  define Sq where "Sq = (case (if the (rvth S0 p) = j then thrd S0 (lsuc S0 p) else thrd S0 j) of
                           None \<Rightarrow> Sp\<lparr>thrd := (thrd Sp)(lsx k := None)\<rparr>
                         | Some a \<Rightarrow> Sp\<lparr>thrd := (thrd Sp)(lsx k \<mapsto> a), rvth := (rvth Sp)(a \<mapsto> lsx k)\<rparr>)"
  define Sr where "Sr = Sq\<lparr>lsuc := (lsuc Sq)(p := lsx k)\<rparr>"
  define Ss where "Ss = (if the (rvth S0 p) \<noteq> j
                         then (case aftn k of
                                 None \<Rightarrow> Sr\<lparr>thrd := (thrd Sr)(the (rvth S0 p) := None)\<rparr>
                               | Some a \<Rightarrow> Sr\<lparr>thrd := (thrd Sr)(the (rvth S0 p) \<mapsto> a), rvth := (rvth Sr)(a \<mapsto> the (rvth S0 p))\<rparr>)
                         else Sr)"
  define St where "St = dirty_pass Ss (drt k)"
  define Su where "Su = stem_num_loop St (snum S0) p i 0 (lsuc St p)"
  define Sv where "Sv = Su\<lparr>snum := (snum Su)(i := snum S0 p)\<rparr>"
  define S2 where "S2 = last_vin_loop Sv j j (lsuc Sv p)"
  define S3 where "S3 = (if jn \<noteq> the (rvth S0 p) \<and> j \<noteq> the (rvth S0 p)
                         then last_vout_loop S2 (the (prnt S0 p)) (if lsuc Sv jn = j then Some jn else None) (lsuc S0 p) (the (rvth S0 p))
                         else if lsuc Sv p \<noteq> lsuc S0 p
                              then last_vout_loop S2 (the (prnt S0 p)) (if lsuc Sv jn = j then Some jn else None) (lsuc S0 p) (lsuc Sv p)
                              else S2)"
  define S4 where "S4 = succ_vin_loop S3 j jn (snum S0 p)"
  define S5 where "S5 = succ_vout_loop S4 (the (prnt S0 p)) jn (snum S0 p)"
  have psSv: "parent_spec (prnt Sv)" using stem_num_loop_fields[OF psN, THEN mp] psN by (simp add: Sv_def Su_def St_def Ss_def Sr_def Sq_def Sp_def Sfin_def split: option.split)
  define Sa where "Sa = fused_vin_loop Sv j j jn (lsuc Sv p) (snum S0 p) True True"
  define Sb where "Sb = (if jn \<noteq> the (rvth S0 p) \<and> j \<noteq> the (rvth S0 p) then fused_vout_loop Sa (the (prnt S0 p)) (if lsuc Sv jn = j then Some jn else None) (lsuc S0 p) (the (rvth S0 p)) jn (snum S0 p) True True else if lsuc Sv p \<noteq> lsuc S0 p then fused_vout_loop Sa (the (prnt S0 p)) (if lsuc Sv jn = j then Some jn else None) (lsuc S0 p) (lsuc Sv p) jn (snum S0 p) True True else fused_vout_loop Sa (the (prnt S0 p)) (if lsuc Sv jn = j then Some jn else None) (lsuc S0 p) (lsuc S0 p) jn (snum S0 p) False True)"
  have UTb: "update_tree S0 i j p jn = Sb" by (simp only: update_tree_def Let_def inep if_False if_True stem_loop_init prod.case Sb_def Sa_def Sv_def Su_def St_def Ss_def Sr_def Sq_def Sp_def)
  have SbS5: "Sb = S5" using update_tree_tail_eq[OF psSv] by (simp only: Sb_def Sa_def S5_def S4_def S3_def S2_def)
  have UT: "update_tree S0 i j p jn = S5" using UTb SbS5 by simp
  have pSp: "prnt Sp = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)" by (simp add: Sp_def Sfin_def)
  have pSq: "prnt Sq = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)" using pSp by (simp add: Sq_def split: option.split)
  have pSr: "prnt Sr = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)" using pSq by (simp add: Sr_def)
  have pSs: "prnt Ss = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)" using pSr by (simp add: Ss_def split: option.split)
  have pSt: "prnt St = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)" using pSs by (simp add: St_def)
  have pSu: "prnt Su = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)"
    using stem_num_loop_fields[OF psN, THEN mp, OF pSt] by (simp add: Su_def)
  have pSv: "prnt Sv = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)" using pSu by (simp add: Sv_def)
  have pS2: "prnt S2 = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)"
    using last_vin_loop_fields[OF psN, THEN mp, OF pSv] by (simp add: S2_def)
  have pS3: "prnt S3 = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)"
    using last_vout_loop_fields[OF psN, THEN mp, OF pS2] pS2 by (simp add: S3_def)
  have pS4: "prnt S4 = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)"
    using succ_vin_loop_fields[OF psN, THEN mp, OF pS3] by (simp add: S4_def)
  have lsSp: "lsuc Sp = lsuc S0" by (simp add: Sp_def Sfin_def)
  have lsSq: "lsuc Sq = lsuc S0" using lsSp by (simp add: Sq_def split: option.split)
  have lsSr: "lsuc Sr = (lsuc S0)(p := lsx k)" using lsSq by (simp add: Sr_def)
  have lsSs: "lsuc Ss = (lsuc S0)(p := lsx k)" using lsSr by (simp add: Ss_def split: option.split)
  have lsSt: "lsuc St = (lsuc S0)(p := lsx k)" using lsSs by (simp add: St_def)
  have lsSu: "lsuc Su = (\<lambda>x. if x \<in> (\<lambda>y. the (((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) y)) ` set (takeWhile (\<lambda>z. z \<noteq> i) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) p)) then lsuc St p else lsuc St x)"
    using stem_num_loop_lsuc[OF psN, THEN mp, OF pSt, THEN mp, OF i_in_follow_newprnt] by (simp add: Su_def)
  have lsSvSu: "lsuc Sv = lsuc Su" by (simp add: Sv_def)
  have lsvz: "\<And>z. z \<notin> s ` {..k} \<Longrightarrow> lsuc Sv z = lsuc S0 z"
  proof -
    fix z assume zns: "z \<notin> s ` {..k}"
    have "z \<notin> (\<lambda>y. the (((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) y)) ` set (takeWhile (\<lambda>z. z \<noteq> i) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) p))"
      using imgStem_sub[OF kpos] zns by auto
    hence "lsuc Su z = lsuc St z" using lsSu by simp
    moreover have "z \<noteq> p" using zns pathk by auto
    ultimately show "lsuc Sv z = lsuc S0 z" using lsSvSu lsSt by simp
  qed
  have lsvp: "lsuc Sv p = lsx k"
  proof -
    have "lsuc Su p = lsuc St p" using lsSu by simp
    thus ?thesis using lsSvSu lsSt by simp
  qed
  have lsS5S3: "lsuc S5 r = lsuc S3 r"
  proof -
    have "lsuc S4 = lsuc S3" using succ_vin_loop_fields[OF psN, THEN mp, OF pS3] by (simp add: S4_def)
    moreover have "lsuc S5 = lsuc S4" using succ_vout_loop_fields[OF psN, THEN mp, OF pS4] by (simp add: S5_def)
    ultimately show ?thesis by simp
  qed
  have rns: "r \<notin> s ` {..k}" by (rule r_notin_stem[OF kpos])
  have lsvr: "lsuc Sv r = lsuc S0 r" by (rule lsvz[OF rns])
  have CHcong: "takeWhile (\<lambda>y. lsuc Sv y = j) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) j) = takeWhile (\<lambda>y. lsuc S0 y = j) (follow (prnt S0) j)"
  proof -
    have fj: "follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) j = follow (prnt S0) j" by (rule follow_newprnt_j)
    have cong: "\<And>y. y \<in> set (follow (prnt S0) j) \<Longrightarrow> (lsuc Sv y = j) = (lsuc S0 y = j)"
    proof -
      fix y assume yj: "y \<in> set (follow (prnt S0) j)"
      have "y \<notin> s ` {..k}" using stem_notin_follow_j yj by auto
      thus "(lsuc Sv y = j) = (lsuc S0 y = j)" using lsvz by simp
    qed
    show ?thesis using takeWhile_cong[OF fj cong] 
      using follow_newprnt_j by force
  qed
  have lsS2: "lsuc S2 = (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. lsuc Sv y = j) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) j)) then lsuc Sv p else lsuc Sv x)"
    using last_vin_loop_lsuc[OF psN, THEN mp, OF pSv] by (simp add: S2_def)
  have lsS2r: "lsuc S2 r = (if lsuc S0 r = j then lsx k else lsuc S0 r)"
  proof -
    have "(r \<in> set (takeWhile (\<lambda>y. lsuc Sv y = j) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) j))) = (lsuc S0 r = j)"
      using CHcong r_in_INchain_iff by simp
    thus ?thesis using lsS2 lsvp lsvr by simp
  qed
  have lvoutval: "\<And>stp gv sv. lsuc (last_vout_loop S2 (the (prnt S0 p)) stp gv sv) = (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. Some y \<noteq> stp \<and> lsuc S2 y = gv) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (the (prnt S0 p)))) then sv else lsuc S2 x)"
    using last_vout_loop_lsuc[OF psN, THEN mp, OF pS2] by simp
  have jnV: "jn \<in> V" using follow_subset_V[OF rinv jV] jnj by auto
  have rjn: "r \<in> set (follow (prnt S0) jn)"
    using last_follow_root[OF rinv jnV] follow_ne_ps[OF ppt, of jn] by (metis last_in_set)
  obtain vo where vo: "prnt S0 p = Some vo"
    using rooted_arborescense_invar_dom[OF rinv] pV pne_r by auto
  have voutp: "follow (prnt S0) p = p # follow (prnt S0) vo" using vo by (subst follow_ps_simps[OF ppt]) simp
  have voinp: "vo \<in> set (follow (prnt S0) p)"
    using voutp follow_hd_ps[OF ppt, of vo] follow_ne_ps[OF ppt, of vo] by (metis hd_in_set list.set_intros(2))
  have voutV: "the (prnt S0 p) \<in> V" using voinp follow_subset_V[OF rinv pV] vo by auto
  have rvout: "r \<in> set (follow (prnt S0) (the (prnt S0 p)))"
    using last_follow_root[OF rinv voutV] follow_ne_ps[OF ppt, of "the (prnt S0 p)"] by (metis last_in_set)
  have lsvjn: "lsuc Sv jn = lsuc S0 jn" using lsvz jn_notin_stem[OF jnp pjn] by simp
  have lspin: "lsuc S0 p \<in> set (block S0 p)"
    using block_props(3)[OF arb pV] block_props(2)[OF arb pV] by (metis last_in_set)
  show ?thesis
  proof (cases "lsuc S0 r = j")
    case caseA: True
    have s2r: "lsuc S2 r = lsx k" using lsS2r caseA by simp
    have lsjnj: "lsuc S0 jn = j" using spine_lemma[OF caseA rV jnV jnj rjn] by auto
    have upl: "(if lsuc Sv jn = j then Some jn else None) = Some jn" using lsvjn lsjnj by simp
    have jnLout: "jn \<in> set (follow (prnt S0) (the (prnt S0 p)))" by (rule jn_on_vout[OF kpos jnp pjn])
    have rnoout: "\<And>gv. r \<notin> set (takeWhile (\<lambda>y. Some y \<noteq> Some jn \<and> lsuc S2 y = gv) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (the (prnt S0 p))))"
    proof -
      fix gv
      show "r \<notin> set (takeWhile (\<lambda>y. Some y \<noteq> Some jn \<and> lsuc S2 y = gv) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (the (prnt S0 p))))"
      proof
        assume "r \<in> set (takeWhile (\<lambda>y. Some y \<noteq> Some jn \<and> lsuc S2 y = gv) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (the (prnt S0 p))))"
        hence rinL: "r \<in> set (takeWhile (\<lambda>y. Some y \<noteq> Some jn \<and> lsuc S2 y = gv) (follow (prnt S0) (the (prnt S0 p))))"
          using follow_newprnt_vout[OF kpos] by simp
        have distL: "distinct (follow (prnt S0) (the (prnt S0 p)))" by (rule follow_distinct_ps[OF ppt])
        have rlast: "r = last (follow (prnt S0) (the (prnt S0 p)))" using last_follow_root[OF rinv voutV] by simp
        have "dropWhile (\<lambda>y. Some y \<noteq> Some jn \<and> lsuc S2 y = gv) (follow (prnt S0) (the (prnt S0 p))) = []"
        proof (rule ccontr)
          assume dne: "dropWhile (\<lambda>y. Some y \<noteq> Some jn \<and> lsuc S2 y = gv) (follow (prnt S0) (the (prnt S0 p))) \<noteq> []"
          have "last (follow (prnt S0) (the (prnt S0 p))) = last (dropWhile (\<lambda>y. Some y \<noteq> Some jn \<and> lsuc S2 y = gv) (follow (prnt S0) (the (prnt S0 p))))"
            using dne by (metis takeWhile_dropWhile_id last_appendR)
          hence "r \<in> set (dropWhile (\<lambda>y. Some y \<noteq> Some jn \<and> lsuc S2 y = gv) (follow (prnt S0) (the (prnt S0 p))))"
            using rlast dne by (metis last_in_set)
          moreover have "set (takeWhile (\<lambda>y. Some y \<noteq> Some jn \<and> lsuc S2 y = gv) (follow (prnt S0) (the (prnt S0 p)))) \<inter> set (dropWhile (\<lambda>y. Some y \<noteq> Some jn \<and> lsuc S2 y = gv) (follow (prnt S0) (the (prnt S0 p)))) = {}"
            using distL  distinct_append takeWhile_dropWhile_id 
            by fastforce
          ultimately show False using rinL by auto
        qed
        hence "takeWhile (\<lambda>y. Some y \<noteq> Some jn \<and> lsuc S2 y = gv) (follow (prnt S0) (the (prnt S0 p))) = follow (prnt S0) (the (prnt S0 p))"
          using append_Nil2 takeWhile_dropWhile_id by simp
        hence "jn \<in> set (takeWhile (\<lambda>y. Some y \<noteq> Some jn \<and> lsuc S2 y = gv) (follow (prnt S0) (the (prnt S0 p))))"
          using jnLout by auto
        hence "Some jn \<noteq> Some jn \<and> lsuc S2 jn = gv" using takeWhile_holds by fast
        thus False by simp
      qed
    qed
    have lss3r: "lsuc S3 r = lsuc S2 r"
    proof (cases "jn \<noteq> the (rvth S0 p) \<and> j \<noteq> the (rvth S0 p)")
      case True
      have "S3 = last_vout_loop S2 (the (prnt S0 p)) (Some jn) (lsuc S0 p) (the (rvth S0 p))"
        using True upl by (simp add: S3_def)
      thus ?thesis using lvoutval[of "Some jn" "lsuc S0 p" "the (rvth S0 p)"] rnoout[of "lsuc S0 p"] by simp
    next
      case c1: False
      show ?thesis
      proof (cases "lsuc Sv p \<noteq> lsuc S0 p")
        case True
        have "S3 = last_vout_loop S2 (the (prnt S0 p)) (Some jn) (lsuc S0 p) (lsuc Sv p)"
          using c1 True upl by (auto simp add: S3_def)
        thus ?thesis using lvoutval[of "Some jn" "lsuc S0 p" "lsuc Sv p"] rnoout[of "lsuc S0 p"] by simp
      next
        case False
        have "S3 = S2" using c1 False by (auto simp add: S3_def)
        thus ?thesis by simp
      qed
    qed
    have "lsuc (update_tree S0 i j p jn) r = lsx k" using UT lsS5S3 lss3r s2r by simp
    thus ?thesis using caseA_match[OF caseA] by simp
  next
    case notj: False
    show ?thesis
    proof (cases "lsuc S0 r \<in> set (block S0 p)")
      case caseC: True
      have s2r: "lsuc S2 r = lsuc S0 r" using lsS2r notj by simp
      have L0old: "lsuc S0 r = lsuc S0 p"
      proof -
        have lastold: "last (follow (thrd S0) r) = lsuc S0 r" using L0_char by simp
        have split: "follow (thrd S0) r = alpha @ block S0 p @ beta" by (rule oldlist_split_eq)
        have dist: "distinct (alpha @ block S0 p @ beta)" using oldlist_distinct split by simp
        have "beta = []"
        proof (rule ccontr)
          assume bne': "beta \<noteq> []"
          have "last (follow (thrd S0) r) = last beta" using split bne' by simp
          hence "lsuc S0 r = last beta" using lastold by simp
          moreover have "last beta \<in> set beta" using bne' by simp
          moreover have "set beta \<inter> set (block S0 p) = {}" using dist by auto
          ultimately show False using caseC by auto
        qed
        hence "last (follow (thrd S0) r) = last (block S0 p)" using split block_props(2)[OF arb pV] by simp
        thus ?thesis using lastold block_props(3)[OF arb pV] by simp
      qed
      have p_anc_lsp: "p \<in> set (follow (prnt S0) (lsuc S0 p))"
        using block_props(4)[OF arb pV] lspin unfolding children_def by simp
      have jn_anc_lsp: "jn \<in> set (follow (prnt S0) (lsuc S0 p))" using follow_trans[OF ppt p_anc_lsp jnp] by auto
      have lsjn_lsp: "lsuc S0 jn = lsuc S0 p" using spine_lemma[OF L0old rV jnV jn_anc_lsp rjn] by auto
      have lspnej: "lsuc S0 p \<noteq> j" using lspin j_notin_block_p by auto
      have upl: "(if lsuc Sv jn = j then Some jn else None) = None" using lsvjn lsjn_lsp lspnej by simp
      have voinlsp: "vo \<in> set (follow (prnt S0) (lsuc S0 p))" using follow_trans[OF ppt p_anc_lsp voinp] by auto
      have allout: "\<And>y. y \<in> set (follow (prnt S0) (the (prnt S0 p))) \<Longrightarrow> lsuc S2 y = lsuc S0 p"
      proof -
        fix y assume yin: "y \<in> set (follow (prnt S0) (the (prnt S0 p)))"
        have yvo: "y \<in> set (follow (prnt S0) vo)" using yin vo by simp
        have ynstem: "y \<notin> s ` {..k}" using stem_notin_follow_vout[OF kpos] yin by auto
        have yV: "y \<in> V" using follow_subset_V[OF rinv voutV] yin by auto
        have ry: "r \<in> set (follow (prnt S0) y)"
          using last_follow_root[OF rinv yV] follow_ne_ps[OF ppt, of y] by (metis last_in_set)
        have y_anc_lsp: "y \<in> set (follow (prnt S0) (lsuc S0 p))" using follow_trans[OF ppt voinlsp yvo] by auto
        have lsy: "lsuc S0 y = lsuc S0 p" using spine_lemma[OF L0old rV yV y_anc_lsp ry] by auto
        have ynotch: "y \<notin> set (takeWhile (\<lambda>y'. lsuc Sv y' = j) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) j))"
        proof
          assume "y \<in> set (takeWhile (\<lambda>y'. lsuc Sv y' = j) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) j))"
          hence "y \<in> set (takeWhile (\<lambda>y'. lsuc S0 y' = j) (follow (prnt S0) j))" using CHcong by simp
          hence "lsuc S0 y = j" using takeWhile_holds by fast
          thus False using lsy lspnej by simp
        qed
        show "lsuc S2 y = lsuc S0 p" using lsS2 ynotch lsvz ynstem lsy by simp
      qed
      have rin_out: "r \<in> set (takeWhile (\<lambda>y. Some y \<noteq> None \<and> lsuc S2 y = lsuc S0 p) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (the (prnt S0 p))))"
      proof -
        have "takeWhile (\<lambda>y. Some y \<noteq> None \<and> lsuc S2 y = lsuc S0 p) (follow (prnt S0) (the (prnt S0 p))) = follow (prnt S0) (the (prnt S0 p))"
          by (rule iffD2[OF takeWhile_eq_all_conv]) (use allout in auto)
        thus ?thesis 
          using follow_newprnt_vout[OF kpos] rvout by argo
      qed
      have lss3r: "lsuc S3 r = last newlist"
      proof (cases "jn \<noteq> the (rvth S0 p) \<and> j \<noteq> the (rvth S0 p)")
        case True
        have "S3 = last_vout_loop S2 (the (prnt S0 p)) None (lsuc S0 p) (the (rvth S0 p))"
          using True upl by (simp add: S3_def)
        hence "lsuc S3 r = the (rvth S0 p)" using lvoutval[of None "lsuc S0 p" "the (rvth S0 p)"] rin_out by simp
        moreover have "last newlist = the (rvth S0 p)" using caseC_match[OF caseC] True by auto
        ultimately show ?thesis by simp
      next
        case c1: False
        have jold: "j = the (rvth S0 p)"
        proof (rule ccontr)
          assume "j \<noteq> the (rvth S0 p)"
          hence "jn \<noteq> the (rvth S0 p)" using jn_ne_old_rev_C[OF caseC jnj] by simp
          thus False using c1 \<open>j \<noteq> the (rvth S0 p)\<close> by simp
        qed
        have lnl: "last newlist = lsx k" using caseC_match[OF caseC] jold by auto
        show ?thesis
        proof (cases "lsuc Sv p \<noteq> lsuc S0 p")
          case True
          have "S3 = last_vout_loop S2 (the (prnt S0 p)) None (lsuc S0 p) (lsuc Sv p)"
            using c1 True upl by (auto simp add: S3_def)
          hence "lsuc S3 r = lsuc Sv p" using lvoutval[of None "lsuc S0 p" "lsuc Sv p"] rin_out by simp
          thus ?thesis using lnl lsvp by simp
        next
          case False
          have "S3 = S2" using c1 False by (auto simp add: S3_def)
          hence "lsuc S3 r = lsuc S2 r" by auto
          thus ?thesis using s2r L0old lsvp lnl
            using s2r \<open>lsuc S3 r = lsuc S2 r\<close> L0old False by fastforce
        qed
      qed
      show ?thesis using UT lsS5S3 lss3r by simp
    next
      case caseB: False
      have s2r: "lsuc S2 r = lsuc S0 r" using lsS2r notj by simp
      have L0nelsp: "lsuc S0 r \<noteq> lsuc S0 p" using caseB lspin by auto
      have rnoout: "\<And>stp. r \<notin> set (takeWhile (\<lambda>y. Some y \<noteq> stp \<and> lsuc S2 y = lsuc S0 p) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (the (prnt S0 p))))"
      proof -
        fix stp
        show "r \<notin> set (takeWhile (\<lambda>y. Some y \<noteq> stp \<and> lsuc S2 y = lsuc S0 p) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (the (prnt S0 p))))"
        proof
          assume "r \<in> set (takeWhile (\<lambda>y. Some y \<noteq> stp \<and> lsuc S2 y = lsuc S0 p) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (the (prnt S0 p))))"
          hence "Some r \<noteq> stp \<and> lsuc S2 r = lsuc S0 p" using takeWhile_holds by fast
          hence "lsuc S2 r = lsuc S0 p" by simp
          thus False using s2r L0nelsp by simp
        qed
      qed
      have lss3r: "lsuc S3 r = lsuc S2 r"
      proof (cases "jn \<noteq> the (rvth S0 p) \<and> j \<noteq> the (rvth S0 p)")
        case True
        have "S3 = last_vout_loop S2 (the (prnt S0 p)) (if lsuc Sv jn = j then Some jn else None) (lsuc S0 p) (the (rvth S0 p))"
          using True by (simp add: S3_def)
        thus ?thesis using lvoutval[of "if lsuc Sv jn = j then Some jn else None" "lsuc S0 p" "the (rvth S0 p)"] rnoout[of "if lsuc Sv jn = j then Some jn else None"] by simp
      next
        case c1: False
        show ?thesis
        proof (cases "lsuc Sv p \<noteq> lsuc S0 p")
          case True
          have "S3 = last_vout_loop S2 (the (prnt S0 p)) (if lsuc Sv jn = j then Some jn else None) (lsuc S0 p) (lsuc Sv p)"
            using c1 True by (auto simp add: S3_def)
          thus ?thesis using lvoutval[of "if lsuc Sv jn = j then Some jn else None" "lsuc S0 p" "lsuc Sv p"] rnoout[of "if lsuc Sv jn = j then Some jn else None"] by simp
        next
          case False
          have "S3 = S2" using c1 False by (auto simp add: S3_def)
          thus ?thesis by simp
        qed
      qed
      have "lsuc (update_tree S0 i j p jn) r = lsuc S0 r" using UT lsS5S3 lss3r s2r by simp
      thus ?thesis using caseB_match[OF notj caseB] by simp
    qed
  qed
qed

text \<open>\<^bold>\<open>Uniqueness of the block boundary\<close>: in a thread @{term "follow (thrd S) v = pre @ suf"}, the last
      node of the contiguous prefix @{term pre} is the \<^emph>\<open>unique\<close> node of @{term pre} whose thread-successor
      leaves @{term "set pre"} (every earlier node is followed inside @{term pre}).  This reduces the
      pointwise \<open>lsuc = last block\<close> obligation to two geometric facts about the field value
      @{term "lsuc S v"}: that it lies in @{term v}'s subtree, and that its successor exits that subtree.\<close>
lemma succ_exits_is_last:
  assumes psF: "parent_spec (thrd S)"
    and split: "follow (thrd S) v = pre @ suf"
    and xin: "x \<in> set pre"
    and exit: "thrd S x = None \<or> the (thrd S x) \<notin> set pre"
  shows "x = last pre"
proof (rule ccontr)
  assume xnl: "x \<noteq> last pre"
  have prene: "pre \<noteq> []" using xin by auto
  obtain idx where idxlt: "idx < length pre" and byidx: "pre ! idx = x" using xin by (meson in_set_conv_nth)
  have "idx \<noteq> length pre - 1"
  proof
    assume e: "idx = length pre - 1"
    have "x = last pre" using byidx e last_conv_nth[OF prene] by simp
    thus False using xnl by simp
  qed
  hence si: "Suc idx < length pre" using idxlt by simp
  define y where "y = pre ! Suc idx"
  have yin: "y \<in> set pre" using si y_def by simp
  have t1: "take (Suc idx) pre = take idx pre @ [x]" using idxlt byidx by (simp add: take_Suc_conv_app_nth)
  have t2: "take (Suc (Suc idx)) pre = take idx pre @ [x, y]" using si t1 y_def by (simp add: take_Suc_conv_app_nth)
  have predecomp: "pre = take idx pre @ x # y # drop (Suc (Suc idx)) pre"
    using t2 append_take_drop_id[of "Suc (Suc idx)" pre] by (metis append.assoc append_Cons append_Nil)
  have fsplit: "follow (thrd S) v = take idx pre @ x # y # (drop (Suc (Suc idx)) pre @ suf)"
    using split predecomp by simp
  have "thrd S x = Some y" by (rule thread_link[OF psF fsplit])
  thus False using exit yin by simp
qed

text \<open>\<^bold>\<open>Stem-region geometry for the pointwise-\<open>lsuc\<close> half\<close>.  For a stem node the new
      \<open>lsuc\<close> value is @{term "lsx k"}; these lemmas supply the two @{thm succ_exits_is_last} obligations for
      that value: (i) @{term "lsx k"} lies in every stem node's new subtree (@{text stem_desc_lsxk}); and
      (ii) its thread-successor @{term "final_thrd (lsx k)"} leaves @{term "set (block S0 p)"}, which
      contains that subtree (@{text final_thrd_lsxk_exits} + @{text children_stem_sub_blockp}).\<close>
lemma stem_anc_p_std:
  assumes kpos: "0 < k" and tk: "t \<le> k"
  shows "s t \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) p)"
proof (cases "t = 0")
  case True
  have "s 0 = i" by (simp add: path0)
  thus ?thesis using i_in_follow_newprnt True by simp
next
  case False
  hence "s t \<in> s ` {1..<Suc k}" using tk by auto
  hence "s t \<in> set (takeWhile (\<lambda>x. x \<noteq> i) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) p))"
    using chainStem_set[OF kpos] by simp
  thus ?thesis by (metis set_takeWhileD)
qed

lemma p_in_follow_lsxk:
  assumes kpos: "0 < k" and jneq: "jn = join_of (prnt S0) i j"
    and jnp: "jn \<in> set (follow (prnt S0) p)" and pjn: "p \<noteq> jn"
  shows "p \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (lsx k))"
proof -
  have ck: "set (contrib k) \<subseteq> children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (s k)"
    using contrib_sub_children_stem[OF kpos jneq jnp pjn le_refl] by auto
  have nb: "newblock = concat (map contrib [0..<k]) @ contrib k" by (rule newblock_split_last)
  have "last newblock = last (contrib k)" using nb contrib_ne by (metis last_appendR)
  hence lk: "lsx k = last (contrib k)" using last_newblock by simp
  have "last (contrib k) \<in> set (contrib k)" using contrib_ne by (metis last_in_set)
  hence "lsx k \<in> children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (s k)" using lk ck by auto
  hence "lsx k \<in> children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) p" by (simp add: pathk)
  thus ?thesis by (simp add: children_def)
qed

lemma stem_desc_lsxk:
  assumes kpos: "0 < k" and jneq: "jn = join_of (prnt S0) i j"
    and jnp: "jn \<in> set (follow (prnt S0) p)" and pjn: "p \<noteq> jn" and tk: "t \<le> k"
  shows "lsx k \<in> children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (s t)"
proof -
  have psN: "parent_spec ((prnt S0 ++ REV k)(p \<mapsto> s_pred k))" using clauseA rooted_arborescense_invar_parent_spec by auto
  have panc: "p \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (lsx k))" using p_in_follow_lsxk[OF kpos jneq jnp pjn] by auto
  have "set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) p) \<subseteq> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (lsx k))"
    using follow_sub_of_mem[OF psN panc] by auto
  moreover have "s t \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) p)" using stem_anc_p_std[OF kpos tk] by auto
  ultimately have "s t \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (lsx k))" by auto
  thus ?thesis by (simp add: children_def)
qed

lemma children_stem_sub_blockp:
  assumes kpos: "0 < k" and jneq: "jn = join_of (prnt S0) i j"
    and jnp: "jn \<in> set (follow (prnt S0) p)" and pjn: "p \<noteq> jn" and tk: "t \<le> k"
  shows "children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (s t) \<subseteq> set (block S0 p)"
proof (cases "t = 0")
  case True
  have "s 0 = i" by (simp add: path0)
  thus ?thesis using children_newprnt_i[OF kpos] True by simp
next
  case False
  hence t1: "1 \<le> t" by simp
  have "children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (s t) = set (block S0 p) - set (block S0 (s (t - 1)))"
    using children_newprnt_stem[OF kpos jneq jnp pjn t1 tk] by auto
  thus ?thesis by auto
qed

lemma final_thrd_lsxk_exits:
  assumes kpos: "0 < k"
  shows "final_thrd (lsx k) = None \<or> the (final_thrd (lsx k)) \<notin> set (block S0 p)"
proof (cases "tl (dropWhile (\<lambda>x. x \<noteq> j) holed) = []")
  case True
  have lnl: "last newlist = lsx k" using last_newlist_nil[OF True] by auto
  have psF: "parent_spec final_thrd" by (rule parent_spec_final_thrd[OF kpos])
  have oe: "follow final_thrd r = newlist" by (rule out_edge[OF kpos])
  have "final_thrd (last newlist) = None" using follow_last_None[OF psF, of r] oe by simp
  hence "final_thrd (lsx k) = None" using lnl by simp
  thus ?thesis by simp
next
  case False
  have "final_thrd (lsx k) = Some (hd (tl (dropWhile (\<lambda>x. x \<noteq> j) holed)))" using tail_seam[OF kpos False] by auto
  moreover have "hd (tl (dropWhile (\<lambda>x. x \<noteq> j) holed)) \<in> set holed"
    using hd_in_set[OF False] set_holed_split by auto
  ultimately show ?thesis using holed_set by auto
qed

text \<open>\<^bold>\<open>IN-chain-region geometry for the pointwise-\<open>lsuc\<close> half\<close>.  An \<^emph>\<open>IN-chain\<close> node
      @{term v} (an ancestor of @{term j} with @{term "lsuc S0 v = j"}) also gets new \<open>lsuc\<close> value
      @{term "lsx k"}: its old subtree ended at @{term j}, and the moved block is spliced right after
      @{term j}, so the new rightmost descendant is @{term "last newblock = lsx k"}.  Its new subtree is
      @{term "children (prnt S0) v \<union> set (block S0 p)"} (@{thm children_newprnt_jpath}); @{text in_desc_lsxk}
      is the \<open>i_desc\<close> half, and @{text final_thrd_lsxk_notin_INdesc} (with @{thm final_thrd_lsxk_exits}) the
      \<open>ii_exit\<close> half.  The generic @{text succ_lsuc_exits_block} says the thread-successor of any node's last
      descendant leaves that node's subtree.\<close>
lemma in_desc_lsxk:
  assumes kpos: "0 < k" and vj: "v \<in> set (follow (prnt S0) j)"
  shows "lsx k \<in> children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v"
proof -
  have "children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v = children (prnt S0) v \<union> set (block S0 p)"
    by (rule children_newprnt_jpath[OF kpos vj])
  moreover have "lsx k \<in> set (block S0 p)" using lsx_in_block_p[OF le_refl kpos] by auto
  ultimately show ?thesis by simp
qed

lemma succ_lsuc_exits_block:
  assumes uV: "u \<in> V" and sw: "thrd S0 (lsuc S0 u) = Some w"
  shows "w \<notin> children (prnt S0) u"
proof -
  have pst: "parent_spec (thrd S0)" using arb unfolding arb_invar_def by simp
  have fb: "follow (thrd S0) u = block S0 u @ follow (thrd S0) w"
    using block_props(1)[OF arb uV] sw by simp
  have dist: "distinct (follow (thrd S0) u)" by (rule follow_distinct_ps[OF pst])
  have hw: "hd (follow (thrd S0) w) = w" using follow_hd_ps[OF pst, of w] by auto
  have fwne: "follow (thrd S0) w \<noteq> []" by (rule follow_ne_ps[OF pst])
  have win: "w \<in> set (follow (thrd S0) w)" using hw fwne by (metis hd_in_set)
  have "distinct (block S0 u @ follow (thrd S0) w)" using dist fb by simp
  hence "set (block S0 u) \<inter> set (follow (thrd S0) w) = {}" by (simp add: distinct_append)
  hence "w \<notin> set (block S0 u)" using win by auto
  thus ?thesis using block_props(4)[OF arb uV] by simp
qed

lemma final_thrd_lsxk_notin_INdesc:
  assumes kpos: "0 < k" and vV: "v \<in> V" and lsvj: "lsuc S0 v = j"
  shows "final_thrd (lsx k) = None \<or> the (final_thrd (lsx k)) \<notin> children (prnt S0) v"
proof (cases "the (rvth S0 p) = j")
  case False
  have ft: "final_thrd (lsx k) = thrd S0 j" using final_thrd_lsx_k[OF kpos] False by simp
  show ?thesis
  proof (cases "thrd S0 j")
    case None thus ?thesis using ft by simp
  next
    case (Some w)
    have "thrd S0 (lsuc S0 v) = Some w" using Some lsvj by simp
    hence "w \<notin> children (prnt S0) v" using succ_lsuc_exits_block[OF vV] by simp
    thus ?thesis using ft Some by simp
  qed
next
  case True
  have ft: "final_thrd (lsx k) = thrd S0 (lsuc S0 p)" using final_thrd_lsx_k[OF kpos] True by simp
  have rvdom: "dom (rvth S0) = V - {r}" using arb unfolding arb_invar_def by simp
  have pdom: "p \<in> dom (rvth S0)" using rvdom pV pne_r by simp
  have "rvth S0 p = Some j" using pdom True by auto
  hence thj: "thrd S0 j = Some p" using arb unfolding arb_invar_def by auto
  show ?thesis
  proof (cases "thrd S0 (lsuc S0 p)")
    case None thus ?thesis using ft by simp
  next
    case (Some w)
    have pst: "parent_spec (thrd S0)" using arb unfolding arb_invar_def by simp
    have fvp: "follow (thrd S0) v = block S0 v @ follow (thrd S0) p"
      using block_props(1)[OF arb vV] lsvj thj by simp
    have fpw: "follow (thrd S0) p = block S0 p @ follow (thrd S0) w"
      using block_props(1)[OF arb pV] Some by simp
    have fv: "follow (thrd S0) v = block S0 v @ block S0 p @ follow (thrd S0) w" using fvp fpw by simp
    have dist: "distinct (follow (thrd S0) v)" by (rule follow_distinct_ps[OF pst])
    have win: "w \<in> set (follow (thrd S0) w)"
      using follow_hd_ps[OF pst, of w] follow_ne_ps[OF pst, of w] by (metis hd_in_set)
    have "distinct (block S0 v @ block S0 p @ follow (thrd S0) w)" using dist fv by simp
    hence "set (block S0 v) \<inter> set (follow (thrd S0) w) = {}" by (auto simp add: distinct_append)
    hence "w \<notin> set (block S0 v)" using win by auto
    hence "w \<notin> children (prnt S0) v" using block_props(4)[OF arb vV] by simp
    thus ?thesis using ft Some by simp
  qed
qed

text \<open>\<^bold>\<open>OUT-chain-region geometry for the pointwise-\<open>lsuc\<close> half\<close>.  An \<^emph>\<open>OUT-chain\<close> node
      @{term v} is a strict ancestor of @{term p} off the @{term j}-path whose old subtree ended in the
      moved block (@{term "lsuc S0 v = lsuc S0 p"}); the surgery removes @{term "block S0 p"} from its
      subtree, so the new \<open>lsuc\<close> becomes the block's thread-predecessor @{term "the (rvth S0 p)"} (\<open>old_rev\<close>).
      @{text old_rev_in_block_anc}: \<open>old_rev\<close> lies in any strict ancestor's subtree; @{text old_rev_in_children_out}
      is the \<open>i_desc\<close> half and @{text final_thrd_oldrev_exits_out} the \<open>ii_exit\<close> half (its successor is
      @{term "aftn k = thrd S0 (lsuc S0 p)"}, which by @{thm succ_lsuc_exits_block} leaves the subtree).\<close>
lemma old_rev_in_block_anc:
  assumes vV: "v \<in> V" and vp: "v \<in> set (follow (prnt S0) p)" and vnep: "p \<noteq> v"
  shows "the (rvth S0 p) \<in> set (block S0 v)"
proof -
  have pst: "parent_spec (thrd S0)" using arb unfolding arb_invar_def by simp
  have G: "\<forall>a b. thrd S0 a = Some b \<longleftrightarrow> rvth S0 b = Some a" using arb unfolding arb_invar_def by simp
  have pchild: "p \<in> children (prnt S0) v" using vp unfolding children_def by simp
  obtain P Q where PQ: "block S0 v = v # P @ block S0 p @ Q" using block_nest[OF arb vV pV pchild vnep] by auto
  have hp: "hd (block S0 p) = p" by (rule block_props(5)[OF arb pV])
  have bpne: "block S0 p \<noteq> []" by (rule block_props(2)[OF arb pV])
  have bp: "block S0 p = p # tl (block S0 p)" using hp bpne by (metis hd_Cons_tl)
  have fv: "follow (thrd S0) v = block S0 v @ (case thrd S0 (lsuc S0 v) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd S0) w)"
    by (rule block_props(1)[OF arb vV])
  define tlv where "tlv = (case thrd S0 (lsuc S0 v) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd S0) w)"
  have step2: "follow (thrd S0) v = (v # P) @ p # (tl (block S0 p) @ Q @ tlv)"
    using fv PQ bp tlv_def by simp
  have vPne: "v # P \<noteq> []" by simp
  obtain front where front: "v # P = front @ [last (v # P)]" using append_butlast_last_id[OF vPne] by metis
  have step3: "follow (thrd S0) v = front @ last (v # P) # p # (tl (block S0 p) @ Q @ tlv)"
    using step2 front by simp
  have "thrd S0 (last (v # P)) = Some p" using thread_link[OF pst step3] by auto
  hence "rvth S0 p = Some (last (v # P))" using G by auto
  hence orv: "the (rvth S0 p) = last (v # P)" by simp
  have "last (v # P) \<in> set (v # P)" by simp
  hence "last (v # P) \<in> set (block S0 v)" using PQ by simp
  thus ?thesis using orv by simp
qed

lemma old_rev_in_children_out:
  assumes kpos: "0 < k" and vV: "v \<in> V" and vp: "v \<in> set (follow (prnt S0) p)" and vnep: "p \<noteq> v"
    and vnj: "v \<notin> set (follow (prnt S0) j)"
  shows "the (rvth S0 p) \<in> children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v"
proof -
  have vnb: "v \<notin> set (block S0 p)"
  proof
    assume "v \<in> set (block S0 p)"
    hence "v \<in> children (prnt S0) p" using block_props(4)[OF arb pV] by simp
    hence pfv: "p \<in> set (follow (prnt S0) v)" unfolding children_def by simp
    have "v = p" using ancestor_antisym[OF ppt vp pfv] by auto
    thus False using vnep by simp
  qed
  have cno: "children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v = children (prnt S0) v - set (block S0 p)"
    by (rule children_newprnt_off_jpath[OF kpos vnb vnj])
  have orblk: "the (rvth S0 p) \<in> set (block S0 v)" using old_rev_in_block_anc[OF vV vp vnep] by auto
  have orch: "the (rvth S0 p) \<in> children (prnt S0) v" using orblk block_props(4)[OF arb vV] by simp
  have ornb: "the (rvth S0 p) \<notin> set (block S0 p)" by (rule old_rev_notin_block_p)
  show ?thesis using cno orch ornb by simp
qed

lemma final_thrd_oldrev_exits_out:
  assumes kpos: "0 < k" and orne: "the (rvth S0 p) \<noteq> j" and vV: "v \<in> V"
    and vp: "v \<in> set (follow (prnt S0) p)" and vnep: "p \<noteq> v" and vnj: "v \<notin> set (follow (prnt S0) j)"
    and lsvp: "lsuc S0 v = lsuc S0 p"
  shows "final_thrd (the (rvth S0 p)) = None \<or> the (final_thrd (the (rvth S0 p))) \<notin> children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v"
proof -
  have fo: "final_thrd (the (rvth S0 p)) = thrd S0 (lsuc S0 p)" using final_thrd_oldrev[OF orne] aftn_eq_thrd_lsuc_p by simp
  have vnb: "v \<notin> set (block S0 p)"
  proof
    assume "v \<in> set (block S0 p)"
    hence "v \<in> children (prnt S0) p" using block_props(4)[OF arb pV] by simp
    hence pfv: "p \<in> set (follow (prnt S0) v)" unfolding children_def by simp
    have "v = p" using ancestor_antisym[OF ppt vp pfv] by auto
    thus False using vnep by simp
  qed
  have cno: "children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v = children (prnt S0) v - set (block S0 p)"
    by (rule children_newprnt_off_jpath[OF kpos vnb vnj])
  show ?thesis
  proof (cases "thrd S0 (lsuc S0 p)")
    case None thus ?thesis using fo by simp
  next
    case (Some w)
    have "thrd S0 (lsuc S0 v) = Some w" using Some lsvp by simp
    hence "w \<notin> children (prnt S0) v" using succ_lsuc_exits_block[OF vV] by simp
    hence "w \<notin> children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v" using cno by simp
    thus ?thesis using fo Some by simp
  qed
qed

text \<open>\<^bold>\<open>Untouched-region geometry for the pointwise-\<open>lsuc\<close> half\<close>.  A node whose \<open>lsuc\<close> is
      not rewritten by any loop keeps value @{term "lsuc S0 v"}.  @{text children_newprnt_supseteq}: any old
      descendant off the moved block stays a new descendant (@{thm follow_newprnt_off_block}); so the old
      last descendant, if outside @{term "block S0 p"}, is still in the new subtree (@{text untouched_i_desc},
      the \<open>i_desc\<close> half).\<close>
lemma children_newprnt_supseteq:
  assumes kpos: "0 < k"
  shows "children (prnt S0) v - set (block S0 p) \<subseteq> children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v"
proof
  fix u assume "u \<in> children (prnt S0) v - set (block S0 p)"
  hence uch: "u \<in> children (prnt S0) v" and unb: "u \<notin> set (block S0 p)" by auto
  have "v \<in> set (follow (prnt S0) u)" using uch unfolding children_def by simp
  hence "v \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u)" using follow_newprnt_off_block[OF kpos unb] by simp
  thus "u \<in> children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v" unfolding children_def by simp
qed

lemma untouched_i_desc:
  assumes kpos: "0 < k" and vV: "v \<in> V" and lsnb: "lsuc S0 v \<notin> set (block S0 p)"
  shows "lsuc S0 v \<in> children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v"
proof -
  have "lsuc S0 v \<in> set (block S0 v)" using block_props(3)[OF arb vV] block_props(2)[OF arb vV] by (metis last_in_set)
  hence "lsuc S0 v \<in> children (prnt S0) v" using block_props(4)[OF arb vV] by simp
  hence "lsuc S0 v \<in> children (prnt S0) v - set (block S0 p)" using lsnb by simp
  thus ?thesis using children_newprnt_supseteq[OF kpos] by auto
qed

text \<open>The thread-predecessor of a non-head node of @{term "block S0 p"} stays inside the block (the block
      is contiguous in the thread), by inverting @{thm block_link} through the @{const rvth} correspondence.\<close>
lemma pred_in_block_p:
  assumes zw: "thrd S0 z = Some w" and wb: "w \<in> set (block S0 p)" and wp: "w \<noteq> p"
  shows "z \<in> set (block S0 p)"
proof -
  have G: "\<forall>a b. thrd S0 a = Some b \<longleftrightarrow> rvth S0 b = Some a" using arb unfolding arb_invar_def by simp
  have hp: "hd (block S0 p) = p" by (rule block_props(5)[OF arb pV])
  have bpne: "block S0 p \<noteq> []" by (rule block_props(2)[OF arb pV])
  obtain idx where idxlt: "idx < length (block S0 p)" and wi: "block S0 p ! idx = w" using wb by (meson in_set_conv_nth)
  have idxpos: "0 < idx"
  proof (rule ccontr)
    assume "\<not> 0 < idx" hence "idx = 0" by simp
    hence "w = hd (block S0 p)" using wi bpne by (simp add: hd_conv_nth)
    thus False using hp wp by simp
  qed
  have s: "Suc (idx - 1) < length (block S0 p)" using idxlt idxpos by simp
  have "thrd S0 (block S0 p ! (idx - 1)) = Some (block S0 p ! Suc (idx - 1))" using block_link[OF pV s] by auto
  hence "thrd S0 (block S0 p ! (idx - 1)) = Some w" using idxpos wi by simp
  hence "rvth S0 w = Some (block S0 p ! (idx - 1))" using G by auto
  moreover have "rvth S0 w = Some z" using zw G by auto
  ultimately have "z = block S0 p ! (idx - 1)" by simp
  moreover have "block S0 p ! (idx - 1) \<in> set (block S0 p)" using s by (metis Suc_lessD nth_mem)
  ultimately show ?thesis by simp
qed

text \<open>\<open>ii_exit\<close> half for the untouched region.  If the old last descendant @{term "lsuc S0 v"} is not
      rewritten by any loop (it is off the moved block and \<^emph>\<open>fresh\<close>), then @{term "final_thrd (lsuc S0 v)"}
      equals its old successor (@{thm final_thrd_fresh}), which by @{thm succ_lsuc_exits_block} leaves
      @{term "children (prnt S0) v"}; and it cannot fall into @{term "block S0 p"} (else @{term "lsuc S0 v"}
      would be  old\_rev or itself in the block, @{thm pred_in_block_p}).  As @{term "children ((prnt
      S0 ++ REV k)(p \<mapsto> s_pred k)) v \<subseteq> children (prnt S0) v \<union> set (block S0 p)"} (@{thm children_newprnt_decomp}),
      the successor leaves the new subtree.\<close>
lemma untouched_ii_exit:
  assumes kpos: "0 < k" and vV: "v \<in> V"
    and lsnb: "lsuc S0 v \<notin> set (block S0 p)"
    and lsl: "lsuc S0 v \<notin> lsx ` {..k}" and lsb: "lsuc S0 v \<notin> bef ` set [0..<k]"
    and lsj: "lsuc S0 v \<noteq> j" and lsor: "lsuc S0 v \<noteq> the (rvth S0 p)"
  shows "final_thrd (lsuc S0 v) = None \<or> the (final_thrd (lsuc S0 v)) \<notin> children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v"
proof -
  have G: "\<forall>a b. thrd S0 a = Some b \<longleftrightarrow> rvth S0 b = Some a" using arb unfolding arb_invar_def by simp
  have ff: "final_thrd (lsuc S0 v) = thrd S0 (lsuc S0 v)" using final_thrd_fresh[OF lsl lsb lsj lsor] by auto
  have subA: "children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v \<subseteq> children (prnt S0) v \<union> set (block S0 p)"
    using children_newprnt_decomp[OF kpos] by auto
  show ?thesis
  proof (cases "thrd S0 (lsuc S0 v)")
    case None thus ?thesis using ff by simp
  next
    case (Some w)
    have wnv: "w \<notin> children (prnt S0) v" by (rule succ_lsuc_exits_block[OF vV Some])
    have wnb: "w \<notin> set (block S0 p)"
    proof
      assume wb: "w \<in> set (block S0 p)"
      show False
      proof (cases "w = p")
        case True
        have "thrd S0 (lsuc S0 v) = Some p" using Some True by simp
        hence "rvth S0 p = Some (lsuc S0 v)" using G by auto
        hence "the (rvth S0 p) = lsuc S0 v" by simp
        thus False using lsor by simp
      next
        case False
        have "lsuc S0 v \<in> set (block S0 p)" using pred_in_block_p[OF Some wb False] by auto
        thus False using lsnb by simp
      qed
    qed
    have "w \<notin> children (prnt S0) v \<union> set (block S0 p)" using wnv wnb by simp
    hence "w \<notin> children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v" using subA by auto
    thus ?thesis using ff Some by simp
  qed
qed

text \<open>An off-stem node inside @{term "block S0 p"} has a subtree entirely disjoint from the stem: any stem
      descendant would make the node a stem node or a strict ancestor of @{term p}, both impossible.  Used to
      show the successor of such a node's last descendant (a stem node in the @{text lsx} case) exits its subtree.\<close>
lemma blockv_offstem_no_stem:
  assumes kpos: "0 < k" and vns: "v \<notin> s ` {..k}" and vV: "v \<in> V"
    and vb: "v \<in> set (block S0 p)" and tk: "t'' \<le> k"
  shows "s t'' \<notin> set (block S0 v)"
proof
  assume "s t'' \<in> set (block S0 v)"
  hence "s t'' \<in> children (prnt S0) v" using block_props(4)[OF arb vV] by simp
  hence vf: "v \<in> set (follow (prnt S0) (s t''))" unfolding children_def by simp
  have "follow (prnt S0) (s t'') = map s [t''..<Suc k] @ follow (prnt S0) (the (prnt S0 p))" using follow_stem_prefix[OF tk] by auto
  hence disj: "v \<in> set (map s [t''..<Suc k]) \<or> v \<in> set (follow (prnt S0) (the (prnt S0 p)))" using vf by auto
  show False
  proof (cases "v \<in> set (map s [t''..<Suc k])")
    case True
    hence "v \<in> s ` {..k}" by auto
    thus False using vns by simp
  next
    case False
    hence vvout: "v \<in> set (follow (prnt S0) (the (prnt S0 p)))" using disj by simp
    have rinv: "rooted_arborescense_invar r V (prnt S0)" using arb unfolding arb_invar_def by simp
    obtain vo where vo: "prnt S0 p = Some vo" using rooted_arborescense_invar_dom[OF rinv] pV pne_r by auto
    have "follow (prnt S0) p = p # follow (prnt S0) vo" using vo by (subst follow_ps_simps[OF ppt]) simp
    hence vp: "v \<in> set (follow (prnt S0) p)" using vvout vo by simp
    have "v \<in> children (prnt S0) p" using vb block_props(4)[OF arb pV] by simp
    hence pv: "p \<in> set (follow (prnt S0) v)" unfolding children_def by simp
    have "v = p" using ancestor_antisym[OF ppt vp pv] by auto
    thus False using vns pathk by auto
  qed
qed

text \<open>Clause E of @{const arb_invar} for the reversal branch: @{term "dom (thrd (update_tree S0 i j p jn))
      = V - {lsuc (update_tree S0 i j p jn) r}"}.\<close>
lemma clauseE:
  assumes kpos: "0 < k" and jnp: "jn \<in> set (follow (prnt S0) p)" and pjn: "p \<noteq> jn"
      and jnj: "jn \<in> set (follow (prnt S0) j)"
  shows "dom (thrd (update_tree S0 i j p jn)) = V - {lsuc (update_tree S0 i j p jn) r}"
  using dom_thrd_update_tree[OF kpos] lsuc_update_tree_r[OF kpos jnp pjn jnj] by simp

lemma final_thrd_lsx:
  assumes tk: "t < k" shows "final_thrd (lsx t) = Some (s (Suc t))"
proof -
  have k0: "0 < k" using tk by simp
  have ne_k: "lsx t \<noteq> lsx k" using lsx_inj_le[of t k] tk by simp
  have inblk: "lsx t \<in> set (block S0 p)" using lsx_in_block_p[of t] tk k0 by simp
  have ne_or: "lsx t \<noteq> the (rvth S0 p)" using inblk old_rev_notin_block_p by auto
  have "final_thrd (lsx t) = thrd_inv k (lsx t)" using final_thrd_off[OF ne_k ne_or] by auto
  also have "\<dots> = Some (s (Suc t))" by (rule thrd_inv_up[OF tk])
  finally show ?thesis .
qed

text \<open>When @{term "s t"}'s right side-part is empty, @{term "bef t"} coincides with @{term "lsx (Suc t)"}
      (a colliding last-successor): both are @{term "the (rvth S0 (s t))"} then.\<close>
lemma bef_collision:
  assumes tk: "t < k" and dq: "defQ t = []" shows "bef t = lsx (Suc t)"
proof -
  have "lsuc S0 (s t) = lsuc S0 (s (Suc t))" by (rule defQ_empty[OF tk dq])
  hence "lsx (Suc t) = the (rvth S0 (s t))" by (simp add: lsx_def)
  thus ?thesis by (simp add: bef_def)
qed

text \<open>\<^bold>\<open>Clause J, pointwise-lsuc half, for all v\<close>: the algorithm-computed
      last-successor equals the geometric rightmost descendant in the new tree, discharging @{text lsuc_last}
      of @{thm clauseJ_from_lsuc}.  Region case-split (stem / IN-chain / OUT-chain / block-internal / untouched),
      reduced via @{text succ_exits_is_last} (re-proved inline as \<open>sel\<close>) to two facts: the value lies in
      the new subtree of @{term v} and its thread-successor exits it.\<close>
lemma lsuc_last:
  assumes kpos: "0 < k"
 and jneq: "jn = join_of (prnt S0) i j"

  and jnp: "jn \<in> set (follow (prnt S0) p)" and pjn: "p \<noteq> jn"
      and vV: "v \<in> V"
      and P1: "follow (thrd (update_tree S0 i j p jn)) v = pre @ suf"
      and P2: "set pre = children (prnt (update_tree S0 i j p jn)) v"
      and P3: "pre \<noteq> []" and P4: "hd pre = v"
  shows "lsuc (update_tree S0 i j p jn) v = last pre" proof -
  have jnj: "jn \<in> set (follow (prnt S0) j)" using join_facts[OF jneq] by simp
  have inep: "i \<noteq> p" using inep_aux[OF kpos] by auto
  have psN: "parent_spec ((prnt S0 ++ REV k)(p \<mapsto> s_pred k))"
    using clauseA rooted_arborescense_invar_parent_spec by auto
  have rinv: "rooted_arborescense_invar r V (prnt S0)" using arb unfolding arb_invar_def by simp
  define Sp where "Sp = Sfin\<lparr>prnt := (prnt Sfin)(p \<mapsto> s_pred k)\<rparr>"
  define Sq where "Sq = (case (if the (rvth S0 p) = j then thrd S0 (lsuc S0 p) else thrd S0 j) of
                           None \<Rightarrow> Sp\<lparr>thrd := (thrd Sp)(lsx k := None)\<rparr>
                         | Some a \<Rightarrow> Sp\<lparr>thrd := (thrd Sp)(lsx k \<mapsto> a), rvth := (rvth Sp)(a \<mapsto> lsx k)\<rparr>)"
  define Sr where "Sr = Sq\<lparr>lsuc := (lsuc Sq)(p := lsx k)\<rparr>"
  define Ss where "Ss = (if the (rvth S0 p) \<noteq> j
                         then (case aftn k of
                                 None \<Rightarrow> Sr\<lparr>thrd := (thrd Sr)(the (rvth S0 p) := None)\<rparr>
                               | Some a \<Rightarrow> Sr\<lparr>thrd := (thrd Sr)(the (rvth S0 p) \<mapsto> a), rvth := (rvth Sr)(a \<mapsto> the (rvth S0 p))\<rparr>)
                         else Sr)"
  define St where "St = dirty_pass Ss (drt k)"
  define Su where "Su = stem_num_loop St (snum S0) p i 0 (lsuc St p)"
  define Sv where "Sv = Su\<lparr>snum := (snum Su)(i := snum S0 p)\<rparr>"
  define S2 where "S2 = last_vin_loop Sv j j (lsuc Sv p)"
  define S3 where "S3 = (if jn \<noteq> the (rvth S0 p) \<and> j \<noteq> the (rvth S0 p)
                         then last_vout_loop S2 (the (prnt S0 p)) (if lsuc Sv jn = j then Some jn else None) (lsuc S0 p) (the (rvth S0 p))
                         else if lsuc Sv p \<noteq> lsuc S0 p
                              then last_vout_loop S2 (the (prnt S0 p)) (if lsuc Sv jn = j then Some jn else None) (lsuc S0 p) (lsuc Sv p)
                              else S2)"
  define S4 where "S4 = succ_vin_loop S3 j jn (snum S0 p)"
  define S5 where "S5 = succ_vout_loop S4 (the (prnt S0 p)) jn (snum S0 p)"
  have psSv: "parent_spec (prnt Sv)" using stem_num_loop_fields[OF psN, THEN mp] psN by (simp add: Sv_def Su_def St_def Ss_def Sr_def Sq_def Sp_def Sfin_def split: option.split)
  define Sa where "Sa = fused_vin_loop Sv j j jn (lsuc Sv p) (snum S0 p) True True"
  define Sb where "Sb = (if jn \<noteq> the (rvth S0 p) \<and> j \<noteq> the (rvth S0 p) then fused_vout_loop Sa (the (prnt S0 p)) (if lsuc Sv jn = j then Some jn else None) (lsuc S0 p) (the (rvth S0 p)) jn (snum S0 p) True True else if lsuc Sv p \<noteq> lsuc S0 p then fused_vout_loop Sa (the (prnt S0 p)) (if lsuc Sv jn = j then Some jn else None) (lsuc S0 p) (lsuc Sv p) jn (snum S0 p) True True else fused_vout_loop Sa (the (prnt S0 p)) (if lsuc Sv jn = j then Some jn else None) (lsuc S0 p) (lsuc S0 p) jn (snum S0 p) False True)"
  have UTb: "update_tree S0 i j p jn = Sb" by (simp only: update_tree_def Let_def inep if_False if_True stem_loop_init prod.case Sb_def Sa_def Sv_def Su_def St_def Ss_def Sr_def Sq_def Sp_def)
  have SbS5: "Sb = S5" using update_tree_tail_eq[OF psSv] by (simp only: Sb_def Sa_def S5_def S4_def S3_def S2_def)
  have UT: "update_tree S0 i j p jn = S5" using UTb SbS5 by simp
  have pSp: "prnt Sp = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)" by (simp add: Sp_def Sfin_def)
  have pSq: "prnt Sq = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)" using pSp by (simp add: Sq_def split: option.split)
  have pSr: "prnt Sr = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)" using pSq by (simp add: Sr_def)
  have pSs: "prnt Ss = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)" using pSr by (simp add: Ss_def split: option.split)
  have pSt: "prnt St = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)" using pSs by (simp add: St_def)
  have pSu: "prnt Su = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)"
    using stem_num_loop_fields[OF psN, THEN mp, OF pSt] by (simp add: Su_def)
  have pSv: "prnt Sv = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)" using pSu by (simp add: Sv_def)
  have pS2: "prnt S2 = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)"
    using last_vin_loop_fields[OF psN, THEN mp, OF pSv] by (simp add: S2_def)
  have pS3: "prnt S3 = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)"
    using last_vout_loop_fields[OF psN, THEN mp, OF pS2] pS2 by (simp add: S3_def)
  have pS4: "prnt S4 = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)"
    using succ_vin_loop_fields[OF psN, THEN mp, OF pS3] by (simp add: S4_def)
  have pS5: "prnt S5 = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)"
    using succ_vout_loop_fields[OF psN, THEN mp, OF pS4] by (simp add: S5_def)
  have lsSp: "lsuc Sp = lsuc S0" by (simp add: Sp_def Sfin_def)
  have lsSq: "lsuc Sq = lsuc S0" using lsSp by (simp add: Sq_def split: option.split)
  have lsSr: "lsuc Sr = (lsuc S0)(p := lsx k)" using lsSq by (simp add: Sr_def)
  have lsSs: "lsuc Ss = (lsuc S0)(p := lsx k)" using lsSr by (simp add: Ss_def split: option.split)
  have lsSt: "lsuc St = (lsuc S0)(p := lsx k)" using lsSs by (simp add: St_def)
  have lsSu: "lsuc Su = (\<lambda>x. if x \<in> (\<lambda>y. the (((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) y)) ` set (takeWhile (\<lambda>z. z \<noteq> i) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) p)) then lsuc St p else lsuc St x)"
    using stem_num_loop_lsuc[OF psN, THEN mp, OF pSt, THEN mp, OF i_in_follow_newprnt] by (simp add: Su_def)
  have lsSvSu: "lsuc Sv = lsuc Su" by (simp add: Sv_def)
  have lsvz: "\<And>z. z \<notin> s ` {..k} \<Longrightarrow> lsuc Sv z = lsuc S0 z"
  proof -
    fix z assume zns: "z \<notin> s ` {..k}"
    have "z \<notin> (\<lambda>y. the (((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) y)) ` set (takeWhile (\<lambda>z. z \<noteq> i) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) p))"
      using imgStem_sub[OF kpos] zns by auto
    hence "lsuc Su z = lsuc St z" using lsSu by simp
    moreover have "z \<noteq> p" using zns pathk by auto
    ultimately show "lsuc Sv z = lsuc S0 z" using lsSvSu lsSt by simp
  qed
  have lsvp: "lsuc Sv p = lsx k"
  proof -
    have "lsuc Su p = lsuc St p" using lsSu by simp
    thus ?thesis using lsSvSu lsSt by simp
  qed
  have lsS5S3: "lsuc S5 = lsuc S3"
  proof -
    have "lsuc S4 = lsuc S3" using succ_vin_loop_fields[OF psN, THEN mp, OF pS3] by (simp add: S4_def)
    moreover have "lsuc S5 = lsuc S4" using succ_vout_loop_fields[OF psN, THEN mp, OF pS4] by (simp add: S5_def)
    ultimately show ?thesis by simp
  qed
  have CHcong: "takeWhile (\<lambda>y. lsuc Sv y = j) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) j) = takeWhile (\<lambda>y. lsuc S0 y = j) (follow (prnt S0) j)"
  proof -
    have fj: "follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) j = follow (prnt S0) j" by (rule follow_newprnt_j)
    have cong: "\<And>y. y \<in> set (follow (prnt S0) j) \<Longrightarrow> (lsuc Sv y = j) = (lsuc S0 y = j)"
    proof -
      fix y assume yj: "y \<in> set (follow (prnt S0) j)"
      have "y \<notin> s ` {..k}" using stem_notin_follow_j yj by auto
      thus "(lsuc Sv y = j) = (lsuc S0 y = j)" using lsvz by simp
    qed
    show ?thesis using takeWhile_cong[OF fj cong] using follow_newprnt_j by force
  qed
  have lsS2: "lsuc S2 = (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. lsuc Sv y = j) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) j)) then lsuc Sv p else lsuc Sv x)"
    using last_vin_loop_lsuc[OF psN, THEN mp, OF pSv] by (simp add: S2_def)
  have lvoutval: "\<And>stp gv sv. lsuc (last_vout_loop S2 (the (prnt S0 p)) stp gv sv) = (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. Some y \<noteq> stp \<and> lsuc S2 y = gv) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (the (prnt S0 p)))) then sv else lsuc S2 x)"
    using last_vout_loop_lsuc[OF psN, THEN mp, OF pS2] by simp
  have jnV: "jn \<in> V" using follow_subset_V[OF rinv jV] jnj by auto
  obtain vo where vo: "prnt S0 p = Some vo" using rooted_arborescense_invar_dom[OF rinv] pV pne_r by auto
  have voutp: "follow (prnt S0) p = p # follow (prnt S0) vo" using vo by (subst follow_ps_simps[OF ppt]) simp
  have voinp: "vo \<in> set (follow (prnt S0) p)" using voutp follow_hd_ps[OF ppt, of vo] follow_ne_ps[OF ppt, of vo] by (metis hd_in_set list.set_intros(2))
  have voutV: "the (prnt S0 p) \<in> V" using voinp follow_subset_V[OF rinv pV] vo by auto
  have lsvjn: "lsuc Sv jn = lsuc S0 jn" using lsvz jn_notin_stem[OF jnp pjn] by simp
  have lspin: "lsuc S0 p \<in> set (block S0 p)" using block_props(3)[OF arb pV] block_props(2)[OF arb pV] by (metis last_in_set)
  have thS5: "thrd S5 = final_thrd" using update_tree_thrd[OF kpos] by (simp add: UT[symmetric])
  have psF: "parent_spec (thrd S5)" using clauseB[OF kpos] by (simp add: UT[symmetric])
  have split: "follow (thrd S5) v = pre @ suf" using P1 by (simp add: UT)
  have setpre: "set pre = children (prnt S5) v" using P2 by (simp add: UT)
  have setpre2: "set pre = {u. v \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u)}"
    using setpre pS5 by (simp add: children_def)
  have lsvstem: "\<And>m. m < k \<Longrightarrow> lsuc Sv (s m) = lsx k"
  proof -
    fix m assume mk: "m < k"
    have "s (Suc m) \<in> s ` {1..<Suc k}" using mk by auto
    hence smem: "s (Suc m) \<in> set (takeWhile (\<lambda>x. x \<noteq> i) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) p))"
      using chainStem_set[OF kpos] by simp
    have ev: "((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (s (Suc m)) = Some (s_pred (Suc m))"
      using Wseq_eval[of "Suc k" "Suc m"] mk newprnt_eq by simp
    have "the (((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (s (Suc m))) = s m"
      using ev mk by (simp add: s_pred_def)
    hence smIMG: "s m \<in> (\<lambda>y. the (((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) y)) ` set (takeWhile (\<lambda>x. x \<noteq> i) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) p))"
      using smem by (metis (no_types, lifting) image_eqI)
    have "lsuc Su (s m) = lsuc St p" using lsSu smIMG by simp
    thus "lsuc Sv (s m) = lsx k" using lsSvSu lsSt by simp
  qed
  have skp: "s k = p" by (simp add: pathk)
  have lsvstemA: "\<And>z. z \<in> s ` {..k} \<Longrightarrow> lsuc Sv z = lsx k"
  proof -
    fix z assume "z \<in> s ` {..k}"
    then obtain m where mk: "m \<le> k" and zm: "z = s m" by auto
    show "lsuc Sv z = lsx k"
    proof (cases "m = k")
      case True thus ?thesis using zm lsvp skp by simp
    next
      case False hence "m < k" using mk by simp
      thus ?thesis using lsvstem zm by simp
    qed
  qed
  have lsS2v: "lsuc S2 v = (if v \<in> set (takeWhile (\<lambda>y. lsuc Sv y = j) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) j)) \<or> v \<in> s ` {..k} then lsx k else lsuc S0 v)"
  proof (cases "v \<in> set (takeWhile (\<lambda>y. lsuc Sv y = j) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) j))")
    case True thus ?thesis using lsS2 lsvp by simp
  next
    case False
    hence e: "lsuc S2 v = lsuc Sv v" using lsS2 by simp
    show ?thesis using e False lsvstemA lsvz by (cases "v \<in> s ` {..k}") auto
  qed
  have lsS3_offout: "\<And>u. u \<notin> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (the (prnt S0 p))) \<Longrightarrow> lsuc S3 u = lsuc S2 u"
  proof -
    fix u assume uout: "u \<notin> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (the (prnt S0 p)))"
    have unot: "\<And>STP GV. u \<notin> set (takeWhile (\<lambda>y. Some y \<noteq> STP \<and> lsuc S2 y = GV) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (the (prnt S0 p))))"
      using uout by (metis set_takeWhileD)
    show "lsuc S3 u = lsuc S2 u"
    proof (cases "jn \<noteq> the (rvth S0 p) \<and> j \<noteq> the (rvth S0 p)")
      case True
      have "S3 = last_vout_loop S2 (the (prnt S0 p)) (if lsuc Sv jn = j then Some jn else None) (lsuc S0 p) (the (rvth S0 p))"
        using True by (simp add: S3_def)
      thus ?thesis using lvoutval[of "if lsuc Sv jn = j then Some jn else None" "lsuc S0 p" "the (rvth S0 p)"] unot by simp
    next
      case c1: False
      show ?thesis
      proof (cases "lsuc Sv p \<noteq> lsuc S0 p")
        case True
        have "S3 = last_vout_loop S2 (the (prnt S0 p)) (if lsuc Sv jn = j then Some jn else None) (lsuc S0 p) (lsuc Sv p)"
          using c1 True by (auto simp add: S3_def)
        thus ?thesis using lvoutval[of "if lsuc Sv jn = j then Some jn else None" "lsuc S0 p" "lsuc Sv p"] unot by simp
      next
        case False
        have "S3 = S2" using c1 False by (auto simp add: S3_def)
        thus ?thesis by simp
      qed
    qed
  qed
  have setpreN: "set pre = children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v" using setpre pS5 by simp
  have stem_case: "v \<in> s ` {..k} \<Longrightarrow> lsuc S5 v \<in> set pre \<and> (thrd S5 (lsuc S5 v) = None \<or> the (thrd S5 (lsuc S5 v)) \<notin> set pre)"
  proof -
    assume vstem: "v \<in> s ` {..k}"
    then obtain t where tk: "t \<le> k" and vt: "v = s t" by auto
    have vnvout: "v \<notin> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (the (prnt S0 p)))"
      using stem_notin_follow_vout[OF kpos] vstem follow_newprnt_vout[OF kpos] by auto
    have val: "lsuc S5 v = lsx k" using lsS3_offout[OF vnvout] lsS2v vstem lsS5S3 by simp
    have id: "lsx k \<in> set pre" using stem_desc_lsxk[OF kpos jneq jnp pjn tk] vt setpreN by simp
    have sub: "set pre \<subseteq> set (block S0 p)" using children_stem_sub_blockp[OF kpos jneq jnp pjn tk] vt setpreN by simp
    have "final_thrd (lsx k) = None \<or> the (final_thrd (lsx k)) \<notin> set (block S0 p)" using final_thrd_lsxk_exits[OF kpos] by auto
    hence ie: "thrd S5 (lsx k) = None \<or> the (thrd S5 (lsx k)) \<notin> set pre" using thS5 sub by auto
    show "lsuc S5 v \<in> set pre \<and> (thrd S5 (lsuc S5 v) = None \<or> the (thrd S5 (lsuc S5 v)) \<notin> set pre)"
      using val id ie by simp
  qed
  have in_case: "v \<in> set (takeWhile (\<lambda>y. lsuc Sv y = j) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) j)) \<Longrightarrow> lsuc S5 v = lsx k \<Longrightarrow> lsuc S5 v \<in> set pre \<and> (thrd S5 (lsuc S5 v) = None \<or> the (thrd S5 (lsuc S5 v)) \<notin> set pre)"
  proof -
    assume vIN: "v \<in> set (takeWhile (\<lambda>y. lsuc Sv y = j) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) j))"
       and val: "lsuc S5 v = lsx k"
    have vINold: "v \<in> set (takeWhile (\<lambda>y. lsuc S0 y = j) (follow (prnt S0) j))" using vIN CHcong by simp
    have vj: "v \<in> set (follow (prnt S0) j)" using set_takeWhileD[OF vINold] by simp
    have lsvj: "lsuc S0 v = j" using set_takeWhileD[OF vINold] by simp
    have id: "lsx k \<in> set pre" using in_desc_lsxk[OF kpos vj] setpreN by simp
    have chj: "set pre = children (prnt S0) v \<union> set (block S0 p)" using setpreN children_newprnt_jpath[OF kpos vj] by simp
    have e1: "final_thrd (lsx k) = None \<or> the (final_thrd (lsx k)) \<notin> set (block S0 p)" using final_thrd_lsxk_exits[OF kpos] by auto
    have e2: "final_thrd (lsx k) = None \<or> the (final_thrd (lsx k)) \<notin> children (prnt S0) v" using final_thrd_lsxk_notin_INdesc[OF kpos vV lsvj] by auto
    have ie: "thrd S5 (lsx k) = None \<or> the (thrd S5 (lsx k)) \<notin> set pre" using e1 e2 thS5 chj by auto
    show ?thesis using val id ie by simp
  qed
  have out_case: "v \<in> set (follow (prnt S0) p) \<Longrightarrow> p \<noteq> v \<Longrightarrow> v \<notin> set (follow (prnt S0) j) \<Longrightarrow> the (rvth S0 p) \<noteq> j \<Longrightarrow> lsuc S0 v = lsuc S0 p \<Longrightarrow> lsuc S5 v = the (rvth S0 p) \<Longrightarrow> lsuc S5 v \<in> set pre \<and> (thrd S5 (lsuc S5 v) = None \<or> the (thrd S5 (lsuc S5 v)) \<notin> set pre)"
  proof -
    assume vp: "v \<in> set (follow (prnt S0) p)" and vnep: "p \<noteq> v" and vnj: "v \<notin> set (follow (prnt S0) j)"
       and orne: "the (rvth S0 p) \<noteq> j" and lsvp: "lsuc S0 v = lsuc S0 p" and val: "lsuc S5 v = the (rvth S0 p)"
    have id: "the (rvth S0 p) \<in> set pre" using old_rev_in_children_out[OF kpos vV vp vnep vnj] setpreN by simp
    have ie0: "final_thrd (the (rvth S0 p)) = None \<or> the (final_thrd (the (rvth S0 p))) \<notin> children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v"
      using final_thrd_oldrev_exits_out[OF kpos orne vV vp vnep vnj lsvp] by auto
    have ie: "thrd S5 (the (rvth S0 p)) = None \<or> the (thrd S5 (the (rvth S0 p))) \<notin> set pre" using ie0 thS5 setpreN by simp
    show ?thesis using val id ie by simp
  qed
  have unt_case: "lsuc S0 v \<notin> set (block S0 p) \<Longrightarrow> lsuc S0 v \<noteq> j \<Longrightarrow> lsuc S5 v = lsuc S0 v \<Longrightarrow> lsuc S5 v \<in> set pre \<and> (thrd S5 (lsuc S5 v) = None \<or> the (thrd S5 (lsuc S5 v)) \<notin> set pre)"
  proof -
    assume lsnb: "lsuc S0 v \<notin> set (block S0 p)" and lsj: "lsuc S0 v \<noteq> j" and val: "lsuc S5 v = lsuc S0 v"
    have id: "lsuc S0 v \<in> set pre" using untouched_i_desc[OF kpos vV lsnb] setpreN by simp
    have lsl: "lsuc S0 v \<notin> lsx ` {..k}"
    proof
      assume "lsuc S0 v \<in> lsx ` {..k}"
      then obtain m where mk: "m \<le> k" and e: "lsuc S0 v = lsx m" by auto
      show False using lsx_in_block_p[OF mk kpos] e lsnb by simp
    qed
    have lsb: "lsuc S0 v \<notin> bef ` set [0..<k]"
    proof
      assume "lsuc S0 v \<in> bef ` set [0..<k]"
      then obtain m where mk: "m \<in> set [0..<k]" and e: "lsuc S0 v = bef m" by auto
      have "m < k" using mk by simp
      thus False using bef_in_block_p[of m] e lsnb by simp
    qed
    have ie: "thrd S5 (lsuc S0 v) = None \<or> the (thrd S5 (lsuc S0 v)) \<notin> set pre"
    proof (cases "lsuc S0 v = the (rvth S0 p)")
      case ornev: False
      have "final_thrd (lsuc S0 v) = None \<or> the (final_thrd (lsuc S0 v)) \<notin> children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v"
        using untouched_ii_exit[OF kpos vV lsnb lsl lsb lsj ornev] by auto
      thus ?thesis using thS5 setpreN by simp
    next
      case oreq: True
      have rvdom: "dom (rvth S0) = V - {r}" using arb unfolding arb_invar_def by simp
      have pdom: "p \<in> dom (rvth S0)" using rvdom pV pne_r by simp
      have "rvth S0 p = Some (the (rvth S0 p))" using pdom by (metis domD option.sel)
      hence thop: "thrd S0 (the (rvth S0 p)) = Some p" using arb unfolding arb_invar_def by auto
      have pst: "parent_spec (thrd S0)" using arb unfolding arb_invar_def by simp
      have fvp: "follow (thrd S0) v = block S0 v @ follow (thrd S0) p"
        using block_props(1)[OF arb vV] thop oreq by simp
      show ?thesis
      proof (cases "the (rvth S0 p) = j")
        case True thus ?thesis using oreq lsj by simp
      next
        case orne2: False
        have fo: "final_thrd (the (rvth S0 p)) = thrd S0 (lsuc S0 p)" using final_thrd_oldrev[OF orne2] aftn_eq_thrd_lsuc_p by simp
        show ?thesis
        proof (cases "thrd S0 (lsuc S0 p)")
          case None thus ?thesis using fo oreq thS5 by simp
        next
          case (Some w)
          have fpw: "follow (thrd S0) p = block S0 p @ follow (thrd S0) w" using block_props(1)[OF arb pV] Some by simp
          have fv: "follow (thrd S0) v = block S0 v @ block S0 p @ follow (thrd S0) w" using fvp fpw by simp
          have win: "w \<in> set (follow (thrd S0) w)" using follow_hd_ps[OF pst, of w] follow_ne_ps[OF pst, of w] by (metis hd_in_set)
          have "distinct (follow (thrd S0) v)" by (rule follow_distinct_ps[OF pst])
          hence dist: "distinct (block S0 v @ block S0 p @ follow (thrd S0) w)" using fv by simp
          have wnv: "w \<notin> children (prnt S0) v" using dist win block_props(4)[OF arb vV] by (auto simp add: distinct_append)
          have wnb: "w \<notin> set (block S0 p)" using dist win by (auto simp add: distinct_append)
          have subA: "children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v \<subseteq> children (prnt S0) v \<union> set (block S0 p)"
            using children_newprnt_decomp[OF kpos] by auto
          have "w \<notin> set pre" using wnv wnb subA setpreN by auto
          thus ?thesis using fo Some oreq thS5 by simp
        qed
      qed
    qed
    show ?thesis using val id ie by simp
  qed
  have INiff: "lsuc S0 v = j \<Longrightarrow> v \<in> set (takeWhile (\<lambda>y. lsuc Sv y = j) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) j))"
  proof -
    assume lvj: "lsuc S0 v = j"
    have jbl: "j \<in> set (block S0 v)" using block_props(3)[OF arb vV] block_props(2)[OF arb vV] lvj by (metis last_in_set)
    have "j \<in> children (prnt S0) v" using jbl block_props(4)[OF arb vV] by simp
    hence vfj: "v \<in> set (follow (prnt S0) j)" unfolding children_def by simp
    obtain G H where GH: "follow (prnt S0) j = G @ v # H" using vfj by (meson split_list)
    have allG: "\<forall>y \<in> set G. lsuc S0 y = j"
    proof
      fix y assume yG: "y \<in> set G"
      then obtain G1 G2 where G12: "G = G1 @ y # G2" by (meson split_list)
      have fj2: "follow (prnt S0) j = G1 @ y # (G2 @ v # H)" using GH G12 by simp
      have "follow (prnt S0) y = y # (G2 @ v # H)" using follow_append_ps[OF ppt] fj2 by auto
      hence vfy: "v \<in> set (follow (prnt S0) y)" by simp
      have yfj: "y \<in> set (follow (prnt S0) j)" using GH G12 by simp
      have yV: "y \<in> V" using follow_subset_V[OF rinv jV] yfj by auto
      show "lsuc S0 y = j" using spine_lemma[OF lvj vV yV yfj vfy] by auto
    qed
    have "takeWhile (\<lambda>y. lsuc S0 y = j) (follow (prnt S0) j) = G @ takeWhile (\<lambda>y. lsuc S0 y = j) (v # H)"
      using GH allG by (simp add: takeWhile_append2)
    hence "v \<in> set (takeWhile (\<lambda>y. lsuc S0 y = j) (follow (prnt S0) j))" using lvj by simp
    thus "v \<in> set (takeWhile (\<lambda>y. lsuc Sv y = j) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) j))" using CHcong by simp
  qed
  have flsx: "\<And>t. t < k \<Longrightarrow> final_thrd (lsx t) = Some (s (Suc t))"
  proof -
    fix t assume tlt: "t < k"
    have ne_k: "lsx t \<noteq> lsx k" using lsx_inj_le[of t k] tlt by simp
    have inblk: "lsx t \<in> set (block S0 p)" using lsx_in_block_p[of t] tlt kpos by simp
    have ne_or: "lsx t \<noteq> the (rvth S0 p)" using inblk old_rev_notin_block_p by auto
    have "final_thrd (lsx t) = thrd_inv k (lsx t)" using final_thrd_off[OF ne_k ne_or] by auto
    also have "\<dots> = Some (s (Suc t))" by (rule thrd_inv_up[OF tlt])
    finally show "final_thrd (lsx t) = Some (s (Suc t))" .
  qed
  have cnb: "\<And>w. w \<in> set (block S0 p) \<Longrightarrow> w \<notin> s ` {..k} \<Longrightarrow> children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) w = children (prnt S0) w"
  proof -
    fix w assume wb: "w \<in> set (block S0 p)" and wns: "w \<notin> s ` {..k}"
    have eq: "\<And>u. (w \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u)) = (w \<in> set (follow (prnt S0) u))"
    proof -
      fix u
      show "(w \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u)) = (w \<in> set (follow (prnt S0) u))"
      proof (cases "u \<in> set (block S0 p)")
        case True thus ?thesis using newpath_nonstem_char[OF kpos wb wns] by auto
      next
        case False thus ?thesis using follow_newprnt_off_block[OF kpos False] by simp
      qed
    qed
    show "children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) w = children (prnt S0) w" unfolding children_def using eq by auto
  qed
  have bons: "\<And>w t''. w \<in> V \<Longrightarrow> w \<notin> s ` {..k} \<Longrightarrow> w \<in> set (block S0 p) \<Longrightarrow> t'' \<le> k \<Longrightarrow> s t'' \<notin> set (block S0 w)"
  proof -
    fix w t'' assume wV: "w \<in> V" and wns: "w \<notin> s ` {..k}" and wb: "w \<in> set (block S0 p)" and tkk: "t'' \<le> k"
    show "s t'' \<notin> set (block S0 w)"
    proof
      assume "s t'' \<in> set (block S0 w)"
      hence "s t'' \<in> children (prnt S0) w" using block_props(4)[OF arb wV] by simp
      hence wf: "w \<in> set (follow (prnt S0) (s t''))" unfolding children_def by simp
      have "follow (prnt S0) (s t'') = map s [t''..<Suc k] @ follow (prnt S0) (the (prnt S0 p))" using follow_stem_prefix[OF tkk] by auto
      hence "w \<in> set (map s [t''..<Suc k]) \<or> w \<in> set (follow (prnt S0) (the (prnt S0 p)))" using wf by auto
      thus False
      proof
        assume "w \<in> set (map s [t''..<Suc k])"
        hence "w \<in> s ` {..k}" by auto
        thus False using wns by simp
      next
        assume vvout: "w \<in> set (follow (prnt S0) (the (prnt S0 p)))"
        have wp: "w \<in> set (follow (prnt S0) p)" using vvout voutp vo by simp
        have "w \<in> children (prnt S0) p" using wb block_props(4)[OF arb pV] by simp
        hence pw: "p \<in> set (follow (prnt S0) w)" unfolding children_def by simp
        have "w = p" using ancestor_antisym[OF ppt wp pw] by auto
        thus False using wns pathk by auto
      qed
    qed
  qed
  have befcoll: "\<And>t. t < k \<Longrightarrow> defQ t = [] \<Longrightarrow> bef t = lsx (Suc t)"
  proof -
    fix t assume tlt: "t < k" and dq: "defQ t = []"
    have "lsuc S0 (s t) = lsuc S0 (s (Suc t))" by (rule defQ_empty[OF tlt dq])
    hence "lsx (Suc t) = the (rvth S0 (s t))" by (simp add: lsx_def)
    thus "bef t = lsx (Suc t)" by (simp add: bef_def)
  qed
  have u2ie: "\<And>w. w \<in> V \<Longrightarrow> w \<in> set (block S0 p) \<Longrightarrow> w \<notin> s ` {..k} \<Longrightarrow> final_thrd (lsuc S0 w) = None \<or> the (final_thrd (lsuc S0 w)) \<notin> children (prnt S0) w"
  proof -
    fix w assume wV: "w \<in> V" and wb: "w \<in> set (block S0 p)" and wns: "w \<notin> s ` {..k}"
    have pst: "parent_spec (thrd S0)" using arb unfolding arb_invar_def by simp
    have wpc: "w \<in> children (prnt S0) p" using wb block_props(4)[OF arb pV] by simp
    have "children (prnt S0) w \<subseteq> children (prnt S0) p" using wpc by (rule children_subset[OF ppt])
    hence bvsub: "set (block S0 w) \<subseteq> set (block S0 p)" using block_props(4)[OF arb wV] block_props(4)[OF arb pV] by simp
    have lsvin: "lsuc S0 w \<in> set (block S0 w)" using block_props(3)[OF arb wV] block_props(2)[OF arb wV] by (metis last_in_set)
    have lvb: "lsuc S0 w \<in> set (block S0 p)" using lsvin bvsub by auto
    show "final_thrd (lsuc S0 w) = None \<or> the (final_thrd (lsuc S0 w)) \<notin> children (prnt S0) w"
    proof (cases "lsuc S0 w \<in> lsx ` {..k}")
      case True
      then obtain t where tk: "t \<le> k" and elx: "lsuc S0 w = lsx t" by auto
      show ?thesis
      proof (cases "t < k")
        case tlt: True
        have sSk: "Suc t \<le> k" using tlt by simp
        have "final_thrd (lsx t) = Some (s (Suc t))" using flsx[OF tlt] by auto
        moreover have "s (Suc t) \<notin> set (block S0 w)" using bons[OF wV wns wb sSk] by auto
        ultimately show ?thesis using elx block_props(4)[OF arb wV] by auto
      next
        case False
        hence "t = k" using tk by simp
        hence "final_thrd (lsuc S0 w) = None \<or> the (final_thrd (lsuc S0 w)) \<notin> set (block S0 p)"
          using final_thrd_lsxk_exits[OF kpos] elx by simp
        thus ?thesis using bvsub block_props(4)[OF arb wV] by auto
      qed
    next
      case notlsx: False
      show ?thesis
      proof (cases "lsuc S0 w \<in> bef ` set [0..<k]")
        case True
        then obtain m where mk: "m \<in> set [0..<k]" and ebf: "lsuc S0 w = bef m" by auto
        have mlt: "m < k" using mk by simp
        have dqne: "defQ m \<noteq> []"
        proof
          assume "defQ m = []"
          hence "bef m = lsx (Suc m)" using befcoll[OF mlt] by simp
          moreover have "lsx (Suc m) \<in> lsx ` {..k}" using mlt by auto
          ultimately show False using notlsx ebf by simp
        qed
        have fbef: "final_thrd (bef m) = out m" using final_thrd_bef[OF mlt dqne] out_eq_hd_defQ[OF mlt dqne] by simp
        have thbef: "thrd S0 (bef m) = Some (s m)" using bef_pred(1)[OF mlt] by auto
        have smV: "s m \<in> V" using sV[of m] mlt by simp
        show ?thesis
        proof (cases "out m")
          case None thus ?thesis using fbef ebf by simp
        next
          case (Some x)
          have outw: "thrd S0 (lsuc S0 (s m)) = Some x" using Some by (simp add: out_def)
          have fvsm: "follow (thrd S0) w = block S0 w @ follow (thrd S0) (s m)"
            using block_props(1)[OF arb wV] ebf thbef by simp
          have fsmw: "follow (thrd S0) (s m) = block S0 (s m) @ follow (thrd S0) x"
            using block_props(1)[OF arb smV] outw by simp
          have fv: "follow (thrd S0) w = block S0 w @ block S0 (s m) @ follow (thrd S0) x" using fvsm fsmw by simp
          have win: "x \<in> set (follow (thrd S0) x)" using follow_hd_ps[OF pst, of x] follow_ne_ps[OF pst, of x] by (metis hd_in_set)
          have dv: "distinct (follow (thrd S0) w)" by (rule follow_distinct_ps[OF pst])
          hence "distinct (block S0 w @ block S0 (s m) @ follow (thrd S0) x)" using fv by simp
          hence "x \<notin> set (block S0 w)" using win by (auto simp add: distinct_append)
          hence "x \<notin> children (prnt S0) w" using block_props(4)[OF arb wV] by simp
          thus ?thesis using fbef Some ebf by simp
        qed
      next
        case notbef: False
        have "lsuc S0 w \<in> (\<Union>t\<in>set [0..<Suc k]. set (contrib t))" using lvb newblock_set newblock_def by auto
        then obtain t where tmem: "t \<in> set [0..<Suc k]" and inct: "lsuc S0 w \<in> set (contrib t)" by blast
        have tk': "t \<le> k" using tmem by auto
        have ff2: "final_thrd (lsuc S0 w) = thrd S0 (lsuc S0 w)" using contrib_fresh[OF inct tk' notlsx notbef] by auto
        show ?thesis
        proof (cases "thrd S0 (lsuc S0 w)")
          case None thus ?thesis using ff2 by simp
        next
          case (Some x)
          have "x \<notin> children (prnt S0) w" by (rule succ_lsuc_exits_block[OF wV Some])
          thus ?thesis using ff2 Some by simp
        qed
      qed
    qed
  qed
  have out_case_u: "v \<in> set (follow (prnt S0) p) \<Longrightarrow> p \<noteq> v \<Longrightarrow> the (rvth S0 p) \<noteq> j \<Longrightarrow> lsuc S0 v = lsuc S0 p \<Longrightarrow> lsuc S5 v = the (rvth S0 p) \<Longrightarrow> lsuc S5 v \<in> set pre \<and> (thrd S5 (lsuc S5 v) = None \<or> the (thrd S5 (lsuc S5 v)) \<notin> set pre)"
  proof -
    assume vp: "v \<in> set (follow (prnt S0) p)" and vnep: "p \<noteq> v" and orne: "the (rvth S0 p) \<noteq> j"
       and lsvp: "lsuc S0 v = lsuc S0 p" and val: "lsuc S5 v = the (rvth S0 p)"
    have orblk: "the (rvth S0 p) \<in> set (block S0 v)" using old_rev_in_block_anc[OF vV vp vnep] by auto
    have orch: "the (rvth S0 p) \<in> children (prnt S0) v" using orblk block_props(4)[OF arb vV] by simp
    have ornb: "the (rvth S0 p) \<notin> set (block S0 p)" by (rule old_rev_notin_block_p)
    have id: "the (rvth S0 p) \<in> set pre"
    proof -
      have "the (rvth S0 p) \<in> children (prnt S0) v - set (block S0 p)" using orch ornb by simp
      thus ?thesis using children_newprnt_supseteq[OF kpos] setpreN by auto
    qed
    have fo: "final_thrd (the (rvth S0 p)) = thrd S0 (lsuc S0 p)" using final_thrd_oldrev[OF orne] aftn_eq_thrd_lsuc_p by simp
    have subD: "set pre \<subseteq> children (prnt S0) v \<union> set (block S0 p)" using setpreN children_newprnt_decomp[OF kpos] by auto
    have ie: "thrd S5 (the (rvth S0 p)) = None \<or> the (thrd S5 (the (rvth S0 p))) \<notin> set pre"
    proof (cases "thrd S0 (lsuc S0 p)")
      case None thus ?thesis using fo thS5 by simp
    next
      case (Some w)
      have "thrd S0 (lsuc S0 v) = Some w" using Some lsvp by simp
      hence wnv: "w \<notin> children (prnt S0) v" using succ_lsuc_exits_block[OF vV] by simp
      have wnb: "w \<notin> set (block S0 p)" using succ_lsuc_exits_block[OF pV Some] block_props(4)[OF arb pV] by simp
      have "w \<notin> set pre" using wnv wnb subD by auto
      thus ?thesis using fo Some thS5 by simp
    qed
    show ?thesis using val id ie by simp
  qed
  have out_case_lsxk: "v \<in> set (follow (prnt S0) j) \<Longrightarrow> the (rvth S0 p) = j \<Longrightarrow> lsuc S0 v = lsuc S0 p \<Longrightarrow> lsuc S5 v = lsx k \<Longrightarrow> lsuc S5 v \<in> set pre \<and> (thrd S5 (lsuc S5 v) = None \<or> the (thrd S5 (lsuc S5 v)) \<notin> set pre)"
  proof -
    assume vj: "v \<in> set (follow (prnt S0) j)" and orj: "the (rvth S0 p) = j"
       and lsvp: "lsuc S0 v = lsuc S0 p" and val: "lsuc S5 v = lsx k"
    have id: "lsx k \<in> set pre" using in_desc_lsxk[OF kpos vj] setpreN by simp
    have chj: "set pre = children (prnt S0) v \<union> set (block S0 p)" using setpreN children_newprnt_jpath[OF kpos vj] by simp
    have fo: "final_thrd (lsx k) = thrd S0 (lsuc S0 p)" using final_thrd_lsx_k[OF kpos] orj by simp
    have ie: "thrd S5 (lsx k) = None \<or> the (thrd S5 (lsx k)) \<notin> set pre"
    proof (cases "thrd S0 (lsuc S0 p)")
      case None thus ?thesis using fo thS5 by simp
    next
      case (Some w)
      have "thrd S0 (lsuc S0 v) = Some w" using Some lsvp by simp
      hence wnv: "w \<notin> children (prnt S0) v" using succ_lsuc_exits_block[OF vV] by simp
      have wnb: "w \<notin> set (block S0 p)" using succ_lsuc_exits_block[OF pV Some] block_props(4)[OF arb pV] by simp
      have "w \<notin> set pre" using wnv wnb chj by simp
      thus ?thesis using fo Some thS5 by simp
    qed
    show ?thesis using val id ie by simp
  qed
  have notvout_case: "v \<notin> s ` {..k} \<Longrightarrow> v \<notin> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (the (prnt S0 p))) \<Longrightarrow> lsuc S5 v \<in> set pre \<and> (thrd S5 (lsuc S5 v) = None \<or> the (thrd S5 (lsuc S5 v)) \<notin> set pre)"
  proof -
    assume notstem: "v \<notin> s ` {..k}" and notvout: "v \<notin> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (the (prnt S0 p)))"
    have v3: "lsuc S5 v = lsuc S2 v" using lsS5S3 lsS3_offout[OF notvout] by simp
    show ?thesis
    proof (cases "v \<in> set (takeWhile (\<lambda>y. lsuc Sv y = j) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) j))")
      case IN: True
      have "lsuc S5 v = lsx k" using v3 lsS2v IN by simp
      thus ?thesis using in_case IN by simp
    next
      case notIN: False
      have vval: "lsuc S5 v = lsuc S0 v" using v3 lsS2v notIN notstem by simp
      show ?thesis
      proof (cases "v \<in> set (block S0 p)")
        case U2: True
        have id: "lsuc S0 v \<in> set pre"
        proof -
          have "lsuc S0 v \<in> set (block S0 v)" using block_props(3)[OF arb vV] block_props(2)[OF arb vV] by (metis last_in_set)
          hence "lsuc S0 v \<in> children (prnt S0) v" using block_props(4)[OF arb vV] by simp
          hence "lsuc S0 v \<in> children ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) v" using cnb[OF U2 notstem] by simp
          thus ?thesis using setpreN by simp
        qed
        have ie: "thrd S5 (lsuc S0 v) = None \<or> the (thrd S5 (lsuc S0 v)) \<notin> set pre"
        proof -
          have e: "final_thrd (lsuc S0 v) = None \<or> the (final_thrd (lsuc S0 v)) \<notin> children (prnt S0) v" using u2ie[OF vV U2 notstem] by auto
          have "children (prnt S0) v = set pre" using cnb[OF U2 notstem] setpreN by simp
          thus ?thesis using e thS5 by auto
        qed
        show ?thesis using vval id ie by simp
      next
        case notblk: False
        have lsj: "lsuc S0 v \<noteq> j" using notIN INiff by auto
        have pstem: "p \<in> s ` {..k}" using skp by auto
        have vnep: "v \<noteq> p" using notstem pstem by auto
        have lsnb: "lsuc S0 v \<notin> set (block S0 p)"
        proof
          assume lb: "lsuc S0 v \<in> set (block S0 p)"
          have lsvin: "lsuc S0 v \<in> set (block S0 v)" using block_props(3)[OF arb vV] block_props(2)[OF arb vV] by (metis last_in_set)
          have vanc: "v \<in> set (follow (prnt S0) (lsuc S0 v))" using lsvin block_props(4)[OF arb vV] unfolding children_def by simp
          have panc: "p \<in> set (follow (prnt S0) (lsuc S0 v))" using lb block_props(4)[OF arb pV] unfolding children_def by simp
          have "v \<in> set (follow (prnt S0) p) \<or> p \<in> set (follow (prnt S0) v)" using follow_linear[OF ppt vanc panc] by auto
          thus False
          proof
            assume vfp: "v \<in> set (follow (prnt S0) p)"
            have "v \<in> set (follow (prnt S0) vo)" using vfp voutp vnep by simp
            hence "v \<in> set (follow (prnt S0) (the (prnt S0 p)))" using vo by simp
            hence "v \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (the (prnt S0 p)))" using follow_newprnt_vout[OF kpos] by simp
            thus False using notvout by simp
          next
            assume "p \<in> set (follow (prnt S0) v)"
            hence "v \<in> children (prnt S0) p" unfolding children_def by simp
            hence "v \<in> set (block S0 p)" using block_props(4)[OF arb pV] by simp
            thus False using notblk by simp
          qed
        qed
        show ?thesis using unt_case[OF lsnb lsj vval] by auto
      qed
    qed
  qed
  have lst_ij: "last (follow (prnt S0) i) = last (follow (prnt S0) j)"
    using last_follow_root[OF rinv iV] last_follow_root[OF rinv jV] by simp
  have iblk: "i \<in> set (block S0 p)" using stem_in_block[OF kpos le0] path0 by simp
  have p_anc_i: "p \<in> set (follow (prnt S0) i)"
    using iblk block_props(4)[OF arb pV] unfolding children_def by simp
  have outset_lsuc_p: "v \<in> set (takeWhile (\<lambda>y. Some y \<noteq> (if lsuc Sv jn = j then Some jn else None) \<and> lsuc S2 y = lsuc S0 p) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (the (prnt S0 p)))) \<Longrightarrow> lsuc S0 v = lsuc S0 p"
  proof -
    assume vout: "v \<in> set (takeWhile (\<lambda>y. Some y \<noteq> (if lsuc Sv jn = j then Some jn else None) \<and> lsuc S2 y = lsuc S0 p) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (the (prnt S0 p))))"
    have s2v: "lsuc S2 v = lsuc S0 p" using set_takeWhileD[OF vout] by simp
    have vin_vout0: "v \<in> set (follow (prnt S0) (the (prnt S0 p)))"
      using set_takeWhileD[OF vout] follow_newprnt_vout[OF kpos] by simp
    have vnstem: "v \<notin> s ` {..k}" using vin_vout0 stem_notin_follow_vout[OF kpos] by auto
    have vfp: "v \<in> set (follow (prnt S0) p)" using vin_vout0 voutp vo by simp
    have vnIN: "v \<notin> set (takeWhile (\<lambda>y. lsuc Sv y = j) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) j))"
    proof
      assume vIN: "v \<in> set (takeWhile (\<lambda>y. lsuc Sv y = j) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) j))"
      have vINold: "v \<in> set (takeWhile (\<lambda>y. lsuc S0 y = j) (follow (prnt S0) j))" using vIN CHcong by simp
      have vfj: "v \<in> set (follow (prnt S0) j)" using set_takeWhileD[OF vINold] by simp
      have lsvj0: "lsuc S0 v = j" using set_takeWhileD[OF vINold] by simp
      have vfi: "v \<in> set (follow (prnt S0) i)" using follow_trans[OF ppt p_anc_i vfp] by auto
      have vfjn: "v \<in> set (follow (prnt S0) jn)" using join_of_first[OF ppt lst_ij vfi vfj] jneq by simp
      have "lsuc S0 jn = j" using spine_lemma[OF lsvj0 vV jnV jnj vfjn] by auto
      hence stpj: "lsuc Sv jn = j" using lsvjn by simp
      have jnvout: "jn \<in> set (follow (prnt S0) (the (prnt S0 p)))" using jnp voutp vo pjn by auto
      obtain A B where AB: "follow (prnt S0) (the (prnt S0 p)) = A @ jn # B" using jnvout by (meson split_list)
      have fjn2: "follow (prnt S0) jn = jn # B" using follow_append_ps[OF ppt] AB by auto
      have vne_jn: "v \<noteq> jn" using set_takeWhileD[OF vout] stpj by auto
      have vB: "v \<in> set B" using vfjn fjn2 vne_jn by simp
      have Pjn: "\<not> (Some jn \<noteq> (if lsuc Sv jn = j then Some jn else None) \<and> lsuc S2 jn = lsuc S0 p)" using stpj by simp
      have fvout_np: "follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (the (prnt S0 p)) = A @ jn # B" using AB follow_newprnt_vout[OF kpos] by simp
      have sub: "set (takeWhile (\<lambda>y. Some y \<noteq> (if lsuc Sv jn = j then Some jn else None) \<and> lsuc S2 y = lsuc S0 p) (A @ jn # B)) \<subseteq> set A"
      proof (cases "\<forall>a\<in>set A. Some a \<noteq> (if lsuc Sv jn = j then Some jn else None) \<and> lsuc S2 a = lsuc S0 p")
        case True
        have "takeWhile (\<lambda>y. Some y \<noteq> (if lsuc Sv jn = j then Some jn else None) \<and> lsuc S2 y = lsuc S0 p) (A @ jn # B) = A @ takeWhile (\<lambda>y. Some y \<noteq> (if lsuc Sv jn = j then Some jn else None) \<and> lsuc S2 y = lsuc S0 p) (jn # B)"
          using True by (simp add: takeWhile_append2)
        also have "takeWhile (\<lambda>y. Some y \<noteq> (if lsuc Sv jn = j then Some jn else None) \<and> lsuc S2 y = lsuc S0 p) (jn # B) = []" using Pjn by simp
        finally show ?thesis by simp
      next
        case False
        then obtain a where "a \<in> set A" and "\<not> (Some a \<noteq> (if lsuc Sv jn = j then Some jn else None) \<and> lsuc S2 a = lsuc S0 p)" by blast
        hence "takeWhile (\<lambda>y. Some y \<noteq> (if lsuc Sv jn = j then Some jn else None) \<and> lsuc S2 y = lsuc S0 p) (A @ jn # B) = takeWhile (\<lambda>y. Some y \<noteq> (if lsuc Sv jn = j then Some jn else None) \<and> lsuc S2 y = lsuc S0 p) A"
          by (simp add: takeWhile_append1)
        thus ?thesis by (auto dest: set_takeWhileD)
      qed
      have "v \<in> set A" using vout fvout_np sub by auto
      moreover have "distinct (A @ jn # B)" using AB follow_distinct_ps[OF ppt, of "the (prnt S0 p)"] by simp
      ultimately show False using vB by auto
    qed
    have "lsuc S2 v = lsuc Sv v" using vnIN lsS2 by simp
    hence "lsuc S2 v = lsuc S0 v" using lsvz vnstem by simp
    thus "lsuc S0 v = lsuc S0 p" using s2v by simp
  qed
  have lpnej: "lsuc S0 p \<noteq> j" using lspin j_notin_block_p by auto
  have p_anc_lsp: "p \<in> set (follow (prnt S0) (lsuc S0 p))"
    using lspin block_props(4)[OF arb pV] unfolding children_def by simp
  have outset_iff: "v \<in> set (follow (prnt S0) (the (prnt S0 p))) \<Longrightarrow> lsuc S0 v = lsuc S0 p \<Longrightarrow> v \<in> set (takeWhile (\<lambda>y. Some y \<noteq> (if lsuc Sv jn = j then Some jn else None) \<and> lsuc S2 y = lsuc S0 p) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (the (prnt S0 p))))"
  proof -
    assume vfvo: "v \<in> set (follow (prnt S0) (the (prnt S0 p)))" and lvp: "lsuc S0 v = lsuc S0 p"
    obtain G H where GH: "follow (prnt S0) (the (prnt S0 p)) = G @ v # H" using vfvo by (meson split_list)
    have Pv: "Some v \<noteq> (if lsuc Sv jn = j then Some jn else None) \<and> lsuc S2 v = lsuc S0 p"
    proof -
      have vnstem: "v \<notin> s ` {..k}" using vfvo stem_notin_follow_vout[OF kpos] by auto
      have "Some v \<noteq> (if lsuc Sv jn = j then Some jn else None)"
      proof (cases "lsuc Sv jn = j")
        case True
        have "lsuc S0 jn = j" using True lsvjn by simp
        hence "v \<noteq> jn" using lvp lpnej by auto
        thus ?thesis using True by simp
      next
        case False thus ?thesis by simp
      qed
      moreover have "lsuc S2 v = lsuc S0 p"
      proof (cases "v \<in> set (takeWhile (\<lambda>z. lsuc Sv z = j) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) j))")
        case True
        hence "lsuc S0 v = j" using CHcong set_takeWhileD by (metis (mono_tags, lifting))
        thus ?thesis using lvp lpnej by simp
      next
        case False
        thus ?thesis using lsS2 lvp lsvz vnstem by simp
      qed
      ultimately show ?thesis by simp
    qed
    have allG: "\<forall>y \<in> set G. Some y \<noteq> (if lsuc Sv jn = j then Some jn else None) \<and> lsuc S2 y = lsuc S0 p"
    proof
      fix y assume yG: "y \<in> set G"
      then obtain G1 G2 where G12: "G = G1 @ y # G2" by (meson split_list)
      have fj2: "follow (prnt S0) (the (prnt S0 p)) = G1 @ y # (G2 @ v # H)" using GH G12 by simp
      have "follow (prnt S0) y = y # (G2 @ v # H)" using follow_append_ps[OF ppt] fj2 by auto
      hence vfy: "v \<in> set (follow (prnt S0) y)" by simp
      have yfvo: "y \<in> set (follow (prnt S0) (the (prnt S0 p)))" using GH G12 by simp
      have yV: "y \<in> V" using follow_subset_V[OF rinv voutV] yfvo by auto
      have ynstem: "y \<notin> s ` {..k}" using yfvo stem_notin_follow_vout[OF kpos] by auto
      have yfp: "y \<in> set (follow (prnt S0) p)" using yfvo voutp vo by simp
      have yflsp: "y \<in> set (follow (prnt S0) (lsuc S0 p))" using follow_trans[OF ppt p_anc_lsp yfp] by auto
      have lsy: "lsuc S0 y = lsuc S0 p" using spine_lemma[OF lvp vV yV yflsp vfy] by auto
      have "Some y \<noteq> (if lsuc Sv jn = j then Some jn else None)"
      proof (cases "lsuc Sv jn = j")
        case True
        have "lsuc S0 jn = j" using True lsvjn by simp
        hence "y \<noteq> jn" using lsy lpnej by auto
        thus ?thesis using True by simp
      next
        case False thus ?thesis by simp
      qed
      moreover have "lsuc S2 y = lsuc S0 p"
      proof (cases "y \<in> set (takeWhile (\<lambda>z. lsuc Sv z = j) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) j))")
        case True
        hence "lsuc S0 y = j" using CHcong set_takeWhileD by (metis (mono_tags, lifting))
        thus ?thesis using lsy lpnej by simp
      next
        case False
        thus ?thesis using lsS2 lsy lsvz ynstem by simp
      qed
      ultimately show "Some y \<noteq> (if lsuc Sv jn = j then Some jn else None) \<and> lsuc S2 y = lsuc S0 p" by simp
    qed
    have "takeWhile (\<lambda>y. Some y \<noteq> (if lsuc Sv jn = j then Some jn else None) \<and> lsuc S2 y = lsuc S0 p) (follow (prnt S0) (the (prnt S0 p))) = G @ takeWhile (\<lambda>y. Some y \<noteq> (if lsuc Sv jn = j then Some jn else None) \<and> lsuc S2 y = lsuc S0 p) (v # H)"
      using GH allG by (simp add: takeWhile_append2)
    hence "v \<in> set (takeWhile (\<lambda>y. Some y \<noteq> (if lsuc Sv jn = j then Some jn else None) \<and> lsuc S2 y = lsuc S0 p) (follow (prnt S0) (the (prnt S0 p))))" using Pv by simp
    thus ?thesis using follow_newprnt_vout[OF kpos] by simp
  qed
  have orv_jn_vac: "the (rvth S0 p) = jn \<Longrightarrow> j \<noteq> jn \<Longrightarrow> lsuc S0 v = lsuc S0 p \<Longrightarrow> v \<in> set (follow (prnt S0) p) \<Longrightarrow> p \<noteq> v \<Longrightarrow> False"
  proof -
    assume orjn: "the (rvth S0 p) = jn" and jnej: "j \<noteq> jn" and lvp: "lsuc S0 v = lsuc S0 p"
       and vp: "v \<in> set (follow (prnt S0) p)" and vnep: "p \<noteq> v"
    have pst: "parent_spec (thrd S0)" using arb unfolding arb_invar_def by simp
    have rvdom: "dom (rvth S0) = V - {r}" using arb unfolding arb_invar_def by simp
    have pdom: "p \<in> dom (rvth S0)" using rvdom pV pne_r by simp
    have "rvth S0 p = Some (the (rvth S0 p))" using pdom by (metis domD option.sel)
    hence "rvth S0 p = Some jn" using orjn by simp
    hence thjnp: "thrd S0 jn = Some p" using arb unfolding arb_invar_def by auto
    have orblk: "jn \<in> set (block S0 v)" using old_rev_in_block_anc[OF vV vp vnep] orjn by simp
    hence "jn \<in> children (prnt S0) v" using block_props(4)[OF arb vV] by simp
    hence vfjn: "v \<in> set (follow (prnt S0) jn)" unfolding children_def by simp
    have jnflsp: "jn \<in> set (follow (prnt S0) (lsuc S0 p))" using follow_trans[OF ppt p_anc_lsp jnp] by auto
    have lsjn: "lsuc S0 jn = lsuc S0 p" using spine_lemma[OF lvp vV jnV jnflsp vfjn] by auto
    have jnnb: "jn \<notin> set (block S0 p)"
    proof
      assume "jn \<in> set (block S0 p)"
      hence "jn \<in> children (prnt S0) p" using block_props(4)[OF arb pV] by simp
      hence "p \<in> set (follow (prnt S0) jn)" unfolding children_def by simp
      hence "jn = p" using ancestor_antisym[OF ppt jnp] by simp
      thus False using pjn by simp
    qed
    have jnne: "jn \<noteq> lsuc S0 p" using jnnb lspin by auto
    have fjn: "follow (thrd S0) jn = jn # follow (thrd S0) p" using thjnp by (subst follow_ps_simps[OF pst]) simp
    have bjn: "block S0 jn = jn # block S0 p" using fjn lsjn jnne by (simp add: block_def)
    have "j \<in> children (prnt S0) jn" using jnj unfolding children_def by simp
    hence "j \<in> set (block S0 jn)" using block_props(4)[OF arb jnV] by simp
    hence "j \<in> insert jn (set (block S0 p))" using bjn by simp
    thus False using jnej j_notin_block_p by simp
  qed
  have route_lsuc2: "v \<notin> s ` {..k} \<Longrightarrow> lsuc S5 v = lsuc S2 v \<Longrightarrow> (v \<notin> set (takeWhile (\<lambda>y. lsuc Sv y = j) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) j)) \<Longrightarrow> lsuc S0 v \<notin> set (block S0 p)) \<Longrightarrow> lsuc S5 v \<in> set pre \<and> (thrd S5 (lsuc S5 v) = None \<or> the (thrd S5 (lsuc S5 v)) \<notin> set pre)"
  proof -
    assume notstem: "v \<notin> s ` {..k}" and v5': "lsuc S5 v = lsuc S2 v"
      and lsnbH: "v \<notin> set (takeWhile (\<lambda>y. lsuc Sv y = j) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) j)) \<Longrightarrow> lsuc S0 v \<notin> set (block S0 p)"
    show ?thesis
    proof (cases "v \<in> set (takeWhile (\<lambda>y. lsuc Sv y = j) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) j))")
      case IN: True
      have "lsuc S5 v = lsx k" using v5' lsS2v IN by simp
      thus ?thesis using in_case IN by simp
    next
      case notIN: False
      have vval: "lsuc S5 v = lsuc S0 v" using v5' lsS2v notIN notstem by simp
      have lsj: "lsuc S0 v \<noteq> j" using notIN INiff by auto
      have lsnb: "lsuc S0 v \<notin> set (block S0 p)" using lsnbH notIN by simp
      show ?thesis using unt_case[OF lsnb lsj vval] by auto
    qed
  qed
  have main2: "lsuc S5 v \<in> set pre \<and> (thrd S5 (lsuc S5 v) = None \<or> the (thrd S5 (lsuc S5 v)) \<notin> set pre)"
  proof (cases "v \<in> s ` {..k}")
    case True thus ?thesis using stem_case by simp
  next
    case notstem: False
    show ?thesis
    proof (cases "v \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (the (prnt S0 p)))")
      case False thus ?thesis using notvout_case[OF notstem] by simp
    next
      case isvout: True
      have vin_vout0: "v \<in> set (follow (prnt S0) (the (prnt S0 p)))" using isvout follow_newprnt_vout[OF kpos] by simp
      have vfp: "v \<in> set (follow (prnt S0) p)" using vin_vout0 voutp vo by simp
      have pstem: "p \<in> s ` {..k}" using skp by auto
      have vnep: "p \<noteq> v" using notstem pstem by auto
      have lsnb_prov: "v \<notin> set (takeWhile (\<lambda>y. Some y \<noteq> (if lsuc Sv jn = j then Some jn else None) \<and> lsuc S2 y = lsuc S0 p) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (the (prnt S0 p)))) \<Longrightarrow> v \<notin> set (takeWhile (\<lambda>y. lsuc Sv y = j) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) j)) \<Longrightarrow> lsuc S0 v \<notin> set (block S0 p)"
      proof -
        assume notOUT: "v \<notin> set (takeWhile (\<lambda>y. Some y \<noteq> (if lsuc Sv jn = j then Some jn else None) \<and> lsuc S2 y = lsuc S0 p) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (the (prnt S0 p))))"
        show "lsuc S0 v \<notin> set (block S0 p)"
        proof
          assume lb: "lsuc S0 v \<in> set (block S0 p)"
          have "lsuc S0 v \<in> children (prnt S0) p" using lb block_props(4)[OF arb pV] by simp
          hence pflv: "p \<in> set (follow (prnt S0) (lsuc S0 v))" unfolding children_def by simp
          have "lsuc S0 v = lsuc S0 p" using spine_lemma[OF refl vV pV pflv vfp] by simp
          hence "v \<in> set (takeWhile (\<lambda>y. Some y \<noteq> (if lsuc Sv jn = j then Some jn else None) \<and> lsuc S2 y = lsuc S0 p) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (the (prnt S0 p))))" using outset_iff[OF vin_vout0] by simp
          thus False using notOUT by simp
        qed
      qed
      show ?thesis
      proof (cases "jn \<noteq> the (rvth S0 p) \<and> j \<noteq> the (rvth S0 p)")
        case br1: True
        have orne: "the (rvth S0 p) \<noteq> j" using br1 by auto
        have S3eq: "S3 = last_vout_loop S2 (the (prnt S0 p)) (if lsuc Sv jn = j then Some jn else None) (lsuc S0 p) (the (rvth S0 p))"
          using br1 by (simp add: S3_def)
        have v5: "lsuc S5 v = (if v \<in> set (takeWhile (\<lambda>y. Some y \<noteq> (if lsuc Sv jn = j then Some jn else None) \<and> lsuc S2 y = lsuc S0 p) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (the (prnt S0 p)))) then the (rvth S0 p) else lsuc S2 v)"
          using lsS5S3 S3eq lvoutval[of "if lsuc Sv jn = j then Some jn else None" "lsuc S0 p" "the (rvth S0 p)"] by simp
        show ?thesis
        proof (cases "v \<in> set (takeWhile (\<lambda>y. Some y \<noteq> (if lsuc Sv jn = j then Some jn else None) \<and> lsuc S2 y = lsuc S0 p) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (the (prnt S0 p))))")
          case OUT: True
          have lvp: "lsuc S0 v = lsuc S0 p" using outset_lsuc_p OUT by simp
          have val: "lsuc S5 v = the (rvth S0 p)" using v5 OUT by simp
          show ?thesis using out_case_u[OF vfp vnep orne lvp val] by auto
        next
          case notOUT: False
          have v5': "lsuc S5 v = lsuc S2 v" using v5 notOUT by simp
          show ?thesis using route_lsuc2[OF notstem v5' lsnb_prov[OF notOUT]] by auto
        qed
      next
        case br23: False
        show ?thesis
        proof (cases "lsuc Sv p \<noteq> lsuc S0 p")
          case br2: True
          have S3eq: "S3 = last_vout_loop S2 (the (prnt S0 p)) (if lsuc Sv jn = j then Some jn else None) (lsuc S0 p) (lsuc Sv p)"
            using br23 br2 by (auto simp add: S3_def)
          have v5: "lsuc S5 v = (if v \<in> set (takeWhile (\<lambda>y. Some y \<noteq> (if lsuc Sv jn = j then Some jn else None) \<and> lsuc S2 y = lsuc S0 p) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (the (prnt S0 p)))) then lsuc Sv p else lsuc S2 v)"
            using lsS5S3 S3eq lvoutval[of "if lsuc Sv jn = j then Some jn else None" "lsuc S0 p" "lsuc Sv p"] by simp
          show ?thesis
          proof (cases "v \<in> set (takeWhile (\<lambda>y. Some y \<noteq> (if lsuc Sv jn = j then Some jn else None) \<and> lsuc S2 y = lsuc S0 p) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (the (prnt S0 p))))")
            case OUT: True
            have lvp: "lsuc S0 v = lsuc S0 p" using outset_lsuc_p OUT by simp
            have jorv: "the (rvth S0 p) = j"
            proof (rule ccontr)
              assume ne: "the (rvth S0 p) \<noteq> j"
              hence "the (rvth S0 p) = jn" using br23 by auto
              hence "j \<noteq> jn" using ne by simp
              show False using orv_jn_vac[OF \<open>the (rvth S0 p) = jn\<close> \<open>j \<noteq> jn\<close> lvp vfp vnep] by auto
            qed
            have vfj: "v \<in> set (follow (prnt S0) j)"
            proof -
              have "the (rvth S0 p) \<in> set (block S0 v)" using old_rev_in_block_anc[OF vV vfp vnep] by auto
              hence "j \<in> children (prnt S0) v" using jorv block_props(4)[OF arb vV] by simp
              thus ?thesis unfolding children_def by simp
            qed
            have val: "lsuc S5 v = lsx k" using v5 OUT lsvp by simp
            show ?thesis using out_case_lsxk[OF vfj jorv lvp val] by auto
          next
            case notOUT: False
            have v5': "lsuc S5 v = lsuc S2 v" using v5 notOUT by simp
            show ?thesis using route_lsuc2[OF notstem v5' lsnb_prov[OF notOUT]] by auto
          qed
        next
          case br3: False
          have S3eq: "S3 = S2" using br23 br3 by (auto simp add: S3_def)
          have v5': "lsuc S5 v = lsuc S2 v" using lsS5S3 S3eq by simp
          have lxlp: "lsx k = lsuc S0 p" using br3 lsvp by simp
          show ?thesis
          proof (cases "v \<in> set (takeWhile (\<lambda>y. lsuc Sv y = j) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) j))")
            case IN: True
            have "lsuc S5 v = lsx k" using v5' lsS2v IN by simp
            thus ?thesis using in_case IN by simp
          next
            case notIN: False
            have vval: "lsuc S5 v = lsuc S0 v" using v5' lsS2v notIN notstem by simp
            show ?thesis
            proof (cases "lsuc S0 v \<in> set (block S0 p)")
              case inblk: True
              have "lsuc S0 v \<in> children (prnt S0) p" using inblk block_props(4)[OF arb pV] by simp
              hence pflv: "p \<in> set (follow (prnt S0) (lsuc S0 v))" unfolding children_def by simp
              have lvp: "lsuc S0 v = lsuc S0 p" using spine_lemma[OF refl vV pV pflv vfp] by simp
              have jorv: "the (rvth S0 p) = j"
              proof (rule ccontr)
                assume ne: "the (rvth S0 p) \<noteq> j"
                hence "the (rvth S0 p) = jn" using br23 by auto
                hence "j \<noteq> jn" using ne by simp
                show False using orv_jn_vac[OF \<open>the (rvth S0 p) = jn\<close> \<open>j \<noteq> jn\<close> lvp vfp vnep] by auto
              qed
              have vfj: "v \<in> set (follow (prnt S0) j)"
              proof -
                have "the (rvth S0 p) \<in> set (block S0 v)" using old_rev_in_block_anc[OF vV vfp vnep] by auto
                hence "j \<in> children (prnt S0) v" using jorv block_props(4)[OF arb vV] by simp
                thus ?thesis unfolding children_def by simp
              qed
              have val: "lsuc S5 v = lsx k" using vval lvp lxlp by simp
              show ?thesis using out_case_lsxk[OF vfj jorv lvp val] by auto
            next
              case notblk: False
              have lsj: "lsuc S0 v \<noteq> j" using notIN INiff by auto
              show ?thesis using unt_case[OF notblk lsj vval] by auto
            qed
          qed
        qed
      qed
    qed
  qed
  have sel: "\<And>SS vv pp ss xx. parent_spec (thrd SS) \<Longrightarrow> follow (thrd SS) vv = pp @ ss \<Longrightarrow> xx \<in> set pp \<Longrightarrow> (thrd SS xx = None \<or> the (thrd SS xx) \<notin> set pp) \<Longrightarrow> xx = last pp"
  proof -
    fix SS vv pp ss xx
    assume psF': "parent_spec (thrd SS)" and split': "follow (thrd SS) vv = pp @ ss"
       and xin': "xx \<in> set pp" and exit': "thrd SS xx = None \<or> the (thrd SS xx) \<notin> set pp"
    show "xx = last pp"
    proof (rule ccontr)
      assume xnl: "xx \<noteq> last pp"
      have prene: "pp \<noteq> []" using xin' by auto
      obtain idx where idxlt: "idx < length pp" and byidx: "pp ! idx = xx" using xin' by (meson in_set_conv_nth)
      have "idx \<noteq> length pp - 1"
      proof
        assume e: "idx = length pp - 1"
        have "xx = last pp" using byidx e last_conv_nth[OF prene] by simp
        thus False using xnl by simp
      qed
      hence si: "Suc idx < length pp" using idxlt by simp
      define yy where "yy = pp ! Suc idx"
      have yin: "yy \<in> set pp" using si yy_def by simp
      have t1: "take (Suc idx) pp = take idx pp @ [xx]" using idxlt byidx by (simp add: take_Suc_conv_app_nth)
      have t2: "take (Suc (Suc idx)) pp = take idx pp @ [xx, yy]" using si t1 yy_def by (simp add: take_Suc_conv_app_nth)
      have predecomp: "pp = take idx pp @ xx # yy # drop (Suc (Suc idx)) pp"
        using t2 append_take_drop_id[of "Suc (Suc idx)" pp] by (metis append.assoc append_Cons append_Nil)
      have fsplit: "follow (thrd SS) vv = take idx pp @ xx # yy # (drop (Suc (Suc idx)) pp @ ss)"
        using split' predecomp by simp
      have "thrd SS xx = Some yy" by (rule thread_link[OF psF' fsplit])
      thus False using exit' yin by simp
    qed
  qed
  have i_desc: "lsuc S5 v \<in> set pre" using main2 by simp
  have ii_exit: "thrd S5 (lsuc S5 v) = None \<or> the (thrd S5 (lsuc S5 v)) \<notin> set pre" using main2 by simp
  show ?thesis unfolding UT using sel[OF psF split i_desc ii_exit] . qed

text \<open>\<^bold>\<open>Clause J of @{const arb_invar} for @{const update_tree}\<close>: assembled from the contiguity

     half @{thm clauseJ_contig} and the pointwise-lsuc half @{thm lsuc_last} via @{thm clauseJ_from_lsuc}.\<close>
lemma clauseJ:
  assumes kpos: "0 < k" and jneq: "jn = join_of (prnt S0) i j"
    and jnp: "jn \<in> set (follow (prnt S0) p)" and pjn: "p \<noteq> jn"
  shows "\<forall>v\<in>V. \<exists>pre. follow (thrd (update_tree S0 i j p jn)) v
           = pre @ (case thrd (update_tree S0 i j p jn) (lsuc (update_tree S0 i j p jn) v) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd (update_tree S0 i j p jn)) w)
           \<and> pre \<noteq> [] \<and> last pre = lsuc (update_tree S0 i j p jn) v \<and> set pre = children (prnt (update_tree S0 i j p jn)) v"
  using clauseJ_from_lsuc[OF kpos jneq jnp pjn lsuc_last[OF kpos jneq jnp pjn]] 
  by fastforce

lemma set_drt_k: "set (drt k) = insert j (lsx ` {..<k})"
  by (auto simp: drt_def)

lemma distinct_drt_k:
  assumes kpos: "0 < k" shows "distinct (drt k)"
proof -
  have inj: "inj_on lsx {0..<k}"
  proof (rule inj_onI)
    fix x y assume xk: "x \<in> {0..<k}" and yk: "y \<in> {0..<k}" and eq: "lsx x = lsx y"
    have "x \<le> k" "y \<le> k" using xk yk by auto
    thus "x = y" using lsx_inj_le[of x y] eq by fastforce
  qed
  have dm: "distinct (map lsx [0..<k])" using inj by (simp add: distinct_map)
  have jni: "j \<notin> lsx ` {..<k}" using j_notin_lsx_img[OF kpos] by (simp add: atLeast0LessThan)
  have "distinct (j # map lsx [0..<k])" using dm jni by (auto simp: atLeast0LessThan)
  thus ?thesis by (simp add: drt_def)
qed

lemma final_thrd_target_in_V:
  assumes kpos: "0 < k" and xy: "final_thrd x = Some y" shows "y \<in> V"
proof -
  obtain i where "Suc i < length newlist" and "newlist ! i = x" and yi: "newlist ! Suc i = y"
    using final_thrd_reverse_chain[OF kpos xy] by auto
  hence "y \<in> set newlist" using yi by (metis nth_mem)
  thus ?thesis using set_newlist by simp
qed

lemma rvth_Sfin: "rvth Sfin = rvth S0 ++ revBR k"
  by (simp add: Sfin_def)

lemma final_thrd_inj:
  assumes kpos: "0 < k" and a: "final_thrd v = Some w" and b: "final_thrd v' = Some w"
  shows "v = v'"
proof -
  obtain i where i1: "Suc i < length newlist" and iv: "newlist ! i = v" and iw: "newlist ! Suc i = w"
    using final_thrd_reverse_chain[OF kpos a] by auto
  obtain i' where i1': "Suc i' < length newlist" and iv': "newlist ! i' = v'" and iw': "newlist ! Suc i' = w"
    using final_thrd_reverse_chain[OF kpos b] by auto
  have "newlist ! Suc i = newlist ! Suc i'" using iw iw' by simp
  hence "Suc i = Suc i'" using distinct_newlist i1 i1' by (simp add: nth_eq_iff_index_eq)
  thus ?thesis using iv iv' by simp
qed

lemma final_rvth_at_dirty_target:
  assumes kpos: "0 < k" and uin: "u \<in> set (drt k)" and fu: "final_thrd u = Some w"
  shows "final_rvth w = Some u"
proof -
  have Pcong: "\<And>u'. u' \<in> set (drt k) \<Longrightarrow> (final_thrd u' = Some w) = (u' = u)"
  proof -
    fix u' assume "u' \<in> set (drt k)"
    show "(final_thrd u' = Some w) = (u' = u)"
    proof
      assume "final_thrd u' = Some w" thus "u' = u" using fu final_thrd_inj[OF kpos] by auto
    next
      assume "u' = u" thus "final_thrd u' = Some w" using fu by simp
    qed
  qed
  have filt: "filter (\<lambda>u'. final_thrd u' = Some w) (drt k) = [u]"
  proof -
    have "filter (\<lambda>u'. final_thrd u' = Some w) (drt k) = filter (\<lambda>u'. u' = u) (drt k)"
      by (rule filter_cong[OF refl]) (simp add: Pcong)
    also have "\<dots> = [u]" using distinct_drt_k[OF kpos] uin by (rule filter_eq_self_single)
    finally show ?thesis .
  qed
  have ex: "\<exists>u'\<in>set (drt k). final_thrd u' = Some w" using uin fu by auto
  have "final_rvth w = Some (last (filter (\<lambda>u'. final_thrd u' = Some w) (drt k)))"
    unfolding final_rvth_def Let_def by (subst foldl_upd_eval) (simp add: ex)
  thus ?thesis using filt by simp
qed

definition rvth_pre where "rvth_pre = (let tc = (if the (rvth S0 p) = j then thrd S0 (lsuc S0 p) else thrd S0 j); r1 = (case tc of None \<Rightarrow> rvth Sfin | Some a \<Rightarrow> (rvth Sfin)(a \<mapsto> lsx k)) in (if the (rvth S0 p) \<noteq> j then (case aftn k of None \<Rightarrow> r1 | Some a \<Rightarrow> r1(a \<mapsto> the (rvth S0 p))) else r1))"

lemma final_rvth_fold: "final_rvth = foldl (\<lambda>R u. case final_thrd u of None \<Rightarrow> R | Some w \<Rightarrow> R(w \<mapsto> u)) rvth_pre (drt k)"
  by (simp add: final_rvth_def rvth_pre_def Let_def)

lemma final_rvth_eval:
  "final_rvth w = (if (\<exists>u\<in>set (drt k). final_thrd u = Some w) then Some (last (filter (\<lambda>u. final_thrd u = Some w) (drt k))) else rvth_pre w)"
  by (subst final_rvth_fold) (rule foldl_upd_eval)

lemma rvth_pre_at_Sq:
  assumes kpos: "0 < k" and fw: "final_thrd (lsx k) = Some w"
  shows "rvth_pre w = Some (lsx k)"
proof -
  have tceq: "(if the (rvth S0 p) = j then thrd S0 (lsuc S0 p) else thrd S0 j) = Some w"
    using final_thrd_lsx_k[OF kpos] fw by simp
  have r1w: "((rvth Sfin)(w \<mapsto> lsx k)) w = Some (lsx k)" by simp
  show ?thesis
  proof (cases "the (rvth S0 p) = j")
    case True thus ?thesis using tceq r1w by (simp add: rvth_pre_def Let_def)
  next
    case False
    show ?thesis
    proof (cases "aftn k")
      case None thus ?thesis using tceq r1w False by (simp add: rvth_pre_def Let_def)
    next
      case (Some a)
      have "w \<noteq> a"
      proof
        assume "w = a"
        have "final_thrd (the (rvth S0 p)) = aftn k" by (rule final_thrd_oldrev[OF False])
        hence "final_thrd (the (rvth S0 p)) = Some w" using Some \<open>w = a\<close> by simp
        hence "the (rvth S0 p) = lsx k" using fw final_thrd_inj[OF kpos] by auto
        moreover have "lsx k \<in> set (block S0 p)" using lsx_in_block_p[of k] kpos by simp
        ultimately show False using old_rev_notin_block_p by auto
      qed
      thus ?thesis using tceq r1w False Some by (simp add: rvth_pre_def Let_def)
    qed
  qed
qed

lemma rvth_pre_at_Ss:
  assumes kpos: "0 < k" and orne: "the (rvth S0 p) \<noteq> j" and fw: "final_thrd (the (rvth S0 p)) = Some w"
  shows "rvth_pre w = Some (the (rvth S0 p))"
proof -
  have "final_thrd (the (rvth S0 p)) = aftn k" by (rule final_thrd_oldrev[OF orne])
  hence aw: "aftn k = Some w" using fw by simp
  show ?thesis using orne aw by (simp add: rvth_pre_def Let_def)
qed

text \<open>The {\isasymsection}12.5 BR/UP collision: when @{term "defQ t = []"} the bridge source @{term "bef t"} coincides
      with the up-link key @{term "lsx (Suc t)"} (so it is a dirty node when @{term "Suc t < k"}, or
      @{term "lsx k"} when @{term "Suc t = k"}); hence a non-dirty @{term "bef t"} (other than @{term "lsx k"})
      has @{term "defQ t \<noteq> []"} and its BR edge survives into @{const final_thrd}.\<close>
lemma bef_non_dirty_defQ:
  assumes tk: "t < k" and nd: "bef t \<notin> set (drt k)" and nlk: "bef t \<noteq> lsx k"
  shows "defQ t \<noteq> []"
proof
  assume dq: "defQ t = []"
  have bc: "bef t = lsx (Suc t)" by (rule bef_collision[OF tk dq])
  show False
  proof (cases "Suc t < k")
    case True
    have "lsx (Suc t) \<in> lsx ` {..<k}" using True by auto
    hence "bef t \<in> set (drt k)" using bc by (simp add: set_drt_k)
    thus False using nd by simp
  next
    case False
    hence "Suc t = k" using tk by simp
    thus False using bc nlk by simp
  qed
qed

lemma out_collision:
  assumes tk: "t < k" and dq: "defQ t = []" shows "out t = out (Suc t)"
proof -
  have "lsuc S0 (s t) = lsuc S0 (s (Suc t))" by (rule defQ_empty[OF tk dq])
  thus ?thesis by (simp add: out_def)
qed

text \<open>The reverse value @{const revBR} records for @{term v'} comes from a NON-collision index (the
      last-write @{term t} cannot have @{term "defQ t = []"} with @{term "Suc t < k"}, else the tie
      @{term "out (Suc t) = out t"} would override it); so unless it is @{term "lsx k"} its BR edge
      survives, giving @{term "final_thrd v = Some v'"} --- the BR case of clause G.\<close>
lemma revBR_value_nondirty:
  assumes kpos: "0 < k" and rb: "revBR k v' = Some v" and nlk: "v \<noteq> lsx k"
  shows "\<exists>t<k. out t = Some v' \<and> bef t = v \<and> defQ t \<noteq> []"
proof -
  obtain t where tk: "t < k" and ot: "out t = Some v'" and bt: "bef t = v"
    and mx: "\<forall>t'. t < t' \<longrightarrow> t' < k \<longrightarrow> out t' \<noteq> Some v'"
    using revBR_eval_last[OF rb] by auto
  have "defQ t \<noteq> []"
  proof
    assume dq: "defQ t = []"
    have bc: "bef t = lsx (Suc t)" by (rule bef_collision[OF tk dq])
    show False
    proof (cases "Suc t < k")
      case True
      have "out (Suc t) = out t" using out_collision[OF tk dq] by simp
      hence "out (Suc t) = Some v'" using ot by simp
      thus False using mx True by simp
    next
      case False
      hence "Suc t = k" using tk by simp
      hence "bef t = lsx k" using bc by simp
      thus False using bt nlk by simp
    qed
  qed
  thus ?thesis using tk ot bt by auto
qed

lemma final_thrd_of_revBR:
  assumes kpos: "0 < k" and rb: "revBR k v' = Some v" and nlk: "v \<noteq> lsx k"
  shows "final_thrd v = Some v'"
proof -
  obtain t where tk: "t < k" and ot: "out t = Some v'" and bt: "bef t = v" and dq: "defQ t \<noteq> []"
    using revBR_value_nondirty[OF kpos rb nlk] by auto
  have "final_thrd (bef t) = Some (hd (defQ t))" by (rule final_thrd_bef[OF tk dq])
  moreover have "out t = Some (hd (defQ t))" by (rule out_eq_hd_defQ[OF tk dq])
  ultimately show ?thesis using ot bt by simp
qed

text \<open>The root has no predecessor in the new thread (it is @{term "newlist ! 0"}); so @{term r} is not
      in the range of @{const final_thrd} --- a step towards @{term "dom final_rvth = V - {r}"} (clause F).\<close>
lemma r_notin_ran_final_thrd:
  assumes kpos: "0 < k" shows "final_thrd v \<noteq> Some r"
proof
  assume "final_thrd v = Some r"
  then obtain i where i1: "Suc i < length newlist" and iw: "newlist ! Suc i = r"
    using final_thrd_reverse_chain[OF kpos] by auto
  have i0lt: "0 < length newlist" using newlist_ne by auto
  have hd0: "newlist ! 0 = r" using hd_newlist newlist_ne by (simp add: hd_conv_nth)
  have "newlist ! Suc i = newlist ! 0" using iw hd0 by simp
  hence "Suc i = 0" using distinct_newlist i1 i0lt by (simp add: nth_eq_iff_index_eq)
  thus False by simp
qed

text \<open>If the value @{const revBR} records for @{term v'} is @{term "lsx k"}, then @{term v'} is a splice
      target (the Sq continuation @{const final_thrd} of @{term "lsx k"}, or the Ss look-ahead @{const aftn}):
      the collision run ending at @{term "k - 1"} makes  "out (k - 1) = out k = aftn k".  Hence off
      the splice targets @{const revBR} never yields @{term "lsx k"}, so @{thm final_thrd_of_revBR} applies.\<close>
lemma revBR_lsxk_splice:
  assumes kpos: "0 < k" and rb: "revBR k v' = Some (lsx k)"
  shows "final_thrd (lsx k) = Some v' \<or> aftn k = Some v'"
proof -
  obtain t where tk: "t < k" and ot: "out t = Some v'" and bt: "bef t = lsx k"
    using revBR_eval_ex[OF rb] by auto
  show ?thesis
  proof (cases "defQ t = []")
    case False
    have "final_thrd (bef t) = Some (hd (defQ t))" by (rule final_thrd_bef[OF tk False])
    moreover have "out t = Some (hd (defQ t))" by (rule out_eq_hd_defQ[OF tk False])
    ultimately have "final_thrd (lsx k) = Some v'" using ot bt by simp
    thus ?thesis by simp
  next
    case True
    have bc: "bef t = lsx (Suc t)" by (rule bef_collision[OF tk True])
    have "lsx (Suc t) = lsx k" using bc bt by simp
    hence "Suc t = k" using lsx_inj_le[of "Suc t" k] tk by fastforce
    hence "out t = out (Suc t)" using out_collision[OF tk True] by simp
    hence "aftn k = Some v'" using ot \<open>Suc t = k\<close> by (simp add: aftn_def)
    thus ?thesis by simp
  qed
qed

text \<open>Off the two splice targets (@{term "final_thrd (lsx k)"} and, when @{term "the (rvth S0 p) \<noteq> j"},
      @{const aftn}), @{const rvth_pre} is just @{term "rvth S0 ++ revBR k"} (the Sq/Ss splices do not fire).\<close>
lemma rvth_pre_off_splice:
  assumes kpos: "0 < k" and tcne: "final_thrd (lsx k) \<noteq> Some v'"
    and aftne: "the (rvth S0 p) \<noteq> j \<Longrightarrow> aftn k \<noteq> Some v'"
  shows "rvth_pre v' = (rvth S0 ++ revBR k) v'"
proof -
  have tc': "(if the (rvth S0 p) = j then thrd S0 (lsuc S0 p) else thrd S0 j) \<noteq> Some v'"
    using final_thrd_lsx_k[OF kpos] tcne by simp
  have r1v: "(case (if the (rvth S0 p) = j then thrd S0 (lsuc S0 p) else thrd S0 j) of None \<Rightarrow> rvth Sfin | Some a \<Rightarrow> (rvth Sfin)(a \<mapsto> lsx k)) v' = rvth Sfin v'"
  proof (cases "if the (rvth S0 p) = j then thrd S0 (lsuc S0 p) else thrd S0 j")
    case None thus ?thesis by simp
  next
    case (Some a)
    have "a \<noteq> v'" using tc' Some by auto
    thus ?thesis using Some by simp
  qed
  show ?thesis
  proof (cases "the (rvth S0 p) = j")
    case True thus ?thesis using r1v by (simp add: rvth_pre_def Let_def rvth_Sfin)
  next
    case False
    have anev: "aftn k \<noteq> Some v'" using aftne False by simp
    show ?thesis
    proof (cases "aftn k")
      case None thus ?thesis using False r1v by (simp add: rvth_pre_def Let_def rvth_Sfin)
    next
      case (Some a)
      have ane: "a \<noteq> v'" using anev Some by auto
      have "rvth_pre v' = ((case (if the (rvth S0 p) = j then thrd S0 (lsuc S0 p) else thrd S0 j) of None \<Rightarrow> rvth Sfin | Some b \<Rightarrow> (rvth Sfin)(b \<mapsto> lsx k))(a \<mapsto> the (rvth S0 p))) v'"
        using False Some by (simp add: rvth_pre_def Let_def)
      also have "\<dots> = (case (if the (rvth S0 p) = j then thrd S0 (lsuc S0 p) else thrd S0 j) of None \<Rightarrow> rvth Sfin | Some b \<Rightarrow> (rvth Sfin)(b \<mapsto> lsx k)) v'"
        using ane by simp
      also have "\<dots> = rvth Sfin v'" using r1v by simp
      finally show ?thesis by (simp add: rvth_Sfin)
    qed
  qed
qed

lemma final_lsxk_of_splice:
  assumes kpos: "0 < k" and disj: "final_thrd (lsx k) = Some v' \<or> aftn k = Some v'"
    and aftne: "the (rvth S0 p) \<noteq> j \<Longrightarrow> aftn k \<noteq> Some v'"
  shows "final_thrd (lsx k) = Some v'"
proof (cases "final_thrd (lsx k) = Some v'")
  case True thus ?thesis .
next
  case False
  hence aw: "aftn k = Some v'" using disj by simp
  have "the (rvth S0 p) = j" using aftne aw by auto
  hence "final_thrd (lsx k) = thrd S0 (lsuc S0 p)" using final_thrd_lsx_k[OF kpos] by simp
  also have "\<dots> = aftn k" using aftn_eq_thrd_lsuc_p by simp
  also have "\<dots> = Some v'" using aw by simp
  finally show ?thesis .
qed

text \<open>Clause G, forward direction: every new-thread edge @{term "final_thrd v = Some v'"} is realised by
      the rebuilt reverse thread, @{term "final_rvth v' = Some v"}.  Case split on @{term v}: dirty node
      (@{thm final_rvth_at_dirty_target}), the two splice sources @{term "lsx k"}/@{term "the (rvth S0 p)"}
      (@{thm rvth_pre_at_Sq}/@{thm rvth_pre_at_Ss}), a surviving BR bridge (@{thm final_thrd_of_revBR}), or
      an untouched old edge (@{thm final_thrd_fresh} + clause G for @{term S0}).\<close>
lemma clauseG_fwd:
  assumes kpos: "0 < k" and fv: "final_thrd v = Some v'"
  shows "final_rvth v' = Some v"
proof (cases "v \<in> set (drt k)")
  case True
  show ?thesis by (rule final_rvth_at_dirty_target[OF kpos True fv])
next
  case notdirty: False
  have ndt: "\<not> (\<exists>u\<in>set (drt k). final_thrd u = Some v')"
  proof
    assume "\<exists>u\<in>set (drt k). final_thrd u = Some v'"
    then obtain u where uin: "u \<in> set (drt k)" and fu: "final_thrd u = Some v'" by auto
    have "u = v" using fu fv final_thrd_inj[OF kpos] by auto
    thus False using uin notdirty by simp
  qed
  have FRE: "final_rvth v' = rvth_pre v'" using final_rvth_eval[of v'] ndt by simp
  consider (Sq) "v = lsx k" | (Ss) "v = the (rvth S0 p)" | (rest) "v \<noteq> lsx k" "v \<noteq> the (rvth S0 p)" by auto
  then show ?thesis
  proof cases
    case Sq
    hence "rvth_pre v' = Some (lsx k)" using rvth_pre_at_Sq[OF kpos] fv by simp
    thus ?thesis using FRE Sq by simp
  next
    case Ss
    have orne: "the (rvth S0 p) \<noteq> j"
    proof
      assume "the (rvth S0 p) = j"
      hence "v = j" using Ss by simp
      moreover have "j \<in> set (drt k)" by (simp add: drt_def)
      ultimately show False using notdirty by simp
    qed
    have "rvth_pre v' = Some (the (rvth S0 p))" using rvth_pre_at_Ss[OF kpos orne] fv Ss by simp
    thus ?thesis using FRE Ss by simp
  next
    case rest
    have tcne: "final_thrd (lsx k) \<noteq> Some v'"
    proof
      assume "final_thrd (lsx k) = Some v'"
      hence "lsx k = v" using fv final_thrd_inj[OF kpos] by auto
      thus False using rest by simp
    qed
    have aftne: "the (rvth S0 p) \<noteq> j \<Longrightarrow> aftn k \<noteq> Some v'"
    proof -
      assume orne: "the (rvth S0 p) \<noteq> j"
      show "aftn k \<noteq> Some v'"
      proof
        assume "aftn k = Some v'"
        hence "final_thrd (the (rvth S0 p)) = Some v'" using final_thrd_oldrev[OF orne] by simp
        hence "the (rvth S0 p) = v" using fv final_thrd_inj[OF kpos] by auto
        thus False using rest by simp
      qed
    qed
    have RP: "rvth_pre v' = (rvth S0 ++ revBR k) v'" by (rule rvth_pre_off_splice[OF kpos tcne aftne])
    show ?thesis
    proof (cases "v' \<in> dom (revBR k)")
      case True
      then obtain w0 where rb: "revBR k v' = Some w0" by auto
      have w0ne: "w0 \<noteq> lsx k"
      proof
        assume "w0 = lsx k"
        hence "revBR k v' = Some (lsx k)" using rb by simp
        hence "final_thrd (lsx k) = Some v' \<or> aftn k = Some v'" by (rule revBR_lsxk_splice[OF kpos])
        hence "final_thrd (lsx k) = Some v'" using final_lsxk_of_splice[OF kpos _ aftne] by simp
        thus False using tcne by simp
      qed
      have "final_thrd w0 = Some v'" by (rule final_thrd_of_revBR[OF kpos rb w0ne])
      hence "w0 = v" using fv final_thrd_inj[OF kpos] by auto
      hence "(rvth S0 ++ revBR k) v' = Some v" using rb by (simp add: map_add_def)
      thus ?thesis using FRE RP by simp
    next
      case norev: False
      hence rvNone: "revBR k v' = None" by (simp add: dom_def)
      have vfresh: "final_thrd v = thrd S0 v"
      proof (rule final_thrd_fresh)
        show "v \<notin> lsx ` {..k}"
        proof
          assume "v \<in> lsx ` {..k}"
          then obtain t where tk: "t \<le> k" and vt: "v = lsx t" by auto
          show False
          proof (cases "t = k")
            case True thus False using vt rest by simp
          next
            case False
            hence "t < k" using tk by simp
            hence "lsx t \<in> lsx ` {..<k}" by auto
            hence "v \<in> set (drt k)" using vt by (simp add: set_drt_k)
            thus False using notdirty by simp
          qed
        qed
        show "v \<notin> bef ` set [0..<k]"
        proof
          assume "v \<in> bef ` set [0..<k]"
          then obtain t where tk: "t < k" and vt: "v = bef t" by auto
          have b1: "bef t \<notin> set (drt k)" using notdirty vt by simp
          have b2: "bef t \<noteq> lsx k" using rest vt by simp
          have defQ: "defQ t \<noteq> []" by (rule bef_non_dirty_defQ[OF tk b1 b2])
          have "final_thrd (bef t) = Some (hd (defQ t))" by (rule final_thrd_bef[OF tk defQ])
          moreover have "out t = Some (hd (defQ t))" by (rule out_eq_hd_defQ[OF tk defQ])
          ultimately have "final_thrd v = out t" using vt by simp
          hence oteq: "out t = Some v'" using fv by simp
          have "v' \<in> dom (revBR k)"
          proof -
            have "v' = the (out t)" using oteq by simp
            moreover have "t \<in> {t. t < k \<and> out t \<noteq> None}" using tk oteq by auto
            ultimately show ?thesis by (auto simp: revBR_dom)
          qed
          thus False using norev by simp
        qed
        show "v \<noteq> j" using notdirty by (auto simp: drt_def)
        show "v \<noteq> the (rvth S0 p)" using rest by simp
      qed
      hence "thrd S0 v = Some v'" using fv by simp
      hence "rvth S0 v' = Some v" using arb unfolding arb_invar_def by auto
      hence "(rvth S0 ++ revBR k) v' = Some v" using rvNone by (simp add: map_add_def)
      thus ?thesis using FRE RP by simp
    qed
  qed
qed

lemma thrd_S0_ran:
  assumes "thrd S0 x = Some y" shows "y \<in> V \<and> y \<noteq> r"
proof -
  have G: "\<forall>v v'. thrd S0 v = Some v' \<longleftrightarrow> rvth S0 v' = Some v" using arb unfolding arb_invar_def by simp
  have F: "dom (rvth S0) = V - {r}" using arb unfolding arb_invar_def by simp
  have "rvth S0 y = Some x" using assms G by auto
  hence "y \<in> dom (rvth S0)" by auto
  thus ?thesis using F by auto
qed

lemma revBR_dom_sub: "dom (revBR k) \<subseteq> V - {r}"
proof
  fix v' assume "v' \<in> dom (revBR k)"
  then obtain w where "revBR k v' = Some w" by auto
  then obtain t where "t < k" and "out t = Some v'" using revBR_eval_ex by auto
  hence "thrd S0 (lsuc S0 (s t)) = Some v'" by (simp add: out_def)
  thus "v' \<in> V - {r}" using thrd_S0_ran by simp
qed

text \<open>Every non-root vertex of @{term V} has a predecessor in the new thread (it is  "newlist ! Suc i"
      for some @{term i}); combined with @{thm r_notin_ran_final_thrd} this pins @{term "ran final_thrd = V - {r}"}.\<close>
lemma ran_final_thrd_ge:
  assumes kpos: "0 < k" and vV: "v' \<in> V" and vne: "v' \<noteq> r"
  shows "\<exists>v. final_thrd v = Some v'"
proof -
  have "v' \<in> set newlist" using vV set_newlist by simp
  then obtain m where mlt: "m < length newlist" and vm: "newlist ! m = v'"
    by (metis in_set_conv_nth)
  have hd0: "newlist ! 0 = r" using hd_newlist newlist_ne by (simp add: hd_conv_nth)
  have m0: "m \<noteq> 0"
  proof
    assume "m = 0"
    hence "v' = r" using vm hd0 by simp
    thus False using vne by simp
  qed
  then obtain i where mi: "m = Suc i" using not0_implies_Suc by auto
  have "Suc i < length newlist" using mlt mi by simp
  hence "final_thrd (newlist ! i) = Some (newlist ! Suc i)" by (rule newlist_link[OF kpos])
  hence "final_thrd (newlist ! i) = Some v'" using vm mi by simp
  thus ?thesis by auto
qed

text \<open>The reverse thread's domain: any key it maps is a non-root vertex (a splice target in @{term "V - {r}"},
      a @{const revBR} out-target, or an old @{const rvth} key @{term "V - {r}"}).\<close>
lemma rvth_pre_dom:
  assumes kpos: "0 < k" and rp: "rvth_pre v' = Some v" shows "v' \<in> V \<and> v' \<noteq> r"
proof (cases "final_thrd (lsx k) = Some v'")
  case True
  have "v' \<in> V" using final_thrd_target_in_V[OF kpos True] by auto
  moreover have "v' \<noteq> r" using r_notin_ran_final_thrd[OF kpos] True by auto
  ultimately show ?thesis by simp
next
  case tcF: False
  show ?thesis
  proof (cases "the (rvth S0 p) \<noteq> j \<and> aftn k = Some v'")
    case True
    hence orne: "the (rvth S0 p) \<noteq> j" and aw: "aftn k = Some v'" by auto
    have ft: "final_thrd (the (rvth S0 p)) = Some v'" using final_thrd_oldrev[OF orne] aw by simp
    have "v' \<in> V" using final_thrd_target_in_V[OF kpos ft] by auto
    moreover have "v' \<noteq> r" using r_notin_ran_final_thrd[OF kpos] ft by auto
    ultimately show ?thesis by simp
  next
    case False
    have aftne: "the (rvth S0 p) \<noteq> j \<Longrightarrow> aftn k \<noteq> Some v'" using False by auto
    have "rvth_pre v' = (rvth S0 ++ revBR k) v'" by (rule rvth_pre_off_splice[OF kpos tcF aftne])
    hence "(rvth S0 ++ revBR k) v' = Some v" using rp by simp
    hence "v' \<in> dom (rvth S0) \<union> dom (revBR k)" by (auto simp: map_add_def split: option.splits)
    thus ?thesis using arb revBR_dom_sub unfolding arb_invar_def by auto
  qed
qed

text \<open>Clause G (both directions): @{const final_thrd} and @{const final_rvth} are mutually inverse.
      Forward is @{thm clauseG_fwd}; backward uses that inclusion of partial functions plus
      @{term "dom final_rvth \<subseteq> ran final_thrd"} (@{thm ran_final_thrd_ge}, @{thm rvth_pre_dom}).\<close>
lemma clauseG:
  assumes kpos: "0 < k"
  shows "(final_thrd v = Some v') = (final_rvth v' = Some v)"
proof
  assume "final_thrd v = Some v'"
  thus "final_rvth v' = Some v" by (rule clauseG_fwd[OF kpos])
next
  assume fr: "final_rvth v' = Some v"
  have vVr: "v' \<in> V \<and> v' \<noteq> r"
  proof (cases "\<exists>u\<in>set (drt k). final_thrd u = Some v'")
    case True
    then obtain u where fu: "final_thrd u = Some v'" by auto
    have "v' \<in> V" using final_thrd_target_in_V[OF kpos fu] by auto
    moreover have "v' \<noteq> r" using r_notin_ran_final_thrd[OF kpos] fu by auto
    ultimately show ?thesis by simp
  next
    case False
    hence "final_rvth v' = rvth_pre v'" using final_rvth_eval[of v'] by simp
    hence "rvth_pre v' = Some v" using fr by simp
    thus ?thesis by (rule rvth_pre_dom[OF kpos])
  qed
  then obtain u where fu: "final_thrd u = Some v'" using ran_final_thrd_ge[OF kpos] by auto
  have "final_rvth v' = Some u" by (rule clauseG_fwd[OF kpos fu])
  hence "u = v" using fr by simp
  thus "final_thrd v = Some v'" using fu by simp
qed

text \<open>Clause F for the reverse thread: @{term "dom final_rvth = V - {r}"} --- its domain is exactly the
      range of @{const final_thrd} (@{thm clauseG}), which is @{term "V - {r}"}.\<close>
lemma dom_final_rvth:
  assumes kpos: "0 < k" shows "dom final_rvth = V - {r}"
proof
  show "dom final_rvth \<subseteq> V - {r}"
  proof
    fix v' assume "v' \<in> dom final_rvth"
    then obtain v where "final_rvth v' = Some v" by auto
    hence ft: "final_thrd v = Some v'" using clauseG[OF kpos] by simp
    have "v' \<in> V" using final_thrd_target_in_V[OF kpos ft] by auto
    moreover have "v' \<noteq> r" using r_notin_ran_final_thrd[OF kpos] ft by auto
    ultimately show "v' \<in> V - {r}" by simp
  qed
next
  show "V - {r} \<subseteq> dom final_rvth"
  proof
    fix v' assume "v' \<in> V - {r}"
    hence "v' \<in> V" and "v' \<noteq> r" by auto
    then obtain v where "final_thrd v = Some v'" using ran_final_thrd_ge[OF kpos] by auto
    hence "final_rvth v' = Some v" using clauseG[OF kpos] by simp
    thus "v' \<in> dom final_rvth" by auto
  qed
qed

text \<open>Clause C for the reverse thread: @{term "parent_spec final_rvth"} --- @{const final_rvth} is the
      converse of the @{const parent_spec} thread @{const final_thrd}, so it chains the DISTINCT list
      @{term "rev newlist"} (via @{thm parent_spec_of_distinct_chain}).\<close>
lemma parent_spec_final_rvth:
  assumes kpos: "0 < k" shows "parent_spec final_rvth"
proof (rule parent_spec_of_distinct_chain[of "rev newlist"])
  show "distinct (rev newlist)" using distinct_newlist by simp
next
  fix x y assume "final_rvth x = Some y"
  hence "final_thrd y = Some x" using clauseG[OF kpos] by simp
  then obtain i where iL: "Suc i < length newlist" and iy: "newlist ! i = y" and ix: "newlist ! Suc i = x"
    using final_thrd_reverse_chain[OF kpos] by auto
  let ?L = "length newlist"
  let ?m = "?L - Suc (Suc i)"
  have mL: "?m < length (rev newlist)" using iL by simp
  have SmL: "Suc ?m < length (rev newlist)" using iL by simp
  have "rev newlist ! ?m = newlist ! (?L - Suc ?m)" using mL by (simp add: rev_nth)
  also have "?L - Suc ?m = Suc i" using iL by simp
  finally have e1: "rev newlist ! ?m = x" using ix by simp
  have "rev newlist ! Suc ?m = newlist ! (?L - Suc (Suc ?m))" using SmL by (simp add: rev_nth)
  also have "?L - Suc (Suc ?m) = i" using iL by simp
  finally have e2: "rev newlist ! Suc ?m = y" using iy by simp
  show "\<exists>m. Suc m < length (rev newlist) \<and> rev newlist ! m = x \<and> rev newlist ! Suc m = y"
    using SmL e1 e2 by auto
qed

text \<open>Clause C of @{const arb_invar} for @{const update_tree}: the new reverse thread is a valid
      parent map.  Twin of @{thm clauseB}: @{thm update_tree_rvth} rewrites
      @{term "rvth (update_tree S0 i j p jn)"} to @{const final_rvth}, then @{thm parent_spec_final_rvth}.\<close>
lemma clauseC:
  assumes kpos: "0 < k"
  shows "parent_spec (rvth (update_tree S0 i j p jn))"
  using update_tree_rvth[OF kpos] parent_spec_final_rvth[OF kpos] by simp

text \<open>Clause F of @{const arb_invar} for @{const update_tree}: the reverse thread is defined exactly on
      @{term "V - {r}"}.  @{thm update_tree_rvth} rewrites to @{const final_rvth}, then
      @{thm dom_final_rvth}.\<close>
lemma clauseF:
  assumes kpos: "0 < k"
  shows "dom (rvth (update_tree S0 i j p jn)) = V - {r}"
  using update_tree_rvth[OF kpos] dom_final_rvth[OF kpos] by simp

end

context stem_setup begin

subsection \<open>Degenerate branch (\<open>i = p\<close>, \<open>k = 0\<close>): the simple subtree move ({\isasymsection}15.6)\<close>

text \<open>When the entering node coincides with the detached-subtree root (\<open>i = p\<close>), @{const update_tree}
      takes its @{text "Sa/Sb/Sc/Sd"} simple-move branch: no stem reversal, the whole subtree of
      @{term p} moves rigidly under @{term j}.  These lemmas are stated for the call
      @{term "update_tree S0 p j p jn"} (the \<open>i\<close>-slot instantiated to @{term p}), so the definition's
      @{text "if i = p"} is always true, independently of the locale stem @{term s}/@{term k}.  They are
      discharged into the top lemma by interpreting @{locale stem_setup} with the trivial stem
      @{term "k = 0"}.  ({\isasymsection}0.5 Tier-3: this branch reuses only the @{text kpos}-free machinery.)\<close>

text \<open>IP-0: field closed forms of the move.  The degenerate tree is @{term "(prnt S0)(p \<mapsto> j)"}, a
      single-edge swap of @{term p}'s parent to @{term j}, legal since @{term "p \<notin> set (follow (prnt S0) j)"}
      (= @{thm jnotp}).  @{text move_S1} names the moved state; the four decoration loops preserve
      @{const prnt}/@{const thrd}/@{const rvth}, so those pass through to @{const update_tree} unchanged.\<close>

lemma parent_spec_newtree_ip: "parent_spec ((prnt S0)(p \<mapsto> j))"
proof -
  have rinv: "rooted_arborescense_invar r V (prnt S0)" using arb unfolding arb_invar_def by simp
  have pdom: "p \<in> dom (prnt S0)" using rinv pV pne_r unfolding rooted_arborescense_invar_def by auto
  then obtain pu where pu: "prnt S0 p = Some pu" by auto
  have pnfj: "p \<notin> set (follow (prnt S0) j)" using jnotp unfolding children_def by simp
  have "rooted_arborescense_invar r V ((prnt S0)(p \<mapsto> j))"
    using rooted_arborescense_swap_parents(1)[OF rinv pu[symmetric] pnfj jV] by simp
  thus ?thesis using rooted_arborescense_invar_parent_spec by auto
qed

definition move_S1 :: "'a ndtree" where
  "move_S1 = (let Sa = S0\<lparr>prnt := (prnt S0)(p \<mapsto> j)\<rparr> in (if thrd Sa j = Some p then Sa else (let aft1 = thrd Sa (lsuc S0 p); Sb = (case aft1 of None \<Rightarrow> Sa\<lparr>thrd := (thrd Sa)(the (rvth S0 p) := None)\<rparr> | Some a \<Rightarrow> Sa\<lparr>thrd := (thrd Sa)(the (rvth S0 p) \<mapsto> a), rvth := (rvth Sa)(a \<mapsto> the (rvth S0 p))\<rparr>); aft2 = thrd Sb j; Sc = Sb\<lparr>thrd := (thrd Sb)(j \<mapsto> p), rvth := (rvth Sb)(p \<mapsto> j)\<rparr> in (case aft2 of None \<Rightarrow> Sc\<lparr>thrd := (thrd Sc)(lsuc S0 p := None)\<rparr> | Some a \<Rightarrow> Sc\<lparr>thrd := (thrd Sc)(lsuc S0 p \<mapsto> a), rvth := (rvth Sc)(a \<mapsto> lsuc S0 p)\<rparr>))))"

lemma move_prnt_S1: "prnt move_S1 = (prnt S0)(p \<mapsto> j)" by (auto simp add: move_S1_def Let_def split: option.split)
lemma move_lsuc_S1: "lsuc move_S1 = lsuc S0" by (auto simp add: move_S1_def Let_def split: option.split)
lemma move_snum_S1: "snum move_S1 = snum S0" by (auto simp add: move_S1_def Let_def split: option.split)

lemma move_UT_fields:
  "prnt (update_tree S0 p j p jn) = (prnt S0)(p \<mapsto> j) \<and> thrd (update_tree S0 p j p jn) = thrd move_S1 \<and> rvth (update_tree S0 p j p jn) = rvth move_S1"
proof -
  define S2 where "S2 = last_vin_loop move_S1 j j (lsuc move_S1 p)"
  define S3 where "S3 = (if jn \<noteq> the (rvth S0 p) \<and> j \<noteq> the (rvth S0 p) then last_vout_loop S2 (the (prnt S0 p)) (if lsuc move_S1 jn = j then Some jn else None) (lsuc S0 p) (the (rvth S0 p)) else if lsuc move_S1 p \<noteq> lsuc S0 p then last_vout_loop S2 (the (prnt S0 p)) (if lsuc move_S1 jn = j then Some jn else None) (lsuc S0 p) (lsuc move_S1 p) else S2)"
  define S4 where "S4 = succ_vin_loop S3 j jn (snum S0 p)"
  define S5 where "S5 = succ_vout_loop S4 (the (prnt S0 p)) jn (snum S0 p)"
  have peq: "(p = p) = True" by simp
  have psMove: "parent_spec (prnt move_S1)" using parent_spec_newtree_ip move_prnt_S1 by simp
  define Sa where "Sa = fused_vin_loop move_S1 j j jn (lsuc move_S1 p) (snum S0 p) True True"
  define Sb where "Sb = (if jn \<noteq> the (rvth S0 p) \<and> j \<noteq> the (rvth S0 p) then fused_vout_loop Sa (the (prnt S0 p)) (if lsuc move_S1 jn = j then Some jn else None) (lsuc S0 p) (the (rvth S0 p)) jn (snum S0 p) True True else if lsuc move_S1 p \<noteq> lsuc S0 p then fused_vout_loop Sa (the (prnt S0 p)) (if lsuc move_S1 jn = j then Some jn else None) (lsuc S0 p) (lsuc move_S1 p) jn (snum S0 p) True True else fused_vout_loop Sa (the (prnt S0 p)) (if lsuc move_S1 jn = j then Some jn else None) (lsuc S0 p) (lsuc S0 p) jn (snum S0 p) False True)"
  have UTb: "update_tree S0 p j p jn = Sb" by (simp only: update_tree_def Let_def peq if_True Sb_def Sa_def move_S1_def)
  have SbS5: "Sb = S5" using update_tree_tail_eq[OF psMove] by (simp only: Sb_def Sa_def S5_def S4_def S3_def S2_def)
  have UT: "update_tree S0 p j p jn = S5" using UTb SbS5 by simp
  have psP: "parent_spec ((prnt S0)(p \<mapsto> j))" using parent_spec_newtree_ip by auto
  have pmove: "prnt move_S1 = (prnt S0)(p \<mapsto> j)" using move_prnt_S1 by auto
  have A2: "prnt S2 = (prnt S0)(p \<mapsto> j) \<and> thrd S2 = thrd move_S1 \<and> rvth S2 = rvth move_S1" using last_vin_loop_fields[OF psP, THEN mp, OF pmove] by (simp add: S2_def)
  have A3: "prnt S3 = (prnt S0)(p \<mapsto> j) \<and> thrd S3 = thrd move_S1 \<and> rvth S3 = rvth move_S1" using last_vout_loop_fields[OF psP, THEN mp, OF conjunct1[OF A2]] A2 by (simp add: S3_def)
  have A4: "prnt S4 = (prnt S0)(p \<mapsto> j) \<and> thrd S4 = thrd move_S1 \<and> rvth S4 = rvth move_S1" using succ_vin_loop_fields[OF psP, THEN mp, OF conjunct1[OF A3]] A3 by (simp add: S4_def)
  have A5: "prnt S5 = (prnt S0)(p \<mapsto> j) \<and> thrd S5 = thrd move_S1 \<and> rvth S5 = rvth move_S1" using succ_vout_loop_fields[OF psP, THEN mp, OF conjunct1[OF A4]] A4 by (simp add: S5_def)
  show ?thesis using UT A5 by simp
qed

lemma move_prnt: "prnt (update_tree S0 p j p jn) = (prnt S0)(p \<mapsto> j)" using move_UT_fields by simp
lemma move_thrd: "thrd (update_tree S0 p j p jn) = thrd move_S1" using move_UT_fields by simp
lemma move_rvth: "rvth (update_tree S0 p j p jn) = rvth move_S1" using move_UT_fields by simp

text \<open>IP-1: the moved thread list.  @{term movlist} is @{const newlist} with @{term "block S0 p"} in
      place of @{const newblock} (which have equal sets, @{thm newblock_set}); it splices the whole,
      unchanged block after @{term j}.  Its @{const set}/@{const distinct}/@{const hd} properties reuse
      the reinsertion-agnostic @{const holed} lemmas verbatim.\<close>

definition movlist :: "'a list" where "movlist = takeWhile (\<lambda>x. x \<noteq> j) holed @ j # block S0 p @ tl (dropWhile (\<lambda>x. x \<noteq> j) holed)"

lemma set_movlist: "set movlist = V"
proof -
  have nl: "set movlist = (set (takeWhile (\<lambda>x. x \<noteq> j) holed) \<union> {j} \<union> set (tl (dropWhile (\<lambda>x. x \<noteq> j) holed))) \<union> set (block S0 p)" unfolding movlist_def by auto
  show ?thesis using nl set_holed_split holed_set block_p_subset_V by auto
qed

lemma movlist_ne: "movlist \<noteq> []" unfolding movlist_def by simp

lemma distinct_movlist: "distinct movlist"
proof -
  have dh: "distinct (takeWhile (\<lambda>x. x \<noteq> j) holed @ j # tl (dropWhile (\<lambda>x. x \<noteq> j) holed))" using holed_distinct holed_split by simp
  have disj: "set (block S0 p) \<inter> set holed = {}" using holed_set block_p_subset_V by auto
  have subTW: "set (takeWhile (\<lambda>x. x \<noteq> j) holed) \<subseteq> set holed" using set_holed_split by auto
  have subTL: "set (tl (dropWhile (\<lambda>x. x \<noteq> j) holed)) \<subseteq> set holed" using set_holed_split by auto
  have jh: "j \<in> set holed" by (rule j_in_holed)
  have nbTW: "set (block S0 p) \<inter> set (takeWhile (\<lambda>x. x \<noteq> j) holed) = {}" using disj subTW by auto
  have nbTL: "set (block S0 p) \<inter> set (tl (dropWhile (\<lambda>x. x \<noteq> j) holed)) = {}" using disj subTL by auto
  have jnb: "j \<notin> set (block S0 p)" using disj jh by auto
  show ?thesis unfolding movlist_def using dh block_distinct_V[OF pV] nbTW nbTL jnb by (auto simp: distinct_append)
qed

lemma hd_movlist: "hd movlist = r"
proof -
  have jh: "j \<in> set holed" by (rule j_in_holed)
  obtain z zs where hz: "holed = z # zs" using jh by (cases holed) auto
  have zr: "z = r" using hd_holed hz by simp
  show ?thesis
  proof (cases "z = j")
    case True
    hence "takeWhile (\<lambda>x. x \<noteq> j) holed = []" using hz by simp
    thus ?thesis unfolding movlist_def using zr True by simp
  next
    case False
    hence "takeWhile (\<lambda>x. x \<noteq> j) holed = z # takeWhile (\<lambda>x. x \<noteq> j) zs" using hz by simp
    thus ?thesis unfolding movlist_def using zr by simp
  qed
qed

text \<open>IP-2 foundations: the @{const thrd} of the moved state.  The code guard @{term "thrd Sa j = Some p"}
      is @{term "thrd S0 j = Some p"} (@{term Sa} only edits @{const prnt}), which by clause G is
      @{term "rvth S0 p = Some j"}, i.e. @{term "the (rvth S0 p) = j"} (the @{text "old_rev = j"} shortcut).
      Splice case (@{text "old_rev \<noteq> j"}): three edits.  Shortcut case: the thread is unchanged.\<close>

lemma move_thrd_splice:
  assumes g: "thrd S0 j \<noteq> Some p"
  shows "thrd move_S1 = (thrd S0)(the (rvth S0 p) := thrd S0 (lsuc S0 p), j \<mapsto> p, lsuc S0 p := thrd S0 j)"
proof -
  have domF: "dom (rvth S0) = V - {r}" using arb unfolding arb_invar_def by simp
  have pdr: "p \<in> dom (rvth S0)" using domF pV pne_r by simp
  then obtain w where w: "rvth S0 p = Some w" by auto
  have Gs: "(thrd S0 j = Some p) = (rvth S0 p = Some j)" using arb unfolding arb_invar_def by auto
  have orne: "the (rvth S0 p) \<noteq> j"
  proof
    assume "the (rvth S0 p) = j"
    hence "rvth S0 p = Some j" using w by simp
    hence "thrd S0 j = Some p" using Gs by simp
    thus False using g by simp
  qed
  have tSa: "thrd (S0\<lparr>prnt := (prnt S0)(p \<mapsto> j)\<rparr>) = thrd S0" by simp
  show ?thesis unfolding move_S1_def Let_def using g orne tSa by (simp split: option.split)
qed

lemma move_thrd_shortcut:
  assumes g: "thrd S0 j = Some p"
  shows "thrd move_S1 = thrd S0"
proof -
  have tSa: "thrd (S0\<lparr>prnt := (prnt S0)(p \<mapsto> j)\<rparr>) = thrd S0" by simp
  show ?thesis unfolding move_S1_def Let_def using g tSa by simp
qed

text \<open>@{term "block S0 p"} is a contiguous middle segment of the old thread
      (@{thm oldlist_split_eq}), so its internal edges are old-thread edges (like @{thm beta_link}).\<close>
lemma block_p_link:
  assumes "Suc t < length (block S0 p)"
  shows "thrd S0 (block S0 p ! t) = Some (block S0 p ! Suc t)"
proof -
  have split: "follow (thrd S0) r = alpha @ block S0 p @ beta" using oldlist_split_eq by simp
  have e1: "follow (thrd S0) r ! (length alpha + t) = block S0 p ! t" using split assms by (simp add: nth_append)
  have e2: "follow (thrd S0) r ! (length alpha + Suc t) = block S0 p ! Suc t" using split assms by (simp add: nth_append)
  have lt: "Suc (length alpha + t) < length (follow (thrd S0) r)" using assms split by simp
  have "thrd S0 (follow (thrd S0) r ! (length alpha + t)) = Some (follow (thrd S0) r ! Suc (length alpha + t))" by (rule oldlist_link[OF lt])
  thus ?thesis using e1 e2 by simp
qed

text \<open>IP-2 (cont.): every consecutive @{const holed} pair whose source is not j is realised by
      @{const move_S1}'s thread: surviving old edges plus the old-rev junction (which the splice sends
      to the block's old successor).  This is the @{const move_S1} analogue of @{thm holed_old_adj}.\<close>

lemma old_rev_ne_j:
  assumes g: "thrd S0 j \<noteq> Some p"
  shows "the (rvth S0 p) \<noteq> j"
proof -
  have domF: "dom (rvth S0) = V - {r}" using arb unfolding arb_invar_def by simp
  have pdr: "p \<in> dom (rvth S0)" using domF pV pne_r by simp
  then obtain w where w: "rvth S0 p = Some w" by auto
  have Gs: "(thrd S0 j = Some p) = (rvth S0 p = Some j)" using arb unfolding arb_invar_def by auto
  show ?thesis
  proof
    assume "the (rvth S0 p) = j"
    hence "rvth S0 p = Some j" using w by simp
    hence "thrd S0 j = Some p" using Gs by simp
    thus False using g by simp
  qed
qed

lemma blockp_succ_beta:
  assumes bne: "beta \<noteq> []"
  shows "thrd S0 (lsuc S0 p) = Some (hd beta)"
proof -
  obtain A B where AB: "follow (thrd S0) r = A @ block S0 p @ B"
      and pA: "A \<noteq> [] \<Longrightarrow> the (rvth S0 p) = last A"
      and pB: "B \<noteq> [] \<Longrightarrow> thrd S0 (lsuc S0 p) = Some (hd B)"
    using block_p_split by auto
  have pst: "parent_spec (thrd S0)" using arb unfolding arb_invar_def by simp
  have dist: "distinct (follow (thrd S0) r)" by (rule follow_distinct_ps[OF pst])
  have hdp: "hd (block S0 p) = p" by (rule block_props(5)[OF arb pV])
  have bne0: "block S0 p \<noteq> []" by (rule block_props(2)[OF arb pV])
  obtain rest where bp: "block S0 p = p # rest" using bne0 hdp by (metis hd_Cons_tl)
  have distA: "distinct (A @ p # rest @ B)" using dist AB bp by simp
  have allA: "\<forall>x\<in>set A. x \<noteq> p" using distA by auto
  have aA: "alpha = A" unfolding alpha_def using AB bp allA by (simp add: takeWhile_append2)
  have "alpha @ block S0 p @ beta = A @ block S0 p @ B" using oldlist_split_eq AB by simp
  hence "beta = B" using aA by simp
  thus ?thesis using pB bne by simp
qed

lemma holed_adj_move:
  assumes g: "thrd S0 j \<noteq> Some p" and lt: "Suc t < length holed" and nj: "holed ! t \<noteq> j"
  shows "thrd move_S1 (holed ! t) = Some (holed ! Suc t)"
proof -
  have tm: "thrd move_S1 = (thrd S0)(the (rvth S0 p) := thrd S0 (lsuc S0 p), j \<mapsto> p, lsuc S0 p := thrd S0 j)" using move_thrd_splice[OF g] by auto
  have orne: "the (rvth S0 p) \<noteq> j" using old_rev_ne_j[OF g] by auto
  have mem: "holed ! t \<in> set holed" using lt by (metis Suc_lessD nth_mem)
  have oll: "lsuc S0 p \<in> set (block S0 p)" by (simp add: block_def)
  have nbl: "holed ! t \<noteq> lsuc S0 p" using mem holed_set oll
    by fastforce
  show ?thesis
  proof (cases "holed ! t = the (rvth S0 p)")
    case True
    have orv_nbl: "the (rvth S0 p) \<noteq> lsuc S0 p" using True nbl by simp
    have oa: "the (rvth S0 p) = last alpha" using old_rev_last_alpha by auto
    have hab: "holed = alpha @ beta" unfolding holed_def by simp
    have ane: "alpha \<noteq> []" by (rule alpha_ne)
    have hd_dist: "distinct holed" by (rule holed_distinct)
    have pos: "holed ! (length alpha - 1) = the (rvth S0 p)" using oa hab ane by (simp add: nth_append last_conv_nth)
    have la_lt: "length alpha - 1 < length holed" using ane hab by (cases alpha) auto
    have teq: "t = length alpha - 1" using True pos hd_dist lt la_lt by (metis Suc_lessD nth_eq_iff_index_eq)
    have bne: "beta \<noteq> []" using lt teq hab ane by (cases beta) auto
    have suceq: "holed ! Suc t = hd beta" using teq hab ane bne by (simp add: nth_append hd_conv_nth)
    show ?thesis using tm True orne orv_nbl blockp_succ_beta[OF bne] suceq by simp
  next
    case False
    have "thrd S0 (holed ! t) = Some (holed ! Suc t)" using holed_old_adj[OF lt False] by auto
    moreover have "thrd move_S1 (holed ! t) = thrd S0 (holed ! t)" using tm nj nbl False by simp
    ultimately show ?thesis by simp
  qed
qed

text \<open>@{const movlist} index helpers (analogues of @{text nl_len}/@{text nl_j}/@{text nl_nb}/@{text nl_tl}
      with @{term "block S0 p"} for @{const newblock}); the @{const holed} helpers are shared.\<close>

lemma ml_len: "length movlist = length (takeWhile (\<lambda>x. x \<noteq> j) holed) + 1 + length (block S0 p) + length (tl (dropWhile (\<lambda>x. x \<noteq> j) holed))" by (simp add: movlist_def)

lemma ml_hd_region:
  assumes "a < length (takeWhile (\<lambda>x. x \<noteq> j) holed)"
  shows "movlist ! a = holed ! a"
proof -
  have "movlist ! a = takeWhile (\<lambda>x. x \<noteq> j) holed ! a" using assms by (simp add: movlist_def nth_append)
  moreover have "holed ! a = takeWhile (\<lambda>x. x \<noteq> j) holed ! a" using assms by (subst holed_split) (simp add: nth_append)
  ultimately show ?thesis by simp
qed

lemma ml_j: "movlist ! (length (takeWhile (\<lambda>x. x \<noteq> j) holed)) = j" by (simp add: movlist_def nth_append)

lemma ml_le_n1:
  assumes "a \<le> length (takeWhile (\<lambda>x. x \<noteq> j) holed)"
  shows "movlist ! a = holed ! a"
proof (cases "a < length (takeWhile (\<lambda>x. x \<noteq> j) holed)")
  case True thus ?thesis by (rule ml_hd_region)
next
  case False
  hence "a = length (takeWhile (\<lambda>x. x \<noteq> j) holed)" using assms by simp
  thus ?thesis using ml_j holed_j_pos by simp
qed

lemma ml_nb:
  assumes "d < length (block S0 p)"
  shows "movlist ! (length (takeWhile (\<lambda>x. x \<noteq> j) holed) + 1 + d) = block S0 p ! d"
  using assms by (simp add: movlist_def nth_append)

lemma ml_tl:
  assumes "c < length (tl (dropWhile (\<lambda>x. x \<noteq> j) holed))"
  shows "movlist ! (length (takeWhile (\<lambda>x. x \<noteq> j) holed) + 1 + length (block S0 p) + c) = holed ! (length (takeWhile (\<lambda>x. x \<noteq> j) holed) + 1 + c)"
proof -
  have "movlist ! (length (takeWhile (\<lambda>x. x \<noteq> j) holed) + 1 + length (block S0 p) + c) = tl (dropWhile (\<lambda>x. x \<noteq> j) holed) ! c"
    using assms by (simp add: movlist_def nth_append)
  moreover have "holed ! (length (takeWhile (\<lambda>x. x \<noteq> j) holed) + 1 + c) = tl (dropWhile (\<lambda>x. x \<noteq> j) holed) ! c"
    using assms by (subst holed_split) (simp add: nth_append)
  ultimately show ?thesis by simp
qed

text \<open>The @{const move_S1} thread realises @{const movlist} (splice case): 5 regions --- @{const holed}
      prefix/suffix via @{thm holed_adj_move}, the @{text "j \<mapsto> p"} seam, the unchanged @{term "block S0 p"}
      interior via @{thm block_p_link}, and the old-last-to-hd-TL tail seam.\<close>

lemma movlist_link:
  assumes g: "thrd S0 j \<noteq> Some p" and lt: "Suc t < length movlist"
  shows "thrd move_S1 (movlist ! t) = Some (movlist ! Suc t)"
proof -
  let ?n1 = "length (takeWhile (\<lambda>x. x \<noteq> j) holed)"
  let ?nb = "length (block S0 p)"
  let ?TL = "tl (dropWhile (\<lambda>x. x \<noteq> j) holed)"
  have hlen: "length holed = ?n1 + 1 + length ?TL" by (rule holed_len)
  have mllen: "length movlist = ?n1 + 1 + ?nb + length ?TL" by (rule ml_len)
  have bne: "block S0 p \<noteq> []" by (rule block_props(2)[OF arb pV])
  have nbpos: "0 < ?nb" using bne by auto
  have tm: "thrd move_S1 = (thrd S0)(the (rvth S0 p) := thrd S0 (lsuc S0 p), j \<mapsto> p, lsuc S0 p := thrd S0 j)" using move_thrd_splice[OF g] by auto
  have orne: "the (rvth S0 p) \<noteq> j" using old_rev_ne_j[OF g] by auto
  have jnbl: "j \<notin> set (block S0 p)" by (rule j_notin_block_p)
  have oll: "lsuc S0 p \<in> set (block S0 p)" by (simp add: block_def)
  have jne_ol: "j \<noteq> lsuc S0 p" using jnbl oll by auto
  consider (TW) "t < ?n1" | (J) "t = ?n1" | (NB) "?n1 < t" "t < ?n1 + ?nb" | (SEAM) "t = ?n1 + ?nb" | (TL) "?n1 + ?nb < t" by linarith
  then show ?thesis
  proof cases
    case TW
    have s: "movlist ! t = holed ! t" using ml_le_n1 TW by simp
    have tgt: "movlist ! Suc t = holed ! Suc t" using ml_le_n1 TW by simp
    have sjt: "Suc t < length holed" using TW hlen by simp
    have nej: "holed ! t \<noteq> j" using holed_ne_j_off TW hlen by simp
    show ?thesis using holed_adj_move[OF g sjt nej] s tgt by simp
  next
    case J
    have s: "movlist ! t = j" using ml_j J by simp
    have tgt: "movlist ! Suc t = p" using J ml_nb[of 0] nbpos bne block_props(5)[OF arb pV] by (simp add: hd_conv_nth)
    have tj: "thrd move_S1 j = Some p" using tm jne_ol by simp
    show ?thesis using tj s tgt by simp
  next
    case NB
    obtain d where td: "t = ?n1 + 1 + d" using NB(1) less_imp_Suc_add by fastforce
    have dnb: "Suc d < ?nb" using NB(2) td by simp
    have s: "movlist ! t = block S0 p ! d" using ml_nb[of d] dnb td by simp
    have tgt: "movlist ! Suc t = block S0 p ! Suc d" using td ml_nb[of "Suc d"] dnb by simp
    have bd: "thrd S0 (block S0 p ! d) = Some (block S0 p ! Suc d)" using block_p_link[of d] dnb by simp
    have dmem: "block S0 p ! d \<in> set (block S0 p)" using dnb by (metis Suc_lessD nth_mem)
    have orv_h: "the (rvth S0 p) \<in> set holed" using old_rev_last_alpha alpha_ne by (simp add: holed_def)
    have orv_nb: "the (rvth S0 p) \<notin> set (block S0 p)" using orv_h holed_set by auto
    have d_ne_orv: "block S0 p ! d \<noteq> the (rvth S0 p)" using orv_nb dmem by auto
    have d_ne_j: "block S0 p ! d \<noteq> j" using jnbl dmem by auto
    have last_bp: "lsuc S0 p = block S0 p ! (?nb - 1)" using bne block_props(3)[OF arb pV] by (simp add: last_conv_nth)
    have d_ne_ol: "block S0 p ! d \<noteq> lsuc S0 p"
    proof -
      have "d \<noteq> ?nb - 1" using dnb by simp
      moreover have "d < ?nb" "?nb - 1 < ?nb" using dnb nbpos by auto
      ultimately show ?thesis using block_distinct_V[OF pV] last_bp by (metis nth_eq_iff_index_eq)
    qed
    have "thrd move_S1 (block S0 p ! d) = thrd S0 (block S0 p ! d)" using tm d_ne_orv d_ne_j d_ne_ol by simp
    thus ?thesis using bd s tgt by simp
  next
    case SEAM
    have TLpos: "0 < length ?TL" using lt mllen SEAM by linarith
    have TLne: "?TL \<noteq> []" using TLpos by (cases ?TL) auto
    obtain nb' where nbeq: "?nb = Suc nb'" using bne by (cases "block S0 p") auto
    have td: "t = ?n1 + 1 + nb'" using SEAM nbeq by simp
    have s: "movlist ! t = lsuc S0 p"
      using ml_nb[of nb'] nbeq td bne block_props(3)[OF arb pV] by (simp add: last_conv_nth)
    have E2: "movlist ! (?n1 + 1 + ?nb + 0) = holed ! (?n1 + 1 + 0)" by (rule ml_tl[OF TLpos])
    have E3: "holed ! (?n1 + 1 + 0) = ?TL ! 0" by (rule holed_TL_nth[OF TLpos])
    have E4: "?TL ! 0 = hd ?TL" using TLne by (simp add: hd_conv_nth)
    have tgt: "movlist ! Suc t = hd ?TL" using SEAM E2 E3 E4 by simp
    have tms: "thrd move_S1 (lsuc S0 p) = thrd S0 j" using tm by simp
    have jpos: "holed ! ?n1 = j" by (rule holed_j_pos)
    have jne_orv: "holed ! ?n1 \<noteq> the (rvth S0 p)" using jpos orne by simp
    have sn1: "Suc ?n1 < length holed" using hlen TLpos by simp
    have "thrd S0 (holed ! ?n1) = Some (holed ! Suc ?n1)" using holed_old_adj[OF sn1 jne_orv] by auto
    hence "thrd S0 j = Some (holed ! (?n1 + 1))" using jpos by simp
    also have "holed ! (?n1 + 1) = ?TL ! 0" using holed_TL_nth[OF TLpos] by simp
    also have "\<dots> = hd ?TL" using TLne by (simp add: hd_conv_nth)
    finally have "thrd S0 j = Some (hd ?TL)" .
    thus ?thesis using tms s tgt by simp
  next
    case TL
    define c where "c = t - (?n1 + 1 + ?nb)"
    have tc: "t = ?n1 + 1 + ?nb + c" using TL c_def by simp
    have clt: "c < length ?TL" using lt mllen tc by linarith
    have c1lt: "Suc c < length ?TL" using lt mllen tc by linarith
    have s: "movlist ! t = holed ! (?n1 + 1 + c)" using ml_tl[OF clt] tc by simp
    have E2: "movlist ! (?n1 + 1 + ?nb + Suc c) = holed ! (?n1 + 1 + Suc c)" by (rule ml_tl[OF c1lt])
    have tgt: "movlist ! Suc t = holed ! Suc (?n1 + 1 + c)" using tc E2 by simp
    have idxlt: "?n1 + 1 + c < length holed" using hlen clt by simp
    have sjt: "Suc (?n1 + 1 + c) < length holed" using hlen c1lt by simp
    have off: "?n1 + 1 + c \<noteq> ?n1" by simp
    have nej: "holed ! (?n1 + 1 + c) \<noteq> j" by (rule holed_ne_j_off[OF idxlt off])
    show ?thesis using holed_adj_move[OF g sjt nej] s tgt by simp
  qed
qed

text \<open>IP-2 assembly: the moved thread is @{const parent_spec} and realises @{const movlist} starting at
      @{term r} (clauses B and D).  Two cases: the shortcut (@{term "thrd S0 j = Some p"}), where the thread
      is unchanged and @{const movlist} equals the old thread; and the splice, via the generic engine
      @{thm follow_eq_of_chain} on @{thm movlist_link} and movlist\_last\_None (below).\<close>

lemma last_movlist_nil:
  assumes "tl (dropWhile (\<lambda>x. x \<noteq> j) holed) = []"
  shows "last movlist = lsuc S0 p"
proof -
  have "movlist = takeWhile (\<lambda>x. x \<noteq> j) holed @ j # block S0 p" using assms by (simp add: movlist_def)
  hence "last movlist = last (j # block S0 p)" by simp
  also have "\<dots> = last (block S0 p)" using block_props(2)[OF arb pV] by simp
  finally show ?thesis using block_props(3)[OF arb pV] by simp
qed

lemma last_movlist_TL:
  assumes TLne: "tl (dropWhile (\<lambda>x. x \<noteq> j) holed) \<noteq> []"
  shows "last movlist = last holed"
proof -
  have "last movlist = last (tl (dropWhile (\<lambda>x. x \<noteq> j) holed))" using TLne by (simp add: movlist_def)
  moreover have "last holed = last (tl (dropWhile (\<lambda>x. x \<noteq> j) holed))" using TLne by (subst holed_split) simp
  ultimately show ?thesis by simp
qed

lemma movlist_last_None:
  assumes g: "thrd S0 j \<noteq> Some p"
  shows "thrd move_S1 (last movlist) = None"
proof -
  have tm: "thrd move_S1 = (thrd S0)(the (rvth S0 p) := thrd S0 (lsuc S0 p), j \<mapsto> p, lsuc S0 p := thrd S0 j)" using move_thrd_splice[OF g] by auto
  have orne: "the (rvth S0 p) \<noteq> j" using old_rev_ne_j[OF g] by auto
  have jnbl: "j \<notin> set (block S0 p)" by (rule j_notin_block_p)
  have oll: "lsuc S0 p \<in> set (block S0 p)" by (simp add: block_def)
  show ?thesis
  proof (cases "tl (dropWhile (\<lambda>x. x \<noteq> j) holed) = []")
    case True
    have lnl: "last movlist = lsuc S0 p" by (rule last_movlist_nil[OF True])
    have jlast: "last holed = j" by (rule last_holed_nil[OF True])
    have bne: "beta \<noteq> []"
    proof
      assume b0: "beta = []"
      have "last holed = the (rvth S0 p)" using last_holed_old_rev[OF b0] by auto
      thus False using jlast orne by simp
    qed
    have lbj: "last beta = j" using last_holed_beta[OF bne] jlast by simp
    have "thrd move_S1 (lsuc S0 p) = thrd S0 j" using tm by simp
    also have "\<dots> = thrd S0 (last beta)" using lbj by simp
    also have "\<dots> = None" using thrd_last_beta_None[OF bne] by simp
    finally show ?thesis using lnl by simp
  next
    case False
    have lnl: "last movlist = last holed" by (rule last_movlist_TL[OF False])
    have znej: "last holed \<noteq> j" by (rule last_holed_ne_j[OF False])
    show ?thesis
    proof (cases "beta = []")
      case True
      have zor: "last holed = the (rvth S0 p)" by (rule last_holed_old_rev[OF True])
      have orv_h: "the (rvth S0 p) \<in> set holed" using old_rev_last_alpha alpha_ne by (simp add: holed_def)
      have orv_nb: "the (rvth S0 p) \<notin> set (block S0 p)" using orv_h holed_set by auto
      have orv_ne_ol: "the (rvth S0 p) \<noteq> lsuc S0 p" using orv_nb oll by auto
      have "thrd move_S1 (last holed) = thrd move_S1 (the (rvth S0 p))" using zor by simp
      also have "\<dots> = thrd S0 (lsuc S0 p)" using tm orne orv_ne_ol by simp
      also have "\<dots> = None" using thrd_lsuc_p_None_of_beta_nil[OF True] by simp
      finally show ?thesis using lnl by simp
    next
      case False
      have zb: "last holed = last beta" by (rule last_holed_beta[OF False])
      have lb_mem: "last beta \<in> set beta" using False by (metis last_in_set)
      have lb_h: "last beta \<in> set holed" using lb_mem set_beta_holed by auto
      have lb_nb: "last beta \<notin> set (block S0 p)" using lb_h holed_set by auto
      have lb_ne_ol: "last beta \<noteq> lsuc S0 p" using lb_nb oll by auto
      have lb_ne_j: "last beta \<noteq> j" using zb znej by simp
      have lb_ne_orv: "last beta \<noteq> the (rvth S0 p)"
      proof -
        have "the (rvth S0 p) = last alpha" by (rule old_rev_last_alpha)
        hence "the (rvth S0 p) \<in> set alpha" using alpha_ne by (metis last_in_set)
        thus ?thesis using lb_mem alpha_beta_disjoint by auto
      qed
      have "thrd move_S1 (last holed) = thrd S0 (last holed)" using tm zb lb_ne_orv lb_ne_j lb_ne_ol by simp
      also have "\<dots> = thrd S0 (last beta)" using zb by simp
      also have "\<dots> = None" using thrd_last_beta_None[OF False] by simp
      finally show ?thesis using lnl by simp
    qed
  qed
qed

lemma move_thrd_dom_V:
  assumes xy: "thrd move_S1 x = Some y"
  shows "x \<in> V"
proof (cases "thrd S0 j = Some p")
  case True
  have "thrd move_S1 = thrd S0" using move_thrd_shortcut[OF True] by auto
  hence "thrd S0 x = Some y" using xy by simp
  hence "x \<in> dom (thrd S0)" by auto
  moreover have "dom (thrd S0) = V - {lsuc S0 r}" using arb unfolding arb_invar_def by simp
  ultimately show ?thesis by auto
next
  case False
  have tm: "thrd move_S1 = (thrd S0)(the (rvth S0 p) := thrd S0 (lsuc S0 p), j \<mapsto> p, lsuc S0 p := thrd S0 j)" using move_thrd_splice[OF False] by auto
  show ?thesis
  proof (cases "x = the (rvth S0 p) \<or> x = j \<or> x = lsuc S0 p")
    case True
    have olV: "lsuc S0 p \<in> V" using block_p_subset_V by (simp add: block_def subset_iff)
    have "the (rvth S0 p) \<in> V" by (rule old_rev_in_V)
    thus ?thesis using True olV jV by auto
  next
    case False
    hence "thrd move_S1 x = thrd S0 x" using tm by auto
    hence "thrd S0 x = Some y" using xy by simp
    hence "x \<in> dom (thrd S0)" by auto
    moreover have "dom (thrd S0) = V - {lsuc S0 r}" using arb unfolding arb_invar_def by simp
    ultimately show ?thesis by auto
  qed
qed

lemma movlist_shortcut:
  assumes g: "thrd S0 j = Some p"
  shows "movlist = follow (thrd S0) r"
proof -
  have pst: "parent_spec (thrd S0)" using arb unfolding arb_invar_def by simp
  have domF: "dom (rvth S0) = V - {r}" using arb unfolding arb_invar_def by simp
  have pdr: "p \<in> dom (rvth S0)" using domF pV pne_r by simp
  then obtain w where w: "rvth S0 p = Some w" by auto
  have Gs: "(thrd S0 j = Some p) = (rvth S0 p = Some j)" using arb unfolding arb_invar_def by auto
  have orvj: "the (rvth S0 p) = j" using g Gs w by auto
  have laj: "last alpha = j" using old_rev_last_alpha orvj by simp
  have ane: "alpha \<noteq> []" by (rule alpha_ne)
  have "distinct (follow (thrd S0) r)" by (rule follow_distinct_ps[OF pst])
  hence odist: "distinct (alpha @ block S0 p @ beta)" using oldlist_split_eq by simp
  hence adist: "distinct alpha" by simp
  have abl: "alpha = butlast alpha @ [j]" using ane laj by (metis append_butlast_last_id)
  have "distinct (butlast alpha @ [j])" using adist abl by simp
  hence jni: "j \<notin> set (butlast alpha)" by auto
  have hab: "holed = butlast alpha @ j # beta" using abl by (simp add: holed_def)
  have tw: "takeWhile (\<lambda>x. x \<noteq> j) holed = butlast alpha"
  proof -
    have "takeWhile (\<lambda>x. x \<noteq> j) (butlast alpha @ (j # beta)) = butlast alpha @ takeWhile (\<lambda>x. x \<noteq> j) (j # beta)"
      by (rule takeWhile_append2) (use jni in auto)
    thus ?thesis using hab by simp
  qed
  have dw: "tl (dropWhile (\<lambda>x. x \<noteq> j) holed) = beta"
  proof -
    have "dropWhile (\<lambda>x. x \<noteq> j) (butlast alpha @ (j # beta)) = dropWhile (\<lambda>x. x \<noteq> j) (j # beta)"
      by (rule dropWhile_append2) (use jni in auto)
    thus ?thesis using hab by simp
  qed
  have "movlist = butlast alpha @ j # block S0 p @ beta" unfolding movlist_def using tw dw by simp
  also have "\<dots> = alpha @ block S0 p @ beta" using abl by simp
  also have "\<dots> = follow (thrd S0) r" using oldlist_split_eq by simp
  finally show ?thesis .
qed

lemma move_thrd_reverse_chain:
  assumes xy: "thrd move_S1 x = Some y"
  shows "\<exists>i. Suc i < length movlist \<and> movlist ! i = x \<and> movlist ! Suc i = y"
proof (cases "thrd S0 j = Some p")
  case True
  have mvo: "movlist = follow (thrd S0) r" using movlist_shortcut[OF True] by auto
  have te: "thrd move_S1 = thrd S0" using move_thrd_shortcut[OF True] by auto
  have xy0: "thrd S0 x = Some y" using xy te by simp
  have xV: "x \<in> V" using move_thrd_dom_V[OF xy] by auto
  have "x \<in> set movlist" using xV set_movlist by simp
  then obtain i where ile: "i < length movlist" and xi: "movlist ! i = x" by (metis in_set_conv_nth)
  show ?thesis
  proof (cases "Suc i < length movlist")
    case True
    have lt': "Suc i < length (follow (thrd S0) r)" using True mvo by simp
    have "thrd S0 (follow (thrd S0) r ! i) = Some (follow (thrd S0) r ! Suc i)" by (rule oldlist_link[OF lt'])
    hence "thrd S0 (movlist ! i) = Some (movlist ! Suc i)" using mvo by simp
    hence "y = movlist ! Suc i" using xi xy0 by simp
    thus ?thesis using True xi by auto
  next
    case False
    hence "i = length movlist - 1" using ile by simp
    hence "movlist ! i = last movlist" using movlist_ne ile by (simp add: last_conv_nth)
    hence "thrd S0 x = None" using xi mvo last_follow_thrd0_None by simp
    thus ?thesis using xy0 by simp
  qed
next
  case False
  note gsp = False
  have xV: "x \<in> V" using move_thrd_dom_V[OF xy] by auto
  have "x \<in> set movlist" using xV set_movlist by simp
  then obtain i where ile: "i < length movlist" and xi: "movlist ! i = x" by (metis in_set_conv_nth)
  show ?thesis
  proof (cases "Suc i < length movlist")
    case True
    have "thrd move_S1 (movlist ! i) = Some (movlist ! Suc i)" by (rule movlist_link[OF gsp True])
    hence "y = movlist ! Suc i" using xi xy by simp
    thus ?thesis using True xi by auto
  next
    case False
    hence "i = length movlist - 1" using ile by simp
    hence "movlist ! i = last movlist" using movlist_ne ile by (simp add: last_conv_nth)
    hence "thrd move_S1 x = None" using xi movlist_last_None[OF gsp] by simp
    thus ?thesis using xy by simp
  qed
qed

lemma parent_spec_move_thrd: "parent_spec (thrd move_S1)"
proof (rule parent_spec_of_distinct_chain[OF distinct_movlist])
  fix x y assume "thrd move_S1 x = Some y"
  thus "\<exists>i. Suc i < length movlist \<and> movlist ! i = x \<and> movlist ! Suc i = y" by (rule move_thrd_reverse_chain)
qed

lemma out_edge_ip: "follow (thrd move_S1) r = movlist"
proof (cases "thrd S0 j = Some p")
  case True
  have "thrd move_S1 = thrd S0" using move_thrd_shortcut[OF True] by auto
  thus ?thesis using movlist_shortcut[OF True] by simp
next
  case False
  have ps: "parent_spec (thrd move_S1)" by (rule parent_spec_move_thrd)
  have "follow (thrd move_S1) (hd movlist) = movlist"
    by (rule follow_eq_of_chain[OF ps movlist_ne movlist_link[OF False] movlist_last_None[OF False]])
  thus ?thesis using hd_movlist by simp
qed

lemma clauseB_ip: "parent_spec (thrd (update_tree S0 p j p jn))"
  using move_thrd parent_spec_move_thrd by simp

lemma clauseD_ip: "set (follow (thrd (update_tree S0 p j p jn)) r) = V"
  using move_thrd out_edge_ip set_movlist by simp

text \<open>IP-3: clauses C, F, G.  Clause G (the reverse thread is the inverse of the forward thread) is a
      direct check that the move keeps @{const rvth} symmetric to @{const thrd} at its @{text "\<le> 3"} edits;
      no @{const dirty_pass} is needed.  F (@{term "dom (rvth move_S1) = V - {r}"}) follows via the range of
      @{const thrd}; C (@{const parent_spec}) via the reversed @{const movlist} chain.\<close>

lemma clauseG_move: "(thrd move_S1 v = Some v') = (rvth move_S1 v' = Some v)"
proof (cases "thrd S0 j = Some p")
  case True
  have te: "thrd move_S1 = thrd S0" using move_thrd_shortcut[OF True] by auto
  have re: "rvth move_S1 = rvth S0" using True by (simp add: move_S1_def)
  have gG: "(thrd S0 v = Some v') = (rvth S0 v' = Some v)" using arb unfolding arb_invar_def by auto
  show ?thesis using te re gG by simp
next
  case False
  have gG: "\<And>a b. (thrd S0 a = Some b) = (rvth S0 b = Some a)" using arb unfolding arb_invar_def by auto
  have domE: "dom (thrd S0) = V - {lsuc S0 r}" using arb unfolding arb_invar_def by simp
  have domF: "dom (rvth S0) = V - {r}" using arb unfolding arb_invar_def by simp
  have orne: "the (rvth S0 p) \<noteq> j" using old_rev_ne_j[OF False] by auto
  have orv_h: "the (rvth S0 p) \<in> set holed" using old_rev_last_alpha alpha_ne by (simp add: holed_def)
  have orv_nb: "the (rvth S0 p) \<notin> set (block S0 p)" using orv_h holed_set by auto
  have oll: "lsuc S0 p \<in> set (block S0 p)" by (simp add: block_def)
  have jnbl: "j \<notin> set (block S0 p)" by (rule j_notin_block_p)
  have orv_ne_ol: "the (rvth S0 p) \<noteq> lsuc S0 p" using orv_nb oll by auto
  have j_ne_ol: "j \<noteq> lsuc S0 p" using jnbl oll by auto
  have olV: "lsuc S0 p \<in> V" using block_p_subset_V oll by auto
  have pdomr: "p \<in> dom (rvth S0)" using domF pV pne_r by simp
  then obtain wr where wr: "rvth S0 p = Some wr" by auto
  have orv_thrd: "thrd S0 (the (rvth S0 p)) = Some p" using wr gG by (metis option.sel)
  have lastfact: "\<And>x. x \<in> V \<Longrightarrow> thrd S0 x = None \<Longrightarrow> x = lsuc S0 r" using domE by auto
  have jNone: "thrd S0 j = None \<Longrightarrow> j = lsuc S0 r" using lastfact jV by simp
  have olNone: "thrd S0 (lsuc S0 p) = None \<Longrightarrow> lsuc S0 p = lsuc S0 r" using lastfact olV by simp
  have rtt: "\<And>a b. rvth S0 a = Some b \<Longrightarrow> thrd S0 b = Some a" using gG by simp
  have rvthinj: "\<And>a b c. rvth S0 a = Some c \<Longrightarrow> rvth S0 b = Some c \<Longrightarrow> a = b" using gG by (metis option.inject)
  show ?thesis
    using False orne orv_ne_ol j_ne_ol gG orv_thrd jNone olNone rvthinj wr
    unfolding move_S1_def Let_def
    by (auto split: option.split_asm option.split if_split_asm dest: rtt)
qed

lemma clauseG_ip: "\<forall>v v'. (thrd (update_tree S0 p j p jn) v = Some v') = (rvth (update_tree S0 p j p jn) v' = Some v)"
  using move_thrd move_rvth clauseG_move by simp

lemma movlist_link_uniform:
  assumes tlt: "Suc t < length movlist"
  shows "thrd move_S1 (movlist ! t) = Some (movlist ! Suc t)"
proof -
  have "Suc t < length (follow (thrd move_S1) r)" using tlt out_edge_ip by simp
  hence "thrd move_S1 (follow (thrd move_S1) r ! t) = Some (follow (thrd move_S1) r ! Suc t)"
    by (rule follow_nth_Suc[OF parent_spec_move_thrd])
  thus ?thesis using out_edge_ip by simp
qed

lemma ran_move_thrd: "ran (thrd move_S1) = V - {r}"
proof
  show "ran (thrd move_S1) \<subseteq> V - {r}"
  proof
    fix y assume "y \<in> ran (thrd move_S1)"
    then obtain x where "thrd move_S1 x = Some y" unfolding ran_def by auto
    then obtain t where t: "Suc t < length movlist \<and> movlist ! t = x \<and> movlist ! Suc t = y" using move_thrd_reverse_chain by auto
    have yset: "y \<in> set movlist" using t by (metis nth_mem)
    have yV: "y \<in> V" using yset set_movlist by simp
    have "y \<noteq> r"
    proof
      assume "y = r"
      hence "movlist ! Suc t = movlist ! 0" using t hd_movlist movlist_ne by (metis hd_conv_nth)
      hence "Suc t = 0" using distinct_movlist t by (metis Suc_lessD nth_eq_iff_index_eq length_greater_0_conv movlist_ne)
      thus False by simp
    qed
    thus "y \<in> V - {r}" using yV by simp
  qed
next
  show "V - {r} \<subseteq> ran (thrd move_S1)"
  proof
    fix y assume "y \<in> V - {r}"
    hence yV: "y \<in> V" and yr: "y \<noteq> r" by auto
    have "y \<in> set movlist" using yV set_movlist by simp
    then obtain k where k: "k < length movlist" "movlist ! k = y" by (metis in_set_conv_nth)
    have "k \<noteq> 0" using yr k hd_movlist movlist_ne by (metis hd_conv_nth)
    then obtain t where kt: "k = Suc t" using not0_implies_Suc by auto
    have "Suc t < length movlist" using k kt by simp
    hence "thrd move_S1 (movlist ! t) = Some (movlist ! Suc t)" by (rule movlist_link_uniform)
    hence "thrd move_S1 (movlist ! t) = Some y" using k kt by simp
    thus "y \<in> ran (thrd move_S1)" unfolding ran_def by auto
  qed
qed

lemma dom_move_rvth: "dom (rvth move_S1) = V - {r}"
proof -
  have "dom (rvth move_S1) = {y. \<exists>x. rvth move_S1 y = Some x}" unfolding dom_def by auto
  also have "\<dots> = {y. \<exists>x. thrd move_S1 x = Some y}" using clauseG_move by auto
  also have "\<dots> = ran (thrd move_S1)" unfolding ran_def by auto
  also have "\<dots> = V - {r}" by (rule ran_move_thrd)
  finally show ?thesis .
qed

lemma clauseF_ip: "dom (rvth (update_tree S0 p j p jn)) = V - {r}"
  using move_rvth dom_move_rvth by simp

lemma parent_spec_move_rvth: "parent_spec (rvth move_S1)"
proof (rule parent_spec_of_distinct_chain)
  show "distinct (rev movlist)" using distinct_movlist by simp
next
  fix x y assume "rvth move_S1 x = Some y"
  hence "thrd move_S1 y = Some x" using clauseG_move by simp
  then obtain t where t: "Suc t < length movlist \<and> movlist ! t = y \<and> movlist ! Suc t = x" using move_thrd_reverse_chain by auto
  have tL: "Suc t < length movlist" using t by simp
  define k where "k = length movlist - Suc (Suc t)"
  have sk: "Suc k = length movlist - Suc t" using tL k_def by (simp add: Suc_diff_Suc)
  have kL: "k < length movlist" using tL k_def by simp
  have skL: "Suc k < length movlist" using tL sk by simp
  have e1: "rev movlist ! k = x"
  proof -
    have "rev movlist ! k = movlist ! (length movlist - Suc k)" using kL by (simp add: rev_nth)
    also have "length movlist - Suc k = Suc t" using sk tL by simp
    finally show ?thesis using t by simp
  qed
  have e2: "rev movlist ! Suc k = y"
  proof -
    have "rev movlist ! Suc k = movlist ! (length movlist - Suc (Suc k))" using skL by (simp add: rev_nth)
    also have "length movlist - Suc (Suc k) = t" using sk skL by simp
    finally show ?thesis using t by simp
  qed
  show "\<exists>k. Suc k < length (rev movlist) \<and> rev movlist ! k = x \<and> rev movlist ! Suc k = y"
    using skL e1 e2 by auto
qed

lemma clauseC_ip: "parent_spec (rvth (update_tree S0 p j p jn))"
  using move_rvth parent_spec_move_rvth by simp

text \<open>IP-4: clause H (every new last-successor is in @{term V}).  The decoration loops write only values
      already in @{term V} (the moved block's own @{const lsuc} values, @{term "the (rvth S0 p)"}, and
      @{term "lsuc S0 p"}); mirror of @{thm update_tree_lsuc_in_V} but with @{const move_S1} (no stem loop).\<close>

lemma clauseH_ip: "\<forall>v\<in>V. lsuc (update_tree S0 p j p jn) v \<in> V"
proof -
  let ?P = "(prnt S0)(p \<mapsto> j)"
  have psP: "parent_spec ?P" by (rule parent_spec_newtree_ip)
  have HS0: "\<forall>v\<in>V. lsuc S0 v \<in> V" using arb unfolding arb_invar_def by simp
  have orV: "the (rvth S0 p) \<in> V" by (rule old_rev_in_V)
  have lmv: "lsuc move_S1 = lsuc S0" by (rule move_lsuc_S1)
  have pmv: "prnt move_S1 = ?P" by (rule move_prnt_S1)
  define S2 where "S2 = last_vin_loop move_S1 j j (lsuc move_S1 p)"
  define S3 where "S3 = (if jn \<noteq> the (rvth S0 p) \<and> j \<noteq> the (rvth S0 p) then last_vout_loop S2 (the (prnt S0 p)) (if lsuc move_S1 jn = j then Some jn else None) (lsuc S0 p) (the (rvth S0 p)) else if lsuc move_S1 p \<noteq> lsuc S0 p then last_vout_loop S2 (the (prnt S0 p)) (if lsuc move_S1 jn = j then Some jn else None) (lsuc S0 p) (lsuc move_S1 p) else S2)"
  define S4 where "S4 = succ_vin_loop S3 j jn (snum S0 p)"
  define S5 where "S5 = succ_vout_loop S4 (the (prnt S0 p)) jn (snum S0 p)"
  have peq: "(p = p) = True" by simp
  have psMove: "parent_spec (prnt move_S1)" using parent_spec_newtree_ip move_prnt_S1 by simp
  define Sa where "Sa = fused_vin_loop move_S1 j j jn (lsuc move_S1 p) (snum S0 p) True True"
  define Sb where "Sb = (if jn \<noteq> the (rvth S0 p) \<and> j \<noteq> the (rvth S0 p) then fused_vout_loop Sa (the (prnt S0 p)) (if lsuc move_S1 jn = j then Some jn else None) (lsuc S0 p) (the (rvth S0 p)) jn (snum S0 p) True True else if lsuc move_S1 p \<noteq> lsuc S0 p then fused_vout_loop Sa (the (prnt S0 p)) (if lsuc move_S1 jn = j then Some jn else None) (lsuc S0 p) (lsuc move_S1 p) jn (snum S0 p) True True else fused_vout_loop Sa (the (prnt S0 p)) (if lsuc move_S1 jn = j then Some jn else None) (lsuc S0 p) (lsuc S0 p) jn (snum S0 p) False True)"
  have UTb: "update_tree S0 p j p jn = Sb" by (simp only: update_tree_def Let_def peq if_True Sb_def Sa_def move_S1_def)
  have SbS5: "Sb = S5" using update_tree_tail_eq[OF psMove] by (simp only: Sb_def Sa_def S5_def S4_def S3_def S2_def)
  have UT: "update_tree S0 p j p jn = S5" using UTb SbS5 by simp
  have pS2: "prnt S2 = ?P" using last_vin_loop_fields[OF psP, THEN mp, OF pmv] by (simp add: S2_def)
  have pS3: "prnt S3 = ?P" using last_vout_loop_fields[OF psP, THEN mp, OF pS2] pS2 by (simp add: S3_def)
  have pS4: "prnt S4 = ?P" using succ_vin_loop_fields[OF psP, THEN mp, OF pS3] by (simp add: S4_def)
  have QM: "\<forall>v\<in>V. lsuc move_S1 v \<in> V" using lmv HS0 by simp
  have lmpV: "lsuc move_S1 p \<in> V" using QM pV by simp
  have QS2: "\<forall>v\<in>V. lsuc S2 v \<in> V"
  proof -
    have "lsuc S2 = (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. lsuc move_S1 y = j) (follow ?P j)) then lsuc move_S1 p else lsuc move_S1 x)"
      using last_vin_loop_lsuc[OF psP, THEN mp, OF pmv] by (simp add: S2_def)
    thus ?thesis using QM lmpV by auto
  qed
  have Qvout: "\<And>u stp gv sv. sv \<in> V \<Longrightarrow> \<forall>v\<in>V. lsuc (last_vout_loop S2 u stp gv sv) v \<in> V"
  proof -
    fix u stp gv sv assume svV: "sv \<in> V"
    have "lsuc (last_vout_loop S2 u stp gv sv) = (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. Some y \<noteq> stp \<and> lsuc S2 y = gv) (follow ?P u)) then sv else lsuc S2 x)"
      using last_vout_loop_lsuc[OF psP, THEN mp, OF pS2] by simp
    thus "\<forall>v\<in>V. lsuc (last_vout_loop S2 u stp gv sv) v \<in> V" using svV QS2 by auto
  qed
  have QS3: "\<forall>v\<in>V. lsuc S3 v \<in> V"
  proof (cases "jn \<noteq> the (rvth S0 p) \<and> j \<noteq> the (rvth S0 p)")
    case True
    have "S3 = last_vout_loop S2 (the (prnt S0 p)) (if lsuc move_S1 jn = j then Some jn else None) (lsuc S0 p) (the (rvth S0 p))" unfolding S3_def by (rule if_P[OF True])
    thus ?thesis by (simp add: Qvout[OF orV])
  next
    case c1: False
    have S3red: "S3 = (if lsuc move_S1 p \<noteq> lsuc S0 p then last_vout_loop S2 (the (prnt S0 p)) (if lsuc move_S1 jn = j then Some jn else None) (lsuc S0 p) (lsuc move_S1 p) else S2)" unfolding S3_def by (rule if_not_P[OF c1])
    show ?thesis
    proof (cases "lsuc move_S1 p \<noteq> lsuc S0 p")
      case True
      have "S3 = last_vout_loop S2 (the (prnt S0 p)) (if lsuc move_S1 jn = j then Some jn else None) (lsuc S0 p) (lsuc move_S1 p)" using S3red by (simp add: True)
      thus ?thesis by (simp add: Qvout[OF lmpV])
    next
      case False
      have "S3 = S2" using S3red by (simp add: False)
      thus ?thesis using QS2 by simp
    qed
  qed
  have QS5: "\<forall>v\<in>V. lsuc S5 v \<in> V"
  proof -
    have "lsuc S4 = lsuc S3" using succ_vin_loop_fields[OF psP, THEN mp, OF pS3] by (simp add: S4_def)
    moreover have "lsuc S5 = lsuc S4" using succ_vout_loop_fields[OF psP, THEN mp, OF pS4] by (simp add: S5_def)
    ultimately show ?thesis using QS3 by simp
  qed
  show ?thesis using UT QS5 by simp
qed

text \<open>IP-7 (partial): clause A and the second goal.  The degenerate tree @{term "(prnt S0)(p \<mapsto> j)"} is a
      legal single-edge swap of @{term p}'s parent to @{term j}; clause A is @{thm clauseA} at @{term "k = 0"},
      composed with @{thm move_prnt}.  The pivot goal @{term "prnt (update_tree S0 p j p jn) p = Some j"} is
      immediate from @{thm move_prnt}.\<close>

lemma rooted_newtree_ip: "rooted_arborescense_invar r V ((prnt S0)(p \<mapsto> j))"
proof -
  have rinv: "rooted_arborescense_invar r V (prnt S0)" using arb unfolding arb_invar_def by simp
  have pdom: "p \<in> dom (prnt S0)" using rinv pV pne_r unfolding rooted_arborescense_invar_def by auto
  then obtain pu where pu: "prnt S0 p = Some pu" by auto
  have pnfj: "p \<notin> set (follow (prnt S0) j)" using jnotp unfolding children_def by simp
  show ?thesis using rooted_arborescense_swap_parents(1)[OF rinv pu[symmetric] pnfj jV] by simp
qed

lemma clauseA_ip: "rooted_arborescense_invar r V (prnt (update_tree S0 p j p jn))"
  using move_prnt rooted_newtree_ip by simp

lemma prnt_ip: "prnt (update_tree S0 p j p jn) p = Some j"
  using move_prnt by simp

text \<open>IP-5 (step 1): the @{const snum} closed form of the degenerate @{const update_tree}.  The move and the
      two @{const last_vin_loop}/@{const last_vout_loop} passes preserve @{const snum} (= @{term "snum S0"}),
      then @{const succ_vin_loop} adds @{term "snum S0 p"} on @{term "takeWhile (\<lambda>y. y \<noteq> jn) (follow ((prnt S0)(p \<mapsto> j)) j)"}
      (the IN-chain) and @{const succ_vout_loop} subtracts it on the OUT-chain.  (Card-match to
      @{term "card (children ((prnt S0)(p \<mapsto> j)) v)"} is step 2, still to do.)\<close>

lemma snum_ip:
  "snum (update_tree S0 p j p jn) x =
     (if x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow ((prnt S0)(p \<mapsto> j)) (the (prnt S0 p))))
      then (if x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow ((prnt S0)(p \<mapsto> j)) j)) then snum S0 x + snum S0 p else snum S0 x) - snum S0 p
      else (if x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow ((prnt S0)(p \<mapsto> j)) j)) then snum S0 x + snum S0 p else snum S0 x))"
proof -
  let ?P = "(prnt S0)(p \<mapsto> j)"
  have psP: "parent_spec ?P" by (rule parent_spec_newtree_ip)
  have smv: "snum move_S1 = snum S0" by (rule move_snum_S1)
  have pmv: "prnt move_S1 = ?P" by (rule move_prnt_S1)
  define S2 where "S2 = last_vin_loop move_S1 j j (lsuc move_S1 p)"
  define S3 where "S3 = (if jn \<noteq> the (rvth S0 p) \<and> j \<noteq> the (rvth S0 p) then last_vout_loop S2 (the (prnt S0 p)) (if lsuc move_S1 jn = j then Some jn else None) (lsuc S0 p) (the (rvth S0 p)) else if lsuc move_S1 p \<noteq> lsuc S0 p then last_vout_loop S2 (the (prnt S0 p)) (if lsuc move_S1 jn = j then Some jn else None) (lsuc S0 p) (lsuc move_S1 p) else S2)"
  define S4 where "S4 = succ_vin_loop S3 j jn (snum S0 p)"
  define S5 where "S5 = succ_vout_loop S4 (the (prnt S0 p)) jn (snum S0 p)"
  have peq: "(p = p) = True" by simp
  have psMove: "parent_spec (prnt move_S1)" using parent_spec_newtree_ip move_prnt_S1 by simp
  define Sa where "Sa = fused_vin_loop move_S1 j j jn (lsuc move_S1 p) (snum S0 p) True True"
  define Sb where "Sb = (if jn \<noteq> the (rvth S0 p) \<and> j \<noteq> the (rvth S0 p) then fused_vout_loop Sa (the (prnt S0 p)) (if lsuc move_S1 jn = j then Some jn else None) (lsuc S0 p) (the (rvth S0 p)) jn (snum S0 p) True True else if lsuc move_S1 p \<noteq> lsuc S0 p then fused_vout_loop Sa (the (prnt S0 p)) (if lsuc move_S1 jn = j then Some jn else None) (lsuc S0 p) (lsuc move_S1 p) jn (snum S0 p) True True else fused_vout_loop Sa (the (prnt S0 p)) (if lsuc move_S1 jn = j then Some jn else None) (lsuc S0 p) (lsuc S0 p) jn (snum S0 p) False True)"
  have UTb: "update_tree S0 p j p jn = Sb" by (simp only: update_tree_def Let_def peq if_True Sb_def Sa_def move_S1_def)
  have SbS5: "Sb = S5" using update_tree_tail_eq[OF psMove] by (simp only: Sb_def Sa_def S5_def S4_def S3_def S2_def)
  have UT: "update_tree S0 p j p jn = S5" using UTb SbS5 by simp
  have pS2: "prnt S2 = ?P" using last_vin_loop_fields[OF psP, THEN mp, OF pmv] by (simp add: S2_def)
  have pS3: "prnt S3 = ?P" using last_vout_loop_fields[OF psP, THEN mp, OF pS2] pS2 by (simp add: S3_def)
  have pS4: "prnt S4 = ?P" using succ_vin_loop_fields[OF psP, THEN mp, OF pS3] by (simp add: S4_def)
  have snS2: "snum S2 = snum S0" using last_vin_loop_fields[OF psP, THEN mp, OF pmv] smv by (simp add: S2_def)
  have snS3: "snum S3 = snum S0" using last_vout_loop_fields[OF psP, THEN mp, OF pS2] snS2 by (auto simp add: S3_def)
  have snS4: "snum S4 = (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow ?P j)) then snum S3 x + snum S0 p else snum S3 x)"
    using succ_vin_loop_snum[OF psP, THEN mp, OF pS3] by (simp add: S4_def)
  have snS5: "snum S5 = (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow ?P (the (prnt S0 p)))) then snum S4 x - snum S0 p else snum S4 x)"
    using succ_vout_loop_snum[OF psP, THEN mp, OF pS4] by (simp add: S5_def)
  show ?thesis using UT snS5 snS4 snS3 by simp
qed

text \<open>IP-5 (step 2, foundations): the descendant decomposition for the degenerate tree.  Off the moved block
      the ancestor walk is unchanged (@{thm follow_upd_fresh}, since @{term p} is not an ancestor of any
      @{term "u \<notin> set (block S0 p)"}); so @{term "children ((prnt S0)(p \<mapsto> j)) v"} splits into the old
      children outside the block plus the block nodes that @{term v} now dominates.  (Region card-match still to do.)\<close>

lemma follow_newtree_off_block_ip:
  assumes unb: "u \<notin> set (block S0 p)"
  shows "follow ((prnt S0)(p \<mapsto> j)) u = follow (prnt S0) u"
proof -
  have rinv: "rooted_arborescense_invar r V (prnt S0)" using arb unfolding arb_invar_def by simp
  have ps: "parent_spec (prnt S0)" by (rule rooted_arborescense_invar_parent_spec[OF rinv])
  have ps': "parent_spec ((prnt S0)(p \<mapsto> j))" by (rule parent_spec_newtree_ip)
  have "p \<notin> set (follow (prnt S0) u)"
  proof
    assume "p \<in> set (follow (prnt S0) u)"
    hence "u \<in> children (prnt S0) p" unfolding children_def by simp
    hence "u \<in> set (block S0 p)" using block_props(4)[OF arb pV] by simp
    thus False using unb by simp
  qed
  thus ?thesis using follow_upd_fresh[OF ps ps'] by simp
qed

lemma children_ip_decomp:
  "children ((prnt S0)(p \<mapsto> j)) v = (children (prnt S0) v - set (block S0 p)) \<union> {u \<in> set (block S0 p). v \<in> set (follow ((prnt S0)(p \<mapsto> j)) u)}"
proof
  show "children ((prnt S0)(p \<mapsto> j)) v \<subseteq> (children (prnt S0) v - set (block S0 p)) \<union> {u \<in> set (block S0 p). v \<in> set (follow ((prnt S0)(p \<mapsto> j)) u)}"
  proof
    fix u assume "u \<in> children ((prnt S0)(p \<mapsto> j)) v"
    hence vu: "v \<in> set (follow ((prnt S0)(p \<mapsto> j)) u)" unfolding children_def by simp
    show "u \<in> (children (prnt S0) v - set (block S0 p)) \<union> {u \<in> set (block S0 p). v \<in> set (follow ((prnt S0)(p \<mapsto> j)) u)}"
    proof (cases "u \<in> set (block S0 p)")
      case True thus ?thesis using vu by auto
    next
      case False
      have "v \<in> set (follow (prnt S0) u)" using vu follow_newtree_off_block_ip[OF False] by simp
      hence "u \<in> children (prnt S0) v" unfolding children_def by simp
      thus ?thesis using False by auto
    qed
  qed
next
  show "(children (prnt S0) v - set (block S0 p)) \<union> {u \<in> set (block S0 p). v \<in> set (follow ((prnt S0)(p \<mapsto> j)) u)} \<subseteq> children ((prnt S0)(p \<mapsto> j)) v"
  proof
    fix u assume "u \<in> (children (prnt S0) v - set (block S0 p)) \<union> {u \<in> set (block S0 p). v \<in> set (follow ((prnt S0)(p \<mapsto> j)) u)}"
    thus "u \<in> children ((prnt S0)(p \<mapsto> j)) v"
    proof
      assume "u \<in> children (prnt S0) v - set (block S0 p)"
      hence unb: "u \<notin> set (block S0 p)" and "v \<in> set (follow (prnt S0) u)" unfolding children_def by auto
      hence "v \<in> set (follow ((prnt S0)(p \<mapsto> j)) u)" using follow_newtree_off_block_ip[OF unb] by simp
      thus ?thesis unfolding children_def by simp
    next
      assume "u \<in> {u \<in> set (block S0 p). v \<in> set (follow ((prnt S0)(p \<mapsto> j)) u)}"
      thus ?thesis unfolding children_def by simp
    qed
  qed
qed

text \<open>IP-5 (step 2, block-ancestor facts): in the new tree the moved block keeps its internal structure and
      hangs entirely below @{term p} (hence below @{term j}); so a node on @{term j}'s path gains the whole
      block as descendants.  These are the @{const move_S1} analogues of @{thm block_p_under_i}/@{thm block_p_desc_of_j}.\<close>

lemma block_p_newprnt_step_ip:
  assumes ub: "u \<in> set (block S0 p)" and unp: "u \<noteq> p"
  shows "\<exists>w. ((prnt S0)(p \<mapsto> j)) u = Some w \<and> w \<in> set (block S0 p)"
proof -
  have rinv: "rooted_arborescense_invar r V (prnt S0)" using arb unfolding arb_invar_def by simp
  have ps: "parent_spec (prnt S0)" by (rule rooted_arborescense_invar_parent_spec[OF rinv])
  have prnr: "prnt S0 r = None" using rinv unfolding rooted_arborescense_invar_def by auto
  have domA: "dom (prnt S0) = V - {r}" using rinv unfolding rooted_arborescense_invar_def by auto
  have uV: "u \<in> V" using ub block_p_subset_V by auto
  have uch: "u \<in> children (prnt S0) p" using ub block_props(4)[OF arb pV] by simp
  hence pfu: "p \<in> set (follow (prnt S0) u)" unfolding children_def by simp
  have unr: "u \<noteq> r"
  proof
    assume "u = r"
    hence "p \<in> set (follow (prnt S0) r)" using pfu by simp
    moreover have "follow (prnt S0) r = [r]" using prnr by (subst follow_ps_simps[OF ps]) simp
    ultimately show False using pne_r by simp
  qed
  hence "u \<in> dom (prnt S0)" using uV domA by simp
  then obtain w where w: "prnt S0 u = Some w" by auto
  have fu: "follow (prnt S0) u = u # follow (prnt S0) w" using w by (subst follow_ps_simps[OF ps]) simp
  have "p \<in> set (follow (prnt S0) w)" using pfu fu unp by simp
  hence "w \<in> children (prnt S0) p" unfolding children_def by simp
  hence wb: "w \<in> set (block S0 p)" using block_props(4)[OF arb pV] by simp
  have "((prnt S0)(p \<mapsto> j)) u = Some w" using w unp by simp
  thus ?thesis using wb by auto
qed

lemma block_p_under_p_ip: "u \<in> set (block S0 p) \<longrightarrow> p \<in> set (follow ((prnt S0)(p \<mapsto> j)) u)"
proof -
  have psP: "parent_spec ((prnt S0)(p \<mapsto> j))" by (rule parent_spec_newtree_ip)
  show ?thesis
  proof (induction rule: parent_spec_i.follow.pinduct[OF follow_dom_ps[OF psP, of u]])
    case (1 u)
    show ?case
    proof
      assume ub: "u \<in> set (block S0 p)"
      show "p \<in> set (follow ((prnt S0)(p \<mapsto> j)) u)"
      proof (cases "u = p")
        case True
        thus ?thesis using follow_hd_ps[OF psP, of p] follow_ne_ps[OF psP, of p] by (metis hd_in_set)
      next
        case False
        obtain w where w: "((prnt S0)(p \<mapsto> j)) u = Some w" and wb: "w \<in> set (block S0 p)"
          using block_p_newprnt_step_ip[OF ub False] by auto
        have "follow ((prnt S0)(p \<mapsto> j)) u = u # follow ((prnt S0)(p \<mapsto> j)) w"
          using w by (subst follow_ps_simps[OF psP]) simp
        moreover have "p \<in> set (follow ((prnt S0)(p \<mapsto> j)) w)" using 1(2)[OF w] wb by (rule mp)
        ultimately show ?thesis by simp
      qed
    qed
  qed
qed

lemma block_p_desc_of_j_ip:
  assumes vj: "v \<in> set (follow (prnt S0) j)" and ub: "u \<in> set (block S0 p)"
  shows "v \<in> set (follow ((prnt S0)(p \<mapsto> j)) u)"
proof -
  have psP: "parent_spec ((prnt S0)(p \<mapsto> j))" by (rule parent_spec_newtree_ip)
  have pfu: "p \<in> set (follow ((prnt S0)(p \<mapsto> j)) u)" using block_p_under_p_ip ub by (rule mp)
  from pfu obtain A B where AB: "follow ((prnt S0)(p \<mapsto> j)) u = A @ p # B" by (meson split_list)
  have "follow ((prnt S0)(p \<mapsto> j)) p = p # B" using follow_append_ps[OF psP AB] by auto
  moreover have "follow ((prnt S0)(p \<mapsto> j)) p = p # follow ((prnt S0)(p \<mapsto> j)) j"
    by (subst follow_ps_simps[OF psP]) simp
  ultimately have "B = follow ((prnt S0)(p \<mapsto> j)) j" by simp
  moreover have "follow ((prnt S0)(p \<mapsto> j)) j = follow (prnt S0) j" using follow_newtree_off_block_ip[OF j_notin_block_p] by auto
  ultimately have "v \<in> set B" using vj by simp
  thus ?thesis using AB by simp
qed

lemma children_ip_jpath:
  assumes vj: "v \<in> set (follow (prnt S0) j)"
  shows "children ((prnt S0)(p \<mapsto> j)) v = children (prnt S0) v \<union> set (block S0 p)"
proof -
  have "{u \<in> set (block S0 p). v \<in> set (follow ((prnt S0)(p \<mapsto> j)) u)} = set (block S0 p)"
    using block_p_desc_of_j_ip[OF vj] by auto
  thus ?thesis using children_ip_decomp[of v] by auto
qed

text \<open>IP-5 (step 2, card-match): clause I for the degenerate branch.  Combining the @{const snum} closed
      form @{thm snum_ip} with the descendant analysis: on the IN-chain (@{term j}'s path strictly below
      @{term jn}) the new subtree gains the block (@{term "snum S0 v + snum S0 p"}); on the OUT-chain
      (@{term "the (prnt S0 p)"}'s path strictly below @{term jn}) it loses the block; on the block interior
      and elsewhere it is unchanged.  A join-geometry disjointness lemma keeps the two chains
      apart.  All region lemmas mirror the reversal's @{text card_children_newprnt_INchain} etc. with i = p.\<close>

lemma p_in_block_ip: "p \<in> set (block S0 p)"
  using block_props(5)[OF arb pV] block_props(2)[OF arb pV] by (metis hd_in_set)

lemma children_ip_p: "children ((prnt S0)(p \<mapsto> j)) p = set (block S0 p)"
proof -
  have "{u \<in> set (block S0 p). p \<in> set (follow ((prnt S0)(p \<mapsto> j)) u)} = set (block S0 p)"
    using block_p_under_p_ip by auto
  moreover have "children (prnt S0) p \<subseteq> set (block S0 p)" using block_props(4)[OF arb pV] by auto
  ultimately show ?thesis using children_ip_decomp[of p] by auto
qed

lemma newprnt_follow_dichotomy_ip:
  assumes ub: "u \<in> set (block S0 p)" and vu: "v \<in> set (follow ((prnt S0)(p \<mapsto> j)) u)"
  shows "v \<in> set (block S0 p) \<or> v \<in> set (follow (prnt S0) j)"
proof -
  have psP: "parent_spec ((prnt S0)(p \<mapsto> j))" by (rule parent_spec_newtree_ip)
  have pu: "p \<in> set (follow ((prnt S0)(p \<mapsto> j)) u)" using block_p_under_p_ip ub by (rule mp)
  from pu obtain A B where AB: "follow ((prnt S0)(p \<mapsto> j)) u = A @ p # B" by (meson split_list)
  have fp: "follow ((prnt S0)(p \<mapsto> j)) p = p # B" using follow_append_ps[OF psP AB] by auto
  have "follow ((prnt S0)(p \<mapsto> j)) p = p # follow ((prnt S0)(p \<mapsto> j)) j" by (subst follow_ps_simps[OF psP]) simp
  hence Beq: "B = follow (prnt S0) j" using fp follow_newtree_off_block_ip[OF j_notin_block_p] by simp
  from vu AB have "v \<in> set A \<or> v \<in> set (p # B)" by auto
  thus ?thesis
  proof
    assume "v \<in> set (p # B)"
    hence "v = p \<or> v \<in> set (follow (prnt S0) j)" using Beq by auto
    thus ?thesis using p_in_block_ip by auto
  next
    assume vA: "v \<in> set A"
    then obtain A1 A2 where "A = A1 @ v # A2" by (meson split_list)
    hence "follow ((prnt S0)(p \<mapsto> j)) u = A1 @ v # (A2 @ p # B)" using AB by simp
    hence "follow ((prnt S0)(p \<mapsto> j)) v = v # (A2 @ p # B)" by (rule follow_append_ps[OF psP])
    hence "p \<in> set (follow ((prnt S0)(p \<mapsto> j)) v)" by simp
    hence "v \<in> children ((prnt S0)(p \<mapsto> j)) p" unfolding children_def by simp
    thus ?thesis using children_ip_p by simp
  qed
qed

lemma children_ip_off_jpath:
  assumes vnb: "v \<notin> set (block S0 p)" and vnj: "v \<notin> set (follow (prnt S0) j)"
  shows "children ((prnt S0)(p \<mapsto> j)) v = children (prnt S0) v - set (block S0 p)"
proof -
  have emp: "{u \<in> set (block S0 p). v \<in> set (follow ((prnt S0)(p \<mapsto> j)) u)} = {}"
  proof -
    { fix u assume "u \<in> set (block S0 p)" and "v \<in> set (follow ((prnt S0)(p \<mapsto> j)) u)"
      hence "v \<in> set (block S0 p) \<or> v \<in> set (follow (prnt S0) j)" using newprnt_follow_dichotomy_ip by auto
      hence False using vnb vnj by simp }
    thus ?thesis by auto
  qed
  have "children ((prnt S0)(p \<mapsto> j)) v = (children (prnt S0) v - set (block S0 p)) \<union> {u \<in> set (block S0 p). v \<in> set (follow ((prnt S0)(p \<mapsto> j)) u)}"
    by (rule children_ip_decomp)
  also have "\<dots> = children (prnt S0) v - set (block S0 p)" unfolding emp by simp
  finally show ?thesis .
qed

lemma inchain_block_disjoint_ip:
  assumes jneq: "jn = join_of (prnt S0) p j"
      and vin: "v \<in> set (takeWhile (\<lambda>x. x \<noteq> jn) (follow (prnt S0) j))" and jnj: "jn \<in> set (follow (prnt S0) j)"
  shows "children (prnt S0) v \<inter> set (block S0 p) = {}"
proof (rule ccontr)
  assume "children (prnt S0) v \<inter> set (block S0 p) \<noteq> {}"
  then obtain u where uv: "u \<in> children (prnt S0) v" and ub: "u \<in> set (block S0 p)" by auto
  have vu: "v \<in> set (follow (prnt S0) u)" using uv unfolding children_def by simp
  have pu: "p \<in> set (follow (prnt S0) u)" using ub block_props(4)[OF arb pV] unfolding children_def by simp
  from vu obtain X Y where XY: "follow (prnt S0) u = X @ v # Y" by (meson split_list)
  have fv: "follow (prnt S0) v = v # Y" using follow_append_ps[OF ppt XY] by auto
  have jnv: "jn \<in> set (follow (prnt S0) v)" and vnej: "v \<noteq> jn" using below_jn[OF vin jnj] by auto
  have vj: "v \<in> set (follow (prnt S0) j)" using vin set_takeWhileD by fastforce
  show False
  proof (cases "p \<in> set (v # Y)")
    case True
    hence "p \<in> set (follow (prnt S0) v)" using fv by simp
    hence vcp: "v \<in> children (prnt S0) p" unfolding children_def by simp
    have "j \<in> children (prnt S0) v" using vj unfolding children_def by simp
    moreover have "children (prnt S0) v \<subseteq> children (prnt S0) p" using vcp by (rule children_subset[OF ppt])
    ultimately have "j \<in> children (prnt S0) p" by auto
    thus False using jnotp by simp
  next
    case False
    hence "p \<in> set X" using pu XY by auto
    then obtain X1 X2 where "X = X1 @ p # X2" by (meson split_list)
    hence "follow (prnt S0) u = X1 @ p # (X2 @ v # Y)" using XY by simp
    hence "follow (prnt S0) p = p # (X2 @ v # Y)" by (rule follow_append_ps[OF ppt])
    hence vfp: "v \<in> set (follow (prnt S0) p)" by simp
    have lst: "last (follow (prnt S0) p) = last (follow (prnt S0) j)"
      using last_follow_root[OF rinv0 pV] last_follow_root[OF rinv0 jV] by simp
    have "v \<in> set (follow (prnt S0) (join_of (prnt S0) p j))" using join_of_first[OF ppt lst vfp vj] by auto
    hence vjn: "v \<in> set (follow (prnt S0) jn)" using jneq by simp
    have "v = jn" using ancestor_antisym[OF ppt vjn jnv] by auto
    thus False using vnej by simp
  qed
qed

lemma card_children_ip_INchain:
  assumes jneq: "jn = join_of (prnt S0) p j"
      and vin: "v \<in> set (takeWhile (\<lambda>x. x \<noteq> jn) (follow (prnt S0) j))" and jnj: "jn \<in> set (follow (prnt S0) j)"
  shows "card (children ((prnt S0)(p \<mapsto> j)) v) = snum S0 v + snum S0 p"
proof -
  have vj: "v \<in> set (follow (prnt S0) j)" using vin set_takeWhileD by fastforce
  have vV: "v \<in> V" using follow_subset_V[OF rinv0 jV] vj by auto
  have chnp: "children ((prnt S0)(p \<mapsto> j)) v = children (prnt S0) v \<union> set (block S0 p)" by (rule children_ip_jpath[OF vj])
  have disj: "children (prnt S0) v \<inter> set (block S0 p) = {}" by (rule inchain_block_disjoint_ip[OF jneq vin jnj])
  show ?thesis using chnp disj children_finite[OF vV] vV on_card arb unfolding arb_invar_def by (simp add: card_Un_disjoint)
qed

lemma card_children_ip_OUTchain:
  assumes jneq: "jn = join_of (prnt S0) p j" and jnp: "jn \<in> set (follow (prnt S0) p)" and pjn: "p \<noteq> jn"
      and vin: "v \<in> set (takeWhile (\<lambda>x. x \<noteq> jn) (follow (prnt S0) (the (prnt S0 p))))"
  shows "card (children ((prnt S0)(p \<mapsto> j)) v) = snum S0 v - snum S0 p"
proof -
  have "p \<in> dom (prnt S0)" using pV pne_r rooted_arborescense_invar_dom[OF rinv0] by simp
  then obtain vo where pvo: "prnt S0 p = Some vo" by auto
  have voeq: "the (prnt S0 p) = vo" using pvo by simp
  have fp: "follow (prnt S0) p = p # follow (prnt S0) vo" using pvo by (subst follow_ps_simps[OF ppt]) simp
  have vofv: "vo \<in> set (follow (prnt S0) vo)" using follow_hd_ps[OF ppt, of vo] follow_ne_ps[OF ppt, of vo] by (metis hd_in_set)
  have voap: "vo \<in> set (follow (prnt S0) p)" using fp vofv by simp
  have distp: "distinct (follow (prnt S0) p)" by (rule follow_distinct_ps[OF ppt])
  have pnvo: "p \<notin> set (follow (prnt S0) vo)" using distp fp by simp
  have jnvo: "jn \<in> set (follow (prnt S0) vo)" using jnp pjn fp by simp
  have vin': "v \<in> set (takeWhile (\<lambda>x. x \<noteq> jn) (follow (prnt S0) vo))" using vin voeq by simp
  have vvo: "v \<in> set (follow (prnt S0) vo)" using vin' set_takeWhileD by fastforce
  have jnv: "jn \<in> set (follow (prnt S0) v)" and vnej: "v \<noteq> jn" using below_jn_gen[OF vin' jnvo] by auto
  have voV: "vo \<in> V" using follow_subset_V[OF rinv0 pV] voap by auto
  have vV: "v \<in> V" using follow_subset_V[OF rinv0 voV] vvo by auto
  have vap: "v \<in> set (follow (prnt S0) p)" using follow_trans[OF ppt voap vvo] by auto
  have vnb: "v \<notin> set (block S0 p)"
  proof
    assume "v \<in> set (block S0 p)"
    hence pfv: "p \<in> set (follow (prnt S0) v)" using block_props(4)[OF arb pV] unfolding children_def by simp
    have "p \<in> set (follow (prnt S0) vo)" using follow_trans[OF ppt vvo pfv] by auto
    thus False using pnvo by simp
  qed
  have vnj: "v \<notin> set (follow (prnt S0) j)"
  proof
    assume vj: "v \<in> set (follow (prnt S0) j)"
    have lst: "last (follow (prnt S0) p) = last (follow (prnt S0) j)" using last_follow_root[OF rinv0 pV] last_follow_root[OF rinv0 jV] by simp
    have "v \<in> set (follow (prnt S0) (join_of (prnt S0) p j))" using join_of_first[OF ppt lst vap vj] by auto
    hence vfjn: "v \<in> set (follow (prnt S0) jn)" using jneq by simp
    have "v = jn" using ancestor_antisym[OF ppt vfjn jnv] by auto
    thus False using vnej by simp
  qed
  have bsub: "set (block S0 p) \<subseteq> children (prnt S0) v"
  proof
    fix u assume "u \<in> set (block S0 p)"
    hence pfu: "p \<in> set (follow (prnt S0) u)" using block_props(4)[OF arb pV] unfolding children_def by simp
    have "v \<in> set (follow (prnt S0) u)" using follow_trans[OF ppt pfu vap] by auto
    thus "u \<in> children (prnt S0) v" unfolding children_def by simp
  qed
  have choff: "children ((prnt S0)(p \<mapsto> j)) v = children (prnt S0) v - set (block S0 p)" by (rule children_ip_off_jpath[OF vnb vnj])
  show ?thesis using choff card_Diff_subset[OF finite_set bsub] vV on_card arb unfolding arb_invar_def by simp
qed

lemma block_p_notin_follow_j:
  assumes vb: "v \<in> set (block S0 p)"
  shows "v \<notin> set (follow (prnt S0) j)"
proof
  assume vj: "v \<in> set (follow (prnt S0) j)"
  have pfv: "p \<in> set (follow (prnt S0) v)" using vb block_props(4)[OF arb pV] unfolding children_def by simp
  have "p \<in> set (follow (prnt S0) j)" using follow_trans[OF ppt vj pfv] by auto
  hence "j \<in> children (prnt S0) p" unfolding children_def by simp
  thus False using jnotp by simp
qed

lemma card_children_ip_jpath_above:
  assumes vj: "v \<in> set (follow (prnt S0) j)" and bsub: "set (block S0 p) \<subseteq> children (prnt S0) v" and vV: "v \<in> V"
  shows "card (children ((prnt S0)(p \<mapsto> j)) v) = snum S0 v"
proof -
  have "children ((prnt S0)(p \<mapsto> j)) v = children (prnt S0) v \<union> set (block S0 p)" by (rule children_ip_jpath[OF vj])
  also have "\<dots> = children (prnt S0) v" using bsub by auto
  finally have "children ((prnt S0)(p \<mapsto> j)) v = children (prnt S0) v" .
  thus ?thesis using vV arb unfolding arb_invar_def by simp
qed

lemma card_children_ip_disjoint:
  assumes vnb: "v \<notin> set (block S0 p)" and vnj: "v \<notin> set (follow (prnt S0) j)"
      and disj: "set (block S0 p) \<inter> children (prnt S0) v = {}" and vV: "v \<in> V"
  shows "card (children ((prnt S0)(p \<mapsto> j)) v) = snum S0 v"
proof -
  have "children ((prnt S0)(p \<mapsto> j)) v = children (prnt S0) v - set (block S0 p)" by (rule children_ip_off_jpath[OF vnb vnj])
  also have "\<dots> = children (prnt S0) v" using disj by auto
  finally have "children ((prnt S0)(p \<mapsto> j)) v = children (prnt S0) v" .
  thus ?thesis using vV arb unfolding arb_invar_def by simp
qed

lemma follow_ip_block_prefix:
  "u \<in> set (block S0 p) \<longrightarrow> (\<forall>v \<in> set (block S0 p). (v \<in> set (follow ((prnt S0)(p \<mapsto> j)) u)) = (v \<in> set (follow (prnt S0) u)))"
proof -
  have psP: "parent_spec ((prnt S0)(p \<mapsto> j))" by (rule parent_spec_newtree_ip)
  have "p \<in> dom (prnt S0)" using pV pne_r rooted_arborescense_invar_dom[OF rinv0] by simp
  then obtain vo where pvo: "prnt S0 p = Some vo" by auto
  have fpS: "follow (prnt S0) p = p # follow (prnt S0) vo" using pvo by (subst follow_ps_simps[OF ppt]) simp
  have distp: "distinct (follow (prnt S0) p)" by (rule follow_distinct_ps[OF ppt])
  have pnvo: "p \<notin> set (follow (prnt S0) vo)" using distp fpS by simp
  show ?thesis
  proof (induction rule: parent_spec_i.follow.pinduct[OF follow_dom_ps[OF psP, of u]])
    case (1 u)
    show ?case
    proof
      assume ub: "u \<in> set (block S0 p)"
      show "\<forall>v \<in> set (block S0 p). (v \<in> set (follow ((prnt S0)(p \<mapsto> j)) u)) = (v \<in> set (follow (prnt S0) u))"
      proof (cases "u = p")
        case True
        have fpP: "follow ((prnt S0)(p \<mapsto> j)) p = p # follow (prnt S0) j"
          using follow_newtree_off_block_ip[OF j_notin_block_p] by (subst follow_ps_simps[OF psP]) simp
        show ?thesis
        proof (intro ballI)
          fix v assume vb: "v \<in> set (block S0 p)"
          have vnfj: "v \<notin> set (follow (prnt S0) j)" by (rule block_p_notin_follow_j[OF vb])
          have vnvo: "v \<notin> set (follow (prnt S0) vo)"
          proof
            assume vvo: "v \<in> set (follow (prnt S0) vo)"
            have pfv: "p \<in> set (follow (prnt S0) v)" using vb block_props(4)[OF arb pV] unfolding children_def by simp
            have "p \<in> set (follow (prnt S0) vo)" using follow_trans[OF ppt vvo pfv] by auto
            thus False using pnvo by simp
          qed
          show "(v \<in> set (follow ((prnt S0)(p \<mapsto> j)) u)) = (v \<in> set (follow (prnt S0) u))"
            using True fpP fpS vnfj vnvo by auto
        qed
      next
        case False
        obtain w where w: "((prnt S0)(p \<mapsto> j)) u = Some w" and wb: "w \<in> set (block S0 p)" using block_p_newprnt_step_ip[OF ub False] by auto
        have wS0: "prnt S0 u = Some w" using w False by (simp add: fun_upd_other)
        have fP: "follow ((prnt S0)(p \<mapsto> j)) u = u # follow ((prnt S0)(p \<mapsto> j)) w" using w by (subst follow_ps_simps[OF psP]) simp
        have fS: "follow (prnt S0) u = u # follow (prnt S0) w" using wS0 by (subst follow_ps_simps[OF ppt]) simp
        have IH: "\<forall>v \<in> set (block S0 p). (v \<in> set (follow ((prnt S0)(p \<mapsto> j)) w)) = (v \<in> set (follow (prnt S0) w))" using 1(2)[OF w] wb by (rule mp)
        show ?thesis using fP fS IH by auto
      qed
    qed
  qed
qed

lemma children_ip_inblock:
  assumes vb: "v \<in> set (block S0 p)"
  shows "children ((prnt S0)(p \<mapsto> j)) v = children (prnt S0) v"
proof -
  have "\<And>u. (u \<in> children ((prnt S0)(p \<mapsto> j)) v) = (u \<in> children (prnt S0) v)"
  proof -
    fix u
    show "(u \<in> children ((prnt S0)(p \<mapsto> j)) v) = (u \<in> children (prnt S0) v)"
    proof (cases "u \<in> set (block S0 p)")
      case True
      have "(v \<in> set (follow ((prnt S0)(p \<mapsto> j)) u)) = (v \<in> set (follow (prnt S0) u))"
        using follow_ip_block_prefix True vb by auto
      thus ?thesis unfolding children_def by simp
    next
      case False
      have "follow ((prnt S0)(p \<mapsto> j)) u = follow (prnt S0) u" by (rule follow_newtree_off_block_ip[OF False])
      thus ?thesis unfolding children_def by simp
    qed
  qed
  thus ?thesis by auto
qed

lemma vout_nb: "the (prnt S0 p) \<notin> set (block S0 p)"
proof -
  have "p \<in> dom (prnt S0)" using pV pne_r rooted_arborescense_invar_dom[OF rinv0] by simp
  then obtain vo where pvo: "prnt S0 p = Some vo" by auto
  have voeq: "the (prnt S0 p) = vo" using pvo by simp
  have fp: "follow (prnt S0) p = p # follow (prnt S0) vo" using pvo by (subst follow_ps_simps[OF ppt]) simp
  have "distinct (follow (prnt S0) p)" by (rule follow_distinct_ps[OF ppt])
  hence pnvo: "p \<notin> set (follow (prnt S0) vo)" using fp by simp
  show ?thesis
  proof
    assume "the (prnt S0 p) \<in> set (block S0 p)"
    hence "vo \<in> set (block S0 p)" using voeq by simp
    hence "p \<in> set (follow (prnt S0) vo)" using block_props(4)[OF arb pV] unfolding children_def by simp
    thus False using pnvo by simp
  qed
qed

lemma snum_ip':
  "snum (update_tree S0 p j p jn) x =
     (if x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow (prnt S0) (the (prnt S0 p))))
      then (if x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow (prnt S0) j)) then snum S0 x + snum S0 p else snum S0 x) - snum S0 p
      else (if x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow (prnt S0) j)) then snum S0 x + snum S0 p else snum S0 x))"
proof -
  have fj: "follow ((prnt S0)(p \<mapsto> j)) j = follow (prnt S0) j" by (rule follow_newtree_off_block_ip[OF j_notin_block_p])
  have fvo: "follow ((prnt S0)(p \<mapsto> j)) (the (prnt S0 p)) = follow (prnt S0) (the (prnt S0 p))" by (rule follow_newtree_off_block_ip[OF vout_nb])
  show ?thesis using snum_ip fj fvo by simp
qed

lemma OUT_notin_follow_j:
  assumes jneq: "jn = join_of (prnt S0) p j" and jnp: "jn \<in> set (follow (prnt S0) p)" and pjn: "p \<noteq> jn"
      and vin: "v \<in> set (takeWhile (\<lambda>x. x \<noteq> jn) (follow (prnt S0) (the (prnt S0 p))))"
  shows "v \<notin> set (follow (prnt S0) j)"
proof -
  have "p \<in> dom (prnt S0)" using pV pne_r rooted_arborescense_invar_dom[OF rinv0] by simp
  then obtain vo where pvo: "prnt S0 p = Some vo" by auto
  have voeq: "the (prnt S0 p) = vo" using pvo by simp
  have fp: "follow (prnt S0) p = p # follow (prnt S0) vo" using pvo by (subst follow_ps_simps[OF ppt]) simp
  have vofv: "vo \<in> set (follow (prnt S0) vo)" using follow_hd_ps[OF ppt, of vo] follow_ne_ps[OF ppt, of vo] by (metis hd_in_set)
  have voap: "vo \<in> set (follow (prnt S0) p)" using fp vofv by simp
  have jnvo: "jn \<in> set (follow (prnt S0) vo)" using jnp pjn fp by simp
  have vin': "v \<in> set (takeWhile (\<lambda>x. x \<noteq> jn) (follow (prnt S0) vo))" using vin voeq by simp
  have vvo: "v \<in> set (follow (prnt S0) vo)" using vin' set_takeWhileD by fastforce
  have jnv: "jn \<in> set (follow (prnt S0) v)" and vnej: "v \<noteq> jn" using below_jn_gen[OF vin' jnvo] by auto
  have vap: "v \<in> set (follow (prnt S0) p)" using follow_trans[OF ppt voap vvo] by auto
  show ?thesis
  proof
    assume vj: "v \<in> set (follow (prnt S0) j)"
    have lst: "last (follow (prnt S0) p) = last (follow (prnt S0) j)" using last_follow_root[OF rinv0 pV] last_follow_root[OF rinv0 jV] by simp
    have "v \<in> set (follow (prnt S0) (join_of (prnt S0) p j))" using join_of_first[OF ppt lst vap vj] by auto
    hence "v \<in> set (follow (prnt S0) jn)" using jneq by simp
    hence "v = jn" using ancestor_antisym[OF ppt _ jnv] by simp
    thus False using vnej by simp
  qed
qed

lemma jpath_above_bsub:
  assumes jnj: "jn \<in> set (follow (prnt S0) j)" and jnp: "jn \<in> set (follow (prnt S0) p)"
      and vj: "v \<in> set (follow (prnt S0) j)" and vnin: "v \<notin> set (takeWhile (\<lambda>x. x \<noteq> jn) (follow (prnt S0) j))"
  shows "set (block S0 p) \<subseteq> children (prnt S0) v"
proof -
  from jnj obtain A B where AB: "follow (prnt S0) j = A @ jn # B" by (meson split_list)
  have fjn: "follow (prnt S0) jn = jn # B" using follow_append_ps[OF ppt AB] by auto
  have dist: "distinct (follow (prnt S0) j)" by (rule follow_distinct_ps[OF ppt])
  have jnA: "jn \<notin> set A" using dist AB by auto
  have tw: "takeWhile (\<lambda>x. x \<noteq> jn) (follow (prnt S0) j) = A"
  proof -
    have "takeWhile (\<lambda>x. x \<noteq> jn) (A @ (jn # B)) = A @ takeWhile (\<lambda>x. x \<noteq> jn) (jn # B)" by (rule takeWhile_append2) (use jnA in auto)
    thus ?thesis using AB by simp
  qed
  have "v \<in> set (jn # B)" using vj AB vnin tw by auto
  hence vjn: "v \<in> set (follow (prnt S0) jn)" using fjn by simp
  have vp: "v \<in> set (follow (prnt S0) p)" using follow_trans[OF ppt jnp vjn] by auto
  show ?thesis
  proof
    fix u assume "u \<in> set (block S0 p)"
    hence pfu: "p \<in> set (follow (prnt S0) u)" using block_props(4)[OF arb pV] unfolding children_def by simp
    have "v \<in> set (follow (prnt S0) u)" using follow_trans[OF ppt pfu vp] by auto
    thus "u \<in> children (prnt S0) v" unfolding children_def by simp
  qed
qed

lemma disjoint_region_disj:
  assumes jnj: "jn \<in> set (follow (prnt S0) j)" and jnp: "jn \<in> set (follow (prnt S0) p)" and pjn: "p \<noteq> jn"
      and vnout: "v \<notin> set (takeWhile (\<lambda>x. x \<noteq> jn) (follow (prnt S0) (the (prnt S0 p))))"
      and vnj: "v \<notin> set (follow (prnt S0) j)" and vnb: "v \<notin> set (block S0 p)"
  shows "set (block S0 p) \<inter> children (prnt S0) v = {}"
proof (rule ccontr)
  assume "set (block S0 p) \<inter> children (prnt S0) v \<noteq> {}"
  then obtain u where ub: "u \<in> set (block S0 p)" and uv: "u \<in> children (prnt S0) v" by auto
  have vfu: "v \<in> set (follow (prnt S0) u)" using uv unfolding children_def by simp
  have pfu: "p \<in> set (follow (prnt S0) u)" using ub block_props(4)[OF arb pV] unfolding children_def by simp
  from vfu obtain X Y where XY: "follow (prnt S0) u = X @ v # Y" by (meson split_list)
  have fv: "follow (prnt S0) v = v # Y" using follow_append_ps[OF ppt XY] by auto
  have "p \<in> dom (prnt S0)" using pV pne_r rooted_arborescense_invar_dom[OF rinv0] by simp
  then obtain vo where pvo: "prnt S0 p = Some vo" by auto
  have voeq: "the (prnt S0 p) = vo" using pvo by simp
  have fp: "follow (prnt S0) p = p # follow (prnt S0) vo" using pvo by (subst follow_ps_simps[OF ppt]) simp
  have jnvo: "jn \<in> set (follow (prnt S0) vo)" using jnp pjn fp by simp
  show False
  proof (cases "p \<in> set (v # Y)")
    case True
    hence "p \<in> set (follow (prnt S0) v)" using fv by simp
    hence "v \<in> children (prnt S0) p" unfolding children_def by simp
    hence "v \<in> set (block S0 p)" using block_props(4)[OF arb pV] by simp
    thus False using vnb by simp
  next
    case False
    hence "p \<in> set X" using pfu XY by auto
    then obtain X1 X2 where "X = X1 @ p # X2" by (meson split_list)
    hence "follow (prnt S0) u = X1 @ p # (X2 @ v # Y)" using XY by simp
    hence "follow (prnt S0) p = p # (X2 @ v # Y)" by (rule follow_append_ps[OF ppt])
    hence vfp: "v \<in> set (follow (prnt S0) p)" by simp
    have vnp: "v \<noteq> p" using vnb p_in_block_ip by auto
    have vvo: "v \<in> set (follow (prnt S0) vo)" using vfp fp vnp by simp
    show False
    proof (cases "v \<in> set (takeWhile (\<lambda>x. x \<noteq> jn) (follow (prnt S0) vo))")
      case True
      thus False using vnout voeq by simp
    next
      case notTW: False
      from jnvo obtain A B where AB: "follow (prnt S0) vo = A @ jn # B" by (meson split_list)
      have fjn: "follow (prnt S0) jn = jn # B" using follow_append_ps[OF ppt AB] by auto
      have dist: "distinct (follow (prnt S0) vo)" by (rule follow_distinct_ps[OF ppt])
      have jnA: "jn \<notin> set A" using dist AB by auto
      have tw: "takeWhile (\<lambda>x. x \<noteq> jn) (follow (prnt S0) vo) = A"
      proof -
        have "takeWhile (\<lambda>x. x \<noteq> jn) (A @ (jn # B)) = A @ takeWhile (\<lambda>x. x \<noteq> jn) (jn # B)" by (rule takeWhile_append2) (use jnA in auto)
        thus ?thesis using AB by simp
      qed
      have vjn: "v \<in> set (follow (prnt S0) jn)" using vvo AB notTW tw fjn by auto
      from jnj obtain C D where CD: "follow (prnt S0) j = C @ jn # D" by (meson split_list)
      have "follow (prnt S0) jn = jn # D" using follow_append_ps[OF ppt CD] by auto
      hence "set (follow (prnt S0) jn) \<subseteq> set (follow (prnt S0) j)" using CD by auto
      thus False using vjn vnj by auto
    qed
  qed
qed

lemma clauseI_ip:
  assumes jneq: "jn = join_of (prnt S0) p j" and jnp: "jn \<in> set (follow (prnt S0) p)" and pjn: "p \<noteq> jn" and jnj: "jn \<in> set (follow (prnt S0) j)"
  shows "\<forall>v\<in>V. snum (update_tree S0 p j p jn) v = card (children (prnt (update_tree S0 p j p jn)) v)"
proof
  fix v assume vV: "v \<in> V"
  have rhs: "card (children (prnt (update_tree S0 p j p jn)) v) = card (children ((prnt S0)(p \<mapsto> j)) v)" using move_prnt by simp
  have sX: "snum S0 v = card (children (prnt S0) v)" using vV arb unfolding arb_invar_def by simp
  have card_else: "v \<notin> set (takeWhile (\<lambda>x. x \<noteq> jn) (follow (prnt S0) (the (prnt S0 p)))) \<Longrightarrow> v \<notin> set (takeWhile (\<lambda>x. x \<noteq> jn) (follow (prnt S0) j)) \<Longrightarrow> card (children ((prnt S0)(p \<mapsto> j)) v) = snum S0 v"
  proof -
    assume notOUT: "v \<notin> set (takeWhile (\<lambda>x. x \<noteq> jn) (follow (prnt S0) (the (prnt S0 p))))"
    assume notIN: "v \<notin> set (takeWhile (\<lambda>x. x \<noteq> jn) (follow (prnt S0) j))"
    show "card (children ((prnt S0)(p \<mapsto> j)) v) = snum S0 v"
    proof (cases "v \<in> set (block S0 p)")
      case True
      have "children ((prnt S0)(p \<mapsto> j)) v = children (prnt S0) v" by (rule children_ip_inblock[OF True])
      thus ?thesis using sX by simp
    next
      case notBlk: False
      show ?thesis
      proof (cases "v \<in> set (follow (prnt S0) j)")
        case True
        have bsub: "set (block S0 p) \<subseteq> children (prnt S0) v" by (rule jpath_above_bsub[OF jnj jnp True notIN])
        thus ?thesis using card_children_ip_jpath_above[OF True bsub vV] by simp
      next
        case notJ: False
        have disj: "set (block S0 p) \<inter> children (prnt S0) v = {}" by (rule disjoint_region_disj[OF jnj jnp pjn notOUT notJ notBlk])
        thus ?thesis using card_children_ip_disjoint[OF notBlk notJ disj vV] by simp
      qed
    qed
  qed
  show "snum (update_tree S0 p j p jn) v = card (children (prnt (update_tree S0 p j p jn)) v)"
  proof (cases "v \<in> set (takeWhile (\<lambda>x. x \<noteq> jn) (follow (prnt S0) (the (prnt S0 p))))")
    case OUT: True
    have notIN: "v \<notin> set (takeWhile (\<lambda>x. x \<noteq> jn) (follow (prnt S0) j))" using OUT_notin_follow_j[OF jneq jnp pjn OUT] set_takeWhileD by fastforce
    have "snum (update_tree S0 p j p jn) v = snum S0 v - snum S0 p" using snum_ip' OUT notIN by simp
    also have "\<dots> = card (children ((prnt S0)(p \<mapsto> j)) v)" using card_children_ip_OUTchain[OF jneq jnp pjn OUT] by simp
    finally show ?thesis using rhs by simp
  next
    case notOUT: False
    show ?thesis
    proof (cases "v \<in> set (takeWhile (\<lambda>x. x \<noteq> jn) (follow (prnt S0) j))")
      case IN: True
      have "snum (update_tree S0 p j p jn) v = snum S0 v + snum S0 p" using snum_ip' notOUT IN by simp
      also have "\<dots> = card (children ((prnt S0)(p \<mapsto> j)) v)" using card_children_ip_INchain[OF jneq IN jnj] by simp
      finally show ?thesis using rhs by simp
    next
      case notIN: False
      have "snum (update_tree S0 p j p jn) v = snum S0 v" using snum_ip' notOUT notIN by simp
      also have "\<dots> = card (children ((prnt S0)(p \<mapsto> j)) v)" using card_else[OF notOUT notIN] by simp
      finally show ?thesis using rhs by simp
    qed
  qed
qed

text \<open>IP-6 (contiguity half of clause J): the moved thread is a DFS-preorder of the new tree, so every
      subtree is a contiguous prefix (@{thm preorder_contiguous}).  The DFS-step @{text movlist_dfs} reuses
      @{thm arb_dfs_step}[OF arb] for surviving old edges (off/inside the block), @{thm splice_dfs} for the
      @{text old_rev} junction, and the seam @{term "old_last \<rightarrow> hd TL"} via @{thm block_p_desc_of_j_ip}.\<close>

lemma holed_dfs_ip:
  assumes lt: "Suc t' < length holed"
  shows "\<exists>a. ((prnt S0)(p \<mapsto> j)) (holed ! Suc t') = Some a \<and> a \<in> set (follow ((prnt S0)(p \<mapsto> j)) (holed ! t'))"
proof -
  have srcin: "holed ! t' \<in> set holed" using lt by (simp add: nth_mem)
  have tgtin: "holed ! Suc t' \<in> set holed" using lt by (simp add: nth_mem)
  have srcnb: "holed ! t' \<notin> set (block S0 p)" using srcin holed_set by auto
  have tgtnb: "holed ! Suc t' \<notin> set (block S0 p)" using tgtin holed_set by auto
  have tgt_ne_p: "holed ! Suc t' \<noteq> p" using tgtnb p_in_block_ip by auto
  have ntt: "((prnt S0)(p \<mapsto> j)) (holed ! Suc t') = prnt S0 (holed ! Suc t')" using tgt_ne_p by simp
  have flsrc: "follow ((prnt S0)(p \<mapsto> j)) (holed ! t') = follow (prnt S0) (holed ! t')" by (rule follow_newtree_off_block_ip[OF srcnb])
  show ?thesis
  proof (cases "holed ! t' = the (rvth S0 p)")
    case False
    have edge: "thrd S0 (holed ! t') = Some (holed ! Suc t')" using holed_old_adj[OF lt] False by simp
    have srcV: "holed ! t' \<in> V" using srcin holed_set by auto
    obtain a where a: "prnt S0 (holed ! Suc t') = Some a" and afl: "a \<in> set (follow (prnt S0) (holed ! t'))" using arb_dfs_step[OF arb srcV edge] by auto
    show ?thesis using ntt a afl flsrc by auto
  next
    case True
    have hd: "holed = alpha @ beta" unfolding holed_def by simp
    have lh: "length holed = length alpha + length beta" using hd by simp
    have la1: "length alpha - 1 < length holed" using alpha_ne lh by (cases "length alpha") auto
    have idx_or: "alpha ! (length alpha - 1) = last alpha" using alpha_ne by (simp add: last_conv_nth)
    have hor: "holed ! (length alpha - 1) = the (rvth S0 p)" using hd alpha_ne old_rev_last_alpha idx_or by (simp add: nth_append)
    have "holed ! t' = holed ! (length alpha - 1)" using True hor by simp
    hence teq: "t' = length alpha - 1" using holed_distinct lt la1 by (metis Suc_lessD nth_eq_iff_index_eq)
    have Suct: "Suc t' = length alpha" using teq alpha_ne by simp
    have bne: "beta \<noteq> []" using lt lh Suct by (cases beta) auto
    have "holed ! Suc t' = beta ! 0" using hd Suct by (simp add: nth_append)
    hence hb: "holed ! Suc t' = hd beta" using bne by (simp add: hd_conv_nth)
    obtain g where g: "prnt S0 (hd beta) = Some g" and gfl: "g \<in> set (follow (prnt S0) (the (rvth S0 p)))" using splice_dfs[OF bne] by auto
    show ?thesis using ntt hb g gfl flsrc True by auto
  qed
qed

lemma block_p_dfs:
  assumes dnb: "Suc d < length (block S0 p)"
  shows "\<exists>a. ((prnt S0)(p \<mapsto> j)) (block S0 p ! Suc d) = Some a \<and> a \<in> set (follow ((prnt S0)(p \<mapsto> j)) (block S0 p ! d))"
proof -
  have edge: "thrd S0 (block S0 p ! d) = Some (block S0 p ! Suc d)" using block_p_link[of d] dnb by simp
  have dmem: "block S0 p ! d \<in> set (block S0 p)" using dnb by (metis Suc_lessD nth_mem)
  have smem: "block S0 p ! Suc d \<in> set (block S0 p)" using dnb by (metis nth_mem)
  have dV: "block S0 p ! d \<in> V" using dmem block_p_subset_V by auto
  obtain a where a: "prnt S0 (block S0 p ! Suc d) = Some a" and afl: "a \<in> set (follow (prnt S0) (block S0 p ! d))" using arb_dfs_step[OF arb dV edge] by auto
  have hdp: "block S0 p ! 0 = p" using block_props(5)[OF arb pV] block_props(2)[OF arb pV] by (simp add: hd_conv_nth)
  have lpos: "0 < length (block S0 p)" using dnb by linarith
  have sne_p: "block S0 p ! Suc d \<noteq> p"
  proof
    assume "block S0 p ! Suc d = p"
    hence "block S0 p ! Suc d = block S0 p ! 0" using hdp by simp
    hence "Suc d = 0" using block_distinct_V[OF pV] dnb lpos by (simp add: nth_eq_iff_index_eq)
    thus False by simp
  qed
  have ntt: "((prnt S0)(p \<mapsto> j)) (block S0 p ! Suc d) = Some a" using a sne_p by simp
  have psuc: "p \<in> set (follow (prnt S0) (block S0 p ! Suc d))" using smem block_props(4)[OF arb pV] unfolding children_def by simp
  have "follow (prnt S0) (block S0 p ! Suc d) = block S0 p ! Suc d # follow (prnt S0) a" using a by (subst follow_ps_simps[OF ppt]) simp
  hence "p \<in> set (follow (prnt S0) a)" using psuc sne_p by simp
  hence "a \<in> children (prnt S0) p" unfolding children_def by simp
  hence amem: "a \<in> set (block S0 p)" using block_props(4)[OF arb pV] by simp
  have "a \<in> set (follow ((prnt S0)(p \<mapsto> j)) (block S0 p ! d))" using follow_ip_block_prefix amem dmem afl by auto
  thus ?thesis using ntt by auto
qed

lemma movlist_dfs:
  assumes lt: "Suc t < length movlist"
  shows "\<exists>a. ((prnt S0)(p \<mapsto> j)) (movlist ! Suc t) = Some a \<and> a \<in> set (follow ((prnt S0)(p \<mapsto> j)) (movlist ! t))"
proof -
  let ?n1 = "length (takeWhile (\<lambda>x. x \<noteq> j) holed)"
  let ?nb = "length (block S0 p)"
  let ?TL = "tl (dropWhile (\<lambda>x. x \<noteq> j) holed)"
  have hlen: "length holed = ?n1 + 1 + length ?TL" by (rule holed_len)
  have mllen: "length movlist = ?n1 + 1 + ?nb + length ?TL" by (rule ml_len)
  have bne: "block S0 p \<noteq> []" by (rule block_props(2)[OF arb pV])
  have nbpos: "0 < ?nb" using bne by auto
  have psP: "parent_spec ((prnt S0)(p \<mapsto> j))" by (rule parent_spec_newtree_ip)
  consider (TW) "t < ?n1" | (J) "t = ?n1" | (NB) "?n1 < t" "t < ?n1 + ?nb" | (SEAM) "t = ?n1 + ?nb" | (TL) "?n1 + ?nb < t" by linarith
  then show ?thesis
  proof cases
    case TW
    have s: "movlist ! t = holed ! t" using ml_le_n1 TW by simp
    have tgt: "movlist ! Suc t = holed ! Suc t" using ml_le_n1 TW by simp
    have sjt: "Suc t < length holed" using TW hlen by simp
    show ?thesis using holed_dfs_ip[OF sjt] s tgt by simp
  next
    case J
    have s: "movlist ! t = j" using ml_j J by simp
    have tgt: "movlist ! Suc t = p" using J ml_nb[of 0] nbpos bne block_props(5)[OF arb pV] by (simp add: hd_conv_nth)
    have "((prnt S0)(p \<mapsto> j)) p = Some j" by simp
    moreover have "j \<in> set (follow ((prnt S0)(p \<mapsto> j)) j)" using follow_hd_ps[OF psP, of j] follow_ne_ps[OF psP, of j] by (metis hd_in_set)
    ultimately show ?thesis using s tgt by auto
  next
    case NB
    obtain d where td: "t = ?n1 + 1 + d" using NB(1) less_imp_Suc_add by fastforce
    have dnb: "Suc d < ?nb" using NB(2) td by simp
    have s: "movlist ! t = block S0 p ! d" using ml_nb[of d] dnb td by simp
    have tgt: "movlist ! Suc t = block S0 p ! Suc d" using td ml_nb[of "Suc d"] dnb by simp
    show ?thesis using block_p_dfs[OF dnb] s tgt by simp
  next
    case SEAM
    have TLpos: "0 < length ?TL" using lt mllen SEAM by linarith
    have TLne: "?TL \<noteq> []" using TLpos by (cases ?TL) auto
    obtain nb' where nbeq: "?nb = Suc nb'" using bne by (cases "block S0 p") auto
    have td: "t = ?n1 + 1 + nb'" using SEAM nbeq by simp
    have s: "movlist ! t = lsuc S0 p"
      using ml_nb[of nb'] nbeq td bne block_props(3)[OF arb pV] by (simp add: last_conv_nth)
    have jpos: "holed ! ?n1 = j" by (rule holed_j_pos)
    have holedhdTL: "holed ! Suc ?n1 = movlist ! Suc t"
    proof -
      have "movlist ! Suc t = holed ! (?n1 + 1 + 0)" using SEAM ml_tl[OF TLpos] by simp
      thus ?thesis by simp
    qed
    have sjt: "Suc ?n1 < length holed" using hlen TLpos by simp
    obtain a where a: "((prnt S0)(p \<mapsto> j)) (holed ! Suc ?n1) = Some a" and afl: "a \<in> set (follow ((prnt S0)(p \<mapsto> j)) (holed ! ?n1))" using holed_dfs_ip[OF sjt] by auto
    have aj: "a \<in> set (follow ((prnt S0)(p \<mapsto> j)) j)" using afl jpos by simp
    have jol: "j \<in> set (follow ((prnt S0)(p \<mapsto> j)) (lsuc S0 p))"
    proof -
      have jfj: "j \<in> set (follow (prnt S0) j)" using follow_hd_ps[OF ppt, of j] follow_ne_ps[OF ppt, of j] by (metis hd_in_set)
      have ol_b: "lsuc S0 p \<in> set (block S0 p)" by (simp add: block_def)
      show ?thesis using block_p_desc_of_j_ip[OF jfj ol_b] by auto
    qed
    have "set (follow ((prnt S0)(p \<mapsto> j)) j) \<subseteq> set (follow ((prnt S0)(p \<mapsto> j)) (lsuc S0 p))" using follow_sub_of_mem[OF psP jol] by auto
    hence afl2: "a \<in> set (follow ((prnt S0)(p \<mapsto> j)) (lsuc S0 p))" using aj by auto
    show ?thesis using a holedhdTL s afl2 by auto
  next
    case TL
    define c where "c = t - (?n1 + 1 + ?nb)"
    have tc: "t = ?n1 + 1 + ?nb + c" using TL c_def by simp
    have clt: "c < length ?TL" using lt mllen tc by linarith
    have c1lt: "Suc c < length ?TL" using lt mllen tc by linarith
    have s: "movlist ! t = holed ! (?n1 + 1 + c)" using ml_tl[OF clt] tc by simp
    have E2: "movlist ! (?n1 + 1 + ?nb + Suc c) = holed ! (?n1 + 1 + Suc c)" by (rule ml_tl[OF c1lt])
    have tgt: "movlist ! Suc t = holed ! Suc (?n1 + 1 + c)" using tc E2 by simp
    have sjt: "Suc (?n1 + 1 + c) < length holed" using hlen c1lt by simp
    show ?thesis using holed_dfs_ip[OF sjt] s tgt by simp
  qed
qed

lemma children_ip_subset_V:
  assumes vV: "v \<in> V"
  shows "children ((prnt S0)(p \<mapsto> j)) v \<subseteq> V"
proof
  fix u assume "u \<in> children ((prnt S0)(p \<mapsto> j)) v"
  hence vfu: "v \<in> set (follow ((prnt S0)(p \<mapsto> j)) u)" unfolding children_def by simp
  have rinvN: "rooted_arborescense_invar r V ((prnt S0)(p \<mapsto> j))" by (rule rooted_newtree_ip)
  have psN: "parent_spec ((prnt S0)(p \<mapsto> j))" using rinvN rooted_arborescense_invar_parent_spec by auto
  show "u \<in> V"
  proof (rule ccontr)
    assume "u \<notin> V"
    hence "u \<notin> dom ((prnt S0)(p \<mapsto> j))" using rooted_arborescense_invar_dom[OF rinvN] by auto
    hence "((prnt S0)(p \<mapsto> j)) u = None" by auto
    hence "follow ((prnt S0)(p \<mapsto> j)) u = [u]" by (subst follow_ps_simps[OF psN]) simp
    hence "v = u" using vfu by simp
    thus False using vV \<open>u \<notin> V\<close> by simp
  qed
qed

lemma clauseJ_contig_ip:
  assumes vV: "v \<in> V"
  shows "\<exists>pre suf. follow (thrd (update_tree S0 p j p jn)) v = pre @ suf \<and> set pre = children (prnt (update_tree S0 p j p jn)) v \<and> pre \<noteq> [] \<and> hd pre = v"
proof -
  have psP: "parent_spec ((prnt S0)(p \<mapsto> j))" by (rule parent_spec_newtree_ip)
  have psF: "parent_spec (thrd move_S1)" by (rule parent_spec_move_thrd)
  have oe: "follow (thrd move_S1) r = movlist" by (rule out_edge_ip)
  have root0: "((prnt S0)(p \<mapsto> j)) (movlist ! 0) = None"
  proof -
    have "movlist ! 0 = r" using hd_movlist movlist_ne by (simp add: hd_conv_nth)
    moreover have "((prnt S0)(p \<mapsto> j)) r = None"
    proof -
      have "prnt S0 r = None" using rinv0 unfolding rooted_arborescense_invar_def by auto
      thus "((prnt S0)(p \<mapsto> j)) r = None" using pne_r by simp
    qed
    ultimately show ?thesis by simp
  qed
  have dfs: "\<And>t. Suc t < length movlist \<Longrightarrow> \<exists>a. ((prnt S0)(p \<mapsto> j)) (movlist ! Suc t) = Some a \<and> a \<in> set (follow ((prnt S0)(p \<mapsto> j)) (movlist ! t))" using movlist_dfs by auto
  have vin: "v \<in> set movlist" using vV set_movlist by simp
  have subv: "children ((prnt S0)(p \<mapsto> j)) v \<subseteq> set movlist" using children_ip_subset_V[OF vV] set_movlist by simp
  obtain pre suf where P1: "follow (thrd move_S1) v = pre @ suf" and P2: "set pre = children ((prnt S0)(p \<mapsto> j)) v" and P3: "pre \<noteq> []" and P4: "hd pre = v"
    using preorder_contiguous[OF psP psF oe root0 dfs vin subv] by auto
  have ft: "thrd (update_tree S0 p j p jn) = thrd move_S1" by (rule move_thrd)
  have pt: "prnt (update_tree S0 p j p jn) = (prnt S0)(p \<mapsto> j)" by (rule move_prnt)
  show ?thesis using P1 P2 P3 P4 by (auto simp: ft pt)
qed

text \<open>IP-6 (pointwise-\<open>lsuc\<close> half of clause J, k=0 / i=p branch).  These helpers mirror the reversal
      branch's @{thm lsuc_last}, specialised to the rigid block move: the moved block @{term "block S0 p"}
      is unchanged internally, so @{const move_S1}'s thread agrees with @{term "thrd S0"} off the three
      spliced keys.  The exit facts (@{text s0_exit}, @{text move_block_exit}, @{text move_IN_exit},
      @{text move_untouched_exit}) show the thread-successor of a node's last descendant leaves that
      node's new subtree; @{text outset_lsuc_p}/@{text outset_iff} characterise the @{const last_vout_loop}
      run on the @{term v_out}-branch (the @{text up_limit} guard argument).\<close>

lemma block_p_notin_follow_vout:
  assumes vb: "v \<in> set (block S0 p)"
  shows "v \<notin> set (follow (prnt S0) (the (prnt S0 p)))"
proof -
  have "p \<in> dom (prnt S0)" using pV pne_r rooted_arborescense_invar_dom[OF rinv0] by simp
  then obtain vo where pvo: "prnt S0 p = Some vo" by auto
  have voeq: "the (prnt S0 p) = vo" using pvo by simp
  have fp: "follow (prnt S0) p = p # follow (prnt S0) vo" using pvo by (subst follow_ps_simps[OF ppt]) simp
  have "distinct (follow (prnt S0) p)" by (rule follow_distinct_ps[OF ppt])
  hence pnvo: "p \<notin> set (follow (prnt S0) vo)" using fp by simp
  show ?thesis
  proof
    assume "v \<in> set (follow (prnt S0) (the (prnt S0 p)))"
    hence vvo: "v \<in> set (follow (prnt S0) vo)" using voeq by simp
    have pfv: "p \<in> set (follow (prnt S0) v)" using vb block_props(4)[OF arb pV] unfolding children_def by simp
    have "p \<in> set (follow (prnt S0) vo)" using follow_trans[OF ppt vvo pfv] by auto
    thus False using pnvo by simp
  qed
qed

lemma thrd_j_notin_block:
  assumes g: "thrd S0 j \<noteq> Some p" and tj: "thrd S0 j = Some a"
  shows "a \<notin> set (block S0 p)"
proof
  assume ab: "a \<in> set (block S0 p)"
  have Gs: "\<And>x y. (thrd S0 x = Some y) = (rvth S0 y = Some x)" using arb unfolding arb_invar_def by auto
  have rj: "rvth S0 a = Some j" using tj Gs by simp
  obtain t where tlen: "t < length (block S0 p)" and at: "block S0 p ! t = a" using ab by (meson in_set_conv_nth)
  show False
  proof (cases t)
    case 0
    have "block S0 p ! 0 = p" using block_props(5)[OF arb pV] block_props(2)[OF arb pV] by (simp add: hd_conv_nth)
    hence "a = p" using at 0 by simp
    thus False using tj g by simp
  next
    case (Suc t')
    have "Suc t' < length (block S0 p)" using tlen Suc by simp
    hence "thrd S0 (block S0 p ! t') = Some (block S0 p ! Suc t')" by (rule block_p_link)
    hence "thrd S0 (block S0 p ! t') = Some a" using at Suc by simp
    hence "rvth S0 a = Some (block S0 p ! t')" using Gs by simp
    hence "block S0 p ! t' = j" using rj by simp
    moreover have "block S0 p ! t' \<in> set (block S0 p)" using tlen Suc by (metis Suc_lessD nth_mem)
    ultimately show False using j_notin_block_p by simp
  qed
qed

lemma s0_exit:
  assumes wV: "w \<in> V"
  shows "thrd S0 (lsuc S0 w) = None \<or> the (thrd S0 (lsuc S0 w)) \<notin> children (prnt S0) w"
proof (cases "thrd S0 (lsuc S0 w)")
  case None thus ?thesis by simp
next
  case (Some x)
  have pst: "parent_spec (thrd S0)" using arb unfolding arb_invar_def by simp
  have fw: "follow (thrd S0) w = block S0 w @ follow (thrd S0) x"
    using block_props(1)[OF arb wV] Some by simp
  have xin: "x \<in> set (follow (thrd S0) x)" using follow_hd_ps[OF pst, of x] follow_ne_ps[OF pst, of x] by (metis hd_in_set)
  have "distinct (follow (thrd S0) w)" by (rule follow_distinct_ps[OF pst])
  hence "x \<notin> set (block S0 w)" using fw xin by (auto simp add: distinct_append)
  hence "x \<notin> children (prnt S0) w" using block_props(4)[OF arb wV] by simp
  thus ?thesis using Some by simp
qed

lemma move_block_exit:
  assumes wV: "w \<in> V" and wb: "w \<in> set (block S0 p)"
  shows "thrd move_S1 (lsuc S0 w) = None \<or> the (thrd move_S1 (lsuc S0 w)) \<notin> children (prnt S0) w"
proof -
  have wpc: "w \<in> children (prnt S0) p" using wb block_props(4)[OF arb pV] by simp
  have bwsub: "set (block S0 w) \<subseteq> set (block S0 p)"
    using children_subset[OF ppt wpc] block_props(4)[OF arb wV] block_props(4)[OF arb pV] by simp
  have lsw_bw: "lsuc S0 w \<in> set (block S0 w)"
    using block_props(3)[OF arb wV] block_props(2)[OF arb wV] by (metis last_in_set)
  have lswb: "lsuc S0 w \<in> set (block S0 p)" using lsw_bw bwsub by auto
  have chw_sub: "children (prnt S0) w \<subseteq> set (block S0 p)" using block_props(4)[OF arb wV] bwsub by simp
  show ?thesis
  proof (cases "thrd S0 j = Some p")
    case True
    have "thrd move_S1 = thrd S0" by (rule move_thrd_shortcut[OF True])
    thus ?thesis using s0_exit[OF wV] by simp
  next
    case False
    have tm: "thrd move_S1 = (thrd S0)(the (rvth S0 p) := thrd S0 (lsuc S0 p), j \<mapsto> p, lsuc S0 p := thrd S0 j)"
      by (rule move_thrd_splice[OF False])
    have lsw_ne_or: "lsuc S0 w \<noteq> the (rvth S0 p)" using lswb old_rev_notin_block_p by auto
    have lsw_ne_j: "lsuc S0 w \<noteq> j" using lswb j_notin_block_p by auto
    show ?thesis
    proof (cases "lsuc S0 w = lsuc S0 p")
      case True
      have "thrd move_S1 (lsuc S0 w) = thrd S0 j" using tm True lsw_ne_or lsw_ne_j by simp
      moreover have "thrd S0 j = None \<or> the (thrd S0 j) \<notin> children (prnt S0) w"
        using thrd_j_notin_block[OF False] chw_sub by (cases "thrd S0 j") auto
      ultimately show ?thesis by simp
    next
      case False
      have "thrd move_S1 (lsuc S0 w) = thrd S0 (lsuc S0 w)" using tm False lsw_ne_or lsw_ne_j by simp
      thus ?thesis using s0_exit[OF wV] by simp
    qed
  qed
qed

lemma move_succ_off:
  assumes x1: "x \<noteq> the (rvth S0 p)" and x2: "x \<noteq> j" and x3: "x \<noteq> lsuc S0 p"
  shows "thrd move_S1 x = thrd S0 x"
proof (cases "thrd S0 j = Some p")
  case True thus ?thesis using move_thrd_shortcut[OF True] by simp
next
  case False thus ?thesis using move_thrd_splice[OF False] x1 x2 x3 by simp
qed

lemma move_IN_exit:
  assumes vV: "v \<in> V" and vj: "v \<in> set (follow (prnt S0) j)" and lvj: "lsuc S0 v = j"
  shows "thrd move_S1 (lsuc S0 p) = None \<or> the (thrd move_S1 (lsuc S0 p)) \<notin> children (prnt S0) v \<union> set (block S0 p)"
proof (cases "thrd S0 j = Some p")
  case False
  have tm: "thrd move_S1 (lsuc S0 p) = thrd S0 j" using move_thrd_splice[OF False] old_rev_ne_j[OF False] by simp
  have e1: "thrd S0 j = None \<or> the (thrd S0 j) \<notin> set (block S0 p)" using thrd_j_notin_block[OF False] by (cases "thrd S0 j") auto
  have e2: "thrd S0 j = None \<or> the (thrd S0 j) \<notin> children (prnt S0) v" using s0_exit[OF vV] lvj by simp
  show ?thesis using tm e1 e2 by (cases "thrd S0 j") auto
next
  case True
  have tm: "thrd move_S1 = thrd S0" by (rule move_thrd_shortcut[OF True])
  have pst: "parent_spec (thrd S0)" using arb unfolding arb_invar_def by simp
  show ?thesis
  proof (cases "thrd S0 (lsuc S0 p)")
    case None thus ?thesis using tm by simp
  next
    case (Some y)
    have fv: "follow (thrd S0) v = block S0 v @ follow (thrd S0) p"
      using block_props(1)[OF arb vV] lvj True by simp
    have fp: "follow (thrd S0) p = block S0 p @ follow (thrd S0) y"
      using block_props(1)[OF arb pV] Some by simp
    have yin: "y \<in> set (follow (thrd S0) y)" using follow_hd_ps[OF pst, of y] follow_ne_ps[OF pst, of y] by (metis hd_in_set)
    have fvd: "follow (thrd S0) v = block S0 v @ block S0 p @ follow (thrd S0) y" using fv fp by simp
    have "distinct (follow (thrd S0) v)" by (rule follow_distinct_ps[OF pst])
    hence "y \<notin> set (block S0 v) \<and> y \<notin> set (block S0 p)" using fvd yin by (auto simp add: distinct_append)
    hence "y \<notin> children (prnt S0) v \<and> y \<notin> set (block S0 p)" using block_props(4)[OF arb vV] by simp
    thus ?thesis using tm Some by auto
  qed
qed


lemma lsuc_last_ip:
  assumes jneq: "jn = join_of (prnt S0) p j" and jnp: "jn \<in> set (follow (prnt S0) p)" and pjn: "p \<noteq> jn" and jnj: "jn \<in> set (follow (prnt S0) j)"
      and vV: "v \<in> V"
      and P1: "follow (thrd (update_tree S0 p j p jn)) v = pre @ suf"
      and P2: "set pre = children (prnt (update_tree S0 p j p jn)) v"
      and P3: "pre \<noteq> []" and P4: "hd pre = v"
  shows "lsuc (update_tree S0 p j p jn) v = last pre"
proof -
  let ?P = "(prnt S0)(p \<mapsto> j)"
  have psP: "parent_spec ?P" by (rule parent_spec_newtree_ip)
  have lmv: "lsuc move_S1 = lsuc S0" by (rule move_lsuc_S1)
  have pmv: "prnt move_S1 = ?P" by (rule move_prnt_S1)
  have fj: "follow ?P j = follow (prnt S0) j" by (rule follow_newtree_off_block_ip[OF j_notin_block_p])
  obtain vo where vo: "prnt S0 p = Some vo" using rooted_arborescense_invar_dom[OF rinv0] pV pne_r by auto
  have voeq: "the (prnt S0 p) = vo" using vo by simp
  have fvo: "follow ?P vo = follow (prnt S0) vo" using follow_newtree_off_block_ip[OF vout_nb] voeq by simp
  define S2 where "S2 = last_vin_loop move_S1 j j (lsuc move_S1 p)"
  define S3 where "S3 = (if jn \<noteq> the (rvth S0 p) \<and> j \<noteq> the (rvth S0 p) then last_vout_loop S2 (the (prnt S0 p)) (if lsuc move_S1 jn = j then Some jn else None) (lsuc S0 p) (the (rvth S0 p)) else if lsuc move_S1 p \<noteq> lsuc S0 p then last_vout_loop S2 (the (prnt S0 p)) (if lsuc move_S1 jn = j then Some jn else None) (lsuc S0 p) (lsuc move_S1 p) else S2)"
  define S4 where "S4 = succ_vin_loop S3 j jn (snum S0 p)"
  define S5 where "S5 = succ_vout_loop S4 (the (prnt S0 p)) jn (snum S0 p)"
  have peq: "(p = p) = True" by simp
  have psMove: "parent_spec (prnt move_S1)" using parent_spec_newtree_ip move_prnt_S1 by simp
  define Sa where "Sa = fused_vin_loop move_S1 j j jn (lsuc move_S1 p) (snum S0 p) True True"
  define Sb where "Sb = (if jn \<noteq> the (rvth S0 p) \<and> j \<noteq> the (rvth S0 p) then fused_vout_loop Sa (the (prnt S0 p)) (if lsuc move_S1 jn = j then Some jn else None) (lsuc S0 p) (the (rvth S0 p)) jn (snum S0 p) True True else if lsuc move_S1 p \<noteq> lsuc S0 p then fused_vout_loop Sa (the (prnt S0 p)) (if lsuc move_S1 jn = j then Some jn else None) (lsuc S0 p) (lsuc move_S1 p) jn (snum S0 p) True True else fused_vout_loop Sa (the (prnt S0 p)) (if lsuc move_S1 jn = j then Some jn else None) (lsuc S0 p) (lsuc S0 p) jn (snum S0 p) False True)"
  have UTb: "update_tree S0 p j p jn = Sb" by (simp only: update_tree_def Let_def peq if_True Sb_def Sa_def move_S1_def)
  have SbS5: "Sb = S5" using update_tree_tail_eq[OF psMove] by (simp only: Sb_def Sa_def S5_def S4_def S3_def S2_def)
  have UT: "update_tree S0 p j p jn = S5" using UTb SbS5 by simp
  have pS2: "prnt S2 = ?P" using last_vin_loop_fields[OF psP, THEN mp, OF pmv] by (simp add: S2_def)
  have pS3: "prnt S3 = ?P" using last_vout_loop_fields[OF psP, THEN mp, OF pS2] pS2 by (simp add: S3_def)
  have pS4: "prnt S4 = ?P" using succ_vin_loop_fields[OF psP, THEN mp, OF pS3] by (simp add: S4_def)
  have pS5: "prnt S5 = ?P" using move_prnt by (simp add: UT[symmetric])
  have thS5: "thrd S5 = thrd move_S1" using move_thrd by (simp add: UT[symmetric])
  have psF: "parent_spec (thrd S5)" using clauseB_ip by (simp add: UT[symmetric])
  have split: "follow (thrd S5) v = pre @ suf" using P1 by (simp add: UT)
  have setpre: "set pre = children ?P v" using P2 pS5 by (simp add: UT)
  have lsS5S3: "lsuc S5 = lsuc S3"
  proof -
    have "lsuc S4 = lsuc S3" using succ_vin_loop_fields[OF psP, THEN mp, OF pS3] by (simp add: S4_def)
    moreover have "lsuc S5 = lsuc S4" using succ_vout_loop_fields[OF psP, THEN mp, OF pS4] by (simp add: S5_def)
    ultimately show ?thesis by simp
  qed
  have rawS2: "lsuc S2 = (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. lsuc move_S1 y = j) (follow ?P j)) then lsuc move_S1 p else lsuc move_S1 x)"
    using last_vin_loop_lsuc[OF psP, THEN mp, OF pmv] by (simp add: S2_def)
  have lsS2: "lsuc S2 = (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. lsuc S0 y = j) (follow (prnt S0) j)) then lsuc S0 p else lsuc S0 x)"
    unfolding rawS2 lmv fj by (rule refl)
  have lmvp: "lsuc move_S1 p = lsuc S0 p" by (simp add: lmv)
  have lmvjn: "lsuc move_S1 jn = lsuc S0 jn" by (simp add: lmv)
  have lvoutval: "\<And>stp gv sv. lsuc (last_vout_loop S2 (the (prnt S0 p)) stp gv sv) = (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. Some y \<noteq> stp \<and> lsuc S2 y = gv) (follow ?P (the (prnt S0 p)))) then sv else lsuc S2 x)"
    using last_vout_loop_lsuc[OF psP, THEN mp, OF pS2] by simp
  have lsS3_off: "\<And>u. u \<notin> set (follow (prnt S0) vo) \<Longrightarrow> lsuc S3 u = lsuc S2 u"
  proof -
    fix u assume uout: "u \<notin> set (follow (prnt S0) vo)"
    have unot: "\<And>stp gv. u \<notin> set (takeWhile (\<lambda>y. Some y \<noteq> stp \<and> lsuc S2 y = gv) (follow ?P (the (prnt S0 p))))"
      using uout voeq fvo by (metis set_takeWhileD)
    show "lsuc S3 u = lsuc S2 u"
    proof (cases "jn \<noteq> the (rvth S0 p) \<and> j \<noteq> the (rvth S0 p)")
      case True
      have "S3 = last_vout_loop S2 (the (prnt S0 p)) (if lsuc move_S1 jn = j then Some jn else None) (lsuc S0 p) (the (rvth S0 p))"
        unfolding S3_def by (rule if_P[OF True])
      thus ?thesis using lvoutval[of "if lsuc move_S1 jn = j then Some jn else None" "lsuc S0 p" "the (rvth S0 p)"] unot by simp
    next
      case c1: False
      have "S3 = (if lsuc move_S1 p \<noteq> lsuc S0 p then last_vout_loop S2 (the (prnt S0 p)) (if lsuc move_S1 jn = j then Some jn else None) (lsuc S0 p) (lsuc move_S1 p) else S2)"
        unfolding S3_def by (rule if_not_P[OF c1])
      also have "\<dots> = S2" using lmvp by simp
      finally show ?thesis by simp
    qed
  qed
  have Gs: "\<And>x y. (thrd S0 x = Some y) = (rvth S0 y = Some x)" using arb unfolding arb_invar_def by auto
  have succ_notin_block: "\<And>x w. thrd S0 x = Some w \<Longrightarrow> x \<notin> set (block S0 p) \<Longrightarrow> x \<noteq> the (rvth S0 p) \<Longrightarrow> w \<notin> set (block S0 p)"
  proof -
    fix x w assume tx: "thrd S0 x = Some w" and xnb: "x \<notin> set (block S0 p)" and xnor: "x \<noteq> the (rvth S0 p)"
    show "w \<notin> set (block S0 p)"
    proof
      assume wb: "w \<in> set (block S0 p)"
      obtain t where tlen: "t < length (block S0 p)" and at: "block S0 p ! t = w" using wb by (meson in_set_conv_nth)
      show False
      proof (cases t)
        case 0
        have "block S0 p ! 0 = p" using block_props(5)[OF arb pV] block_props(2)[OF arb pV] by (simp add: hd_conv_nth)
        hence "w = p" using at 0 by simp
        hence "rvth S0 p = Some x" using tx Gs by simp
        hence "x = the (rvth S0 p)" by simp
        thus False using xnor by simp
      next
        case (Suc t')
        have "Suc t' < length (block S0 p)" using tlen Suc by simp
        hence "thrd S0 (block S0 p ! t') = Some (block S0 p ! Suc t')" by (rule block_p_link)
        hence "thrd S0 (block S0 p ! t') = Some w" using at Suc by simp
        hence "rvth S0 w = Some (block S0 p ! t')" using Gs by simp
        moreover have "rvth S0 w = Some x" using tx Gs by simp
        ultimately have "x = block S0 p ! t'" by simp
        moreover have "block S0 p ! t' \<in> set (block S0 p)" using tlen Suc by (metis Suc_lessD nth_mem)
        ultimately show False using xnb by simp
      qed
    qed
  qed
  have rvpV: "dom (rvth S0) = V - {r}" using arb unfolding arb_invar_def by simp
  have rvp: "rvth S0 p = Some (the (rvth S0 p))" using rvpV pV pne_r by (metis DiffI domD option.sel singletonD)
  have thd_or_p: "thrd S0 (the (rvth S0 p)) = Some p" using rvp Gs by simp
  have pst: "parent_spec (thrd S0)" using arb unfolding arb_invar_def by simp
  have oll_bp: "lsuc S0 p \<in> set (block S0 p)" using block_props(3)[OF arb pV] block_props(2)[OF arb pV] by (metis last_in_set)
  have move_untouched_exit: "\<And>u. u \<in> V \<Longrightarrow> lsuc S0 u \<notin> set (block S0 p) \<Longrightarrow> lsuc S0 u \<noteq> j \<Longrightarrow> thrd move_S1 (lsuc S0 u) = None \<or> the (thrd move_S1 (lsuc S0 u)) \<notin> children (prnt S0) u \<union> set (block S0 p)"
  proof -
    fix u assume uV: "u \<in> V" and lsnb: "lsuc S0 u \<notin> set (block S0 p)" and lsj: "lsuc S0 u \<noteq> j"
    have lsne_ol: "lsuc S0 u \<noteq> lsuc S0 p" using lsnb oll_bp by auto
    show "thrd move_S1 (lsuc S0 u) = None \<or> the (thrd move_S1 (lsuc S0 u)) \<notin> children (prnt S0) u \<union> set (block S0 p)"
    proof (cases "lsuc S0 u = the (rvth S0 p)")
      case False
      have tm: "thrd move_S1 (lsuc S0 u) = thrd S0 (lsuc S0 u)" by (rule move_succ_off[OF False lsj lsne_ol])
      have e1: "thrd S0 (lsuc S0 u) = None \<or> the (thrd S0 (lsuc S0 u)) \<notin> children (prnt S0) u" using s0_exit[OF uV] by auto
      have e2: "thrd S0 (lsuc S0 u) = None \<or> the (thrd S0 (lsuc S0 u)) \<notin> set (block S0 p)"
        using succ_notin_block[of "lsuc S0 u"] lsnb False by (cases "thrd S0 (lsuc S0 u)") auto
      show ?thesis using tm e1 e2 by (cases "thrd S0 (lsuc S0 u)") auto
    next
      case True
      have g: "thrd S0 j \<noteq> Some p"
      proof
        assume "thrd S0 j = Some p"
        hence "rvth S0 p = Some j" using Gs by simp
        hence "the (rvth S0 p) = j" by simp
        thus False using True lsj by simp
      qed
      have or_ne_ol: "the (rvth S0 p) \<noteq> lsuc S0 p" using lsne_ol True by simp
      have tm: "thrd move_S1 (lsuc S0 u) = thrd S0 (lsuc S0 p)" using move_thrd_splice[OF g] True old_rev_ne_j[OF g] or_ne_ol by simp
      show ?thesis
      proof (cases "thrd S0 (lsuc S0 p)")
        case None thus ?thesis using tm by simp
      next
        case (Some w)
        have fu: "follow (thrd S0) u = block S0 u @ follow (thrd S0) p"
          using block_props(1)[OF arb uV] True thd_or_p by simp
        have fp: "follow (thrd S0) p = block S0 p @ follow (thrd S0) w" using block_props(1)[OF arb pV] Some by simp
        have win: "w \<in> set (follow (thrd S0) w)" using follow_hd_ps[OF pst, of w] follow_ne_ps[OF pst, of w] by (metis hd_in_set)
        have fud: "follow (thrd S0) u = block S0 u @ block S0 p @ follow (thrd S0) w" using fu fp by simp
        have "distinct (follow (thrd S0) u)" by (rule follow_distinct_ps[OF pst])
        hence "w \<notin> set (block S0 u) \<and> w \<notin> set (block S0 p)" using fud win by (auto simp add: distinct_append)
        hence "w \<notin> children (prnt S0) u \<and> w \<notin> set (block S0 p)" using block_props(4)[OF arb uV] by simp
        thus ?thesis using tm Some by auto
      qed
    qed
  qed
  have INiff: "lsuc S0 v = j \<Longrightarrow> v \<in> set (takeWhile (\<lambda>y. lsuc S0 y = j) (follow (prnt S0) j))"
  proof -
    assume lvj: "lsuc S0 v = j"
    have jbl: "j \<in> set (block S0 v)" using block_props(3)[OF arb vV] block_props(2)[OF arb vV] lvj by (metis last_in_set)
    have "j \<in> children (prnt S0) v" using jbl block_props(4)[OF arb vV] by simp
    hence vfj: "v \<in> set (follow (prnt S0) j)" unfolding children_def by simp
    obtain G H where GH: "follow (prnt S0) j = G @ v # H" using vfj by (meson split_list)
    have allG: "\<forall>y \<in> set G. lsuc S0 y = j"
    proof
      fix y assume yG: "y \<in> set G"
      then obtain G1 G2 where G12: "G = G1 @ y # G2" by (meson split_list)
      have fj2: "follow (prnt S0) j = G1 @ y # (G2 @ v # H)" using GH G12 by simp
      have "follow (prnt S0) y = y # (G2 @ v # H)" using follow_append_ps[OF ppt] fj2 by auto
      hence vfy: "v \<in> set (follow (prnt S0) y)" by simp
      have yfj: "y \<in> set (follow (prnt S0) j)" using GH G12 by simp
      have yV: "y \<in> V" using follow_subset_V[OF rinv0 jV] yfj by auto
      show "lsuc S0 y = j" using spine_lemma[OF lvj vV yV yfj vfy] by auto
    qed
    have "takeWhile (\<lambda>y. lsuc S0 y = j) (follow (prnt S0) j) = G @ takeWhile (\<lambda>y. lsuc S0 y = j) (v # H)"
      using GH allG by (simp add: takeWhile_append2)
    thus ?thesis using lvj by simp
  qed
  have fpvo: "follow (prnt S0) p = p # follow (prnt S0) vo" using vo by (subst follow_ps_simps[OF ppt]) simp
  have lsuc_notin_untouched: "v \<notin> set (block S0 p) \<Longrightarrow> v \<notin> set (follow (prnt S0) vo) \<Longrightarrow> lsuc S0 v \<notin> set (block S0 p)"
  proof -
    assume notBlk: "v \<notin> set (block S0 p)" and notOUT: "v \<notin> set (follow (prnt S0) vo)"
    show "lsuc S0 v \<notin> set (block S0 p)"
    proof
      assume lb: "lsuc S0 v \<in> set (block S0 p)"
      have pfl: "p \<in> set (follow (prnt S0) (lsuc S0 v))" using lb block_props(4)[OF arb pV] unfolding children_def by simp
      have lbv: "lsuc S0 v \<in> set (block S0 v)" using block_props(3)[OF arb vV] block_props(2)[OF arb vV] by (metis last_in_set)
      have vfl: "v \<in> set (follow (prnt S0) (lsuc S0 v))" using lbv block_props(4)[OF arb vV] unfolding children_def by simp
      obtain A B where AB: "follow (prnt S0) (lsuc S0 v) = A @ v # B" using vfl by (meson split_list)
      have fv: "follow (prnt S0) v = v # B" using follow_append_ps[OF ppt AB] by auto
      from pfl AB have "p \<in> set A \<or> p \<in> set (v # B)" by auto
      thus False
      proof
        assume "p \<in> set (v # B)"
        hence "p \<in> set (follow (prnt S0) v)" using fv by simp
        hence "v \<in> children (prnt S0) p" unfolding children_def by simp
        hence "v \<in> set (block S0 p)" using block_props(4)[OF arb pV] by simp
        thus False using notBlk by simp
      next
        assume "p \<in> set A"
        then obtain A1 A2 where A12: "A = A1 @ p # A2" by (meson split_list)
        have "follow (prnt S0) (lsuc S0 v) = A1 @ p # (A2 @ v # B)" using AB A12 by simp
        hence "follow (prnt S0) p = p # (A2 @ v # B)" using follow_append_ps[OF ppt] by auto
        hence vfp: "v \<in> set (follow (prnt S0) p)" by simp
        have "v \<noteq> p" using notBlk p_in_block_ip by auto
        hence "v \<in> set (follow (prnt S0) vo)" using vfp fpvo by simp
        thus False using notOUT by simp
      qed
    qed
  qed
  have jnV: "jn \<in> V" using follow_subset_V[OF rinv0 jV] jnj by auto
  have jnvo: "jn \<in> set (follow (prnt S0) vo)" using jnp pjn fpvo by simp
  have pnvo: "p \<notin> set (follow (prnt S0) vo)" using follow_distinct_ps[OF ppt, of p] fpvo by simp
  have blk_res: "v \<in> set (block S0 p) \<Longrightarrow> lsuc S5 v \<in> set pre \<and> (thrd S5 (lsuc S5 v) = None \<or> the (thrd S5 (lsuc S5 v)) \<notin> set pre)"
  proof -
    assume Blk: "v \<in> set (block S0 p)"
    have vnvo: "v \<notin> set (follow (prnt S0) vo)" using block_p_notin_follow_vout[OF Blk] voeq by simp
    have vnj: "v \<notin> set (follow (prnt S0) j)" using block_p_notin_follow_j[OF Blk] by auto
    have vnIN: "v \<notin> set (takeWhile (\<lambda>y. lsuc S0 y = j) (follow (prnt S0) j))" using vnj set_takeWhileD by fastforce
    have val: "lsuc S5 v = lsuc S0 v" using lsS5S3 lsS3_off[OF vnvo] lsS2 vnIN by simp
    have chv: "children ?P v = children (prnt S0) v" using children_ip_inblock[OF Blk] by auto
    have id: "lsuc S0 v \<in> set pre"
    proof -
      have "lsuc S0 v \<in> set (block S0 v)" using block_props(3)[OF arb vV] block_props(2)[OF arb vV] by (metis last_in_set)
      hence "lsuc S0 v \<in> children (prnt S0) v" using block_props(4)[OF arb vV] by simp
      thus ?thesis using setpre chv by simp
    qed
    have ex: "thrd move_S1 (lsuc S0 v) = None \<or> the (thrd move_S1 (lsuc S0 v)) \<notin> children (prnt S0) v" using move_block_exit[OF vV Blk] by auto
    have ie: "thrd S5 (lsuc S5 v) = None \<or> the (thrd S5 (lsuc S5 v)) \<notin> set pre" using ex val thS5 setpre chv by simp
    show ?thesis using val id ie by simp
  qed
  have chP_sub: "children ?P v \<subseteq> children (prnt S0) v \<union> set (block S0 p)"
    using children_ip_decomp[of v] by auto
  have chP_decomp_notblk: "lsuc S0 v \<in> children (prnt S0) v \<Longrightarrow> lsuc S0 v \<notin> set (block S0 p) \<Longrightarrow> lsuc S0 v \<in> children ?P v"
    using children_ip_decomp[of v] by auto
  have notout_res: "v \<notin> set (block S0 p) \<Longrightarrow> v \<notin> set (follow (prnt S0) vo) \<Longrightarrow> lsuc S5 v \<in> set pre \<and> (thrd S5 (lsuc S5 v) = None \<or> the (thrd S5 (lsuc S5 v)) \<notin> set pre)"
  proof -
    assume notBlk: "v \<notin> set (block S0 p)" and notOUT: "v \<notin> set (follow (prnt S0) vo)"
    have val0: "lsuc S5 v = lsuc S2 v" using lsS5S3 lsS3_off[OF notOUT] by simp
    show ?thesis
    proof (cases "v \<in> set (takeWhile (\<lambda>y. lsuc S0 y = j) (follow (prnt S0) j))")
      case IN: True
      have vj: "v \<in> set (follow (prnt S0) j)" using IN set_takeWhileD by fastforce
      have lvj: "lsuc S0 v = j" using IN set_takeWhileD by fastforce
      have val: "lsuc S5 v = lsuc S0 p" using val0 lsS2 IN by simp
      have chj: "children ?P v = children (prnt S0) v \<union> set (block S0 p)" using children_ip_jpath[OF vj] by auto
      have id: "lsuc S0 p \<in> set pre"
      proof -
        have "lsuc S0 p \<in> set (block S0 p)" using oll_bp by auto
        thus ?thesis using setpre chj by simp
      qed
      have ex: "thrd move_S1 (lsuc S0 p) = None \<or> the (thrd move_S1 (lsuc S0 p)) \<notin> children (prnt S0) v \<union> set (block S0 p)" using move_IN_exit[OF vV vj lvj] by auto
      have ie: "thrd S5 (lsuc S5 v) = None \<or> the (thrd S5 (lsuc S5 v)) \<notin> set pre" using ex val thS5 setpre chj by simp
      show ?thesis using val id ie by simp
    next
      case notIN: False
      have val: "lsuc S5 v = lsuc S0 v" using val0 lsS2 notIN by simp
      have lsj: "lsuc S0 v \<noteq> j" using notIN INiff by auto
      have lsnb: "lsuc S0 v \<notin> set (block S0 p)" using lsuc_notin_untouched notBlk notOUT by simp
      have lsc: "lsuc S0 v \<in> children (prnt S0) v"
      proof -
        have "lsuc S0 v \<in> set (block S0 v)" using block_props(3)[OF arb vV] block_props(2)[OF arb vV] by (metis last_in_set)
        thus ?thesis using block_props(4)[OF arb vV] by simp
      qed
      have id: "lsuc S0 v \<in> set pre" using chP_decomp_notblk[OF lsc lsnb] setpre by simp
      have ex: "thrd move_S1 (lsuc S0 v) = None \<or> the (thrd move_S1 (lsuc S0 v)) \<notin> children (prnt S0) v \<union> set (block S0 p)" using move_untouched_exit[OF vV lsnb lsj] by auto
      have ie: "thrd S5 (lsuc S5 v) = None \<or> the (thrd S5 (lsuc S5 v)) \<notin> set pre" using ex val thS5 setpre chP_sub by auto
      show ?thesis using val id ie by simp
    qed
  qed
  have in_case: "v \<in> set (follow (prnt S0) j) \<Longrightarrow> lsuc S0 v = j \<Longrightarrow> lsuc S5 v = lsuc S0 p \<Longrightarrow> lsuc S5 v \<in> set pre \<and> (thrd S5 (lsuc S5 v) = None \<or> the (thrd S5 (lsuc S5 v)) \<notin> set pre)"
  proof -
    assume vj: "v \<in> set (follow (prnt S0) j)" and lvj: "lsuc S0 v = j" and val: "lsuc S5 v = lsuc S0 p"
    have chj: "children ?P v = children (prnt S0) v \<union> set (block S0 p)" using children_ip_jpath[OF vj] by auto
    have id: "lsuc S0 p \<in> set pre" using oll_bp setpre chj by simp
    have ex: "thrd move_S1 (lsuc S0 p) = None \<or> the (thrd move_S1 (lsuc S0 p)) \<notin> children (prnt S0) v \<union> set (block S0 p)" using move_IN_exit[OF vV vj lvj] by auto
    have ie: "thrd S5 (lsuc S5 v) = None \<or> the (thrd S5 (lsuc S5 v)) \<notin> set pre" using ex val thS5 setpre chj by simp
    show ?thesis using val id ie by simp
  qed
  have unt_case: "lsuc S0 v \<notin> set (block S0 p) \<Longrightarrow> lsuc S0 v \<noteq> j \<Longrightarrow> lsuc S5 v = lsuc S0 v \<Longrightarrow> lsuc S5 v \<in> set pre \<and> (thrd S5 (lsuc S5 v) = None \<or> the (thrd S5 (lsuc S5 v)) \<notin> set pre)"
  proof -
    assume lsnb: "lsuc S0 v \<notin> set (block S0 p)" and lsj: "lsuc S0 v \<noteq> j" and val: "lsuc S5 v = lsuc S0 v"
    have lsc: "lsuc S0 v \<in> children (prnt S0) v"
    proof -
      have "lsuc S0 v \<in> set (block S0 v)" using block_props(3)[OF arb vV] block_props(2)[OF arb vV] by (metis last_in_set)
      thus ?thesis using block_props(4)[OF arb vV] by simp
    qed
    have id: "lsuc S0 v \<in> set pre" using chP_decomp_notblk[OF lsc lsnb] setpre by simp
    have ex: "thrd move_S1 (lsuc S0 v) = None \<or> the (thrd move_S1 (lsuc S0 v)) \<notin> children (prnt S0) v \<union> set (block S0 p)" using move_untouched_exit[OF vV lsnb lsj] by auto
    have ie: "thrd S5 (lsuc S5 v) = None \<or> the (thrd S5 (lsuc S5 v)) \<notin> set pre" using ex val thS5 setpre chP_sub by auto
    show ?thesis using val id ie by simp
  qed
  have chP_gen: "\<And>x. x \<in> children (prnt S0) v \<Longrightarrow> x \<notin> set (block S0 p) \<Longrightarrow> x \<in> children ?P v"
    using children_ip_decomp[of v] by auto
  have or_nb: "the (rvth S0 p) \<notin> set (block S0 p)" by (rule old_rev_notin_block_p)
  have or_ne_ol2: "the (rvth S0 p) \<noteq> lsuc S0 p" using or_nb oll_bp by auto
  have out_case_u: "v \<in> set (follow (prnt S0) p) \<Longrightarrow> p \<noteq> v \<Longrightarrow> the (rvth S0 p) \<noteq> j \<Longrightarrow> lsuc S0 v = lsuc S0 p \<Longrightarrow> lsuc S5 v = the (rvth S0 p) \<Longrightarrow> lsuc S5 v \<in> set pre \<and> (thrd S5 (lsuc S5 v) = None \<or> the (thrd S5 (lsuc S5 v)) \<notin> set pre)"
  proof -
    assume vfp: "v \<in> set (follow (prnt S0) p)" and vnep: "p \<noteq> v" and orne: "the (rvth S0 p) \<noteq> j"
       and lvp: "lsuc S0 v = lsuc S0 p" and val: "lsuc S5 v = the (rvth S0 p)"
    have orbv: "the (rvth S0 p) \<in> children (prnt S0) v"
      using old_rev_in_block_anc[OF vV vfp vnep] block_props(4)[OF arb vV] by simp
    have id: "the (rvth S0 p) \<in> set pre" using chP_gen[OF orbv or_nb] setpre by simp
    have g: "thrd S0 j \<noteq> Some p"
    proof
      assume "thrd S0 j = Some p"
      hence "rvth S0 p = Some j" using Gs by simp
      thus False using rvp orne by simp
    qed
    have tm: "thrd move_S1 (the (rvth S0 p)) = thrd S0 (lsuc S0 p)"
      using move_thrd_splice[OF g] orne or_ne_ol2 by simp
    have e1: "thrd S0 (lsuc S0 p) = None \<or> the (thrd S0 (lsuc S0 p)) \<notin> children (prnt S0) v" using s0_exit[OF vV] lvp by simp
    have e2: "thrd S0 (lsuc S0 p) = None \<or> the (thrd S0 (lsuc S0 p)) \<notin> set (block S0 p)"
      using s0_exit[OF pV] block_props(4)[OF arb pV] by simp
    have ie: "thrd S5 (lsuc S5 v) = None \<or> the (thrd S5 (lsuc S5 v)) \<notin> set pre"
      using tm e1 e2 val thS5 setpre chP_sub by (cases "thrd S0 (lsuc S0 p)") auto
    show ?thesis using val id ie by simp
  qed
  have out_case_lsxk: "v \<in> set (follow (prnt S0) j) \<Longrightarrow> the (rvth S0 p) = j \<Longrightarrow> lsuc S0 v = lsuc S0 p \<Longrightarrow> lsuc S5 v = lsuc S0 p \<Longrightarrow> lsuc S5 v \<in> set pre \<and> (thrd S5 (lsuc S5 v) = None \<or> the (thrd S5 (lsuc S5 v)) \<notin> set pre)"
  proof -
    assume vj: "v \<in> set (follow (prnt S0) j)" and jorv: "the (rvth S0 p) = j" and lvp: "lsuc S0 v = lsuc S0 p" and val: "lsuc S5 v = lsuc S0 p"
    have g: "thrd S0 j = Some p" using rvp jorv Gs by simp
    have tm: "thrd move_S1 = thrd S0" by (rule move_thrd_shortcut[OF g])
    have chj: "children ?P v = children (prnt S0) v \<union> set (block S0 p)" using children_ip_jpath[OF vj] by auto
    have id: "lsuc S0 p \<in> set pre" using oll_bp setpre chj by simp
    have e1: "thrd S0 (lsuc S0 p) = None \<or> the (thrd S0 (lsuc S0 p)) \<notin> children (prnt S0) v" using s0_exit[OF vV] lvp by simp
    have e2: "thrd S0 (lsuc S0 p) = None \<or> the (thrd S0 (lsuc S0 p)) \<notin> set (block S0 p)"
      using s0_exit[OF pV] block_props(4)[OF arb pV] by simp
    have ie: "thrd S5 (lsuc S5 v) = None \<or> the (thrd S5 (lsuc S5 v)) \<notin> set pre"
      using e1 e2 val thS5 tm setpre chj by (cases "thrd S0 (lsuc S0 p)") auto
    show ?thesis using val id ie by simp
  qed
  have lst: "last (follow (prnt S0) p) = last (follow (prnt S0) j)" using last_follow_root[OF rinv0 pV] last_follow_root[OF rinv0 jV] by simp
  have lpnej: "lsuc S0 p \<noteq> j" using oll_bp j_notin_block_p by auto
  have p_anc_lsp: "p \<in> set (follow (prnt S0) (lsuc S0 p))" using oll_bp block_props(4)[OF arb pV] unfolding children_def by simp
  have outset_lsuc_p: "v \<in> set (takeWhile (\<lambda>y. Some y \<noteq> (if lsuc move_S1 jn = j then Some jn else None) \<and> lsuc S2 y = lsuc S0 p) (follow ?P vo)) \<Longrightarrow> lsuc S0 v = lsuc S0 p"
  proof -
    assume vout: "v \<in> set (takeWhile (\<lambda>y. Some y \<noteq> (if lsuc move_S1 jn = j then Some jn else None) \<and> lsuc S2 y = lsuc S0 p) (follow ?P vo))"
    have s2v: "lsuc S2 v = lsuc S0 p" using set_takeWhileD[OF vout] by simp
    have vin_vout0: "v \<in> set (follow (prnt S0) vo)" using set_takeWhileD[OF vout] fvo by simp
    have vfp: "v \<in> set (follow (prnt S0) p)" using vin_vout0 fpvo by simp
    have vnIN: "v \<notin> set (takeWhile (\<lambda>y. lsuc S0 y = j) (follow (prnt S0) j))"
    proof
      assume vIN: "v \<in> set (takeWhile (\<lambda>y. lsuc S0 y = j) (follow (prnt S0) j))"
      have vfj: "v \<in> set (follow (prnt S0) j)" using set_takeWhileD[OF vIN] by simp
      have lsvj0: "lsuc S0 v = j" using set_takeWhileD[OF vIN] by simp
      have vfjn: "v \<in> set (follow (prnt S0) jn)" using join_of_first[OF ppt lst vfp vfj] jneq by simp
      have "lsuc S0 jn = j" using spine_lemma[OF lsvj0 vV jnV jnj vfjn] by auto
      hence stpj: "lsuc move_S1 jn = j" using lmvjn by simp
      obtain A B where AB: "follow (prnt S0) vo = A @ jn # B" using jnvo by (meson split_list)
      have fjn2: "follow (prnt S0) jn = jn # B" using follow_append_ps[OF ppt] AB by auto
      have vne_jn: "v \<noteq> jn" using set_takeWhileD[OF vout] stpj by auto
      have vB: "v \<in> set B" using vfjn fjn2 vne_jn by simp
      have Pjn: "\<not> (Some jn \<noteq> (if lsuc move_S1 jn = j then Some jn else None) \<and> lsuc S2 jn = lsuc S0 p)" using stpj by simp
      have fvout_np: "follow ?P vo = A @ jn # B" using AB fvo by simp
      have sub: "set (takeWhile (\<lambda>y. Some y \<noteq> (if lsuc move_S1 jn = j then Some jn else None) \<and> lsuc S2 y = lsuc S0 p) (A @ jn # B)) \<subseteq> set A"
      proof (cases "\<forall>a\<in>set A. Some a \<noteq> (if lsuc move_S1 jn = j then Some jn else None) \<and> lsuc S2 a = lsuc S0 p")
        case True
        have "takeWhile (\<lambda>y. Some y \<noteq> (if lsuc move_S1 jn = j then Some jn else None) \<and> lsuc S2 y = lsuc S0 p) (A @ jn # B) = A @ takeWhile (\<lambda>y. Some y \<noteq> (if lsuc move_S1 jn = j then Some jn else None) \<and> lsuc S2 y = lsuc S0 p) (jn # B)"
          using True by (simp add: takeWhile_append2)
        also have "takeWhile (\<lambda>y. Some y \<noteq> (if lsuc move_S1 jn = j then Some jn else None) \<and> lsuc S2 y = lsuc S0 p) (jn # B) = []" using Pjn by simp
        finally show ?thesis by simp
      next
        case False
        then obtain a where "a \<in> set A" and "\<not> (Some a \<noteq> (if lsuc move_S1 jn = j then Some jn else None) \<and> lsuc S2 a = lsuc S0 p)" by blast
        hence "takeWhile (\<lambda>y. Some y \<noteq> (if lsuc move_S1 jn = j then Some jn else None) \<and> lsuc S2 y = lsuc S0 p) (A @ jn # B) = takeWhile (\<lambda>y. Some y \<noteq> (if lsuc move_S1 jn = j then Some jn else None) \<and> lsuc S2 y = lsuc S0 p) A"
          by (simp add: takeWhile_append1)
        thus ?thesis by (auto dest: set_takeWhileD)
      qed
      have "v \<in> set A" using vout fvout_np sub by auto
      moreover have "distinct (A @ jn # B)" using AB follow_distinct_ps[OF ppt, of vo] by simp
      ultimately show False using vB by auto
    qed
    have "lsuc S2 v = lsuc S0 v" using vnIN lsS2 by simp
    thus "lsuc S0 v = lsuc S0 p" using s2v by simp
  qed
  have voinp: "vo \<in> set (follow (prnt S0) p)" using fpvo follow_hd_ps[OF ppt, of vo] follow_ne_ps[OF ppt, of vo] by (metis hd_in_set list.set_intros(2))
  have voV: "vo \<in> V" using follow_subset_V[OF rinv0 pV] voinp by auto
  have outset_iff: "v \<in> set (follow (prnt S0) vo) \<Longrightarrow> lsuc S0 v = lsuc S0 p \<Longrightarrow> v \<in> set (takeWhile (\<lambda>y. Some y \<noteq> (if lsuc move_S1 jn = j then Some jn else None) \<and> lsuc S2 y = lsuc S0 p) (follow ?P vo))"
  proof -
    assume vfvo: "v \<in> set (follow (prnt S0) vo)" and lvp: "lsuc S0 v = lsuc S0 p"
    obtain G H where GH: "follow (prnt S0) vo = G @ v # H" using vfvo by (meson split_list)
    have Pv: "Some v \<noteq> (if lsuc move_S1 jn = j then Some jn else None) \<and> lsuc S2 v = lsuc S0 p"
    proof -
      have "Some v \<noteq> (if lsuc move_S1 jn = j then Some jn else None)"
      proof (cases "lsuc move_S1 jn = j")
        case True
        have "lsuc S0 jn = j" using True lmvjn by simp
        hence "v \<noteq> jn" using lvp lpnej by auto
        thus ?thesis using True by simp
      next
        case False thus ?thesis by simp
      qed
      moreover have "lsuc S2 v = lsuc S0 p"
      proof (cases "v \<in> set (takeWhile (\<lambda>z. lsuc S0 z = j) (follow (prnt S0) j))")
        case True
        hence "lsuc S0 v = j" using set_takeWhileD by (metis (mono_tags, lifting))
        thus ?thesis using lvp lpnej by simp
      next
        case False thus ?thesis using lsS2 lvp by simp
      qed
      ultimately show ?thesis by simp
    qed
    have allG: "\<forall>y \<in> set G. Some y \<noteq> (if lsuc move_S1 jn = j then Some jn else None) \<and> lsuc S2 y = lsuc S0 p"
    proof
      fix y assume yG: "y \<in> set G"
      then obtain G1 G2 where G12: "G = G1 @ y # G2" by (meson split_list)
      have fj2: "follow (prnt S0) vo = G1 @ y # (G2 @ v # H)" using GH G12 by simp
      have "follow (prnt S0) y = y # (G2 @ v # H)" using follow_append_ps[OF ppt] fj2 by auto
      hence vfy: "v \<in> set (follow (prnt S0) y)" by simp
      have yfvo: "y \<in> set (follow (prnt S0) vo)" using GH G12 by simp
      have yV: "y \<in> V" using follow_subset_V[OF rinv0 voV] yfvo by auto
      have yfp: "y \<in> set (follow (prnt S0) p)" using yfvo fpvo by simp
      have yflsp: "y \<in> set (follow (prnt S0) (lsuc S0 p))" using follow_trans[OF ppt p_anc_lsp yfp] by auto
      have lsy: "lsuc S0 y = lsuc S0 p" using spine_lemma[OF lvp vV yV yflsp vfy] by auto
      have "Some y \<noteq> (if lsuc move_S1 jn = j then Some jn else None)"
      proof (cases "lsuc move_S1 jn = j")
        case True
        have "lsuc S0 jn = j" using True lmvjn by simp
        hence "y \<noteq> jn" using lsy lpnej by auto
        thus ?thesis using True by simp
      next
        case False thus ?thesis by simp
      qed
      moreover have "lsuc S2 y = lsuc S0 p"
      proof (cases "y \<in> set (takeWhile (\<lambda>z. lsuc S0 z = j) (follow (prnt S0) j))")
        case True
        hence "lsuc S0 y = j" using set_takeWhileD by (metis (mono_tags, lifting))
        thus ?thesis using lsy lpnej by simp
      next
        case False thus ?thesis using lsS2 lsy by simp
      qed
      ultimately show "Some y \<noteq> (if lsuc move_S1 jn = j then Some jn else None) \<and> lsuc S2 y = lsuc S0 p" by simp
    qed
    have "takeWhile (\<lambda>y. Some y \<noteq> (if lsuc move_S1 jn = j then Some jn else None) \<and> lsuc S2 y = lsuc S0 p) (follow (prnt S0) vo) = G @ takeWhile (\<lambda>y. Some y \<noteq> (if lsuc move_S1 jn = j then Some jn else None) \<and> lsuc S2 y = lsuc S0 p) (v # H)"
      using GH allG by (simp add: takeWhile_append2)
    hence "v \<in> set (takeWhile (\<lambda>y. Some y \<noteq> (if lsuc move_S1 jn = j then Some jn else None) \<and> lsuc S2 y = lsuc S0 p) (follow (prnt S0) vo))" using Pv by simp
    thus ?thesis using fvo by simp
  qed
  have orv_jn_vac: "the (rvth S0 p) = jn \<Longrightarrow> j \<noteq> jn \<Longrightarrow> lsuc S0 v = lsuc S0 p \<Longrightarrow> v \<in> set (follow (prnt S0) p) \<Longrightarrow> p \<noteq> v \<Longrightarrow> False"
  proof -
    assume orjn: "the (rvth S0 p) = jn" and jnej: "j \<noteq> jn" and lvp: "lsuc S0 v = lsuc S0 p"
       and vp: "v \<in> set (follow (prnt S0) p)" and vnep: "p \<noteq> v"
    have "rvth S0 p = Some jn" using rvp orjn by simp
    hence thjnp: "thrd S0 jn = Some p" using Gs by simp
    have orblk: "jn \<in> set (block S0 v)" using old_rev_in_block_anc[OF vV vp vnep] orjn by simp
    hence "jn \<in> children (prnt S0) v" using block_props(4)[OF arb vV] by simp
    hence vfjn: "v \<in> set (follow (prnt S0) jn)" unfolding children_def by simp
    have jnflsp: "jn \<in> set (follow (prnt S0) (lsuc S0 p))" using follow_trans[OF ppt p_anc_lsp jnp] by auto
    have lsjn: "lsuc S0 jn = lsuc S0 p" using spine_lemma[OF lvp vV jnV jnflsp vfjn] by auto
    have jnnb: "jn \<notin> set (block S0 p)"
    proof
      assume "jn \<in> set (block S0 p)"
      hence "jn \<in> children (prnt S0) p" using block_props(4)[OF arb pV] by simp
      hence "p \<in> set (follow (prnt S0) jn)" unfolding children_def by simp
      hence "jn = p" using ancestor_antisym[OF ppt jnp] by simp
      thus False using pjn by simp
    qed
    have jnne: "jn \<noteq> lsuc S0 p" using jnnb oll_bp by auto
    have fjn: "follow (thrd S0) jn = jn # follow (thrd S0) p" using thjnp by (subst follow_ps_simps[OF pst]) simp
    have bjn: "block S0 jn = jn # block S0 p" using fjn lsjn jnne by (simp add: block_def)
    have "j \<in> children (prnt S0) jn" using jnj unfolding children_def by simp
    hence "j \<in> set (block S0 jn)" using block_props(4)[OF arb jnV] by simp
    hence "j \<in> insert jn (set (block S0 p))" using bjn by simp
    thus False using jnej j_notin_block_p by simp
  qed
  have route_lsuc2: "lsuc S5 v = lsuc S2 v \<Longrightarrow> (v \<notin> set (takeWhile (\<lambda>y. lsuc S0 y = j) (follow (prnt S0) j)) \<Longrightarrow> lsuc S0 v \<notin> set (block S0 p)) \<Longrightarrow> lsuc S5 v \<in> set pre \<and> (thrd S5 (lsuc S5 v) = None \<or> the (thrd S5 (lsuc S5 v)) \<notin> set pre)"
  proof -
    assume v5': "lsuc S5 v = lsuc S2 v"
       and lsnbH: "v \<notin> set (takeWhile (\<lambda>y. lsuc S0 y = j) (follow (prnt S0) j)) \<Longrightarrow> lsuc S0 v \<notin> set (block S0 p)"
    show ?thesis
    proof (cases "v \<in> set (takeWhile (\<lambda>y. lsuc S0 y = j) (follow (prnt S0) j))")
      case IN: True
      have vj: "v \<in> set (follow (prnt S0) j)" using set_takeWhileD[OF IN] by simp
      have lvj: "lsuc S0 v = j" using set_takeWhileD[OF IN] by simp
      have LL: "lsuc S5 v = lsuc S0 p" using v5' lsS2 IN by simp
      show ?thesis using in_case[OF vj lvj LL] by auto
    next
      case notIN: False
      have vval: "lsuc S5 v = lsuc S0 v" using v5' lsS2 notIN by simp
      have lsj: "lsuc S0 v \<noteq> j" using notIN INiff by auto
      have lsnb: "lsuc S0 v \<notin> set (block S0 p)" using lsnbH notIN by simp
      show ?thesis using unt_case[OF lsnb lsj vval] by auto
    qed
  qed
  have main2: "lsuc S5 v \<in> set pre \<and> (thrd S5 (lsuc S5 v) = None \<or> the (thrd S5 (lsuc S5 v)) \<notin> set pre)"
  proof (cases "v \<in> set (block S0 p)")
    case True thus ?thesis using blk_res by simp
  next
    case notblk: False
    show ?thesis
    proof (cases "v \<in> set (follow (prnt S0) vo)")
      case False thus ?thesis using notout_res[OF notblk] by simp
    next
      case isvout: True
      have vfp: "v \<in> set (follow (prnt S0) p)" using isvout fpvo by simp
      have vnep: "p \<noteq> v" using isvout pnvo by auto
      have lsnb_prov: "v \<notin> set (takeWhile (\<lambda>y. Some y \<noteq> (if lsuc move_S1 jn = j then Some jn else None) \<and> lsuc S2 y = lsuc S0 p) (follow ?P vo)) \<Longrightarrow> lsuc S0 v \<notin> set (block S0 p)"
      proof -
        assume notOUT: "v \<notin> set (takeWhile (\<lambda>y. Some y \<noteq> (if lsuc move_S1 jn = j then Some jn else None) \<and> lsuc S2 y = lsuc S0 p) (follow ?P vo))"
        show "lsuc S0 v \<notin> set (block S0 p)"
        proof
          assume lb: "lsuc S0 v \<in> set (block S0 p)"
          have "lsuc S0 v \<in> children (prnt S0) p" using lb block_props(4)[OF arb pV] by simp
          hence pflv: "p \<in> set (follow (prnt S0) (lsuc S0 v))" unfolding children_def by simp
          have "lsuc S0 v = lsuc S0 p" using spine_lemma[OF refl vV pV pflv vfp] by simp
          hence "v \<in> set (takeWhile (\<lambda>y. Some y \<noteq> (if lsuc move_S1 jn = j then Some jn else None) \<and> lsuc S2 y = lsuc S0 p) (follow ?P vo))" using outset_iff[OF isvout] by simp
          thus False using notOUT by simp
        qed
      qed
      show ?thesis
      proof (cases "jn \<noteq> the (rvth S0 p) \<and> j \<noteq> the (rvth S0 p)")
        case arm1: True
        have orne: "the (rvth S0 p) \<noteq> j" using arm1 by auto
        have S3eq: "S3 = last_vout_loop S2 (the (prnt S0 p)) (if lsuc move_S1 jn = j then Some jn else None) (lsuc S0 p) (the (rvth S0 p))"
          unfolding S3_def by (rule if_P[OF arm1])
        have v5: "lsuc S5 v = (if v \<in> set (takeWhile (\<lambda>y. Some y \<noteq> (if lsuc move_S1 jn = j then Some jn else None) \<and> lsuc S2 y = lsuc S0 p) (follow ?P vo)) then the (rvth S0 p) else lsuc S2 v)"
          using lsS5S3 S3eq lvoutval[of "if lsuc move_S1 jn = j then Some jn else None" "lsuc S0 p" "the (rvth S0 p)"] voeq by simp
        show ?thesis
        proof (cases "v \<in> set (takeWhile (\<lambda>y. Some y \<noteq> (if lsuc move_S1 jn = j then Some jn else None) \<and> lsuc S2 y = lsuc S0 p) (follow ?P vo))")
          case OUT: True
          have lvp: "lsuc S0 v = lsuc S0 p" using outset_lsuc_p[OF OUT] by auto
          have val: "lsuc S5 v = the (rvth S0 p)" using v5 OUT by simp
          show ?thesis using out_case_u[OF vfp vnep orne lvp val] by auto
        next
          case notOUT: False
          have v5': "lsuc S5 v = lsuc S2 v" using v5 notOUT by simp
          show ?thesis using route_lsuc2[OF v5' lsnb_prov[OF notOUT]] by auto
        qed
      next
        case arm23: False
        have "S3 = (if lsuc move_S1 p \<noteq> lsuc S0 p then last_vout_loop S2 (the (prnt S0 p)) (if lsuc move_S1 jn = j then Some jn else None) (lsuc S0 p) (lsuc move_S1 p) else S2)"
          unfolding S3_def by (rule if_not_P[OF arm23])
        also have "\<dots> = S2" using lmvp by simp
        finally have S3S2: "S3 = S2" .
        have v5': "lsuc S5 v = lsuc S2 v" using lsS5S3 S3S2 by simp
        show ?thesis
        proof (cases "v \<in> set (takeWhile (\<lambda>y. lsuc S0 y = j) (follow (prnt S0) j))")
          case IN: True
          have vj: "v \<in> set (follow (prnt S0) j)" using set_takeWhileD[OF IN] by simp
          have lvj: "lsuc S0 v = j" using set_takeWhileD[OF IN] by simp
          have LL: "lsuc S5 v = lsuc S0 p" using v5' lsS2 IN by simp
          show ?thesis using in_case[OF vj lvj LL] by auto
        next
          case notIN: False
          have vval: "lsuc S5 v = lsuc S0 v" using v5' lsS2 notIN by simp
          show ?thesis
          proof (cases "lsuc S0 v \<in> set (block S0 p)")
            case inblk: True
            have "lsuc S0 v \<in> children (prnt S0) p" using inblk block_props(4)[OF arb pV] by simp
            hence pflv: "p \<in> set (follow (prnt S0) (lsuc S0 v))" unfolding children_def by simp
            have lvp: "lsuc S0 v = lsuc S0 p" using spine_lemma[OF refl vV pV pflv vfp] by simp
            have jorv: "the (rvth S0 p) = j"
            proof (rule ccontr)
              assume ne: "the (rvth S0 p) \<noteq> j"
              hence "the (rvth S0 p) = jn" using arm23 by auto
              hence "j \<noteq> jn" using ne by simp
              show False using orv_jn_vac[OF \<open>the (rvth S0 p) = jn\<close> \<open>j \<noteq> jn\<close> lvp vfp vnep] by auto
            qed
            have vfj: "v \<in> set (follow (prnt S0) j)"
            proof -
              have "the (rvth S0 p) \<in> set (block S0 v)" using old_rev_in_block_anc[OF vV vfp vnep] by auto
              hence "j \<in> children (prnt S0) v" using jorv block_props(4)[OF arb vV] by simp
              thus ?thesis unfolding children_def by simp
            qed
            have val: "lsuc S5 v = lsuc S0 p" using vval lvp by simp
            show ?thesis using out_case_lsxk[OF vfj jorv lvp val] by auto
          next
            case notblk2: False
            have lsj: "lsuc S0 v \<noteq> j" using notIN INiff by auto
            show ?thesis using unt_case[OF notblk2 lsj vval] by auto
          qed
        qed
      qed
    qed
  qed
  show ?thesis unfolding UT using succ_exits_is_last[OF psF split conjunct1[OF main2] conjunct2[OF main2]] by auto
qed

text \<open>IP-6 assembly: the full clause J for the @{term "i = p"} branch, from the contiguity half
      @{thm clauseJ_contig_ip} and the pointwise half @{thm lsuc_last_ip} (mirrors @{thm clauseJ_from_lsuc}).\<close>
lemma clauseJ_ip:
  assumes jneq: "jn = join_of (prnt S0) p j" and jnp: "jn \<in> set (follow (prnt S0) p)" and pjn: "p \<noteq> jn" and jnj: "jn \<in> set (follow (prnt S0) j)"
  shows "\<forall>v\<in>V. \<exists>pre. follow (thrd (update_tree S0 p j p jn)) v
           = pre @ (case thrd (update_tree S0 p j p jn) (lsuc (update_tree S0 p j p jn) v) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd (update_tree S0 p j p jn)) w)
           \<and> pre \<noteq> [] \<and> last pre = lsuc (update_tree S0 p j p jn) v \<and> set pre = children (prnt (update_tree S0 p j p jn)) v"
proof -
  define S5 where S5d: "S5 = update_tree S0 p j p jn"
  have psF: "parent_spec (thrd S5)" unfolding S5d by (rule clauseB_ip)
  have contig: "\<And>v. v \<in> V \<Longrightarrow> \<exists>pre suf. follow (thrd S5) v = pre @ suf \<and> set pre = children (prnt S5) v \<and> pre \<noteq> [] \<and> hd pre = v"
    unfolding S5d using clauseJ_contig_ip by auto
  have lsl0: "\<And>v pre suf. v \<in> V \<Longrightarrow> follow (thrd S5) v = pre @ suf \<Longrightarrow> set pre = children (prnt S5) v \<Longrightarrow> pre \<noteq> [] \<Longrightarrow> hd pre = v \<Longrightarrow> lsuc S5 v = last pre"
    unfolding S5d using lsuc_last_ip[OF jneq jnp pjn jnj] by auto
  have main: "\<forall>v\<in>V. \<exists>pre. follow (thrd S5) v = pre @ (case thrd S5 (lsuc S5 v) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd S5) w)
             \<and> pre \<noteq> [] \<and> last pre = lsuc S5 v \<and> set pre = children (prnt S5) v"
  proof
    fix v assume vV: "v \<in> V"
    obtain pre suf where P1: "follow (thrd S5) v = pre @ suf" and P2: "set pre = children (prnt S5) v"
      and P3: "pre \<noteq> []" and P4: "hd pre = v" using contig[OF vV] by blast
    have lsl: "lsuc S5 v = last pre" using lsl0[OF vV P1 P2 P3 P4] by auto
    have cont: "(case thrd S5 (lsuc S5 v) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd S5) w) = suf"
    proof (cases suf)
      case Nil
      have fv: "follow (thrd S5) v = pre" using P1 Nil by simp
      have "thrd S5 (last pre) = None" using follow_last_None[OF psF, of v] fv by simp
      thus ?thesis using lsl Nil by simp
    next
      case (Cons y ys)
      have P1c: "follow (thrd S5) v = pre @ y # ys" using P1 Cons by simp
      have pe: "pre = butlast pre @ [last pre]" using append_butlast_last_id[OF P3] by simp
      have "pre @ y # ys = butlast pre @ last pre # y # ys" by (subst pe) simp
      hence split: "follow (thrd S5) v = butlast pre @ last pre # y # ys" using P1c by simp
      have edge: "thrd S5 (last pre) = Some y" using thread_link[OF psF split] by auto
      have "follow (thrd S5) y = y # ys" by (rule follow_append_ps[OF psF P1c])
      hence "follow (thrd S5) y = suf" using Cons by simp
      thus ?thesis using edge lsl by simp
    qed
    have g1: "follow (thrd S5) v = pre @ (case thrd S5 (lsuc S5 v) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd S5) w)" using P1 cont by simp
    show "\<exists>pre. follow (thrd S5) v = pre @ (case thrd S5 (lsuc S5 v) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd S5) w)
             \<and> pre \<noteq> [] \<and> last pre = lsuc S5 v \<and> set pre = children (prnt S5) v"
    proof (intro exI[of _ pre] conjI)
      show "follow (thrd S5) v = pre @ (case thrd S5 (lsuc S5 v) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd S5) w)" by (rule g1)
      show "pre \<noteq> []" by (rule P3)
      show "last pre = lsuc S5 v" by (rule lsl[symmetric])
      show "set pre = children (prnt S5) v" by (rule P2)
    qed
  qed
  show ?thesis by (rule main[unfolded S5d])
qed

text \<open>IP-2 clause E for the @{term "i = p"} branch.  @{const move_S1}'s thread realises the distinct
      spanning list @{const movlist} (@{thm out_edge_ip}), so its domain is @{term "V - {last movlist}"}
      (@{text dom_move_thrd}); and the root's new last successor equals @{term "last movlist"} by
      @{thm lsuc_last_ip} at the root (whose block is the whole thread, since @{term r}'s subtree is
      all of @{term V}).\<close>

lemma children_ip_root: "children ((prnt S0)(p \<mapsto> j)) r = V"
proof
  have rV': "r \<in> V" by (rule rV)
  show "children ((prnt S0)(p \<mapsto> j)) r \<subseteq> V" by (rule children_ip_subset_V[OF rV'])
  show "V \<subseteq> children ((prnt S0)(p \<mapsto> j)) r"
  proof
    fix u assume uV: "u \<in> V"
    have "last (follow ((prnt S0)(p \<mapsto> j)) u) = r" by (rule last_follow_root[OF rooted_newtree_ip uV])
    hence "r \<in> set (follow ((prnt S0)(p \<mapsto> j)) u)" using follow_ne_ps[OF parent_spec_newtree_ip, of u] last_in_set by metis
    thus "u \<in> children ((prnt S0)(p \<mapsto> j)) r" unfolding children_def by simp
  qed
qed

lemma dom_move_thrd: "dom (thrd move_S1) = V - {last movlist}"
proof -
  have oe: "follow (thrd move_S1) r = movlist" by (rule out_edge_ip)
  have ps: "parent_spec (thrd move_S1)" by (rule parent_spec_move_thrd)
  have lastNone: "thrd move_S1 (last movlist) = None" using follow_last_None[OF ps, of r] oe by simp
  show ?thesis
  proof
    show "dom (thrd move_S1) \<subseteq> V - {last movlist}"
    proof
      fix x assume "x \<in> dom (thrd move_S1)"
      then obtain y where xy: "thrd move_S1 x = Some y" by auto
      have "x \<in> V" using move_thrd_dom_V[OF xy] by auto
      moreover have "x \<noteq> last movlist" using xy lastNone by auto
      ultimately show "x \<in> V - {last movlist}" by simp
    qed
  next
    show "V - {last movlist} \<subseteq> dom (thrd move_S1)"
    proof
      fix x assume "x \<in> V - {last movlist}"
      hence xV: "x \<in> V" and xne: "x \<noteq> last movlist" by auto
      have "x \<in> set movlist" using xV set_movlist by simp
      then obtain i where ile: "i < length movlist" and xi: "movlist ! i = x" by (metis in_set_conv_nth)
      have "Suc i < length movlist"
      proof (rule ccontr)
        assume "\<not> Suc i < length movlist"
        hence "i = length movlist - 1" using ile by simp
        hence "x = last movlist" using xi movlist_ne ile by (simp add: last_conv_nth)
        thus False using xne by simp
      qed
      hence lt: "Suc i < length (follow (thrd move_S1) r)" using oe by simp
      have "thrd move_S1 (follow (thrd move_S1) r ! i) = Some (follow (thrd move_S1) r ! Suc i)" by (rule follow_nth_Suc[OF ps lt])
      hence "thrd move_S1 (movlist ! i) = Some (movlist ! Suc i)" using oe by simp
      thus "x \<in> dom (thrd move_S1)" using xi by auto
    qed
  qed
qed

lemma clauseE_ip:
  assumes jneq: "jn = join_of (prnt S0) p j" and jnp: "jn \<in> set (follow (prnt S0) p)" and pjn: "p \<noteq> jn" and jnj: "jn \<in> set (follow (prnt S0) j)"
  shows "dom (thrd (update_tree S0 p j p jn)) = V - {lsuc (update_tree S0 p j p jn) r}"
proof -
  have rV': "r \<in> V" by (rule rV)
  have UTt: "thrd (update_tree S0 p j p jn) = thrd move_S1" by (rule move_thrd)
  have domUT: "dom (thrd (update_tree S0 p j p jn)) = V - {last movlist}" using dom_move_thrd UTt by simp
  obtain pre suf where P1: "follow (thrd (update_tree S0 p j p jn)) r = pre @ suf" and P2: "set pre = children (prnt (update_tree S0 p j p jn)) r" and P3: "pre \<noteq> []" and P4: "hd pre = r"
    using clauseJ_contig_ip[OF rV'] by blast
  have lsr: "lsuc (update_tree S0 p j p jn) r = last pre" using lsuc_last_ip[OF jneq jnp pjn jnj rV' P1 P2 P3 P4] by auto
  have setpre_V: "set pre = V" using P2 move_prnt children_ip_root by simp
  have fr: "follow (thrd (update_tree S0 p j p jn)) r = movlist" using out_edge_ip UTt by simp
  have prefix: "pre @ suf = movlist" using P1 fr by simp
  have distps: "distinct (pre @ suf)" using prefix distinct_movlist by simp
  have d: "set pre \<inter> set suf = {}" using distps by (simp add: distinct_append)
  have unionV: "set pre \<union> set suf = V"
  proof -
    have a1: "set pre \<union> set suf = set (pre @ suf)" by simp
    have a2: "set (pre @ suf) = set movlist" using prefix by simp
    show ?thesis using a1 a2 set_movlist by simp
  qed
  have sufsub: "set suf \<subseteq> set pre" using unionV setpre_V by auto
  have iabs: "set pre \<inter> set suf = set suf" by (rule Int_absorb1[OF sufsub])
  have sufempty: "set suf = {}" using iabs d by simp
  have su: "suf = []" using sufempty by simp
  have lpm: "last pre = last movlist" using prefix su by simp
  have "lsuc (update_tree S0 p j p jn) r = last movlist" using lsr lpm by simp
  thus ?thesis using domUT by simp
qed

text \<open>IP-8: the @{term "i = p"} branch bundle --- all ten @{const arb_invar} clauses for the degenerate
      move, assembled by @{thm arb_invarI}.\<close>
lemma arb_invar_update_tree_ip:
  assumes jneq: "jn = join_of (prnt S0) p j" and jnp: "jn \<in> set (follow (prnt S0) p)" and pjn: "p \<noteq> jn" and jnj: "jn \<in> set (follow (prnt S0) j)"
  shows "arb_invar r V (update_tree S0 p j p jn)"
  by (rule arb_invarI[OF clauseA_ip clauseB_ip clauseC_ip clauseD_ip clauseE_ip[OF jneq jnp pjn jnj] clauseF_ip clauseG_ip clauseH_ip clauseI_ip[OF jneq jnp pjn jnj] clauseJ_ip[OF jneq jnp pjn jnj]])

text \<open>The reversal branch (@{term "0 < k"}) bundle --- the ten @{const arb_invar} clauses
      @{thm clauseA}..@{thm clauseJ}, bridged to @{const update_tree} via @{thm update_tree_prnt},
      @{thm update_tree_thrd}, @{thm update_tree_rvth}.\<close>
lemma arb_invar_update_tree:
  assumes kpos: "0 < k" and jneq: "jn = join_of (prnt S0) i j"
      and jnp: "jn \<in> set (follow (prnt S0) p)" and pjn: "p \<noteq> jn" and jnj: "jn \<in> set (follow (prnt S0) j)"
  shows "arb_invar r V (update_tree S0 i j p jn)"
proof (rule arb_invarI)
  show "rooted_arborescense_invar r V (prnt (update_tree S0 i j p jn))"
    using clauseA update_tree_prnt[OF kpos] by simp
  show "parent_spec (thrd (update_tree S0 i j p jn))" by (rule clauseB[OF kpos])
  show "parent_spec (rvth (update_tree S0 i j p jn))" by (rule clauseC[OF kpos])
  show "set (follow (thrd (update_tree S0 i j p jn)) r) = V" by (rule clauseD[OF kpos])
  show "dom (thrd (update_tree S0 i j p jn)) = V - {lsuc (update_tree S0 i j p jn) r}" by (rule clauseE[OF kpos jnp pjn jnj])
  show "dom (rvth (update_tree S0 i j p jn)) = V - {r}" by (rule clauseF[OF kpos])
  show "\<forall>v v'. (thrd (update_tree S0 i j p jn) v = Some v') = (rvth (update_tree S0 i j p jn) v' = Some v)"
    by (simp add: update_tree_thrd[OF kpos] update_tree_rvth[OF kpos] clauseG[OF kpos])
  show "\<forall>v\<in>V. lsuc (update_tree S0 i j p jn) v \<in> V" by (rule update_tree_lsuc_in_V[OF kpos])
  show "\<forall>v\<in>V. snum (update_tree S0 i j p jn) v = card (children (prnt (update_tree S0 i j p jn)) v)" by (rule clauseI[OF kpos jneq])
  show "\<forall>v\<in>V. \<exists>pre. follow (thrd (update_tree S0 i j p jn)) v = pre @ (case thrd (update_tree S0 i j p jn) (lsuc (update_tree S0 i j p jn) v) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd (update_tree S0 i j p jn)) w) \<and> pre \<noteq> [] \<and> last pre = lsuc (update_tree S0 i j p jn) v \<and> set pre = children (prnt (update_tree S0 i j p jn)) v"
    by (rule clauseJ[OF kpos jneq jnp pjn])
qed

end

text \<open>The assembly bridge ({\isasymsection}14): @{const arb_invar} together with the four pivot preconditions yield
      an interpretation of @{locale stem_setup}.  The path @{term s}, @{term k} comes from
      @{thm follow_path}; the no-cycle precondition @{thm stem_setup.jnotp} from @{thm no_cycle}
      (both @{term i} and @{term j} reach the root @{term r}, so @{thm last_follow_root} supplies its
      @{text lst} hypothesis).  Thus the whole {\isasymsection}13 stem-loop result applies to the actual pivot.\<close>
lemma pivot_stem_setup:
  assumes arb: "arb_invar r V S0"
      and iV: "i \<in> V" and jV: "j \<in> V"
      and pi: "p \<in> set (follow (prnt S0) i)"
      and jnp: "jn \<in> set (follow (prnt S0) p)"
      and jndef: "jn = join_of (prnt S0) i j"
      and pne: "p \<noteq> jn"
  obtains s k where "stem_setup S0 r V i j p k s"
proof -
  have rinv: "rooted_arborescense_invar r V (prnt S0)" using arb unfolding arb_invar_def by simp
  have ps: "parent_spec (prnt S0)" by (rule rooted_arborescense_invar_parent_spec[OF rinv])
  obtain s k where s0: "s 0 = i" and sk: "s k = p"
    and step: "\<And>t. t < k \<Longrightarrow> prnt S0 (s t) = Some (s (Suc t))"
    and inj: "inj_on s {..k}"
    and mem: "\<And>t. t \<le> k \<Longrightarrow> s t \<in> set (follow (prnt S0) i)"
    using follow_path[OF ps pi] by auto
  have lst: "last (follow (prnt S0) i) = last (follow (prnt S0) j)"
    using last_follow_root[OF rinv iV] last_follow_root[OF rinv jV] by simp
  have "p \<notin> set (follow (prnt S0) j)" using no_cycle[OF ps lst pi jnp jndef pne] by auto
  hence jnotp: "j \<notin> children (prnt S0) p" unfolding children_def by simp
  have pnr: "p \<noteq> r" using pivot_p_ne_r[OF arb jnp] pne by auto
  have "stem_setup S0 r V i j p k s"
    by (unfold_locales) (use arb s0 step sk inj jnotp pnr iV jV in auto)
  thus ?thesis using that by auto
qed

subsection \<open>Correctness: the swap preserves the invariant\<close>

text \<open>
  Preconditions, reading off the pivot (@{term T} abbreviates @{term "prnt S"}):
  \<^item> the combined invariant holds;
  \<^item> @{term i}, @{term j} are vertices;
  \<^item> @{term "jn = join_of (prnt S) i j"}: @{term jn} is the apex of the cycle;
  \<^item> @{term "p \<in> set (follow (prnt S) i)"}: @{term p} is an ancestor-or-self of @{term i};
  \<^item> @{term "jn \<in> set (follow (prnt S) p)"} and @{term "p \<noteq> jn"}: @{term p} lies strictly between
    @{term i} and the apex, so the leaving edge @{term "(p, the (prnt S p))"} sits on the cycle
    below the apex (in particular @{term "p \<noteq> r"} and @{term j} is outside the detached subtree
    @{term "children (prnt S) p"}, so inserting @{term "(i,j)"} creates no cycle).
\<close>

lemma update_tree_preserves_arb_invar:
  assumes arb: "arb_invar r V S"
      and iV: "i \<in> V"
      and jV: "j \<in> V"
      and jneq: "jn = join_of (prnt S) i j"
      and pi: "p \<in> set (follow (prnt S) i)"
      and jnp: "jn \<in> set (follow (prnt S) p)"
      and pne: "p \<noteq> jn"
    shows "arb_invar r V (update_tree S i j p jn)"
      and "prnt (update_tree S i j p jn) i = Some j"
proof -
  obtain s k where SS: "stem_setup S r V i j p k s"
    by (rule pivot_stem_setup[OF arb iV jV pi jnp jneq pne])
  interpret ss: stem_setup S r V i j p k s by (rule SS)
  have jnj: "jn \<in> set (follow (prnt S) j)" using ss.join_facts[OF jneq] by simp
  have kpos_of_ne: "i \<noteq> p \<Longrightarrow> 0 < k"
  proof (rule ccontr)
    assume "i \<noteq> p" and "\<not> 0 < k"
    hence "k = 0" by simp
    hence "i = p" using ss.path0 ss.pathk by simp
    thus False using \<open>i \<noteq> p\<close> by simp
  qed
  have goal1: "arb_invar r V (update_tree S i j p jn)"
  proof (cases "i = p")
    case True
    have jneq': "jn = join_of (prnt S) p j" using jneq True by simp
    have "arb_invar r V (update_tree S p j p jn)" by (rule ss.arb_invar_update_tree_ip[OF jneq' jnp pne jnj])
    thus ?thesis using True by simp
  next
    case False
    have kpos: "0 < k" using kpos_of_ne False by simp
    show ?thesis by (rule ss.arb_invar_update_tree[OF kpos jneq jnp pne jnj])
  qed
  have goal2: "prnt (update_tree S i j p jn) i = Some j"
  proof (cases "i = p")
    case True
    thus ?thesis using ss.prnt_ip by simp
  next
    case False
    have kpos: "0 < k" using kpos_of_ne False by simp
    show ?thesis by (rule ss.update_tree_prnt_i[OF kpos])
  qed
  show "arb_invar r V (update_tree S i j p jn)" by (rule goal1)
  show "prnt (update_tree S i j p jn) i = Some j" by (rule goal2)
qed

(*
text \<open>The whole pivot is code-generatable: it only walks the maps.\<close>
export_code join_of stem_loop stem_num_loop last_vin_loop last_vout_loop
            succ_vin_loop succ_vout_loop dirty_pass update_tree
  in SML*)


section \<open>Basic properties of the subtree iteration and the pair-of-paths search\<close>

text \<open>This section verifies the two arborescence-ADT operations defined on the threaded tree in
      \<open>Rooted_Arborescense_Defs\<close>: the subtree iteration
      @{const iterate_root_opposed_impl} (a plain recursion on the thread) and the pair-of-paths
      search @{const get_path_pair_impl} (a snum-guided climb of the two parent chains).\<close>

subsection \<open>The subtree iteration folds over the children (subtree) in thread order\<close>

text \<open>@{const subtree_fold} walks the thread from a node up to the (fresh) stop marker, folding
      @{term f} left-to-right over exactly that thread block.\<close>
lemma subtree_fold_follow:
  assumes ps: "parent_spec (thrd S)"
      and L: "follow (thrd S) u = bl @ stp # rest"
      and notin: "stp \<notin> set bl"
  shows "subtree_fold S stp u f acc = foldl (\<lambda>a x. f x a) acc (bl @ [stp])"
  using L notin
proof (induct bl arbitrary: u acc)
  case Nil
  have "hd (follow (thrd S) u) = u" by (rule follow_hd_ps[OF ps])
  hence "u = stp" using Nil.prems(1) by simp
  thus ?case by (subst subtree_fold.simps) (simp add: Let_def)
next
  case (Cons b bs)
  have hd: "u = b" using follow_hd_ps[OF ps, of u] Cons.prems(1) by simp
  have une: "u \<noteq> stp" using Cons.prems(2) hd by auto
  have flu: "follow (thrd S) u = u # (bs @ stp # rest)" using Cons.prems(1) hd by simp
  have tw_ne: "thrd S u \<noteq> None"
  proof
    assume "thrd S u = None"
    hence "follow (thrd S) u = [u]" by (subst follow_ps_simps[OF ps]) simp
    thus False using flu by simp
  qed
  then obtain w where tw: "thrd S u = Some w" by auto
  have fw: "follow (thrd S) w = bs @ stp # rest"
    using flu tw follow_ps_simps[OF ps, of u] by simp
  have notin': "stp \<notin> set bs" using Cons.prems(2) by simp
  have step: "subtree_fold S stp u f acc = subtree_fold S stp w f (f u acc)"
    using une tw by (subst subtree_fold.simps) (simp add: Let_def)
  have IH: "subtree_fold S stp w f (f u acc) = foldl (\<lambda>a x. f x a) (f u acc) (bs @ [stp])"
    using Cons.hyps[OF fw notin'] .
  show ?case using step IH hd by simp
qed

text \<open>Hence the iteration folds over the whole @{const block} of @{term v} (its subtree, in thread
      order).\<close>
lemma iterate_root_opposed_impl_block:
  assumes inv: "arb_invar r V S" and vV: "v \<in> V"
  shows "iterate_root_opposed_impl S v f acc = foldl (\<lambda>a x. f x a) acc (block S v)"
proof -
  have pst: "parent_spec (thrd S)" using inv unfolding arb_invar_def by simp
  have bne: "block S v \<noteq> []" by (rule block_props(2)[OF inv vV])
  have blast': "last (block S v) = lsuc S v" by (rule block_props(3)[OF inv vV])
  have decomp: "follow (thrd S) v = block S v @ (case thrd S (lsuc S v) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd S) w)"
    by (rule block_props(1)[OF inv vV])
  define bl where "bl = butlast (block S v)"
  have blk: "block S v = bl @ [lsuc S v]"
    unfolding bl_def using append_butlast_last_id[OF bne] blast' by simp
  have distf: "distinct (follow (thrd S) v)" by (rule follow_distinct_ps[OF pst])
  have distb: "distinct (block S v)" using distf decomp by (metis distinct_append)
  have notin: "lsuc S v \<notin> set bl" using distb blk by simp
  have L: "follow (thrd S) v = bl @ lsuc S v # (case thrd S (lsuc S v) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd S) w)"
    using decomp blk by simp
  have "subtree_fold S (lsuc S v) v f acc = foldl (\<lambda>a x. f x a) acc (bl @ [lsuc S v])"
    by (rule subtree_fold_follow[OF pst L notin])
  thus ?thesis using blk by (simp add: iterate_root_opposed_impl_def)
qed

text \<open>The arborescence-ADT specification form: there is a \<^emph>\<open>distinct\<close> list of exactly the children
      (@{const children}, the subtree of @{term v}) over which the iteration is a @{const foldr}.\<close>
theorem iterate_root_opposed_impl_foldr:
  assumes inv: "arb_invar r V S" and vV: "v \<in> V"
  shows "\<exists>xs. distinct xs \<and> set xs = children (prnt S) v
             \<and> iterate_root_opposed_impl S v f acc = foldr f xs acc"
proof -
  have pst: "parent_spec (thrd S)" using inv unfolding arb_invar_def by simp
  have decomp: "follow (thrd S) v = block S v @ (case thrd S (lsuc S v) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd S) w)"
    by (rule block_props(1)[OF inv vV])
  have distf: "distinct (follow (thrd S) v)" by (rule follow_distinct_ps[OF pst])
  have distb: "distinct (block S v)" using distf decomp by (metis distinct_append)
  have setb: "set (block S v) = children (prnt S) v" by (rule block_props(4)[OF inv vV])
  have "iterate_root_opposed_impl S v f acc = foldl (\<lambda>a x. f x a) acc (block S v)"
    by (rule iterate_root_opposed_impl_block[OF inv vV])
  also have "... = foldr f (rev (block S v)) acc" by (simp add: foldr_conv_foldl)
  finally have eq: "iterate_root_opposed_impl S v f acc = foldr f (rev (block S v)) acc" .
  show ?thesis
    by (intro exI[where x="rev (block S v)"]) (simp add: distb setb eq)
qed

subsection \<open>The pair-of-paths search returns the two branches up to the join\<close>

text \<open>Strict monotonicity of @{const snum} towards the root: a \<^emph>\<open>proper\<close> ancestor has a strictly
      larger subtree.  This is what makes the snum-guided climb correct (the join node, being an
      ancestor of both endpoints, is never the smaller one, hence never lifted).\<close>
lemma snum_proper_anc_lt:
  assumes inv: "arb_invar r V (S :: 'a ndtree)" and aV: "a \<in> V"
      and amem: "a \<in> set (follow (prnt S) b)" and ane: "a \<noteq> b"
  shows "snum S b < snum S a"
proof -
  have rinv: "rooted_arborescense_invar r V (prnt S)" using inv unfolding arb_invar_def by simp
  have ps: "parent_spec (prnt S)" by (rule rooted_arborescense_invar_parent_spec[OF rinv])
  have bV: "b \<in> V"
  proof (rule ccontr)
    assume "b \<notin> V"
    hence "prnt S b = None" using rooted_arborescense_invar_dom[OF rinv] by auto
    hence "follow (prnt S) b = [b]" by (subst follow_ps_simps[OF ps]) simp
    thus False using amem ane by simp
  qed
  have bchild_a: "b \<in> children (prnt S) a" using amem unfolding children_def by simp
  have sub: "children (prnt S) b \<subseteq> children (prnt S) a" by (rule children_subset[OF ps bchild_a])
  have aa: "a \<in> children (prnt S) a"
    using follow_hd_ps[OF ps, of a] follow_ne_ps[OF ps, of a]
    by (metis children_def hd_in_set mem_Collect_eq)
  have a_notin_b: "a \<notin> children (prnt S) b"
  proof
    assume "a \<in> children (prnt S) b"
    hence "b \<in> set (follow (prnt S) a)" unfolding children_def by simp
    hence "a = b" using ancestor_antisym[OF ps amem] by simp
    thus False using ane by simp
  qed
  have finA: "finite (children (prnt S) a)"
    using block_props(4)[OF inv aV] by (metis List.finite_set)
  have psub: "children (prnt S) b \<subset> children (prnt S) a" using sub aa a_notin_b by blast
  have "card (children (prnt S) b) < card (children (prnt S) a)"
    by (rule psubset_card_mono[OF finA psub])
  moreover have "snum S b = card (children (prnt S) b)" using inv bV unfolding arb_invar_def by simp
  moreover have "snum S a = card (children (prnt S) a)" using inv aV unfolding arb_invar_def by simp
  ultimately show ?thesis by simp
qed

text \<open>A node with a proper ancestor @{term j} has a parent, and @{term j} stays on the parent's
      root-path.\<close>
lemma follow_cons_of_anc:
  assumes ps: "parent_spec T" and jf: "j \<in> set (follow T x)" and xne: "x \<noteq> j"
  shows "\<exists>w. T x = Some w \<and> follow T x = x # follow T w \<and> j \<in> set (follow T w)"
proof (cases "T x")
  case None
  hence "follow T x = [x]" by (subst follow_ps_simps[OF ps]) simp
  thus ?thesis using jf xne by simp
next
  case (Some w)
  hence fx: "follow T x = x # follow T w" by (subst follow_ps_simps[OF ps]) simp
  have "j \<in> set (follow T w)" using jf fx xne by simp
  thus ?thesis using Some fx by auto
qed

text \<open>The root-path of a vertex in @{term V} ends at the root @{term r}.\<close>
lemma follow_last_root:
  assumes inv: "arb_invar r V S" and uV: "u \<in> V"
  shows "last (follow (prnt S) u) = r"
proof -
  have rinv: "rooted_arborescense_invar r V (prnt S)" using inv unfolding arb_invar_def by simp
  have ps: "parent_spec (prnt S)" by (rule rooted_arborescense_invar_parent_spec[OF rinv])
  define L where "L = follow (prnt S) u"
  have Lne: "L \<noteq> []" unfolding L_def by (rule follow_ne_ps[OF ps])
  define l where "l = last L"
  have lmem: "l \<in> set L" using Lne by (simp add: l_def)
  have lV: "l \<in> V" using follow_subset_V[OF rinv uV] lmem by (auto simp: L_def)
  have Ld: "follow (prnt S) u = butlast L @ l # []" using Lne by (simp add: l_def L_def)
  have fl: "follow (prnt S) l = [l]" using follow_append_ps[OF ps Ld] by simp
  have "prnt S l = None"
  proof (cases "prnt S l")
    case (Some w)
    hence "follow (prnt S) l = l # follow (prnt S) w" by (subst follow_ps_simps[OF ps]) simp
    hence "follow (prnt S) w = []" using fl by simp
    thus ?thesis using follow_ne_ps[OF ps, of w] by simp
  qed simp
  hence "l \<notin> dom (prnt S)" by (simp add: dom_def)
  hence "l \<notin> V - {r}" using rooted_arborescense_invar_dom[OF rinv] by simp
  thus ?thesis using lV by (simp add: l_def L_def)
qed

text \<open>The core loop invariant: @{const join_paths_loop} climbs the two parent chains to the join
      @{term j} (any common ancestor supplied as parameter), accumulating on each side exactly the
      strictly-below-@{term j} prefix of that root-path.  Proved by strong induction on the combined
      length of the two remaining root-paths; the guard "j {\isasymin} set (follow (prnt S) {\isasymdots})" and the
      disjointness of the two prefixes are maintained, and @{thm snum_proper_anc_lt} guarantees the
      join node is never lifted.\<close>
lemma join_paths_loop_eval:
  assumes inv: "arb_invar r V S"
      and cuV0: "cu0 \<in> V" and cvV0: "cv0 \<in> V"
      and jcu0: "j \<in> set (follow (prnt S) cu0)"
      and jcv0: "j \<in> set (follow (prnt S) cv0)"
      and disj0: "set (takeWhile (\<lambda>x. x \<noteq> j) (follow (prnt S) cu0))
                   \<inter> set (takeWhile (\<lambda>x. x \<noteq> j) (follow (prnt S) cv0)) = {}"
  shows "join_paths_loop S cu0 cv0 acc1 acc2
          = (rev acc1 @ takeWhile (\<lambda>x. x \<noteq> j) (follow (prnt S) cu0),
             rev acc2 @ takeWhile (\<lambda>x. x \<noteq> j) (follow (prnt S) cv0))"
proof -
  have rinv: "rooted_arborescense_invar r V (prnt S)" using inv unfolding arb_invar_def by simp
  have ps: "parent_spec (prnt S)" by (rule rooted_arborescense_invar_parent_spec[OF rinv])
  have jV: "j \<in> V" using follow_subset_V[OF rinv cuV0] jcu0 by auto
  define W where "W = (\<lambda>x. takeWhile (\<lambda>y. y \<noteq> j) (follow (prnt S) x))"
  { fix N cu cv a1 a2
    have "length (follow (prnt S) cu) + length (follow (prnt S) cv) = N \<Longrightarrow>
          cu \<in> V \<Longrightarrow> cv \<in> V \<Longrightarrow> j \<in> set (follow (prnt S) cu) \<Longrightarrow> j \<in> set (follow (prnt S) cv) \<Longrightarrow>
          set (W cu) \<inter> set (W cv) = {} \<Longrightarrow>
          join_paths_loop S cu cv a1 a2 = (rev a1 @ W cu, rev a2 @ W cv)"
    proof (induct N arbitrary: cu cv a1 a2 rule: less_induct)
      case (less N cu cv a1 a2)
      note eqN = less.prems(1) and cuV = less.prems(2) and cvV = less.prems(3)
        and jcu = less.prems(4) and jcv = less.prems(5) and disj = less.prems(6)
      show ?case
      proof (cases "cu = cv")
        case True
        note eqcc = True
        have cuj: "cu = j"
        proof (rule ccontr)
          assume cune: "cu \<noteq> j"
          have "cu \<in> set (W cu)"
          proof -
            have ne: "follow (prnt S) cu \<noteq> []" by (rule follow_ne_ps[OF ps])
            have hd: "hd (follow (prnt S) cu) = cu" by (rule follow_hd_ps[OF ps])
            show ?thesis using ne hd cune by (cases "follow (prnt S) cu") (auto simp: W_def)
          qed
          moreover have "cu \<in> set (W cv)" using eqcc calculation by simp
          ultimately show False using disj by auto
        qed
        have Wcu: "W cu = []"
          using cuj follow_ne_ps[OF ps, of cu] follow_hd_ps[OF ps, of cu]
          by (simp add: W_def takeWhile_eq_Nil_iff)
        have Wcv: "W cv = []" using Wcu eqcc by simp
        show ?thesis using eqcc Wcu Wcv by (subst join_paths_loop.simps) simp
      next
        case False
        note cune_cv = False
        show ?thesis
        proof (cases "snum S cu \<le> snum S cv")
          case True
          note le = True
          have cune: "cu \<noteq> j"
          proof (rule ccontr)
            assume "\<not> cu \<noteq> j" hence cj: "cu = j" by simp
            have cvne: "cv \<noteq> j" using cune_cv cj by auto
            have "snum S cv < snum S j" using snum_proper_anc_lt[OF inv jV jcv] cvne by simp
            thus False using le cj by simp
          qed
          obtain w where Pw: "prnt S cu = Some w"
            and fcu: "follow (prnt S) cu = cu # follow (prnt S) w"
            and jcw: "j \<in> set (follow (prnt S) w)"
            using follow_cons_of_anc[OF ps jcu cune] by auto
          have Wcu: "W cu = cu # W w" using fcu cune by (simp add: W_def)
          have wmem: "w \<in> set (follow (prnt S) cu)"
            using fcu follow_hd_ps[OF ps, of w] follow_ne_ps[OF ps, of w]
            by (metis hd_in_set list.set_intros(2))
          have wV: "w \<in> V" using follow_subset_V[OF rinv cuV] wmem by auto
          have disj': "set (W w) \<inter> set (W cv) = {}" using disj Wcu by auto
          have lenlt: "length (follow (prnt S) w) + length (follow (prnt S) cv) < N"
            using eqN fcu by simp
          have step: "join_paths_loop S cu cv a1 a2 = join_paths_loop S w cv (cu # a1) a2"
            using cune_cv le Pw by (subst join_paths_loop.simps) simp
          have rec: "join_paths_loop S w cv (cu # a1) a2 = (rev (cu # a1) @ W w, rev a2 @ W cv)"
            by (rule less.hyps[OF lenlt refl wV cvV jcw jcv disj'])
          show ?thesis using step rec Wcu by simp
        next
          case False
          note notle = False
          have cvne: "cv \<noteq> j"
          proof (rule ccontr)
            assume "\<not> cv \<noteq> j" hence cj: "cv = j" by simp
            have cune: "cu \<noteq> j" using cune_cv cj by auto
            have "snum S cu < snum S j" using snum_proper_anc_lt[OF inv jV jcu] cune by simp
            thus False using notle cj by simp
          qed
          obtain w where Pw: "prnt S cv = Some w"
            and fcv: "follow (prnt S) cv = cv # follow (prnt S) w"
            and jcw: "j \<in> set (follow (prnt S) w)"
            using follow_cons_of_anc[OF ps jcv cvne] by auto
          have Wcv: "W cv = cv # W w" using fcv cvne by (simp add: W_def)
          have wmem: "w \<in> set (follow (prnt S) cv)"
            using fcv follow_hd_ps[OF ps, of w] follow_ne_ps[OF ps, of w]
            by (metis hd_in_set list.set_intros(2))
          have wV: "w \<in> V" using follow_subset_V[OF rinv cvV] wmem by auto
          have disj': "set (W cu) \<inter> set (W w) = {}" using disj Wcv by auto
          have lenlt: "length (follow (prnt S) cu) + length (follow (prnt S) w) < N"
            using eqN fcv by simp
          have step: "join_paths_loop S cu cv a1 a2 = join_paths_loop S cu w a1 (cv # a2)"
            using cune_cv notle Pw by (subst join_paths_loop.simps) simp
          have rec: "join_paths_loop S cu w a1 (cv # a2) = (rev a1 @ W cu, rev (cv # a2) @ W w)"
            by (rule less.hyps[OF lenlt refl cuV wV jcu jcw disj'])
          show ?thesis using step rec Wcv by simp
        qed
      qed
    qed }
  note KEY = this
  have disjW: "set (W cu0) \<inter> set (W cv0) = {}" using disj0 by (simp add: W_def)
  have "join_paths_loop S cu0 cv0 acc1 acc2 = (rev acc1 @ W cu0, rev acc2 @ W cv0)"
    by (rule KEY[OF refl cuV0 cvV0 jcu0 jcv0 disjW])
  thus ?thesis by (simp add: W_def)
qed

text \<open>Any member @{term j} of a root-path splits it into the before-@{term j} prefix and the
      root-path of @{term j}.\<close>
lemma follow_split_at_j:
  assumes ps: "parent_spec T" and jf: "j \<in> set (follow T u)"
  shows "follow T u = takeWhile (\<lambda>x. x \<noteq> j) (follow T u) @ follow T j"
proof -
  obtain A C where uAC: "follow T u = A @ j # C" using jf by (meson split_list)
  have dist: "distinct (follow T u)" by (rule follow_distinct_ps[OF ps])
  have jnotA: "j \<notin> set A" using dist uAC by auto
  have twA: "takeWhile (\<lambda>x. x \<noteq> j) (follow T u) = A"
  proof -
    have "takeWhile (\<lambda>x. x \<noteq> j) (A @ (j # C)) = A @ takeWhile (\<lambda>x. x \<noteq> j) (j # C)"
      by (rule takeWhile_append2) (use jnotA in auto)
    thus ?thesis using uAC by simp
  qed
  have "follow T j = j # C" using follow_append_ps[OF ps uAC] .
  thus ?thesis using uAC twA by simp
qed

text \<open>The two before-join prefixes are disjoint: the join @{const join_of} is the \<^emph>\<open>first\<close> common
      node of the two root-paths.\<close>
lemma join_takeWhile_disjoint:
  assumes inv: "arb_invar r V S" and uV: "u \<in> V" and vV: "v \<in> V"
      and jdef: "j = join_of (prnt S) u v"
  shows "set (takeWhile (\<lambda>x. x \<noteq> j) (follow (prnt S) u))
        \<inter> set (takeWhile (\<lambda>x. x \<noteq> j) (follow (prnt S) v)) = {}"
proof -
  have rinv: "rooted_arborescense_invar r V (prnt S)" using inv unfolding arb_invar_def by simp
  have ps: "parent_spec (prnt S)" by (rule rooted_arborescense_invar_parent_spec[OF rinv])
  have lst: "last (follow (prnt S) u) = last (follow (prnt S) v)"
    using follow_last_root[OF inv uV] follow_last_root[OF inv vV] by simp
  have ju: "j \<in> set (follow (prnt S) u)" using join_of_mem(1)[OF ps lst] jdef by simp
  have jv: "j \<in> set (follow (prnt S) v)" using join_of_mem(2)[OF ps lst] jdef by simp
  have splu: "follow (prnt S) u = takeWhile (\<lambda>x. x \<noteq> j) (follow (prnt S) u) @ follow (prnt S) j"
    by (rule follow_split_at_j[OF ps ju])
  have du: "distinct (follow (prnt S) u)" by (rule follow_distinct_ps[OF ps])
  have disu: "set (takeWhile (\<lambda>x. x \<noteq> j) (follow (prnt S) u)) \<inter> set (follow (prnt S) j) = {}"
    using du splu by (metis distinct_append)
  have "\<And>x. x \<in> set (takeWhile (\<lambda>y. y \<noteq> j) (follow (prnt S) u)) \<Longrightarrow>
            x \<in> set (takeWhile (\<lambda>y. y \<noteq> j) (follow (prnt S) v)) \<Longrightarrow> False"
  proof -
    fix x assume xu: "x \<in> set (takeWhile (\<lambda>y. y \<noteq> j) (follow (prnt S) u))"
             and xv: "x \<in> set (takeWhile (\<lambda>y. y \<noteq> j) (follow (prnt S) v))"
    have xfu: "x \<in> set (follow (prnt S) u)" using xu by (auto dest: set_takeWhileD)
    have xfv: "x \<in> set (follow (prnt S) v)" using xv by (auto dest: set_takeWhileD)
    have "x \<in> set (follow (prnt S) j)" using join_of_first[OF ps lst xfu xfv] jdef by simp
    thus False using xu disu by auto
  qed
  thus ?thesis by auto
qed

text \<open>The arborescence-ADT specification form for @{const get_path_pair_impl}.  Writing @{term j}
      for the join of @{term u} and @{term v}: each returned path @{term p1}/@{term p2} is the
      before-@{term j} prefix of the corresponding root-path (so @{term "p1 @ [j]"} is an initial
      segment of @{term "follow (prnt S) u"}); both path tips @{term "p1 @ [j]"} and @{term "p2 @ [j]"}
      are distinct lists; the two branches @{term p1} and @{term p2} are disjoint; and the tips share
      exactly the single vertex @{term j} (their common last element, the join).\<close>
theorem get_path_pair_impl_correct:
  assumes inv: "arb_invar r V S" and uV: "u \<in> V" and vV: "v \<in> V"
      and pp: "get_path_pair_impl S u v = (p1, p2)"
  defines "j \<equiv> join_of (prnt S) u v"
  shows "follow (prnt S) u = p1 @ follow (prnt S) j"
    and "follow (prnt S) v = p2 @ follow (prnt S) j"
    and "distinct (p1 @ [j])"
    and "distinct (p2 @ [j])"
    and "set p1 \<inter> set p2 = {}"
    and "set (p1 @ [j]) \<inter> set (p2 @ [j]) = {j}"
proof -
  have rinv: "rooted_arborescense_invar r V (prnt S)" using inv unfolding arb_invar_def by simp
  have ps: "parent_spec (prnt S)" by (rule rooted_arborescense_invar_parent_spec[OF rinv])
  have lst: "last (follow (prnt S) u) = last (follow (prnt S) v)"
    using follow_last_root[OF inv uV] follow_last_root[OF inv vV] by simp
  have ju: "j \<in> set (follow (prnt S) u)" using join_of_mem(1)[OF ps lst] by (simp add: j_def)
  have jv: "j \<in> set (follow (prnt S) v)" using join_of_mem(2)[OF ps lst] by (simp add: j_def)
  have disjj: "set (takeWhile (\<lambda>x. x \<noteq> j) (follow (prnt S) u))
              \<inter> set (takeWhile (\<lambda>x. x \<noteq> j) (follow (prnt S) v)) = {}"
    using join_takeWhile_disjoint[OF inv uV vV] by (simp add: j_def)
  have eval: "join_paths_loop S u v [] []
              = (takeWhile (\<lambda>x. x \<noteq> j) (follow (prnt S) u), takeWhile (\<lambda>x. x \<noteq> j) (follow (prnt S) v))"
    using join_paths_loop_eval[OF inv uV vV ju jv disjj, of "[]" "[]"] by simp
  have pp': "get_path_pair_impl S u v
              = (takeWhile (\<lambda>x. x \<noteq> j) (follow (prnt S) u), takeWhile (\<lambda>x. x \<noteq> j) (follow (prnt S) v))"
    using eval by (simp add: get_path_pair_impl_def)
  have p1eq: "p1 = takeWhile (\<lambda>x. x \<noteq> j) (follow (prnt S) u)"
    and p2eq: "p2 = takeWhile (\<lambda>x. x \<noteq> j) (follow (prnt S) v)"
    using pp pp' by auto
  have du: "distinct (follow (prnt S) u)" by (rule follow_distinct_ps[OF ps])
  have dv: "distinct (follow (prnt S) v)" by (rule follow_distinct_ps[OF ps])
  have fj: "follow (prnt S) j = j # tl (follow (prnt S) j)"
    using follow_hd_ps[OF ps, of j] follow_ne_ps[OF ps, of j] by (metis hd_Cons_tl)
  show P1: "follow (prnt S) u = p1 @ follow (prnt S) j"
    using follow_split_at_j[OF ps ju] p1eq by simp
  show P2: "follow (prnt S) v = p2 @ follow (prnt S) j"
    using follow_split_at_j[OF ps jv] p2eq by simp
  have dup: "distinct (p1 @ j # tl (follow (prnt S) j))" using du P1 fj by simp
  have dvp: "distinct (p2 @ j # tl (follow (prnt S) j))" using dv P2 fj by simp
  have jnp1: "j \<notin> set p1" using dup by (auto simp: distinct_append)
  have jnp2: "j \<notin> set p2" using dvp by (auto simp: distinct_append)
  show "distinct (p1 @ [j])" using dup by (auto simp: distinct_append)
  show "distinct (p2 @ [j])" using dvp by (auto simp: distinct_append)
  show P5: "set p1 \<inter> set p2 = {}" using disjj p1eq p2eq by simp
  show "set (p1 @ [j]) \<inter> set (p2 @ [j]) = {j}" using P5 jnp1 jnp2 by auto
qed


end
