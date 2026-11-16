theory Ear_Decomposition
  imports Edmonds_Gallai
begin

provenance ai_human

section \<open>Ear Decompositions\<close>

text \<open>An ear in \<open>G\<close> relative to the subgraph with edge set \<open>H\<close>
  and vertex set \<open>X\<close> is a nonempty simple path, or a simple cycle,
  whose endpoints lie in \<open>X\<close> and whose internal vertices are new.
  All its edges are outside \<open>H\<close>. Closed ears are allowed; a cycle
  is represented by a vertex list repeating its first vertex at the end.
  Single-edge ears are allowed, but traversing an edge twice is not a cycle.\<close>

definition "ear G H X p =
  (H \<subseteq> G \<and> Vs H \<subseteq> X \<and> path G p \<and> 2 \<le> length p \<and>
   (distinct p \<or> (hd p = last p \<and> 4 \<le> length p \<and> distinct (tl p))) \<and>
   hd p \<in> X \<and> last p \<in> X \<and>
   set (tl (butlast p)) \<inter> X = {} \<and> set (edges_of_path p) \<inter> H = {})"

text \<open>A decomposition records its initial vertex \<open>r\<close> and the
  successive ears \<open>Ps\<close>. The vertex set is explicit because the
  initial singleton cannot be represented by its empty edge set alone.
  Each step adds exactly the edges and vertices of its ear; thus the final
  edge set is all of \<open>G\<close>, not merely a spanning subgraph.\<close>

inductive ear_decomposition :: "'a graph \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'a list list \<Rightarrow> bool" where
  single_vertex: "ear_decomposition {} {r} r []"
| add_ear:
    "\<lbrakk>ear_decomposition H X r Ps; ear (H \<union> set (edges_of_path p)) H X p\<rbrakk>
     \<Longrightarrow> ear_decomposition (H \<union> set (edges_of_path p)) (X \<union> set p) r (Ps @ [p])"

text \<open>Oddness refers to the number of edges, rather than the number of
  entries in the vertex list. The initial singleton contributes no ear,
  so its empty decomposition is also odd.\<close>

definition "odd_ear_decomposition G X r Ps =
  (ear_decomposition G X r Ps \<and> (\<forall>p \<in> set Ps. odd (length (edges_of_path p))))"

text \<open>For an induced subgraph on \<open>X\<close>, use the edge set
  \<open>G \<lbrakk>X\<rbrakk>\<close>. Factor-criticality is expressed exactly as in
  @{const edmonds_gallai}, using the existing matching predicates:
  @{term "\<forall>x \<in> X. \<exists>M. graph_matching (G \<lbrakk>X\<rbrakk>) M \<and> Vs M = X - {x}"}.
  The component conditions in the decomposition additionally require
  \<open>X \<noteq> {}\<close>. No separate notion of factor-criticality is introduced.\<close>

subsection \<open>Matchings on Ears\<close>

lemma ear_endpoints:
  "\<lbrakk>ear G H X p\<rbrakk> \<Longrightarrow>
    path G p \<and> 2 \<le> length p \<and> hd p \<in> X \<and> last p \<in> X"
  by (auto simp: ear_def)

lemma ear_interior:
  "ear G H X (a # q @ [b]) \<Longrightarrow>
    distinct q \<and> set q \<inter> X = {} \<and> a \<in> X \<and> b \<in> X"
  by (auto simp: ear_def)

lemma odd_ear_length:
  "\<lbrakk>ear G H X p; odd (length (edges_of_path p))\<rbrakk> \<Longrightarrow> even (length p)"
  by (auto simp: ear_def edges_of_path_length)

lemma ear_matching_on_interior:
  "\<lbrakk>ear G H X (a # q @ [b]); even (length q)\<rbrakk> \<Longrightarrow>
    \<exists>M. graph_matching G M \<and> Vs M = set q"
  using even_path_matching[of G q] path_pref[of G q "[b]"] tl_path_is_path[of G "a # q @ [b]"]
  by (auto simp: ear_def)

lemma ear_matching_remove_interior:
  assumes "ear G H X (a # q @ [b])" "even (length q)" "x \<in> set q"
  shows "\<exists>z M. z \<in> X \<and> graph_matching G M \<and> Vs M = insert z (set q - {x})"
proof-
  obtain qs rs where "q = qs @ x # rs"
    using assms(3)
    by (auto dest: split_list)
  have "path G (a # qs)" "path G (rs @ [b])"
    using assms(1) \<open>q = qs @ x # rs\<close>
      path_pref[of G "a # qs" "x # rs @ [b]"]
      path_suff[of G "a # qs @ [x]" "rs @ [b]"]
    by (auto simp: ear_def)
  obtain q1 q2 z where
    "path G q1" "distinct q1" "even (length q1)"
    "path G q2" "distinct q2" "even (length q2)"
    "set q1 \<inter> set q2 = {}" "z \<in> X"
    "set q1 \<union> set q2 = insert z (set q - {x})"
  proof(cases "even (length qs)")
    case True
    show ?thesis
      by (rule that[of qs "rs @ [b]" b]; use True assms(1,2) ear_interior[of G H X a q b] \<open>q = qs @ x # rs\<close>
        \<open>path G (a # qs)\<close> \<open>path G (rs @ [b])\<close> tl_path_is_path[of G "a # qs"]
      in auto)
  next
    case False
    show ?thesis
      by (rule that[of "a # qs" rs a]; use False assms(1,2) ear_interior[of G H X a q b] \<open>q = qs @ x # rs\<close>
        \<open>path G (a # qs)\<close> \<open>path G (rs @ [b])\<close> path_pref[of G rs "[b]"]
      in auto)
  qed
  obtain M N where "graph_matching G M" "Vs M = set q1"
    "graph_matching G N" "Vs N = set q2"
    using even_path_matching[OF \<open>path G q1\<close> \<open>distinct q1\<close> \<open>even (length q1)\<close>]
      even_path_matching[OF \<open>path G q2\<close> \<open>distinct q2\<close> \<open>even (length q2)\<close>]
    by blast
  hence "graph_matching G (M \<union> N)" "Vs (M \<union> N) = insert z (set q - {x})"
    using \<open>set q1 \<inter> set q2 = {}\<close> \<open>set q1 \<union> set q2 = insert z (set q - {x})\<close>
    by (auto simp: vs_union intro!: matching_vertex_disj_union)
  thus ?thesis
    using \<open>z \<in> X\<close>
    by blast
qed

lemma odd_ear_preserves_factor_critical:
  assumes "ear G H X p" "odd (length (edges_of_path p))"
    "\<And>x. x \<in> X \<Longrightarrow> \<exists>M. graph_matching H M \<and> Vs M = X - {x}"
    "x \<in> X \<union> set p"
  shows "\<exists>M. graph_matching G M \<and> Vs M = (X \<union> set p) - {x}"
proof-
  obtain a q b where "p = a # q @ [b]"
    using assms(1)
    by (cases p rule: list_cases_hd_and_last) (auto simp: ear_def)
  have "ear G H X (a # q @ [b])" "even (length q)"
    "H \<subseteq> G" "set q \<inter> X = {}" "a \<in> X" "b \<in> X"
    using assms(1,2) \<open>p = a # q @ [b]\<close>
    by (auto simp: ear_def edges_of_path_length)
  show ?thesis
  proof(cases "x \<in> X")
    case True
    obtain M where "graph_matching H M" "Vs M = X - {x}"
      using assms(3)[of x] True
      by auto
    obtain N where "graph_matching G N" "Vs N = set q"
      using ear_matching_on_interior[of G H X a q b]
        \<open>ear G H X (a # q @ [b])\<close> \<open>even (length q)\<close>
      by auto
    show ?thesis
      using \<open>graph_matching H M\<close> \<open>Vs M = X - {x}\<close>
        \<open>graph_matching G N\<close> \<open>Vs N = set q\<close> \<open>H \<subseteq> G\<close>
        \<open>set q \<inter> X = {}\<close> \<open>a \<in> X\<close> \<open>b \<in> X\<close> \<open>p = a # q @ [b]\<close> True
      by (intro exI[of _ "M \<union> N"]) (auto simp: vs_union intro!: matching_vertex_disj_union)
  next
    case False
    obtain z N where "z \<in> X" "graph_matching G N" "Vs N = insert z (set q - {x})"
      using ear_matching_remove_interior[of G H X a q b x] assms(4) False
        \<open>ear G H X (a # q @ [b])\<close> \<open>even (length q)\<close>
        \<open>a \<in> X\<close> \<open>b \<in> X\<close> \<open>p = a # q @ [b]\<close>
      by auto
    then obtain M where "graph_matching H M" "Vs M = X - {z}"
      using assms(3)[of z]
      by auto
    thus ?thesis
      using \<open>H \<subseteq> G\<close> \<open>set q \<inter> X = {}\<close> \<open>a \<in> X\<close> \<open>b \<in> X\<close>
        \<open>graph_matching G N\<close> \<open>Vs N = insert z (set q - {x})\<close>
        \<open>z \<in> X\<close> \<open>p = a # q @ [b]\<close> False
      by (intro exI[of _ "M \<union> N"]) (auto simp: vs_union intro!: matching_vertex_disj_union)
  qed
qed

lemma odd_ear_decomposition_factor_critical:
  assumes "odd_ear_decomposition G X r Ps" "x \<in> X"
  shows "\<exists>M. graph_matching G M \<and> Vs M = X - {x}"
  using assms(1)[unfolded odd_ear_decomposition_def, THEN conjunct1]
    assms(1)[unfolded odd_ear_decomposition_def, THEN conjunct2] assms(2)
  by (induction arbitrary: x rule: ear_decomposition.induct)
    ((erule odd_ear_preserves_factor_critical; auto) | (force simp: Vs_def))+

lemma ear_decomposition_vertices:
  "ear_decomposition G X r Ps \<Longrightarrow> r \<in> X \<and> Vs G \<subseteq> X \<and> finite X"
  by (induction rule: ear_decomposition.induct)
    (auto simp: vs_union dest: subsetD[OF edges_of_path_Vs])

lemma odd_ear_decomposition_singleton[simp]:
  "odd_ear_decomposition {} {r} r []"
  by (auto simp: odd_ear_decomposition_def intro: ear_decomposition.single_vertex)

subsection \<open>Alternating Paths for Extending a Decomposition\<close>

lemma odd_ear_from_path:
  "\<lbrakk>H \<subseteq> G; Vs H \<subseteq> Y; a \<in> Y; b \<in> Y;
    q \<noteq> []; even (length q); distinct q; set q \<inter> Y = {};
    path G (a # q @ [b])\<rbrakk> \<Longrightarrow>
    ear G H Y (a # q @ [b]) \<and> odd (length (edges_of_path (a # q @ [b])))"
  using path_edges_disjoint_from_old_graph[of q H a b]
  by (cases q rule: list_cases3) (auto simp: ear_def edges_of_path_length)

lemma alternating_path_odd_ear:
  assumes "H \<subseteq> G" "Vs H \<subseteq> Y" "matching M"
    "N \<subseteq> M" "Vs N = Y - {r}" "r \<notin> Vs M"
    "a \<in> Y" "y \<notin> Y" "{a,y} \<in> G"
    "path G p" "distinct p" "rev_alt_path M p" "hd p = y" "last p \<in> Y" "p \<noteq> []"
  shows "\<exists>q N'. ear G H Y q \<and> odd (length (edges_of_path q)) \<and>
    N' \<subseteq> M \<and> N' \<subseteq> set (edges_of_path q) \<and> Vs N' = set q - Y \<and> y \<in> set q"
proof-
  obtain b q s where "p = q @ b # s" "b \<in> Y" "set q \<inter> Y = {}"
    using one_mem_pure_pref[of "last p" p "\<lambda>v. v \<in> Y"] assms(14,15)
    by auto
  have "q \<noteq> []" "distinct q" "hd q = y"
    using assms(8,11,13) \<open>p = q @ b # s\<close> \<open>b \<in> Y\<close>
    by (auto simp: hd_append split: if_splits)
  have "path G (q @ [b])" "rev_alt_path M (q @ [b])" "rev_alt_path M q"
    using assms(10,12) \<open>p = q @ b # s\<close>
      path_pref[of G "q @ [b]" s]
      alt_path_prefix[of "-M" "q @ [b]" s] alt_path_prefix[of "-M" q "b # s"]
    by auto
  have "last (edges_of_path (q @ [b])) \<notin> M"
    using matching_submatching_no_cross[OF assms(3-6) \<open>b \<in> Y\<close>, of "last q"]
      \<open>q \<noteq> []\<close> \<open>set q \<inter> Y = {}\<close> last_edge_is[of "q @ [b]"]
    by (auto simp: insert_commute Suc_le_eq dest: last_in_set)
  hence "even (length q)"
    using alternating_list_odd_last[OF \<open>rev_alt_path M (q @ [b])\<close>]
    by (auto simp: edges_of_path_length)
  have "path G (a # q @ [b])"
    using path_Cons_hd[OF \<open>path G (q @ [b])\<close>, of y a]
      assms(9) \<open>hd q = y\<close> \<open>q \<noteq> []\<close>
    by (auto simp: hd_append)
  hence "ear G H Y (a # q @ [b]) \<and> odd (length (edges_of_path (a # q @ [b])))"
    using assms(1,2,7) \<open>b \<in> Y\<close> \<open>q \<noteq> []\<close> \<open>even (length q)\<close>
      \<open>distinct q\<close> \<open>set q \<inter> Y = {}\<close>
    using odd_ear_from_path[of H G Y a b q]
    by blast
  moreover have "Vs (M \<inter> set (edges_of_path q)) = set q"
    using rev_alt_path_matching_vertices[OF assms(3) \<open>rev_alt_path M q\<close> \<open>even (length q)\<close>] .
  moreover have "set (edges_of_path q) \<subseteq> set (edges_of_path (a # q @ [b]))"
    using edges_of_path_append_subset_2[of q "[b]"] edges_of_path_append_subset[of "q @ [b]" "[a]"]
    by auto
  ultimately show ?thesis
    using assms(7) \<open>b \<in> Y\<close> \<open>set q \<inter> Y = {}\<close> \<open>q \<noteq> []\<close> \<open>hd q = y\<close>
    by (intro exI[of _ "a # q @ [b]"] exI[of _ "M \<inter> set (edges_of_path q)"]) auto
qed

lemma single_edge_ear:
  "\<lbrakk>H \<subseteq> G; Vs H \<subseteq> Y; a \<in> Y; b \<in> Y; a \<noteq> b; {a,b} \<in> G - H\<rbrakk>
    \<Longrightarrow> ear G H Y [a,b]"
  by (auto simp: ear_def Vs_def)

lemma ear_restrict_graph:
  "ear G H X p \<Longrightarrow> ear (H \<union> set (edges_of_path p)) H X p"
  using path_edges_of_path_refl[of p]
  by (auto simp: ear_def intro: path_subset)

lemma ear_edges_nonempty:
  "ear G H X p \<Longrightarrow> set (edges_of_path p) \<noteq> {}"
  using edges_of_path_length[of p]
  by (auto simp: ear_def)

lemma odd_ear_decomposition_add:
  "\<lbrakk>odd_ear_decomposition H X r Ps; ear G H X p; odd (length (edges_of_path p))\<rbrakk>
    \<Longrightarrow> odd_ear_decomposition (H \<union> set (edges_of_path p)) (X \<union> set p) r (Ps @ [p])"
  by (auto simp: odd_ear_decomposition_def intro: ear_decomposition.add_ear ear_restrict_graph)

lemma factor_critical_extending_ear:
  assumes "graph_invar G" "Vs G \<subseteq> X"
    "\<And>x. x \<in> X \<Longrightarrow> \<exists>L. graph_matching G L \<and> Vs L = X - {x}"
    "graph_matching G M" "Vs M = X - {r}"
    "H \<subset> G" "Vs H \<subseteq> Y" "Y \<subseteq> X" "r \<in> Y" "N \<subseteq> M" "Vs N = Y - {r}"
  shows "\<exists>p N'. ear G H Y p \<and> odd (length (edges_of_path p)) \<and>
    N' \<subseteq> M \<and> N' \<subseteq> set (edges_of_path p) \<and> Vs N' = set p - Y"
proof(cases "Y = X")
  case True
  obtain a b where "a \<noteq> b" "{a,b} \<in> G - H"
    using assms(1,6)
    by (fastforce simp: psubset_eq)
  thus ?thesis
    using assms(2,6,7) True
    by (intro exI[of _ "[a,b]"] exI[of _ "{}"])
      (auto simp: Vs_def intro!: single_edge_ear)
next
  case False
  obtain a y where "a \<in> Y" "y \<notin> Y" "{a,y} \<in> G"
    using factor_critical_crossing_edge[OF assms(1-3,9)] assms(8) False
    by blast
  hence "y \<in> X" "y \<noteq> r"
    using assms(2,9)
    by (auto simp: Vs_def)
  obtain p where "path G p" "distinct p" "alt_path M p"
    "odd (length p)" "hd p = r" "last p = y"
    using factor_critical_even_path[OF assms(1,2,4,5,3) \<open>y \<in> X\<close> \<open>y \<noteq> r\<close>]
    by blast
  hence "rev_alt_path M (rev p)"
    using rev_of_rev_alt_path_is_alt_path[of "-M" p]
    by simp
  moreover have "path G (rev p)" "distinct (rev p)" "hd (rev p) = y"
    "last (rev p) \<in> Y" "rev p \<noteq> []"
    using \<open>path G p\<close> \<open>distinct p\<close> \<open>odd (length p)\<close>
      \<open>hd p = r\<close> \<open>last p = y\<close> assms(9)
    by (auto simp: rev_path_is_path_iff hd_rev last_rev)
  ultimately show ?thesis
    using alternating_path_odd_ear[of H G Y M N r a y "rev p"]
      assms(4-7,10,11) \<open>a \<in> Y\<close> \<open>y \<notin> Y\<close> \<open>{a,y} \<in> G\<close>
    by blast
qed

subsection \<open>Lovasz's Odd Ear Decomposition Theorem\<close>

lemma factor_critical_odd_ear_decomposition:
  assumes "graph_invar G" "Vs G \<subseteq> X" "r \<in> X"
    "\<And>x. x \<in> X \<Longrightarrow> \<exists>M. graph_matching G M \<and> Vs M = X - {x}"
  shows "\<exists>Ps. odd_ear_decomposition G X r Ps"
proof-
  obtain M where "graph_matching G M" "Vs M = X - {r}"
    using assms(3,4)
    by blast
  have "\<exists>Qs. odd_ear_decomposition G X r Qs"
    if "H \<subseteq> G" "Y \<subseteq> X" "odd_ear_decomposition H Y r Ps"
      "N \<subseteq> M" "Vs N = Y - {r}" for H Y Ps N
    using that
  proof(induction H arbitrary: Y Ps N rule: measure_induct_rule[where f="\<lambda>H. card (G - H)"])
    case (less H)
    have "r \<in> Y" "Vs H \<subseteq> Y"
      using less.prems(3) ear_decomposition_vertices[of H Y r Ps]
      by (auto simp: odd_ear_decomposition_def)
    show ?case
    proof(cases "H = G")
      case True
      have "Y = X"
        using less.prems(2) \<open>r \<in> Y\<close> \<open>Vs H \<subseteq> Y\<close>          \<open>Vs M = X - {r}\<close> Vs_subset[OF \<open>graph_matching G M\<close>[THEN conjunct2]] True
        by blast
      thus ?thesis
        using less.prems(3) True
        by blast
    next
      case False
      obtain p N' where "ear G H Y p" "odd (length (edges_of_path p))"
        "N' \<subseteq> M" "N' \<subseteq> set (edges_of_path p)" "Vs N' = set p - Y"
        using factor_critical_extending_ear[OF assms(1,2,4)
          \<open>graph_matching G M\<close> \<open>Vs M = X - {r}\<close>, of H Y N]
          less.prems \<open>r \<in> Y\<close> \<open>Vs H \<subseteq> Y\<close> False
        by blast
      have "set (edges_of_path p) \<subseteq> G"
        "set (edges_of_path p) \<subseteq> G - H" "set p \<subseteq> X"
        using \<open>ear G H Y p\<close> assms(2) path_edges_subset[of G p] subset_path_Vs[of G p]
        by (auto simp: ear_def)
      hence "card (G - (H \<union> set (edges_of_path p))) < card (G - H)"
        using graph_invar_finite[OF assms(1)] ear_edges_nonempty[OF \<open>ear G H Y p\<close>]
        by (cases "edges_of_path p"; intro psubset_card_mono) (auto simp: psubset_eq)
      moreover have "odd_ear_decomposition (H \<union> set (edges_of_path p)) (Y \<union> set p) r (Ps @ [p])"
        using odd_ear_decomposition_add[OF less.prems(3)
          \<open>ear G H Y p\<close> \<open>odd (length (edges_of_path p))\<close>] .
      ultimately show ?thesis
        using less.IH[of "H \<union> set (edges_of_path p)" "Y \<union> set p" "Ps @ [p]" "N \<union> N'"]
          less.prems \<open>set (edges_of_path p) \<subseteq> G\<close> \<open>set p \<subseteq> X\<close>
          \<open>N' \<subseteq> M\<close> \<open>Vs N' = set p - Y\<close> \<open>r \<in> Y\<close>
        by (auto simp: vs_union)
    qed
  qed
  from this[of "{}" "{r}" "[]" "{}"] show ?thesis
    using assms(3)
    by (auto simp: Vs_def)
qed

text \<open>The initial vertex may be chosen arbitrarily in \<open>X\<close>.
  The matching condition is the same one used for the factor-critical
  components of the Edmonds-Gallai decomposition. The explicit vertex
  set also includes the singleton case, whose induced edge set is empty.\<close>

theorem lovasz_odd_ear_decomposition:
  assumes "graph_invar G" "r \<in> X"
  shows "(\<forall>x \<in> X. \<exists>M. graph_matching (G \<lbrakk>X\<rbrakk>) M \<and> Vs M = X - {x})
    \<longleftrightarrow> (\<exists>Ps. odd_ear_decomposition (G \<lbrakk>X\<rbrakk>) X r Ps)"
  using assms graph_inter_Vs_subset(2)[of G X] graph_invar_graph_inter_Vs[of G X]
  by (auto intro!: factor_critical_odd_ear_decomposition dest: odd_ear_decomposition_factor_critical)

end



