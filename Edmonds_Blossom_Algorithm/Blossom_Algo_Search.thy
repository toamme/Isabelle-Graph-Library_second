theory Blossom_Algo_Search              
  imports Graph_Algorithms_Dev.Parent_Map Blossom_Algo_Compute_Aug_Path 
          Basic_Matching.Alternating_Forest_Executable
begin                                                        

subsection \<open>Main Search Procedure: Finding Alternating Paths\<close>

subsubsection \<open>Modelling the Search Procedure as a Recursive Function\<close> 

locale compute_alt_path = match G M + choose sel 
+ alternating_forest_ordinary_extension_spec 
  where abstract_forest= abstract_forest and evens = evens
for abstract_forest::"'F \<Rightarrow> 'a set set" and evens::"'F \<Rightarrow> 'vset"
and G M::"'a set set" and sel::"'a set \<Rightarrow> 'a" +
fixes unmatcheds::'vset
assumes unmatcheds: "vset_invar unmatcheds" "vset_to_set unmatcheds =  Vs G  - Vs M"
begin

notation abstract_forest ("\<lbrace> _ \<rbrace>")

abbreviation "aevens F \<equiv> vset_to_set (evens F)"
abbreviation "aodds F \<equiv> vset_to_set (odds F)"
abbreviation "aroots F \<equiv> vset_to_set (roots F)"
abbreviation "FVs F \<equiv> Vs (\<lbrace>F\<rbrace>)"

text \<open>At this stage we don't want t assume that the vertices have any ordering.\<close>

definition "if1_cond F = 
      (\<exists>v1 v2. {v1, v2} \<in> G - \<lbrace>F\<rbrace> \<and> v1 \<in> aevens F \<and> v2 \<notin> FVs F \<and> (\<exists>v3. {v2, v3} \<in> M))"


definition if1 where (*I am using this because when the RHS is in the function the function package messes up the pairing.*)
  "if1 F v1 v2 v3 = ({v1, v2} \<in> G - \<lbrace>F\<rbrace> \<and> v1 \<in> aevens F \<and> v2 \<notin> FVs F \<and> {v2, v3} \<in> M)"

interpretation matching_graph: graph_abs M
  apply(unfold_locales)
  using graph_invar_subset[OF graph matching(2)] .

definition 
  "sel_if1 F = 
     (let es = D \<inter> {(v1,v2)| v1 v2. {v1, v2} \<in> G - \<lbrace>F\<rbrace> \<and> v1 \<in> aevens F \<and> v2 \<notin> FVs F \<and> (\<exists>v3. {v2, v3} \<in> M) \<and> v2 \<in> Vs M};
         (v1,v2) = sel_pair es;
         v3 = sel (Undirected_Set_Graphs.neighbourhood M v2)
     in (v1,v2,v3))"

definition if2_cond where "if2_cond F =
   (\<exists>v1 v2. {v1, v2} \<in> G \<and> v1 \<in> aevens F \<and> v2 \<in> aevens F)"

definition if2 where 
  "if2 F v1 v2 = ({v1, v2} \<in> G \<and> v1 \<in> aevens F \<and> v2 \<in> aevens F)"

definition 
  "sel_if2 F = 
     (let es = D \<inter> {(v1,v2)| v1 v2. {v1, v2} \<in> G \<and> v1 \<in> aevens F \<and> v2 \<in> aevens F};
         (v1,v2) = sel_pair es
     in (v1,v2))"

(*definition if1_1_cond where "if1_1_cond flabel v2 \<equiv> flabel v2 = None \<and> (\<exists>v3. {v2, v3} \<in> M)"*)

function (domintros) compute_alt_path:: "'F \<Rightarrow> (('a list \<times> 'a list) option)" where
  "compute_alt_path F = 
    (if if1_cond F then
       let
         (v1,v2,v3) = sel_if1 F;
          F' = extend_forest_even_unclassified F v1 v2 v3;
         return = compute_alt_path F'
       in
         return
     else if if2_cond F then
        let
          (v1,v2) = sel_if2 F; 
          return = Some (get_path F v1, get_path F v2)
        in
          return
     else
       let
          return = None
       in
         return)"
  by pat_completeness auto

subsubsection \<open>Reasoning Infrastructure\<close>

lemma if1_cond_props:
  "if1_cond F \<Longrightarrow> (\<exists>v1 v2. {v1, v2} \<in> G - \<lbrace>F\<rbrace> \<and> v1 \<in> aevens F \<and> v2 \<notin> FVs F \<and> (\<exists>v3. {v2, v3} \<in> M))"
  unfolding if1_cond_def
  .

lemma if1_cond_props':
  "if1_cond F \<Longrightarrow> (\<exists>v1 v2 v3. if1 F v1 v2 v3)"
  unfolding if1_cond_def if1_def by simp

lemma if2_cond_props:
  "if2_cond F \<Longrightarrow> (\<exists>v1 v2. {v1, v2} \<in> G \<and> v1 \<in> aevens F \<and> v2 \<in> aevens F)"
  unfolding if2_cond_def if2_def
  .

lemma if1_props:
  assumes "if1 F v1 v2 v3"
  shows 
    "{v1, v2} \<in> G - \<lbrace>F\<rbrace>" "v1 \<in>  aevens F" "v2 \<notin> FVs F" "{v2, v3} \<in> M"
  using assms
  unfolding if1_def 
  by auto

lemma if1_cond_props'':
  assumes "if1_cond F"
  obtains v1 v2 v3 where "if1 F v1 v2 v3"
  using assms(1)
  unfolding if1_cond_def if1_def
  by (smt surj_pair)


lemma if1_cond_props''':
  assumes "if1_cond F" "(v1, v2, v3) = sel_if1 F"
  shows "if1 F v1 v2 v3"
proof-

  have "case (sel_if1 F) of (v1,v2,v3) \<Rightarrow> if1 F v1 v2 v3"
  proof-
    let ?es = "D \<inter> {(v1,v2)| v1 v2. {v1, v2} \<in> G - \<lbrace>F\<rbrace> 
                   \<and> v1 \<in> aevens F \<and> v2 \<notin> FVs F \<and> (\<exists>v3. {v2, v3} \<in> M) \<and> v2 \<in> Vs M}"
    have "?es\<noteq>{}"
      using assms 
      apply (clarsimp elim!: if1_cond_props'' simp: sel_if1_def edge_iff_edge_1 if1_def insert_commute split: prod.split)
      using insert_commute
      by blast
    moreover have "finite ?es"
      using Vs_eq_dVs finite_Vs finite_vertices_iff
      by fastforce
    ultimately have "sel_pair ?es \<in> ?es"
      by force
    moreover obtain v1 v2 where "sel_pair ?es = (v1,v2)"
      by (cases "sel_pair ?es") auto
    ultimately have "(Undirected_Set_Graphs.neighbourhood M v2) \<noteq> {}"
      using assms \<open>?es \<noteq> {}\<close> matching_graph.vs_member'
      by (auto elim!: if1_cond_props''
               simp: sel_if1_def edge_iff_edge_1 if1_def Undirected_Set_Graphs.neighbourhood_def 
               split: prod.split)
    moreover have "finite (Undirected_Set_Graphs.neighbourhood M v2)"
      by (meson matching_graph.graph neighbourhood_subset_Vs rev_finite_subset)
    ultimately have "sel (Undirected_Set_Graphs.neighbourhood M v2) \<in> (Undirected_Set_Graphs.neighbourhood M v2)"
      by (auto simp add: sel)
    hence "{v2, sel (Undirected_Set_Graphs.neighbourhood M v2)} \<in> M"
      by auto

    moreover have "v1 \<in> aevens F"
      using \<open>sel_pair ?es \<in> ?es\<close> \<open>sel_pair ?es = (v1, v2)\<close>
      by auto

    ultimately show ?thesis
      using \<open>sel_pair ?es \<in> ?es\<close> \<open>sel_pair ?es = (v1, v2)\<close> \<open>if1_cond F\<close>
      by(auto simp: sel_if1_def if1_def)
  qed
  thus ?thesis
    using assms(2)
    by auto
qed

lemma if1_cond_props'''':
  assumes "if1_cond F"
  shows "\<exists>v1 v2 v3 . (v1, v2, v3) = sel_if1 F \<and> if1 F v1 v2 v3"
proof-
  let ?q = "sel_if1 F"
  have "(fst ?q, fst (snd ?q), snd (snd ?q)) = ?q"
    by simp
  then show ?thesis
    using if1_cond_props'''[OF assms]
    by metis
qed

lemma if2_cond_props'':
  assumes "if2_cond F"
  obtains v1 v2 where "if2 F v1 v2"
  using assms(1)
  unfolding if2_cond_def if2_def
  by (smt surj_pair)

lemma if2_cond_props''':
  assumes "if2_cond F" "(v1, v2) = sel_if2 F"
  shows "if2 F v1 v2 "
proof-

  have "case (sel_if2 F) of (v1,v2) \<Rightarrow> if2 F v1 v2"
  proof-
    let ?es = " D \<inter> {(v1,v2)| v1 v2. {v1, v2} \<in> G \<and> v1 \<in> aevens F \<and> v2 \<in> aevens F}"
    have "?es\<noteq>{}"
      using assms 
      by (auto elim!: if2_cond_props'' simp: sel_if2_def edge_iff_edge_1 if2_def insert_commute split: prod.split)
    moreover have "finite ?es"
      using Vs_eq_dVs finite_Vs finite_vertices_iff
      by fastforce
    ultimately have "sel_pair ?es \<in> ?es"
      by force
    moreover obtain v1 v2 where "sel_pair ?es = (v1,v2)"
      by (cases "sel_pair ?es") auto
  

    moreover have "v1 \<in> aevens F" "v2 \<in> aevens F"
      using \<open>sel_pair ?es \<in> ?es\<close> \<open>sel_pair ?es = (v1, v2)\<close>
      by auto
    ultimately show ?thesis
      using \<open>sel_pair ?es \<in> ?es\<close> \<open>sel_pair ?es = (v1, v2)\<close> \<open>if2_cond F\<close>
      by(auto simp: sel_if2_def if2_def)
  qed

  thus ?thesis
    using assms(2)
    by force
qed

lemma if2_cond_props'''':
  assumes "if2_cond F"
  shows "\<exists>v1 v2 . (v1, v2) = sel_if2 F \<and> if2 F v1 v2"
proof-
  let ?q = "sel_if2 F"
  have "(fst ?q, snd ?q) = ?q"
    by simp
  then show ?thesis
    using if2_cond_props'''[OF assms]
    by metis
qed


lemma compute_alt_path_if1:
  assumes "compute_alt_path_dom F" 
    "if1_cond F"
    "(v1, v2, v3) = sel_if1 F"
    "F' = extend_forest_even_unclassified F v1 v2 v3"
  shows "compute_alt_path F = compute_alt_path F'"
  using assms
  by (auto simp add: compute_alt_path.psimps[OF assms(1)] Let_def split: if_splits prod.splits)

lemma compute_alt_path_pinduct_2':
  assumes "compute_alt_path_dom F"
  "(\<And>F. compute_alt_path_dom F \<Longrightarrow>
    (\<And>v1 v2 v3 F'.
        \<lbrakk>if1_cond F; (v1,v2,v3) = sel_if1 F; F' = extend_forest_even_unclassified F v1 v2 v3\<rbrakk> \<Longrightarrow> P F')
       \<Longrightarrow> P F)"
  shows "P F"
  apply(rule compute_alt_path.pinduct[OF assms(1)])
  using assms(2)
  by metis

lemma compute_alt_path_pinduct_2:
  "compute_alt_path_dom F \<Longrightarrow> 
  (\<And>F. compute_alt_path_dom F \<Longrightarrow>
    (\<And>v1 v2 v3 F'.
        \<lbrakk>if1_cond F; (v1,v2,v3) = sel_if1 F; F' = extend_forest_even_unclassified F v1 v2 v3\<rbrakk>
       \<Longrightarrow> P F') \<Longrightarrow>
    P F) \<Longrightarrow> P F"
  apply (rule compute_alt_path_pinduct_2')
  by metis+

lemma if_1_forest_extension_precond:
  "\<lbrakk>forest_invar M F; if1 F v1 v2 v3\<rbrakk> \<Longrightarrow> forest_extension_precond F M v1 v2 v3"
proof(rule forest_extension_precondI, goal_cases)
  case 3
  then show ?case 
    using  evens_and_odds(3)[of M F] higher_forest_properties(2)[of M F v2 v3] 
    by(auto simp add: if1_def)
next
  case 4
  then show ?case
    using evens_and_odds(3)[of M F] higher_forest_properties(2)[of M F v1 v2]
    by(auto simp add: if1_def)
next
  case 7
  then show ?case 
    by (simp add: graph_abs.edge_iff_edge_1 graph_abs_axioms if1_def no_self_loops_2)
next
  case 8
  then show ?case 
    using if1_props(4) by fastforce
next
  case 9
  then show ?case 
    using
        evens_and_odds(3)[of M F] higher_forest_properties(2)[of M F v1 v2]
    by(auto simp add: if1_def insert_commute)
qed (simp_all add: if1_props  matching(1))

subsubsection \<open>Termination of the Search Procedure\<close>

definition "compute_alt_path_meas F = card (G - \<lbrace>F\<rbrace>)"

lemma compute_alt_path_dom:
  assumes "finite \<lbrace>F\<rbrace>" "\<lbrace>F\<rbrace> \<subseteq> G" "forest_invar M F"
  shows "compute_alt_path_dom F"
  using assms
proof(induction "compute_alt_path_meas F" arbitrary: F rule: nat_less_induct)
  case 1
  then have IH: "compute_alt_path_dom F'"
    if "compute_alt_path_meas F' < compute_alt_path_meas F" "finite \<lbrace>F'\<rbrace>" "\<lbrace>F'\<rbrace> \<subseteq> G"
       "forest_invar M F'"
    for F'
    using that
    by simp

  show ?case
  proof (cases "if1_cond F")
    case True
    {
      fix v1 v2 v3
      assume "(v1, v2, v3) = sel_if1 F"
      then have "if1 F v1 v2 v3"
        by(rule if1_cond_props'''[OF True])
      then have  v1v2: "{v1, v2} \<in> G - \<lbrace>F\<rbrace>" "{v2, v3} \<in> M"  "v1 \<in> aevens F" "v2 \<notin> FVs F"
        by(rule if1_props)+
      then have "{v1, v2} \<in> G" "{v1, v2} \<notin> \<lbrace>F\<rbrace>"
        by simp+
      define F' where "F' = extend_forest_even_unclassified F v1 v2 v3"

      have precd:"forest_extension_precond F M v1 v2 v3"
        by (simp add: "1.prems"(3) \<open>if1 F v1 v2 v3\<close> if_1_forest_extension_precond)
      note F'_props = forest_extend[OF precd, folded F'_def]
      have "{v1, v2} \<notin> G - insert {v1, v2} (insert {v2, v3} \<lbrace> F \<rbrace>)" 
        by simp
      moreover have  "G - insert {v1, v2} (insert {v2, v3} \<lbrace> F \<rbrace>) \<subseteq> G - \<lbrace> F \<rbrace>"
        by auto
      ultimately have "G - insert {v1, v2} (insert {v2, v3} \<lbrace> F \<rbrace>) \<subset> G - \<lbrace> F \<rbrace>"
        using v1v2 by auto
     hence measure_decr:"compute_alt_path_meas F' < compute_alt_path_meas F"
       by(auto intro!: psubset_card_mono 
             simp add: compute_alt_path_meas_def F'_props(2) finite_E)
     hence "compute_alt_path_dom F'"
       using F'_props(1,2) finite_forest(3)[of M F'] "1.prems"(2) \<open>{v1, v2} \<in> G\<close> matching(2) v1v2(2) 
       by (auto intro!: IH)
    }
    then show ?thesis
      using compute_alt_path.domintros
      by metis
  next
    case False
    then show ?thesis
      apply(subst compute_alt_path.domintros)
      by blast+
  qed
qed

subsection \<open>General Soundness\<close>

lemma compute_alt_path_from_tree_1:
  assumes invars: "forest_invar M F"
  and ret:"compute_alt_path F = Some (p1, p2)" 
  and init: "finite \<lbrace>F\<rbrace>" "\<lbrace>F\<rbrace> \<subseteq> G"
  shows "last p1 \<notin> Vs M \<and>
       last p2 \<notin> Vs M \<and>
       hd p1 \<noteq> hd p2 \<and>
       odd (length p1) \<and>
       odd (length p2) \<and>
       distinct p1 \<and>
       distinct p2 \<and>
       path G p1 \<and>
       path G p2 \<and>
       {hd p1, hd p2} \<in> G \<and>
       (\<forall>x pref1 post1 pref2 post2. p1 = pref1 @ x # post1 \<and> p2 = pref2 @ x # post2 \<longrightarrow> post1 = post2) \<and>
       alt_path M (hd p1 # p2) \<and> 
       alt_path M (hd p2 # p1)" 
  using assms
proof(induction F arbitrary: p1 p2 rule: compute_alt_path_pinduct_2)
  case 1
  then show ?case
    by(intro compute_alt_path_dom init invars)
next
  case (2 F p1 p2)
  show ?case
  proof(cases "if1_cond F")
    case True
    obtain v1 v2 v3 where sel: "(v1,v2,v3) = sel_if1 F" "if1 F v1 v2 v3"
      using if1_cond_props''''[OF True] by metis
    hence  v1v2: "{v1, v2} \<in> G - \<lbrace>F\<rbrace>" "{v2, v3} \<in> M"  "v1 \<in> aevens F" "v2 \<notin> FVs F"
        using if1_props by auto
      then have "{v1, v2} \<in> G" "{v1, v2} \<notin> \<lbrace>F\<rbrace>"
        by simp+
      define F' where "F' = extend_forest_even_unclassified F v1 v2 v3"

      have precd:"forest_extension_precond F M v1 v2 v3"
        by (simp add: 2(3) \<open>if1 F v1 v2 v3\<close> if_1_forest_extension_precond)
      note F'_props = forest_extend[OF precd, folded F'_def]
      have "forest_invar M (extend_forest_even_unclassified F v1 v2 v3)"
        using F'_def F'_props(1) by blast
      moreover have "compute_alt_path (extend_forest_even_unclassified F v1 v2 v3) = Some (p1, p2)"
        using "2.hyps" "2.prems"(2) True compute_alt_path_if1 sel(1) by force
      moreover have "finite \<lbrace> extend_forest_even_unclassified F v1 v2 v3 \<rbrace>"
        using calculation(1) finite_forest(3) by auto
      moreover have "\<lbrace> extend_forest_even_unclassified F v1 v2 v3 \<rbrace> \<subseteq> G"
        using "2.prems"(4) F'_def F'_props(2) \<open>{v1, v2} \<in> G\<close> matching(2) v1v2(2) by auto
    ultimately show ?thesis
      by(rule 2(2)[OF True sel(1) refl])
  next
    case False
    then have if2_holds: "if2_cond F"
      using 2(4)
      by(auto simp add: compute_alt_path.psimps[OF 2(1)] split: if_splits prod.splits)
    then obtain v1 v2  where v1v2r: "(v1,v2) = sel_if2 F" "if2 F v1 v2"
      using if2_cond_props''''
      by force
    hence s: "v1 \<in> aevens F" "p1 = get_path F v1" "v2 \<in> aevens F" "p2 = get_path F v2" "{v1, v2} \<in> G"
      unfolding if2_def
      using False 2(4) v1v2r(1)
      by (auto simp add: compute_alt_path.psimps[OF 2(1)] Let_def split: if_splits prod.splits)
    note p1_props = get_path[OF 2(3) s(1,2)]
    note p2_props = get_path[OF 2(3) s(3,4)]
    have v1v2_not_in_M: "{v1, v2} \<notin> M"
    proof(rule ccontr, goal_cases)
      case 1
      have "{v1, v2} \<inter> (FVs F \<union> vset_to_set (roots F)) \<noteq> {}"
        using "2.prems"(1) evens_and_odds(3) s(1) by auto
      hence "{v1, v2} \<in> \<lbrace> F \<rbrace>"
        using higher_forest_properties(2)[OF 2(3), of v1 v2] 1 by auto
      thus False
        using higher_forest_properties(3)[OF 2(3), of v1 v2]
              "2.prems"(1) evens_and_odds(4) s(1,3) 
        by auto
    qed
    have "v1 = hd p1" "v2 = hd p2"
      using get_path[OF 2(3), of v1 p1] get_path[OF 2(3), of v2 p2] s walk_reflexive'
      by(unfold walk_betw_def) force+
    hence "hd p1 \<noteq> hd p2" "{hd p1, hd p2} \<in> G"
      using edge_iff_edge_1 no_self_loops_2 s(5) by presburger+
    moreover have "\<lbrakk>p1 = pref1 @ x # post1; p2 = pref2 @ x # post2\<rbrakk>\<Longrightarrow> post1 = post2"
      for x pref1 post1 pref2 post2
      by(auto intro!: get_path_prefices[OF 2(3), of pref1 x post1 v1 pref2 post2 v2]
              simp add: s(2,4)) 
    moreover have "last p1 \<notin> Vs M" "odd (length p1)" "distinct p1"
      using p1_props roots(3)[OF 2(3)]
      by auto
    moreover have "path G p1"
      using edges_are_Vs[OF s(5)] p1_props roots(3)[OF 2(3)] graph_abs_axioms 2(6)
      by(cases "p1 = [v1]")
        (auto intro: path_subset[of "\<lbrace>F\<rbrace>" _ G]
                     graph_abs.walk_between_nonempty_path'(1)[of "\<lbrace>F\<rbrace>"] graph_abs_subset)
    moreover have "last p2 \<notin> Vs M" "odd (length p2)" "distinct p2"
      using p2_props roots(3)[OF 2(3)]
      by auto
    moreover have "path G p2"
      using edges_are_Vs_2[OF s(5)] p2_props roots(3)[OF 2(3)] graph_abs_axioms 2(6)
      by(cases "p2 = [v2]")
        (auto intro: path_subset[of "\<lbrace>F\<rbrace>" _ G]
                     graph_abs.walk_between_nonempty_path'(1)[of "\<lbrace>F\<rbrace>"] graph_abs_subset)
    moreover have "alt_path M (hd p1 # p2)"
      using \<open>v1 = hd p1\<close> \<open>v2 = hd p2\<close> v1v2_not_in_M p2_props
      by(auto intro!: nin_M_alt_path)
    moreover have "alt_path M (hd p2 # p1)"
      using \<open>v1 = hd p1\<close> \<open>v2 = hd p2\<close> v1v2_not_in_M p1_props
      by(auto intro!: nin_M_alt_path simp add: insert_commute)
    ultimately show ?thesis
      by auto
  qed
qed

subsection \<open>General Completeness\<close>

lemma what_if_search_fails:
  assumes "compute_alt_path F = None"
   and     init: "finite \<lbrace>F\<rbrace>" "\<lbrace>F\<rbrace> \<subseteq> G"
   and invars: "forest_invar M F"
 shows "\<exists> F'. \<not> if1_cond F' \<and> \<not> if2_cond F' \<and> forest_invar M F' \<and> aroots F' = aroots F"
  using assms(1) invars
proof(induction F rule: compute_alt_path_pinduct_2)
  case 1
  then show ?case
    by(intro compute_alt_path_dom init invars)
next
  case (2 F)
  note IH = this
  show ?case
  proof(cases "if1_cond F")
    case True
    obtain v1 v2 v3 where sel: "(v1,v2,v3) = sel_if1 F" "if1 F v1 v2 v3"
      using if1_cond_props''''[OF True] by metis
    hence  v1v2: "{v1, v2} \<in> G - \<lbrace>F\<rbrace>" "{v2, v3} \<in> M"  "v1 \<in> aevens F" "v2 \<notin> FVs F"
        using if1_props by auto
      then have "{v1, v2} \<in> G" "{v1, v2} \<notin> \<lbrace>F\<rbrace>"
        by simp+
      define F' where "F' = extend_forest_even_unclassified F v1 v2 v3"

      have precd:"forest_extension_precond F M v1 v2 v3"
        by (simp add: 2(4) \<open>if1 F v1 v2 v3\<close> if_1_forest_extension_precond)
      note F'_props = forest_extend[OF precd, folded F'_def]
      show ?thesis
        using IH(3)
        by(auto intro!: IH(2)[OF True sel(1) F'_def] 
              simp add: F'_props(5)[symmetric]
                        compute_alt_path_if1[OF IH(1) True sel(1) F'_def] F'_props(1))
  next
    case False
    note false = this
    show ?thesis
    proof(cases "if2_cond F")
      case True
      hence False
        using IH(3) false
        by(subst (asm) compute_alt_path.psimps[OF IH(1)], cases "sel_if2 F")
          (auto dest!:  if2_cond_props'''') 
      thus ?thesis
        by simp
  next
    case False
    thus ?thesis
      using false
      by(auto intro!: exI[of _ F] exI[of _ F] simp add: IH(4-))
  qed
qed
qed

text \<open>Central lemma for completeness proof:
 On M-alternating paths with the first vertex being unmatched,
labels alternate between Even and Odd, starting with Even.\<close>

lemma termination_conditions_alt_paths_alternating_labels:
  assumes  "\<not> if1_cond F" "\<not> if2_cond F" "forest_invar M F" "Vs G - Vs M \<subseteq> aevens F"
       "alt_path M (p1)" "length (p1) \<ge> 1" "hd (p1) \<notin> Vs M" 
        "l = length p1" "set (p1) \<subseteq> Vs G" "set (edges_of_path p1) \<subseteq> G"
  shows "alt_list (\<lambda> x. x \<in> aevens F) (\<lambda> x. x \<in> aodds F) p1"
  using assms(5-)
proof(induction l arbitrary: p1 rule: less_induct)
  case (less l)
  show ?case
  proof(cases l)
    case 0
    then show ?thesis
      by (simp add: alt_list_empty less.prems(4))
  next
    case (Suc ll)
    note suc = Suc
    then obtain p11 x where p1_split_off_last:"p1 = p11@[x]"
      using less.prems(4) by(cases p1 rule: rev_cases) auto
    show ?thesis 
    proof(cases ll)
      case 0
      hence p1_is:"p1 = [x]" and "x \<notin> Vs M" "x \<in> Vs G"
        using less.prems(3,4,5) p1_split_off_last suc by auto
      hence "x \<in> aevens F"
        using assms(4) less(6) p1_is by auto
      then show ?thesis 
        by(auto simp add: p1_is intro!: alt_list.intros)
    next
      case (Suc nat)
      then obtain p12 y where p11_split_off_last: "p11 = p12@[y]"
        using less.prems(4) p1_split_off_last suc by(cases p11 rule: rev_cases) auto
      hence p1_is: "p1 = p12@[y, x]"
        by (simp add: p1_split_off_last)
      have alt_path_p11:      "alt_path M p11"
       and hd_p1_not_matched: "hd p11 \<notin> Vs M" 
        using  alt_list_append_1 less.prems(1-6)  p11_split_off_last p1_split_off_last 
              edges_of_path_append_3[of "p12@[y]" "[x]", simplified] hd_append2[of p11 "[x]"] 
        by auto     
      have p11_length: "1 \<le> length p11"
          using less.prems(3) p1_split_off_last 
          by(simp add: p11_split_off_last)
      have IH_applied:
       "alt_list (\<lambda>x. x \<in> aevens F) (\<lambda>x. x \<in> aodds F) p11"
        using suc less.prems(4,5,6) p11_length edges_of_path_append_subset_2 p1_split_off_last 
        by (intro less(1)[of ll p11, OF _ alt_path_p11, OF _ _  hd_p1_not_matched]) auto
      hence either_odd_or_even:
         "\<And> y . y \<in> set p11 \<Longrightarrow> y \<in> aevens F = (y \<notin> aodds F)"
        using assms(3) by(auto dest!: alt_list_or evens_and_odds(4))
      hence y_label_or: "y \<in> aevens F \<or> y \<in> aodds F"
        using p11_split_off_last alt_list_or[OF IH_applied(1), of y] by auto
      show ?thesis 
      proof(cases "{y, x} \<in> M")
        case True
        note xy_in_M = this
        show ?thesis
        proof(cases rule: disjE[OF y_label_or], goal_cases)
          case 1
          hence x_Odd:"x \<in> aodds F"
            using xy_in_M evens_and_odds(3)[OF assms(3)] higher_forest_properties(2,3)[OF assms(3)]
            by blast
          show ?case
            using IH_applied either_odd_or_even 1 x_Odd 
            by(auto intro!: alt_list_last_known_append_one(1)[of _ _ "p12@[y]" x, simplified]
                  simp add: p1_split_off_last p11_split_off_last)
        next
          case 2
          hence x_Even:"x \<in> aevens F"
            using xy_in_M evens_and_odds(3)[OF assms(3)] 
                  higher_forest_properties(2,3)[OF assms(3), of x y]
            by(auto simp add: insert_commute)
          show ?case
            using IH_applied either_odd_or_even 2 x_Even 
            by(auto intro!: alt_list_last_known_append_one(2)[of _ _ "p12@[y]" x, simplified]
                  simp add: p1_split_off_last p11_split_off_last)
        qed
        next
          case False
          note yx_not_matching = this
          moreover have "alt_path M (p12@[y,x])"
            using less.prems(1) p1_is by simp
          ultimately have odd_edge_length: "odd (length (edges_of_path (p12@[y,x])))"
            using alternating_list_even_last edges_of_path_snoc_2[of p12 y x]
            by fastforce
          hence even_edge_length:"even (length (p12@[y,x]))" "odd (length (p12@[y]))"
                 "even (length p12)"
            unfolding edges_of_path_length even_Suc[symmetric]
            by auto
           hence y_Even: "y \<in> aevens F"
             using last_odd_P2[OF IH_applied(1), simplified p11_split_off_last]
             by auto
           show ?thesis
           proof(cases "{y, x} \<in> \<lbrace>F\<rbrace>")
             case True
             hence x_Odd: "x \<in> aodds F"
               using y_Even assms(4)  assms(3) higher_forest_properties(3) by force     
             show ?thesis 
               using IH_applied either_odd_or_even y_Even x_Odd 
               by(auto intro!: alt_list_last_known_append_one(1)[of _ _ "p12@[y]" x, simplified]
                     simp add: p1_split_off_last p11_split_off_last)
           next
             case False
             note false = False
             have yx_in_G:"{x, y} \<in> G"
               using  edges_of_path_append_2'[of "[y,x]" p12] less.prems(6) 
               by (fastforce simp add:  p1_is)
             show ?thesis 
             proof(cases "\<exists> e \<in> M. x \<in> e")
               case True
               then obtain v1 v2 where v1v2:"{v1, v2} \<in> M" "x \<in> {v1, v2}"
                 using matching(2) by blast
               hence v1v2_neq_xy:"{v1, v2} \<noteq> {x, y}"
                 using rev_pair_set yx_not_matching by force
               have "x \<notin> aodds F  \<Longrightarrow> if1_cond F"
                 using false y_Even yx_in_G assms(2) evens_and_odds(3)[OF assms(3)] True
                  by(auto intro!: exI[of "\<lambda> y. \<exists> x. _ x y" y, OF exI[of _ x]]
                        simp add: if1_cond_def insert_commute if2_cond_def
                                  matching_graph.vs_member'[symmetric])
              hence x_Odd: "x \<in> aodds F"
                  using assms(1) by blast
              show ?thesis 
                using IH_applied either_odd_or_even y_Even x_Odd 
                by(auto intro!: alt_list_last_known_append_one(1)[of _ _ "p12@[y]" x, simplified]
                  simp add: p1_split_off_last p11_split_off_last)
        next
          case False
          hence "x \<notin> Vs M"
            by (simp add: vs_member)
          moreover have "x \<in> Vs G" 
            using yx_in_G by blast
          ultimately have "x \<in> aevens F" 
            using assms(5,4) by auto
          thus ?thesis
            using assms(2) y_Even yx_in_G
            by(auto simp add: if2_cond_def)
        qed
      qed
    qed
  qed
 qed
qed

text \<open>We use the previous lemma to show:
if the algorithm terminates without finding two paths 
and if there were nevertheless an augmenting path,
then the last vertex in this path should be Odd, 
contradicting the fact that it is even, since unmatched.
nota bene: This way, we could also show the absence of blossoms easily,
 which is not necessary, however.\<close>

lemma termination_conditions_no_augpath:
  assumes "\<not> if1_cond F" "\<not> if2_cond F" "forest_invar M F" "Vs G - Vs M \<subseteq> aevens F"
          "graph_augmenting_path G M p"
    shows False
proof-
  have p_simple_props: "length p \<ge> 2" "hd p \<notin> Vs M" "path G p" "hd p \<notin> Vs M" "last p \<notin> Vs M"
    using assms(5)
    by(auto elim: matching_augmenting_pathE)
  have p_harder_props: "set p \<subseteq> Vs G" "set (edges_of_path p) \<subseteq> G" "last p \<in> Vs G"
    using  mem_path_Vs[OF p_simple_props(3) last_in_set] p_simple_props(1) 
    by  (simp add: p_simple_props(3) subset_path_Vs path_edges_subset | force)+
  have path_looks_like:
     "alt_list (\<lambda>x. x \<in> aevens F) (\<lambda>x. x \<in> aodds F) p"
    using termination_conditions_alt_paths_alternating_labels[OF assms(1-4), of p]
           p_harder_props  p_simple_props 
    by (auto simp add: assms(5) matching_augmenting_path_feats(2))
  have length_p: "even (length p)"
    using assms(5) aug_paths_are_even by auto
  have last_in_p_Odd: "last p \<in> aodds F" 
    using last_even_P2[OF path_looks_like(1) length_p] p_simple_props(1) by fastforce
  moreover have "last p \<in> aevens F"
    using p_simple_props(3,5) assms(4,5) p_harder_props(3)
    by auto
  ultimately show False 
    using assms(3) evens_and_odds(4) by auto
qed

lemma compute_alt_path_from_tree_2:
  assumes invars: "forest_invar M F" 
  and ret: "compute_alt_path F = None"
  and init: "finite \<lbrace>F\<rbrace>" "\<lbrace>F\<rbrace> \<subseteq> G" 
  and unmatcheds_even: "Vs G - Vs M \<subseteq> aroots F"
shows "\<nexists>p. matching_augmenting_path M p \<and> path G p \<and> distinct p"
proof(rule ccontr, unfold not_not, goal_cases)
  case 1
  then obtain p where "matching_augmenting_path M p" "path G p" "distinct p" by auto
  hence augpath: "graph_augmenting_path G M p" by simp
  obtain F' where final:
   "\<not> if1_cond F'" "\<not> if2_cond F'"
   "forest_invar M F'" "aroots F' = aroots F"
    using what_if_search_fails[OF ret init invars] by auto
  hence "Vs G - Vs M \<subseteq> aevens F'"
    using roots(2) unmatcheds_even by fastforce
  thus False
    using termination_conditions_no_augpath[OF final(1-3)] augpath by auto
qed

subsection \<open>Bringing it All Together: Final Correctness Theorems\<close>

lemma init_props:
  shows
  "forest_invar M (empty_forest unmatcheds)"
  "finite \<lbrace>empty_forest unmatcheds\<rbrace>"
  "\<lbrace>empty_forest unmatcheds\<rbrace> \<subseteq> G"
  "Vs G - Vs M \<subseteq> aroots (empty_forest unmatcheds)"
proof-
  show invar: "forest_invar M (empty_forest unmatcheds)" 
    by(auto intro!: empty_forest(5) simp add: matching(1) unmatcheds finite_Vs)
  have "\<lbrace> empty_forest unmatcheds \<rbrace> = {}"
    by(auto simp add:empty_forest(4) matching(1) unmatcheds finite_Vs)
  thus "finite \<lbrace> empty_forest unmatcheds \<rbrace>" "\<lbrace> empty_forest unmatcheds \<rbrace> \<subseteq> G"
    by auto
  show "Vs G - Vs M \<subseteq> aroots (empty_forest unmatcheds)"
    using empty_forest(1,3) evens_and_odds(3)[OF invar] unmatcheds(2) 
    by auto
qed

lemma compute_alt_path_from_tree_sound:
  assumes "compute_alt_path (empty_forest unmatcheds) = Some (p1, p2)"
  shows "last p1 \<notin> Vs M \<and>
       last p2 \<notin> Vs M \<and>
       hd p1 \<noteq> hd p2 \<and>
       odd (length p1) \<and>
       odd (length p2) \<and>
       distinct p1 \<and>
       distinct p2 \<and>
       path G p1 \<and>
       path G p2 \<and>
       {hd p1, hd p2} \<in> G \<and>
       (\<forall>x pref1 post1 pref2 post2. p1 = pref1 @ x # post1 \<and> p2 = pref2 @ x # post2 \<longrightarrow> post1 = post2) \<and>
       alt_path M (hd p1 # p2) \<and> 
       alt_path M (hd p2 # p1)"
  using init_props assms
  by(intro compute_alt_path_from_tree_1[of "empty_forest unmatcheds"]) auto

lemma compute_alt_path_from_tree_sound':
  shows "compute_alt_path_spec G M (compute_alt_path (empty_forest unmatcheds))"
  using compute_alt_path_from_tree_sound
  unfolding compute_alt_path_spec_def
  apply(intro conjI)
  by metis+

lemma compute_alt_path_from_tree_complete:
  assumes "\<exists>p. matching_augmenting_path M p \<and> path G p \<and> distinct p"
  shows "\<exists>match_blossom_comp. compute_alt_path (empty_forest unmatcheds) = Some match_blossom_comp"
  using compute_alt_path_from_tree_2[of "empty_forest unmatcheds"] init_props assms
  by force

end 

locale compute_alt_path_use =
  g: graph_abs E +
  choose sel +
  create_vert create_vert 
  for sel create_vert:: "'a set \<Rightarrow> 'a" and E::"'a set set "
begin

definition "set_iterate f init S = foldl f init (SOME vs. distinct vs \<and> set vs = S)"

lemma selected_list_ok:
  "finite S \<Longrightarrow> distinct (SOME vs. distinct vs \<and> set vs = S)"
  "finite S \<Longrightarrow> set (SOME vs. distinct vs \<and> set vs = S) = S"
  using someI_ex[of "\<lambda>  vs. distinct vs \<and> set vs = S"]
  by(auto dest!: finite_distinct_list )

lemma set_interate_correct: 
  "finite V \<Longrightarrow> \<exists>vs. V = set vs \<and> distinct vs \<and> set_iterate f init V = foldl f init vs"
  by(auto intro!: exI[of _ "SOME vs. distinct vs \<and> set vs = V"] 
            dest: selected_list_ok
        simp add: set_iterate_def)

interpretation forest: forest_manipulation 
  where parent_empty = "\<lambda> x. None"
  and parent_upd = "\<lambda> x y P z. if z = x then Some y else P z"
  and parent_delete = "\<lambda> x P z. if z = x then None else P z"
  and parent_lookup = "\<lambda> P x. P x"
  and parent_invar = "\<lambda> P. True"
  and origin_empty = "\<lambda> x. None"
  and origin_upd = "\<lambda> x y or z. if z = x then Some y else or z"
  and origin_delete = "\<lambda> x or z. if z = x then None else or z"
  and origin_lookup = "\<lambda> or x. or x"
  and origin_invar = "\<lambda> or. True"
  and vset_empty = "{}"
  and vset_insert = "\<lambda> x S. S \<union> {x}"
  and vset_delete = "\<lambda> x S. S - {x}"
  and vset_isin = "\<lambda> S x. x \<in> S"
  and vset_to_set = id
  and vset_invar = "\<lambda> S. finite S"
  and vset_iterate = set_iterate
  by(auto intro!: forest_manipulation.intro forest_manipulation_spec.intro Map.intro Set.intro 
                  forest_manipulation_axioms.intro set_interate_correct)

definition "compute_paths G M = 
  compute_alt_path.compute_alt_path id 
     forest.get_path forest.extend_forest_even_unclassified
      forest.abstract_forest evens G M sel (forest.empty_forest (Vs G - Vs M))"

context 
  fixes G M::"'a set set"
  assumes "graph_invar G" "matching M" "M \<subseteq> G"
begin

interpretation path_compute: compute_alt_path
  where vset_invar = "\<lambda> V. finite V"
    and vset_to_set = id
    and odds = odds
    and get_path = forest.get_path
    and forest_invar = forest.forest_invar
    and roots = roots
    and vset_empty = "{}"
    and extend_forest_even_unclassified = forest.extend_forest_even_unclassified
    and empty_forest = forest.empty_forest
    and abstract_forest = forest.abstract_forest
    and evens = evens
    and G = G
    and M = M
    and sel = sel
    and unmatcheds = "Vs G - Vs M"
     using forest.satisified
   by(auto intro!: compute_alt_path.intro choose_axioms compute_alt_path_axioms.intro
         simp add: graph_abs.intro match_axioms.intro match_def g.graph_abs_axioms 
                   \<open>M \<subseteq> G\<close> \<open>matching M\<close> match_axioms_def  \<open>graph_invar G\<close> graph_abs_def)

lemmas compute_alt_path_props = 
  path_compute.compute_alt_path_from_tree_sound'
  path_compute.compute_alt_path_from_tree_complete

end

interpretation compute_match_blossom'_use E sel create_vert compute_paths
proof(unfold_locales,goal_cases)
  case (2 G M)
  thus  ?case
    using compute_alt_path_props(2)[OF 2(1,2,3)]
    by(auto simp add: compute_paths_def)
next
  case (1 G M)
  thus  ?case
    using compute_alt_path_props(1)[OF 1(1,2,3)]
    by(auto simp add: compute_paths_def)
qed

lemmas find_max_matching_works = find_max_matching_works 
end
end