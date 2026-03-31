theory Blossom_Tree
  imports Laminar_Family.Laminar_Family "HOL-Data_Structures.Map_Specs"
           "HOL-Data_Structures.Set_Specs" Directed_Set_Graphs.More_Lists
begin

datatype ('v, 'id) contracted_blossom = elem_vert (the_vert: 'v) 
  | subverts (the_children :"'id list")

locale blossom_tree = 
 map : Map where update = update + 
 top_set : Set where insert = top_insert and empty = top_empty and delete = top_delete 
               and invar = top_invar and set = top_set for
  top_insert::"'id \<Rightarrow> 'set \<Rightarrow> 'set"
 and update :: "'id \<Rightarrow> ('v, 'id) contracted_blossom \<Rightarrow> 'map \<Rightarrow> 'map"
and top_empty::'set and top_delete and top_invar and top_set
begin

definition "max_ids M = 
   {i | i. lookup M i \<noteq> None \<and> 
           (\<nexists> i' vs. lookup M i' = Some (subverts vs) \<and> i \<in> set vs)}"

definition "children_nempty M =
   (\<forall> i vs. lookup M i = Some (subverts vs) \<longrightarrow> vs \<noteq> [])"

lemma children_nemptyI:
  "(\<And>i vs. lookup M i = Some (subverts vs) \<Longrightarrow> vs \<noteq> []) 
  \<Longrightarrow> children_nempty M"
  unfolding children_nempty_def by blast

lemma children_nemptyE:
  "\<lbrakk>children_nempty M;
    (\<And>i vs. lookup M i = Some (subverts vs) \<Longrightarrow> vs \<noteq> []) \<Longrightarrow> P\<rbrakk> 
  \<Longrightarrow> P"
  unfolding children_nempty_def by blast

lemma children_nemptyD:
  "\<lbrakk>children_nempty M; lookup M i = Some (subverts vs)\<rbrakk> 
  \<Longrightarrow> vs \<noteq> []"
  unfolding children_nempty_def by blast

definition "domain_recursive M =
   (\<forall> i j vs. lookup M i = Some (subverts vs) \<and> j \<in> set vs \<longrightarrow> lookup M j \<noteq> None)"

lemma domain_recursiveI:
  "(\<And>i j vs. \<lbrakk>lookup M i = Some (subverts vs); j \<in> set vs\<rbrakk> \<Longrightarrow> lookup M j \<noteq> None) 
  \<Longrightarrow> domain_recursive M"
  unfolding domain_recursive_def by blast

lemma domain_recursiveE:
  "\<lbrakk>domain_recursive M;
    (\<And>i j vs. \<lbrakk>lookup M i = Some (subverts vs); j \<in> set vs\<rbrakk> \<Longrightarrow> lookup M j \<noteq> None) \<Longrightarrow> P\<rbrakk> 
  \<Longrightarrow> P"
  unfolding domain_recursive_def by blast

lemma domain_recursiveD:
  "\<lbrakk>domain_recursive M; lookup M i = Some (subverts vs); j \<in> set vs\<rbrakk> 
  \<Longrightarrow> lookup M j \<noteq> None"
  unfolding domain_recursive_def by blast

context 
  fixes M :: 'map
begin

function (domintros) ids_of_sub_blossoms where 
 "ids_of_sub_blossoms i =
          (case lookup M i of None \<Rightarrow> {} 
           | Some B \<Rightarrow> 
             (case B of elem_vert _ \<Rightarrow> {i} |
                        subverts vs \<Rightarrow> {i} 
               \<union> \<Union> (ids_of_sub_blossoms `  set vs)))"
  by pat_completeness auto

definition "blossom_forest_rel = (\<lambda> j i. \<exists> vs. lookup M i = Some (subverts vs) \<and> j \<in> set vs)"

definition "blossom_forest_cons = {(j, i) | i j vs. lookup M i = Some (subverts vs) \<and>j \<in> set vs}"

lemma ids_of_sub_blossoms_rel_def[simp]:
  "ids_of_sub_blossoms_rel = blossom_forest_rel"
  unfolding ids_of_sub_blossoms_rel.simps blossom_forest_rel_def
  by (auto intro!: ext)

lemma ids_dom_if_wf:
  assumes "wf blossom_forest_cons"
  shows "ids_of_sub_blossoms_dom i"
proof-
  show ?thesis
    apply(rule accp_wfpD)
    unfolding wfp_def
    apply(rule forw_subst[where P= wf, OF _ assms])
    unfolding ids_of_sub_blossoms_rel_def blossom_forest_cons_def blossom_forest_rel_def
    by auto
 qed

lemmas ids_of_sub_blossoms_simps =
   ids_of_sub_blossoms.psimps[OF ids_dom_if_wf]

lemma in_ids_of_sub_blossoms_cases:
  assumes "wf blossom_forest_cons"
          "j \<in> ids_of_sub_blossoms i"
          "\<And> x. \<lbrakk>lookup M i = Some (elem_vert x); i = j\<rbrakk> \<Longrightarrow> P"
          "\<And> vs.\<lbrakk>lookup M i = Some (subverts vs); i = j\<rbrakk> \<Longrightarrow> P"
         "\<And> vs i'. \<lbrakk>lookup M i = Some (subverts vs); i' \<in> set vs; j  \<in> ids_of_sub_blossoms i'\<rbrakk> \<Longrightarrow> P"
       shows P
  using assms(2)
  unfolding ids_of_sub_blossoms_simps[OF assms(1), of i]
proof(cases "lookup M i", goal_cases)
  case 1
  then show ?case 
    by auto
next
  case (2 a)
  then show ?case 
  proof(cases a, goal_cases)
    case (1 x1)
    then show ?thesis 
      by (auto  intro!: assms(3))
  next
    case (2 x2)
    then show ?thesis
      by(auto intro: assms(4,5))
  qed
qed

lemma ids_of_sub_blossoms_induct:
assumes "wf blossom_forest_cons"
shows "(\<And>i. (\<And>x2 x2a x.
          lookup M i = Some x2 \<Longrightarrow>
          x2 = subverts x2a \<Longrightarrow> x \<in> set x2a \<Longrightarrow> P x) \<Longrightarrow>
      P i) \<Longrightarrow> P i"
  using ids_of_sub_blossoms.pinduct ids_dom_if_wf[OF assms] 
  by auto

lemma ids_mono:
 assumes "wf blossom_forest_cons"
   shows "j \<in> ids_of_sub_blossoms i \<Longrightarrow> ids_of_sub_blossoms j \<subseteq> ids_of_sub_blossoms i"
proof(induction rule: ids_of_sub_blossoms_induct[OF assms])
  case (1 i)
  note IH = this
  show ?case 
    using 1(2)
    unfolding ids_of_sub_blossoms_simps[OF assms, of i]
  proof(cases "lookup M i", goal_cases)
    case 1
    then show ?case by simp
  next
    case (2 a)
    then show ?case
    proof(cases a, goal_cases)
      case (1 x1)
      then show ?case 
        by(simp add: ids_of_sub_blossoms_simps[OF assms])
    next
      case (2 vs)
      then show ?case 
      proof(cases "j = i", goal_cases)
        case 1
        then show ?case
          by(auto simp add: ids_of_sub_blossoms_simps[OF assms])
      next
        case 2
        then obtain i' where i': "i' \<in> set vs" "j \<in> ids_of_sub_blossoms i'"
          by auto
        then show ?case
          using  IH(1) 2 by fastforce         
      qed
    qed
  qed
qed

lemma ids_in_dom:
assumes "wf blossom_forest_cons"
shows "ids_of_sub_blossoms i \<subseteq> dom (lookup M)"
proof(induction rule: ids_of_sub_blossoms_induct[OF assms])
  case (1 i)
  note IH = this
  show ?case 
    unfolding ids_of_sub_blossoms_simps[OF assms, of i]
  proof(cases "lookup M i", goal_cases)
    case 1
    then show ?case by simp
  next
    case (2 a)
    then show ?case
    proof(cases a, goal_cases)
      case (1 x1)
      then show ?case 
        by(auto simp add: ids_of_sub_blossoms_simps[OF assms])
    next
      case (2 vs)
      note two = this
      have "{i} \<union> \<Union> (ids_of_sub_blossoms ` set vs) \<subseteq> dom (lookup M)"
      proof(rule, elim UnE, goal_cases)
        case (1 x)
        then show ?case 
          using 2 by auto
      next
        case (2 x)
        then obtain i' where i': "i' \<in> set vs" "x \<in> ids_of_sub_blossoms i'"
          by auto
        then show ?case
          using  IH(1)[OF two] by fastforce         
      qed
      thus ?case
        using two by auto
    qed
  qed
qed

lemma not_in_subtree:
  assumes "wf blossom_forest_cons" "lookup M i = Some (subverts vs)" "j \<in> set vs"
   shows  "i \<notin> ids_of_sub_blossoms j"
  using assms(3,2)
proof(induction arbitrary: i vs rule: ids_of_sub_blossoms_induct[OF assms(1)])
  case (1 j)
  note IH = this
  show ?case 
    using IH(2-3)
  unfolding ids_of_sub_blossoms_simps[OF assms(1), of j]
  proof(cases "lookup M j", goal_cases)
    case 1
    then show ?case by simp
  next
    case (2 a)
    then show ?case
    proof(cases a, goal_cases)
      case (1 x1)
      then show ?case 
        by(auto simp add: ids_of_sub_blossoms_simps[OF assms(1)])
    next
      case (2 vsa)
      note two = this
      moreover have "\<lbrakk>x \<in> set vsa; i \<in> ids_of_sub_blossoms x\<rbrakk> \<Longrightarrow> False" for x
      proof(goal_cases)
        case 1
        hence "j \<notin> ids_of_sub_blossoms x"
          using 2
          by(intro IH(1)[OF 2(3,4), of x vsa j]) auto
        moreover have "j \<in> ids_of_sub_blossoms i"
          using assms(1) ids_of_sub_blossoms_simps two(1,2,3,4)
          by fastforce
        moreover have "ids_of_sub_blossoms i \<subseteq> ids_of_sub_blossoms x" 
          using 1 assms(1) ids_mono by blast
        ultimately show ?case 
          by auto
      qed
      thus ?case
        using two(1,2,3,4)
        by (fastforce simp add: ids_of_sub_blossoms_simps[OF assms(1), of j])
    qed
  qed
qed

lemma self_in_ids:
  assumes "wf blossom_forest_cons" "lookup M i \<noteq> None"
    shows "i \<in> ids_of_sub_blossoms i"
  using assms(2)
  by(auto simp add: ids_of_sub_blossoms_simps[OF assms(1)]
             split: option.split contracted_blossom.split)

lemma immediate_childrenin_ids:
  assumes "wf blossom_forest_cons"
          "lookup M i = Some (subverts vs)" "j \<in> set vs" "lookup M j \<noteq> None"
    shows "j \<in> ids_of_sub_blossoms i"
  using assms(2,3) self_in_ids[OF assms(1,4)]
  by(auto simp add: ids_of_sub_blossoms_simps[OF assms(1), of i]
             split: option.split contracted_blossom.split)

lemma in_dom_a_max_id:
  assumes "wf blossom_forest_cons"
          "finite (dom (lookup M))" "x \<in> dom (lookup M)"
    shows "\<exists> i \<in> max_ids M. x \<in> ids_of_sub_blossoms i"
proof-
  define n where 
   "n = card {i | i. x \<in> ids_of_sub_blossoms i}"
  then show ?thesis
    using assms(3)
  proof(induction n arbitrary: x rule: less_induct)
    case (less n)
    have finit4ea:"finite {i |i. x \<in> ids_of_sub_blossoms i}" for x
      by(auto intro!: finite_subset[OF _ assms(2)]
            simp add: ids_of_sub_blossoms_simps[OF assms(1)] option.split)
    show ?case 
    proof(cases "x \<in> max_ids M")
      case False
      then obtain x' vs where x': "lookup M x' = Some (subverts vs)" "x \<in> set vs"
        using less.prems(2) by (auto simp add: max_ids_def)
      moreover hence "x \<notin> {i | i. x' \<in> ids_of_sub_blossoms i}"
        using not_in_subtree[OF assms(1)] by auto
      moreover have "x \<in> {i | i. x \<in> ids_of_sub_blossoms i}"
      using less(3) x'
      by(auto simp add: ids_of_sub_blossoms_simps[OF assms(1), of x]
                 split: contracted_blossom.split)
    moreover have subst:"{i | i. x \<in> ids_of_sub_blossoms i} \<supseteq> {i | i. x' \<in> ids_of_sub_blossoms i}"
      using x' ids_mono[OF assms(1)] immediate_childrenin_ids[OF assms(1)] less.prems(2)
      by force
    ultimately have "{i | i. x \<in> ids_of_sub_blossoms i} \<supset> {i | i. x' \<in> ids_of_sub_blossoms i}"
      by auto
    hence card_less: "card {i | i. x' \<in> ids_of_sub_blossoms i} < n"
        using finit4ea ids_mono[OF assms(1)]
        by(auto intro!: psubset_card_mono simp add: less(2))
    obtain i where "i \<in> max_ids M" "x' \<in> ids_of_sub_blossoms i" 
      using less(1)[OF card_less refl] x'(1) by auto
    moreover hence "x \<in> ids_of_sub_blossoms i" 
      using local.subst by auto
    ultimately show ?thesis
      by auto
    next
      case True
      then show ?thesis 
        using less.prems(2) self_in_ids[OF assms(1)]
        by(auto intro!: bexI[of _ x])
    qed
  qed
qed

lemma dom_is_ids_of_sub_blossoms_of_max_ids:
  assumes "wf blossom_forest_cons"
          "finite (dom (lookup M))"
    shows "\<Union> (ids_of_sub_blossoms ` (max_ids M)) = dom (lookup M)"
proof(rule, goal_cases)
  case 1
  then show ?case
    using ids_in_dom[OF assms(1)] by auto
next
  case 2
  then show ?case 
    using in_dom_a_max_id[OF assms] by auto
qed

function (domintros) collect_verts where 
 "collect_verts i =
          (case lookup M i of None \<Rightarrow> {} 
           | Some B \<Rightarrow> 
             (case B of elem_vert x \<Rightarrow> {x} |
                        subverts vs \<Rightarrow>  \<Union> (collect_verts `  set vs)))"
  by pat_completeness auto

lemma collect_verts_rel_def:
  "collect_verts_rel = blossom_forest_rel"
  unfolding collect_verts_rel.simps blossom_forest_rel_def
  by (auto intro!: ext)

lemma collected_verts_dom_if_wf:
  assumes "wf blossom_forest_cons"
  shows "collect_verts_dom i"
proof-
  show ?thesis
    apply(rule accp_wfpD)
    unfolding wfp_def
    apply(rule forw_subst[where P= wf, OF _ assms])
     unfolding collect_verts_rel_def blossom_forest_cons_def blossom_forest_rel_def
     by auto
 qed

lemmas collect_verts_simps =
   collect_verts.psimps[OF collected_verts_dom_if_wf]

lemma collect_verts_induct:
assumes "wf blossom_forest_cons"
shows "(\<And>i. (\<And>x2 x2a x.
          lookup M i = Some x2 \<Longrightarrow>
          x2 = subverts x2a \<Longrightarrow> x \<in> set x2a \<Longrightarrow> P x) \<Longrightarrow>
      P i) \<Longrightarrow> P i"
  using collect_verts.pinduct collected_verts_dom_if_wf[OF assms] 
  by auto

lemma collect_verts_uf:
  assumes "wf blossom_forest_cons"
  shows "collect_verts i = \<Union> (collect_verts ` (ids_of_sub_blossoms i))"
proof(rule, goal_cases)
  case 1
  then show ?case 
    by(auto simp add: ids_of_sub_blossoms_simps[OF assms, of i]
                collect_verts_simps[OF assms, of i] 
              split: option.split contracted_blossom.split)
next
  case 2
  then show ?case
  proof(induction rule: collect_verts_induct[OF assms])
    case (1 i)
    thus ?case
      by(auto simp add: ids_of_sub_blossoms_simps[OF assms, of i]
                        collect_verts_simps[OF assms, of i]
                 split: option.split contracted_blossom.split) blast
  qed
qed

lemma collect_verts_uf':
  assumes "wf blossom_forest_cons"
  shows "collect_verts i = {x | x i'. i' \<in> ids_of_sub_blossoms i \<and> lookup M i' = Some (elem_vert x)}"
  proof(induction rule: collect_verts_induct[OF assms])
    case (1 i)
    thus ?case
     by(auto simp add: ids_of_sub_blossoms_simps[OF assms, of i]
                        collect_verts_simps[OF assms, of i]
                 split: option.split contracted_blossom.split) 
 qed

lemma Nil_iff_no_elem: "xs \<noteq> Nil \<Longrightarrow> \<exists> x. x \<in> set xs"
  by(cases xs) auto

lemma collect_verts_nempty:
  assumes "wf blossom_forest_cons" "children_nempty M" "i \<in> dom (lookup M)" "domain_recursive M"
  shows "collect_verts i \<noteq> {}"
  using assms(3)
proof(induction rule: collect_verts_induct[OF assms(1)])
  case (1 i)
  note IH =this
  show ?case
    unfolding collect_verts_simps[OF assms(1), of i] 
  proof(cases "lookup M i", goal_cases)
    case 1
    then show ?case 
      using IH by auto
  next
    case (2 a)
    then show ?case 
    proof(cases a)
      case (elem_vert x1)
      then show ?thesis 
        using 2 by auto
    next
      case (subverts vs)
      hence "vs \<noteq> []" 
        using assms(2) 2 by(auto elim!: children_nemptyE)
      then obtain x where x: "x \<in> set vs"
        by(cases vs) auto
      have "collect_verts x \<noteq> {}"
        using assms(4) subverts 2 x
        by(intro IH(1)[OF 2 subverts x])(auto dest!: domain_recursiveD[of _ i vs])
      thus ?thesis
        using 2 subverts x by auto
    qed
  qed
qed

end


definition "disjoint_subids M = 
 (\<forall> i vs. lookup M i = Some (subverts vs) \<longrightarrow>
      (\<forall> j k. j \<in> set vs \<and> k \<in> set vs \<and> j \<noteq> k 
         \<longrightarrow> ids_of_sub_blossoms M j \<inter> ids_of_sub_blossoms M k = {}))"

lemma disjoint_subidsI:
  "(\<And>i vs j k. \<lbrakk>lookup M i = Some (subverts vs); j \<in> set vs; k \<in> set vs; j \<noteq> k\<rbrakk> 
     \<Longrightarrow> ids_of_sub_blossoms M j \<inter> ids_of_sub_blossoms M k = {}) 
  \<Longrightarrow> disjoint_subids M"
  unfolding disjoint_subids_def by simp

lemma disjoint_subidsD:
  "\<lbrakk>disjoint_subids M; lookup M i = Some (subverts vs); j \<in> set vs; k \<in> set vs; j \<noteq> k\<rbrakk> 
  \<Longrightarrow> ids_of_sub_blossoms M j \<inter> ids_of_sub_blossoms M k = {}"
  unfolding disjoint_subids_def by blast

lemma disjoint_subidsE:
  "\<lbrakk>disjoint_subids M; 
    (\<And> i j k. \<lbrakk>lookup M i = Some (subverts vs); j \<in> set vs; k \<in> set vs; j \<noteq> k\<rbrakk> \<Longrightarrow>
    ids_of_sub_blossoms M j \<inter> ids_of_sub_blossoms M k = {}) \<Longrightarrow> P\<rbrakk> 
  \<Longrightarrow> P"
  unfolding disjoint_subids_def by blast

definition "disjoint_trees M = 
  (\<forall> i j. i \<in> max_ids M \<and> j \<in> max_ids M \<and> i \<noteq> j 
          \<longrightarrow> ids_of_sub_blossoms M j \<inter> ids_of_sub_blossoms M i = {})"

lemma disjoint_treesI:
  "(\<And>i j. \<lbrakk>i \<in> max_ids M; j \<in> max_ids M; i \<noteq> j\<rbrakk> 
     \<Longrightarrow> ids_of_sub_blossoms M j \<inter> ids_of_sub_blossoms M i = {}) 
  \<Longrightarrow> disjoint_trees M"
  unfolding disjoint_trees_def by simp

lemma disjoint_treesD:
  "\<lbrakk>disjoint_trees M; i \<in> max_ids M; j \<in> max_ids M; i \<noteq> j\<rbrakk> 
  \<Longrightarrow> ids_of_sub_blossoms M j \<inter> ids_of_sub_blossoms M i = {}"
  unfolding disjoint_trees_def by blast

lemma disjoint_treesE:
  "\<lbrakk>disjoint_trees M; (\<And> i k. \<lbrakk>i \<in> max_ids M; j \<in> max_ids M; i \<noteq> j\<rbrakk>
    \<Longrightarrow> ids_of_sub_blossoms M j \<inter> ids_of_sub_blossoms M i = {}) \<Longrightarrow> P\<rbrakk> 
  \<Longrightarrow> P"
  unfolding disjoint_trees_def by blast

definition "elem_unique_id M =
  (\<forall> x i j. lookup M i = Some (elem_vert x) \<and> lookup M j = Some (elem_vert x)
            \<longrightarrow> i = j)"

lemma elem_unique_idI:
  "(\<And>x i j. \<lbrakk>lookup M i = Some (elem_vert x); lookup M j = Some (elem_vert x)\<rbrakk> \<Longrightarrow> i = j) 
  \<Longrightarrow> elem_unique_id M"
  unfolding elem_unique_id_def by blast

lemma elem_unique_idE:
  "\<lbrakk>elem_unique_id M; 
    (\<And>x i j. \<lbrakk>lookup M i = Some (elem_vert x); lookup M j = Some (elem_vert x)\<rbrakk> \<Longrightarrow> i = j) \<Longrightarrow> P\<rbrakk> 
  \<Longrightarrow> P"
  unfolding elem_unique_id_def by blast

lemma elem_unique_idD:
  "\<lbrakk>elem_unique_id M; lookup M i = Some (elem_vert x); lookup M j = Some (elem_vert x)\<rbrakk> 
  \<Longrightarrow> i = j"
  unfolding elem_unique_id_def by blast

definition "disjoint_elem_verts M = 
 (\<forall> i vs. lookup M i = Some (subverts vs) \<longrightarrow>
      (\<forall> j k. j \<in> set vs \<and> k \<in> set vs \<and> j \<noteq> k 
         \<longrightarrow> collect_verts M j \<inter> collect_verts M k = {}))"

lemma disjoint_elem_vertsI:
  "(\<And>i vs j k. \<lbrakk>lookup M i = Some (subverts vs); j \<in> set vs; k \<in> set vs; j \<noteq> k\<rbrakk> 
     \<Longrightarrow> collect_verts M j \<inter> collect_verts M k = {}) 
  \<Longrightarrow> disjoint_elem_verts M"
  unfolding disjoint_elem_verts_def by blast

lemma disjoint_elem_vertsE:
  "\<lbrakk>disjoint_elem_verts M;
    (\<And>i vs j k. \<lbrakk>lookup M i = Some (subverts vs); j \<in> set vs; k \<in> set vs; j \<noteq> k\<rbrakk> 
     \<Longrightarrow> collect_verts M j \<inter> collect_verts M k = {}) \<Longrightarrow> P\<rbrakk> 
  \<Longrightarrow> P"
  unfolding disjoint_elem_verts_def by blast

lemma disjoint_elem_vertsD:
  "\<lbrakk>disjoint_elem_verts M; lookup M i = Some (subverts vs); j \<in> set vs; k \<in> set vs; j \<noteq> k\<rbrakk> 
  \<Longrightarrow> collect_verts M j \<inter> collect_verts M k = {}"
  unfolding disjoint_elem_verts_def by blast

lemma disjoint_elems_if_disjoint_subids_and_elem_unique_id:
  assumes "wf (blossom_forest_cons M)" "elem_unique_id M" "disjoint_subids M"
  shows "disjoint_elem_verts M"                   
proof(rule disjoint_elem_vertsI, rule ccontr, goal_cases)
  case (1 i vs j k)
  then obtain x where x: "x \<in> collect_verts M j" "x \<in> collect_verts M k"
    by auto
  then obtain jx kx where jx_kx:"lookup M jx = Some (elem_vert x)" "jx \<in> ids_of_sub_blossoms M j"
           "lookup M kx = Some (elem_vert x)" "kx \<in> ids_of_sub_blossoms M k"
    using "1"(1,2,3,4) assms(2,3)
    by(auto simp add: collect_verts_uf' [OF assms(1), of j] collect_verts_uf' [OF assms(1), of k])
  hence "j = k" 
    using "1"(1,2,3) assms(2,3)  disjoint_subidsD elem_unique_idD by blast
  then show ?case 
    using 1 by simp
qed

definition "disjoint_elems_over_trees M = 
  (\<forall> i j. i \<in> max_ids M \<and> j \<in> max_ids M \<and> i \<noteq> j 
          \<longrightarrow> collect_verts M j \<inter> collect_verts M i = {})"

lemma disjoint_elems_over_treesI:
  "(\<And>i j. \<lbrakk>i \<in> max_ids M; j \<in> max_ids M; i \<noteq> j\<rbrakk> 
     \<Longrightarrow> collect_verts M j \<inter> collect_verts M i = {}) 
  \<Longrightarrow> disjoint_elems_over_trees M"
  unfolding disjoint_elems_over_trees_def by blast

lemma disjoint_elems_over_treesE:
  "\<lbrakk>disjoint_elems_over_trees M;
    (\<And>i j. \<lbrakk>i \<in> max_ids M; j \<in> max_ids M; i \<noteq> j\<rbrakk> 
     \<Longrightarrow> collect_verts M j \<inter> collect_verts M i = {}) \<Longrightarrow> P\<rbrakk> 
  \<Longrightarrow> P"
  unfolding disjoint_elems_over_trees_def by blast

lemma disjoint_elems_over_treesD:
  "\<lbrakk>disjoint_elems_over_trees M; i \<in> max_ids M; j \<in> max_ids M; i \<noteq> j\<rbrakk> 
  \<Longrightarrow> collect_verts M j \<inter> collect_verts M i = {}"
  unfolding disjoint_elems_over_trees_def by blast

lemma disjoint_elems_over_trees_if_disjoint_subids_and_elem_unique_id:
  assumes "wf (blossom_forest_cons M)" "elem_unique_id M" "disjoint_trees M"
  shows "disjoint_elems_over_trees M"                   
proof(rule disjoint_elems_over_treesI, rule ccontr, goal_cases)
  case (1 j k)
  then obtain x where x: "x \<in> collect_verts M j" "x \<in> collect_verts M k"
    by auto
  then obtain jx kx where jx_kx:"lookup M jx = Some (elem_vert x)" "jx \<in> ids_of_sub_blossoms M j"
           "lookup M kx = Some (elem_vert x)" "kx \<in> ids_of_sub_blossoms M k"
    using "1"(1,2,3,4) assms(2,3)
    by(auto simp add: collect_verts_uf' [OF assms(1), of j] collect_verts_uf' [OF assms(1), of k])
  hence "j = k" 
    using "1"(1,2,3) assms(2,3)
    by(auto dest: disjoint_treesD elem_unique_idD)
  then show ?case 
    using 1 by simp
qed

lemma disjoint_elem_verts_prelaminarity:
  assumes "wf (blossom_forest_cons M)" 
    "X = collect_verts M i"  "Y = collect_verts M j" 
    "i \<in> ids_of_sub_blossoms M t " "j \<in> ids_of_sub_blossoms M t"
    "disjoint_elem_verts M"
  shows "X \<subseteq> Y \<or> Y \<subseteq> X \<or> X \<inter> Y = {}"
  using assms(2-5)
proof(induction rule: ids_of_sub_blossoms_induct[OF assms(1)])
  case (1 i)
  note IH = this
  show ?case 
  proof(cases rule: in_ids_of_sub_blossoms_cases[OF assms(1) IH(4)], goal_cases)
    case (1 x)
    then show ?case 
      using assms(1,2) IH(3,5)  collect_verts_uf[of M i] by auto
  next
    case (2 vs)
    then show ?case 
      using assms(1,2) IH(3,5)  collect_verts_uf[of M i] by auto
  next
    case (3 vs i')
    then show ?case 
    proof(cases rule: in_ids_of_sub_blossoms_cases[OF assms(1) IH(5)], goal_cases)
      case (1 x)
      then show ?case 
        by simp
    next
      case (2 vs')
      then show ?case 
        using assms(1,2,3) IH(4) collect_verts_uf[of M i]
        by auto
    next
      case (3 vs' i'')
      hence vs_eq:"subverts vs = subverts vs'" by auto
      show ?case 
      proof(cases "i' = i''")
        case True
        then show ?thesis 
          using IH(1)[OF 3(1) vs_eq 3(5) IH(2,3) ] 3 by auto
      next
        case False
        hence "X \<inter> Y = {}"
          using disjoint_elem_vertsD[OF assms(6) 3(1,2) _ False] 3  assms(1,2,3) vs_eq 
          by(auto simp add: collect_verts_uf[of M i'] collect_verts_uf[of M i''])
        then show ?thesis 
          by simp
      qed
    qed  
  qed  
qed

lemma disjoint_ids_prelaminarity:
  assumes "wf (blossom_forest_cons M)" 
    "X = ids_of_sub_blossoms M i"  "Y = ids_of_sub_blossoms M j" 
    "i \<in> ids_of_sub_blossoms M t " "j \<in> ids_of_sub_blossoms M t"
    "disjoint_subids M"
  shows "X \<subseteq> Y \<or> Y \<subseteq> X \<or> X \<inter> Y = {}"
  using assms(2-5)
proof(induction rule: ids_of_sub_blossoms_induct[OF assms(1)])
  case (1 i)
  note IH = this
  show ?case 
  proof(cases rule: in_ids_of_sub_blossoms_cases[OF assms(1) IH(4)], goal_cases)
    case (1 x)
    then show ?case 
      using assms(1,2) IH(3,5)
      by (simp add: ids_mono) 
  next
    case (2 vs)
    then show ?case 
      using assms(1,2) IH(3,5)
      by (simp add: ids_mono)
  next
    case (3 vs i')
    then show ?case 
    proof(cases rule: in_ids_of_sub_blossoms_cases[OF assms(1) IH(5)], goal_cases)
      case (1 x)
      then show ?case 
        by simp
    next
      case (2 vs')
      then show ?case 
        using assms(1,2,3) IH(4) by (simp add: ids_mono)
    next
      case (3 vs' i'')
      hence vs_eq:"subverts vs = subverts vs'" by auto
      show ?case 
      proof(cases "i' = i''")
        case True
        then show ?thesis 
          using IH(1)[OF 3(1) vs_eq 3(5) IH(2,3) ] 3 by auto
      next
        case False
        hence "X \<inter> Y = {}"
          using disjoint_subidsD[OF assms(6) 3(1,2) _ False] 3  assms(1,2,3) vs_eq 
                Int_mono[of X "ids_of_sub_blossoms M i'" Y "ids_of_sub_blossoms M i''"] ids_mono
          by auto
        then show ?thesis 
          by simp
      qed
    qed  
  qed  
qed

definition "branching_properly M =
   (\<forall> i vs. lookup M i = Some (subverts vs) \<longrightarrow> length vs \<ge> 2)"

lemma branching_properlyI:
  "(\<And>i vs. lookup M i = Some (subverts vs) \<Longrightarrow> length vs \<ge> 2) 
  \<Longrightarrow> branching_properly M"
  unfolding branching_properly_def by blast

lemma branching_properlyE:
  "\<lbrakk>branching_properly M;
    (\<And>i vs. lookup M i = Some (subverts vs) \<Longrightarrow> length vs \<ge> 2) \<Longrightarrow> P\<rbrakk> 
  \<Longrightarrow> P"
  unfolding branching_properly_def by blast

lemma branching_properlyD:
  "\<lbrakk>branching_properly M; lookup M i = Some (subverts vs)\<rbrakk> 
  \<Longrightarrow> length vs \<ge> 2"
  unfolding branching_properly_def by blast

lemma branching_properly_children_nempty:
  "branching_properly M \<Longrightarrow> children_nempty M"
  by(auto intro!: children_nemptyI dest!: branching_properlyD)

definition "distinct_children M = (\<forall> i vs. lookup M i = Some (subverts vs) \<longrightarrow> distinct vs)"

lemma distinct_childrenI:
  "(\<And>i vs. lookup M i = Some (subverts vs) \<Longrightarrow> distinct vs) 
  \<Longrightarrow> distinct_children M"
  unfolding distinct_children_def by blast

lemma distinct_childrenE:
  "\<lbrakk>distinct_children M;
    (\<And>i vs. lookup M i = Some (subverts vs) \<Longrightarrow> distinct vs) \<Longrightarrow> P\<rbrakk> 
  \<Longrightarrow> P"
  unfolding distinct_children_def by blast

lemma distinct_childrenD:
  "\<lbrakk>distinct_children M; lookup M i = Some (subverts vs)\<rbrakk> 
  \<Longrightarrow> distinct vs"
  unfolding distinct_children_def by blast

lemma disjoint_elem_verts_pre_inj_of_collect:
  assumes "wf (blossom_forest_cons M)" 
    "collect_verts M i = collect_verts M j" 
    "i \<in> ids_of_sub_blossoms M t " "j \<in> ids_of_sub_blossoms M t"
    "disjoint_elem_verts M" "distinct_children M" "branching_properly M"
    "domain_recursive M" "elem_unique_id M"
  shows "i = j"
  using assms(2-4)
proof(induction arbitrary: i j rule: ids_of_sub_blossoms_induct[OF assms(1)])
  case (1 t)
  note IH = this
  show ?case 
  proof(cases rule: in_ids_of_sub_blossoms_cases[OF assms(1) IH(4)], goal_cases)
    case (1 x)
    then show ?case
      using IH(3) assms(1) ids_of_sub_blossoms_simps by auto
  next
    case (2 vs)
      then show ?case 
       proof(cases rule: in_ids_of_sub_blossoms_cases[OF assms(1) IH(3)], goal_cases)
         case (3 vs' i')
       then obtain i'' where i''': " i'' \<in> set vs'" "i'' \<noteq> i'"
            using branching_properlyD[OF assms(7), of t vs']
                  distinct_childrenD[OF assms(6), of t vs']
            by(cases vs' rule: list_cases3) auto
          hence "collect_verts M i' \<inter> collect_verts M i'' = {}" 
            using  disjoint_elem_vertsD collect_verts_uf[OF assms(1)]  "3"(3,4) assms(5) by blast
          moreover have "collect_verts M i'' \<noteq> {}" 
            using assms(1,7,8) i'''(1) "3"(3) collect_verts_nempty[of M i'']
            by (auto dest: domain_recursiveD simp add: branching_properly_children_nempty)
          ultimately have "collect_verts M i \<subset> collect_verts M j" 
            using "3"(2,3,5) i''' assms(8) 
              disjoint_iff[of "collect_verts M i''" "collect_verts M i''"]
              disjoint_iff[of "collect_verts M i'" "collect_verts M i''"] IH(2) 
              immediate_childrenin_ids[OF assms(1), of j vs' i'']
            by (force dest!: domain_recursiveD 
                   simp add: collect_verts_uf[OF assms(1), of j]  collect_verts_uf[OF assms(1), of i'])
          then show ?case
            by (simp add: IH(2))
        qed simp+
  next
    case (3 vs i')
    then show ?case 
    proof(cases rule: in_ids_of_sub_blossoms_cases[OF assms(1) IH(3)], goal_cases)
      case (2 vs')
           then obtain i'' where i''': " i'' \<in> set vs'" "i'' \<noteq> i'"
            using branching_properlyD[OF assms(7), of t vs']
                  distinct_childrenD[OF assms(6), of t vs']
            by(cases vs' rule: list_cases3) auto
          hence "collect_verts M i' \<inter> collect_verts M i'' = {}"
            using "2"(4) "3"(1,2) assms(5) disjoint_elem_vertsD by auto
          moreover have "collect_verts M i'' \<noteq> {}" 
            using assms(1,7,8) i'''(1) "2"(4) collect_verts_nempty[of M i'']
            by (auto dest: domain_recursiveD simp add: branching_properly_children_nempty)
          ultimately have "collect_verts M i \<subset> collect_verts M j" 
            using assms(1) "2"(4,5) i'''(1) "3"(3)  IH(2)
            by(auto simp add: collect_verts_uf[of M i'] collect_verts_simps[of M i])
          then show ?case
            by (simp add: IH(2))
      then show ?case 
        using assms(1,2,3) IH(4) collect_verts_uf[of M i]
        by auto
    next
      case (3 vs' i'')
      hence vs_eq:"subverts vs = subverts vs'" by auto
      show ?case 
      proof(cases "i' = i''")
        case True
        then show ?thesis
          using "1.IH" "3"(1,2,3,6) IH(2) by blast
      next
        case False
        hence "collect_verts M i' \<inter> collect_verts M i''  = {}" 
          using "3"(1,2,5) assms(5) disjoint_elem_vertsD vs_eq by auto
        moreover have "collect_verts M i \<subseteq> collect_verts M i'"
          using assms(1) "3"(3) IH(2) collect_verts_uf[of M i']
          by blast
        moreover have "collect_verts M j \<subseteq> collect_verts M i''" 
          using assms(1) "3"(6) IH(2) collect_verts_uf[of M i''] by auto
        ultimately have "collect_verts M i \<inter> collect_verts M j  = {}" 
          by auto
        moreover have "collect_verts M i \<noteq> {}"
          using "3"(6) assms(1,7,8) branching_properly_children_nempty collect_verts_nempty ids_in_dom
          by fastforce
        moreover have "collect_verts M j \<noteq> {}"
          using "3"(3) assms(1,7,8) branching_properly_children_nempty collect_verts_nempty ids_in_dom
          by fastforce
        ultimately have "collect_verts M i \<noteq> collect_verts M j"
          by blast
        hence False
          using IH(2) by auto
        thus ?thesis
          by simp
      qed
    qed  
  qed  
qed

fun blossom_forest_invar where
 "blossom_forest_invar (tops, M) = 
  (top_invar tops \<and> invar M \<and> max_ids M = top_set tops \<and> 
   disjoint_subids M \<and> disjoint_trees M \<and> elem_unique_id M
  \<and> wf (blossom_forest_cons M) \<and> finite (dom (lookup M)) \<and>
  branching_properly M \<and> domain_recursive M \<and> distinct_children M)"

lemma blossom_forest_invarI [intro]:
  "\<lbrakk>top_invar tops; invar M; max_ids M = top_set tops; 
    disjoint_subids M; disjoint_trees M; elem_unique_id M; 
    wf (blossom_forest_cons M); finite (dom (lookup M));
    branching_properly M; domain_recursive M; distinct_children M \<rbrakk> 
  \<Longrightarrow> blossom_forest_invar (tops, M)"
  by simp

lemma blossom_forest_invarE [elim]:
  "\<lbrakk>blossom_forest_invar (tops, M);
    \<lbrakk>top_invar tops; invar M; max_ids M = top_set tops; 
     disjoint_subids M; disjoint_trees M; elem_unique_id M; 
     wf (blossom_forest_cons M); finite (dom (lookup M));
     branching_properly M; domain_recursive M;distinct_children M\<rbrakk> \<Longrightarrow> P\<rbrakk> 
  \<Longrightarrow> P"
  by simp

lemma blossom_forest_invarD:
  "blossom_forest_invar (tops, M) \<Longrightarrow> top_invar tops" 
  "blossom_forest_invar (tops, M) \<Longrightarrow> invar M" 
  "blossom_forest_invar (tops, M) \<Longrightarrow> max_ids M = top_set tops" 
  "blossom_forest_invar (tops, M) \<Longrightarrow> disjoint_subids M" 
  "blossom_forest_invar (tops, M) \<Longrightarrow> disjoint_trees M" 
  "blossom_forest_invar (tops, M) \<Longrightarrow> elem_unique_id M" 
  "blossom_forest_invar (tops, M) \<Longrightarrow> wf (blossom_forest_cons M)"
  "blossom_forest_invar (tops, M) \<Longrightarrow> finite (dom (lookup M))"
  "blossom_forest_invar (tops, M) \<Longrightarrow> branching_properly M"
  "blossom_forest_invar (tops, M) \<Longrightarrow> domain_recursive M"
  "blossom_forest_invar (tops, M) \<Longrightarrow> distinct_children M"
  by simp_all

lemma collect_eq_dest:"Collect P = Collect Q \<Longrightarrow> (\<And> x. P x \<longleftrightarrow> Q x)"
  by auto

definition "all_verts M = {v | i v. lookup M i = Some (elem_vert v)}"

lemma finite_image_subst:
 "\<lbrakk>finite A; B = f ` A\<rbrakk> \<Longrightarrow> finite B"
  by auto

lemma finite_all_verts_dom:
  "finite (dom (lookup M)) \<Longrightarrow> finite (all_verts M)"
  by(auto intro!: finite_image_subst[of " {i | i v. lookup M i = Some (elem_vert v)}" _ 
                     "\<lambda> i. the_vert (the (lookup M i))"] 
                  finite_subset[of _ "dom (lookup M)"] rev_image_eqI
        simp add: all_verts_def)

lemma
  assumes "blossom_forest_invar (tops, M)"
  shows  "inj_on (collect_verts M) (dom (lookup M))" (is ?th1)
  and "laminar (all_verts M) ({collect_verts M i| i. i \<in> dom (lookup M)})" (is ?th2)
  and "bij_betw (collect_verts M) (dom (lookup M)) {collect_verts M i| i. i \<in> dom (lookup M)}" (is ?th3)
  and "card (dom (lookup M)) \<le> 2 * card (all_verts M) - 1" (is ?th4)
proof-
  note blossom_forest_invarD = blossom_forest_invarD[OF assms]
  note disjointness_over_verts = 
        disjoint_elems_over_trees_if_disjoint_subids_and_elem_unique_id 
          [OF blossom_forest_invarD(7,6,5)]
        disjoint_elems_if_disjoint_subids_and_elem_unique_id
          [OF blossom_forest_invarD(7,6,4)]
show th2: ?th2
proof(rule laminarI, goal_cases)
  case (1 X Y)
  then obtain i j where ij: "i \<in> dom (lookup M)" "X = collect_verts M i"
                        "j \<in> dom (lookup M)" "Y = collect_verts M j"
    by auto
  then obtain i' j' where i'j':"i' \<in> max_ids M" "i \<in> ids_of_sub_blossoms M i'"
       "j' \<in> max_ids M" "j \<in> ids_of_sub_blossoms M j'"
    by (meson assms blossom_forest_invar.simps in_dom_a_max_id)
  show ?case 
  proof(rule ccontr, goal_cases)
    case 1
    hence props: "\<not> X \<subseteq> Y" "\<not> Y \<subseteq> X" "X \<inter> Y \<noteq> {}"
      by auto
    hence "i' = j'"
      using ij(2,4) i'j' disjoint_elems_over_treesD[OF disjointness_over_verts(1) i'j'(1,3)] 
      by(auto simp add: collect_verts_uf[OF blossom_forest_invarD(7), of i'] 
                        collect_verts_uf[OF blossom_forest_invarD(7), of j'])
    hence "X \<subseteq> Y \<or> Y \<subseteq> X \<or> X \<inter> Y = {}"
      using i'j'(2,4) disjointness_over_verts(2)
      by(intro disjoint_elem_verts_prelaminarity[of M _ i _ j j'] blossom_forest_invarD(7) ij(2,4))
     simp+
    thus False 
      using props by simp
  qed
next
  case (2 X)
  then obtain i where i: "i \<in> dom (lookup M)" "X = collect_verts M i"
    by auto
  thus ?case
    using all_verts_def blossom_forest_invarD(10,7,9) collect_verts_nempty collect_verts_uf'
    by (auto simp add: branching_properly_children_nempty)
qed
  show th1: ?th1
  proof (rule inj_onI, rule ccontr, goal_cases)
    case (1 i j)
    note one = this
    then obtain i' j' where i'j': "i' \<in> max_ids M" "i \<in> ids_of_sub_blossoms M i'"
       "j' \<in> max_ids M" "j \<in> ids_of_sub_blossoms M j'"
      by (meson assms blossom_forest_invar.simps in_dom_a_max_id)
    hence "(ids_of_sub_blossoms M i' \<inter> ids_of_sub_blossoms M j' = {} \<and> i' \<noteq> j') \<or> i' = j'"
      using blossom_forest_invarD(5) disjoint_treesD by force
    thus ?case
    proof(elim disjE,goal_cases)
      case 1
      hence "collect_verts M j' \<inter> collect_verts M i' = {}"
        using disjoint_elems_over_treesD[OF disjointness_over_verts(1) i'j'(1,3)] by auto
      moreover have "collect_verts M i \<subseteq> collect_verts M i'" 
        using i'j'(2)  collect_verts_uf[OF blossom_forest_invarD(7)] by fast
      moreover have "collect_verts M j \<subseteq> collect_verts M j'" 
        using i'j'(4)  collect_verts_uf[OF blossom_forest_invarD(7)] by fast
      moreover have "collect_verts M j' \<inter> collect_verts M i' \<noteq>{}"
        using blossom_forest_invarD(10,7,9) calculation(2,3) collect_verts_nempty one(1,3)
              branching_properly_children_nempty
        by fastforce
      ultimately show False
        by simp
    next
      case 2
      thus False
        using blossom_forest_invarD(10,11,6,7,9) disjoint_elem_verts_pre_inj_of_collect
          disjointness_over_verts(2) i'j'(2,4) one(3,4) by blast
    qed
  qed
  show ?th3
  proof(rule bij_betw_imageI, goal_cases)
    case 1
    then show ?case
      using th1 by simp
  next
    case 2
    then show ?case 
      by blast
  qed
  thus th4: ?th4
    by(auto intro!: laminar_family_number_of_sets[simplified] finite_all_verts_dom
          simp add: bij_betw_same_card th2 blossom_forest_invarD(8))
qed
  

lemma new_blossom_max_ids:
  assumes  "wf {(j, i) | i j vs. lookup M i = Some (subverts vs) \<and>j \<in> set vs}"
  assumes  "set vs \<subseteq> max_ids M" "i \<notin> dom (lookup M)"
           "M' = update i (subverts vs) M"
   shows  "wf {(j, i) | i j vs. lookup M' i = Some (subverts vs) \<and>j \<in> set vs}"
          "ids_of_sub_blossoms M "

inductive disjoint_subids where
  "lookup M i = Some (elem_vert x) \<Longrightarrow> disjoint_subids i" |
  "lookup M i = Some (elem_vert x) \<Longrightarrow> disjoint_subids i"


end
end