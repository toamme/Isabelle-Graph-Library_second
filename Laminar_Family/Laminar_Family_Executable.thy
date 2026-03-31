theory Laminar_Family_Executable
  imports Laminar_Family.Laminar_Family "HOL-Data_Structures.Map_Specs"
           "HOL-Data_Structures.Set_Specs" Directed_Set_Graphs.More_Lists
          Laminar_Spec
begin

datatype ('v, 'id) contracted_laminar = elem_vert (the_vert: 'v) 
  | subverts (the_children :"'id list")
term foldl
locale laminar_tree = 
 map : Map where update = update + 
 top_set : Set where insert = top_insert and empty = top_empty and delete = top_delete 
               and invar = top_invar and set = top_set for
  top_insert::"'id \<Rightarrow> 'set \<Rightarrow> 'set"
 and update :: "'id \<Rightarrow> ('v, 'id) contracted_laminar \<Rightarrow> 'map \<Rightarrow> 'map"
and top_empty::'set and top_delete and top_invar and top_set +
fixes set_fold :: "('acc \<Rightarrow> 'id \<Rightarrow> 'acc) \<Rightarrow> 'acc \<Rightarrow> 'set \<Rightarrow> 'acc"
assumes set_fold: 
  "\<And> S f acc. top_invar S \<Longrightarrow> \<exists> xs. set xs = top_set S \<and> distinct xs \<and>
             set_fold f acc S = foldl f acc xs"
begin

subsection \<open>Function Definitions\<close>

context 
  fixes M :: 'map
begin

function (domintros) ids_of_sub_laminars where 
 "ids_of_sub_laminars i =
          (case lookup M i of None \<Rightarrow> {} 
           | Some B \<Rightarrow> 
             (case B of elem_vert _ \<Rightarrow> {i} |
                        subverts vs \<Rightarrow> {i} 
               \<union> \<Union> (ids_of_sub_laminars `  set vs)))"
  by pat_completeness auto

definition "laminar_forest_rel = (\<lambda> j i. \<exists> vs. lookup M i = Some (subverts vs) \<and> j \<in> set vs)"

definition "laminar_forest_cons = {(j, i) | i j vs. lookup M i = Some (subverts vs) \<and>j \<in> set vs}"

lemma ids_of_sub_laminars_rel_def[simp]:
  "ids_of_sub_laminars_rel = laminar_forest_rel"
  unfolding ids_of_sub_laminars_rel.simps laminar_forest_rel_def
  by (auto intro!: ext)

lemma ids_dom_if_wf:
  assumes "wf laminar_forest_cons"
  shows "ids_of_sub_laminars_dom i"
proof-
  show ?thesis
    apply(rule accp_wfpD)
    unfolding wfp_def
    apply(rule forw_subst[where P= wf, OF _ assms])
    unfolding ids_of_sub_laminars_rel_def laminar_forest_cons_def laminar_forest_rel_def
    by auto
 qed

lemmas ids_of_sub_laminars_simps =
   ids_of_sub_laminars.psimps[OF ids_dom_if_wf]

lemma in_ids_of_sub_laminars_cases:
  assumes "wf laminar_forest_cons"
          "j \<in> ids_of_sub_laminars i"
          "\<And> x. \<lbrakk>lookup M i = Some (elem_vert x); i = j\<rbrakk> \<Longrightarrow> P"
          "\<And> vs.\<lbrakk>lookup M i = Some (subverts vs); i = j\<rbrakk> \<Longrightarrow> P"
         "\<And> vs i'. \<lbrakk>lookup M i = Some (subverts vs); i' \<in> set vs; j  \<in> ids_of_sub_laminars i'\<rbrakk> \<Longrightarrow> P"
       shows P
  using assms(2)
  unfolding ids_of_sub_laminars_simps[OF assms(1), of i]
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

lemma ids_of_sub_laminars_induct:
assumes "wf laminar_forest_cons"
shows "(\<And>i. (\<And>x2 x2a x.
          lookup M i = Some x2 \<Longrightarrow>
          x2 = subverts x2a \<Longrightarrow> x \<in> set x2a \<Longrightarrow> P x) \<Longrightarrow>
      P i) \<Longrightarrow> P i"
  using ids_of_sub_laminars.pinduct ids_dom_if_wf[OF assms] 
  by auto

lemma ids_mono:
 assumes "wf laminar_forest_cons"
   shows "j \<in> ids_of_sub_laminars i \<Longrightarrow> ids_of_sub_laminars j \<subseteq> ids_of_sub_laminars i"
proof(induction rule: ids_of_sub_laminars_induct[OF assms])
  case (1 i)
  note IH = this
  show ?case 
    using 1(2)
    unfolding ids_of_sub_laminars_simps[OF assms, of i]
  proof(cases "lookup M i", goal_cases)
    case 1
    then show ?case by simp
  next
    case (2 a)
    then show ?case
    proof(cases a, goal_cases)
      case (1 x1)
      then show ?case 
        by(simp add: ids_of_sub_laminars_simps[OF assms])
    next
      case (2 vs)
      then show ?case 
      proof(cases "j = i", goal_cases)
        case 1
        then show ?case
          by(auto simp add: ids_of_sub_laminars_simps[OF assms])
      next
        case 2
        then obtain i' where i': "i' \<in> set vs" "j \<in> ids_of_sub_laminars i'"
          by auto
        then show ?case
          using  IH(1) 2 by fastforce         
      qed
    qed
  qed
qed

lemma ids_in_dom:
assumes "wf laminar_forest_cons"
shows "ids_of_sub_laminars i \<subseteq> dom (lookup M)"
proof(induction rule: ids_of_sub_laminars_induct[OF assms])
  case (1 i)
  note IH = this
  show ?case 
    unfolding ids_of_sub_laminars_simps[OF assms, of i]
  proof(cases "lookup M i", goal_cases)
    case 1
    then show ?case by simp
  next
    case (2 a)
    then show ?case
    proof(cases a, goal_cases)
      case (1 x1)
      then show ?case 
        by(auto simp add: ids_of_sub_laminars_simps[OF assms])
    next
      case (2 vs)
      note two = this
      have "{i} \<union> \<Union> (ids_of_sub_laminars ` set vs) \<subseteq> dom (lookup M)"
      proof(rule, elim UnE, goal_cases)
        case (1 x)
        then show ?case 
          using 2 by auto
      next
        case (2 x)
        then obtain i' where i': "i' \<in> set vs" "x \<in> ids_of_sub_laminars i'"
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
  assumes "wf laminar_forest_cons" "lookup M i = Some (subverts vs)" "j \<in> set vs"
   shows  "i \<notin> ids_of_sub_laminars j"
  using assms(3,2)
proof(induction arbitrary: i vs rule: ids_of_sub_laminars_induct[OF assms(1)])
  case (1 j)
  note IH = this
  show ?case 
    using IH(2-3)
  unfolding ids_of_sub_laminars_simps[OF assms(1), of j]
  proof(cases "lookup M j", goal_cases)
    case 1
    then show ?case by simp
  next
    case (2 a)
    then show ?case
    proof(cases a, goal_cases)
      case (1 x1)
      then show ?case 
        by(auto simp add: ids_of_sub_laminars_simps[OF assms(1)])
    next
      case (2 vsa)
      note two = this
      moreover have "\<lbrakk>x \<in> set vsa; i \<in> ids_of_sub_laminars x\<rbrakk> \<Longrightarrow> False" for x
      proof(goal_cases)
        case 1
        hence "j \<notin> ids_of_sub_laminars x"
          using 2
          by(intro IH(1)[OF 2(3,4), of x vsa j]) auto
        moreover have "j \<in> ids_of_sub_laminars i"
          using assms(1) ids_of_sub_laminars_simps two(1,2,3,4)
          by fastforce
        moreover have "ids_of_sub_laminars i \<subseteq> ids_of_sub_laminars x" 
          using 1 assms(1) ids_mono by blast
        ultimately show ?case 
          by auto
      qed
      thus ?case
        using two(1,2,3,4)
        by (fastforce simp add: ids_of_sub_laminars_simps[OF assms(1), of j])
    qed
  qed
qed

lemma self_in_ids:
  assumes "wf laminar_forest_cons" "lookup M i \<noteq> None"
    shows "i \<in> ids_of_sub_laminars i"
  using assms(2)
  by(auto simp add: ids_of_sub_laminars_simps[OF assms(1)]
             split: option.split contracted_laminar.split)

lemma immediate_childrenin_ids:
  assumes "wf laminar_forest_cons"
          "lookup M i = Some (subverts vs)" "j \<in> set vs" "lookup M j \<noteq> None"
    shows "j \<in> ids_of_sub_laminars i"
  using assms(2,3) self_in_ids[OF assms(1,4)]
  by(auto simp add: ids_of_sub_laminars_simps[OF assms(1), of i]
             split: option.split contracted_laminar.split)


function (domintros) collect_verts where 
 "collect_verts i =
          (case lookup M i of None \<Rightarrow> {} 
           | Some B \<Rightarrow> 
             (case B of elem_vert x \<Rightarrow> {x} |
                        subverts vs \<Rightarrow>  \<Union> (collect_verts `  set vs)))"
  by pat_completeness auto

lemma collect_verts_rel_def:
  "collect_verts_rel = laminar_forest_rel"
  unfolding collect_verts_rel.simps laminar_forest_rel_def
  by (auto intro!: ext)

lemma collected_verts_dom_if_wf:
  assumes "wf laminar_forest_cons"
  shows "collect_verts_dom i"
proof-
  show ?thesis
    apply(rule accp_wfpD)
    unfolding wfp_def
    apply(rule forw_subst[where P= wf, OF _ assms])
     unfolding collect_verts_rel_def laminar_forest_cons_def laminar_forest_rel_def
     by auto
 qed

lemmas collect_verts_simps =
   collect_verts.psimps[OF collected_verts_dom_if_wf]

lemma collect_verts_induct:
assumes "wf laminar_forest_cons"
shows "(\<And>i. (\<And>x2 x2a x.
          lookup M i = Some x2 \<Longrightarrow>
          x2 = subverts x2a \<Longrightarrow> x \<in> set x2a \<Longrightarrow> P x) \<Longrightarrow>
      P i) \<Longrightarrow> P i"
  using collect_verts.pinduct collected_verts_dom_if_wf[OF assms] 
  by auto

lemma collect_verts_uf:
  assumes "wf laminar_forest_cons"
  shows "collect_verts i = \<Union> (collect_verts ` (ids_of_sub_laminars i))"
proof(rule, goal_cases)
  case 1
  then show ?case 
    by(auto simp add: ids_of_sub_laminars_simps[OF assms, of i]
                collect_verts_simps[OF assms, of i] 
              split: option.split contracted_laminar.split)
next
  case 2
  then show ?case
  proof(induction rule: collect_verts_induct[OF assms])
    case (1 i)
    thus ?case
      by(auto simp add: ids_of_sub_laminars_simps[OF assms, of i]
                        collect_verts_simps[OF assms, of i]
                 split: option.split contracted_laminar.split) blast
  qed
qed

lemma collect_verts_uf':
  assumes "wf laminar_forest_cons"
  shows "collect_verts i = {x | x i'. i' \<in> ids_of_sub_laminars i \<and> lookup M i' = Some (elem_vert x)}"
  proof(induction rule: collect_verts_induct[OF assms])
    case (1 i)
    thus ?case
     by(auto simp add: ids_of_sub_laminars_simps[OF assms, of i]
                        collect_verts_simps[OF assms, of i]
                 split: option.split contracted_laminar.split) 
 qed

lemma Nil_iff_no_elem: "xs \<noteq> Nil \<Longrightarrow> \<exists> x. x \<in> set xs"
  by(cases xs) auto

function (domintros) laminar_tree_fold where 
 "laminar_tree_fold f acc i =
       (case lookup M i of None \<Rightarrow> acc 
           | Some B \<Rightarrow> 
             (case B of elem_vert _ \<Rightarrow> f acc i |
                        subverts vs \<Rightarrow> foldl (\<lambda> acc i. laminar_tree_fold f acc i) (f acc i) vs))"
  by pat_completeness auto

function (domintros) laminar_fold_singletons where 
 "laminar_fold_singletons f acc i =
       (case lookup M i of None \<Rightarrow> acc 
           | Some B \<Rightarrow> 
             (case B of elem_vert x \<Rightarrow> f acc x |
                        subverts vs \<Rightarrow> foldl (\<lambda> acc i. laminar_fold_singletons f acc i) acc vs))"
  by pat_completeness auto

lemma  laminar_forest_cons_def': 
  "laminar_forest_cons = {(x, y) |x y. laminar_forest_rel x y}"
  by(auto simp add:  laminar_forest_cons_def laminar_forest_rel_def)

lemma laminar_tree_fold_dom:
  assumes "wf laminar_forest_cons"
  shows "laminar_tree_fold_dom (f, acc, i)" 
  by(induction arbitrary: f acc rule: ids_of_sub_laminars_induct[OF assms])
    (auto intro: laminar_tree_fold.domintros)

lemmas laminar_tree_fold_simps = laminar_tree_fold.psimps[OF laminar_tree_fold_dom]

lemma laminar_tree_fold_rel_wf:
  assumes "wf laminar_forest_cons"
  shows "wf {(x, y). laminar_tree_fold_rel x y}" 
  using laminar_tree_fold_dom[OF assms]
  unfolding wfp_def[of laminar_tree_fold_rel,  symmetric]
  by(force intro!: accp_wfpI)

lemma laminar_tree_fold_rel_wf':
  assumes "wf laminar_forest_cons"
  shows  "wf {(x, y) | x y . laminar_tree_fold_rel x y}" 
  by(rule forw_subst[of _ "{(x, y) . laminar_tree_fold_rel x y}"])
    (auto intro!:  laminar_tree_fold_rel_wf[OF assms])

lemma laminar_fold_singletons_dom:
  assumes "wf laminar_forest_cons"
  shows "laminar_fold_singletons_dom (f, acc, i)" 
  by(induction arbitrary: f acc rule: ids_of_sub_laminars_induct[OF assms])
    (auto intro: laminar_fold_singletons.domintros)

lemmas laminar_fold_singletons_simps = laminar_fold_singletons.psimps[OF laminar_fold_singletons_dom]

lemma laminar_fold_singletons_rel_wf:
  assumes "wf laminar_forest_cons"
  shows "wf {(x, y). laminar_fold_singletons_rel x y}" 
  using laminar_fold_singletons_dom[OF assms]
  unfolding wfp_def[of laminar_fold_singletons_rel,  symmetric]
  by(force intro!: accp_wfpI)

lemma laminar_fold_singletons_rel_wf':
  assumes "wf laminar_forest_cons"
  shows  "wf {(x, y) | x y . laminar_fold_singletons_rel x y}" 
  by(rule forw_subst[of _ "{(x, y) . laminar_fold_singletons_rel x y}"])
    (auto intro!:  laminar_fold_singletons_rel_wf[OF assms])

end

definition 
  "max_qualified_fold P M f acc S =
     set_fold (\<lambda> acc i. if P i then laminar_tree_fold M f acc i else acc) acc S"

definition
  "compound = (\<lambda> (maxes, L) id. case lookup L id of None \<Rightarrow> False
                                    | Some node \<Rightarrow>
                                       case node of elem_vert _ \<Rightarrow> False
                                      | subverts _ \<Rightarrow> True)"

subsection \<open>Invariant Definitions\<close>

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

definition "disjoint_subids M = 
 (\<forall> i vs. lookup M i = Some (subverts vs) \<longrightarrow>
      (\<forall> j k. j \<in> set vs \<and> k \<in> set vs \<and> j \<noteq> k 
         \<longrightarrow> ids_of_sub_laminars M j \<inter> ids_of_sub_laminars M k = {}))"

lemma disjoint_subidsI:
  "(\<And>i vs j k. \<lbrakk>lookup M i = Some (subverts vs); j \<in> set vs; k \<in> set vs; j \<noteq> k\<rbrakk> 
     \<Longrightarrow> ids_of_sub_laminars M j \<inter> ids_of_sub_laminars M k = {}) 
  \<Longrightarrow> disjoint_subids M"
  unfolding disjoint_subids_def by simp

lemma disjoint_subidsD:
  "\<lbrakk>disjoint_subids M; lookup M i = Some (subverts vs); j \<in> set vs; k \<in> set vs; j \<noteq> k\<rbrakk> 
  \<Longrightarrow> ids_of_sub_laminars M j \<inter> ids_of_sub_laminars M k = {}"
  unfolding disjoint_subids_def by blast

lemma disjoint_subidsE:
  "\<lbrakk>disjoint_subids M; 
    (\<And> i j k. \<lbrakk>lookup M i = Some (subverts vs); j \<in> set vs; k \<in> set vs; j \<noteq> k\<rbrakk> \<Longrightarrow>
    ids_of_sub_laminars M j \<inter> ids_of_sub_laminars M k = {}) \<Longrightarrow> P\<rbrakk> 
  \<Longrightarrow> P"
  unfolding disjoint_subids_def by blast

definition "disjoint_trees M = 
  (\<forall> i j. i \<in> max_ids M \<and> j \<in> max_ids M \<and> i \<noteq> j 
          \<longrightarrow> ids_of_sub_laminars M j \<inter> ids_of_sub_laminars M i = {})"

lemma disjoint_treesI:
  "(\<And>i j. \<lbrakk>i \<in> max_ids M; j \<in> max_ids M; i \<noteq> j\<rbrakk> 
     \<Longrightarrow> ids_of_sub_laminars M j \<inter> ids_of_sub_laminars M i = {}) 
  \<Longrightarrow> disjoint_trees M"
  unfolding disjoint_trees_def by simp

lemma disjoint_treesD:
  "\<lbrakk>disjoint_trees M; i \<in> max_ids M; j \<in> max_ids M; i \<noteq> j\<rbrakk> 
  \<Longrightarrow> ids_of_sub_laminars M j \<inter> ids_of_sub_laminars M i = {}"
  unfolding disjoint_trees_def by blast

lemma disjoint_treesE:
  "\<lbrakk>disjoint_trees M; (\<And> i k. \<lbrakk>i \<in> max_ids M; j \<in> max_ids M; i \<noteq> j\<rbrakk>
    \<Longrightarrow> ids_of_sub_laminars M j \<inter> ids_of_sub_laminars M i = {}) \<Longrightarrow> P\<rbrakk> 
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

fun laminar_forest_invar where
 "laminar_forest_invar (tops, M) = 
  (top_invar tops \<and> invar M \<and> top_set tops = max_ids M  \<and> 
   disjoint_subids M \<and> disjoint_trees M \<and> elem_unique_id M
  \<and> wf (laminar_forest_cons M) \<and> finite (dom (lookup M)) \<and>
  branching_properly M \<and> domain_recursive M \<and> distinct_children M)"

lemma laminar_forest_invarI [intro]:
  "\<lbrakk>top_invar tops; invar M; max_ids M = top_set tops; 
    disjoint_subids M; disjoint_trees M; elem_unique_id M; 
    wf (laminar_forest_cons M); finite (dom (lookup M));
    branching_properly M; domain_recursive M; distinct_children M \<rbrakk> 
  \<Longrightarrow> laminar_forest_invar (tops, M)"
  by simp

lemma laminar_forest_invarE [elim]:
  "\<lbrakk>laminar_forest_invar (tops, M);
    \<lbrakk>top_invar tops; invar M; max_ids M = top_set tops; 
     disjoint_subids M; disjoint_trees M; elem_unique_id M; 
     wf (laminar_forest_cons M); finite (dom (lookup M));
     branching_properly M; domain_recursive M;distinct_children M\<rbrakk> \<Longrightarrow> P\<rbrakk> 
  \<Longrightarrow> P"
  by simp

lemma laminar_forest_invarD:
  "laminar_forest_invar (tops, M) \<Longrightarrow> top_invar tops" 
  "laminar_forest_invar (tops, M) \<Longrightarrow> invar M" 
  "laminar_forest_invar (tops, M) \<Longrightarrow> max_ids M = top_set tops" 
  "laminar_forest_invar (tops, M) \<Longrightarrow> disjoint_subids M" 
  "laminar_forest_invar (tops, M) \<Longrightarrow> disjoint_trees M" 
  "laminar_forest_invar (tops, M) \<Longrightarrow> elem_unique_id M" 
  "laminar_forest_invar (tops, M) \<Longrightarrow> wf (laminar_forest_cons M)"
  "laminar_forest_invar (tops, M) \<Longrightarrow> finite (dom (lookup M))"
  "laminar_forest_invar (tops, M) \<Longrightarrow> branching_properly M"
  "laminar_forest_invar (tops, M) \<Longrightarrow> domain_recursive M"
  "laminar_forest_invar (tops, M) \<Longrightarrow> distinct_children M"
  by simp_all

definition "all_verts M = {v | i v. lookup M i = Some (elem_vert v)}"

subsection \<open>Properties\<close>

lemma in_dom_a_max_id:
  assumes "wf (laminar_forest_cons M)"
          "finite (dom (lookup M))" "x \<in> dom (lookup M)"
    shows "\<exists> i \<in> max_ids M. x \<in> ids_of_sub_laminars M i"
proof-
  define n where 
   "n = card {i | i. x \<in> ids_of_sub_laminars M i}"
  then show ?thesis
    using assms(3)
  proof(induction n arbitrary: x rule: less_induct)
    case (less n)
    have finit4ea:"finite {i |i. x \<in> ids_of_sub_laminars M i}" for x
      by(auto intro!: finite_subset[OF _ assms(2)]
            simp add: ids_of_sub_laminars_simps[OF assms(1)] option.split)
    show ?case 
    proof(cases "x \<in> max_ids M")
      case False
      then obtain x' vs where x': "lookup M x' = Some (subverts vs)" "x \<in> set vs"
        using less.prems(2) by (auto simp add: max_ids_def)
      moreover hence "x \<notin> {i | i. x' \<in> ids_of_sub_laminars M i}"
        using not_in_subtree[OF assms(1)] by auto
      moreover have "x \<in> {i | i. x \<in> ids_of_sub_laminars M i}"
      using less(3) x'
      by(auto simp add: ids_of_sub_laminars_simps[OF assms(1), of x]
                 split: contracted_laminar.split)
    moreover have subst:"{i | i. x \<in> ids_of_sub_laminars M i} 
                           \<supseteq> {i | i. x' \<in> ids_of_sub_laminars M i}"
      using x' ids_mono[OF assms(1)] immediate_childrenin_ids[OF assms(1)] less.prems(2)
      by force
    ultimately have "{i | i. x \<in> ids_of_sub_laminars M i} \<supset> {i | i. x' \<in> ids_of_sub_laminars M i}"
      by auto
    hence card_less: "card {i | i. x' \<in> ids_of_sub_laminars M i} < n"
        using finit4ea ids_mono[OF assms(1)]
        by(auto intro!: psubset_card_mono simp add: less(2))
    obtain i where "i \<in> max_ids M" "x' \<in> ids_of_sub_laminars M i" 
      using less(1)[OF card_less refl] x'(1) by auto
    moreover hence "x \<in> ids_of_sub_laminars M i" 
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

lemma dom_is_ids_of_sub_laminars_of_max_ids:
  assumes "wf (laminar_forest_cons M)"
          "finite (dom (lookup M))"
    shows "\<Union> (ids_of_sub_laminars M ` (max_ids M)) = dom (lookup M)"
proof(rule, goal_cases)
  case 1
  then show ?case
    using ids_in_dom[OF assms(1)] by auto
next
  case 2
  then show ?case 
    using in_dom_a_max_id[OF assms] by auto
qed

lemma disjoint_elems_if_disjoint_subids_and_elem_unique_id:
  assumes "wf (laminar_forest_cons M)" "elem_unique_id M" "disjoint_subids M"
  shows "disjoint_elem_verts M"                   
proof(rule disjoint_elem_vertsI, rule ccontr, goal_cases)
  case (1 i vs j k)
  then obtain x where x: "x \<in> collect_verts M j" "x \<in> collect_verts M k"
    by auto
  then obtain jx kx where jx_kx:"lookup M jx = Some (elem_vert x)" "jx \<in> ids_of_sub_laminars M j"
           "lookup M kx = Some (elem_vert x)" "kx \<in> ids_of_sub_laminars M k"
    using "1"(1,2,3,4) assms(2,3)
    by(auto simp add: collect_verts_uf' [OF assms(1), of j] collect_verts_uf' [OF assms(1), of k])
  hence "j = k" 
    using "1"(1,2,3) assms(2,3)  disjoint_subidsD elem_unique_idD by blast
  then show ?case 
    using 1 by simp
qed

lemma disjoint_elems_over_trees_if_disjoint_subids_and_elem_unique_id:
  assumes "wf (laminar_forest_cons M)" "elem_unique_id M" "disjoint_trees M"
  shows "disjoint_elems_over_trees M"                   
proof(rule disjoint_elems_over_treesI, rule ccontr, goal_cases)
  case (1 j k)
  then obtain x where x: "x \<in> collect_verts M j" "x \<in> collect_verts M k"
    by auto
  then obtain jx kx where jx_kx:"lookup M jx = Some (elem_vert x)" "jx \<in> ids_of_sub_laminars M j"
           "lookup M kx = Some (elem_vert x)" "kx \<in> ids_of_sub_laminars M k"
    using "1"(1,2,3,4) assms(2,3)
    by(auto simp add: collect_verts_uf' [OF assms(1), of j] collect_verts_uf' [OF assms(1), of k])
  hence "j = k" 
    using "1"(1,2,3) assms(2,3)
    by(auto dest: disjoint_treesD elem_unique_idD)
  then show ?case 
    using 1 by simp
qed

lemma disjoint_elem_verts_prelaminarity:
  assumes "wf (laminar_forest_cons M)" 
    "X = collect_verts M i"  "Y = collect_verts M j" 
    "i \<in> ids_of_sub_laminars M t " "j \<in> ids_of_sub_laminars M t"
    "disjoint_elem_verts M"
  shows "X \<subseteq> Y \<or> Y \<subseteq> X \<or> X \<inter> Y = {}"
  using assms(2-5)
proof(induction rule: ids_of_sub_laminars_induct[OF assms(1)])
  case (1 i)
  note IH = this
  show ?case 
  proof(cases rule: in_ids_of_sub_laminars_cases[OF assms(1) IH(4)], goal_cases)
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
    proof(cases rule: in_ids_of_sub_laminars_cases[OF assms(1) IH(5)], goal_cases)
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
  assumes "wf (laminar_forest_cons M)" 
    "X = ids_of_sub_laminars M i"  "Y = ids_of_sub_laminars M j" 
    "i \<in> ids_of_sub_laminars M t " "j \<in> ids_of_sub_laminars M t"
    "disjoint_subids M"
  shows "X \<subseteq> Y \<or> Y \<subseteq> X \<or> X \<inter> Y = {}"
  using assms(2-5)
proof(induction rule: ids_of_sub_laminars_induct[OF assms(1)])
  case (1 i)
  note IH = this
  show ?case 
  proof(cases rule: in_ids_of_sub_laminars_cases[OF assms(1) IH(4)], goal_cases)
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
    proof(cases rule: in_ids_of_sub_laminars_cases[OF assms(1) IH(5)], goal_cases)
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
                Int_mono[of X "ids_of_sub_laminars M i'" Y "ids_of_sub_laminars M i''"] ids_mono
          by auto
        then show ?thesis 
          by simp
      qed
    qed  
  qed  
qed

lemma branching_properly_children_nempty:
  "branching_properly M \<Longrightarrow> children_nempty M"
  by(auto intro!: children_nemptyI dest!: branching_properlyD)

lemma laminar_tree_fold_correct:
  assumes "wf (laminar_forest_cons M)"  "distinct_children M" "disjoint_subids M"
    shows "\<exists> xs. set xs = ids_of_sub_laminars M i \<and> distinct xs 
                \<and> laminar_tree_fold M f acc i = foldl f acc xs"
proof(induction arbitrary: acc rule: ids_of_sub_laminars_induct[OF assms(1)])
  case (1 i)
  note IH = this
  show ?case
  proof(cases "lookup M i")
    case None
    then show ?thesis 
      by(auto simp add: ids_of_sub_laminars_simps[OF assms(1)]
                        laminar_tree_fold_simps[OF assms(1)])
  next
    case (Some a)
    then show ?thesis 
    proof(cases a)
      case (elem_vert x1)
      then show ?thesis
        by(auto intro!: exI[of _ "[i]"]
              simp add: ids_of_sub_laminars_simps[OF assms(1)]
                        laminar_tree_fold_simps[OF assms(1)] Some)
    next
      case (subverts vs)
      note IH = IH[OF Some subverts]
      moreover have "distinct vs" 
        using assms(2) Some by(auto elim!: distinct_childrenE simp add: subverts) 
      moreover have "\<And> v v'. \<lbrakk>v \<in> set vs; v' \<in> set vs; v \<noteq> v'\<rbrakk> 
               \<Longrightarrow> ids_of_sub_laminars M v \<inter> ids_of_sub_laminars M v' = {}"
        using Some assms(3) disjoint_subidsD subverts by blast
      ultimately have "\<exists>xs. set xs = \<Union> (ids_of_sub_laminars M ` set vs) \<and>
         distinct xs \<and> foldl (laminar_tree_fold M f) acc vs = foldl f acc xs" for acc
      proof(induction vs arbitrary: acc)
        case Nil
        then show ?case 
          by (auto intro!: exI[of _ "[i]"])
      next
        case (Cons a vs)
        obtain xs where xs: "set xs = \<Union> (ids_of_sub_laminars M ` set vs)" "distinct xs"
           "foldl (laminar_tree_fold M f) (laminar_tree_fold M f acc a) vs =
                foldl f (laminar_tree_fold M f acc a) xs" 
          using Cons(1)[of "laminar_tree_fold M f acc a", OF Cons(2) _ Cons(4), simplified] Cons(3)
          by auto
        obtain xs' where xs': "set xs' = ids_of_sub_laminars M a" "distinct xs'" 
                "laminar_tree_fold M f acc a = foldl f acc xs'"
          using Cons(2)[of a acc] by auto
        have eq: "foldl (laminar_tree_fold M f) (laminar_tree_fold M f acc a) vs 
                   = foldl f (foldl f acc xs') xs"
          unfolding xs(3) unfolding xs'(3) by simp
        show ?case 
         using Cons.prems(2,3)
         by(auto intro!: exI[of _ "xs'@xs"] simp add: eq xs'(1,2) xs)+
     qed
     then obtain xs where xs: "set xs = \<Union> (ids_of_sub_laminars M ` set vs)"
         "distinct xs" "foldl (laminar_tree_fold M f)  (f acc i) vs = foldl f  (f acc i) xs"
       by blast
     thus ?thesis 
       using not_in_subtree[OF assms(1)]
       by(auto intro!: exI[of _ "i#xs"]
           simp add: ids_of_sub_laminars_simps[OF assms(1), of i] 
             Some laminar_tree_fold_simps[OF assms(1)] subverts)
    qed
  qed
qed

lemma laminar_fold_singletons_correct:
  assumes "wf (laminar_forest_cons M)" "distinct_children M" "disjoint_elem_verts M"
    shows "\<exists> xs. set xs = collect_verts M i \<and> distinct xs 
                \<and> laminar_fold_singletons M f acc i = foldl f acc xs"
proof(induction arbitrary: acc rule: ids_of_sub_laminars_induct[OF assms(1)])
  case (1 i)
  note IH = this
  show ?case
  proof(cases "lookup M i")
    case None
    then show ?thesis 
      by(auto simp add: collect_verts_simps[OF assms(1)]
                        laminar_fold_singletons_simps[OF assms(1)])
  next
    case (Some a)
    then show ?thesis 
    proof(cases a)
      case (elem_vert x)
      then show ?thesis
        by(auto intro!: exI[of _ "[x]"]
              simp add: collect_verts_simps[OF assms(1)]
                        laminar_fold_singletons_simps[OF assms(1)] Some)
    next
      case (subverts vs)
      note IH = IH[OF Some subverts]
      moreover have "distinct vs" 
        using assms(2) Some by(auto elim!: distinct_childrenE simp add: subverts) 
      moreover have "\<And> v v'. \<lbrakk>v \<in> set vs; v' \<in> set vs; v \<noteq> v'\<rbrakk> 
               \<Longrightarrow> collect_verts M v \<inter> collect_verts M v' = {}"
        using Some assms(3) disjoint_elem_vertsD subverts by blast
      ultimately have "\<exists>xs. set xs = \<Union> (collect_verts M ` set vs) \<and>
         distinct xs \<and> foldl (laminar_fold_singletons M f) acc vs = foldl f acc xs" for acc
      proof(induction vs arbitrary: acc)
        case (Cons a vs)
        obtain xs where xs: "set xs = \<Union> (collect_verts M ` set vs)" "distinct xs"
           "foldl (laminar_fold_singletons M f) (laminar_fold_singletons M f acc a) vs =
                foldl f (laminar_fold_singletons M f acc a) xs" 
          using Cons(1)[of "laminar_fold_singletons M f acc a", OF Cons(2) _ Cons(4), simplified] Cons(3)
          by auto
        obtain xs' where xs': "set xs' = collect_verts M a" "distinct xs'" 
                "laminar_fold_singletons M f acc a = foldl f acc xs'"
          using Cons(2)[of a acc] by auto
        have eq: "foldl (laminar_fold_singletons M f) (laminar_fold_singletons M f acc a) vs 
                   = foldl f (foldl f acc xs') xs"
          unfolding xs(3) unfolding xs'(3) by simp
        show ?case 
         using Cons.prems(2,3)
         by(auto intro!: exI[of _ "xs'@xs"] simp add: eq xs'(1,2) xs)+
     qed simp
     thus ?thesis 
       using not_in_subtree[OF assms(1)]
       by(auto simp add: collect_verts_simps[OF assms(1), of i] 
             Some laminar_fold_singletons_simps[OF assms(1)] subverts)
    qed
  qed
qed

lemma collect_verts_nempty:
  assumes "wf (laminar_forest_cons M)" "children_nempty M" "i \<in> dom (lookup M)" "domain_recursive M"
  shows "collect_verts M i \<noteq> {}"
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
      have "collect_verts M x \<noteq> {}"
        using assms(4) subverts 2 x
        by(intro IH(1)[OF 2 subverts x])(auto dest!: domain_recursiveD[of _ i vs])
      thus ?thesis
        using 2 subverts x by auto
    qed
  qed
qed

lemma collect_verts_empty:
  assumes "wf (laminar_forest_cons M)"  "i \<notin> dom (lookup M)"
  shows "collect_verts M i = {}"
  using assms
  by(auto simp add: collect_verts_simps)

lemma disjoint_elem_verts_pre_inj_of_collect:
  assumes "wf (laminar_forest_cons M)" 
    "collect_verts M i = collect_verts M j" 
    "i \<in> ids_of_sub_laminars M t " "j \<in> ids_of_sub_laminars M t"
    "disjoint_elem_verts M" "distinct_children M" "branching_properly M"
    "domain_recursive M" "elem_unique_id M"
  shows "i = j"
  using assms(2-4)
proof(induction arbitrary: i j rule: ids_of_sub_laminars_induct[OF assms(1)])
  case (1 t)
  note IH = this
  show ?case 
  proof(cases rule: in_ids_of_sub_laminars_cases[OF assms(1) IH(4)], goal_cases)
    case (1 x)
    then show ?case
      using IH(3) assms(1) ids_of_sub_laminars_simps by auto
  next
    case (2 vs)
      then show ?case 
       proof(cases rule: in_ids_of_sub_laminars_cases[OF assms(1) IH(3)], goal_cases)
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
    proof(cases rule: in_ids_of_sub_laminars_cases[OF assms(1) IH(3)], goal_cases)
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

lemma psubsetI': "A \<subseteq> B \<Longrightarrow> B \<noteq> A \<Longrightarrow> A \<subset> B"
  unfolding less_le by blast

lemma elem_cong: "x \<in> X \<Longrightarrow> Y = X \<Longrightarrow> x \<in> Y" by auto

lemma strict_subids_immediate_parent:
  assumes "wf (laminar_forest_cons M)" 
    "disjoint_subids M" "i \<in> dom (lookup M)" "ids_of_sub_laminars M i \<subset> ids_of_sub_laminars M j"
  shows "\<exists> i' vs. lookup M i' = Some (subverts vs) \<and> i \<in> set vs"
  using  assms(4)
proof(induction j rule: ids_of_sub_laminars_induct[OF assms(1)], goal_cases)
  case (1 j)
  note IH = this
  show ?case 
  proof(cases "lookup M j")
    case None
    then show ?thesis
      using IH(2) assms(1) 
      by (auto simp add: ids_of_sub_laminars_simps[OF assms(1), of j]) 
  next
    case (Some a)
    then show ?thesis 
    proof(cases a, goal_cases)
      case (1 x)
      then show ?case 
        using IH(2) self_in_ids[OF assms(1)] assms(3)
        by (auto simp add: ids_of_sub_laminars_simps[OF assms(1), of j])
    next
      case (2 vs)
      then show ?case 
      proof(cases "i \<in> set vs")
        case True
        then show ?thesis
          using 2
          by(auto intro!: exI[of _ j] exI[of _ vs] )
      next
        case False
        then obtain j' where j': "ids_of_sub_laminars M i \<subseteq> ids_of_sub_laminars M j'" "j' \<in> set vs"
          using assms(1,3) "2"(2) Some IH(2)
            inf.absorb_iff2[of "ids_of_sub_laminars M i" "ids_of_sub_laminars M j"] 
            self_in_ids[OF assms(1), of i] ids_mono[OF assms(1), of i]
            in_ids_of_sub_laminars_cases[OF assms(1), of i j]
            IntE[of i "ids_of_sub_laminars M j" "ids_of_sub_laminars M i"] 
          by force
        moreover hence "j' \<in> ids_of_sub_laminars M j" 
          using 2(2) Some assms(3) ids_of_sub_laminars_simps[OF assms(1), of j'] 
                self_in_ids[OF assms(1), of i] self_in_ids[OF assms(1), of j'] 
          by(force simp add: ids_of_sub_laminars_simps[OF assms(1), of j]
                      split: option.split contracted_laminar.split)
        moreover have "j' \<notin> ids_of_sub_laminars M i"
          using False calculation(1,2) assms(3) self_in_ids[OF assms(1), of i]
                ids_mono[OF assms(1), of j'] not_in_subtree[OF assms(1), of i]
          by(force elim!: in_ids_of_sub_laminars_cases[OF assms(1), of j' i])
        ultimately have i_in_j':"ids_of_sub_laminars M i \<subset> ids_of_sub_laminars M j'" 
          using assms(1,3) ids_of_sub_laminars_simps[of M j'] self_in_ids[of M i] self_in_ids[of M j']
          by force
        then obtain i' vs where "lookup M i' = Some (subverts vs)" "i \<in> set vs"
          using IH(1)[OF 2 j'(2) i_in_j'] by auto
        then show ?thesis
          by auto
      qed
    qed
  qed
qed
lemma Union_singleton_iff: "\<Union> A = {x} \<longleftrightarrow> A = {{x}} \<or> A = {{x},{}}"
  apply (auto dest!:  subset_singletonD) 
     apply (metis Sup_bot_conv(2) Union_upper subset_singletonD)
    apply (metis Union_upper empty_Union_conv insert_not_empty subset_singletonD)
   apply (metis Union_upper insertI1 subset_singletonD)
  by (metis Union_empty Union_upper all_not_in_conv insert_not_empty subset_singleton_iff)

lemma two_sets_union_singleton_iff:
  "A \<union> B = {x} \<longleftrightarrow> (A = {x} \<and> B = {} \<or> B = {x} \<and> A = {} \<or> A = {x} \<and> B = {x})"
  by auto

lemma strict_elem_verts_immediate_parent:
  assumes "wf (laminar_forest_cons M)" 
    "disjoint_elem_verts M" "lookup M i = Some (subverts vs)"
    "branching_properly M" "domain_recursive M" "distinct_children M"
  shows "\<nexists> x. collect_verts M i = {x}"
  using assms(3)
proof(induction i rule: ids_of_sub_laminars_induct[OF assms(1)], goal_cases)
  case (1 i)
  note IH = this
  thm collect_verts_nempty[OF assms(1) children_nemptyI _ assms(5)]
  have vs_nempty:"vs \<noteq> []" 
    using IH(2) assms(4) branching_properly_children_nempty children_nemptyD by blast
  obtain x y xs where vs_split:"vs = x#y#xs" 
    using assms(4) IH(2) by(cases vs rule: list_cases3)(auto dest!: branching_properlyD)
  have y_empty_False:"collect_verts M y = {} \<Longrightarrow> False"
   and x_empty_False: "collect_verts M x = {} \<Longrightarrow> False" 
    using assms(1,3) branching_properly_children_nempty[OF assms(4)] 
          collect_verts_nempty[OF assms(1) _ _ assms(5), of i] IH(1)
    by(auto simp add: vs_split assms(5) collect_verts_nempty domIff domain_recursiveD)
  have x_y_same_elem_False: "\<lbrakk>collect_verts M x = {xa}; collect_verts M y = {xa}\<rbrakk> \<Longrightarrow> False" for xa
    using disjoint_elem_vertsD[OF assms(2) IH(2), of x y] assms(3,6)
    by(auto dest: distinct_childrenD simp add: vs_split)
  show ?case
    by (auto dest: y_empty_False x_empty_False x_y_same_elem_False
         simp add: two_sets_union_singleton_iff vs_split  collect_verts_simps[OF assms(1), of i] IH(2))
qed   
(*
lemma strict_elem_verts_immediate_parent:
  assumes "wf (laminar_forest_cons M)" 
    "disjoint_subids M" "i \<in> dom (lookup M)" "collect_verts M i \<subset> collect_verts M j"
    "branching_properly M" "domain_recursive M" "distinct_children M"
    "disjoint_elem_verts M"
  shows "\<exists> i' vs. lookup M i' = Some (subverts vs) \<and> i \<in> set vs"
  using  assms(4)
proof(induction j rule: ids_of_sub_laminars_induct[OF assms(1)], goal_cases)
  case (1 j)
  note IH = this
  show ?case 
  proof(cases "lookup M j")
    case None
    then show ?thesis
      using IH(2) assms(1) 
      by (auto simp add: collect_verts_simps[OF assms(1), of j]) 
  next
    case (Some a)
    then show ?thesis 
    proof(cases a, goal_cases)
      case (1 x)
      then show ?case
        using IH(2)  assms(1,3,5,6)
             collect_verts_nempty[of M i] branching_properly_children_nempty[of M]
       by (auto simp add: collect_verts_simps[OF assms(1), of j]
                         collect_verts_simps[OF assms(1), of i] contracted_laminar.split)
    next
      case (2 vs)
      then show ?case 
      proof(cases "i \<in> set vs")
        case True
        then show ?thesis
          using 2
          by(auto intro!: exI[of _ j] exI[of _ vs] )
      next
        case False
        note one = 1
        have lookup_Mi: "lookup M j = Some (subverts vs)"
          by (simp add: "2"(2) Some)
        have "collect_verts M i \<noteq> {}"
          by (simp add: assms(1,3,5,6) branching_properly_children_nempty collect_verts_nempty)
        then obtain j' where j': "collect_verts M i \<inter> collect_verts M j' \<noteq> {}" "j' \<in> set vs"
          using 1(2) by(auto simp add: collect_verts_simps[OF assms(1), of j] Some 2)
        have "collect_verts M i \<subseteq> collect_verts M j'" 
        proof(rule ccontr, goal_cases)
          case 1
          then obtain j'' where j'': "collect_verts M i \<inter> collect_verts M j'' \<noteq> {}"
                    "j'' \<in> set vs" "j'' \<noteq> j'"
          using one(2) by(auto simp add: collect_verts_simps[OF assms(1), of j] Some 2)
          then show ?case sorry
        qed
          using 1(2) apply(auto simp add: collect_verts_simps[OF assms(1), of j] Some 2)
          subgoal for x xa xb xc
          using branching_properlyD[OF assms(5) lookup_Mi]
                disjoint_elem_vertsD[OF assms(8) lookup_Mi, of j' xa] 
                distinct_childrenD[OF assms(7) lookup_Mi]
       then obtain j' where j': "ids_of_sub_laminars M i \<subseteq> ids_of_sub_laminars M j'" "j' \<in> set vs"
        
        then obtain j' where j': "ids_of_sub_laminars M i \<subseteq> ids_of_sub_laminars M j'" "j' \<in> set vs"
          using IH(2)
          using assms(1,3) "2"(2) Some IH(2)
            inf.absorb_iff2[of "ids_of_sub_laminars M i" "ids_of_sub_laminars M j"] 
            self_in_ids[OF assms(1), of i] ids_mono[OF assms(1), of i]
            in_ids_of_sub_laminars_cases[OF assms(1), of i j]
            IntE[of i "ids_of_sub_laminars M j" "ids_of_sub_laminars M i"] 
          apply auto
           apply (metis in_mono) 
          
        moreover hence "j' \<in> ids_of_sub_laminars M j" 
          using 2(2) Some assms(3) ids_of_sub_laminars_simps[OF assms(1), of j'] 
                self_in_ids[OF assms(1), of i] self_in_ids[OF assms(1), of j'] 
          by(fo rce simp add: ids_of_sub_laminars_simps[OF assms(1), of j]
                      split: option.split contracted_laminar.split)
        moreover have "j' \<notin> ids_of_sub_laminars M i"
          using False calculation(1,2) assms(3) self_in_ids[OF assms(1), of i]
                ids_mono[OF assms(1), of j'] not_in_subtree[OF assms(1), of i]
          by(force elim!: in_ids_of_sub_laminars_cases[OF assms(1), of j' i])
        ultimately have i_in_j':"ids_of_sub_laminars M i \<subset> ids_of_sub_laminars M j'" 
          using assms(1,3) ids_of_sub_laminars_simps[of M j'] self_in_ids[of M i] self_in_ids[of M j']
          by force
        then obtain i' vs where "lookup M i' = Some (subverts vs)" "i \<in> set vs"
          using IH(1)[OF 2 j'(2) i_in_j'] by auto
        then show ?thesis
          by auto
      qed
    qed
  qed
qed
*)
lemma collect_eq_dest:"Collect P = Collect Q \<Longrightarrow> (\<And> x. P x \<longleftrightarrow> Q x)"
  by auto

lemma finite_image_subst:
 "\<lbrakk>finite A; B = f ` A\<rbrakk> \<Longrightarrow> finite B"
  by auto

lemma finite_all_verts_dom:
  "finite (dom (lookup M)) \<Longrightarrow> finite (all_verts M)"
  by(auto intro!: finite_image_subst[of " {i | i v. lookup M i = Some (elem_vert v)}" _ 
                     "\<lambda> i. the_vert (the (lookup M i))"] 
                  finite_subset[of _ "dom (lookup M)"] rev_image_eqI
        simp add: all_verts_def)

lemma important_properties:
  assumes "laminar_forest_invar (tops, M)"
  shows  "inj_on (collect_verts M) (dom (lookup M))" (is ?th1)
  and "laminar (all_verts M) ({collect_verts M i| i. i \<in> dom (lookup M)})" (is ?th2)
  and "bij_betw (collect_verts M) (dom (lookup M)) {collect_verts M i| i. i \<in> dom (lookup M)}" (is ?th3)
  and "card (dom (lookup M)) \<le> 2 * card (all_verts M) - 1" (is ?th4)
  and "max_ids M = {i | i. i \<in> dom (lookup M) \<and>
          collect_verts M i \<in> maximal_sets {collect_verts M i| i. i \<in> dom (lookup M)}}" (is ?th5)
  and "\<And> i vs. lookup M i = Some (subverts vs) \<Longrightarrow> card (collect_verts M i) > 1" 
             (is "\<And> i vs. ?asm i vs \<Longrightarrow> ?th6 i")
proof-
  note laminar_forest_invarD = laminar_forest_invarD[OF assms]
  note disjointness_over_verts = 
        disjoint_elems_over_trees_if_disjoint_subids_and_elem_unique_id 
          [OF laminar_forest_invarD(7,6,5)]
        disjoint_elems_if_disjoint_subids_and_elem_unique_id
          [OF laminar_forest_invarD(7,6,4)]
show th2: ?th2
proof(rule laminarI, goal_cases)
  case (1 X Y)
  then obtain i j where ij: "i \<in> dom (lookup M)" "X = collect_verts M i"
                        "j \<in> dom (lookup M)" "Y = collect_verts M j"
    by auto
  then obtain i' j' where i'j':"i' \<in> max_ids M" "i \<in> ids_of_sub_laminars M i'"
       "j' \<in> max_ids M" "j \<in> ids_of_sub_laminars M j'"
    by (meson assms laminar_forest_invar.simps in_dom_a_max_id)
  show ?case 
  proof(rule ccontr, goal_cases)
    case 1
    hence props: "\<not> X \<subseteq> Y" "\<not> Y \<subseteq> X" "X \<inter> Y \<noteq> {}"
      by auto
    hence "i' = j'"
      using ij(2,4) i'j' disjoint_elems_over_treesD[OF disjointness_over_verts(1) i'j'(1,3)] 
      by(auto simp add: collect_verts_uf[OF laminar_forest_invarD(7), of i'] 
                        collect_verts_uf[OF laminar_forest_invarD(7), of j'])
    hence "X \<subseteq> Y \<or> Y \<subseteq> X \<or> X \<inter> Y = {}"
      using i'j'(2,4) disjointness_over_verts(2)
      by(intro disjoint_elem_verts_prelaminarity[of M _ i _ j j'] laminar_forest_invarD(7) ij(2,4))
     simp+
    thus False 
      using props by simp
  qed
next
  case (2 X)
  then obtain i where i: "i \<in> dom (lookup M)" "X = collect_verts M i"
    by auto
  thus ?case
    using all_verts_def laminar_forest_invarD(10,7,9) collect_verts_nempty collect_verts_uf'
    by (auto simp add: branching_properly_children_nempty)
qed
  show th1: ?th1
  proof (rule inj_onI, rule ccontr, goal_cases)
    case (1 i j)
    note one = this
    then obtain i' j' where i'j': "i' \<in> max_ids M" "i \<in> ids_of_sub_laminars M i'"
       "j' \<in> max_ids M" "j \<in> ids_of_sub_laminars M j'"
      by (meson assms laminar_forest_invar.simps in_dom_a_max_id)
    hence "(ids_of_sub_laminars M i' \<inter> ids_of_sub_laminars M j' = {} \<and> i' \<noteq> j') \<or> i' = j'"
      using laminar_forest_invarD(5) disjoint_treesD by force
    thus ?case
    proof(elim disjE,goal_cases)
      case 1
      hence "collect_verts M j' \<inter> collect_verts M i' = {}"
        using disjoint_elems_over_treesD[OF disjointness_over_verts(1) i'j'(1,3)] by auto
      moreover have "collect_verts M i \<subseteq> collect_verts M i'" 
        using i'j'(2)  collect_verts_uf[OF laminar_forest_invarD(7)] by fast
      moreover have "collect_verts M j \<subseteq> collect_verts M j'" 
        using i'j'(4)  collect_verts_uf[OF laminar_forest_invarD(7)] by fast
      moreover have "collect_verts M j' \<inter> collect_verts M i' \<noteq>{}"
        using laminar_forest_invarD(10,7,9) calculation(2,3) collect_verts_nempty one(1,3)
              branching_properly_children_nempty
        by fastforce
      ultimately show False
        by simp
    next
      case 2
      thus False
        using laminar_forest_invarD(10,11,6,7,9) disjoint_elem_verts_pre_inj_of_collect
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
          simp add: bij_betw_same_card th2 laminar_forest_invarD(8))
  show th5: ?th5
  proof(rule, all \<open>rule\<close>, goal_cases)
    case (1 i)
    note one = this
    hence i_props:"lookup M i \<noteq> None"
           "(\<nexists> i' vs. lookup M i' = Some (subverts vs) \<and> i \<in> set vs)" 
      by(auto simp add: max_ids_def)
    have "collect_verts M i \<in> maximal_sets {collect_verts M i |i. i \<in> dom (lookup M)}"
    proof(rule in_maximal_setsI, goal_cases)
      case 1
      then show ?case 
        using i_props(1) by auto
    next
      case 2
      then show ?case 
      proof(rule ccontr, goal_cases)
        case 1
        then obtain i' where i': "i' \<in> dom (lookup M)" "collect_verts M i \<subset> collect_verts M i'" 
          by auto
        then obtain vs where "lookup M i' = Some (subverts vs)"
        proof(cases "lookup M i'", goal_cases)
          case 1
          then show ?thesis 
            by auto
        next
          case (2 a)
          then show ?thesis 
            using i_props(1) laminar_forest_invarD(10,7,9)
              all_not_in_conv[of "collect_verts M i"] domIff[of i "lookup M"]
              collect_verts_nempty[of M i]
              branching_properly_children_nempty[of M] in_mono[of "collect_verts M i" "collect_verts M i'"]
            by (cases a)(auto simp add: collect_verts_simps[of M i'])
        qed
        moreover then obtain k where k: "k\<in>max_ids M" "i' \<in> ids_of_sub_laminars M k"
          using in_dom_a_max_id laminar_forest_invarD(7,8) by auto
        moreover hence "ids_of_sub_laminars M i \<inter> ids_of_sub_laminars M k = {}" 
          using  laminar_forest_invarD(7) i'(2)
          by (intro disjoint_treesD[OF laminar_forest_invarD(5)])
             (auto simp add: one  collect_verts_uf[of _ i]) 
        moreover have "collect_verts M i \<inter> collect_verts M k = {}"
          using laminar_forest_invarD(7) i'(2) one k
          by (intro disjoint_elems_over_treesD[OF disjointness_over_verts(1)])
             (auto simp add: one  collect_verts_uf[of _ i]) 
        moreover have "collect_verts M i \<noteq> {}"
          by (simp add: branching_properly_children_nempty collect_verts_nempty domIff i_props(1)
              laminar_forest_invarD(10,7,9))
        ultimately obtain i'' vs' where "lookup M i'' = Some (subverts vs')" "i \<in> set vs'"
          using i'(2) by(force simp add: collect_verts_uf[OF laminar_forest_invarD(7), of k])
        then show ?case 
          using i_props by simp
      qed
    qed
    then show ?case
      using i_props(1) by blast
  next
    case (2 i)
    note two = this
    hence i_props: "i \<in> dom (lookup M)"
          "\<And> j. j \<in> dom (lookup M) \<Longrightarrow> \<not> collect_verts M j \<supset> collect_verts M i"
      by(auto simp add: maximal_sets_def)
    show ?case 
    proof(rule ccontr, goal_cases)
      case 1
      then obtain i' vs where i': "lookup M i' = Some (subverts vs)" "i \<in> set vs" 
        using i_props(1) by (auto simp add: max_ids_def)
      then obtain j where j:"j \<in> set vs" "j \<noteq> i" 
        using laminar_forest_invarD(11,9)
        by(cases vs rule: list_cases3)
          (fastforce elim!: distinct_childrenE branching_properlyE)+
      have "collect_verts M j \<subseteq> collect_verts M i'" "collect_verts M i \<subseteq> collect_verts M i'"
        using laminar_forest_invarD(10,7) i' j(1) immediate_childrenin_ids
        by(force elim!: domain_recursiveE simp add: collect_verts_uf[of M i'])+
      moreover have "collect_verts M j \<inter> collect_verts M i = {}"
        using disjoint_elem_verts_def disjointness_over_verts(2) i'(1,2) j(1,2) by blast
      moreover have "collect_verts M j \<noteq> {}"  "collect_verts M i' \<noteq> {}"
        using  i'(1)  j(1) laminar_forest_invarD(10,7,9)
        by(auto elim!:  domain_recursiveE 
             simp add: laminar_forest_invarD(10)  branching_properly_children_nempty 
                       collect_verts_nempty domIff domain_recursiveD)
      ultimately have "collect_verts M i \<subset> collect_verts M i'"
        by auto
      then show ?case 
        using i_props i'(1) by auto
    qed
  qed
  show "\<And> i vs. ?asm i vs \<Longrightarrow> ?th6 i"
  proof(goal_cases)
    case (1 i vs)
    then obtain v1 v2 vs' where vs_split: "vs = v1#v2#vs'"
      using  laminar_forest_invarD(9)
      by(cases vs rule: list_cases3)(auto dest: branching_properlyD)
    have h1:"collect_verts M i \<supseteq> collect_verts M v1" 
          "collect_verts M i \<supseteq> collect_verts M v2" 
      by (auto simp add: "1" collect_verts_simps laminar_forest_invarD(7) vs_split)
    moreover have h2:"collect_verts M v1 \<inter> collect_verts M v2 = {}" 
      using laminar_forest_invarD(11) disjointness_over_verts(2) 1
      by(fastforce elim!: distinct_childrenD disjoint_elem_vertsE distinct_childrenE 
             simp add: vs_split) 
    moreover have h3:"finite (collect_verts M i)"
      using disjointness_over_verts(2) 
          laminar_forest_invarD(11,7)
      by(auto dest!: laminar_fold_singletons_correct[of M i undefined undefined] sym[of "set _"]) 
    ultimately have "card (collect_verts M i)
                \<ge> card (collect_verts M v1) + card (collect_verts M v2)"
      using 
        card_Un_disjoint[of "collect_verts M v1" "collect_verts M v2"]
        card_mono[of "collect_verts M i" "collect_verts M v1 \<union> collect_verts M v2"]
        finite_subset[of "collect_verts M v1" "collect_verts M i"]
        finite_subset[of "collect_verts M v2" "collect_verts M i"]
      by auto
    moreover have "card (collect_verts M v1) \<ge> 1" 
    proof-
      have "collect_verts M v1 \<noteq> {}"
        using laminar_forest_invarD(10,7,9) 1
        by(intro collect_verts_nempty[of M v1])
          (auto elim!: domain_recursiveE simp add: branching_properly_children_nempty vs_split)
      thus ?thesis
      using h1(1) h3 rev_finite_subset by(auto simp add: card_geq_1_iff)
  qed
    moreover have "card (collect_verts M v2) \<ge> 1" 
    proof-
      have "collect_verts M v2 \<noteq> {}"
        using laminar_forest_invarD(10,7,9) 1
        by(intro collect_verts_nempty[of M v2])
          (auto elim!: domain_recursiveE simp add: branching_properly_children_nempty vs_split)
      thus ?thesis
      using h1(2) h3 rev_finite_subset by(auto simp add: card_geq_1_iff)
  qed
  ultimately show ?case
    by linarith
qed
qed

interpretation laminar_family_spec_statisfied: laminar_family_spec
  where all_ids = "\<lambda> (maxes, L). dom (lookup L)"
  and universe =  "\<lambda> (maxes, L). all_verts L"
  and collect_elems = "\<lambda> (maxes, L). collect_verts L"
  and max_ids = "\<lambda> (maxes, L). max_ids L"
  and laminar_invar = laminar_forest_invar
  and laminar_abstract = "\<lambda> (maxes, L). {collect_verts L i | i. i \<in> dom (lookup L)}"
  and compound = compound
proof(rule laminar_family_spec.intro, goal_cases)
  case (1 L i)
  then show ?case  
    using collect_verts_uf'
    by (auto simp add: all_verts_def)
next
  case (2 L)
  then show ?case 
  proof(cases L, goal_cases)
    case (1 top L)
    then show ?case 
      using important_properties(5)[of top L]
      by simp
  qed
next
  case (3 L)
  then show ?case
  proof(cases L, goal_cases)
    case (1 top L)
    then show ?case 
      by(auto intro!: forw_subst[of _ _ "laminar (all_verts L)",
                   OF _ important_properties(2)[of top L]])
  qed
next
  case (4 L)
  then show ?case 
  proof(cases L, goal_cases)
    case (1 top L)
    then show ?case 
      using important_properties(3)[of top L] 
      by simp
  qed
next
  case (5 L id)
  then show ?case
  proof(cases L, goal_cases)
    case (1 top L)
    note one = this
    then show ?case 
    proof(cases "lookup L id", goal_cases)
      case 1
      then show ?thesis 
        by(auto simp add: compound_def)
    next
      case (Some a)
      then show ?thesis 
      proof(cases a, goal_cases)
        case (1 x1)
        then show ?case
          using 5
          by(auto simp add: compound_def one)
      next
        case (2 x2)
        then show ?case 
          using important_properties(6)[of top L id] 5 one 
          by simp
      qed
    qed
  qed
qed

lemma new_laminar_max_ids:
  assumes  "wf {(j, i) | i j vs. lookup M i = Some (subverts vs) \<and>j \<in> set vs}"
  assumes  "set vs \<subseteq> max_ids M" "i \<notin> dom (lookup M)"
           "M' = update i (subverts vs) M"
   shows  "wf {(j, i) | i j vs. lookup M' i = Some (subverts vs) \<and>j \<in> set vs}"
          "ids_of_sub_laminars M "

inductive disjoint_subids where
  "lookup M i = Some (elem_vert x) \<Longrightarrow> disjoint_subids i" |
  "lookup M i = Some (elem_vert x) \<Longrightarrow> disjoint_subids i"


end
end