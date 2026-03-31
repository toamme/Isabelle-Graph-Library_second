section \<open>Laminar Families\<close>

theory Laminar_Family
  imports Main "HOL-Eisbach.Eisbach"
begin

lemma card_geq_1_iff: "card X \<ge> Suc 0 \<longleftrightarrow> (finite X \<and> X \<noteq> {})"
  using  card_gt_0_iff[of X] by auto

definition "laminar U \<X> = 
            ((\<forall> X Y. X \<in> \<X> \<longrightarrow> Y \<in> \<X> \<longrightarrow> (X \<subseteq> Y \<or> Y \<subseteq> X \<or> X \<inter> Y = {}))
            \<and> (\<forall> X \<in> \<X>. X \<noteq> {} \<and> X \<subseteq> U))"

lemma laminarI: 
 "\<lbrakk>\<And> X Y. \<lbrakk>X \<in> \<X>; Y \<in> \<X>\<rbrakk> \<Longrightarrow> (X \<subseteq> Y \<or> Y \<subseteq> X \<or> X \<inter> Y = {});
   \<And> X.  X \<in> \<X> \<Longrightarrow> X \<noteq> {} \<and> X \<subseteq> U\<rbrakk> \<Longrightarrow> laminar U \<X>"
and  laminarE: 
 "\<lbrakk>laminar U \<X>;
   \<lbrakk>\<And> X Y. \<lbrakk>X \<in> \<X>; Y \<in> \<X>\<rbrakk> \<Longrightarrow> (X \<subseteq> Y \<or> Y \<subseteq> X \<or> X \<inter> Y = {});
    \<And> X.  X \<in> \<X> \<Longrightarrow> X \<noteq> {} \<and> X \<subseteq> U\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(auto simp add: laminar_def)

lemma finite_U_finite_family:
  "\<lbrakk>finite U; laminar U \<X>\<rbrakk> \<Longrightarrow> finite \<X>"
  by (meson Sup_le_iff finite_UnionD finite_subset laminar_def)

lemma laminar_subset:
 "\<lbrakk>laminar U \<X>; U \<subseteq> U'; \<X>' \<subseteq> \<X>\<rbrakk> \<Longrightarrow> laminar U' \<X>'"
  by(auto intro!: laminarI elim!: laminarE) blast+

lemma laminar_union:
 "\<lbrakk>laminar U \<X>; laminar U' \<X>'; U \<inter> U' = {}\<rbrakk> \<Longrightarrow> laminar (U \<union> U') (\<X> \<union> \<X>')"
  by(auto intro!: laminarI 
           elim!: laminarE 
        simp add: subset_eq[of _ U'] subset_eq[of _ U] disjoint_iff[of U U'], force, force)
    (metis disjoint_insert(1) insert_absorb insert_subset)

lemma empty_nin_laminar: "laminar U \<X> \<Longrightarrow> {} \<notin> \<X>"
  by(auto elim!: laminarE)

lemma laminar_Union_finite: "\<lbrakk>finite U; laminar U \<X>\<rbrakk> \<Longrightarrow> finite (\<Union> \<X>)"
  by(auto intro!: finite_Union rev_finite_subset[of U] 
           elim!: laminarE simp add: finite_U_finite_family laminarI) 

definition "maximal_sets \<X> = { X| X. X \<in> \<X> \<and> (\<nexists> Y. Y \<in> \<X> \<and> Y \<supset> X)}"

lemma in_maximal_setsE:
  "\<lbrakk>X \<in> maximal_sets \<X>; \<lbrakk>X \<in> \<X>; \<And> Y. Y \<in> \<X> \<Longrightarrow> \<not> Y \<supset> X\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
and in_maximal_setsI:
  "\<lbrakk>X \<in> \<X>; \<nexists> Y. Y \<in> \<X> \<and> Y \<supset> X\<rbrakk> \<Longrightarrow> X \<in> maximal_sets \<X>"
and in_maximal_setsD:
  "\<lbrakk>X \<in> maximal_sets \<X>; X \<in> \<X>; Y \<in> \<X>\<rbrakk> \<Longrightarrow> \<not> Y \<supset> X"
  by (auto simp add: maximal_sets_def)

lemma maximal_sets_subset: "maximal_sets \<X> \<subseteq> \<X>"
  by(auto simp add: maximal_sets_def)

lemma disjoint_maximal_sets_insert:
  assumes "maxes \<subseteq> maximal_sets \<X>" "maxes \<noteq> {}" 
          "\<And> X Y. \<lbrakk>X \<in> maxes; Y \<in> maxes\<rbrakk> \<Longrightarrow> X \<inter> Y = {}"
  shows   "maximal_sets (insert (\<Union> maxes) \<X>) = maximal_sets \<X> - maxes \<union> {\<Union> maxes}"
  using assms
  by(force simp add: maximal_sets_def)

lemma finite_there_is_maximal_set:
  "\<lbrakk>finite \<X>; X \<in> \<X>\<rbrakk> \<Longrightarrow> \<exists> M \<in> maximal_sets \<X>. X \<subseteq> M"
  by (auto dest!: finite_has_maximal2 simp add: maximal_sets_def)

lemma finite_maximal_set:
  "\<lbrakk>finite (\<Union> \<X>); X \<in> maximal_sets \<X>\<rbrakk> \<Longrightarrow> finite X"
  by (meson Sup_upper in_maximal_setsE rev_finite_subset)

lemma split_with_maximal_sets:
  "finite \<X> \<Longrightarrow> \<X> = \<Union> {{X | X. X \<in> \<X> \<and> X \<subseteq> M} | M. M \<in> maximal_sets \<X>}" 
proof(rule, goal_cases)
  case 1
  then show ?case 
    by (auto dest!: finite_there_is_maximal_set)
next
  case 2
  then show ?case 
    by auto
qed

lemma union_split_with_maximal_sets:
  "finite \<X> \<Longrightarrow> \<Union> \<X> = \<Union> (maximal_sets \<X>)" 
proof(rule, goal_cases)
  case 1
  then show ?case 
    by (auto dest!: finite_there_is_maximal_set)
next
  case 2
  then show ?case 
    by (simp add: Sup_subset_mono maximal_sets_subset)
qed
 
lemma laminar_maximal_sets_disjoint:
 "\<lbrakk>laminar U \<X>; X \<in> maximal_sets \<X>; Y \<in> maximal_sets \<X>; X \<noteq> Y\<rbrakk> \<Longrightarrow> X \<inter> Y = {}"
  by(auto elim!: laminarE simp add: maximal_sets_def) fast+

lemma maximal_disjoint_subsets_disjoint:
  assumes  "M \<in> maximal_sets \<X>"  "M' \<in> maximal_sets \<X>" "M \<inter> M' = {}" "{} \<notin> \<X>"
  shows "{X |X. X \<in> \<X> \<and> X \<subseteq> M} \<inter> {X |X. X \<in> \<X> \<and> X \<subseteq> M'} = {}"
  using assms
  by (auto simp add: maximal_sets_def) (metis le_inf_iff subset_empty)

lemma laminar_maximal_sets_nempty:
 "\<lbrakk>laminar U \<X>; X \<in> maximal_sets \<X>\<rbrakk> \<Longrightarrow> X \<noteq> {}"
  by(auto elim!: laminarE simp add: maximal_sets_def)

lemma laminar_union_maximal_sets_not_in:
 "\<lbrakk>laminar U \<X>; X \<in> maximal_sets \<X>; Y \<in> maximal_sets \<X>; X \<noteq> Y\<rbrakk> \<Longrightarrow> X \<union> Y \<notin> \<X>"
  by(auto elim!: laminarE simp add: maximal_sets_def)

lemma insertE_strict:
  "\<lbrakk>y \<in> insert x X; y \<in> X \<Longrightarrow> P; \<lbrakk>y = x;y \<notin> X\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by blast

lemma laminar_extension_with_maximal_sets:
  assumes "laminar U \<X>" "\<Y> \<subseteq> maximal_sets \<X>" "\<Y> \<noteq> {}"
  shows "laminar U (insert (\<Union> \<Y>) \<X>)"
proof(cases "(\<Union> \<Y>) \<in> \<X>")
  case True
  hence "insert (\<Union> \<Y>) \<X> = \<X>" by blast
  then show ?thesis 
    using assms(1) by simp 
next
  case False
  show ?thesis 
  proof(rule laminarI, goal_cases)
    case (1 X Y)
    then show ?case 
  proof(elim insertE_strict, goal_cases)
    case 1
    then show ?case
      using assms(1) by(auto elim!: laminarE)
  next
    case 2
    have "\<lbrakk>X \<in> \<X>; x \<in> X; \<forall>xa\<in>\<Y>. x \<notin> xa; xa \<in> Xa; Xa \<in> \<Y>; xa \<notin> X; xb \<in> X; xb \<in> Xaa; Xaa \<in> \<Y>\<rbrakk>
          \<Longrightarrow> False"
      for x xa Xa xb Xaa
       proof(goal_cases)
      case 1
      then show ?case 
      proof(cases "Xa = Xaa", goal_cases)
        case 1
        then show ?case 
          using  assms(1,2)  maximal_sets_subset[of \<X>] 
          by(auto elim!: laminarE simp add: disjoint_iff dest!: subsetD)       
      next
        case 2
        hence maximals:"Xa \<in> maximal_sets \<X>" "Xaa \<in> maximal_sets \<X>"
          using assms(2) by auto
        hence "X \<subseteq> Xaa \<or> Xaa \<subseteq> X \<or> X \<inter> Xaa = {}" 
          using "2"(1,5) assms(1)
          by(auto elim!: in_maximal_setsE laminarE)
        moreover have "Xaa \<in> \<X>" 
          using in_maximal_setsE maximals(2) by blast
        moreover have "\<not> Xaa \<subset> X"
           using "2"(1)  maximals(2)
           by(auto elim!: in_maximal_setsE)
        ultimately show ?case 
          using "2"(2-9) by auto  
      qed
    qed
    then show ?case 
      using 2 by blast
  next
    case 3
    note 2 = this
     have "\<lbrakk>Y \<in> \<X>; x \<in> Y; \<forall>xa\<in>\<Y>. x \<notin> xa; xa \<in> Xa; Xa \<in> \<Y>; xa \<notin> Y; xb \<in> Y; xb \<in> Xaa; Xaa \<in> \<Y>\<rbrakk>
          \<Longrightarrow> False"
      for x xa Xa xb Xaa
       proof(goal_cases)
      case 1
      then show ?case 
      proof(cases "Xa = Xaa", goal_cases)
        case 1
        then show ?case 
          using  assms(1,2)  maximal_sets_subset[of \<X>] 
          by(auto elim!: laminarE simp add: disjoint_iff dest!: subsetD)       
      next
        case 2
        hence maximals:"Xa \<in> maximal_sets \<X>" "Xaa \<in> maximal_sets \<X>"
          using assms(2) by auto
        hence "Y \<subseteq> Xaa \<or> Xaa \<subseteq> Y \<or> Y \<inter> Xaa = {}" 
          using "2"(1,5) assms(1)
          by(auto elim!: in_maximal_setsE laminarE)
        moreover have "Xaa \<in> \<X>" 
          using in_maximal_setsE maximals(2) by blast
        moreover have "\<not> Xaa \<subset> Y"
           using "2"(1)  maximals(2)
           by(auto elim!: in_maximal_setsE)
        ultimately show ?case 
          using "2"(2-9) by auto  
      qed
    qed
    then show ?case 
      using 2 by blast
  next
    case 4
    then show ?case 
      by simp
  qed
  next
    case (2 X)
    then show ?case 
      using assms(1-3) by (force elim!: laminarE  in_maximal_setsE)
  qed
qed

lemma laminar_family_number_of_sets:
  assumes "n = card U" "finite U" "laminar U \<X>"
  shows "card \<X> \<le> 2 * n - 1"
  using assms
proof(induction n arbitrary: \<X> U)
  case 0
  then show ?case 
    unfolding laminar_def by simp
next
  case (Suc n)
  note IH = this
  show ?case 
  proof(cases n)
    case 0
    then obtain x where x_prop:"U = {x}" 
      using Suc.prems(1) card_1_singletonE by auto
    hence "\<X> = {{x}} \<or> \<X> = {}"
    proof(cases "\<X> = {}")
      case False
      then obtain X where "X \<in> \<X>" by auto
      hence "X = {x}"
        using Suc(4) x_prop unfolding laminar_def by auto
      moreover have "Y \<in> \<X> \<Longrightarrow> Y = {x}" for Y
        using Suc(4) x_prop unfolding laminar_def by auto
      ultimately show ?thesis by auto
    qed simp
    then show ?thesis
      by force
  next
    case (Suc nat)
    have "card \<X> = 0 \<Longrightarrow> card \<X> \<le> 2 * Suc n - 1" by simp
    moreover have "card \<X> = 1 \<Longrightarrow> card \<X> \<le> 2 * Suc n - 1" by simp
    moreover have "card \<X> \<ge> 2 \<Longrightarrow> card \<X> \<le> 2 * Suc n - 1"
    proof(goal_cases)
      case 1
      note cardX = this
    then obtain x V where x_V_prop:"U = insert x V \<and> x \<notin> V"
      by (metis Suc.prems(1) card_Suc_eq)
    have V_non_empt: "V \<noteq> {}"
      using Suc Suc.prems(1) x_V_prop by fastforce
    define \<Y> where "\<Y> = {X - {x} | X.  X \<in> \<X> \<and> X - {x} \<noteq> {}}"
    have laminar_Y: "laminar V \<Y>"
    proof(rule laminarI, goal_cases)
      case (1 X Y)
      note XY = this
      obtain X' where X'_prop: "X = X' \<or> insert x X = X'" "X' \<in> \<X>"
        using 1 unfolding \<Y>_def by auto
      obtain Y' where Y'_prop: "Y = Y' \<or> insert x Y = Y'" "Y' \<in> \<X>"
        using 1 unfolding \<Y>_def by auto
      have xXY: "x \<notin> X" "x \<notin> Y" 
        using XY unfolding \<Y>_def by auto
      have "\<not> X \<subseteq> Y \<Longrightarrow> \<not> Y \<subseteq> X \<Longrightarrow> \<not>  X \<inter> Y = {} \<Longrightarrow> False"
      proof(goal_cases)
        case 1
        obtain a where aXY: "a \<in> X" "a \<notin> Y" using 1 by auto
        have a1:"a \<noteq> x" 
          using \<open>a \<in> X\<close> xXY(1) by auto
        hence a2:"a \<notin> Y'" 
          using Y'_prop(1) aXY(2) by blast
        have a3: "\<not> X' \<subseteq> Y'"  
          using X'_prop(1) a2 aXY(1) by blast
        obtain b where bXY: "b \<in> Y" "b \<notin> X" using 1 by auto
        have a4:"b \<noteq> x" 
          using bXY(1) xXY(2) by blast
        hence a5:"b \<notin> X'" 
          using X'_prop(1) bXY(2) by auto
        have a6: "\<not> Y' \<subseteq> X'"  
          using Y'_prop(1) a5 bXY(1) by blast
        have "X' \<inter> Y' = {}" 
          using Suc.prems(3) X'_prop(2) Y'_prop(2) a3 a6 unfolding laminar_def by auto
        hence "X \<inter> Y = {}"
          using X'_prop(1) Y'_prop(1) by blast
        thus False using 1(3) by simp
      qed
      thus ?case by auto
    next
      case (2 X)
      note XX = this
      obtain X' where X'_prop: "X = X' \<or> (insert x X = X' \<and> x \<notin> X)" "X' \<in> \<X>"
        using 2 unfolding \<Y>_def by auto
      have "X \<noteq> {}"
        using "2" \<Y>_def by fastforce
      moreover have "X \<subseteq> V"
      proof(cases rule: disjE[OF  X'_prop(1)])
        case 1
        hence "x \<notin> X'"
          using XX \<Y>_def by blast
        then show ?thesis 
          using "1" Suc.prems(3) X'_prop(2) x_V_prop
          unfolding laminar_def 
          by auto
      next
        case 2
        then show ?thesis 
          using  Suc.prems(3) X'_prop(2)   x_V_prop 
          unfolding  laminar_def by auto
      qed
      ultimately show ?case by simp
    qed
    have cardY: "card \<Y> \<le> 2 * n - 1"
      using Suc.prems(1) Suc.prems(2) x_V_prop  
      by (fastforce intro!: IH(1)[OF _ _  laminar_Y])
    have finite_X: "finite \<X>"
      using IH(4)[simplified laminar_def] IH(3) 
      by (simp add: Suc.prems(3) finite_U_finite_family)
    hence finite_Y: "finite \<Y>" unfolding \<Y>_def
      by simp
    have "\<Y> \<subseteq> {X. X \<in> \<X> \<and> x \<notin> X \<and> insert x X \<notin> \<X>}
            \<union> {X. X \<in> \<X> \<and> x \<notin> X \<and> insert x X \<in> \<X>}
            \<union> {X. X \<notin> \<X> \<and> x \<notin> X \<and> insert x X \<in> \<X> \<and> X \<noteq> {}}" 
      unfolding \<Y>_def 
    proof(rule, goal_cases)
      case (1 Y)
      then obtain X where X_pr:"X \<in> \<X> " "X - {x} \<noteq> {}" "Y = X - {x}"
        by auto
      show ?case
      proof(cases "Y \<in> \<X>")
        case True
        then show ?thesis 
          using X_pr by simp
      next
        case False
        hence " insert x Y = X"
          using X_pr(1) X_pr(3) by auto
        moreover have "Y \<noteq> {}" 
          using X_pr(2) X_pr(3) by blast
        ultimately show ?thesis 
          by (simp add: X_pr(1) X_pr(3))
      qed
    qed
    moreover have "{X. X \<in> \<X> \<and> x \<notin> X \<and> insert x X \<notin> \<X>} \<subseteq> \<Y>" 
      unfolding \<Y>_def 
    proof(rule, goal_cases)
      case (1 X)
      hence "X \<in> \<X> \<and> x \<notin> X \<and> insert x X \<notin> \<X>" by simp
      hence "X \<in> \<X> \<and> X - {x} \<noteq> {}" "X = X - {x}"
        using Suc.prems(3) laminar_def
        by (fastforce, simp add: \<open>X \<in> \<X> \<and> x \<notin> X \<and> insert x X \<notin> \<X>\<close>)
      then show ?case 
        by auto
    qed
    moreover have "{X. X \<in> \<X> \<and> x \<notin> X \<and> insert x X \<in> \<X>} \<subseteq> \<Y>" 
      unfolding \<Y>_def
    proof(rule, goal_cases)
      case (1 X)
      hence "X \<in> \<X> \<and> x \<notin> X \<and> insert x X \<in> \<X>" by simp
      moreover hence "insert x X \<in> \<X> \<and> insert x X - {x} \<noteq> {}"
        using Suc.prems(3) laminar_def by fastforce
      ultimately show ?case
        by blast
    qed
    moreover have " {X. X \<notin> \<X> \<and> x \<notin> X \<and> insert x X \<in> \<X> \<and> X \<noteq> {}} \<subseteq> \<Y>" 
      unfolding \<Y>_def 
    proof(rule, goal_cases)
      case (1 X)
      hence " insert x X \<in> \<X> \<and> (insert x X) - {x} \<noteq> {}" 
        by blast
      moreover hence "X = (insert x X) - {x}" 
        using 1 by auto
      ultimately show ?case by force
    qed
    ultimately have Y_same:"\<Y> = {X. X \<in> \<X> \<and> x \<notin> X \<and> insert x X \<notin> \<X>}
            \<union> {X. X \<in> \<X> \<and> x \<notin> X \<and> insert x X \<in> \<X>}
            \<union> {X. X \<notin> \<X> \<and> x \<notin> X \<and> insert x X \<in> \<X> \<and> X \<noteq> {}}" by auto
(*TODO MOVE*)
    have add_cong1: "a = b \<Longrightarrow> c + a = c + b" for a b c by simp
    have add_cong2: "a = b \<Longrightarrow> a +c = b + c" for a b c by simp
    have aa: "finite {X. X \<notin> \<X> \<and> x \<notin> X \<and> insert x X \<in> \<X> \<and> X \<noteq> {}}"
      using \<open>{X. X \<notin> \<X> \<and> x \<notin> X \<and> insert x X \<in> \<X> \<and> X \<noteq> {}} \<subseteq> \<Y>\<close> finite_Y infinite_super by auto
    have bb:"{X \<in> \<X>. x \<in> X \<and> X - {x} \<notin> \<X> \<and> X - {x} \<noteq> {}}
           \<subseteq> insert x ` {X. X \<notin> \<X> \<and> x \<notin> X \<and> insert x X \<in> \<X> \<and> X \<noteq> {}}"
    proof(rule, goal_cases)
      case (1 Y)
      hence "(Y- {x}) \<notin> \<X> \<and> x \<notin> (Y- {x}) \<and> insert x (Y- {x}) \<in> \<X> \<and> (Y- {x}) \<noteq> {}"
        by (simp add: insert_absorb)
      moreover hence "insert x (Y - {x}) = Y" 
        using "1" by blast
      ultimately show ?case by blast
    qed    
    have " card ({X. X \<in> \<X> \<and> x \<notin> X \<and> insert x X \<notin> \<X>}
            \<union> {X. X \<in> \<X> \<and> x \<notin> X \<and> insert x X \<in> \<X>}
            \<union> {X. X \<notin> \<X> \<and> x \<notin> X \<and> insert x X \<in> \<X> \<and> X \<noteq> {}}) =
           card {X. X \<in> \<X> \<and> x \<notin> X \<and> insert x X \<notin> \<X>} +
           card {X. X \<in> \<X> \<and> x \<notin> X \<and> insert x X \<in> \<X>} +
           card {X. X \<notin> \<X> \<and> x \<notin> X \<and> insert x X \<in> \<X> \<and> X \<noteq> {}}"
      apply(subst card_Un_disjnt[OF _ aa], simp add: finite_X, subst disjnt_Un1, rule)
      using finite_X  disjnt_iff
      by (blast, blast, subst card_Un_disjnt) auto
    also have "... = card {X. X \<in> \<X> \<and> x \<notin> X \<and> insert x X \<notin> \<X>} +
           card {X. X \<in> \<X> \<and> x \<notin> X \<and> insert x X \<in> \<X>} +
           card {X. X \<in> \<X> \<and> x \<in> X \<and> X - {x}  \<notin> \<X> \<and> X - {x} \<noteq> {}}"
      using bb 
      by (auto intro!:add_cong1 bij_betw_same_card[where f="insert x"] 
             simp add: bij_betw_def inj_on_def)
    also have "... = card ({X. X \<in> \<X> \<and> x \<notin> X \<and> insert x X \<notin> \<X>}
                           \<union> {X. X \<in> \<X> \<and> x \<notin> X \<and> insert x X \<in> \<X>}
                           \<union> {X. X \<in> \<X> \<and> x \<in> X \<and> X - {x}  \<notin> \<X> \<and> X - {x} \<noteq> {}})"
      apply(subst card_Un_disjnt[OF])
      using finite_X apply(simp, simp)
      apply(fastforce simp add: disjnt_iff , rule add_cong2, subst card_Un_disjnt)
      using finite_X disjnt_iff by auto
    also have "... = card (\<X> - insert {x} {X. X \<in> \<X> \<and> x \<in> X \<and> X - {x}  \<in> \<X> \<and> X - {x} \<noteq> {}})"
    proof(rule cong[of _ card, OF refl], rule, goal_cases)
      case 1
      show ?case 
      proof(rule, goal_cases)
        case (1 Y)
        hence "Y \<in> \<X>" by auto
        moreover have " Y \<notin> insert {x} {X \<in> \<X>. x \<in> X \<and> X - {x} \<in> \<X> \<and> X - {x} \<noteq> {}}"
          using 1 by blast
        ultimately show ?case by simp
      qed
    next
      case 2
      show ?case 
      proof(rule, goal_cases)
        case (1 Y)
        hence Y_prop: "Y \<in> \<X>"  "Y \<noteq> {x}" "Y \<notin> {X \<in> \<X>. x \<in> X \<and> X - {x} \<in> \<X> \<and> X - {x} \<noteq> {}}"
          by auto
        show ?case
        proof(cases "x \<notin> Y ")
          case True
          then show ?thesis 
            using Y_prop by simp
        next
          case False
          hence xY:"x \<in> Y" by simp
          have "x \<in> Y \<and> Y - {x} \<notin> \<X> \<and> Y - {x} \<noteq> {}"
            using False Y_prop(1) Y_prop(2) Y_prop(3) by blast
          then show ?thesis 
            using Y_prop by simp
        qed
      qed
    qed
    also have "\<dots> \<ge> card \<X> - 2"
    proof(rule order.trans[OF _ diff_card_le_card_Diff], rule diff_le_mono2,
          subst card.insert_remove, goal_cases)
      case 2
      show ?case 
      proof(rule ccontr, goal_cases)
        case 1
        then obtain X Y where X_prop: "X \<in> \<X>" "x \<in> X" "X - {x} \<in> \<X>" "\<not> X \<subseteq> {x}"
                        and   Y_prop: "Y \<in> \<X>" "x \<in> Y" "Y - {x} \<in> \<X>" "\<not> Y \<subseteq> {x}" 
                        and  X_neq_Y: "X \<noteq> Y" 
          by simp (metis (mono_tags, lifting) card.infinite card_le_Suc0_iff_eq le_SucI le_zero_eq mem_Collect_eq)
        hence X_Y_subs:"X \<subseteq> Y \<or> Y \<subseteq> X" using IH(4)[simplified laminar_def] by auto
        show ?case
        proof(rule disjE[OF X_Y_subs], goal_cases)
          case 1
          note X_subs_Y = this
          have "\<not> X \<subseteq> Y - {x}"
            using X_prop(2) by blast
          moreover have " \<not> Y - {x} \<subseteq> X"
          proof(rule , goal_cases)
            case 1
            hence "Y \<subseteq> insert x X" by auto
            moreover have "insert x X \<subseteq> X" using X_prop by simp
            ultimately show ?case using X_subs_Y X_neq_Y by auto
          qed
          moreover have "X \<inter> (Y - {x}) \<noteq> {}" 
            using X_prop(4) X_subs_Y by auto
          ultimately show ?case 
            using IH(4)[simplified laminar_def] X_prop(1) Y_prop(3) by auto
        next
          case 2
          note Y_subs_X = this
          have "\<not> Y \<subseteq> X - {x}"
            using Y_prop(2) by blast
          moreover have " \<not> X - {x} \<subseteq> Y"
          proof(rule , goal_cases)
            case 1
            hence "X \<subseteq> insert x Y" by auto
            moreover have "insert x Y \<subseteq> Y" using Y_prop by simp
            ultimately show ?case using Y_subs_X X_neq_Y by auto
          qed
          moreover have "Y \<inter> (X - {x}) \<noteq> {}" 
            using Y_prop(4) Y_subs_X by auto
          ultimately show ?case 
            using IH(4)[simplified laminar_def] Y_prop(1) X_prop(3) by auto
        qed
      qed
    qed (auto simp add: finite_X)
    finally have "card \<Y> \<ge> card \<X> - 2" 
      using Y_same by auto
    hence card_Y_card_X_2:"card \<X> \<le> card \<Y> + 2" by simp
    also have "\<dots> \<le>  2 * n - 1 + 2"
      using cardY by simp
    also have "\<dots> = 2*(Suc n) - 1" 
      by (simp add: Suc)
    finally show ?thesis by simp
  qed
  ultimately show ?thesis by force
 qed
qed

lemma laminar_card_and_maximal_sets:
  assumes "finite U" "laminar U \<X>" 
  shows   "card \<X> \<le> 2* card (\<Union> \<X>) - card (maximal_sets \<X>)"
proof-
  have X_split:"\<X> = \<Union> {{X | X. X \<in> \<X> \<and> X \<subseteq> M} | M. M \<in> maximal_sets \<X>}"
    using assms(1,2) finite_U_finite_family 
    by(intro split_with_maximal_sets) auto
  have X_split':"\<Union> \<X> = \<Union> (maximal_sets \<X>)"
    using assms(1,2) finite_U_finite_family 
    by(intro union_split_with_maximal_sets) auto
  have "card \<X> = sum card {{X | X. X \<in> \<X> \<and> X \<subseteq> M} | M. M \<in> maximal_sets \<X>}"
  proof(subst  X_split, rule card_UN_disjoint[where A = id, simplified], goal_cases)
    case 1
    then show ?case 
      using assms(1,2) X_split finite_U_finite_family[of U \<X>]
        finite_UnionD[of "{{uuba \<in> \<X>. uuba \<subseteq> uub} |uub. uub \<in> maximal_sets \<X>}"]
      by simp
  next
    case 2
    then show ?case 
      using assms(1,2) finite_U_finite_family by fastforce
  next
    case 3
    then show ?case
    proof(rule, rule,rule, rule, rule, goal_cases)
      case (1 XX YY X)
      then obtain M M' where MM': "M \<in> maximal_sets \<X>" "XX = {X |X. X \<in> \<X> \<and> X \<subseteq> M}"
          "M' \<in> maximal_sets \<X>" "YY = {X |X. X \<in> \<X> \<and> X \<subseteq> M'}"
        by auto
      hence X_props: "X \<in> \<X>" "X \<subseteq> M"  "X \<subseteq> M'"
        using 1 by auto
      then show ?case 
        using 1(3,4) MM' laminar_maximal_sets_disjoint[OF assms(2) MM'(1,3)]
              empty_nin_laminar[OF assms(2)] subset_empty[of X] 
        by blast
    next
      case (2 i j)
      then show ?case
        by simp
    qed
  qed
  also have "... = sum (\<lambda> M. card {X |X. X \<in> \<X> \<and> X \<subseteq> M}) (maximal_sets \<X>)"
  proof(subst comm_monoid_add_class.sum.reindex[of
            "\<lambda> M. {X |X. X \<in> \<X> \<and> X \<subseteq> M}"_ card, simplified comp_def, symmetric], goal_cases)
    case 1
    then show ?case
      by(auto intro!: inj_onI elim!: in_maximal_setsE)
  next
    case 2
    then show ?case  
      by(auto intro!: arg_cong[of _ _ "sum _"])
  qed
  also have "... \<le> sum (\<lambda> X. 2* card X - 1) (maximal_sets \<X>)"
  proof(rule ordered_comm_monoid_add_class.sum_mono, goal_cases)
    case (1 M)
    then show ?case 
      using assms(1,2)
      by(intro laminar_family_number_of_sets[OF refl])
        (auto intro: finite_maximal_set[OF laminar_Union_finite]
             intro!: laminarI
               elim: laminarE) 
  qed
  also have "... =  2* sum card (maximal_sets \<X>) - card (maximal_sets \<X>)"
  proof(subst sum_subtractf_nat, goal_cases)
    case (1 x)
    then show ?case
      using assms(1,2)
      by (auto simp add: card_geq_1_iff finite_maximal_set[OF laminar_Union_finite] 
                         laminar_maximal_sets_nempty)
  next
    case 2
    then show ?case 
      by(auto intro!: arg_cong2[where f = "(-)"] simp add: semiring_0_class.sum_distrib_left)
  qed
  also have "... = 2 * (card (\<Union> \<X>)) - card (maximal_sets \<X>)"
  proof(rule arg_cong2[where f = "(-)", OF _ refl], goal_cases)
    case 1
    have "sum card (maximal_sets \<X>) = card (\<Union> \<X>)"
    proof(subst X_split', subst card_UN_disjoint[where A = id, simplified], goal_cases)
      case 1
      then show ?case 
        by(auto intro!: finite_UnionD laminar_Union_finite[OF assms(1,2)] simp add: X_split'[symmetric])
    next
      case 2
      then show ?case 
        using assms(1,2) 
        by(auto intro: finite_maximal_set[OF laminar_Union_finite])
    next
      case 3
      then show ?case
        using assms(2) laminar_maximal_sets_disjoint by fastforce
    next
      case 4
      then show ?case by simp
    qed
    then show ?case 
      by simp
  qed
  finally show ?thesis 
    by simp
qed

lemma laminar_card_and_maximal_sets_card_universe:
  assumes "finite U" "laminar U \<X>" 
  shows   "card \<X> \<le> 2* card U - card (maximal_sets \<X>)"
proof-
  note laminar_card_and_maximal_sets[OF assms]
  moreover have "2 * card (\<Union> \<X>) - card (maximal_sets \<X>) \<le> 2 * card U - card (maximal_sets \<X>)"
    using assms(1,2) by(auto elim!: laminarE intro!: diff_le_mono card_mono)+
  ultimately show ?thesis
    by simp
qed

lemma two_maxes_laminar_card_not_max:
  assumes "finite U" "laminar U \<X>" "X \<in> maximal_sets \<X>" "Y \<in> maximal_sets \<X>" "X \<noteq> Y"
  shows   "card \<X> \<le> 2* (card U - 1)"
proof(rule ccontr, goal_cases)
  case 1
  hence "card \<X> = 2 * card U - 1"
    using laminar_family_number_of_sets[OF refl assms(1,2)] by simp
  moreover have "card (insert (X \<union> Y) \<X>) = card \<X> + 1"
    using laminar_union_maximal_sets_not_in assms finite_U_finite_family[OF assms(1)]
    by(subst card_insert_disjoint) auto
  moreover have "laminar U (insert (X \<union> Y) \<X>)"
    using assms(3,4)
    by(auto intro!: laminar_extension_with_maximal_sets[OF assms(2), of "{X, Y}", simplified])
  moreover hence  "card (insert (X \<union> Y) \<X>) \<le> 2 * card U - 1" 
    using laminar_family_number_of_sets[OF refl assms(1)] by simp
  ultimately show ?case 
    by simp
qed

end