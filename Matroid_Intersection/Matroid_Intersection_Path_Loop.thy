theory Matroid_Intersection_Path_Loop
  imports Matroid_Intersection
begin

section \<open>Matroid Intersection as a Loop over an Abstract Path Search\<close>

text \<open>The augmentation loop of unweighted matroid intersection. 
  It is parametrised by a function \<open>augmenting_path\<close> that returns a shortest
  augmenting path in the exchange graph of the current solution, or nothing.
  How this path is found (explicit graph, implicit graph, oracles, BFS) is
  invisible here.\<close>

record 'sol intersection_state = solution::'sol

lemma solution_remove: "solution (state \<lparr> solution:= new_sol \<rparr>) = new_sol"
  by auto

subsection \<open>Augmentation\<close>

text \<open>Augmenting a solution along a path, shared by every loop that augments along
  exchange-graph paths (unweighted and weighted).\<close>

locale intersection_augment_spec =
fixes set_insert::"'a \<Rightarrow> 'mset \<Rightarrow> 'mset"
  and set_delete::"'a \<Rightarrow> 'mset \<Rightarrow> 'mset"
  and to_set::"'mset \<Rightarrow> 'a set"
  and set_invar::"'mset \<Rightarrow> bool"
  and set_empty::"'mset"
begin

fun augment where
  "augment X Nil = X"|
  "augment X [x] = set_insert x X"|
  "augment X (x#y#xs) = augment (set_insert x (set_delete y X)) xs"

lemmas [code] = augment.simps

end

locale intersection_augment =
  intersection_augment_spec +
  fixes carrier::"'a set"
  assumes set_insert: "\<And> S x. \<lbrakk>set_invar S; x \<in> carrier\<rbrakk> \<Longrightarrow> set_invar (set_insert x S)"
    "\<And> S x. \<lbrakk>set_invar S; x \<in> carrier\<rbrakk> \<Longrightarrow> to_set (set_insert x S) = Set.insert x (to_set S)"
  assumes set_delete: "\<And> S x. \<lbrakk>set_invar S; x \<in> carrier\<rbrakk> \<Longrightarrow> set_invar (set_delete x S)"
    "\<And> S x. \<lbrakk>set_invar S; x \<in> carrier\<rbrakk> \<Longrightarrow> to_set (set_delete x S) = (to_set S) - {x}"
  assumes set_empty: "set_invar set_empty" "to_set set_empty = {}"
begin

lemma effect_of_augmentation:
  assumes "set_invar X" "to_set X \<subseteq> carrier" "set p \<subseteq> carrier" "distinct p"
    "X' = ((to_set X \<union> {p ! i | i. i < length p \<and> even i}) -  {p ! i | i. i < length p \<and> odd i})"
  shows "set_invar (augment X p)" "to_set (augment X p) = X'"
proof-
  have "set p \<subseteq> carrier \<Longrightarrow> set_invar (augment X p)" for p
    using  assms(1,2) 
  proof(induction p arbitrary: X rule: induct_list012)
    case (sucsuc x y zs)
    note 3 = this
    show ?case 
      using 3(2-) 
      by(auto intro!: 3(1) intro: set_insert set_delete simp add: set_insert set_delete)
  qed (auto simp add: intro: set_insert set_delete)
  thus "set_invar (augment X p)"
    by (simp add: assms(3))
  show "to_set (augment X p) = X'"
    using assms
  proof(induction p arbitrary: X X' rule: induct_list012)
    case (sucsuc x y zs)
    have same_set:"Set.insert x (to_set X - {y}) \<union> {zs ! i |i. i < length zs \<and> even i} - {zs ! i |i. i < length zs \<and> odd i} =
    to_set X \<union> {(x # y # zs) ! i |i. i < length (x # y # zs) \<and> even i} -
    {(x # y # zs) ! i |i. i < length (x # y # zs) \<and> odd i}"
      using  "sucsuc.prems"(4)  
      by (auto simp add: nth_eq_iff_index_eq less_Suc_eq_0_disj gr0_conv_Suc)
        (metis dvd_0_right nth_Cons_0  nth_Cons_Suc even_Suc)+
    have help1: "to_set (set_insert x (set_delete y X)) \<subseteq> carrier" 
      using "sucsuc.prems"(1-3) local.set_insert(2) set_delete(1) set_delete(2) by auto
    show ?case 
      using sucsuc(2-) same_set set_insert set_delete
      by (auto simp add:  sucsuc(1)[OF  _ help1 _ _ refl])
  qed (auto simp add: set_insert)
qed

end

subsection \<open>The Loop\<close>

locale unweighted_intersection_path_loop_spec =
  intersection_augment_spec set_insert set_delete to_set set_invar set_empty
  for set_insert::"'a \<Rightarrow> 'mset \<Rightarrow> 'mset" and set_delete to_set set_invar set_empty +
  fixes augmenting_path::"'mset \<Rightarrow> 'a list option"
begin

function (domintros) matroid_intersection::"'mset intersection_state\<Rightarrow> 'mset intersection_state"  where
  "matroid_intersection state =
 (let X = solution state in
     (case augmenting_path X of 
          None \<Rightarrow> state |
          Some p \<Rightarrow> matroid_intersection (state \<lparr> solution := augment X p\<rparr>) ))"
  by pat_completeness auto

definition "matroid_intersection_recurse_cond state =
(let X = solution state in
     (case augmenting_path X of 
          None \<Rightarrow> False |
          Some p \<Rightarrow> True))"

lemma matroid_intersection_recurse_condE:
  "matroid_intersection_recurse_cond state \<Longrightarrow>
 (\<And> p X. X = solution state \<Longrightarrow> augmenting_path X = Some p \<Longrightarrow> P) \<Longrightarrow> P"
  by(force simp add: matroid_intersection_recurse_cond_def Let_def)

definition "matroid_intersection_recurse_upd state =
(let X = solution state in
     state \<lparr> solution := augment X (the (augmenting_path X)) \<rparr>)"

lemma P_of_matroid_intersection_recurseI:
  "matroid_intersection_recurse_cond state \<Longrightarrow> 
   (\<And> p X. X = solution state \<Longrightarrow> augmenting_path X = Some p 
            \<Longrightarrow> P (state \<lparr> solution := augment X p\<rparr>)) 
    \<Longrightarrow> P (matroid_intersection_recurse_upd state)"
  unfolding matroid_intersection_recurse_cond_def
    matroid_intersection_recurse_upd_def Let_def 
  by(cases "augmenting_path (solution state)") auto

definition "matroid_intersection_terminates_cond state =
(let X = solution state in
     (case augmenting_path X of 
          None \<Rightarrow> True |
          Some p \<Rightarrow> False))"

lemma matroid_intersection_terminates_condE:
  "matroid_intersection_terminates_cond state \<Longrightarrow>
 (\<And> X. X = solution state \<Longrightarrow> augmenting_path X = None \<Longrightarrow> P) \<Longrightarrow> P"
  by(force simp add: matroid_intersection_terminates_cond_def Let_def)

lemma matroid_intersection_cases:
  "(matroid_intersection_terminates_cond state \<Longrightarrow> P) \<Longrightarrow>
 (matroid_intersection_recurse_cond state \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding matroid_intersection_terminates_cond_def matroid_intersection_recurse_cond_def Let_def
  by(cases "augmenting_path (solution state)") auto

lemma matroid_intersection_simps:
  assumes "matroid_intersection_dom state"
  shows "matroid_intersection_terminates_cond state \<Longrightarrow> matroid_intersection state = state"
    "matroid_intersection_recurse_cond state \<Longrightarrow>
           matroid_intersection state =
     matroid_intersection (matroid_intersection_recurse_upd state)"  
  by(auto intro:  P_of_matroid_intersection_recurseI matroid_intersection_terminates_condE 
      simp add: matroid_intersection.psimps[OF assms] 
      split: option.split)

lemma matroid_intersection_induct:
  assumes "matroid_intersection_dom state"
    "\<And> state. matroid_intersection_dom state  \<Longrightarrow>
                 (matroid_intersection_recurse_cond state
 \<Longrightarrow> P (matroid_intersection_recurse_upd state)) \<Longrightarrow> P state"
  shows   "P state"
  apply(rule matroid_intersection.pinduct[OF assms(1)])
  apply(rule assms(2)[simplified matroid_intersection_terminates_cond_def 
        matroid_intersection_recurse_cond_def matroid_intersection_recurse_upd_def])
  by(auto simp: Let_def split: option.splits)

partial_function (tailrec) matroid_intersection_impl::
  "'mset intersection_state \<Rightarrow> 'mset intersection_state" where
  "matroid_intersection_impl state =
 (let X = solution state in
     (case augmenting_path X of 
          None \<Rightarrow> state |
          Some p \<Rightarrow> matroid_intersection_impl (state \<lparr> solution := augment X p \<rparr>)))"

lemma implementation_is_same:
  "matroid_intersection_dom state \<Longrightarrow> matroid_intersection_impl state = matroid_intersection state"
  apply(induction state rule: matroid_intersection.pinduct)
  apply(subst matroid_intersection_impl.simps)
  apply(subst matroid_intersection.psimps, simp)
  by(auto simp add: Let_def split: option.split)

definition "initial_state = \<lparr> solution = set_empty \<rparr>"

lemmas [code] = matroid_intersection_impl.simps initial_state_def

end

text \<open>Specification of the path search: \<open>None\<close> iff there is no walk from \<open>S\<close> to \<open>T\<close>
  in the exchange graph, and a returned path is such a walk which is shortest 
  between its endpoints.\<close>

locale unweighted_intersection_path_loop =
  unweighted_intersection_path_loop_spec
  where set_insert = "set_insert::'a \<Rightarrow> 'mset \<Rightarrow> 'mset"
    + intersection_augment where set_insert = set_insert and carrier = carrier
    + double_matroid 
  where carrier = "carrier::'a set"
  for set_insert carrier +
  assumes augmenting_path:
    "\<And> X. \<lbrakk>set_invar X; to_set X \<subseteq> carrier; indep1 (to_set X); indep2 (to_set X)\<rbrakk>
      \<Longrightarrow> augmenting_path X = None \<longleftrightarrow> 
           (\<nexists> p u v. (vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) u p v \<or> (p = [u] \<and> u = v)) \<and>
                       u \<in> S (to_set X) \<and> v \<in> T (to_set X))"
    "\<And> X p. \<lbrakk>set_invar X; to_set X \<subseteq> carrier; indep1 (to_set X); indep2 (to_set X);
             augmenting_path X = Some p\<rbrakk>
      \<Longrightarrow> \<exists> u v. (vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) u p v \<or> (p = [u] \<and> u = v))
                  \<and> u \<in> S (to_set X) \<and> v \<in> T (to_set X) \<and>
             (\<nexists> p'. (vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) u p' v \<or> (p' = [u] \<and> u = v))
                         \<and> length p' < length p)"
begin

definition "indep_invar state = 
   (indep1 (to_set (solution state)) \<and> (indep2 (to_set (solution state))))"

lemma indep_invar_recurse_improvement:
  assumes "matroid_intersection_recurse_cond state" "indep_invar state"
    "set_invar (solution state)" "to_set (solution state) \<subseteq> carrier"
  shows   "indep_invar (matroid_intersection_recurse_upd state)"
    "set_invar (solution (matroid_intersection_recurse_upd state))" 
    "to_set (solution (matroid_intersection_recurse_upd state)) \<subseteq> carrier"
    "card (to_set (solution (matroid_intersection_recurse_upd state))) = 
          card (to_set (solution state)) + 1"
    "S (to_set (solution state)) \<noteq> {}"
    "T (to_set (solution state)) \<noteq> {}"
    and   "\<exists>u v p. (vwalk_bet (A1 (to_set (solution state)) \<union> A2 (to_set (solution state))) u p v
                     \<or> (p = [u] \<and> u = v)) \<and>
           u \<in> S (to_set (solution state)) \<and>
           v \<in> T (to_set (solution state))" (is ?last_thesis)
proof(all \<open>rule P_of_matroid_intersection_recurseI[OF assms(1)]\<close>)
  fix p X
  assume 1: "X = solution state" "augmenting_path X = Some p"
  have Xincarrier: "to_set X \<subseteq> carrier"
    by (simp add: "1"(1) assms(4))
  have indep1X: "indep1 (to_set X)"
    using assms(2) 1(1) indep_invar_def by auto
  have indep2X: "indep2 (to_set X)" 
    using assms(2) 1(1) indep_invar_def by auto
  have Xinvar: "set_invar X"
    using assms(3) 1(1) by simp
  define G where "G = A1 (to_set X) \<union> A2 (to_set X)"
  have SXincarrier: "S (to_set X) \<subseteq> carrier" 
    using S_in_carrier indep1X indep2X by simp
  have graphverticesincarrier: "dVs G \<subseteq> carrier" 
    using dVs_A1A2_carrier indep1X indep2X by (simp add: G_def)
  obtain u v where p_prop: "vwalk_bet G u p v \<or> (p = [u] \<and> u = v)"
    "u \<in> S (to_set X)" "v \<in> T (to_set X)"
    "(\<nexists>p'. (vwalk_bet G u p' v \<or> (p' = [u] \<and> u = v)) \<and> length p' < length p)"
    using augmenting_path(2)[OF Xinvar Xincarrier indep1X indep2X 1(2)] by (auto simp add: G_def)
  have pincarrier:"set p \<subseteq> carrier"
    using p_prop(1-3)
    using graphverticesincarrier in_mono vwalk_bet_in_vertices[of G u p v] SXincarrier 
    by (auto simp add: vwalk_bet_def)
  have p_not_empty:"p \<noteq> []" 
    using p_prop(1) by(auto simp add:  vwalk_bet_def) 
  have distinctp:"distinct p"
  proof(rule ccontr, goal_cases)
    case 1
    then obtain p1 x p2 p3 where p_decomp:"p = p1@[x]@p2@[x]@p3"
      using not_distinct_decomp by blast
    moreover hence "length p \<ge> 2" by auto
    moreover hence "vwalk_bet G u p v"
      using p_prop(1) by(auto simp add: vwalk_bet_def)
    ultimately have "vwalk_bet G u (p1@[x]@p3) v"
      by (meson vwalk_bet_cycle_delete)
    moreover have "length (p1@[x]@p3)< length p"
      using p_decomp by simp
    ultimately show ?case
      using p_prop(4) by blast
  qed
  have indep_after_aug:"indep1 (to_set (augment X p))"
    using augment_in_matroid1_single[OF indep1X indep2X, of u]
      augment_in_matroid1[OF indep1X indep2X, of u p v] p_prop
    by(subst effect_of_augmentation(2)[OF Xinvar Xincarrier pincarrier distinctp refl])
      (auto intro: vwalk_arcs.cases[of p] simp add: G_def p_not_empty vwalk_bet_def)  
  moreover have "indep2 (to_set (augment X p))"
    using augment_in_matroid2_single[OF indep1X indep2X, of u]
      augment_in_matroid2[OF indep1X indep2X, of u p v] p_prop
    by(subst effect_of_augmentation(2)[OF Xinvar Xincarrier pincarrier distinctp refl])
      (auto intro: vwalk_arcs.cases[of p] simp add: G_def p_not_empty vwalk_bet_def)  
  ultimately show "indep_invar (state \<lparr> solution := (augment X p) \<rparr>)"
    by(simp add: indep_invar_def)
  show "set_invar (solution (state \<lparr> solution := (augment X p)\<rparr>))"
    using Xincarrier Xinvar distinctp effect_of_augmentation(1) pincarrier by simp
  show "to_set (solution (state \<lparr> solution :=(augment X p) \<rparr>)) \<subseteq> carrier"
    by (simp add: indep_after_aug matroid1.indep_subset_carrier)
  show "card (to_set (solution (state \<lparr> solution := (augment X p)\<rparr>))) 
             = card (to_set (solution state)) + 1"
    using augment_in_both_matroids_single(3)[OF indep1X indep2X, of u] 
      augment_in_both_matroids(3)[OF indep1X indep2X _ _ _ _ refl, of u p v] p_prop
    by(subst solution_remove, 
        subst effect_of_augmentation(2)[OF Xinvar Xincarrier pincarrier distinctp refl])
      (auto intro: vwalk_arcs.cases[of p] simp add: 1(1) G_def p_not_empty vwalk_bet_def)
  show ?last_thesis 
    using p_prop 1(1) by (auto simp add: G_def)
  thus "S (to_set (solution state)) \<noteq> {}" "T (to_set (solution state)) \<noteq> {}" by auto
qed

lemma indep_invar_max_found:
  assumes "matroid_intersection_terminates_cond state" "indep_invar state"
    "set_invar (solution state)" "to_set (solution state) \<subseteq> carrier"
  shows   "is_max (to_set (solution state))"
proof(rule matroid_intersection_terminates_condE[OF assms(1)])
  fix X
  assume 1: "X = solution state" "augmenting_path X = None"
  have Xincarrier: "to_set X \<subseteq> carrier"
    by (simp add: assms(4) 1(1))
  have indep1X: "indep1 (to_set X)"
    using assms(2) indep_invar_def 1(1)  by auto
  have indep2X: "indep2 (to_set X)" 
    using assms(2) indep_invar_def 1(1) by auto
  have Xinvar: "set_invar X"
    using assms(3) 1(1) by simp
  have "\<nexists>p x y. x \<in> S (to_set X) \<and> y \<in> T (to_set X) \<and> 
                (vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) x p y \<or> x = y)"
    using augmenting_path(1)[OF Xinvar Xincarrier indep1X indep2X] 1(2) by blast
  thus  "is_max (to_set (solution state))"
    using if_no_augpath_then_maximum(1)[OF indep1X indep2X _ refl]
      indep1X indep2X 1(1) by(auto simp add: is_max_def)
qed

lemma matroid_intersection_terminates_general:
  assumes  "indep_invar state" "set_invar (solution state)" "to_set (solution state) \<subseteq> carrier"
    "m = card carrier - card (to_set (solution state))"
  shows    "matroid_intersection_dom state"
  using assms
proof(induction m arbitrary: state)
  case 0
  hence X_is_carrier:"to_set (solution state) = carrier" 
    by (simp add: card_seteq matroid2.carrier_finite)
  show ?case 
  proof(cases state rule: matroid_intersection_cases)
    case 1
    show ?thesis 
      by(rule matroid_intersection_terminates_condE[OF 1])
        (auto intro: matroid_intersection.domintros)
  next
    case 2
    have "S (to_set (solution state)) \<noteq> {}"
      using indep_invar_recurse_improvement(5)[OF 2 0(1,2,3)] by auto
    moreover have  "S (to_set (solution state)) = {}"
      by(simp add: X_is_carrier  S_def)
    ultimately show ?thesis by simp
  qed
next
  case (Suc m)
  show ?case  
  proof(cases state rule: matroid_intersection_cases)
    case 1
    show ?thesis 
      by(rule matroid_intersection_terminates_condE[OF 1])
        (auto intro: matroid_intersection.domintros)
  next
    case 2
    show ?thesis
    proof(rule matroid_intersection_recurse_condE[OF 2], goal_cases)
      case (1 p X)
      have helper:"indep1 (to_set (augment X p))" "indep2 (to_set (augment X p))" 
               "set_invar (augment X p)"  "to_set (augment X p) \<subseteq> carrier"
        using 1 2  indep_invar_recurse_improvement[OF 2 Suc.prems(1,2,3)] 
        by(auto simp add: matroid_intersection_recurse_upd_def indep_invar_def)
      have card_decrease: "m = card carrier - card (to_set (augment X p))"
        using 1 2 Suc.prems(4) indep_invar_recurse_improvement[OF 2 Suc.prems(1,2,3)] 
        by(auto simp add: matroid_intersection_recurse_upd_def)
      show ?case 
        apply(rule matroid_intersection.domintros)
        using helper 1 card_decrease
        by (auto intro!: Suc(1) simp add: indep_invar_def)
    qed
  qed
qed

lemma matroid_intersection_correctness_general:
  assumes "indep_invar state" "set_invar (solution state)" "to_set (solution state) \<subseteq> carrier"
  shows "is_max (to_set (solution (matroid_intersection state)))"
  using assms
proof(induction state rule: matroid_intersection_induct)
  case 1
  then show ?case 
    using matroid_intersection_terminates_general[OF assms refl] by simp
next
  case (2 state)
  note IH = this
  show ?case 
  proof(cases state rule: matroid_intersection_cases)
    case 1
    then show ?thesis 
      by (simp add: "2.hyps" "2.prems" indep_invar_max_found matroid_intersection_simps(1))
  next
    case 2
    show ?thesis 
      apply(subst matroid_intersection_simps(2)[OF IH(1) 2])+
      apply(rule IH(2)[OF 2])
      by(auto simp add: "2" IH(3-) indep_invar_recurse_improvement)
  qed
qed

lemma matroid_intersection_correctness:
  "indep_invar (matroid_intersection initial_state)"
  "is_max (to_set (solution (matroid_intersection initial_state)))"
  using matroid_intersection_correctness_general
  by(simp add: indep_invar_def initial_state_def is_max_def local.set_empty(1) local.set_empty(2))+

lemma matroid_intersection_terminates: "matroid_intersection_dom initial_state"
  by(rule matroid_intersection_terminates_general)
    (auto simp add: indep_invar_def set_empty initial_state_def)

lemma matroid_intersection_total_correctness:
  "is_max (to_set (solution (matroid_intersection initial_state)))"
  "matroid_intersection_dom initial_state"
  using matroid_intersection_correctness matroid_intersection_terminates by auto

lemma same_result: "matroid_intersection_impl initial_state = matroid_intersection initial_state"
  by(simp add: implementation_is_same matroid_intersection_terminates)

lemma impl_total_correctness:
  "is_max (to_set (solution (matroid_intersection_impl initial_state)))"
  using matroid_intersection_total_correctness(1) same_result by simp

end

end