theory Matroid_Intersection_Imp_Loop
  imports Matroid_Intersection_Path_Loop "Data_Structures.Imp_Bool_Set"
begin

section \<open>The Augmentation Loop in Imperative HOL\<close>

text \<open>The imperative counterpart of @{locale unweighted_intersection_path_loop}. Elements are the
  nats below \<open>n\<close>, the solution is an abstract imperative set (@{locale imp_nat_set}), and the
  path search is an abstract heap function that writes a path, reversed, into an array given by
  the caller and returns its length. The loop allocates nothing: it works on the handles it
  receives. It is refined against the functional loop with the set model of solutions: the
  handle ends up representing the functional result.\<close>

subsection \<open>Paths\<close>

text \<open>A path array of length \<open>n\<close>, and a path result: no path and \<open>None\<close>, or a path written
  reversed into the first \<open>k\<close> cells and \<open>Some k\<close>.\<close>

definition parr_assn :: "nat \<Rightarrow> nat array \<Rightarrow> assn" where
  "parr_assn n Ra = (\<exists>\<^sub>A ps. Ra \<mapsto>\<^sub>a ps * \<up>(length ps = n))"

definition path_assn :: "nat \<Rightarrow> nat list option \<Rightarrow> nat option \<Rightarrow> nat array \<Rightarrow> assn" where
  "path_assn n po ko Ra = (case po of
      None \<Rightarrow> (\<exists>\<^sub>A ps. Ra \<mapsto>\<^sub>a ps * \<up>(length ps = n \<and> ko = None))
    | Some p \<Rightarrow> (\<exists>\<^sub>A k ps. Ra \<mapsto>\<^sub>a ps *
                   \<up>(length ps = n \<and> ko = Some k \<and> k \<le> n \<and> rev (take k ps) = p)))"

lemma nth_in_take: "\<lbrakk>j < k; k \<le> length ps\<rbrakk> \<Longrightarrow> ps ! j \<in> set (take k ps)"
  using nth_mem[of j "take k ps"] by simp

lemma rev_take_Suc_Suc:
  "Suc (Suc j) \<le> length ps \<Longrightarrow> rev (take (Suc (Suc j)) ps) = ps ! Suc j # ps ! j # rev (take j ps)"
  by (simp add: take_Suc_conv_app_nth)

subsection \<open>Augmentation\<close>

locale intersection_augment_imp_spec =
  fixes sins_imp :: "nat \<Rightarrow> 'si \<Rightarrow> unit Heap"
    and sdel_imp :: "nat \<Rightarrow> 'si \<Rightarrow> unit Heap"
begin

text \<open>Augmentation along the path in the first \<open>k\<close> cells of the array, read from the end, i.e.
  from the start of the path. Mirrors @{const intersection_augment_spec.augment}.\<close>

partial_function (heap) aug_imp :: "'si \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "aug_imp Si Ra k =
     (if k = 0 then return ()
      else if k = 1 then do { x \<leftarrow> Array.nth Ra 0; sins_imp x Si }
      else do { x \<leftarrow> Array.nth Ra (k - 1); y \<leftarrow> Array.nth Ra (k - 2);
                sdel_imp y Si; sins_imp x Si; aug_imp Si Ra (k - 2) })"

end

locale intersection_augment_imp =
  intersection_augment_imp_spec sins_imp sdel_imp +
  imp_nat_set n sol_assn smemb_imp sins_imp sdel_imp +
  intersection_augment_spec where set_insert = "insert :: nat \<Rightarrow> nat set \<Rightarrow> nat set"
    and set_delete = "\<lambda> x X. X - {x}" and to_set = "\<lambda> X. X" and set_invar = finite
    and set_empty = "{}"
  for n sol_assn smemb_imp sins_imp sdel_imp
begin

lemma aug_imp_rule:
  "\<lbrakk>k \<le> length ps; set (rev (take k ps)) \<subseteq> {..<n}\<rbrakk> \<Longrightarrow>
   <sol_assn X Si * Ra \<mapsto>\<^sub>a ps> aug_imp Si Ra k
   <\<lambda> _. sol_assn (augment X (rev (take k ps))) Si * Ra \<mapsto>\<^sub>a ps>"
proof(induction k arbitrary: X rule: less_induct)
  case (less k)
  have tk: "set (take k ps) \<subseteq> {..<n}"
    using less.prems(2) by simp
  consider "k = 0" | "k = 1" | j where "k = Suc (Suc j)"
  proof-
    assume a: "k = 0 \<Longrightarrow> thesis" "k = 1 \<Longrightarrow> thesis" "\<And> j. k = Suc (Suc j) \<Longrightarrow> thesis"
    show thesis
    proof(cases k)
      case 0
      then show ?thesis
        by (rule a(1))
    next
      case (Suc k')
      then show ?thesis
        by (cases k') (auto intro: a(2) a(3))
    qed
  qed
  then show ?case
  proof cases
    case 1
    show ?thesis
      unfolding 1 aug_imp.simps[of Si Ra 0] if_P[OF refl] take_0 rev.simps(1) augment.simps(1)
      by sep_auto
  next
    case 2
    have x: "ps ! 0 < n" "ps \<noteq> []"
      using tk nth_in_take[of 0 k ps] less.prems(1) 2 by auto
    have p: "rev (take 1 ps) = [ps ! 0]"
      using x(2) by (cases ps) simp_all
    have a: "aug_imp Si Ra 1 = do { x \<leftarrow> Array.nth Ra 0; sins_imp x Si }"
      by (subst aug_imp.simps) simp
    show ?thesis
      unfolding 2 p augment.simps(2) a
      by (sep_auto heap: sins_rule simp: x)
  next
    case 3
    have x: "ps ! Suc j < n" "ps ! j < n" "Suc j < length ps" "j < length ps"
      using tk nth_in_take[of "Suc j" k ps] nth_in_take[of j k ps] less.prems(1) 3 by auto
    have p: "rev (take (Suc (Suc j)) ps) = ps ! Suc j # ps ! j # rev (take j ps)"
      using less.prems(1) 3 by (simp only: rev_take_Suc_Suc)
    have tj: "set (rev (take j ps)) \<subseteq> {..<n}"
      using tk set_take_subset_set_take[of j k ps] 3 by simp
    have IH: "<sol_assn Y Si * Ra \<mapsto>\<^sub>a ps> aug_imp Si Ra j
               <\<lambda> _. sol_assn (augment Y (rev (take j ps))) Si * Ra \<mapsto>\<^sub>a ps>" for Y
      by (rule less.IH) (use less.prems(1) 3 tj in simp_all)
    have a: "aug_imp Si Ra (Suc (Suc j)) =
               do { x \<leftarrow> Array.nth Ra (Suc j); y \<leftarrow> Array.nth Ra j;
                    sdel_imp y Si; sins_imp x Si; aug_imp Si Ra j }"
      by (subst aug_imp.simps) simp
    show ?thesis
      unfolding 3 p augment.simps(3) a
      by (sep_auto heap: sdel_rule sins_rule IH simp: x)
  qed
qed

end

subsection \<open>Code\<close>

locale unweighted_intersection_imp_loop_spec =
  intersection_augment_imp_spec sins_imp sdel_imp
  for sins_imp :: "nat \<Rightarrow> 'si \<Rightarrow> unit Heap"
    and sdel_imp :: "nat \<Rightarrow> 'si \<Rightarrow> unit Heap" +
  fixes aug_path_imp :: "'si \<Rightarrow> nat array \<Rightarrow> nat option Heap"
begin

partial_function (heap) mi_loop_imp :: "'si \<Rightarrow> nat array \<Rightarrow> unit Heap" where
  "mi_loop_imp Si Ra = do {
     r \<leftarrow> aug_path_imp Si Ra;
     (case r of None \<Rightarrow> return ()
      | Some k \<Rightarrow> do { aug_imp Si Ra k; mi_loop_imp Si Ra }) }"

end

subsection \<open>Correctness\<close>

text \<open>The path search refines the functional one on every solution reached by the loop. The
  assertion \<open>st\<close> holds the data of the path search that the loop passes on untouched.\<close>

locale unweighted_intersection_imp_loop =
  unweighted_intersection_imp_loop_spec sins_imp sdel_imp aug_path_imp +
  intersection_augment_imp n sol_assn smemb_imp sins_imp sdel_imp +
  unweighted_intersection_path_loop where set_insert = "insert :: nat \<Rightarrow> nat set \<Rightarrow> nat set"
    and set_delete = "\<lambda> x X. X - {x}" and to_set = "\<lambda> X. X" and set_invar = finite
    and set_empty = "{}"
  for n sol_assn smemb_imp sins_imp sdel_imp aug_path_imp +
  fixes st :: assn
  assumes carrier_bound: "carrier \<subseteq> {..<n}"
    and aug_path_imp: "\<And> X Si Ra. \<lbrakk>finite X; X \<subseteq> carrier; indep1 X; indep2 X\<rbrakk> \<Longrightarrow>
      <sol_assn X Si * parr_assn n Ra * st> aug_path_imp Si Ra
      <\<lambda> res. sol_assn X Si * path_assn n (augmenting_path X) res Ra * st>"
begin

context
  fixes X
  assumes X: "finite X" "X \<subseteq> carrier" "indep1 X" "indep2 X"
begin

lemma aug_path_imp_None:
  assumes "augmenting_path X = None"
  shows "<sol_assn X Si * parr_assn n Ra * st> aug_path_imp Si Ra
         <\<lambda> res. sol_assn X Si * parr_assn n Ra * st * \<up>(res = None)>"
  by (rule ht_cons_post[OF aug_path_imp[OF X]])
     (unfold assms path_assn_def parr_assn_def option.case(1), sep_auto)

lemma path_in_carrier:
  assumes "augmenting_path X = Some p"
  shows "set p \<subseteq> carrier"
proof-
  obtain u v where uv: "vwalk_bet (A1 X \<union> A2 X) u p v \<or> (p = [u] \<and> u = v)" "u \<in> S X"
    using augmenting_path(2)[OF X assms] by blast
  show ?thesis
  proof(cases "vwalk_bet (A1 X \<union> A2 X) u p v")
    case True
    show ?thesis
      using vwalk_bet_in_dVs[OF True] dVs_A1A2_carrier[OF X(3,4)] by (rule subset_trans)
  next
    case False
    then have "p = [u]"
      using uv(1) by simp
    then show ?thesis
      using uv(2) S_in_carrier[OF X(3,4)] by auto
  qed
qed

lemma aug_path_imp_Some:
  assumes "augmenting_path X = Some p"
  shows "<sol_assn X Si * parr_assn n Ra * st> aug_path_imp Si Ra
         <\<lambda> res. \<exists>\<^sub>A k ps. sol_assn X Si * Ra \<mapsto>\<^sub>a ps * st *
            \<up>(res = Some k \<and> length ps = n \<and> k \<le> n \<and> rev (take k ps) = p)>"
  by (rule ht_cons_post[OF aug_path_imp[OF X]])
     (unfold assms path_assn_def option.case(2), sep_auto)

lemma path_bound:
  assumes "augmenting_path X = Some p"
  shows "set p \<subseteq> {..<n}"
  using path_in_carrier[OF assms] carrier_bound by (rule subset_trans)

end

lemma mi_loop_imp_rule:
  assumes "matroid_intersection_dom state" "indep_invar state" "finite (solution state)"
          "solution state \<subseteq> carrier"
  shows "<sol_assn (solution state) Si * parr_assn n Ra * st> mi_loop_imp Si Ra
         <\<lambda> _. sol_assn (solution (matroid_intersection state)) Si * parr_assn n Ra * st>"
  using assms(2-4)
proof(induction state arbitrary: Ra rule: matroid_intersection_induct)
  case 1
  show ?case
    by (rule assms(1))
next
  case (2 state)
  define X where "X = solution state"
  have X: "finite X" "X \<subseteq> carrier" "indep1 X" "indep2 X"
    using 2(3-5) unfolding X_def indep_invar_def by auto
  show ?case
  proof(cases "augmenting_path X")
    case None
    have f: "matroid_intersection state = state"
      using None unfolding X_def by (simp add: matroid_intersection.psimps[OF 2(1)])
    show ?thesis
      unfolding f X_def[symmetric]
      by (subst mi_loop_imp.simps) (sep_auto heap: aug_path_imp_None[OF X None])
  next
    case (Some p)
    have rc: "matroid_intersection_recurse_cond state"
      using Some unfolding X_def matroid_intersection_recurse_cond_def by simp
    have upd: "matroid_intersection_recurse_upd state = state \<lparr>solution := augment X p\<rparr>"
      using Some unfolding X_def matroid_intersection_recurse_upd_def by simp
    have f: "matroid_intersection state = matroid_intersection (state \<lparr>solution := augment X p\<rparr>)"
      using Some unfolding X_def by (simp add: matroid_intersection.psimps[OF 2(1)])
    note inv = indep_invar_recurse_improvement[OF rc 2(3-5), unfolded upd]
    have IH: "<sol_assn (augment X p) Si * parr_assn n Qa * st> mi_loop_imp Si Qa
              <\<lambda> _. sol_assn (solution (matroid_intersection
                        (state \<lparr>solution := augment X p\<rparr>))) Si * parr_assn n Qa * st>" for Qa
      using 2(2)[OF rc, unfolded upd, OF inv(1-3)] by simp
    have IH': "<sol_assn (augment X p) Si * Qa \<mapsto>\<^sub>a ps * st> mi_loop_imp Si Qa
              <\<lambda> _. sol_assn (solution (matroid_intersection
                        (state \<lparr>solution := augment X p\<rparr>))) Si * parr_assn n Qa * st>"
      if "length ps = n" for Qa ps
      by (rule ht_cons_pre[OF _ IH]) (unfold parr_assn_def, sep_auto simp: that)
    show ?thesis
      unfolding f X_def[symmetric]
      by (subst mi_loop_imp.simps)
         (sep_auto heap: aug_path_imp_Some[OF X Some] aug_imp_rule IH' simp: path_bound[OF X Some])
  qed
qed

theorem mi_loop_imp_correct:
  "<sol_assn {} Si * parr_assn n Ra * st> mi_loop_imp Si Ra
   <\<lambda> _. \<exists>\<^sub>A X. sol_assn X Si * parr_assn n Ra * st * \<up>(is_max X)>"
proof-
  have init: "matroid_intersection_dom initial_state" "indep_invar initial_state"
             "finite (solution initial_state)" "solution initial_state \<subseteq> carrier"
    using matroid_intersection_terminates matroid_intersection_correctness(1)
    by (auto simp: initial_state_def indep_invar_def matroid1.indep_empty matroid2.indep_empty)
  have loop: "<sol_assn {} Si * parr_assn n Ra * st> mi_loop_imp Si Ra
         <\<lambda> _. sol_assn (solution (matroid_intersection_impl initial_state)) Si * parr_assn n Ra * st>"
    unfolding same_result
    by (rule ht_cons_pre[OF _ mi_loop_imp_rule[OF init]]) (simp add: initial_state_def)
  show ?thesis
    by (rule ht_cons_post[OF loop]) (use impl_total_correctness in sep_auto)
qed

end

end