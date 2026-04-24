theory Array_Map_Iterator
  imports Separation_Logic_Imperative_HOL_Partial.Array_Map_Impl
begin

subsection \<open>Iterators\<close>

subsubsection \<open>Definitions\<close>
type_synonym 'v iam_it = "(nat \<times> 'v array_map)"

partial_function (heap) iam_it_adjust :: "('v::heap) iam_it \<Rightarrow> ('v iam_it) Heap" where
 "iam_it_adjust it =
  (case it of (i, A) \<Rightarrow> 
    do{l \<leftarrow> Array.len A;
       if i \<ge> l then return (l, A)
       else do {x \<leftarrow> Array.nth A i;
               case x of None \<Rightarrow> iam_it_adjust (Suc i, A)
               | Some _ \<Rightarrow> return (i, A) }})"


definition iam_it_init 
  :: "('v::heap) array_map \<Rightarrow> ('v iam_it) Heap"
  where 
  "iam_it_init A \<equiv> do {
   let it = (0, A);
   iam_it_adjust it}"

definition iam_it_has_next 
  :: "('v::heap) iam_it \<Rightarrow> bool Heap"
  where "iam_it_has_next it 
  \<equiv> case it of (i, A) \<Rightarrow>
     do {l \<leftarrow> Array.len A;
         return (i < l)}"

definition iam_it_next::"('v::heap) iam_it \<Rightarrow> ((nat \<times> 'v) \<times> 'v iam_it) Heap"
  where "iam_it_next it = 
  (case it of (i, A) \<Rightarrow>
    do {x \<leftarrow> Array.nth A i;
        it' \<leftarrow> iam_it_adjust (Suc i, A);
        return ((i, the x), it')})"

definition "iam_is_it m A m' = (\<lambda> (i, A').
      (\<exists>\<^sub>Al. A\<mapsto>\<^sub>al * \<up>(m=iam_of_list l \<and> A = A' \<and> i \<le> length l \<and> (i < length l \<longrightarrow> l ! i \<noteq> None)
            \<and> m' = (\<lambda> j. if j \<ge> i then iam_of_list (drop i l) (j - i) else None))))"

definition "iam_is_it' m A m' = (\<lambda> (i, A').
      (\<exists>\<^sub>Al. A\<mapsto>\<^sub>al * \<up>(m=iam_of_list l \<and> A = A' \<and> i \<le> length l
            \<and> m' = (\<lambda> j. if j \<ge> i then iam_of_list (drop i l) (j - i) else None))))"

lemma is_am_implies_iam_is_it':"is_iam m A \<Longrightarrow>\<^sub>A iam_is_it' m A m (0, A)"
  by(sep_auto simp: is_iam_def iam_is_it'_def)

lemma iam_it_adjust_rule:
  "<iam_is_it' m A m' (i, A')> iam_it_adjust (i, A') <iam_is_it m A m'>"
proof(induction arbitrary: i rule: iam_it_adjust.fixp_induct, goal_cases)
  case 1
  then show ?case 
    by simp
next
  case 2
  then show ?case 
    by simp
next
  case (3 f i)
  show ?case
    unfolding iam_is_it'_def
    unfolding prod.case
    apply(rule ht_exEI)
    subgoal for l
      apply(rule ht_bind[where R = 
    "\<lambda> r. A \<mapsto>\<^sub>a l * \<up> (m = iam_of_list l \<and> A = A' \<and> i \<le> length l 
              \<and> m' = (\<lambda>j. if i \<le> j then iam_of_list (drop i l) (j - i) else None) \<and> r = length l)"])
      subgoal
        by sep_auto
      apply(clarsimp split!: if_split)
      subgoal for len
        by(sep_auto  simp: iam_is_it_def)
      subgoal for len
        apply(rule ht_bind[where R = "\<lambda> r. 
             A \<mapsto>\<^sub>a l *
     \<up> (m = iam_of_list l \<and> A = A' \<and> i \<le> length l \<and> m' = (\<lambda>j. if i \<le> j then iam_of_list (drop i l) (j - i) else None) 
            \<and> len = length l \<and> r = l ! i \<and> i < length l)"])
        subgoal
          by sep_auto
        subgoal for x
          apply(cases x)
          subgoal
            apply simp
            apply(rule ht_cons_pre[OF _ 3])
            apply(sep_auto simp: iam_is_it'_def)
            apply(rule ent_ex_postI[of _ _ l])
            apply sep_auto 
            apply(rule ext)
            by (auto simp add: iam_of_list_def)
          subgoal for xx
            apply simp
            apply (sep_auto simp: iam_is_it_def)
            apply(rule mod_exI[of _ l])
            apply (sep_auto simp:  mod_pure_star_dist)
            using domIff by fastforce
          done
        done
      done
    done
qed

lemma iam_it_init_rule:
  "<is_iam m A> iam_it_init A <iam_is_it m A m>"
  unfolding iam_it_init_def
  unfolding Let_def
  apply(rule ht_cons_pre)
  apply(rule  is_am_implies_iam_is_it')
  by(rule iam_it_adjust_rule)

lemma assn_ex_impl_same_witness: "(\<And> x. P x \<Longrightarrow>\<^sub>A Q x) \<Longrightarrow> \<exists>\<^sub>A x. P x \<Longrightarrow>\<^sub>A \<exists>\<^sub>A x. Q x"
  apply(rule ent_ex_preI)
  apply(rule ent_ex_postI)
  by auto

lemma iam_it_next_rule:
  assumes "m' \<noteq> (\<lambda>x. None)"
  shows "<iam_is_it m A m' it> iam_it_next it
    <\<lambda>((k, v), it'). iam_is_it m A (m' |` (- {k})) it' * \<up> (m' k = Some v)>"
  unfolding iam_it_next_def
  apply(cases it)
  subgoal for i A'
    apply simp
    apply(rule ht_bind[where R = "\<lambda> r. iam_is_it m A m' (i, A')* \<up> (r = m' i \<and> (\<exists> rr. r = Some rr))"])
    subgoal
      apply(sep_auto simp: iam_is_it_def)
      subgoal for l a b y
        apply(rule mod_exI[of _ l])
        by (sep_auto simp: iam_of_list_def)
      done
    subgoal for xx
      apply(rule ht_cons_pre[where P' = "iam_is_it' m A (m' |` (- {i})) (Suc i, A')*
                    \<up> (xx = m' i \<and> (\<exists>rr. xx = Some rr))"])
      subgoal
        apply (sep_auto simp: iam_is_it'_def iam_is_it_def)
        apply(rule assn_ex_impl_same_witness)
        subgoal for l
          using assms
          apply (sep_auto simp: iam_of_list_def)
          subgoal for a b rr y
            apply(rule ext)
            subgoal for j
              apply(cases "Suc i \<le> j")
              subgoal
                by(auto simp add: iam_of_list_def)
              subgoal 
                by(cases "i \<le> j") auto
              done
            done
          done
        done
      using iam_it_adjust_rule[of m A "m' |` (- {i})" "Suc i" A']
      by sep_auto
    done
  done

lemma iam_it_has_next_rule:
  "<iam_is_it m p m' it> iam_it_has_next it <\<lambda>r. iam_is_it m p m' it * \<up> (r = (m' \<noteq> (\<lambda>x. None)))>"
  unfolding iam_it_has_next_def
  apply(cases it)
  apply (sep_auto simp: iam_is_it_def)
  subgoal for l a b
    by (sep_auto intro: mod_exI[of _ l] simp: mod_pure_star_dist iam_of_list_def)
  subgoal for i l a b y
    apply(rule mod_exI[of _ l])
    apply (sep_auto simp: mod_pure_star_dist iam_of_list_def)
    by (metis (no_types, lifting) Cons_nth_drop_Suc diff_diff_cancel drop_all iam_lookup_abs1 le_eq_less_or_eq
        length_drop list.size(3) nth_Cons_0 option.distinct(1) zero_less_diff)
  done

lemma iam_it_finish':
  "iam_is_it m p m' it \<Longrightarrow>\<^sub>A is_iam m p"
  by(cases it)
    (sep_auto simp: iam_is_it_def is_iam_def)

lemma iam_it_finish:
  "iam_is_it m p m' it \<Longrightarrow>\<^sub>A is_iam m p * true"
  by(cases it)
    (sep_auto simp: iam_is_it_def is_iam_def)

interpretation iam: imp_map_iterate is_iam iam_is_it iam_it_init iam_it_has_next iam_it_next
proof( unfold_locales, goal_cases)
  case (1 s p)
  then show ?case 
    using iam_it_init_rule by auto
next
  case (2 m' m A it)
  then show ?case 
    using iam_it_next_rule[of m' m A it] by simp
  next
  case (3 m p m' it)
  then show ?case
    using iam_it_has_next_rule[of m p m' it] by simp
next
  case (4 m p m' it)
  then show ?case 
    using  iam_it_finish[of m p m' it] by simp
qed

end