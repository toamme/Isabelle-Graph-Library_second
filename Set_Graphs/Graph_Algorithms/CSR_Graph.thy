theory CSR_Graph
  imports Separation_Logic_Imperative_HOL_Partial.Imp_Map_Spec
    Directed_Set_Graphs.Pair_Graph_Imperative BFS_Refinement
begin                       

term nths

value "nths [(0::nat),1,2,3,4,5,6,7,8] (Set.insert 6 {(1::nat)..4})"

lemma intervall_rw1:"{0..ed} = {..< Suc ed}"
  by auto

lemma intervall_rw2:"{j. j \<le> n} = {..<Suc n}"
  by auto

lemma nths_intervall_as_drop_and_take:
  "nths list {start..ed} = drop (start) (take (Suc ed) list)"
  apply(induction list arbitrary: start ed)
  subgoal
    by simp
  subgoal for a list start ed
    apply(cases start)
     apply(all \<open>cases ed\<close>)
       apply (auto simp add: nths_Cons)
    subgoal
      by(auto simp add: intervall_rw2)
    by(auto simp add: nths_def)
  done

lemma nths_intervall_split_off_first:
  assumes "start \<le> end" "end < length list"
  shows "(nths list {start..end}) =  (list ! start # nths list {Suc start..end})"
  unfolding nths_intervall_as_drop_and_take
  apply(subst Cons_nth_drop_Suc[of start, symmetric])
  using assms(1,2)
  by (auto intro!: arg_cong2[where f = Cons] simp add: assms(1) le_imp_less_Suc)

lemma nth_shifted_by_lower_bound_of_nths_intervall:
  assumes "u < length xs" "i \<ge> l" "i \<le> u"
  shows "nths xs {l..u} ! (i -l) = xs ! i" 
  unfolding nths_intervall_as_drop_and_take
  using assms
  by (subst nth_drop)(auto simp add: le_imp_less_Suc)

lemma nth_of_nths_intervall_shifted_by_lower_bound:
  assumes "u < length xs" "l + i \<le> u" 
  shows "nths xs {l..u} ! (i) = xs ! (i + l)" 
  unfolding nths_intervall_as_drop_and_take
  using assms
  by (subst nth_drop)(auto simp add: le_imp_less_Suc algebra_simps)

lemma zip_foldl_map:
     "ys = map y xs \<Longrightarrow> foldl (\<lambda>acc a. case a of (x, y) \<Rightarrow> f x y acc) acc (zip xs ys)
      = foldl (\<lambda>acc x. f x (y x) acc) acc xs"
  by(induction xs arbitrary: acc ys) auto

lemma length_nths_of_intervall:
  assumes  "u < length xs"
  shows "length (nths xs {l..u})  = (u + 1) - l" 
  using assms
  by(auto simp add: nths_intervall_as_drop_and_take)

partial_function (heap) iterate_range where
  "iterate_range arr start end fi acc=
    (if start \<le> end then
      do{ current \<leftarrow> Array.nth arr start;
          acc' \<leftarrow> fi current acc;
          iterate_range arr (Suc start) end fi acc'}
     else return acc)"

definition "put arr new = Array.upd arr 0 new"


lemma iterate_range_rule:
  assumes "\<And> acc acci x. <acc_assn acc acci * F> fi x acci 
            <\<lambda> r. acc_assn (f acc x) r * F>"
  shows "<arr \<mapsto>\<^sub>a list * \<up> (start \<le> length list \<and> end < length list) *F * acc_assn acc acci>
          iterate_range arr start end fi acci 
         <\<lambda> r. arr \<mapsto>\<^sub>a list * acc_assn (foldl f acc (nths list {start..end})) r *  F>"
proof(induction arbitrary: start acc acci rule: iterate_range.fixp_induct, goal_cases)
  case 1
  then show ?case
    by simp
next
  case 2
  then show ?case 
    by simp
next
  case (3 fi start acc acci)
  note IH = this
  show ?case 
     using assms(1) IH(1)[of "Suc start" "f acc _"]
     by (sep_auto simp: nths_intervall_split_off_first[of start] split: if_split)
 qed

partial_function (heap) iterate_range_infoed where
  "iterate_range_infoed arr info_arr start end fi acc=
    (if start \<le> end then
      do{ current \<leftarrow> Array.nth arr start;
          current_info \<leftarrow> Array.nth info_arr start;
          acc' \<leftarrow> fi current current_info acc;
          iterate_range_infoed arr info_arr (Suc start) end fi acc'}
     else return acc)"

lemma iterate_range_infoed_rule:
  assumes "\<And> acc acci x y. <acc_assn acc acci * F> fi x y acci 
            <\<lambda> r. acc_assn (f acc (x, y)) r * F>"
  shows "<arr \<mapsto>\<^sub>a list * info_arr \<mapsto>\<^sub>a info_list *
          \<up> (start \<le> length list \<and> end < length list \<and>
             start \<le> length info_list \<and> end < length info_list) *F * acc_assn acc acci>
          iterate_range_infoed arr info_arr start end fi acci 
       <\<lambda> r. arr \<mapsto>\<^sub>a list *  info_arr \<mapsto>\<^sub>a info_list * 
        acc_assn (foldl f acc (zip (nths list {start..end}) (nths info_list {start..end}))) r * F>"
proof(induction arbitrary: start acc acci rule: iterate_range_infoed.fixp_induct, goal_cases)
  case 1
  then show ?case
    by simp
next
  case 2
  then show ?case 
    by simp
next
  case (3 fi start acc acci)
  note IH = this
  show ?case 
     using assms(1) IH(1)[of "Suc start" "f acc _"]
     by (sep_auto simp: nths_intervall_split_off_first[of start] split: if_split)
 qed

locale CSR_map = 
 imp_map_lookup is_index_map index_lookup
 for is_index_map and index_lookup::" nat \<Rightarrow> 'indices \<Rightarrow> nat option Heap"
begin

definition "CSR_assn_raw nhlists Gi sindicesi eindicesi nha sindices eindices= 
  (Gi \<mapsto>\<^sub>a nha * is_index_map sindices sindicesi
      * is_index_map eindices eindicesi * 
       \<up> (dom eindices = dom sindices \<and> dom nhlists = dom sindices \<and>
          (\<forall> v \<in> dom sindices. (the (sindices v) < length nha  \<and> the (eindices v) < length nha) 
               \<and> the (nhlists v) = nths nha {the (sindices v)..the (eindices v)})
         \<and> (\<forall> u v. ({u, v} \<subseteq> dom sindices \<and> u \<noteq> v)
             \<longrightarrow> {the (sindices v)..the (eindices v)} \<inter> {the (sindices u)..the (eindices v)} = {}))
       )"

definition "CSR_assn nhlists Gi sindicesi eindicesi = 
  (\<exists>\<^sub>A nha sindices eindices. CSR_assn_raw nhlists Gi sindicesi eindicesi nha sindices eindices)"


definition "iterate_neighbourhood Gi sindicesi eindicesi v fi acci= 
   do{ vstarto \<leftarrow> index_lookup v sindicesi;
       case vstarto of None \<Rightarrow> return acci
       | Some vstart \<Rightarrow> do{
          vendo \<leftarrow> index_lookup v eindicesi;
          let vend = the vendo;
          iterate_range Gi vstart vend (fi v) acci}}"

lemma iterate_neighbourhood_raw_rule:
  assumes "\<And> acc acci x. <acc_assn acc acci * F> fi v x acci 
            <\<lambda> r. acc_assn (f v acc x) r * F>"
  shows "<CSR_assn_raw nhlists Gi sindicesi eindicesi nha sindices eindices* acc_assn acc acci * F>
         iterate_neighbourhood Gi sindicesi eindicesi v fi acci
        <\<lambda> r. CSR_assn_raw nhlists Gi sindicesi eindicesi nha sindices eindices* F* 
              acc_assn (case nhlists v of None \<Rightarrow> acc
                        | Some vs \<Rightarrow> foldl (f v) acc vs) r>"
proof-
  let ?big_assn = "Gi \<mapsto>\<^sub>a nha * is_index_map sindices sindicesi * is_index_map eindices eindicesi *
     \<up> (dom eindices = dom sindices \<and>
        dom nhlists = dom sindices \<and>
        (\<forall>v\<in>dom sindices.
            (the (sindices v) < length nha \<and> the (eindices v) < length nha) \<and>
            the (nhlists v) = nths nha {the (sindices v)..the (eindices v)}) \<and>
        (\<forall>u v. {u, v} \<subseteq> dom sindices \<and> u \<noteq> v \<longrightarrow>
               {the (sindices v)..the (eindices v)} \<inter> {the (sindices u)..the (eindices v)} = {})) *
     acc_assn acc acci *F"
  let ?help_assn ="\<lambda> vstart vend. is_index_map sindices sindicesi * is_index_map eindices eindicesi *
     \<up> (dom eindices = dom sindices \<and>
        dom nhlists = dom sindices \<and>
        (\<forall>v\<in>dom sindices.
            the (sindices v) < length nha \<and>
            the (eindices v) < length nha \<and>
            the (nhlists v) = nths nha {the (sindices v)..the (eindices v)}) \<and>
        (\<forall>u v. {u, v} \<subseteq> dom sindices \<and> u \<noteq> v \<longrightarrow>
               {the (sindices v)..the (eindices v)} \<inter> {the (sindices u)..the (eindices v)} = {})) *
     \<up> (Some vstart = sindices v) *
     \<up> (Some vend = eindices v)"
  show ?thesis
    unfolding iterate_neighbourhood_def CSR_assn_raw_def 
    apply(rule ht_bind[where R = "\<lambda> r. ?big_assn * \<up> (r = sindices v)"])
    subgoal
      using lookup_rule by sep_auto
    subgoal for vstarto
     apply(clarsimp split!: option.split)
      subgoal 
        by sep_auto
      subgoal 
        apply sep_auto 
        by (metis domIff domI)
      subgoal
        apply sep_auto
        by (metis domI domIff)
      subgoal for vstart vs
        apply(rule ht_bind[where R = 
             "\<lambda> r. ?big_assn * \<up> (Some vstart = sindices v) * \<up> (r = eindices v)"])
        subgoal
          using lookup_rule by sep_auto
        subgoal for vendo
          apply(cases vendo)
           apply clarsimp
          subgoal
            apply sep_auto
            by (metis domIff domI)
          subgoal for vend
            apply clarsimp
            apply(rule ht_cons_prec[of _ "?help_assn vstart vend *
                Gi \<mapsto>\<^sub>a nha * \<up> (vstart \<le> length nha \<and> vend < length nha) * F * acc_assn acc acci"
                   "\<lambda> r. ?help_assn vstart vend 
               * Gi \<mapsto>\<^sub>a nha * acc_assn (foldl (f v) acc (nths nha {vstart..vend})) r * F"])
            subgoal
              apply (sep_auto simp: domIff mod_pure_star_dist)
              by (metis domI le_eq_less_or_eq option.sel)+
            subgoal for res
              apply (sep_auto  simp: domIff mod_pure_star_dist)
               apply(rule forw_subst[of vs "nths nha {vstart..vend}"])
              apply (metis option.sel domI)
              by sep_auto 
            subgoal
              using iterate_range_rule[of acc_assn F "fi v" "f v" Gi nha vstart vend acc acci, OF assms]
              by sep_auto
            done
          done
        done
      done
    done
qed

lemma iterate_neighbourhood_rule:
  assumes "\<And> acc acci x. <acc_assn acc acci * F> fi v x acci 
            <\<lambda> r. acc_assn (f v acc x) r * F>"
  shows "<CSR_assn nhlists Gi sindicesi eindicesi* acc_assn acc acci * F>
         iterate_neighbourhood Gi sindicesi eindicesi v fi acci
        <\<lambda> r. CSR_assn nhlists Gi sindicesi eindicesi* F* 
              acc_assn (case nhlists v of None \<Rightarrow> acc
                        | Some vs \<Rightarrow> foldl (f v) acc vs) r>"
  using iterate_neighbourhood_raw_rule[of acc_assn F fi v f, OF assms, 
      of nhlists Gi sindicesi eindicesi]
  unfolding CSR_assn_def 
  by sep_auto

definition "weighted_CSR_assn_raw nhlists w Gi Wi sindicesi eindicesi nha ws sindices eindices= 
  (Gi \<mapsto>\<^sub>a nha *  Wi \<mapsto>\<^sub>a ws * is_index_map sindices sindicesi
      * is_index_map eindices eindicesi * 
       \<up> (  dom eindices = dom sindices \<and> dom nhlists = dom sindices \<and>
           (\<forall> v \<in> dom sindices. (the (sindices v) < length nha  \<and> the (eindices v) < length nha \<and>
                   the (sindices v) < length ws  \<and> the (eindices v) < length ws) 
                \<and> the (nhlists v) = nths nha {the (sindices v)..the (eindices v)} \<and> 
                  (\<forall> u \<in> {the (sindices v)..the (eindices v)}. ws ! u = w v (nha ! u))) \<and>
           (\<forall> u v. ({u, v} \<subseteq> dom sindices \<and> u \<noteq> v)
              \<longrightarrow> {the (sindices v)..the (eindices v)} \<inter> {the (sindices u)..the (eindices v)} = {})
         ))"

definition "weighted_CSR_assn nhlists w Gi Wi sindicesi eindicesi = 
  (\<exists>\<^sub>A nha ws sindices eindices. 
      weighted_CSR_assn_raw nhlists w Gi Wi sindicesi eindicesi nha ws sindices eindices)"

definition "weighted_CSR_assn_raw_alt nhlists w Gi Wi sindicesi eindicesi nha ws sindices eindices= 
  (Gi \<mapsto>\<^sub>a nha *  Wi \<mapsto>\<^sub>a ws * is_index_map sindices sindicesi
      * is_index_map eindices eindicesi * 
       \<up> (  dom eindices = dom sindices \<and> dom nhlists = dom sindices \<and>
           (\<forall> v \<in> dom sindices. (the (sindices v) < length nha  \<and> the (eindices v) < length nha \<and>
                   the (sindices v) < length ws  \<and> the (eindices v) < length ws) 
                \<and> the (nhlists v) = nths nha {the (sindices v)..the (eindices v)} \<and> 
                  (\<forall> u \<in> {the (sindices v)..the (eindices v)}. 
                          ws ! u = w v (the (nhlists v) ! (u - the (sindices v))))) \<and>
           (\<forall> u v. ({u, v} \<subseteq> dom sindices \<and> u \<noteq> v)
              \<longrightarrow> {the (sindices v)..the (eindices v)} \<inter> {the (sindices u)..the (eindices v)} = {})
         ))"

lemma weighted_CSR_assn_raw_alt_same: "weighted_CSR_assn_raw_alt = weighted_CSR_assn_raw"
proof((rule ext)+, goal_cases)
  case (1 nhlists w Gi Wi sindicesi eindicesi nha ws sindices eindices)
  thus ?case
    unfolding weighted_CSR_assn_raw_alt_def weighted_CSR_assn_raw_def
    apply(rule ent_iffI)
    apply(all \<open>sep_auto simp: domIff mod_pure_star_dist,
             subst nth_shifted_by_lower_bound_of_nths_intervall\<close>)
    by auto
qed

partial_function (heap) iterate_range_infoed where
  "iterate_range_infoed arr info_arr start end fi acc=
    (if start \<le> end then
      do{ current \<leftarrow> Array.nth arr start;
          current_info \<leftarrow> Array.nth info_arr start;
          acc' \<leftarrow> fi current current_info acc;
          iterate_range_infoed arr info_arr (Suc start) end fi acc'}
     else return acc)"

lemma iterate_range_infoed_rule:
  assumes "\<And> acc acci x y. <acc_assn acc acci * F> fi x y acci 
            <\<lambda> r. acc_assn (f acc (x, y)) r * F>"
  shows "<arr \<mapsto>\<^sub>a list * info_arr \<mapsto>\<^sub>a info_list *
          \<up> (start \<le> length list \<and> end < length list \<and>
             start \<le> length info_list \<and> end < length info_list) *F * acc_assn acc acci>
          iterate_range_infoed arr info_arr start end fi acci 
       <\<lambda> r. arr \<mapsto>\<^sub>a list *  info_arr \<mapsto>\<^sub>a info_list * 
        acc_assn (foldl f acc (zip (nths list {start..end}) (nths info_list {start..end}))) r * F>"
proof(induction arbitrary: start acc acci rule: iterate_range_infoed.fixp_induct, goal_cases)
  case 1
  then show ?case
    by simp
next
  case 2
  then show ?case 
    by simp
next
  case (3 fi start acc acci)
  note IH = this
  show ?case 
     using assms(1) IH(1)[of "Suc start" "f acc _"]
     by (sep_auto simp: nths_intervall_split_off_first[of start] split: if_split)
 qed

definition "iterate_weighted_neighbourhood Gi Wi sindicesi eindicesi v fi acci= 
   do{ vstarto \<leftarrow> index_lookup v sindicesi;
       case vstarto of None \<Rightarrow> return acci
       | Some vstart \<Rightarrow> do{
          vendo \<leftarrow> index_lookup v eindicesi;
          let vend = the vendo;
          iterate_range_infoed Gi Wi vstart vend (fi v) acci}}"

lemma iterate_weighted_neighbourhood_raw_rule:
  assumes "\<And> acc acci x y. <acc_assn acc acci * F> fi v x y acci 
            <\<lambda> r. acc_assn (f v x y acc) r * F>"
  shows "<weighted_CSR_assn_raw nhlists w Gi Wi sindicesi eindicesi nha ws sindices eindices
        * acc_assn acc acci * F>
         iterate_weighted_neighbourhood Gi Wi sindicesi eindicesi v fi acci
      <\<lambda> r. weighted_CSR_assn_raw nhlists w Gi Wi sindicesi eindicesi nha ws sindices eindices* F* 
              acc_assn (case nhlists v of None \<Rightarrow> acc
                        | Some vs \<Rightarrow> foldl (\<lambda> acc x. f v x (w v x) acc) acc vs) r>"
proof-
  let ?big_assn = "Gi \<mapsto>\<^sub>a nha * Wi \<mapsto>\<^sub>a ws * is_index_map sindices sindicesi * is_index_map eindices eindicesi *
     \<up> (dom eindices = dom sindices \<and>
        dom nhlists = dom sindices \<and>
        (\<forall>v\<in>dom sindices.
            (the (sindices v) < length nha \<and>
             the (eindices v) < length nha \<and>
             the (sindices v) < length ws \<and> the (eindices v) < length ws) \<and>
            the (nhlists v) = nths nha {the (sindices v)..the (eindices v)} \<and>
            (\<forall>u\<in>{the (sindices v)..the (eindices v)}. ws ! u = w v (nha ! u))) \<and>
        (\<forall>u v. {u, v} \<subseteq> dom sindices \<and> u \<noteq> v \<longrightarrow>
               {the (sindices v)..the (eindices v)} \<inter> {the (sindices u)..the (eindices v)} = {})) *
     acc_assn acc acci *
     F"
  let ?help_assn ="\<lambda> vstart vend. is_index_map sindices sindicesi * is_index_map eindices eindicesi *
      \<up> (dom eindices = dom sindices \<and>
        dom nhlists = dom sindices \<and>
        (\<forall>v\<in>dom sindices.
            the (sindices v) < length nha \<and>
            the (eindices v) < length nha \<and>
            the (sindices v) < length ws \<and>
            the (eindices v) < length ws \<and>
            the (nhlists v) = nths nha {the (sindices v)..the (eindices v)} \<and>
            (\<forall>u\<in>{the (sindices v)..the (eindices v)}. ws ! u = w v (nha ! u))) \<and>
        (\<forall>u v. u \<in> dom sindices \<and> v \<in> dom sindices \<and> u \<noteq> v \<longrightarrow>
               the (sindices v) \<le> the (eindices v) \<longrightarrow> \<not> the (sindices u) \<le> the (eindices v))
       \<and> vstart \<le> length nha \<and> vend < length nha \<and>  vstart \<le> length ws \<and> vend < length ws 
       \<and> Some vstart = sindices v \<and> Some vend = eindices v)"
  have assn_change:
    "<acc_assn acc acci * F> fi v x y acci
        <\<lambda>r. acc_assn (case (x, y) of (x, y) \<Rightarrow> f v x y acc) r * F>" for acc acci x y
   using assms[of acc acci x y] by simp
  show ?thesis
    unfolding iterate_weighted_neighbourhood_def weighted_CSR_assn_raw_def 
    apply(rule ht_bind[where R = "\<lambda> r. ?big_assn * \<up> (r = sindices v)"])
    subgoal
      using lookup_rule by sep_auto
    subgoal for vstarto
     apply(clarsimp split!: option.split)
      subgoal 
        by sep_auto
      subgoal 
        apply sep_auto 
        by (metis domIff domI)
      subgoal
        apply sep_auto
        by (metis domI domIff)
      subgoal for vstart vs
        apply(rule ht_bind[where R = 
             "\<lambda> r. ?big_assn * \<up> (Some vstart = sindices v) * \<up> (r = eindices v)"])
        subgoal
          using lookup_rule by sep_auto
        subgoal for vendo
          apply(cases vendo)
           apply clarsimp
          subgoal
            apply sep_auto
            by (metis domIff domI)
          subgoal for vend
            apply clarsimp
            apply(rule ht_cons_prec[of _ "?help_assn vstart vend *
                Gi \<mapsto>\<^sub>a nha * Wi \<mapsto>\<^sub>a ws  * F * acc_assn acc acci"
                   "\<lambda> r. ?help_assn vstart vend 
               * Gi \<mapsto>\<^sub>a nha *  Wi \<mapsto>\<^sub>a ws * acc_assn (foldl (\<lambda> acc (x, y). f v x y acc) acc 
                    (zip (nths nha {vstart..vend}) (nths ws {vstart..vend}))) r * F"])
            subgoal
              apply (sep_auto simp: domIff mod_pure_star_dist)
              by (metis domI le_eq_less_or_eq option.sel)+
            subgoal for res
              apply (sep_auto  simp: domIff mod_pure_star_dist)
              apply(rule forw_subst[of vs "nths nha {vstart..vend}"])
              subgoal
                apply(elim ballE[where x = v])
                 apply (auto intro!: arg_cong[where f = "nths nha"])
                by (metis option.sel)+
              apply(subst zip_foldl_map[where y = "w v"])
              subgoal
                apply(rule nth_equalityI)
                subgoal
                  apply simp
                  apply (subst length_nths_of_intervall)
                   apply (metis option.sel domI)
                  apply (subst length_nths_of_intervall)
                   apply (metis option.sel domI)
                  by simp
                subgoal for i
                  apply(subst (asm) length_nths_of_intervall)
                     apply (metis option.sel domI)
                  apply simp
                  apply(subst nth_map)
                  subgoal
                     apply(subst length_nths_of_intervall)
                     apply (metis option.sel domI)
                     by simp
                  apply(subst nth_of_nths_intervall_shifted_by_lower_bound)
                  subgoal
                    by (metis option.sel domI)
                  subgoal
                    by simp
                  apply(subst nth_of_nths_intervall_shifted_by_lower_bound)
                  subgoal
                    by (metis option.sel domI)
                  subgoal
                    by simp
                  apply(elim ballE[of _ _ v])
                  subgoal
                    apply auto
                    apply(elim ballE[of _ _ "i + vstart"])
                    subgoal
                      by auto
                    subgoal
                      unfolding eq_commute[of "Some vend"]  eq_commute[of "Some vstart"]
                      by simp
                    done
                  by auto
                done
              by sep_auto
            subgoal
              using iterate_range_infoed_rule[of acc_assn F "fi v" "\<lambda>acc (x, y). f v x y acc",
                     OF assn_change, of Gi nha Wi ws vstart vend acc acci]
              by sep_auto
            done
          done
        done
      done
    done
qed

lemma iterate_weighted_neighbourhood_rule:
  assumes "\<And> acc acci x y. <acc_assn acc acci * F> fi v x y acci 
            <\<lambda> r. acc_assn (f v x y acc) r * F>"
  shows "<weighted_CSR_assn nhlists w Gi Wi sindicesi eindicesi * acc_assn acc acci * F>
         iterate_weighted_neighbourhood Gi Wi sindicesi eindicesi v fi acci
       <\<lambda> r. weighted_CSR_assn nhlists w Gi Wi sindicesi eindicesi* F* 
             acc_assn (case nhlists v of None \<Rightarrow> acc
                        | Some vs \<Rightarrow> foldl (\<lambda> acc x. f v x (w v x) acc) acc vs) r>"
  unfolding weighted_CSR_assn_def ex_assn_move_out(1)
proof((rule ht_ex_pre_and_post_I)+, goal_cases)
  case (1 nha ws sindices eindices)
  thus ?case
  using iterate_weighted_neighbourhood_raw_rule[of acc_assn F fi v f, OF assms, 
      of nhlists w Gi Wi sindicesi eindicesi nha ws sindices eindices acc acci]
  by simp
qed
end

locale CSR_array 
begin

definition "CSR_assn_raw nhlists Gi sindicesi eindicesi nha sindices eindices= 
  (Gi \<mapsto>\<^sub>a nha * sindicesi \<mapsto>\<^sub>a sindices
      * eindicesi \<mapsto>\<^sub>a eindices* 
       \<up> (
          dom nhlists \<subseteq> {0..<length sindices} \<and> dom nhlists \<subseteq> {0..<length eindices} \<and>
          length sindices = length eindices \<and>
          (\<forall> v \<in> dom nhlists. sindices ! v < length nha  \<and> eindices ! v < length nha
               \<and> the (nhlists v) = nths nha {sindices ! v..eindices ! v} \<and>
           the (nhlists v) = nths nha {sindices ! v..eindices ! v}) \<and>
          (\<forall> v. v \<notin> dom nhlists \<and> v < length sindices \<longrightarrow>
               sindices ! v > eindices ! v)
         \<and> (\<forall> u v. ({u, v} \<subseteq> dom nhlists \<and> u \<noteq> v)
             \<longrightarrow> {sindices ! v..eindices ! v} \<inter> {sindices ! u..eindices ! v} = {})
        )
   )"

definition "CSR_assn nhlists Gi sindicesi eindicesi = 
  (\<exists>\<^sub>A nha sindices eindices. CSR_assn_raw nhlists Gi sindicesi eindicesi nha sindices eindices)"

definition "iterate_neighbourhood Gi sindicesi eindicesi v fi acci= 
   do{ n \<leftarrow> Array.len sindicesi;
      if v \<ge> n then return acci
      else do{
        vstart \<leftarrow> Array.nth sindicesi v;
        vend \<leftarrow> Array.nth eindicesi v;
          iterate_range Gi vstart vend (fi v) acci}}"

lemma iterate_neighbourhood_raw_rule:
  assumes "\<And> acc acci x. <acc_assn acc acci * F> fi v x acci 
            <\<lambda> r. acc_assn (f v acc x) r * F>"
  shows "<CSR_assn_raw nhlists Gi sindicesi eindicesi nha sindices eindices* acc_assn acc acci * F>
         iterate_neighbourhood Gi sindicesi eindicesi v fi acci
        <\<lambda> r. CSR_assn_raw nhlists Gi sindicesi eindicesi nha sindices eindices* F* 
              acc_assn (foldl (f v) acc (case nhlists v of None \<Rightarrow> Nil | Some vs \<Rightarrow> vs)) r>"
proof-
  let ?big_assn = "Gi \<mapsto>\<^sub>a nha * sindicesi \<mapsto>\<^sub>a sindices * eindicesi \<mapsto>\<^sub>a eindices *
     \<up> (dom nhlists \<subseteq> {0..<length sindices} \<and>
        dom nhlists \<subseteq> {0..<length eindices} \<and>
        length sindices = length eindices \<and>
        (\<forall>v\<in>dom nhlists.
            sindices ! v < length nha \<and>
            eindices ! v < length nha \<and>
            the (nhlists v) = nths nha {sindices ! v..eindices ! v} \<and>
            the (nhlists v) = nths nha {sindices ! v..eindices ! v}) \<and>
        (\<forall>v. v \<notin> dom nhlists \<and> v < length sindices \<longrightarrow> eindices ! v < sindices ! v) \<and>
        (\<forall>u v. {u, v} \<subseteq> dom nhlists \<and> u \<noteq> v \<longrightarrow>
               {sindices ! v..eindices ! v} \<inter> {sindices ! u..eindices ! v} = {})) *
     acc_assn acc acci *
     F"
  let ?help_assn ="\<lambda> vstart vend n. sindicesi \<mapsto>\<^sub>a sindices * eindicesi \<mapsto>\<^sub>a eindices *
     \<up> (dom nhlists \<subseteq> {0..<length sindices} \<and>
        dom nhlists \<subseteq> {0..<length eindices} \<and>
        length sindices = length eindices \<and>
        (\<forall>v\<in>dom nhlists.
            sindices ! v < length nha \<and>
            eindices ! v < length nha \<and> the (nhlists v) = nths nha {sindices ! v..eindices ! v}) \<and>
        (\<forall>v. v \<notin> dom nhlists \<and> v < length sindices \<longrightarrow> eindices ! v < sindices ! v) \<and>
        (\<forall>u v. u \<in> dom nhlists \<and> v \<in> dom nhlists \<and> u \<noteq> v \<longrightarrow>
               sindices ! v \<le> eindices ! v \<longrightarrow> \<not> sindices ! u \<le> eindices ! v)) *
        \<up> (vstart \<le> length nha \<and> vend < length nha \<and>
                           n = length sindices \<and> vstart = sindices ! v \<and> vend = eindices ! v)"
  show ?thesis
    unfolding iterate_neighbourhood_def CSR_assn_raw_def 
    apply(rule ht_bind[where R = "\<lambda> r. ?big_assn * \<up> (r = length sindices)"])
    subgoal
       by sep_auto
    apply(clarsimp split!: if_split option.split)
    subgoal for n
      by sep_auto
    subgoal for n vs
      by sep_auto
    subgoal for n
      by (sep_auto elim:  allE[of "\<lambda> v. v \<notin> dom nhlists \<and> v < length eindices 
                   \<longrightarrow> eindices ! v < sindices ! v" v] simp: iterate_range.simps)
    subgoal for n vs
        apply(rule ht_bind[where R = 
             "\<lambda> r. ?big_assn * \<up> (n = length sindices \<and> r = sindices ! v)"])
      subgoal
        by sep_auto
      subgoal for vstart
        apply(rule ht_bind[where R = 
             "\<lambda> r. ?big_assn * \<up> (n = length sindices \<and> vstart = sindices ! v \<and> r = eindices ! v)"])
        subgoal
           by sep_auto
          subgoal for vend
            apply clarsimp
            apply(rule ht_cons_prec[of _ "?help_assn vstart vend n *  Gi \<mapsto>\<^sub>a nha * F * acc_assn acc acci"
                   "\<lambda> r. ?help_assn vstart vend  n * Gi \<mapsto>\<^sub>a nha * 
                       acc_assn (foldl (f v) acc (nths nha {vstart..vend})) r * F"])
            subgoal
              apply (sep_auto simp: domIff mod_pure_star_dist)
              by (metis domI le_eq_less_or_eq option.sel)+
            subgoal for res
              apply (sep_auto simp: domIff mod_pure_star_dist)
               apply(rule forw_subst[of vs "nths nha {vstart..vend}"])
              apply (metis domI option.sel)
              by sep_auto 
            subgoal
              using iterate_range_rule[of acc_assn F "fi v" "f v" Gi nha vstart vend acc acci, OF assms]
              by sep_auto
            done
          done
        done
      done
qed

lemma iterate_neighbourhood_rule:
  assumes "\<And> acc acci x. <acc_assn acc acci * F> fi v x acci 
            <\<lambda> r. acc_assn (f v acc x) r * F>"
  shows "<CSR_assn nhlists Gi sindicesi eindicesi* acc_assn acc acci * F>
         iterate_neighbourhood Gi sindicesi eindicesi v fi acci
        <\<lambda> r. CSR_assn nhlists Gi sindicesi eindicesi* F* 
              acc_assn (foldl (f v) acc (case nhlists v of None \<Rightarrow> Nil | Some vs \<Rightarrow> vs)) r>"
  using iterate_neighbourhood_raw_rule[of acc_assn F fi v f, OF assms, 
      of nhlists Gi sindicesi eindicesi]
  unfolding CSR_assn_def 
  by sep_auto

definition "weighted_CSR_assn_raw nhlists w Gi Wi sindicesi eindicesi nha ws sindices eindices= 
  (Gi \<mapsto>\<^sub>a nha * sindicesi \<mapsto>\<^sub>a sindices * eindicesi \<mapsto>\<^sub>a eindices * Wi \<mapsto>\<^sub>a ws* 
       \<up> (
          dom nhlists \<subseteq> {0..<length sindices} \<and> dom nhlists \<subseteq> {0..<length eindices} \<and>
          length sindices = length eindices \<and>
          (\<forall> v \<in> dom nhlists. sindices ! v < length nha  \<and> eindices ! v < length nha
               \<and> the (nhlists v) = nths nha {sindices ! v..eindices ! v} \<and>
               sindices ! v < length ws  \<and> eindices ! v < length ws \<and>
           the (nhlists v) = nths nha {sindices ! v..eindices ! v} \<and> 
            (\<forall> u \<in> {(sindices ! v)..(eindices ! v)}. ws ! u = w v (nha ! u))) \<and>
          (\<forall> v. v \<notin> dom nhlists \<and> v < length sindices \<longrightarrow>
               sindices ! v > eindices ! v)
         \<and> (\<forall> u v. ({u, v} \<subseteq> dom nhlists \<and> u \<noteq> v)
             \<longrightarrow> {sindices ! v..eindices ! v} \<inter> {sindices ! u..eindices ! v} = {})
        )
      )"

definition "weighted_CSR_assn nhlists w Gi Wi sindicesi eindicesi = 
  (\<exists>\<^sub>A nha ws sindices eindices. 
      weighted_CSR_assn_raw nhlists w Gi Wi sindicesi eindicesi nha ws sindices eindices)"

definition "weighted_CSR_assn_raw_alt nhlists w Gi Wi sindicesi eindicesi nha ws sindices eindices= 
  (Gi \<mapsto>\<^sub>a nha * sindicesi \<mapsto>\<^sub>a sindices * eindicesi \<mapsto>\<^sub>a eindices * Wi \<mapsto>\<^sub>a ws* 
       \<up> (
          dom nhlists \<subseteq> {0..<length sindices} \<and> dom nhlists \<subseteq> {0..<length eindices} \<and>
          length sindices = length eindices \<and>
          (\<forall> v \<in> dom nhlists. sindices ! v < length nha  \<and> eindices ! v < length nha
               \<and> the (nhlists v) = nths nha {sindices ! v..eindices ! v} \<and>
               sindices ! v < length ws  \<and> eindices ! v < length ws \<and>
           the (nhlists v) = nths nha {sindices ! v..eindices ! v} \<and> 
            (\<forall> u \<in> {(sindices ! v)..(eindices ! v)}. ws ! u = w v (the (nhlists v) ! (u - sindices ! v)))) \<and>
          (\<forall> v. v \<notin> dom nhlists \<and> v < length sindices \<longrightarrow>
               sindices ! v > eindices ! v)
         \<and> (\<forall> u v. ({u, v} \<subseteq> dom nhlists \<and> u \<noteq> v)
             \<longrightarrow> {sindices ! v..eindices ! v} \<inter> {sindices ! u..eindices ! v} = {})
        )
      )"

lemma weighted_CSR_assn_raw_alt_same: "weighted_CSR_assn_raw_alt = weighted_CSR_assn_raw"
proof((rule ext)+, goal_cases)
  case (1 nhlists w Gi Wi sindicesi eindicesi nha ws sindices eindices)
  thus ?case
    unfolding weighted_CSR_assn_raw_alt_def weighted_CSR_assn_raw_def
    apply(rule ent_iffI)
    apply(all \<open>sep_auto simp: domIff mod_pure_star_dist,
             subst nth_shifted_by_lower_bound_of_nths_intervall\<close>)
    by auto
qed

definition "iterate_weighted_neighbourhood Gi Wi sindicesi eindicesi v fi acci= 
   do{n \<leftarrow> Array.len sindicesi;
      if v \<ge> n then return acci
      else do{
        vstart \<leftarrow> Array.nth sindicesi v;
        vend \<leftarrow> Array.nth eindicesi v;
        iterate_range_infoed Gi Wi vstart vend (fi v) acci}}"

lemma iterate_weighted_neighbourhood_raw_rule:
  assumes "\<And> acc acci x y. <acc_assn acc acci * F> fi v x y acci 
            <\<lambda> r. acc_assn (f v x y acc) r * F>"
  shows "<weighted_CSR_assn_raw nhlists w Gi Wi sindicesi eindicesi nha ws sindices eindices
        * acc_assn acc acci * F>
         iterate_weighted_neighbourhood Gi Wi sindicesi eindicesi v fi acci
      <\<lambda> r. weighted_CSR_assn_raw nhlists w Gi Wi sindicesi eindicesi nha ws sindices eindices* F* 
              acc_assn (case nhlists v of None \<Rightarrow> acc
                        | Some vs \<Rightarrow> foldl (\<lambda> acc x. f v x (w v x) acc) acc vs) r>"
proof-
  let ?big_assn = "Gi \<mapsto>\<^sub>a nha * sindicesi \<mapsto>\<^sub>a sindices * eindicesi \<mapsto>\<^sub>a eindices * Wi \<mapsto>\<^sub>a ws *
     \<up> (dom nhlists \<subseteq> {0..<length sindices} \<and>
        dom nhlists \<subseteq> {0..<length eindices} \<and>
        length sindices = length eindices \<and>
        (\<forall>v\<in>dom nhlists.
            sindices ! v < length nha \<and>
            eindices ! v < length nha \<and>
            the (nhlists v) = nths nha {sindices ! v..eindices ! v} \<and>
            sindices ! v < length ws \<and>
            eindices ! v < length ws \<and>
            the (nhlists v) = nths nha {sindices ! v..eindices ! v} \<and>
            (\<forall>u\<in>{sindices ! v..eindices ! v}. ws ! u = w v (nha ! u))) \<and>
        (\<forall>v. v \<notin> dom nhlists \<and> v < length sindices \<longrightarrow> eindices ! v < sindices ! v) \<and>
        (\<forall>u v. {u, v} \<subseteq> dom nhlists \<and> u \<noteq> v \<longrightarrow> {sindices ! v..eindices ! v} \<inter> {sindices ! u..eindices ! v} = {})) *
     acc_assn acc acci *
     F"
  let ?help_assn ="\<lambda> vstart vend n vs.  sindicesi \<mapsto>\<^sub>a sindices * eindicesi \<mapsto>\<^sub>a eindices * 
     \<up> (dom nhlists \<subseteq> {0..<length sindices} \<and>
        dom nhlists \<subseteq> {0..<length eindices} \<and>
        length sindices = length eindices \<and>
        (\<forall>v\<in>dom nhlists.
            sindices ! v < length nha \<and>
            eindices ! v < length nha \<and>
            the (nhlists v) = nths nha {sindices ! v..eindices ! v} \<and>
            sindices ! v < length ws \<and>
            eindices ! v < length ws \<and>
            the (nhlists v) = nths nha {sindices ! v..eindices ! v} \<and>
            (\<forall>u\<in>{sindices ! v..eindices ! v}. ws ! u = w v (nha ! u))) \<and>
        (\<forall>v. v \<notin> dom nhlists \<and> v < length sindices \<longrightarrow> eindices ! v < sindices ! v) \<and>
        (\<forall>u v. u \<in> dom nhlists \<and> v \<in> dom nhlists \<and> u \<noteq> v \<longrightarrow>
               sindices ! v \<le> eindices ! v \<longrightarrow> \<not> sindices ! u \<le> eindices ! v) \<and>
          n = length sindices \<and> vstart = sindices ! v \<and> vend = eindices ! v \<and>
          vstart \<le> length nha \<and> vend < length nha \<and>
                         vstart \<le> length ws \<and> vend < length ws \<and>
           vs = nths nha {sindices ! v..eindices ! v})"
  have assn_change:
    "<acc_assn acc acci * F> fi v x y acci
        <\<lambda>r. acc_assn (case (x, y) of (x, y) \<Rightarrow> f v x y acc) r * F>" for acc acci x y
   using assms[of acc acci x y] by simp
  show ?thesis
    unfolding iterate_weighted_neighbourhood_def weighted_CSR_assn_raw_def 
    apply(rule ht_bind[where R = "\<lambda> r. ?big_assn * \<up> (r = length sindices)"])
    subgoal
       by sep_auto
    apply(clarsimp split!: if_split option.split)
    subgoal for n
      by sep_auto
    subgoal for n vs
      by sep_auto
    subgoal for n
      by (sep_auto elim:  allE[of "\<lambda> v. v \<notin> dom nhlists \<and> v < length eindices 
                   \<longrightarrow> eindices ! v < sindices ! v" v] simp: iterate_range_infoed.simps)
    subgoal for n vs
        apply(rule ht_bind[where R = 
             "\<lambda> r. ?big_assn * \<up> (n = length sindices \<and> r = sindices ! v)"])
      subgoal
        by sep_auto
      subgoal for vstart
        apply(rule ht_bind[where R = 
             "\<lambda> r. ?big_assn * \<up> (n = length sindices \<and> vstart = sindices ! v \<and> r = eindices ! v)"])
        subgoal
           by sep_auto
       subgoal for vend
            apply clarsimp
          apply(rule ht_cons_prec[of _ "?help_assn vstart vend n vs*  Gi \<mapsto>\<^sub>a nha * Wi \<mapsto>\<^sub>a ws* F * acc_assn acc acci"
                   "\<lambda> r. ?help_assn vstart vend n vs* Gi \<mapsto>\<^sub>a nha * Wi \<mapsto>\<^sub>a ws* 
                      acc_assn (foldl (\<lambda> acc (x, y). f v x y acc) acc 
                    (zip (nths nha {vstart..vend}) (nths ws {vstart..vend}))) r * F"])
            subgoal
              apply (sep_auto simp: domIff mod_pure_star_dist)
              by (metis domI le_eq_less_or_eq option.sel)+
            subgoal for res
              apply sep_auto
              apply(rule forw_subst[of vs "nths nha {vstart..vend}"])
               apply force
              apply(subst zip_foldl_map[where y = "w v"])
              subgoal
                apply(rule nth_equalityI)
                subgoal
                  apply simp
                  apply (subst length_nths_of_intervall)
                   apply (metis option.sel domI)
                  apply (subst length_nths_of_intervall)
                   apply (metis option.sel domI)
                  by simp
                subgoal for i
                  apply(subst (asm) length_nths_of_intervall)
                     apply (metis option.sel domI)
                  apply simp
                  apply(subst nth_map)
                  subgoal
                     apply(subst length_nths_of_intervall)
                     apply (metis option.sel domI)
                     by simp
                  apply(subst nth_of_nths_intervall_shifted_by_lower_bound)
                  subgoal
                    by (metis option.sel domI)
                  subgoal
                    by simp
                  apply(subst nth_of_nths_intervall_shifted_by_lower_bound)
                  subgoal
                    by (metis option.sel domI)
                  subgoal
                    by simp
                  by(auto elim: ballE[of _ _ v])
                done
              subgoal
                by sep_auto
              subgoal
                by sep_auto
              subgoal
                by sep_auto
              subgoal
                by sep_auto
              subgoal
                by sep_auto
              subgoal
                by sep_auto
              subgoal 
                apply sep_auto
                by (metis domI option.sel)
              subgoal
                by sep_auto
              subgoal
                by sep_auto
              subgoal
                apply sep_auto
                by (metis domI option.sel)
              subgoal 
                apply sep_auto
                by force
              subgoal
                by sep_auto
              subgoal
                apply sep_auto
                by blast
              done
            subgoal
              using iterate_range_infoed_rule[of acc_assn F "fi v" "\<lambda>acc (x, y). f v x y acc",
                     OF assn_change, of Gi nha Wi ws vstart vend acc acci]
              by sep_auto
            done
          done
        done
      done
qed

lemma iterate_weighted_neighbourhood_rule:
  assumes "\<And> acc acci x y. <acc_assn acc acci * F> fi v x y acci 
            <\<lambda> r. acc_assn (f v x y acc) r * F>"
  shows "<weighted_CSR_assn nhlists w Gi Wi sindicesi eindicesi * acc_assn acc acci * F>
         iterate_weighted_neighbourhood Gi Wi sindicesi eindicesi v fi acci
       <\<lambda> r. weighted_CSR_assn nhlists w Gi Wi sindicesi eindicesi* F* 
              acc_assn (case nhlists v of None \<Rightarrow> acc
                        | Some vs \<Rightarrow> foldl (\<lambda> acc x. f v x (w v x) acc) acc vs) r>"
  unfolding weighted_CSR_assn_def ex_assn_move_out(1)
proof((rule ht_ex_pre_and_post_I)+, goal_cases)
  case (1 nha ws sindices eindices)
  thus ?case
  using iterate_weighted_neighbourhood_raw_rule[of acc_assn F fi v f, OF assms, 
      of nhlists w Gi Wi sindicesi eindicesi nha ws sindices eindices acc acci]
  by simp
qed
end

locale imp_map_copy = imp_map +
  constrains is_map :: "('k \<rightharpoonup> 'v) \<Rightarrow> 'm \<Rightarrow> assn"
  fixes copy :: "'m \<Rightarrow> 'm Heap"
  assumes copy_rule[sep_heap_rules]: 
    "<is_map m p> copy p <\<lambda>r. is_map m p * is_map m r>"

definition "iam_copy m = 
  do {l \<leftarrow> Array.len m;
      m' \<leftarrow> Array.new l undefined;
      blit m 0 m' 0 l;
      return m'}"

lemma iam_copy_rule:
  "<is_iam m p> iam_copy p <\<lambda>r. is_iam m p * is_iam m r>"
  unfolding is_iam_def iam_copy_def
  by sep_auto

interpretation iam_copy: imp_map_copy is_iam iam_copy
  using iam_copy_rule
  by unfold_locales


(*
definition "stack_assn = (\<lambda> stack (stackarr, sp) . 
              (\<exists>\<^sub>A xs. stackarr \<mapsto>\<^sub>a xs * \<up> (sp < length xs \<and> take sp xs =  rev stack)))"

definition "push_to_stack stack x = "

  oops
definition "stack_assn_raw stack stacktail stackarr sp = stackarr \<mapsto>"
*)

