theory CSR_Graph_Simple
  imports Separation_Logic_Imperative_HOL_Partial.Imp_Map_Spec
    Directed_Set_Graphs.Pair_Graph_Imperative 
    Directed_Set_Graphs.Multigraph Imperative.Array_Range_Iteration
begin  

section \<open>The CSR Representation of a Graph by Plain Arrays\<close>

text \<open>The neighbours of all vertices are stored consecutively in one array, together with two
      arrays of the first and the last position of the neighbours of each vertex.\<close>

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
  assumes "\<And> acc acci x vs. \<lbrakk>nhlists v = Some vs; x \<in> set vs\<rbrakk> \<Longrightarrow>
               <acc_assn acc acci * F> fi v x acci 
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
        (\<forall>v. v \<notin> dom nhlists \<and> v < length sindices \<longrightarrow> eindices ! v < sindices ! v)) *
     acc_assn acc acci *
     F"
  let ?help_assn ="\<lambda> vstart vend n. sindicesi \<mapsto>\<^sub>a sindices * eindicesi \<mapsto>\<^sub>a eindices *
     \<up> (dom nhlists \<subseteq> {0..<length sindices} \<and>
        dom nhlists \<subseteq> {0..<length eindices} \<and>
        length sindices = length eindices \<and>
        (\<forall>v\<in>dom nhlists.
            sindices ! v < length nha \<and>
            eindices ! v < length nha \<and> the (nhlists v) = nths nha {sindices ! v..eindices ! v}) \<and>
        (\<forall>v. v \<notin> dom nhlists \<and> v < length sindices \<longrightarrow> eindices ! v < sindices ! v)) *
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
              by (metis domI le_eq_less_or_eq option.sel)
            subgoal for res
              apply (sep_auto simp: domIff mod_pure_star_dist)
               apply(rule forw_subst[of vs "nths nha {vstart..vend}"])
              apply (metis domI option.sel)
              by sep_auto 
            subgoal
              using iterate_range_rule[of nha vstart vend acc_assn F "fi v" "f v" Gi  acc acci, OF assms]
              apply (sep_auto simp: mod_pure_star_dist[where P = "_ * _ *_ *_*_*_", simplified])
              apply (metis option.sel domI)
              by(sep_auto simp: mod_pure_star_dist[where P = "_ * _ *_ *_*_*_", simplified])
            done
          done
        done
      done
qed

lemma iterate_neighbourhood_rule:
  assumes "\<And> acc acci x vs. \<lbrakk>nhlists v = Some vs; x \<in> set vs\<rbrakk> 
              \<Longrightarrow><acc_assn acc acci * F> fi v x acci 
            <\<lambda> r. acc_assn (f v acc x) r * F>"
  shows "<CSR_assn nhlists Gi sindicesi eindicesi* acc_assn acc acci * F>
         iterate_neighbourhood Gi sindicesi eindicesi v fi acci
        <\<lambda> r. CSR_assn nhlists Gi sindicesi eindicesi* F* 
              acc_assn (foldl (f v) acc (case nhlists v of None \<Rightarrow> Nil | Some vs \<Rightarrow> vs)) r>"
  using iterate_neighbourhood_raw_rule[of nhlists v acc_assn F fi  f, OF assms, simplified]
  unfolding CSR_assn_def 
  by sep_auto
(*
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
qed(*
end*)

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
*)
end