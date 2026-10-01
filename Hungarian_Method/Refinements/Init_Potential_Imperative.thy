theory Init_Potential_Imperative
  imports Init_Potential_Collection Data_Structures.Imp_Map_Set_Addons 
          Directed_Set_Graphs.Weighted_Neighbourhoods_Imperative_Spec
          Data_Structures.Real_Embedding
begin

section \<open>Imperative Computation of the Initial Potential\<close>

text \<open>The imperative counterpart of @{locale init_potential_coll}. The weights are read at the
      cursor of the collection. The potential is an imperative map, the left vertices an
      imperative set iterated in the order @{term lst}. The program does not allocate: the
      potential handle is passed in, and represents the empty potential.\<close>

locale init_potential_imp_code =
  fixes has_imp :: "'ci \<Rightarrow> 'v \<Rightarrow> bool Heap"
    and current_cost_imp :: "'ci \<Rightarrow> 'v \<Rightarrow> 'n::linordered_idom Heap"
    and move_imp :: "'ci \<Rightarrow> 'v \<Rightarrow> unit Heap"
    and reset_imp :: "'ci \<Rightarrow> 'v \<Rightarrow> unit Heap"
    and pot_lookup_imp :: "'v \<Rightarrow> 'pi \<Rightarrow> 'n option Heap"
    and pot_update_imp :: "'v \<Rightarrow> 'n \<Rightarrow> 'pi \<Rightarrow> 'pi Heap"
    and left_it_init :: "'li \<Rightarrow> 'lit Heap"
    and left_it_has_next :: "'lit \<Rightarrow> bool Heap"
    and left_it_next :: "'lit \<Rightarrow> ('v \<times> 'lit) Heap"
begin

definition "upd_min_imp u c Pti = do {
   x \<leftarrow> pot_lookup_imp u Pti;
   (case x of None \<Rightarrow> pot_update_imp u c Pti
            | Some r \<Rightarrow> if r \<le> c then return Pti else pot_update_imp u c Pti) }"

partial_function (heap) scan_min_imp :: "'ci \<Rightarrow> 'v \<Rightarrow> 'pi \<Rightarrow> 'pi Heap" where
  "scan_min_imp Ci u Pti = do {
     b \<leftarrow> has_imp Ci u;
     (if b then do { c \<leftarrow> current_cost_imp Ci u;
                     move_imp Ci u;
                     Pti' \<leftarrow> upd_min_imp u c Pti;
                     scan_min_imp Ci u Pti' }
      else return Pti) }"

definition "init_pot_step Ci u Pti = do { reset_imp Ci u; scan_min_imp Ci u Pti }"

definition "init_pot_imp Ci Li Pti = do {
   it \<leftarrow> left_it_init Li;
   iter_fold left_it_has_next left_it_next (init_pot_step Ci) it Pti }"

end

locale init_potential_imp =
  init_potential_coll where cost = cost and vset_to_set = vset_to_set +
  real_embedding h +
  nb: weighted_neighbourhoods_imp_spec
    where idx_invar = rnb_invar and idx_abstract = rnb_abstract and idx_current = rnb_current
      and idx_has = rnb_has and idx_iterated = rnb_iterated and idx_remaining = rnb_remaining
      and idx_move = rnb_move and idx_reset = rnb_reset and K = K
      and cost = cost and wval = h and nb_init = nb_init and nb_assn = nb_assn
      and has_imp = has_imp and current_imp = current_imp and current_cost_imp = current_cost_imp
      and move_imp = move_imp and reset_imp = reset_imp and reset_all_imp = reset_all_imp +
  pot: imp_map_conn
    where is_map = pot_is_map and lookup_imp = pot_lookup_imp and update_imp = pot_update_imp
      and m_update = potential_upd and m_lookup = potential_lookup and m_invar = potential_invar
      and R = "\<lambda>_ c x. h c = x" +
  left: imp_set_ordered_iterate
    where is_set = left_is_set and lst = lst and is_it = left_is_it and it_init = left_it_init
      and it_has_next = left_it_has_next and it_next = left_it_next
  for cost :: "'v \<Rightarrow> 'v \<Rightarrow> real" and vset_to_set :: "'vset \<Rightarrow> 'v set"
    and h :: "'n::linordered_idom \<Rightarrow> real"
    and nb_init nb_assn has_imp current_imp current_cost_imp move_imp reset_imp reset_all_imp
    and pot_is_map pot_lookup_imp pot_update_imp
    and left_is_set left_is_it left_it_init left_it_has_next left_it_next

sublocale init_potential_imp \<subseteq> code: init_potential_imp_code
  has_imp current_cost_imp move_imp reset_imp pot_lookup_imp pot_update_imp
  left_it_init left_it_has_next left_it_next .

context init_potential_imp
begin

lemma upd_min_imp_rule:
  assumes "potential_invar \<pi>" "h c = cst"
  shows "<pot.map_assn \<pi> Pti> code.upd_min_imp u c Pti <pot.map_assn (upd_min u cst \<pi>)>"
proof-

  have case_rule:
    "rel_option (\<lambda>c x. h c = x) r (potential_lookup \<pi> u) \<Longrightarrow>
     <pot.map_assn \<pi> Pti>
     (case r of None \<Rightarrow> pot_update_imp u c Pti
              | Some r \<Rightarrow> if r \<le> c then return Pti else pot_update_imp u c Pti)
     <pot.map_assn (upd_min u cst \<pi>)>" for r
    using assms
    by (cases r; cases "potential_lookup \<pi> u")
       (sep_auto heap: pot.map_assn_update_rule simp: upd_min_def)+
  show ?thesis
    unfolding code.upd_min_imp_def
    apply(rule ht_bind[OF pot.map_assn_lookup_rule])
    apply(rule ht_extract_pre_pure)
    apply(rule case_rule)
    by simp
qed


lemma upd_min_invar: "potential_invar \<pi> \<Longrightarrow> potential_invar (upd_min u c \<pi>)"
  by (auto simp: upd_min_def pot.invar_update split: option.splits)

lemma scan_min_imp_rule:
  assumes "rnb_invar C" "u \<in> K" "finite (rnb_remaining C u)" "potential_invar \<pi>"
  shows "<nb_assn C Ci * pot.map_assn \<pi> Pti> code.scan_min_imp Ci u Pti
         <\<lambda>Pti'. nb_assn (fst (scan_min u C \<pi>)) Ci * pot.map_assn (snd (scan_min u C \<pi>)) Pti'>"
  using assms
proof(induction "card (rnb_remaining C u)" arbitrary: C \<pi> Pti rule: less_induct)
  case less
  show ?case
  proof(cases "rnb_has C u")
    case True
    have ne: "rnb_remaining C u \<noteq> {}" using rnb.idx_has[OF less.prems(1,2)] True by simp
    have x_in: "rnb_current C u \<in> rnb_remaining C u"
      using rnb.idx_current[OF less.prems(1,2) ne] .
    have C': "rnb_invar (rnb_move C u)"
             "rnb_remaining (rnb_move C u) u = rnb_remaining C u - {rnb_current C u}"
      using rnb.idx_move_invar[OF less.prems(1,2)] rnb.idx_move_remaining[OF less.prems(1,2) ne]
      by auto
    have card_less: "card (rnb_remaining (rnb_move C u) u) < card (rnb_remaining C u)"
      using card_Diff1_less[OF less.prems(3) x_in] by (simp add: C'(2))
    have fin': "finite (rnb_remaining (rnb_move C u) u)" using less.prems(3) by (simp add: C'(2))
    have eq: "scan_min u C \<pi> = scan_min u (rnb_move C u) (upd_min u (cost u (rnb_current C u)) \<pi>)"
      by (simp add: scan_min.simps[of u C \<pi>] True)
    note IH = less.hyps[OF card_less C'(1) less.prems(2) fin' upd_min_invar[OF less.prems(4)]]
    note um = upd_min_imp_rule[OF less.prems(4)]
    show ?thesis
      apply(subst code.scan_min_imp.simps)
      apply(sep_auto heap: nb.has_rule nb.current_cost_rule nb.move_rule
                     simp: less.prems(1,2) True ne)
      apply(sep_auto heap: um)
      by (sep_auto heap: IH simp: eq True)
  next
    case False
    have eq: "scan_min u C \<pi> = (C, \<pi>)" by (simp add: scan_min.simps[of u C \<pi>] False)
    show ?thesis
      apply(subst code.scan_min_imp.simps)
      by (sep_auto heap: nb.has_rule simp: less.prems(1,2) False eq)
  qed
qed

lemma init_pot_step_rule:
  assumes "rnb_invar C" "rnb_abstract C = rnb_abstract C0" "u \<in> K"
          "finite (rnb_abstract C0 u)" "potential_invar \<pi>"
  shows "<nb_assn C Ci * pot.map_assn \<pi> Pti> code.init_pot_step Ci u Pti
         <\<lambda>Pti'. nb_assn (fst (init_step (C, \<pi>) u)) Ci * pot.map_assn (snd (init_step (C, \<pi>) u)) Pti'>"
proof-
  have C1: "rnb_invar (rnb_reset C u)" "finite (rnb_remaining (rnb_reset C u) u)"
    using rnb.idx_reset_invar[OF assms(1,3)] rnb.idx_reset_remaining[OF assms(1,3)] assms(2,4)
    by auto
  note sc = scan_min_imp_rule[OF C1(1) assms(3) C1(2) assms(5)]
  show ?thesis
    unfolding code.init_pot_step_def init_step_def
    by (sep_auto heap: nb.reset_rule sc simp: assms(1,3))
qed

definition "init_pre C0 u Cp =
  (u \<in> K \<and> finite (rnb_abstract C0 u) \<and> rnb_invar (fst Cp) \<and>
   rnb_abstract (fst Cp) = rnb_abstract C0 \<and> potential_invar (snd Cp))"

lemma init_fold_pre_imp:
  "\<lbrakk>init_inv C0 pot0 S Cp; set xs \<subseteq> K; \<forall>u\<in>set xs. finite (rnb_abstract C0 u)\<rbrakk> \<Longrightarrow>
   fold_pre (init_pre C0) init_step Cp xs"
proof(induction xs arbitrary: S Cp)
  case (Cons x xs)
  have "init_inv C0 pot0 (insert x S) (init_step Cp x)"
    using init_step_inv[OF Cons.prems(1)] Cons.prems(2,3) by simp
  hence "fold_pre (init_pre C0) init_step (init_step Cp x) xs"
    using Cons.IH Cons.prems(2,3) by simp
  moreover have "init_pre C0 x Cp"
    using Cons.prems by (auto simp: init_pre_def init_inv_def)
  ultimately show ?case by simp
qed simp

theorem init_pot_imp_rule:
  assumes "rnb_invar C0" "vset_invar left" "finite (vset_to_set left)"
          "vset_to_set left \<subseteq> K" "\<And>u. u \<in> vset_to_set left \<Longrightarrow> finite (rnb_abstract C0 u)"
  shows "<nb_assn C0 Ci * pot.map_assn potential_empty Pti * left_is_set (vset_to_set left) Li>
         code.init_pot_imp Ci Li Pti
         <\<lambda>Pti'. nb_assn (fst (init_potential_coll C0 potential_empty left)) Ci *
                pot.map_assn (snd (init_potential_coll C0 potential_empty left)) Pti' *
                left_is_set (vset_to_set left) Li>"
proof-
  have i0: "init_inv C0 potential_empty {} (C0, potential_empty)"
    using assms(1) by (auto simp: init_inv_def pot.invar_empty pot.map_empty)
  have res: "init_potential_coll C0 potential_empty left =
             foldl init_step (C0, potential_empty) (lst (vset_to_set left))"
    by (simp add: init_potential_coll_def vset_iterate_lst[OF assms(2)])
  have pre: "fold_pre (init_pre C0) init_step (C0, potential_empty) (lst (vset_to_set left))"
    using init_fold_pre_imp[OF i0] assms(4,5) lst_set[OF assms(3)] by auto
  have step: "\<And>u Cp Pti. init_pre C0 u Cp \<Longrightarrow>
     <nb_assn (fst Cp) Ci * pot.map_assn (snd Cp) Pti> code.init_pot_step Ci u Pti
     <\<lambda>Pti'. nb_assn (fst (init_step Cp u)) Ci * pot.map_assn (snd (init_step Cp u)) Pti'>"
  proof-
    fix u Cp Pti assume a: "init_pre C0 u Cp"
    obtain C \<pi> where Cp: "Cp = (C, \<pi>)" by (cases Cp) auto
    show "<nb_assn (fst Cp) Ci * pot.map_assn (snd Cp) Pti> code.init_pot_step Ci u Pti
     <\<lambda>Pti'. nb_assn (fst (init_step Cp u)) Ci * pot.map_assn (snd (init_step Cp u)) Pti'>"
      using a init_pot_step_rule[of C C0 u \<pi> Ci Pti] by (simp add: init_pre_def Cp)
  qed
  note fold = iter_fold_rule_gen[where I = "left_is_it (vset_to_set left) Li"
      and Q = "left_is_set (vset_to_set left) Li"
      and A = "\<lambda>Cp Pti. nb_assn (fst Cp) Ci * pot.map_assn (snd Cp) Pti",
      OF left.it_has_next_rule left.it_next_rule left.quit_iteration step pre]
  show ?thesis
    unfolding code.init_pot_imp_def res
    by (sep_auto heap: left.it_init_rule fold[simplified])
qed
end

end
