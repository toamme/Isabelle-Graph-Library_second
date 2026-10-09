theory Path_Search_Shortcut_Imperative
  imports Path_Search_Shortcut Neighbourhood_Best_Scan_Imperative 
          Data_Structures.Imp_Map_Set_Addons
          Primal_Dual_Path_Search_Imperative
begin

section \<open>The Imperative Shortcut\<close>

text \<open>The imperative counterpart of @{const path_search_shortcut_spec.shortcut}. The cursors are
      reset once. The free left vertices are tried in iteration order until one succeeds. The key
      of a neighbour @{term r} of @{term l} is its reduced cost, read at the cursor together with
      the information whether @{term r} is free. If the shortcut succeeds, the potential of the
      row is written and the path @{term "[l, j]"} is stored in the path array. Nothing is
      allocated. The count of the matched left vertices, which decides whether the shortcut is
      tried, is a separate program.\<close>

locale path_search_shortcut_imp_code =
  fixes pot_lookup_imp :: "'v::heap \<Rightarrow> 'pi \<Rightarrow> 'n::linordered_idom option Heap"
    and pot_update_imp :: "'v \<Rightarrow> 'n \<Rightarrow> 'pi \<Rightarrow> 'pi Heap"
    and buddy_imp :: "'bdi \<Rightarrow> 'v \<Rightarrow> 'v option Heap"
    and left_it_init :: "'li \<Rightarrow> 'lit Heap"
    and left_it_has_next :: "'lit \<Rightarrow> bool Heap"
    and left_it_next :: "'lit \<Rightarrow> ('v \<times> 'lit) Heap"
    and has_imp :: "'ci \<Rightarrow> 'v \<Rightarrow> bool Heap"
    and current_imp :: "'ci \<Rightarrow> 'v \<Rightarrow> 'v Heap"
    and current_cost_imp :: "'ci \<Rightarrow> 'v \<Rightarrow> 'n Heap"
    and move_imp :: "'ci \<Rightarrow> 'v \<Rightarrow> unit Heap"
    and reset_imp :: "'ci \<Rightarrow> 'v \<Rightarrow> unit Heap"
    and reset_all_imp :: "'ci \<Rightarrow> unit Heap"
begin

sublocale bs: nb_best_scan_imp_code has_imp move_imp reset_imp .

definition "cur_red_imp Pti Bdi Ci l = do {
   r \<leftarrow> current_imp Ci l;
   c \<leftarrow> current_cost_imp Ci l;
   p \<leftarrow> pot_lookup_imp r Pti;
   b \<leftarrow> buddy_imp Bdi r;
   return (c - val_of p, r, b = None) }"

definition "row_try_imp Ci Pti Bdi l = do {
   bl \<leftarrow> buddy_imp Bdi l;
   (case bl of
      Some _ \<Rightarrow> return None
    | None \<Rightarrow> do {
        b \<leftarrow> bs.best_of_imp (cur_red_imp Pti Bdi) Ci l;
        return (case b of None \<Rightarrow> None | Some (x, j, f) \<Rightarrow> if f then Some (j, x) else None) }) }"

definition "first_success_imp Ci Li Pti Bdi = do {
   reset_all_imp Ci;
   it \<leftarrow> left_it_init Li;
   iter_find left_it_has_next left_it_next (row_try_imp Ci Pti Bdi) it }"

definition "shortcut_imp Ci Li Bdi Pti Ra = do {
   r \<leftarrow> first_success_imp Ci Li Pti Bdi;
   (case r of
      None \<Rightarrow> return (False, Pti)
    | Some (l, j, x) \<Rightarrow> do {
        Pti' \<leftarrow> pot_update_imp l x Pti;
        _ \<leftarrow> Array.upd 0 l Ra;
        _ \<leftarrow> Array.upd 1 j Ra;
        return (True, Pti') }) }"


end

locale path_search_shortcut_imp =
  path_search_shortcut where G = "G :: 'v set set"
    and potential_lookup = potential_lookup and potential_upd = potential_upd +
  bs: nb_best_scan_imp
    where rnb_current = rnb_current and rnb_has = rnb_has and rnb_move = rnb_move
      and rnb_reset = rnb_reset and rnb_invar = rnb_invar and rnb_abstract = rnb_abstract
      and rnb_iterated = rnb_iterated and rnb_remaining = rnb_remaining and K = K
      and h = h and cost = edge_costs_code and wval = h and nb_init = rnb_init
      and nb_assn = nb_assn and has_imp = has_imp and current_imp = current_imp
      and current_cost_imp = current_cost_imp and move_imp = move_imp and reset_imp = reset_imp
      and reset_all_imp = reset_all_imp +
  pot: imp_map_conn
    where is_map = pot_is_map and lookup_imp = pot_lookup_imp and update_imp = pot_update_imp
      and m_update = potential_upd and m_lookup = potential_lookup and m_invar = pot_m_invar
      and R = "\<lambda>_ c x. h c = x" +
  left: imp_set_ordered_iterate
    where is_set = left_is_set and lst = lst and is_it = left_is_it and it_init = left_it_init
      and it_has_next = left_it_has_next and it_next = left_it_next
  for G :: "'v::heap set set"
    and potential_lookup :: "'potential \<Rightarrow> 'v \<Rightarrow> real option"
    and potential_upd :: "'v \<Rightarrow> real \<Rightarrow> 'potential \<Rightarrow> 'potential"
    and h :: "'n::linordered_idom \<Rightarrow> real"
    and nb_assn has_imp current_imp current_cost_imp move_imp reset_imp reset_all_imp
    and pot_is_map pot_lookup_imp pot_update_imp pot_m_invar
    and left_is_set and lst :: "'v set \<Rightarrow> 'v list"
    and left_is_it left_it_init left_it_has_next left_it_next +
  fixes buddy_assn and buddy_imp
  assumes buddy_rule[sep_heap_rules]:
      "<buddy_assn M Bdi> buddy_imp Bdi v <\<lambda>r. buddy_assn M Bdi * \<up>(r = buddy_lookup M v)>"
    and left_order_lst: "left_order = lst L"

sublocale path_search_shortcut_imp \<subseteq> code: path_search_shortcut_imp_code
  pot_lookup_imp pot_update_imp buddy_imp left_it_init left_it_has_next left_it_next
  has_imp current_imp current_cost_imp move_imp reset_imp reset_all_imp .

context path_search_shortcut_imp
begin

text \<open>The result of a row: the imperative key represents the functional one.\<close>

definition "res_rel = (\<lambda>(j, x) (j', x'). j = j' \<and> h x = x')"

lemma val_of_h:
  "rel_option (\<lambda>c x. h c = x) p (potential_lookup \<pi> r) \<Longrightarrow>
   h (val_of p) = abstract_real_map (potential_lookup \<pi>) r"
  by (cases p; cases "potential_lookup \<pi> r") (auto simp: val_of_def abstract_real_map_def)

lemma cur_red_imp_rule:
  assumes "rnb_invar C" "l \<in> K" "rnb_remaining C l \<noteq> {}"
  shows "<nb_assn C Ci * (pot.map_assn \<pi> Pti * buddy_assn M Bdi)> code.cur_red_imp Pti Bdi Ci l
         <\<lambda>(k, r, f). nb_assn C Ci * (pot.map_assn \<pi> Pti * buddy_assn M Bdi) *
                     \<up>(h k = red \<pi> l r \<and> r = rnb_current C l \<and> f = free M r)>"
  unfolding code.cur_red_imp_def
  by (sep_auto heap: bs.nb.current_rule bs.nb.current_cost_rule pot.map_assn_lookup_rule
               simp: assms red_def free_def val_of_h)

lemma row_try_imp_rule:
  assumes "rnb_invar C" "rnb_abstract C = rnb_abstract rnb_init" "l \<in> L"
  shows "<nb_assn C Ci * (pot.map_assn \<pi> Pti * buddy_assn M Bdi)> code.row_try_imp Ci Pti Bdi l
         <\<lambda>r. nb_assn (fst (row_try M \<pi> C l)) Ci * (pot.map_assn \<pi> Pti * buddy_assn M Bdi) *
              \<up>(rel_option res_rel r (snd (row_try M \<pi> C l)))>"
proof(cases "buddy_lookup M l")
  case (Some u)
  show ?thesis
    unfolding code.row_try_imp_def
    by (sep_auto simp: row_try_def free_def Some)
next
  case None
  have lK: "l \<in> K" using assms(3) G(3) by auto
  have fin: "finite (rnb_abstract C l)" using rnb_init(3)[OF assms(3)] assms(2) by simp
  note bo = bs.best_of_imp_rule[where cur = "code.cur_red_imp Pti Bdi"
              and Ctx = "pot.map_assn \<pi> Pti * buddy_assn M Bdi" and key = "red \<pi>" and pref = "free M"
              and u = l, OF cur_red_imp_rule[OF _ lK] assms(1) lK fin]
  obtain C' b where Cb: "best_of (red \<pi>) (free M) l C = (C', b)" by fastforce
  have post: "bs.best_rel (free M) bi b \<Longrightarrow>
     rel_option res_rel (case bi of None \<Rightarrow> None | Some (x, j, f) \<Rightarrow> if f then Some (j, x) else None)
                        (snd (row_try M \<pi> C l)) \<and> fst (row_try M \<pi> C l) = C'" for bi
    using None Cb
    by (cases bi) (auto simp: row_try_def free_def bs.best_rel_def res_rel_def)
  show ?thesis
    unfolding code.row_try_imp_def
    by (sep_auto heap: bo simp: None Cb dest: post)
qed

lemma fs_step_eq:
  "fs_step M \<pi> = (\<lambda>(s, r) x. case r of
                     None \<Rightarrow> (case row_try M \<pi> s x of (s', y) \<Rightarrow> (s', map_option (Pair x) y))
                   | Some _ \<Rightarrow> (s, r))"
  by (auto simp: fun_eq_iff fs_step_def split: option.splits prod.splits)

lemma first_success_imp_rule:
  assumes "rnb_invar C" "\<forall>i\<in>K. rnb_abstract C i = rnb_abstract rnb_init i"
  shows "<nb_assn C Ci * pot.map_assn \<pi> Pti * buddy_assn M Bdi * left_is_set L Li>
         code.first_success_imp Ci Li Pti Bdi
         <\<lambda>r. nb_assn (fst (first_success M \<pi>)) Ci * pot.map_assn \<pi> Pti * buddy_assn M Bdi *
              left_is_set L Li * \<up>(rel_option (rel_prod (=) res_rel) r (snd (first_success M \<pi>)))>"
proof-
  note find = iter_find_rule_gen[where I = "left_is_it L Li" and Q = "left_is_set L Li"
      and A = "\<lambda>C. nb_assn C Ci * (pot.map_assn \<pi> Pti * buddy_assn M Bdi)"
      and g = "row_try M \<pi>" and P = "\<lambda>C. rnb_invar C \<and> rnb_abstract C = rnb_abstract rnb_init"
      and Rel = res_rel and f = "code.row_try_imp Ci Pti Bdi" and xs = "lst L" and s = rnb_init,
      OF left.it_has_next_rule left.it_next_rule left.quit_iteration]
  have find': "<left_is_it L Li (lst L) it * nb_assn rnb_init Ci * pot.map_assn \<pi> Pti *
                buddy_assn M Bdi>
     iter_find left_it_has_next left_it_next (code.row_try_imp Ci Pti Bdi) it
     <\<lambda>r. left_is_set L Li * nb_assn (fst (first_success M \<pi>)) Ci * pot.map_assn \<pi> Pti *
          buddy_assn M Bdi * \<up>(rel_option (rel_prod (=) res_rel) r (snd (first_success M \<pi>)))>"
    for it
    using find[of it] row_try_imp_rule row_try_invar bs.nb.nb_init_invar
    by (simp add: G(2) first_success_def fs_step_eq left_order_lst[symmetric] mult.assoc)
  show ?thesis
    unfolding code.first_success_imp_def
    by (sep_auto heap: bs.nb.reset_all_rule find' simp: assms)
qed

lemma rel_some:
  "rel_option (rel_prod (=) res_rel) r (Some (l, j, x)) \<longleftrightarrow> (\<exists>xi. r = Some (l, j, xi) \<and> h xi = x)"
  by (cases r) (auto simp: res_rel_def)

text \<open>The cursors may be anywhere, as long as they belong to the collection of the
      neighbourhoods. Afterwards, they still do. The path is written only on success.\<close>

theorem shortcut_imp_rule:
  assumes "rnb_invar C" "\<forall>i\<in>K. rnb_abstract C i = rnb_abstract rnb_init i"
      and len: "\<And>l j \<pi>'. shortcut M \<pi> = Some (l, j, \<pi>') \<Longrightarrow> 2 \<le> length xs"
  shows "<nb_assn C Ci * left_is_set L Li * buddy_assn M Bdi * pot.map_assn \<pi> Pti * Ra \<mapsto>\<^sub>a xs>
         code.shortcut_imp Ci Li Bdi Pti Ra
         <\<lambda>(b, Pti'). \<exists>\<^sub>Axs'. nb_assn (fst (first_success M \<pi>)) Ci * left_is_set L Li *
            buddy_assn M Bdi * Ra \<mapsto>\<^sub>a xs' * \<up>(length xs' = length xs) *
            (case shortcut M \<pi> of
               None \<Rightarrow> \<up>(\<not> b \<and> xs' = xs) * pot.map_assn \<pi> Pti'
             | Some (l, j, \<pi>') \<Rightarrow> \<up>(b \<and> take 2 xs' = [l, j]) * pot.map_assn \<pi>' Pti')>"
proof(cases "snd (first_success M \<pi>)")
  case None
  hence sc: "shortcut M \<pi> = None" by (simp add: shortcut_def)
  show ?thesis
    unfolding code.shortcut_imp_def
    by (sep_auto heap: first_success_imp_rule simp: assms(1,2) None sc)
next
  case (Some a)
  then obtain l j x where fs: "snd (first_success M \<pi>) = Some (l, j, x)" by (cases a) auto
  hence sc: "shortcut M \<pi> = Some (l, j, potential_upd l x \<pi>)" by (simp add: shortcut_def)
  have l2: "xs \<noteq> []" "1 < length xs" "Suc 0 < length xs" using len[OF sc] by auto
  have t: "take 2 (list_update (list_update xs 0 l) (Suc 0) j) = [l, j]"
    using l2 by (cases xs; cases "tl xs") (auto simp: numeral_2_eq_2)
  note fsr = first_success_imp_rule[OF assms(1,2), where M = M and \<pi> = \<pi>, unfolded fs rel_some]
  show ?thesis
    unfolding code.shortcut_imp_def
    using t by (sep_auto heap: fsr pot.map_assn_update_rule simp: sc l2)
qed


end

end