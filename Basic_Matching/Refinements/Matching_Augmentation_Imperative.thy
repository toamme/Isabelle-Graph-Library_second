theory Matching_Augmentation_Imperative
  imports Data_Structures.Imp_Map_Set_Addons Basic_Matching.Matching_Augmentation_Executable
begin

section \<open>Imperative Augmentation of Matchings\<close>

text \<open>This is the imperative counterpart of @{locale matching_augmentation_spec}. It is generic in
      the buddy map and uses the imperative map only through its interface. The augmenting path
      is not a list but the prefix of length @{term k} of an array, which belongs to the caller.
      The program does not allocate.\<close>

locale matching_augmentation_imp =
  matching_augmentation_spec buddy_empty buddy_upd buddy_delete buddy_lookup buddy_invar +
  bm: imp_map_conn
    where is_map = is_map and lookup_imp = lookup_imp and update_imp = update_imp
      and m_update = buddy_upd and m_lookup = buddy_lookup and m_invar = buddy_invar
      and R = "\<lambda>_ vi v. vi = v"
  for buddy_empty and buddy_upd :: "'v::heap \<Rightarrow> 'v \<Rightarrow> 'buddy \<Rightarrow> 'buddy"
    and buddy_delete buddy_lookup buddy_invar
    and is_map :: "('v \<rightharpoonup> 'v) \<Rightarrow> 'bi \<Rightarrow> assn" and lookup_imp update_imp
begin

abbreviation "buddy_assn \<equiv> bm.map_assn"

lemma rel_option_eq_iff[simp]: "rel_option (\<lambda>x y. x = y) a b \<longleftrightarrow> a = b"
  by (simp add: option.rel_eq)

lemma buddy_lookup_rule[sep_heap_rules]:
  "<buddy_assn M Bi> lookup_imp u Bi <\<lambda>r. buddy_assn M Bi * \<up>(r = buddy_lookup M u)>"
  by (sep_auto heap: bm.map_assn_lookup_rule)

partial_function (heap) augment_loop :: "'bi \<Rightarrow> 'v array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'bi Heap" where
  "augment_loop Bi Ra i k =
     (if i + 1 < k
      then do { u \<leftarrow> Array.nth Ra i;
                v \<leftarrow> Array.nth Ra (i + 1);
                Bi' \<leftarrow> update_imp u v Bi;
                Bi'' \<leftarrow> update_imp v u Bi';
                augment_loop Bi'' Ra (i + 2) k }
      else return Bi)"

definition "augment_imp Bi Ra k = augment_loop Bi Ra 0 k"

lemma drop_take_Cons_Cons:
  "\<lbrakk>i + 1 < k; k \<le> length xs\<rbrakk> \<Longrightarrow>
   drop i (take k xs) = xs ! i # xs ! (i + 1) # drop (i + 2) (take k xs)"
  using Cons_nth_drop_Suc[of i "take k xs"] Cons_nth_drop_Suc[of "Suc i" "take k xs"]
  by simp

lemma drop_take_short:
  "\<not> i + 1 < k \<Longrightarrow> length (drop i (take k xs)) \<le> 1"
  by simp

lemma augment_impl_short:
  "length p \<le> 1 \<Longrightarrow> augment_impl M p = M"
  by (cases "(M, p)" rule: augment_impl.cases) auto

lemma augment_loop_rule:
  "k \<le> length xs \<Longrightarrow>
   <buddy_assn M Bi * Ra \<mapsto>\<^sub>a xs> augment_loop Bi Ra i k
   <\<lambda>Bi'. buddy_assn (augment_impl M (drop i (take k xs))) Bi' * Ra \<mapsto>\<^sub>a xs>"
proof(induction "k - i" arbitrary: i M Bi rule: less_induct)
  case less
  show ?case
  proof(cases "i + 1 < k")
    case True
    note IH = less(1)[of "i + 2", OF _ less(2)]
    show ?thesis
      apply(subst augment_loop.simps)
      using True less(2)
      by (sep_auto simp: drop_take_Cons_Cons heap: IH)
  next
    case False
    show ?thesis
      apply(subst augment_loop.simps)
      using False
      by (sep_auto simp: augment_impl_short)
  qed
qed

theorem augment_imp_rule:
  "k \<le> length xs \<Longrightarrow>
   <buddy_assn M Bi * Ra \<mapsto>\<^sub>a xs> augment_imp Bi Ra k
   <\<lambda>Bi'. buddy_assn (augment_impl M (take k xs)) Bi' * Ra \<mapsto>\<^sub>a xs>"
  unfolding augment_imp_def
  using augment_loop_rule[of k xs M Bi Ra 0]
  by simp

subsection \<open>Matchings with a Cached Cardinality\<close>

text \<open>A buddy map together with a reference to the cardinality of the matching. Augmentation
      increments the reference, hence the cardinality is read in constant time.\<close>

definition counted_assn :: "'buddy \<Rightarrow> 'bi \<times> nat ref \<Rightarrow> assn" where
  "counted_assn M = (\<lambda>(Bi, Ki). buddy_assn M Bi * Ki \<mapsto>\<^sub>r card (\<M> M))"

lemma counted_assn_pair: "counted_assn M (Bi, Ki) = buddy_assn M Bi * Ki \<mapsto>\<^sub>r card (\<M> M)"
  by (simp add: counted_assn_def)

definition "augment_counted_imp = (\<lambda>(Bi, Ki) Ra k. do {
   Bi' \<leftarrow> augment_imp Bi Ra k;
   c \<leftarrow> !Ki;
   Ki := Suc c;
   return (Bi', Ki) })"

definition "matching_card_imp = (\<lambda>(Bi, Ki). !Ki)"

lemma matching_card_imp_rule:
  "<counted_assn M Mi> matching_card_imp Mi <\<lambda>c. counted_assn M Mi * \<up>(c = card (\<M> M))>"
  by (cases Mi) (sep_auto simp: counted_assn_pair matching_card_imp_def)

theorem augment_counted_imp_rule:
  "\<lbrakk>k \<le> length xs; card (\<M> (augment_impl M (take k xs))) = Suc (card (\<M> M))\<rbrakk> \<Longrightarrow>
   <counted_assn M Mi * Ra \<mapsto>\<^sub>a xs> augment_counted_imp Mi Ra k
   <\<lambda>Mi'. counted_assn (augment_impl M (take k xs)) Mi' * Ra \<mapsto>\<^sub>a xs>"
  by (cases Mi) (sep_auto heap: augment_imp_rule simp: counted_assn_pair augment_counted_imp_def)

end

end