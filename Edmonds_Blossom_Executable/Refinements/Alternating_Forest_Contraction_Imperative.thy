theory Alternating_Forest_Contraction_Imperative
  imports Basic_Matching.Alternating_Forest_Imperative
    Blossom_Executable.Alternating_Forest_Contraction
    Data_Structures.Fixed_Univ_Buckets_Specs
begin

provenance ai

section "An indexed collection with a sentinel-valued selection"

locale fixed_univ_buckets_nil_imp =
  fixed_univ_buckets U K buckets_invar buckets_abstract buckets_empty buckets_insert
    buckets_remove buckets_pick buckets_move
  for U :: "'v::heap set" and K :: "'k set"
    and buckets_invar :: "'b \<Rightarrow> bool"
    and buckets_abstract :: "'b \<Rightarrow> 'v \<Rightarrow> 'k option"
    and buckets_empty buckets_insert buckets_remove buckets_pick buckets_move +
  fixes nil :: 'v
    and buckets_assn :: "'b \<Rightarrow> 'bi \<Rightarrow> assn"
    and buckets_empty_imp :: "'bi Heap"
    and buckets_clear_imp :: "'bi \<Rightarrow> unit Heap"
    and buckets_insert_imp :: "'bi \<Rightarrow> 'v \<Rightarrow> 'k \<Rightarrow> unit Heap"
    and buckets_remove_imp :: "'bi \<Rightarrow> 'v \<Rightarrow> 'k \<Rightarrow> unit Heap"
    and buckets_pick_imp :: "'bi \<Rightarrow> 'k \<Rightarrow> 'v Heap"
  assumes nil: "nil \<notin> U"
    and buckets_empty_rule[sep_heap_rules]:
      "<emp> buckets_empty_imp <buckets_assn buckets_empty>"
    and buckets_clear_rule[sep_heap_rules]:
      "buckets_invar B \<Longrightarrow>
       <buckets_assn B Bi> buckets_clear_imp Bi <\<lambda>_. buckets_assn buckets_empty Bi>"
    and buckets_insert_rule[sep_heap_rules]:
      "\<lbrakk>buckets_invar B; x \<in> U; k \<in> K; buckets_abstract B x = None\<rbrakk> \<Longrightarrow>
       <buckets_assn B Bi> buckets_insert_imp Bi x k
       <\<lambda>_. buckets_assn (buckets_insert B x k) Bi>"
    and buckets_remove_rule[sep_heap_rules]:
      "\<lbrakk>buckets_invar B; buckets_abstract B x = Some k\<rbrakk> \<Longrightarrow>
       <buckets_assn B Bi> buckets_remove_imp Bi x k
       <\<lambda>_. buckets_assn (buckets_remove B x k) Bi>"
    and buckets_pick_rule[sep_heap_rules]:
      "\<lbrakk>buckets_invar B; k \<in> K\<rbrakk> \<Longrightarrow>
       <buckets_assn B Bi> buckets_pick_imp Bi k
       <\<lambda>x. buckets_assn B Bi * \<up>(buckets_pick B k = (if x = nil then None else Some x))>"
begin

lemma buckets_pick_nil:
  "\<lbrakk>buckets_invar B; k \<in> K;
    buckets_pick B k = (if x = nil then None else Some x)\<rbrakk> \<Longrightarrow>
   (x = nil \<longleftrightarrow> {v. buckets_abstract B v = Some k} = {})"
  by(auto simp: buckets_pick(1) split: if_splits dest: buckets_pick(2))

lemma buckets_pick_member:
  "\<lbrakk>buckets_invar B; k \<in> K; x \<noteq> nil;
    buckets_pick B k = (if x = nil then None else Some x)\<rbrakk> \<Longrightarrow>
   buckets_abstract B x = Some k \<and> x \<in> U"
  by(auto dest: buckets_pick(2) buckets_universe)

end

locale Alternating_Forest_Contraction_Imperative =
  forest_contract_manipulation where K = K +
  par: fixed_univ_map_imp K parent_invar parent_upd parent_get id parent_assn parent_upd_imp parent_get_imp +
  parc: fixed_univ_map_clear_imp K parent_invar parent_get id parent_assn parent_get_imp
    parent_empty parent_clear_imp +
  pari: fixed_univ_map_init_imp K parent_invar parent_get id parent_assn parent_get_imp
    parent_empty parent_empty_imp +
  Labels: fixed_univ_map_imp K label_invar label_upd label_get id label_assn label_upd_imp label_get_imp +
  Label_Init: fixed_univ_map_init_imp K label_invar label_get id label_assn label_get_imp
    label_empty label_empty_imp +
  Label_Clear: fixed_univ_map_clear_imp K label_invar label_get id label_assn label_get_imp
    label_empty label_clear_imp +
  Children: fixed_univ_buckets_nil_imp K K children_invar children_abstract children_empty
    children_insert children_remove children_pick children_move nil children_assn
    children_empty_imp children_clear_imp children_insert_imp children_remove_imp children_pick_imp
  for K :: "'v::heap set"
    and parent_assn parent_upd_imp parent_get_imp parent_clear_imp parent_empty_imp
    and label_invar :: "'labels \<Rightarrow> bool"
    and label_upd :: "'labels \<Rightarrow> 'v \<Rightarrow> nat \<Rightarrow> 'labels"
    and label_get label_assn label_upd_imp label_get_imp label_empty label_empty_imp label_clear_imp
    and children_invar :: "'children \<Rightarrow> bool"
    and children_abstract :: "'children \<Rightarrow> 'v \<Rightarrow> 'v option"
    and children_empty children_insert children_remove children_pick children_move
    and children_assn :: "'children \<Rightarrow> 'ci \<Rightarrow> assn"
    and children_empty_imp children_clear_imp children_insert_imp children_remove_imp children_pick_imp +
  assumes label_empty: "label_invar label_empty" "label_get label_empty = (\<lambda>_. 0)"
begin

definition "forest_labels_assn E Od li =
  (\<exists>\<^sub>AL. label_assn L li * \<up>(label_invar L \<and> vset_invar E \<and> vset_invar Od \<and>
    vset_to_set E \<inter> vset_to_set Od = {} \<and>
    (\<forall>x\<in>K. label_get L x =
      (if x \<in> vset_to_set Od then 1 else if x \<in> vset_to_set E then 2 else 0))))"

definition "indexed_parents_assn P B pai bi =
  (\<exists>\<^sub>AQ C. parent_assn Q pai * children_assn C bi *
    \<up>(parent_invar Q \<and> children_invar C \<and> parent_get Q = P \<and> children_abstract C = B))"

definition "forest_storage_assn E Od P B Ci = (case Ci of (li, pai, bi) \<Rightarrow>
  forest_labels_assn E Od li * indexed_parents_assn P B pai bi)"

definition "contractable_forest_assn F Ci =
  forest_storage_assn (evens F) (odds F) (parent_get (parents F))
    (\<lambda>x. if x \<in> vset_to_set (odds F) then parent_lookup (parents F) x else None) Ci"

definition "classify_imp Ci x = (case Ci of (li, pai, bi) \<Rightarrow> label_get_imp li x)"

lemma classify_rule:
  "x \<in> K \<Longrightarrow>
   <forest_storage_assn E Od P B Ci> classify_imp Ci x
   <\<lambda>c. forest_storage_assn E Od P B Ci *
     \<up>(c = (if x \<in> vset_to_set Od then 1 else if x \<in> vset_to_set E then 2 else 0))>"
  unfolding classify_imp_def forest_storage_assn_def forest_labels_assn_def
  by(sep_auto)

lemma forest_labels_delete_rule:
  "\<lbrakk>x \<in> K; vset_invar E; vset_invar Od; vset_to_set E \<inter> vset_to_set Od = {}\<rbrakk> \<Longrightarrow>
   <forest_labels_assn E Od li> label_upd_imp li x 0
   <\<lambda>_. forest_labels_assn (vset_delete x E) (vset_delete x Od) li>"
  unfolding forest_labels_assn_def
  by(sep_auto simp: Labels.fixed_univ_map_upd_invar Labels.fixed_univ_map_upd vset.fixed_univ_set_delete)

lemma forest_labels_even_rule:
  "\<lbrakk>x \<in> K; vset_invar E; vset_invar Od; x \<notin> vset_to_set Od;
    vset_to_set E \<inter> vset_to_set Od = {}\<rbrakk> \<Longrightarrow>
   <forest_labels_assn E Od li> label_upd_imp li x 2
   <\<lambda>_. forest_labels_assn (vset_insert x E) Od li>"
  unfolding forest_labels_assn_def
  by(sep_auto simp: Labels.fixed_univ_map_upd_invar Labels.fixed_univ_map_upd vset.fixed_univ_set_insert)

lemma forest_labels_odd_rule:
  "\<lbrakk>x \<in> K; vset_invar E; vset_invar Od; x \<notin> vset_to_set E;
    vset_to_set E \<inter> vset_to_set Od = {}\<rbrakk> \<Longrightarrow>
   <forest_labels_assn E Od li> label_upd_imp li x 1
   <\<lambda>_. forest_labels_assn E (vset_insert x Od) li>"
  unfolding forest_labels_assn_def
  by(sep_auto simp: Labels.fixed_univ_map_upd_invar Labels.fixed_univ_map_upd vset.fixed_univ_set_insert)

definition "redirect_child_imp pai bi x source target = do {
  children_remove_imp bi x source;
  children_insert_imp bi x target;
  parent_upd_imp pai x target }"

partial_function (heap) redirect_children_imp where
  "redirect_children_imp pai bi source target = do {
    x \<leftarrow> children_pick_imp bi source;
    if x = nil then return ()
    else do { redirect_child_imp pai bi x source target;
              redirect_children_imp pai bi source target } }"

lemma indexed_pick_rule:
  "source \<in> K \<Longrightarrow>
   <indexed_parents_assn P B pai bi> children_pick_imp bi source
   <\<lambda>x. indexed_parents_assn P B pai bi *
     \<up>((x = nil \<longleftrightarrow> {v. B v = Some source} = {}) \<and>
       (x \<noteq> nil \<longrightarrow> B x = Some source \<and> x \<in> K))>"
  unfolding indexed_parents_assn_def
  by(sep_auto dest: Children.buckets_pick_nil Children.buckets_pick_member)

lemma redirect_child_rule:
  "\<lbrakk>x \<in> K; target \<in> K; B x = Some source\<rbrakk> \<Longrightarrow>
   <indexed_parents_assn P B pai bi> redirect_child_imp pai bi x source target
   <\<lambda>_. indexed_parents_assn (fun_upd P x target) (fun_upd B x (Some target)) pai bi>"
  unfolding redirect_child_imp_def indexed_parents_assn_def
  by(sep_auto simp: Children.buckets_remove Children.buckets_insert
    parent_map.fixed_univ_map_upd_invar parent_map.fixed_univ_map_upd)

definition "redirected_parents P B source target =
  (\<lambda>x. if B x = Some source then target else P x)"

definition "redirected_children B source target =
  (\<lambda>x. if B x = Some source then Some target else B x)"

lemma redirect_child_effect:
  assumes "B x = Some source" "source \<noteq> target"
  shows "{v. (fun_upd B x (Some target)) v = Some source} = {v. B v = Some source} - {x}"
    "redirected_parents (fun_upd P x target) (fun_upd B x (Some target)) source target =
      redirected_parents P B source target"
    "redirected_children (fun_upd B x (Some target)) source target = redirected_children B source target"
  using assms
  by(auto simp: redirected_parents_def redirected_children_def fun_eq_iff)

lemma redirect_children_rule:
  assumes "finite S"
  shows "\<lbrakk>source \<in> K; target \<in> K; source \<noteq> target; S = {x. B x = Some source}\<rbrakk> \<Longrightarrow>
   <indexed_parents_assn P B pai bi> redirect_children_imp pai bi source target
   <\<lambda>_. indexed_parents_assn (redirected_parents P B source target)
     (redirected_children B source target) pai bi>"
  using assms
proof(induction S arbitrary: P B rule: finite_psubset_induct)
  case IH: (psubset S)
  have step: "<indexed_parents_assn (fun_upd P x target) (fun_upd B x (Some target)) pai bi>
      redirect_children_imp pai bi source target
      <\<lambda>_. indexed_parents_assn (redirected_parents P B source target)
        (redirected_children B source target) pai bi>"
    if "B x = Some source" for x
    using IH(2)[of "S - {x}" "fun_upd B x (Some target)" "fun_upd P x target"] IH(3-6) that
    by(simp only: redirect_child_effect[where B=B and x=x and source=source and target=target, OF that IH(5)]; auto simp: fun_upd_def)
  show ?case
    using IH(3-6)
    by(subst redirect_children_imp.simps;
      sep_auto heap: indexed_pick_rule redirect_child_rule step
        simp: redirected_parents_def redirected_children_def)
qed

lemma forest_labels_lookup_rule:
  "x \<in> K \<Longrightarrow>
   <forest_labels_assn E Od li> label_get_imp li x
   <\<lambda>c. forest_labels_assn E Od li *
     \<up>(c = (if x \<in> vset_to_set Od then 1 else if x \<in> vset_to_set E then 2 else 0))>"
  unfolding forest_labels_assn_def
  by(sep_auto)

lemma indexed_parent_write_rule:
  "x \<in> K \<Longrightarrow>
   <indexed_parents_assn P B pai bi> parent_upd_imp pai x v
   <\<lambda>_. indexed_parents_assn (fun_upd P x v) B pai bi>"
  unfolding indexed_parents_assn_def
  by(sep_auto simp: parent_map.fixed_univ_map_upd_invar parent_map.fixed_univ_map_upd)

definition "remove_indexed_child_imp pai bi x = do {
  p \<leftarrow> parent_get_imp pai x; children_remove_imp bi x p }"

lemma remove_indexed_child_raw:
  assumes "parent_invar Q" "children_invar C" "x \<in> K"
    "children_abstract C x = Some (parent_get Q x)"
  shows "<parent_assn Q pai * children_assn C bi> remove_indexed_child_imp pai bi x
   <\<lambda>_. parent_assn Q pai * children_assn (children_remove C x (parent_get Q x)) bi>"
  unfolding remove_indexed_child_imp_def
proof(rule ht_bind[where R="\<lambda>p. parent_assn Q pai * children_assn C bi * \<up>(p = parent_get Q x)"])
  show "<parent_assn Q pai * children_assn C bi> parent_get_imp pai x
    <\<lambda>p. parent_assn Q pai * children_assn C bi * \<up>(p = parent_get Q x)>"
    using assms
    by(sep_auto)
next
  fix p
  show "<parent_assn Q pai * children_assn C bi * \<up>(p = parent_get Q x)>
    children_remove_imp bi x p
    <\<lambda>_. parent_assn Q pai * children_assn (children_remove C x (parent_get Q x)) bi>"
    using assms
    by(sep_auto)
qed

lemma remove_indexed_child_rule:
  "\<lbrakk>x \<in> K; B x = Some (P x)\<rbrakk> \<Longrightarrow>
   <indexed_parents_assn P B pai bi> remove_indexed_child_imp pai bi x
   <\<lambda>_. indexed_parents_assn P (fun_upd B x None) pai bi>"
  unfolding indexed_parents_assn_def
  by(sep_auto heap: remove_indexed_child_raw simp: Children.buckets_remove)

definition "retire_vertex_imp x Ci = (case Ci of (li, pai, bi) \<Rightarrow> do {
  c \<leftarrow> label_get_imp li x;
  (if c = 1 then remove_indexed_child_imp pai bi x else return ());
  label_upd_imp li x 0;
  parent_upd_imp pai x nil;
  return Ci })"

lemma retire_vertex_rule:
  "\<lbrakk>x \<in> K; vset_invar E; vset_invar Od; vset_to_set E \<inter> vset_to_set Od = {};
    B x = (if x \<in> vset_to_set Od then Some (P x) else None)\<rbrakk> \<Longrightarrow>
   <forest_storage_assn E Od P B Ci> retire_vertex_imp x Ci
   <\<lambda>_. forest_storage_assn (vset_delete x E) (vset_delete x Od)
     (fun_upd P x nil) (fun_upd B x None) Ci>"
  unfolding retire_vertex_imp_def forest_storage_assn_def
  by(cases "x \<in> vset_to_set Od"; cases "x \<in> vset_to_set E"; sep_auto split: prod.splits
    heap: forest_labels_lookup_rule forest_labels_delete_rule
      indexed_parent_write_rule remove_indexed_child_rule simp: fun_upd_idem)

definition "retired_lookup f value p = (\<lambda>x. if x \<in> set p then value else f x)"

lemma retired_lookup_Cons[simp]:
  "retired_lookup f value (x # p) = retired_lookup (fun_upd f x value) value p"
  by(auto simp: retired_lookup_def fun_eq_iff)

lemma retired_lookup_Nil[simp]: "retired_lookup f value [] = f"
  by(simp add: retired_lookup_def)

partial_function (heap) retire_buffer_imp where
  "retire_buffer_imp Ci Ra i n = (if i < n then do {
    x \<leftarrow> Array.nth Ra i;
    retire_vertex_imp x Ci;
    retire_buffer_imp Ci Ra (Suc i) n }
   else return ())"

lemma retire_buffer_rule:
  "\<lbrakk>vset_invar E; vset_invar Od; set p \<subseteq> K;
    vset_to_set E \<inter> vset_to_set Od = {};
    \<forall>x\<in>set p. B x = (if x \<in> vset_to_set Od then Some (P x) else None)\<rbrakk> \<Longrightarrow>
   <forest_storage_assn E Od P B Ci * Ra \<mapsto>\<^sub>a (pre @ p @ suf)>
   retire_buffer_imp Ci Ra (length pre) (length pre + length p)
   <\<lambda>_. forest_storage_assn (foldl (\<lambda>S x. vset_delete x S) E p)
      (foldl (\<lambda>S x. vset_delete x S) Od p)
      (retired_lookup P nil p) (retired_lookup B None p) Ci * Ra \<mapsto>\<^sub>a (pre @ p @ suf)>"
proof(induction p arbitrary: pre E Od P B)
  case Nil
  show ?case
    by(subst retire_buffer_imp.simps; sep_auto)
next
  case IH: (Cons x p)
  show ?case
    using IH.prems
    by(subst retire_buffer_imp.simps;
      sep_auto heap: retire_vertex_rule
        IH.IH[of "vset_delete x E" "vset_delete x Od" "fun_upd B x None"
          "fun_upd P x nil" "pre @ [x]", simplified]
        simp: vset.fixed_univ_set_delete nth_append fun_upd_def; auto)
qed

subsection "Redirecting the even positions of a buffered path"

definition "children_parent_relation P B = (\<forall>x k. B x = Some k \<longrightarrow> P x = k)"

definition "redirected_parents_set P B S target =
  (\<lambda>x. if B x \<in> Some ` S then target else P x)"

definition "redirected_children_set B S target =
  (\<lambda>x. if B x \<in> Some ` S then Some target else B x)"

lemma redirected_children_dom[simp]:
  "dom (redirected_children B source target) = dom B"
  by(auto simp: redirected_children_def dom_def)

lemma finite_child_bucket:
  "finite (dom B) \<Longrightarrow> finite {x. B x = Some source}"
  by(rule finite_subset[where B="dom B"]; auto)

lemma redirected_parent_relation:
  "children_parent_relation P B \<Longrightarrow>
   children_parent_relation (redirected_parents P B source target) (redirected_children B source target)"
  by(auto simp: children_parent_relation_def redirected_parents_def redirected_children_def)

lemma redirected_same:
  "children_parent_relation P B \<Longrightarrow> redirected_parents P B target target = P"
  "redirected_children B target target = B"
  by(auto simp: children_parent_relation_def redirected_parents_def redirected_children_def fun_eq_iff)

lemma redirected_set_insert:
  "redirected_parents_set (redirected_parents P B source target)
      (redirected_children B source target) S target =
    redirected_parents_set P B (insert source S) target"
  "redirected_children_set (redirected_children B source target) S target =
    redirected_children_set B (insert source S) target"
  by(auto simp: redirected_parents_set_def redirected_children_set_def
    redirected_parents_def redirected_children_def fun_eq_iff)

lemma redirected_set_empty[simp]:
  "redirected_parents_set P B {} target = P"
  "redirected_children_set B {} target = B"
  by(auto simp: redirected_parents_set_def redirected_children_set_def)

lemma redirected_set_singleton:
  "redirected_parents_set P B {source} target = redirected_parents P B source target"
  "redirected_children_set B {source} target = redirected_children B source target"
  by(auto simp: redirected_parents_set_def redirected_children_set_def
    redirected_parents_def redirected_children_def)

definition "redirect_bucket_imp pai bi source target =
  (if source = target then return () else redirect_children_imp pai bi source target)"

lemma redirect_bucket_rule:
  "\<lbrakk>source \<in> K; target \<in> K; finite (dom B); children_parent_relation P B\<rbrakk> \<Longrightarrow>
   <indexed_parents_assn P B pai bi> redirect_bucket_imp pai bi source target
   <\<lambda>_. indexed_parents_assn (redirected_parents P B source target)
      (redirected_children B source target) pai bi>"
  unfolding redirect_bucket_imp_def
  by(sep_auto heap: redirect_children_rule[where S="{x. B x = Some source}"] intro: finite_child_bucket simp: redirected_same)

partial_function (heap) redirect_buffer_imp where
  "redirect_buffer_imp pai bi Ra i n target = (if i < n then do {
    source \<leftarrow> Array.nth Ra i;
    redirect_bucket_imp pai bi source target;
    redirect_buffer_imp pai bi Ra (i + 2) n target }
   else return ())"

lemma redirect_buffer_done:
  "n \<le> i \<Longrightarrow> <A> redirect_buffer_imp pai bi Ra i n target <\<lambda>_. A>"
  by(subst redirect_buffer_imp.simps; sep_auto)

lemma redirect_buffer_rule:
  "\<lbrakk>set p \<subseteq> K; target \<in> K; finite (dom B); children_parent_relation P B\<rbrakk> \<Longrightarrow>
   <indexed_parents_assn P B pai bi * Ra \<mapsto>\<^sub>a (pre @ p @ suf)>
   redirect_buffer_imp pai bi Ra (length pre) (length pre + length p) target
   <\<lambda>_. indexed_parents_assn (redirected_parents_set P B (set (take_evens p)) target)
      (redirected_children_set B (set (take_evens p)) target) pai bi *
      Ra \<mapsto>\<^sub>a (pre @ p @ suf)>"
proof(induction p arbitrary: pre P B rule: take_evens.induct)
  case 1
  show ?case
    by(subst redirect_buffer_imp.simps; sep_auto)
next
  case (2 x)
  then show ?case
    by(subst redirect_buffer_imp.simps;
      sep_auto heap: redirect_bucket_rule redirect_buffer_done
        simp: nth_append redirected_set_singleton; auto)
next
  case IH: (3 x y p)
  show ?case
    using IH.prems
    by(subst redirect_buffer_imp.simps;
      sep_auto heap: redirect_bucket_rule
        IH.IH[of "redirected_children B x target" "redirected_parents P B x target" "pre @ [x,y]",
          simplified]
        simp: nth_append redirected_set_insert intro: redirected_parent_relation; auto)
qed

lemma retired_parent_relation:
  "children_parent_relation P B \<Longrightarrow>
   children_parent_relation (retired_lookup P nil p) (retired_lookup B None p)"
  by(auto simp: children_parent_relation_def retired_lookup_def)

lemma retired_children_dom[simp]:
  "dom (retired_lookup B None p) = dom B - set p"
  by(auto simp: retired_lookup_def dom_def)

definition "forest_parent_imp x Ci = (case Ci of (li, pai, bi) \<Rightarrow>
  parent_get_imp pai x)"

lemma forest_parent_rule:
  "x \<in> K \<Longrightarrow>
   <forest_storage_assn E Od P B Ci> forest_parent_imp x Ci
   <\<lambda>v. forest_storage_assn E Od P B Ci * \<up>(v = P x)>"
  unfolding forest_parent_imp_def forest_storage_assn_def indexed_parents_assn_def
  by(sep_auto split: prod.splits)

definition "redirect_path_imp Ci Ra i n target = (case Ci of (li, pai, bi) \<Rightarrow>
  redirect_buffer_imp pai bi Ra i n target)"

lemma redirect_path_rule:
  "\<lbrakk>set p \<subseteq> K; target \<in> K; finite (dom B); children_parent_relation P B\<rbrakk> \<Longrightarrow>
   <forest_storage_assn E Od P B Ci * Ra \<mapsto>\<^sub>a (pre @ p @ suf)>
   redirect_path_imp Ci Ra (length pre) (length pre + length p) target
   <\<lambda>_. forest_storage_assn E Od (redirected_parents_set P B (set (take_evens p)) target)
      (redirected_children_set B (set (take_evens p)) target) Ci *
      Ra \<mapsto>\<^sub>a (pre @ p @ suf)>"
  unfolding redirect_path_imp_def forest_storage_assn_def
  by(sep_auto split: prod.splits heap: redirect_buffer_rule)

definition "install_contracted_imp target outside Ci = (case Ci of (li, pai, bi) \<Rightarrow> do {
  parent_upd_imp pai target outside;
  label_upd_imp li target 2;
  return Ci })"

lemma install_contracted_rule:
  "\<lbrakk>target \<in> K; vset_invar E; vset_invar Od;
    vset_to_set E \<inter> vset_to_set Od = {}; target \<notin> vset_to_set Od\<rbrakk> \<Longrightarrow>
   <forest_storage_assn E Od P B Ci> install_contracted_imp target outside Ci
   <\<lambda>_. forest_storage_assn (vset_insert target E) Od (fun_upd P target outside) B Ci>"
  unfolding install_contracted_imp_def forest_storage_assn_def
  by(sep_auto split: prod.splits heap: forest_labels_even_rule indexed_parent_write_rule)

lemma buffered_path_last:
  "p \<noteq> [] \<Longrightarrow> (pre @ p @ suf) ! (length pre + length p - 1) = last p"
  by(cases p rule: rev_cases; auto simp: nth_append)

subsection "Contraction within caller-owned path buffers"

definition "contracted_parents P B p target =
  fun_upd (redirected_parents_set (retired_lookup P nil p) (retired_lookup B None p)
    (set (take_evens p)) target) target (P (last p))"

definition "contracted_children B p target =
  redirected_children_set (retired_lookup B None p) (set (take_evens p)) target"

definition "contract_path_buffer_imp Ci Ra i n target = do {
  base \<leftarrow> Array.nth Ra (n - 1);
  outside \<leftarrow> forest_parent_imp base Ci;
  retire_buffer_imp Ci Ra i n;
  redirect_path_imp Ci Ra i n target;
  install_contracted_imp target outside Ci }"

lemma contract_path_buffer_storage_rule:
  assumes "vset_invar E" "vset_invar Od" "p \<noteq> []" "set p \<subseteq> K" "target \<in> K"
    "vset_to_set E \<inter> vset_to_set Od = {}" "finite (dom B)"
    "\<forall>x. B x = (if x \<in> vset_to_set Od then Some (P x) else None)"
    "target \<notin> vset_to_set Od - set p"
  shows "<forest_storage_assn E Od P B Ci * Ra \<mapsto>\<^sub>a (pre @ p @ suf)>
   contract_path_buffer_imp Ci Ra (length pre) (length pre + length p) target
   <\<lambda>_. forest_storage_assn (vset_insert target (foldl (\<lambda>S x. vset_delete x S) E p))
      (foldl (\<lambda>S x. vset_delete x S) Od p)
      (contracted_parents P B p target) (contracted_children B p target) Ci *
      Ra \<mapsto>\<^sub>a (pre @ p @ suf)>"
proof-
  have index: "B = (\<lambda>x. if x \<in> vset_to_set Od then Some (P x) else None)"
    using assms(8)
    by(auto simp: fun_eq_iff)
  have "children_parent_relation P B"
    using assms(8)
    by(auto simp: children_parent_relation_def split: if_splits)
  with assms(1-7,9) show ?thesis
    unfolding contract_path_buffer_imp_def contracted_parents_def contracted_children_def index
    by(sep_auto heap: forest_parent_rule
      retire_buffer_rule[where p=p and pre=pre and suf=suf]
      redirect_path_rule[where p=p and pre=pre and suf=suf] install_contracted_rule
      simp: buffered_path_last[where p=p and pre=pre and suf=suf, OF assms(3), simplified One_nat_def] vset_delete_list intro: retired_parent_relation; auto)
qed

subsection "Agreement with functional forest contraction"

interpretation Forest: alternating_forest_fork_contraction_spec
  vset_invar vset_to_set evens odds get_path abstract_forest forest_invar roots K contract_fork
  by(rule spec_satisfied)

lemma parent_lookup_total_eq:
  "parent_lookup P = (\<lambda>x. if Q x = nil then None else Some (Q x)) \<longleftrightarrow> parent_get P = Q"
  by(auto simp: parent_lookup_def fun_eq_iff split: if_splits)

lemma alternating_path_positions:
  assumes "alt_list (\<lambda>x. x \<in> E) (\<lambda>x. x \<in> Od) p" "E \<inter> Od = {}"
  shows "set (take_evens p) = E \<inter> set p" "set (take_odds p) = Od \<inter> set p"
  using assms
  by(induction p rule: take_evens.induct; auto simp: alt_list_empty alt_list_step alt_list_singleton)+

lemma forest_odd_parents_defined:
  "forest_invar M F \<Longrightarrow> \<forall>x\<in>vset_to_set (odds F). parent_get (parents F) x \<noteq> nil"
  using forest_invarD(7)[of M F]
  by(auto simp: invar_odd_to_parent_non_matching_def parent_lookup_def split: if_splits)

lemma contract_path_parent_view:
  assumes "forest_invar M F" "p \<noteq> []" "set p \<subseteq> K" "target \<in> K"
    "origin_lookup (origins F) (last p) \<noteq> None"
    "set (take_evens p) = vset_to_set (evens F) \<inter> set p"
    "set (take_odds p) = vset_to_set (odds F) \<inter> set p"
    "target \<notin> vset_to_set (odds F) - set p"
    "target \<notin> set p \<longrightarrow> parent_get (parents F) target = nil"
  shows "parent_get (parents (contract_path F p target)) =
    contracted_parents (parent_get (parents F))
      (\<lambda>x. if x \<in> vset_to_set (odds F) then Some (parent_get (parents F) x) else None) p target"
proof-
  note basic = invar_basicD[OF forest_invarD(1)[OF assms(1)]]
  note effect = effect_of_contract_path[where evs="evens F" and ods="odds F" and rts="roots F"
    and prnts="parents F" and orngs="origins F" and p=p and new_vert=target
    and new_forest="contract_path F p target", unfolded alt_forest.collapse,
    OF basic(2,3,1,4,5) refl assms(3-5)]
  let ?Q = "contracted_parents (parent_get (parents F))
    (\<lambda>x. if x \<in> vset_to_set (odds F) then Some (parent_get (parents F) x) else None) p target"
  show ?thesis
  proof(rule parent_lookup_total_eq[THEN iffD1], rule ext)
    fix x
    show "parent_lookup (parents (contract_path F p target)) x =
      (if ?Q x = nil then None else Some (?Q x))"
      unfolding effect(9) take_evens_set[symmetric] take_odds_set[symmetric] assms(6,7)
      using forest_odd_parents_defined[OF assms(1)] assms(4,8,9) nil
      by(cases "x = target"; cases "x \<in> set p"; cases "x \<in> vset_to_set (odds F)";
        auto simp: contracted_parents_def redirected_parents_set_def retired_lookup_def
          parent_lookup_def assms(6) split: if_splits)
  qed
qed

lemma forest_children_view:
  "forest_invar M F \<Longrightarrow>
   (\<lambda>x. if x \<in> vset_to_set (odds F) then parent_lookup (parents F) x else None) =
   (\<lambda>x. if x \<in> vset_to_set (odds F) then Some (parent_get (parents F) x) else None)"
  using forest_odd_parents_defined[of M F]
  by(auto simp: parent_lookup_def fun_eq_iff)

lemma contracted_children_view:
  assumes "target \<noteq> nil" "\<forall>x\<in>Od. P x \<noteq> nil" "target \<notin> Od - set p"
  shows "contracted_children (\<lambda>x. if x \<in> Od then Some (P x) else None) p target =
    (\<lambda>x. if x \<in> Od - set p then
      (let q = contracted_parents P (\<lambda>x. if x \<in> Od then Some (P x) else None) p target x
       in if q = nil then None else Some q) else None)"
  using assms
  by(auto simp: contracted_children_def contracted_parents_def redirected_children_set_def
    redirected_parents_set_def retired_lookup_def fun_eq_iff Let_def split: if_splits)

lemma forest_labels_assn_cong:
  "\<lbrakk>vset_invar E; vset_invar Od; vset_invar E'; vset_invar Od';
    vset_to_set E = vset_to_set E'; vset_to_set Od = vset_to_set Od'\<rbrakk> \<Longrightarrow>
   forest_labels_assn E Od li = forest_labels_assn E' Od' li"
  by(simp add: forest_labels_assn_def)

lemma contract_path_storage:
  assumes "forest_invar M F" "p \<noteq> []" "set p \<subseteq> K" "target \<in> K"
    "origin_lookup (origins F) (last p) \<noteq> None"
    "set (take_evens p) = vset_to_set (evens F) \<inter> set p"
    "set (take_odds p) = vset_to_set (odds F) \<inter> set p"
    "target \<notin> vset_to_set (odds F) - set p"
    "target \<notin> set p \<longrightarrow> parent_get (parents F) target = nil"
  shows "contractable_forest_assn (contract_path F p target) Ci =
    forest_storage_assn (vset_insert target (foldl (\<lambda>S x. vset_delete x S) (evens F) p))
      (foldl (\<lambda>S x. vset_delete x S) (odds F) p)
      (contracted_parents (parent_get (parents F))
        (\<lambda>x. if x \<in> vset_to_set (odds F) then Some (parent_get (parents F) x) else None) p target)
      (contracted_children
        (\<lambda>x. if x \<in> vset_to_set (odds F) then Some (parent_get (parents F) x) else None) p target) Ci"
proof-
  let ?F = "contract_path F p target"
  let ?B = "\<lambda>x. if x \<in> vset_to_set (odds F) then Some (parent_get (parents F) x) else None"
  note basic = invar_basicD[OF forest_invarD(1)[OF assms(1)]]
  note effect = effect_of_contract_path[where evs="evens F" and ods="odds F" and rts="roots F"
    and prnts="parents F" and orngs="origins F" and p=p and new_vert=target
    and new_forest="?F", unfolded alt_forest.collapse, OF basic(2,3,1,4,5) refl assms(3-5)]
  have sets: "forest_labels_assn (evens ?F) (odds ?F) li =
      forest_labels_assn (vset_insert target (foldl (\<lambda>S x. vset_delete x S) (evens F) p))
        (foldl (\<lambda>S x. vset_delete x S) (odds F) p) li" for li
    using effect(2,3,7,8) basic(2,3) assms(4,6,7)
    by(intro forest_labels_assn_cong; auto simp: vset_delete_list vset.fixed_univ_set_insert
      take_evens_set[symmetric] take_odds_set[symmetric])
  have target_ne: "target \<noteq> nil"
    using assms(4) nil
    by blast
  note index = contracted_children_view[where target=target and Od="vset_to_set (odds F)"
    and P="parent_get (parents F)" and p=p,
    OF target_ne forest_odd_parents_defined[OF assms(1)] assms(8), unfolded Let_def]
  have children: "(\<lambda>x. if x \<in> vset_to_set (odds ?F) then parent_lookup (parents ?F) x else None) =
      contracted_children ?B p target"
    unfolding parent_lookup_def
    by(simp only: index effect(7) take_odds_set[symmetric] assms(7)
      contract_path_parent_view[OF assms]; auto)
  show ?thesis
    unfolding contractable_forest_assn_def forest_storage_assn_def
    by(simp add: sets children contract_path_parent_view[OF assms] split: prod.splits)
qed

lemma contract_path_buffer_rule:
  assumes "forest_invar M F" "p \<noteq> []" "set p \<subseteq> K" "target \<in> K"
    "origin_lookup (origins F) (last p) \<noteq> None"
    "set (take_evens p) = vset_to_set (evens F) \<inter> set p"
    "set (take_odds p) = vset_to_set (odds F) \<inter> set p"
    "target \<notin> vset_to_set (odds F) - set p"
    "target \<notin> set p \<longrightarrow> parent_get (parents F) target = nil"
  shows "<contractable_forest_assn F Ci * Ra \<mapsto>\<^sub>a (pre @ p @ suf)>
    contract_path_buffer_imp Ci Ra (length pre) (length pre + length p) target
    <\<lambda>_. contractable_forest_assn (contract_path F p target) Ci *
      Ra \<mapsto>\<^sub>a (pre @ p @ suf)>"
  using assms invar_basicD[OF forest_invarD(1)[OF assms(1)]]
  unfolding contract_path_storage[OF assms]
  by(unfold contractable_forest_assn_def forest_children_view[OF assms(1)];
    intro contract_path_buffer_storage_rule; auto simp: dom_def)

lemma contract_prefix_buffer_rule:
  assumes "forest_invar M F" "get_path F v = p @ [u] @ rest"
    "v \<in> vset_to_set (evens F)" "u \<in> vset_to_set (evens F)" "target \<in> K"
    "target \<notin> vset_to_set (evens F) \<union> vset_to_set (odds F) - set (p @ [u])"
  shows "<contractable_forest_assn F Ci * Ra \<mapsto>\<^sub>a (pre @ (p @ [u]) @ suf)>
    contract_path_buffer_imp Ci Ra (length pre) (length pre + length (p @ [u])) target
    <\<lambda>_. contractable_forest_assn (contract_path F (p @ [u]) target) Ci *
      Ra \<mapsto>\<^sub>a (pre @ (p @ [u]) @ suf)>"
proof-
  note invariants = forest_invarD[OF assms(1)]
  note basic = invar_basicD[OF invariants(1)]
  have path: "set (p @ [u]) \<subseteq> K"
    using path_follow_verts_in_verts_F[OF invariants(1,6,4), of v]
      forest_vertices_in_universe[OF assms(1)] assms(2,3) basic(6)
    by(auto simp: get_path_eq_follow[OF assms(1)]; blast)
  have alternating: "alt_list (\<lambda>x. x \<in> vset_to_set (evens F))
      (\<lambda>x. x \<in> vset_to_set (odds F)) (p @ [u])"
    using follow_alternating_paths(3)[OF assms(1) _ assms(3)] assms(2)
    by(auto simp: get_path_eq_follow[OF assms(1)] 
      dest: alt_list_append_1[of _ _ "p @ [u]" rest, simplified])
  have "origin_lookup (origins F) u \<noteq> None"
    using invar_rootsD(2)[OF invariants(6)] assms(4) basic(6)
    by blast
  moreover have "target \<notin> set (p @ [u]) \<longrightarrow> parent_get (parents F) target = nil"
    using basic(6,14) assms(6)
    by(auto simp: dom_def parent_lookup_def split: if_splits)
  ultimately show ?thesis
    using assms path alternating_path_positions[OF alternating basic(7)]
    by(intro contract_path_buffer_rule; auto)
qed

definition "contract_fork_buffer_imp Ci Pa plen Qa qlen target = do {
  base \<leftarrow> Array.nth Pa (plen - 1);
  contract_path_buffer_imp Ci Pa 0 plen base;
  contract_path_buffer_imp Ci Qa 0 qlen target }"

lemma contract_fork_buffer_rule:
  assumes "Forest.contract_fork_precond M F v w p q u target rest contr"
    "u \<in> vset_to_set (evens F)" "target \<in> K"
  shows "<contractable_forest_assn F Ci * Pa \<mapsto>\<^sub>a ((p @ [u]) @ ps) *
      Qa \<mapsto>\<^sub>a ((q @ [u]) @ qs)>
    contract_fork_buffer_imp Ci Pa (length (p @ [u])) Qa (length (q @ [u])) target
    <\<lambda>_. contractable_forest_assn (contract_fork F (p @ [u]) (q @ [u]) target) Ci *
      Pa \<mapsto>\<^sub>a ((p @ [u]) @ ps) * Qa \<mapsto>\<^sub>a ((q @ [u]) @ qs)>"
proof-
  have pre: "forest_invar M F" "matching M" "dblton_graph M"
    "get_path F v = p @ [u] @ rest" "get_path F w = q @ [u] @ rest"
    "set p \<inter> set q = {}" "v \<in> vset_to_set (evens F)" "w \<in> vset_to_set (evens F)"
    "target \<notin> Vs M \<union> vset_to_set (evens F) \<union> vset_to_set (odds F) -
      (set p \<union> set q \<union> {u})"
    using assms(1)
    by(auto simp: Forest.contract_fork_precond_def)
  have paths: "follow (parent_lookup (parents F)) v = p @ [u] @ rest"
    "follow (parent_lookup (parents F)) w = q @ [u] @ rest"
    using pre(4,5)
    by(simp add: get_path_eq_follow[OF pre(1)])+
  have universe: "u \<in> K"
    using vset.fixed_univ_set_universe[OF invar_basicD(2)[OF forest_invarD(1)[OF pre(1)]]] assms(2)
    by blast
  let ?F = "contract_path F (p @ [u]) u"
  let ?M = "quot_graph (\<lambda>x. if x \<in> set (p @ [u]) then u else x) M - {{u}}"
  note first = contract_path_correct[where rts="roots F" and evs="evens F" and ods="odds F"
    and prnts="parents F" and orngs="origins F" and v=v and u=u
    and new_vert=u and contr="\<lambda>x. if x \<in> set (p @ [u]) then u else x" and new_forest="?F",
    unfolded alt_forest.collapse, OF pre(1) paths(1) pre(7) assms(2) pre(2) _ pre(3) refl refl universe,
    simplified]
  have second: "get_path ?F (if q = [] then u else w) = q @ [u] @ rest"
    using first(7)[OF paths(2)[simplified] pre(6)]
    by(simp add: get_path_eq_follow[OF first(1)])
  moreover have "(if q = [] then u else w) \<in> vset_to_set (evens ?F)"
    using pre(6,8) paths(2) first(4)
      parent.follow_hd[OF follow_dom_invar_parent_wf(1)[OF forest_invarD(4)[OF pre(1)]], of w, folded follow_def]
    by(cases q; auto)
  ultimately have second_heap:
    "<contractable_forest_assn ?F Ci * Qa \<mapsto>\<^sub>a ((q @ [u]) @ qs)>
      contract_path_buffer_imp Ci Qa 0 (length (q @ [u])) target
      <\<lambda>_. contractable_forest_assn (contract_path ?F (q @ [u]) target) Ci *
        Qa \<mapsto>\<^sub>a ((q @ [u]) @ qs)>"
    using contract_prefix_buffer_rule[where M="?M" and F="?F" and v="if q = [] then u else w"
      and p=q and u=u and rest=rest and pre="[]" and suf=qs and target=target and Ci=Ci and Ra=Qa]
      first(1,3,4) pre(9) assms(3)
    by auto
  show ?thesis
    using pre(1,4,7) assms(2) universe
    unfolding contract_fork_buffer_imp_def contract_fork_def
    by(sep_auto heap: contract_prefix_buffer_rule[where M=M and F=F and v=v and p=p and u=u
        and rest=rest and target=u and pre="[]" and suf=ps, simplified] second_heap[simplified]
      simp: buffered_path_last[where pre="[]" and p="p @ [u]" and suf=ps, simplified])
qed

subsection "Initialization and ordinary extension"

definition "contractable_empty_imp = do {
  li \<leftarrow> label_empty_imp;
  pai \<leftarrow> parent_empty_imp;
  bi \<leftarrow> children_empty_imp;
  return (li, pai, bi) }"

definition "contractable_clear_imp Ci = (case Ci of (li, pai, bi) \<Rightarrow> do {
  label_clear_imp li; parent_clear_imp pai; children_clear_imp bi; return Ci })"

definition "contractable_add_root_imp v Ci = (case Ci of (li, pai, bi) \<Rightarrow> do {
  label_upd_imp li v 2; return Ci })"

definition "contractable_extend_imp x y z Ci = (case Ci of (li, pai, bi) \<Rightarrow> do {
  label_upd_imp li y 1;
  label_upd_imp li z 2;
  parent_upd_imp pai y x;
  parent_upd_imp pai z y;
  children_insert_imp bi y x;
  return Ci })"

lemma contractable_empty_rule:
  "\<lbrakk>vset_invar R; vset_to_set R = {}\<rbrakk> \<Longrightarrow>
   <emp> contractable_empty_imp <contractable_forest_assn (empty_forest R)>"
  unfolding contractable_empty_imp_def contractable_forest_assn_def forest_storage_assn_def
    forest_labels_assn_def indexed_parents_assn_def empty_forest_def
  by(sep_auto simp: label_empty empties Children.buckets_empty vset.fixed_univ_set_empty)

lemma contractable_clear_rule:
  "\<lbrakk>vset_invar R; vset_to_set R = {}\<rbrakk> \<Longrightarrow>
   <contractable_forest_assn F Ci> contractable_clear_imp Ci <contractable_forest_assn (empty_forest R)>"
  unfolding contractable_clear_imp_def contractable_forest_assn_def forest_storage_assn_def
    forest_labels_assn_def indexed_parents_assn_def empty_forest_def
  by(sep_auto split: prod.splits simp: label_empty empties Children.buckets_empty vset.fixed_univ_set_empty)

lemma contractable_add_root_rule:
  "\<lbrakk>vset_invar R; vset_invar R'; vset_to_set R' = insert v (vset_to_set R)\<rbrakk> \<Longrightarrow>
   <contractable_forest_assn (empty_forest R) Ci> contractable_add_root_imp v Ci
   <contractable_forest_assn (empty_forest R')>"
  unfolding contractable_add_root_imp_def contractable_forest_assn_def forest_storage_assn_def
    forest_labels_assn_def indexed_parents_assn_def empty_forest_def
  by(sep_auto split: prod.splits simp: Labels.fixed_univ_map_upd_invar Labels.fixed_univ_map_upd
    vset.fixed_univ_set_empty dest: vset.fixed_univ_set_universe)

lemma forest_extension_bounds:
  "forest_extension_precond F M x y z \<Longrightarrow> x \<in> K \<and> y \<in> K \<and> z \<in> K"
  by(auto elim!: forest_extension_precondE forest_invarE invar_basicE
    dest: vset.fixed_univ_set_universe edges_are_Vs edges_are_Vs_2)

lemma contractable_extend_rule:
  assumes "forest_extension_precond F M x y z"
  shows "<contractable_forest_assn F Ci> contractable_extend_imp x y z Ci
    <contractable_forest_assn (extend_forest_even_unclassified F x y z)>"
proof-
  have bounds: "x \<in> K" "y \<in> K" "z \<in> K" "x \<noteq> nil" "y \<noteq> nil"
    "y \<notin> vset_to_set (evens F) \<union> vset_to_set (odds F)"
    "z \<notin> vset_to_set (evens F) \<union> vset_to_set (odds F)" "y \<noteq> z"
    "vset_invar (evens F)" "vset_invar (odds F)" "parent_invar (parents F)"
    using assms forest_extension_bounds[OF assms] nil
    by(auto elim!: forest_extension_precondE forest_invarE invar_basicE)
  show ?thesis
    using bounds
    unfolding contractable_extend_imp_def contractable_forest_assn_def forest_storage_assn_def
      forest_labels_assn_def indexed_parents_assn_def extend_forest_even_unclassified_def
    by(sep_auto split: prod.splits simp: Labels.fixed_univ_map_upd_invar Labels.fixed_univ_map_upd
      Children.buckets_insert parent_lookup_def parent_map.fixed_univ_map_upd
      parent_map.fixed_univ_map_upd_invar vset.fixed_univ_set_insert)
qed

subsection "Paired rootward traversal"

definition "rootward P v = (if v = nil then [] else follow (parent_lookup P) v)"

lemma rootward_step:
  "\<lbrakk>parent (parent_lookup P); v \<noteq> nil\<rbrakk> \<Longrightarrow>
   rootward P v = v # rootward P (parent_get P v)"
  by(cases "parent_get P v = nil";
    simp add: rootward_def parent.follow_psimps[folded follow_def] parent_lookup_def)

lemma rootward_distinct:
  "parent (parent_lookup P) \<Longrightarrow> distinct (rootward P v)"
  by(simp add: rootward_def parent.follow_distinct[folded follow_def])

lemma rootward_suffix:
  "\<lbrakk>parent (parent_lookup P); rootward P v = pre @ u # rest; u \<noteq> nil\<rbrakk> \<Longrightarrow>
   rootward P u = u # rest"
  unfolding rootward_def
  by(auto dest: parent.follow_append[folded follow_def] split: if_splits)

definition "paired_marks tag p q A I =
  ((\<forall>i<length p. label_get A (p ! i) = 2 * tag + 1 \<and> label_get I (p ! i) = i) \<and>
   (\<forall>i<length q. label_get A (q ! i) = 2 * tag + 2 \<and> label_get I (q ! i) = i) \<and>
   (\<forall>x\<in>K - set p - set q. label_get A x < 2 * tag + 1))"

lemma paired_marks_left:
  "\<lbrakk>paired_marks tag p q A I; x \<in> set p\<rbrakk> \<Longrightarrow>
   label_get A x = 2 * tag + 1 \<and> label_get I x < length p \<and> p ! label_get I x = x"
  by(auto simp: paired_marks_def in_set_conv_nth)

lemma paired_marks_right:
  "\<lbrakk>paired_marks tag p q A I; x \<in> set q\<rbrakk> \<Longrightarrow>
   label_get A x = 2 * tag + 2 \<and> label_get I x < length q \<and> q ! label_get I x = x"
  by(auto simp: paired_marks_def in_set_conv_nth)

lemma paired_marks_lookup:
  "\<lbrakk>paired_marks tag p q A I; x \<in> K\<rbrakk> \<Longrightarrow>
   (label_get A x = 2 * tag + 1 \<longleftrightarrow> x \<in> set p) \<and>
   (label_get A x = 2 * tag + 2 \<longleftrightarrow> x \<in> set q)"
  using paired_marks_left[of tag p q A I x] paired_marks_right[of tag p q A I x]
  by(cases "x \<in> set p"; cases "x \<in> set q"; auto simp: paired_marks_def Ball_def)

lemma paired_marks_bound:
  "\<lbrakk>paired_marks tag p q A I; x \<in> K\<rbrakk> \<Longrightarrow> label_get A x < 2 * Suc tag + 1"
  using paired_marks_left[of tag p q A I x] paired_marks_right[of tag p q A I x]
  by(cases "x \<in> set p"; cases "x \<in> set q"; auto simp: paired_marks_def Ball_def)

lemma paired_marks_append_left:
  "\<lbrakk>paired_marks tag p q A I; label_invar A; label_invar I; x \<in> K;
     x \<notin> set p; x \<notin> set q\<rbrakk> \<Longrightarrow>
   paired_marks tag (p @ [x]) q (label_upd A x (2 * tag + 1)) (label_upd I x (length p))"
  by(auto simp: paired_marks_def Labels.fixed_univ_map_upd nth_append split: if_splits)

lemma paired_marks_append_right:
  "\<lbrakk>paired_marks tag p q A I; label_invar A; label_invar I; x \<in> K;
     x \<notin> set p; x \<notin> set q\<rbrakk> \<Longrightarrow>
   paired_marks tag p (q @ [x]) (label_upd A x (2 * tag + 2)) (label_upd I x (length q))"
  by(auto simp: paired_marks_def Labels.fixed_univ_map_upd nth_append split: if_splits)
definition "paired_marks_assn tag p q mi ii =
  (\<exists>\<^sub>AA I. label_assn A mi * label_assn I ii *
    \<up>(label_invar A \<and> label_invar I \<and> paired_marks tag p q A I))"

lemma paired_mark_lookup_rule:
  "x \<in> K \<Longrightarrow>
   <paired_marks_assn tag p q mi ii> label_get_imp mi x
   <\<lambda>c. paired_marks_assn tag p q mi ii *
     \<up>((c = 2 * tag + 1 \<longleftrightarrow> x \<in> set p) \<and>
         (c = 2 * tag + 2 \<longleftrightarrow> x \<in> set q))>"
  unfolding paired_marks_assn_def
  by(sep_auto dest: paired_marks_lookup)

lemma paired_position_left_rule:
  "\<lbrakk>x \<in> K; x \<in> set p\<rbrakk> \<Longrightarrow>
   <paired_marks_assn tag p q mi ii> label_get_imp ii x
   <\<lambda>i. paired_marks_assn tag p q mi ii * \<up>(i < length p \<and> p ! i = x)>"
  unfolding paired_marks_assn_def
  by(sep_auto dest: paired_marks_left)

lemma paired_position_right_rule:
  "\<lbrakk>x \<in> K; x \<in> set q\<rbrakk> \<Longrightarrow>
   <paired_marks_assn tag p q mi ii> label_get_imp ii x
   <\<lambda>i. paired_marks_assn tag p q mi ii * \<up>(i < length q \<and> q ! i = x)>"
  unfolding paired_marks_assn_def
  by(sep_auto dest: paired_marks_right)

definition "paired_mark_imp mi ii x code pos = do {
  label_upd_imp mi x code; label_upd_imp ii x pos }"

lemma paired_mark_left_rule:
  "\<lbrakk>x \<in> K; x \<notin> set p; x \<notin> set q\<rbrakk> \<Longrightarrow>
   <paired_marks_assn tag p q mi ii> paired_mark_imp mi ii x (2 * tag + 1) (length p)
   <\<lambda>_. paired_marks_assn tag (p @ [x]) q mi ii>"
  unfolding paired_marks_assn_def paired_mark_imp_def
  by(sep_auto simp: Labels.fixed_univ_map_upd_invar intro: paired_marks_append_left[simplified])

lemma paired_mark_right_rule:
  "\<lbrakk>x \<in> K; x \<notin> set p; x \<notin> set q\<rbrakk> \<Longrightarrow>
   <paired_marks_assn tag p q mi ii> paired_mark_imp mi ii x (2 * tag + 2) (length q)
   <\<lambda>_. paired_marks_assn tag p (q @ [x]) mi ii>"
  unfolding paired_marks_assn_def paired_mark_imp_def
  by(sep_auto simp: Labels.fixed_univ_map_upd_invar intro: paired_marks_append_right[simplified])

lemma paired_marks_fresh:
  "paired_marks tag p q A I \<Longrightarrow> paired_marks (Suc tag) [] [] A I"
  by(simp only: paired_marks_def[of "Suc tag" "[]" "[]" A I];
    auto intro: paired_marks_bound[simplified])

lemma paired_marks_reuse:
  "paired_marks_assn tag p q mi ii \<Longrightarrow>\<^sub>A paired_marks_assn (Suc tag) [] [] mi ii"
  unfolding paired_marks_assn_def
  by(sep_auto intro: paired_marks_fresh)

definition "path_buffer_assn p cap Ra =
  (\<exists>\<^sub>Axs. Ra \<mapsto>\<^sub>a xs * \<up>(take (length p) xs = p \<and> length xs = cap))"

lemma path_buffer_append_rule:
  "length p < cap \<Longrightarrow>
   <path_buffer_assn p cap Ra> Array.upd (length p) x Ra
   <\<lambda>_. path_buffer_assn (p @ [x]) cap Ra>"
  unfolding path_buffer_assn_def
  by(sep_auto simp: take_Suc_conv_app_nth)

lemma path_buffer_prefix:
  assumes "n \<le> length p"
  shows "path_buffer_assn p cap Ra \<Longrightarrow>\<^sub>A path_buffer_assn (take n p) cap Ra"
  using assms
  unfolding path_buffer_assn_def
  by(sep_auto simp: min_absorb1 min_absorb2 dest: arg_cong[where f="take n"])

definition "paired_hit_left_imp ii x plen = do {
  i \<leftarrow> label_get_imp ii x; return (True, Suc plen, Suc i) }"

definition "paired_hit_right_imp ii y qlen = do {
  i \<leftarrow> label_get_imp ii y; return (True, Suc i, Suc qlen) }"

definition "paired_advance_imp pai mi ii x code pos = do {
  paired_mark_imp mi ii x code pos; parent_get_imp pai x }"

lemma paired_advance_left_rule:
  "\<lbrakk>parent_invar P; x \<in> K; x \<notin> set p; x \<notin> set q\<rbrakk> \<Longrightarrow>
   <parent_assn P pai * paired_marks_assn tag p q mi ii>
   paired_advance_imp pai mi ii x (2 * tag + 1) (length p)
   <\<lambda>next. parent_assn P pai * paired_marks_assn tag (p @ [x]) q mi ii *
     \<up>(next = parent_get P x)>"
  unfolding paired_advance_imp_def
  by(sep_auto heap: paired_mark_left_rule[simplified])

lemma paired_advance_right_rule:
  "\<lbrakk>parent_invar P; x \<in> K; x \<notin> set p; x \<notin> set q\<rbrakk> \<Longrightarrow>
   <parent_assn P pai * paired_marks_assn tag p q mi ii>
   paired_advance_imp pai mi ii x (2 * tag + 2) (length q)
   <\<lambda>next. parent_assn P pai * paired_marks_assn tag p (q @ [x]) mi ii *
     \<up>(next = parent_get P x)>"
  unfolding paired_advance_imp_def
  by(sep_auto heap: paired_mark_right_rule[simplified])
definition "paired_prefixes_result xs ys shared p q =
  (if shared then p \<noteq> [] \<and> q \<noteq> [] \<and> last p = last q \<and>
     set (butlast p) \<inter> set (butlast q) = {} \<and>
     (\<exists>r. xs = p @ r \<and> ys = q @ r)
   else p = xs \<and> q = ys \<and> set xs \<inter> set ys = {})"

lemma paired_prefixes_result_sym:
  "paired_prefixes_result xs ys shared p q \<longleftrightarrow> paired_prefixes_result ys xs shared q p"
  by(auto simp: paired_prefixes_result_def)

lemma paired_prefixes_hit:
  assumes "parent (parent_lookup P)" "rootward P v = p @ rootward P x"
    "rootward P w = q @ rootward P y" "set p \<inter> set q = {}"
    "x \<noteq> nil" "i < length q" "q ! i = x"
  shows "paired_prefixes_result (rootward P v) (rootward P w) True (p @ [x]) (take (Suc i) q)"
proof-
  have split: "q = take i q @ [x] @ drop (Suc i) q"
    using id_take_nth_drop[OF assms(6)] assms(7)
    by simp
  have suffix: "rootward P x = x # (drop (Suc i) q @ rootward P y)"
    by(rule rootward_suffix[OF assms(1) _ assms(5), where v=w and pre="take i q"];
      subst assms(3); subst split; simp)
  have remainder: "rootward P w = take (Suc i) q @ (drop (Suc i) q @ rootward P y)"
    by(simp add: assms(3) append.assoc[symmetric])
  show ?thesis
    using assms(2,4,6,7) set_take_subset[of i q] remainder
    unfolding paired_prefixes_result_def
    by(auto simp: take_Suc_conv_app_nth suffix
      intro!: exI[of _ "drop (Suc i) q @ rootward P y"])

qed

partial_function (heap) paired_ascent_imp where
  "paired_ascent_imp pai mi ii Pa Qa plen qlen x y turn tag =
   (if x = nil \<and> y = nil then return (False, plen, qlen)
    else if (turn \<and> x \<noteq> nil) \<or> y = nil then do {
      code \<leftarrow> label_get_imp mi x;
      Array.upd plen x Pa;
      if code = 2 * tag + 2 then paired_hit_left_imp ii x plen
      else do {
        next \<leftarrow> paired_advance_imp pai mi ii x (2 * tag + 1) plen;
        paired_ascent_imp pai mi ii Pa Qa (Suc plen) qlen next y False tag } }
    else do {
      code \<leftarrow> label_get_imp mi y;
      Array.upd qlen y Qa;
      if code = 2 * tag + 1 then paired_hit_right_imp ii y qlen
      else do {
        next \<leftarrow> paired_advance_imp pai mi ii y (2 * tag + 2) qlen;
        paired_ascent_imp pai mi ii Pa Qa plen (Suc qlen) x next True tag } })"

definition "paired_ascent_post P v w tag pcap qcap pai mi ii Pa Qa result =
  (case result of (shared, plen, qlen) \<Rightarrow>
    (\<exists>\<^sub>Ap q. parent_assn P pai * paired_marks_assn (Suc tag) [] [] mi ii *
      path_buffer_assn p pcap Pa * path_buffer_assn q qcap Qa *
      \<up>(plen \<le> length p \<and> qlen \<le> length q \<and>
        paired_prefixes_result (rootward P v) (rootward P w) shared (take plen p) (take qlen q))))"
lemma paired_ascent_rule:
  assumes "parent_invar P" "parent (parent_lookup P)"
    "set (rootward P v) \<subseteq> K" "set (rootward P w) \<subseteq> K"
    "length (rootward P v) \<le> pcap" "length (rootward P w) \<le> qcap"
  shows "\<lbrakk>rootward P v = p @ rootward P x; rootward P w = q @ rootward P y;
      set p \<inter> set q = {}\<rbrakk> \<Longrightarrow>
    <parent_assn P pai * paired_marks_assn tag p q mi ii *
      path_buffer_assn p pcap Pa * path_buffer_assn q qcap Qa>
    paired_ascent_imp pai mi ii Pa Qa (length p) (length q) x y turn tag
    <paired_ascent_post P v w tag pcap qcap pai mi ii Pa Qa>"
proof(induction "length (rootward P x) + length (rootward P y)" arbitrary: x y p q turn rule: less_induct)
  case IH: (less x y p q turn)
  have left_props: "x \<in> K" "x \<notin> set p" "length p < pcap" if "x \<noteq> nil"
    using assms(3,5) IH(2) rootward_distinct[OF assms(2), of v] rootward_step[OF assms(2) that]
    by auto
  have right_props: "y \<in> K" "y \<notin> set q" "length q < qcap" if "y \<noteq> nil"
    using assms(4,6) IH(3) rootward_distinct[OF assms(2), of w] rootward_step[OF assms(2) that]
    by auto
  have next_left:
    "<parent_assn P pai * paired_marks_assn tag (p @ [x]) q mi ii *
      path_buffer_assn (p @ [x]) pcap Pa * path_buffer_assn q qcap Qa>
      paired_ascent_imp pai mi ii Pa Qa (Suc (length p)) (length q) nx ny False tag
      <paired_ascent_post P v w tag pcap qcap pai mi ii Pa Qa>"
    if "x \<noteq> nil" "x \<notin> set q" "nx = parent_get P x" "ny = y" for nx ny
    using IH(1)[of "parent_get P x" y "p @ [x]" q False] IH(2-4)
      rootward_step[OF assms(2) that(1)] that(2-4)
    by auto
  have next_right:
    "<parent_assn P pai * paired_marks_assn tag p (q @ [y]) mi ii *
      path_buffer_assn p pcap Pa * path_buffer_assn (q @ [y]) qcap Qa>
      paired_ascent_imp pai mi ii Pa Qa (length p) (Suc (length q)) nx ny True tag
      <paired_ascent_post P v w tag pcap qcap pai mi ii Pa Qa>"
    if "y \<noteq> nil" "y \<notin> set p" "nx = x" "ny = parent_get P y" for nx ny
    using IH(1)[of x "parent_get P y" p "q @ [y]" True] IH(2-4)
      rootward_step[OF assms(2) that(1)] that(2-4)
    by auto
  have finished:
    "<parent_assn P pai * paired_marks_assn tag p q mi ii *
      path_buffer_assn p pcap Pa * path_buffer_assn q qcap Qa>
      return (False, length p, length q) <paired_ascent_post P v w tag pcap qcap pai mi ii Pa Qa>"
    if "x = nil" "y = nil"
    using IH(2-4) that
    unfolding paired_ascent_post_def paired_marks_assn_def
    by(sep_auto simp: rootward_def paired_prefixes_result_def intro: paired_marks_fresh)
  have hit_left:
    "<parent_assn P pai * paired_marks_assn tag p q mi ii *
      path_buffer_assn (p @ [x]) pcap Pa * path_buffer_assn q qcap Qa>
      paired_hit_left_imp ii x (length p)
      <paired_ascent_post P v w tag pcap qcap pai mi ii Pa Qa>"
    if "x \<noteq> nil" "x \<in> set q"
    using left_props(1)[OF that(1)] that(2)
    unfolding paired_ascent_post_def paired_marks_assn_def paired_hit_left_imp_def paired_hit_right_imp_def
    by(sep_auto dest: paired_marks_right
      intro: paired_marks_fresh paired_prefixes_hit[OF assms(2) IH(2-4) that(1)])
  have hit_right:
    "<parent_assn P pai * paired_marks_assn tag p q mi ii *
      path_buffer_assn p pcap Pa * path_buffer_assn (q @ [y]) qcap Qa>
      paired_hit_right_imp ii y (length q)
      <paired_ascent_post P v w tag pcap qcap pai mi ii Pa Qa>"
    if "y \<noteq> nil" "y \<in> set p"
    using right_props(1)[OF that(1)] that(2) IH(4)
    unfolding paired_ascent_post_def paired_marks_assn_def paired_hit_left_imp_def paired_hit_right_imp_def
    by(sep_auto dest: paired_marks_left intro: paired_marks_fresh
      paired_prefixes_hit[OF assms(2) IH(3,2) _ that(1), THEN paired_prefixes_result_sym[THEN iffD1]])
  show ?case
    using assms(1) left_props right_props
    by(cases "x = nil"; cases "y = nil"; cases turn;
      subst paired_ascent_imp.simps; simp only: if_True if_False simp_thms;
      (simp only: finished)?;
      sep_auto heap: hit_left hit_right next_left next_right paired_mark_lookup_rule
        paired_advance_left_rule[simplified] paired_advance_right_rule[simplified]
        path_buffer_append_rule par.fixed_univ_map_lookup_rule; auto)
qed

lemma parent_lookup_cong:
  "parent_get P = parent_get Q \<Longrightarrow> parent_lookup P = parent_lookup Q"
  by(auto simp: parent_lookup_def fun_eq_iff)
lemma forest_parent_view_wf:
  assumes "forest_invar M F" "parent_get P = parent_get (parents F)"
  shows "parent (parent_lookup P)"
  using assms follow_dom_invar_parent_wf(1)[of F] forest_invarD(4)[of M F]
    parent_lookup_cong[of P "parents F"]
  by auto

lemma rootward_forest_view:
  assumes "forest_invar M F" "v \<in> vset_to_set (evens F)"
    "parent_get P = parent_get (parents F)"
  shows "rootward P v = get_path F v"
  using assms nil parent_lookup_cong[of P "parents F"]
  by(auto simp: rootward_def get_path_eq_follow
    dest: forest_invarD(1) invar_basicD(2) vset.fixed_univ_set_universe)

lemma forest_path_in_universe:
  "\<lbrakk>forest_invar M F; v \<in> vset_to_set (evens F)\<rbrakk> \<Longrightarrow> set (get_path F v) \<subseteq> K"
  using path_follow_verts_in_verts_F[of M F v] forest_vertices_in_universe[of M F]
    invar_basicD(6)[of M F]
  by(auto simp: get_path_eq_follow dest: forest_invarD; blast)

definition "paths_into Ci mi ii Pa Qa v w tag = (case Ci of (li, pai, bi) \<Rightarrow>
  paired_ascent_imp pai mi ii Pa Qa 0 0 v w True tag)"

definition "forest_paths_post F Ci v w tag pcap qcap mi ii Pa Qa result =
  (case result of (shared, plen, qlen) \<Rightarrow>
    (\<exists>\<^sub>Ap q. contractable_forest_assn F Ci * paired_marks_assn (Suc tag) [] [] mi ii *
      path_buffer_assn p pcap Pa * path_buffer_assn q qcap Qa *
      \<up>(plen \<le> length p \<and> qlen \<le> length q \<and>
        paired_prefixes_result (get_path F v) (get_path F w) shared (take plen p) (take qlen q))))"
lemma paths_into_rule:
  assumes "forest_invar M F" "v \<in> vset_to_set (evens F)" "w \<in> vset_to_set (evens F)"
    "length (get_path F v) \<le> pcap" "length (get_path F w) \<le> qcap"
  shows "<contractable_forest_assn F Ci * paired_marks_assn tag [] [] mi ii *
      path_buffer_assn [] pcap Pa * path_buffer_assn [] qcap Qa>
    paths_into Ci mi ii Pa Qa v w tag
    <forest_paths_post F Ci v w tag pcap qcap mi ii Pa Qa>"
  using assms forest_path_in_universe[OF assms(1,2)] forest_path_in_universe[OF assms(1,3)]
  unfolding paths_into_def forest_paths_post_def contractable_forest_assn_def
    forest_storage_assn_def indexed_parents_assn_def
  by(sep_auto split: prod.splits
    heap: paired_ascent_rule[where p="[]" and q="[]" and x=v and y=w and v=v and w=w
      and turn=True, simplified, unfolded paired_ascent_post_def]
    simp: rootward_forest_view[OF assms(1,2)] rootward_forest_view[OF assms(1,3)]
    intro: forest_parent_view_wf[OF assms(1)])

definition "paired_workspace_new = do {
  mi \<leftarrow> label_empty_imp; ii \<leftarrow> label_empty_imp; return (mi, ii) }"

definition "paired_workspace_clear mi ii = label_clear_imp mi"

lemma paired_workspace_new_rule:
  "<emp> paired_workspace_new <\<lambda>(mi, ii). paired_marks_assn tag [] [] mi ii>"
  unfolding paired_workspace_new_def paired_marks_assn_def paired_marks_def
  by(sep_auto simp: label_empty)

lemma paired_workspace_clear_rule:
  "<paired_marks_assn old p q mi ii> paired_workspace_clear mi ii
   <\<lambda>_. paired_marks_assn tag [] [] mi ii>"
  unfolding paired_workspace_clear_def paired_marks_assn_def paired_marks_def
  by(sep_auto simp: label_empty)
definition "forest_paths_array_post F Ci v w tag pcap qcap mi ii Pa Qa result =
  (case result of (shared, plen, qlen) \<Rightarrow>
    (\<exists>\<^sub>Axs ys. contractable_forest_assn F Ci * paired_marks_assn (Suc tag) [] [] mi ii *
      Pa \<mapsto>\<^sub>a xs * Qa \<mapsto>\<^sub>a ys *
      \<up>(length xs = pcap \<and> length ys = qcap \<and> plen \<le> pcap \<and> qlen \<le> qcap \<and>
        paired_prefixes_result (get_path F v) (get_path F w) shared (take plen xs) (take qlen ys))))"
lemma forest_paths_array_postI:
  "forest_paths_post F Ci v w tag pcap qcap mi ii Pa Qa r \<Longrightarrow>\<^sub>A
   forest_paths_array_post F Ci v w tag pcap qcap mi ii Pa Qa r"
proof(cases r)
  case fields: (fields shared plen qlen)
  have prefix: "n \<le> length xs" "take n xs = take n p"
    if "take (length p) xs = p" "n \<le> length p" for n and xs p :: "'v list"
    using arg_cong[OF that(1), of length] arg_cong[OF that(1), of "take n"] that(2)
    by(auto simp: min_absorb1[OF that(2)] min_def split: if_splits)
  show ?thesis
    unfolding fields forest_paths_post_def forest_paths_array_post_def path_buffer_assn_def prod.case ex_assn_move_out
  proof(intro ent_ex_preI, goal_cases)
    case (1 p q ys xs)
show ?case
      by(sep_auto simp: prefix(2)[of p xs plen] prefix(2)[of q ys qlen]
        intro: prefix(1)[of p xs plen] prefix(1)[of q ys qlen])
  qed
qed

lemma paths_into_array_rule:
  assumes "forest_invar M F" "v \<in> vset_to_set (evens F)" "w \<in> vset_to_set (evens F)"
    "length (get_path F v) \<le> length xs" "length (get_path F w) \<le> length ys"
  shows "<contractable_forest_assn F Ci * paired_marks_assn tag [] [] mi ii *
      Pa \<mapsto>\<^sub>a xs * Qa \<mapsto>\<^sub>a ys>
    paths_into Ci mi ii Pa Qa v w tag
    <forest_paths_array_post F Ci v w tag (length xs) (length ys) mi ii Pa Qa>"
proof-
  have "<contractable_forest_assn F Ci * paired_marks_assn tag [] [] mi ii *
      Pa \<mapsto>\<^sub>a xs * Qa \<mapsto>\<^sub>a ys>
    paths_into Ci mi ii Pa Qa v w tag
    <forest_paths_post F Ci v w tag (length xs) (length ys) mi ii Pa Qa>"
    by(rule ht_cons_pre[OF _ paths_into_rule[OF assms]]) (sep_auto simp: path_buffer_assn_def)
  then show ?thesis
    by(rule ht_cons_post) (rule ent_true_drop(2)[OF forest_paths_array_postI])
qed

end

lemma ht_observe_frame:
  assumes "<P> c <\<lambda>x. P * \<up>(S x)>"
  shows "<P * R> c <\<lambda>x. P * R * \<up>(S x)>"
  using ht_frame[OF assms, where R=R]
  by(rule ht_cons_post) (sep_auto)

context Alternating_Forest_Contraction_Imperative
begin

definition "contractable_clear_into Ci = (case Ci of (li,pai,bi) \<Rightarrow> do {
  label_clear_imp li; parent_clear_imp pai; children_clear_imp bi })"

definition "contractable_add_root_into v Ci =
  (case Ci of (li,pai,bi) \<Rightarrow> label_upd_imp li v 2)"

definition "contractable_extend_into x y z Ci = (case Ci of (li,pai,bi) \<Rightarrow> do {
  label_upd_imp li y 1; label_upd_imp li z 2;
  parent_upd_imp pai y x; parent_upd_imp pai z y; children_insert_imp bi y x })"

lemma contractable_clear_into_rule:
  assumes "vset_invar R" "vset_to_set R = {}"
  shows "<contractable_forest_assn F Ci> contractable_clear_into Ci
    <\<lambda>_. contractable_forest_assn (empty_forest R) Ci>"
  using assms
  unfolding contractable_clear_into_def contractable_forest_assn_def forest_storage_assn_def
    forest_labels_assn_def indexed_parents_assn_def empty_forest_def
  by(sep_auto split: prod.splits simp: label_empty empties Children.buckets_empty vset.fixed_univ_set_empty)

lemma contractable_add_root_into_rule:
  assumes "vset_invar R" "vset_invar R'" "vset_to_set R' = insert v (vset_to_set R)"
  shows "<contractable_forest_assn (empty_forest R) Ci> contractable_add_root_into v Ci
    <\<lambda>_. contractable_forest_assn (empty_forest R') Ci>"
  using assms
  unfolding contractable_add_root_into_def contractable_forest_assn_def forest_storage_assn_def
    forest_labels_assn_def indexed_parents_assn_def empty_forest_def
  by(sep_auto split: prod.splits simp: Labels.fixed_univ_map_upd_invar Labels.fixed_univ_map_upd
    vset.fixed_univ_set_empty dest: vset.fixed_univ_set_universe)

lemma contractable_extend_into_rule:
  assumes "forest_extension_precond F M x y z"
  shows "<contractable_forest_assn F Ci> contractable_extend_into x y z Ci
    <\<lambda>_. contractable_forest_assn (extend_forest_even_unclassified F x y z) Ci>"
proof-
  have bounds: "x \<in> K" "y \<in> K" "z \<in> K" "x \<noteq> nil" "y \<noteq> nil"
    "y \<notin> vset_to_set (evens F) \<union> vset_to_set (odds F)"
    "z \<notin> vset_to_set (evens F) \<union> vset_to_set (odds F)" "y \<noteq> z"
    "vset_invar (evens F)" "vset_invar (odds F)" "parent_invar (parents F)"
    using assms forest_extension_bounds[OF assms] nil
    by(auto elim!: forest_extension_precondE forest_invarE invar_basicE)
  show ?thesis
    using bounds
    unfolding contractable_extend_into_def contractable_forest_assn_def forest_storage_assn_def
      forest_labels_assn_def indexed_parents_assn_def extend_forest_even_unclassified_def
    by(sep_auto split: prod.splits simp: Labels.fixed_univ_map_upd_invar Labels.fixed_univ_map_upd
      Children.buckets_insert parent_lookup_def parent_map.fixed_univ_map_upd
      parent_map.fixed_univ_map_upd_invar vset.fixed_univ_set_insert)
qed

end

context Alternating_Forest_Contraction_Imperative
begin

lemma forest_storage_raw:
  "forest_storage_assn E Od P B (li,pai,bi) =
   (\<exists>\<^sub>AL Q C. label_assn L li * (parent_assn Q pai * children_assn C bi) *
    \<up>(label_invar L \<and> parent_invar Q \<and> children_invar C \<and>
      vset_invar E \<and> vset_invar Od \<and> vset_to_set E \<inter> vset_to_set Od = {} \<and>
      parent_get Q = P \<and> children_abstract C = B \<and>
      (\<forall>x\<in>K. label_get L x =
        (if x \<in> vset_to_set Od then 1 else if x \<in> vset_to_set E then 2 else 0))))"
  unfolding forest_storage_assn_def forest_labels_assn_def indexed_parents_assn_def
  by(rule ent_iffI; sep_auto)

lemma indexed_remove_rule:
  "B x = Some source \<Longrightarrow>
    <indexed_parents_assn P B pai bi> children_remove_imp bi x source
    <\<lambda>_. indexed_parents_assn P (fun_upd B x None) pai bi>"
  unfolding indexed_parents_assn_def
  by(sep_auto simp: Children.buckets_remove)

lemma indexed_insert_rule:
  "\<lbrakk>x \<in> K; target \<in> K; B x = None\<rbrakk> \<Longrightarrow>
    <indexed_parents_assn P B pai bi> children_insert_imp bi x target
    <\<lambda>_. indexed_parents_assn P (fun_upd B x (Some target)) pai bi>"
  unfolding indexed_parents_assn_def
  by(sep_auto simp: Children.buckets_insert)

lemma indexed_read_rule:
  "x \<in> K \<Longrightarrow>
    <indexed_parents_assn P B pai bi> parent_get_imp pai x
    <\<lambda>v. indexed_parents_assn P B pai bi * \<up>(v = P x)>"
  unfolding indexed_parents_assn_def
  by(sep_auto)

interpretation Forest: alternating_forest_fork_contraction_spec
  vset_invar vset_to_set evens odds get_path abstract_forest forest_invar roots K contract_fork
  by(rule spec_satisfied)

lemma contract_fork_first_invar:
  assumes "Forest.contract_fork_precond M F v w p q u target rest contr"
    "u \<in> vset_to_set (evens F)"
  shows "forest_invar (quot_graph (\<lambda>x. if x \<in> set (p @ [u]) then u else x) M - {{u}})
    (contract_path F (p @ [u]) u)"
proof-
  have pre: "forest_invar M F" "matching M" "dblton_graph M"
    "get_path F v = p @ [u] @ rest" "v \<in> vset_to_set (evens F)"
    using assms(1)
    by(auto simp: Forest.contract_fork_precond_def)
  have "u \<in> K"
    using forest_path_in_universe[OF pre(1,5)] pre(4)
    by auto
  with pre assms(2) show ?thesis
    by(intro contract_path_correct(1)[where rts="roots F" and evs="evens F" and ods="odds F"
        and prnts="parents F" and orngs="origins F" and v=v and u=u
        and new_vert=u and new_forest="contract_path F (p @ [u]) u", unfolded alt_forest.collapse];
      auto simp: get_path_eq_follow[OF pre(1)])
qed

end

end
