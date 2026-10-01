theory Alternating_Forest_Imperative
  imports Alternating_Forest_Imperative_Spec 
          Basic_Matching.Alternating_Forest_Executable
begin

section \<open>Imperative Implementation of Alternating Forests\<close>

text \<open>This is the imperative counterpart of @{locale forest_manipulation}. It is generic in the
      parent map, the origin map and the vertex sets, exactly as the functional module, and it
      uses the imperative sets and maps only through their interfaces.

      A forest is represented by the imperative sets of its even and its odd vertices and the
      imperative parent map. The roots and the origins are not stored; they are ghost components of
      the functional forest, which the representation does not mention.\<close>


locale forest_imp =
  forest_manipulation parent_empty parent_upd parent_delete parent_lookup parent_invar
     origin_empty origin_upd origin_delete origin_lookup origin_invar
     vset_empty vset_insert vset_delete vset_isin vset_to_set vset_invar vset_iterate +
  vs: imp_set_conn
    where s_empty = vset_empty and s_insert = vset_insert and s_delete = vset_delete
      and s_isin = vset_isin and s_set = vset_to_set and s_invar = vset_invar
      and is_set = is_set and memb_imp = memb_imp and ins_imp = ins_imp
      and clear_imp = set_clear_imp and lst = lst and is_it = is_it and it_init = it_init
      and it_has_next = it_has_next and it_next = it_next +
  vs_empty: imp_set_empty is_set set_empty_imp +
  par: imp_map_conn_clear
    where is_map = is_map and lookup_imp = lookup_imp and update_imp = update_imp
      and m_update = parent_upd and m_lookup = parent_lookup and m_invar = parent_invar
      and R = "\<lambda>_ vi v. vi = v" and clear_imp = map_clear_imp and m_empty = parent_empty +
  par_empty: imp_map_empty is_map map_empty_imp
  for parent_empty and parent_upd :: "'v::heap \<Rightarrow> 'v \<Rightarrow> 'parent \<Rightarrow> 'parent"
    and parent_delete parent_lookup parent_invar
    and origin_empty and origin_upd :: "'v \<Rightarrow> 'v \<Rightarrow> 'origin \<Rightarrow> 'origin"
    and origin_delete origin_lookup origin_invar
    and vset_empty and vset_insert :: "'v \<Rightarrow> 'vset \<Rightarrow> 'vset"
    and vset_delete vset_isin vset_to_set vset_invar vset_iterate
    and is_set :: "'v set \<Rightarrow> 's \<Rightarrow> assn" and memb_imp ins_imp set_clear_imp set_empty_imp
    and lst and is_it :: "'v set \<Rightarrow> 's \<Rightarrow> 'v list \<Rightarrow> 'it \<Rightarrow> assn"
    and it_init it_has_next it_next
    and is_map :: "('v \<rightharpoonup> 'v) \<Rightarrow> 'mi \<Rightarrow> assn" and lookup_imp update_imp map_clear_imp
    and map_empty_imp
begin

subsection \<open>Representation\<close>

definition "forest_assn F Fi = (case Fi of (ei, oi, pai) \<Rightarrow>
   vs.set_assn (evens F) ei * vs.set_assn (odds F) oi * par.map_assn (parents F) pai)"

definition "forest_is_it F Fi p xs it = (case Fi of (ei, oi, pai) \<Rightarrow>
   (case p of
      Evens \<Rightarrow> is_it (vset_to_set (evens F)) ei xs it * is_set (vset_to_set (odds F)) oi
    | Odds \<Rightarrow> is_set (vset_to_set (evens F)) ei * is_it (vset_to_set (odds F)) oi xs it) *
   par.map_assn (parents F) pai * \<up>(vset_invar (evens F) \<and> vset_invar (odds F)))"

subsection \<open>Programs\<close>

definition "forest_empty_imp =
  do { ei \<leftarrow> set_empty_imp; oi \<leftarrow> set_empty_imp; pai \<leftarrow> map_empty_imp; return (ei, oi, pai) }"

definition "forest_clear_imp Fi = (case Fi of (ei, oi, pai) \<Rightarrow>
  do { ei' \<leftarrow> set_clear_imp ei; oi' \<leftarrow> set_clear_imp oi; pai' \<leftarrow> map_clear_imp pai;
       return (ei', oi', pai') })"

definition "forest_add_root_imp v Fi = (case Fi of (ei, oi, pai) \<Rightarrow>
  do { ei' \<leftarrow> ins_imp v ei; return (ei', oi, pai) })"

definition "forest_extend_imp x y z Fi = (case Fi of (ei, oi, pai) \<Rightarrow>
  do { oi' \<leftarrow> ins_imp y oi;
       ei' \<leftarrow> ins_imp z ei;
       pai' \<leftarrow> update_imp y x pai;
       pai'' \<leftarrow> update_imp z y pai';
       return (ei', oi', pai'') })"

definition "evens_memb_imp v Fi = (case Fi of (ei, oi, pai) \<Rightarrow> memb_imp v ei)"

definition "odds_memb_imp v Fi = (case Fi of (ei, oi, pai) \<Rightarrow> memb_imp v oi)"

definition "forest_it_init p Fi = (case Fi of (ei, oi, pai) \<Rightarrow>
  (case p of Evens \<Rightarrow> it_init ei | Odds \<Rightarrow> it_init oi))"

partial_function (heap) get_path_loop :: "'mi \<Rightarrow> 'v array \<Rightarrow> nat \<Rightarrow> 'v \<Rightarrow> nat Heap" where
  "get_path_loop pai Ra k v = do {
     _ \<leftarrow> Array.upd k v Ra;
     r \<leftarrow> lookup_imp v pai;
     (case r of None \<Rightarrow> return (k + 1)
              | Some v' \<Rightarrow> get_path_loop pai Ra (k + 1) v') }"

definition "get_path_imp Fi Ra k v = (case Fi of (ei, oi, pai) \<Rightarrow> get_path_loop pai Ra k v)"

subsection \<open>Correctness\<close>

lemma empty_forest_parts[simp]:
  "evens (empty_forest R) = R" "odds (empty_forest R) = vset_empty"
  "parents (empty_forest R) = parent_empty"
  by (auto simp: empty_forest_def)

lemma extend_forest_parts[simp]:
  "evens (extend_forest_even_unclassified F x y z) = vset_insert z (evens F)"
  "odds (extend_forest_even_unclassified F x y z) = vset_insert y (odds F)"
  "parents (extend_forest_even_unclassified F x y z) = parent_upd z y (parent_upd y x (parents F))"
  by (auto simp: extend_forest_even_unclassified_def)

lemma set_assn_empty_set:
  "\<lbrakk>vset_invar R; vset_to_set R = {}\<rbrakk> \<Longrightarrow> vs.set_assn R Vi = is_set {} Vi"
  by (simp add: vs.set_assn_def)

lemma map_assn_empty:
  "par.map_assn parent_empty pai = (\<exists>\<^sub>Amm. is_map mm pai * \<up>(mm = Map.empty))"
  by (auto simp: par.map_assn_def par.m_invar_empty par.m_lookup_empty option.rel_eq fun_eq_iff
          intro!: ent_iffI)

lemma forest_empty_imp_rule:
  "\<lbrakk>vset_invar R; vset_to_set R = {}\<rbrakk> \<Longrightarrow>
   <emp> forest_empty_imp <forest_assn (empty_forest R)>"
  unfolding forest_empty_imp_def forest_assn_def
  by (sep_auto simp: set_assn_empty_set vs.set_assn_def vset.set_empty vset.invar_empty
                     map_assn_empty)

lemma forest_clear_imp_rule:
  "\<lbrakk>vset_invar R; vset_to_set R = {}\<rbrakk> \<Longrightarrow>
   <forest_assn F Fi> forest_clear_imp Fi <forest_assn (empty_forest R)>"
  unfolding forest_clear_imp_def forest_assn_def
  by (sep_auto split: prod.splits
               simp: set_assn_empty_set vs.set_assn_def vset.set_empty vset.invar_empty
                     map_assn_empty)

lemma forest_empty_cong:
  "\<lbrakk>vset_invar R; vset_invar R'; vset_to_set R = vset_to_set R'\<rbrakk> \<Longrightarrow>
   forest_assn (empty_forest R) = forest_assn (empty_forest R')"
  by (auto simp: forest_assn_def vs.set_assn_def fun_eq_iff)

lemma forest_add_root_imp_rule:
  "\<lbrakk>vset_invar R; vset_invar R'; vset_to_set R' = insert v (vset_to_set R)\<rbrakk> \<Longrightarrow>
   <forest_assn (empty_forest R) Fi> forest_add_root_imp v Fi <forest_assn (empty_forest R')>"
  unfolding forest_add_root_imp_def forest_assn_def
  by (sep_auto split: prod.splits simp: vs.set_assn_def)

lemma forest_extend_imp_rule:
  "<forest_assn F Fi> forest_extend_imp x y z Fi
   <forest_assn (extend_forest_even_unclassified F x y z)>"
  unfolding forest_extend_imp_def forest_assn_def
  by (sep_auto split: prod.splits)

lemma evens_memb_imp_rule:
  "<forest_assn F Fi> evens_memb_imp v Fi
   <\<lambda>r. forest_assn F Fi * \<up>(r \<longleftrightarrow> v \<in> vset_to_set (evens F))>"
  unfolding evens_memb_imp_def forest_assn_def
  by (sep_auto split: prod.splits simp: vs.set_assn_def vset.set_isin)

lemma odds_memb_imp_rule:
  "<forest_assn F Fi> odds_memb_imp v Fi
   <\<lambda>r. forest_assn F Fi * \<up>(r \<longleftrightarrow> v \<in> vset_to_set (odds F))>"
  unfolding odds_memb_imp_def forest_assn_def
  by (sep_auto split: prod.splits simp: vs.set_assn_def vset.set_isin)

lemma forest_it_init_rule:
  "<forest_assn F Fi> forest_it_init p Fi
   <forest_is_it F Fi p (lst (vset_to_set (case p of Evens \<Rightarrow> evens F | Odds \<Rightarrow> odds F)))>"
  unfolding forest_it_init_def forest_assn_def forest_is_it_def
  by (sep_auto split: prod.splits forest_part.splits simp: vs.set_assn_def)

lemma forest_it_next_rule:
  "<forest_is_it F Fi p (x # xs) it> it_next it
   <\<lambda>(y, it'). forest_is_it F Fi p xs it' * \<up>(y = x)>"
  unfolding forest_is_it_def
  by (sep_auto split: prod.splits forest_part.splits)

lemma forest_it_has_next_rule:
  "<forest_is_it F Fi p xs it> it_has_next it
   <\<lambda>r. forest_is_it F Fi p xs it * \<up>(r \<longleftrightarrow> xs \<noteq> [])>"
  unfolding forest_is_it_def
  by (sep_auto split: prod.splits forest_part.splits)

lemma forest_quit_iteration:
  "forest_is_it F Fi p xs it \<Longrightarrow>\<^sub>A forest_assn F Fi"
  unfolding forest_is_it_def forest_assn_def
  apply(rule entailsI)
  apply(cases p; clarsimp split: prod.splits simp: mod_pure_star_dist)
  by (sep_frame_fwd rule: vs.quit_iteration, sep_auto simp: vs.set_assn_def)+

lemma rel_option_eq_iff[simp]: "rel_option (\<lambda>x y. x = y) a b \<longleftrightarrow> a = b"
  by (simp add: option.rel_eq)

lemma par_lookup_rule[sep_heap_rules]:
  "<par.map_assn m mi> lookup_imp k mi <\<lambda>r. par.map_assn m mi * \<up>(r = parent_lookup m k)>"
  by (sep_auto heap: par.map_assn_lookup_rule)

lemma take_drop_list_update:
  "\<lbrakk>k < length xs; k < j\<rbrakk> \<Longrightarrow>
   take (Suc k) (xs[k := v]) @ ys @ drop j (xs[k := v]) = take k xs @ v # ys @ drop j xs"
  by (simp add: take_Suc_conv_app_nth list_update_append)

lemma get_path_loop_rule:
  assumes "parent_spec_i.follow_dom (parent_lookup P) v"
  shows "k + length (follow (parent_lookup P) v) \<le> length xs \<Longrightarrow>
    <par.map_assn P pai * Ra \<mapsto>\<^sub>a xs> get_path_loop pai Ra k v
    <\<lambda>k'. par.map_assn P pai * Ra \<mapsto>\<^sub>a (take k xs @ follow (parent_lookup P) v @ drop k' xs) *
          \<up>(k' = k + length (follow (parent_lookup P) v))>"
  using assms
proof(induction arbitrary: k xs rule: parent_spec_i.follow.pinduct)
  case (1 v)
  show ?case
  proof(cases "parent_lookup P v")
    case None
    hence fol: "follow (parent_lookup P) v = [v]"
      by (simp add: parent_spec_i.follow.psimps[OF 1(1)])
    show ?thesis
      using 1(3)
      apply(subst get_path_loop.simps)
      by (sep_auto simp: fol None upd_conv_take_nth_drop)
  next
    case (Some v')
    note pv = Some
    hence fol: "follow (parent_lookup P) v = v # follow (parent_lookup P) v'"
      by (simp add: parent_spec_i.follow.psimps[OF 1(1)])
    have len: "Suc k + length (follow (parent_lookup P) v') \<le> length (xs[k := v])"
      using 1(3) by (simp add: fol)
    note IH = 1(2)[OF pv len]
    show ?thesis
      using 1(3)
      apply(subst get_path_loop.simps)
      supply par.map_assn_lookup_rule[sep_heap_rules del]
      apply(sep_auto simp: pv fol heap: IH)
      by (sep_auto simp: fol take_Suc_conv_app_nth list_update_append)
  qed
qed

lemma get_path_imp_rule:
  "\<lbrakk>forest_invar M F; v \<in> vset_to_set (evens F); k + length (get_path F v) \<le> length xs\<rbrakk> \<Longrightarrow>
   <forest_assn F Fi * Ra \<mapsto>\<^sub>a xs> get_path_imp Fi Ra k v
   <\<lambda>k'. forest_assn F Fi * Ra \<mapsto>\<^sub>a (take k xs @ get_path F v @ drop k' xs) *
         \<up>(k' = k + length (get_path F v))>"
  using follow_dom_invar_parent_wf(2)[OF forest_invarD(4)]
  unfolding get_path_imp_def forest_assn_def get_path_def
  by (sep_auto split: prod.splits simp: parent_spec_i.follow_dom_impl_same
               heap: get_path_loop_rule)

subsection \<open>Interpretation of the Imperative Forest Specification\<close>

lemma alternating_forest_imp_spec:
  "alternating_forest_imp_spec vset_invar vset_to_set odds abstract_forest forest_invar
     roots vset_empty extend_forest_even_unclassified empty_forest get_path evens lst
     forest_assn forest_empty_imp forest_clear_imp forest_add_root_imp forest_extend_imp
     evens_memb_imp odds_memb_imp forest_is_it forest_it_init it_has_next it_next get_path_imp"
  by (intro alternating_forest_imp_spec.intro alternating_forest_imp_spec_axioms.intro
            satisified vs.set_order_axioms
            forest_empty_imp_rule forest_clear_imp_rule forest_empty_cong forest_add_root_imp_rule
            forest_extend_imp_rule evens_memb_imp_rule odds_memb_imp_rule forest_it_init_rule
            forest_it_next_rule forest_it_has_next_rule forest_quit_iteration get_path_imp_rule)

end

end
