theory Cubic_Blossom_Instantiation
  imports Data_Structures.UnionFind_Representative_Specs Data_Structures.Imp_Array_Fun
    Data_Structures.Imp_Array_Buckets Blossom_Executable.Alternating_Forest_Contraction_Imperative
    Blossom_Executable.Quadratic_Blossom_Search_Imperative Directed_Set_Graphs.CSR_Edge_Input
    Blossom_Executable.Blossom_Forest Blossom_Executable.Cubic_Blossom_Imperative
begin

provenance ai_human

section "Direct representatives with circular member lists"

fun quf_chain :: "(nat \<Rightarrow> nat) \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool" where
  "quf_chain f [] z = True"
| "quf_chain f (x # xs) z =
    (f x = (if xs = [] then z else hd xs) \<and> quf_chain f xs z)"

lemma quf_chain_cong:
  "(\<And>x. x \<in> set xs \<Longrightarrow> f x = g x) \<Longrightarrow>
    quf_chain f xs z = quf_chain g xs z"
  by(induction xs) auto

lemma quf_chain_append[simp]:
  "quf_chain f (xs @ ys) z =
    (quf_chain f xs (if ys = [] then z else hd ys) \<and> quf_chain f ys z)"
  by(induction xs) (auto split: list.splits)

lemma quf_chain_splice:
  assumes "distinct (a # xs)" "distinct (b # ys)" "set (a # xs) \<inter> set (b # ys) = {}"
    "quf_chain f (a # xs) a" "quf_chain f (b # ys) b"
  shows "quf_chain (fun_upd (fun_upd f a (f b)) b (f a)) (a # ys @ b # xs) a"
proof-
  have "quf_chain (fun_upd (fun_upd f a (f b)) b (f a)) xs a = quf_chain f xs a"
    "quf_chain (fun_upd (fun_upd f a (f b)) b (f a)) ys b = quf_chain f ys b"
    using assms
    by(intro quf_chain_cong; auto)+
  with assms show ?thesis
    by(auto split: list.splits)
qed

record 'map Quadratic_Union_Find_state =
  quf_representatives :: 'map
  quf_next :: 'map
  quf_size :: 'map

locale Quadratic_Union_Find =
  Map: fixed_univ_map "{..<N}" map_invar map_update map_lookup
  for N :: nat
    and map_invar :: "'map \<Rightarrow> bool"
    and map_update :: "'map \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'map"
    and map_lookup :: "'map \<Rightarrow> nat \<Rightarrow> nat"
begin

declare Map.fixed_univ_map_upd[simp] Map.fixed_univ_map_upd_invar[intro]

definition "maps_invar U \<longleftrightarrow>
  map_invar (quf_representatives U) \<and> map_invar (quf_next U) \<and> map_invar (quf_size U)"

definition "representative U = map_lookup (quf_representatives U)"

definition "component U r xs \<longleftrightarrow>
  distinct (r # xs) \<and> set (r # xs) = {x. x < N \<and> representative U x = r} \<and>
  quf_chain (map_lookup (quf_next U)) (r # xs) r \<and>
  map_lookup (quf_size U) r = Suc (length xs)"

definition "invar U \<longleftrightarrow> maps_invar U \<and>
  (\<forall>x<N. representative U x < N \<and> representative U (representative U x) = representative U x) \<and>
  (\<forall>r<N. representative U r = r \<longrightarrow> (\<exists>xs. component U r xs))"

definition "find_rep U x = (representative U x, U)"

definition "relabel_step links target state =
  (case state of (R,x) \<Rightarrow> (map_update R x target, map_lookup links x))"

definition "relabel U source target =
  fst ((relabel_step (quf_next U) target ^^ map_lookup (quf_size U) source)
    (quf_representatives U, source))"

definition "merge_rep U source target = U \<lparr>
  quf_representatives := relabel U source target,
  quf_next := map_update (map_update (quf_next U) source (map_lookup (quf_next U) target))
    target (map_lookup (quf_next U) source),
  quf_size := map_update (quf_size U) target
    (map_lookup (quf_size U) source + map_lookup (quf_size U) target)\<rparr>"

definition "union_rep U x y =
  (let a = representative U x; b = representative U y in
    if a = b then U else if map_lookup (quf_size U) a \<le> map_lookup (quf_size U) b
    then merge_rep U a b else merge_rep U b a)"

definition "reset_step U x = U \<lparr>
  quf_representatives := map_update (quf_representatives U) x x,
  quf_next := map_update (quf_next U) x x,
  quf_size := map_update (quf_size U) x 1\<rparr>"

definition "reset_rep U = foldl reset_step U [0..<N]"

lemma update_fold:
  assumes "map_invar R" "set xs \<subseteq> {..<N}"
  shows "map_invar (foldl (\<lambda>R x. map_update R x target) R xs)"
    "map_lookup (foldl (\<lambda>R x. map_update R x target) R xs) =
      (\<lambda>x. if x \<in> set xs then target else map_lookup R x)"
  using assms
  by(induction xs arbitrary: R) (auto simp: Map.fixed_univ_map_upd_invar fun_eq_iff)

lemma relabel_chain:
  "quf_chain (map_lookup links) xs z \<Longrightarrow>
    (relabel_step links target ^^ length xs) (R, if xs = [] then z else hd xs) =
      (foldl (\<lambda>R x. map_update R x target) R xs, z)"
  by(induction xs arbitrary: R)
    (auto simp: funpow_Suc_right relabel_step_def simp del: funpow.simps(2))

lemma component_props:
  assumes "component U a xs"
  shows "distinct (a # xs)" "set (a # xs) = {x. x < N \<and> representative U x = a}" "quf_chain (map_lookup
    (quf_next U)) (a # xs) a" "map_lookup (quf_size U) a = Suc (length xs)"
  using assms
  by(auto simp only: component_def)

lemma relabel_component_fold:
  assumes "component U a xs"
  shows "relabel U a b = foldl (\<lambda>R x. map_update R x b) (quf_representatives U) (a # xs)"
  using relabel_chain[OF component_props(3)[OF assms], of b "quf_representatives U"]
  unfolding relabel_def
  by(simp only: component_props(4)[OF assms] length_Cons list.distinct if_False list.sel fst_conv)

lemma relabel_component:
  assumes "maps_invar U" "component U a xs"
  shows "map_invar (relabel U a b)" "map_lookup (relabel U a b) = (\<lambda>x. if x < N \<and> representative
    U x = a then b else representative U x)"
proof-
  have "map_invar (quf_representatives U)" "set (a # xs) \<subseteq> {..<N}"
    using assms
    by(auto simp: maps_invar_def component_def)
  from update_fold[OF this, of b]
  show "map_invar (relabel U a b)" "map_lookup (relabel U a b) = (\<lambda>x. if x < N \<and> representative U
    x = a then b else representative U x)"
    by(simp_all only: relabel_component_fold[OF assms(2)] component_props(2)[OF assms(2)] mem_Collect_eq
      representative_def)
qed

lemma component_keys:
  assumes "component U a xs"
  shows "a < N" "representative U a = a" "set (a # xs) \<subseteq> {..<N}"
  using assms
  by(auto simp: component_def)

lemma merge_effects:
  assumes "maps_invar U" "component U a xs" "component U b ys"
  shows "maps_invar (merge_rep U a b)" "representative (merge_rep U a b) = (\<lambda>x. if x < N \<and>
    representative U x = a then b else representative U x)" "map_lookup (quf_next (merge_rep U a b)) = fun_upd
    (fun_upd (map_lookup (quf_next U)) a (map_lookup (quf_next U) b)) b (map_lookup (quf_next U) a)"
    "map_lookup (quf_size (merge_rep U a b)) = fun_upd (map_lookup (quf_size U)) b (map_lookup (quf_size U) a
    + map_lookup (quf_size U) b)"
  using assms relabel_component[OF assms(1,2), of b] component_keys[OF assms(2)] component_keys[OF assms(3)]
  by(auto simp: merge_rep_def maps_invar_def representative_def Map.fixed_univ_map_upd_invar)

lemma component_intro: "\<lbrakk>distinct (a # xs); set (a # xs) = {x. x < N \<and> representative U x = a};
  quf_chain (map_lookup (quf_next U)) (a # xs) a; map_lookup (quf_size U) a = Suc (length xs)\<rbrakk>
  \<Longrightarrow> component U a xs"
  by(simp only: component_def)

lemma merge_target_component:
  assumes "maps_invar U" "component U a xs" "component U b ys" "a \<noteq> b"
  shows "component (merge_rep U a b) b (xs @ a # ys)"
proof-
  have "quf_chain (fun_upd (fun_upd (map_lookup (quf_next U)) b (map_lookup (quf_next U) a)) a
      (map_lookup (quf_next U) b)) (b # xs @ a # ys) b"
    using assms
    by(intro quf_chain_splice; auto simp: component_def)
  hence "quf_chain (map_lookup (quf_next (merge_rep U a b))) (b # xs @ a # ys) b"
    by(simp only: merge_effects(3)[OF assms(1-3)] fun_upd_twist[OF assms(4)])
  moreover have "set (a # xs) \<inter> set (b # ys) = {}"
    using assms(2-4)
    by(auto simp: component_def)
  hence "distinct (b # xs @ a # ys)"
    using component_props(1)[OF assms(2)] component_props(1)[OF assms(3)]
    by auto
  moreover have "set (b # xs @ a # ys) = {x. x < N \<and> representative (merge_rep U a b) x = b}"
    using component_props(2)[OF assms(2)] component_props(2)[OF assms(3)]
      merge_effects(2)[OF assms(1-3)] assms(4)
    by auto
  moreover have "map_lookup (quf_size (merge_rep U a b)) b = Suc (length (xs @ a # ys))"
    using merge_effects(4)[OF assms(1-3)] component_props(4)[OF assms(2)] component_props(4)[OF assms(3)]
    by simp
  ultimately show ?thesis
    by(simp only: component_def)
qed

lemma merge_other_component:
  assumes "maps_invar U" "component U a xs" "component U b ys" "component U c zs" "c \<noteq> a" "c \<noteq>
    b"
  shows "component (merge_rep U a b) c zs"
proof-
  have "quf_chain (map_lookup (quf_next (merge_rep U a b))) (c # zs) c = quf_chain (map_lookup (quf_next U))
    (c # zs) c"
    using merge_effects(3)[OF assms(1-3)] component_props(2)[OF assms(4)] component_keys(2)[OF assms(2)]
      component_keys(2)[OF assms(3)] assms(5,6)
    by(intro quf_chain_cong) auto
  hence "quf_chain (map_lookup (quf_next (merge_rep U a b))) (c # zs) c"
    using component_props(3)[OF assms(4)]
    by blast
  moreover have "set (c # zs) = {x. x < N \<and> representative (merge_rep U a b) x = c}"
    using component_props(2)[OF assms(4)] merge_effects(2)[OF assms(1-3)] assms(5,6)
    by auto
  ultimately show ?thesis
    using component_props(1,4)[OF assms(4)] merge_effects(4)[OF assms(1-3)] assms(6)
    by(intro component_intro) auto
qed

lemma merge_invar: "\<lbrakk>invar U; component U a xs; component U b ys; a \<noteq> b\<rbrakk>
  \<Longrightarrow> invar (merge_rep U a b)"
  using merge_effects[of U a xs b ys] merge_target_component[of U a xs b ys] merge_other_component[of U a xs b
    ys] component_keys[of U a xs] component_keys[of U b ys]
proof(auto simp: invar_def split: if_splits, goal_cases)
  case (1 r)
  then
  show ?case
  proof(cases "r = b")
    case True
    with 1
    show ?thesis
      by auto
    next
    case False
    with 1
    obtain zs where "component U r zs"
      by auto
    with 1 False
    show ?thesis
      by auto
  qed
qed

lemma reset_fold:
  assumes "maps_invar U" "set xs \<subseteq> {..<N}"
  shows "maps_invar (foldl reset_step U xs)" "representative (foldl reset_step U xs) = (\<lambda>x. if x \<in>
    set xs then x else representative U x)" "map_lookup (quf_next (foldl reset_step U xs)) = (\<lambda>x. if x
    \<in> set xs then x else map_lookup (quf_next U) x)" "map_lookup (quf_size (foldl reset_step U xs)) =
    (\<lambda>x. if x \<in> set xs then 1 else map_lookup (quf_size U) x)"
  using assms
  by(induction xs arbitrary: U) (auto simp: maps_invar_def reset_step_def representative_def
    Map.fixed_univ_map_upd_invar fun_eq_iff)

lemma reset_invar: "maps_invar U \<Longrightarrow> invar (reset_rep U)"
  using reset_fold[of U "[0..<N]"]
  by(auto simp: invar_def reset_rep_def component_def subset_eq intro!: exI[where x="[]"])

lemma reset_representative: "\<lbrakk>maps_invar U; x < N\<rbrakk> \<Longrightarrow> representative (reset_rep
  U) x = x"
  using reset_fold(2)[of U "[0..<N]"]
  by(auto simp: reset_rep_def subset_eq)

lemma union_props:
  assumes "invar U" "x < N" "y < N"
  shows "invar (union_rep U x y)" "representative (union_rep U x y) x \<in> {representative U x,
    representative U y}" "z < N \<Longrightarrow> representative (union_rep U x y) z = (if representative U z
    \<in> {representative U x, representative U y} then representative (union_rep U x y) x else representative
    U z)"
proof-
  obtain xs ys where components: "component U (representative U x) xs" "component U (representative U y) ys"
    using assms
    by(fastforce simp: invar_def)
  have "maps_invar U"
    using assms(1)
    by(auto simp: invar_def)
  with assms components merge_effects[of U "representative U x" xs "representative U y" ys] merge_effects[of U
    "representative U y" ys "representative U x" xs] merge_invar[of U "representative U x" xs "representative
    U y" ys] merge_invar[of U "representative U y" ys "representative U x" xs]
  show "invar (union_rep U x y)" "representative (union_rep U x y) x \<in> {representative U x, representative
    U y}" "z < N \<Longrightarrow> representative (union_rep U x y) z = (if representative U z \<in>
    {representative U x, representative U y} then representative (union_rep U x y) x else representative U z)"
    by(auto simp: union_rep_def Let_def split: if_splits)
qed

sublocale Spec: fixed_univ_union_find "{..<N}" invar representative find_rep union_rep reset_rep
  by(unfold_locales) (auto simp: find_rep_def dest: invar_def[THEN iffD1] intro: union_props reset_invar
    reset_representative; fastforce dest: union_props(2,3))+

end

section "In-place refinement over fixed-universe maps"

locale Quadratic_Union_Find_Imp =
  Quadratic_Union_Find N map_invar map_update map_lookup +
  Storage: fixed_univ_map_imp "{..<N}" map_invar map_update map_lookup id
    map_assn map_update_imp map_lookup_imp
  for N :: nat
    and map_invar :: "'map \<Rightarrow> bool"
    and map_update :: "'map \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'map"
    and map_lookup :: "'map \<Rightarrow> nat \<Rightarrow> nat"
    and map_assn :: "'map \<Rightarrow> 'mapi \<Rightarrow> assn"
    and map_update_imp :: "'mapi \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap"
    and map_lookup_imp :: "'mapi \<Rightarrow> nat \<Rightarrow> nat Heap"
begin

definition "uf_assn U Ri Li Si = map_assn (quf_representatives U) Ri *
  map_assn (quf_next U) Li * map_assn (quf_size U) Si"

partial_function (heap) relabel_imp ::
  "'mapi \<Rightarrow> 'mapi \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "relabel_imp Ri Li target k current =
    (if k = 0 then return () else do {
      next \<leftarrow> map_lookup_imp Li current;
      map_update_imp Ri current target;
      relabel_imp Ri Li target (k - 1) next
    })"

lemma relabel_imp_chain:
  assumes "map_invar R" "map_invar links" "set xs \<subseteq> {..<N}"
    "quf_chain (map_lookup links) xs z"
  shows "<map_assn R Ri * map_assn links Li>
    relabel_imp Ri Li target (length xs) (if xs = [] then z else hd xs)
    <\<lambda>_. map_assn (foldl (\<lambda>R x. map_update R x target) R xs) Ri * map_assn links Li>"
  using assms
proof(induction xs arbitrary: R)
  case Nil
  then show ?case
    by(subst relabel_imp.simps) sep_auto
next
  case (Cons x xs)
  then show ?case
    by(subst relabel_imp.simps)
      (sep_auto heap: Cons.IH simp: Map.fixed_univ_map_upd_invar)
qed

lemma relabel_imp_rule:
  assumes "maps_invar U" "component U a xs"
  shows "<map_assn (quf_representatives U) Ri * map_assn (quf_next U) Li>
    relabel_imp Ri Li b (map_lookup (quf_size U) a) a
    <\<lambda>_. map_assn (relabel U a b) Ri * map_assn (quf_next U) Li>"
  using relabel_imp_chain[where xs="a # xs" and R="quf_representatives U"
    and links="quf_next U" and z=a and target=b and Ri=Ri and Li=Li] assms
  by(auto simp: maps_invar_def component_def relabel_component_fold[OF assms(2)])

definition "merge_imp Ri Li Si a b na nb = do {
  next_a \<leftarrow> map_lookup_imp Li a;
  next_b \<leftarrow> map_lookup_imp Li b;
  relabel_imp Ri Li b na a;
  map_update_imp Li a next_b;
  map_update_imp Li b next_a;
  map_update_imp Si b (na + nb)
}"

lemma merge_imp_rule[sep_heap_rules]:
  assumes "maps_invar U" "component U a xs" "component U b ys"
  shows "<uf_assn U Ri Li Si>
    merge_imp Ri Li Si a b (map_lookup (quf_size U) a) (map_lookup (quf_size U) b)
    <\<lambda>_. uf_assn (merge_rep U a b) Ri Li Si>"
  using assms component_keys[OF assms(2)] component_keys[OF assms(3)]
  unfolding merge_imp_def uf_assn_def merge_rep_def
  by(sep_auto heap: relabel_imp_rule[OF assms(1,2)]
      simp: maps_invar_def Map.fixed_univ_map_upd_invar)

definition "union_imp Ri Li Si x y = do {
  a \<leftarrow> map_lookup_imp Ri x;
  b \<leftarrow> map_lookup_imp Ri y;
  if a = b then return () else do {
    na \<leftarrow> map_lookup_imp Si a;
    nb \<leftarrow> map_lookup_imp Si b;
    if na \<le> nb then merge_imp Ri Li Si a b na nb
    else merge_imp Ri Li Si b a nb na
  }
}"

lemma union_imp_rule[sep_heap_rules]:
  assumes "invar U" "x < N" "y < N"
  shows "<uf_assn U Ri Li Si> union_imp Ri Li Si x y
    <\<lambda>_. uf_assn (union_rep U x y) Ri Li Si>"
proof-
  obtain xs ys where components:
    "component U (representative U x) xs" "component U (representative U y) ys"
    using assms
    by(fastforce simp: invar_def)
  have "maps_invar U"
    using assms(1)
    by(auto simp: invar_def)
  with assms components component_keys[OF components(1)] component_keys[OF components(2)]
  show ?thesis
    unfolding union_imp_def union_rep_def uf_assn_def
    by(sep_auto heap: merge_imp_rule[OF _ components, unfolded uf_assn_def representative_def]
        merge_imp_rule[OF _ components(2,1), unfolded uf_assn_def representative_def]
        simp: maps_invar_def representative_def Let_def)
qed

lemma find_imp_rule[sep_heap_rules]:
  "\<lbrakk>invar U; x < N\<rbrakk> \<Longrightarrow>
    <uf_assn U Ri Li Si> map_lookup_imp Ri x
    <\<lambda>r. uf_assn U Ri Li Si * \<up>(r = representative U x)>"
  unfolding uf_assn_def
  by(sep_auto simp: representative_def invar_def maps_invar_def)

definition "reset_step_imp Ri Li Si i = do {
  map_update_imp Ri i i;
  map_update_imp Li i i;
  map_update_imp Si i 1
}"

definition "reset_imp Ri Li Si =
  foldl_range_imp (\<lambda>i _. reset_step_imp Ri Li Si i) 0 N ()"

lemma reset_step_imp_rule[sep_heap_rules]:
  "\<lbrakk>maps_invar U; i < N\<rbrakk> \<Longrightarrow>
    <uf_assn U Ri Li Si> reset_step_imp Ri Li Si i
    <\<lambda>_. uf_assn (reset_step U i) Ri Li Si>"
  unfolding reset_step_imp_def uf_assn_def reset_step_def
  by(sep_auto simp: maps_invar_def)

lemma reset_step_invar:
  "\<lbrakk>maps_invar U; i < N\<rbrakk> \<Longrightarrow> maps_invar (reset_step U i)"
  by(auto simp: maps_invar_def reset_step_def Map.fixed_univ_map_upd_invar)

lemma reset_imp_rule[sep_heap_rules]:
  "maps_invar U \<Longrightarrow> <uf_assn U Ri Li Si> reset_imp Ri Li Si
    <\<lambda>_. uf_assn (reset_rep U) Ri Li Si>"
  unfolding reset_imp_def reset_rep_def
  by(rule ht_cons[rotated 2, OF foldl_range_imp_rule[where
      A="\<lambda>U _. uf_assn U Ri Li Si * \<up>(maps_invar U)"
      and g="\<lambda>i U. reset_step U i" and F=emp and a=U]])
    (sep_auto simp: reset_step_invar)+

declare relabel_imp.simps[code]
end

global_interpretation Array_Union_Find: Quadratic_Union_Find_Imp N
  "\<lambda>_. True" array_fun_upd array_fun_lookup "array_fun_assn N"
  array_fun_upd_imp array_fun_lookup_imp for N
  defines array_uf_invar = Array_Union_Find.invar
    and array_uf_representative = Array_Union_Find.representative
    and array_uf_find = Array_Union_Find.find_rep
    and array_uf_union = Array_Union_Find.union_rep
    and array_uf_reset = Array_Union_Find.reset_rep
    and array_uf_assn = Array_Union_Find.uf_assn
    and array_uf_relabel_imp = Array_Union_Find.relabel_imp
    and array_uf_merge_imp = Array_Union_Find.merge_imp
    and array_uf_union_imp = Array_Union_Find.union_imp
    and array_uf_reset_step_imp = Array_Union_Find.reset_step_imp
    and array_uf_reset_imp = Array_Union_Find.reset_imp
  by(intro Quadratic_Union_Find_Imp.intro Quadratic_Union_Find.intro
      array_fun_fixed_univ_map array_fun_fixed_univ_map_imp)

definition "array_uf_initial N = array_uf_reset N
  \<lparr>quf_representatives = (\<lambda>_. 0), quf_next = (\<lambda>_. 0), quf_size = (\<lambda>_. 0)\<rparr>"

definition "array_uf_handle_assn N U Ui =
  (case Ui of (Ri,Li,Si) \<Rightarrow> array_uf_assn N U Ri Li Si)"

definition "array_uf_new N = do {
  Ri \<leftarrow> Array.new N (0::nat);
  Li \<leftarrow> Array.new N (0::nat);
  Si \<leftarrow> Array.new N (0::nat);
  array_uf_reset_imp N Ri Li Si;
  return (Ri,Li,Si)
}"

definition array_uf_query :: "(nat array \<times> nat array \<times> nat array) \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "array_uf_query Ui x = array_fun_lookup_imp (fst Ui) x"
definition "array_uf_union_into Ui x y =
  (case Ui of (Ri,Li,Si) \<Rightarrow> array_uf_union_imp Ri Li Si x y)"
definition "array_uf_reset_into N Ui =
  (case Ui of (Ri,Li,Si) \<Rightarrow> array_uf_reset_imp N Ri Li Si)"

lemma array_uf_initial_invar[simp]: "array_uf_invar N (array_uf_initial N)"
  unfolding array_uf_initial_def
  by(rule Array_Union_Find.reset_invar) (simp add: Array_Union_Find.maps_invar_def)

lemma array_uf_initial_rep:
  "x < N \<Longrightarrow> array_uf_representative (array_uf_initial N) x = x"
  unfolding array_uf_initial_def
  by(rule Array_Union_Find.reset_representative) (auto simp: Array_Union_Find.maps_invar_def)

lemma array_uf_new_rule[sep_heap_rules]:
  "<emp> array_uf_new N <array_uf_handle_assn N (array_uf_initial N)>"
  unfolding array_uf_new_def array_uf_initial_def array_uf_handle_assn_def
  by(sep_auto heap: array_fun_assn_new Array_Union_Find.reset_imp_rule[where U="\<lparr>quf_representatives = (\<lambda>_. 0), quf_next = (\<lambda>_. 0), quf_size = (\<lambda>_. 0)\<rparr>", unfolded Array_Union_Find.uf_assn_def, simplified]
      simp: Array_Union_Find.uf_assn_def Array_Union_Find.maps_invar_def)

lemma array_uf_query_rule[sep_heap_rules]:
  "\<lbrakk>array_uf_invar N U; x < N\<rbrakk> \<Longrightarrow>
    <array_uf_handle_assn N U Ui> array_uf_query Ui x
    <\<lambda>r. array_uf_handle_assn N U Ui * \<up>(r = array_uf_representative U x)>"
  unfolding array_uf_handle_assn_def array_uf_query_def
  by(cases Ui) (sep_auto heap: Array_Union_Find.find_imp_rule)

lemma array_uf_union_into_rule[sep_heap_rules]:
  "\<lbrakk>array_uf_invar N U; x < N; y < N\<rbrakk> \<Longrightarrow>
    <array_uf_handle_assn N U Ui> array_uf_union_into Ui x y
    <\<lambda>_. array_uf_handle_assn N (array_uf_union U x y) Ui>"
  unfolding array_uf_handle_assn_def array_uf_union_into_def
  by(cases Ui) (sep_auto heap: Array_Union_Find.union_imp_rule)

lemma array_uf_reset_into_rule[sep_heap_rules]:
  "<array_uf_handle_assn N U Ui> array_uf_reset_into N Ui
    <\<lambda>_. array_uf_handle_assn N (array_uf_reset N U) Ui>"
  unfolding array_uf_handle_assn_def array_uf_reset_into_def
  by(cases Ui) (sep_auto heap: Array_Union_Find.reset_imp_rule
      simp: Array_Union_Find.maps_invar_def)

section "Nil-coded bucket indices"

definition "nil_pointer nil x = (if x = nil then None else Some x)"

global_interpretation Nil_Pointer_Array: fixed_univ_map_imp "{..<n}" "\<lambda>_. True"
  array_fun_upd array_fun_lookup "nil_pointer nil" "array_fun_val_assn (nil_pointer nil) n"
  array_fun_upd_imp array_fun_lookup_imp for n nil
  by(rule array_fun_val_fixed_univ_map_imp)

global_interpretation Nil_Pointer_Clear: fixed_univ_map_clear_imp "{..<n}" "\<lambda>_. True"
  array_fun_lookup "nil_pointer nil" "array_fun_val_assn (nil_pointer nil) n"
  array_fun_lookup_imp "\<lambda>_. nil_pointer nil nil" "array_fun_clear_unit nil n" for n nil
  by(rule array_fun_val_fixed_univ_map_clear_imp)

type_synonym nil_buckets = "nat array \<times> nat array \<times> nat array"

fun nil_buckets_assn :: "nat \<Rightarrow> nat \<Rightarrow> abk \<Rightarrow> nil_buckets \<Rightarrow> assn" where
  "nil_buckets_assn n nb (H,T,NX,PV) (Hi,NXi,PVi) =
    array_fun_val_assn (nil_pointer n) nb H Hi *
    array_fun_val_assn (nil_pointer n) n NX NXi * array_fun_val_assn (nil_pointer n) n PV PVi"

definition "nil_buckets_new n nb = do {
  Hi \<leftarrow> Array.new nb n;
  NXi \<leftarrow> Array.new n n;
  PVi \<leftarrow> Array.new n n;
  return (Hi,NXi,PVi)
}"

definition "nil_buckets_clear n nb Bi =
  (case Bi of (Hi,NXi,PVi) \<Rightarrow> do {
    array_fun_clear_unit n nb Hi;
    array_fun_clear_unit n n NXi;
    array_fun_clear_unit n n PVi
  })"

definition "nil_buckets_insert n Bi x k =
  (case Bi of (Hi,NXi,PVi) \<Rightarrow> do {
    f \<leftarrow> array_fun_lookup_imp Hi k;
    array_fun_upd_imp Hi k x;
    array_fun_upd_imp NXi x f;
    array_fun_upd_imp PVi x n;
    if f = n then return () else array_fun_upd_imp PVi f x
  })"

definition "nil_buckets_remove n Bi x k =
  (case Bi of (Hi,NXi,PVi) \<Rightarrow> do {
    p \<leftarrow> array_fun_lookup_imp PVi x;
    q \<leftarrow> array_fun_lookup_imp NXi x;
    _ \<leftarrow> (if p = n then array_fun_upd_imp Hi k q else array_fun_upd_imp NXi p q);
    if q = n then return () else array_fun_upd_imp PVi q p
  })"

definition nil_buckets_pick :: "nil_buckets \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "nil_buckets_pick Bi k = array_fun_lookup_imp (fst Bi) k"

lemma nil_buckets_new_rule[sep_heap_rules]:
  "<emp> nil_buckets_new n nb <nil_buckets_assn n nb abk_empty>"
  unfolding nil_buckets_new_def abk_empty_def
  by(sep_auto heap: array_fun_assn_new simp: array_fun_val_assn_def nil_pointer_def)

lemma nil_buckets_clear_rule[sep_heap_rules]:
  "<nil_buckets_assn n nb B Bi> nil_buckets_clear n nb Bi
    <\<lambda>_. nil_buckets_assn n nb abk_empty Bi>"
  unfolding nil_buckets_clear_def abk_empty_def
  by(cases B; cases Bi) (sep_auto simp: nil_pointer_def)

lemma nil_buckets_pick_rule[sep_heap_rules]:
  "k < nb \<Longrightarrow>
    <nil_buckets_assn n nb B Bi> nil_buckets_pick Bi k
    <\<lambda>r. nil_buckets_assn n nb B Bi * \<up>(abk_pick B k = nil_pointer n r)>"
  unfolding nil_buckets_pick_def abk_pick_def
  by(cases B; cases Bi) (sep_auto simp: array_fun_lookup_def)

lemma nil_buckets_insert_rule[sep_heap_rules]:
  assumes "abk_invar n nb B" "x < n" "k < nb"
  shows "<nil_buckets_assn n nb B Bi> nil_buckets_insert n Bi x k
    <\<lambda>_. nil_buckets_assn n nb (abk_insert B x k) Bi>"
proof-
  obtain H T NX PV Hi NXi PVi L where state:
    "B = (H,T,NX,PV)" "Bi = (Hi,NXi,PVi)" "abk_good n nb (H,T,NX,PV) L"
    using assms(1)
    by(cases B; cases Bi) (auto simp: abk_invar_def)
  have "H k = Some y \<Longrightarrow> y < n" for y
    using abk_pointers(1)[OF state(3) assms(3)]
    by simp
  with assms(2,3) show ?thesis
    unfolding nil_buckets_insert_def abk_insert_def state(1,2)
    by(cases "H k")
      (sep_auto simp: array_fun_lookup_def array_fun_upd_def nil_pointer_def)+
qed

lemma nil_buckets_remove_rule[sep_heap_rules]:
  assumes "abk_invar n nb B" "abk_abstract n nb B x = Some k"
  shows "<nil_buckets_assn n nb B Bi> nil_buckets_remove n Bi x k
    <\<lambda>_. nil_buckets_assn n nb (abk_remove B x k) Bi>"
proof-
  obtain H T NX PV Hi NXi PVi L where state:
    "B = (H,T,NX,PV)" "Bi = (Hi,NXi,PVi)" "abk_good n nb (H,T,NX,PV) L"
    "x \<in> set (L k)"
    using assms
    by(cases B; cases Bi) (auto elim!: abk_invarE simp: lists_abs_Some)
  have "x < n" "k < nb" "PV x = Some a \<Longrightarrow> a < n"
    "NX x = Some b \<Longrightarrow> b < n" for a b
    using abk_good_in[OF state(3,4)] abk_pointers(3,4)[OF state(3,4)]
    by auto
  thus ?thesis
    unfolding nil_buckets_remove_def abk_remove_def state(1,2)
    by(cases "PV x"; cases "NX x")
      (sep_auto simp: array_fun_lookup_def array_fun_upd_def nil_pointer_def
        remove_nx_def remove_pv_def)+
qed

lemma nil_buckets_instance:
  "fixed_univ_buckets_nil_imp {..<n} {..<nb} (abk_invar n nb) (abk_abstract n nb)
    abk_empty abk_insert abk_remove abk_pick abk_move n (nil_buckets_assn n nb)
    (nil_buckets_new n nb) (nil_buckets_clear n nb) (nil_buckets_insert n)
    (nil_buckets_remove n) nil_buckets_pick"
  by(intro fixed_univ_buckets_nil_imp.intro abk_fixed_univ_buckets
      fixed_univ_buckets_nil_imp_axioms.intro)
    (auto intro: nil_buckets_new_rule nil_buckets_clear_rule nil_buckets_insert_rule
      nil_buckets_remove_rule nil_buckets_pick_rule[unfolded nil_pointer_def])
subsection "Saved cycle traversals"

type_synonym quadratic_cycle_slot = "nat \<times> nat \<times> nat \<times> nat \<times> bool \<times> nat \<times> nat"

fun cycle_stack_encode :: "quadratic_cycle_slot \<Rightarrow> nat list" where
  "cycle_stack_encode (off,len,cur,stop,forward,entry,exit) =
    [off,len,cur,stop,if forward then 1 else 0,entry,exit]"

definition "cycle_stack_cells F k = cycle_stack_encode (F (k div 7)) ! (k mod 7)"
definition "cycle_stack_map_assn capacity F Ai = array_fun_assn (7 * capacity) (cycle_stack_cells F) Ai"

definition "cycle_stack_new capacity = Array.new (7 * capacity) (0::nat)"

definition cycle_stack_read :: "nat array \<Rightarrow> nat \<Rightarrow> quadratic_cycle_slot Heap" where
  "cycle_stack_read Ai i = (let pos = 7 * i in do {
    off \<leftarrow> array_fun_lookup_imp Ai pos;
    len \<leftarrow> array_fun_lookup_imp Ai (pos + 1);
    cur \<leftarrow> array_fun_lookup_imp Ai (pos + 2);
    stop \<leftarrow> array_fun_lookup_imp Ai (pos + 3);
    direction \<leftarrow> array_fun_lookup_imp Ai (pos + 4);
    entry \<leftarrow> array_fun_lookup_imp Ai (pos + 5);
    exit \<leftarrow> array_fun_lookup_imp Ai (pos + 6);
    return (off,len,cur,stop,direction \<noteq> 0,entry,exit)
  })"

definition cycle_stack_write ::
  "nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "cycle_stack_write Ai i off len cur stop forward entry exit = (let pos = 7 * i in do {
    array_fun_upd_imp Ai pos off;
    array_fun_upd_imp Ai (pos + 1) len;
    array_fun_upd_imp Ai (pos + 2) cur;
    array_fun_upd_imp Ai (pos + 3) stop;
    array_fun_upd_imp Ai (pos + 4) (if forward then 1 else 0);
    array_fun_upd_imp Ai (pos + 5) entry;
    array_fun_upd_imp Ai (pos + 6) exit
  })"

lemma cycle_stack_cells_index:
  "j < 7 \<Longrightarrow> cycle_stack_cells F (7 * i + j) = cycle_stack_encode (F i) ! j"
  by(simp add: cycle_stack_cells_def)

lemmas cycle_stack_cells_slots =
  cycle_stack_cells_index[where j=0, simplified]
  cycle_stack_cells_index[where j=1, simplified]
  cycle_stack_cells_index[where j=2, simplified]
  cycle_stack_cells_index[where j=3, simplified]
  cycle_stack_cells_index[where j=4, simplified]
  cycle_stack_cells_index[where j=5, simplified]
  cycle_stack_cells_index[where j=6, simplified]

lemma cycle_stack_read_rule[sep_heap_rules]:
  assumes "i < capacity"
  shows "<cycle_stack_map_assn capacity F Ai> cycle_stack_read Ai i
    <\<lambda>r. cycle_stack_map_assn capacity F Ai * \<up>(r = F i)>"
proof-
  obtain off len cur stop forward entry exit where "F i = (off,len,cur,stop,forward,entry,exit)"
    by(cases "F i") auto
  with assms show ?thesis
    unfolding cycle_stack_read_def cycle_stack_map_assn_def Let_def
    by(sep_auto simp: cycle_stack_cells_slots array_fun_lookup_def)
qed

lemma cycle_stack_cells_update:
  "cycle_stack_cells (fun_upd F i (off,len,cur,stop,forward,entry,exit)) =
    array_fun_upd (array_fun_upd (array_fun_upd (array_fun_upd (array_fun_upd (array_fun_upd
      (array_fun_upd (cycle_stack_cells F) (7 * i + 0) off) (7 * i + 1) len) (7 * i + 2) cur) (7 * i + 3) stop)
       (7 * i + 4) (if forward then 1 else 0)) (7 * i + 5) entry) (7 * i + 6) exit"
    (is "?lhs = ?rhs")
proof(rule ext)
  fix k :: nat
  show "?lhs k = ?rhs k"
  proof(cases "k div 7 = i")
    case True
    hence "k = 7 * i \<or> k = 7 * i + 1 \<or> k = 7 * i + 2 \<or> k = 7 * i + 3 \<or>
        k = 7 * i + 4 \<or> k = 7 * i + 5 \<or> k = 7 * i + 6"
      by presburger
    thus ?thesis
      by(elim disjE; simp add: cycle_stack_cells_slots array_fun_upd_def)
  next
    case False
    then show ?thesis
      by(auto simp: cycle_stack_cells_def array_fun_upd_def split: if_splits)
  qed
qed

lemma cycle_stack_write_rule[sep_heap_rules]:
  "i < capacity \<Longrightarrow> <cycle_stack_map_assn capacity F Ai>
    cycle_stack_write Ai i off len cur stop forward entry exit
    <\<lambda>_. cycle_stack_map_assn capacity (fun_upd F i (off,len,cur,stop,forward,entry,exit)) Ai>"
  unfolding cycle_stack_write_def cycle_stack_map_assn_def Let_def
  by(sep_auto simp: cycle_stack_cells_update)

lemma cycle_stack_cells_zero:
  "cycle_stack_cells (\<lambda>_. (0,0,0,0,False,0,0)) = (\<lambda>_. 0)"
proof(rule ext)
  fix k :: nat
  have "cycle_stack_encode (0,0,0,0,False,0,0) = replicate 7 0"
    by(simp add: numeral_eq_Suc)
  thus "cycle_stack_cells (\<lambda>_. (0,0,0,0,False,0,0)) k = 0"
    by(simp add: cycle_stack_cells_def)
qed

lemma cycle_stack_new_rule[sep_heap_rules]:
  "<emp> cycle_stack_new capacity <cycle_stack_map_assn capacity (\<lambda>_. (0,0,0,0,False,0,0))>"
  unfolding cycle_stack_new_def cycle_stack_map_assn_def cycle_stack_cells_zero
  by(sep_auto heap: array_fun_assn_new)

definition "cycle_stack_update Ai k slot = (case slot of (off,len,i,j,forward,a,z) \<Rightarrow>
  cycle_stack_write Ai k off len i j forward a z)"

lemma cycle_stack_map_instance:
  "fixed_univ_map_imp {..<capacity} (\<lambda>_. True) array_fun_upd array_fun_lookup id
    (cycle_stack_map_assn capacity) cycle_stack_update cycle_stack_read"
  by(intro fixed_univ_map_imp.intro array_fun_fixed_univ_map
      fixed_univ_map_basic_imp.intro fixed_univ_map_imp_axioms.intro)
    (auto simp: cycle_stack_update_def array_fun_upd_def array_fun_lookup_def
      intro: cycle_stack_read_rule cycle_stack_write_rule split: prod.splits)

lemma cycle_stack_map_init_instance:
  "fixed_univ_map_init_imp {..<capacity} (\<lambda>_. True) array_fun_lookup id
    (cycle_stack_map_assn capacity) cycle_stack_read (\<lambda>_. (0,0,0,0,False,0,0))
    (cycle_stack_new capacity)"
  by(intro fixed_univ_map_init_imp.intro
      fixed_univ_map_imp.axioms(2)[OF cycle_stack_map_instance]
      fixed_univ_map_init_imp_axioms.intro cycle_stack_new_rule)

subsection "Pairs in a flat array"

definition "pair_map_cells F k =
  (if k mod 2 = 0 then fst (F (k div 2)) else snd (F (k div 2)))"

definition "pair_map_assn N F Ai = array_fun_assn (2 * N) (pair_map_cells F) Ai"

definition pair_map_read :: "nat array \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) Heap" where
  "pair_map_read Ai i = (let pos = 2 * i in do {
    a \<leftarrow> array_fun_lookup_imp Ai pos;
    b \<leftarrow> array_fun_lookup_imp Ai (Suc pos);
    return (a,b)
  })"

definition pair_map_write :: "nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "pair_map_write Ai i a b = (let pos = 2 * i in do {
    array_fun_upd_imp Ai pos a;
    array_fun_upd_imp Ai (Suc pos) b
  })"

definition "pair_map_update Ai i value = (case value of (a,b) \<Rightarrow> pair_map_write Ai i a b)"

definition pair_map_clear :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat array \<Rightarrow> unit Heap" where
  "pair_map_clear N a b Ai = do {
    _ \<leftarrow> fill_range_imp (\<lambda>k. if k mod 2 = 0 then a else b) (2 * N) Ai;
    return ()
  }"

definition "pair_map_new N a b = do {
  Ai \<leftarrow> Array.new (2 * N) (0::nat);
  pair_map_clear N a b Ai;
  return Ai
}"

lemma pair_map_cells_lookup[simp]:
  "pair_map_cells F (2 * i) = fst (F i)"
  "pair_map_cells F (Suc (2 * i)) = snd (F i)"
  by(auto simp: pair_map_cells_def)

lemma pair_map_read_rule[sep_heap_rules]:
  "i < N \<Longrightarrow> <pair_map_assn N F Ai> pair_map_read Ai i
    <\<lambda>r. pair_map_assn N F Ai * \<up>(r = F i)>"
  unfolding pair_map_assn_def pair_map_read_def Let_def
  by(sep_auto simp: array_fun_lookup_def)

lemma pair_map_cells_update:
  "pair_map_cells (fun_upd F i (a,b)) =
    array_fun_upd (array_fun_upd (pair_map_cells F) (2 * i) a) (Suc (2 * i)) b"
    (is "?lhs = ?rhs")
proof(rule ext)
  fix k :: nat
  have "k div 2 = i \<longleftrightarrow> k = 2 * i \<or> k = Suc (2 * i)"
    by presburger
  thus "?lhs k = ?rhs k"
    by(auto simp: pair_map_cells_def array_fun_upd_def)
qed

lemma pair_map_write_rule[sep_heap_rules]:
  "i < N \<Longrightarrow> <pair_map_assn N F Ai> pair_map_write Ai i a b
    <\<lambda>_. pair_map_assn N (fun_upd F i (a,b)) Ai>"
  unfolding pair_map_assn_def pair_map_write_def Let_def
  by(sep_auto simp: pair_map_cells_update)

lemma pair_map_cells_constant:
  "pair_map_cells (\<lambda>_. (a,b)) = (\<lambda>k. if k mod 2 = 0 then a else b)"
  by(rule ext) (simp add: pair_map_cells_def)

lemma pair_map_clear_rule[sep_heap_rules]:
  "<pair_map_assn N F Ai> pair_map_clear N a b Ai
    <\<lambda>_. pair_map_assn N (\<lambda>_. (a,b)) Ai>"
  unfolding pair_map_clear_def pair_map_assn_def array_fun_assn_def pair_map_cells_constant
  by(sep_auto heap: fill_range_imp_rule)

lemma pair_map_new_rule[sep_heap_rules]:
  "<emp> pair_map_new N a b <pair_map_assn N (\<lambda>_. (a,b))>"
  unfolding pair_map_new_def pair_map_clear_def pair_map_assn_def array_fun_assn_def pair_map_cells_constant
  by(sep_auto heap: fill_range_imp_rule)

lemma pair_map_instance:
  "fixed_univ_map_imp {..<N} (\<lambda>_. True) array_fun_upd array_fun_lookup id
    (pair_map_assn N) pair_map_update pair_map_read"
  by(intro fixed_univ_map_imp.intro array_fun_fixed_univ_map
      fixed_univ_map_basic_imp.intro fixed_univ_map_imp_axioms.intro)
    (auto simp: pair_map_update_def array_fun_upd_def array_fun_lookup_def
      intro: pair_map_read_rule pair_map_write_rule split: prod.splits)

lemma pair_map_init_instance:
  "fixed_univ_map_init_imp {..<N} (\<lambda>_. True) array_fun_lookup id
    (pair_map_assn N) pair_map_read (\<lambda>_. (a,b)) (pair_map_new N a b)"
  by(intro fixed_univ_map_init_imp.intro
      fixed_univ_map_imp.axioms(2)[OF pair_map_instance]
      fixed_univ_map_init_imp_axioms.intro pair_map_new_rule)

lemma pair_map_clear_instance:
  "fixed_univ_map_clear_imp {..<N} (\<lambda>_. True) array_fun_lookup id
    (pair_map_assn N) pair_map_read (\<lambda>_. (a,b)) (pair_map_clear N a b)"
  by(intro fixed_univ_map_clear_imp.intro
      fixed_univ_map_imp.axioms(2)[OF pair_map_instance]
      fixed_univ_map_clear_imp_axioms.intro pair_map_clear_rule)

section "Array storage views"

lemma array_length_map:
  "len_assn n Ai \<Longrightarrow>\<^sub>A (\<exists>\<^sub>A f. array_fun_assn n f Ai)"
  unfolding len_assn_def
proof(rule ent_ex_preI, goal_cases)
  case (1 xs)
  show ?case
    by(rule ent_ex_postI[where x="nth xs"]) (sep_auto simp: array_fun_assn_def map_nth)
qed

section "Concrete adapters"

lemma pair_map_cells_inverse:
  "pair_map_cells (\<lambda>i. (f (2 * i), f (2 * i + 1))) = (f::nat \<Rightarrow> nat)"
  by(rule ext) (auto simp: pair_map_cells_def intro!: arg_cong[where f=f]; presburger)

lemma pair_map_storage:
  "len_assn (2 * N) (Ai::nat array) \<Longrightarrow>\<^sub>A (\<exists>\<^sub>A F. pair_map_assn N F Ai)"
  unfolding len_assn_def
proof(rule ent_ex_preI, rule ent_pure_preI, goal_cases)
  case (1 xs)
  show ?case
    unfolding pair_map_assn_def 1[symmetric]
    by(rule ent_ex_postI[where x="\<lambda>i. (xs ! (2 * i), xs ! (2 * i + 1))"])
      (simp add: pair_map_cells_inverse[of "nth xs", simplified] array_fun_assn_def map_nth)
qed

lemmas quadratic_buffer_instance = array_fun_fixed_univ_map_imp[
  unfolded array_fun_upd_def array_fun_lookup_def, folded id_def Quadratic_Blossom_Search_Path_Buffer_def]

lemmas quadratic_cycle_stack_instance = cycle_stack_map_instance[
  unfolded array_fun_upd_def array_fun_lookup_def, folded id_def Quadratic_Cycle_Stack_def]

lemma quadratic_set_iteration:
  "finite S ==>
    EX xs. S = set xs & distinct xs & foldl f init (sorted_list_of_set S) = foldl f init xs"
  by(intro exI[of _ "sorted_list_of_set S"]) simp

lemma quadratic_forest_model:
  "forest_contract_manipulation {..<N::nat}
    (\<lambda>_. True) fun_upd id (\<lambda>_. True) fun_upd id
    (\<lambda>S. S \<subseteq> {..<N}) id {} (\<lambda>x S. S - {x}) (\<lambda>S x. x \<in> S)
    (\<lambda>f init S. foldl f init (sorted_list_of_set S)) N
    (\<lambda>f init S. foldl f init (sorted_list_of_set S)) (\<union>) insert (\<lambda>_. N) (\<lambda>_. N)"
  by unfold_locales (auto simp: id_def intro: quadratic_set_iteration dest: finite_subset)

lemma quadratic_forest_instance:
  "Alternating_Forest_Contraction_Imperative
    (\<lambda>_. True) fun_upd id (\<lambda>_. True) fun_upd id
    (\<lambda>S. S \<subseteq> {..<N::nat}) id {} (\<lambda>x S. S - {x}) (\<lambda>S x. x \<in> S)
    (\<lambda>f init S. foldl f init (sorted_list_of_set S)) N
    (\<lambda>f init S. foldl f init (sorted_list_of_set S)) (\<union>) insert (\<lambda>_. N) (\<lambda>_. N)
    {..<N} (array_fun_assn N) array_fun_upd_imp array_fun_lookup_imp
    (array_fun_clear_unit N N) (Array.new N N)
    (\<lambda>_. True) fun_upd id (array_fun_assn N) array_fun_upd_imp array_fun_lookup_imp
    (\<lambda>_. 0) (Array.new N 0) (array_fun_clear_unit 0 N)
    (abk_invar N N) (abk_abstract N N) abk_empty abk_insert abk_remove abk_pick abk_move
    (nil_buckets_assn N N) (nil_buckets_new N N) (nil_buckets_clear N N)
    (nil_buckets_insert N) (nil_buckets_remove N) nil_buckets_pick"
  by(intro Alternating_Forest_Contraction_Imperative.intro quadratic_forest_model
      array_fun_fixed_univ_map_imp[unfolded array_fun_upd_def array_fun_lookup_def, folded id_def]
      array_fun_fixed_univ_map_clear_imp[unfolded array_fun_lookup_def, folded id_def]
      array_fun_fixed_univ_map_init_imp[unfolded array_fun_lookup_def, folded id_def]
      nil_buckets_instance Alternating_Forest_Contraction_Imperative_axioms.intro)
    (simp_all add: id_def)

subsection "Resetting raw union-find storage"

definition array_uf_singletons :: "(nat \<Rightarrow> nat) Quadratic_Union_Find_state" where
  "array_uf_singletons = \<lparr>quf_representatives = id, quf_next = id, quf_size = (\<lambda>_. 1)\<rparr>"

lemma array_uf_reset_singletons[simp]:
  "array_uf_reset N array_uf_singletons = array_uf_singletons"
proof-
  have "Array_Union_Find.reset_step array_uf_singletons i = array_uf_singletons" for i
    by(auto simp: Array_Union_Find.reset_step_def array_uf_singletons_def array_fun_upd_def fun_eq_iff)
  hence "foldl Array_Union_Find.reset_step array_uf_singletons xs = array_uf_singletons" for xs
    by(induction xs) auto
  thus ?thesis
    by(simp add: Array_Union_Find.reset_rep_def)
qed

lemma array_uf_singletons_invar[simp]: "array_uf_invar N array_uf_singletons"
  using Array_Union_Find.reset_invar[where N=N and U=array_uf_singletons]
  by(simp add: Array_Union_Find.maps_invar_def)

lemma array_uf_singletons_rep[simp]:
  "array_uf_representative array_uf_singletons v = v"
  by(simp add: Array_Union_Find.representative_def array_uf_singletons_def array_fun_lookup_def)

lemma array_length_map_eq:
  "len_assn n Ai = (\<exists>\<^sub>A f. array_fun_assn n f Ai)"
  by(rule ent_iffI[OF array_length_map], rule ent_ex_preI, rule array_fun_len)

lemma array_uf_storage:
  "len_assn N Ri * len_assn N Li * len_assn N Si \<Longrightarrow>\<^sub>A
    (\<exists>\<^sub>A U. array_uf_handle_assn N (U::(nat \<Rightarrow> nat) Quadratic_Union_Find_state) (Ri,Li,Si))"
proof(sep_auto simp: array_length_map_eq array_uf_handle_assn_def Array_Union_Find.uf_assn_def,
    (rule ent_ex_preI)+, goal_cases)
  case (1 S L R)
  show ?case
    by(rule ent_ex_postI[where x="\<lparr>quf_representatives = R, quf_next = L, quf_size = S\<rparr>"]) simp
qed

lemma array_uf_reset_maps:
  "i < N \<Longrightarrow> quf_representatives (array_uf_reset N U) i = i"
  "i < N \<Longrightarrow> quf_next (array_uf_reset N U) i = i"
  "i < N \<Longrightarrow> quf_size (array_uf_reset N U) i = 1"
  using Array_Union_Find.reset_fold(2-4)[where N=N and U=U and xs="[0..<N]"]
  by(auto simp: Array_Union_Find.maps_invar_def Array_Union_Find.reset_rep_def
      Array_Union_Find.representative_def array_fun_lookup_def subset_eq fun_eq_iff)

lemma array_uf_reset_assn:
  "array_uf_handle_assn N (array_uf_reset N U) Ui =
    array_uf_handle_assn N array_uf_singletons Ui"
proof-
  have "map (quf_representatives (array_uf_reset N U)) [0..<N] = map id [0..<N]"
    "map (quf_next (array_uf_reset N U)) [0..<N] = map id [0..<N]"
    "map (quf_size (array_uf_reset N U)) [0..<N] = map (\<lambda>_. 1) [0..<N]"
    by(auto intro!: map_idI map_cong simp: array_uf_reset_maps)
  thus ?thesis
    by(auto simp: array_uf_handle_assn_def Array_Union_Find.uf_assn_def array_uf_singletons_def
        array_fun_assn_def simp del: map_eq_conv split: prod.splits)
qed

lemma array_uf_reset_storage_rule[sep_heap_rules]:
  "<len_assn N Ri * len_assn N Li * len_assn N Si>
    array_uf_reset_into N (Ri,Li,Si) <\<lambda>_. array_uf_handle_assn N array_uf_singletons (Ri,Li,Si)>"
  by(rule ht_cons_pre[OF array_uf_storage], rule ht_ex_pre)
    (sep_auto heap: array_uf_reset_into_rule simp: array_uf_reset_assn)

subsection "Concrete forest operations"

global_interpretation quadratic_forest: Alternating_Forest_Contraction_Imperative
  where parent_invar = "\<lambda>_. True"
    and parent_upd = "fun_upd"
    and parent_get = "id"
    and origin_invar = "\<lambda>_. True"
    and origin_upd = "fun_upd"
    and origin_get = "id"
    and vset_invar = "\<lambda>S. S \<subseteq> {..<N}"
    and vset_to_set = "id"
    and vset_empty = "{}"
    and vset_delete = "\<lambda>x S. S - {x}"
    and vset_isin = "\<lambda>S x. x \<in> S"
    and vset_iterate = "\<lambda>f init S. foldl f init (sorted_list_of_set S)"
    and nil = "N"
    and vset_iterate_parent = "\<lambda>f init S. foldl f init (sorted_list_of_set S)"
    and vset_union = "(\<union>)"
    and vset_insert = "insert"
    and parent_empty = "\<lambda>_. N"
    and origin_empty = "\<lambda>_. N"
    and K = "{..<N}"
    and parent_assn = "array_fun_assn N"
    and parent_upd_imp = "array_fun_upd_imp"
    and parent_get_imp = "array_fun_lookup_imp"
    and parent_clear_imp = "array_fun_clear_unit N N"
    and parent_empty_imp = "Array.new N N"
    and label_invar = "\<lambda>_. True"
    and label_upd = "fun_upd"
    and label_get = "id"
    and label_assn = "array_fun_assn N"
    and label_upd_imp = "array_fun_upd_imp"
    and label_get_imp = "array_fun_lookup_imp"
    and label_empty = "\<lambda>_. 0"
    and label_empty_imp = "Array.new N 0"
    and label_clear_imp = "array_fun_clear_unit 0 N"
    and children_invar = "abk_invar N N"
    and children_abstract = "abk_abstract N N"
    and children_empty = "abk_empty"
    and children_insert = "abk_insert"
    and children_remove = "abk_remove"
    and children_pick = "abk_pick"
    and children_move = "abk_move"
    and children_assn = "nil_buckets_assn N N"
    and children_empty_imp = "nil_buckets_new N N"
    and children_clear_imp = "nil_buckets_clear N N"
    and children_insert_imp = "nil_buckets_insert N"
    and children_remove_imp = "nil_buckets_remove N"
    and children_pick_imp = "nil_buckets_pick"
  for N :: nat
  defines quadratic_forest_assn = quadratic_forest.contractable_forest_assn
    and quadratic_forest_classify = quadratic_forest.classify_imp
    and quadratic_forest_clear_into = quadratic_forest.contractable_clear_into
    and quadratic_forest_add_root_into = quadratic_forest.contractable_add_root_into
    and quadratic_forest_extend_into = quadratic_forest.contractable_extend_into
    and quadratic_forest_contract = quadratic_forest.contract_fork_buffer_imp
    and quadratic_forest_paths_into = quadratic_forest.paths_into
    and quadratic_forest_model_empty = quadratic_forest.empty_forest
    and quadratic_forest_model_extend = quadratic_forest.extend_forest_even_unclassified
    and quadratic_forest_model_path = quadratic_forest.get_path
    and quadratic_forest_model_path_loop = quadratic_forest.get_path_loop
    and quadratic_forest_redirect_child = quadratic_forest.redirect_child_imp
    and quadratic_forest_redirect_children = quadratic_forest.redirect_children_imp
    and quadratic_forest_remove_indexed_child = quadratic_forest.remove_indexed_child_imp
    and quadratic_forest_retire_vertex = quadratic_forest.retire_vertex_imp
    and quadratic_forest_retire_buffer = quadratic_forest.retire_buffer_imp
    and quadratic_forest_redirect_bucket = quadratic_forest.redirect_bucket_imp
    and quadratic_forest_redirect_buffer = quadratic_forest.redirect_buffer_imp
    and quadratic_forest_parent = quadratic_forest.forest_parent_imp
    and quadratic_forest_redirect_path = quadratic_forest.redirect_path_imp
    and quadratic_forest_install_contracted = quadratic_forest.install_contracted_imp
    and quadratic_forest_contract_path_buffer = quadratic_forest.contract_path_buffer_imp
    and quadratic_forest_paired_mark = quadratic_forest.paired_mark_imp
    and quadratic_forest_paired_hit_left = quadratic_forest.paired_hit_left_imp
    and quadratic_forest_paired_hit_right = quadratic_forest.paired_hit_right_imp
    and quadratic_forest_paired_advance = quadratic_forest.paired_advance_imp
    and quadratic_forest_paired_ascent = quadratic_forest.paired_ascent_imp
    and quadratic_forest_paired_workspace_new = quadratic_forest.paired_workspace_new
  by(rule quadratic_forest_instance)

lemmas [code] =
  quadratic_forest.classify_imp_def
  quadratic_forest.contractable_clear_into_def
  quadratic_forest.contractable_add_root_into_def
  quadratic_forest.contractable_extend_into_def
  quadratic_forest.contract_fork_buffer_imp_def
  quadratic_forest.paths_into_def
  quadratic_forest.redirect_child_imp_def
  quadratic_forest.redirect_children_imp.simps
  quadratic_forest.remove_indexed_child_imp_def
  quadratic_forest.retire_vertex_imp_def
  quadratic_forest.retire_buffer_imp.simps
  quadratic_forest.redirect_bucket_imp_def
  quadratic_forest.redirect_buffer_imp.simps
  quadratic_forest.forest_parent_imp_def
  quadratic_forest.redirect_path_imp_def
  quadratic_forest.install_contracted_imp_def
  quadratic_forest.contract_path_buffer_imp_def
  quadratic_forest.paired_mark_imp_def
  quadratic_forest.paired_hit_left_imp_def
  quadratic_forest.paired_hit_right_imp_def
  quadratic_forest.paired_advance_imp_def
  quadratic_forest.paired_ascent_imp.simps

definition "quadratic_forest_contract_into N Ci Pa plen Qa qlen target = do {
  _ \<leftarrow> quadratic_forest_contract N Ci Pa plen Qa qlen target; return ()
}"

lemmas quadratic_forest_contract_into_rule = ht_bind[
  OF quadratic_forest.contract_fork_buffer_rule ht_return_wp[where Q="\<lambda>_. _" and x="()"],
  folded quadratic_forest_contract_into_def]

lemma nil_buckets_clear_storage_rule[sep_heap_rules]:
  "<len_assn nb Hi * len_assn n NXi * len_assn n PVi>
    nil_buckets_clear n nb (Hi,NXi,PVi) <\<lambda>_. nil_buckets_assn n nb abk_empty (Hi,NXi,PVi)>"
  unfolding nil_buckets_clear_def array_fun_clear_unit_def
  by(sep_auto heap: array_fun_val_clear_rule[where h="nil_pointer n"] simp: abk_empty_def nil_pointer_def)

lemma quadratic_forest_clear_storage_rule[sep_heap_rules]:
  "<len_assn N li * len_assn N pai * len_assn N Hi * len_assn N NXi * len_assn N PVi>
    quadratic_forest_clear_into N (li,pai,(Hi,NXi,PVi))
    <\<lambda>_. quadratic_forest_assn N (quadratic_forest_model_empty N {}) (li,pai,(Hi,NXi,PVi))>"
  unfolding quadratic_forest.contractable_clear_into_def array_fun_clear_unit_def
    quadratic_forest.contractable_forest_assn_def quadratic_forest.forest_storage_assn_def
    quadratic_forest.forest_labels_assn_def quadratic_forest.indexed_parents_assn_def
    quadratic_forest.empty_forest_def
  by(sep_auto heap: array_fun_clear_rule nil_buckets_clear_storage_rule
      simp: quadratic_forest.Children.buckets_empty quadratic_forest.empties quadratic_forest.label_empty)

lemma array_clear_storage_rule[sep_heap_rules]:
  "<len_assn n (Ai::nat array)> array_fun_clear_unit v n Ai
    <\<lambda>_. array_fun_assn n (\<lambda>_. v) Ai>"
  unfolding array_fun_clear_unit_def
  by(sep_auto heap: array_fun_clear_rule)

subsection "Scalar CSR row iteration"

definition csr_row_begin :: "nat array \<times> 'e::heap array \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) Heap" where
  "csr_row_begin = (\<lambda>(Ba,Ea) v. do {
    i \<leftarrow> Array.nth Ba v; e \<leftarrow> Array.nth Ba (Suc v); return (i,e) })"

definition "csr_row_has (it::nat \<times> nat) \<longleftrightarrow> fst it < snd it"

definition csr_row_read :: "nat array \<times> 'e::heap array \<Rightarrow> nat \<times> nat \<Rightarrow> 'e Heap" where
  "csr_row_read = (\<lambda>(Ba,Ea) (i,e). Array.nth Ea i)"

definition "csr_row_advance (it::nat \<times> nat) = (Suc (fst it), snd it)"

context csr_graph_blocks_imp
begin

definition "csr_row_rel c v it \<longleftrightarrow> fst it = c v \<and> snd it = B ! Suc v"

lemma csr_row_reset_rel:
  "csr_row_rel (csr_reset c v) v (B ! v, B ! Suc v)"
  by(simp add: csr_row_rel_def csr_reset_def)

lemma csr_row_has_refine:
  "csr_row_rel c v it \<Longrightarrow> csr_row_has it = csr_has c v"
  by(simp add: csr_row_rel_def csr_row_has_def csr_has_def)

lemma csr_row_current_refine:
  "csr_row_rel c v it \<Longrightarrow> E ! fst it = csr_current c v"
  by(simp add: csr_row_rel_def csr_current_def)

lemma csr_row_advance_refine:
  "\<lbrakk>csr_row_rel c v it; csr_row_has it\<rbrakk> \<Longrightarrow>
   csr_row_rel (csr_move c v) v (csr_row_advance it)"
  by(auto simp: csr_row_rel_def csr_row_advance_def csr_move_def csr_row_has_def)

lemma csr_row_bounds:
  "\<lbrakk>csr_invar c; v \<in> K; csr_row_rel c v it\<rbrakk> \<Longrightarrow>
   B ! v \<le> fst it \<and> fst it \<le> snd it \<and> snd it \<le> length E"
  using B_bound[of v] K_less[of v]
  by(auto simp: csr_invar_def csr_row_rel_def)

lemma csr_row_read_bound:
  "\<lbrakk>v \<in> K; csr_row_rel c v it; csr_row_has it\<rbrakk> \<Longrightarrow> fst it < length E"
  using B_bound[of v] K_less[of v]
  by(auto simp: csr_row_rel_def csr_row_has_def)

lemma csr_row_remaining:
  "csr_row_rel c v it \<Longrightarrow> csr_remaining c v = (!) E ` {fst it..<snd it}"
  by(simp add: csr_row_rel_def csr_remaining_def seg_def)

lemma csr_row_iterated:
  "csr_row_rel c v it \<Longrightarrow> csr_iterated c v = (!) E ` {B ! v..<fst it}"
  by(simp add: csr_row_rel_def csr_iterated_def seg_def)

lemma csr_row_finished:
  "csr_row_rel c v it \<Longrightarrow> (\<not> csr_row_has it) = (csr_remaining c v = {})"
  using remaining_ne[of c v] csr_row_has_refine[of c v it]
  by(auto simp: csr_has_def)

lemma csr_row_begin_rule:
  assumes "v \<in> K"
  shows "<csr_blocks_assn c Ci> csr_row_begin Ci v
    <\<lambda>it. csr_blocks_assn (csr_reset c v) Ci * \<up>(csr_row_rel (csr_reset c v) v it)>"
  using K_less[OF assms] B_length
  by(cases Ci) (sep_auto simp: csr_blocks_assn_def csr_row_begin_def csr_row_rel_def csr_reset_def)

lemma csr_row_read_rule:
  assumes "v \<in> K" "csr_row_rel c v it" "csr_row_has it"
  shows "<csr_blocks_assn c Ci> csr_row_read Ci it
    <\<lambda>x. csr_blocks_assn c Ci * \<up>(x = csr_current c v)>"
  using assms csr_row_read_bound[OF assms]
  by(cases Ci; cases it)
    (sep_auto simp: csr_blocks_assn_def csr_row_read_def csr_row_rel_def csr_current_def)

lemma csr_reset_unscanned:
  "\<lbrakk>csr_invar c; v \<in> K; csr_iterated c v = {}\<rbrakk> \<Longrightarrow> csr_reset c v = c"
  by(auto simp: csr_invar_def csr_iterated_def seg_empty_iff csr_reset_def fun_eq_iff)

lemma csr_row_begin_unscanned_rule:
  "\<lbrakk>csr_invar c; v \<in> K; csr_iterated c v = {}\<rbrakk> \<Longrightarrow>
    <csr_blocks_assn c Ci> csr_row_begin Ci v
    <\<lambda>it. csr_blocks_assn c Ci * \<up>(csr_row_rel c v it)>"
  using csr_row_begin_rule[of v c Ci]
  by(auto simp: csr_reset_unscanned)

end

subsection "Matching and frontier models"

global_interpretation quadratic_matching: matching_augmentation
  "{..<N}" "\<lambda>_. True" fun_upd id "\<lambda>_. N" N
  for N::nat
  defines quadratic_matching_invar = quadratic_matching.invar_matching
    and quadratic_matching_abstract = quadratic_matching.\<M>
    and quadratic_matching_partner = quadratic_matching.get_partner
    and quadratic_matching_lookup = quadratic_matching.buddy_lookup
    and quadratic_matching_augment = quadratic_matching.augment_impl
    and quadratic_matching_contract = quadratic_matching.contract_path
    and quadratic_matching_expand = quadratic_matching.expand_path_at_matched
    and quadratic_matching_add = quadratic_matching.add_alternatingly
  by(intro matching_augmentation.intro matching_augmentation_axioms.intro
      Matching_Augmentation_Specs.intro
      array_fun_fixed_univ_map[unfolded array_fun_upd_def array_fun_lookup_def, folded id_def])
    (simp_all add: id_def)

lemma quadratic_list_queue:
  "bounded_queue cap (\<lambda>xs. length xs \<le> cap) id []
    (\<lambda>xs x. xs @ [x]) (\<lambda>xs. (hd xs, tl xs)) (\<lambda>xs. xs = [])"
  by unfold_locales (auto simp: id_def)

definition quadratic_matching_extend :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "quadratic_matching_extend n N M = (\<lambda>v. if v < n then M v else N)"

lemma quadratic_matching_extend_lookup[simp]:
  "v < n \<Longrightarrow> quadratic_matching_extend n N M v = M v"
  "n \<le> v \<Longrightarrow> quadratic_matching_extend n N M v = N"
  by(auto simp: quadratic_matching_extend_def)

lemma quadratic_matching_extend_update:
  "u < n \<Longrightarrow> quadratic_matching_extend n N (fun_upd M u v) =
    fun_upd (quadratic_matching_extend n N M) u v"
  by(auto simp: quadratic_matching_extend_def fun_eq_iff)

lemma quadratic_matching_extend_idem[simp]:
  "quadratic_matching_extend n N (quadratic_matching_extend n N M) =
    quadratic_matching_extend n N M"
  by(auto simp: quadratic_matching_extend_def fun_eq_iff)

lemma quadratic_matching_extend_augment:
  "set p \<subseteq> {..<n} \<Longrightarrow>
    quadratic_matching_extend n N (quadratic_matching_augment M p) =
    quadratic_matching_augment (quadratic_matching_extend n N M) p"
  by(induction M p rule: quadratic_matching.augment_impl.induct)
    (auto simp: quadratic_matching_extend_update)

lemma quadratic_matching_arrays:
  "matching_augmentation_imp {..<n} (\<lambda>_. True) fun_upd id
    (array_fun_assn n) array_fun_upd_imp array_fun_lookup_imp"
  by(intro matching_augmentation_imp.intro Matching_Augmentation_Specs.intro
      array_fun_fixed_univ_map[unfolded array_fun_upd_def array_fun_lookup_def, folded id_def]
      array_fun_fixed_univ_map_imp[unfolded array_fun_upd_def array_fun_lookup_def, folded id_def])

definition "quadratic_matching_augment_into = matching_augmentation_imp.augment_imp array_fun_upd_imp"

definition "quadratic_matching_augment_loop = matching_augmentation_imp.augment_loop array_fun_upd_imp"

lemmas quadratic_matching_augment_into_code[code] = matching_augmentation_imp.augment_imp_def[
  OF quadratic_matching_arrays, folded quadratic_matching_augment_into_def quadratic_matching_augment_loop_def]
lemmas quadratic_matching_augment_loop_simps[code] = matching_augmentation_imp.augment_loop.simps[
  OF quadratic_matching_arrays, folded quadratic_matching_augment_loop_def]

lemmas quadratic_matching_array_augment_rule = matching_augmentation_imp.augment_imp_rule[
  OF quadratic_matching_arrays, folded quadratic_matching_augment_def quadratic_matching_augment_into_def]

definition "quadratic_matching_assn n N M Mi =
  array_fun_assn n M Mi * \<up>(M = quadratic_matching_extend n N M)"

lemma quadratic_matching_array_view:
  "array_fun_assn n (quadratic_matching_extend n N M) Mi = array_fun_assn n M Mi"
  by(unfold array_fun_assn_def quadratic_matching_extend_def,
      intro arg_cong[where f="\<lambda>xs. Mi \<mapsto>\<^sub>a xs"] map_cong) auto

lemma quadratic_matching_storage:
  "array_fun_assn n M Mi \<Longrightarrow>\<^sub>A
    quadratic_matching_assn n N (quadratic_matching_extend n N M) Mi"
  by(simp add: quadratic_matching_assn_def quadratic_matching_array_view)

lemma quadratic_matching_read_rule[sep_heap_rules]:
  "u < n \<Longrightarrow> <quadratic_matching_assn n N M Mi> array_fun_lookup_imp Mi u
    <\<lambda>v. quadratic_matching_assn n N M Mi * \<up>(v = M u)>"
  unfolding quadratic_matching_assn_def
  by(sep_auto heap: array_fun_lookup_rule simp: array_fun_lookup_def)

lemma quadratic_matching_augment_rule[sep_heap_rules]:
  "\<lbrakk>k \<le> length xs; set (take k xs) \<subseteq> {..<n}\<rbrakk> \<Longrightarrow>
    <quadratic_matching_assn n N M Mi * Ra \<mapsto>\<^sub>a xs>
    quadratic_matching_augment_into Mi Ra k
    <\<lambda>_. quadratic_matching_assn n N (quadratic_matching_augment M (take k xs)) Mi * Ra \<mapsto>\<^sub>a xs>"
  unfolding quadratic_matching_assn_def
  by(sep_auto heap: quadratic_matching_array_augment_rule
      simp: quadratic_matching_extend_augment)

lemmas quadratic_matching_instance = quadratic_matching.blossom_matching_spec_satisfied[
  folded quadratic_matching_invar_def]

lemma quadratic_matching_supported:
  "\<lbrakk>quadratic_matching_invar N G M; Vs G \<subseteq> {..<n}\<rbrakk> \<Longrightarrow>
    M = quadratic_matching_extend n N M"
  using quadratic_matching.matching.matching[of N G M]
    quadratic_matching.matching.get_partner[of N G M]
  by(auto simp: quadratic_matching_extend_def quadratic_matching_invar_def fun_eq_iff Vs_def; blast)

lemma quadratic_matching_original_storage:
  "\<lbrakk>quadratic_matching_invar N G M; Vs G \<subseteq> {..<n}\<rbrakk> \<Longrightarrow>
    array_fun_assn n M Mi \<Longrightarrow>\<^sub>A quadratic_matching_assn n N M Mi"
  by(simp add: quadratic_matching_assn_def quadratic_matching_supported)

lemma quadratic_matching_empty_storage[simp]:
  "quadratic_matching_assn n N (\<lambda>_. N) Mi = array_fun_assn n (\<lambda>_. N) Mi"
  by(simp add: quadratic_matching_assn_def quadratic_matching_extend_def)

lemma quadratic_matching_empty:
  "\<lbrakk>Vs G \<subseteq> {..<n}; n \<le> N\<rbrakk> \<Longrightarrow>
    quadratic_matching_invar N G (\<lambda>_. N)"
  by(rule quadratic_matching.empty_matching_props(1)[folded quadratic_matching_invar_def]) auto

subsection "The ordered hierarchy model"

text "The hierarchy is a ghost of the search; it never enters the generated code. It is the
  laminar tree of the library over function maps and sets of identifiers."

context laminar_tree
begin

interpretation ordered_family: laminar_family_spec
  "%(tops, L). dom (lookup L)" "%(tops, L). all_verts L"
  "%(tops, L). collect_verts L" "%(tops, L). max_ids L" blossom_forest_invar
  "%(tops, L). {collect_verts L i |i. i : dom (lookup L)}" compound
  using laminar_family_spec_statisfied_axioms
  unfolding laminar_family_spec_def
  by(fastforce dest: blossom_forest_invarD(1))

interpretation ordered_base: blossom_forest_spec
  where all_ids = "%(tops, L). dom (lookup L)"
    and universe = "%(tops, L). all_verts L"
    and collect_elems = "%(tops, L). collect_verts L"
    and max_ids = "%(tops, L). max_ids L"
    and blossom_forest_invar = blossom_forest_invar
    and laminar_abstract = "%(tops, L). {collect_verts L i |i. i : dom (lookup L)}"
    and compound = compound and blossom_edges = blossom_edges
proof(intro blossom_forest_spec.intro ordered_family.laminar_family_spec_axioms
    blossom_forest_spec_axioms.intro, goal_cases)
  case (1 H i)
  thus ?case
    by(cases H) (auto dest: branching_odd_collect_verts_odd)
next
  case (2 H)
  thus ?case
    using blossom_edges_props(1)
    by(cases H) auto
next
  case (3 H)
  thus ?case
    using blossom_edges_props(2)
    by(cases H) auto
next
  case (4 H i j)
  thus ?case
    by(cases H) (force intro!: blossom_edges_props(3)[of _ _ i j])
qed

interpretation ordered_merge: blossom_forest_merge_spec
  where all_ids = "%(tops, L). dom (lookup L)"
    and universe = "%(tops, L). all_verts L"
    and collect_elems = "%(tops, L). collect_verts L"
    and max_ids = "%(tops, L). max_ids L"
    and blossom_forest_invar = blossom_forest_invar
    and laminar_abstract = "%(tops, L). {collect_verts L i |i. i : dom (lookup L)}"
    and compound = compound and blossom_edges = blossom_edges and merge = merge
  using merge_props
  by(intro blossom_forest_merge_spec.intro ordered_base.blossom_forest_spec_axioms)
    (auto simp: blossom_forest_merge_spec_axioms_def split_paired_all all_verts_def)

lemma laminar_ordered_children:
  "Blossom_Forest_Ordered_axioms (%(tops, L). dom (lookup L))
    (%(tops, L). max_ids L) blossom_forest_invar merge
    (%H b. case lookup (snd H) b of Some (subverts cs) => cs | _ => [])"
  by(auto simp: Blossom_Forest_Ordered_axioms_def split_paired_all
    ordered_base.blossom_forest_merge_precond_def ordered_family.laminar_merge_precond_def
    map.map_update split: if_splits)

lemmas laminar_blossom_merge_spec = ordered_merge.blossom_forest_merge_spec_axioms

end

lemma quadratic_laminar_tree:
  "laminar_tree Map.empty (%k m. fun_upd m k None) (%m. m) (%_. True) (%S x. x : S) insert
    (%k v m. fun_upd m k (Some v)) ({} :: nat set) (%x S. S - {x}) finite id
    (%f init S. foldl f init (sorted_list_of_set S))"
  by unfold_locales (auto dest: quadratic_set_iteration)

type_synonym quadratic_hierarchy = "nat set * (nat => (nat, nat) contracted_laminar option)"

definition "quadratic_hierarchy_ids (H :: quadratic_hierarchy) = dom (snd H)"
definition "quadratic_hierarchy_universe (H :: quadratic_hierarchy) = laminar_tree.all_verts (%m. m) (snd H)"
definition "quadratic_hierarchy_members (H :: quadratic_hierarchy) = laminar_tree.collect_verts (%m. m) (snd H)"
definition "quadratic_hierarchy_tops (H :: quadratic_hierarchy) = laminar_tree.max_ids (%m. m) (snd H)"
definition "quadratic_hierarchy_invar (H :: quadratic_hierarchy) =
  laminar_tree.blossom_forest_invar (%m. m) (%_. True) finite id H"
definition "quadratic_hierarchy_abstract (H :: quadratic_hierarchy) =
  {quadratic_hierarchy_members H i |i. i : quadratic_hierarchy_ids H}"
definition "quadratic_hierarchy_compound (H :: quadratic_hierarchy) = laminar_tree.compound (%m. m) H"
definition "quadratic_hierarchy_edges (H :: quadratic_hierarchy) = laminar_tree.blossom_edges (%m. m) H"
definition "quadratic_hierarchy_merge (H :: quadratic_hierarchy) =
  laminar_tree.merge insert (%k v m. fun_upd m k (Some v)) (%x S. S - {x}) H"
definition "quadratic_hierarchy_children (H :: quadratic_hierarchy) b =
  (case snd H b of Some (subverts cs) => cs | _ => [])"

lemmas quadratic_hierarchy_defs = quadratic_hierarchy_ids_def quadratic_hierarchy_universe_def
  quadratic_hierarchy_members_def quadratic_hierarchy_tops_def quadratic_hierarchy_invar_def
  quadratic_hierarchy_abstract_def quadratic_hierarchy_compound_def quadratic_hierarchy_edges_def
  quadratic_hierarchy_merge_def quadratic_hierarchy_children_def

global_interpretation quadratic_hierarchy: Blossom_Forest_Ordered
  where all_ids = quadratic_hierarchy_ids and universe = quadratic_hierarchy_universe
    and collect_elems = quadratic_hierarchy_members and max_ids = quadratic_hierarchy_tops
    and blossom_forest_invar = quadratic_hierarchy_invar and laminar_abstract = quadratic_hierarchy_abstract
    and compound = quadratic_hierarchy_compound and blossom_edges = quadratic_hierarchy_edges
    and merge = quadratic_hierarchy_merge and children = quadratic_hierarchy_children
  unfolding quadratic_hierarchy_defs
  using laminar_tree.laminar_blossom_merge_spec[OF quadratic_laminar_tree]
    laminar_tree.laminar_ordered_children[OF quadratic_laminar_tree]
  by(intro Blossom_Forest_Ordered.intro) (simp_all add: case_prod_unfold)

text "Initially every input vertex is a singleton blossom named by itself."

definition quadratic_singletons :: "nat => quadratic_hierarchy" where
  "quadratic_singletons n = ({..<n}, %v. if v < n then Some (elem_vert v) else None)"

lemma quadratic_singletons_relation[simp]:
  "laminar_tree.laminar_forest_cons (%m. m) (snd (quadratic_singletons n)) = {}"
  by(auto simp: laminar_tree.laminar_forest_cons_def[OF quadratic_laminar_tree] quadratic_singletons_def
    split: if_splits)

lemma quadratic_singletons_subids:
  "laminar_tree.ids_of_sub_laminars (%m. m) (snd (quadratic_singletons n)) v = (if v < n then {v} else {})"
  "laminar_tree.collect_verts (%m. m) (snd (quadratic_singletons n)) v = (if v < n then {v} else {})"
  using quadratic_singletons_relation[of n]
  by(simp_all add: laminar_tree.ids_of_sub_laminars_simps[OF quadratic_laminar_tree]
    laminar_tree.collect_verts_simps[OF quadratic_laminar_tree] quadratic_singletons_def)

lemma quadratic_singletons_observations[simp]:
  "quadratic_hierarchy_ids (quadratic_singletons n) = {..<n}"
  "quadratic_hierarchy_tops (quadratic_singletons n) = {..<n}"
  "quadratic_hierarchy_universe (quadratic_singletons n) = {..<n}"
  "quadratic_hierarchy_members (quadratic_singletons n) v = (if v < n then {v} else {})"
  "quadratic_hierarchy_children (quadratic_singletons n) v = []"
  using quadratic_singletons_subids[of n]
  by(auto simp: quadratic_hierarchy_defs dom_def laminar_tree.max_ids_def[OF quadratic_laminar_tree]
    laminar_tree.all_verts_def[OF quadratic_laminar_tree] quadratic_singletons_def split: if_splits)

lemma quadratic_singletons_invar[simp]:
  "quadratic_hierarchy_invar (quadratic_singletons n)"
proof-
  have "laminar_tree.blossom_forest_invar (%m. m) (%_. True) finite id
    (fst (quadratic_singletons n), snd (quadratic_singletons n))"
    using quadratic_singletons_subids[of n] quadratic_singletons_observations(2,3)[of n,
      unfolded quadratic_hierarchy_defs] quadratic_singletons_relation[of n]
    by(intro laminar_tree.blossom_forest_invarI[OF quadratic_laminar_tree]
        laminar_tree.laminar_forest_invarI[OF quadratic_laminar_tree])
      (auto simp: laminar_tree.disjoint_subids_def[OF quadratic_laminar_tree]
        laminar_tree.disjoint_trees_def[OF quadratic_laminar_tree]
        laminar_tree.elem_unique_id_def[OF quadratic_laminar_tree]
        laminar_tree.branching_properly_def[OF quadratic_laminar_tree]
        laminar_tree.domain_recursive_def[OF quadratic_laminar_tree]
        laminar_tree.distinct_children_def[OF quadratic_laminar_tree]
        laminar_tree.branching_odd_def[OF quadratic_laminar_tree] quadratic_singletons_def dom_def
        split: if_splits)
  thus ?thesis
    by(simp add: quadratic_hierarchy_invar_def)
qed

end
