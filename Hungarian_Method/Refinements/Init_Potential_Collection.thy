theory Init_Potential_Collection
  imports Data_Structures.Iterable_Set_Specs "HOL-Data_Structures.Map_Specs"
          Directed_Set_Graphs.More_Arith
begin

section \<open>The Initial Potential over a Collection of Neighbourhoods\<close>

text \<open>The initial potential of the Hungarian method assigns to every left vertex @{term u} the
      minimum weight of an edge at @{term u}, and nothing to the right vertices. Here, the
      neighbourhoods are given by a collection with cursors (@{locale indexed_iterable_set}), which
      is scanned vertex by vertex. This is the functional counterpart of the imperative
      computation over CSR neighbourhoods, which reads the weights at the cursor.\<close>

locale init_potential_coll_spec =
  fixes potential_upd :: "'v \<Rightarrow> real \<Rightarrow> 'potential \<Rightarrow> 'potential"
    and potential_lookup :: "'potential \<Rightarrow> 'v \<Rightarrow> real option"
    and rnb_current :: "'g \<Rightarrow> 'v \<Rightarrow> 'v"
    and rnb_has :: "'g \<Rightarrow> 'v \<Rightarrow> bool"
    and rnb_move :: "'g \<Rightarrow> 'v \<Rightarrow> 'g"
    and rnb_reset :: "'g \<Rightarrow> 'v \<Rightarrow> 'g"
    and cost :: "'v \<Rightarrow> 'v \<Rightarrow> real"
    and vset_iterate :: "('g \<times> 'potential \<Rightarrow> 'v \<Rightarrow> 'g \<times> 'potential)
                          \<Rightarrow> 'g \<times> 'potential \<Rightarrow> 'vset \<Rightarrow> 'g \<times> 'potential"
begin

definition "upd_min u c \<pi> =
  (case potential_lookup \<pi> u of
     None \<Rightarrow> potential_upd u c \<pi>
   | Some r \<Rightarrow> if r \<le> c then \<pi> else potential_upd u c \<pi>)"

partial_function (tailrec) scan_min :: "'v \<Rightarrow> 'g \<Rightarrow> 'potential \<Rightarrow> 'g \<times> 'potential" where
  "scan_min u C \<pi> =
     (if rnb_has C u then scan_min u (rnb_move C u) (upd_min u (cost u (rnb_current C u)) \<pi>)
      else (C, \<pi>))"

definition "init_step Cp u = scan_min u (rnb_reset (fst Cp) u) (snd Cp)"

definition "init_potential_coll C0 pot0 left = vset_iterate init_step (C0, pot0) left"

lemmas [code] = upd_min_def scan_min.simps init_step_def init_potential_coll_def

end

locale init_potential_coll = init_potential_coll_spec +
  pot: Map potential_empty potential_upd potential_delete potential_lookup potential_invar +
  rnb: indexed_iterable_set rnb_invar rnb_abstract rnb_current rnb_has rnb_iterated
      rnb_remaining rnb_move rnb_reset K
  for potential_empty potential_delete potential_invar
    and rnb_invar rnb_abstract rnb_iterated rnb_remaining K +
  fixes vset_to_set and vset_invar and lst
  assumes vset_iterate_lst:
      "\<And>V f init. vset_invar V \<Longrightarrow> vset_iterate f init V = foldl f init (lst (vset_to_set V))"
    and lst_set: "\<And>S. finite S \<Longrightarrow> set (lst S) = S"
begin

abbreviation "fmin u \<equiv> (\<lambda>\<pi> v. upd_min u (cost u v) \<pi>)"

lemma scan_min_is_foldl:
  assumes "rnb_invar C" "u \<in> K" "finite (rnb_remaining C u)"
  shows "\<exists>rs. set rs = rnb_remaining C u \<and>
            snd (scan_min u C \<pi>) = foldl (fmin u) \<pi> rs \<and>
            rnb_invar (fst (scan_min u C \<pi>)) \<and>
            rnb_abstract (fst (scan_min u C \<pi>)) = rnb_abstract C"
  using assms
proof(induction "card (rnb_remaining C u)" arbitrary: C \<pi>)
  case 0
  hence empty: "rnb_remaining C u = {}" by simp
  hence not_has: "\<not> rnb_has C u" using rnb.idx_has[OF 0(2,3)] by simp
  show ?case
    using 0(2) by (auto intro!: exI[of _ "[]"] simp: scan_min.simps[of u C \<pi>] not_has empty)
next
  case (Suc n)
  hence ne: "rnb_remaining C u \<noteq> {}" by auto
  hence has: "rnb_has C u" using rnb.idx_has[OF Suc(3,4)] by simp
  define x where "x = rnb_current C u"
  define C' where "C' = rnb_move C u"
  have x_in: "x \<in> rnb_remaining C u" using rnb.idx_current[OF Suc(3,4) ne] by (simp add: x_def)
  have C': "rnb_invar C'" "rnb_remaining C' u = rnb_remaining C u - {x}"
           "rnb_abstract C' = rnb_abstract C"
    using rnb.idx_move_invar[OF Suc(3,4)] rnb.idx_move_remaining[OF Suc(3,4) ne]
          rnb.idx_move_abstract[OF Suc(3,4) ne]
    by (auto simp: C'_def x_def fun_eq_iff)
  have card: "n = card (rnb_remaining C' u)" using Suc(2,5) x_in by (simp add: C'(2))
  obtain rs where rs: "set rs = rnb_remaining C' u"
     "snd (scan_min u C' (fmin u \<pi> x)) = foldl (fmin u) (fmin u \<pi> x) rs"
     "rnb_invar (fst (scan_min u C' (fmin u \<pi> x)))"
     "rnb_abstract (fst (scan_min u C' (fmin u \<pi> x))) = rnb_abstract C'"
    using Suc(1)[OF card C'(1) Suc(4)] Suc(5) by (auto simp: C'(2))
  have eq: "scan_min u C \<pi> = scan_min u C' (fmin u \<pi> x)"
    by (simp add: scan_min.simps[of u C \<pi>] has C'_def x_def)
  show ?case
    using rs x_in by (intro exI[of _ "x # rs"]) (auto simp: eq C'(2,3))
qed

lemma foldl_fmin:
  "potential_invar \<pi> \<Longrightarrow>
   potential_invar (foldl (fmin u) \<pi> rs) \<and>
   (\<forall>w. w \<noteq> u \<longrightarrow> potential_lookup (foldl (fmin u) \<pi> rs) w = potential_lookup \<pi> w) \<and>
   (\<forall>v\<in>set rs. \<exists>r. potential_lookup (foldl (fmin u) \<pi> rs) u = Some r \<and> r \<le> cost u v) \<and>
   (\<forall>r. potential_lookup \<pi> u = Some r \<longrightarrow>
        (\<exists>r'. potential_lookup (foldl (fmin u) \<pi> rs) u = Some r' \<and> r' \<le> r)) \<and>
   (rs = [] \<longrightarrow> foldl (fmin u) \<pi> rs = \<pi>)"
proof(induction rs arbitrary: \<pi>)
  case (Cons v rs)
  define \<pi>' where "\<pi>' = fmin u \<pi> v"
  have p': "potential_invar \<pi>'"
           "\<And>w. w \<noteq> u \<Longrightarrow> potential_lookup \<pi>' w = potential_lookup \<pi> w"
           "\<exists>r. potential_lookup \<pi>' u = Some r \<and> r \<le> cost u v"
           "\<And>r. potential_lookup \<pi> u = Some r \<Longrightarrow> \<exists>r'. potential_lookup \<pi>' u = Some r' \<and> r' \<le> r"
    using Cons.prems
    by (auto simp: \<pi>'_def upd_min_def pot.map_update pot.invar_update split: option.splits)
  note IH = Cons.IH[OF p'(1)]
  show ?case
  proof(intro conjI allI impI ballI)
    show "potential_invar (foldl (fmin u) \<pi> (v # rs))" using IH by (simp add: \<pi>'_def)
  next
    fix w assume "w \<noteq> u"
    thus "potential_lookup (foldl (fmin u) \<pi> (v # rs)) w = potential_lookup \<pi> w"
      using IH p'(2) by (simp add: \<pi>'_def)
  next
    fix v' assume v': "v' \<in> set (v # rs)"
    show "\<exists>r. potential_lookup (foldl (fmin u) \<pi> (v # rs)) u = Some r \<and> r \<le> cost u v'"
    proof(cases "v' \<in> set rs")
      case True
      thus ?thesis using IH by (simp add: \<pi>'_def)
    next
      case False
      hence "v' = v" using v' by simp
      then obtain r where "potential_lookup \<pi>' u = Some r" "r \<le> cost u v'" using p'(3) by blast
      then obtain r' where "potential_lookup (foldl (fmin u) \<pi>' rs) u = Some r'" "r' \<le> r"
        using IH by blast
      thus ?thesis using \<open>r \<le> cost u v'\<close> by (auto simp: \<pi>'_def)
    qed
  next
    fix r assume "potential_lookup \<pi> u = Some r"
    then obtain r1 where "potential_lookup \<pi>' u = Some r1" "r1 \<le> r" using p'(4) by blast
    then obtain r2 where "potential_lookup (foldl (fmin u) \<pi>' rs) u = Some r2" "r2 \<le> r1"
      using IH by blast
    thus "\<exists>r'. potential_lookup (foldl (fmin u) \<pi> (v # rs)) u = Some r' \<and> r' \<le> r"
      using \<open>r1 \<le> r\<close> by (auto simp: \<pi>'_def)
  qed simp
qed simp

text \<open>The invariant of the iteration over the left vertices.\<close>

definition "init_inv C0 pot0 S Cp =
  (rnb_invar (fst Cp) \<and> rnb_abstract (fst Cp) = rnb_abstract C0 \<and>
   potential_invar (snd Cp) \<and>
   (\<forall>u\<in>S. \<forall>v\<in>rnb_abstract C0 u.
       \<exists>r. potential_lookup (snd Cp) u = Some r \<and> r \<le> cost u v) \<and>
   dom (potential_lookup (snd Cp)) \<subseteq> dom (potential_lookup pot0) \<union> S)"

lemma init_step_inv:
  assumes "init_inv C0 pot0 S Cp" "u \<in> K" "finite (rnb_abstract C0 u)"
  shows "init_inv C0 pot0 (insert u S) (init_step Cp u)"
proof-
  obtain C \<pi> where Cp: "Cp = (C, \<pi>)" by (cases Cp) auto
  have I: "rnb_invar C" "rnb_abstract C = rnb_abstract C0" "potential_invar \<pi>"
          "\<forall>u\<in>S. \<forall>v\<in>rnb_abstract C0 u. \<exists>r. potential_lookup \<pi> u = Some r \<and> r \<le> cost u v"
          "dom (potential_lookup \<pi>) \<subseteq> dom (potential_lookup pot0) \<union> S"
    using assms(1) by (auto simp: init_inv_def Cp)
  define C1 where "C1 = rnb_reset C u"
  have C1: "rnb_invar C1" "rnb_remaining C1 u = rnb_abstract C0 u"
           "rnb_abstract C1 = rnb_abstract C0"
    using rnb.idx_reset_invar[OF I(1) assms(2)] rnb.idx_reset_remaining[OF I(1) assms(2)]
          rnb.idx_reset_abstract[OF I(1) assms(2)] I(2)
    by (auto simp: C1_def fun_eq_iff)
  obtain rs where rs: "set rs = rnb_abstract C0 u"
      "snd (scan_min u C1 \<pi>) = foldl (fmin u) \<pi> rs"
      "rnb_invar (fst (scan_min u C1 \<pi>))"
      "rnb_abstract (fst (scan_min u C1 \<pi>)) = rnb_abstract C1"
    using scan_min_is_foldl[OF C1(1) assms(2), of \<pi>] assms(3) C1(2) by auto
  note F = foldl_fmin[OF I(3), of u rs]
  have st: "init_step Cp u = scan_min u C1 \<pi>" by (simp add: init_step_def Cp C1_def)
  have dom_new: "dom (potential_lookup (foldl (fmin u) \<pi> rs)) \<subseteq> dom (potential_lookup \<pi>) \<union> {u}"
    using F by (auto simp: dom_def)
  show ?thesis
    unfolding init_inv_def st
  proof(intro conjI ballI)
    show "rnb_invar (fst (scan_min u C1 \<pi>))" using rs(3) .
    show "rnb_abstract (fst (scan_min u C1 \<pi>)) = rnb_abstract C0" using rs(4) C1(3) by simp
    show "potential_invar (snd (scan_min u C1 \<pi>))" using F rs(2) by simp
  next
    fix u' v assume u': "u' \<in> insert u S" and v: "v \<in> rnb_abstract C0 u'"
    show "\<exists>r. potential_lookup (snd (scan_min u C1 \<pi>)) u' = Some r \<and> r \<le> cost u' v"
    proof(cases "u' = u")
      case True
      thus ?thesis using F v rs(1,2) by auto
    next
      case False
      hence "u' \<in> S" using u' by simp
      thus ?thesis using F I(4) v False rs(2) by auto
    qed
  next
    show "dom (potential_lookup (snd (scan_min u C1 \<pi>))) \<subseteq>
          dom (potential_lookup pot0) \<union> insert u S"
      using dom_new I(5) rs(2) by auto
  qed
qed

lemma foldl_init_step_inv:
  "\<lbrakk>init_inv C0 pot0 S Cp; set xs \<subseteq> K; \<forall>u\<in>set xs. finite (rnb_abstract C0 u)\<rbrakk> \<Longrightarrow>
   init_inv C0 pot0 (S \<union> set xs) (foldl init_step Cp xs)"
proof(induction xs arbitrary: S Cp)
  case (Cons x xs)
  have "init_inv C0 pot0 (insert x S) (init_step Cp x)"
    using init_step_inv[OF Cons.prems(1)] Cons.prems(2,3) by simp
  from Cons.IH[OF this] Cons.prems(2,3) show ?case by simp
qed simp

theorem init_potential_coll_props:
  assumes "rnb_invar C0" "vset_invar left" "finite (vset_to_set left)"
          "vset_to_set left \<subseteq> K" "\<And>u. u \<in> vset_to_set left \<Longrightarrow> finite (rnb_abstract C0 u)"
  defines "res \<equiv> init_potential_coll C0 potential_empty left"
  shows "potential_invar (snd res)"
        "\<And>u v. \<lbrakk>u \<in> vset_to_set left; v \<in> rnb_abstract C0 u\<rbrakk> \<Longrightarrow>
               abstract_real_map (potential_lookup (snd res)) u \<le> cost u v"
        "dom (potential_lookup (snd res)) \<subseteq> vset_to_set left"
        "rnb_invar (fst res)" "rnb_abstract (fst res) = rnb_abstract C0"
proof-
  have i0: "init_inv C0 potential_empty {} (C0, potential_empty)"
    using assms(1) by (auto simp: init_inv_def pot.invar_empty pot.map_empty)
  have res: "res = foldl init_step (C0, potential_empty) (lst (vset_to_set left))"
    by (simp add: res_def init_potential_coll_def vset_iterate_lst[OF assms(2)])
  have I: "init_inv C0 potential_empty (vset_to_set left) res"
    using foldl_init_step_inv[OF i0, of "lst (vset_to_set left)"] assms(4,5)
          lst_set[OF assms(3)]
    by (simp add: res)
  show "potential_invar (snd res)" "rnb_invar (fst res)" "rnb_abstract (fst res) = rnb_abstract C0"
    using I by (auto simp: init_inv_def)
  show "dom (potential_lookup (snd res)) \<subseteq> vset_to_set left"
    using I by (auto simp: init_inv_def pot.map_empty)
  fix u v assume uv: "u \<in> vset_to_set left" "v \<in> rnb_abstract C0 u"
  then obtain r where "potential_lookup (snd res) u = Some r" "r \<le> cost u v"
    using I unfolding init_inv_def by blast
  thus "abstract_real_map (potential_lookup (snd res)) u \<le> cost u v"
    by (simp add: abstract_real_map_def)
qed

end

end
