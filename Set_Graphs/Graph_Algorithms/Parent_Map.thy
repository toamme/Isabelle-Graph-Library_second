theory Parent_Map
  imports "HOL-Data_Structures.Map_Specs"  "HOL-Data_Structures.Set_Specs"
          Undirected_Set_Graphs.Directed_Undirected
         Directed_Set_Graphs.Multigraph
begin                          

definition parent_spec::"('a \<Rightarrow> 'a option) \<Rightarrow> bool" where
  "parent_spec parent = wf {(x, y) |x y. (Some x = parent y)}"

locale parent_spec = 
  fixes parent::"'a \<Rightarrow> 'a option" and
    parent_rel::"'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

function (domintros) follow where
  "follow v = (case (parent v) of Some v' \<Rightarrow> v # (follow v') | _  \<Rightarrow> [v])"
  by pat_completeness auto

partial_function (tailrec) follow_impl_loop  where
  "follow_impl_loop v acc =  
  (case (parent v) of Some v' \<Rightarrow> (follow_impl_loop v' (v#acc)) 
     | _  \<Rightarrow> v#acc)"

lemma follow_dom_impl_same_loop:
  assumes "follow_dom v"
  shows   "follow_impl_loop v acc = rev (rev acc @ follow v)"
  apply(induction arbitrary: acc rule: follow.pinduct[OF assms(1)])
  apply(subst follow_impl_loop.simps)
  by(auto simp add: follow.psimps split: option.split)

definition "follow_impl v = rev (follow_impl_loop v Nil)"

lemma follow_dom_impl_same: "follow_dom v \<Longrightarrow> follow_impl v = follow v"
  by(auto simp add: follow_impl_def follow_dom_impl_same_loop)

lemmas [code] = follow_impl_def follow_impl_loop.simps

lemma assumes "parent v = None"
  shows "follow_dom v"
  apply(rule follow.domintros)
  using assms
  by auto

lemma assumes "parent v' = Some v" "follow_dom v"
  shows "Wellfounded.accp follow_rel v'"
  apply(rule follow.domintros)
  using assms
  by auto

lemma wfP_follow_rel:
  assumes "wfP follow_rel"
  shows "follow_dom v"
  using accp_wfpD[OF assms]
  by blast

lemma wf_follow_rel:
  assumes "wf {(x,y) | x y. follow_rel x y}"
  shows "follow_dom v"
  using wfP_follow_rel assms
  unfolding wfp_def
  by force

end

global_interpretation parent_spec_i: parent_spec parent parent_rel for parent parent_rel
  defines follow_impl = parent_spec_i.follow_impl
    and follow_impl_loop = parent_spec_i.follow_impl_loop
    and follow = parent_spec_i.follow
  done

value "follow_impl (\<lambda> (x::nat). if x = 3 then Some 2 
                                else if x = 2 then Some 1 
                                else if x = 1 then Some 0 
                                else None) 
                   3"


locale parent = 
  parent_spec+
  assumes parent_rel:
    "parent_spec parent"
begin

lemma parent_eq_follow_rel: "follow_rel = (\<lambda>v' v. Some v' = parent v)"
  unfolding parent_rel follow_rel.simps
  apply simp
  apply(rule HOL.ext)+
  by auto

lemma wf_found_rel:
  "wf {(x,y) | x y. follow_rel x y}"
  unfolding parent_eq_follow_rel
  using parent_rel[unfolded parent_spec_def]
  by simp

lemma follow_dom:
  "follow_dom v"
  using wf_found_rel wf_follow_rel
  by force

lemma follow_impl_is_follow:
  "follow_impl = follow"
  by(auto simp add: follow_dom_impl_same parent.follow_dom parent_axioms)

lemma follow_cons:
  "follow u = v # p \<Longrightarrow> v = u"
  by (auto simp: follow.psimps[OF follow_dom] split: option.splits)

lemma follow_cons_2:
  "follow v = v # v' # p \<Longrightarrow> follow v' = v' # p"
  "follow v = v # v' # p \<Longrightarrow> parent v = Some v'"
  by(cases "parent v"; simp add: follow.psimps[OF follow_dom]; clarsimp split: option.splits)+

lemma follow_append:
  "follow v = p @ u # p' \<Longrightarrow> follow u = u # p'"
proof(induction "follow v" arbitrary: v p)
  case nil1: Nil
  then show ?case 
    by auto
next
  case cons1: (Cons v' follow_v')
  then have "v' = v"
    using follow_cons
    by metis
  show ?case
  proof (cases follow_v')
    case nil2: Nil
    then have "v = u" "p = []"
      using cons1 \<open>v' = v\<close>
      by (simp add: Cons_eq_append_conv)+
    then show ?thesis
      using cons1
      by auto
  next
    case cons2: (Cons v'' follow_v'')
    then show ?thesis
      using cons1
      by (metis \<open>v' = v\<close> append_eq_Cons_conv follow_cons_2 list.sel(1))
  qed
qed

lemma from_tree:
  assumes "follow v1 = p1 @ u # p1'" "follow v2 = p2 @ u # p2'"
  shows "p1' = p2'"
  using follow_append follow_append
    assms parent_axioms
  by fastforce

lemma follow_psimps:
  "follow v = (case parent v of None \<Rightarrow> [v] | Some v' \<Rightarrow> v # follow v')"
  using follow.psimps[OF follow_dom] .

lemma follow_hd: "hd (follow  v) = v"
  by(auto simp add:  follow_psimps split: option.split)

lemma follow_nempty: "follow v \<noteq> []"
  apply(subst follow.psimps[OF follow_dom])
  by(auto simp add: option.case_eq_if split: if_splits)

lemma follow_None:
  "follow v = [v'] \<Longrightarrow> parent v = None"
  apply(subst (asm) follow.psimps[OF follow_dom])
  by(auto simp add: follow_nempty option.case_eq_if split: if_splits)

lemma nin_ancestors: 
 "\<lbrakk>\<forall>v2\<in>set (follow v1). parent v2 \<noteq> Some v3; v3 \<noteq> v1\<rbrakk> \<Longrightarrow>  v3 \<notin> set (follow v1)"
proof(induction rule: follow.pinduct[OF follow_dom[of v1]])
  case (1 v)
  then show ?case
  proof (cases "parent v")
    case None
    then show ?thesis
      using 1
      by (simp add: follow_psimps)
  next
    case (Some a)
    then show ?thesis
      using 1
      using follow_psimps by auto
  qed
qed

lemma follow_walk_betw:
  "walk_betw {{x, y}| x y. follow_rel x y} v (follow v) (last (follow v)) \<or> 
   follow v = [v]"
proof(induction rule: follow.pinduct[OF follow_dom])
  case (1 v)
  show ?case 
  proof(cases "parent v")
    case None
    then show ?thesis 
      by (simp add: follow_psimps)
  next
    case (Some u)
    have one_step: "walk_betw { {x, y} | x y. (follow_rel x y)} v [v, u] u"
      using Some
      by(fastforce intro!: edges_are_walks simp add: parent_eq_follow_rel)
    show ?thesis 
      using 1(2)[OF Some]
      by(auto simp add: follow_psimps[of v, simplified Some, simplified]
          intro: walk_transitive_3[OF _ one_step, simplified] one_step)
  qed
qed
  
lemma follow_valk_bet:
  "vwalk_bet {(y, x)| x y. follow_rel x y} v (follow v) (last (follow v)) \<or> 
   follow v = [v]"
proof(induction rule: follow.pinduct[OF follow_dom])
  case (1 v)
  show ?case 
  proof(cases "parent v")
    case None
    then show ?thesis 
      by (simp add: follow_psimps)
  next
    case (Some u)
    have one_step: "vwalk_bet { (y, x) | x y. (follow_rel x y)} v [v, u] u"
      using Some
      by(force intro!: edges_are_vwalk_bet simp add: parent_eq_follow_rel)
    show ?thesis 
      using 1(2)[OF Some] hd_of_vwalk_bet one_step
      by(force simp add: follow_psimps[of v, simplified Some, simplified])
  qed
qed

lemma follow_R_one_star:
  assumes "follow v = p1@[x]@p2"
  shows "(v, x) \<in> {(x, y) | x y. (follow_rel y x)}\<^sup>*"
  using assms
proof(induction arbitrary:  x p1 p2 rule: follow.pinduct[OF follow_dom])
  case (1 v x p1 p2)
  show ?case 
  proof(cases p1)
    case Nil
    hence "v = x"
      using "1.prems" follow_cons by auto
    then show ?thesis by simp
  next
    case (Cons a list)
    show ?thesis
    proof(cases "parent v")
      case None
      then show ?thesis 
        using 1(3)
        by(auto simp add: follow_psimps[of v] append_eq_Cons_conv Cons_eq_append_conv)
    next
      case (Some u)
      have "(u, x) \<in> {(x, y) | x y. (follow_rel y x)}\<^sup>*"
        using Some Cons 1(3)
        by(force intro!:  1(2)[of u list x p2]  simp add: follow_psimps[of v])
      moreover have "(v, u) \<in> {(x, y) | x y. (follow_rel y x)}\<^sup>*" 
        using Some by(auto simp add: parent_eq_follow_rel)
      ultimately show ?thesis by auto
    qed
  qed
qed

lemma follow_R_two_plus:
  assumes "follow v = p1@[x]@p2@[y]@p3"
  shows "(x, y) \<in> {(x, y) | x y. (follow_rel y x)}\<^sup>+"
  using assms
proof(induction arbitrary:  x p1 p2 p2 y rule: follow.pinduct[OF follow_dom])
  case (1 v)
  show ?case 
  proof(cases "parent v")
    case None
    then show ?thesis 
      using 1(3)
      by (simp add: follow_psimps)
  next
    case (Some u)
    show ?thesis
    proof(cases p1)
      case Nil
      hence "v = x"
        using "1.prems" follow_cons by auto
      moreover hence "(u, y) \<in> {(x, y) | x y. (follow_rel y x)}\<^sup>*"
        using 1(3) Some Nil 
        by(force intro!:  follow_R_one_star[of u "p2" y p3] simp add:  follow_psimps[of x])
      moreover have "(v, u)\<in> {(x, y) | x y. (follow_rel y x)}\<^sup>+" 
        by (simp add: Some parent_eq_follow_rel trancl.r_into_trancl)
      ultimately show ?thesis by simp
    next
      case (Cons a list)
      show ?thesis 
        using Cons 1(3) Some
        by(force intro!: 1(2)[OF Some, of list x p2 y] simp add:  follow_psimps[of v])
    qed
  qed
qed

lemma follow_distinct: "distinct (follow v)"
proof(rule ccontr, goal_cases)
  case 1
  then obtain p1 x p2 p3 where split: "follow v = p1@[x]@p2@[x]@p3"
    using not_distinct_decomp by blast
  hence "follow x = [x]@p2@[x]@p3" 
    by (simp add: follow_append)
  moreover have "follow x = [x]@p3"
    by (metis append.assoc append_Cons calculation follow_append)
  ultimately show False 
    by simp
qed

lemma follow_cons_3: "\<exists>l. follow v = v # l"
  by (metis follow_cons follow_nempty list.exhaust)

lemma follow_cons_3': obtains l where "follow v = v # l"
  by (metis follow_cons follow_nempty list.exhaust)

lemma follow_cons_4: "parent v = Some v' \<Longrightarrow> follow v = v # (follow v')"
  using follow_psimps
  by auto

lemma follow_pinduct:
  "(\<And>v. (\<And>x2. parent v = Some x2 \<Longrightarrow> P x2) \<Longrightarrow> P v) \<Longrightarrow> P a"
  by (metis follow.pinduct[OF follow_dom])

end

lemma follow_cong:
  assumes "parent par" "parent_spec.follow_dom par v"
  shows "\<lbrakk>(\<forall>v'\<in>set(parent_spec.follow par v). par v' = par' v'); parent par'\<rbrakk>
          \<Longrightarrow> parent_spec.follow par v = parent_spec.follow par' v"
  using assms(2)
proof(induction rule: parent_spec.follow.pinduct[OF assms(2)])
  case (1 v)
  then show ?case
  proof(cases "par v")
    case None
    then show ?thesis
      apply( simp add: parent.follow_psimps[OF 1(4)])
      by (metis (mono_tags, lifting) "1.hyps" "1.prems"(1) assms(1) list.set_intros(1) option.case_eq_if 
          parent_spec.follow.psimps)
  next
    case (Some a)
    have "\<forall>v\<in>set (parent_spec.follow par a). par v = par' v"
      by (simp add: "1.prems"(1) "1.prems"(3) Some assms(1) parent_spec.follow.psimps)
    moreover have "parent_spec.follow_dom par a"
      by (simp add: assms(1) parent.follow_dom)
    ultimately have "parent_spec.follow par a = parent_spec.follow par' a" 
      using 1
      using Some by blast
    moreover have "par' v = Some a"
      using "1.hyps" "1.prems"(1) Some assms(1) parent_spec.follow.psimps by fastforce
    ultimately show ?thesis
      using 1(4) Some
      by(auto simp add: parent.follow_psimps[OF assms(1)] parent.follow_psimps[OF 1(4)] )
  qed
qed

lemma v2_nin_ancestors:
  assumes "parent par" "\<forall>v''. par v'' \<noteq> Some v2" "v2 \<noteq> v"
  shows "\<forall>v'\<in>set(parent_spec.follow par v). v' \<noteq> v2"
  using assms
proof(induction v rule: parent_spec.follow.pinduct[OF parent.follow_dom[OF assms(1)]])
  case (1 v)
  show ?case
  proof(cases "par v")
    case None
    then show ?thesis
      using 1(5)
      by(simp add: parent.follow_psimps[OF 1(3)])
  next
    case (Some a)
    have "\<forall>v\<in>set (parent_spec.follow par a). v \<noteq> v2"
      using "1.IH" Some assms(1) assms(2) by blast
    then show ?thesis
      using "1.hyps" "1.prems"(3) Some assms(1) parent_spec.follow.psimps by fastforce
  qed    
qed

lemma ancestors_unaffected_1:
  assumes "parent par" "\<forall>v'\<in>set(parent_spec.follow par v). v' \<noteq> v2"
  and f': "f' = (f(v2 \<mapsto> v1))"
  shows "\<forall>v'\<in>set(parent_spec.follow par v). f v' = f' v'"
  using assms
proof(induction v rule: parent_spec.follow.pinduct[OF  parent.follow_dom[OF assms(1)]])
  case (1 v)
  show ?case
  proof(cases "par v")
    case None
    then show ?thesis
      using 1
      by( simp add: parent.follow_psimps[OF 1(3)])
  next
    case (Some a)
    then have "\<forall>v\<in>set (parent_spec.follow par a). f v = f' v"
      apply(intro 1)
      using 1(4)
      by (simp add: f' parent.follow_psimps[OF 1(3)])+
    then show ?thesis
      by (simp add: "1.prems"(2) "1.prems"(3))
  qed
qed

lemma no_children_not_in_follow:
  assumes "parent par" "\<forall>v''. par v'' \<noteq> Some v2" "v2 \<noteq> v"
  and par': "par' = (par(v2 \<mapsto> v1))"
  shows "\<forall>v'\<in>set(parent_spec.follow par v). par v' = par' v'"
  using assms
proof(induction  rule: parent_spec.follow.pinduct[OF parent.follow_dom[OF assms(1)]])
  case (1 v)
  show ?case
  proof(cases "par v")
    case None
    then show ?thesis
      using 1
      by( simp add: parent.follow_psimps[OF 1(3)])
  next
    case (Some a)
    have "\<forall>v\<in>set (parent_spec.follow par a). par v = par' v"
      using "1.IH" Some assms(1) assms(2) par' by blast
    then show ?thesis
      using "1.hyps" "1.prems"(3) Some assms(1) par' parent_spec.follow.psimps by fastforce
  qed    
qed

lemma wf_par':
  assumes wf: "parent_spec par" 
  and par': "par' = par(v2 := Some v1, v3 := Some v2)"
  and neq: "v1 \<noteq> v2" "v2 \<noteq> v3" "v1 \<noteq> v3"
  and no_ances: "\<forall>v. par v \<noteq> Some v2" "\<forall>v. par v \<noteq> Some v3"
  and no_par: "par v2 = None" "par v3 = None"
  shows "parent_spec par'" (is ?g1) "parent_spec (par(v2 := Some v1))" (is ?g2)
proof-
  have "(v2, v1) \<notin> {(x,y) | x y. (Some x = par y)}\<^sup>*"
    using neq(1) no_ances(1)
    apply clarsimp
    by (metis (mono_tags, lifting) converse_rtranclE mem_Collect_eq old.prod.case)
  then have wf_v2_v1: "wf (insert (v1, v2) {(x,y) | x y. (Some x = par y)})"
    using wf[unfolded parent_spec_def] by blast
  moreover have "{(x, y) |x y. Some x = (par(v2 \<mapsto> v1)) y} = (insert (v1, v2) {(x, y) |x y. Some x = par y})"
    using neq(1) no_par
    by auto
  ultimately show ?g2
    unfolding parent_spec_def
    by simp
  have "(v3, v2) \<notin> {(x,y) | x y. (Some x = par y)}\<^sup>*"
    using neq(2) no_ances(2)
    apply clarsimp
    by (metis (mono_tags, lifting) converse_rtranclE mem_Collect_eq old.prod.case)
  moreover have "(v3, v2) \<notin>  {(x, y). (x, v1) \<in> {(x,y) | x y. (Some x = par y)}\<^sup>* \<and> (v2, y) \<in> {(x,y) | x y. (Some x = par y)}\<^sup>*}"
    using neq(3) no_ances(2)
    apply clarsimp
    by (metis (mono_tags, lifting) converse_rtranclE mem_Collect_eq old.prod.case)
  ultimately have "(v3, v2) \<notin> (insert (v1, v2) {(x,y) | x y. (Some x = par y)})\<^sup>*"
    unfolding rtrancl_insert
    by simp
  then have "wf (insert (v2, v3) (insert (v1, v2) {(x,y) | x y. (Some x = par y)}))"
    apply(subst wf_insert)
    using wf_v2_v1
    by simp
  moreover have "{(x,y) | x y. (Some x = par' y)} = insert (v2, v3) (insert (v1, v2) {(x,y) | x y. (Some x = par y)})"
    using neq(1,2) no_par
    by(auto simp add: par')
  ultimately show ?g1
    unfolding parent_spec_def
    by simp
qed

lemma parent_specD:
  "parent_spec parent \<Longrightarrow> wf {(x, y) |x y. (Some x = parent y)}"
  and parent_specE:
  "parent_spec parent \<Longrightarrow> (wf {(x, y) |x y. (Some x = parent y)} \<Longrightarrow> P) \<Longrightarrow> P"
  and parent_specI:
  "wf {(x, y) |x y. (Some x = parent y)} \<Longrightarrow> parent_spec parent" for parent
  by(auto simp add: parent_spec_def)

lemma parent_follow_same:
   "parent p \<Longrightarrow> follow_impl p = follow p"
  by(auto intro!: ext simp add: parent.follow_dom parent_spec_i.follow_dom_impl_same)

interpretation mg_for_pg : multigraph_spec 
  where \<E> = G
  and fst = fst
  and snd = snd
  and create_edge = Pair
for G
  done

abbreviation "delta_plus \<equiv> mg_for_pg.delta_plus" 
abbreviation "delta_minus \<equiv> mg_for_pg.delta_minus"

notation delta_minus ("\<delta>\<^sup>- _ _")
notation delta_plus ("\<delta>\<^sup>+ _ _")

lemmas delta_minus_def = mg_for_pg.delta_minus_def
lemmas delta_plus_def = mg_for_pg.delta_plus_def

abbreviation "Delta_plus \<equiv> mg_for_pg.Delta_plus" 
abbreviation "Delta_minus \<equiv> mg_for_pg.Delta_minus"

notation Delta_minus ("\<Delta>\<^sup>- _ _")
notation Delta_plus ("\<Delta>\<^sup>+ _ _")

lemmas Delta_minus_def = mg_for_pg.Delta_minus_def
lemmas Delta_plus_def = mg_for_pg.Delta_plus_def

abbreviation "gamma_plus \<equiv> mg_for_pg.gamma_plus" 
abbreviation "gamma_minus \<equiv> mg_for_pg.gamma_minus"

notation gamma_minus ("\<gamma>\<^sup>- _ _")
notation gamma_plus ("\<gamma>\<^sup>+ _ _")

lemmas gamma_minus_def = mg_for_pg.gamma_minus_def
lemmas gamma_plus_def = mg_for_pg.gamma_plus_def
lemmas finite_gamma_minus = finite_gamma_minus[of _ fst snd]
lemmas finite_gamma_plus = finite_gamma_plus[of _ fst snd]

abbreviation "Gamma_plus \<equiv> mg_for_pg.Gamma_plus" 
abbreviation "Gamma_minus \<equiv> mg_for_pg.Gamma_minus"

notation Gamma_minus ("\<Gamma>\<^sup>- _ _")
notation Gamma_plus ("\<Gamma>\<^sup>+ _ _")

lemmas Gamma_minus_def = mg_for_pg.Gamma_minus_def
lemmas Gamma_plus_def = mg_for_pg.Gamma_plus_def

(*TODO MOVE*)
lemma acyc_rel_vwalk_bet: "acyclic G \<longleftrightarrow> (\<nexists> u p. vwalk_bet G u p u \<and> length p \<ge> 2)"
proof(rule, all \<open>rule ccontr\<close>, goal_cases)
  case 1
  then obtain u p where "vwalk_bet G u p u" "2 \<le> length p"
    by auto
  hence "(u, u) \<in> G\<^sup>+" 
    by(cases p rule: list_cases_betw)
      (auto intro!: exI[of _ "butlast (tl p)"] simp add: reachable1_vwalk_iff vwalk_bet_def)
  then show ?case 
    using 1(1)
    by(auto simp add: acyclic_def)
next
  case 2
  then obtain u where "(u, u) \<in> G\<^sup>+"
    by(auto simp add: acyclic_def)
  then obtain p where "Vwalk.vwalk G (u#p@[u])"
    by (auto simp add: reachable1_vwalk_iff)
  hence "vwalk_bet G u (u#p@[u]) u" "length (u#p@[u]) \<ge> 2"
    by(auto simp add: vwalk_bet_def)
  then show ?case
    using 2(1) by fast
qed

lemma cycle_rotate: 
 "\<lbrakk>vwalk_bet G u p u; v \<in> set p\<rbrakk> 
  \<Longrightarrow> \<exists> q. vwalk_bet G v q v \<and> length q = length p \<and> set p = set q
        \<and> set (edges_of_vwalk q) = set (edges_of_vwalk p)"
proof(goal_cases)
  case 1
  then obtain p1 p2 where p_split: "p = p1@[v]@p2"
    by (metis single_in_append split_list)
  have h1: "vwalk_bet G v (v # p2 @ tl p1 @ [v]) v" 
    if "vwalk_bet G u (p1 @ v # p2) u" "p = p1 @ v # p2" "p1 \<noteq> []"
    apply(rule  vwalk_bet_vertex_decompE[OF that(1) refl])
    using that(3) vwalk_bet_transitive by fastforce
   have h2: "(a, b) \<in> set (edges_of_vwalk (p1 @ [v]))"
    if "vwalk_bet G u (p1 @ [v]) u" "p1 \<noteq> []" "p = p1 @ [v]" 
       "(a, b) \<in> set (edges_of_vwalk (v # tl p1 @ [v]))"
     for a b
    using that
    by(auto simp add: vwalk_bet_def append_Cons[symmetric] simp del: append_Cons)
  have h3: "(a, b) \<in> set (edges_of_vwalk (v # tl p1 @ [v]))"
    if "vwalk_bet G u (p1 @ [v]) u" "p1 \<noteq> []"
       "(a, b) \<in> set (edges_of_vwalk (p1 @ [v]))"
     for a b
    using that
    by(auto simp add: vwalk_bet_def append_Cons[symmetric] simp del: append_Cons)
  have h4: "(a, b) \<in> set (edges_of_vwalk (p1 @ v # p2)) 
             \<longleftrightarrow> (a, b) \<in> set (edges_of_vwalk (v # p2 @ tl p1 @ [v]))"
    if "vwalk_bet G u (p1 @ v # p2) u" "p1 \<noteq> []" "p2 \<noteq> []" "p = p1 @ v # p2"  for a b
    using that
    by(cases p1, all \<open> cases p2 rule: rev_cases\<close>)
      (auto simp add: edges_of_vwalk_append_3 append_Cons[symmetric] vwalk_bet_def 
            simp del: append_Cons)
  have h5: "\<lbrakk>vwalk_bet G u (p1 @ [v]) u; x \<in> set p1; x \<notin> set (tl p1)\<rbrakk> \<Longrightarrow> x = v" for x
    by(cases p1)
      (auto simp add:  append_Cons[symmetric] vwalk_bet_def 
            simp del: append_Cons)
  have h6: "\<lbrakk>vwalk_bet G u (p1 @ v # p2) u; x \<in> set p1; x \<noteq> v; x \<notin> set (tl p1)\<rbrakk> \<Longrightarrow> x \<in> set p2"
    for x
    by(cases p1)
      (auto simp add: append_Cons[symmetric] vwalk_bet_def simp del: append_Cons)
  have h7: "vwalk_bet G u (v # p2) u \<Longrightarrow> vwalk_bet G v (v # p2) v"
    using hd_of_vwalk_bet' by fastforce
  show ?case
    using 1(1) hd_of_vwalk_bet'  p_split h1 h2 h3 h4 
    apply(cases "p1 = []")
    apply(all \<open>cases "p2 = []"\<close>)
    by(auto intro!: exI[of _ "if p1 = [] \<and> p2 = [] then [v]
                               else if p1 = [] then p
                               else v#p2@tl p1@[v]"]
           simp add: vwalk_bet_in_vertices vwalk_bet_reflexive_cong 
               dest: vwalk_bet_snoc Vwalk.list_set_tl
             intro: h5 h6 h7)
qed

lemma in_edges_of_vwalkE:
  "\<lbrakk>(y, x) \<in> set (edges_of_vwalk xs); \<And> xs1 xs2. xs = xs1@[y,x]@xs2 \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (meson edges_in_vwalk_split)

lemma v_in_edge_in_vwalk': 
  assumes "(u, v) \<in> set (edges_of_vwalk p)"
  shows "u \<in> set (butlast p)" "v \<in> set (tl p)"
  using assms
  by (induction p rule: edges_of_vwalk.induct) auto

lemma edges_of_vwalk_double_Cons:
  "edges_of_vwalk (xs@[x,y]@ys) = edges_of_vwalk (xs@[x]) @[(x,y)]@edges_of_vwalk (y#ys)"
  using  edges_of_vwalk_append_2 [of "y#ys" "xs@[x]"]
  by (auto simp add: edges_of_vwalk_append_two_vertices)

lemma distinct_edge_one_known_other_fixed1:
  "\<lbrakk>distinct xs; (y, x) \<in> set (edges_of_vwalk xs); (y', x) \<in> set (edges_of_vwalk xs)\<rbrakk>  \<Longrightarrow> y = y'" 
proof(goal_cases)
  case 1
  note one = this
  obtain xs1 xs2 where xs1xs2: "xs = xs1@[y,x]@xs2" 
    using "1"(2) edges_in_vwalk_split by fastforce
  obtain xs1' xs2' where xs1'xs2': "xs = xs1'@[y',x]@xs2'" 
    using "1"(3) edges_in_vwalk_split by fastforce
  have "(y', x) \<in> set (edges_of_vwalk (xs1@[y])) \<Longrightarrow> False"
  proof(goal_cases)
    case 1
    hence "x \<in> set (xs1@[y])" 
      using v_in_edge_in_vwalk(2) by force
    thus False
      using one(1) xs1xs2 by auto
  qed
  moreover have "(y', x) \<in> set (edges_of_vwalk (x#xs2)) \<Longrightarrow> False"
  proof(goal_cases)
    case 1
    hence "x \<in> set xs2" 
      using  v_in_edge_in_vwalk' by force
    thus False
      using one(1) xs1xs2 by auto
  qed
  ultimately show "y = y'"
    using one(3) by(auto simp add: xs1xs2 edges_of_vwalk_double_Cons[simplified])
qed

lemma distinct_edge_one_known_other_fixed2:
  "\<lbrakk>distinct xs; (y, x) \<in> set (edges_of_vwalk xs); (y, x') \<in> set (edges_of_vwalk xs)\<rbrakk>  \<Longrightarrow> x = x'" 
proof(goal_cases)
  case 1
  note one = this
  obtain xs1 xs2 where xs1xs2: "xs = xs1@[y,x]@xs2" 
    using "1"(2) edges_in_vwalk_split by fastforce
  obtain xs1' xs2' where xs1'xs2': "xs = xs1'@[y,x']@xs2'" 
    using "1"(3) edges_in_vwalk_split by fastforce
  have "(y, x') \<in> set (edges_of_vwalk (xs1@[y])) \<Longrightarrow> False"
  proof(goal_cases)
    case 1
    hence "y \<in> set xs1" 
      using butlast_snoc v_in_edge_in_vwalk'(1) by force
    thus False
      using one(1) xs1xs2 by auto
  qed
  moreover have "(y, x') \<in> set (edges_of_vwalk (x#xs2)) \<Longrightarrow> False"
  proof(goal_cases)
    case 1
    hence "x' \<in> set xs2" 
      using v_in_edge_in_vwalk'(2) by fastforce
    thus False
      using "1" one(1) v_in_edge_in_vwalk(1) xs1xs2 by fastforce
  qed
  ultimately show "x = x'"
    using one(3) by(auto simp add: xs1xs2 edges_of_vwalk_double_Cons[simplified])
qed

lemma vwalk_bet3:
  "vwalk_bet G u (u' # v # vs) b \<longleftrightarrow> ((u,v) \<in> G \<and> vwalk_bet G v (v # vs) b \<and> u = u')"
  by(auto simp: vwalk_bet_def)

lemma cycle_distinct_cycle:
  "\<lbrakk>vwalk_bet G u p u; length p \<ge> 2\<rbrakk> \<Longrightarrow> \<exists> q. vwalk_bet G u (u#q) u \<and>  distinct q \<and> length q \<ge> 1"
proof(cases p rule: list_cases3, goal_cases)
  case (3 x y xs)
  obtain q where "vwalk_bet G y q u" "distinct q"
    apply(rule distinct_vwalk_betE[OF  vwalk_bet_to_distinct_is_distinct_vwalk_bet, of G y "y#xs" u]) 
    using 3(1) split_vwalk vwalk_bet2[of G x y xs] vwalk_bet_transitive_2 
    by (fastforce simp add: 3(3))+
  then show ?case 
    using 3 vwalk_bet3[of G u x y xs] hd_of_vwalk_bet
    by(fastforce intro!: exI[of _ q])
qed auto

lemma vwalk_add_edge_right: 
  "\<lbrakk>(a, x) \<in> G; vwalk_bet G u (vs @ [a]) a; b = x\<rbrakk> \<Longrightarrow> vwalk_bet G u (vs @ [a, x]) x"
  by (metis butlast_snoc edge_iff_vwalk_bet vwalk_bet_transitive_2)

lemma vwalk_rev_bet3:
  "vwalk_bet G u (vs@[a,b]) x \<longleftrightarrow> ((a,b) \<in> G \<and> vwalk_bet G u (vs@[a]) a \<and> b = x)"
  using split_vwalk last_of_vwalk_bet 
  by (fastforce simp add: vwalk_bet_pref intro: vwalk_add_edge_right)

lemma edge_iff_vwalk_bet': 
  "vwalk_bet E u' [u, v] v' \<longleftrightarrow> ((u, v) \<in> E \<and> u = u' \<and> v = v')"
  by (auto simp: edges_are_vwalk_bet vwalk_bet_def dVsI)


lemma vwalk_bet_unused_vertex:
  "\<lbrakk>vwalk_bet G u p v; x \<notin> set p; length p \<ge> 2 \<rbrakk> \<Longrightarrow> vwalk_bet (G - \<delta>\<^sup>+ G x - \<delta>\<^sup>- G x) u p v"
  by(rule vwalk_bet_subset[OF vwalk_bet_in_its_own_edges])
    (auto dest: vwalk_bet_edges_in_edges  v_in_edge_in_vwalk simp add: delta_plus_def delta_minus_def)
 
lemma acyclic_vert_replace:
  assumes"y \<notin> dVs G" "\<nexists> u p. vwalk_bet G u p u \<and> length p \<ge> 2"
  and G'_def: "G' = G - \<delta>\<^sup>+ G x - \<delta>\<^sup>- G x 
                    \<union> {(yy, y) | yy. yy \<in> \<gamma>\<^sup>- G x}
                    \<union> {(y, yy) | yy. yy \<in> \<gamma>\<^sup>+ G x}"
shows "\<nexists> u p. vwalk_bet G' u p u \<and> length p \<ge> 2"
proof(rule ccontr, goal_cases)
  case 1
  note one = this
  then obtain u p where up: "vwalk_bet G' u p u" "2 \<le> length p"
    by auto
  then obtain pp where pp: "vwalk_bet G' u (u # pp) u" "distinct pp" "length pp \<ge> 1"
    using cycle_distinct_cycle[OF up] by auto
   define p where "p = u#pp"
  have up: "vwalk_bet G' u p u" "length p \<ge> 2" "distinct (tl p)"
    using up pp by (auto simp add: p_def )
  hence  edges_p_in_G': "set (edges_of_vwalk p) \<subseteq> G'" 
    using vwalk_bet_edges_in_edges by fastforce

  show ?case
  proof(cases "y  \<notin> set p")
    case True
    hence "set (edges_of_vwalk p) \<subseteq> G"
      using edges_p_in_G' assms(3) 
      by(auto simp add: G'_def dest!: set_mp dest: v_in_edge_in_vwalk) 
    hence  "vwalk_bet G u p u"
      using up(1,2) by(auto intro: vwalk_bet_subset[OF vwalk_bet_in_its_own_edges])
    then show ?thesis 
      using assms(2) up(2) by blast
  next
    case False
    note false = this
    obtain p' where p': "vwalk_bet G' y p' y" "length p' \<ge> 2"
      using  cycle_rotate up(1)
      by (metis False up(2))
    show ?thesis
  proof(cases "length p' = 2")
    case True
    hence "p' = [y,y]" 
      using p' last_of_vwalk_bet 
      by(cases p' rule: list_cases4) (fastforce simp add: vwalk_bet3)+
    hence "(y,y) \<in> G'"
      using p'(1) by auto
    hence "(x,x) \<in> G"
      using assms(1) by(auto simp add: G'_def gamma_minus_def gamma_plus_def)
    hence  "vwalk_bet G x [x,x] x" "length [x,x] \<ge> 2"
      by auto
    then show ?thesis 
      using assms(2) by blast
  next
    case False
     have snd_gamma_plus: "hd (tl p') \<in> \<gamma>\<^sup>+ G x" 
      using p' assms(1-3) 
      by(cases p' rule: list_cases3)
        (auto simp add: G'_def gamma_plus_def gamma_minus_def vwalk_bet3 elim!: in_dVsE(2))
    have "vwalk_bet G' (hd (tl p')) (tl p') y" 
      using p' False
      by(cases p' rule: list_cases_both_sides)
        (auto simp add: vwalk_bet_def intro: append_vwalk_pref vwalk_ConsD)
    then obtain p'' where p'': "vwalk_bet G' (hd (tl p')) p'' y"  "distinct p''" 
      by (meson distinct_vwalk_bet_def vwalk_bet_to_distinct_is_distinct_vwalk_bet)
    have snd_p'_neq_y:"hd (tl p') \<noteq> y" 
      using assms(1) dVsI'(2)  snd_gamma_plus by(auto simp add: gamma_plus_def) 
    have length_p'': "length p'' \<ge> 2 "
      using p'' snd_p'_neq_y by(cases p'' rule: rev_cases3)(auto simp add: vwalk_bet_def) 
    have snd_to_last_gamma_minus: "last (butlast p'') \<in> \<gamma>\<^sup>- G x" 
      using p'' assms(1-2) length_p''
      by(cases p'' rule: rev_cases3)
        (auto simp add: G'_def gamma_plus_def gamma_minus_def vwalk_rev_bet3 butlast_append)
    have last_p'': "last p'' = y"
      using p''(1) by fastforce
    have vwalk_bet_butlast_p'':"vwalk_bet G' (hd (tl p')) (butlast p'') (last (butlast p''))"
    proof(rule vwalk_bet_vertex_decompE[OF p''(1), of "butlast p''" y Nil],
           rule append_butlast_last_id[of p'', simplified last_p'', symmetric], goal_cases)
      case 1
      thus ?case
        using p''(1) by auto
    next
      case (2 q r)
      thus ?case
      using p'' assms(1-2) length_p'' 
      by(cases p'' rule: rev_cases3)
        (auto simp add: vwalk_rev_bet3 intro: vwalk_bet_props)
  qed
  have "vwalk_bet G x (x#butlast p''@[x]) x"
  proof(cases "length (butlast p'') \<ge> 2")
    case True
    have "vwalk_bet (G' - \<delta>\<^sup>+ G' y - \<delta>\<^sup>- G' y) (hd (tl p')) (butlast p'') (last (butlast p''))"
      apply(rule vwalk_bet_unused_vertex[OF vwalk_bet_butlast_p'', of y])
      using length_p'' p''(1,2)   last_p'' True
      by(all \<open>cases p'' rule: rev_cases3\<close>)(auto simp add: butlast_append)
    hence "vwalk_bet G (hd (tl p')) (butlast p'') (last (butlast p''))"
      by(auto simp add: G'_def delta_plus_def delta_minus_def intro!: vwalk_bet_subset[of _ _ _  _ G])
    then show ?thesis
      using snd_gamma_plus snd_to_last_gamma_minus
      by(auto simp add: gamma_plus_def gamma_minus_def
                        Vwalk.vwalkI vwalk_append_single vwalk_bet_def)
  next
    case False
    then show ?thesis 
      using length_p'' snd_gamma_plus snd_to_last_gamma_minus p''(1)
      by(cases p'' rule: list_cases4)
        (auto simp add: gamma_plus_def gamma_minus_def dest: hd_of_vwalk_bet')
  qed
  moreover have "length (x # butlast p'' @ [x]) \<ge> 2"
    by auto
  ultimately show False
    using assms(2) by blast
  qed
 qed
qed

lemma edges_are_vwalk_bet_length2:
  assumes "(v, w) \<in> E"
  shows "vwalk_bet E v [v, w] w" "length [v, w] \<ge> 2"
  unfolding vwalk_bet_def
  using assms
  by (simp add: dVsI)+

lemma acyclic_squeeze_two_in:
  assumes "y \<noteq> z"  "y \<notin> dVs G"  "z \<notin> dVs G - {x}"
          "\<nexists> u p. vwalk_bet G u p u \<and> length p \<ge> 2"
  and G'_def: "G' = G - \<delta>\<^sup>+ G x - \<delta>\<^sup>- G x 
                    \<union> {(yy, y) | yy. yy \<in> \<gamma>\<^sup>- G x}
                    \<union> {(z, y) | y. y \<in> \<gamma>\<^sup>+ G x}
                    \<union> {(y, z)}"
  shows "\<nexists> u p. vwalk_bet G' u p u \<and> length p \<ge> 2"
proof(rule ccontr, goal_cases)
  case 1
  note one = this
  then obtain u p where up: "vwalk_bet G' u p u" "2 \<le> length p"
    by auto
  then obtain pp where pp: "vwalk_bet G' u (u # pp) u" "distinct pp" "length pp \<ge> 1"
    using cycle_distinct_cycle[OF up] by auto
  have old_vwalk_False: "\<lbrakk>vwalk_bet G u p u; length p \<ge> 2\<rbrakk> \<Longrightarrow> False" for u p
    using assms(4) by auto
   define p where "p = u#pp"
  have up: "vwalk_bet G' u p u" "length p \<ge> 2" "distinct (tl p)"
    using up pp by (auto simp add: p_def )
  hence  edges_p_in_G': "set (edges_of_vwalk p) \<subseteq> G'" 
    using vwalk_bet_edges_in_edges by fastforce
  have A: "y \<in> set p \<Longrightarrow> (y, z) \<in> set (edges_of_vwalk p)"
  proof(goal_cases)
    case 1
    then obtain p1 p2 where "p = p1@[y]@p2"
      by (metis single_in_append split_list_last)
    moreover hence "(y, if p2 = [] then hd (tl (p1@[y])) else hd p2) \<in> set (edges_of_vwalk p)" 
      using up(1,2) vwalk_edges_of_vwalk_refl[OF up(2)]
      by(cases p2, all \<open>cases p1\<close>)
        (auto elim: vwalk_ConsE[OF vwalk_in_its_own_edges] 
             intro: vwalk_snoc_edge_2[of _ "u # _"] 
          simp add: edges_of_vwalk_double_Cons[of "_ # _", simplified]  vwalk_bet_def)
    moreover hence "(y, if p2 = [] then hd (tl (p1@[y])) else hd p2) \<in> G'" 
      using up(1) vwalk_ball_edges by(auto simp add: vwalk_bet_def)
    moreover hence "(if p2 = [] then hd (tl (p1@[y])) else hd p2) = z"
      using assms(1,2)
     by(auto simp add: G'_def gamma_minus_def gamma_plus_def)
   ultimately show ?case 
     by simp
 qed
  have B: "z \<in> set p \<Longrightarrow> (y, z) \<in> set (edges_of_vwalk p)"
  proof(goal_cases)
    case 1
    then obtain p1 p2 where "p = p1@[z]@p2"
      by (metis single_in_append split_list_last)
    moreover hence "(if p1 = [] then last (butlast (z#p2)) else last p1, z) \<in> set (edges_of_vwalk p)" 
      using up(1,2) 
      apply(cases p2 rule: rev_cases , all \<open>cases p1 rule: rev_cases\<close>)
      using append_vwalk_suff vwalk_2 vwalk_edges_of_vwalk_refl[OF up(2)] 
      by (auto simp add: edges_of_vwalk_append_two_vertices)
         (force  elim: vwalk_ConsE[OF vwalk_in_its_own_edges]
               intro!: vwalk_append_edge[of  _ _ "[z]", simplified] 
             simp add: vwalk_bet_def)+
    moreover hence "(if p1 = [] then last (butlast (z#p2)) else last p1, z) \<in> G'" 
      using up(1) vwalk_ball_edges by (metis vwalk_bet_def)
    moreover hence "(if p1 = [] then last (butlast (z#p2)) else last p1) = y"
      using assms(1,3,4) calculation(1,2)
      by(auto simp add: G'_def gamma_minus_def gamma_plus_def delta_plus_def delta_minus_def
                    dest: edges_are_vwalk_bet_length2[of _ _ G])
   ultimately show ?case 
     by simp
 qed
  show ?case
  proof(cases "{y, z} \<inter> set p = {}")
    case True
    hence "set (edges_of_vwalk p) \<subseteq> G"
      using edges_p_in_G' assms(3) 
      by(auto simp add: G'_def dest!: set_mp dest: v_in_edge_in_vwalk) 
    hence  "vwalk_bet G u p u"
      using up(1,2) by(auto intro: vwalk_bet_subset[OF vwalk_bet_in_its_own_edges])
    then show ?thesis 
      using assms(4) up(2) by blast
  next
    case False
    hence yz_in_edgs:"(y, z) \<in> set (edges_of_vwalk p)"
      using A B by blast
    obtain p' where p': "vwalk_bet G' z p' y" 
      using  cycle_rotate in_set_conv_decomp split_vwalk up(1)
          v_in_edge_in_vwalk(1,2)[OF yz_in_edgs]
      by metis
    then obtain p' where p': "vwalk_bet G' z p' y"  "distinct p'"
      by (meson distinct_vwalk_betE vwalk_bet_to_distinct_is_distinct_vwalk_bet)
    moreover hence "set (edges_of_vwalk p') \<subseteq> G' - {(y, z)}" 
      using assms(1) v_in_edge_in_vwalk'(2)[of y z p']
            vwalk_betE[of G' z p' y] vwalk_bet_edges_in_edges[of G' z p' y] 
      by force
    ultimately have zy_path: "vwalk_bet (G' - {(y, z)}) z p' y" "2 \<le> length p'"
      using assms(1)
      by(auto intro!: unused_edge_vwalk_bet vwalk_bet_diff_verts_length_geq_2)
    have length_p': "length p' \<ge> 3"
      using zy_path assms(1-4)
      by(cases p' rule: list_cases4)
        (auto simp add: G'_def edge_iff_vwalk_bet' gamma_plus_def gamma_minus_def
                  dest: edges_are_vwalk_bet_length2[of _ _ G])
    have snd_gamma_plus: "hd (tl p') \<in> \<gamma>\<^sup>+ G x" 
      using zy_path assms(1-4) 
      by(cases p' rule: list_cases3)
        (auto simp add: G'_def gamma_plus_def gamma_minus_def vwalk_bet3 
                 elim!: in_dVsE(2)
                 intro: old_vwalk_False[OF edges_are_vwalk_bet_length2])
    moreover have snd_to_last_gamma_minus: "last (butlast p') \<in> \<gamma>\<^sup>- G x" 
      using zy_path assms(1-4) 
      by(cases p' rule: rev_cases3)
        (auto simp add: G'_def gamma_plus_def gamma_minus_def vwalk_rev_bet3 butlast_append 
                 elim!: in_dVsE(2))
    have "vwalk_bet (G' - {(y, z)}) (hd (tl p')) (butlast (tl p')) (last (butlast p'))"
      using zy_path length_p'
      by(cases p' rule: list_cases_both_sides)
        (auto simp add: vwalk_bet_def intro: append_vwalk_pref vwalk_ConsD)
    moreover hence "set (edges_of_vwalk (butlast (tl p'))) \<subseteq> G" 
      using length_p'  p'(2) vwalk_bet_nonempty_vwalk[OF p'(1)] 
      by (cases p' rule: list_cases_both_sides)
         (auto dest!: vwalk_bet_edges_in_edges set_mp 
                dest: v_in_edge_in_vwalk 
            simp add: G'_def gamma_plus_def gamma_minus_def)
    ultimately have "vwalk_bet G (hd (tl p')) (butlast (tl p')) (last (butlast p'))" 
    proof(cases "length p' = 3", goal_cases)
      case 1
      hence "last (butlast p') = hd (tl p')" "butlast (tl p') = [hd (tl p')]"
        using  length_p' 
        by(cases p' rule: list_cases_both_sides, all \<open> cases p' rule: list_cases4\<close>)
          (auto simp add: hd_last_same)
      then show ?thesis 
        using snd_gamma_plus
        by (auto simp add: vwalk_bet_def gamma_plus_def)   
    next
      case 2
      then show ?thesis 
        using length_p' 
        by(auto intro!: vwalk_bet_subset[OF vwalk_bet_in_its_own_edges, of  _ _ _ _ G])
    qed
    hence "vwalk_bet G x (x#butlast (tl p')@[x]) x" 
      using snd_gamma_plus snd_to_last_gamma_minus
      by(auto simp add: gamma_plus_def gamma_minus_def vwalk_bet_def Vwalk.vwalkI vwalk_append_single)
    thus False 
      using assms(4) by fastforce
  qed
qed

lemma acyclic_squeeze_in:
  assumes "x \<in> dVs G" "distinct xs" "xs \<noteq> []" "set xs \<inter> dVs G \<subseteq> {x}"
          "\<nexists> u p. vwalk_bet G u p u \<and> length p \<ge> 2"
  and G'_def: "G' = G - \<delta>\<^sup>+ G x - \<delta>\<^sup>- G x 
                    \<union> {(y, hd xs) | y. y \<in> \<gamma>\<^sup>- G x}
                    \<union> {(last xs, y) | y. y \<in> \<gamma>\<^sup>+ G x}
                    \<union> (set (edges_of_vwalk xs))"
shows "\<nexists> u p. vwalk_bet G' u p u \<and> length p \<ge> 2"
  using assms
proof(induction xs arbitrary: G' x G)
  case (Cons y xs)
  note G'_def = Cons(7)
  from Cons show ?case 
  proof(cases xs, goal_cases)
    case 1
    show ?thesis 
    proof(cases "x = y")
      case True
      have "G' = G"
        by(auto simp add: G'_def 1 True delta_plus_def delta_minus_def gamma_plus_def gamma_minus_def)
      then show ?thesis 
        by (simp add: Cons.prems(5))
    next
      case False
      show ?thesis 
        apply(rule acyclic_vert_replace[of y G _ x])
        using "1"(8) Cons.prems(4,5,6) False by auto
    qed
  next
    case (2 z rest)
    note two = this
    define G'' where 
     "G'' =  G - \<delta>\<^sup>+ G x - \<delta>\<^sup>- G x \<union> {(ya, hd xs) |ya. ya \<in> \<gamma>\<^sup>- G x} \<union>
                                  {(last xs, ya) |ya. ya \<in> \<gamma>\<^sup>+ G x} \<union> set (edges_of_vwalk xs)"
    have G''_is_also: 
    "G' = G'' - \<delta>\<^sup>+ G'' z - \<delta>\<^sup>- G'' z 
               \<union> {(yy, y) |yy. yy \<in> \<gamma>\<^sup>- G'' z} \<union> {(z, y) |y. y \<in> \<gamma>\<^sup>+ G'' z} \<union> {(y, z)}"
    proof(cases "x = z")
      case True
      have helper1:"\<lbrakk>x = z; (a, b) \<in> G'; (a, b) \<notin> G''; a \<noteq> z; a \<notin> \<gamma>\<^sup>- G'' z\<rbrakk> \<Longrightarrow> b = z" for a b
        by(auto simp add: G'_def G''_def two(8) delta_plus_def delta_minus_def, 
           auto simp add: gamma_plus_def gamma_minus_def)
      have helper2: "\<lbrakk>x = z; (a, b) \<in> G'; (a, b) \<notin> G''; a \<noteq> z; a \<notin> \<gamma>\<^sup>- G'' z\<rbrakk> \<Longrightarrow> a = y" for a b
        by(auto simp add: G'_def G''_def two(8) delta_plus_def delta_minus_def, 
           auto simp add: gamma_plus_def gamma_minus_def)
      show ?thesis 
        using True 
          using  two(3,6)
          by(auto, auto intro: helper2 helper1)
            (auto simp add: G'_def G''_def two(8) delta_plus_def
                            delta_minus_def gamma_plus_def gamma_minus_def  
                     dest:  edges_are_vwalk_bet_length2 v_in_edge_in_vwalk')
      next
        case False
        thus ?thesis

      using two(3,5)
      by(auto simp add: G''_def  delta_plus_def delta_minus_def gamma_plus_def gamma_minus_def
                        G'_def two(8) 
                  dest: v_in_edge_in_vwalk')
  qed
    have no_cycl_G'': "\<nexists>u p. vwalk_bet G'' u p u \<and> 2 \<le> length p"
    proof(rule Cons(1)[OF _ _ _ _ _ G''_def], goal_cases)
      case 2
      show ?case
        using two(3) by auto
    next
      case 4
      show ?case
         using two(5) by auto
     qed (auto simp add: two(2,6,8))
     have y_not_in_G'': "y \<notin> dVs G''"
         using two(3,5,6,8)
         by(cases "x = y")
           (auto simp add: G''_def delta_plus_def delta_minus_def gamma_plus_def gamma_minus_def 
                    elim!: in_dVsE
                     dest: edges_are_vwalk_bet_length2 v_in_edge_in_vwalk' v_in_edge_in_vwalk)
    show ?thesis 
      using two(3,8)
      by (intro acyclic_squeeze_two_in[OF _ y_not_in_G'' _ no_cycl_G'' G''_is_also]) auto
  qed
next
  case Nil
  thus ?case
    by blast
qed

lemma wf_squeeze_in:
  assumes "finite G" "wf G"
          "x \<in> dVs G" "distinct xs" "xs \<noteq> []" "set xs \<inter> dVs G \<subseteq> {x}"
  and G'_def: "G' = G - \<delta>\<^sup>+ G x - \<delta>\<^sup>- G x 
                    \<union> {(y, hd xs) | y. y \<in> \<gamma>\<^sup>- G x}
                    \<union> {(last xs, y) | y. y \<in> \<gamma>\<^sup>+ G x}
                    \<union> (set (edges_of_vwalk xs))"
  shows "wf G'"
proof(rule finite_acyclic_wf)
  show "finite G'"
    using assms(1)
    by(auto intro!: finite_imageI finite_gamma_minus finite_gamma_plus 
          simp add: G'_def   setcompr_eq_image)
  have "acyclic G"
    by (simp add: assms(2) wf_acyclic)
  thus "acyclic G'"
    using acyclic_squeeze_in[OF assms(3-6)]
    by(auto simp add: acyc_rel_vwalk_bet G'_def)
qed

lemma vwalk_bet_3_verts:
  "\<lbrakk>(a, b) \<in> G; (b, c) \<in> G\<rbrakk> \<Longrightarrow> vwalk_bet G a [a,b,c] c"
  by auto

lemmas vwalk_bet_if_edges_in =
   vwalk_bet_subset[OF vwalk_bet_in_its_own_edges]

lemma vwalk_another_edge_in_front:
 "\<lbrakk>(y, x) \<in> G;  vwalk_bet G x q' z\<rbrakk> \<Longrightarrow> vwalk_bet G y (y # q') z" 
  using hd_of_vwalk_bet by fastforce

lemma acyclic_contract_edge:
  assumes  "z \<notin> dVs G - {x, y}"
          "\<nexists> u p. vwalk_bet G u p u \<and> length p \<ge> 2"
            "\<And> x y z. \<lbrakk>(y, x)\<in> G; (z, x) \<in> G\<rbrakk> \<Longrightarrow> y = z" "(x, y) \<in> G"
  and G'_def: "G' = G - \<delta>\<^sup>+ G x - \<delta>\<^sup>- G x - \<delta>\<^sup>+ G y - \<delta>\<^sup>- G y
                    \<union> {(z, yy) | yy. yy \<in> \<Gamma>\<^sup>+ G {x, y}}
                    \<union> {(yy, z) | yy. yy \<in> \<Gamma>\<^sup>- G {x, y}}"
shows "\<nexists> u p. vwalk_bet G' u p u \<and> length p \<ge> 2"
and "\<And> x y z. \<lbrakk>(y, x)\<in> G'; (z, x) \<in> G'\<rbrakk> \<Longrightarrow> y = z"
proof(rule ccontr, goal_cases)
  case 1
  then obtain u p where "vwalk_bet G' u p u" "2 \<le> length p" by auto
  then obtain q where uq: "vwalk_bet G' u (u#q) u" "distinct q" "length q \<ge> 1" 
    using cycle_distinct_cycle by force
  have  uq_in_G': "set (edges_of_vwalk (u#q)) \<subseteq> G'"
    by (meson uq(1) vwalk_bet_edges_in_edges)
  have z_not_there_in_es_G:
      "\<lbrakk>set (edges_of_vwalk p) \<subseteq> G'; z \<notin> set p\<rbrakk>\<Longrightarrow> set (edges_of_vwalk p) \<subseteq> G" for p
      by(auto simp add: G'_def Delta_plus_def Delta_minus_def 
                             Gamma_plus_def Gamma_minus_def delta_plus_def delta_minus_def
                dest: v_in_edge_in_vwalk(1,2))
  show ?case
  proof(cases "z \<in> set (u#q)")
    case False
    hence "set (edges_of_vwalk (u#q)) \<subseteq> G"
      using uq_in_G' z_not_there_in_es_G by simp
    hence "vwalk_bet G u (u#q) u" "length (u#q) \<ge> 2" 
      using uq(3)
      by(auto intro!: vwalk_bet_subset[OF  vwalk_bet_in_its_own_edges, OF uq(1)])
    thus False
      using assms(2) by blast
  next
    case True
    then obtain q1 q2 where q_split: "u#q = q1@[z]@q2"
      by (metis in_set_conv_decomp single_in_append)
    have q1_edges: "set (edges_of_vwalk q1) \<subseteq> set (edges_of_vwalk (u#q))" 
      using q_split
      by(cases q1) 
        (auto  simp add:  edges_of_vwalk_append_3[of "u # _" "z#q2", simplified])
    have q2_edges: "set (edges_of_vwalk q2) \<subseteq> set (edges_of_vwalk (u#q))" 
      using q_split edges_of_vwalk_append_subset[of "_ # _" "q1@[z]"]
      by(cases q2)  auto
    have G_no_self_loop: "(a, a) \<in> G \<Longrightarrow> False" for  a 
      by (meson assms(2) edges_are_vwalk_bet edges_are_vwalk_bet_length2(2))
    have G_cycle: "\<lbrakk>vwalk_bet G u p u; 2 \<le> length p\<rbrakk> \<Longrightarrow> False" for u p 
      using assms(2) by auto
    have "\<exists> q'. vwalk_bet G' z (z#q'@[z]) z \<and> z\<notin> set q' \<and> distinct q'"
    proof(cases q1)
      case Nil
      have helper:"\<lbrakk>vwalk_bet G' z (z # q2) z; distinct q2; Suc 0 \<le> length q2; q1 = []; u = z;
             q = q2; z \<in> set (butlast q2)\<rbrakk> \<Longrightarrow> False"
        using uq(2)
        by(cases q2 rule: rev_cases)(auto dest!: last_of_vwalk_bet')
      from Nil show ?thesis 
        using uq q_split Suc_le_eq vwalk_bet_props
        by(force intro!: exI[of _ "butlast q2"] helper distinct_butlast)
    next
      case (Cons a list)
      from Cons show ?thesis 
        using uq q_split
        by(auto intro!: exI[of _ "q2@tl q1"] 
                        vwalk_bet_transitive[of G' z "z#q2" a "a#list@[z]", simplified]
                        vwalk_bet_suff[of G' a "a#list" z q2]
                        vwalk_bet_pref[of G' a "a#list" z q2, simplified])
    qed
    then obtain q' where q'_vwalk: "vwalk_bet G' z (z#q'@[z]) z" 
                  and z_not_in_q': "z\<notin> set q'"
                  and distinct_q': "distinct q'"
      by auto
    have  rotpath_in_G': "set (edges_of_vwalk (z#q'@[z])) \<subseteq> G'"
      by (meson q'_vwalk vwalk_bet_edges_in_edges)
    show ?thesis
      proof(cases q')
        case Nil
     have "(x, y) \<in> G"
      using rotpath_in_G' assms(1)
      by (auto simp add: Nil G'_def delta_plus_def delta_minus_def Gamma_plus_def Gamma_minus_def 
                   dest: G_no_self_loop)
    moreover have "(y, x) \<in> G"
      using rotpath_in_G' assms(1)
      by (auto simp add: Nil G'_def delta_plus_def delta_minus_def Gamma_plus_def Gamma_minus_def 
                   dest: G_no_self_loop)    
    ultimately have "vwalk_bet G x [x, y,x] x" 
      by(auto intro: vwalk_bet_3_verts)
    then show ?thesis 
      by(auto intro!: G_cycle[of x "[x,y,x]"])
  next
    case (Cons aa list)
    hence q'_neq_Nil: "q' \<noteq> []" by auto
    have q'_in_G:"set (edges_of_vwalk q') \<subseteq> G" 
      apply(rule z_not_there_in_es_G[OF _ z_not_in_q'])
      using q'_vwalk  q'_neq_Nil
      by(auto intro!: vwalk_bet_edges_in_edges[of _ "hd q'" _ "last q'"] 
                      vwalk_bet_prefix_is_vwalk_bet[of q' G' "hd q'" "[z]" z] 
            simp add: q'_neq_Nil
               dest!: vwalk_bet_suffix_is_vwalk_bet[of "q'@[z]" G' z "[z]" z, simplified])
    have  "hd q' \<in> \<gamma>\<^sup>+ G' z" "last q' \<in> \<gamma>\<^sup>- G' z"
      using gamma_plus_def local.Cons q'_vwalk uq(1) apply fastforce
      using q'_vwalk 
      by(auto simp add: gamma_minus_def 
                        append_butlast_last_cancel[OF q'_neq_Nil, symmetric] 
                        vwalk_rev_bet3[of _ _ "_ # _", simplified])
    hence  hd_q':"hd q' \<in> \<gamma>\<^sup>+ G y \<union> \<gamma>\<^sup>+ G x"  and last_q': "last q' \<in> \<gamma>\<^sup>- G y \<union> \<gamma>\<^sup>- G x"
      using assms(1)
      by(auto simp add: G'_def gamma_plus_def gamma_minus_def delta_plus_def delta_minus_def
                             Gamma_plus_def Gamma_minus_def)
    have vwalk_q'_G:"vwalk_bet G (hd q') q' (last q')" 
    proof(cases "length q' \<ge> 2")
      case True
      moreover hence "q' \<noteq> []" by auto
      ultimately show ?thesis
        using q'_vwalk 
        by(auto intro!: vwalk_bet_if_edges_in[OF _  _ q'_in_G, of G']
            vwalk_bet_prefix_is_vwalk_bet[of q' G' "hd q'" "[z]"] 
              dest!: vwalk_bet_cons)
    next
      case False
      then show ?thesis 
        using hd_q'
        by(auto simp add: Cons gamma_plus_def Suc_leI intro!: vwalk_bet_reflexive_cong)  
    qed
    have case1: False
      if asms: "hd q' \<in> \<gamma>\<^sup>+ G y" "last q' \<in> \<gamma>\<^sup>- G y"
    proof-
      have "vwalk_bet G y (y#q'@[y]) y"
        using asms   vwalk_q'_G
        by(auto intro!: vwalk_bet_transitive[of G y "y#q'" "last q'"
                                "[last q', y]" y, simplified] 
                        vwalk_another_edge_in_front[of y "hd q'" G q']
              simp add: gamma_minus_def  gamma_plus_def )
      thus False 
        using G_cycle by fastforce
    qed
    moreover  have case2: False
      if asms: "hd q' \<in> \<gamma>\<^sup>+ G x" "last q' \<in> \<gamma>\<^sup>- G x"
    proof-
      have "vwalk_bet G x (x#q'@[x]) x"
        using asms   vwalk_q'_G
        by(auto intro!: vwalk_bet_transitive[of G x "x#q'" "last q'"
                                "[last q', x]" x, simplified] 
                        vwalk_another_edge_in_front[of x "hd q'" G q']
              simp add: gamma_minus_def  gamma_plus_def )
      thus False 
        using G_cycle by fastforce
    qed
    moreover have case3: False
      if asms: "hd q' \<in> \<gamma>\<^sup>+ G x" "last q' \<in> \<gamma>\<^sup>- G y"  
    proof-
      have "last q' = x" 
        using assms(4) asms by(auto simp add: gamma_minus_def assms(3))
      hence "vwalk_bet G x (x#q') x"
        using asms  vwalk_q'_G
        by(auto simp add: gamma_minus_def  gamma_plus_def vwalk_another_edge_in_front)
      thus False
        using Cons
        by(auto intro!: G_cycle[of x "x#q'"])
    qed
    moreover have case4: False
      if asms: "hd q' \<in> \<gamma>\<^sup>+ G y" "last q' \<in> \<gamma>\<^sup>- G x"  
    proof-
      have "vwalk_bet G x (x#y#q'@[x]) x"
        using asms vwalk_q'_G
        by(auto intro!: vwalk_bet_transitive[of G y "y#q'" "last q'"
                                "[last q', x]" x, simplified] 
                        vwalk_another_edge_in_front[of y "hd q'" G q']
              simp add: assms(4) gamma_minus_def  gamma_plus_def )
      thus False
        by(auto intro!: G_cycle[of x "x#y#q'@[x]"])
    qed
    ultimately show False
      using hd_q' last_q' by blast
  qed
qed
next
  fix x y z
  assume "(y, x) \<in> G'" "(z, x) \<in> G'"
  thus "y = z"
    using assms(1,4)
    by(auto simp add: G'_def delta_plus_def delta_minus_def Gamma_plus_def Gamma_minus_def assms(3))
qed


lemma acyclic_contract:
  assumes "vwalk_bet G x xs y"  "distinct xs" "z \<notin> dVs G - set xs"
          "\<nexists> u p. vwalk_bet G u p u \<and> length p \<ge> 2"
           "\<And> x y z. \<lbrakk>(y, x)\<in> G; (z, x) \<in> G\<rbrakk> \<Longrightarrow> y = z"
  and G'_def: "G' = G - \<Union> {\<delta>\<^sup>+ G x | x. x \<in> set xs} - \<Union> {\<delta>\<^sup>- G x | x. x \<in> set xs}
                    \<union> {(z, y) | y. y \<in> \<Gamma>\<^sup>+ G (set xs)}
                    \<union> {(y, z) | y. y \<in> \<Gamma>\<^sup>- G (set xs)}"
shows "\<nexists> u p. vwalk_bet G' u p u \<and> length p \<ge> 2"
 "\<And> x y z. \<lbrakk>(y, x)\<in> G'; (z, x) \<in> G'\<rbrakk> \<Longrightarrow> y = z"
proof-
  have "(\<nexists> u p. vwalk_bet G' u p u \<and> length p \<ge> 2) \<and>
         (\<forall> x y z. (y, x)\<in> G' \<and> (z, x) \<in> G' \<longrightarrow> y = z)"
 using assms
proof(induction xs arbitrary: G' x G z)
  case (Cons xx xs)
  note G'_def = Cons(7)
  have no_self_loop: "(x,x) \<in> G \<Longrightarrow> False" for x
    using Cons.prems(4) edge_iff_vwalk_bet[of x x G] edges_are_vwalk_bet_length2(2)[of x x G]
    by fast
  have xx_is_x:"xx = x" 
    using Cons.prems(1) hd_of_vwalk_bet' by fastforce
  from Cons show ?case 
  proof(cases xs, goal_cases)
    case 1
    hence xx_is_y:"xx = y" 
      by (metis last.simps vwalk_bet_props)
    have x_is_y: "x = y"
      using Cons.prems(1) hd_of_vwalk_bet xx_is_y by fastforce
    show ?thesis 
    proof(cases "z = y")
      case True
      have "G' = G"
        by(auto simp add: G'_def 1 True delta_plus_def delta_minus_def xx_is_y
                           Gamma_plus_def Gamma_minus_def 
                          dest: no_self_loop)
      then show ?thesis
        using Cons.prems(5)
        by (auto simp add: Cons.prems(4)) 
    next
      case False
      have G'_is: "G' = G - \<delta>\<^sup>+ G x - \<delta>\<^sup>- G x \<union> {(yy, z) |yy. yy \<in> \<gamma>\<^sup>- G x} \<union> {(z, yy) |yy. yy \<in> \<gamma>\<^sup>+ G x}"
        by (auto simp add: xx_is_y G'_def x_is_y 1(8) delta_minus_def Gamma_plus_def 
                           Gamma_minus_def delta_plus_def gamma_plus_def gamma_minus_def 
                      dest: no_self_loop)  
      note one = 1
      show ?thesis 
      proof(rule, goal_cases)
        case 1
        then show ?case 
         apply(rule acyclic_vert_replace[of z G _ x])
         using one(8) Cons.prems(3-5) False G'_is by (auto simp add: xx_is_y)
      next
        case 2
        then show ?case 
          using one(4,8)
          by(auto dest: one(6) 
              simp add: G'_def delta_plus_def delta_minus_def 
                        Gamma_plus_def Gamma_minus_def 1(8) xx_is_y)
      qed

    qed
  next
    case (2 x2 rest)
    note two = this
    define G'' where  "G'' = G - \<delta>\<^sup>+ G x - \<delta>\<^sup>- G x - \<delta>\<^sup>+ G x2 - \<delta>\<^sup>- G x2
                    \<union> {(x2, yy) | yy. yy \<in> \<Gamma>\<^sup>+ G {x, x2}}
                    \<union> {(yy, x2) | yy. yy \<in> \<Gamma>\<^sup>- G {x, x2}}" 
    have G'_is:"G' =
    G'' - \<Union> {\<delta>\<^sup>+ G'' x |x. x \<in> set xs} - \<Union> {\<delta>\<^sup>- G'' x |x. x \<in> set xs} \<union>
    {(z, y) |y. y \<in> \<Gamma>\<^sup>+ G'' set xs} \<union>
    {(y, z) |y. y \<in> \<Gamma>\<^sup>- G'' set xs}"
   proof(rule, all \<open>rule\<close>, goal_cases)
      case (1 e)
      then show ?case 
        unfolding G'_def
      proof(elim UnE, goal_cases)
        case 1
        then show ?case
          using two(8)
          by (auto simp add: delta_plus_def delta_minus_def
                             G''_def Gamma_minus_def Gamma_plus_def xx_is_x)
      next
        case 2
        have helper1:
            "\<lbrakk>y \<in> \<Gamma>\<^sup>+ G insert xx (set xs);e = (z, y); y \<notin> \<Gamma>\<^sup>+ G'' set xs; y \<noteq> z\<rbrakk>
                  \<Longrightarrow> (z, y) \<in> G''" for y
            using two(8)
            by (auto simp add: delta_plus_def delta_minus_def
                             G''_def Gamma_minus_def Gamma_plus_def xx_is_x, auto)
          have helper2:
             "\<lbrakk>y \<in> \<Gamma>\<^sup>+ G insert xx (set xs); e = (z, y); y \<notin> \<Gamma>\<^sup>+ G'' set xs;
                z \<notin> \<Gamma>\<^sup>- G'' set xs\<rbrakk> \<Longrightarrow> (z, y) \<in> G''" for y

              using two(8)
              by(auto simp add: G''_def)
                ((auto simp add: Gamma_plus_def Gamma_minus_def xx_is_x
                                 delta_plus_def delta_minus_def)[1]; blast?)+
       
           from 2 show ?case
             by (auto intro: helper1 helper2, insert two(8),
                 auto simp add: G''_def Gamma_plus_def Gamma_minus_def xx_is_x delta_plus_def delta_minus_def)
      next
        case 3
        have helper1:
            "\<lbrakk>y \<in> \<Gamma>\<^sup>- G insert xx (set xs); e = (y, z); y \<notin> \<Gamma>\<^sup>- G'' set xs;
              y \<noteq> z\<rbrakk> \<Longrightarrow> (y, z) \<in> G''" for y
            by(auto simp add: Gamma_minus_def G''_def delta_plus_def 
                                 delta_minus_def  Gamma_plus_def xx_is_x two(8)) blast
          have helper2:
             "\<lbrakk>y \<in> \<Gamma>\<^sup>- G insert xx (set xs); e = (y, z); y \<notin> \<Gamma>\<^sup>- G'' set xs;
               z \<notin> \<Gamma>\<^sup>+ G'' set xs\<rbrakk> \<Longrightarrow> (y, z) \<in> G''" for y
            by(auto simp add: G''_def)
              ((auto simp add: Gamma_minus_def  delta_plus_def 
                               delta_minus_def  Gamma_plus_def xx_is_x two(8))[1]; blast?)+
          from 3 show ?case 
          by (auto intro: helper1 helper2, insert two(8),
                 auto simp add: G''_def Gamma_plus_def Gamma_minus_def xx_is_x delta_plus_def delta_minus_def)
      qed
    next
      case (2 e)
      then show ?case 
      proof(elim UnE, goal_cases)
        case 1
        then show ?case 
          using two(3,8)
          by(auto simp add: G'_def G''_def delta_plus_def 
                            delta_minus_def Gamma_plus_def Gamma_minus_def xx_is_x)
           (smt (z3) fst_conv snd_conv mem_Collect_eq)+
      next
        case 2
        then show ?case
          by(auto simp add: G'_def G''_def Gamma_plus_def
                            Gamma_minus_def delta_plus_def delta_minus_def xx_is_x two(8))
      next
        case 3
        then show ?case 
          by(auto simp add: G'_def G''_def Gamma_plus_def
                            Gamma_minus_def delta_plus_def delta_minus_def xx_is_x two(8))
      qed
    qed
    have no_cyc_G'':"\<nexists>u p. vwalk_bet G'' u p u \<and> 2 \<le> length p"
      apply(rule acyclic_contract_edge(1)[of x2 G x x2])
      using two(2) 
      by(auto simp add: xx_is_x  G''_def two(5,6,8))
    have determ:"\<And> x y z. \<lbrakk>(y, x) \<in> G''; (z, x) \<in> G''\<rbrakk> \<Longrightarrow> y = z"
      apply(rule acyclic_contract_edge(2)[of x2 G x x2])
      using two(2) 
      by(auto simp add: xx_is_x  G''_def two(5,6,8))
    show ?case
    proof(cases rest)
      case Nil
      hence xs_is: "xs = [y]"
        using last_of_vwalk_bet two(2,8) by fastforce
      show ?thesis 
      proof(rule, goal_cases)
        case 1
        then show ?case 
         apply(rule acyclic_contract_edge(1)[of z G x y])
         using two(2,4) xs_is xx_is_x 
         by(auto simp add: G'_def xs_is xx_is_x two(5,6))
      next
        case 2
        then show ?case
        proof(rule+, elim conjE, goal_cases)
          case (1 x' y' z')
           show ?case 
            apply(rule acyclic_contract_edge(2)[of z G x y G', OF _ _ _ _ _ 1])
            using two(2,4) xs_is xx_is_x 
            by(auto simp add: G'_def xs_is xx_is_x two(5,6))
        qed
      qed
    next
      case (Cons a list)
      hence True: "length xs \<ge> 2" 
        by (simp add: two(8))
      have xs_vwalk:"vwalk_bet G x2 xs y" 
        using two(2,8) xx_is_x by force
      have vwalk_xs_G'':"vwalk_bet G'' x2 xs y"
        apply(rule vwalk_bet_if_edges_in[OF xs_vwalk True])
        using vwalk_bet_edges_in_edges[OF xs_vwalk] two(3)
               no_self_loop v_in_edge_in_vwalk 
        by(auto simp add: G''_def Gamma_plus_def Gamma_minus_def
                          delta_plus_def delta_minus_def xx_is_x) fastforce+
      have z_good:"z \<notin> dVs G'' - set xs"
        using Cons.prems(3) two(8)
        by(auto elim: in_dVsE 
            simp add: G''_def delta_plus_def delta_minus_def
                      Gamma_plus_def Gamma_minus_def  xx_is_x)
      show ?thesis 
       apply(rule two(1)[of G'' x2 z G'])
       using vwalk_xs_G''  two(3)  no_cyc_G'' z_good determ 
       by(auto simp add: G'_is two(8))
   qed
 qed
qed auto
  thus "\<nexists>u p. vwalk_bet G' u p u \<and> 2 \<le> length p"
       "\<And>x y z. \<lbrakk>(y, x) \<in> G'; (z, x) \<in> G'\<rbrakk> \<Longrightarrow> y = z"
    by auto
qed

lemma wf_contract:
  assumes "finite G" "wf G"
          "vwalk_bet G x xs y"  "distinct xs" "z \<notin> dVs G - set xs"
           "\<And> x y z. \<lbrakk>(y, x)\<in> G; (z, x) \<in> G\<rbrakk> \<Longrightarrow> y = z"
  and G'_def: "G' = G - \<Union> {\<delta>\<^sup>+ G x | x. x \<in> set xs} - \<Union> {\<delta>\<^sup>- G x | x. x \<in> set xs}
                    \<union> {(z, y) | y. y \<in> \<Gamma>\<^sup>+ G (set xs)}
                    \<union> {(y, z) | y. y \<in> \<Gamma>\<^sup>- G (set xs)}"
shows "wf G'"
      "\<And> x y z. \<lbrakk>(y, x)\<in> G'; (z, x) \<in> G'\<rbrakk> \<Longrightarrow> y = z"
proof(rule finite_acyclic_wf)
  show "finite G'"
    using assms(1)
    by(auto intro!: finite_gamma_minus finite_gamma_plus 
                    finite_subset[of _ "dVs G", simplified finite_vertices_iff]
          simp add: G'_def  setcompr_eq_image Gamma_plus_def Gamma_minus_def)
  have "acyclic G"
    by (simp add: assms(2) wf_acyclic)
  thus "acyclic G'"  "\<And> x y z. \<lbrakk>(y, x)\<in> G'; (z, x) \<in> G'\<rbrakk> \<Longrightarrow> y = z"
    using acyclic_contract[OF assms(3,4,5) _ assms(6) G'_def]
    by(auto simp add: acyc_rel_vwalk_bet)
qed

end