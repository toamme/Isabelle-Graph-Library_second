theory Neighbourhood_Best_Scan_Imperative
  imports Neighbourhood_Best_Scan Directed_Set_Graphs.Weighted_Neighbourhoods_Imperative_Spec
          Data_Structures.Iterable_Set_Specs_Imp Data_Structures.Real_Embedding
begin

section \<open>Imperative Scan for the Best Neighbour\<close>

text \<open>The imperative counterpart of @{const nb_best_scan_spec.best_of}. The key and the preference
      of the neighbour at the cursor are read by a heap program @{term cur}, which is an argument.
      It may read further state, which is framed through the scan by an assertion @{term Ctx}.
      The program does not allocate.\<close>

locale nb_best_scan_imp_code =
  fixes has_imp :: "'ci \<Rightarrow> 'v \<Rightarrow> bool Heap"
    and move_imp :: "'ci \<Rightarrow> 'v \<Rightarrow> unit Heap"
    and reset_imp :: "'ci \<Rightarrow> 'v \<Rightarrow> unit Heap"
begin

definition better_imp :: "'n::linorder \<times> 'v \<times> bool \<Rightarrow> 'n \<times> 'v \<times> bool \<Rightarrow> bool" where
  "better_imp p q = (fst p < fst q \<or> (fst p = fst q \<and> snd (snd p) \<and> \<not> snd (snd q)))"

definition "best_upd_imp b c =
  (case b of None \<Rightarrow> Some c | Some p \<Rightarrow> if better_imp c p then Some c else b)"

partial_function (heap) scan_best_imp ::
  "('ci \<Rightarrow> 'v \<Rightarrow> ('n::linorder \<times> 'v \<times> bool) Heap) \<Rightarrow> 'ci \<Rightarrow> 'v \<Rightarrow>
   ('n \<times> 'v \<times> bool) option \<Rightarrow> ('n \<times> 'v \<times> bool) option Heap" where
  "scan_best_imp cur Ci u b = do {
     t \<leftarrow> has_imp Ci u;
     (if t then do { c \<leftarrow> cur Ci u;
                     move_imp Ci u;
                     scan_best_imp cur Ci u (best_upd_imp b c) }
      else return b) }"

definition "best_of_imp cur Ci u = do { reset_imp Ci u; scan_best_imp cur Ci u None }"

end

locale nb_best_scan_imp =
  nb_best_scan +
  real_embedding h +
  nb: weighted_neighbourhoods_imp_spec
    where idx_invar = rnb_invar and idx_abstract = rnb_abstract and idx_current = rnb_current
      and idx_has = rnb_has and idx_iterated = rnb_iterated and idx_remaining = rnb_remaining
      and idx_move = rnb_move and idx_reset = rnb_reset and K = K
      and cost = cost and wval = wval and nb_init = nb_init and nb_assn = nb_assn
      and has_imp = has_imp and current_imp = current_imp and current_cost_imp = current_cost_imp
      and move_imp = move_imp and reset_imp = reset_imp and reset_all_imp = reset_all_imp
  for h :: "'n::linordered_idom \<Rightarrow> real"
    and cost wval nb_init nb_assn has_imp current_imp current_cost_imp move_imp reset_imp
        reset_all_imp

sublocale nb_best_scan_imp \<subseteq> code: nb_best_scan_imp_code has_imp move_imp reset_imp .

context nb_best_scan_imp
begin

text \<open>The imperative best candidate @{term bi} represents the functional one @{term b}.\<close>

definition "best_rel pref bi b =
  (b = map_option (\<lambda>(k, r, f). (h k, r)) bi \<and> (\<forall>k r f. bi = Some (k, r, f) \<longrightarrow> f = pref r))"

lemma best_upd_imp_rel:
  "\<lbrakk>best_rel pref bi b; key u r = h k; f = pref r\<rbrakk> \<Longrightarrow>
   best_rel pref (code.best_upd_imp bi (k, r, f)) (best_upd key pref u b r)"
  by (cases bi)
     (auto simp: best_rel_def code.best_upd_imp_def best_upd_def code.better_imp_def better_def)

lemma scan_best_imp_rule:
  assumes cur: "\<And>C. \<lbrakk>rnb_invar C; rnb_remaining C u \<noteq> {}\<rbrakk> \<Longrightarrow>
                  <nb_assn C Ci * Ctx> cur Ci u
                  <\<lambda>(k, r, f). nb_assn C Ci * Ctx *
                               \<up>(h k = key u r \<and> r = rnb_current C u \<and> f = pref r)>"
      and "rnb_invar C" "u \<in> K" "finite (rnb_remaining C u)" "best_rel pref bi b"
  shows "<nb_assn C Ci * Ctx> code.scan_best_imp cur Ci u bi
         <\<lambda>bi'. nb_assn (fst (scan_best key pref u C b)) Ci * Ctx *
                \<up>(best_rel pref bi' (snd (scan_best key pref u C b)))>"
  using assms(2-5)
proof(induction "card (rnb_remaining C u)" arbitrary: C b bi rule: less_induct)
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
    define b' where "b' = best_upd key pref u b (rnb_current C u)"
    have eq: "scan_best key pref u C b = scan_best key pref u (rnb_move C u) b'"
      by (simp add: scan_best.simps[of key pref u C b] True b'_def)
    have step: "\<And>k. h k = key u (rnb_current C u) \<Longrightarrow>
       <nb_assn (rnb_move C u) Ci * Ctx>
        code.scan_best_imp cur Ci u (code.best_upd_imp bi (k, rnb_current C u, pref (rnb_current C u)))
       <\<lambda>bi'. nb_assn (fst (scan_best key pref u C b)) Ci * Ctx *
              \<up>(best_rel pref bi' (snd (scan_best key pref u C b)))>"
      unfolding eq b'_def
      by (rule less.hyps[OF card_less C'(1) less.prems(2) fin' best_upd_imp_rel[OF less.prems(4)]])
         simp_all
    show ?thesis
      apply(subst code.scan_best_imp.simps)
      by (sep_auto heap: nb.has_rule cur[OF less.prems(1) ne] nb.move_rule step
                   simp: less.prems(1,2) True ne)
  next
    case False
    have eq: "scan_best key pref u C b = (C, b)" by (simp add: scan_best.simps[of key pref u C b] False)
    show ?thesis
      apply(subst code.scan_best_imp.simps)
      by (sep_auto heap: nb.has_rule simp: less.prems False eq)
  qed
qed

theorem best_of_imp_rule:
  assumes cur: "\<And>C. \<lbrakk>rnb_invar C; rnb_remaining C u \<noteq> {}\<rbrakk> \<Longrightarrow>
                  <nb_assn C Ci * Ctx> cur Ci u
                  <\<lambda>(k, r, f). nb_assn C Ci * Ctx *
                               \<up>(h k = key u r \<and> r = rnb_current C u \<and> f = pref r)>"
      and "rnb_invar C" "u \<in> K" "finite (rnb_abstract C u)"
  shows "<nb_assn C Ci * Ctx> code.best_of_imp cur Ci u
         <\<lambda>bi. nb_assn (fst (best_of key pref u C)) Ci * Ctx *
               \<up>(best_rel pref bi (snd (best_of key pref u C)))>"
proof-
  have R: "rnb_invar (rnb_reset C u)" "finite (rnb_remaining (rnb_reset C u) u)"
    using rnb.idx_reset_invar[OF assms(2,3)] rnb.idx_reset_remaining[OF assms(2,3)] assms(4)
    by auto
  note sc = scan_best_imp_rule[where key = key and pref = pref and cur = cur and Ctx = Ctx
                                 and bi = None and b = None, OF cur R(1) assms(3) R(2)]
  show ?thesis
    unfolding code.best_of_imp_def best_of_def
    by (sep_auto heap: nb.reset_rule sc simp: assms(2,3) best_rel_def)
qed

end

end
