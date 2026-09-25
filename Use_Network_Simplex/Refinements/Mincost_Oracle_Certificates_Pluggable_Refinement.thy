theory Mincost_Oracle_Certificates_Pluggable_Refinement
  imports Mincost_Oracle_Certificates_Refinement Mincost_Oracle_Certificates_Pluggable
begin

section ‹Imperative refinement of the pluggable checker›

text ‹‹Mincost_Oracle_Certificates_Pluggable› abstracts the one call site of
      ‹mcf_oracle_cleanup_spec.decide› that decides an accepted certificate, turning the fixed
      ‹screen›/‹verdict_of› pair into a locale parameter ‹checker›.  This theory does the same thing
      one layer down, to the imperative pipeline of ‹Mincost_Oracle_Certificates_Refinement›: ‹decide_imp›
      hard-wires ‹check_answer_imp› and ‹flag_of› exactly the way ‹decide› hard-wires ‹screen› and
      ‹verdict_of›, and that is the one call site abstracted here.

      The two pipelines are otherwise proved completely independently --- the imperative one never
      goes through ‹decide›/‹solve› at all, so making it pluggable needs its own locale, its own
      assumed checker triple, and its own proof that today's checker discharges it.›

subsection ‹The pipeline, generic in the checker›

text ‹Same shape as ‹mcf_oracle_heap_pipeline_spec›, with one more parameter: ‹checker_imp› replaces
      the fixed ‹check_answer_imp›/‹flag_of› pair.  A checker call and a cleanup call are the same
      shape a level up --- an instance in, a verdict (optionally) out --- so this is the only change
      ‹decide_imp›'s definition needs.  Everything else --- ‹oracle_imp›, ‹cleanup_imp›,
      ‹rectify_imp› --- is inherited unchanged from ‹mcf_oracle_heap_pipeline_spec›.›

locale mcf_oracle_heap_pluggable_checker_spec =
  mcf_oracle_heap_pipeline_spec where capacity_list = capacity_list
  for capacity_list :: "('n :: {heap, linordered_idom}) list" +
  fixes checker_imp ::
      "checker_mode ⇒ nat ⇒
       nat array ⇒ nat array ⇒ 'n array ⇒ 'n array ⇒ 'n array ⇒ 'n array ⇒ 'n answer_imp
       ⇒ verdict_flag option Heap"
begin

definition decide_imp' ::
  "checker_mode ⇒ nat ⇒
   nat array ⇒ nat array ⇒ 'n array ⇒ 'n array ⇒ 'n array ⇒ 'n array ⇒ 'n answer_imp
   ⇒ verdict_flag Heap" where
  "decide_imp' cm M fa sa ca oa ba fla ai =
     do {
       co ← checker_imp cm M fa sa ca oa ba fla ai;
       case co of Some r ⇒ return r
                | None ⇒ do { _ ← rectify_imp ca fla 0 m; cleanup_imp fa sa ca oa ba fla } }"

definition solve_imp' ::
  "checker_mode ⇒ nat ⇒
   nat array ⇒ nat array ⇒ 'n array ⇒ 'n array ⇒ 'n array ⇒ 'n array ⇒ verdict_flag Heap" where
  "solve_imp' cm M fa sa ca oa ba fla =
     do { ai ← oracle_imp fa sa ca oa ba fla; decide_imp' cm M fa sa ca oa ba fla ai }"

end

text ‹The proof layer adds one thing: the checker's triple.  An accepted verdict (‹Some r›) has to
      be true of the instance; a deferral (‹None›) says nothing, exactly as ‹checker_correct› says
      nothing about the functional ‹checker› on ‹None›.  ‹oracle_imp_rule› and ‹cleanup_imp_rule› are
      carried over unchanged from ‹mcf_oracle_heap›.›

locale mcf_oracle_heap_pluggable_checker =
  mcf_oracle_heap_checks where capacity_list = capacity_list and h = h +
  mcf_oracle_heap_pluggable_checker_spec where capacity_list = capacity_list
  for capacity_list :: "('n :: {heap, linordered_idom}) list" and h +
  assumes oracle_imp_rule:
      "length fl = m ⟹
       <inst_assn fa sa ca oa ba * fla ↦⇩a fl>
         oracle_imp fa sa ca oa ba fla
       <λai. inst_assn fa sa ca oa ba * answer_assn fla orc_answer ai>"
    and cleanup_imp_rule:
      "⟦length fl = m;
        ⋀e. e < m ⟹ 0 ≤ fl ! e;
        ⋀e. ⟦e < m; capacity_list ! e ≠ - 1⟧ ⟹ fl ! e ≤ capacity_list ! e⟧ ⟹
       <inst_assn fa sa ca oa ba * fla ↦⇩a fl>
         cleanup_imp fa sa ca oa ba fla
       <λr. ∃⇩A fl'. inst_assn fa sa ca oa ba * fla ↦⇩a fl'
                    * ↑(length fl' = m ∧ verdict_ok (verdict_of_flag r fl'))>"
    and checker_imp_rule:
      "answer_wf a ⟹ 0 < M ⟹
       <inst_assn fa sa ca oa ba * answer_assn fla a ai>
         checker_imp cm M fa sa ca oa ba fla ai
       <λr. inst_assn fa sa ca oa ba * answer_assn fla a ai
            * ↑(case r of Some r' ⇒ verdict_ok_dispatch cm M (verdict_of_flag r' (oa_flow a))
                        | None ⇒ True)>"
begin

text ‹The rectification pass is proved exactly as in ‹mcf_oracle_heap›: it is not part of the
      specification, only of this proof, so it has no counterpart to inherit and is re-derived here
      from ‹mcf_oracle_heap_checks›'s ‹capacity_format› alone --- no dependence on either assumed
      triple above.›

definition clamp1 :: "'n ⇒ 'n ⇒ 'n" where
  "clamp1 c f = (if f < 0 then 0 else if c ≠ - 1 ∧ c < f then c else f)"

fun rectify :: "'n list ⇒ nat ⇒ nat ⇒ 'n list" where
  "rectify fl e 0 = fl"
| "rectify fl e (Suc k) = rectify (fl[e := clamp1 (capacity_list ! e) (fl ! e)]) (Suc e) k"

definition cap_ok :: "'n list ⇒ nat ⇒ bool" where
  "cap_ok fl i = (0 ≤ fl ! i ∧ (capacity_list ! i ≠ - 1 ⟶ fl ! i ≤ capacity_list ! i))"

lemma rectify_imp_rule:
  "⟦e + k ≤ length fl; length capacity_list = m; e + k ≤ m⟧ ⟹
   <ca ↦⇩a capacity_list * fla ↦⇩a fl> rectify_imp ca fla e k
   <λ_. ca ↦⇩a capacity_list * fla ↦⇩a rectify fl e k>"
proof(induction k arbitrary: e fl)
  case 0
  thus ?case by(subst rectify_imp.simps) sep_auto
next
  case (Suc k)
  have ef: "e < length fl" and ec: "e < length capacity_list" using Suc.prems by simp_all
  have IH: "<ca ↦⇩a capacity_list * fla ↦⇩a (fl[e := clamp1 (capacity_list ! e) (fl ! e)])>
              rectify_imp ca fla (Suc e) k
            <λ_. ca ↦⇩a capacity_list
                 * fla ↦⇩a rectify (fl[e := clamp1 (capacity_list ! e) (fl ! e)]) (Suc e) k>"
    using Suc.IH[of "Suc e" "fl[e := clamp1 (capacity_list ! e) (fl ! e)]"] Suc.prems by simp
  show ?case
    by(subst rectify_imp.simps) (sep_auto simp: ef ec clamp1_def[symmetric] heap: IH)
qed

lemma rectify_length: "length (rectify fl e k) = length fl"
  by(induction k arbitrary: e fl) simp_all

lemma rectify_outside: "i < e ∨ e + k ≤ i ⟹ rectify fl e k ! i = fl ! i"
  by(induction k arbitrary: e fl) (auto simp add: nth_list_update)

lemma cap_ok_clamp1:
  assumes "e < m" "e < length fl"
  shows "cap_ok (fl[e := clamp1 (capacity_list ! e) (fl ! e)]) e"
  using assms capacity_format[OF assms(1)] by(auto simp add: cap_ok_def clamp1_def)

lemma rectify_inside:
  "⟦e + k ≤ m; e + k ≤ length fl; e ≤ i; i < e + k⟧ ⟹ cap_ok (rectify fl e k) i"
proof(induction k arbitrary: e fl)
  case 0
  thus ?case by simp
next
  case (Suc k)
  show ?case
  proof(cases "i = e")
    case True
    have "rectify (fl[e := clamp1 (capacity_list ! e) (fl ! e)]) (Suc e) k ! e
            = fl[e := clamp1 (capacity_list ! e) (fl ! e)] ! e"
      by(rule rectify_outside) simp
    thus ?thesis
      using cap_ok_clamp1[of e fl] Suc.prems True by(simp add: cap_ok_def)
  next
    case False
    hence "Suc e ≤ i" using Suc.prems by simp
    thus ?thesis
      using Suc.IH[of "Suc e" "fl[e := clamp1 (capacity_list ! e) (fl ! e)]"] Suc.prems by simp
  qed
qed

lemma rectify_facts:
  assumes fl: "length fl = m"
  shows "length (rectify fl 0 m) = m"
    and "e < m ⟹ 0 ≤ rectify fl 0 m ! e"
    and "⟦e < m; capacity_list ! e ≠ - 1⟧ ⟹ rectify fl 0 m ! e ≤ capacity_list ! e"
  using rectify_length[of fl 0 m] fl rectify_inside[of 0 m fl e]
  by(auto simp add: cap_ok_def)

subsection ‹The pipeline is correct›

text ‹Deciding is correct.  If the checker accepts, its own triple makes the verdict true; if it
      defers, the flow is rectified into the capacities --- exactly what ‹cleanup_imp_rule› demands
      --- and the verdict is the cleanup's.  Structurally identical to ‹decide_imp_correct›, with the
      Boolean case split of ‹check_answer_imp_rule› replaced by the option case split of
      ‹checker_imp_rule›.›

lemma decide_imp'_correct:
  assumes wf: "answer_wf a" and Mpos: "0 < M"
  shows "<inst_assn fa sa ca oa ba * answer_assn fla a ai>
           decide_imp' cm M fa sa ca oa ba fla ai
         <λr. ∃⇩A fl'. inst_assn fa sa ca oa ba * fla ↦⇩a fl'
              * ↑(length fl' = m ∧ verdict_ok_dispatch cm M (verdict_of_flag r fl'))>"
proof -
  have flm: "length (oa_flow a) = m" using wf by(simp add: answer_wf_def)
  have rect: "<ca ↦⇩a capacity_list * fla ↦⇩a oa_flow a>
                rectify_imp ca fla 0 m
              <λ_. ca ↦⇩a capacity_list * fla ↦⇩a rectify (oa_flow a) 0 m>"
    by(rule rectify_imp_rule) (simp_all add: flm length_capacity)
  have clean: "<inst_assn fa sa ca oa ba * fla ↦⇩a rectify (oa_flow a) 0 m>
                 cleanup_imp fa sa ca oa ba fla
               <λr. ∃⇩A fl'. inst_assn fa sa ca oa ba * fla ↦⇩a fl'
                    * ↑(length fl' = m ∧ verdict_ok (verdict_of_flag r fl'))>"
    by(rule cleanup_imp_rule) (auto simp add: rectify_facts[OF flm])
  have clean_dispatch: "<inst_assn fa sa ca oa ba * fla ↦⇩a rectify (oa_flow a) 0 m>
                 cleanup_imp fa sa ca oa ba fla
               <λr. ∃⇩A fl'. inst_assn fa sa ca oa ba * fla ↦⇩a fl'
                    * ↑(length fl' = m ∧ verdict_ok_dispatch cm M (verdict_of_flag r fl'))>"
    using Mpos by(sep_auto heap: clean simp: verdict_ok_imp_dispatch)
  show ?thesis
    unfolding decide_imp'_def
    apply(sep_auto heap: checker_imp_rule[OF wf Mpos])
     apply(sep_auto simp: answer_assn_def inst_assn_def
                    heap: rect[unfolded inst_assn_def] clean_dispatch[unfolded inst_assn_def])
    apply(sep_auto simp: flm)
    done
qed

text ‹And the pipeline: call the untrusted oracle, ask the checker, and if it defers fall back on
      the verified cleanup.  Same statement as ‹mcf_oracle_heap.solve_imp_correct› --- generic in
      ‹checker_imp› rather than fixed to ‹check_answer_imp›.›

theorem solve_imp'_correct:
  assumes fl: "length fl = m" and wf: "answer_wf orc_answer" and Mpos: "0 < M"
  shows "<inst_assn fa sa ca oa ba * fla ↦⇩a fl>
           solve_imp' cm M fa sa ca oa ba fla
         <λr. ∃⇩A fl'. inst_assn fa sa ca oa ba * fla ↦⇩a fl'
              * ↑(length fl' = m ∧ verdict_ok_dispatch cm M (verdict_of_flag r fl'))>"
  unfolding solve_imp'_def
  by(sep_auto heap: oracle_imp_rule[OF fl] decide_imp'_correct[OF wf Mpos])

end

subsection ‹The current checker instantiates it for free›

text ‹‹check_answer_imp› composed with ‹flag_of› is already exactly a function of ‹checker_imp›'s
      type.  The definition is given in ‹mcf_oracle_heap_pipeline_spec› itself --- assumption-free,
      like ‹check_answer_imp› and ‹flag_of› it is built from --- rather than in the proof locale
      below: a definition inside a locale that carries ‹mcf_oracle›'s real assumptions would export
      as a conditional code equation, and code generation cannot discharge that condition.›

context mcf_oracle_heap_pipeline_spec
begin

definition current_checker_imp ::
  "checker_mode ⇒ nat ⇒
   nat array ⇒ nat array ⇒ 'n array ⇒ 'n array ⇒ 'n array ⇒ 'n array ⇒ 'n answer_imp
   ⇒ verdict_flag option Heap" where
  "current_checker_imp cm M fa sa ca oa ba fla ai =
     do {
       ok ← check_answer_imp cm M fa sa ca oa ba fla ai;
       return (if ok then Some (flag_of ai) else None) }"

end

text ‹Its correctness needs only ‹mcf_oracle_heap_checks› --- the four check refinements --- and
      none of ‹mcf_oracle_heap›'s two assumed triples, so it is proved in a locale that combines the
      checks with the pipeline's definitions and assumes nothing further.  (‹check_answer_imp_rule›
      is reproved here rather than inherited: in ‹Mincost_Oracle_Certificates_Refinement› it lives in
      ‹mcf_oracle_heap› itself, bundled with the two assumed triples it does not actually need.)›

locale mcf_oracle_heap_current_checker =
  mcf_oracle_heap_checks where capacity_list = capacity_list and h = h +
  mcf_oracle_heap_pipeline_spec where capacity_list = capacity_list
  for capacity_list :: "('n :: {heap, linordered_idom}) list" and h
begin

lemma check_answer_imp_rule:
  assumes wf: "answer_wf a" and Mpos: "0 < M"
  shows "<inst_assn fa sa ca oa ba * answer_assn fla a ai>
     check_answer_imp cm M fa sa ca oa ba fla ai
   <λr. inst_assn fa sa ca oa ba * answer_assn fla a ai * ↑(r = check_answer_dispatch cm a)>"
proof(cases a)
  case (OracleOptimum fl pot certm)
  have len: "length fl = m ∧ length pot = Suc n"
    using wf by(simp add: answer_wf_def OracleOptimum)
  show ?thesis
  proof(cases ai)
    case (OptimumI pota certm')
    show ?thesis
      unfolding OracleOptimum OptimumI check_answer_imp_def answer_assn_def
      by(sep_auto simp: check_answer_dispatch_def heap: check_optimum_dispatch_imp_rule[OF len])
  qed (simp_all add: OracleOptimum answer_assn_def)
next
  case (OracleInfeasible fl S)
  have len: "length S = Suc n"
    using wf by(simp add: answer_wf_def OracleInfeasible)
  show ?thesis
  proof(cases ai)
    case (InfeasibleI sca)
    show ?thesis
      unfolding OracleInfeasible InfeasibleI check_answer_imp_def answer_assn_def
      by(sep_auto simp: check_answer_dispatch_def heap: check_infeasible_imp_rule[OF len])
  qed (simp_all add: OracleInfeasible answer_assn_def)
next
  case (OracleUnbounded fl cyc)
  have rule: "<inst_assn fa sa ca oa ba * cyca ↦⇩a (cyc @ rst)>
                check_unbounded_imp fa sa ca oa cyca (length cyc)
              <λr. inst_assn fa sa ca oa ba * cyca ↦⇩a (cyc @ rst)
                   * ↑(r = check_unbounded cyc)>" for rst cyca
    using check_unbounded_imp_rule[OF length_fst_list length_snd_list length_capacity
                                      length_cost_list, of "length cyc" "cyc @ rst"]
    by simp
  show ?thesis
  proof(cases ai)
    case (UnboundedI cyca k)
    show ?thesis
      unfolding OracleUnbounded UnboundedI check_answer_imp_def answer_assn_def
      by(sep_auto simp: check_answer_dispatch_def heap: rule)
  qed (simp_all add: OracleUnbounded answer_assn_def)
qed

lemma verdict_of_flag_of:
  "answer_assn fla a ai = false ∨ verdict_of_flag (flag_of ai) (oa_flow a) = verdict_of a"
  by(cases a; cases ai) (auto simp add: answer_assn_def verdict_of_flag_def verdict_of_def)

lemma current_checker_imp_rule:
  assumes wf: "answer_wf a" and Mpos: "0 < M"
  shows "<inst_assn fa sa ca oa ba * answer_assn fla a ai>
           current_checker_imp cm M fa sa ca oa ba fla ai
         <λr. inst_assn fa sa ca oa ba * answer_assn fla a ai
              * ↑(case r of Some r' ⇒ verdict_ok_dispatch cm M (verdict_of_flag r' (oa_flow a))
                          | None ⇒ True)>"
proof(cases "answer_assn fla a ai = false")
  case True
  thus ?thesis by(simp add: current_checker_imp_def)
next
  case False
  hence vf: "verdict_of_flag (flag_of ai) (oa_flow a) = verdict_of a"
    using verdict_of_flag_of by blast
  show ?thesis
    unfolding current_checker_imp_def
    by(sep_auto simp: verdict_of_dispatch_sound vf Mpos heap: check_answer_imp_rule[OF wf Mpos])
qed

end

text ‹And the punchline: plugging the current checker into the new, generic pipeline satisfies
      exactly the triple ‹mcf_oracle_heap.solve_imp_correct› already proves.  The restructuring
      changes nothing about what is computed today; it only gives the call site a second, as yet
      unused, way to be filled in --- the imperative counterpart of
      ‹mcf_oracle_cleanup.decide'_current_checker_eq_decide›.›

context mcf_oracle_heap
begin

sublocale current: mcf_oracle_heap_current_checker
  where capacity_list = capacity_list and h = h and oracle_imp = oracle_imp
    and cleanup_imp = cleanup_imp
  by unfold_locales

sublocale pluggable: mcf_oracle_heap_pluggable_checker
  where capacity_list = capacity_list and h = h and oracle_imp = oracle_imp
    and cleanup_imp = cleanup_imp and checker_imp = current_checker_imp
  apply(unfold_locales)
     apply(rule oracle_imp_rule)
     apply assumption
    apply(rule cleanup_imp_rule)
      apply assumption
     apply assumption
    apply assumption
   apply(rule current.current_checker_imp_rule)
   apply assumption
  apply assumption
  done

end

end

