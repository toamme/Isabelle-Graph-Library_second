section ‹A pluggable checker for the oracle/cleanup pipeline›

text ‹‹mcf_oracle_cleanup›'s ‹decide› calls exactly one concrete checker --- ‹screen› composed
      with ‹verdict_of› --- to decide between reporting the oracle's own verdict and falling back
      to ‹cleanup›. This theory abstracts ∗‹only that one call site›: the checker becomes a locale
      parameter, constrained by nothing but the same soundness property ‹checked_verdict› already
      has. Nothing in ‹Mincost_Oracle_Certificates› changes; ‹decide› and ‹solve› are untouched,
      and the theorem at the end shows the new, pluggable pipeline instantiated with the current,
      concrete checker computes exactly the same ‹decide› as before --- so today's checker needs
      no change to fit the new shape.›

theory Mincost_Oracle_Certificates_Pluggable
  imports Mincost_Oracle_Certificates
begin

subsection ‹The pipeline, generic in the checker›

text ‹Same shape as ‹mcf_oracle_cleanup_spec›, with one more parameter: ‹checker› replaces the
      fixed ‹map_option verdict_of ∘ screen›. A checker call and a cleanup call are the same shape
      a level up --- an instance in, a verdict (optionally) out --- so this is the only change
      ‹decide›'s definition needs.›

locale mcf_oracle_pluggable_checker =
  mcf_oracle_cleanup_spec where capacity_list = capacity_list
  for capacity_list :: "('n :: linordered_idom) list" +
  fixes checker :: "'n oracle_answer ⇒ 'n solver_verdict option"
begin

definition decide' :: "'n oracle_answer ⇒ 'n solver_verdict" where
  "decide' a = (case checker a of Some b ⇒ b | None ⇒ cleanup orc_input (oa_flow a))"

definition solve' :: "'n solver_verdict" where
  "solve' = decide' orc_answer"

end

text ‹The one property assumed of ‹checker›: an accepted verdict is true of the instance. Exactly
      ‹checked_verdict_sound›'s shape, asked of an arbitrary function rather than of the one
      ‹Mincost_Oracle_Certificates› happens to define.›

locale mcf_oracle_pluggable_checker_proof =
  mcf_oracle + mcf_oracle_pluggable_checker +
  assumes cleanup_correct: "⋀g. verdict_ok (cleanup orc_input g)"
      and checker_correct: "⋀a r. checker a = Some r ⟹ verdict_ok r"
begin

theorem solve'_correct: "verdict_ok solve'"
  using checker_correct cleanup_correct
  by (auto simp add: solve'_def decide'_def split: option.splits)

end

subsection ‹The current checker instantiates it for free›

text ‹‹screen› composed with ‹verdict_of› is already exactly a function of ‹checker›'s type, and
      ‹verdict_of_sound› is already exactly ‹checker_correct› for it --- no new proof, only a
      repackaging of one that exists.›

context mcf_oracle
begin

definition current_checker :: "'n oracle_answer ⇒ 'n solver_verdict option" where
  "current_checker a = map_option verdict_of (screen a)"

lemma current_checker_correct: "current_checker a = Some r ⟹ verdict_ok r"
  using verdict_of_sound by (auto simp add: current_checker_def screen_def split: if_splits)

end

text ‹And the punchline: plugging the current checker into the new, generic pipeline reproduces
      ‹decide› exactly, pointwise. The restructuring changes nothing about what is computed today;
      it only gives the call site a second, as yet unused, way to be filled in.›

context mcf_oracle_cleanup
begin

sublocale pluggable: mcf_oracle_pluggable_checker_proof
  where capacity_list = capacity_list and cleanup = cleanup and checker = current_checker
  by unfold_locales (auto simp add: current_checker_correct cleanup_correct)

lemma decide'_current_checker_eq_decide: "pluggable.decide' a = decide a"
  unfolding pluggable.decide'_def decide_def current_checker_def
  by (cases "screen a") auto

end

end
