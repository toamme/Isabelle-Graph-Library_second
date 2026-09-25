section \<open>A pluggable checker for the oracle/cleanup pipeline\<close>

text \<open>\<open>mcf_oracle_cleanup\<close>'s \<open>decide\<close> calls exactly one concrete checker --- \<open>screen\<close> composed
      with \<open>verdict_of\<close> --- to decide between reporting the oracle's own verdict and falling back
      to \<open>cleanup\<close>. This theory abstracts \<^emph>\<open>only that one call site\<close>: the checker becomes a locale
      parameter, constrained by nothing but the same soundness property \<open>checked_verdict\<close> already
      has. Nothing in \<open>Mincost_Oracle_Certificates\<close> changes; \<open>decide\<close> and \<open>solve\<close> are untouched,
      and the theorem at the end shows the new, pluggable pipeline instantiated with the current,
      concrete checker computes exactly the same \<open>decide\<close> as before --- so today's checker needs
      no change to fit the new shape.\<close>

theory Mincost_Oracle_Certificates_Pluggable
  imports Mincost_Oracle_Certificates
begin

subsection \<open>The pipeline, generic in the checker\<close>

text \<open>Same shape as \<open>mcf_oracle_cleanup_spec\<close>, with one more parameter: \<open>checker\<close> replaces the
      fixed \<open>map_option verdict_of \<circ> screen\<close>. A checker call and a cleanup call are the same shape
      a level up --- an instance in, a verdict (optionally) out --- so this is the only change
      \<open>decide\<close>'s definition needs.\<close>

locale mcf_oracle_pluggable_checker =
  mcf_oracle_cleanup_spec where capacity_list = capacity_list
  for capacity_list :: "('n :: linordered_idom) list" +
  fixes checker :: "'n oracle_answer \<Rightarrow> 'n solver_verdict option"
begin

definition decide' :: "'n oracle_answer \<Rightarrow> 'n solver_verdict" where
  "decide' a = (case checker a of Some b \<Rightarrow> b | None \<Rightarrow> cleanup orc_input (oa_flow a))"

definition solve' :: "'n solver_verdict" where
  "solve' = decide' orc_answer"

end

text \<open>The one property assumed of \<open>checker\<close>: an accepted verdict is true of the instance. Exactly
      \<open>checked_verdict_sound\<close>'s shape, asked of an arbitrary function rather than of the one
      \<open>Mincost_Oracle_Certificates\<close> happens to define.\<close>

locale mcf_oracle_pluggable_checker_proof =
  mcf_oracle + mcf_oracle_pluggable_checker +
  assumes cleanup_correct: "\<And>g. verdict_ok (cleanup orc_input g)"
      and checker_correct: "\<And>a r. checker a = Some r \<Longrightarrow> verdict_ok r"
begin

theorem solve'_correct: "verdict_ok solve'"
  using checker_correct cleanup_correct
  by (auto simp add: solve'_def decide'_def split: option.splits)

end

subsection \<open>The current checker instantiates it for free\<close>

text \<open>\<open>screen\<close> composed with \<open>verdict_of\<close> is already exactly a function of \<open>checker\<close>'s type, and
      \<open>verdict_of_sound\<close> is already exactly \<open>checker_correct\<close> for it --- no new proof, only a
      repackaging of one that exists.\<close>

context mcf_oracle
begin

definition current_checker :: "'n oracle_answer \<Rightarrow> 'n solver_verdict option" where
  "current_checker a = map_option verdict_of (screen a)"

lemma current_checker_correct: "current_checker a = Some r \<Longrightarrow> verdict_ok r"
  using verdict_of_sound by (auto simp add: current_checker_def screen_def split: if_splits)

end

text \<open>And the punchline: plugging the current checker into the new, generic pipeline reproduces
      \<open>decide\<close> exactly, pointwise. The restructuring changes nothing about what is computed today;
      it only gives the call site a second, as yet unused, way to be filled in.\<close>

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
