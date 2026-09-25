
theory Network_Simplex_Initial_Basis_Selector
  imports Network_Simplex_Initial_Basis_Arb
begin

section ‹A concrete entering-edge selector: candidate-list block search›

text ‹We implement the @{locale edge_selector} ADT concretely, following the improved block-search
      pseudocode.  The selector state is a record holding a wrap-around ∗‹bookmark› into the
      augmented arc set @{term ‹{0..<m + Kart}›} (an arc is its own index, so ‹arc_array ! i = i›)
      and a ∗‹candidate list› of shortlisted edge ids.  A single call to the selection function
      sees the potentials @{term π} and the edge-tag array @{term es} as constants; all persistence
      lives in the record, threaded as the ADT's selector value.

      The rule proceeds in two phases.  ❙‹Minor iteration› (@{text scan_best}) re-prices the cached
      candidate list against the current @{term π}/@{term es}, drops the edges that are no longer
      eligible, and returns the most-violating survivor — so a returned edge is always eligible
      ∗‹now›, which is all the ADT demands.  ❙‹Major iteration› (@{text scan}) is reached only when the
      cache is exhausted; it sweeps the arc array in blocks from the bookmark, refilling the cache
      (up to @{term max_candidates}) and simultaneously tracking the best edge to return, with a
      ceiling bailout (list full) and a floor bailout (enough fuel, checked at block boundaries).
      If a full sweep of all @{term ‹m + Kart›} arcs inserts nothing, no eligible edge exists and the
      selector returns @{term None} — discharging the ADT's @{term None} contract, from which the
      outer loop later derives optimality.›

locale initial_basis_selector =
  initial_basis_correct where capacity_list = capacity_list and h = h
  for capacity_list :: "('n :: linordered_idom) list" and h :: "'n ⇒ real" +
  assumes block_size_pos:     "0 < block_size"
      and min_candidates_pos: "0 < min_candidates"
      and min_le_max:         "min_candidates ≤ max_candidates"
begin

text ‹The number of augmented arcs.›


subsection ‹Reduced cost and eligibility in the big-M descriptor world›

text ‹The cost of an edge as a big-M descriptor: an ordinary cost for a real edge, and the symbolic
      @{term bigM} (tag ‹+1›) for an artificial edge, so that
      @{term ‹pval_abstract bigM (cost_pval e) = cost_all ! e›}.›


text ‹The reduced cost @{term ‹𝖼 e + π (fst e) - π (snd e)›} assembled in the descriptor type; the
      potentials are looked up in the list-backed potential array.  Its abstract value is faithful to
      the real reduced cost under the network-simplex guard, via @{thm pot_plus_faithful}
      / @{thm pot_minus_faithful}.›


definition rc_val :: "(mtag × 'n) list ⇒ nat ⇒ real" where
  "rc_val π e = pval_abstract bigM (red_cost π e)"

text ‹❙‹Faithfulness of the M-free sign tests.›  The executable eligibility test uses the M-free
      ‹pval_neg› / ‹pval_pos›; they agree with the true sign of the abstract reduced
      cost @{term ‹pval_abstract bigM g›} whenever @{term g} satisfies the reduced-cost invariant
      @{const rc_invar} — its ordinary part is bounded by @{term ‹3 * sum_list (map abs cost_list)›},
      comfortably below @{term bigM}, so the big-M coefficient alone fixes the sign.  This is where the
      value of @{term bigM} does its work: in the proof, not in the code.›

lemma pval_neg_abstract:
  assumes "rc_invar g" shows "pval_neg g ⟷ pval_abstract bigM g < 0"
proof -
  have ob: "h (snd g) ≤ 3 * h (sum_list (map abs cost_list))"
           "- h (snd g) ≤ 3 * h (sum_list (map abs cost_list))"
    using h_rc_bound[OF assms] by (simp_all add: abs_le_iff)
  have bM: "bigM = 6 * h (sum_list (map abs cost_list)) + 1" by (simp add: bigM_def)
  have s0: "0 ≤ h (sum_list (map abs cost_list))" using sabs_nonneg by simp
  show ?thesis
    using ob bM s0
    by (cases "fst g"; simp_all add: pval_neg_def pval_abstract_def; linarith)
qed

lemma pval_pos_abstract:
  assumes "rc_invar g" shows "pval_pos g ⟷ 0 < pval_abstract bigM g"
proof -
  have ob: "h (snd g) ≤ 3 * h (sum_list (map abs cost_list))"
           "- h (snd g) ≤ 3 * h (sum_list (map abs cost_list))"
    using h_rc_bound[OF assms] by (simp_all add: abs_le_iff)
  have bM: "bigM = 6 * h (sum_list (map abs cost_list)) + 1" by (simp add: bigM_def)
  have s0: "0 ≤ h (sum_list (map abs cost_list))" using sabs_nonneg by simp
  show ?thesis
    using ob bM s0
    by (cases "fst g"; simp_all add: pval_pos_def pval_abstract_def; linarith)
qed

text ‹An @{term InL} edge is eligible when its reduced cost is negative, an @{term InU} edge when it
      is positive; tree edges are never eligible.  Both tests are the ∗‹M-free› ‹pval_neg› /
      ‹pval_pos›.  The violation is the magnitude of the reduced cost, and larger violation
      makes a better pivot (compared M-free by ‹viol_gt›).›



definition gviol :: "mtag × 'n ⇒ real" where
  "gviol g = ¦pval_abstract bigM g¦"

text ‹❙‹Compute-once evaluation› of an edge.  A single pass reads the tag once and builds the reduced
      cost @{term ‹red_cost π e›} once, returning what the two loops need: the eligibility flag (via
      the ∗‹M-free› ‹pval_neg› / ‹pval_pos›), the @{term in_U} flag, and the reduced-cost
      descriptor @{term g} itself.  ∗‹No abstract value and no @{term bigM} multiply is ever formed› —
      the violation ordering is likewise done M-free by ‹viol_gt› on the descriptors.  It is the
      executable counterpart of @{const eligible} / @{const ent_in_U} / @{const red_cost}, tied to them
      by @{text evaluate_eq}.›


text ‹@{const evaluate} short-circuits: for a self-loop it returns @{term False} ∗‹without› pricing
      the edge (no @{const red_cost}), so its three projections are: the eligibility flag and the
      @{const ent_in_U} flag always, but the reduced-cost descriptor only on the non-self-loop
      (equivalently, eligible) branch — which is the only branch where the loop ever reads it.›

lemma evaluate_elig: "fst (evaluate es π e) = eligible es π e"
  by (simp add: evaluate_def eligible_def red_cost_def Let_def split: edge_tag.split)

lemma evaluate_inU: "fst (snd (evaluate es π e)) = ent_in_U es e"
  by (simp add: evaluate_def ent_in_U_def Let_def)

lemma evaluate_red:
  assumes "eligible es π e" shows "snd (snd (evaluate es π e)) = red_cost π e"
proof -
  have "fst_all ! e ≠ snd_all ! e" using assms by (simp add: eligible_def)
  thus ?thesis by (simp add: evaluate_def red_cost_def Let_def)
qed

subsection ‹Selecting the most-violating edge›

text ‹Offer a candidate to the flat running best: take it if nothing is held yet (@{term ‹¬ found›}) or
      it is strictly more violating, otherwise keep the incumbent.  Comparison is ∗‹M-free› via
      ‹viol_gt› on the reduced-cost descriptors (bigger big-M coefficient first, then bigger
      ordinary part); no reduced cost is abstracted through @{term bigM}, and ∗‹no option is formed›.›


text ‹Two array lemmas backing the ∗‹swap-with-last› deletion of the minor iteration: the live
      prefix can only shrink (subset), and a still-live element survives the deletion of a
      ∗‹different› one.  No distinctness is needed.›

lemma set_take_img: "nn ≤ length xs ⟹ set (take nn xs) = (λk. xs ! k) ` {0..<nn}"
  by (auto simp: in_set_conv_nth) (metis atLeastLessThan_iff imageI nth_take zero_le)

lemma set_take_swapdel_subset:
  assumes "i < len" "len ≤ length a"
  shows "set (take (len-1) (a[i := a ! (len-1)])) ⊆ set (take len a)"
proof -
  have A: "set (take (len-1) (a[i := a!(len-1)])) = (λk. (a[i := a!(len-1)]) ! k) ` {0..<len-1}"
    using assms by (intro set_take_img) simp
  have B: "set (take len a) = (λk. a ! k) ` {0..<len}" using assms by (intro set_take_img) simp
  show ?thesis unfolding A B using assms by (auto simp: nth_list_update)
qed

lemma mem_survives_swapdel:
  assumes "i < len" "len ≤ length a" "e ∈ set (take len a)" "e ≠ a ! i"
  shows "e ∈ set (take (len-1) (a[i := a ! (len-1)]))"
proof -
  have A: "set (take (len-1) (a[i := a!(len-1)])) = (λk. (a[i := a!(len-1)]) ! k) ` {0..<len-1}"
    using assms by (intro set_take_img) simp
  have B: "set (take len a) = (λk. a ! k) ` {0..<len}" using assms by (intro set_take_img) simp
  from assms(3) B obtain j where j: "j < len" "e = a ! j" by auto
  have jni: "j ≠ i" using j assms(4) by auto
  show ?thesis unfolding A
  proof (cases "j = len-1")
    case True
    have iL: "i < len-1" using assms(1) jni True by linarith
    have "(a[i := a!(len-1)]) ! i = e" using j True assms iL by (simp add: nth_list_update)
    thus "e ∈ (λk. (a[i := a!(len-1)]) ! k) ` {0..<len-1}" using iL by auto
  next
    case False
    hence jL: "j < len-1" using j by linarith
    have "(a[i := a!(len-1)]) ! j = e" using jni j by (simp add: nth_list_update)
    thus "e ∈ (λk. (a[i := a!(len-1)]) ! k) ` {0..<len-1}" using jL by auto
  qed
qed

text ‹And the lemma backing the ∗‹push-at-pointer› insertion of the major iteration.›

lemma take_push_eq:
  assumes "len < length a"
  shows "take (Suc len) (a[len := c]) = take len a @ [c]"
proof -
  have "take (Suc len) (a[len := c]) = take len (a[len := c]) @ [(a[len := c]) ! len]"
    using assms by (simp add: take_Suc_conv_app_nth)
  also have "take len (a[len := c]) = take len a" by simp
  also have "(a[len := c]) ! len = c" using assms by simp
  finally show ?thesis .
qed

lemma set_take_push:
  assumes "len < length a"
  shows "set (take (Suc len) (a[len := c])) = insert c (set (take len a))"
  using take_push_eq[OF assms] by simp

text ‹The running-best invariant @{term bok}: while the ∗‹found› flag is set, the stored edge is
      eligible, its @{term in_U} flag and reduced-cost descriptor are the ones @{const evaluate}
      would compute, and the edge lies in the current live prefix.›


lemma bok_no_best[simp]: "bok es pt no_best a len"
  by (simp add: bok_def no_best_def)

lemma bok_better_keep:
  assumes "bok es pt best a len" "eligible es pt e" "e ∈ set (take len a)"
  shows "bok es pt (better best (e, ent_in_U es e, red_cost pt e)) a len"
  using assms by (cases best) (auto simp: bok_def)

text ‹❙‹Minor iteration›, in a single pass over the live prefix @{term ‹take len a›} of the backing
      array @{term a}.  We walk an index @{term i} (against the pointer @{term len}, never against
      @{term ‹length a›}); a still-eligible entry is kept, priced once, offered to the running best,
      and @{term i} advances; an ineligible (dud) entry is removed by ∗‹swap-with-last› — write the
      last live entry @{term ‹a ! (len - 1)›} into slot @{term i} and drop the pointer, ∗‹without›
      advancing @{term i} — i.e. the ‹O(1)› in-place deletion
      @{text ‹a[i] := a[len - 1]; len := len - 1›}.  The backing list keeps its length (the vacated
      slot @{term ‹len - 1›} is just left behind the pointer); the result is the same array with the
      pointer moved and the most-violating survivor.›


text ‹❙‹Specification of the minor iteration.›  From any live prefix, the single pass returns an
      array of unchanged capacity whose new live prefix is no longer than and contained in the old
      one, the running best stays @{const bok} (so a ∗‹found› result is a genuine eligible edge of the
      prefix), the ∗‹found› flag is monotone, and — crucially for the @{term None} certificate — if the
      pass finds nothing then it has emptied the prefix (@{term ‹rl = i›}, i.e. @{term ‹rl = 0›} from
      the start pointer @{term ‹i = 0›}).  Distinctness plays no role.›

lemma scan_cache_spec:
  "i ≤ len ⟹ len ≤ length a ⟹ bok es pt best a len ⟹
   (case scan_cache es pt i a len best of (ra,rl,rb) ⇒
      length ra = length a ∧ rl ≤ len ∧ set (take rl ra) ⊆ set (take len a)
      ∧ bok es pt rb ra rl ∧ (fst best ⟶ fst rb) ∧ (¬ fst rb ⟶ rl = i))"
proof (induction es pt i a len best rule: scan_cache.induct)
  case (1 es pt i a len best)
  show ?case
  proof (cases "len ≤ i")
    case True
    hence il: "i = len" using 1(3) by simp
    show ?thesis using True 1(3) 1(4) 1(5) by (simp add: scan_cache.simps[of es pt i] il)
  next
    case False
    note nli = False
    have il: "i < len" using nli by simp
    define e where "e = a ! i"
    obtain elig u g where ev: "evaluate es pt e = (elig, u, g)" by (metis prod_cases3)
    have evd1: "elig = eligible es pt e" using ev evaluate_elig[of es pt e] by simp
    have evd2: "u = ent_in_U es e" using ev evaluate_inU[of es pt e] by simp
    show ?thesis
    proof (cases "eligible es pt e")
      case True
      have eligv: "elig" using evd1 True by simp
      have evd3: "g = red_cost pt e" using ev evaluate_red[OF True] by simp
      have ei: "e ∈ set (take len a)" using set_take_img[OF 1(4)] il e_def by auto
      have step: "scan_cache es pt i a len best = scan_cache es pt (Suc i) a len (better best (e,u,g))" using nli ev eligv by (simp add: scan_cache.simps[of es pt i] e_def Let_def)
      have bok2: "bok es pt (better best (e,u,g)) a len" using bok_better_keep[OF 1(5) True ei] evd2 evd3 by simp
      have fnd: "fst (better best (e,u,g))" by (cases best) auto
      have ilsuc: "Suc i ≤ len" using il by simp
      have IH: "(case scan_cache es pt (Suc i) a len (better best (e,u,g)) of (ra,rl,rb) ⇒ length ra = length a ∧ rl ≤ len ∧ set (take rl ra) ⊆ set (take len a) ∧ bok es pt rb ra rl ∧ (fst (better best (e,u,g)) ⟶ fst rb) ∧ (¬ fst rb ⟶ rl = Suc i))" using 1(1)[OF nli e_def ev[symmetric] refl refl eligv ilsuc 1(4) bok2] by simp
      obtain ra rl rb where r: "scan_cache es pt (Suc i) a len (better best (e,u,g)) = (ra,rl,rb)" by (metis prod_cases3)
      have fbest: "fst rb" using IH fnd r by simp
      show ?thesis unfolding step r using IH r fbest by simp
    next
      case False
      have neligv: "¬ elig" using evd1 False by simp
      have step: "scan_cache es pt i a len best = scan_cache es pt i (a[i := a ! (len - 1)]) (len-1) best" using nli ev neligv by (simp add: scan_cache.simps[of es pt i] e_def Let_def)
      have lenlen: "len - 1 ≤ length (a[i := a ! (len - 1)])" using 1(4) by simp
      have ile: "i ≤ len - 1" using il by simp
      have sub2: "set (take (len-1) (a[i := a ! (len - 1)])) ⊆ set (take len a)" using set_take_swapdel_subset[OF il 1(4)] by simp
      have bok2: "bok es pt best (a[i := a ! (len - 1)]) (len-1)"
      proof (cases "fst best")
        case True
        then obtain e0 u0 g0 where b0: "best = (True,e0,u0,g0)" by (cases best) auto
        have elig0: "eligible es pt e0" and mem0: "e0 ∈ set (take len a)" using 1(5) b0 by (auto simp: bok_def)
        have "e0 ≠ e" using elig0 False by (cases "e0 = e") auto
        hence "e0 ∈ set (take (len-1) (a[i := a ! (len - 1)]))" using mem_survives_swapdel[OF il 1(4) mem0] e_def by simp
        thus ?thesis using 1(5) b0 by (auto simp: bok_def)
      next
        case False thus ?thesis by (cases best) (auto simp: bok_def)
      qed
      have IH: "(case scan_cache es pt i (a[i := a ! (len - 1)]) (len-1) best of (ra,rl,rb) ⇒ length ra = length (a[i := a ! (len-1)]) ∧ rl ≤ len-1 ∧ set (take rl ra) ⊆ set (take (len-1) (a[i := a ! (len-1)])) ∧ bok es pt rb ra rl ∧ (fst best ⟶ fst rb) ∧ (¬ fst rb ⟶ rl = i))" using 1(2)[OF nli e_def ev[symmetric] refl refl neligv ile lenlen bok2] by simp
      obtain ra rl rb where r: "scan_cache es pt i (a[i := a ! (len - 1)]) (len-1) best = (ra,rl,rb)" by (metis prod_cases3)
      show ?thesis unfolding step r using IH r sub2 1(4) by auto
    qed
  qed
qed

subsection ‹Major iteration: block search over the arc array›

text ‹One straight sweep with three counters: @{term fuel} arcs remain to be scanned overall,
      @{term bpos} arcs remain in the current block (‹0› marks a block boundary), and @{term len}
      tracks @{term ‹length cand›} in ‹O(1)› so the ceiling/floor tests never re-measure the list.
      We refill up to @{term max_candidates} (ceiling) and stop pulling new blocks once the pointer
      reaches @{term min_candidates} (floor, checked only at boundaries).  An inserted edge is
      ∗‹pushed at the pointer› — @{text ‹a[len] := cur; len := len + 1›}, the @{const list_update}
      @{term ‹a[len := cur]›} — overwriting the stale slot rather than growing the list, so the
      backing array keeps its capacity and nothing is allocated.  The bookmark advances cyclically by a
      ∗‹conditional reset› @{term ‹if cur + 1 = mc then 0 else cur + 1›} rather than a modulo — a
      compare instead of a division — which coincides with @{term ‹(cur + 1) mod mc›} on every state
      reached from a legal bookmark @{term ‹cur < mc›}.  The arc count @{term mc} (always @{term marc})
      is threaded as a ∗‹fixed loop parameter›, so the wrap bound is read from a register each iteration
      rather than re-deriving the locale constant @{term marc} (hence never re-running @{term build_tree}).
      The best edge seen is accumulated for immediate return; termination is by the strictly decreasing
      @{term fuel}.›


text ‹Cyclic-sweep arithmetic for the block bookmark: the conditional wrap coincides with
      @{term ‹(cur + 1) mod mc›} and stays in range, and a full sweep of @{term mc} consecutive
      residues from any start covers every arc.›

lemma wrap_eq: "cur < (mc::nat) ⟹ (if cur + 1 = mc then 0 else cur + 1) = (cur + 1) mod mc"
  by (cases "cur + 1 = mc") (auto simp: mod_less)

lemma wrap_lt: "0 < (mc::nat) ⟹ cur < mc ⟹ (if cur + 1 = mc then 0 else cur + 1) < mc"
  by auto

lemma cyc_cover:
  assumes A: "0 < (mc::nat)" and B: "cur < mc" and C: "e < mc"
  shows "∃t<mc. (cur + t) mod mc = e"
proof -
  let ?t = "(e + mc - cur) mod mc"
  have t1: "?t < mc" using A by simp
  have ar: "cur + (e + mc - cur) = e + mc" using B by simp
  have "(cur + ?t) mod mc = (cur + (e + mc - cur)) mod mc" by (metis mod_add_right_eq)
  also have "... = (e + mc) mod mc" using ar by simp
  also have "... = e" using C by simp
  finally have "(cur + ?t) mod mc = e" .
  thus ?thesis using t1 by blast
qed

text ‹The ∗‹found› flag of the major iteration is monotone.›

lemma scan_found_mono:
  "scan es pt mc fuel bpos cur a len best = (cur2,a2,len2,best2) ⟹ fst best ⟹ fst best2"
proof (induction es pt mc fuel bpos cur a len best arbitrary: cur2 a2 len2 best2 rule: scan.induct)
  case (1 es pt mc fuel bpos cur a len best)
  show ?case
  proof (cases "fuel = 0 ∨ max_candidates ≤ len ∨ (bpos = 0 ∧ min_candidates ≤ len)")
    case True
    hence "scan es pt mc fuel bpos cur a len best = (cur,a,len,best)" by (auto simp: scan.simps[of es pt mc fuel])
    thus ?thesis using 1(2) 1(3) by simp
  next
    case False
    from False have g1: "fuel ≠ 0" and g2: "¬ max_candidates ≤ len" and g3: "¬ (bpos = 0 ∧ min_candidates ≤ len)" by auto
    obtain elig u g where ev: "evaluate es pt cur = (elig,u,g)" by (metis prod_cases3)
    have step: "scan es pt mc fuel bpos cur a len best = scan es pt mc (fuel-1) ((if bpos=0 then block_size else bpos)-1) (if cur+1=mc then 0 else cur+1) (if elig then a[len:=cur] else a) (if elig then Suc len else len) (if elig then better best (cur,u,g) else best)" using g1 g2 g3 ev by (auto simp: scan.simps[of es pt mc fuel] Let_def)
    have fb1: "fst (if elig then better best (cur,u,g) else best)" using 1(3) by (cases best) auto
    have subeq: "scan es pt mc (fuel-1) ((if bpos=0 then block_size else bpos)-1) (if cur+1=mc then 0 else cur+1) (if elig then a[len:=cur] else a) (if elig then Suc len else len) (if elig then better best (cur,u,g) else best) = (cur2,a2,len2,best2)" using 1(2) step by simp
    show ?thesis using 1(1)[OF g1 g2 g3 refl ev[symmetric] refl refl refl refl refl refl subeq] fb1 by simp
  qed
qed

text ‹❙‹The @{term None} certificate of the major iteration.›  If the sweep returns with nothing
      found, then it consumed its whole fuel with no eligible arc ∗‹anywhere› on the cyclic run — the
      precondition @{term ‹¬ fst best ⟶ len = 0›} (no insert without a find) rules out the
      ceiling/floor bail-outs.›

lemma scan_none:
  "scan es pt mc fuel bpos cur a len best = (cur2,a2,len2,best2) ⟹ ¬ fst best2 ⟹ (¬ fst best ⟶ len = 0) ⟹ 0 < min_candidates ⟹ 0 < max_candidates ⟹ cur < mc ⟹ 0 < mc ⟹ (∀t<fuel. ¬ eligible es pt ((cur + t) mod mc))"
proof (induction es pt mc fuel bpos cur a len best arbitrary: cur2 a2 len2 best2 rule: scan.induct)
  case (1 es pt mc fuel bpos cur a len best)
  show ?case
  proof (cases "fuel = 0")
    case True thus ?thesis by simp
  next
    case False
    have nfb: "¬ fst best" using scan_found_mono[OF 1(2)] 1(3) by blast
    have nlen: "len = 0" using nfb 1(4) by simp
    have g2: "¬ max_candidates ≤ len" using nlen 1(6) by simp
    have g3: "¬ (bpos = 0 ∧ min_candidates ≤ len)" using nlen 1(5) by simp
    obtain elig u g where ev: "evaluate es pt cur = (elig,u,g)" by (metis prod_cases3)
    have step: "scan es pt mc fuel bpos cur a len best = scan es pt mc (fuel-1) ((if bpos=0 then block_size else bpos)-1) (if cur+1=mc then 0 else cur+1) (if elig then a[len:=cur] else a) (if elig then Suc len else len) (if elig then better best (cur,u,g) else best)" using False g2 g3 ev by (auto simp: scan.simps[of es pt mc fuel] Let_def)
    have subeq: "scan es pt mc (fuel-1) ((if bpos=0 then block_size else bpos)-1) (if cur+1=mc then 0 else cur+1) (if elig then a[len:=cur] else a) (if elig then Suc len else len) (if elig then better best (cur,u,g) else best) = (cur2,a2,len2,best2)" using 1(2) step by simp
    have curnel: "¬ eligible es pt cur"
    proof
      assume ec: "eligible es pt cur"
      hence "elig" using ev evaluate_elig[of es pt cur] by simp
      hence "fst (if elig then better best (cur,u,g) else best)" by (cases best) auto
      hence "fst best2" using scan_found_mono[OF subeq] by simp
      thus False using 1(3) by simp
    qed
    have cm: "cur mod mc = cur" using 1(7) by simp
    have t0: "¬ eligible es pt ((cur + 0) mod mc)" using curnel cm by simp
    have cur1lt: "(if cur+1=mc then 0 else cur+1) < mc" using wrap_lt[OF 1(8) 1(7)] by simp
    have cur1eq: "(if cur+1=mc then 0 else cur+1) = (cur + 1) mod mc" using wrap_eq[OF 1(7)] by simp
    have subPlen: "¬ fst (if elig then better best (cur,u,g) else best) ⟶ (if elig then Suc len else len) = 0" using 1(4) by (cases elig; cases best; auto)
    have IH: "∀t<fuel-1. ¬ eligible es pt (((if cur+1=mc then 0 else cur+1) + t) mod mc)" using 1(1)[OF False g2 g3 refl ev[symmetric] refl refl refl refl refl refl subeq 1(3) subPlen 1(5) 1(6) cur1lt 1(8)] .
    show ?thesis
    proof (intro allI impI)
      fix t assume tf: "t < fuel"
      show "¬ eligible es pt ((cur + t) mod mc)"
      proof (cases "t = 0")
        case True thus ?thesis using t0 by simp
      next
        case False
        hence tm: "t - 1 < fuel - 1" using tf by simp
        have ne: "¬ eligible es pt (((if cur+1=mc then 0 else cur+1) + (t-1)) mod mc)" using IH tm by blast
        have "((if cur+1=mc then 0 else cur+1) + (t-1)) mod mc = ((cur + 1) mod mc + (t-1)) mod mc" using cur1eq by simp
        also have "... = ((cur + 1) + (t-1)) mod mc" by (rule mod_add_left_eq)
        also have "... = (cur + t) mod mc" using False by simp
        finally show ?thesis using ne by simp
      qed
    qed
  qed
qed

text ‹❙‹The insertion-side invariants of the major iteration.›  The candidate array keeps its capacity,
      the pointer never exceeds it, the bookmark stays in range, every candidate is a real arc, and the
      running best stays @{const bok}.›

lemma scan_some_spec:
  "scan es pt mc fuel bpos cur a len best = (cur2,a2,len2,best2) ⟹ 0 < mc ⟹ cur < mc ⟹ length a = max_candidates ⟹ len ≤ max_candidates ⟹ set (take len a) ⊆ {0..<mc} ⟹ bok es pt best a len ⟹ 0 < max_candidates ⟹ length a2 = max_candidates ∧ len2 ≤ max_candidates ∧ cur2 < mc ∧ set (take len2 a2) ⊆ {0..<mc} ∧ bok es pt best2 a2 len2"
proof (induction es pt mc fuel bpos cur a len best arbitrary: cur2 a2 len2 best2 rule: scan.induct)
  case (1 es pt mc fuel bpos cur a len best)
  show ?case
  proof (cases "fuel = 0 ∨ max_candidates ≤ len ∨ (bpos = 0 ∧ min_candidates ≤ len)")
    case True
    hence "scan es pt mc fuel bpos cur a len best = (cur,a,len,best)" by (auto simp: scan.simps[of es pt mc fuel])
    hence "(cur2,a2,len2,best2) = (cur,a,len,best)" using 1(2) by simp
    thus "length a2 = max_candidates ∧ len2 ≤ max_candidates ∧ cur2 < mc ∧ set (take len2 a2) ⊆ {0..<mc} ∧ bok es pt best2 a2 len2" using 1(4) 1(5) 1(6) 1(7) 1(8) by simp
  next
    case False
    from False have g1: "fuel ≠ 0" and g2: "¬ max_candidates ≤ len" and g3: "¬ (bpos = 0 ∧ min_candidates ≤ len)" by auto
    have lla: "len < length a" using g2 1(5) by simp
    obtain elig u g where ev: "evaluate es pt cur = (elig,u,g)" by (metis prod_cases3)
    have evd1: "elig = eligible es pt cur" using ev evaluate_elig[of es pt cur] by simp
    have evd2: "u = ent_in_U es cur" using ev evaluate_inU[of es pt cur] by simp
    have step: "scan es pt mc fuel bpos cur a len best = scan es pt mc (fuel-1) ((if bpos=0 then block_size else bpos)-1) (if cur+1=mc then 0 else cur+1) (if elig then a[len:=cur] else a) (if elig then Suc len else len) (if elig then better best (cur,u,g) else best)" using g1 g2 g3 ev by (auto simp: scan.simps[of es pt mc fuel] Let_def)
    have subeq: "scan es pt mc (fuel-1) ((if bpos=0 then block_size else bpos)-1) (if cur+1=mc then 0 else cur+1) (if elig then a[len:=cur] else a) (if elig then Suc len else len) (if elig then better best (cur,u,g) else best) = (cur2,a2,len2,best2)" using 1(2) step by simp
    have s_cur: "(if cur+1=mc then 0 else cur+1) < mc" using wrap_lt[OF 1(3) 1(4)] by simp
    have s_len_a: "length (if elig then a[len:=cur] else a) = max_candidates" using 1(5) by (cases elig) simp_all
    have s_len: "(if elig then Suc len else len) ≤ max_candidates" using 1(6) g2 by (cases elig) auto
    have s_range: "set (take (if elig then Suc len else len) (if elig then a[len:=cur] else a)) ⊆ {0..<mc}"
    proof (cases elig)
      case True
      have "set (take (Suc len) (a[len:=cur])) = insert cur (set (take len a))" using set_take_push[OF lla] by simp
      thus ?thesis using True 1(4) 1(7) by auto
    next
      case False thus ?thesis using 1(7) by simp
    qed
    have s_bok: "bok es pt (if elig then better best (cur,u,g) else best) (if elig then a[len:=cur] else a) (if elig then Suc len else len)"
    proof (cases elig)
      case True
      have ec: "eligible es pt cur" using evd1 True by simp
      have evd3: "g = red_cost pt cur" using ev evaluate_red[OF ec] by simp
      have setpush: "set (take (Suc len) (a[len:=cur])) = insert cur (set (take len a))" using set_take_push[OF lla] by simp
      have "bok es pt (better best (cur,u,g)) (a[len:=cur]) (Suc len)" using ec evd2 evd3 setpush 1(8) by (cases best) (auto simp: bok_def)
      thus ?thesis using True by simp
    next
      case False thus ?thesis using 1(8) by simp
    qed
    have IH: "length a2 = max_candidates ∧ len2 ≤ max_candidates ∧ cur2 < mc ∧ set (take len2 a2) ⊆ {0..<mc} ∧ bok es pt best2 a2 len2" using 1(1)[OF g1 g2 g3 refl ev[symmetric] refl refl refl refl refl refl subeq 1(3) s_cur s_len_a s_len s_range s_bok 1(9)] by simp
    thus "length a2 = max_candidates ∧ len2 ≤ max_candidates ∧ cur2 < mc ∧ set (take len2 a2) ⊆ {0..<mc} ∧ bok es pt best2 a2 len2" .
  qed
qed

text ‹❙‹From the M-free eligibility test to the true reduced-cost sign.›  Under the reduced-cost
      invariant these turn the executable @{const eligible} test into the sign of the abstract reduced
      cost @{term ‹pval_abstract bigM (red_cost pt e)›}.›

lemma elig_L: "rc_invar (red_cost pt e) ⟹ nth es e = InL ⟹ eligible es pt e = (fst_all ! e ≠ snd_all ! e ∧ pval_abstract bigM (red_cost pt e) < 0)"
  by (simp add: eligible_def pval_neg_abstract)

lemma elig_U: "rc_invar (red_cost pt e) ⟹ nth es e = InU ⟹ eligible es pt e = (fst_all ! e ≠ snd_all ! e ∧ 0 < pval_abstract bigM (red_cost pt e))"
  by (simp add: eligible_def pval_pos_abstract)

text ‹A found eligible edge is guaranteed a ∗‹non-self-loop› (the self-loop skip added to
      @{const eligible}) on top of the sign of its reduced cost.›

lemma sign_helper:
  assumes rc: "rc_invar (red_cost pt e)" and el: "eligible es pt e" and iu: "in_U = ent_in_U es e"
  shows "fst_all ! e ≠ snd_all ! e ∧ (if in_U then nth es e = InU ∧ 0 < pval_abstract bigM (red_cost pt e) else nth es e = InL ∧ pval_abstract bigM (red_cost pt e) < 0)"
proof (intro conjI)
  show "fst_all ! e ≠ snd_all ! e" using el by (simp add: eligible_def)
next
  show "(if in_U then nth es e = InU ∧ 0 < pval_abstract bigM (red_cost pt e) else nth es e = InL ∧ pval_abstract bigM (red_cost pt e) < 0)"
  proof (cases "nth es e")
    case InTree thus ?thesis using el by (simp add: eligible_def)
  next
    case InL
    hence "¬ in_U" using iu by (simp add: ent_in_U_def)
    thus ?thesis using InL el elig_L[OF rc InL] by simp
  next
    case InU
    hence "in_U" using iu by (simp add: ent_in_U_def)
    thus ?thesis using InU el elig_U[OF rc InU] by simp
  qed
qed


subsection ‹The selection function and the selector invariant›

text ‹Try the cache first; on a hit keep the pruned survivors (bookmark unchanged).  Otherwise run a
      major iteration from the bookmark: return its best, or @{term None} if the whole arc set was
      swept without finding an eligible edge.›


text ‹The selector invariant records only structural facts about the state — it cannot mention
      @{term π} (the ADT invariant sees the selector alone), which is exactly why the minor iteration
      re-validates every cached edge before returning it.  The range bound is stated about the
      ∗‹live prefix› @{term ‹take (sel_len sel) (sel_arr sel)›} (its members are genuine arcs, so a
      returned edge lies in @{term ℰ}); the stale tail beyond the pointer is unconstrained.  The fixed
      capacity is pinned by @{term ‹length (sel_arr sel) = max_candidates›}, which keeps the pointer a
      legal index for insertion.  Candidate-list ∗‹distinctness› is deliberately ∗‹not› asserted: the
      ADT axioms never need it (the loop treats ‹sel_invar_impl› abstractly), so requiring it
      would be pure proof cost.›



lemma sel_invar_init_sel: "sel_invar_impl init_sel"
  by (simp add: sel_invar_impl_def init_sel_def)


subsection ‹Pricing bridge: reduced-cost faithfulness from the good-potential invariant›

text ‹The remaining ADT obligation.  The two selector theorems above are stated with the abstract
      reduced cost @{term ‹pval_abstract bigM (red_cost π e)›} and a hypothesis
      @{term ‹rc_invar (red_cost π e)›}.  Both are discharged from the good-potential invariant that the
      network-simplex loop maintains: every stored potential value is a signed cost sum over augmented
      edges touching the artificial root @{term vcount} at most once (the descriptor-level
      ‹good_pot_val_c›, the concrete instance of @{term good_pot_val}), and the root's own
      potential is zero.  Under it the coefficient of every potential lies in @{term ‹{- 1, 0, 1}›} and
      its ordinary part is bounded by @{term ‹sum_list (map abs cost_list)›}; the clamped tag arithmetic
      is then ∗‹faithful› because the reduced-cost coefficient never leaves @{term ‹{- 2 .. 2}›} (an
      artificial edge always has the coefficient-zero root as one endpoint, ruling out ‹\<pm> 3›).›

lemma pval_plus_faithful_coeff: "- 2 ≤ of_mtag (fst p) + of_mtag (fst g) ⟹ of_mtag (fst p) + of_mtag (fst g) ≤ 2 ⟹ pval_abstract bigM (pval_plus p g) = pval_abstract bigM p + pval_abstract bigM g"
  unfolding pval_abstract_def pval_plus_def tag_add_def by (simp add: of_mtag_mtag_of algebra_simps h_add)

lemma pval_minus_faithful_coeff: "- 2 ≤ of_mtag (fst p) - of_mtag (fst g) ⟹ of_mtag (fst p) - of_mtag (fst g) ≤ 2 ⟹ pval_abstract bigM (pval_minus p g) = pval_abstract bigM p - pval_abstract bigM g"
  unfolding pval_abstract_def pval_minus_def tag_sub_def by (simp add: of_mtag_mtag_of algebra_simps)

lemma pval_plus_coeff: "- 2 ≤ of_mtag (fst p) + of_mtag (fst g) ⟹ of_mtag (fst p) + of_mtag (fst g) ≤ 2 ⟹ of_mtag (fst (pval_plus p g)) = of_mtag (fst p) + of_mtag (fst g)"
  unfolding pval_plus_def tag_add_def by (simp add: of_mtag_mtag_of)

lemma pval_minus_coeff: "- 2 ≤ of_mtag (fst p) - of_mtag (fst g) ⟹ of_mtag (fst p) - of_mtag (fst g) ≤ 2 ⟹ of_mtag (fst (pval_minus p g)) = of_mtag (fst p) - of_mtag (fst g)"
  unfolding pval_minus_def tag_sub_def by (simp add: of_mtag_mtag_of)

definition good_pot_val_c :: "mtag × 'n ⇒ bool" where "good_pot_val_c p = (∃A D. A ⊆ {0..<m+Kart} ∧ D ⊆ {0..<m+Kart} ∧ card {e ∈ A ∪ D. fst_all ! e = vcount ∨ snd_all ! e = vcount} ≤ 1 ∧ pval_abstract bigM p = (∑e∈A. cost_all ! e) - (∑e∈D. cost_all ! e))"

lemma gpv_coeff:
  assumes gp: "good_pot_val_c p" and pv: "pv_invar p"
  shows "of_mtag (fst p) ∈ {- 1, 0, 1} ∧ ¦snd p¦ ≤ sum_list (map abs cost_list)"
proof -
  define sabs where "sabs = h (sum_list (map abs cost_list))"
  have sabs0: "0 ≤ sabs" using sabs_nonneg by (simp add: sabs_def)
  have bM: "bigM = 6 * sabs + 1" by (simp add: bigM_def sabs_def)
  obtain A D where AD: "A ⊆ {0..<m+Kart}" "D ⊆ {0..<m+Kart}" "card {e ∈ A ∪ D. fst_all ! e = vcount ∨ snd_all ! e = vcount} ≤ 1" "pval_abstract bigM p = (∑e∈A. cost_all ! e) - (∑e∈D. cost_all ! e)" using gp by (auto simp: good_pot_val_c_def)
  obtain e0 R where dec: "e0 ∈ {- 1, 0, 1}" "¦R¦ ≤ sabs" "(∑e∈A. cost_all ! e) - (∑e∈D. cost_all ! e) = real_of_int e0 * bigM + R" using cost_decompose[OF AD(1) AD(2) AD(3)] by (auto simp: sabs_def)
  define c where "c = of_mtag (fst p)"
  have absp: "pval_abstract bigM p = real_of_int c * bigM + h (snd p)" by (simp add: pval_abstract_def c_def)
  have pb: "¦h (snd p)¦ ≤ 2 * sabs" using h_pv_bound[OF pv] by (simp add: sabs_def)
  have eqn: "real_of_int (c - e0) * bigM = R - h (snd p)" using absp AD(4) dec(3) by (simp add: algebra_simps)
  have bnd: "¦R - h (snd p)¦ < bigM"
  proof -
    have "¦R - h (snd p)¦ ≤ ¦R¦ + ¦h (snd p)¦" by simp
    also have "... ≤ sabs + 2 * sabs" using dec(2) pb by linarith
    also have "... < bigM" using bM sabs0 by linarith
    finally show ?thesis .
  qed
  have "¦real_of_int (c - e0)¦ * bigM < bigM" using eqn bnd by (simp add: abs_mult)
  hence lt1: "¦real_of_int (c - e0)¦ < 1" using bigM_pos by simp
  have n0: "c - e0 = 0"
  proof -
    have "real_of_int ¦c - e0¦ < 1" using lt1 by (simp add: of_int_abs)
    hence "¦c - e0¦ < 1" by (metis of_int_1 of_int_less_iff)
    thus ?thesis by linarith
  qed
  hence ceq: "c = e0" by simp
  have Req: "h (snd p) = R" using eqn n0 by simp
  have sndbnd: "¦snd p¦ ≤ sum_list (map abs cost_list)"
  proof -
    have "¦h (snd p)¦ ≤ h (sum_list (map abs cost_list))" using Req dec(2) by (simp add: sabs_def)
    thus ?thesis by (simp add: h_abs[symmetric])
  qed
  show ?thesis using ceq dec(1) sndbnd by (simp add: c_def)
qed

lemma costlist_bound: "e < m ⟹ ¦cost_list ! e¦ ≤ sum_list (map abs cost_list)"
proof -
  { assume e: "e < m"
    have mem: "¦cost_list ! e¦ ∈ set (map abs cost_list)" using e length_cost_list_m by (metis length_map nth_map nth_mem)
    have "¦cost_list ! e¦ ≤ sum_list (map abs cost_list)" by (rule member_le_sum_list[OF mem]) auto }
  thus "e < m ⟹ ¦cost_list ! e¦ ≤ sum_list (map abs cost_list)" by blast
qed

text ‹A good potential value whose ∗‹abstract› reading is @{term ‹0::real›} has M-coefficient
      exactly @{term ‹0::int›}: the ordinary part is bounded by @{term ‹sum_list (map abs cost_list)›}
      and the M-coefficient lives in @{term ‹{- 1, 0, 1}›}, while @{term bigM} exceeds that bound, so no
      nonzero coefficient can cancel to zero. This is what lets the abstract root-potential-zero
      precondition of the network-simplex ADT stand in for the concrete @{term pval_zero} the pricing
      used before.›

lemma gpv_root_zero:
  assumes g: "good_pot_val_c p" and pv: "pv_invar p" and z: "pval_abstract bigM p = 0"
  shows "of_mtag (fst p) = 0"
proof -
  define sabs where "sabs = h (sum_list (map abs cost_list))"
  have b1: "of_mtag (fst p) ∈ {- 1, 0, 1}" using gpv_coeff[OF g pv] by simp
  have b2: "¦h (snd p)¦ ≤ sabs"
  proof -
    have "¦snd p¦ ≤ sum_list (map abs cost_list)" using gpv_coeff[OF g pv] by simp
    hence "h ¦snd p¦ ≤ h (sum_list (map abs cost_list))" by (rule h_mono)
    thus ?thesis by (simp add: h_abs sabs_def)
  qed
  have bM: "bigM = 6 * sabs + 1" by (simp add: bigM_def sabs_def)
  have s0: "0 ≤ sabs" using sabs_nonneg by (simp add: sabs_def)
  have b2': "- sabs ≤ h (snd p)" "h (snd p) ≤ sabs" using b2 by auto
  have eq: "real_of_int (of_mtag (fst p)) * bigM + h (snd p) = 0" using z by (simp add: pval_abstract_def)
  from b1 consider "of_mtag (fst p) = -1" | "of_mtag (fst p) = 0" | "of_mtag (fst p) = 1" by auto
  thus ?thesis
  proof cases
    case 1
    have "real_of_int (-1) * bigM + h (snd p) = 0" using eq 1 by simp
    hence False using b2' bM s0 by simp
    thus ?thesis by simp
  next
    case 2 thus ?thesis .
  next
    case 3
    have "real_of_int 1 * bigM + h (snd p) = 0" using eq 3 by simp
    hence False using b2' bM s0 by simp
    thus ?thesis by simp
  qed
qed

text ‹Every augmented edge (@{term ‹e < marc›}) has both endpoints in the arborescence carrier
      @{term Varb} — real endpoints in @{term ‹set vs_list›} (@{thm fst_snd_vs}), artificial endpoints
      in @{term ‹insert vcount (set vs_list)›} (@{thm build_tree_tail_sub}). Hence the pricing only ever
      reads potentials at vertices where the good-potential invariant is known.›

lemma endpt_in_Varb:
  assumes "e < marc" shows "fst_all ! e ∈ Varb ∧ snd_all ! e ∈ Varb"
proof (cases "e < m")
  case True
  have fe: "fst_all ! e = fst_list ! e" and se: "snd_all ! e = snd_list ! e"
    using True by (simp_all add: fst_all_real snd_all_real)
  have "fst_list ! e ∈ set fst_list ∪ set snd_list" using True by (metis UnI1 len_fst_list_m nth_mem)
  moreover have "snd_list ! e ∈ set fst_list ∪ set snd_list" using True by (metis UnI2 len_snd_list_m nth_mem)
  ultimately have "fst_list ! e ∈ Vseen" "snd_list ! e ∈ Vseen"
    using edged_in_V V_sub_Vseen by auto
  thus ?thesis using fe se by (simp add: Varb_def)
next
  case False
  have emK: "e < m + Kart" using assms by (simp add: marc_def)
  define k where "k = e - m"
  have kdef: "e = m + k" using False by (simp add: k_def)
  have kK: "k < Kart" using emK kdef by simp
  have "ds_afst (build_tree acyc_flow) ! k ∈ insert vcount Vseen ∧ ds_asnd (build_tree acyc_flow) ! k ∈ insert vcount Vseen"
    using build_tree_tail_sub kK by (simp add: tail_sub_def Kart_def seen_set_build_tree)
  moreover have "fst_all ! e = ds_afst (build_tree acyc_flow) ! k" "snd_all ! e = ds_asnd (build_tree acyc_flow) ! k"
    using kdef kK by (simp_all add: fst_all_art snd_all_art)
  ultimately show ?thesis by (simp add: Varb_def)
qed

text ‹The potential store is ∗‹good› when every arborescence vertex carries a good potential value
      (invariant @{const good_pot_val_c} and descriptor bound @{const pv_invar}) and the root
      @{const vcount} reads abstractly as @{term ‹0::real›}. This is exactly what the network-simplex
      selection precondition supplies once @{term pot_value_invar} is instantiated to the good-potential
      predicate and the abstract root-zero precondition is available; the quantifier ranges over
      @{term Varb} (= the graph vertex set) rather than @{term ‹{0..<vcount}›}, matching the vertex names
      the algorithm actually uses.›

definition pot_ok :: "(mtag × 'n) list ⇒ bool" where
  "pot_ok pt = ((∀v∈Varb. good_pot_val_c (nth pt v) ∧ pv_invar (nth pt v))
                 ∧ pval_abstract bigM (nth pt vcount) = 0)"

lemma plook_bound:
  assumes ok: "pot_ok pt" and x: "x ∈ Varb"
  shows "of_mtag (fst (nth pt x)) ∈ {- 1, 0, 1} ∧ ¦snd (nth pt x)¦ ≤ sum_list (map abs cost_list)"
proof -
  have "good_pot_val_c (nth pt x) ∧ pv_invar (nth pt x)"
    using ok x by (simp add: pot_ok_def)
  thus ?thesis using gpv_coeff by blast
qed

lemma endpt_le:
  assumes "e < m + Kart" shows "fst_all ! e ≤ vcount ∧ snd_all ! e ≤ vcount"
proof (cases "e < m")
  case True
  thus ?thesis using real_fst_lt_vcount[of e] real_snd_lt_vcount[of e] by simp
next
  case False
  then obtain k where k: "e = m + k" "k < Kart" using assms by (metis add.commute le_Suc_ex not_le nat_add_left_cancel_less add_diff_inverse_nat)
  have tok: "tail_edge_ok (build_tree acyc_flow) k" using k(2) tail_edge_ok_build_tree by simp
  then obtain subj where s: "subj < vcount"
    "ds_afst (build_tree acyc_flow) ! k = (if art_dir subj then subj else vcount)"
    "ds_asnd (build_tree acyc_flow) ! k = (if art_dir subj then vcount else subj)"
    unfolding tail_edge_ok_def by auto
  show ?thesis using k s by (cases "art_dir subj"; auto simp: fst_all_art snd_all_art)
qed

lemma red_cost_faithful:
  assumes ok: "pot_ok pt" and em: "e < marc"
  shows "rc_invar (red_cost pt e) ∧ pval_abstract bigM (red_cost pt e) = cost_all ! e + pval_abstract bigM (nth pt (fst_all ! e)) - pval_abstract bigM (nth pt (snd_all ! e))"
proof -
  define sabs where "sabs = sum_list (map abs cost_list)"
  have sabs0: "0 ≤ sabs" using sabs_nonneg by (simp add: sabs_def)
  have emK: "e < m + Kart" using em by (simp add: marc_def)
  have lef: "fst_all ! e ∈ Varb" and les: "snd_all ! e ∈ Varb" using endpt_in_Varb[OF em] by auto
  define pf where "pf = nth pt (fst_all ! e)"
  define ps where "ps = nth pt (snd_all ! e)"
  have bf: "of_mtag (fst pf) ∈ {- 1, 0, 1}" "¦snd pf¦ ≤ sabs" using plook_bound[OF ok lef] by (auto simp: pf_def sabs_def)
  have bs: "of_mtag (fst ps) ∈ {- 1, 0, 1}" "¦snd ps¦ ≤ sabs" using plook_bound[OF ok les] by (auto simp: ps_def sabs_def)
  define cf where "cf = of_mtag (fst pf)"
  define cs where "cs = of_mtag (fst ps)"
  have dmb: "- 2 ≤ cf - cs" "cf - cs ≤ 2" using bf(1) bs(1) by (auto simp: cf_def cs_def)
  have df_abs: "pval_abstract bigM (pval_minus pf ps) = pval_abstract bigM pf - pval_abstract bigM ps" using pval_minus_faithful_coeff dmb by (simp add: cf_def cs_def)
  have df_coeff: "of_mtag (fst (pval_minus pf ps)) = cf - cs" using pval_minus_coeff dmb by (simp add: cf_def cs_def)
  have df_snd: "snd (pval_minus pf ps) = snd pf - snd ps" by (simp add: pval_minus_def)
  have redeq: "red_cost pt e = pval_plus (cost_pval e) (pval_minus pf ps)" by (simp add: red_cost_def pf_def ps_def)
  have ce_abs: "pval_abstract bigM (cost_pval e) = cost_all ! e"
  proof (cases "e < m")
    case True thus ?thesis by (simp add: cost_pval_def pval_abstract_def cost_all_real)
  next
    case False
    hence "cost_pval e = pval_M" by (simp add: cost_pval_def)
    thus ?thesis using emK False by (simp add: pval_M_def pval_abstract_def cost_all_art')
  qed
  have ce_coeff: "of_mtag (fst (cost_pval e)) = (if e < m then 0 else 1)" by (simp add: cost_pval_def pval_M_def)
  have ce_snd: "¦snd (cost_pval e)¦ ≤ sabs"
  proof (cases "e < m")
    case True thus ?thesis using costlist_bound by (simp add: cost_pval_def sabs_def)
  next
    case False thus ?thesis using sabs0 by (simp add: cost_pval_def pval_M_def)
  qed
  have outer: "- 2 ≤ of_mtag (fst (cost_pval e)) + (cf - cs) ∧ of_mtag (fst (cost_pval e)) + (cf - cs) ≤ 2"
  proof (cases "e < m")
    case True thus ?thesis using ce_coeff dmb by simp
  next
    case False
    have tr: "fst_all ! e = vcount ∨ snd_all ! e = vcount" using touches_root_iff[OF emK] False by simp
    have z: "cf = 0 ∨ cs = 0"
    proof (cases "fst_all ! e = vcount")
      case True
      have pfv: "pf = nth pt vcount" using True by (simp add: pf_def)
      have g: "good_pot_val_c pf" and pv: "pv_invar pf" using ok r_in_V pfv by (auto simp: pot_ok_def)
      have zz: "pval_abstract bigM pf = 0" using ok pfv by (simp add: pot_ok_def)
      have "of_mtag (fst pf) = 0" using gpv_root_zero[OF g pv zz] .
      thus ?thesis by (simp add: cf_def)
    next
      case False
      hence sv: "snd_all ! e = vcount" using tr by simp
      have psv: "ps = nth pt vcount" using sv by (simp add: ps_def)
      have g: "good_pot_val_c ps" and pv: "pv_invar ps" using ok r_in_V psv by (auto simp: pot_ok_def)
      have zz: "pval_abstract bigM ps = 0" using ok psv by (simp add: pot_ok_def)
      have "of_mtag (fst ps) = 0" using gpv_root_zero[OF g pv zz] .
      thus ?thesis by (simp add: cs_def)
    qed
    show ?thesis using ce_coeff False z bf(1) bs(1) by (auto simp: cf_def cs_def)
  qed
  have "pval_abstract bigM (red_cost pt e) = pval_abstract bigM (cost_pval e) + pval_abstract bigM (pval_minus pf ps)"
    unfolding redeq using pval_plus_faithful_coeff[of "cost_pval e" "pval_minus pf ps"] outer df_coeff by simp
  also have "... = cost_all ! e + pval_abstract bigM pf - pval_abstract bigM ps" using ce_abs df_abs by simp
  finally have faith: "pval_abstract bigM (red_cost pt e) = cost_all ! e + pval_abstract bigM pf - pval_abstract bigM ps" .
  have "snd (red_cost pt e) = snd (cost_pval e) + snd (pval_minus pf ps)" unfolding redeq by (simp add: pval_plus_def)
  hence "¦snd (red_cost pt e)¦ ≤ ¦snd (cost_pval e)¦ + ¦snd pf¦ + ¦snd ps¦" using df_snd by simp
  also have "... ≤ 3 * sabs" using ce_snd bf(2) bs(2) by simp
  finally have rci: "rc_invar (red_cost pt e)" by (simp add: rc_invar_def sabs_def)
  show ?thesis using rci faith by (simp add: pf_def ps_def)
qed


subsection ‹Preservation of the potential invariant under the network-simplex conditions›

text ‹The strengthened potential invariant is ‹pval_pot_invar›: the descriptor bound
      @{const pv_invar} together with the good-potential certificate ‹good_pot_val_c›.  Under
      exactly the preconditions the network-simplex locale prescribes for its mixed potential
      arithmetic (@{thm[source] pot_plus_faithful} / @{thm[source] pot_minus_faithful}: the operand
      invariants and the ‹≤ 1›-root-touch signed-cost-sum certificate for the ∗‹result›), a
      @{const pval_plus} / @{const pval_minus} step keeps the invariant.  The certificate needs no work
      of its own: once faithfulness rewrites @{term ‹pval_abstract bigM (pval_plus p g)›} to
      @{term ‹pval_abstract bigM p + pval_abstract bigM g›}, the very sets @{term A}, @{term D} witnessing
      the precondition witness ‹good_pot_val_c› of the result.  These two lemmas are the concrete
      @{text pot_value_plus_spec} / @{text pot_value_minus_spec} obligations of @{locale network_simplex_spec}
      with @{term pot_value_invar} instantiated to ‹pval_pot_invar›.›

lemma good_pot_val_c_plus:
  assumes pv: "pv_invar p" and rc: "rc_invar g" and cert: "(∃A D. A ⊆ {0..<m+Kart} ∧ D ⊆ {0..<m+Kart} ∧ card {e ∈ A ∪ D. fst_all ! e = vcount ∨ snd_all ! e = vcount} ≤ 1 ∧ pval_abstract bigM p + pval_abstract bigM g = (∑e∈A. cost_all ! e) - (∑e∈D. cost_all ! e))"
  shows "good_pot_val_c (pval_plus p g)"
proof -
  from cert obtain A D where AD: "A ⊆ {0..<m+Kart}" "D ⊆ {0..<m+Kart}" "card {e ∈ A ∪ D. fst_all ! e = vcount ∨ snd_all ! e = vcount} ≤ 1" "pval_abstract bigM p + pval_abstract bigM g = (∑e∈A. cost_all ! e) - (∑e∈D. cost_all ! e)" by blast
  have "pval_abstract bigM (pval_plus p g) = pval_abstract bigM p + pval_abstract bigM g" using pot_plus_faithful[OF pv rc] cert by blast
  hence "pval_abstract bigM (pval_plus p g) = (∑e∈A. cost_all ! e) - (∑e∈D. cost_all ! e)" using AD(4) by simp
  thus ?thesis using AD(1,2,3) by (auto simp: good_pot_val_c_def)
qed

lemma good_pot_val_c_minus:
  assumes pv: "pv_invar p" and rc: "rc_invar g" and cert: "(∃A D. A ⊆ {0..<m+Kart} ∧ D ⊆ {0..<m+Kart} ∧ card {e ∈ A ∪ D. fst_all ! e = vcount ∨ snd_all ! e = vcount} ≤ 1 ∧ pval_abstract bigM p - pval_abstract bigM g = (∑e∈A. cost_all ! e) - (∑e∈D. cost_all ! e))"
  shows "good_pot_val_c (pval_minus p g)"
proof -
  from cert obtain A D where AD: "A ⊆ {0..<m+Kart}" "D ⊆ {0..<m+Kart}" "card {e ∈ A ∪ D. fst_all ! e = vcount ∨ snd_all ! e = vcount} ≤ 1" "pval_abstract bigM p - pval_abstract bigM g = (∑e∈A. cost_all ! e) - (∑e∈D. cost_all ! e)" by blast
  have "pval_abstract bigM (pval_minus p g) = pval_abstract bigM p - pval_abstract bigM g" using pot_minus_faithful[OF pv rc] cert by blast
  hence "pval_abstract bigM (pval_minus p g) = (∑e∈A. cost_all ! e) - (∑e∈D. cost_all ! e)" using AD(4) by simp
  thus ?thesis using AD(1,2,3) by (auto simp: good_pot_val_c_def)
qed

definition pval_pot_invar :: "mtag × 'n ⇒ bool" where "pval_pot_invar p = (pv_invar p ∧ good_pot_val_c p)"

lemma pot_value_plus_spec_conc:
  assumes "pval_pot_invar p" and "rc_invar g" and cert: "(∃A D. A ⊆ {0..<m+Kart} ∧ D ⊆ {0..<m+Kart} ∧ card {e ∈ A ∪ D. fst_all ! e = vcount ∨ snd_all ! e = vcount} ≤ 1 ∧ pval_abstract bigM p + pval_abstract bigM g = (∑e∈A. cost_all ! e) - (∑e∈D. cost_all ! e))"
  shows "pval_abstract bigM (pval_plus p g) = pval_abstract bigM p + pval_abstract bigM g ∧ pval_pot_invar (pval_plus p g)"
  using pot_plus_faithful[OF _ assms(2) cert] good_pot_val_c_plus[OF _ assms(2) cert] assms(1) by (simp add: pval_pot_invar_def)

lemma pot_value_minus_spec_conc:
  assumes "pval_pot_invar p" and "rc_invar g" and cert: "(∃A D. A ⊆ {0..<m+Kart} ∧ D ⊆ {0..<m+Kart} ∧ card {e ∈ A ∪ D. fst_all ! e = vcount ∨ snd_all ! e = vcount} ≤ 1 ∧ pval_abstract bigM p - pval_abstract bigM g = (∑e∈A. cost_all ! e) - (∑e∈D. cost_all ! e))"
  shows "pval_abstract bigM (pval_minus p g) = pval_abstract bigM p - pval_abstract bigM g ∧ pval_pot_invar (pval_minus p g)"
  using pot_minus_faithful[OF _ assms(2) cert] good_pot_val_c_minus[OF _ assms(2) cert] assms(1) by (simp add: pval_pot_invar_def)

lemma maxpos: "0 < max_candidates" using min_candidates_pos min_le_max by simp

text ‹❙‹The @{term None} axiom ‹sel_select_None› for this selector.›
      A @{term None} return certifies that every non-tree arc is priced with the optimal sign.  The
      final identification of @{term ‹pval_abstract bigM (red_cost π e)›} with the true reduced cost
      @{term ‹𝖼 e + π(fst e) - π(snd e)›}, and the hypothesis @{term ‹rc_invar (red_cost π e)›}, both
      follow from the good-potential invariant (@{text good_pot_val}) via
      @{thm[source] pot_plus_faithful} / @{thm[source] pot_minus_faithful} at the @{text network_simplex_init}
      interpretation, where @{term pot_value_invar} is instantiated to it.›

lemma sel_select_impl_None:
  assumes inv: "sel_invar_impl sel" and rcinv: "⋀e. e < marc ⟹ rc_invar (red_cost pt e)" and none: "sel_select_impl sel pt es = None"
  shows "(∀e<marc. fst_all ! e ≠ snd_all ! e ⟶ nth es e = InL ⟶ 0 ≤ pval_abstract bigM (red_cost pt e)) ∧ (∀e<marc. fst_all ! e ≠ snd_all ! e ⟶ nth es e = InU ⟶ pval_abstract bigM (red_cost pt e) ≤ 0)"
proof -
  have larr: "length (sel_arr sel) = max_candidates" and lenmax: "sel_len sel ≤ max_candidates" and curlt: "0 < marc ⟶ sel_cur sel < marc" and rng: "set (take (sel_len sel) (sel_arr sel)) ⊆ {0..<marc}" using inv by (auto simp: sel_invar_impl_def)
  obtain a1 len1 b1 where sc: "scan_cache es pt 0 (sel_arr sel) (sel_len sel) no_best = (a1,len1,b1)" by (metis prod_cases3)
  have sc_spec: "length a1 = length (sel_arr sel) ∧ len1 ≤ sel_len sel ∧ set (take len1 a1) ⊆ set (take (sel_len sel) (sel_arr sel)) ∧ bok es pt b1 a1 len1 ∧ (fst no_best ⟶ fst b1) ∧ (¬ fst b1 ⟶ len1 = 0)" using scan_cache_spec[of 0 "sel_len sel" "sel_arr sel" es pt no_best, unfolded sc] lenmax larr by (simp add: no_best_def bok_def)
  obtain f1 eb ub gb where b1e: "b1 = (f1,eb,ub,gb)" by (cases b1)
  obtain cur2 a2 len2 b2 where scn: "scan es pt marc marc block_size (sel_cur sel) a1 len1 no_best = (cur2,a2,len2,b2)"
    by (cases "scan es pt marc marc block_size (sel_cur sel) a1 len1 no_best" rule: prod_cases4)
  have nf1: "¬ f1" using none sc b1e scn by (auto simp: sel_select_impl_def split: if_splits)
  have nf2: "¬ fst b2"
  proof (rule notI)
    assume h: "fst b2"
    obtain e2 u2 g2 where b2e: "b2 = (True, e2, u2, g2)" using h by (cases b2) auto
    have "sel_select_impl sel pt es ≠ None"
      using sc b1e scn nf1 b2e by (simp add: sel_select_impl_def Let_def)
    thus False using none by simp
  qed
  have len1z: "len1 = 0" using sc_spec nf1 unfolding b1e by force
  have allne: "∀e<marc. ¬ eligible es pt e"
  proof (cases "marc = 0")
    case True thus ?thesis by simp
  next
    case False
    hence mpos: "0 < marc" by simp
    have curm: "sel_cur sel < marc" using curlt mpos by simp
    have sweep: "∀t<marc. ¬ eligible es pt ((sel_cur sel + t) mod marc)" using scan_none[of es pt marc marc block_size "sel_cur sel" a1 len1 no_best cur2 a2 len2 b2] scn nf2 len1z min_candidates_pos maxpos curm mpos by simp
    show ?thesis
    proof (intro allI impI)
      fix e assume "e < marc"
      then obtain t where "t < marc" "(sel_cur sel + t) mod marc = e" using cyc_cover[OF mpos curm] by blast
      thus "¬ eligible es pt e" using sweep by auto
    qed
  qed
  show ?thesis
  proof (intro conjI allI impI)
    fix e assume e: "e < marc" and neq: "fst_all ! e ≠ snd_all ! e" and tg: "nth es e = InL"
    have ne: "¬ eligible es pt e" using allne e by blast
    show "0 ≤ pval_abstract bigM (red_cost pt e)" using ne neq elig_L[OF rcinv[OF e] tg] by simp
  next
    fix e assume e: "e < marc" and neq: "fst_all ! e ≠ snd_all ! e" and tg: "nth es e = InU"
    have ne: "¬ eligible es pt e" using allne e by blast
    show "pval_abstract bigM (red_cost pt e) ≤ 0" using ne neq elig_U[OF rcinv[OF e] tg] by simp
  qed
qed

text ‹❙‹The @{term Some} axiom ‹sel_select_Some› for this selector.›
      A returned edge is a genuine arc @{term ‹e < marc›}, eligible on its side, with descriptor
      @{term ‹g = red_cost π e›}; the selector invariant is preserved.  As for @{term None}, the
      identification of @{term ‹pval_abstract bigM (red_cost π e)›} with the true reduced cost and the
      @{term rc_invar} hypothesis are discharged from @{text good_pot_val} at interpretation.›

lemma sel_select_impl_Some:
  assumes inv: "sel_invar_impl sel" and rcinv: "⋀e. e < marc ⟹ rc_invar (red_cost pt e)" and some: "sel_select_impl sel pt es = Some (e,in_U,g,s2)"
  shows "sel_invar_impl s2 ∧ rc_invar g ∧ g = red_cost pt e ∧ e < marc ∧ fst_all ! e ≠ snd_all ! e ∧ (if in_U then nth es e = InU ∧ 0 < pval_abstract bigM (red_cost pt e) else nth es e = InL ∧ pval_abstract bigM (red_cost pt e) < 0)"
proof -
  have larr: "length (sel_arr sel) = max_candidates" and lenmax: "sel_len sel ≤ max_candidates" and curlt: "0 < marc ⟶ sel_cur sel < marc" and rng: "set (take (sel_len sel) (sel_arr sel)) ⊆ {0..<marc}" using inv by (auto simp: sel_invar_impl_def)
  obtain a1 len1 b1 where sc: "scan_cache es pt 0 (sel_arr sel) (sel_len sel) no_best = (a1,len1,b1)" by (metis prod_cases3)
  have sc_spec: "length a1 = length (sel_arr sel) ∧ len1 ≤ sel_len sel ∧ set (take len1 a1) ⊆ set (take (sel_len sel) (sel_arr sel)) ∧ bok es pt b1 a1 len1 ∧ (fst no_best ⟶ fst b1) ∧ (¬ fst b1 ⟶ len1 = 0)" using scan_cache_spec[of 0 "sel_len sel" "sel_arr sel" es pt no_best, unfolded sc] lenmax larr by (simp add: no_best_def bok_def)
  obtain f1 eb ub gb where b1e: "b1 = (f1,eb,ub,gb)" by (cases b1)
  show ?thesis
  proof (cases f1)
    case True
    have selSome: "sel_select_impl sel pt es = Some (eb, ub, gb, sel⦇sel_arr := a1, sel_len := len1⦈)" using sc b1e True by (simp add: sel_select_impl_def)
    have eq: "e = eb" "in_U = ub" "g = gb" "s2 = sel⦇sel_arr := a1, sel_len := len1⦈" using some selSome by auto
    have bokd: "eligible es pt eb ∧ ub = ent_in_U es eb ∧ gb = red_cost pt eb ∧ eb ∈ set (take len1 a1)" using sc_spec b1e True by (simp add: bok_def)
    have em: "e < marc" using bokd sc_spec eq rng by auto
    have ge: "g = red_cost pt e" using bokd eq by simp
    have rc: "rc_invar (red_cost pt e)" using rcinv[OF em] by simp
    have siv: "sel_invar_impl s2" using eq larr lenmax sc_spec rng curlt by (auto simp: sel_invar_impl_def)
    have el: "eligible es pt e" using bokd eq by simp
    have iu: "in_U = ent_in_U es e" using bokd eq by simp
    have sgn: "fst_all ! e ≠ snd_all ! e ∧ (if in_U then nth es e = InU ∧ 0 < pval_abstract bigM (red_cost pt e) else nth es e = InL ∧ pval_abstract bigM (red_cost pt e) < 0)" using sign_helper[OF rc el iu] .
    show ?thesis using siv rc ge em sgn by simp
  next
    case False
    hence len1z: "len1 = 0" using sc_spec b1e by force
    obtain cur2 a2 len2 b2 where scn:
"scan es pt marc marc block_size (sel_cur sel) a1 len1 no_best
 = (cur2,a2,len2,b2)" by (cases "scan es pt marc marc block_size (sel_cur sel) a1 len1 no_best" rule: prod_cases4)
    have sel2: "sel_select_impl sel pt es = (case b2 of (found2,e2,u2,g2) ⇒ if found2 then Some (e2, u2, g2, ⦇sel_cur = cur2, sel_arr = a2, sel_len = len2⦈) else None)" using sc b1e False scn by (simp add: sel_select_impl_def)
    obtain f2 eb2 ub2 gb2 where b2e: "b2 = (f2,eb2,ub2,gb2)" by (cases b2)
    have f2t: "f2" using some sel2 b2e by (auto split: if_splits)
    have mpos: "0 < marc"
    proof (rule ccontr)
      assume "¬ 0 < marc"
      hence m0: "marc = 0" by simp
      have "scan es pt 0 0 block_size (sel_cur sel) a1 len1 no_best = (sel_cur sel, a1, len1, no_best)" by (subst scan.simps) simp
      hence "b2 = no_best" using scn m0 by simp
      thus False using f2t b2e by (simp add: no_best_def)
    qed
    have curm: "sel_cur sel < marc" using curlt mpos by simp
    have la1: "length a1 = max_candidates" using sc_spec larr by force
    have some_spec: "length a2 = max_candidates ∧ len2 ≤ max_candidates ∧ cur2 < marc ∧ set (take len2 a2) ⊆ {0..<marc} ∧ bok es pt b2 a2 len2" using scan_some_spec[of es pt marc marc block_size "sel_cur sel" a1 len1 no_best cur2 a2 len2 b2] scn mpos curm la1 len1z maxpos by simp
    have selSome: "sel_select_impl sel pt es = Some (eb2, ub2, gb2, ⦇sel_cur = cur2, sel_arr = a2, sel_len = len2⦈)" using sel2 f2t b2e by simp
    have eq: "e = eb2" "in_U = ub2" "g = gb2" "s2 = ⦇sel_cur = cur2, sel_arr = a2, sel_len = len2⦈" using some selSome by auto
    have bokd: "eligible es pt eb2 ∧ ub2 = ent_in_U es eb2 ∧ gb2 = red_cost pt eb2 ∧ eb2 ∈ set (take len2 a2)" using some_spec b2e f2t by (simp add: bok_def)
    have em: "e < marc" using bokd some_spec eq by auto
    have ge: "g = red_cost pt e" using bokd eq by simp
    have rc: "rc_invar (red_cost pt e)" using rcinv[OF em] by simp
    have siv: "sel_invar_impl s2" using eq some_spec mpos by (auto simp: sel_invar_impl_def)
    have el: "eligible es pt e" using bokd eq by simp
    have iu: "in_U = ent_in_U es e" using bokd eq by simp
    have sgn: "fst_all ! e ≠ snd_all ! e ∧ (if in_U then nth es e = InU ∧ 0 < pval_abstract bigM (red_cost pt e) else nth es e = InL ∧ pval_abstract bigM (red_cost pt e) < 0)" using sign_helper[OF rc el iu] .
    show ?thesis using siv rc ge em sgn by simp
  qed
qed

subsection ‹The ADT axioms, unconditionally, from the good-potential invariant›

text ‹Folding @{thm red_cost_faithful} into the two theorems above yields exactly the shape of
      ‹sel_select_Some› / ‹sel_select_None›: the
      abstract reduced cost @{term ‹rcabs π e›} (the concrete @{term reduced_cost}) with no leftover
      @{const rc_invar} hypothesis.  These are what the @{text network_simplex_init} interpretation feeds
      to the ADT, instantiating @{term pot_value_invar} with the good-potential predicate so that
      @{term pot_valid} entails @{const pot_ok}.›

definition rcabs :: "(mtag × 'n) list ⇒ nat ⇒ real" where "rcabs pt e = cost_all ! e + pval_abstract bigM (nth pt (fst_all ! e)) - pval_abstract bigM (nth pt (snd_all ! e))"

lemma sel_select_impl_None_final:
  assumes inv: "sel_invar_impl sel" and ok: "pot_ok pt" and none: "sel_select_impl sel pt es = None"
  shows "(∀e<marc. fst_all ! e ≠ snd_all ! e ⟶ nth es e = InL ⟶ 0 ≤ rcabs pt e) ∧ (∀e<marc. fst_all ! e ≠ snd_all ! e ⟶ nth es e = InU ⟶ rcabs pt e ≤ 0)"
proof -
  have rcinv: "⋀e. e < marc ⟹ rc_invar (red_cost pt e)" using red_cost_faithful[OF ok] by simp
  have base: "(∀e<marc. fst_all ! e ≠ snd_all ! e ⟶ nth es e = InL ⟶ 0 ≤ pval_abstract bigM (red_cost pt e)) ∧ (∀e<marc. fst_all ! e ≠ snd_all ! e ⟶ nth es e = InU ⟶ pval_abstract bigM (red_cost pt e) ≤ 0)" using sel_select_impl_None[OF inv rcinv none] .
  show ?thesis
  proof (intro conjI allI impI)
    fix e assume e: "e < marc" and neq: "fst_all ! e ≠ snd_all ! e" and t: "nth es e = InL"
    have "0 ≤ pval_abstract bigM (red_cost pt e)" using base e neq t by blast
    thus "0 ≤ rcabs pt e" using red_cost_faithful[OF ok e] by (simp add: rcabs_def)
  next
    fix e assume e: "e < marc" and neq: "fst_all ! e ≠ snd_all ! e" and t: "nth es e = InU"
    have "pval_abstract bigM (red_cost pt e) ≤ 0" using base e neq t by blast
    thus "rcabs pt e ≤ 0" using red_cost_faithful[OF ok e] by (simp add: rcabs_def)
  qed
qed

lemma sel_select_impl_Some_final:
  assumes inv: "sel_invar_impl sel" and ok: "pot_ok pt" and some: "sel_select_impl sel pt es = Some (e,in_U,g,s2)"
  shows "sel_invar_impl s2 ∧ rc_invar g ∧ pval_abstract bigM g = rcabs pt e ∧ e < marc ∧ fst_all ! e ≠ snd_all ! e ∧ (if in_U then nth es e = InU ∧ 0 < rcabs pt e else nth es e = InL ∧ rcabs pt e < 0)"
proof -
  have rcinv: "⋀e. e < marc ⟹ rc_invar (red_cost pt e)" using red_cost_faithful[OF ok] by simp
  have base: "sel_invar_impl s2 ∧ rc_invar g ∧ g = red_cost pt e ∧ e < marc ∧ fst_all ! e ≠ snd_all ! e ∧ (if in_U then nth es e = InU ∧ 0 < pval_abstract bigM (red_cost pt e) else nth es e = InL ∧ pval_abstract bigM (red_cost pt e) < 0)" using sel_select_impl_Some[OF inv rcinv some] .
  have em: "e < marc" and geq: "g = red_cost pt e" using base by auto
  have rcf: "pval_abstract bigM (red_cost pt e) = rcabs pt e" using red_cost_faithful[OF ok em] by (simp add: rcabs_def)
  show ?thesis using base geq rcf by (simp split: if_splits)
qed


section ‹The @{locale network_simplex_spec} interpretation for the augmented network›

text ‹The augmented cost-flow network (@{const fst_all} / @{const snd_all} / @{const cap_all} /
      @{const cost_all} over @{term ‹{0..<m+Kart}›}), the threaded arborescence @{term Sarb} with root
      @{const vcount} and carrier @{term Varb} (= the graph vertex set, @{thm NSg_verts_Varb}), the
      list-backed potential/flow/parent/dir/edge-state arrays and the block-scan selector together form a
      concrete @{locale network_simplex_spec}. The graph and arborescence axioms come from @{term NSg} /
      the @{const arb_invar} facts (rewriting the graph vertex set to @{term Varb} through
      @{thm NSg_verts_Varb}); the abstract-array laws from @{thm list_abstract_array}; the pricing axioms
      @{text sel_select_Some} / @{text sel_select_None} from @{thm sel_select_impl_Some_final} /
      @{thm sel_select_impl_None_final} (with @{term pot_value_invar} instantiated to the good-potential
      predicate so the selection precondition entails @{const pot_ok}); and the descriptor arithmetic
      @{text pot_value_plus_spec} / @{text pot_value_minus_spec} from @{thm pot_plus_faithful} /
      @{thm pot_minus_faithful} with @{thm good_pot_val_c_plus} / @{thm good_pot_val_c_minus}.›

interpretation NS: network_simplex
  where fst = "λ e. if e < m+Kart then fst_all ! e else Product_Type.fst (prod_decode (e - (m+Kart)))"
    and snd = "λ e. if e < m+Kart then snd_all ! e else Product_Type.snd (prod_decode (e - (m+Kart)))"
    and create_edge = "λ u v. (m+Kart) + prod_encode (u, v)"
    and ℰ = "{0..<m+Kart}"
    and 𝗎 = "λ e. if e < m+Kart then (if cap_all ! e = - 1 then ∞ else ereal (h (cap_all ! e))) else ∞"
    and 𝖼 = "λ e. cost_all ! e"
    and r = vcount
    and shift_pot = shift_pot_impl
    and arborescense_invar = "arb_invar vcount Varb"
    and abstract_arborescense = abstract_arb
    and get_path_pair = get_path_pair_impl
    and swap_edge = swap_edge_impl
    and flow_invar = "λxs. ∀k∈{0..<m+Kart}. k < length xs" and flow_upd = list_update and flow_lookup = nth
    and pot_invar = "λxs. ∀v∈Varb. v < length xs" and pot_upd = list_update and pot_lookup = nth
    and parent_invar = "λxs. ∀v∈Varb - {vcount}. v < length xs" and parent_upd = list_update and parent_lookup = nth
    and dir_invar = "λxs. ∀v∈Varb - {vcount}. v < length xs" and dir_upd = list_update and dir_lookup = nth
    and es_invar = "λxs. ∀k∈{0..<m+Kart}. k < length xs" and es_upd = list_update and es_lookup = nth
    and sel_invar = sel_invar_impl and sel_select = sel_select_impl
    and b = "λ v. h (b_lookup v)"
    and cap = "λ e. cap_all ! e"
    and pot_value_invar = "λ p. good_pot_val_c p ∧ pv_invar p"
    and pot_value_abstract = "pval_abstract bigM"
    and pot_value_plus = pval_plus
    and pot_value_minus = pval_minus
    and rcost_invar = rc_invar
    and rcost_abstract = "pval_abstract bigM"
    and fst_exec = "λ e. fst_all ! e"
    and snd_exec = "λ e. snd_all ! e"
  apply unfold_locales
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal using num_edges_gtr_0 by simp
  subgoal using cap_all_nonneg by (auto simp: zero_ereal_def)
  subgoal using r_in_V NSg_verts_Varb by simp
  subgoal by (rule graph_invar_abstract_arb)
  subgoal premises p using p NSg_verts_Varb by (metis general_axiom3)
  subgoal premises p using p NSg_verts_Varb by (metis Vs_abstract_arb)
  subgoal premises p by (rule get_path_pair_axiom1[OF p(1) p(2) p(3) p(4)[simplified NSg_verts_Varb] p(5)[simplified NSg_verts_Varb]])
  subgoal premises p by (rule get_path_pair_axiom2[OF p(1) p(2) p(3) p(4)[simplified NSg_verts_Varb] p(5)[simplified NSg_verts_Varb]])
  subgoal premises p by (rule swap_edge_axiom1[OF p(1) p(2) p(3) p(4) p(5) p(6) p(7)[simplified NSg_verts_Varb] p(8)[simplified NSg_verts_Varb]])
  subgoal premises p by (rule swap_edge_axiom2[OF p(1) p(2) p(3) p(4) p(5) p(6) p(7)[simplified NSg_verts_Varb] p(8)[simplified NSg_verts_Varb]])
  subgoal by (auto simp: NSg_verts_Varb nth_fun_list_update) ― ‹flow upd›
  subgoal by (auto simp: NSg_verts_Varb nth_fun_list_update) ― ‹flow upd_invar›
  subgoal by (auto simp: NSg_verts_Varb nth_fun_list_update) ― ‹pot upd›
  subgoal by (auto simp: NSg_verts_Varb nth_fun_list_update) ― ‹pot upd_invar›
  subgoal by (auto simp: NSg_verts_Varb nth_fun_list_update) ― ‹parent upd›
  subgoal by (auto simp: NSg_verts_Varb nth_fun_list_update) ― ‹parent upd_invar›
  subgoal by (auto simp: NSg_verts_Varb nth_fun_list_update) ― ‹dir upd›
  subgoal by (auto simp: NSg_verts_Varb nth_fun_list_update) ― ‹dir upd_invar›
  subgoal by (auto simp: NSg_verts_Varb nth_fun_list_update) ― ‹es upd›
  subgoal by (auto simp: NSg_verts_Varb nth_fun_list_update) ― ‹es upd_invar›
  subgoal by auto ― ‹fst_exec›
  subgoal by auto ― ‹snd_exec›
  subgoal by auto ― ‹cap sentinel: (cap = -1) ⟷ (𝗎 = ∞)›
  subgoal by auto ― ‹cap value on the non-sentinel branch›
  subgoal using cap_all_nonneg by auto ― ‹cap validity: 0 ≤ cap ∨ cap = -1›
  subgoal premises p for sel π es e in_U γ sel'
  proof -
    have ok: "pot_ok π" using p(3)[simplified NSg_verts_Varb] p(4) by (simp add: pot_ok_def)
    show ?thesis using sel_select_impl_Some_final[OF p(1) ok p(6)] by (auto simp: rcabs_def marc_def)
  qed
  subgoal premises p for sel π es
  proof -
    have ok: "pot_ok π" using p(3)[simplified NSg_verts_Varb] p(4) by (simp add: pot_ok_def)
    show ?thesis using sel_select_impl_None_final[OF p(1) ok p(6)] by (auto simp: rcabs_def marc_def)
  qed
  subgoal premises p for p g
  proof -
    have pv: "pv_invar p" and gc: "good_pot_val_c p" using p(1) by auto
    have rc: "rc_invar g" using p(2) .
    have cert: "∃A D. A ⊆ {0..<m+Kart} ∧ D ⊆ {0..<m+Kart} ∧ card {e ∈ A ∪ D. fst_all ! e = vcount ∨ snd_all ! e = vcount} ≤ 1 ∧ pval_abstract bigM p + pval_abstract bigM g = sum ((!) cost_all) A - sum ((!) cost_all) D"
    proof -
      from p(3) obtain A D where AD: "A ⊆ {0..<m+Kart}" "D ⊆ {0..<m+Kart}"
        "card {e ∈ A ∪ D. (if e < m+Kart then fst_all ! e else fst (prod_decode (e - (m+Kart)))) = vcount ∨ (if e < m+Kart then snd_all ! e else snd (prod_decode (e - (m+Kart)))) = vcount} ≤ 1"
        "pval_abstract bigM p + pval_abstract bigM g = sum ((!) cost_all) A - sum ((!) cost_all) D" by (elim exE conjE)
      have SE: "{e ∈ A ∪ D. (if e < m+Kart then fst_all ! e else fst (prod_decode (e - (m+Kart)))) = vcount ∨ (if e < m+Kart then snd_all ! e else snd (prod_decode (e - (m+Kart)))) = vcount} = {e ∈ A ∪ D. fst_all ! e = vcount ∨ snd_all ! e = vcount}"
        using AD(1,2) by auto
      have "card {e ∈ A ∪ D. fst_all ! e = vcount ∨ snd_all ! e = vcount} ≤ 1" using AD(3) SE by simp
      thus ?thesis using AD(1,2,4) by (intro exI[of _ A] exI[of _ D]) auto
    qed
    show ?thesis using pot_plus_faithful[OF pv rc cert] good_pot_val_c_plus[OF pv rc cert] by simp
  qed
  subgoal premises p for p g
  proof -
    have pv: "pv_invar p" and gc: "good_pot_val_c p" using p(1) by auto
    have rc: "rc_invar g" using p(2) .
    have cert: "∃A D. A ⊆ {0..<m+Kart} ∧ D ⊆ {0..<m+Kart} ∧ card {e ∈ A ∪ D. fst_all ! e = vcount ∨ snd_all ! e = vcount} ≤ 1 ∧ pval_abstract bigM p - pval_abstract bigM g = sum ((!) cost_all) A - sum ((!) cost_all) D"
    proof -
      from p(3) obtain A D where AD: "A ⊆ {0..<m+Kart}" "D ⊆ {0..<m+Kart}"
        "card {e ∈ A ∪ D. (if e < m+Kart then fst_all ! e else fst (prod_decode (e - (m+Kart)))) = vcount ∨ (if e < m+Kart then snd_all ! e else snd (prod_decode (e - (m+Kart)))) = vcount} ≤ 1"
        "pval_abstract bigM p - pval_abstract bigM g = sum ((!) cost_all) A - sum ((!) cost_all) D" by (elim exE conjE)
      have SE: "{e ∈ A ∪ D. (if e < m+Kart then fst_all ! e else fst (prod_decode (e - (m+Kart)))) = vcount ∨ (if e < m+Kart then snd_all ! e else snd (prod_decode (e - (m+Kart)))) = vcount} = {e ∈ A ∪ D. fst_all ! e = vcount ∨ snd_all ! e = vcount}"
        using AD(1,2) by auto
      have "card {e ∈ A ∪ D. fst_all ! e = vcount ∨ snd_all ! e = vcount} ≤ 1" using AD(3) SE by simp
      thus ?thesis using AD(1,2,4) by (intro exI[of _ A] exI[of _ D]) auto
    qed
    show ?thesis using pot_minus_faithful[OF pv rc cert] good_pot_val_c_minus[OF pv rc cert] by simp
  qed
  subgoal premises p by (rule shift_pot_impl_spec[OF p(1) p(2)[simplified NSg_verts_Varb]])
  done


subsection ‹Assembling the @{locale network_simplex_init} correctness obligations›

text ‹The concrete starting basis discharges five of the ten @{locale network_simplex_init}
      obligations directly from the proved @{const build_tree} corollaries: the two trivial ones
      (store invariant and @{thm arb_invar_Sarb}), the selector seed @{const init_sel}, the flow/edge
      partition fit (@{thm build_tree_tail_content} together with the real-edge status lemmas), and the
      potential fit (@{thm build_tree_rc_zero} together with @{thm build_tree_root_pot}). The remaining
      five — @{term ‹NS.pot_valid›}, the @{term ‹NS.isbflow›}, the spanning-tree partition, strong
      feasibility and the tree correspondence — need additional carried invariants and are left as
      ∗‹sorry› for now.›

lemma NS_V_Varb: "NS.𝒱 = Varb" using NSg_verts_Varb by simp

lemma NS_V_minus_root: "NS.𝒱 - {vcount} = Vseen"
  using NS_V_Varb by (auto simp: Varb_def Vseen_def)

lemma NS_V_minus_root_sub: "NS.𝒱 - {vcount} ⊆ set vs_list"
  using NS_V_minus_root Vseen_eq_V V_sub_vs_list by simp

lemma len_par_bt: "length (ds_par (build_tree acyc_flow)) = Suc vcount"
  using build_tree_inv by (simp add: dfs_inv_def dfs_sized_def)

lemma len_dir_bt: "length (ds_dir (build_tree acyc_flow)) = Suc vcount"
  using build_tree_inv by (simp add: dfs_inv_def dfs_sized_def)

lemma plook_par: "v ∈ set vs_list ⟹ nth (ds_par (build_tree acyc_flow)) v = ds_par (build_tree acyc_flow) ! v"
  by simp

lemma plook_dir: "v ∈ set vs_list ⟹ nth (ds_dir (build_tree acyc_flow)) v = ds_dir (build_tree acyc_flow) ! v"
  by simp

text ‹Every non-root tree vertex's parent edge index lies inside the augmented edge range: interior
      vertices point at a real free edge (below @{term m}), component roots at their artificial edge.›

lemma par_lt_marc:
  assumes w: "w < vcount" "ds_seen (build_tree acyc_flow) ! w"
  shows "ds_par (build_tree acyc_flow) ! w < m + Kart"
proof (cases "ds_prnt (build_tree acyc_flow) ! w < vcount")
  case True
  have "ds_par (build_tree acyc_flow) ! w < m" using build_tree_par_edge[OF w True] by simp
  thus ?thesis by simp
next
  case False
  have tsi: "tree_seen_inv (build_tree acyc_flow)" using build_tree_inv by (simp add: dfs_inv_def)
  have "ds_prnt (build_tree acyc_flow) ! w = vcount" using tsi w False unfolding tree_seen_inv_def by blast
  hence cr: "comproot_edge_ok (build_tree acyc_flow) w" using build_tree_comproot_inv w by (simp add: comproot_inv_def)
  have "ds_par (build_tree acyc_flow) ! w - m < Kart" using cr by (simp add: comproot_edge_ok_def Kart_def)
  moreover have "m ≤ ds_par (build_tree acyc_flow) ! w" using cr by (simp add: comproot_edge_ok_def)
  ultimately show ?thesis by simp
qed

lemma pval_abstract_zero: "pval_abstract bigM pval_zero = 0"
  by (simp add: pval_abstract_def pval_zero_def)

text ‹Obligation 8 (‹potential_fits_spanning_tree_partition›): the root potential is zero
      (@{thm build_tree_root_pot}) and every tree edge has zero reduced cost (@{thm build_tree_rc_zero}).›

lemma NSinit_pot_fits:
  "NS.potential_fits_spanning_tree_partition vcount
     (nth (ds_par (build_tree acyc_flow)) ` (NS.𝒱 - {vcount}))
     (NS.abstract_pot (ds_pot (build_tree acyc_flow)))"
proof (unfold NS.potential_fits_spanning_tree_partition_def, intro conjI ballI)
  show "NS.abstract_pot (ds_pot (build_tree acyc_flow)) vcount = 0"
    using build_tree_root_pot plook_pot[of vcount] pval_abstract_zero by simp
next
  fix e assume "e ∈ nth (ds_par (build_tree acyc_flow)) ` (NS.𝒱 - {vcount})"
  then obtain v where v: "v ∈ Vseen" and e: "e = ds_par (build_tree acyc_flow) ! v"
    using NS_V_minus_root by auto
  have vlt: "v < vcount" and vseen: "ds_seen (build_tree acyc_flow) ! v" using v by (auto simp: Vseen_def)
  show "cost_all ! e
          + NS.abstract_pot (ds_pot (build_tree acyc_flow)) (if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart))))
          - NS.abstract_pot (ds_pot (build_tree acyc_flow)) (if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart)))) = 0"
    by (simp only: e if_P[OF par_lt_marc[OF vlt vseen]] build_tree_rc_zero[OF vlt vseen])
qed

text ‹Obligation 3 (selector invariant): the empty seed trivially satisfies @{const sel_invar_impl}.›

lemma NSinit_sel_invar: "sel_invar_impl init_sel"
  using num_edges_gtr_0 by (simp add: sel_invar_impl_def init_sel_def marc_def)

text ‹Obligation 7 (‹flow_fits_spanning_tree_partition›): an @{const InL} edge carries no flow
      and an @{const InU} edge is saturated at a finite capacity — real edges by their status
      characterisation, artificial edges by @{thm build_tree_tail_content}.›

lemma slook: "e < m + Kart ⟹ nth state_all e = state_all ! e"
  by simp

lemma flook: "e < m + Kart ⟹ nth flow_all e = flow_all ! e"
  by simp

lemma art_state_not_InL: "k < Kart ⟹ ds_aest (build_tree acyc_flow) ! k ≠ InL"
  using tail_edge_ok_build_tree[of k] by (auto simp: tail_edge_ok_def)

lemma art_InU_flow_cap:
  assumes k: "k < Kart" and u: "ds_aest (build_tree acyc_flow) ! k = InU"
  shows "ds_aflw (build_tree acyc_flow) ! k = ds_acap (build_tree acyc_flow) ! k ∧ 0 ≤ ds_acap (build_tree acyc_flow) ! k"
  using tail_edge_ok_build_tree[OF k] u by (auto simp: tail_edge_ok_def art_flow_def)

lemma NSinit_flow_fits:
  "NS.flow_fits_spanning_tree_partition
     (nth (ds_par (build_tree acyc_flow)) ` (NS.𝒱 - {vcount}))
     {e ∈ {0..<m + Kart}. nth state_all e = InL}
     {e ∈ {0..<m + Kart}. nth state_all e = InU}
     (λe. h (nth flow_all e))"
proof (unfold NS.flow_fits_spanning_tree_partition_def, intro conjI ballI)
  fix e assume "e ∈ {e ∈ {0..<m + Kart}. nth state_all e = InL}"
  hence e: "e < m + Kart" and sl: "nth state_all e = InL" by auto
  from sl slook[OF e] have st: "state_all ! e = InL" by simp
  show "h (nth flow_all e) = 0"
  proof (cases "e < m")
    case True
    have "(edge_state acyc_flow) ! e = InL" using st state_all_real[OF True] by simp
    hence "acyc_flow ! e = 0" using edge_state_InL_iff[OF True] by simp
    thus ?thesis using flook[OF e] flow_all_real[OF True] by simp
  next
    case False
    then obtain k where ek: "e = m + k" by (metis add.commute le_Suc_ex not_less)
    have kK: "k < Kart" using e ek by simp
    have "state_all ! e = ds_aest (build_tree acyc_flow) ! k" using ek kK state_all_art by simp
    thus ?thesis using st art_state_not_InL[OF kK] by simp
  qed
next
  fix e assume "e ∈ {e ∈ {0..<m + Kart}. nth state_all e = InU}"
  hence e: "e < m + Kart" and sl: "nth state_all e = InU" by auto
  from sl slook[OF e] have st: "state_all ! e = InU" by simp
  show "ereal (h (nth flow_all e))
        = (if e < m + Kart then if cap_all ! e = - 1 then ∞ else ereal (h (cap_all ! e)) else ∞)"
  proof (cases "e < m")
    case True
    have es: "(edge_state acyc_flow) ! e = InU" using st state_all_real[OF True] by simp
    have "acyc_flow ! e ≠ 0 ∧ capacity_list ! e ≠ - 1 ∧ acyc_flow ! e = capacity_list ! e"
      using edge_state_InU_iff[OF True] es by simp
    hence fc: "acyc_flow ! e = capacity_list ! e" and cne: "capacity_list ! e ≠ - 1" by auto
    have cc: "cap_all ! e = capacity_list ! e" using cap_all_real[OF True] .
    have "nth flow_all e = capacity_list ! e" using flook[OF e] flow_all_real[OF True] fc by simp
    thus ?thesis using cc cne e by simp
  next
    case False
    then obtain k where ek: "e = m + k" by (metis add.commute le_Suc_ex not_less)
    have kK: "k < Kart" using e ek by simp
    have su: "ds_aest (build_tree acyc_flow) ! k = InU" using st ek kK state_all_art by simp
    have fc: "ds_aflw (build_tree acyc_flow) ! k = ds_acap (build_tree acyc_flow) ! k" and cnn: "0 ≤ ds_acap (build_tree acyc_flow) ! k"
      using art_InU_flow_cap[OF kK su] by auto
    have fe: "nth flow_all e = ds_aflw (build_tree acyc_flow) ! k" using flook[OF e] ek kK flow_all_art by simp
    have ce: "cap_all ! e = ds_acap (build_tree acyc_flow) ! k" using ek kK cap_all_art by simp
    have "cap_all ! e ≠ - 1" using ce cnn by simp
    thus ?thesis using fe ce fc e by simp
  qed
qed


subsection ‹A combined DFS invariant: component-root direction and artificial-edge fields›

text ‹Obligation 9 (strong feasibility) needs, at every component root @{term c}, the tree-edge
      direction @{term ‹ds_dir (build_tree acyc_flow) ! c = art_dir c›} and the artificial edge's tag/flow/cap.
      These four facts are carried through the builder as a single invariant ‹cr_ext_inv›,
      proved together with @{const comproot_inv} in one shared @{const build_dfs}/@{const open_tree_component}/
      @{const emit_U_edge}/fold induction.  The direction is frozen by @{const build_dfs} at already-seen
      vertices (‹build_dfs_dir_frozen›); the artificial-edge fields sit below the tail cursor and are
      frozen by @{thm build_dfs_art} and update-at-a-fresh-index reasoning.›

lemma bd_upd1_dir:
  assumes inv: "dfs_inv fl s" and c: "bd_call1_conds fl s" and x: "x < vcount" and sx: "ds_seen s ! x"
  shows "ds_dir (bd_upd1 fl s) ! x = ds_dir s ! x"
proof -
  from c obtain v oc ic rest where stk: "ds_stk s = (v,oc,ic)#rest" and oclt: "oc < (free_out_hi fl) ! v"
    by (auto simp: bd_call1_conds_def split: list.splits prod.splits)
  have wf: "dfs_wf s" using inv by (auto simp: dfs_inv_def)
  from wf stk have vlt: "v < vcount" and olo: "out_lo ! v ≤ oc" by (auto simp: dfs_wf_def)
  let ?e = "(free_out_edges fl) ! oc" let ?w = "snd_list ! ?e"
  have wlt: "?w < vcount" using Hout_valid[OF vlt olo oclt] .
  show ?thesis
  proof (cases "ds_seen s ! ?w")
    case True
    have "bd_upd1 fl s = s⦇ds_stk := (v, Suc oc, ic) # rest⦈" using stk True by (simp add: bd_upd1_def Let_def)
    thus ?thesis by simp
  next
    case False
    have up: "bd_upd1 fl s = dfs_discover (s⦇ds_stk := (v, Suc oc, ic) # rest⦈) v ?w ?e"
      using stk False by (simp add: bd_upd1_def Let_def)
    have xnw: "x ≠ ?w" using sx False by auto
    thus ?thesis using up by (simp add: dfs_discover_def Let_def nth_list_update_neq)
  qed
qed

lemma bd_upd2_dir:
  assumes inv: "dfs_inv fl s" and c: "bd_call2_conds fl s" and x: "x < vcount" and sx: "ds_seen s ! x"
  shows "ds_dir (bd_upd2 fl s) ! x = ds_dir s ! x"
proof -
  from c obtain v oc ic rest where stk: "ds_stk s = (v,oc,ic)#rest"
      and noc: "¬ oc < (free_out_hi fl) ! v" and iclt: "ic < (free_in_hi fl) ! v"
    by (auto simp: bd_call2_conds_def split: list.splits prod.splits)
  have wf: "dfs_wf s" using inv by (auto simp: dfs_inv_def)
  from wf stk have vlt: "v < vcount" and ilo: "in_lo ! v ≤ ic" by (auto simp: dfs_wf_def)
  let ?e = "(free_in_edges fl) ! ic" let ?w = "fst_list ! ?e"
  have wlt: "?w < vcount" using Hin_valid[OF vlt ilo iclt] .
  show ?thesis
  proof (cases "ds_seen s ! ?w")
    case True
    have "bd_upd2 fl s = s⦇ds_stk := (v, oc, Suc ic) # rest⦈" using stk True by (simp add: bd_upd2_def Let_def)
    thus ?thesis by simp
  next
    case False
    have up: "bd_upd2 fl s = dfs_discover (s⦇ds_stk := (v, oc, Suc ic) # rest⦈) v ?w ?e"
      using stk False by (simp add: bd_upd2_def Let_def)
    have xnw: "x ≠ ?w" using sx False by auto
    thus ?thesis using up by (simp add: dfs_discover_def Let_def nth_list_update_neq)
  qed
qed

lemma bd_upd3_dir:
  assumes c: "bd_call3_conds fl s" shows "ds_dir (bd_upd3 s) ! x = ds_dir s ! x"
proof -
  from c obtain v oc ic rest where stk: "ds_stk s = (v,oc,ic)#rest"
    by (auto simp: bd_call3_conds_def split: list.splits prod.splits)
  have "bd_upd3 s = dfs_finish s v rest" using stk by (simp add: bd_upd3_def)
  thus ?thesis by (simp add: dfs_finish_def Let_def)
qed

lemma build_dfs_dir_frozen:
  assumes dom: "build_dfs_dom (fl, s)" and inv0: "dfs_inv fl s" and xlt: "x < vcount" and sx0: "ds_seen s ! x"
  shows "ds_dir (build_dfs fl s) ! x = ds_dir s ! x"
proof -
  have "dfs_inv fl s ⟶ ds_seen s ! x ⟶ ds_dir (build_dfs fl s) ! x = ds_dir s ! x"
  proof (induct rule: bd_induct[OF dom])
    case IH: (1 fl s)
    show ?case
    proof (intro impI)
      assume invs: "dfs_inv fl s" and sx: "ds_seen s ! x"
      show "ds_dir (build_dfs fl s) ! x = ds_dir s ! x"
      proof (rule bd_cases[where s=s and fl=fl])
        assume c: "bd_call1_conds fl s"
        have step: "build_dfs fl s = build_dfs fl (bd_upd1 fl s)" using bd_simps(1)[OF IH(1) c] .
        have inv1: "dfs_inv fl (bd_upd1 fl s)" using bd_upd1_inv[OF invs c] .
        have sx1: "ds_seen (bd_upd1 fl s) ! x" using bd_upd1_seen_mono[OF c sx] .
        show ?thesis using IH(2)[OF c] inv1 sx1 bd_upd1_dir[OF invs c xlt sx] step by simp
      next
        assume c: "bd_call2_conds fl s"
        have step: "build_dfs fl s = build_dfs fl (bd_upd2 fl s)" using bd_simps(2)[OF IH(1) c] .
        have inv1: "dfs_inv fl (bd_upd2 fl s)" using bd_upd2_inv[OF invs c] .
        have sx1: "ds_seen (bd_upd2 fl s) ! x" using bd_upd2_seen_mono[OF c sx] .
        show ?thesis using IH(3)[OF c] inv1 sx1 bd_upd2_dir[OF invs c xlt sx] step by simp
      next
        assume c: "bd_call3_conds fl s"
        have step: "build_dfs fl s = build_dfs fl (bd_upd3 s)" using bd_simps(3)[OF IH(1) c] .
        have inv1: "dfs_inv fl (bd_upd3 s)" using bd_upd3_inv[OF invs c] .
        have sx1: "ds_seen (bd_upd3 s) ! x" using bd_upd3_seen_mono[OF c sx] .
        show ?thesis using IH(4)[OF c] inv1 sx1 bd_upd3_dir[OF c] step by simp
      next
        assume c: "bd_ret_conds s"
        have "build_dfs fl s = s" using bd_simps(4)[OF IH(1) c] .
        thus ?thesis by simp
      qed
    qed
  qed
  thus ?thesis using inv0 sx0 by blast
qed

text ‹A fuller version of @{thm open_tree_component_seed} that also exposes the seed's direction flag
      and the freshly-written artificial edge's tag, flow and capacity.›

lemma otc_seed:
  assumes inv: "dfs_inv acyc_flow s" and c: "c < vcount" and unseen: "¬ ds_seen s ! c" and cnz: "c ≠ 0"
      and stke: "ds_stk s = []"
  obtains sd where
    "open_tree_component acyc_flow s c = build_dfs acyc_flow sd"
    "dfs_inv acyc_flow sd"
    "ds_nxt sd = Suc (ds_nxt s)"
    "ds_seen sd = (ds_seen s)[c := True]"
    "ds_prnt sd = (ds_prnt s)[c := vcount]"
    "ds_par sd = (ds_par s)[c := m + ds_nxt s]"
    "ds_dir sd = (ds_dir s)[c := art_dir c]"
    "ds_aest sd = (ds_aest s)[ds_nxt s := InTree]"
    "ds_aflw sd = (ds_aflw s)[ds_nxt s := art_flow c]"
    "ds_acap sd = (ds_acap s)[ds_nxt s := art_tree_cap c]"
proof -
  define sd where "sd = s⦇
      ds_afst := (ds_afst s)[ds_nxt s := (if 0 ≤ imbalance ! c then c else vcount)],
      ds_asnd := (ds_asnd s)[ds_nxt s := (if 0 ≤ imbalance ! c then vcount else c)],
      ds_acap := (ds_acap s)[ds_nxt s := (if 0 ≤ imbalance ! c then ¦imbalance ! c¦ + 1 else ¦imbalance ! c¦)],
      ds_aflw := (ds_aflw s)[ds_nxt s := ¦imbalance ! c¦],
      ds_aest := (ds_aest s)[ds_nxt s := InTree],
      ds_nxt  := Suc (ds_nxt s),
      ds_seen := (ds_seen s)[c := True],
      ds_prnt := (ds_prnt s)[c := vcount],
      ds_par  := (ds_par s)[c := m + ds_nxt s],
      ds_dir  := (ds_dir s)[c := (0 ≤ imbalance ! c)],
      ds_pot  := (ds_pot s)[c := (if 0 ≤ imbalance ! c then pval_negM else pval_M)],
      ds_thrd := (ds_thrd s)[ds_prev s := c],
      ds_rvth := (ds_rvth s)[c := ds_prev s],
      ds_snum := (ds_snum s)[c := 1],
      ds_prev := c,
      ds_stk  := [(c, out_lo ! c, in_lo ! c)] ⦈"
  have opd: "open_tree_component acyc_flow s c = build_dfs acyc_flow sd"
    by (simp add: open_tree_component_def Let_def sd_def)
  have invsd: "dfs_inv acyc_flow sd"
    unfolding sd_def dfs_inv_def
    apply (intro conjI)
    subgoal using inv c by (auto simp: dfs_inv_def dfs_wf_def dfs_sized_def tree_seen_inv_def nth_list_update)
    subgoal using inv c by (auto simp: dfs_inv_def dfs_wf_def dfs_sized_def tree_seen_inv_def nth_list_update)
    subgoal using inv c by (auto simp: dfs_inv_def dfs_wf_def dfs_sized_def tree_seen_inv_def nth_list_update)
    subgoal
      apply (rule thread_inv_upd[where s = s and w = c])
      using inv c unseen cnz by (auto simp: dfs_inv_def dfs_sized_def)
    subgoal using inv c by (auto simp: dfs_inv_def dfs_sized_def par_edge_inv_def nth_list_update)
    subgoal
      apply (rule pot_inv_seed[where s = s and c = c])
      using inv c unseen by (auto simp: dfs_inv_def dfs_sized_def nth_list_update)
    subgoal using inv c by (auto simp: dfs_inv_def dfs_sized_def root_pot_inv_def nth_list_update)
    subgoal using inv c by (auto simp: dfs_inv_def dfs_sized_def stk_prnt_inv_def nth_list_update)
    subgoal
      apply (rule emit_ord_inv_seed[where s = s and c = c])
      using inv c unseen by (auto simp: dfs_inv_def dfs_sized_def)
    subgoal
      apply (rule snum_inv_seed[where s = s and c = c])
      using inv c unseen stke by (auto simp: dfs_inv_def dfs_sized_def)
    subgoal
      apply (rule lsuc_inv_seed[where s = s and c = c])
      using inv c unseen stke by (auto simp: dfs_inv_def dfs_sized_def)
    done
  show ?thesis
    apply (rule that[of sd])
    subgoal by (rule opd)
    subgoal by (rule invsd)
    subgoal by (simp add: sd_def)
    subgoal by (simp add: sd_def)
    subgoal by (simp add: sd_def)
    subgoal by (simp add: sd_def)
    subgoal by (simp add: sd_def art_dir_def)
    subgoal by (simp add: sd_def)
    subgoal by (simp add: sd_def art_flow_def)
    subgoal by (simp add: sd_def art_tree_cap_def art_flow_def art_dir_def)
    done
qed

definition cr_ext_ok :: "'n dfs_state ⇒ nat ⇒ bool" where
  "cr_ext_ok s c ⟷ ds_dir s ! c = art_dir c
     ∧ ds_aest s ! (ds_par s ! c - m) = InTree
     ∧ ds_aflw s ! (ds_par s ! c - m) = art_flow c
     ∧ ds_acap s ! (ds_par s ! c - m) = art_tree_cap c"

definition cr_ext_inv :: "'n dfs_state ⇒ bool" where
  "cr_ext_inv s ⟷ (∀c<vcount. ds_seen s ! c ⟶ ds_prnt s ! c = vcount ⟶ cr_ext_ok s c)"

lemma emit_U_edge_crext:
  assumes ci: "comproot_inv s" and ce: "cr_ext_inv s"
  shows "cr_ext_inv (emit_U_edge s v)"
  unfolding cr_ext_inv_def
proof (intro allI impI)
  fix c assume clt: "c < vcount" and sc: "ds_seen (emit_U_edge s v) ! c" and pc: "ds_prnt (emit_U_edge s v) ! c = vcount"
  have seq: "ds_seen (emit_U_edge s v) = ds_seen s" "ds_prnt (emit_U_edge s v) = ds_prnt s"
            "ds_par (emit_U_edge s v) = ds_par s" "ds_dir (emit_U_edge s v) = ds_dir s"
    by (simp_all add: emit_U_edge_def Let_def)
  have sc': "ds_seen s ! c" and pc': "ds_prnt s ! c = vcount" using sc pc seq by simp_all
  have ok: "comproot_edge_ok s c" using ci clt sc' pc' by (simp add: comproot_inv_def)
  have bnd: "ds_par s ! c - m < ds_nxt s" using ok by (simp add: comproot_edge_ok_def)
  have ext: "cr_ext_ok s c" using ce clt sc' pc' by (simp add: cr_ext_inv_def)
  have aest': "ds_aest (emit_U_edge s v) ! (ds_par s ! c - m) = ds_aest s ! (ds_par s ! c - m)"
    using bnd by (simp add: emit_U_edge_def Let_def nth_list_update_neq)
  have aflw': "ds_aflw (emit_U_edge s v) ! (ds_par s ! c - m) = ds_aflw s ! (ds_par s ! c - m)"
    using bnd by (simp add: emit_U_edge_def Let_def nth_list_update_neq)
  have acap': "ds_acap (emit_U_edge s v) ! (ds_par s ! c - m) = ds_acap s ! (ds_par s ! c - m)"
    using bnd by (simp add: emit_U_edge_def Let_def nth_list_update_neq)
  show "cr_ext_ok (emit_U_edge s v) c"
    unfolding cr_ext_ok_def using seq ext aest' aflw' acap' by (simp add: cr_ext_ok_def)
qed

lemma open_tree_component_crext:
  assumes inv: "dfs_inv acyc_flow s" and c: "c < vcount" and unseen: "¬ ds_seen s ! c" and cnz: "c ≠ 0"
      and stke: "ds_stk s = []" and al: "art_len s" and inb: "ds_nxt s < length vs_list"
      and ci: "comproot_inv s" and ce: "cr_ext_inv s"
  shows "cr_ext_inv (open_tree_component acyc_flow s c)"
proof -
  obtain sd where opd: "open_tree_component acyc_flow s c = build_dfs acyc_flow sd" and invsd: "dfs_inv acyc_flow sd"
      and seensd: "ds_seen sd = (ds_seen s)[c := True]"
      and prntsd: "ds_prnt sd = (ds_prnt s)[c := vcount]"
      and parsd: "ds_par sd = (ds_par s)[c := m + ds_nxt s]"
      and dirsd: "ds_dir sd = (ds_dir s)[c := art_dir c]"
      and aestsd: "ds_aest sd = (ds_aest s)[ds_nxt s := InTree]"
      and aflwsd: "ds_aflw sd = (ds_aflw s)[ds_nxt s := art_flow c]"
      and acapsd: "ds_acap sd = (ds_acap s)[ds_nxt s := art_tree_cap c]"
    using otc_seed[OF inv c unseen cnz stke] .
  have dom: "build_dfs_dom (acyc_flow, sd)" using invsd by (simp add: dfs_inv_def build_dfs_dom_wf')
  from build_dfs_art[OF dom]
  have artAe: "ds_aest (build_dfs acyc_flow sd) = ds_aest sd" and artAf: "ds_aflw (build_dfs acyc_flow sd) = ds_aflw sd"
   and artAc: "ds_acap (build_dfs acyc_flow sd) = ds_acap sd" by simp_all
  have lens: "length (ds_par s) = Suc vcount" "length (ds_dir s) = Suc vcount"
    using inv by (simp_all add: dfs_inv_def dfs_sized_def)
  have laest: "length (ds_aest s) = length vs_list" and laflw: "length (ds_aflw s) = length vs_list"
   and lacap: "length (ds_acap s) = length vs_list" using al by (simp_all add: art_len_def)
  show ?thesis
    unfolding cr_ext_inv_def
  proof (intro allI impI)
    fix w assume wlt: "w < vcount" and sw: "ds_seen (open_tree_component acyc_flow s c) ! w"
        and pw: "ds_prnt (open_tree_component acyc_flow s c) ! w = vcount"
    have bw: "ds_seen (build_dfs acyc_flow sd) ! w" using sw opd by simp
    have bpw: "ds_prnt (build_dfs acyc_flow sd) ! w = vcount" using pw opd by simp
    have cr: "ds_seen sd ! w ∧ ds_prnt sd ! w = vcount
              ∧ ds_par (build_dfs acyc_flow sd) ! w = ds_par sd ! w ∧ ds_pot (build_dfs acyc_flow sd) ! w = ds_pot sd ! w"
      using build_dfs_cr[OF dom invsd wlt bw bpw] .
    have swsd: "ds_seen sd ! w" using cr by simp
    have parw: "ds_par (open_tree_component acyc_flow s c) ! w = ds_par sd ! w" using cr opd by simp
    have dirw: "ds_dir (open_tree_component acyc_flow s c) ! w = ds_dir sd ! w"
      using build_dfs_dir_frozen[OF dom invsd wlt swsd] opd by simp
    show "cr_ext_ok (open_tree_component acyc_flow s c) w"
    proof (cases "w = c")
      case True
      have parval: "ds_par (open_tree_component acyc_flow s c) ! w = m + ds_nxt s"
        using parw parsd True c lens by (simp add: nth_list_update_eq)
      have idx: "ds_par (open_tree_component acyc_flow s c) ! w - m = ds_nxt s" using parval by simp
      have dirval: "ds_dir (open_tree_component acyc_flow s c) ! w = art_dir c"
        using dirw dirsd True c lens by (simp add: nth_list_update_eq)
      have aestval: "ds_aest (open_tree_component acyc_flow s c) ! (ds_par (open_tree_component acyc_flow s c) ! w - m) = InTree"
        using opd artAe aestsd idx inb laest by (simp add: nth_list_update_eq)
      have aflwval: "ds_aflw (open_tree_component acyc_flow s c) ! (ds_par (open_tree_component acyc_flow s c) ! w - m) = art_flow c"
        using opd artAf aflwsd idx inb laflw by (simp add: nth_list_update_eq)
      have acapval: "ds_acap (open_tree_component acyc_flow s c) ! (ds_par (open_tree_component acyc_flow s c) ! w - m) = art_tree_cap c"
        using opd artAc acapsd idx inb lacap by (simp add: nth_list_update_eq)
      show ?thesis unfolding cr_ext_ok_def using dirval aestval aflwval acapval True by simp
    next
      case False
      have swseed: "ds_seen s ! w" using swsd seensd False by (simp add: nth_list_update_neq)
      have pwseed: "ds_prnt s ! w = vcount" using cr prntsd False by (simp add: nth_list_update_neq)
      have okw: "comproot_edge_ok s w" using ci wlt swseed pwseed by (simp add: comproot_inv_def)
      have bndw: "ds_par s ! w - m < ds_nxt s" using okw by (simp add: comproot_edge_ok_def)
      have extw: "cr_ext_ok s w" using ce wlt swseed pwseed by (simp add: cr_ext_inv_def)
      have parw2: "ds_par (open_tree_component acyc_flow s c) ! w = ds_par s ! w"
        using parw parsd False by (simp add: nth_list_update_neq)
      have dirw2: "ds_dir (open_tree_component acyc_flow s c) ! w = ds_dir s ! w"
        using dirw dirsd False by (simp add: nth_list_update_neq)
      have idxne: "ds_par s ! w - m ≠ ds_nxt s" using bndw by simp
      have aest': "ds_aest (open_tree_component acyc_flow s c) ! (ds_par s ! w - m) = ds_aest s ! (ds_par s ! w - m)"
        using opd artAe aestsd idxne by (simp add: nth_list_update_neq)
      have aflw': "ds_aflw (open_tree_component acyc_flow s c) ! (ds_par s ! w - m) = ds_aflw s ! (ds_par s ! w - m)"
        using opd artAf aflwsd idxne by (simp add: nth_list_update_neq)
      have acap': "ds_acap (open_tree_component acyc_flow s c) ! (ds_par s ! w - m) = ds_acap s ! (ds_par s ! w - m)"
        using opd artAc acapsd idxne by (simp add: nth_list_update_neq)
      show ?thesis unfolding cr_ext_ok_def using extw parw2 dirw2 aest' aflw' acap' by (simp add: cr_ext_ok_def)
    qed
  qed
qed

lemma phase1_step_crext:
  assumes v: "v ∈ set vs_list" and inv: "dfs_inv acyc_flow s" and stke: "ds_stk s = []" and al: "art_len s"
      and ci: "comproot_inv s" and ce: "cr_ext_inv s" and inb: "ds_nxt (phase1_step acyc_flow v s) ≤ length vs_list"
  shows "cr_ext_inv (phase1_step acyc_flow v s)"
proof (cases "imbalance ! v = 0")
  case True thus ?thesis using ce by (simp add: phase1_step_def)
next
  case nz: False
  have vlt: "v < vcount" using v vs_less_vcount by simp
  show ?thesis
  proof (cases "ds_seen s ! v")
    case seen: True
    have eq: "phase1_step acyc_flow v s = emit_U_edge s v" using nz seen by (simp add: phase1_step_def)
    thus ?thesis using emit_U_edge_crext[OF ci ce] by simp
  next
    case notseen: False
    have vnz: "v ≠ 0" using v no_zero_node by metis
    have eq: "phase1_step acyc_flow v s = open_tree_component acyc_flow s v" using nz notseen by (simp add: phase1_step_def)
    have nxt: "ds_nxt (open_tree_component acyc_flow s v) = Suc (ds_nxt s)" using open_tree_component_nxt[OF inv vlt] .
    have inbs: "ds_nxt s < length vs_list" using inb eq nxt by simp
    show ?thesis using eq open_tree_component_crext[OF inv vlt notseen vnz stke al inbs ci ce] by simp
  qed
qed

lemma phase2_step_crext:
  assumes v: "v ∈ set vs_list" and inv: "dfs_inv acyc_flow s" and stke: "ds_stk s = []" and al: "art_len s"
      and ci: "comproot_inv s" and ce: "cr_ext_inv s" and inb: "ds_nxt (phase2_step acyc_flow v s) ≤ length vs_list"
  shows "cr_ext_inv (phase2_step acyc_flow v s)"
proof (cases "ds_seen s ! v ∨ is_lonely v")
  case True thus ?thesis using ce by (simp add: phase2_step_def)
next
  case False
  hence notseen: "¬ ds_seen s ! v" and nl: "¬ is_lonely v" by auto
  have vlt: "v < vcount" using v vs_less_vcount by simp
  have vnz: "v ≠ 0" using v no_zero_node by metis
  have eq: "phase2_step acyc_flow v s = open_tree_component acyc_flow s v" using notseen nl by (simp add: phase2_step_def)
  have nxt: "ds_nxt (open_tree_component acyc_flow s v) = Suc (ds_nxt s)" using open_tree_component_nxt[OF inv vlt] .
  have inbs: "ds_nxt s < length vs_list" using inb eq nxt by simp
  show ?thesis using eq open_tree_component_crext[OF inv vlt notseen vnz stke al inbs ci ce] by simp
qed

lemma fold_emit_crc1:
  assumes "distinct xs" "set xs ⊆ set vs_list" "dfs_inv acyc_flow s" "ds_stk s = []"
      "art_len s" "comproot_inv s" "cr_ext_inv s"
      "finite E" "E ⊆ {v ∈ set vs_list. ds_seen s ! v}" "E ∩ set xs = {}" "ds_nxt s = card E"
  shows "art_len (fold (phase1_step acyc_flow) xs s) ∧ comproot_inv (fold (phase1_step acyc_flow) xs s)
         ∧ cr_ext_inv (fold (phase1_step acyc_flow) xs s)
         ∧ (∃E'. finite E' ∧ E' ⊆ {v ∈ set vs_list. ds_seen (fold (phase1_step acyc_flow) xs s) ! v}
                 ∧ ds_nxt (fold (phase1_step acyc_flow) xs s) = card E')"
  using assms
proof (induct xs arbitrary: s E)
  case Nil thus ?case by auto
next
  case (Cons x rest)
  have xvs: "x ∈ set vs_list" using Cons.prems(2) by simp
  have xlt: "x < vcount" using xvs vs_less_vcount by simp
  have inv1: "dfs_inv acyc_flow (phase1_step acyc_flow x s)" "ds_stk (phase1_step acyc_flow x s) = []"
    using phase1_step_inv[OF xvs conjI[OF Cons.prems(3) Cons.prems(4)]] by auto
  have al1: "art_len (phase1_step acyc_flow x s)" using phase1_step_art_len[OF xvs Cons.prems(3) Cons.prems(5)] .
  have Emono: "E ⊆ {v ∈ set vs_list. ds_seen (phase1_step acyc_flow x s) ! v}"
    using Cons.prems(9) phase1_step_seen_mono[OF Cons.prems(3) xlt] by auto
  have Edisj: "E ∩ set rest = {}" using Cons.prems(10) by auto
  have distr: "distinct rest" using Cons.prems(1) by simp
  have subr: "set rest ⊆ set vs_list" using Cons.prems(2) by simp
  have Esub: "E ⊆ set vs_list" using Cons.prems(9) by auto
  have xnotE: "x ∉ E" using Cons.prems(10) by auto
  have step_inb: "ds_nxt (phase1_step acyc_flow x s) ≤ length vs_list"
    using phase1_step_nxt[OF Cons.prems(3) xlt]
  proof
    assume "ds_nxt (phase1_step acyc_flow x s) = ds_nxt s"
    thus ?thesis using Cons.prems(11) card_sub_vs_le[OF Esub] by simp
  next
    assume A: "ds_nxt (phase1_step acyc_flow x s) = Suc (ds_nxt s) ∧ ds_seen (phase1_step acyc_flow x s) ! x"
    have "insert x E ⊆ set vs_list" using Esub xvs by auto
    hence "card (insert x E) ≤ length vs_list" by (rule card_sub_vs_le)
    thus ?thesis using A Cons.prems(11) xnotE Cons.prems(8) by (simp add: card_insert_disjoint)
  qed
  have ci1: "comproot_inv (phase1_step acyc_flow x s)"
    using phase1_step_cri[OF xvs Cons.prems(3) Cons.prems(4) Cons.prems(5) Cons.prems(6) step_inb] .
  have ce1: "cr_ext_inv (phase1_step acyc_flow x s)"
    using phase1_step_crext[OF xvs Cons.prems(3) Cons.prems(4) Cons.prems(5) Cons.prems(6) Cons.prems(7) step_inb] .
  from phase1_step_nxt[OF Cons.prems(3) xlt] show ?case
  proof
    assume A: "ds_nxt (phase1_step acyc_flow x s) = ds_nxt s"
    have card1: "ds_nxt (phase1_step acyc_flow x s) = card E" using A Cons.prems(11) by simp
    show ?thesis
      using Cons.hyps[OF distr subr inv1(1) inv1(2) al1 ci1 ce1 Cons.prems(8) Emono Edisj card1] by simp
  next
    assume B: "ds_nxt (phase1_step acyc_flow x s) = Suc (ds_nxt s) ∧ ds_seen (phase1_step acyc_flow x s) ! x"
    define E2 where "E2 = insert x E"
    have fin2: "finite E2" using Cons.prems(8) by (simp add: E2_def)
    have E2seen: "E2 ⊆ {v ∈ set vs_list. ds_seen (phase1_step acyc_flow x s) ! v}" using Emono B xvs by (auto simp: E2_def)
    have E2disj: "E2 ∩ set rest = {}" using Edisj Cons.prems(1) by (auto simp: E2_def)
    have card2: "ds_nxt (phase1_step acyc_flow x s) = card E2" using B Cons.prems(11) xnotE Cons.prems(8) by (simp add: E2_def card_insert_disjoint)
    show ?thesis using Cons.hyps[OF distr subr inv1(1) inv1(2) al1 ci1 ce1 fin2 E2seen E2disj card2] by simp
  qed
qed

lemma fold_emit_crc2:
  assumes "set xs ⊆ set vs_list" "dfs_inv acyc_flow s" "ds_stk s = []"
      "art_len s" "comproot_inv s" "cr_ext_inv s"
      "finite E" "E ⊆ {v ∈ set vs_list. ds_seen s ! v}" "ds_nxt s = card E"
  shows "art_len (fold (phase2_step acyc_flow) xs s) ∧ comproot_inv (fold (phase2_step acyc_flow) xs s)
         ∧ cr_ext_inv (fold (phase2_step acyc_flow) xs s)
         ∧ (∃E'. finite E' ∧ E' ⊆ {v ∈ set vs_list. ds_seen (fold (phase2_step acyc_flow) xs s) ! v}
                 ∧ ds_nxt (fold (phase2_step acyc_flow) xs s) = card E')"
  using assms
proof (induct xs arbitrary: s E)
  case Nil thus ?case by auto
next
  case (Cons x rest)
  have xvs: "x ∈ set vs_list" using Cons.prems(1) by simp
  have xlt: "x < vcount" using xvs vs_less_vcount by simp
  have inv1: "dfs_inv acyc_flow (phase2_step acyc_flow x s)" "ds_stk (phase2_step acyc_flow x s) = []"
    using phase2_step_inv[OF xvs conjI[OF Cons.prems(2) Cons.prems(3)]] by auto
  have al1: "art_len (phase2_step acyc_flow x s)" using phase2_step_art_len[OF xvs Cons.prems(2) Cons.prems(4)] .
  have Emono: "E ⊆ {v ∈ set vs_list. ds_seen (phase2_step acyc_flow x s) ! v}"
    using Cons.prems(8) phase2_step_seen_mono[OF Cons.prems(2) xlt] by auto
  have subr: "set rest ⊆ set vs_list" using Cons.prems(1) by simp
  have Esub: "E ⊆ set vs_list" using Cons.prems(8) by auto
  have step_inb: "ds_nxt (phase2_step acyc_flow x s) ≤ length vs_list"
    using phase2_step_nxt2[OF Cons.prems(2) xlt]
  proof
    assume "ds_nxt (phase2_step acyc_flow x s) = ds_nxt s"
    thus ?thesis using Cons.prems(9) card_sub_vs_le[OF Esub] by simp
  next
    assume A: "ds_nxt (phase2_step acyc_flow x s) = Suc (ds_nxt s) ∧ ¬ ds_seen s ! x ∧ ds_seen (phase2_step acyc_flow x s) ! x"
    have xnotE: "x ∉ E" using A Cons.prems(8) by auto
    have "insert x E ⊆ set vs_list" using Esub xvs by auto
    hence "card (insert x E) ≤ length vs_list" by (rule card_sub_vs_le)
    thus ?thesis using A Cons.prems(9) xnotE Cons.prems(7) by (simp add: card_insert_disjoint)
  qed
  have ci1: "comproot_inv (phase2_step acyc_flow x s)"
    using phase2_step_cri[OF xvs Cons.prems(2) Cons.prems(3) Cons.prems(4) Cons.prems(5) step_inb] .
  have ce1: "cr_ext_inv (phase2_step acyc_flow x s)"
    using phase2_step_crext[OF xvs Cons.prems(2) Cons.prems(3) Cons.prems(4) Cons.prems(5) Cons.prems(6) step_inb] .
  from phase2_step_nxt2[OF Cons.prems(2) xlt] show ?case
  proof
    assume A: "ds_nxt (phase2_step acyc_flow x s) = ds_nxt s"
    have card1: "ds_nxt (phase2_step acyc_flow x s) = card E" using A Cons.prems(9) by simp
    show ?thesis
      using Cons.hyps[OF subr inv1(1) inv1(2) al1 ci1 ce1 Cons.prems(7) Emono card1] by simp
  next
    assume B: "ds_nxt (phase2_step acyc_flow x s) = Suc (ds_nxt s) ∧ ¬ ds_seen s ! x ∧ ds_seen (phase2_step acyc_flow x s) ! x"
    have xnotE: "x ∉ E" using B Cons.prems(8) by auto
    define E2 where "E2 = insert x E"
    have fin2: "finite E2" using Cons.prems(7) by (simp add: E2_def)
    have E2seen: "E2 ⊆ {v ∈ set vs_list. ds_seen (phase2_step acyc_flow x s) ! v}" using Emono B xvs by (auto simp: E2_def)
    have card2: "ds_nxt (phase2_step acyc_flow x s) = card E2" using B Cons.prems(9) xnotE Cons.prems(7) by (simp add: E2_def card_insert_disjoint)
    show ?thesis using Cons.hyps[OF subr inv1(1) inv1(2) al1 ci1 ce1 fin2 E2seen card2] by simp
  qed
qed

lemma build_tree_crext: "cr_ext_inv (build_tree acyc_flow)"
proof -
  have i0: "dfs_inv acyc_flow dfs_init ∧ ds_stk dfs_init = []" using dfs_init_inv by (simp add: dfs_init_def)
  have al0: "art_len dfs_init" by (rule dfs_init_art_len)
  have ci0: "comproot_inv dfs_init" by (simp add: comproot_inv_def dfs_init_def del: replicate_Suc)
  have ce0: "cr_ext_inv dfs_init" by (simp add: cr_ext_inv_def dfs_init_def del: replicate_Suc)
  have C1: "art_len (fold (phase1_step acyc_flow) vs_list dfs_init) ∧ comproot_inv (fold (phase1_step acyc_flow) vs_list dfs_init)
        ∧ cr_ext_inv (fold (phase1_step acyc_flow) vs_list dfs_init)
        ∧ (∃E'. finite E' ∧ E' ⊆ {v ∈ set vs_list. ds_seen (fold (phase1_step acyc_flow) vs_list dfs_init) ! v}
                ∧ ds_nxt (fold (phase1_step acyc_flow) vs_list dfs_init) = card E')"
    apply (rule fold_emit_crc1[where E="{}"])
    subgoal by (rule distinct_vs_list)
    subgoal by simp
    subgoal using i0 by simp
    subgoal using i0 by simp
    subgoal by (rule al0)
    subgoal by (rule ci0)
    subgoal by (rule ce0)
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by (simp add: dfs_init_def)
    done
  have P1: "art_len (phase1 acyc_flow dfs_init)" using C1 by (simp add: phase1_def)
  have CI1: "comproot_inv (phase1 acyc_flow dfs_init)" using C1 by (simp add: phase1_def)
  have CE1: "cr_ext_inv (phase1 acyc_flow dfs_init)" using C1 by (simp add: phase1_def)
  have E1ex: "∃E'. finite E' ∧ E' ⊆ {v ∈ set vs_list. ds_seen (phase1 acyc_flow dfs_init) ! v}
                ∧ ds_nxt (phase1 acyc_flow dfs_init) = card E'" using C1 by (simp add: phase1_def)
  have p1inv: "dfs_inv acyc_flow (phase1 acyc_flow dfs_init) ∧ ds_stk (phase1 acyc_flow dfs_init) = []" using phase1_inv[OF i0] .
  obtain E1 where E1f: "finite E1" and E1s: "E1 ⊆ {v ∈ set vs_list. ds_seen (phase1 acyc_flow dfs_init) ! v}"
    and E1n: "ds_nxt (phase1 acyc_flow dfs_init) = card E1" using E1ex by blast
  have C2: "art_len (fold (phase2_step acyc_flow) vs_list (phase1 acyc_flow dfs_init))
        ∧ comproot_inv (fold (phase2_step acyc_flow) vs_list (phase1 acyc_flow dfs_init))
        ∧ cr_ext_inv (fold (phase2_step acyc_flow) vs_list (phase1 acyc_flow dfs_init))
        ∧ (∃E'. finite E' ∧ E' ⊆ {v ∈ set vs_list. ds_seen (fold (phase2_step acyc_flow) vs_list (phase1 acyc_flow dfs_init)) ! v}
                ∧ ds_nxt (fold (phase2_step acyc_flow) vs_list (phase1 acyc_flow dfs_init)) = card E')"
    apply (rule fold_emit_crc2[where E=E1 and s="phase1 acyc_flow dfs_init"])
    subgoal by simp
    subgoal using p1inv by simp
    subgoal using p1inv by simp
    subgoal by (rule P1)
    subgoal by (rule CI1)
    subgoal by (rule CE1)
    subgoal by (rule E1f)
    subgoal by (rule E1s)
    subgoal by (rule E1n)
    done
  have "cr_ext_inv (phase2 acyc_flow (phase1 acyc_flow dfs_init))" using C2 by (simp add: phase2_def)
  thus ?thesis by (simp add: build_tree_def Let_def cr_ext_inv_def cr_ext_ok_def)
qed

text ‹Obligation 9 (‹init_strict›, strong feasibility): each non-root tree vertex's parent edge
      is strictly interior in the required direction.  Interior edges are free (both residual bounds
      hold); component-root edges are artificial, and their direction together with the tree-capacity
      (@{const art_tree_cap}) makes exactly the required bound strict.›

lemma strict_interior:
  assumes vlt: "v < vcount" and vseen: "ds_seen (build_tree acyc_flow) ! v" and prnt: "ds_prnt (build_tree acyc_flow) ! v < vcount"
  shows "if ds_dir (build_tree acyc_flow) ! v
         then ereal (h (flow_all ! (ds_par (build_tree acyc_flow) ! v)))
                < (if cap_all ! (ds_par (build_tree acyc_flow) ! v) = - 1 then ∞ else ereal (h (cap_all ! (ds_par (build_tree acyc_flow) ! v))))
         else 0 < flow_all ! (ds_par (build_tree acyc_flow) ! v)"
proof -
  have pe: "ds_par (build_tree acyc_flow) ! v < m" and free: "is_free acyc_flow (ds_par (build_tree acyc_flow) ! v)"
    using build_tree_par_edge[OF vlt vseen prnt] by simp_all
  have pos: "0 < acyc_flow ! (ds_par (build_tree acyc_flow) ! v)"
   and disj: "capacity_list ! (ds_par (build_tree acyc_flow) ! v) = - 1 ∨ acyc_flow ! (ds_par (build_tree acyc_flow) ! v) < capacity_list ! (ds_par (build_tree acyc_flow) ! v)"
    using free is_free_iff[OF acyc_flow_nonneg acyc_flow_le_cap pe] by simp_all
  have fa: "flow_all ! (ds_par (build_tree acyc_flow) ! v) = acyc_flow ! (ds_par (build_tree acyc_flow) ! v)" using flow_all_real[OF pe] .
  have ca: "cap_all ! (ds_par (build_tree acyc_flow) ! v) = capacity_list ! (ds_par (build_tree acyc_flow) ! v)" using cap_all_real[OF pe] .
  show ?thesis
  proof (cases "ds_dir (build_tree acyc_flow) ! v")
    case dir: True
    show ?thesis
    proof (cases "capacity_list ! (ds_par (build_tree acyc_flow) ! v) = - 1")
      case True thus ?thesis using dir fa ca by simp
    next
      case False
      have lt: "acyc_flow ! (ds_par (build_tree acyc_flow) ! v) < capacity_list ! (ds_par (build_tree acyc_flow) ! v)" using disj False by simp
      show ?thesis using dir fa ca False lt by simp
    qed
  next
    case False
    show ?thesis using False fa pos by simp
  qed
qed

lemma strict_comproot:
  assumes vlt: "v < vcount" and vseen: "ds_seen (build_tree acyc_flow) ! v" and prnt: "ds_prnt (build_tree acyc_flow) ! v = vcount"
  shows "if ds_dir (build_tree acyc_flow) ! v
         then ereal (h (flow_all ! (ds_par (build_tree acyc_flow) ! v)))
                < (if cap_all ! (ds_par (build_tree acyc_flow) ! v) = - 1 then ∞ else ereal (h (cap_all ! (ds_par (build_tree acyc_flow) ! v))))
         else 0 < flow_all ! (ds_par (build_tree acyc_flow) ! v)"
proof -
  have ext: "cr_ext_ok (build_tree acyc_flow) v" using build_tree_crext vlt vseen prnt by (simp add: cr_ext_inv_def)
  have cok: "comproot_edge_ok (build_tree acyc_flow) v" using build_tree_comproot_inv vlt vseen prnt by (simp add: comproot_inv_def)
  have pm: "m ≤ ds_par (build_tree acyc_flow) ! v" and knxt: "ds_par (build_tree acyc_flow) ! v - m < ds_nxt (build_tree acyc_flow)"
    using cok by (simp_all add: comproot_edge_ok_def)
  have kK: "ds_par (build_tree acyc_flow) ! v - m < Kart" using knxt by (simp add: Kart_def)
  have mm: "m + (ds_par (build_tree acyc_flow) ! v - m) = ds_par (build_tree acyc_flow) ! v" using pm by simp
  have dirv: "ds_dir (build_tree acyc_flow) ! v = art_dir v" using ext by (simp add: cr_ext_ok_def)
  have flw: "flow_all ! (ds_par (build_tree acyc_flow) ! v) = art_flow v"
  proof -
    have "flow_all ! (ds_par (build_tree acyc_flow) ! v) = ds_aflw (build_tree acyc_flow) ! (ds_par (build_tree acyc_flow) ! v - m)"
      using flow_all_art[OF kK] mm by simp
    thus ?thesis using ext by (simp add: cr_ext_ok_def)
  qed
  have cpv: "cap_all ! (ds_par (build_tree acyc_flow) ! v) = art_tree_cap v"
  proof -
    have "cap_all ! (ds_par (build_tree acyc_flow) ! v) = ds_acap (build_tree acyc_flow) ! (ds_par (build_tree acyc_flow) ! v - m)"
      using cap_all_art[OF kK] mm by simp
    thus ?thesis using ext by (simp add: cr_ext_ok_def)
  qed
  have nn: "0 ≤ art_flow v" by (simp add: art_flow_def)
  show ?thesis
  proof (cases "art_dir v")
    case up: True
    have cc: "cap_all ! (ds_par (build_tree acyc_flow) ! v) = art_flow v + 1" using cpv up by (simp add: art_tree_cap_def)
    have ne: "cap_all ! (ds_par (build_tree acyc_flow) ! v) ≠ - 1" using cc nn by simp
    have lt: "ereal (h (flow_all ! (ds_par (build_tree acyc_flow) ! v))) < ereal (h (cap_all ! (ds_par (build_tree acyc_flow) ! v)))"
      using flw cc by simp
    have dtrue: "ds_dir (build_tree acyc_flow) ! v" using dirv up by simp
    show ?thesis using dtrue ne lt by simp
  next
    case down: False
    have gt: "0 < art_flow v" using down by (simp add: art_flow_def art_dir_def)
    have dfalse: "¬ ds_dir (build_tree acyc_flow) ! v" using dirv down by simp
    show ?thesis using dfalse flw gt by simp
  qed
qed

lemma strict_core:
  assumes v: "v ∈ Vseen"
  shows "if ds_dir (build_tree acyc_flow) ! v
         then ereal (h (flow_all ! (ds_par (build_tree acyc_flow) ! v)))
                < (if cap_all ! (ds_par (build_tree acyc_flow) ! v) = - 1 then ∞ else ereal (h (cap_all ! (ds_par (build_tree acyc_flow) ! v))))
         else 0 < flow_all ! (ds_par (build_tree acyc_flow) ! v)"
proof -
  have vlt: "v < vcount" and vseen: "ds_seen (build_tree acyc_flow) ! v" using v by (auto simp: Vseen_def)
  show ?thesis
  proof (cases "ds_prnt (build_tree acyc_flow) ! v < vcount")
    case True thus ?thesis using strict_interior[OF vlt vseen] by simp
  next
    case False
    have tsi: "tree_seen_inv (build_tree acyc_flow)" using build_tree_inv by (simp add: dfs_inv_def)
    have "ds_prnt (build_tree acyc_flow) ! v = vcount" using tsi vlt vseen False unfolding tree_seen_inv_def by blast
    thus ?thesis using strict_comproot[OF vlt vseen] by simp
  qed
qed

lemma NSinit_strict:
  "∀v∈NS.𝒱 - {vcount}.
      if nth (ds_dir (build_tree acyc_flow)) v
      then ereal (h (nth flow_all (nth (ds_par (build_tree acyc_flow)) v)))
             < (if nth (ds_par (build_tree acyc_flow)) v < m + Kart
                then if cap_all ! nth (ds_par (build_tree acyc_flow)) v = - 1 then ∞
                     else ereal (h (cap_all ! nth (ds_par (build_tree acyc_flow)) v))
                else ∞)
      else 0 < nth flow_all (nth (ds_par (build_tree acyc_flow)) v)"
proof (rule ballI)
  fix v assume "v ∈ NS.𝒱 - {vcount}"
  hence v: "v ∈ Vseen" using NS_V_minus_root by simp
  have vlt: "v < vcount" and vseen: "ds_seen (build_tree acyc_flow) ! v" using v by (auto simp: Vseen_def)
  have emarc: "ds_par (build_tree acyc_flow) ! v < m + Kart" using par_lt_marc[OF vlt vseen] .
  show "if nth (ds_dir (build_tree acyc_flow)) v
        then ereal (h (nth flow_all (nth (ds_par (build_tree acyc_flow)) v)))
               < (if nth (ds_par (build_tree acyc_flow)) v < m + Kart
                  then if cap_all ! nth (ds_par (build_tree acyc_flow)) v = - 1 then ∞
                       else ereal (h (cap_all ! nth (ds_par (build_tree acyc_flow)) v))
                  else ∞)
        else 0 < nth flow_all (nth (ds_par (build_tree acyc_flow)) v)"
    unfolding if_P[OF emarc] by (rule strict_core[OF v])
qed


subsection ‹Obligation 10 (init_tree_corr): the parent edges realise the abstract arborescence›

text ‹Every non-root tree vertex's parent edge realises its tree edge (endpoints ‹{v, ds_prnt bt ! v}›,
      correctly oriented by the direction flag), the finished parent-edge set has exactly the abstract
      arborescence @{term ‹abstract_arb Sarb›} as its endpoint-set family, and the walk to the root is the
      @{const follow} chain (@{thm follow_walk_root}).›

lemma tc_endpoints_interior:
  assumes vlt: "v < vcount" and vseen: "ds_seen (build_tree acyc_flow) ! v" and prnt: "ds_prnt (build_tree acyc_flow) ! v < vcount"
  shows "fst_all ! (ds_par (build_tree acyc_flow) ! v) = (if ds_dir (build_tree acyc_flow) ! v then v else ds_prnt (build_tree acyc_flow) ! v)
       ∧ snd_all ! (ds_par (build_tree acyc_flow) ! v) = (if ds_dir (build_tree acyc_flow) ! v then ds_prnt (build_tree acyc_flow) ! v else v)"
proof -
  from build_tree_par_edge[OF vlt vseen prnt]
  have pe: "ds_par (build_tree acyc_flow) ! v < m"
   and fl: "fst_list ! (ds_par (build_tree acyc_flow) ! v) = (if ds_dir (build_tree acyc_flow) ! v then v else ds_prnt (build_tree acyc_flow) ! v)"
   and sl: "snd_list ! (ds_par (build_tree acyc_flow) ! v) = (if ds_dir (build_tree acyc_flow) ! v then ds_prnt (build_tree acyc_flow) ! v else v)"
    by blast+
  have fa: "fst_all ! (ds_par (build_tree acyc_flow) ! v) = fst_list ! (ds_par (build_tree acyc_flow) ! v)" using fst_all_real[OF pe] .
  have sa: "snd_all ! (ds_par (build_tree acyc_flow) ! v) = snd_list ! (ds_par (build_tree acyc_flow) ! v)" using snd_all_real[OF pe] .
  show ?thesis using fa sa fl sl by simp
qed

lemma tc_endpoints_comproot:
  assumes vlt: "v < vcount" and vseen: "ds_seen (build_tree acyc_flow) ! v" and prnt: "ds_prnt (build_tree acyc_flow) ! v = vcount"
  shows "fst_all ! (ds_par (build_tree acyc_flow) ! v) = (if ds_dir (build_tree acyc_flow) ! v then v else ds_prnt (build_tree acyc_flow) ! v)
       ∧ snd_all ! (ds_par (build_tree acyc_flow) ! v) = (if ds_dir (build_tree acyc_flow) ! v then ds_prnt (build_tree acyc_flow) ! v else v)"
proof -
  have ext: "cr_ext_ok (build_tree acyc_flow) v" using build_tree_crext vlt vseen prnt by (simp add: cr_ext_inv_def)
  have cok: "comproot_edge_ok (build_tree acyc_flow) v" using build_tree_comproot_inv vlt vseen prnt by (simp add: comproot_inv_def)
  have pm: "m ≤ ds_par (build_tree acyc_flow) ! v" and knxt: "ds_par (build_tree acyc_flow) ! v - m < ds_nxt (build_tree acyc_flow)"
    and af: "ds_afst (build_tree acyc_flow) ! (ds_par (build_tree acyc_flow) ! v - m) = (if art_dir v then v else vcount)"
    and as: "ds_asnd (build_tree acyc_flow) ! (ds_par (build_tree acyc_flow) ! v - m) = (if art_dir v then vcount else v)"
    using cok by (simp_all add: comproot_edge_ok_def)
  have kK: "ds_par (build_tree acyc_flow) ! v - m < Kart" using knxt by (simp add: Kart_def)
  have mm: "m + (ds_par (build_tree acyc_flow) ! v - m) = ds_par (build_tree acyc_flow) ! v" using pm by simp
  have dirv: "ds_dir (build_tree acyc_flow) ! v = art_dir v" using ext by (simp add: cr_ext_ok_def)
  have fa: "fst_all ! (ds_par (build_tree acyc_flow) ! v) = ds_afst (build_tree acyc_flow) ! (ds_par (build_tree acyc_flow) ! v - m)"
    using fst_all_art[OF kK] mm by simp
  have sa: "snd_all ! (ds_par (build_tree acyc_flow) ! v) = ds_asnd (build_tree acyc_flow) ! (ds_par (build_tree acyc_flow) ! v - m)"
    using snd_all_art[OF kK] mm by simp
  show ?thesis using fa sa af as dirv prnt by simp
qed

lemma tc_endpoints:
  assumes v: "v ∈ Vseen"
  shows "fst_all ! (ds_par (build_tree acyc_flow) ! v) = (if ds_dir (build_tree acyc_flow) ! v then v else ds_prnt (build_tree acyc_flow) ! v)
       ∧ snd_all ! (ds_par (build_tree acyc_flow) ! v) = (if ds_dir (build_tree acyc_flow) ! v then ds_prnt (build_tree acyc_flow) ! v else v)"
proof -
  have vlt: "v < vcount" and vseen: "ds_seen (build_tree acyc_flow) ! v" using v by (auto simp: Vseen_def)
  show ?thesis
  proof (cases "ds_prnt (build_tree acyc_flow) ! v < vcount")
    case True thus ?thesis using tc_endpoints_interior[OF vlt vseen] by simp
  next
    case False
    have tsi: "tree_seen_inv (build_tree acyc_flow)" using build_tree_inv by (simp add: dfs_inv_def)
    have "ds_prnt (build_tree acyc_flow) ! v = vcount" using tsi vlt vseen False unfolding tree_seen_inv_def by blast
    thus ?thesis using tc_endpoints_comproot[OF vlt vseen] by simp
  qed
qed

lemma tc_orient: "v ∈ Vseen ⟹
  (if ds_dir (build_tree acyc_flow) ! v then fst_all ! (ds_par (build_tree acyc_flow) ! v) else snd_all ! (ds_par (build_tree acyc_flow) ! v)) = v"
  using tc_endpoints[of v] by (cases "ds_dir (build_tree acyc_flow) ! v") simp_all

lemma tc_other: "v ∈ Vseen ⟹
  (if ds_dir (build_tree acyc_flow) ! v then snd_all ! (ds_par (build_tree acyc_flow) ! v) else fst_all ! (ds_par (build_tree acyc_flow) ! v)) = ds_prnt (build_tree acyc_flow) ! v"
  using tc_endpoints[of v] by (cases "ds_dir (build_tree acyc_flow) ! v") simp_all

lemma tc_edge: "v ∈ Vseen ⟹
  {fst_all ! (ds_par (build_tree acyc_flow) ! v), snd_all ! (ds_par (build_tree acyc_flow) ! v)} = {v, ds_prnt (build_tree acyc_flow) ! v}"
  using tc_endpoints[of v] by (cases "ds_dir (build_tree acyc_flow) ! v") (auto simp: insert_commute)

lemma arb_edge_set: "abstract_arb Sarb = (λv. {v, ds_prnt (build_tree acyc_flow) ! v}) ` Vseen"
proof -
  have "abstract_arb Sarb = {{x, y} |x y. Sprnt x = Some y}" by (simp add: abstract_arb_def Sarb_sel)
  also have "… = (λv. {v, ds_prnt (build_tree acyc_flow) ! v}) ` Vseen"
    by (auto simp: Sprnt_def split: if_splits)
  finally show ?thesis .
qed

lemma tc_elt:
  assumes v: "v ∈ Vseen"
  shows "(λe. {if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart))),
                if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart)))})
           (nth (ds_par (build_tree acyc_flow)) v) = {v, ds_prnt (build_tree acyc_flow) ! v}"
proof -
  have vlt: "v < vcount" and vseen: "ds_seen (build_tree acyc_flow) ! v" using v by (auto simp: Vseen_def)
  have emarc: "ds_par (build_tree acyc_flow) ! v < m + Kart" using par_lt_marc[OF vlt vseen] .
  show ?thesis by (simp only: if_P[OF emarc] tc_edge[OF v])
qed

lemma tc_image:
  "(λe. {if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart))),
           if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart)))})
     ` (nth (ds_par (build_tree acyc_flow)) ` (NS.𝒱 - {vcount})) = abstract_arb Sarb"
proof -
  let ?f = "λe. {if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart))),
                  if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart)))}"
  have "?f ` (nth (ds_par (build_tree acyc_flow)) ` (NS.𝒱 - {vcount}))
      = (λv. ?f (nth (ds_par (build_tree acyc_flow)) v)) ` Vseen"
    by (simp only: NS_V_minus_root image_image)
  also have "… = (λv. {v, ds_prnt (build_tree acyc_flow) ! v}) ` Vseen"
    by (rule image_cong[OF refl tc_elt])
  also have "… = abstract_arb Sarb" by (rule arb_edge_set[symmetric])
  finally show ?thesis .
qed

lemma tc_walk:
  assumes vVs: "v ∈ Vseen"
  shows "∃q. distinct (v # ds_prnt (build_tree acyc_flow) ! v # q)
             ∧ walk_betw (abstract_arb Sarb) v (v # ds_prnt (build_tree acyc_flow) ! v # q) vcount"
proof -
  have vVarb: "v ∈ Varb" using vVs by (simp add: Varb_def)
  have sprntv: "Sprnt v = Some (ds_prnt (build_tree acyc_flow) ! v)" using vVs by (simp add: Sprnt_def)
  have f1: "follow Sprnt v = v # follow Sprnt (ds_prnt (build_tree acyc_flow) ! v)"
    using follow_ps_simps[OF parent_spec_Sprnt] sprntv by simp
  have f2: "follow Sprnt (ds_prnt (build_tree acyc_flow) ! v) = ds_prnt (build_tree acyc_flow) ! v # tl (follow Sprnt (ds_prnt (build_tree acyc_flow) ! v))"
    using follow_ps_simps[OF parent_spec_Sprnt, of "ds_prnt (build_tree acyc_flow) ! v"] by (auto split: option.splits)
  define q where "q = tl (follow Sprnt (ds_prnt (build_tree acyc_flow) ! v))"
  have flist: "follow Sprnt v = v # ds_prnt (build_tree acyc_flow) ! v # q" using f1 f2 q_def by simp
  have dist: "distinct (follow Sprnt v)" by (rule follow_distinct_ps[OF parent_spec_Sprnt])
  have walk: "walk_betw (abstract_arb Sarb) v (follow Sprnt v) vcount"
    using follow_walk_root[OF arb_invar_Sarb vVarb] by (simp add: Sarb_sel)
  from dist walk have "distinct (v # ds_prnt (build_tree acyc_flow) ! v # q)
        ∧ walk_betw (abstract_arb Sarb) v (v # ds_prnt (build_tree acyc_flow) ! v # q) vcount"
    using flist by simp
  thus ?thesis by blast
qed

lemma tc_orient_listarr:
  assumes v: "v ∈ Vseen"
  shows "if nth (ds_dir (build_tree acyc_flow)) v
          then (if nth (ds_par (build_tree acyc_flow)) v < m + Kart then fst_all ! nth (ds_par (build_tree acyc_flow)) v else fst (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) = v
          else (if nth (ds_par (build_tree acyc_flow)) v < m + Kart then snd_all ! nth (ds_par (build_tree acyc_flow)) v else snd (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) = v"
proof -
  have vlt: "v < vcount" and vseen: "ds_seen (build_tree acyc_flow) ! v" using v by (auto simp: Vseen_def)
  have emarc: "ds_par (build_tree acyc_flow) ! v < m + Kart" using par_lt_marc[OF vlt vseen] .
  have red: "(if nth (ds_dir (build_tree acyc_flow)) v
          then (if nth (ds_par (build_tree acyc_flow)) v < m + Kart then fst_all ! nth (ds_par (build_tree acyc_flow)) v else fst (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) = v
          else (if nth (ds_par (build_tree acyc_flow)) v < m + Kart then snd_all ! nth (ds_par (build_tree acyc_flow)) v else snd (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) = v)
       = (if ds_dir (build_tree acyc_flow) ! v then fst_all ! (ds_par (build_tree acyc_flow) ! v) = v else snd_all ! (ds_par (build_tree acyc_flow) ! v) = v)"
    by (simp only: if_P[OF emarc])
  show ?thesis unfolding red using tc_orient[OF v] by (cases "ds_dir (build_tree acyc_flow) ! v") simp_all
qed

lemma tc_walk_listarr:
  assumes v: "v ∈ Vseen"
  shows "∃q. distinct (v # (if nth (ds_dir (build_tree acyc_flow)) v then if nth (ds_par (build_tree acyc_flow)) v < m + Kart then snd_all ! nth (ds_par (build_tree acyc_flow)) v else snd (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart))) else if nth (ds_par (build_tree acyc_flow)) v < m + Kart then fst_all ! nth (ds_par (build_tree acyc_flow)) v else fst (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) # q)
             ∧ walk_betw (abstract_arb Sarb) v (v # (if nth (ds_dir (build_tree acyc_flow)) v then if nth (ds_par (build_tree acyc_flow)) v < m + Kart then snd_all ! nth (ds_par (build_tree acyc_flow)) v else snd (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart))) else if nth (ds_par (build_tree acyc_flow)) v < m + Kart then fst_all ! nth (ds_par (build_tree acyc_flow)) v else fst (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) # q) vcount"
proof -
  have vlt: "v < vcount" and vseen: "ds_seen (build_tree acyc_flow) ! v" using v by (auto simp: Vseen_def)
  have emarc: "ds_par (build_tree acyc_flow) ! v < m + Kart" using par_lt_marc[OF vlt vseen] .
  have Xval: "(if nth (ds_dir (build_tree acyc_flow)) v then if nth (ds_par (build_tree acyc_flow)) v < m + Kart then snd_all ! nth (ds_par (build_tree acyc_flow)) v else snd (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart))) else if nth (ds_par (build_tree acyc_flow)) v < m + Kart then fst_all ! nth (ds_par (build_tree acyc_flow)) v else fst (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) = ds_prnt (build_tree acyc_flow) ! v"
    by (simp only: if_P[OF emarc]) (rule tc_other[OF v])
  show ?thesis unfolding Xval by (rule tc_walk[OF v])
qed

lemma NSinit_tree_corr:
  "(∀v∈NS.𝒱 - {vcount}. nth (ds_par (build_tree acyc_flow)) v ∈ {0..<m + Kart}
      ∧ (if nth (ds_dir (build_tree acyc_flow)) v
          then (if nth (ds_par (build_tree acyc_flow)) v < m + Kart then fst_all ! nth (ds_par (build_tree acyc_flow)) v else fst (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) = v
          else (if nth (ds_par (build_tree acyc_flow)) v < m + Kart then snd_all ! nth (ds_par (build_tree acyc_flow)) v else snd (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) = v)
      ∧ (∃q. distinct (v # (if nth (ds_dir (build_tree acyc_flow)) v then if nth (ds_par (build_tree acyc_flow)) v < m + Kart then snd_all ! nth (ds_par (build_tree acyc_flow)) v else snd (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart))) else if nth (ds_par (build_tree acyc_flow)) v < m + Kart then fst_all ! nth (ds_par (build_tree acyc_flow)) v else fst (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) # q)
             ∧ walk_betw (abstract_arb Sarb) v (v # (if nth (ds_dir (build_tree acyc_flow)) v then if nth (ds_par (build_tree acyc_flow)) v < m + Kart then snd_all ! nth (ds_par (build_tree acyc_flow)) v else snd (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart))) else if nth (ds_par (build_tree acyc_flow)) v < m + Kart then fst_all ! nth (ds_par (build_tree acyc_flow)) v else fst (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) # q) vcount))
   ∧ (λe. {if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart))), if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart)))}) ` nth (ds_par (build_tree acyc_flow)) ` (NS.𝒱 - {vcount}) = abstract_arb Sarb"
proof (rule conjI)
  show "∀v∈NS.𝒱 - {vcount}. nth (ds_par (build_tree acyc_flow)) v ∈ {0..<m + Kart}
      ∧ (if nth (ds_dir (build_tree acyc_flow)) v
          then (if nth (ds_par (build_tree acyc_flow)) v < m + Kart then fst_all ! nth (ds_par (build_tree acyc_flow)) v else fst (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) = v
          else (if nth (ds_par (build_tree acyc_flow)) v < m + Kart then snd_all ! nth (ds_par (build_tree acyc_flow)) v else snd (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) = v)
      ∧ (∃q. distinct (v # (if nth (ds_dir (build_tree acyc_flow)) v then if nth (ds_par (build_tree acyc_flow)) v < m + Kart then snd_all ! nth (ds_par (build_tree acyc_flow)) v else snd (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart))) else if nth (ds_par (build_tree acyc_flow)) v < m + Kart then fst_all ! nth (ds_par (build_tree acyc_flow)) v else fst (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) # q)
             ∧ walk_betw (abstract_arb Sarb) v (v # (if nth (ds_dir (build_tree acyc_flow)) v then if nth (ds_par (build_tree acyc_flow)) v < m + Kart then snd_all ! nth (ds_par (build_tree acyc_flow)) v else snd (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart))) else if nth (ds_par (build_tree acyc_flow)) v < m + Kart then fst_all ! nth (ds_par (build_tree acyc_flow)) v else fst (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) # q) vcount)"
  proof (rule ballI)
    fix v assume "v ∈ NS.𝒱 - {vcount}"
    hence v: "v ∈ Vseen" using NS_V_minus_root by simp
    have vlt: "v < vcount" and vseen: "ds_seen (build_tree acyc_flow) ! v" using v by (auto simp: Vseen_def)
    have emarc: "ds_par (build_tree acyc_flow) ! v < m + Kart" using par_lt_marc[OF vlt vseen] .
    show "nth (ds_par (build_tree acyc_flow)) v ∈ {0..<m + Kart}
      ∧ (if nth (ds_dir (build_tree acyc_flow)) v
          then (if nth (ds_par (build_tree acyc_flow)) v < m + Kart then fst_all ! nth (ds_par (build_tree acyc_flow)) v else fst (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) = v
          else (if nth (ds_par (build_tree acyc_flow)) v < m + Kart then snd_all ! nth (ds_par (build_tree acyc_flow)) v else snd (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) = v)
      ∧ (∃q. distinct (v # (if nth (ds_dir (build_tree acyc_flow)) v then if nth (ds_par (build_tree acyc_flow)) v < m + Kart then snd_all ! nth (ds_par (build_tree acyc_flow)) v else snd (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart))) else if nth (ds_par (build_tree acyc_flow)) v < m + Kart then fst_all ! nth (ds_par (build_tree acyc_flow)) v else fst (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) # q)
             ∧ walk_betw (abstract_arb Sarb) v (v # (if nth (ds_dir (build_tree acyc_flow)) v then if nth (ds_par (build_tree acyc_flow)) v < m + Kart then snd_all ! nth (ds_par (build_tree acyc_flow)) v else snd (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart))) else if nth (ds_par (build_tree acyc_flow)) v < m + Kart then fst_all ! nth (ds_par (build_tree acyc_flow)) v else fst (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) # q) vcount)"
    proof (intro conjI)
      show "nth (ds_par (build_tree acyc_flow)) v ∈ {0..<m + Kart}"
        using emarc by simp
    next
      show "if nth (ds_dir (build_tree acyc_flow)) v
          then (if nth (ds_par (build_tree acyc_flow)) v < m + Kart then fst_all ! nth (ds_par (build_tree acyc_flow)) v else fst (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) = v
          else (if nth (ds_par (build_tree acyc_flow)) v < m + Kart then snd_all ! nth (ds_par (build_tree acyc_flow)) v else snd (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) = v"
        by (rule tc_orient_listarr[OF v])
    next
      show "∃q. distinct (v # (if nth (ds_dir (build_tree acyc_flow)) v then if nth (ds_par (build_tree acyc_flow)) v < m + Kart then snd_all ! nth (ds_par (build_tree acyc_flow)) v else snd (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart))) else if nth (ds_par (build_tree acyc_flow)) v < m + Kart then fst_all ! nth (ds_par (build_tree acyc_flow)) v else fst (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) # q)
             ∧ walk_betw (abstract_arb Sarb) v (v # (if nth (ds_dir (build_tree acyc_flow)) v then if nth (ds_par (build_tree acyc_flow)) v < m + Kart then snd_all ! nth (ds_par (build_tree acyc_flow)) v else snd (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart))) else if nth (ds_par (build_tree acyc_flow)) v < m + Kart then fst_all ! nth (ds_par (build_tree acyc_flow)) v else fst (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) # q) vcount"
        by (rule tc_walk_listarr[OF v])
    qed
  qed
next
  show "(λe. {if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart))), if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart)))}) ` nth (ds_par (build_tree acyc_flow)) ` (NS.𝒱 - {vcount}) = abstract_arb Sarb"
    by (rule tc_image)
qed


section ‹The @{locale network_simplex_init} interpretation for the constructed initial basis›

text ‹Extending @{term NS} with the concrete starting basis produced by @{const build_tree}: the flow
      @{const flow_all}, the potentials @{term ‹ds_pot (build_tree acyc_flow)›}, the arborescence @{term Sarb}, the
      parent/direction maps @{term ‹ds_par (build_tree acyc_flow)›} / @{term ‹ds_dir (build_tree acyc_flow)›}, the edge-state
      array @{const state_all} and the selector seed @{const init_sel}. Because @{term NS} already
      discharges every ‹network_simplex_spec› axiom, ‹unfold_locales› leaves only the 10
      @{locale network_simplex_init} obligations. Seven are now proved — the trivial store invariant,
      the tree invariant @{thm arb_invar_Sarb}, the selector seed (@{thm NSinit_sel_invar}), the
      flow/edge-partition fit (@{thm NSinit_flow_fits}), the potential fit (@{thm NSinit_pot_fits}),
      strong feasibility (@{thm NSinit_strict}) and the tree correspondence (@{thm NSinit_tree_corr}).
      The remaining three (the store validity @{term ‹NS.pot_valid›}, the ‹b›-flow and the
      spanning-tree partition) each need extra carried invariants and are left as ∗‹sorry› for now.›

subsection ‹Validity of the initial potentials (obligation 2 / init_pot_valid)›

text ‹The built potential is a valid network-simplex potential: it satisfies the store-length
      invariant and, at every vertex, the good-potential certificate good_pot_val_c together with
      the descriptor bound pv_invar. The certificate is obtained from a closed form of the
      potential as a signed sum of tree-path edge costs (pot_repr), proved by well-founded
      induction along the parent relation; distinctness of the path edges (par_inj) keeps the
      cost sums honest, and exactly one artificial (root-incident) edge sits at the top of each
      path, which is what bounds the root-incident count by one.›

lemma par_inj:
  assumes u: "u ∈ Vseen" and u': "u' ∈ Vseen"
    and eq: "ds_par (build_tree acyc_flow) ! u = ds_par (build_tree acyc_flow) ! u'"
  shows "u = u'"
proof -
  let ?bt = "build_tree acyc_flow"
  let ?p = "λx. ds_prnt ?bt ! x"
  have ult: "u < vcount" and useen: "ds_seen ?bt ! u" using u by (auto simp: Vseen_def)
  have u'lt: "u' < vcount" and u'seen: "ds_seen ?bt ! u'" using u' by (auto simp: Vseen_def)
  have stepu: "(u, ?p u) ∈ pstep ?bt" using ult useen by (auto simp: pstep_def)
  have stepu': "(u', ?p u') ∈ pstep ?bt" using u'lt u'seen by (auto simp: pstep_def)
  have unp: "u ≠ ?p u"
  proof
    assume "u = ?p u"
    hence "(u, u) ∈ (pstep ?bt)⇧+" using stepu by (auto intro: r_into_trancl)
    thus False using pstep_acyclic by (simp add: acyclic_def)
  qed
  have u'np: "u' ≠ ?p u'"
  proof
    assume "u' = ?p u'"
    hence "(u', u') ∈ (pstep ?bt)⇧+" using stepu' by (auto intro: r_into_trancl)
    thus False using pstep_acyclic by (simp add: acyclic_def)
  qed
  have setu: "{fst_all ! (ds_par ?bt ! u), snd_all ! (ds_par ?bt ! u)} = {u, ?p u}"
    using tc_endpoints[OF u] by (cases "ds_dir ?bt ! u") auto
  have setu': "{fst_all ! (ds_par ?bt ! u'), snd_all ! (ds_par ?bt ! u')} = {u', ?p u'}"
    using tc_endpoints[OF u'] by (cases "ds_dir ?bt ! u'") auto
  have "{u, ?p u} = {u', ?p u'}" using setu setu' eq by simp
  hence "(u = u' ∧ ?p u = ?p u') ∨ (u = ?p u' ∧ ?p u = u')"
    using unp u'np by (auto simp: doubleton_eq_iff)
  thus ?thesis
  proof
    assume "u = u' ∧ ?p u = ?p u'" thus ?thesis by simp
  next
    assume A: "u = ?p u' ∧ ?p u = u'"
    have "(u, u') ∈ pstep ?bt" using stepu A by argo
    moreover have "(u', u) ∈ pstep ?bt" using stepu' A by argo
    ultimately have "(u, u) ∈ (pstep ?bt)⇧+" by (meson trancl.simps)
    thus ?thesis using pstep_acyclic by (simp add: acyclic_def)
  qed
qed

lemma PS_finite: "finite (pstep (build_tree acyc_flow))"
proof -
  have "pstep (build_tree acyc_flow) = (λx. (x, ds_prnt (build_tree acyc_flow) ! x)) ` Vseen"
    by (auto simp: pstep_def Vseen_def)
  thus ?thesis using Vseen_finite by simp
qed

lemma wf_PS_conv: "wf ((pstep (build_tree acyc_flow))¯)"
  using PS_finite pstep_acyclic
  by (simp add: finite_acyclic_wf acyclic_converse finite_converse)

lemma anc_step:
  assumes w: "w ∈ Vseen"
  shows "{u. (w,u) ∈ (pstep (build_tree acyc_flow))⇧*} = insert w {u. (ds_prnt (build_tree acyc_flow) ! w, u) ∈ (pstep (build_tree acyc_flow))⇧*}"
    (is "?L = insert w ?R")
proof
  have wlt: "w < vcount" and wseen: "ds_seen (build_tree acyc_flow) ! w" using w by (auto simp: Vseen_def)
  have step: "(w, ds_prnt (build_tree acyc_flow) ! w) ∈ pstep (build_tree acyc_flow)"
    using wlt wseen by (auto simp: pstep_def)
  have sv: "⋀y. (w, y) ∈ pstep (build_tree acyc_flow) ⟹ y = ds_prnt (build_tree acyc_flow) ! w"
    using wlt wseen by (auto simp: pstep_def)
  show "?L ⊆ insert w ?R"
  proof
    fix u assume "u ∈ ?L"
    hence "(w,u) ∈ (pstep (build_tree acyc_flow))⇧*" by simp
    thus "u ∈ insert w ?R"
      by (cases rule: converse_rtranclE) (auto dest: sv)
  qed
next
  have wlt: "w < vcount" and wseen: "ds_seen (build_tree acyc_flow) ! w" using w by (auto simp: Vseen_def)
  have step: "(w, ds_prnt (build_tree acyc_flow) ! w) ∈ pstep (build_tree acyc_flow)"
    using wlt wseen by (auto simp: pstep_def)
  show "insert w ?R ⊆ ?L"
    using step by (auto intro: converse_rtrancl_into_rtrancl)
qed

lemma w_notin_anc_parent:
  assumes w: "w ∈ Vseen"
  shows "w ∉ {u. (ds_prnt (build_tree acyc_flow) ! w, u) ∈ (pstep (build_tree acyc_flow))⇧*}"
proof
  assume "w ∈ {u. (ds_prnt (build_tree acyc_flow) ! w, u) ∈ (pstep (build_tree acyc_flow))⇧*}"
  hence "(ds_prnt (build_tree acyc_flow) ! w, w) ∈ (pstep (build_tree acyc_flow))⇧*" by simp
  moreover have "(w, ds_prnt (build_tree acyc_flow) ! w) ∈ pstep (build_tree acyc_flow)"
    using w by (auto simp: pstep_def Vseen_def)
  ultimately have "(w, w) ∈ (pstep (build_tree acyc_flow))⇧+" by (meson rtrancl_into_trancl2)
  thus False using pstep_acyclic by (simp add: acyclic_def)
qed

lemma anc_sub:
  assumes "(w0, u) ∈ (pstep (build_tree acyc_flow))⇧*" and "w0 ∈ insert vcount Vseen"
  shows "u ∈ insert vcount Vseen"
  using assms
proof (induction rule: rtrancl_induct)
  case base thus ?case by simp
next
  case (step y z)
  from step(2) have ylt: "y < vcount" and yseen: "ds_seen (build_tree acyc_flow) ! y"
    and zp: "z = ds_prnt (build_tree acyc_flow) ! y" by (auto simp: pstep_def)
  show ?case using build_tree_parent_in_seen[OF ylt yseen] zp by (auto simp: Vseen_def)
qed

lemma pot_repr:
  assumes "w ∈ insert vcount Vseen"
  shows "∃A D. A ⊆ {0..<m+Kart} ∧ D ⊆ {0..<m+Kart} ∧ A ∩ D = {}
      ∧ A ∪ D ⊆ (!) (ds_par (build_tree acyc_flow)) ` ({u. (w,u) ∈ (pstep (build_tree acyc_flow))⇧*} - {vcount})
      ∧ card {e ∈ A ∪ D. fst_all ! e = vcount ∨ snd_all ! e = vcount} ≤ 1
      ∧ pval_abstract bigM (ds_pot (build_tree acyc_flow) ! w) = (∑e∈A. cost_all ! e) - (∑e∈D. cost_all ! e)
      ∧ snd (ds_pot (build_tree acyc_flow) ! w) = (∑e∈A∩{0..<m}. cost_list ! e) - (∑e∈D∩{0..<m}. cost_list ! e)"
  using assms
proof (induction w rule: wf_induct_rule[OF wf_PS_conv])
  case (1 w)
  note [simp del] = NS.fst_exec_eq NS.snd_exec_eq
  note IH = "1.IH" and prem = "1.prems"
  let ?bt = "build_tree acyc_flow"
  let ?PS = "pstep ?bt"
  let ?anc = "λx. {u. (x,u) ∈ ?PS⇧*}"
  show ?case
  proof (cases "w = vcount")
    case True
    have novc: "⋀y. (vcount, y) ∉ ?PS" by (auto simp: pstep_def)
    have "?anc vcount ⊆ {vcount}"
    proof
      fix u assume "u ∈ ?anc vcount"
      hence "(vcount, u) ∈ ?PS⇧*" by simp
      thus "u ∈ {vcount}"
        by (cases rule: converse_rtranclE) (auto simp: novc)
    qed
    hence "?anc vcount = {vcount}" by auto
    hence ancv: "?anc w - {vcount} = {}" using True by simp
    have "ds_pot ?bt ! w = pval_zero" using True by (simp add: build_tree_root_pot)
    hence "pval_abstract bigM (ds_pot ?bt ! w) = 0" and "snd (ds_pot ?bt ! w) = 0"
      by (simp_all add: pval_abstract_def pval_zero_def)
    thus ?thesis using ancv by (intro exI[of _ "{}"] exI[of _ "{}"]) auto
  next
    case False
    hence wV: "w ∈ Vseen" using prem by simp
    have wlt: "w < vcount" and wseen: "ds_seen ?bt ! w" using wV by (auto simp: Vseen_def)
    define p where "p = ds_prnt ?bt ! w"
    define e where "e = ds_par ?bt ! w"
    have step: "(w, p) ∈ ?PS" using wlt wseen by (auto simp: pstep_def p_def)
    have stepc: "(p, w) ∈ ?PS¯" using step by simp
    have ancw: "?anc w - {vcount} = insert w (?anc p) - {vcount}"
      using anc_step[OF wV] by (simp add: p_def)
    have wneP: "w ∉ ?anc p" using w_notin_anc_parent[OF wV] by (simp add: p_def)
    have eendpts: "{fst_all ! e, snd_all ! e} = {w, p}"
      using tc_endpoints[OF wV] by (cases "ds_dir ?bt ! w") (auto simp: e_def p_def)
    show ?thesis
    proof (cases "p = vcount")
      case True  ― ‹root child: artificial edge, seed potential›
      have pV: "p ∈ insert vcount Vseen" using True by simp
      have ok: "comproot_edge_ok ?bt w"
        using build_tree_comproot_inv wlt wseen True by (simp add: comproot_inv_def p_def)
      have em: "m ≤ e" and pot_seed: "ds_pot ?bt ! w = (if art_dir w then pval_negM else pval_M)"
        using ok by (auto simp: comproot_edge_ok_def e_def)
      have knxt: "Kart = ds_nxt (build_tree acyc_flow)" by (simp add: Kart_def)
      have "e - m < ds_nxt (build_tree acyc_flow)" using ok by (simp add: comproot_edge_ok_def e_def)
      hence elt: "e < m + Kart" using em knxt by linarith
      have coste: "cost_all ! e = bigM" using em elt by (simp add: cost_all_art')
      have "vcount ∈ {fst_all ! e, snd_all ! e}" using eendpts True by simp
      hence rootinc: "fst_all ! e = vcount ∨ snd_all ! e = vcount" by auto
      have wanc: "w ∈ ?anc w - {vcount}"
      proof -
        have "(w, w) ∈ (pstep ?bt)⇧*" by simp
        thus ?thesis using wlt by simp
      qed
      have esub: "{e} ⊆ (!) (ds_par ?bt) ` (?anc w - {vcount})"
      proof -
        have "e = (!) (ds_par ?bt) w" by (simp add: e_def)
        thus ?thesis using wanc by blast
      qed
      have ele: "e ∈ {0..<m+Kart}" using em elt by simp
      have enotorig: "e ∉ {0..<m}" using em by simp
      show ?thesis
      proof (cases "art_dir w")
        case True
        have pa: "pval_abstract bigM (ds_pot ?bt ! w) = - bigM"
          using pot_seed True by (simp add: pval_abstract_def pval_negM_def)
        have sn: "snd (ds_pot ?bt ! w) = 0" using pot_seed True by (simp add: pval_negM_def)
        show ?thesis
        proof (rule exI[of _ "{}"], rule exI[of _ "{e}"], intro conjI)
          show "({}::nat set) ⊆ {0..<m+Kart}" by simp
          show "{e} ⊆ {0..<m+Kart}" using ele by simp
          show "({}::nat set) ∩ {e} = {}" by simp
          show "{} ∪ {e} ⊆ (!) (ds_par ?bt) ` (?anc w - {vcount})" using esub by simp
          have "{ee ∈ {} ∪ {e}. fst_all ! ee = vcount ∨ snd_all ! ee = vcount} = {e}"
            using rootinc by auto
          thus "card {ee ∈ {} ∪ {e}. fst_all ! ee = vcount ∨ snd_all ! ee = vcount} ≤ 1" by simp
          show "pval_abstract bigM (ds_pot ?bt ! w) = (∑ee∈{}. cost_all ! ee) - (∑ee∈{e}. cost_all ! ee)"
            using pa coste by simp
          show "snd (ds_pot ?bt ! w) = (∑ee∈{}∩{0..<m}. cost_list ! ee) - (∑ee∈{e}∩{0..<m}. cost_list ! ee)"
            using sn enotorig by simp
        qed
      next
        case False
        have pa: "pval_abstract bigM (ds_pot ?bt ! w) = bigM"
          using pot_seed False by (simp add: pval_abstract_def pval_M_def)
        have sn: "snd (ds_pot ?bt ! w) = 0" using pot_seed False by (simp add: pval_M_def)
        show ?thesis
        proof (rule exI[of _ "{e}"], rule exI[of _ "{}"], intro conjI)
          show "{e} ⊆ {0..<m+Kart}" using ele by simp
          show "({}::nat set) ⊆ {0..<m+Kart}" by simp
          show "{e} ∩ ({}::nat set) = {}" by simp
          show "{e} ∪ {} ⊆ (!) (ds_par ?bt) ` (?anc w - {vcount})" using esub by simp
          have "{ee ∈ {e} ∪ {}. fst_all ! ee = vcount ∨ snd_all ! ee = vcount} = {e}"
            using rootinc by auto
          thus "card {ee ∈ {e} ∪ {}. fst_all ! ee = vcount ∨ snd_all ! ee = vcount} ≤ 1" by simp
          show "pval_abstract bigM (ds_pot ?bt ! w) = (∑ee∈{e}. cost_all ! ee) - (∑ee∈{}. cost_all ! ee)"
            using pa coste by simp
          show "snd (ds_pot ?bt ! w) = (∑ee∈{e}∩{0..<m}. cost_list ! ee) - (∑ee∈{}∩{0..<m}. cost_list ! ee)"
            using sn enotorig by simp
        qed
      qed
    next
      case False  ― ‹interior: real parent edge, potential recursion›
      have plt: "p < vcount" and pseen: "ds_seen ?bt ! p"
        using build_tree_parent_in_seen[OF wlt wseen] False by (auto simp: p_def)
      have pV: "p ∈ insert vcount Vseen" using plt pseen by (simp add: Vseen_def)
      have pd: "ds_prnt ?bt ! w < vcount" using plt by (simp add: p_def)
      have IH: "∃A D. A ⊆ {0..<m+Kart} ∧ D ⊆ {0..<m+Kart} ∧ A ∩ D = {}
          ∧ A ∪ D ⊆ (!) (ds_par ?bt) ` (?anc p - {vcount})
          ∧ card {ee ∈ A ∪ D. fst_all ! ee = vcount ∨ snd_all ! ee = vcount} ≤ 1
          ∧ pval_abstract bigM (ds_pot ?bt ! p) = (∑ee∈A. cost_all ! ee) - (∑ee∈D. cost_all ! ee)
          ∧ snd (ds_pot ?bt ! p) = (∑ee∈A∩{0..<m}. cost_list ! ee) - (∑ee∈D∩{0..<m}. cost_list ! ee)"
        using IH[OF stepc pV] .
      then obtain A D where AD: "A ⊆ {0..<m+Kart}" "D ⊆ {0..<m+Kart}" "A ∩ D = {}"
          "A ∪ D ⊆ (!) (ds_par ?bt) ` (?anc p - {vcount})"
          "card {ee ∈ A ∪ D. fst_all ! ee = vcount ∨ snd_all ! ee = vcount} ≤ 1"
          "pval_abstract bigM (ds_pot ?bt ! p) = (∑ee∈A. cost_all ! ee) - (∑ee∈D. cost_all ! ee)"
          "snd (ds_pot ?bt ! p) = (∑ee∈A∩{0..<m}. cost_list ! ee) - (∑ee∈D∩{0..<m}. cost_list ! ee)" by blast
      have par_e: "e < m" using build_tree_par_edge[OF wlt wseen pd] by (simp add: e_def)
      have coste: "cost_all ! e = h (cost_list ! e)" using par_e by (simp add: cost_all_real)
      have pot_rec: "ds_pot ?bt ! w = pval_plus (ds_pot ?bt ! p) (M_0, if p = fst_list ! e then cost_list ! e else - cost_list ! e)"
        using build_tree_pot[OF wlt wseen pd] by (simp add: e_def p_def)
      define s where "s = (if p = fst_list ! e then cost_list ! e else - cost_list ! e)"
      have absw: "pval_abstract bigM (ds_pot ?bt ! w) = pval_abstract bigM (ds_pot ?bt ! p) + h s"
        unfolding s_def using pot_rec by (simp add: pval_plus_M0)
      have sndw: "snd (ds_pot ?bt ! w) = snd (ds_pot ?bt ! p) + s"
        unfolding s_def using pot_rec by (simp add: pval_plus_def)
      have efresh: "e ∉ A ∪ D"
      proof
        assume "e ∈ A ∪ D"
        then obtain u where uanc: "u ∈ ?anc p - {vcount}" and eu: "e = ds_par ?bt ! u" using AD(4) by auto
        have "u ∈ insert vcount Vseen" using anc_sub[of p u] uanc pV by simp
        hence uV: "u ∈ Vseen" using uanc by simp
        have "w = u" using par_inj[OF wV uV] eu by (simp add: e_def)
        thus False using uanc wneP by simp
      qed
      have enotroot: "fst_all ! e ≠ vcount ∧ snd_all ! e ≠ vcount"
        using eendpts wlt plt by auto
      have ele: "e ∈ {0..<m}" using par_e by simp
      have wanc: "w ∈ ?anc w - {vcount}"
      proof -
        have "(w, w) ∈ (pstep ?bt)⇧*" by simp
        thus ?thesis using wlt by simp
      qed
      have ancpw: "?anc p - {vcount} ⊆ ?anc w - {vcount}" using ancw by auto
      have esub: "insert e (A ∪ D) ⊆ (!) (ds_par ?bt) ` (?anc w - {vcount})"
      proof -
        have "e ∈ (!) (ds_par ?bt) ` (?anc w - {vcount})" using imageI[OF wanc] by (simp add: e_def)
        moreover have "A ∪ D ⊆ (!) (ds_par ?bt) ` (?anc w - {vcount})"
          using AD(4) ancpw by blast
        ultimately show ?thesis by simp
      qed
      show ?thesis
      proof (cases "s = cost_list ! e")
        case True  ― ‹edge oriented up: goes into A›
        let ?A = "insert e A" let ?D = D
        have g6: "pval_abstract bigM (ds_pot ?bt ! w) = (∑ee∈?A. cost_all ! ee) - (∑ee∈?D. cost_all ! ee)"
          using absw AD(6) True coste efresh AD(1) by (simp add: sum.insert_if finite_subset)
        have g7: "snd (ds_pot ?bt ! w) = (∑ee∈?A∩{0..<m}. cost_list ! ee) - (∑ee∈?D∩{0..<m}. cost_list ! ee)"
          using sndw AD(7) True efresh ele by (simp add: sum.insert_if Int_insert_left)
        have g5: "card {ee ∈ ?A ∪ ?D. fst_all ! ee = vcount ∨ snd_all ! ee = vcount} ≤ 1"
        proof -
          have "{ee ∈ ?A ∪ ?D. fst_all ! ee = vcount ∨ snd_all ! ee = vcount}
                = {ee ∈ A ∪ D. fst_all ! ee = vcount ∨ snd_all ! ee = vcount}"
            using enotroot by auto
          thus ?thesis using AD(5) by simp
        qed
        show ?thesis
        proof (rule exI[of _ ?A], rule exI[of _ ?D], intro conjI)
          show "?A ⊆ {0..<m+Kart}" using AD(1) ele by auto
          show "?D ⊆ {0..<m+Kart}" using AD(2) by simp
          show "?A ∩ ?D = {}" using AD(3) efresh by auto
          show "?A ∪ ?D ⊆ (!) (ds_par ?bt) ` (?anc w - {vcount})" using esub by simp
          show "card {ee ∈ ?A ∪ ?D. fst_all ! ee = vcount ∨ snd_all ! ee = vcount} ≤ 1" by (rule g5)
          show "pval_abstract bigM (ds_pot ?bt ! w) = (∑ee∈?A. cost_all ! ee) - (∑ee∈?D. cost_all ! ee)" by (rule g6)
          show "snd (ds_pot ?bt ! w) = (∑ee∈?A∩{0..<m}. cost_list ! ee) - (∑ee∈?D∩{0..<m}. cost_list ! ee)" by (rule g7)
        qed
      next
        case False
        have sD: "s = - cost_list ! e" using ‹s ≠ cost_list ! e› by (simp add: s_def split: if_splits)
        let ?A = A let ?D = "insert e D"
        have g6: "pval_abstract bigM (ds_pot ?bt ! w) = (∑ee∈?A. cost_all ! ee) - (∑ee∈?D. cost_all ! ee)"
          using absw AD(6) sD coste efresh AD(2) by (simp add: sum.insert_if finite_subset)
        have g7: "snd (ds_pot ?bt ! w) = (∑ee∈?A∩{0..<m}. cost_list ! ee) - (∑ee∈?D∩{0..<m}. cost_list ! ee)"
          using sndw AD(7) sD efresh ele by (simp add: sum.insert_if Int_insert_left)
        have g5: "card {ee ∈ ?A ∪ ?D. fst_all ! ee = vcount ∨ snd_all ! ee = vcount} ≤ 1"
        proof -
          have "{ee ∈ ?A ∪ ?D. fst_all ! ee = vcount ∨ snd_all ! ee = vcount}
                = {ee ∈ A ∪ D. fst_all ! ee = vcount ∨ snd_all ! ee = vcount}"
            using enotroot by auto
          thus ?thesis using AD(5) by simp
        qed
        show ?thesis
        proof (rule exI[of _ ?A], rule exI[of _ ?D], intro conjI)
          show "?A ⊆ {0..<m+Kart}" using AD(1) by simp
          show "?D ⊆ {0..<m+Kart}" using AD(2) ele by auto
          show "?A ∩ ?D = {}" using AD(3) efresh by auto
          show "?A ∪ ?D ⊆ (!) (ds_par ?bt) ` (?anc w - {vcount})" using esub by simp
          show "card {ee ∈ ?A ∪ ?D. fst_all ! ee = vcount ∨ snd_all ! ee = vcount} ≤ 1" by (rule g5)
          show "pval_abstract bigM (ds_pot ?bt ! w) = (∑ee∈?A. cost_all ! ee) - (∑ee∈?D. cost_all ! ee)" by (rule g6)
          show "snd (ds_pot ?bt ! w) = (∑ee∈?A∩{0..<m}. cost_list ! ee) - (∑ee∈?D∩{0..<m}. cost_list ! ee)" by (rule g7)
        qed
      qed
    qed
  qed
qed

lemma pot_value_ok:
  assumes "w ∈ insert vcount Vseen"
  shows "good_pot_val_c (ds_pot (build_tree acyc_flow) ! w) ∧ pv_invar (ds_pot (build_tree acyc_flow) ! w)"
proof -
  obtain A D where AD: "A ⊆ {0..<m+Kart}" "D ⊆ {0..<m+Kart}" "A ∩ D = {}"
      "A ∪ D ⊆ (!) (ds_par (build_tree acyc_flow)) ` ({u. (w,u) ∈ (pstep (build_tree acyc_flow))⇧*} - {vcount})"
      "card {e ∈ A ∪ D. fst_all ! e = vcount ∨ snd_all ! e = vcount} ≤ 1"
      "pval_abstract bigM (ds_pot (build_tree acyc_flow) ! w) = (∑e∈A. cost_all ! e) - (∑e∈D. cost_all ! e)"
      "snd (ds_pot (build_tree acyc_flow) ! w) = (∑e∈A∩{0..<m}. cost_list ! e) - (∑e∈D∩{0..<m}. cost_list ! e)"
    using pot_repr[OF assms] by blast
  have gp: "good_pot_val_c (ds_pot (build_tree acyc_flow) ! w)"
    unfolding good_pot_val_c_def using AD(1,2,5,6) by blast
  have "¦(∑e∈A∩{0..<m}. cost_list ! e) - (∑e∈D∩{0..<m}. cost_list ! e)¦
        ≤ ¦(∑e∈A∩{0..<m}. cost_list ! e)¦ + ¦(∑e∈D∩{0..<m}. cost_list ! e)¦" by simp
  also have "… ≤ (∑e∈A∩{0..<m}. ¦cost_list ! e¦) + (∑e∈D∩{0..<m}. ¦cost_list ! e¦)"
    by (intro add_mono sum_abs)
  also have "… ≤ (∑e∈{0..<m}. ¦cost_list ! e¦) + (∑e∈{0..<m}. ¦cost_list ! e¦)"
    by (intro add_mono sum_mono2) auto
  also have "… = 2 * sum_list (map abs cost_list)"
    by (simp add: sum_list_sum_nth atLeast0LessThan length_cost_list_m)
  finally have "¦snd (ds_pot (build_tree acyc_flow) ! w)¦ ≤ 2 * sum_list (map abs cost_list)"
    using AD(7) by simp
  hence "pv_invar (ds_pot (build_tree acyc_flow) ! w)" by (simp add: pv_invar_def)
  thus ?thesis using gp by simp
qed

lemma NS_verts: "NS.𝒱 = insert vcount Vseen"
proof -
  note [simp del] = NS.fst_exec_eq NS.snd_exec_eq
  have dvs: "NS.𝒱 = (⋃e∈{0..<m+Kart}. {fst_all!e, snd_all!e})"
    by (auto simp: dVs_def NS.make_pair_function)
  show ?thesis
  proof (rule set_eqI, rule iffI)
    fix x assume "x ∈ NS.𝒱"
    then obtain e where e: "e < m+Kart" and xe: "x = fst_all!e ∨ x = snd_all!e"
      using dvs by auto
    show "x ∈ insert vcount Vseen"
    proof (cases "e < m")
      case True
      have fe: "fst_all!e = fst_list!e" and se: "snd_all!e = snd_list!e"
        using True by (simp_all add: fst_all_real snd_all_real)
      have "fst_list!e ∈ set fst_list" using True by (metis length_fst_list_m nth_mem)
      moreover have "snd_list!e ∈ set snd_list" using True by (metis length_snd_list_m nth_mem)
      ultimately have "fst_list!e ∈ Vseen" "snd_list!e ∈ Vseen" using Vseen_eq_V V_orig_eq by auto
      thus ?thesis using xe fe se by auto
    next
      case False
      define k where "k = e - m"
      have kK: "k < Kart" using e False by (simp add: k_def)
      have em: "e = m + k" using False by (simp add: k_def)
      have "fst_all!e = ds_afst (build_tree acyc_flow)!k" using kK em by (simp add: fst_all_art)
      moreover have "snd_all!e = ds_asnd (build_tree acyc_flow)!k" using kK em by (simp add: snd_all_art)
      moreover have "ds_afst (build_tree acyc_flow)!k ∈ insert vcount Vseen
                     ∧ ds_asnd (build_tree acyc_flow)!k ∈ insert vcount Vseen"
        using build_tree_tail_sub kK by (simp add: tail_sub_def Kart_def seen_set_build_tree)
      ultimately show ?thesis using xe by auto
    qed
  next
    fix x assume "x ∈ insert vcount Vseen"
    hence "x = vcount ∨ x ∈ Vseen" by simp
    thus "x ∈ NS.𝒱"
    proof
      assume xv: "x = vcount"
      have k0: "0 < Kart" by (rule Kart_pos)
      have tok: "tail_edge_ok (build_tree acyc_flow) 0" using build_tree_tail_content k0 by (simp add: tail_content_def Kart_def)
      then obtain subj where subj: "subj < vcount"
        and af: "ds_afst (build_tree acyc_flow)!0 = (if art_dir subj then subj else vcount)"
        and as: "ds_asnd (build_tree acyc_flow)!0 = (if art_dir subj then vcount else subj)"
        by (auto simp: tail_edge_ok_def)
      have am: "fst_all!m = ds_afst (build_tree acyc_flow)!0" using k0 fst_all_art[of 0] by simp
      have sm: "snd_all!m = ds_asnd (build_tree acyc_flow)!0" using k0 snd_all_art[of 0] by simp
      have "vcount = fst_all!m ∨ vcount = snd_all!m"
        using af as am sm by (cases "art_dir subj") auto
      moreover have "m ∈ {0..<m+Kart}" using k0 by simp
      ultimately show ?thesis using dvs xv by auto
    next
      assume xvs: "x ∈ Vseen"
      have "∃e<m. x = fst_all!e ∨ x = snd_all!e"
      proof -
        from xvs have "x ∈ set fst_list ∨ x ∈ set snd_list" using Vseen_eq_V V_orig_eq by blast
        thus ?thesis
        proof
          assume "x ∈ set fst_list"
          then obtain e where e: "e < m" and "fst_list!e = x" using length_fst_list_m by (metis in_set_conv_nth)
          hence "x = fst_all!e" using fst_all_real[OF e] by simp
          thus ?thesis using e by auto
        next
          assume "x ∈ set snd_list"
          then obtain e where e: "e < m" and "snd_list!e = x" using length_snd_list_m by (metis in_set_conv_nth)
          hence "x = snd_all!e" using snd_all_real[OF e] by simp
          thus ?thesis using e by auto
        qed
      qed
      then obtain e where elt: "e < m" and xe: "x = fst_all!e ∨ x = snd_all!e" by blast
      have "e ∈ {0..<m+Kart}" using elt by simp
      thus ?thesis using dvs xe by auto
    qed
  qed
qed

lemma pot_valid_build_tree: "NS.pot_valid (ds_pot (build_tree acyc_flow))"
proof -
  have "∀v∈Varb. v < length (ds_pot (build_tree acyc_flow))"
    using len_pot_bt by (auto simp: Varb_def Vseen_def)
  moreover have "∀v∈NS.𝒱. good_pot_val_c (ds_pot (build_tree acyc_flow) ! v)
                          ∧ pv_invar (ds_pot (build_tree acyc_flow) ! v)"
  proof
    fix v assume "v ∈ NS.𝒱"
    hence "v ∈ insert vcount Vseen" using NS_verts by simp
    thus "good_pot_val_c (ds_pot (build_tree acyc_flow) ! v) ∧ pv_invar (ds_pot (build_tree acyc_flow) ! v)"
      by (rule pot_value_ok)
  qed
  ultimately show ?thesis by (simp add: NS.pot_valid_def)
qed

subsection ‹Towards the spanning-tree partition (obligation 9 / init_partition): the edge tags›

text ‹The parent edges are exactly the InTree-tagged edges. The easy inclusion (a parent edge is
      InTree) is here: an interior parent edge is a free real edge (build_tree_par_edge), a component
      root's parent edge is an artificial tree edge tagged InTree (build_tree_crext). Every edge is
      tagged with one of the three tags (state_total). The reverse inclusion (an InTree edge is a
      parent edge) is the free-edge coverage theorem, still owed.›

lemma state_par_InTree:
  assumes v: "v ∈ Vseen"
  shows "state_all ! (ds_par (build_tree acyc_flow) ! v) = InTree"
proof -
  let ?bt = "build_tree acyc_flow"
  have vlt: "v < vcount" and vseen: "ds_seen ?bt ! v" using v by (auto simp: Vseen_def)
  show ?thesis
  proof (cases "ds_prnt ?bt ! v = vcount")
    case False
    hence pd: "ds_prnt ?bt ! v < vcount"
      using build_tree_parent_in_seen[OF vlt vseen] by simp
    have pe: "ds_par ?bt ! v < m" and free: "is_free acyc_flow (ds_par ?bt ! v)"
      using build_tree_par_edge[OF vlt vseen pd] by simp_all
    have "edge_state acyc_flow ! (ds_par ?bt ! v) = InTree"
      using free is_free_iff[OF acyc_flow_nonneg acyc_flow_le_cap pe]
            edge_state_InTree_iff[OF acyc_flow_nonneg acyc_flow_le_cap pe] by simp
    thus ?thesis using pe by (simp add: state_all_real)
  next
    case True
    have ok: "cr_ext_ok ?bt v"
      using build_tree_crext vlt vseen True by (simp add: cr_ext_inv_def)
    have em: "m ≤ ds_par ?bt ! v"
      using build_tree_comproot_inv vlt vseen True by (simp add: comproot_inv_def comproot_edge_ok_def)
    obtain k where ek: "ds_par ?bt ! v = m + k" using em le_Suc_ex by (metis add.commute)
    have "ds_par ?bt ! v - m < ds_nxt ?bt"
      using build_tree_comproot_inv vlt vseen True by (simp add: comproot_inv_def comproot_edge_ok_def)
    hence kK: "k < Kart" using ek by (simp add: Kart_def)
    have "ds_aest ?bt ! k = InTree" using ok ek by (simp add: cr_ext_ok_def)
    thus ?thesis using ek kK by (simp add: state_all_art)
  qed
qed

lemma state_total:
  assumes e: "e < m + Kart"
  shows "state_all ! e = InL ∨ state_all ! e = InU ∨ state_all ! e = InTree"
proof (cases "e < m")
  case True
  have "state_all ! e = classify acyc_flow e" using True by (simp add: state_all_real edge_state_nth)
  thus ?thesis by (auto simp: classify_def)
next
  case False
  obtain k where ek: "e = m + k" using False le_Suc_ex by (metis add.commute not_less)
  have kK: "k < Kart" using e ek by simp
  have "ds_aest (build_tree acyc_flow) ! k = InTree ∨ ds_aest (build_tree acyc_flow) ! k = InU"
    using tail_edge_ok_build_tree[OF kK] by (auto simp: tail_edge_ok_def)
  thus ?thesis using ek kK by (auto simp: state_all_art)
qed

lemma T_sub_InTree:
  "(!) (ds_par (build_tree acyc_flow)) ` (NS.𝒱 - {vcount}) ⊆ {e ∈ {0..<m + Kart}. state_all ! e = InTree}"
proof
  fix x assume "x ∈ (!) (ds_par (build_tree acyc_flow)) ` (NS.𝒱 - {vcount})"
  then obtain v where vV: "v ∈ Vseen" and xv: "x = ds_par (build_tree acyc_flow) ! v"
    using NS_V_minus_root by auto
  have "state_all ! x = InTree" using xv state_par_InTree[OF vV] by simp
  moreover have "x ∈ {0..<m + Kart}"
    using xv NSinit_tree_corr vV NS_V_minus_root by auto
  ultimately show "x ∈ {e ∈ {0..<m + Kart}. state_all ! e = InTree}" by simp
qed

text ‹Four of the seven still-open @{locale network_simplex_init} obligations are the store-length
      invariants; they are immediate from the array sizes (flow_all / state_all have length m + Kart;
      the vertex-indexed arrays have length Suc vcount, and every vertex name is below vcount).›

lemma NSinit_flow_invar: "∀k∈{0..<m + Kart}. k < length flow_all" by (simp add: length_flow_all)
lemma NSinit_es_invar_len: "∀k∈{0..<m + Kart}. k < length state_all" by (simp add: length_state_all)
lemma NSinit_par_invar: "∀v∈Varb - {vcount}. v < length (ds_par (build_tree acyc_flow))"
  using build_tree_sized[of acyc_flow] by (auto simp: dfs_sized_def Varb_def Vseen_def)
lemma NSinit_dir_invar: "∀v∈Varb - {vcount}. v < length (ds_dir (build_tree acyc_flow))"
  using build_tree_sized[of acyc_flow] by (auto simp: dfs_sized_def Varb_def Vseen_def)




section ‹Total correctness of the solver›

text ‹The final statement about solve, phrased entirely in terms of the original network: the
      original_network sublocales, whose edge set is 0 ..< m, whose capacities and costs are read off
      capacity_list and cost_list, and whose balance is b_lookup. Neither the Kart artificial edges
      nor the big-M costs occur anywhere below; they are an internal device of the search, and the
      three verdicts speak only about the problem the caller posed.

      Optimum carries a flow on the m original edges that is a minimum-cost b_lookup-flow
      (original_network.is_Opt): feasible, and no feasible flow is cheaper.

      Infeasible certifies that the original network admits no b_lookup-flow at all, not merely that
      this run failed to find one.

      Neg_inf_cycle certifies neg_infty_cycle: a directed closed walk of original arcs, each of
      infinite capacity, whose total cost is negative, so the objective is unbounded below. This is
      the verdict of the acyclifier (acyc_flow_opt = None) and of an unbounded loop return alike;
      both are sound for the same reason.

      Note the asymmetry that makes the Infeasible case meaningful: it is a statement about every
      candidate flow, obtained because the artificial edges make the augmented network
      unconditionally feasible, so an augmented optimum that still loads an artificial edge is a
      proof of original infeasibility rather than a failure report.›

abbreviation neg_infty_cycle :: bool where
  "neg_infty_cycle ≡ 
  has_neg_infty_cycle original_network.make_pair 
         {0..<m} (λ e. cost_list ! e) 
          (λ e. if e < m then (if capacity_list ! e = - 1 then ∞ 
            else ereal (h (capacity_list ! e))) else ∞)"

subsection ‹Bridging the executable orchestrator to the verified loop›

text ‹solve runs NS.ns_loop_impl from the state assembled out of the concrete reader
      tree_st art_tree, whereas NSinit reasons about NS.ns_loop from the abstract Sarb. The two trees
      are the same record: Sarb is tree_st of art_tree once Vseen and Varb are unfolded. So the two
      starting states coincide, and the executable twin agrees with the specification loop on the
      domain, which NSinit.network_simplex_correct(1) supplies.›

lemma Sarb_tree_st: "Sarb = tree_st art_tree"
  by (simp add: Sarb_def tree_st_def Sprnt_def sprnt_st_def Sthrd_def sthrd_st_def
                Srvth_def srvth_st_def Vseen_def vseen_st_def Varb_def varb_st_def fun_eq_iff)



text ‹The loop always leaves notyetterm behind: it stops only at NS.ns_optimal or
      NS.ns_unbounded_upd, which set the flag to success resp. unbounded. This is what upgrades
      "not unbounded" to success in the two feasible branches.›

lemma ns_loop_terminates:
  assumes "NS.ns_loop_dom s"
  shows "return (NS.ns_loop s) = success ∨ return (NS.ns_loop s) = unbounded"
proof (induction rule: NS.ns_loop_induct[OF assms])
  case (1 s)
  note IH = this
  note dom = IH(1)
  show ?case
  proof (cases s rule: NS.ns_loop_cases)
    case 1 thus ?thesis by (simp add: NS.ns_loop_simps(1)[OF dom] NS.ns_optimal_def)
  next
    case 2 thus ?thesis by (simp add: NS.ns_loop_simps(2)[OF dom] NS.ns_unbounded_upd_def)
  next
    case 3 thus ?thesis using IH(2)[OF 3] by (simp add: NS.ns_loop_simps(3)[OF dom])
  next
    case 4 thus ?thesis using IH(3)[OF 4] by (simp add: NS.ns_loop_simps(4)[OF dom])
  qed
qed



subsection ‹The acyclifier's None verdict is an original negative infinite-capacity cycle›

text ‹make_acyclic_none_unbounded is reused verbatim. Its balance premise af_feasible b f0 is
      schematic in b, since af_feasible takes the balance as an argument rather than reading a locale
      parameter. So although flow_list is only assumed capacity-feasible (flow_nonneg, flow_le_cap)
      and is not a b_lookup-flow, we may instantiate b with flow_list's own balance and the premise
      becomes vacuous. No change to Acyclic_Flow is needed.›

lemma acyc_none_neg_cycle:
  assumes "acyc_flow_opt = None" shows neg_infty_cycle
proof -
  have vv: "vtx_invar ⦇vi_list = edged_vs_list, vi_pos = 0⦈"
    using distinct_vs_list by (simp add: vtx_invar_def edged_vs_list_def distinct_filter)
  have vab: "vtx_abstract ⦇vi_list = edged_vs_list, vi_pos = 0⦈ ⊆ original_network.𝒱"
    by (simp add: vtx_abstract_def V_orig_eq_edged)
  have ff: "length flow_list = m" using length_flow length_edges by simp
  have res: "make_acyclic flow_list = None" using assms by (simp add: acyc_flow_opt_def)
  have feas: "af_feasible (λv. - original_network.ex (h ∘ (!) flow_list) v) flow_list"
    by (rule af_feasibleI[OF af_cap_feasible_flow_list]) simp
  have ninf: "neg_inf_cycle" by (rule make_acyclic_none_unbounded[OF multigraph_inv_csr ff feas vv vab res])
  from ninf obtain D
    where cw: "closed_w (original_network.make_pair ` {0..<m}) (map original_network.make_pair D)"
      and cst: "foldr (λe. (+) (h (cost_list ! e))) D 0 < 0"
      and sD: "set D ⊆ {0..<m}"
      and inf: "∀e∈set D. (if e < m then if capacity_list ! e = - 1 then ∞ else ereal (h (capacity_list ! e)) else ∞) = PInfty"
    unfolding has_neg_infty_cycle_def by blast
  have foldeq: "foldr (λe. (+) (h (cost_list ! e))) D 0 = h (foldr (λe. (+) (cost_list ! e)) D 0)"
    by (induction D) (simp_all add: h_add)
  have c2: "foldr (λe. (+) (cost_list ! e)) D 0 < 0" using cst foldeq by simp
  show neg_infty_cycle unfolding has_neg_infty_cycle_def using cw c2 sD inf by blast
qed

subsection ‹An augmented ∞-cycle is already an original ∞-cycle›

text ‹Every artificial edge carries a finite capacity: tail_edge_ok_build_tree pins it to
      art_tree_cap subj or art_flow subj, both non-negative, hence never the -1 sentinel that decodes
      to an infinite capacity. So a cycle all of whose arcs have infinite capacity cannot touch the
      artificial part, and on the original part the endpoint, cost and capacity arrays agree by
      fst_all_real, snd_all_real, cap_all_real and cost_all_real. The artificial device therefore
      cannot manufacture an unboundedness verdict of its own.›

lemma cap_all_art_fin:
  assumes e1: "m ≤ e" and e2: "e < m + Kart" shows "cap_all ! e ≠ - 1"
proof -
  obtain k where ek: "e = m + k" using e1 by (metis le_Suc_ex)
  have kK: "k < Kart" using e2 ek by simp
  have "cap_all ! e = ds_acap (build_tree acyc_flow) ! k" using ek kK by (simp add: cap_all_art)
  moreover have "0 ≤ ds_acap (build_tree acyc_flow) ! k"
    using tail_edge_ok_build_tree[OF kK]
    by (auto simp: tail_edge_ok_def art_tree_cap_def art_flow_def)
  ultimately show ?thesis by simp
qed

lemma closed_w_restrict:
  assumes cw: "closed_w E p" and sub: "set p ⊆ E'"
  shows "closed_w E' p"
proof -
  from cw obtain u where u: "awalk E u p u" and len: "0 < length p" by (auto simp: closed_w_def)
  from u have cas: "cas u p u" by (simp add: awalk_def)
  obtain a b q where p: "p = (a, b) # q" using len by (cases p) auto
  have ua: "u = a" using cas p by simp
  have "(a, b) ∈ E'" using sub p by simp
  hence "u ∈ dVs E'" using ua by (auto simp: dVs_def)
  thus ?thesis using cas sub len by (auto simp: closed_w_def awalk_def)
qed

text ‹Note. The simplifier calls below are deliberately "simp only". Under the NS interpretation
      the endpoint bridge NS.fst_exec_eq instantiates to

        e : {0..<m+Kart} ==> fst_all ! e = (if e < m + Kart then fst_all ! e else ...)

      whose right-hand side contains its own left-hand side. As a [simp] rule it rewrites fst_all ! e
      to itself forever, so any plain simp on a goal mentioning fst_all ! e or snd_all ! e with
      e < m + Kart dischargeable diverges. The same holds for NS.snd_exec_eq. Declaring the two
      [simp del] removes the loop, but the fallout on existing proofs has not been measured, so the
      workaround here is local: unfold with simp only and discharge the conditions by hand.›

lemma make_pair_real:
  assumes e: "e < m" shows "NS.make_pair e = original_network.make_pair e"
proof -
  have lt: "e < m + Kart" using e by simp
  show ?thesis
    by (simp only: NS.make_pair_def original_network.make_pair_def if_P[OF lt] if_P[OF e]
                   fst_all_real[OF e] snd_all_real[OF e])
qed

lemma cost_fold_real:
  "set D ⊆ {0..<m} ⟹ foldr (λe. (+) (cost_all ! e)) D 0 = h (foldr (λe. (+) (cost_list ! e)) D 0)"
  by (induction D) (simp_all add: cost_all_real h_add)

lemma aug_neg_cycle_orig:
  assumes "has_neg_infty_cycle NS.make_pair {0..<m + Kart} ((!) cost_all)
             (λe. if e < m + Kart then if cap_all ! e = - 1 then ∞ else ereal (h (cap_all ! e)) else ∞)"
  shows neg_infty_cycle
proof -
  obtain D where cw: "closed_w (NS.make_pair ` {0..<m + Kart}) (map NS.make_pair D)"
    and cst: "foldr (λe. (+) (cost_all ! e)) D 0 < 0"
    and sD: "set D ⊆ {0..<m + Kart}"
    and inf: "∀e ∈ set D. (if e < m + Kart then if cap_all ! e = - 1 then ∞
                            else ereal (h (cap_all ! e)) else ∞) = PInfty"
    using assms unfolding has_neg_infty_cycle_def by blast
  have Dm: "e < m" if eD: "e ∈ set D" for e
  proof (rule ccontr)
    assume ne: "¬ e < m"
    have elt: "e < m + Kart" using sD eD by auto
    have "cap_all ! e = - 1" using bspec[OF inf eD] elt by (simp split: if_splits)
    thus False using cap_all_art_fin[OF _ elt] ne by simp
  qed
  hence sDm: "set D ⊆ {0..<m}" by auto
  have mapeq: "map NS.make_pair D = map original_network.make_pair D"
    using make_pair_real Dm by (simp add: map_eq_conv)
  have c1: "closed_w (original_network.make_pair ` {0..<m}) (map original_network.make_pair D)"
    by (rule closed_w_restrict[OF cw[unfolded mapeq]]) (use sDm in auto)
  have c2: "foldr (λe. (+) (cost_list ! e)) D 0 < 0" using cst cost_fold_real[OF sDm] by simp
  have c3: "∀e ∈ set D. (if e < m then if capacity_list ! e = - 1 then ∞
                          else ereal (h (capacity_list ! e)) else ∞) = PInfty"
  proof
    fix e assume eD: "e ∈ set D"
    have em: "e < m" by (rule Dm[OF eD])
    hence elt: "e < m + Kart" by simp
    have "cap_all ! e = - 1" using bspec[OF inf eD] elt by (simp split: if_splits)
    hence "capacity_list ! e = - 1" using em by (simp add: cap_all_real)
    thus "(if e < m then if capacity_list ! e = - 1 then ∞ else ereal (h (capacity_list ! e)) else ∞) = PInfty"
      using em by simp
  qed
  show neg_infty_cycle using c1 c2 sDm c3 unfolding has_neg_infty_cycle_def by blast
qed

subsection ‹The unbounded verdict›



subsection ‹The big-M transfer ∗‹(still owed)››

text ‹The two feasible verdicts both rest on transferring the augmented optimum
      NSinit.network_simplex_correct(3) back to the original network. This is the classical big-M
      argument, and it is the only part of solve_correct not yet discharged.

      aug_opt_zero_art_orig_opt: if the augmented optimum loads no artificial edge it restricts to an
      original b_lookup-flow, and it is optimal there because every original b_lookup-flow extends to
      an augmented one of equal cost (put 0 on the artificial edges, which is feasible at the root
      because b_lookup vcount = 0). This direction needs no bound on bigM.

      aug_opt_nonzero_art_infeasible: the converse, and the hard one. Suppose an original
      b_lookup-flow f existed and extend it by 0 to an augmented f'. Then g optimal gives
      C_aug g <= C_aug f' = C_orig f, and C_aug g = C_orig g + bigM * t where t is the total
      artificial flow. To contradict t > 0 one needs a lower bound on C_orig g in terms of C_orig f
      and t, i.e.

        C_orig f - C_orig g <= t * sum_list (map abs cost_list).

      Note what this is and is not. Restricted to the original edges g is a b'-flow for a balance b'
      that differs from b only at the artificial endpoints, with total deviation at most 2*t; the
      displayed bound is therefore a *sensitivity* (Lipschitz) statement about the minimum-cost
      function as the balance is perturbed, not a statement about any single path or cycle. It has to
      be proved by decomposing f - g (restricted to the original edges) into paths and cycles, the
      paths carrying at most t units in total; flowcycle_decomposition in Flow_Theory/Decomposition.thy
      is the intended starting point.

      Two traps to record, both of which cost a wrong sketch here already.

      First, the bound must be on the *rate*, not the total. Flows are real-valued, so t can be
      arbitrarily small and then bigM * t is small too; no bound of the form "bigM exceeds any
      achievable original cost" closes the argument.

      Second, a per-cycle argument does not work. Decomposing f' - g into residual cycles of g gives
      each cycle a non-negative cost, since g is optimal. But every artificial edge is incident to the
      root, so a *simple* residual cycle that touches the root uses exactly two artificial arcs; if one
      is traversed forwards and the other backwards their bigM contributions cancel, and the cycle's
      non-negative cost yields no contradiction however large bigM is. The cancellation is why the
      argument has to go through the aggregate sensitivity bound above.

      Both lemmas are stated on the abstract flow g of the augmented network; the theorem below feeds
      them NS.ns_flow_of (NS.ns_loop NSinit.init_state) and the artificial-edge test that solve
      performs.›

text ‹The loop carries its invariant to the terminal state, so the returned flow array is still long
      enough to be truncated at m. Only the two recursive branches do any work: the terminal ones just
      set the return flag, and ns_invar does not mention that field.

      The simp del below is not optional. Under the NS interpretation NS.fst_exec_eq and
      NS.snd_exec_eq are [simp] rules whose right-hand side contains their own left-hand side (see the
      note further down), and unfolding ns_invar_tree_def exposes fst_all ! ... , at which point a
      plain simp diverges.›

lemma ns_invar_ret: "NS.ns_invar (s⦇return := r⦈) = NS.ns_invar s"
  by (simp del: NS.fst_exec_eq NS.snd_exec_eq
           add: NS.ns_invar_def NS.ns_invar_impl_def NS.ns_invar_bflow_def NS.ns_invar_partition_def
                NS.ns_invar_flow_fits_def NS.ns_invar_pot_fits_def NS.ns_invar_strict_def
                NS.ns_invar_tree_def NS.ns_invar_selfloop_def NS.ns_L_of_def NS.ns_U_of_def
                NS.par_edge_def NS.par_up_def NS.par_vx_def)

lemma ns_loop_invar:
  assumes dom: "NS.ns_loop_dom s"
  shows "NS.ns_invar s ⟹ NS.ns_invar (NS.ns_loop s)"
proof (induction rule: NS.ns_loop_induct[OF dom])
  case (1 s)
  note IH = this
  show ?case
  proof (cases s rule: NS.ns_loop_cases)
    case 1
    show ?thesis using IH(4)
      by (simp add: NS.ns_loop_simps(1)[OF IH(1) 1] NS.ns_optimal_def ns_invar_ret)
  next
    case 2
    show ?thesis using IH(4)
      by (simp add: NS.ns_loop_simps(2)[OF IH(1) 2] NS.ns_unbounded_upd_def ns_invar_ret)
  next
    case 3
    show ?thesis using IH(2)[OF 3 NS.ns_flip_preservation(1)[OF IH(4) 3]]
      by (simp add: NS.ns_loop_simps(3)[OF IH(1) 3])
  next
    case 4
    show ?thesis using IH(3)[OF 4 NS.ns_pivot_preservation(1)[OF IH(4) 4]]
      by (simp add: NS.ns_loop_simps(4)[OF IH(1) 4])
  qed
qed



text ‹Supporting facts for the transfer between the augmented and original networks. They all rest on
      the same two observations: on the original edges 0 ..< m the augmented arrays coincide with the
      input lists (fst_all_real, snd_all_real, cap_all_real, cost_all_real), and a flow that is zero on
      the artificial edges m ..< m + Kart contributes nothing there. Several proofs carry
      "note [simp del] = NS.fst_exec_eq NS.snd_exec_eq" because those two rewrite fst_all ! e /
      snd_all ! e to themselves under the NS interpretation (see the note further down).›

lemma delta_plus_orig: "original_network.delta_plus v = NS.delta_plus v ∩ {0..<m}"
  and delta_minus_orig: "original_network.delta_minus v = NS.delta_minus v ∩ {0..<m}"
  by (auto simp del: NS.fst_exec_eq NS.snd_exec_eq
           simp add: original_network.delta_plus_def NS.delta_plus_def
                     original_network.delta_minus_def NS.delta_minus_def fst_all_real snd_all_real)

lemma delta_fin: "finite (NS.delta_plus v)" "finite (NS.delta_minus v)"
  by (auto simp del: NS.fst_exec_eq NS.snd_exec_eq simp add: NS.delta_plus_def NS.delta_minus_def)

text ‹For a flow that vanishes on the artificial edges the augmented and original excesses agree at
      every vertex, because the delta sets differ only by artificial edges, which carry no flow.›

lemma ex_agree:
  assumes z: "⋀k. m ≤ k ⟹ k < m + Kart ⟹ g k = 0"
  shows "NS.ex g v = original_network.ex g v"
proof -
  have sub: "NS.delta_plus v ⊆ {0..<m + Kart}"
    by (auto simp del: NS.fst_exec_eq NS.snd_exec_eq simp add: NS.delta_plus_def)
  have step: "(∑e ∈ NS.delta_plus v. g e) = (∑e ∈ NS.delta_plus v ∩ {0..<m}. g e)"
  proof (rule sum.mono_neutral_right)
    show "finite (NS.delta_plus v)" by (rule delta_fin)
    show "NS.delta_plus v ∩ {0..<m} ⊆ NS.delta_plus v" by auto
    show "∀e ∈ NS.delta_plus v - NS.delta_plus v ∩ {0..<m}. g e = 0"
    proof
      fix e assume e: "e ∈ NS.delta_plus v - NS.delta_plus v ∩ {0..<m}"
      hence "m ≤ e" "e < m + Kart" using sub by auto
      thus "g e = 0" by (rule z)
    qed
  qed
  hence P: "(∑e ∈ NS.delta_plus v. g e) = (∑e ∈ original_network.delta_plus v. g e)"
    by (simp add: delta_plus_orig)
  have sub2: "NS.delta_minus v ⊆ {0..<m + Kart}"
    by (auto simp del: NS.fst_exec_eq NS.snd_exec_eq simp add: NS.delta_minus_def)
  have "(∑e ∈ NS.delta_minus v. g e) = (∑e ∈ NS.delta_minus v ∩ {0..<m}. g e)"
  proof (rule sum.mono_neutral_right)
    show "finite (NS.delta_minus v)" by (rule delta_fin)
    show "NS.delta_minus v ∩ {0..<m} ⊆ NS.delta_minus v" by auto
    show "∀e ∈ NS.delta_minus v - NS.delta_minus v ∩ {0..<m}. g e = 0"
    proof
      fix e assume e: "e ∈ NS.delta_minus v - NS.delta_minus v ∩ {0..<m}"
      hence "m ≤ e" "e < m + Kart" using sub2 by auto
      thus "g e = 0" by (rule z)
    qed
  qed
  hence M: "(∑e ∈ NS.delta_minus v. g e) = (∑e ∈ original_network.delta_minus v. g e)"
    by (simp add: delta_minus_orig)
  show ?thesis unfolding NS.ex_def original_network.ex_def using P M by simp
qed

text ‹Likewise the augmented and original costs of such a flow agree.›

lemma cost_agree:
  assumes z: "⋀k. m ≤ k ⟹ k < m + Kart ⟹ g k = 0"
  shows "NS.𝒞 g = original_network.𝒞 g"
proof -
  have "NS.𝒞 g = (∑e ∈ {0..<m + Kart}. g e * cost_all ! e)" by (simp add: NS.𝒞_def)
  also have "… = (∑e ∈ {0..<m}. g e * cost_all ! e)"
  proof (rule sum.mono_neutral_right)
    show "finite {0..<m + Kart}" by simp
    show "{0..<m} ⊆ {0..<m + Kart}" by auto
    show "∀e ∈ {0..<m + Kart} - {0..<m}. g e * cost_all ! e = 0"
    proof
      fix e assume "e ∈ {0..<m + Kart} - {0..<m}"
      hence "m ≤ e" "e < m + Kart" by auto
      thus "g e * cost_all ! e = 0" using z by simp
    qed
  qed
  also have "… = (∑e ∈ {0..<m}. g e * h (cost_list ! e))" by (simp add: cost_all_real)
  also have "… = original_network.𝒞 g" by (simp add: original_network.𝒞_def)
  finally show ?thesis .
qed

text ‹An augmented flow restricts to an original flow: dropping the (unused) artificial edges keeps
      capacity-compliance and, by ex_agree at every original vertex, the balances.›

lemma isuflow_restrict:
  assumes "NS.isuflow g"
  shows "original_network.isuflow g"
proof (unfold original_network.isuflow_def, rule ballI)
  fix e assume e: "e ∈ {0..<m}"
  hence em: "e < m" by simp
  have cc: "cap_all ! e = capacity_list ! e" by (rule cap_all_real[OF em])
  from assms e have "ereal (g e) ≤ (if e < m + Kart then (if cap_all ! e = - 1 then ∞ else ereal (h (cap_all ! e))) else ∞) ∧ 0 ≤ g e"
    unfolding NS.isuflow_def by auto
  hence "ereal (g e) ≤ (if cap_all ! e = - 1 then ∞ else ereal (h (cap_all ! e))) ∧ 0 ≤ g e"
    using em by simp
  hence "ereal (g e) ≤ (if capacity_list ! e = - 1 then ∞ else ereal (h (capacity_list ! e))) ∧ 0 ≤ g e"
    unfolding cc .
  thus "ereal (g e) ≤ (if e < m then if capacity_list ! e = - 1 then ∞ else ereal (h (capacity_list ! e)) else ∞) ∧ 0 ≤ g e"
    using em by simp
qed

lemma bflow_restrict:
  assumes bf: "NS.isbflow g (λv. h (b_lookup v))"
    and z: "⋀k. m ≤ k ⟹ k < m + Kart ⟹ g k = 0"
  shows "original_network.isbflow g (λv. h (b_lookup v))"
proof (rule original_network.isbflowI)
  show "original_network.isuflow g" using bf isuflow_restrict by (auto simp: NS.isbflow_def)
  fix v assume "v ∈ original_network.𝒱"
  hence vin: "v ∈ NS.𝒱" using NS_verts Vseen_eq_V by auto
  have "- NS.ex g v = h (b_lookup v)" using bf vin by (auto simp: NS.isbflow_def)
  thus "- original_network.ex g v = h (b_lookup v)" using ex_agree[OF z, where v=v] by simp
qed

text ‹Conversely an original flow extends to an augmented one by putting zero on the artificial edges.
      Capacity holds (artificial capacities are non-negative), the balances hold at every original
      vertex, and at the root because b_lookup vcount = 0. The cost is unchanged.›

lemma orig_ex_ext:
  "original_network.ex (λe. if e < m then f e else 0) v = original_network.ex f v"
proof -
  have "⋀e. e ∈ original_network.delta_plus v ⟹ (if e < m then f e else 0) = f e"
    by (auto simp: original_network.delta_plus_def)
  moreover have "⋀e. e ∈ original_network.delta_minus v ⟹ (if e < m then f e else 0) = f e"
    by (auto simp: original_network.delta_minus_def)
  ultimately show ?thesis
    by (simp add: original_network.ex_def cong: sum.cong)
qed

lemma orig_ex_notin_V:
  assumes "v ∉ set vs_list"
  shows "original_network.ex f v = 0"
proof -
  have dp: "original_network.delta_plus v = {}"
    using assms fst_list_nth_vertex by (auto simp: original_network.delta_plus_def original_network.make_pair_def)
  have dm: "original_network.delta_minus v = {}"
    using assms snd_list_nth_vertex by (auto simp: original_network.delta_minus_def original_network.make_pair_def)
  show ?thesis by (simp add: original_network.ex_def dp dm)
qed

lemma isuflow_ext:
  assumes "original_network.isuflow f"
  shows "NS.isuflow (λe. if e < m then f e else 0)"
proof (unfold NS.isuflow_def, rule ballI)
  fix e assume e: "e ∈ {0..<m + Kart}"
  hence eK: "e < m + Kart" by simp
  show "ereal (if e < m then f e else 0) ≤ (if e < m + Kart then (if cap_all ! e = - 1 then ∞ else ereal (h (cap_all ! e))) else ∞) ∧ 0 ≤ (if e < m then f e else 0)"
  proof (cases "e < m")
    case True
    have cc: "cap_all ! e = capacity_list ! e" by (rule cap_all_real[OF True])
    have "ereal (f e) ≤ (if e < m then if capacity_list ! e = - 1 then ∞ else ereal (h (capacity_list ! e)) else ∞) ∧ 0 ≤ f e"
      using assms True unfolding original_network.isuflow_def by auto
    hence "ereal (f e) ≤ (if capacity_list ! e = - 1 then ∞ else ereal (h (capacity_list ! e))) ∧ 0 ≤ f e"
      using True by simp
    hence "ereal (f e) ≤ (if cap_all ! e = - 1 then ∞ else ereal (h (cap_all ! e))) ∧ 0 ≤ f e"
      unfolding cc .
    thus ?thesis using True eK by simp
  next
    case False
    have cap: "0 ≤ cap_all ! e ∨ cap_all ! e = - 1" using cap_all_nonneg[OF eK] .
    show ?thesis using False eK cap by (auto simp: zero_ereal_def)
  qed
qed

lemma bflow_ext:
  assumes bf: "original_network.isbflow f (λv. h (b_lookup v))"
  shows "NS.isbflow (λe. if e < m then f e else 0) (λv. h (b_lookup v))"
proof (rule NS.isbflowI)
  show "NS.isuflow (λe. if e < m then f e else 0)"
    using bf isuflow_ext by (auto simp: original_network.isbflow_def)
next
  fix v assume vV: "v ∈ NS.𝒱"
  have zz: "⋀k. m ≤ k ⟹ k < m + Kart ⟹ (λe. if e < m then f e else 0) k = 0" by simp
  have exeq: "NS.ex (λe. if e < m then f e else 0) v = original_network.ex f v"
    using ex_agree[OF zz, where v=v] orig_ex_ext[where v=v] by simp
  from vV have "v = vcount ∨ v ∈ Vseen" using NS_verts by auto
  thus "- NS.ex (λe. if e < m then f e else 0) v = h (b_lookup v)"
  proof
    assume "v = vcount"
    thus ?thesis using exeq orig_ex_notin_V[where v=vcount and f=f] vs_less_vcount b_lookup_root by auto
  next
    assume vvs: "v ∈ Vseen"
    hence "v ∈ original_network.𝒱" using Vseen_eq_V by simp
    hence "- original_network.ex f v = h (b_lookup v)" using bf by (auto simp: original_network.isbflow_def)
    thus ?thesis using exeq by simp
  qed
qed

lemma cost_ext: "NS.𝒞 (λe. if e < m then f e else 0) = original_network.𝒞 f"
proof -
  have z: "⋀k. m ≤ k ⟹ k < m + Kart ⟹ (λe. if e < m then f e else 0) k = 0" by simp
  have "NS.𝒞 (λe. if e < m then f e else 0) = original_network.𝒞 (λe. if e < m then f e else 0)"
    by (rule cost_agree[OF z])
  also have "… = original_network.𝒞 f"
    by (simp add: original_network.𝒞_def)
  finally show ?thesis .
qed

lemma aug_opt_zero_art_orig_opt:
  assumes opt: "NS.is_Opt (λv. h (b_lookup v)) g"
    and zero: "⋀k. m ≤ k ⟹ k < m + Kart ⟹ g k = 0"
  shows "original_network.is_Opt (λv. h (b_lookup v)) g"
proof (rule original_network.is_OptI)
  have gbf: "NS.isbflow g (λv. h (b_lookup v))" using opt by (simp add: NS.is_Opt_def)
  show orig_bf: "original_network.isbflow g (λv. h (b_lookup v))" by (rule bflow_restrict[OF gbf zero])
  fix f' assume f'bf: "original_network.isbflow f' (λv. h (b_lookup v))"
  let ?e = "λe. if e < m then f' e else 0"
  have "NS.isbflow ?e (λv. h (b_lookup v))" by (rule bflow_ext[OF f'bf])
  hence "NS.𝒞 g ≤ NS.𝒞 ?e" using opt by (simp add: NS.is_Opt_def)
  moreover have "NS.𝒞 g = original_network.𝒞 g" by (rule cost_agree[OF zero])
  moreover have "NS.𝒞 ?e = original_network.𝒞 f'" by (rule cost_ext)
  ultimately show "original_network.𝒞 f' ≥ original_network.𝒞 g" by simp
qed

text ‹Note the shape of the second premise. Stating it with a free k, as in

    and nz: "m <= k" "k < m + Kart" "g k ~= 0"

  exports k as a schematic ?k, so the premise becomes ?g ?k ~= 0: a schematic function applied to a
  schematic argument. Resolving that against a concrete fact is a flex-flex higher-order unification
  problem, and instantiating the lemma with OF then diverges. Binding k with an existential keeps the
  occurrence as ?g applied to a bound variable, which is a Miller pattern and unifies in one step.
  The sibling lemma above is safe for the same reason: its k is bound by the meta-quantifier.›

lemma cost_res_F: "NS.𝔠 (F (e::nat)) = cost_all ! e"
  using NS.ℭ_def[of "[F e]"] by simp
lemma cost_res_B: "NS.𝔠 (B (e::nat)) = - cost_all ! e"
  using NS.ℭ_def[of "[B e]"] by simp


lemma abs_cost_orig_bound:
  "(∑c ∈ ({F e |e. e < m} ∪ {B e |e. e < m}). ¦NS.𝔠 c¦) = 2 * h (sum_list (map abs cost_list))"
proof -
  have finF: "finite {F e |e. e < (m::nat)}" and finB: "finite {B e |e. e < (m::nat)}"
    by (auto simp: finite_image_set)
  have disj: "{F e |e. e < m} ∩ {B e |e. e < m} = {}" by auto
  have injF: "inj_on F {e. e < m}" and injB: "inj_on B {e. e < m}" by (auto simp: inj_on_def)
  have "(∑e ∈ {e. e < m}. ¦cost_all ! e¦) = h (sum_list (map abs cost_list))"
  proof -
    have "(∑e ∈ {e. e < m}. ¦cost_all ! e¦) = (∑e ∈ {0..<m}. h ¦cost_list ! e¦)"
      by (auto simp: cost_all_real h_abs atLeast0LessThan lessThan_def intro: sum.cong)
    also have "… = h (∑e ∈ {0..<m}. ¦cost_list ! e¦)" by (simp add: h_sum)
    also have "… = h (sum_list (map abs cost_list))"
      by (simp add: sum_list_sum_nth atLeast0LessThan length_cost_list_m)
    finally show ?thesis .
  qed
  moreover have "(∑c ∈ {F e |e. e < m}. ¦NS.𝔠 c¦) = (∑e ∈ {e. e < m}. ¦cost_all ! e¦)"
    by (simp add: setcompr_eq_image sum.reindex[OF injF] cost_res_F)
  moreover have "(∑c ∈ {B e |e. e < m}. ¦NS.𝔠 c¦) = (∑e ∈ {e. e < m}. ¦cost_all ! e¦)"
    by (simp add: setcompr_eq_image sum.reindex[OF injB] cost_res_B)
  ultimately show ?thesis
    by (subst sum.union_disjoint[OF finF finB disj]) simp
qed

text ‹A distinct residual arc list living in the augmented residual graph, containing at least one
      reverse artificial arc and no forward artificial arc, has strictly negative residual cost: each
      reverse artificial arc contributes -bigM, while the original arcs together contribute at most
      2 * sum_list (map abs cost_list) in absolute value, and bigM dominates that.›

lemma neg_res_cost:
  assumes dist: "distinct cs"
    and sub: "set cs ⊆ NS.𝔈"
    and noFart: "⋀k'. m ≤ k' ⟹ k' < m + Kart ⟹ F k' ∉ set cs"
    and Bk: "B k ∈ set cs" and k1: "m ≤ k" and k2: "k < m + Kart"
  shows "NS.ℭ cs < 0"
proof -
  define S where "S = set cs"
  define A where "A = {c ∈ S. ∃k'. m ≤ k' ∧ k' < m + Kart ∧ c = B k'}"
  define Oo where "Oo = S - A"
  have finS: "finite S" by (simp add: S_def)
  have SE: "S ⊆ NS.𝔈" using sub by (simp add: S_def)
  have Oo_orig: "Oo ⊆ {F e |e. e < m} ∪ {B e |e. e < m}"
  proof
    fix c assume c: "c ∈ Oo"
    hence cS: "c ∈ S" and cnA: "c ∉ A" by (auto simp: Oo_def)
    from cS SE have "c ∈ NS.𝔈" by auto
    then obtain d where d: "d < m + Kart" and cd: "c = F d ∨ c = B d" by (auto simp: NS.𝔈_def)
    show "c ∈ {F e |e. e < m} ∪ {B e |e. e < m}"
    proof (cases "d < m")
      case True thus ?thesis using cd by auto
    next
      case False
      hence dm: "m ≤ d" by simp
      from cd show ?thesis
      proof
        assume "c = F d" thus ?thesis using noFart[OF dm d] cS by (simp add: S_def)
      next
        assume cB: "c = B d"
        hence "c ∈ A" using dm d cS by (auto simp: A_def)
        thus ?thesis using cnA by simp
      qed
    qed
  qed
  have finA: "finite A" and finO: "finite Oo" using finS by (auto simp: A_def Oo_def)
  have Ainter: "A ∩ Oo = {}" by (auto simp: Oo_def)
  have SAO: "S = A ∪ Oo" by (auto simp: Oo_def A_def)
  have costA: "⋀c. c ∈ A ⟹ NS.𝔠 c = - bigM"
    by (auto simp: A_def cost_res_B cost_all_art')
  have "NS.ℭ cs = (∑c ∈ S. NS.𝔠 c)" by (simp add: NS.ℭ_def S_def)
  also have "… = (∑c ∈ A. NS.𝔠 c) + (∑c ∈ Oo. NS.𝔠 c)"
    using SAO Ainter finA finO by (simp add: sum.union_disjoint)
  finally have split: "NS.ℭ cs = (∑c ∈ A. NS.𝔠 c) + (∑c ∈ Oo. NS.𝔠 c)" .
  have Aval: "(∑c ∈ A. NS.𝔠 c) = - bigM * real (card A)"
    using costA by simp
  have Anz: "B k ∈ A" using Bk k1 k2 by (auto simp: A_def S_def)
  have cA: "card A ≠ 0" using finA Anz by auto
  have Alb: "(∑c ∈ A. NS.𝔠 c) ≤ - bigM"
  proof -
    have "(1::real) ≤ real (card A)" using cA by (simp add: Suc_leI)
    hence "bigM ≤ bigM * real (card A)" using bigM_pos by simp
    thus ?thesis using Aval by simp
  qed
  have "(∑c ∈ Oo. NS.𝔠 c) ≤ (∑c ∈ Oo. ¦NS.𝔠 c¦)" by (rule sum_mono) simp
  also have "… ≤ (∑c ∈ ({F e |e. e < m} ∪ {B e |e. e < m}). ¦NS.𝔠 c¦)"
    by (rule sum_mono2) (auto simp: Oo_orig finite_image_set)
  also have "… = 2 * h (sum_list (map abs cost_list))" by (rule abs_cost_orig_bound)
  finally have Oub: "(∑c ∈ Oo. NS.𝔠 c) ≤ 2 * h (sum_list (map abs cost_list))" .
  have "NS.ℭ cs ≤ - bigM + 2 * h (sum_list (map abs cost_list))"
    using split Alb Oub by simp
  also have "… < 0"
  proof -
    have "0 ≤ h (sum_list (map abs cost_list))" using sabs_nonneg by (rule h_nonneg)
    thus ?thesis using bigM_gt by linarith
  qed
  finally show ?thesis .
qed

lemma aug_opt_nonzero_art_infeasible:
  assumes opt: "NS.is_Opt (λv. h (b_lookup v)) g"
    and nz: "∃k. m ≤ k ∧ k < m + Kart ∧ g k ≠ 0"
  shows "∄ f. original_network.isbflow f (λv. h (b_lookup v))"
proof (rule notI)
  assume "∃f. original_network.isbflow f (λv. h (b_lookup v))"
  then obtain f where forig: "original_network.isbflow f (λv. h (b_lookup v))" by blast
  interpret rf: flow_network where fst = NS.fstv and snd = NS.sndv
      and create_edge = NS.create_edge_residual and ℰ = "NS.𝔈" and 𝗎 = "λ _. PInfty"
    using NS.make_pair NS.create_edge NS.E_not_empty NS.oedge_on_𝔈
    by (auto simp add: NS.finite_𝔈 NS.make_pair[OF refl refl] NS.create_edge
                       cost_flow_network_def flow_network_axioms_def flow_network_def multigraph_def)
  obtain k where k1: "m ≤ k" and k2: "k < m + Kart" and gk: "g k ≠ 0" using nz by blast
  define ef where "ef = (λe. if e < m then f e else 0)"
  define d where "d = NS.difference ef g"
  have gbf: "NS.isbflow g (λv. h (b_lookup v))" using opt by (simp add: NS.is_Opt_def)
  have guf: "NS.isuflow g" using gbf by (simp add: NS.isbflow_def)
  have efbf: "NS.isbflow ef (λv. h (b_lookup v))" using bflow_ext[OF forig] by (simp add: ef_def)
  have efuf: "NS.isuflow ef" using efbf by (simp add: NS.isbflow_def)
  have gnn: "⋀e. e < m + Kart ⟹ 0 ≤ g e"
    using guf by (auto simp: NS.isuflow_def)
  have gk0: "g k > 0" using gnn[OF k2] gk by simp
  ― ‹d is a non-negative residual circulation›
  have circ: "rf.is_circ d" using NS.diff_is_res_circ[OF gbf efbf] by (simp add: d_def)
  have nn: "rf.flow_non_neg d" using NS.diff_non_neg by (simp add: d_def rf.flow_non_neg_def)
  ― ‹B k is in the support: it reduces the loaded artificial edge›
  have efk: "ef k = 0" using k1 by (simp add: ef_def)
  have dBk: "d (B k) = g k" using efk gk0 by (simp add: d_def)
  have BkE: "B k ∈ NS.𝔈" using k1 k2 by (auto simp: NS.𝔈_def)
  have BkSupp: "B k ∈ rf.support d" using dBk gk0 BkE by (simp add: rf.support_def)
  have Abs_pos: "rf.Abs d > 0"
  proof -
    have "0 < d (B k)" using dBk gk0 by simp
    moreover have "rf.flow_non_neg d" by (rule nn)
    ultimately show ?thesis using BkE by (auto simp: rf.Abs_def rf.flow_non_neg_def
        intro: sum_pos2[of NS.𝔈 "B k" d] NS.finite_𝔈)
  qed
  have supp_ne: "rf.support d ≠ {}" using BkSupp by auto
  ― ‹no forward artificial arc is in the support: g ≥ 0 and ef is zero there›
  have noFart: "⋀k'. m ≤ k' ⟹ k' < m + Kart ⟹ F k' ∉ rf.support d"
  proof -
    fix k' assume a1: "m ≤ k'" and a2: "k' < m + Kart"
    have "ef k' = 0" using a1 by (simp add: ef_def)
    moreover have "0 ≤ g k'" using gnn[OF a2] .
    ultimately have "d (F k') = 0" by (simp add: d_def)
    thus "F k' ∉ rf.support d" by (simp add: rf.support_def)
  qed
  ― ‹decompose the circulation›
  obtain css ws where cw:
      "length css = length ws" "set css ≠ {}" "∀w∈set ws. 0 < w"
      "∀cs∈set css. rf.flowcycle d cs ∧ set cs ⊆ rf.support d ∧ distinct cs"
      "∀e∈NS.𝔈. d e = (∑i<length css. if e ∈ set (css ! i) then ws ! i else 0)"
    using rf.flowcycle_decomposition[OF nn Abs_pos circ supp_ne refl] by blast
  have "d (B k) = (∑i<length css. if B k ∈ set (css ! i) then ws ! i else 0)"
    using cw(5) BkE by blast
  hence pos: "(∑i<length css. if B k ∈ set (css ! i) then ws ! i else 0) > 0" using dBk gk0 by simp
  have "∃i<length css. B k ∈ set (css ! i)"
  proof (rule ccontr)
    assume "¬ (∃i<length css. B k ∈ set (css ! i))"
    hence "(∑i<length css. if B k ∈ set (css ! i) then ws ! i else 0) = 0"
      by (intro sum.neutral) auto
    thus False using pos by simp
  qed
  then obtain i where iL: "i < length css" and Bki: "B k ∈ set (css ! i)" by blast
  define cs where "cs = css ! i"
  have cyc: "rf.flowcycle d cs" and cssub: "set cs ⊆ rf.support d" and cdist: "distinct cs"
    using cw(4) iL by (auto simp: cs_def)
  ― ‹the selected cycle has negative residual cost (big-M dominates)›
  have csE: "set cs ⊆ NS.𝔈" using cssub by (auto simp: rf.support_def)
  have noF: "⋀k'. m ≤ k' ⟹ k' < m + Kart ⟹ F k' ∉ set cs"
    using noFart cssub by blast
  have Bk_cs: "B k ∈ set cs" using Bki by (simp add: cs_def)
  have neg: "NS.ℭ cs < 0" by (rule neg_res_cost[OF cdist csE noF Bk_cs k1 k2])
  ― ‹the cycle is an augmenting cycle of g: positive residual capacity, closed, distinct›
  have rcap_pos: "⋀e. e ∈ set cs ⟹ 0 < NS.rcap g e"
  proof -
    fix e assume "e ∈ set cs"
    hence "e ∈ rf.support d" using cssub by blast
    hence eE: "e ∈ NS.𝔈" and de: "0 < d e" by (auto simp: rf.support_def)
    show "0 < NS.rcap g e"
      using NS.pos_difference_pos_rcap[OF guf efuf eE] de by (simp add: d_def)
  qed
  have flowpath: "rf.flowpath d cs" and cs_ne: "cs ≠ []"
      and closed: "NS.fstv (hd cs) = NS.sndv (last cs)"
    using cyc by (auto simp: rf.flowcycle_def)
  have mpath: "rf.multigraph_path cs" using flowpath by (simp add: rf.flowpath_def)
  have prepath: "NS.prepath cs"
    using mpath cs_ne by (simp add: NS.prepath_def rf.multigraph_path_def NS.to_vertex_pair_fst_snd)
  have rcap_min: "0 < NS.Rcap g (set cs)"
  proof -
    have fin: "finite {NS.rcap g e |e. e ∈ set cs}" by simp
    have "∀x∈insert PInfty {NS.rcap g e |e. e ∈ set cs}. 0 < x"
      using rcap_pos by (auto simp: zero_less_iff_neq_zero)
    thus ?thesis by (simp add: NS.Rcap_def Min_gr_iff)
  qed
  have augpath: "NS.augpath g cs" using prepath rcap_min by (simp add: NS.augpath_def)
  have "NS.augcycle g cs"
    using neg augpath closed cdist csE by (simp add: NS.augcycle_def)
  thus False using NS.min_cost_flow_no_augcycle[OF opt] by blast
qed

text ‹original_network.is_Opt only reads the edges 0 ..< m, so truncating the augmented flow with
      take m does not change it.›

lemma is_Opt_take:
  assumes "m ≤ length f"
  shows "original_network.is_Opt (λv. h (b_lookup v)) (h ∘ nth (take m f)) = original_network.is_Opt (λv. h (b_lookup v)) (h ∘ nth f)"
proof
  have agree: "(h ∘ nth (take m f)) e = (h ∘ nth f) e" if "e ∈ {0..<m}" for e using that assms by (simp add: comp_def)
  assume "original_network.is_Opt (λv. h (b_lookup v)) (h ∘ nth (take m f))"
  thus "original_network.is_Opt (λv. h (b_lookup v)) (h ∘ nth f)"
    by (rule original_network.is_Opt_cong[rotated 2]) (use agree in auto)
next
  have agree: "(h ∘ nth f) e = (h ∘ nth (take m f)) e" if "e ∈ {0..<m}" for e using that assms by (simp add: comp_def)
  assume "original_network.is_Opt (λv. h (b_lookup v)) (h ∘ nth f)"
  thus "original_network.is_Opt (λv. h (b_lookup v)) (h ∘ nth (take m f))"
    by (rule original_network.is_Opt_cong[rotated 2]) (use agree in auto)
qed

subsection ‹Total correctness of solve›

text ‹Toward free-edge coverage (obligation 9, the reverse inclusion). Under acyclicity the acyclified
      flow has no closed pre-path of distinct free arcs (flow_no_free_cycle). The engine below packages
      that as: any closed walk of distinct free real edges is impossible. Coverage will feed it the
      cycle formed by an uncovered free edge together with the interior tree path between its endpoints.›

lemma is_free_af_arc_free:
  assumes "e < m" and "is_free acyc_flow e"
  shows "af_arc_free acyc_flow e"
proof -
  have "edge_state acyc_flow ! e = InTree" using assms(2) by (simp add: is_free_def)
  hence "0 < acyc_flow ! e ∧ (capacity_list ! e = - 1 ∨ acyc_flow ! e < capacity_list ! e)"
    using edge_state_InTree_iff[OF acyc_flow_nonneg acyc_flow_le_cap assms(1)] by simp
  thus ?thesis by (simp add: af_arc_free_def Let_def)
qed

lemma free_walk_no_cycle:
  assumes acyc: "original_network.acyclic_flow (h ∘ nth acyc_flow)"
    and ne: "C ≠ []"
    and free: "⋀a. a ∈ set C ⟹ original_network.oedge a < m ∧ is_free acyc_flow (original_network.oedge a)"
    and dist: "distinct (map original_network.oedge C)"
    and sub: "set C ⊆ original_network.𝔈"
    and pp: "original_network.prepath C"
    and closed: "original_network.fstv (hd C) = original_network.sndv (last C)"
  shows False
proof -
  have "af_arc_free acyc_flow (original_network.oedge a)" if "a ∈ set C" for a
    using free[OF that] is_free_af_arc_free by blast
  hence "∃C. original_network.prepath C ∧ (∀e∈set C. af_arc_free acyc_flow (original_network.oedge e))
       ∧ distinct (map original_network.oedge C)
       ∧ original_network.fstv (hd C) = original_network.sndv (last C) ∧ set C ⊆ original_network.𝔈"
    using pp dist closed sub by blast
  thus False using flow_no_free_cycle[OF acyc_flow_nonneg acyc_flow_le_cap acyc] by blast
qed

subsection ‹Free-edge coverage: the scan-completeness invariant of the DFS (obligation 9, core)›

text ‹scan_complete tracks that every free edge already scanned from a vertex has its far endpoint
      seen: for a stack frame, the edges before its cursor; for a finished (seen, off-stack) vertex,
      all of its edges. It needs no acyclicity — it is pure DFS scan structure — and is preserved by
      each build_dfs step. At the end (empty stack) it says every free neighbour of every vertex is
      seen, which is what lets an uncovered free edge be closed into a free cycle for the engine.›

definition out_scanned_seen :: "'n dfs_state ⇒ nat ⇒ nat ⇒ bool" where
  "out_scanned_seen s v k ⟷ (∀j. out_lo ! v ≤ j ∧ j < k ⟶ ds_seen s ! (snd_list ! (free_out_edges acyc_flow ! j)))"

definition in_scanned_seen :: "'n dfs_state ⇒ nat ⇒ nat ⇒ bool" where
  "in_scanned_seen s v k ⟷ (∀j. in_lo ! v ≤ j ∧ j < k ⟶ ds_seen s ! (fst_list ! (free_in_edges acyc_flow ! j)))"

definition scan_complete :: "'n dfs_state ⇒ bool" where
  "scan_complete s ⟷
     (∀(v,oc,ic)∈set (ds_stk s). out_scanned_seen s v oc ∧ in_scanned_seen s v ic)
   ∧ (∀v<vcount. ds_seen s ! v ∧ v ∉ fst ` set (ds_stk s) ⟶
        out_scanned_seen s v (free_out_hi acyc_flow ! v) ∧ in_scanned_seen s v (free_in_hi acyc_flow ! v))"

lemma out_scanned_seen_mono:
  "out_scanned_seen s v k ⟹ (⋀x. ds_seen s ! x ⟹ ds_seen s' ! x) ⟹ out_scanned_seen s' v k"
  by (auto simp: out_scanned_seen_def)
lemma in_scanned_seen_mono:
  "in_scanned_seen s v k ⟹ (⋀x. ds_seen s ! x ⟹ ds_seen s' ! x) ⟹ in_scanned_seen s' v k"
  by (auto simp: in_scanned_seen_def)

lemma discover_seen_eq: "ds_seen (dfs_discover s v w e) = (ds_seen s)[w := True]"
  by (simp add: dfs_discover_def Let_def)

lemma dfs_discover_seen_mono:
  assumes "ds_seen s ! x" shows "ds_seen (dfs_discover s v w e) ! x"
  unfolding discover_seen_eq using assms
  by (cases "w < length (ds_seen s)"; cases "x = w") (auto simp: nth_list_update list_update_beyond)

lemma dfs_discover_seen_w:
  assumes "w < length (ds_seen s)" shows "ds_seen (dfs_discover s v w e) ! w"
  unfolding discover_seen_eq using assms by (simp add: nth_list_update)

lemma bd_upd1_scan_complete:
  assumes wf: "dfs_wf s" and sc: "scan_complete s" and c: "bd_call1_conds acyc_flow s"
  shows "scan_complete (bd_upd1 acyc_flow s)"
proof -
  from c obtain v oc ic rest where stk: "ds_stk s = (v,oc,ic) # rest"
    and oclt: "oc < free_out_hi acyc_flow ! v"
    by (auto simp: bd_call1_conds_def split: list.splits prod.splits)
  have vlt: "v < vcount" and oclo: "out_lo ! v ≤ oc"
    using wf stk by (auto simp: dfs_wf_def)
  define e where "e = free_out_edges acyc_flow ! oc"
  define w where "w = snd_list ! e"
  have fst_e: "fst_list ! e = v" and free_e: "is_free acyc_flow e" and em: "e < m"
    using free_out_edge_fst[OF vlt oclo oclt] by (simp_all add: e_def)
  have wvc: "w < vcount" using em snd_list_nth_vertex[of e] vs_less_vcount by (simp add: w_def)
  have wlen: "w < length (ds_seen s)" using wvc wf by (simp add: dfs_wf_def)
  have s1: "s⦇ds_stk := (v, Suc oc, ic) # rest⦈ = s⦇ds_stk := (v, Suc oc, ic) # rest⦈" ..
  ― ‹the update›
  have upd: "bd_upd1 acyc_flow s = (if ds_seen s ! w then s⦇ds_stk := (v, Suc oc, ic) # rest⦈
                                    else dfs_discover (s⦇ds_stk := (v, Suc oc, ic) # rest⦈) v w e)"
    using stk by (simp add: bd_upd1_def e_def w_def Let_def)
  let ?res = "bd_upd1 acyc_flow s"
  have wseen_res: "ds_seen ?res ! w"
  proof (cases "ds_seen s ! w")
    case True thus ?thesis using upd by simp
  next
    case False
    have "ds_seen (dfs_discover (s⦇ds_stk := (v, Suc oc, ic) # rest⦈) v w e) ! w"
      using wlen by (simp add: dfs_discover_seen_w)
    thus ?thesis using upd False by simp
  qed
  have seen_mono: "⋀x. ds_seen s ! x ⟹ ds_seen ?res ! x"
  proof -
    fix x assume "ds_seen s ! x"
    show "ds_seen ?res ! x"
    proof (cases "ds_seen s ! w")
      case True thus ?thesis using upd ‹ds_seen s ! x› by simp
    next
      case False
      thus ?thesis using upd ‹ds_seen s ! x› by (simp add: dfs_discover_seen_mono)
    qed
  qed
  have stk_res: "ds_stk ?res = (if ds_seen s ! w then (v, Suc oc, ic) # rest
                                 else (w, out_lo ! w, in_lo ! w) # (v, Suc oc, ic) # rest)"
    using upd by (simp add: dfs_discover_def Let_def)
  have sndoc: "snd_list ! (free_out_edges acyc_flow ! oc) = w" by (simp add: e_def w_def)
  have vframe: "out_scanned_seen ?res v (Suc oc) ∧ in_scanned_seen ?res v ic"
  proof
    have base_out: "out_scanned_seen s v oc" and base_in: "in_scanned_seen s v ic"
      using sc stk by (auto simp: scan_complete_def)
    show "out_scanned_seen ?res v (Suc oc)"
      unfolding out_scanned_seen_def
    proof (intro allI impI)
      fix j assume j: "out_lo ! v ≤ j ∧ j < Suc oc"
      show "ds_seen ?res ! (snd_list ! (free_out_edges acyc_flow ! j))"
      proof (cases "j = oc")
        case True thus ?thesis using wseen_res sndoc by simp
      next
        case False
        hence "out_lo ! v ≤ j ∧ j < oc" using j by simp
        thus ?thesis using base_out seen_mono by (auto simp: out_scanned_seen_def)
      qed
    qed
    show "in_scanned_seen ?res v ic" using base_in seen_mono by (rule in_scanned_seen_mono)
  qed
  have fin_from_s: "u ∉ fst ` set (ds_stk ?res) ⟹ u ∉ fst ` set (ds_stk s)" for u
    using stk stk_res by (cases "ds_seen s ! w") auto
  have part1: "∀(a,b,cc)∈set (ds_stk ?res). out_scanned_seen ?res a b ∧ in_scanned_seen ?res a cc"
  proof (rule ballI)
    fix fr assume frm0: "fr ∈ set (ds_stk ?res)"
    obtain aa bb ccc where frx: "fr = (aa,bb,ccc)" by (cases fr)
    have frm: "(aa,bb,ccc) ∈ set (ds_stk ?res)" using frm0 frx by simp
    have rest_case: "(aa,bb,ccc) ∈ set rest ⟹ out_scanned_seen ?res aa bb ∧ in_scanned_seen ?res aa ccc"
    proof -
      assume "(aa,bb,ccc) ∈ set rest"
      hence "(aa,bb,ccc) ∈ set (ds_stk s)" using stk by simp
      hence "out_scanned_seen s aa bb ∧ in_scanned_seen s aa ccc" using sc by (auto simp: scan_complete_def)
      thus ?thesis using seen_mono by (auto intro: out_scanned_seen_mono in_scanned_seen_mono)
    qed
    have "out_scanned_seen ?res aa bb ∧ in_scanned_seen ?res aa ccc"
    proof (cases "ds_seen s ! w")
      case True
      hence "(aa,bb,ccc) = (v, Suc oc, ic) ∨ (aa,bb,ccc) ∈ set rest" using frm stk_res by auto
      thus ?thesis using vframe rest_case by auto
    next
      case False
      hence "(aa,bb,ccc) = (w, out_lo!w, in_lo!w) ∨ (aa,bb,ccc) = (v, Suc oc, ic) ∨ (aa,bb,ccc) ∈ set rest"
        using frm stk_res by auto
      thus ?thesis using vframe rest_case by (auto simp: out_scanned_seen_def in_scanned_seen_def)
    qed
    thus "case fr of (a,b,cc) ⇒ out_scanned_seen ?res a b ∧ in_scanned_seen ?res a cc" using frx by simp
  qed
  have part2: "∀u<vcount. ds_seen ?res ! u ∧ u ∉ fst ` set (ds_stk ?res) ⟶
                 out_scanned_seen ?res u (free_out_hi acyc_flow ! u) ∧ in_scanned_seen ?res u (free_in_hi acyc_flow ! u)"
  proof (intro allI impI, elim conjE)
    fix u assume ult: "u < vcount" and us1: "ds_seen ?res ! u" and us2: "u ∉ fst ` set (ds_stk ?res)"
    have useen_s: "ds_seen s ! u"
    proof (cases "ds_seen s ! w")
      case True
      have "?res = s⦇ds_stk := (v, Suc oc, ic) # rest⦈" using upd True by simp
      thus ?thesis using us1 by simp
    next
      case wF: False
      have unotw: "u ≠ w" using us2 stk_res wF by auto
      have rd: "?res = dfs_discover (s⦇ds_stk := (v, Suc oc, ic) # rest⦈) v w e" using upd wF by simp
      have "ds_seen ?res ! u = ds_seen s ! u"
        by (simp add: rd discover_seen_eq nth_list_update_neq[OF unotw[symmetric]])
      thus ?thesis using us1 by simp
    qed
    have uns: "u ∉ fst ` set (ds_stk s)" using us2 fin_from_s by blast
    have "out_scanned_seen s u (free_out_hi acyc_flow ! u) ∧ in_scanned_seen s u (free_in_hi acyc_flow ! u)"
      using sc ult useen_s uns by (simp add: scan_complete_def)
    thus "out_scanned_seen ?res u (free_out_hi acyc_flow ! u) ∧ in_scanned_seen ?res u (free_in_hi acyc_flow ! u)"
      using seen_mono by (auto intro: out_scanned_seen_mono in_scanned_seen_mono)
  qed
  show ?thesis unfolding scan_complete_def using part1 part2 by blast
qed

lemma bd_upd2_scan_complete:
  assumes wf: "dfs_wf s" and sc: "scan_complete s" and c: "bd_call2_conds acyc_flow s"
  shows "scan_complete (bd_upd2 acyc_flow s)"
proof -
  from c obtain v oc ic rest where stk: "ds_stk s = (v,oc,ic) # rest"
    and iclt: "ic < free_in_hi acyc_flow ! v"
    by (auto simp: bd_call2_conds_def split: list.splits prod.splits)
  have vlt: "v < vcount" and iclo: "in_lo ! v ≤ ic"
    using wf stk by (auto simp: dfs_wf_def)
  define e where "e = free_in_edges acyc_flow ! ic"
  define w where "w = fst_list ! e"
  have snd_e: "snd_list ! e = v" and free_e: "is_free acyc_flow e" and em: "e < m"
    using free_in_edge_snd[OF vlt iclo iclt] by (simp_all add: e_def)
  have wvc: "w < vcount" using em fst_list_nth_vertex[of e] vs_less_vcount by (simp add: w_def)
  have wlen: "w < length (ds_seen s)" using wvc wf by (simp add: dfs_wf_def)
  have s1: "s⦇ds_stk := (v, oc, Suc ic) # rest⦈ = s⦇ds_stk := (v, oc, Suc ic) # rest⦈" ..
  ― ‹the update›
  have upd: "bd_upd2 acyc_flow s = (if ds_seen s ! w then s⦇ds_stk := (v, oc, Suc ic) # rest⦈
                                    else dfs_discover (s⦇ds_stk := (v, oc, Suc ic) # rest⦈) v w e)"
    using stk by (simp add: bd_upd2_def e_def w_def Let_def)
  let ?res = "bd_upd2 acyc_flow s"
  have wseen_res: "ds_seen ?res ! w"
  proof (cases "ds_seen s ! w")
    case True thus ?thesis using upd by simp
  next
    case False
    have "ds_seen (dfs_discover (s⦇ds_stk := (v, oc, Suc ic) # rest⦈) v w e) ! w"
      using wlen by (simp add: dfs_discover_seen_w)
    thus ?thesis using upd False by simp
  qed
  have seen_mono: "⋀x. ds_seen s ! x ⟹ ds_seen ?res ! x"
  proof -
    fix x assume "ds_seen s ! x"
    show "ds_seen ?res ! x"
    proof (cases "ds_seen s ! w")
      case True thus ?thesis using upd ‹ds_seen s ! x› by simp
    next
      case False
      thus ?thesis using upd ‹ds_seen s ! x› by (simp add: dfs_discover_seen_mono)
    qed
  qed
  have stk_res: "ds_stk ?res = (if ds_seen s ! w then (v, oc, Suc ic) # rest
                                 else (w, out_lo ! w, in_lo ! w) # (v, oc, Suc ic) # rest)"
    using upd by (simp add: dfs_discover_def Let_def)
  have sndoc: "fst_list ! (free_in_edges acyc_flow ! ic) = w" by (simp add: e_def w_def)
  have vframe: "out_scanned_seen ?res v oc ∧ in_scanned_seen ?res v (Suc ic)"
  proof
    have base_out: "out_scanned_seen s v oc" and base_in: "in_scanned_seen s v ic"
      using sc stk by (auto simp: scan_complete_def)
    show "out_scanned_seen ?res v oc" using base_out seen_mono by (rule out_scanned_seen_mono)
    show "in_scanned_seen ?res v (Suc ic)"
      unfolding in_scanned_seen_def
    proof (intro allI impI)
      fix j assume j: "in_lo ! v ≤ j ∧ j < Suc ic"
      show "ds_seen ?res ! (fst_list ! (free_in_edges acyc_flow ! j))"
      proof (cases "j = ic")
        case True thus ?thesis using wseen_res sndoc by simp
      next
        case False
        hence "in_lo ! v ≤ j ∧ j < ic" using j by simp
        thus ?thesis using base_in seen_mono by (auto simp: in_scanned_seen_def)
      qed
    qed
  qed
  have fin_from_s: "u ∉ fst ` set (ds_stk ?res) ⟹ u ∉ fst ` set (ds_stk s)" for u
    using stk stk_res by (cases "ds_seen s ! w") auto
  have part1: "∀(a,b,cc)∈set (ds_stk ?res). out_scanned_seen ?res a b ∧ in_scanned_seen ?res a cc"
  proof (rule ballI)
    fix fr assume frm0: "fr ∈ set (ds_stk ?res)"
    obtain aa bb ccc where frx: "fr = (aa,bb,ccc)" by (cases fr)
    have frm: "(aa,bb,ccc) ∈ set (ds_stk ?res)" using frm0 frx by simp
    have rest_case: "(aa,bb,ccc) ∈ set rest ⟹ out_scanned_seen ?res aa bb ∧ in_scanned_seen ?res aa ccc"
    proof -
      assume "(aa,bb,ccc) ∈ set rest"
      hence "(aa,bb,ccc) ∈ set (ds_stk s)" using stk by simp
      hence "out_scanned_seen s aa bb ∧ in_scanned_seen s aa ccc" using sc by (auto simp: scan_complete_def)
      thus ?thesis using seen_mono by (auto intro: out_scanned_seen_mono in_scanned_seen_mono)
    qed
    have "out_scanned_seen ?res aa bb ∧ in_scanned_seen ?res aa ccc"
    proof (cases "ds_seen s ! w")
      case True
      hence "(aa,bb,ccc) = (v, oc, Suc ic) ∨ (aa,bb,ccc) ∈ set rest" using frm stk_res by auto
      thus ?thesis using vframe rest_case by auto
    next
      case False
      hence "(aa,bb,ccc) = (w, out_lo!w, in_lo!w) ∨ (aa,bb,ccc) = (v, oc, Suc ic) ∨ (aa,bb,ccc) ∈ set rest"
        using frm stk_res by auto
      thus ?thesis using vframe rest_case by (auto simp: out_scanned_seen_def in_scanned_seen_def)
    qed
    thus "case fr of (a,b,cc) ⇒ out_scanned_seen ?res a b ∧ in_scanned_seen ?res a cc" using frx by simp
  qed
  have part2: "∀u<vcount. ds_seen ?res ! u ∧ u ∉ fst ` set (ds_stk ?res) ⟶
                 out_scanned_seen ?res u (free_out_hi acyc_flow ! u) ∧ in_scanned_seen ?res u (free_in_hi acyc_flow ! u)"
  proof (intro allI impI, elim conjE)
    fix u assume ult: "u < vcount" and us1: "ds_seen ?res ! u" and us2: "u ∉ fst ` set (ds_stk ?res)"
    have useen_s: "ds_seen s ! u"
    proof (cases "ds_seen s ! w")
      case True
      have "?res = s⦇ds_stk := (v, oc, Suc ic) # rest⦈" using upd True by simp
      thus ?thesis using us1 by simp
    next
      case wF: False
      have unotw: "u ≠ w" using us2 stk_res wF by auto
      have rd: "?res = dfs_discover (s⦇ds_stk := (v, oc, Suc ic) # rest⦈) v w e" using upd wF by simp
      have "ds_seen ?res ! u = ds_seen s ! u"
        by (simp add: rd discover_seen_eq nth_list_update_neq[OF unotw[symmetric]])
      thus ?thesis using us1 by simp
    qed
    have uns: "u ∉ fst ` set (ds_stk s)" using us2 fin_from_s by blast
    have "out_scanned_seen s u (free_out_hi acyc_flow ! u) ∧ in_scanned_seen s u (free_in_hi acyc_flow ! u)"
      using sc ult useen_s uns by (simp add: scan_complete_def)
    thus "out_scanned_seen ?res u (free_out_hi acyc_flow ! u) ∧ in_scanned_seen ?res u (free_in_hi acyc_flow ! u)"
      using seen_mono by (auto intro: out_scanned_seen_mono in_scanned_seen_mono)
  qed
  show ?thesis unfolding scan_complete_def using part1 part2 by blast
qed

lemma dfs_finish_seen: "ds_seen (dfs_finish s v rest) = ds_seen s"
  by (simp add: dfs_finish_def Let_def)
lemma dfs_finish_stk: "ds_stk (dfs_finish s v rest) = rest"
  by (simp add: dfs_finish_def Let_def)

lemma bd_upd3_scan_complete:
  assumes wf: "dfs_wf s" and sc: "scan_complete s" and c: "bd_call3_conds acyc_flow s"
  shows "scan_complete (bd_upd3 s)"
proof -
  from c obtain v oc ic rest where stk: "ds_stk s = (v,oc,ic) # rest"
    and ocge: "¬ oc < free_out_hi acyc_flow ! v" and icge: "¬ ic < free_in_hi acyc_flow ! v"
    by (auto simp: bd_call3_conds_def split: list.splits prod.splits)
  have vlt: "v < vcount" using wf stk by (auto simp: dfs_wf_def)
  have res: "bd_upd3 s = dfs_finish s v rest" using stk by (simp add: bd_upd3_def)
  have seen_eq: "⋀x. ds_seen (bd_upd3 s) ! x = ds_seen s ! x" by (simp add: res dfs_finish_seen)
  have stk_eq: "ds_stk (bd_upd3 s) = rest" by (simp add: res dfs_finish_stk)
  ― ‹v's frame gives its finished coverage since its cursors are at/past the high marks›
  have vfin: "out_scanned_seen (bd_upd3 s) v (free_out_hi acyc_flow ! v)
              ∧ in_scanned_seen (bd_upd3 s) v (free_in_hi acyc_flow ! v)"
  proof
    have "out_scanned_seen s v oc ∧ in_scanned_seen s v ic" using sc stk by (auto simp: scan_complete_def)
    hence bo: "out_scanned_seen s v oc" and bi: "in_scanned_seen s v ic" by simp_all
    show "out_scanned_seen (bd_upd3 s) v (free_out_hi acyc_flow ! v)"
      unfolding out_scanned_seen_def using bo ocge seen_eq by (auto simp: out_scanned_seen_def)
    show "in_scanned_seen (bd_upd3 s) v (free_in_hi acyc_flow ! v)"
      unfolding in_scanned_seen_def using bi icge seen_eq by (auto simp: in_scanned_seen_def)
  qed
  show ?thesis
    unfolding scan_complete_def
  proof (intro conjI)
    show "∀(a,b,cc)∈set (ds_stk (bd_upd3 s)). out_scanned_seen (bd_upd3 s) a b ∧ in_scanned_seen (bd_upd3 s) a cc"
    proof (rule ballI)
      fix fr assume "fr ∈ set (ds_stk (bd_upd3 s))"
      hence frs: "fr ∈ set (ds_stk s)" using stk_eq stk by simp
      obtain a b cc where fr: "fr = (a,b,cc)" by (cases fr)
      have "out_scanned_seen s a b ∧ in_scanned_seen s a cc" using sc frs fr by (auto simp: scan_complete_def)
      hence "out_scanned_seen (bd_upd3 s) a b ∧ in_scanned_seen (bd_upd3 s) a cc"
        using seen_eq by (auto simp: out_scanned_seen_def in_scanned_seen_def)
      thus "case fr of (a,b,cc) ⇒ out_scanned_seen (bd_upd3 s) a b ∧ in_scanned_seen (bd_upd3 s) a cc"
        using fr by simp
    qed
  next
    show "∀u<vcount. ds_seen (bd_upd3 s) ! u ∧ u ∉ fst ` set (ds_stk (bd_upd3 s)) ⟶
             out_scanned_seen (bd_upd3 s) u (free_out_hi acyc_flow ! u) ∧ in_scanned_seen (bd_upd3 s) u (free_in_hi acyc_flow ! u)"
    proof (intro allI impI, elim conjE)
      fix u assume ult: "u < vcount" and us1: "ds_seen (bd_upd3 s) ! u" and us2: "u ∉ fst ` set (ds_stk (bd_upd3 s))"
      show "out_scanned_seen (bd_upd3 s) u (free_out_hi acyc_flow ! u) ∧ in_scanned_seen (bd_upd3 s) u (free_in_hi acyc_flow ! u)"
      proof (cases "u = v")
        case True thus ?thesis using vfin by simp
      next
        case False
        have "u ∉ fst ` set (ds_stk s)" using us2 stk_eq stk False by auto
        moreover have "ds_seen s ! u" using us1 seen_eq by simp
        ultimately have "out_scanned_seen s u (free_out_hi acyc_flow ! u) ∧ in_scanned_seen s u (free_in_hi acyc_flow ! u)"
          using sc ult by (auto simp: scan_complete_def)
        thus ?thesis using seen_eq by (auto simp: out_scanned_seen_def in_scanned_seen_def)
      qed
    qed
  qed
qed

lemma build_dfs_sc_aux:
  assumes dom: "build_dfs_dom (fl, s)"
  shows "fl = acyc_flow ⟶ dfs_wf s ∧ scan_complete s ⟶ dfs_wf (build_dfs fl s) ∧ scan_complete (build_dfs fl s)"
proof (induct rule: bd_induct[OF dom])
  case IH: (1 fl s)
  show ?case
  proof (intro impI, elim conjE)
    assume fleq: "fl = acyc_flow" and wf: "dfs_wf s" and sc: "scan_complete s"
    show "dfs_wf (build_dfs fl s) ∧ scan_complete (build_dfs fl s)"
    proof (rule bd_cases[where fl = fl and s = s])
      assume c: "bd_call1_conds fl s"
      have wf1: "dfs_wf (bd_upd1 fl s)" using bd_upd1_wf[OF Hout_valid wf c] .
      have sc1: "scan_complete (bd_upd1 fl s)"
        using bd_upd1_scan_complete[OF wf sc] c fleq by simp
      have "build_dfs fl s = build_dfs fl (bd_upd1 fl s)" using IH(1) c by (rule bd_simps(1))
      thus "dfs_wf (build_dfs fl s) ∧ scan_complete (build_dfs fl s)"
        using IH(2)[OF c] fleq wf1 sc1 by simp
    next
      assume c: "bd_call2_conds fl s"
      have wf1: "dfs_wf (bd_upd2 fl s)" using bd_upd2_wf[OF Hin_valid wf c] .
      have sc1: "scan_complete (bd_upd2 fl s)"
        using bd_upd2_scan_complete[OF wf sc] c fleq by simp
      have "build_dfs fl s = build_dfs fl (bd_upd2 fl s)" using IH(1) c by (rule bd_simps(2))
      thus "dfs_wf (build_dfs fl s) ∧ scan_complete (build_dfs fl s)"
        using IH(3)[OF c] fleq wf1 sc1 by simp
    next
      assume c: "bd_call3_conds fl s"
      have wf1: "dfs_wf (bd_upd3 s)" using bd_upd3_wf[OF wf c] .
      have sc1: "scan_complete (bd_upd3 s)"
        using bd_upd3_scan_complete[OF wf sc] c fleq by simp
      have "build_dfs fl s = build_dfs fl (bd_upd3 s)" using IH(1) c by (rule bd_simps(3))
      thus "dfs_wf (build_dfs fl s) ∧ scan_complete (build_dfs fl s)"
        using IH(4)[OF c] fleq wf1 sc1 by simp
    next
      assume c: "bd_ret_conds s"
      have "build_dfs fl s = s" using IH(1) c by (rule bd_simps(4))
      thus "dfs_wf (build_dfs fl s) ∧ scan_complete (build_dfs fl s)" using wf sc by simp
    qed
  qed
qed

lemma build_dfs_scan_complete:
  assumes wf: "dfs_wf s" and sc: "scan_complete s"
  shows "scan_complete (build_dfs acyc_flow s)"
proof -
  have dom: "build_dfs_dom (acyc_flow, s)" using wf by (rule build_dfs_dom_wf')
  show ?thesis using build_dfs_sc_aux[OF dom] wf sc by simp
qed

lemma emit_U_edge_seen: "ds_seen (emit_U_edge s v) = ds_seen s"
  by (simp add: emit_U_edge_def Let_def)
lemma emit_U_edge_stk: "ds_stk (emit_U_edge s v) = ds_stk s"
  by (simp add: emit_U_edge_def Let_def)

lemma open_tree_component_scan_complete:
  assumes sc: "scan_complete s" and wf: "dfs_wf s" and emp: "ds_stk s = []"
    and cv: "c < vcount"
  shows "scan_complete (open_tree_component acyc_flow s c) ∧ dfs_wf (open_tree_component acyc_flow s c)"
proof -
  define t where "t = (let imb = imbalance ! c; up = 0 ≤ imb; af = ¦imb¦; cp = (if up then af + 1 else af); pv = ds_prev s
    in s⦇ ds_afst := (ds_afst s)[ds_nxt s := (if up then c else vcount)],
          ds_asnd := (ds_asnd s)[ds_nxt s := (if up then vcount else c)],
          ds_acap := (ds_acap s)[ds_nxt s := cp],
          ds_aflw := (ds_aflw s)[ds_nxt s := af],
          ds_aest := (ds_aest s)[ds_nxt s := InTree],
          ds_nxt  := Suc (ds_nxt s),
          ds_seen := (ds_seen s)[c := True],
          ds_prnt := (ds_prnt s)[c := vcount],
          ds_par  := (ds_par s)[c := m + ds_nxt s],
          ds_dir  := (ds_dir s)[c := up],
          ds_pot  := (ds_pot s)[c := (if up then pval_negM else pval_M)],
          ds_thrd := (ds_thrd s)[pv := c],
          ds_rvth := (ds_rvth s)[c := pv],
          ds_snum := (ds_snum s)[c := 1],
          ds_prev := c,
          ds_stk  := [(c, out_lo ! c, in_lo ! c)] ⦈)"
  have otc: "open_tree_component acyc_flow s c = build_dfs acyc_flow t"
    by (simp add: open_tree_component_def Let_def t_def)
  have tseen: "ds_seen t = (ds_seen s)[c := True]" by (simp add: t_def Let_def)
  have tstk: "ds_stk t = [(c, out_lo ! c, in_lo ! c)]" by (simp add: t_def Let_def)
  have tlen: "length (ds_seen t) = Suc vcount" using wf by (simp add: tseen dfs_wf_def)
  have seen_mono: "⋀x. ds_seen s ! x ⟹ ds_seen t ! x"
    unfolding tseen by (metis list_update_beyond nth_list_update_eq nth_list_update_neq linorder_not_le)
  have wft: "dfs_wf t" using cv tlen by (simp add: dfs_wf_def tstk)
  have sct: "scan_complete t"
    unfolding scan_complete_def
  proof (intro conjI)
    show "∀(a,b,cc)∈set (ds_stk t). out_scanned_seen t a b ∧ in_scanned_seen t a cc"
      by (auto simp: tstk out_scanned_seen_def in_scanned_seen_def)
  next
    show "∀u<vcount. ds_seen t ! u ∧ u ∉ fst ` set (ds_stk t) ⟶
             out_scanned_seen t u (free_out_hi acyc_flow ! u) ∧ in_scanned_seen t u (free_in_hi acyc_flow ! u)"
    proof (intro allI impI, elim conjE)
      fix u assume ult: "u < vcount" and us1: "ds_seen t ! u" and us2: "u ∉ fst ` set (ds_stk t)"
      have unc: "u ≠ c" using us2 tstk by auto
      have "ds_seen s ! u" using us1 unc by (simp add: tseen nth_list_update_neq)
      moreover have "u ∉ fst ` set (ds_stk s)" using emp by simp
      ultimately have "out_scanned_seen s u (free_out_hi acyc_flow ! u) ∧ in_scanned_seen s u (free_in_hi acyc_flow ! u)"
        using sc ult by (auto simp: scan_complete_def)
      thus "out_scanned_seen t u (free_out_hi acyc_flow ! u) ∧ in_scanned_seen t u (free_in_hi acyc_flow ! u)"
        using seen_mono by (auto intro: out_scanned_seen_mono in_scanned_seen_mono)
    qed
  qed
  have "scan_complete (build_dfs acyc_flow t)" using build_dfs_scan_complete[OF wft sct] .
  moreover have "dfs_wf (build_dfs acyc_flow t)"
    using build_dfs_sc_aux[OF build_dfs_dom_wf'[OF wft]] wft sct by simp
  ultimately show ?thesis using otc by simp
qed

lemma build_dfs_stk_empty_aux:
  assumes dom: "build_dfs_dom (fl, s)"
  shows "ds_stk (build_dfs fl s) = []"
proof (induct rule: bd_induct[OF dom])
  case IH: (1 fl s)
  show ?case
  proof (rule bd_cases[where fl = fl and s = s])
    assume c: "bd_call1_conds fl s"
    have "build_dfs fl s = build_dfs fl (bd_upd1 fl s)" using IH(1) c by (rule bd_simps(1))
    thus "ds_stk (build_dfs fl s) = []" using IH(2)[OF c] by simp
  next
    assume c: "bd_call2_conds fl s"
    have "build_dfs fl s = build_dfs fl (bd_upd2 fl s)" using IH(1) c by (rule bd_simps(2))
    thus "ds_stk (build_dfs fl s) = []" using IH(3)[OF c] by simp
  next
    assume c: "bd_call3_conds fl s"
    have "build_dfs fl s = build_dfs fl (bd_upd3 s)" using IH(1) c by (rule bd_simps(3))
    thus "ds_stk (build_dfs fl s) = []" using IH(4)[OF c] by simp
  next
    assume c: "bd_ret_conds s"
    have "build_dfs fl s = s" using IH(1) c by (rule bd_simps(4))
    thus "ds_stk (build_dfs fl s) = []" using c by (simp add: bd_ret_conds_def)
  qed
qed

lemma build_dfs_stk_empty: "dfs_wf s ⟹ ds_stk (build_dfs acyc_flow s) = []"
  using build_dfs_stk_empty_aux[OF build_dfs_dom_wf'] .

lemma open_tree_component_full:
  assumes sc: "scan_complete s" and wf: "dfs_wf s" and emp: "ds_stk s = []" and cv: "c < vcount"
  shows "scan_complete (open_tree_component acyc_flow s c) ∧ dfs_wf (open_tree_component acyc_flow s c)
         ∧ ds_stk (open_tree_component acyc_flow s c) = []"
proof -
  define t where "t = (let imb = imbalance ! c; up = 0 ≤ imb; af = ¦imb¦; cp = (if up then af + 1 else af); pv = ds_prev s
    in s⦇ ds_afst := (ds_afst s)[ds_nxt s := (if up then c else vcount)], ds_asnd := (ds_asnd s)[ds_nxt s := (if up then vcount else c)],
          ds_acap := (ds_acap s)[ds_nxt s := cp], ds_aflw := (ds_aflw s)[ds_nxt s := af], ds_aest := (ds_aest s)[ds_nxt s := InTree],
          ds_nxt := Suc (ds_nxt s), ds_seen := (ds_seen s)[c := True], ds_prnt := (ds_prnt s)[c := vcount],
          ds_par := (ds_par s)[c := m + ds_nxt s], ds_dir := (ds_dir s)[c := up], ds_pot := (ds_pot s)[c := (if up then pval_negM else pval_M)],
          ds_thrd := (ds_thrd s)[pv := c], ds_rvth := (ds_rvth s)[c := pv], ds_snum := (ds_snum s)[c := 1], ds_prev := c,
          ds_stk := [(c, out_lo ! c, in_lo ! c)] ⦈)"
  have otc: "open_tree_component acyc_flow s c = build_dfs acyc_flow t"
    by (simp add: open_tree_component_def Let_def t_def)
  have wft: "dfs_wf t" using cv wf by (simp add: dfs_wf_def t_def Let_def)
  show ?thesis using open_tree_component_scan_complete[OF sc wf emp cv] build_dfs_stk_empty[OF wft] otc by simp
qed

lemma emit_U_edge_scan_complete: "scan_complete (emit_U_edge s v) = scan_complete s"
  by (simp add: scan_complete_def emit_U_edge_seen emit_U_edge_stk out_scanned_seen_def in_scanned_seen_def)
lemma emit_U_edge_wf: "dfs_wf (emit_U_edge s v) = dfs_wf s"
  by (simp add: dfs_wf_def emit_U_edge_seen emit_U_edge_stk)

definition scI :: "'n dfs_state ⇒ bool" where
  "scI s ⟷ ds_stk s = [] ∧ dfs_wf s ∧ scan_complete s"

lemma phase1_step_scI:
  assumes "scI s" and v: "v ∈ set vs_list"
  shows "scI (phase1_step acyc_flow v s)"
proof -
  have vc: "v < vcount" using v vs_less_vcount by simp
  have wf: "dfs_wf s" and emp: "ds_stk s = []" and sc: "scan_complete s" using assms(1) by (auto simp: scI_def)
  show ?thesis
  proof (cases "imbalance ! v = 0")
    case True thus ?thesis using assms(1) by (simp add: phase1_step_def)
  next
    case False
    show ?thesis
    proof (cases "ds_seen s ! v")
      case False
      thus ?thesis using open_tree_component_full[OF sc wf emp vc] ‹imbalance ! v ≠ 0›
        by (simp add: phase1_step_def scI_def)
    next
      case True
      thus ?thesis using ‹imbalance ! v ≠ 0› wf emp sc
        by (simp add: phase1_step_def scI_def emit_U_edge_scan_complete emit_U_edge_wf emit_U_edge_stk)
    qed
  qed
qed

lemma phase2_step_scI:
  assumes "scI s" and v: "v ∈ set vs_list"
  shows "scI (phase2_step acyc_flow v s)"
proof -
  have vc: "v < vcount" using v vs_less_vcount by simp
  have wf: "dfs_wf s" and emp: "ds_stk s = []" and sc: "scan_complete s" using assms(1) by (auto simp: scI_def)
  show ?thesis
  proof (cases "ds_seen s ! v")
    case True thus ?thesis using assms(1) by (simp add: phase2_step_def)
  next
    case False
    show ?thesis
    proof (cases "is_lonely v")
      case True
      thus ?thesis using assms(1) by (simp add: phase2_step_def)
    next
      case False
      with ‹¬ ds_seen s ! v› show ?thesis
        using open_tree_component_full[OF sc wf emp vc] by (simp add: phase2_step_def scI_def)
    qed
  qed
qed

lemma fold_phase1_scI: "scI s ⟹ set xs ⊆ set vs_list ⟹ scI (fold (phase1_step acyc_flow) xs s)"
  by (induct xs arbitrary: s) (auto simp: phase1_step_scI)
lemma fold_phase2_scI: "scI s ⟹ set xs ⊆ set vs_list ⟹ scI (fold (phase2_step acyc_flow) xs s)"
  by (induct xs arbitrary: s) (auto simp: phase2_step_scI)

lemma scI_dfs_init: "scI dfs_init"
  by (simp add: scI_def dfs_init_def dfs_wf_def scan_complete_def del: replicate_Suc)

lemma phase1_scI: "scI (phase1 acyc_flow dfs_init)"
  using fold_phase1_scI[OF scI_dfs_init] by (simp add: phase1_def)
lemma phase2_scI: "scI (phase2 acyc_flow (phase1 acyc_flow dfs_init))"
  using fold_phase2_scI[OF phase1_scI] by (simp add: phase2_def)

lemma build_tree_scan_complete: "scan_complete (build_tree acyc_flow)"
proof -
  have "scan_complete (phase2 acyc_flow (phase1 acyc_flow dfs_init))"
    using phase2_scI by (simp add: scI_def)
  thus ?thesis by (simp add: build_tree_def Let_def scan_complete_def out_scanned_seen_def in_scanned_seen_def)
qed

subsection ‹Free-edge coverage: ancestor extraction and the walk-builder›

text ‹Two reusable pieces toward the coverage theorem. First, from stk_prnt_inv (the stack is a parent
      vchain) a vertex on the stack is a pstep-ancestor of the top — this is what the merged invariant's
      ancinv conjunct uses at dfs_discover. Second, chain_redge turns a tree edge into the residual arc
      oriented from child to parent, and chain_redge_props certifies it is a free real edge of the
      original residual graph with the right endpoints — the atom the walk-builder assembles into a
      pstep-chain prepath for free_walk_no_cycle.›

lemma vchain_pstep_reach:
  assumes "vchain (ds_prnt s) (v # vs)"
    and "⋀y. y ∈ set (v # vs) ⟹ y < vcount ∧ ds_seen s ! y"
    and "x ∈ set (v # vs)"
  shows "(v, x) ∈ (pstep s)⇧*"
  using assms
proof (induct vs arbitrary: v)
  case Nil
  hence "x = v" by simp
  thus ?case by simp
next
  case (Cons u us)
  have chain: "ds_prnt s ! v = u" and rest: "vchain (ds_prnt s) (u # us)"
    using Cons.prems(1) by auto
  have vseen: "v < vcount ∧ ds_seen s ! v" using Cons.prems(2) by simp
  have step: "(v, u) ∈ pstep s" using chain vseen by (auto simp: pstep_def)
  show ?case
  proof (cases "x = v")
    case True thus ?thesis by simp
  next
    case False
    hence "x ∈ set (u # us)" using Cons.prems(3) by simp
    hence "(u, x) ∈ (pstep s)⇧*" using Cons.hyps[OF rest] Cons.prems(2) by simp
    thus ?thesis using step by (simp add: converse_rtrancl_into_rtrancl)
  qed
qed

lemma stk_ancestor:
  assumes spi: "stk_prnt_inv s" and tsi: "tree_seen_inv s" and wf: "dfs_wf s"
    and top: "ds_stk s = (v,oc,ic) # rest"
    and x: "x ∈ fst ` set (ds_stk s)"
  shows "(v, x) ∈ (pstep s)⇧*"
proof -
  have vc: "vchain (ds_prnt s) (v # map (λ(v,oc,ic). v) rest)"
    using spi top by (simp add: stk_prnt_inv_def)
  have seenv: "⋀y. y ∈ set (v # map (λ(v,oc,ic). v) rest) ⟹ y < vcount ∧ ds_seen s ! y"
    using wf tsi top by (auto simp: dfs_wf_def tree_seen_inv_def split: prod.splits)
  have xin: "x ∈ set (v # map (λ(v,oc,ic). v) rest)"
  proof -
    from x obtain fr where fr: "fr ∈ set (ds_stk s)" and xf: "x = fst fr" by auto
    obtain a b cc where "fr = (a,b,cc)" by (cases fr)
    thus ?thesis using fr xf top by (force simp: image_iff)
  qed
  show ?thesis using vchain_pstep_reach[OF vc seenv xin] .
qed

lemma cr_fstv_F: "e < m ⟹ original_network.fstv (F e) = fst_list ! e"
  by simp
lemma cr_sndv_F: "e < m ⟹ original_network.sndv (F e) = snd_list ! e"
  by simp
lemma cr_inE_F: "e < m ⟹ F e ∈ original_network.𝔈"
  by (simp add: original_network.𝔈_def)
lemma cr_inE_B: "e < m ⟹ B e ∈ original_network.𝔈"
  by (simp add: original_network.𝔈_def)

lemma cr_fstv_B: "e < m ⟹ original_network.fstv (B e) = snd_list ! e" by simp
lemma cr_sndv_B: "e < m ⟹ original_network.sndv (B e) = fst_list ! e" by simp

definition chain_redge :: "nat ⇒ nat Redge" where
  "chain_redge x = (if fst_list ! (ds_par (build_tree acyc_flow) ! x) = x
                    then F (ds_par (build_tree acyc_flow) ! x) else B (ds_par (build_tree acyc_flow) ! x))"

lemma chain_redge_props:
  assumes x: "x ∈ Vseen" and pd: "ds_prnt (build_tree acyc_flow) ! x < vcount"
  shows "original_network.oedge (chain_redge x) = ds_par (build_tree acyc_flow) ! x
       ∧ ds_par (build_tree acyc_flow) ! x < m
       ∧ is_free acyc_flow (ds_par (build_tree acyc_flow) ! x)
       ∧ original_network.fstv (chain_redge x) = x
       ∧ original_network.sndv (chain_redge x) = ds_prnt (build_tree acyc_flow) ! x
       ∧ chain_redge x ∈ original_network.𝔈"
proof -
  let ?bt = "build_tree acyc_flow"
  let ?e = "ds_par ?bt ! x"
  have xlt: "x < vcount" and xseen: "ds_seen ?bt ! x" using x by (auto simp: Vseen_def)
  note bp = build_tree_par_edge[OF xlt xseen pd]
  have pe: "?e < m" using bp[THEN conjunct1] .
  have free: "is_free acyc_flow ?e" using bp[THEN conjunct2, THEN conjunct1] .
  have orient: "fst_list ! ?e = (if ds_dir ?bt ! x then x else ds_prnt ?bt ! x)"
    using bp[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1] .
  have orient2: "snd_list ! ?e = (if ds_dir ?bt ! x then ds_prnt ?bt ! x else x)"
    using bp[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2] .
  have pnx: "ds_prnt ?bt ! x ≠ x"
  proof
    assume "ds_prnt ?bt ! x = x"
    hence "(x, x) ∈ pstep ?bt" using xlt xseen by (auto simp: pstep_def)
    thus False using pstep_acyclic by (metis acyclic_def r_into_trancl)
  qed
  show ?thesis
  proof (cases "ds_dir ?bt ! x")
    case True
    have cr: "chain_redge x = F ?e" using True orient by (simp add: chain_redge_def)
    have oe: "original_network.oedge (chain_redge x) = ?e" by (simp add: cr)
    have fv: "original_network.fstv (chain_redge x) = x"
      using cr cr_fstv_F[OF pe] orient True by simp
    have sv: "original_network.sndv (chain_redge x) = ds_prnt ?bt ! x"
      using cr cr_sndv_F[OF pe] orient2 True by simp
    have ie: "chain_redge x ∈ original_network.𝔈" using cr cr_inE_F[OF pe] by simp
    show ?thesis using oe pe free fv sv ie by simp
  next
    case False
    have fne: "fst_list ! ?e ≠ x" using False orient pnx by simp
    have cr: "chain_redge x = B ?e" using fne by (simp add: chain_redge_def)
    have oe: "original_network.oedge (chain_redge x) = ?e" by (simp add: cr)
    have fv: "original_network.fstv (chain_redge x) = x"
      using cr cr_fstv_B[OF pe] orient2 False by simp
    have sv: "original_network.sndv (chain_redge x) = ds_prnt ?bt ! x"
      using cr cr_sndv_B[OF pe] orient False by simp
    have ie: "chain_redge x ∈ original_network.𝔈" using cr cr_inE_B[OF pe] by simp
    show ?thesis using oe pe free fv sv ie by simp
  qed
qed

text ‹prepath plumbing: original_network is only a flow_network_spec, so the flow_network-level
      prepath_intros are unavailable; op_prepath_single/cons rebuild the single-arc and cons introduction
      rules from prepath_def and awalk_Cons_iff over the UNIV pair-graph. The walk-builder then turns a
      pstep-chain u ↝* w to a real ancestor w into an interior free-real prepath from u to w (chain_redge
      per step, oriented child→parent), tracking that its residual arcs are exactly the parent edges of
      the chain vertices — hence distinct (par_inj) and never equal to an uncovered edge.›

lemma op_tvp: "original_network.to_vertex_pair e = (original_network.fstv e, original_network.sndv e)"
  by (cases e) (auto simp add: original_network.make_pair_def)

lemma dVs_UNIV_all: "(x::nat) ∈ dVs UNIV"
  by (auto simp: dVs_def)

lemma op_prepath_single: "original_network.prepath [e]"
  by (simp add: original_network.prepath_def op_tvp awalk_Cons_iff awalk_Nil_iff dVs_UNIV_all)

lemma op_prepath_cons:
  assumes "original_network.sndv e = original_network.fstv (hd p)" and "original_network.prepath p"
  shows "original_network.prepath (e # p)"
proof -
  obtain d es where p: "p = d # es" using assms(2) by (cases p) (auto simp: original_network.prepath_def)
  show ?thesis
    using assms
    by (auto simp: original_network.prepath_def op_tvp awalk_Cons_iff dVs_UNIV_all p)
qed

lemma pstep_chain_prepath:
  assumes uw: "(u, w) ∈ (pstep (build_tree acyc_flow))⇧*" and wv: "w < vcount"
  shows "u = w ∨ (∃C. C ≠ [] ∧ original_network.prepath C
     ∧ original_network.fstv (hd C) = u ∧ original_network.sndv (last C) = w
     ∧ (∀a∈set C. original_network.oedge a < m ∧ is_free acyc_flow (original_network.oedge a))
     ∧ distinct (map original_network.oedge C)
     ∧ (∀e'∈original_network.oedge ` set C. ∃y∈Vseen. e' = ds_par (build_tree acyc_flow) ! y
             ∧ (u,y) ∈ (pstep (build_tree acyc_flow))⇧* ∧ (y,w) ∈ (pstep (build_tree acyc_flow))⇧+))"
  using uw
proof (induct rule: converse_rtrancl_induct)
  case base
  show ?case by simp
next
  case (step a b)
  let ?bt = "build_tree acyc_flow"
  let ?P = "pstep ?bt"
  have ab: "(a, b) ∈ ?P" and bwstar: "(b, w) ∈ ?P⇧*" by (rule step(1), rule step(2))
  have alt: "a < vcount" and aseen: "ds_seen ?bt ! a" and bpar: "b = ds_prnt ?bt ! a"
    using ab by (auto simp: pstep_def)
  have aV: "a ∈ Vseen" using alt aseen by (simp add: Vseen_def)
  have bv: "b < vcount"
  proof (rule ccontr)
    assume nb: "¬ b < vcount"
    have "b = w"
    proof (rule converse_rtranclE[OF bwstar])
      show "b = w ⟹ b = w" .
    next
      fix c assume "(b, c) ∈ ?P"
      hence "b < vcount" by (simp add: pstep_def)
      thus "b = w" using nb by simp
    qed
    thus False using nb wv by simp
  qed
  have bpd: "ds_prnt ?bt ! a < vcount" using bpar bv by simp
  note crp = chain_redge_props[OF aV bpd]
  have cr_oe: "original_network.oedge (chain_redge a) = ds_par ?bt ! a"
    using crp[THEN conjunct1] .
  have cr_pe: "ds_par ?bt ! a < m" using crp[THEN conjunct2, THEN conjunct1] .
  have cr_free: "is_free acyc_flow (ds_par ?bt ! a)"
    using crp[THEN conjunct2, THEN conjunct2, THEN conjunct1] .
  have cr_fv: "original_network.fstv (chain_redge a) = a"
    using crp[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1] .
  have cr_sv: "original_network.sndv (chain_redge a) = b"
    using crp[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1] bpar by simp
  ― ‹freshness: ds_par a is not among edges of any chain from b›
  have fresh_helper: "⋀y. y ∈ Vseen ⟹ (b,y) ∈ ?P⇧* ⟹ ds_par ?bt ! y ≠ ds_par ?bt ! a"
  proof -
    fix y assume yseen: "y ∈ Vseen" and by_: "(b,y) ∈ ?P⇧*"
    show "ds_par ?bt ! y ≠ ds_par ?bt ! a"
    proof
      assume eq: "ds_par ?bt ! y = ds_par ?bt ! a"
      have "y = a" using par_inj[OF yseen aV] eq by simp
      hence "(a,a) ∈ ?P⇧+" using rtrancl_into_trancl2[OF ab] by_ by simp
      thus False using pstep_acyclic by (simp add: acyclic_def)
    qed
  qed
  show ?case
  proof (cases "b = w")
    case True
    have aw: "(a, w) ∈ ?P⇧+" using ab True by (simp add: r_into_trancl)
    have pp: "original_network.prepath [chain_redge a]" by (rule op_prepath_single)
    have "∀e'∈original_network.oedge ` set [chain_redge a]. ∃y∈Vseen. e' = ds_par ?bt ! y
             ∧ (a,y) ∈ ?P⇧* ∧ (y,w) ∈ ?P⇧+"
      using cr_oe aV aw by auto
    hence "[chain_redge a] ≠ [] ∧ original_network.prepath [chain_redge a]
       ∧ original_network.fstv (hd [chain_redge a]) = a ∧ original_network.sndv (last [chain_redge a]) = w
       ∧ (∀aa∈set [chain_redge a]. original_network.oedge aa < m ∧ is_free acyc_flow (original_network.oedge aa))
       ∧ distinct (map original_network.oedge [chain_redge a])
       ∧ (∀e'∈original_network.oedge ` set [chain_redge a]. ∃y∈Vseen. e' = ds_par ?bt ! y
             ∧ (a,y) ∈ ?P⇧* ∧ (y,w) ∈ ?P⇧+)"
      using pp cr_oe cr_pe cr_free cr_fv cr_sv True by simp
    thus ?thesis by blast
  next
    case False
    with step(3) obtain C where C: "C ≠ []" "original_network.prepath C"
      "original_network.fstv (hd C) = b" "original_network.sndv (last C) = w"
      "∀aa∈set C. original_network.oedge aa < m ∧ is_free acyc_flow (original_network.oedge aa)"
      "distinct (map original_network.oedge C)"
      "∀e'∈original_network.oedge ` set C. ∃y∈Vseen. e' = ds_par ?bt ! y ∧ (b,y) ∈ ?P⇧* ∧ (y,w) ∈ ?P⇧+"
      by blast
    have sf: "original_network.sndv (chain_redge a) = original_network.fstv (hd C)"
      using cr_sv C(3) by simp
    have pp: "original_network.prepath (chain_redge a # C)"
      by (rule op_prepath_cons[OF sf C(2)])
    have fresh: "ds_par ?bt ! a ∉ original_network.oedge ` set C"
    proof
      assume "ds_par ?bt ! a ∈ original_network.oedge ` set C"
      then obtain y where yy: "y ∈ Vseen" "ds_par ?bt ! a = ds_par ?bt ! y" "(b,y) ∈ ?P⇧*"
        using C(7) by blast
      thus False using fresh_helper[OF yy(1) yy(3)] by simp
    qed
    have hC: "original_network.fstv (hd (chain_redge a # C)) = a" using cr_fv by simp
    have lC: "original_network.sndv (last (chain_redge a # C)) = w" using C(1) C(4) by simp
    have edgesC: "∀aa∈set (chain_redge a # C). original_network.oedge aa < m ∧ is_free acyc_flow (original_network.oedge aa)"
      using cr_oe cr_pe cr_free C(5) by auto
    have distC: "distinct (map original_network.oedge (chain_redge a # C))"
      using C(6) fresh cr_oe by simp
    have coverC: "∀e'∈original_network.oedge ` set (chain_redge a # C). ∃y∈Vseen. e' = ds_par ?bt ! y
             ∧ (a,y) ∈ ?P⇧* ∧ (y,w) ∈ ?P⇧+"
    proof
      fix e' assume "e' ∈ original_network.oedge ` set (chain_redge a # C)"
      hence "e' = ds_par ?bt ! a ∨ e' ∈ original_network.oedge ` set C" using cr_oe by auto
      thus "∃y∈Vseen. e' = ds_par ?bt ! y ∧ (a,y) ∈ ?P⇧* ∧ (y,w) ∈ ?P⇧+"
      proof
        assume "e' = ds_par ?bt ! a"
        moreover have "(a, w) ∈ ?P⇧+" using ab bwstar by (simp add: rtrancl_into_trancl2)
        ultimately show ?thesis using aV by auto
      next
        assume "e' ∈ original_network.oedge ` set C"
        then obtain y where "y∈Vseen" "e' = ds_par ?bt ! y" "(b,y) ∈ ?P⇧*" "(y,w) ∈ ?P⇧+"
          using C(7) by blast
        moreover have "(a,y) ∈ ?P⇧*" using ab ‹(b,y) ∈ ?P⇧*› by (simp add: converse_rtrancl_into_rtrancl)
        ultimately show ?thesis by blast
      qed
    qed
    have "chain_redge a # C ≠ [] ∧ original_network.prepath (chain_redge a # C)
       ∧ original_network.fstv (hd (chain_redge a # C)) = a ∧ original_network.sndv (last (chain_redge a # C)) = w
       ∧ (∀aa∈set (chain_redge a # C). original_network.oedge aa < m ∧ is_free acyc_flow (original_network.oedge aa))
       ∧ distinct (map original_network.oedge (chain_redge a # C))
       ∧ (∀e'∈original_network.oedge ` set (chain_redge a # C). ∃y∈Vseen. e' = ds_par ?bt ! y
             ∧ (a,y) ∈ ?P⇧* ∧ (y,w) ∈ ?P⇧+)"
      using pp hC lC edgesC distC coverC by simp
    thus ?thesis by blast
  qed
qed

subsection ‹Block completeness: every free edge sits in its owner's CSR scan block›

text ‹Block soundness (free_out_edges_block) + size (scW_out) do not by themselves say a ∗‹specific›
      free edge occupies a slot of its owner's block. We track block ∗‹content› as a fold invariant
      (scW_out_ct / scW_in_ct: slot ‹out_lo!v + i› holds the i-th free edge with tail v in [0..<m]-order),
      reusing sc_block_disj for the scatter write; the corollaries free_out/in_edge_in_block give the
      completeness the covinv finished-vertex contradiction needs.›

lemma mem_test:
  assumes em: "e < m" and cl: "classify fl e = InTree" and fe: "fst_list ! e = v"
  shows "e ∈ set (filter (λy. classify fl y = InTree ∧ fst_list ! y = v) [0..<m])"
proof -
  have e1: "e ∈ set [0..<m]" using em by simp
  show ?thesis using e1 cl fe by (subst set_filter) blast
qed

lemma mem_test_snd:
  assumes em: "e < m" and cl: "classify fl e = InTree" and fe: "snd_list ! e = v"
  shows "e ∈ set (filter (λy. classify fl y = InTree ∧ snd_list ! y = v) [0..<m])"
proof -
  have e1: "e ∈ set [0..<m]" using em by simp
  show ?thesis using e1 cl fe by (subst set_filter) blast
qed

definition scW_out_ct ::
  "'n list ⇒ nat list ⇒ edge_tag list × 'n list × nat list × nat list × nat list × nat list ⇒ bool" where
  "scW_out_ct fl dn s ⟷ (∀v<vcount. ∀i<length (filter (λy. classify fl y = InTree ∧ fst_list ! y = v) dn).
        fst (snd (snd s)) ! (out_lo ! v + i) = filter (λy. classify fl y = InTree ∧ fst_list ! y = v) dn ! i)"

lemma scW_out_ct_step:
  assumes split: "[0..<m] = dn @ e # rest" and sz: "sized s"
      and inv: "scW_out fl dn s" and invc: "scW_out_ct fl dn s"
  shows "scW_out_ct fl (dn @ [e]) (passA_step fl e s)"
proof (cases "classify fl e = InTree")
  case notfree: False
  have oe': "fst (snd (snd (passA_step fl e s))) = fst (snd (snd s))"
    by (simp add: passA_step_oe notfree)
  have filt: "⋀v. filter (λy. classify fl y = InTree ∧ fst_list ! y = v) (dn @ [e])
                 = filter (λy. classify fl y = InTree ∧ fst_list ! y = v) dn"
    using notfree by simp
  show ?thesis using invc unfolding scW_out_ct_def oe' filt by simp
next
  case free: True
  define x where "x = fst_list ! e"
  have es: "e ∈ set [0..<m]" using split by simp
  hence em: "e < m" by simp
  have xlt: "x < vcount" using es keys_fst_lt x_def by blast
  have loc: "length (fst (snd (snd (snd s)))) = vcount" using sz by (cases s) (simp add: sized_def)
  have loe: "length (fst (snd (snd s))) = m" using sz by (cases s) (simp add: sized_def)
  define W where "W = fst (snd (snd (snd s))) ! x"
  have oe': "fst (snd (snd (passA_step fl e s))) = (fst (snd (snd s)))[W := e]"
    using free by (simp add: passA_step_oe x_def W_def)
  have countI: "⋀v. v < vcount ⟹ fst (snd (snd (snd s))) ! v
        = out_lo ! v + length (filter (λy. classify fl y = InTree ∧ fst_list ! y = v) dn)"
    using inv by (simp add: scW_out_def)
  have Wval: "W = out_lo ! x + length (filter (λy. classify fl y = InTree ∧ fst_list ! y = x) dn)"
    using countI[OF xlt] W_def by simp
  have cntx_lt: "length (filter (λy. classify fl y = InTree ∧ fst_list ! y = x) dn)
                   < ct vcount (nth fst_list) [0..<m] ! x"
  proof -
    have dnlt: "length (filter (λy. fst_list ! y = x) dn) < length (filter (λy. fst_list ! y = x) [0..<m])"
      using split x_def by simp
    have "length (filter (λy. classify fl y = InTree ∧ fst_list ! y = x) dn)
            ≤ length (filter (λy. fst_list ! y = x) dn)" by (rule length_filter_conj_le)
    thus ?thesis using dnlt xlt by (simp add: ct_nth)
  qed
  have Wm: "W < m"
  proof -
    have "W = out_lo ! x + length (filter (λy. classify fl y = InTree ∧ fst_list ! y = x) dn)" by (rule Wval)
    also have "… < out_lo ! x + ct vcount (nth fst_list) [0..<m] ! x" using cntx_lt by simp
    also have "… = sc_lo vcount (nth fst_list) [0..<m] (Suc x)"
      using xlt by (simp add: out_lo_eq_sc_lo sc_lo_Suc)
    also have "… ≤ length [0..<m]"
      using xlt sc_lo_le_length[OF keys_fst_lt, of "Suc x"] by simp
    finally show ?thesis by simp
  qed
  have contI: "⋀v i. v < vcount ⟹ i < length (filter (λy. classify fl y = InTree ∧ fst_list ! y = v) dn) ⟹
        fst (snd (snd s)) ! (out_lo ! v + i) = filter (λy. classify fl y = InTree ∧ fst_list ! y = v) dn ! i"
    using invc by (simp add: scW_out_ct_def)
  show ?thesis unfolding scW_out_ct_def oe'
  proof (intro allI impI)
    fix v i assume v: "v < vcount"
      and ilt: "i < length (filter (λy. classify fl y = InTree ∧ fst_list ! y = v) (dn @ [e]))"
    let ?fv = "filter (λy. classify fl y = InTree ∧ fst_list ! y = v)"
    show "(fst (snd (snd s)))[W := e] ! (out_lo ! v + i) = ?fv (dn @ [e]) ! i"
    proof (cases "v = x")
      case vx: True
      have fvsplit: "?fv (dn @ [e]) = ?fv dn @ [e]" using free vx x_def by simp
      show ?thesis
      proof (cases "i < length (?fv dn)")
        case ismall: True
        have neq: "out_lo ! v + i ≠ W" using Wval vx ismall by simp
        have "(fst (snd (snd s)))[W := e] ! (out_lo ! v + i) = fst (snd (snd s)) ! (out_lo ! v + i)"
          using neq by (simp add: nth_list_update_neq)
        also have "… = ?fv dn ! i" using contI[OF v] ismall by simp
        also have "… = ?fv (dn @ [e]) ! i" using fvsplit ismall by (simp add: nth_append)
        finally show ?thesis .
      next
        case ibig: False
        have ieq: "i = length (?fv dn)" using ilt fvsplit ibig by auto
        have "out_lo ! v + i = W" using Wval vx ieq by simp
        hence "(fst (snd (snd s)))[W := e] ! (out_lo ! v + i) = e"
          using Wm loe by (simp add: nth_list_update_eq)
        also have "… = ?fv (dn @ [e]) ! i" using fvsplit ieq by (simp add: nth_append)
        finally show ?thesis .
      qed
    next
      case vne: False
      have fvsame: "?fv (dn @ [e]) = ?fv dn" using vne x_def by auto
      have ismall: "i < length (?fv dn)" using ilt fvsame by simp
      have avct: "i < ct vcount (nth fst_list) [0..<m] ! v"
      proof -
        have "length (?fv dn) ≤ length (filter (λy. fst_list ! y = v) dn)" by (rule length_filter_conj_le)
        also have "… ≤ length (filter (λy. fst_list ! y = v) [0..<m])" using split by simp
        finally show ?thesis using ismall v by (simp add: ct_nth)
      qed
      have neq: "out_lo ! v + i ≠ W"
      proof -
        have "sc_lo vcount (nth fst_list) [0..<m] x
                + length (filter (λy. classify fl y = InTree ∧ fst_list ! y = x) dn)
              ≠ sc_lo vcount (nth fst_list) [0..<m] v + i"
          by (rule sc_block_disj[OF xlt v vne cntx_lt avct])
        thus ?thesis using Wval out_lo_eq_sc_lo[OF xlt] out_lo_eq_sc_lo[OF v] by simp
      qed
      have "(fst (snd (snd s)))[W := e] ! (out_lo ! v + i) = fst (snd (snd s)) ! (out_lo ! v + i)"
        using neq by (simp add: nth_list_update_neq)
      also have "… = ?fv dn ! i" using contI[OF v] ismall by simp
      also have "… = ?fv (dn @ [e]) ! i" using fvsame by simp
      finally show ?thesis .
    qed
  qed
qed

lemma scW_out_ct_fold:
  assumes "[0..<m] = dn @ rest" "sized s" "scW_out fl dn s" "scW_out_ct fl dn s"
  shows "scW_out_ct fl [0..<m] (fold (passA_step fl) rest s)"
  using assms
proof (induction rest arbitrary: dn s)
  case Nil thus ?case by simp
next
  case (Cons e rest)
  have split: "[0..<m] = dn @ e # rest" using Cons.prems(1) by simp
  have split': "[0..<m] = (dn @ [e]) @ rest" using Cons.prems(1) by simp
  have stepW: "scW_out fl (dn @ [e]) (passA_step fl e s)"
    by (rule scW_out_step[OF split Cons.prems(2) Cons.prems(3)])
  have stepC: "scW_out_ct fl (dn @ [e]) (passA_step fl e s)"
    by (rule scW_out_ct_step[OF split Cons.prems(2) Cons.prems(3) Cons.prems(4)])
  have sz': "sized (passA_step fl e s)" using Cons.prems(2) by (rule passA_step_sized)
  show ?case using Cons.IH[OF split' sz' stepW stepC] by simp
qed

lemma scW_out_ct_init:
  "scW_out_ct fl [] (replicate m InL, replicate (Suc vcount) (0::'n), csr_edges out_csr, out_lo,
               csr_edges in_csr, in_lo)"
  by (simp add: scW_out_ct_def)

lemma scW_out_ct_passA: "scW_out_ct fl [0..<m] (passA fl)"
proof -
  have sz0: "sized (replicate m InL, replicate (Suc vcount) (0::'n), csr_edges out_csr, out_lo,
                csr_edges in_csr, in_lo)"
    by (simp add: sized_def length_out_lo length_in_lo out_csr_eq in_csr_eq)
  have "scW_out_ct fl [0..<m] (fold (passA_step fl) [0..<m]
          (replicate m InL, replicate (Suc vcount) (0::'n), csr_edges out_csr, out_lo,
           csr_edges in_csr, in_lo))"
    by (rule scW_out_ct_fold[OF _ sz0 scW_out_init scW_out_ct_init]) simp
  thus ?thesis by (simp add: passA_def)
qed

lemma free_out_block_content:
  assumes v: "v < vcount"
      and i: "i < length (filter (λy. classify fl y = InTree ∧ fst_list ! y = v) [0..<m])"
  shows "free_out_edges fl ! (out_lo ! v + i) = filter (λy. classify fl y = InTree ∧ fst_list ! y = v) [0..<m] ! i"
proof -
  have "fst (snd (snd (passA fl))) ! (out_lo ! v + i)
          = filter (λy. classify fl y = InTree ∧ fst_list ! y = v) [0..<m] ! i"
    using scW_out_ct_passA[unfolded scW_out_ct_def, rule_format, OF v i] .
  thus ?thesis by (simp add: free_out_edges_def case6_3rd)
qed

lemma free_out_edge_in_block:
  assumes em: "e < m" and cl: "classify fl e = InTree" and fe: "fst_list ! e = v" and v: "v < vcount"
  shows "∃j. out_lo ! v ≤ j ∧ j < free_out_hi fl ! v ∧ free_out_edges fl ! j = e"
proof -
  let ?F = "filter (λy. classify fl y = InTree ∧ fst_list ! y = v) [0..<m]"
  have mem: "e ∈ set ?F" using mem_test[OF em cl fe] .
  then obtain i where i: "i < length ?F" and ei: "?F ! i = e"
    unfolding in_set_conv_nth by blast
  have hit: "free_out_edges fl ! (out_lo ! v + i) = e"
    using free_out_block_content[OF v i] ei by presburger
  have hilt: "out_lo ! v + i < free_out_hi fl ! v" using i free_out_hi_count[OF v] by simp
  show ?thesis using hit hilt le_add1 by blast
qed

definition scW_in_ct ::
  "'n list ⇒ nat list ⇒ edge_tag list × 'n list × nat list × nat list × nat list × nat list ⇒ bool" where
  "scW_in_ct fl dn s ⟷ (∀v<vcount. ∀i<length (filter (λy. classify fl y = InTree ∧ snd_list ! y = v) dn).
        fst (snd (snd (snd (snd s)))) ! (in_lo ! v + i) = filter (λy. classify fl y = InTree ∧ snd_list ! y = v) dn ! i)"

lemma scW_in_ct_step:
  assumes split: "[0..<m] = dn @ e # rest" and sz: "sized s"
      and inv: "scW_in fl dn s" and invc: "scW_in_ct fl dn s"
  shows "scW_in_ct fl (dn @ [e]) (passA_step fl e s)"
proof (cases "classify fl e = InTree")
  case notfree: False
  have oe': "fst (snd (snd (snd (snd (passA_step fl e s))))) = fst (snd (snd (snd (snd s))))"
    by (simp add: passA_step_ie notfree)
  have filt: "⋀v. filter (λy. classify fl y = InTree ∧ snd_list ! y = v) (dn @ [e])
                 = filter (λy. classify fl y = InTree ∧ snd_list ! y = v) dn"
    using notfree by simp
  show ?thesis using invc unfolding scW_in_ct_def oe' filt by simp
next
  case free: True
  define x where "x = snd_list ! e"
  have es: "e ∈ set [0..<m]" using split by simp
  hence em: "e < m" by simp
  have xlt: "x < vcount" using es keys_snd_lt x_def by blast
  have loc: "length (snd (snd (snd (snd (snd s))))) = vcount" using sz by (cases s) (simp add: sized_def)
  have loe: "length (fst (snd (snd (snd (snd s))))) = m" using sz by (cases s) (simp add: sized_def)
  define W where "W = snd (snd (snd (snd (snd s)))) ! x"
  have oe': "fst (snd (snd (snd (snd (passA_step fl e s))))) = (fst (snd (snd (snd (snd s)))))[W := e]"
    using free by (simp add: passA_step_ie x_def W_def)
  have countI: "⋀v. v < vcount ⟹ snd (snd (snd (snd (snd s)))) ! v
        = in_lo ! v + length (filter (λy. classify fl y = InTree ∧ snd_list ! y = v) dn)"
    using inv by (simp add: scW_in_def)
  have Wval: "W = in_lo ! x + length (filter (λy. classify fl y = InTree ∧ snd_list ! y = x) dn)"
    using countI[OF xlt] W_def by simp
  have cntx_lt: "length (filter (λy. classify fl y = InTree ∧ snd_list ! y = x) dn)
                   < ct vcount (nth snd_list) [0..<m] ! x"
  proof -
    have dnlt: "length (filter (λy. snd_list ! y = x) dn) < length (filter (λy. snd_list ! y = x) [0..<m])"
      using split x_def by simp
    have "length (filter (λy. classify fl y = InTree ∧ snd_list ! y = x) dn)
            ≤ length (filter (λy. snd_list ! y = x) dn)" by (rule length_filter_conj_le)
    thus ?thesis using dnlt xlt by (simp add: ct_nth)
  qed
  have Wm: "W < m"
  proof -
    have "W = in_lo ! x + length (filter (λy. classify fl y = InTree ∧ snd_list ! y = x) dn)" by (rule Wval)
    also have "… < in_lo ! x + ct vcount (nth snd_list) [0..<m] ! x" using cntx_lt by simp
    also have "… = sc_lo vcount (nth snd_list) [0..<m] (Suc x)"
      using xlt by (simp add: in_lo_eq_sc_lo sc_lo_Suc)
    also have "… ≤ length [0..<m]"
      using xlt sc_lo_le_length[OF keys_snd_lt, of "Suc x"] by simp
    finally show ?thesis by simp
  qed
  have contI: "⋀v i. v < vcount ⟹ i < length (filter (λy. classify fl y = InTree ∧ snd_list ! y = v) dn) ⟹
        fst (snd (snd (snd (snd s)))) ! (in_lo ! v + i) = filter (λy. classify fl y = InTree ∧ snd_list ! y = v) dn ! i"
    using invc by (simp add: scW_in_ct_def)
  show ?thesis unfolding scW_in_ct_def oe'
  proof (intro allI impI)
    fix v i assume v: "v < vcount"
      and ilt: "i < length (filter (λy. classify fl y = InTree ∧ snd_list ! y = v) (dn @ [e]))"
    let ?fv = "filter (λy. classify fl y = InTree ∧ snd_list ! y = v)"
    show "(fst (snd (snd (snd (snd s)))))[W := e] ! (in_lo ! v + i) = ?fv (dn @ [e]) ! i"
    proof (cases "v = x")
      case vx: True
      have fvsplit: "?fv (dn @ [e]) = ?fv dn @ [e]" using free vx x_def by simp
      show ?thesis
      proof (cases "i < length (?fv dn)")
        case ismall: True
        have neq: "in_lo ! v + i ≠ W" using Wval vx ismall by simp
        have "(fst (snd (snd (snd (snd s)))))[W := e] ! (in_lo ! v + i) = fst (snd (snd (snd (snd s)))) ! (in_lo ! v + i)"
          using neq by (simp add: nth_list_update_neq)
        also have "… = ?fv dn ! i" using contI[OF v] ismall by simp
        also have "… = ?fv (dn @ [e]) ! i" using fvsplit ismall by (simp add: nth_append)
        finally show ?thesis .
      next
        case ibig: False
        have ieq: "i = length (?fv dn)" using ilt fvsplit ibig by auto
        have "in_lo ! v + i = W" using Wval vx ieq by simp
        hence "(fst (snd (snd (snd (snd s)))))[W := e] ! (in_lo ! v + i) = e"
          using Wm loe by (simp add: nth_list_update_eq)
        also have "… = ?fv (dn @ [e]) ! i" using fvsplit ieq by (simp add: nth_append)
        finally show ?thesis .
      qed
    next
      case vne: False
      have fvsame: "?fv (dn @ [e]) = ?fv dn" using vne x_def by auto
      have ismall: "i < length (?fv dn)" using ilt fvsame by simp
      have avct: "i < ct vcount (nth snd_list) [0..<m] ! v"
      proof -
        have "length (?fv dn) ≤ length (filter (λy. snd_list ! y = v) dn)" by (rule length_filter_conj_le)
        also have "… ≤ length (filter (λy. snd_list ! y = v) [0..<m])" using split by simp
        finally show ?thesis using ismall v by (simp add: ct_nth)
      qed
      have neq: "in_lo ! v + i ≠ W"
      proof -
        have "sc_lo vcount (nth snd_list) [0..<m] x
                + length (filter (λy. classify fl y = InTree ∧ snd_list ! y = x) dn)
              ≠ sc_lo vcount (nth snd_list) [0..<m] v + i"
          by (rule sc_block_disj[OF xlt v vne cntx_lt avct])
        thus ?thesis using Wval in_lo_eq_sc_lo[OF xlt] in_lo_eq_sc_lo[OF v] by simp
      qed
      have "(fst (snd (snd (snd (snd s)))))[W := e] ! (in_lo ! v + i) = fst (snd (snd (snd (snd s)))) ! (in_lo ! v + i)"
        using neq by (simp add: nth_list_update_neq)
      also have "… = ?fv dn ! i" using contI[OF v] ismall by simp
      also have "… = ?fv (dn @ [e]) ! i" using fvsame by simp
      finally show ?thesis .
    qed
  qed
qed

lemma scW_in_ct_fold:
  assumes "[0..<m] = dn @ rest" "sized s" "scW_in fl dn s" "scW_in_ct fl dn s"
  shows "scW_in_ct fl [0..<m] (fold (passA_step fl) rest s)"
  using assms
proof (induction rest arbitrary: dn s)
  case Nil thus ?case by simp
next
  case (Cons e rest)
  have split: "[0..<m] = dn @ e # rest" using Cons.prems(1) by simp
  have split': "[0..<m] = (dn @ [e]) @ rest" using Cons.prems(1) by simp
  have stepW: "scW_in fl (dn @ [e]) (passA_step fl e s)"
    by (rule scW_in_step[OF split Cons.prems(2) Cons.prems(3)])
  have stepC: "scW_in_ct fl (dn @ [e]) (passA_step fl e s)"
    by (rule scW_in_ct_step[OF split Cons.prems(2) Cons.prems(3) Cons.prems(4)])
  have sz': "sized (passA_step fl e s)" using Cons.prems(2) by (rule passA_step_sized)
  show ?case using Cons.IH[OF split' sz' stepW stepC] by simp
qed

lemma scW_in_ct_init:
  "scW_in_ct fl [] (replicate m InL, replicate (Suc vcount) (0::'n), csr_edges out_csr, out_lo,
               csr_edges in_csr, in_lo)"
  by (simp add: scW_in_ct_def)

lemma scW_in_ct_passA: "scW_in_ct fl [0..<m] (passA fl)"
proof -
  have sz0: "sized (replicate m InL, replicate (Suc vcount) (0::'n), csr_edges out_csr, out_lo,
                csr_edges in_csr, in_lo)"
    by (simp add: sized_def length_out_lo length_in_lo out_csr_eq in_csr_eq)
  have "scW_in_ct fl [0..<m] (fold (passA_step fl) [0..<m]
          (replicate m InL, replicate (Suc vcount) (0::'n), csr_edges out_csr, out_lo,
           csr_edges in_csr, in_lo))"
    by (rule scW_in_ct_fold[OF _ sz0 scW_in_init scW_in_ct_init]) simp
  thus ?thesis by (simp add: passA_def)
qed

lemma free_in_block_content:
  assumes v: "v < vcount"
      and i: "i < length (filter (λy. classify fl y = InTree ∧ snd_list ! y = v) [0..<m])"
  shows "free_in_edges fl ! (in_lo ! v + i) = filter (λy. classify fl y = InTree ∧ snd_list ! y = v) [0..<m] ! i"
proof -
  have "fst (snd (snd (snd (snd (passA fl))))) ! (in_lo ! v + i)
          = filter (λy. classify fl y = InTree ∧ snd_list ! y = v) [0..<m] ! i"
    using scW_in_ct_passA[unfolded scW_in_ct_def, rule_format, OF v i] .
  thus ?thesis by (simp add: free_in_edges_def case6_5th)
qed

lemma free_in_edge_in_block:
  assumes em: "e < m" and cl: "classify fl e = InTree" and fe: "snd_list ! e = v" and v: "v < vcount"
  shows "∃j. in_lo ! v ≤ j ∧ j < free_in_hi fl ! v ∧ free_in_edges fl ! j = e"
proof -
  let ?F = "filter (λy. classify fl y = InTree ∧ snd_list ! y = v) [0..<m]"
  have mem: "e ∈ set ?F" using mem_test_snd[OF em cl fe] .
  then obtain i where i: "i < length ?F" and ei: "?F ! i = e"
    unfolding in_set_conv_nth by blast
  have hit: "free_in_edges fl ! (in_lo ! v + i) = e"
    using free_in_block_content[OF v i] ei by presburger
  have hilt: "in_lo ! v + i < free_in_hi fl ! v" using i free_in_hi_count[OF v] by simp
  show ?thesis using hit hilt le_add1 by blast
qed

subsection ‹Comparability of free-edge endpoints (covinv) and its discover-step maintenance›

text ‹covinv: any free real edge whose both endpoints are seen has pstep-comparable endpoints (one is a
      tree-ancestor of the other). Its only non-trivial maintenance is at dfs_discover: a newly seen w
      and an already-seen free-neighbour a of it must be comparable. free_neighbor_on_stack shows a is on
      the stack (a finished a would, by scan_complete + block-completeness, already have seen w); then
      stk_ancestor makes a an ancestor of the stack top v, and w becomes v's child, so (w,a)∈pstep*.›

lemma is_free_classify: "e < m ⟹ is_free acyc_flow e ⟹ classify acyc_flow e = InTree"
  by (simp add: is_free_def edge_state_nth)

definition covinv :: "'n dfs_state ⇒ bool" where
  "covinv s ⟷ (∀e<m. is_free acyc_flow e ⟶
      ds_seen s ! (fst_list ! e) ⟶ ds_seen s ! (snd_list ! e) ⟶
      (fst_list ! e, snd_list ! e) ∈ (pstep s)⇧* ∨ (snd_list ! e, fst_list ! e) ∈ (pstep s)⇧*)"

lemma free_neighbor_on_stack:
  assumes wf: "dfs_wf s" and sc: "scan_complete s"
    and em: "e < m" and free: "is_free acyc_flow e"
    and wns: "¬ ds_seen s ! w"
    and aseen: "ds_seen s ! a"
    and inc: "(fst_list ! e = a ∧ snd_list ! e = w) ∨ (fst_list ! e = w ∧ snd_list ! e = a)"
  shows "a ∈ fst ` set (ds_stk s)"
proof (rule ccontr)
  assume ans: "a ∉ fst ` set (ds_stk s)"
  have cl: "classify acyc_flow e = InTree" using is_free_classify[OF em free] .
  have avc: "a < vcount"
    using inc vs_less_vcount[OF fst_list_nth_vertex[OF em]] vs_less_vcount[OF snd_list_nth_vertex[OF em]] by auto
  have fin: "out_scanned_seen s a (free_out_hi acyc_flow ! a) ∧ in_scanned_seen s a (free_in_hi acyc_flow ! a)"
    using sc avc aseen ans by (simp add: scan_complete_def)
  from inc show False
  proof
    assume o: "fst_list ! e = a ∧ snd_list ! e = w"
    obtain j where jr: "out_lo ! a ≤ j" "j < free_out_hi acyc_flow ! a" "free_out_edges acyc_flow ! j = e"
      using free_out_edge_in_block[OF em cl _ avc] o by auto
    have "ds_seen s ! (snd_list ! (free_out_edges acyc_flow ! j))"
      using fin jr by (auto simp: out_scanned_seen_def)
    thus False using jr(3) o wns by simp
  next
    assume o: "fst_list ! e = w ∧ snd_list ! e = a"
    obtain j where jr: "in_lo ! a ≤ j" "j < free_in_hi acyc_flow ! a" "free_in_edges acyc_flow ! j = e"
      using free_in_edge_in_block[OF em cl _ avc] o by auto
    have "ds_seen s ! (fst_list ! (free_in_edges acyc_flow ! j))"
      using fin jr by (auto simp: in_scanned_seen_def)
    thus False using jr(3) o wns by simp
  qed
qed

lemma covinv_discover:
  assumes wf: "dfs_wf s" and sz: "dfs_sized s" and sc: "scan_complete s" and ci: "covinv s"
    and spi: "stk_prnt_inv s" and tsi: "tree_seen_inv s"
    and stk: "ds_stk s = (v,oc,ic) # rest"
    and em: "e < m" and free: "is_free acyc_flow e"
    and econn: "(fst_list ! e = v ∧ snd_list ! e = w) ∨ (fst_list ! e = w ∧ snd_list ! e = v)"
    and wns: "¬ ds_seen s ! w" and wvc: "w < vcount"
    and seent: "ds_seen t = (ds_seen s)[w := True]"
    and prntt: "ds_prnt t = (ds_prnt s)[w := v]"
  shows "covinv t"
proof -
  have lseen: "length (ds_seen s) = Suc vcount" and lprnt: "length (ds_prnt s) = Suc vcount"
    using sz by (auto simp: dfs_sized_def)
  have pstept: "pstep t = insert (w, v) (pstep s)"
    by (rule pstep_upd[OF prntt seent wvc wns lseen lprnt])
  have mono: "pstep s ⊆ pstep t" using pstept by auto
  have wvpair: "(w, v) ∈ pstep t" using pstept by simp
  have wl: "w < length (ds_seen s)" using wvc lseen by simp
  have tne: "⋀x. x ≠ w ⟹ ds_seen t ! x = ds_seen s ! x" using seent by (simp add: nth_list_update_neq)
  show ?thesis
    unfolding covinv_def
  proof (intro allI impI)
    fix d assume dm: "d < m" and dfree: "is_free acyc_flow d"
      and sa: "ds_seen t ! (fst_list ! d)" and sb: "ds_seen t ! (snd_list ! d)"
    let ?a = "fst_list ! d" and ?b = "snd_list ! d"
    show "(?a, ?b) ∈ (pstep t)⇧* ∨ (?b, ?a) ∈ (pstep t)⇧*"
    proof (cases "ds_seen s ! ?a ∧ ds_seen s ! ?b")
      case True
      hence "(?a, ?b) ∈ (pstep s)⇧* ∨ (?b, ?a) ∈ (pstep s)⇧*"
        using ci dm dfree by (simp add: covinv_def)
      thus ?thesis using mono rtrancl_mono by blast
    next
      case False
      have aw: "?a = w ∨ ?b = w"
      proof (rule ccontr)
        assume "¬ (?a = w ∨ ?b = w)"
        hence "ds_seen s ! ?a" "ds_seen s ! ?b" using sa sb tne by auto
        thus False using False by simp
      qed
      show ?thesis
      proof (cases "?a = w")
        case aw': True
        show ?thesis
        proof (cases "?b = w")
          case True thus ?thesis using aw' by simp
        next
          case False
          hence sbs: "ds_seen s ! ?b" using sb tne by simp
          have inc: "(fst_list ! d = ?b ∧ snd_list ! d = w) ∨ (fst_list ! d = w ∧ snd_list ! d = ?b)"
            using aw' by simp
          have "?b ∈ fst ` set (ds_stk s)"
            by (rule free_neighbor_on_stack[OF wf sc dm dfree wns sbs inc])
          hence "(v, ?b) ∈ (pstep s)⇧*" by (rule stk_ancestor[OF spi tsi wf stk])
          hence "(v, ?b) ∈ (pstep t)⇧*" using mono rtrancl_mono by blast
          hence "(w, ?b) ∈ (pstep t)⇧*" using wvpair by (simp add: converse_rtrancl_into_rtrancl)
          thus ?thesis using aw' by simp
        qed
      next
        case False
        hence bw: "?b = w" using aw by simp
        have sas: "ds_seen s ! ?a" using sa tne False by simp
        have inc: "(fst_list ! d = ?a ∧ snd_list ! d = w) ∨ (fst_list ! d = w ∧ snd_list ! d = ?a)"
          using bw by simp
        have "?a ∈ fst ` set (ds_stk s)"
          by (rule free_neighbor_on_stack[OF wf sc dm dfree wns sas inc])
        hence "(v, ?a) ∈ (pstep s)⇧*" by (rule stk_ancestor[OF spi tsi wf stk])
        hence "(v, ?a) ∈ (pstep t)⇧*" using mono rtrancl_mono by blast
        hence "(w, ?a) ∈ (pstep t)⇧*" using wvpair by (simp add: converse_rtrancl_into_rtrancl)
        thus ?thesis using bw by simp
      qed
    qed
  qed
qed

lemma covinv_cong:
  assumes s: "ds_seen s = ds_seen t" and p: "ds_prnt s = ds_prnt t" and ci: "covinv s"
  shows "covinv t"
proof -
  have eq: "pstep t = pstep s" using pstep_cong[OF p s] by simp
  show ?thesis using ci unfolding covinv_def eq s .
qed
lemma discover_prnt_eq: "ds_prnt (dfs_discover s v w e) = (ds_prnt s)[w := v]"
  by (simp add: dfs_discover_def Let_def)

lemma bd_upd1_covinv:
  assumes wf: "dfs_wf s" and sz: "dfs_sized s" and sc: "scan_complete s" and ci: "covinv s"
    and spi: "stk_prnt_inv s" and tsi: "tree_seen_inv s" and c: "bd_call1_conds acyc_flow s"
  shows "covinv (bd_upd1 acyc_flow s)"
proof -
  from c obtain v oc ic rest where stk: "ds_stk s = (v,oc,ic) # rest"
    and oclt: "oc < free_out_hi acyc_flow ! v"
    by (auto simp: bd_call1_conds_def split: list.splits prod.splits)
  have vlt: "v < vcount" and oclo: "out_lo ! v ≤ oc" using wf stk by (auto simp: dfs_wf_def)
  define e where "e = free_out_edges acyc_flow ! oc"
  define w where "w = snd_list ! e"
  have fst_e: "fst_list ! e = v" and free_e: "is_free acyc_flow e" and em: "e < m"
    using free_out_edge_fst[OF vlt oclo oclt] by (simp_all add: e_def)
  have wvc: "w < vcount" using Hout_valid[OF vlt oclo oclt] by (simp add: e_def w_def)
  have upd: "bd_upd1 acyc_flow s = (if ds_seen s ! w then s⦇ds_stk := (v, Suc oc, ic) # rest⦈
                                    else dfs_discover (s⦇ds_stk := (v, Suc oc, ic) # rest⦈) v w e)"
    using stk by (simp add: bd_upd1_def e_def w_def Let_def)
  show ?thesis
  proof (cases "ds_seen s ! w")
    case True
    have "covinv (s⦇ds_stk := (v, Suc oc, ic) # rest⦈)"
      by (rule covinv_cong[OF _ _ ci]) simp_all
    thus ?thesis using upd True by simp
  next
    case False
    let ?s1 = "s⦇ds_stk := (v, Suc oc, ic) # rest⦈"
    let ?t = "dfs_discover ?s1 v w e"
    have seent: "ds_seen ?t = (ds_seen s)[w := True]" by (simp add: discover_seen_eq)
    have prntt: "ds_prnt ?t = (ds_prnt s)[w := v]" by (simp add: discover_prnt_eq)
    have econn: "(fst_list ! e = v ∧ snd_list ! e = w) ∨ (fst_list ! e = w ∧ snd_list ! e = v)"
      using fst_e w_def by simp
    have "covinv ?t"
      by (rule covinv_discover[OF wf sz sc ci spi tsi stk em free_e econn False wvc seent prntt])
    thus ?thesis using upd False by simp
  qed
qed

lemma bd_upd2_covinv:
  assumes wf: "dfs_wf s" and sz: "dfs_sized s" and sc: "scan_complete s" and ci: "covinv s"
    and spi: "stk_prnt_inv s" and tsi: "tree_seen_inv s" and c: "bd_call2_conds acyc_flow s"
  shows "covinv (bd_upd2 acyc_flow s)"
proof -
  from c obtain v oc ic rest where stk: "ds_stk s = (v,oc,ic) # rest"
    and iclt: "ic < free_in_hi acyc_flow ! v"
    by (auto simp: bd_call2_conds_def split: list.splits prod.splits)
  have vlt: "v < vcount" and iclo: "in_lo ! v ≤ ic" using wf stk by (auto simp: dfs_wf_def)
  define e where "e = free_in_edges acyc_flow ! ic"
  define w where "w = fst_list ! e"
  have snd_e: "snd_list ! e = v" and free_e: "is_free acyc_flow e" and em: "e < m"
    using free_in_edge_snd[OF vlt iclo iclt] by (simp_all add: e_def)
  have wvc: "w < vcount" using Hin_valid[OF vlt iclo iclt] by (simp add: e_def w_def)
  have upd: "bd_upd2 acyc_flow s = (if ds_seen s ! w then s⦇ds_stk := (v, oc, Suc ic) # rest⦈
                                    else dfs_discover (s⦇ds_stk := (v, oc, Suc ic) # rest⦈) v w e)"
    using stk by (simp add: bd_upd2_def e_def w_def Let_def)
  show ?thesis
  proof (cases "ds_seen s ! w")
    case True
    have "covinv (s⦇ds_stk := (v, oc, Suc ic) # rest⦈)"
      by (rule covinv_cong[OF _ _ ci]) simp_all
    thus ?thesis using upd True by simp
  next
    case False
    let ?s1 = "s⦇ds_stk := (v, oc, Suc ic) # rest⦈"
    let ?t = "dfs_discover ?s1 v w e"
    have seent: "ds_seen ?t = (ds_seen s)[w := True]" by (simp add: discover_seen_eq)
    have prntt: "ds_prnt ?t = (ds_prnt s)[w := v]" by (simp add: discover_prnt_eq)
    have econn: "(fst_list ! e = v ∧ snd_list ! e = w) ∨ (fst_list ! e = w ∧ snd_list ! e = v)"
      using snd_e w_def by simp
    have "covinv ?t"
      by (rule covinv_discover[OF wf sz sc ci spi tsi stk em free_e econn False wvc seent prntt])
    thus ?thesis using upd False by simp
  qed
qed

lemma bd_upd3_covinv:
  assumes ci: "covinv s" and ne: "ds_stk s = (v,oc,ic) # rest"
  shows "covinv (bd_upd3 s)"
proof -
  have e1: "bd_upd3 s = dfs_finish s v rest" using ne by (simp add: bd_upd3_def)
  have e2: "ds_seen (dfs_finish s v rest) = ds_seen s" and e3: "ds_prnt (dfs_finish s v rest) = ds_prnt s"
    by (simp_all add: dfs_finish_def Let_def)
  show ?thesis using covinv_cong[OF e2[symmetric] e3[symmetric] ci] e1 by simp
qed

text ‹Threading covinv (jointly with dfs_inv and scan_complete, which its discover-step needs) through
      build_dfs, open_tree_component (the component-root seed adds no comparability obligation: a seen
      free-neighbour of the fresh root would, by free_neighbor_on_stack + the empty stack, be a
      contradiction), and the two phase folds, giving build_tree_covinv.›

lemma build_dfs_covinv_aux:
  assumes dom: "build_dfs_dom (fl, s)"
  shows "fl = acyc_flow ⟶ dfs_inv fl s ∧ scan_complete s ∧ covinv s ⟶
           dfs_inv fl (build_dfs fl s) ∧ scan_complete (build_dfs fl s) ∧ covinv (build_dfs fl s)"
proof (induct rule: bd_induct[OF dom])
  case IH: (1 fl s)
  show ?case
  proof (intro impI, elim conjE)
    assume fleq: "fl = acyc_flow" and inv: "dfs_inv fl s" and sc: "scan_complete s" and ci: "covinv s"
    have wf: "dfs_wf s" and sz: "dfs_sized s" and tsi: "tree_seen_inv s" and spi: "stk_prnt_inv s"
      using inv by (auto simp: dfs_inv_def)
    show "dfs_inv fl (build_dfs fl s) ∧ scan_complete (build_dfs fl s) ∧ covinv (build_dfs fl s)"
    proof (rule bd_cases[where fl = fl and s = s])
      assume c: "bd_call1_conds fl s"
      have i1: "dfs_inv fl (bd_upd1 fl s)" using bd_upd1_inv[OF inv c] .
      have s1: "scan_complete (bd_upd1 fl s)" using bd_upd1_scan_complete[OF wf sc] c fleq by simp
      have v1: "covinv (bd_upd1 fl s)" using bd_upd1_covinv[OF wf sz sc ci spi tsi] c fleq by simp
      have "build_dfs fl s = build_dfs fl (bd_upd1 fl s)" using IH(1) c by (rule bd_simps(1))
      thus ?thesis using IH(2)[OF c] fleq i1 s1 v1 by simp
    next
      assume c: "bd_call2_conds fl s"
      have i1: "dfs_inv fl (bd_upd2 fl s)" using bd_upd2_inv[OF inv c] .
      have s1: "scan_complete (bd_upd2 fl s)" using bd_upd2_scan_complete[OF wf sc] c fleq by simp
      have v1: "covinv (bd_upd2 fl s)" using bd_upd2_covinv[OF wf sz sc ci spi tsi] c fleq by simp
      have "build_dfs fl s = build_dfs fl (bd_upd2 fl s)" using IH(1) c by (rule bd_simps(2))
      thus ?thesis using IH(3)[OF c] fleq i1 s1 v1 by simp
    next
      assume c: "bd_call3_conds fl s"
      from c obtain v oc ic rest where stk: "ds_stk s = (v,oc,ic) # rest"
        by (auto simp: bd_call3_conds_def split: list.splits prod.splits)
      have i1: "dfs_inv fl (bd_upd3 s)" using bd_upd3_inv[OF inv c] .
      have s1: "scan_complete (bd_upd3 s)" using bd_upd3_scan_complete[OF wf sc] c fleq by simp
      have v1: "covinv (bd_upd3 s)" using bd_upd3_covinv[OF ci stk] .
      have "build_dfs fl s = build_dfs fl (bd_upd3 s)" using IH(1) c by (rule bd_simps(3))
      thus ?thesis using IH(4)[OF c] fleq i1 s1 v1 by simp
    next
      assume c: "bd_ret_conds s"
      have "build_dfs fl s = s" using IH(1) c by (rule bd_simps(4))
      thus ?thesis using inv sc ci by simp
    qed
  qed
qed

lemma build_dfs_covinv:
  assumes inv: "dfs_inv acyc_flow s" and sc: "scan_complete s" and ci: "covinv s"
  shows "covinv (build_dfs acyc_flow s)"
proof -
  have dom: "build_dfs_dom (acyc_flow, s)" using inv by (simp add: dfs_inv_def build_dfs_dom_wf')
  show ?thesis using build_dfs_covinv_aux[OF dom] inv sc ci by simp
qed

lemma open_tree_component_covinv:
  assumes inv: "dfs_inv acyc_flow s" and sc: "scan_complete s" and ci: "covinv s"
    and emp: "ds_stk s = []" and cv: "c < vcount" and unseen: "¬ ds_seen s ! c" and cnz: "c ≠ 0"
  shows "covinv (open_tree_component acyc_flow s c)"
proof -
  define t where "t = (let imb = imbalance ! c; up = 0 ≤ imb; af = ¦imb¦; cp = (if up then af + 1 else af); pv = ds_prev s
    in s⦇ ds_afst := (ds_afst s)[ds_nxt s := (if up then c else vcount)], ds_asnd := (ds_asnd s)[ds_nxt s := (if up then vcount else c)],
          ds_acap := (ds_acap s)[ds_nxt s := cp], ds_aflw := (ds_aflw s)[ds_nxt s := af], ds_aest := (ds_aest s)[ds_nxt s := InTree],
          ds_nxt := Suc (ds_nxt s), ds_seen := (ds_seen s)[c := True], ds_prnt := (ds_prnt s)[c := vcount],
          ds_par := (ds_par s)[c := m + ds_nxt s], ds_dir := (ds_dir s)[c := up], ds_pot := (ds_pot s)[c := (if up then pval_negM else pval_M)],
          ds_thrd := (ds_thrd s)[pv := c], ds_rvth := (ds_rvth s)[c := pv], ds_snum := (ds_snum s)[c := 1], ds_prev := c,
          ds_stk := [(c, out_lo ! c, in_lo ! c)] ⦈)"
  have otc: "open_tree_component acyc_flow s c = build_dfs acyc_flow t"
    by (simp add: open_tree_component_def Let_def t_def)
  have seent: "ds_seen t = (ds_seen s)[c := True]" by (simp add: t_def Let_def)
  have prntt: "ds_prnt t = (ds_prnt s)[c := vcount]" by (simp add: t_def Let_def)
  have stkt: "ds_stk t = [(c, out_lo ! c, in_lo ! c)]" by (simp add: t_def Let_def)
  ― ‹dfs_inv of the seed (same block as open_tree_component_inv)›
  have invt: "dfs_inv acyc_flow t"
    unfolding t_def dfs_inv_def
    apply (intro conjI)
    subgoal using inv cv by (auto simp: dfs_inv_def dfs_wf_def dfs_sized_def tree_seen_inv_def nth_list_update Let_def)
    subgoal using inv cv by (auto simp: dfs_inv_def dfs_wf_def dfs_sized_def tree_seen_inv_def nth_list_update Let_def)
    subgoal using inv cv by (auto simp: dfs_inv_def dfs_wf_def dfs_sized_def tree_seen_inv_def nth_list_update Let_def)
    subgoal apply (rule thread_inv_upd[where s = s and w = c])
      using inv cv unseen cnz by (auto simp: dfs_inv_def dfs_sized_def Let_def)
    subgoal using inv cv by (auto simp: dfs_inv_def dfs_sized_def par_edge_inv_def nth_list_update Let_def)
    subgoal apply (rule pot_inv_seed[where s = s and c = c])
      using inv cv unseen by (auto simp: dfs_inv_def dfs_sized_def nth_list_update Let_def)
    subgoal using inv cv by (auto simp: dfs_inv_def dfs_sized_def root_pot_inv_def nth_list_update Let_def)
    subgoal using inv cv by (auto simp: dfs_inv_def dfs_sized_def stk_prnt_inv_def nth_list_update Let_def)
    subgoal apply (rule emit_ord_inv_seed[where s = s and c = c])
      using inv cv unseen by (auto simp: dfs_inv_def dfs_sized_def Let_def)
    subgoal apply (rule snum_inv_seed[where s = s and c = c])
      using inv cv unseen emp by (auto simp: dfs_inv_def dfs_sized_def Let_def)
    subgoal apply (rule lsuc_inv_seed[where s = s and c = c])
      using inv cv unseen emp by (auto simp: dfs_inv_def dfs_sized_def Let_def)
    done
  have wf: "dfs_wf s" using inv by (simp add: dfs_inv_def)
  have wl: "c < length (ds_seen s)" using cv wf by (simp add: dfs_wf_def)
  have lseen: "length (ds_seen s) = Suc vcount" and lprnt: "length (ds_prnt s) = Suc vcount"
    using inv by (auto simp: dfs_inv_def dfs_sized_def)
  have seen_mono_t: "⋀x. ds_seen s ! x ⟹ ds_seen t ! x"
  proof -
    fix x assume "ds_seen s ! x"
    thus "ds_seen t ! x" using seent wl by (cases "x = c") (auto simp: nth_list_update_eq nth_list_update_neq)
  qed
  have sct: "scan_complete t"
    unfolding scan_complete_def
  proof (intro conjI)
    show "∀(a,b,cc)∈set (ds_stk t). out_scanned_seen t a b ∧ in_scanned_seen t a cc"
      by (auto simp: stkt out_scanned_seen_def in_scanned_seen_def)
  next
    show "∀u<vcount. ds_seen t ! u ∧ u ∉ fst ` set (ds_stk t) ⟶
             out_scanned_seen t u (free_out_hi acyc_flow ! u) ∧ in_scanned_seen t u (free_in_hi acyc_flow ! u)"
    proof (intro allI impI, elim conjE)
      fix u assume ult: "u < vcount" and us1: "ds_seen t ! u" and us2: "u ∉ fst ` set (ds_stk t)"
      have unc: "u ≠ c" using us2 stkt by auto
      have "ds_seen s ! u" using us1 unc seent by (simp add: nth_list_update_neq)
      moreover have "u ∉ fst ` set (ds_stk s)" using emp by simp
      ultimately have "out_scanned_seen s u (free_out_hi acyc_flow ! u) ∧ in_scanned_seen s u (free_in_hi acyc_flow ! u)"
        using sc ult by (auto simp: scan_complete_def)
      thus "out_scanned_seen t u (free_out_hi acyc_flow ! u) ∧ in_scanned_seen t u (free_in_hi acyc_flow ! u)"
        using seen_mono_t by (auto intro: out_scanned_seen_mono in_scanned_seen_mono)
    qed
  qed
  have pstept: "pstep t = insert (c, vcount) (pstep s)"
    by (rule pstep_upd[OF prntt seent cv unseen lseen lprnt])
  have mono: "pstep s ⊆ pstep t" using pstept by auto
  have covt: "covinv t"
    unfolding covinv_def
  proof (intro allI impI)
    fix d assume dm: "d < m" and dfree: "is_free acyc_flow d"
      and sa: "ds_seen t ! (fst_list ! d)" and sb: "ds_seen t ! (snd_list ! d)"
    have tne: "⋀x. x ≠ c ⟹ ds_seen t ! x = ds_seen s ! x" using seent by (simp add: nth_list_update_neq)
    show "(fst_list ! d, snd_list ! d) ∈ (pstep t)⇧* ∨ (snd_list ! d, fst_list ! d) ∈ (pstep t)⇧*"
    proof (cases "ds_seen s ! (fst_list ! d) ∧ ds_seen s ! (snd_list ! d)")
      case True
      hence "(fst_list ! d, snd_list ! d) ∈ (pstep s)⇧* ∨ (snd_list ! d, fst_list ! d) ∈ (pstep s)⇧*"
        using ci dm dfree by (simp add: covinv_def)
      thus ?thesis using mono rtrancl_mono by blast
    next
      case False
      show ?thesis
      proof (cases "fst_list ! d = c")
        case fc: True
        show ?thesis
        proof (cases "snd_list ! d = c")
          case True thus ?thesis using fc by simp
        next
          case False
          hence sbs: "ds_seen s ! (snd_list ! d)" using sb tne by simp
          have "snd_list ! d ∈ fst ` set (ds_stk s)"
            using free_neighbor_on_stack[OF wf sc dm dfree unseen sbs] fc by auto
          thus ?thesis using emp by simp
        qed
      next
        case fnc: False
        have "snd_list ! d = c"
          using False sa sb tne fnc by metis
        moreover have sas: "ds_seen s ! (fst_list ! d)" using sa tne fnc by simp
        ultimately have "fst_list ! d ∈ fst ` set (ds_stk s)"
          using free_neighbor_on_stack[OF wf sc dm dfree unseen sas] by auto
        thus ?thesis using emp by simp
      qed
    qed
  qed
  show ?thesis using otc build_dfs_covinv[OF invt sct covt] by simp
qed

lemma emit_U_edge_covinv:
  assumes "covinv s" shows "covinv (emit_U_edge s v)"
proof (rule covinv_cong[OF _ _ assms])
  show "ds_seen s = ds_seen (emit_U_edge s v)" by (simp add: emit_U_edge_def Let_def)
  show "ds_prnt s = ds_prnt (emit_U_edge s v)" by (simp add: emit_U_edge_def Let_def)
qed

definition cvI :: "'n dfs_state ⇒ bool" where
  "cvI s ⟷ dfs_inv acyc_flow s ∧ scan_complete s ∧ covinv s ∧ ds_stk s = []"

lemma phase1_step_cvI:
  assumes "cvI s" and v: "v ∈ set vs_list"
  shows "cvI (phase1_step acyc_flow v s)"
proof -
  have vc: "v < vcount" using v vs_less_vcount by simp
  have vnz: "v ≠ 0" using v no_zero_node by metis
  have inv: "dfs_inv acyc_flow s" and sc: "scan_complete s" and ci: "covinv s" and emp: "ds_stk s = []"
    using assms(1) by (auto simp: cvI_def)
  have wf: "dfs_wf s" using inv by (simp add: dfs_inv_def)
  show ?thesis
  proof (cases "imbalance ! v = 0")
    case True thus ?thesis using assms(1) by (simp add: phase1_step_def)
  next
    case nz: False
    show ?thesis
    proof (cases "ds_seen s ! v")
      case True
      have "phase1_step acyc_flow v s = emit_U_edge s v" using nz True by (simp add: phase1_step_def)
      thus ?thesis using inv sc ci emp emit_U_edge_inv emit_U_edge_scan_complete emit_U_edge_covinv emit_U_edge_stk
        by (simp add: cvI_def)
    next
      case False
      have "phase1_step acyc_flow v s = open_tree_component acyc_flow s v" using nz False by (simp add: phase1_step_def)
      thus ?thesis
        using open_tree_component_inv[OF inv vc False vnz emp] open_tree_component_full[OF sc wf emp vc]
              open_tree_component_covinv[OF inv sc ci emp vc False vnz]
        by (simp add: cvI_def)
    qed
  qed
qed

lemma phase2_step_cvI:
  assumes "cvI s" and v: "v ∈ set vs_list"
  shows "cvI (phase2_step acyc_flow v s)"
proof -
  have vc: "v < vcount" using v vs_less_vcount by simp
  have vnz: "v ≠ 0" using v no_zero_node by metis
  have inv: "dfs_inv acyc_flow s" and sc: "scan_complete s" and ci: "covinv s" and emp: "ds_stk s = []"
    using assms(1) by (auto simp: cvI_def)
  have wf: "dfs_wf s" using inv by (simp add: dfs_inv_def)
  show ?thesis
  proof (cases "ds_seen s ! v ∨ is_lonely v")
    case True thus ?thesis using assms(1) by (simp add: phase2_step_def)
  next
    case False
    hence notseen: "¬ ds_seen s ! v" and nl: "¬ is_lonely v" by auto
    have "phase2_step acyc_flow v s = open_tree_component acyc_flow s v" using notseen nl by (simp add: phase2_step_def)
    thus ?thesis
      using open_tree_component_inv[OF inv vc notseen vnz emp] open_tree_component_full[OF sc wf emp vc]
            open_tree_component_covinv[OF inv sc ci emp vc notseen vnz]
      by (simp add: cvI_def)
  qed
qed

lemma fold_phase1_cvI: "cvI s ⟹ set xs ⊆ set vs_list ⟹ cvI (fold (phase1_step acyc_flow) xs s)"
  by (induct xs arbitrary: s) (auto simp: phase1_step_cvI)
lemma fold_phase2_cvI: "cvI s ⟹ set xs ⊆ set vs_list ⟹ cvI (fold (phase2_step acyc_flow) xs s)"
  by (induct xs arbitrary: s) (auto simp: phase2_step_cvI)

lemma covinv_dfs_init: "covinv dfs_init"
  unfolding covinv_def
proof (intro allI impI)
  fix e assume em: "e < m" and "is_free acyc_flow e" and se: "ds_seen dfs_init ! (fst_list ! e)"
  have "fst_list ! e < vcount" using vs_less_vcount[OF fst_list_nth_vertex[OF em]] .
  hence "¬ ds_seen dfs_init ! (fst_list ! e)" by (simp add: dfs_init_def del: replicate_Suc)
  thus "(fst_list ! e, snd_list ! e) ∈ (pstep dfs_init)⇧* ∨ (snd_list ! e, fst_list ! e) ∈ (pstep dfs_init)⇧*"
    using se by simp
qed

lemma cvI_dfs_init: "cvI dfs_init"
  unfolding cvI_def
proof (intro conjI)
  show "dfs_inv acyc_flow dfs_init" by (rule dfs_init_inv)
  show "scan_complete dfs_init" by (simp add: dfs_init_def scan_complete_def del: replicate_Suc)
  show "covinv dfs_init" by (rule covinv_dfs_init)
  show "ds_stk dfs_init = []" by (simp add: dfs_init_def)
qed

lemma phase1_cvI: "cvI (phase1 acyc_flow dfs_init)"
  using fold_phase1_cvI[OF cvI_dfs_init] by (simp add: phase1_def)
lemma phase2_cvI: "cvI (phase2 acyc_flow (phase1 acyc_flow dfs_init))"
  using fold_phase2_cvI[OF phase1_cvI] by (simp add: phase2_def)

lemma build_tree_covinv: "covinv (build_tree acyc_flow)"
proof -
  have "covinv (phase2 acyc_flow (phase1 acyc_flow dfs_init))" using phase2_cvI by (simp add: cvI_def)
  thus ?thesis by (simp add: build_tree_def Let_def covinv_def pstep_def)
qed

subsection ‹Free-edge coverage: every free real edge is a tree (parent) edge›

text ‹The payoff of covinv + the walk-builder + the acyclicity engine: an uncovered free real edge e,
      with both endpoints seen (build_tree_spans) and pstep-comparable (build_tree_covinv), would close a
      free residual cycle (the tree chain between its endpoints plus e), contradicting acyclicity. Hence
      e is a parent edge. Needs acyclic_flow (nth acyc_flow), delivered on the Some branch by acyc_of_some.›

lemma redge_in_E: "original_network.oedge a < m ⟹ a ∈ original_network.𝔈"
  by (cases a) (auto simp: original_network.𝔈_def)

lemma cycle_contra:
  assumes acyc: "original_network.acyclic_flow (h ∘ nth acyc_flow)"
    and ab: "(a, b) ∈ (pstep (build_tree acyc_flow))⇧*" and bv: "b < vcount"
    and re_fv: "original_network.fstv re = b" and re_sv: "original_network.sndv re = a"
    and re_oe: "original_network.oedge re = e" and em: "e < m" and free: "is_free acyc_flow e"
    and notcov: "⋀v. v ∈ Vseen ⟹ ds_par (build_tree acyc_flow) ! v ≠ e"
  shows False
proof -
  have reE: "re ∈ original_network.𝔈" using re_oe em by (simp add: redge_in_E)
  have refree: "original_network.oedge re < m ∧ is_free acyc_flow (original_network.oedge re)"
    using re_oe em free by simp
  from pstep_chain_prepath[OF ab bv] show False
  proof
    assume "a = b"
    have cl: "original_network.fstv (hd [re]) = original_network.sndv (last [re])"
      using re_fv re_sv ‹a = b› by simp
    show False
      by (rule free_walk_no_cycle[OF acyc _ _ _ _ op_prepath_single cl])
         (use reE refree in ‹auto›)
  next
    assume "∃C. C ≠ [] ∧ original_network.prepath C
       ∧ original_network.fstv (hd C) = a ∧ original_network.sndv (last C) = b
       ∧ (∀x∈set C. original_network.oedge x < m ∧ is_free acyc_flow (original_network.oedge x))
       ∧ distinct (map original_network.oedge C)
       ∧ (∀e'∈original_network.oedge ` set C. ∃y∈Vseen. e' = ds_par (build_tree acyc_flow) ! y
             ∧ (a,y) ∈ (pstep (build_tree acyc_flow))⇧* ∧ (y,b) ∈ (pstep (build_tree acyc_flow))⇧+)"
    then obtain C where C: "C ≠ []" "original_network.prepath C"
      "original_network.fstv (hd C) = a" "original_network.sndv (last C) = b"
      "∀x∈set C. original_network.oedge x < m ∧ is_free acyc_flow (original_network.oedge x)"
      "distinct (map original_network.oedge C)"
      "∀e'∈original_network.oedge ` set C. ∃y∈Vseen. e' = ds_par (build_tree acyc_flow) ! y
             ∧ (a,y) ∈ (pstep (build_tree acyc_flow))⇧* ∧ (y,b) ∈ (pstep (build_tree acyc_flow))⇧+"
      by blast
    let ?C = "re # C"
    have pp: "original_network.prepath ?C"
      by (rule op_prepath_cons) (use re_sv C(2,3) in simp_all)
    have hd_last: "original_network.fstv (hd ?C) = original_network.sndv (last ?C)"
      using re_fv C(1,4) by simp
    have enotC: "e ∉ original_network.oedge ` set C"
    proof
      assume "e ∈ original_network.oedge ` set C"
      then obtain y where "y ∈ Vseen" "e = ds_par (build_tree acyc_flow) ! y" using C(7) by blast
      thus False using notcov by auto
    qed
    have dist: "distinct (map original_network.oedge ?C)" using C(6) enotC re_oe by simp
    have edges: "⋀x. x ∈ set ?C ⟹ original_network.oedge x < m ∧ is_free acyc_flow (original_network.oedge x)"
      using C(5) refree by auto
    have sub: "set ?C ⊆ original_network.𝔈" using reE C(5) redge_in_E by auto
    show False
      by (rule free_walk_no_cycle[OF acyc _ edges dist sub pp hd_last]) simp
  qed
qed

lemma free_edge_covered:
  assumes acyc: "original_network.acyclic_flow (h ∘ nth acyc_flow)"
    and em: "e < m" and free: "is_free acyc_flow e"
  shows "∃v ∈ Vseen. ds_par (build_tree acyc_flow) ! v = e"
proof (rule ccontr)
  assume nc: "¬ (∃v ∈ Vseen. ds_par (build_tree acyc_flow) ! v = e)"
  hence notcov: "⋀v. v ∈ Vseen ⟹ ds_par (build_tree acyc_flow) ! v ≠ e" by auto
  let ?u = "fst_list ! e" and ?w = "snd_list ! e"
  have ue: "?u ∈ set fst_list" using em by (metis length_fst_list_m nth_mem)
  have we: "?w ∈ set snd_list" using em by (metis length_snd_list_m nth_mem)
  have uV: "?u ∈ Vseen" and wV: "?w ∈ Vseen" using ue we Vseen_eq_V V_orig_eq by auto
  have uv: "?u < vcount" and wv: "?w < vcount" using uV wV by (auto simp: Vseen_def)
  have us: "ds_seen (build_tree acyc_flow) ! ?u" and ws: "ds_seen (build_tree acyc_flow) ! ?w"
    using uV wV by (auto simp: Vseen_def)
  have cmp: "(?u, ?w) ∈ (pstep (build_tree acyc_flow))⇧* ∨ (?w, ?u) ∈ (pstep (build_tree acyc_flow))⇧*"
    using build_tree_covinv em free us ws by (simp add: covinv_def)
  have fF: "original_network.fstv (F e) = ?u" and sF: "original_network.sndv (F e) = ?w"
    and fB: "original_network.fstv (B e) = ?w" and sB: "original_network.sndv (B e) = ?u"
    using em by (simp_all add: cr_fstv_F cr_sndv_F cr_fstv_B cr_sndv_B)
  from cmp show False
  proof
    assume "(?u, ?w) ∈ (pstep (build_tree acyc_flow))⇧*"
    show False
      by (rule cycle_contra[OF acyc ‹(?u,?w)∈_› wv fB sB _ em free notcov]) simp
  next
    assume "(?w, ?u) ∈ (pstep (build_tree acyc_flow))⇧*"
    show False
      by (rule cycle_contra[OF acyc ‹(?w,?u)∈_› uv fF sF _ em free notcov]) simp
  qed
qed

subsection ‹Artificial-edge reverse coverage: every artificial InTree edge is a component-root's edge›

text ‹art_owned: for every emitted artificial slot k with tag InTree there is a component root c
      (‹ds_prnt c = vcount›) whose parent edge is exactly that slot (‹ds_par c = m + k›). This is the
      reverse of cr_ext_inv and completes InTree ⊆ T for the artificial range. Threaded like the forward
      cr_ext machinery: build_dfs adds no InTree artificial edge and freezes seen roots
      (build_dfs_seen_frozen — the forward field-freeze proved here), open_tree_component installs the new
      root's witness, emit_U_edge only adds an InU edge, and the two phase folds carry it with the same
      ds_nxt ≤ length vs_list bound (card of a seen-vertex witness set).›

lemma bd_upd1_seen_frozen:
  assumes wf: "dfs_wf s" and c: "bd_call1_conds fl s" and sx: "ds_seen s ! x"
  shows "ds_prnt (bd_upd1 fl s) ! x = ds_prnt s ! x ∧ ds_par (bd_upd1 fl s) ! x = ds_par s ! x"
proof -
  from c obtain v oc ic rest where stk: "ds_stk s = (v,oc,ic) # rest"
    by (auto simp: bd_call1_conds_def split: list.splits prod.splits)
  let ?e = "free_out_edges fl ! oc" let ?w = "snd_list ! ?e"
  have upd: "bd_upd1 fl s = (if ds_seen s ! ?w then s⦇ds_stk := (v, Suc oc, ic) # rest⦈
                            else dfs_discover (s⦇ds_stk := (v, Suc oc, ic) # rest⦈) v ?w ?e)"
    using stk by (simp add: bd_upd1_def Let_def)
  show ?thesis
  proof (cases "ds_seen s ! ?w")
    case True thus ?thesis using upd by simp
  next
    case False
    hence xnw: "x ≠ ?w" using sx by auto
    show ?thesis using upd False xnw by (simp add: dfs_discover_def Let_def nth_list_update_neq)
  qed
qed

lemma bd_upd2_seen_frozen:
  assumes wf: "dfs_wf s" and c: "bd_call2_conds fl s" and sx: "ds_seen s ! x"
  shows "ds_prnt (bd_upd2 fl s) ! x = ds_prnt s ! x ∧ ds_par (bd_upd2 fl s) ! x = ds_par s ! x"
proof -
  from c obtain v oc ic rest where stk: "ds_stk s = (v,oc,ic) # rest"
    by (auto simp: bd_call2_conds_def split: list.splits prod.splits)
  let ?e = "free_in_edges fl ! ic" let ?w = "fst_list ! ?e"
  have upd: "bd_upd2 fl s = (if ds_seen s ! ?w then s⦇ds_stk := (v, oc, Suc ic) # rest⦈
                            else dfs_discover (s⦇ds_stk := (v, oc, Suc ic) # rest⦈) v ?w ?e)"
    using stk by (simp add: bd_upd2_def Let_def)
  show ?thesis
  proof (cases "ds_seen s ! ?w")
    case True thus ?thesis using upd by simp
  next
    case False
    hence xnw: "x ≠ ?w" using sx by auto
    show ?thesis using upd False xnw by (simp add: dfs_discover_def Let_def nth_list_update_neq)
  qed
qed

lemma bd_upd3_seen_frozen:
  assumes c: "bd_call3_conds fl s"
  shows "ds_prnt (bd_upd3 s) ! x = ds_prnt s ! x ∧ ds_par (bd_upd3 s) ! x = ds_par s ! x"
proof -
  from c obtain v oc ic rest where stk: "ds_stk s = (v,oc,ic) # rest"
    by (auto simp: bd_call3_conds_def split: list.splits prod.splits)
  have "bd_upd3 s = dfs_finish s v rest" using stk by (simp add: bd_upd3_def)
  thus ?thesis by (simp add: dfs_finish_def Let_def)
qed

lemma build_dfs_seen_frozen:
  assumes dom: "build_dfs_dom (fl, s)"
  shows "dfs_inv fl s ⟶ ds_seen s ! x ⟶
           ds_prnt (build_dfs fl s) ! x = ds_prnt s ! x ∧ ds_par (build_dfs fl s) ! x = ds_par s ! x"
proof (induct rule: bd_induct[OF dom])
  case IH: (1 fl s)
  show ?case
  proof (intro impI)
    assume inv: "dfs_inv fl s" and sx: "ds_seen s ! x"
    have wf: "dfs_wf s" using inv by (simp add: dfs_inv_def)
    show "ds_prnt (build_dfs fl s) ! x = ds_prnt s ! x ∧ ds_par (build_dfs fl s) ! x = ds_par s ! x"
    proof (rule bd_cases[where fl = fl and s = s])
      assume c: "bd_call1_conds fl s"
      have fr: "ds_prnt (bd_upd1 fl s) ! x = ds_prnt s ! x ∧ ds_par (bd_upd1 fl s) ! x = ds_par s ! x"
        by (rule bd_upd1_seen_frozen[OF wf c sx])
      have sx1: "ds_seen (bd_upd1 fl s) ! x" using bd_upd1_seen_mono[OF c sx] .
      have "build_dfs fl s = build_dfs fl (bd_upd1 fl s)" using IH(1) c by (rule bd_simps(1))
      thus ?thesis using IH(2)[OF c] bd_upd1_inv[OF inv c] sx1 fr by simp
    next
      assume c: "bd_call2_conds fl s"
      have fr: "ds_prnt (bd_upd2 fl s) ! x = ds_prnt s ! x ∧ ds_par (bd_upd2 fl s) ! x = ds_par s ! x"
        by (rule bd_upd2_seen_frozen[OF wf c sx])
      have sx1: "ds_seen (bd_upd2 fl s) ! x" using bd_upd2_seen_mono[OF c sx] .
      have "build_dfs fl s = build_dfs fl (bd_upd2 fl s)" using IH(1) c by (rule bd_simps(2))
      thus ?thesis using IH(3)[OF c] bd_upd2_inv[OF inv c] sx1 fr by simp
    next
      assume c: "bd_call3_conds fl s"
      have fr: "ds_prnt (bd_upd3 s) ! x = ds_prnt s ! x ∧ ds_par (bd_upd3 s) ! x = ds_par s ! x"
        by (rule bd_upd3_seen_frozen[OF c])
      have sx1: "ds_seen (bd_upd3 s) ! x" using bd_upd3_seen_mono[OF c sx] .
      have "build_dfs fl s = build_dfs fl (bd_upd3 s)" using IH(1) c by (rule bd_simps(3))
      thus ?thesis using IH(4)[OF c] bd_upd3_inv[OF inv c] sx1 fr by simp
    next
      assume c: "bd_ret_conds s"
      have "build_dfs fl s = s" using IH(1) c by (rule bd_simps(4))
      thus ?thesis by simp
    qed
  qed
qed

definition art_owned :: "'n dfs_state ⇒ bool" where
  "art_owned s ⟷ (∀k < ds_nxt s. ds_aest s ! k = InTree ⟶
      (∃c<vcount. ds_seen s ! c ∧ ds_prnt s ! c = vcount ∧ ds_par s ! c = m + k))"

lemma build_dfs_art_owned:
  assumes dom: "build_dfs_dom (fl, s)" and inv: "dfs_inv fl s" and ao: "art_owned s"
  shows "art_owned (build_dfs fl s)"
proof -
  have aest: "ds_aest (build_dfs fl s) = ds_aest s" and nxt: "ds_nxt (build_dfs fl s) = ds_nxt s"
    using build_dfs_art[of fl s] dom by simp_all
  show ?thesis
    unfolding art_owned_def
  proof (intro allI impI)
    fix k assume klt: "k < ds_nxt (build_dfs fl s)" and kIT: "ds_aest (build_dfs fl s) ! k = InTree"
    have ks: "k < ds_nxt s" using klt nxt by simp
    have kITs: "ds_aest s ! k = InTree" using kIT aest by simp
    obtain c where c: "c < vcount" "ds_seen s ! c" "ds_prnt s ! c = vcount" "ds_par s ! c = m + k"
      using ao ks kITs by (auto simp: art_owned_def)
    have scb: "ds_seen (build_dfs fl s) ! c" using build_dfs_seen_mono[OF dom c(2)] .
    have "ds_prnt (build_dfs fl s) ! c = ds_prnt s ! c ∧ ds_par (build_dfs fl s) ! c = ds_par s ! c"
      using build_dfs_seen_frozen[OF dom] inv c(2) by simp
    hence "ds_prnt (build_dfs fl s) ! c = vcount" "ds_par (build_dfs fl s) ! c = m + k"
      using c(3,4) by simp_all
    thus "∃c<vcount. ds_seen (build_dfs fl s) ! c ∧ ds_prnt (build_dfs fl s) ! c = vcount ∧ ds_par (build_dfs fl s) ! c = m + k"
      using c(1) scb by blast
  qed
qed

lemma emit_U_edge_art_owned:
  assumes ao: "art_owned s" and al: "art_len s" and inb: "ds_nxt s < length vs_list"
  shows "art_owned (emit_U_edge s v)"
proof -
  have laest: "length (ds_aest s) = length vs_list" using al by (simp add: art_len_def)
  have seq: "ds_seen (emit_U_edge s v) = ds_seen s" "ds_prnt (emit_U_edge s v) = ds_prnt s"
       "ds_par (emit_U_edge s v) = ds_par s"
    by (simp_all add: emit_U_edge_def Let_def)
  show ?thesis
    unfolding art_owned_def
  proof (intro allI impI)
    fix k assume klt: "k < ds_nxt (emit_U_edge s v)" and kIT: "ds_aest (emit_U_edge s v) ! k = InTree"
    have klt': "k < Suc (ds_nxt s)" using klt by (simp add: emit_U_edge_nxt)
    have "k < ds_nxt s"
    proof (rule ccontr)
      assume "¬ k < ds_nxt s"
      hence keq: "k = ds_nxt s" using klt' by simp
      have "ds_aest (emit_U_edge s v) ! k = InU"
        using keq inb laest by (simp add: emit_U_edge_def Let_def nth_list_update_eq)
      thus False using kIT by simp
    qed
    hence ks: "k < ds_nxt s" .
    have kITs: "ds_aest s ! k = InTree"
      using kIT ks by (simp add: emit_U_edge_def Let_def nth_list_update_neq)
    obtain c where c: "c < vcount" "ds_seen s ! c" "ds_prnt s ! c = vcount" "ds_par s ! c = m + k"
      using ao ks kITs by (auto simp: art_owned_def)
    show "∃c<vcount. ds_seen (emit_U_edge s v) ! c ∧ ds_prnt (emit_U_edge s v) ! c = vcount ∧ ds_par (emit_U_edge s v) ! c = m + k"
      using c seq by auto
  qed
qed

lemma open_tree_component_art_owned:
  assumes inv: "dfs_inv acyc_flow s" and ao: "art_owned s" and c: "c < vcount"
    and unseen: "¬ ds_seen s ! c" and cnz: "c ≠ 0" and stke: "ds_stk s = []"
    and al: "art_len s" and inb: "ds_nxt s < length vs_list"
  shows "art_owned (open_tree_component acyc_flow s c)"
proof -
  obtain sd where opd: "open_tree_component acyc_flow s c = build_dfs acyc_flow sd"
      and invsd: "dfs_inv acyc_flow sd" and nxtsd: "ds_nxt sd = Suc (ds_nxt s)"
      and seensd: "ds_seen sd = (ds_seen s)[c := True]" and prntsd: "ds_prnt sd = (ds_prnt s)[c := vcount]"
      and parsd: "ds_par sd = (ds_par s)[c := m + ds_nxt s]" and aestsd: "ds_aest sd = (ds_aest s)[ds_nxt s := InTree]"
    using otc_seed[OF inv c unseen cnz stke] .
  have dom: "build_dfs_dom (acyc_flow, sd)" using invsd by (simp add: dfs_inv_def build_dfs_dom_wf')
  have lseen: "length (ds_seen s) = Suc vcount" and lprnt: "length (ds_prnt s) = Suc vcount"
       and lpar: "length (ds_par s) = Suc vcount" using inv by (simp_all add: dfs_inv_def dfs_sized_def)
  have laest: "length (ds_aest s) = length vs_list" using al by (simp add: art_len_def)
  have aosd: "art_owned sd"
    unfolding art_owned_def
  proof (intro allI impI)
    fix k assume klt: "k < ds_nxt sd" and kIT: "ds_aest sd ! k = InTree"
    have klt': "k < Suc (ds_nxt s)" using klt nxtsd by simp
    show "∃c'<vcount. ds_seen sd ! c' ∧ ds_prnt sd ! c' = vcount ∧ ds_par sd ! c' = m + k"
    proof (cases "k = ds_nxt s")
      case True
      have "ds_seen sd ! c ∧ ds_prnt sd ! c = vcount ∧ ds_par sd ! c = m + k"
        using seensd prntsd parsd True c lseen lprnt lpar by (simp add: nth_list_update_eq)
      thus ?thesis using c by blast
    next
      case False
      hence ks: "k < ds_nxt s" using klt' by simp
      have kITs: "ds_aest s ! k = InTree" using kIT aestsd False by (simp add: nth_list_update_neq)
      obtain c0 where c0: "c0 < vcount" "ds_seen s ! c0" "ds_prnt s ! c0 = vcount" "ds_par s ! c0 = m + k"
        using ao ks kITs by (auto simp: art_owned_def)
      have c0nc: "c0 ≠ c" using c0(2) unseen by auto
      have "ds_seen sd ! c0 ∧ ds_prnt sd ! c0 = vcount ∧ ds_par sd ! c0 = m + k"
        using seensd prntsd parsd c0 c0nc by (simp add: nth_list_update_neq)
      thus ?thesis using c0(1) by blast
    qed
  qed
  show ?thesis using opd build_dfs_art_owned[OF dom invsd aosd] by simp
qed

lemma phase1_step_art_owned:
  assumes v: "v ∈ set vs_list" and inv: "dfs_inv acyc_flow s" and stke: "ds_stk s = []" and al: "art_len s"
      and ao: "art_owned s" and inb: "ds_nxt (phase1_step acyc_flow v s) ≤ length vs_list"
  shows "art_owned (phase1_step acyc_flow v s)"
proof (cases "imbalance ! v = 0")
  case True thus ?thesis using ao by (simp add: phase1_step_def)
next
  case nz: False
  have vlt: "v < vcount" using v vs_less_vcount by simp
  show ?thesis
  proof (cases "ds_seen s ! v")
    case seen: True
    have eq: "phase1_step acyc_flow v s = emit_U_edge s v" using nz seen by (simp add: phase1_step_def)
    have inbs: "ds_nxt s < length vs_list" using inb eq by (simp add: emit_U_edge_nxt)
    thus ?thesis using eq emit_U_edge_art_owned[OF ao al inbs] by simp
  next
    case notseen: False
    have vnz: "v ≠ 0" using v no_zero_node by metis
    have eq: "phase1_step acyc_flow v s = open_tree_component acyc_flow s v" using nz notseen by (simp add: phase1_step_def)
    have nxt: "ds_nxt (open_tree_component acyc_flow s v) = Suc (ds_nxt s)" using open_tree_component_nxt[OF inv vlt] .
    have inbs: "ds_nxt s < length vs_list" using inb eq nxt by simp
    show ?thesis using eq open_tree_component_art_owned[OF inv ao vlt notseen vnz stke al inbs] by simp
  qed
qed

lemma phase2_step_art_owned:
  assumes v: "v ∈ set vs_list" and inv: "dfs_inv acyc_flow s" and stke: "ds_stk s = []" and al: "art_len s"
      and ao: "art_owned s" and inb: "ds_nxt (phase2_step acyc_flow v s) ≤ length vs_list"
  shows "art_owned (phase2_step acyc_flow v s)"
proof (cases "ds_seen s ! v ∨ is_lonely v")
  case True thus ?thesis using ao by (simp add: phase2_step_def)
next
  case False
  hence notseen: "¬ ds_seen s ! v" and nl: "¬ is_lonely v" by auto
  have vlt: "v < vcount" using v vs_less_vcount by simp
  have vnz: "v ≠ 0" using v no_zero_node by metis
  have eq: "phase2_step acyc_flow v s = open_tree_component acyc_flow s v" using notseen nl by (simp add: phase2_step_def)
  have nxt: "ds_nxt (open_tree_component acyc_flow s v) = Suc (ds_nxt s)" using open_tree_component_nxt[OF inv vlt] .
  have inbs: "ds_nxt s < length vs_list" using inb eq nxt by simp
  show ?thesis using eq open_tree_component_art_owned[OF inv ao vlt notseen vnz stke al inbs] by simp
qed

lemma fold_phase1_art_owned:
  assumes "distinct xs" "set xs ⊆ set vs_list" "dfs_inv acyc_flow s" "ds_stk s = []"
      "art_len s" "art_owned s"
      "finite E" "E ⊆ {v ∈ set vs_list. ds_seen s ! v}" "E ∩ set xs = {}" "ds_nxt s = card E"
  shows "art_len (fold (phase1_step acyc_flow) xs s) ∧ art_owned (fold (phase1_step acyc_flow) xs s)
         ∧ (∃E'. finite E' ∧ E' ⊆ {v ∈ set vs_list. ds_seen (fold (phase1_step acyc_flow) xs s) ! v}
                 ∧ ds_nxt (fold (phase1_step acyc_flow) xs s) = card E')"
  using assms
proof (induct xs arbitrary: s E)
  case Nil thus ?case by auto
next
  case (Cons x rest)
  have xvs: "x ∈ set vs_list" using Cons.prems(2) by simp
  have xlt: "x < vcount" using xvs vs_less_vcount by simp
  have inv1: "dfs_inv acyc_flow (phase1_step acyc_flow x s)" "ds_stk (phase1_step acyc_flow x s) = []"
    using phase1_step_inv[OF xvs conjI[OF Cons.prems(3) Cons.prems(4)]] by auto
  have al1: "art_len (phase1_step acyc_flow x s)" using phase1_step_art_len[OF xvs Cons.prems(3) Cons.prems(5)] .
  have Emono: "E ⊆ {v ∈ set vs_list. ds_seen (phase1_step acyc_flow x s) ! v}"
    using Cons.prems(8) phase1_step_seen_mono[OF Cons.prems(3) xlt] by auto
  have Edisj: "E ∩ set rest = {}" using Cons.prems(9) by auto
  have distr: "distinct rest" using Cons.prems(1) by simp
  have subr: "set rest ⊆ set vs_list" using Cons.prems(2) by simp
  have Esub: "E ⊆ set vs_list" using Cons.prems(8) by auto
  have xnotE: "x ∉ E" using Cons.prems(9) by auto
  have step_inb: "ds_nxt (phase1_step acyc_flow x s) ≤ length vs_list"
    using phase1_step_nxt[OF Cons.prems(3) xlt]
  proof
    assume "ds_nxt (phase1_step acyc_flow x s) = ds_nxt s"
    thus ?thesis using Cons.prems(10) card_sub_vs_le[OF Esub] by simp
  next
    assume A: "ds_nxt (phase1_step acyc_flow x s) = Suc (ds_nxt s) ∧ ds_seen (phase1_step acyc_flow x s) ! x"
    have "insert x E ⊆ set vs_list" using Esub xvs by auto
    hence "card (insert x E) ≤ length vs_list" by (rule card_sub_vs_le)
    thus ?thesis using A Cons.prems(10) xnotE Cons.prems(7) by (simp add: card_insert_disjoint)
  qed
  have ao1: "art_owned (phase1_step acyc_flow x s)"
    using phase1_step_art_owned[OF xvs Cons.prems(3) Cons.prems(4) Cons.prems(5) Cons.prems(6) step_inb] .
  from phase1_step_nxt[OF Cons.prems(3) xlt] show ?case
  proof
    assume A: "ds_nxt (phase1_step acyc_flow x s) = ds_nxt s"
    have card1: "ds_nxt (phase1_step acyc_flow x s) = card E" using A Cons.prems(10) by simp
    show ?thesis
      using Cons.hyps[OF distr subr inv1(1) inv1(2) al1 ao1 Cons.prems(7) Emono Edisj card1] by simp
  next
    assume B: "ds_nxt (phase1_step acyc_flow x s) = Suc (ds_nxt s) ∧ ds_seen (phase1_step acyc_flow x s) ! x"
    define E2 where "E2 = insert x E"
    have fin2: "finite E2" using Cons.prems(7) by (simp add: E2_def)
    have E2seen: "E2 ⊆ {v ∈ set vs_list. ds_seen (phase1_step acyc_flow x s) ! v}" using Emono B xvs by (auto simp: E2_def)
    have E2disj: "E2 ∩ set rest = {}" using Edisj Cons.prems(1) by (auto simp: E2_def)
    have card2: "ds_nxt (phase1_step acyc_flow x s) = card E2" using B Cons.prems(10) xnotE Cons.prems(7) by (simp add: E2_def card_insert_disjoint)
    show ?thesis using Cons.hyps[OF distr subr inv1(1) inv1(2) al1 ao1 fin2 E2seen E2disj card2] by simp
  qed
qed

lemma fold_phase2_art_owned:
  assumes "set xs ⊆ set vs_list" "dfs_inv acyc_flow s" "ds_stk s = []"
      "art_len s" "art_owned s"
      "finite E" "E ⊆ {v ∈ set vs_list. ds_seen s ! v}" "ds_nxt s = card E"
  shows "art_len (fold (phase2_step acyc_flow) xs s) ∧ art_owned (fold (phase2_step acyc_flow) xs s)
         ∧ (∃E'. finite E' ∧ E' ⊆ {v ∈ set vs_list. ds_seen (fold (phase2_step acyc_flow) xs s) ! v}
                 ∧ ds_nxt (fold (phase2_step acyc_flow) xs s) = card E')"
  using assms
proof (induct xs arbitrary: s E)
  case Nil thus ?case by auto
next
  case (Cons x rest)
  have xvs: "x ∈ set vs_list" using Cons.prems(1) by simp
  have xlt: "x < vcount" using xvs vs_less_vcount by simp
  have inv1: "dfs_inv acyc_flow (phase2_step acyc_flow x s)" "ds_stk (phase2_step acyc_flow x s) = []"
    using phase2_step_inv[OF xvs conjI[OF Cons.prems(2) Cons.prems(3)]] by auto
  have al1: "art_len (phase2_step acyc_flow x s)" using phase2_step_art_len[OF xvs Cons.prems(2) Cons.prems(4)] .
  have Emono: "E ⊆ {v ∈ set vs_list. ds_seen (phase2_step acyc_flow x s) ! v}"
    using Cons.prems(7) phase2_step_seen_mono[OF Cons.prems(2) xlt] by auto
  have subr: "set rest ⊆ set vs_list" using Cons.prems(1) by simp
  have Esub: "E ⊆ set vs_list" using Cons.prems(7) by auto
  have step_inb: "ds_nxt (phase2_step acyc_flow x s) ≤ length vs_list"
    using phase2_step_nxt2[OF Cons.prems(2) xlt]
  proof
    assume "ds_nxt (phase2_step acyc_flow x s) = ds_nxt s"
    thus ?thesis using Cons.prems(8) card_sub_vs_le[OF Esub] by simp
  next
    assume A: "ds_nxt (phase2_step acyc_flow x s) = Suc (ds_nxt s) ∧ ¬ ds_seen s ! x ∧ ds_seen (phase2_step acyc_flow x s) ! x"
    have xnotE: "x ∉ E" using A Cons.prems(7) by auto
    have "insert x E ⊆ set vs_list" using Esub xvs by auto
    hence "card (insert x E) ≤ length vs_list" by (rule card_sub_vs_le)
    thus ?thesis using A Cons.prems(8) xnotE Cons.prems(6) by (simp add: card_insert_disjoint)
  qed
  have ao1: "art_owned (phase2_step acyc_flow x s)"
    using phase2_step_art_owned[OF xvs Cons.prems(2) Cons.prems(3) Cons.prems(4) Cons.prems(5) step_inb] .
  from phase2_step_nxt2[OF Cons.prems(2) xlt] show ?case
  proof
    assume A: "ds_nxt (phase2_step acyc_flow x s) = ds_nxt s"
    have card1: "ds_nxt (phase2_step acyc_flow x s) = card E" using A Cons.prems(8) by simp
    show ?thesis
      using Cons.hyps[OF subr inv1(1) inv1(2) al1 ao1 Cons.prems(6) Emono card1] by simp
  next
    assume B: "ds_nxt (phase2_step acyc_flow x s) = Suc (ds_nxt s) ∧ ¬ ds_seen s ! x ∧ ds_seen (phase2_step acyc_flow x s) ! x"
    have xnotE: "x ∉ E" using B Cons.prems(7) by auto
    define E2 where "E2 = insert x E"
    have fin2: "finite E2" using Cons.prems(6) by (simp add: E2_def)
    have E2seen: "E2 ⊆ {v ∈ set vs_list. ds_seen (phase2_step acyc_flow x s) ! v}" using Emono B xvs by (auto simp: E2_def)
    have card2: "ds_nxt (phase2_step acyc_flow x s) = card E2" using B Cons.prems(8) xnotE Cons.prems(6) by (simp add: E2_def card_insert_disjoint)
    show ?thesis using Cons.hyps[OF subr inv1(1) inv1(2) al1 ao1 fin2 E2seen card2] by simp
  qed
qed

lemma art_owned_dfs_init: "art_owned dfs_init"
  by (simp add: art_owned_def dfs_init_def)

lemma build_tree_art_owned: "art_owned (build_tree acyc_flow)"
proof -
  have i0: "dfs_inv acyc_flow dfs_init ∧ ds_stk dfs_init = []" using dfs_init_inv by (simp add: dfs_init_def)
  have al0: "art_len dfs_init" by (rule dfs_init_art_len)
  have C1: "art_len (fold (phase1_step acyc_flow) vs_list dfs_init) ∧ art_owned (fold (phase1_step acyc_flow) vs_list dfs_init)
        ∧ (∃E'. finite E' ∧ E' ⊆ {v ∈ set vs_list. ds_seen (fold (phase1_step acyc_flow) vs_list dfs_init) ! v}
                ∧ ds_nxt (fold (phase1_step acyc_flow) vs_list dfs_init) = card E')"
    apply (rule fold_phase1_art_owned[where E="{}"])
    subgoal by (rule distinct_vs_list)
    subgoal by simp
    subgoal using i0 by simp
    subgoal using i0 by simp
    subgoal by (rule al0)
    subgoal by (rule art_owned_dfs_init)
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by (simp add: dfs_init_def)
    done
  have P1: "art_len (phase1 acyc_flow dfs_init)" using C1 by (simp add: phase1_def)
  have AO1: "art_owned (phase1 acyc_flow dfs_init)" using C1 by (simp add: phase1_def)
  have E1ex: "∃E'. finite E' ∧ E' ⊆ {v ∈ set vs_list. ds_seen (phase1 acyc_flow dfs_init) ! v}
                ∧ ds_nxt (phase1 acyc_flow dfs_init) = card E'" using C1 by (simp add: phase1_def)
  have p1inv: "dfs_inv acyc_flow (phase1 acyc_flow dfs_init) ∧ ds_stk (phase1 acyc_flow dfs_init) = []" using phase1_inv[OF i0] .
  obtain E1 where E1f: "finite E1" and E1s: "E1 ⊆ {v ∈ set vs_list. ds_seen (phase1 acyc_flow dfs_init) ! v}"
    and E1n: "ds_nxt (phase1 acyc_flow dfs_init) = card E1" using E1ex by blast
  have C2: "art_len (fold (phase2_step acyc_flow) vs_list (phase1 acyc_flow dfs_init))
        ∧ art_owned (fold (phase2_step acyc_flow) vs_list (phase1 acyc_flow dfs_init))
        ∧ (∃E'. finite E' ∧ E' ⊆ {v ∈ set vs_list. ds_seen (fold (phase2_step acyc_flow) vs_list (phase1 acyc_flow dfs_init)) ! v}
                ∧ ds_nxt (fold (phase2_step acyc_flow) vs_list (phase1 acyc_flow dfs_init)) = card E')"
    apply (rule fold_phase2_art_owned[where E=E1 and s="phase1 acyc_flow dfs_init"])
    subgoal by simp
    subgoal using p1inv by simp
    subgoal using p1inv by simp
    subgoal by (rule P1)
    subgoal by (rule AO1)
    subgoal by (rule E1f)
    subgoal by (rule E1s)
    subgoal by (rule E1n)
    done
  have "art_owned (phase2 acyc_flow (phase1 acyc_flow dfs_init))" using C2 by (simp add: phase2_def)
  thus ?thesis by (simp add: build_tree_def Let_def art_owned_def)
qed

subsection ‹The tree edges are exactly the InTree edges (real coverage + artificial coverage)›

lemma InTree_subseteq_T:
  assumes acyc: "original_network.acyclic_flow (h ∘ nth acyc_flow)"
  shows "{e ∈ {0..<m + Kart}. state_all ! e = InTree}
           ⊆ (!) (ds_par (build_tree acyc_flow)) ` (NS.𝒱 - {vcount})"
proof
  fix e assume "e ∈ {e ∈ {0..<m + Kart}. state_all ! e = InTree}"
  hence e: "e < m + Kart" and st: "state_all ! e = InTree" by auto
  show "e ∈ (!) (ds_par (build_tree acyc_flow)) ` (NS.𝒱 - {vcount})"
  proof (cases "e < m")
    case True
    have "edge_state acyc_flow ! e = InTree" using st state_all_real[OF True] by simp
    hence free: "is_free acyc_flow e" by (simp add: is_free_def)
    obtain v where v: "v ∈ Vseen" and pe: "ds_par (build_tree acyc_flow) ! v = e"
      using free_edge_covered[OF acyc True free] by blast
    have vS: "v ∈ NS.𝒱 - {vcount}" using v NS_V_minus_root by simp
    have "ds_par (build_tree acyc_flow) ! v ∈ (!) (ds_par (build_tree acyc_flow)) ` (NS.𝒱 - {vcount})"
      using vS by (rule imageI)
    thus ?thesis using pe by simp
  next
    case False
    then obtain k where ek: "e = m + k" by (metis add.commute le_Suc_ex not_less)
    have kK: "k < Kart" using e ek by simp
    have kn: "k < ds_nxt (build_tree acyc_flow)" using kK by (simp add: Kart_def)
    have "ds_aest (build_tree acyc_flow) ! k = InTree" using st ek kK state_all_art by simp
    then obtain c where c: "c < vcount" "ds_seen (build_tree acyc_flow) ! c"
        "ds_par (build_tree acyc_flow) ! c = m + k"
      using build_tree_art_owned kn by (auto simp: art_owned_def)
    have cV: "c ∈ Vseen" using c(1,2) by (simp add: Vseen_def)
    have cS: "c ∈ NS.𝒱 - {vcount}" using cV NS_V_minus_root by simp
    have "ds_par (build_tree acyc_flow) ! c ∈ (!) (ds_par (build_tree acyc_flow)) ` (NS.𝒱 - {vcount})"
      using cS by (rule imageI)
    thus ?thesis using c(3) ek by simp
  qed
qed

lemma T_eq_InTree:
  assumes acyc: "original_network.acyclic_flow (h ∘ nth acyc_flow)"
  shows "(!) (ds_par (build_tree acyc_flow)) ` (NS.𝒱 - {vcount}) = {e ∈ {0..<m + Kart}. state_all ! e = InTree}"
  using T_sub_InTree InTree_subseteq_T[OF acyc] by blast

subsection ‹The spanning-tree partition: edge cover and tag disjointness›

lemma edge_partition:
  assumes acyc: "original_network.acyclic_flow (h ∘ nth acyc_flow)"
  shows "{0..<m + Kart} =
           (!) (ds_par (build_tree acyc_flow)) ` (NS.𝒱 - {vcount})
           ∪ {e ∈ {0..<m + Kart}. state_all ! e = InU}
           ∪ {e ∈ {0..<m + Kart}. state_all ! e = InL}"
proof -
  have T: "(!) (ds_par (build_tree acyc_flow)) ` (NS.𝒱 - {vcount}) = {e ∈ {0..<m + Kart}. state_all ! e = InTree}"
    by (rule T_eq_InTree[OF acyc])
  show ?thesis unfolding T by (auto dest: state_total)
qed

lemma part_disj:
  assumes acyc: "original_network.acyclic_flow (h ∘ nth acyc_flow)"
  shows "(!) (ds_par (build_tree acyc_flow)) ` (NS.𝒱 - {vcount}) ∩ {e ∈ {0..<m + Kart}. state_all ! e = InU} = {}"
    and "(!) (ds_par (build_tree acyc_flow)) ` (NS.𝒱 - {vcount}) ∩ {e ∈ {0..<m + Kart}. state_all ! e = InL} = {}"
    and "{e ∈ {0..<m + Kart}. state_all ! e = InL} ∩ {e ∈ {0..<m + Kart}. state_all ! e = InU} = {}"
proof -
  have T: "(!) (ds_par (build_tree acyc_flow)) ` (NS.𝒱 - {vcount}) = {e ∈ {0..<m + Kart}. state_all ! e = InTree}"
    by (rule T_eq_InTree[OF acyc])
  show "(!) (ds_par (build_tree acyc_flow)) ` (NS.𝒱 - {vcount}) ∩ {e ∈ {0..<m + Kart}. state_all ! e = InU} = {}"
    unfolding T by auto
  show "(!) (ds_par (build_tree acyc_flow)) ` (NS.𝒱 - {vcount}) ∩ {e ∈ {0..<m + Kart}. state_all ! e = InL} = {}"
    unfolding T by auto
  show "{e ∈ {0..<m + Kart}. state_all ! e = InL} ∩ {e ∈ {0..<m + Kart}. state_all ! e = InU} = {}"
    by auto
qed

subsection ‹The spanning-tree partition: arborescence and spanning (Some branch)›

text ‹The remaining four conjuncts of @{const NS.spanning_tree_partition}: the parent edges form a
      graph (endpoint-set injectivity), a @{const graph_abs}, a rooted @{const graph_abs.arborescence}
      (via the unique-distinct-walk bridge @{thm unique_walks_arborescence}, whose uniqueness premise is
      exactly the arborescence-ADT axiom @{thm NS.general}(3)), and span the vertex set. Together with the
      edge cover / tag disjointness above this assembles @{const NS.spanning_tree_partition} on the Some
      branch (acyclicity is needed only through @{thm edge_partition} / @{thm part_disj}).›

lemma dVs_make_pair_Vs_gen:
  "dVs ((λe. (g e, k e)) ` X) = Vs ((λe. {g e, k e}) ` X)"
  by (auto simp: dVs_def Vs_def)

lemma tree_edge_endpoint_inj:
  assumes u: "u ∈ Vseen" and u': "u' ∈ Vseen"
    and eq: "{fst_all ! (ds_par (build_tree acyc_flow) ! u), snd_all ! (ds_par (build_tree acyc_flow) ! u)}
           = {fst_all ! (ds_par (build_tree acyc_flow) ! u'), snd_all ! (ds_par (build_tree acyc_flow) ! u')}"
  shows "u = u'"
proof -
  let ?bt = "build_tree acyc_flow"
  let ?p = "λx. ds_prnt ?bt ! x"
  have uvs: "u ∈ set vs_list" and u'vs: "u' ∈ set vs_list" using u u' V_sub_vs_list Vseen_eq_V by auto
  have ult: "u < vcount" and useen: "ds_seen ?bt ! u" using u by (auto simp: Vseen_def)
  have u'lt: "u' < vcount" and u'seen: "ds_seen ?bt ! u'" using u' by (auto simp: Vseen_def)
  have stepu: "(u, ?p u) ∈ pstep ?bt" using ult useen by (auto simp: pstep_def)
  have stepu': "(u', ?p u') ∈ pstep ?bt" using u'lt u'seen by (auto simp: pstep_def)
  have unp: "u ≠ ?p u" using stepu pstep_acyclic by (metis acyclic_def r_into_trancl)
  have u'np: "u' ≠ ?p u'" using stepu' pstep_acyclic by (metis acyclic_def r_into_trancl)
  have setu: "{fst_all ! (ds_par ?bt ! u), snd_all ! (ds_par ?bt ! u)} = {u, ?p u}"
    using tc_endpoints[OF u] by (cases "ds_dir ?bt ! u") auto
  have setu': "{fst_all ! (ds_par ?bt ! u'), snd_all ! (ds_par ?bt ! u')} = {u', ?p u'}"
    using tc_endpoints[OF u'] by (cases "ds_dir ?bt ! u'") auto
  have "{u, ?p u} = {u', ?p u'}" using setu setu' eq by simp
  hence "(u = u' ∧ ?p u = ?p u') ∨ (u = ?p u' ∧ ?p u = u')"
    using unp u'np by (auto simp: doubleton_eq_iff)
  thus ?thesis
  proof
    assume "u = u' ∧ ?p u = ?p u'" thus ?thesis by simp
  next
    assume A: "u = ?p u' ∧ ?p u = u'"
    have "(u, u') ∈ pstep ?bt" using stepu A by argo
    moreover have "(u', u) ∈ pstep ?bt" using stepu' A by argo
    ultimately have "(u, u) ∈ (pstep ?bt)⇧+" by (meson trancl.simps)
    thus ?thesis using pstep_acyclic by (simp add: acyclic_def)
  qed
qed

lemma NSinit_partition:
  assumes acyc: "original_network.acyclic_flow (h ∘ nth acyc_flow)"
  shows "NS.spanning_tree_partition vcount
           ((!) (ds_par (build_tree acyc_flow)) ` (NS.𝒱 - {vcount}))
           {e ∈ {0..<m + Kart}. state_all ! e = InL}
           {e ∈ {0..<m + Kart}. state_all ! e = InU}"
proof (rule NS.spanning_tree_partitionI)
  let ?T = "(!) (ds_par (build_tree acyc_flow)) ` (NS.𝒱 - {vcount})"
  let ?U = "{e ∈ {0..<m + Kart}. state_all ! e = InU}"
  let ?L = "{e ∈ {0..<m + Kart}. state_all ! e = InL}"
  let ?f = "λe. {if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart))),
                  if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart)))}"
  have tci: "?f ` ?T = abstract_arb Sarb" by (rule tc_image)
  have gi: "graph_invar (abstract_arb Sarb)" by (rule graph_invar_abstract_arb[OF arb_invar_Sarb])
  show "{0..<m + Kart} = ?T ∪ ?U ∪ ?L" using edge_partition[OF acyc] by simp
  show "?T ∩ ?U = {}" by (rule part_disj(1)[OF acyc])
  show "?T ∩ ?L = {}" by (rule part_disj(2)[OF acyc])
  show "?L ∩ ?U = {}" by (rule part_disj(3)[OF acyc])
  show "graph_abs (?f ` ?T)"
    unfolding tci using gi by (simp add: graph_abs_def)
  show "graph_abs.arborescence (?f ` ?T) vcount (?f ` ?T)"
    unfolding tci
  proof (rule unique_walks_arborescence)
    show "graph_invar (abstract_arb Sarb)" by (rule gi)
    show "vcount ∈ Vs (abstract_arb Sarb)" using Vs_abstract_arb[OF arb_invar_Sarb] r_in_V by simp
  next
    fix x y assume "x ∈ Vs (abstract_arb Sarb)" and "y ∈ Vs (abstract_arb Sarb)"
    hence xV: "x ∈ NS.𝒱" and yV: "y ∈ NS.𝒱" using Vs_abstract_arb[OF arb_invar_Sarb] NS_V_Varb by auto
    show "∃!p. walk_betw (abstract_arb Sarb) x p y ∧ distinct p"
      using NS.general(3)[OF arb_invar_Sarb yV xV] by simp
  qed
  show "∀e e'. {e, e'} ⊆ ?T ∧ {if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart))),
                              if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart)))}
                          = {if e' < m + Kart then fst_all ! e' else fst (prod_decode (e' - (m + Kart))),
                             if e' < m + Kart then snd_all ! e' else snd (prod_decode (e' - (m + Kart)))}
               ⟶ e = e'"
  proof (intro allI impI, elim conjE)
    fix e e' assume sub: "{e, e'} ⊆ ?T"
      and eeq: "{if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart))),
                  if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart)))}
              = {if e' < m + Kart then fst_all ! e' else fst (prod_decode (e' - (m + Kart))),
                 if e' < m + Kart then snd_all ! e' else snd (prod_decode (e' - (m + Kart)))}"
    have eT: "e ∈ ?T" using sub by simp
    have e'T: "e' ∈ ?T" using sub by simp
    from eT obtain u where uV: "u ∈ NS.𝒱 - {vcount}" and eu: "e = ds_par (build_tree acyc_flow) ! u"
      unfolding image_iff by blast
    from e'T obtain u' where u'V: "u' ∈ NS.𝒱 - {vcount}" and eu': "e' = ds_par (build_tree acyc_flow) ! u'"
      unfolding image_iff by blast
    have uVs: "u ∈ Vseen" using uV NS_V_minus_root by simp
    have u'Vs: "u' ∈ Vseen" using u'V NS_V_minus_root by simp
    have ult: "u < vcount" and useen: "ds_seen (build_tree acyc_flow) ! u" using uVs by (auto simp: Vseen_def)
    have u'lt: "u' < vcount" and u'seen: "ds_seen (build_tree acyc_flow) ! u'" using u'Vs by (auto simp: Vseen_def)
    have emK': "ds_par (build_tree acyc_flow) ! u < m + Kart" using par_lt_marc[OF ult useen] .
    have e'mK': "ds_par (build_tree acyc_flow) ! u' < m + Kart" using par_lt_marc[OF u'lt u'seen] .
    have endeq: "{fst_all ! (ds_par (build_tree acyc_flow) ! u), snd_all ! (ds_par (build_tree acyc_flow) ! u)}
               = {fst_all ! (ds_par (build_tree acyc_flow) ! u'), snd_all ! (ds_par (build_tree acyc_flow) ! u')}"
      using eeq by (simp only: eu eu' if_P[OF emK'] if_P[OF e'mK'])
    have "u = u'" by (rule tree_edge_endpoint_inj[OF uVs u'Vs endeq])
    thus "e = e'" using eu eu' by simp
  qed
  show "dVs (NS.make_pair ` ?T) = NS.𝒱"
  proof -
    have mp: "NS.make_pair = (λe. (if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart))),
                                    if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart)))))"
      by (rule ext) (simp add: NS.make_pair_def)
    have "dVs (NS.make_pair ` ?T) = Vs (?f ` ?T)"
      unfolding mp by (rule dVs_make_pair_Vs_gen)
    thus ?thesis using tci Vs_abstract_arb[OF arb_invar_Sarb] NS_V_Varb by simp
  qed
qed

subsection ‹Towards @{text init_bflow}: excess decomposition of the assembled flow›

text ‹The augmented excess of @{const flow_all} splits into a real part and an artificial part. On the
      real edges @{term ‹e < m›} the assembled flow is @{const acyc_flow}, so — since the augmented and
      original in/out-edge sets agree there (@{thm delta_minus_orig} / @{thm delta_plus_orig}) — the real
      part is exactly ‹original_network.ex (h ∘ nth acyc_flow) v›. The artificial part is the signed
      flow on the artificial in/out edges of @{term v}; identifying it with @{term ‹imbalance ! v›} (and,
      with @{thm make_acyclic_ex}, ‹original_network.ex (h ∘ nth acyc_flow) v = h (excess ! v)›) is the
      remaining step toward @{text init_bflow}.›

lemma flow_all_ex_real:
  "(∑e∈NS.delta_minus v ∩ {0..<m}. h (flow_all ! e)) - (∑e∈NS.delta_plus v ∩ {0..<m}. h (flow_all ! e))
     = original_network.ex (h ∘ nth acyc_flow) v"
proof -
  have m1: "NS.delta_minus v ∩ {0..<m} = original_network.delta_minus v" using delta_minus_orig by simp
  have p1: "NS.delta_plus v ∩ {0..<m} = original_network.delta_plus v" using delta_plus_orig by simp
  have dmreal: "⋀e. e ∈ original_network.delta_minus v ⟹ flow_all ! e = acyc_flow ! e"
    using flow_all_real by (auto simp: original_network.delta_minus_def)
  have dpreal: "⋀e. e ∈ original_network.delta_plus v ⟹ flow_all ! e = acyc_flow ! e"
    using flow_all_real by (auto simp: original_network.delta_plus_def)
  have "(∑e∈NS.delta_minus v ∩ {0..<m}. h (flow_all ! e)) = (∑e∈original_network.delta_minus v. h (acyc_flow ! e))"
    unfolding m1 by (rule sum.cong[OF refl]) (simp add: dmreal)
  moreover have "(∑e∈NS.delta_plus v ∩ {0..<m}. h (flow_all ! e)) = (∑e∈original_network.delta_plus v. h (acyc_flow ! e))"
    unfolding p1 by (rule sum.cong[OF refl]) (simp add: dpreal)
  ultimately show ?thesis by (simp add: original_network.ex_def comp_def)
qed

lemma ex_flow_all_decomp:
  "NS.ex (h ∘ nth flow_all) v = original_network.ex (h ∘ nth acyc_flow) v
     + h ((∑e∈NS.delta_minus v ∩ {m..<m+Kart}. flow_all ! e) - (∑e∈NS.delta_plus v ∩ {m..<m+Kart}. flow_all ! e))"
proof -
  have dmsub: "NS.delta_minus v ⊆ {0..<m+Kart}"
    by (auto simp del: NS.fst_exec_eq NS.snd_exec_eq simp add: NS.delta_minus_def)
  have dpsub: "NS.delta_plus v ⊆ {0..<m+Kart}"
    by (auto simp del: NS.fst_exec_eq NS.snd_exec_eq simp add: NS.delta_plus_def)
  have split: "{0..<m+Kart} = {0..<m} ∪ {m..<m+Kart}" by auto
  have dmU: "NS.delta_minus v = (NS.delta_minus v ∩ {0..<m}) ∪ (NS.delta_minus v ∩ {m..<m+Kart})"
    using dmsub split by blast
  have dpU: "NS.delta_plus v = (NS.delta_plus v ∩ {0..<m}) ∪ (NS.delta_plus v ∩ {m..<m+Kart})"
    using dpsub split by blast
  have dmdisj: "(NS.delta_minus v ∩ {0..<m}) ∩ (NS.delta_minus v ∩ {m..<m+Kart}) = {}" by auto
  have dpdisj: "(NS.delta_plus v ∩ {0..<m}) ∩ (NS.delta_plus v ∩ {m..<m+Kart}) = {}" by auto
  have sm: "(∑e∈NS.delta_minus v. h (nth flow_all e))
          = (∑e∈NS.delta_minus v ∩ {0..<m}. h (flow_all ! e)) + (∑e∈NS.delta_minus v ∩ {m..<m+Kart}. h (flow_all ! e))"
    by (subst dmU) (rule sum.union_disjoint[OF _ _ dmdisj], auto simp: delta_fin[unfolded NS.delta_minus_def])
  have sp: "(∑e∈NS.delta_plus v. h (nth flow_all e))
          = (∑e∈NS.delta_plus v ∩ {0..<m}. h (flow_all ! e)) + (∑e∈NS.delta_plus v ∩ {m..<m+Kart}. h (flow_all ! e))"
    by (subst dpU) (rule sum.union_disjoint[OF _ _ dpdisj], auto simp: delta_fin[unfolded NS.delta_plus_def])
  have "NS.ex (h ∘ nth flow_all) v = (∑e∈NS.delta_minus v. h (nth flow_all e)) - (∑e∈NS.delta_plus v. h (nth flow_all e))"
    by (simp add: NS.ex_def comp_def)
  also have "… = ((∑e∈NS.delta_minus v ∩ {0..<m}. h (flow_all ! e)) - (∑e∈NS.delta_plus v ∩ {0..<m}. h (flow_all ! e)))
               + ((∑e∈NS.delta_minus v ∩ {m..<m+Kart}. h (flow_all ! e)) - (∑e∈NS.delta_plus v ∩ {m..<m+Kart}. h (flow_all ! e)))"
    using sm sp by (simp add: algebra_simps)
  also have "… = original_network.ex (h ∘ nth acyc_flow) v
               + ((∑e∈NS.delta_minus v ∩ {m..<m+Kart}. h (flow_all ! e)) - (∑e∈NS.delta_plus v ∩ {m..<m+Kart}. h (flow_all ! e)))"
    using flow_all_ex_real by simp
  also have "… = original_network.ex (h ∘ nth acyc_flow) v
               + h ((∑e∈NS.delta_minus v ∩ {m..<m+Kart}. flow_all ! e) - (∑e∈NS.delta_plus v ∩ {m..<m+Kart}. flow_all ! e))"
    by (simp add: h_sum)
  finally show ?thesis .
qed

text ‹The artificial in/out edge-sums at @{term v} reindex to sums over the artificial ∗‹slots›
      @{term ‹k < Kart›}: edge @{term ‹m + k›} is the ‹k›-th artificial edge, carrying
      @{term ‹ds_aflw (build_tree acyc_flow) ! k›} (@{thm flow_all_art}). The membership rewrites
      @{text dm_art_iff}/@{text dp_art_iff} strip the augmented endpoint functions down to the plain
      arrays (the ‹fst_exec›/‹snd_exec› simp rules must be disabled throughout — they are
      self-referential and loop on any ‹fst_all ! e› / ‹snd_all ! e›).›

lemma dm_art_iff: "e ∈ NS.delta_minus v ∩ {m..<m+Kart} ⟷ (m ≤ e ∧ e < m+Kart ∧ snd_all ! e = v)"
proof -
  have "e ∈ NS.delta_minus v ⟷ (e ∈ {0..<m+Kart} ∧ snd_all ! e = v)"
    by (simp del: NS.fst_exec_eq NS.snd_exec_eq add: NS.delta_minus_def)
  thus ?thesis by auto
qed

lemma dp_art_iff: "e ∈ NS.delta_plus v ∩ {m..<m+Kart} ⟷ (m ≤ e ∧ e < m+Kart ∧ fst_all ! e = v)"
proof -
  have "e ∈ NS.delta_plus v ⟷ (e ∈ {0..<m+Kart} ∧ fst_all ! e = v)"
    by (simp del: NS.fst_exec_eq NS.snd_exec_eq add: NS.delta_plus_def)
  thus ?thesis by auto
qed

lemma dm_art_set: "NS.delta_minus v ∩ {m..<m+Kart} = {e. m ≤ e ∧ e < m+Kart ∧ snd_all!e = v}"
  using dm_art_iff by blast

lemma dp_art_set: "NS.delta_plus v ∩ {m..<m+Kart} = {e. m ≤ e ∧ e < m+Kart ∧ fst_all!e = v}"
  using dp_art_iff by blast

lemma art_reindex_minus:
  "(∑e∈NS.delta_minus v ∩ {m..<m+Kart}. flow_all ! e)
     = (∑k∈{k. k < Kart ∧ snd_all ! (m+k) = v}. ds_aflw (build_tree acyc_flow) ! k)"
proof -
  let ?S = "{k. k < Kart ∧ snd_all ! (m+k) = v}"
  have inj: "inj_on (λk. m+k) ?S" by (auto simp: inj_on_def)
  have setEq: "{e. m ≤ e ∧ e < m+Kart ∧ snd_all!e = v} = (λk. m+k) ` ?S"
  proof (rule set_eqI, rule iffI)
    fix e assume "e ∈ {e. m ≤ e ∧ e < m+Kart ∧ snd_all!e = v}"
    hence e1: "m ≤ e" "e < m+Kart" and sv: "snd_all!e = v" by blast+
    have mke: "m + (e - m) = e" using e1 by simp
    have kk: "e - m < Kart" using e1 by simp
    have ss: "snd_all ! (m + (e - m)) = v" using sv mke by argo
    show "e ∈ (λk. m+k) ` ?S"
      using kk ss mke by (intro image_eqI[of e _ "e - m"]) (simp_all del: NS.fst_exec_eq NS.snd_exec_eq)
  next
    fix e assume "e ∈ (λk. m+k) ` ?S"
    then obtain k where k: "e = m+k" and kS: "k<Kart" "snd_all!(m+k)=v" by blast
    show "e ∈ {e. m ≤ e ∧ e < m+Kart ∧ snd_all!e = v}" using k kS by (simp del: NS.fst_exec_eq NS.snd_exec_eq)
  qed
  have "(∑e∈NS.delta_minus v ∩ {m..<m+Kart}. flow_all ! e) = (∑e∈(λk. m+k) ` ?S. flow_all ! e)"
    by (simp only: dm_art_set setEq)
  also have "… = (∑k∈?S. flow_all ! (m+k))" by (subst sum.reindex[OF inj]) simp
  also have "… = (∑k∈?S. ds_aflw (build_tree acyc_flow) ! k)"
    by (rule sum.cong[OF refl]) (auto simp del: NS.fst_exec_eq NS.snd_exec_eq simp add: flow_all_art)
  finally show ?thesis .
qed

lemma art_reindex_plus:
  "(∑e∈NS.delta_plus v ∩ {m..<m+Kart}. flow_all ! e)
     = (∑k∈{k. k < Kart ∧ fst_all ! (m+k) = v}. ds_aflw (build_tree acyc_flow) ! k)"
proof -
  let ?S = "{k. k < Kart ∧ fst_all ! (m+k) = v}"
  have inj: "inj_on (λk. m+k) ?S" by (auto simp: inj_on_def)
  have setEq: "{e. m ≤ e ∧ e < m+Kart ∧ fst_all!e = v} = (λk. m+k) ` ?S"
  proof (rule set_eqI, rule iffI)
    fix e assume "e ∈ {e. m ≤ e ∧ e < m+Kart ∧ fst_all!e = v}"
    hence e1: "m ≤ e" "e < m+Kart" and sv: "fst_all!e = v" by blast+
    have mke: "m + (e - m) = e" using e1 by simp
    have kk: "e - m < Kart" using e1 by simp
    have ss: "fst_all ! (m + (e - m)) = v" using sv mke by argo
    show "e ∈ (λk. m+k) ` ?S"
      using kk ss mke by (intro image_eqI[of e _ "e - m"]) (simp_all del: NS.fst_exec_eq NS.snd_exec_eq)
  next
    fix e assume "e ∈ (λk. m+k) ` ?S"
    then obtain k where k: "e = m+k" and kS: "k<Kart" "fst_all!(m+k)=v" by blast
    show "e ∈ {e. m ≤ e ∧ e < m+Kart ∧ fst_all!e = v}" using k kS by (simp del: NS.fst_exec_eq NS.snd_exec_eq)
  qed
  have "(∑e∈NS.delta_plus v ∩ {m..<m+Kart}. flow_all ! e) = (∑e∈(λk. m+k) ` ?S. flow_all ! e)"
    by (simp only: dp_art_set setEq)
  also have "… = (∑k∈?S. flow_all ! (m+k))" by (subst sum.reindex[OF inj]) simp
  also have "… = (∑k∈?S. ds_aflw (build_tree acyc_flow) ! k)"
    by (rule sum.cong[OF refl]) (auto simp del: NS.fst_exec_eq NS.snd_exec_eq simp add: flow_all_art)
  finally show ?thesis .
qed

subsection ‹Towards @{text init_bflow}: the artificial excess accumulator›

text ‹@{term ‹aex s v›} is the artificial-edge contribution to @{term v}'s excess in state @{term s}:
      the signed per-slot flow over the slots already emitted (@{term ‹k < ds_nxt s›}). Each emission
      — @{const emit_U_edge} or the seed of @{const open_tree_component} (the enclosed @{const build_dfs}
      freezes the artificial arrays, @{thm build_dfs_art}) — changes @{term ‹aex s v›} by exactly
      @{term ‹- imbalance ! v›} at the processed vertex and @{term ‹imbalance ! v›} at the root, so over
      a whole phase-1 sweep the increments accumulate as one @{const sum_list}. The @{term E}-witness
      (@{term ‹ds_nxt s = card E›}) carries the @{term ‹ds_nxt s < length vs_list›} bound the emission
      step lemmas need, exactly as in @{thm fold_phase1_art_owned}.›

definition aex :: "'n dfs_state ⇒ nat ⇒ 'n" where
  "aex s v = (∑k = 0..<ds_nxt s. (if ds_asnd s ! k = v then ds_aflw s ! k else 0)
                                - (if ds_afst s ! k = v then ds_aflw s ! k else 0))"

lemma emit_U_edge_aex:
  assumes al: "art_len s" and inb: "ds_nxt s < length vs_list" and vlt: "v < vcount"
  shows "aex (emit_U_edge s v) w
           = aex s w + (if w = v then - imbalance ! v else if w = vcount then imbalance ! v else 0)"
proof -
  let ?n = "ds_nxt s"
  let ?up = "0 ≤ imbalance ! v"
  have lens: "length (ds_afst s) = length vs_list" "length (ds_asnd s) = length vs_list"
             "length (ds_aflw s) = length vs_list" using al by (auto simp: art_len_def)
  have nb: "?n < length (ds_afst s)" "?n < length (ds_asnd s)" "?n < length (ds_aflw s)"
    using inb lens by simp_all
  have nxt': "ds_nxt (emit_U_edge s v) = Suc ?n" by (simp add: emit_U_edge_def Let_def)
  have asnd_n: "ds_asnd (emit_U_edge s v) ! ?n = (if ?up then vcount else v)"
    using nb by (simp add: emit_U_edge_def Let_def art_dir_def)
  have afst_n: "ds_afst (emit_U_edge s v) ! ?n = (if ?up then v else vcount)"
    using nb by (simp add: emit_U_edge_def Let_def art_dir_def)
  have aflw_n: "ds_aflw (emit_U_edge s v) ! ?n = ¦imbalance ! v¦"
    using nb by (simp add: emit_U_edge_def Let_def)
  have keep: "⋀k. k < ?n ⟹ ds_asnd (emit_U_edge s v) ! k = ds_asnd s ! k
                          ∧ ds_afst (emit_U_edge s v) ! k = ds_afst s ! k
                          ∧ ds_aflw (emit_U_edge s v) ! k = ds_aflw s ! k"
    by (auto simp: emit_U_edge_def Let_def nth_list_update_neq)
  have "aex (emit_U_edge s v) w
      = (∑k = 0..<Suc ?n. (if ds_asnd (emit_U_edge s v) ! k = w then ds_aflw (emit_U_edge s v) ! k else 0)
                        - (if ds_afst (emit_U_edge s v) ! k = w then ds_aflw (emit_U_edge s v) ! k else 0))"
    by (simp add: aex_def nxt')
  also have "… = (∑k = 0..<?n. (if ds_asnd (emit_U_edge s v) ! k = w then ds_aflw (emit_U_edge s v) ! k else 0)
                             - (if ds_afst (emit_U_edge s v) ! k = w then ds_aflw (emit_U_edge s v) ! k else 0))
               + ((if ds_asnd (emit_U_edge s v) ! ?n = w then ds_aflw (emit_U_edge s v) ! ?n else 0)
                - (if ds_afst (emit_U_edge s v) ! ?n = w then ds_aflw (emit_U_edge s v) ! ?n else 0))"
    by (simp add: sum.atLeast0_lessThan_Suc)
  also have "(∑k = 0..<?n. (if ds_asnd (emit_U_edge s v) ! k = w then ds_aflw (emit_U_edge s v) ! k else 0)
                        - (if ds_afst (emit_U_edge s v) ! k = w then ds_aflw (emit_U_edge s v) ! k else 0))
           = aex s w"
    by (simp add: aex_def) (rule sum.cong[OF refl], simp add: keep)
  finally show ?thesis
    using vlt no_zero_node
    by (cases ?up) (auto simp: asnd_n afst_n aflw_n art_flow_def imbalance_def)
qed

lemma open_tree_component_aex:
  assumes inv: "dfs_inv acyc_flow s" and al: "art_len s" and inb: "ds_nxt s < length vs_list" and vlt: "v < vcount"
  shows "aex (open_tree_component acyc_flow s v) w
           = aex s w + (if w = v then - imbalance ! v else if w = vcount then imbalance ! v else 0)"
proof -
  let ?n = "ds_nxt s"
  let ?t = "open_tree_component acyc_flow s v"
  have nxt': "ds_nxt ?t = Suc ?n" using open_tree_component_nxt[OF inv vlt] .
  have asnd_n: "ds_asnd ?t ! ?n = (if art_dir v then vcount else v)" using open_tree_component_asnd_at[OF inv vlt inb al] .
  have afst_n: "ds_afst ?t ! ?n = (if art_dir v then v else vcount)" using open_tree_component_afst_at[OF inv vlt inb al] .
  have aflw_n: "ds_aflw ?t ! ?n = art_flow v" using open_tree_component_aflw_at[OF inv vlt inb al] .
  have keep: "⋀k. k < ?n ⟹ ds_asnd ?t ! k = ds_asnd s ! k ∧ ds_afst ?t ! k = ds_afst s ! k ∧ ds_aflw ?t ! k = ds_aflw s ! k"
    using open_tree_component_asnd_old[OF inv vlt] open_tree_component_afst_old[OF inv vlt] open_tree_component_aflw_old[OF inv vlt] by simp
  have "aex ?t w
      = (∑k = 0..<Suc ?n. (if ds_asnd ?t ! k = w then ds_aflw ?t ! k else 0) - (if ds_afst ?t ! k = w then ds_aflw ?t ! k else 0))"
    by (simp add: aex_def nxt')
  also have "… = (∑k = 0..<?n. (if ds_asnd ?t ! k = w then ds_aflw ?t ! k else 0) - (if ds_afst ?t ! k = w then ds_aflw ?t ! k else 0))
               + ((if ds_asnd ?t ! ?n = w then ds_aflw ?t ! ?n else 0) - (if ds_afst ?t ! ?n = w then ds_aflw ?t ! ?n else 0))"
    by (simp add: sum.atLeast0_lessThan_Suc)
  also have "(∑k = 0..<?n. (if ds_asnd ?t ! k = w then ds_aflw ?t ! k else 0) - (if ds_afst ?t ! k = w then ds_aflw ?t ! k else 0)) = aex s w"
    by (simp add: aex_def) (rule sum.cong[OF refl], simp add: keep)
  finally show ?thesis
    using vlt no_zero_node
    by (cases "art_dir v") (auto simp: asnd_n afst_n aflw_n art_flow_def art_dir_def)
qed

lemma phase1_step_aex:
  assumes v: "v ∈ set vs_list" and inv: "dfs_inv acyc_flow s" and stke: "ds_stk s = []"
      and al: "art_len s" and inb: "ds_nxt s < length vs_list"
  shows "aex (phase1_step acyc_flow v s) w = aex s w + (if w = v then - imbalance!v else if w = vcount then imbalance!v else 0)"
proof (cases "imbalance ! v = 0")
  case True
  hence "phase1_step acyc_flow v s = s" by (simp add: phase1_step_def)
  thus ?thesis using True by simp
next
  case nz: False
  have vlt: "v < vcount" using v vs_less_vcount by simp
  show ?thesis
  proof (cases "ds_seen s ! v")
    case True
    have "phase1_step acyc_flow v s = emit_U_edge s v" using nz True by (simp add: phase1_step_def)
    thus ?thesis using emit_U_edge_aex[OF al inb vlt] by simp
  next
    case False
    have "phase1_step acyc_flow v s = open_tree_component acyc_flow s v" using nz False by (simp add: phase1_step_def)
    thus ?thesis using open_tree_component_aex[OF inv al inb vlt] by simp
  qed
qed

lemma fold_phase1_aex:
  assumes "distinct xs" "set xs ⊆ set vs_list" "dfs_inv acyc_flow s" "ds_stk s = []"
      "art_len s" "finite E" "E ⊆ {v ∈ set vs_list. ds_seen s ! v}" "E ∩ set xs = {}" "ds_nxt s = card E"
  shows "aex (fold (phase1_step acyc_flow) xs s) w
           = aex s w + (∑v←xs. (if w = v then - imbalance!v else if w = vcount then imbalance!v else 0))
         ∧ art_len (fold (phase1_step acyc_flow) xs s)
         ∧ dfs_inv acyc_flow (fold (phase1_step acyc_flow) xs s)
         ∧ ds_stk (fold (phase1_step acyc_flow) xs s) = []
         ∧ (∃E'. finite E' ∧ E' ⊆ {v ∈ set vs_list. ds_seen (fold (phase1_step acyc_flow) xs s) ! v}
                 ∧ ds_nxt (fold (phase1_step acyc_flow) xs s) = card E')"
  using assms
proof (induct xs arbitrary: s E)
  case Nil thus ?case by auto
next
  case (Cons x rest)
  have xvs: "x ∈ set vs_list" using Cons.prems(2) by simp
  have xlt: "x < vcount" using xvs vs_less_vcount by simp
  have Esub: "E ⊆ set vs_list" using Cons.prems(7) by auto
  have xnotE: "x ∉ E" using Cons.prems(8) by auto
  have insub: "insert x E ⊆ set vs_list" using Esub xvs by auto
  have cardins: "card (insert x E) ≤ length vs_list" using insub by (rule card_sub_vs_le)
  have inbs: "ds_nxt s < length vs_list"
    using cardins Cons.prems(6,9) xnotE by (simp add: card_insert_disjoint)
  have stepaex: "aex (phase1_step acyc_flow x s) w
                   = aex s w + (if w = x then - imbalance!x else if w = vcount then imbalance!x else 0)"
    using phase1_step_aex[OF xvs Cons.prems(3) Cons.prems(4) Cons.prems(5) inbs] .
  have inv1: "dfs_inv acyc_flow (phase1_step acyc_flow x s)" "ds_stk (phase1_step acyc_flow x s) = []"
    using phase1_step_inv[OF xvs conjI[OF Cons.prems(3) Cons.prems(4)]] by auto
  have al1: "art_len (phase1_step acyc_flow x s)" using phase1_step_art_len[OF xvs Cons.prems(3) Cons.prems(5)] .
  have Emono: "E ⊆ {v ∈ set vs_list. ds_seen (phase1_step acyc_flow x s) ! v}"
    using Cons.prems(7) phase1_step_seen_mono[OF Cons.prems(3) xlt] by auto
  have distr: "distinct rest" using Cons.prems(1) by simp
  have subr: "set rest ⊆ set vs_list" using Cons.prems(2) by simp
  from phase1_step_nxt[OF Cons.prems(3) xlt] show ?case
  proof
    assume A: "ds_nxt (phase1_step acyc_flow x s) = ds_nxt s"
    have card1: "ds_nxt (phase1_step acyc_flow x s) = card E" using A Cons.prems(9) by simp
    have Edisj: "E ∩ set rest = {}" using Cons.prems(8) by auto
    note IH = Cons.hyps[OF distr subr inv1(1) inv1(2) al1 Cons.prems(6) Emono Edisj card1]
    show ?thesis using IH stepaex by simp
  next
    assume B: "ds_nxt (phase1_step acyc_flow x s) = Suc (ds_nxt s) ∧ ds_seen (phase1_step acyc_flow x s) ! x"
    define E2 where "E2 = insert x E"
    have fin2: "finite E2" using Cons.prems(6) by (simp add: E2_def)
    have E2seen: "E2 ⊆ {v ∈ set vs_list. ds_seen (phase1_step acyc_flow x s) ! v}" using Emono B xvs by (auto simp: E2_def)
    have E2disj: "E2 ∩ set rest = {}" using Cons.prems(8) Cons.prems(1) by (auto simp: E2_def)
    have card2: "ds_nxt (phase1_step acyc_flow x s) = card E2" using B Cons.prems(9) xnotE Cons.prems(6) by (simp add: E2_def card_insert_disjoint)
    note IH = Cons.hyps[OF distr subr inv1(1) inv1(2) al1 fin2 E2seen E2disj card2]
    show ?thesis using IH stepaex by simp
  qed
qed

text ‹The accumulator reaches its target already after phase 1 (every imbalanced vertex is opened
      or gets its @{const emit_U_edge}, hence seen), and phase 2 only opens the remaining — balanced,
      hence zero-flow — vertices, so it leaves @{const aex} unchanged; the final @{const ds_lsuc}
      touch-up is irrelevant. Thus each real vertex's artificial excess is exactly
      @{term ‹- imbalance ! w›}.›

lemma aex_dfs_init: "aex dfs_init v = 0"
  by (simp add: aex_def dfs_init_def)

lemma aex_lsuc: "aex (s⦇ds_lsuc := x⦈) v = aex s v"
  by (simp add: aex_def cong: if_cong)

lemma phase1_step_marks_imb:
  assumes nz: "imbalance!x ≠ 0" and inv: "dfs_inv acyc_flow s" and xlt: "x < vcount"
  shows "ds_seen (phase1_step acyc_flow x s) ! x"
proof (cases "ds_seen s ! x")
  case True thus ?thesis using nz by (simp add: phase1_step_def emit_U_edge_def Let_def)
next
  case False thus ?thesis using nz open_tree_component_marks[OF inv xlt] by (simp add: phase1_step_def)
qed

lemma fold_phase1_imb_seen:
  assumes "set xs ⊆ set vs_list" "dfs_inv acyc_flow s" "ds_stk s = []"
      "ds_seen s ! v ∨ (v ∈ set xs ∧ imbalance!v ≠ 0)"
  shows "ds_seen (fold (phase1_step acyc_flow) xs s) ! v"
  using assms
proof (induct xs arbitrary: s)
  case Nil thus ?case by auto
next
  case (Cons x rest)
  have xvs: "x ∈ set vs_list" using Cons.prems(1) by simp
  have xlt: "x < vcount" using xvs vs_less_vcount by simp
  have inv': "dfs_inv acyc_flow (phase1_step acyc_flow x s)" "ds_stk (phase1_step acyc_flow x s) = []"
    using phase1_step_inv[OF xvs conjI[OF Cons.prems(2) Cons.prems(3)]] by auto
  have subr: "set rest ⊆ set vs_list" using Cons.prems(1) by simp
  have "ds_seen (phase1_step acyc_flow x s) ! v ∨ (v ∈ set rest ∧ imbalance!v ≠ 0)"
    using Cons.prems(4)
  proof
    assume "ds_seen s ! v"
    hence "ds_seen (phase1_step acyc_flow x s) ! v" using phase1_step_seen_mono[OF Cons.prems(2) xlt] by simp
    thus ?thesis by simp
  next
    assume A: "v ∈ set (x#rest) ∧ imbalance!v ≠ 0"
    show ?thesis
    proof (cases "v = x")
      case True
      hence "ds_seen (phase1_step acyc_flow x s) ! v"
        using A phase1_step_marks_imb[OF _ Cons.prems(2) xlt] by auto
      thus ?thesis by simp
    next
      case False
      thus ?thesis using A by simp
    qed
  qed
  thus ?case using Cons.hyps[OF subr inv'(1) inv'(2)] by simp
qed

lemma phase2_step_aex:
  assumes inv: "dfs_inv acyc_flow s" and al: "art_len s" and inb: "ds_nxt s < length vs_list"
      and v: "v ∈ set vs_list" and imb0: "imbalance!v = 0"
  shows "aex (phase2_step acyc_flow v s) w = aex s w"
proof (cases "ds_seen s ! v ∨ is_lonely v")
  case True thus ?thesis by (simp add: phase2_step_def)
next
  case False
  hence notseen: "¬ ds_seen s ! v" and nl: "¬ is_lonely v" by auto
  have vlt: "v < vcount" using v vs_less_vcount by simp
  have "phase2_step acyc_flow v s = open_tree_component acyc_flow s v" using notseen nl by (simp add: phase2_step_def)
  thus ?thesis using open_tree_component_aex[OF inv al inb vlt] imb0 by simp
qed

lemma fold_phase2_aex:
  assumes "set xs ⊆ set vs_list" "dfs_inv acyc_flow s" "ds_stk s = []" "art_len s"
      "finite E" "E ⊆ {u ∈ set vs_list. ds_seen s ! u}" "ds_nxt s = card E"
      "∀u ∈ set vs_list. ¬ ds_seen s ! u ⟶ imbalance!u = 0"
  shows "aex (fold (phase2_step acyc_flow) xs s) w = aex s w
         ∧ art_len (fold (phase2_step acyc_flow) xs s) ∧ dfs_inv acyc_flow (fold (phase2_step acyc_flow) xs s)
         ∧ ds_stk (fold (phase2_step acyc_flow) xs s) = []
         ∧ (∀u ∈ set vs_list. ¬ ds_seen (fold (phase2_step acyc_flow) xs s) ! u ⟶ imbalance!u = 0)"
  using assms
proof (induct xs arbitrary: s E)
  case Nil thus ?case by auto
next
  case (Cons x rest)
  have xvs: "x ∈ set vs_list" using Cons.prems(1) by simp
  have xlt: "x < vcount" using xvs vs_less_vcount by simp
  have subr: "set rest ⊆ set vs_list" using Cons.prems(1) by simp
  have inv1: "dfs_inv acyc_flow (phase2_step acyc_flow x s)" "ds_stk (phase2_step acyc_flow x s) = []"
    using phase2_step_inv[OF xvs conjI[OF Cons.prems(2) Cons.prems(3)]] by auto
  have al1: "art_len (phase2_step acyc_flow x s)" using phase2_step_art_len[OF xvs Cons.prems(2) Cons.prems(4)] .
  have bal1: "∀u ∈ set vs_list. ¬ ds_seen (phase2_step acyc_flow x s) ! u ⟶ imbalance!u = 0"
  proof (intro ballI impI)
    fix u assume uvs: "u ∈ set vs_list" and uns: "¬ ds_seen (phase2_step acyc_flow x s) ! u"
    have ults: "u < vcount" using uvs vs_less_vcount by simp
    have "¬ ds_seen s ! u" using uns phase2_step_seen_mono[OF Cons.prems(2) xlt] by blast
    thus "imbalance!u = 0" using Cons.prems(8) uvs by simp
  qed
  show ?case
  proof (cases "ds_seen s ! x")
    case seen: True
    have eq: "phase2_step acyc_flow x s = s" by (simp add: phase2_step_def seen)
    have aexeq: "aex (phase2_step acyc_flow x s) w = aex s w" by (simp add: eq)
    have Eeq: "E ⊆ {u ∈ set vs_list. ds_seen (phase2_step acyc_flow x s) ! u}" using Cons.prems(6) eq by simp
    have cardeq: "ds_nxt (phase2_step acyc_flow x s) = card E" using Cons.prems(7) eq by simp
    note IH = Cons.hyps[OF subr inv1(1) inv1(2) al1 Cons.prems(5) Eeq cardeq bal1]
    show ?thesis using IH aexeq by simp
  next
    case notseen: False
    show ?thesis
    proof (cases "is_lonely x")
      case lonely: True
      have eq: "phase2_step acyc_flow x s = s" by (simp add: phase2_step_def notseen lonely)
      have aexeq: "aex (phase2_step acyc_flow x s) w = aex s w" by (simp add: eq)
      have Eeq: "E ⊆ {u ∈ set vs_list. ds_seen (phase2_step acyc_flow x s) ! u}" using Cons.prems(6) eq by simp
      have cardeq: "ds_nxt (phase2_step acyc_flow x s) = card E" using Cons.prems(7) eq by simp
      note IH = Cons.hyps[OF subr inv1(1) inv1(2) al1 Cons.prems(5) Eeq cardeq bal1]
      show ?thesis using IH aexeq by simp
    next
      case nl: False
      have imb0: "imbalance!x = 0" using Cons.prems(8) xvs notseen by simp
      have xnotE: "x ∉ E" using Cons.prems(6) notseen by auto
      have insub: "insert x E ⊆ set vs_list" using Cons.prems(6) xvs by auto
      have inbs: "ds_nxt s < length vs_list"
        using card_sub_vs_le[OF insub] Cons.prems(5,7) xnotE by (simp add: card_insert_disjoint)
      have aexeq: "aex (phase2_step acyc_flow x s) w = aex s w"
        using phase2_step_aex[OF Cons.prems(2) Cons.prems(4) inbs xvs imb0] .
      have nxt': "ds_nxt (phase2_step acyc_flow x s) = Suc (ds_nxt s)"
        using notseen open_tree_component_nxt[OF Cons.prems(2) xlt] nl by (simp add: phase2_step_def)
      define E2 where "E2 = insert x E"
      have fin2: "finite E2" using Cons.prems(5) by (simp add: E2_def)
      have xseen1: "ds_seen (phase2_step acyc_flow x s) ! x" using phase2_step_marks[OF Cons.prems(2) xlt nl] .
      have E2seen: "E2 ⊆ {u ∈ set vs_list. ds_seen (phase2_step acyc_flow x s) ! u}"
        using Cons.prems(6) phase2_step_seen_mono[OF Cons.prems(2) xlt] xvs xseen1 by (auto simp: E2_def)
      have card2: "ds_nxt (phase2_step acyc_flow x s) = card E2"
        using nxt' Cons.prems(5,7) xnotE by (simp add: E2_def card_insert_disjoint)
      note IH = Cons.hyps[OF subr inv1(1) inv1(2) al1 fin2 E2seen card2 bal1]
      show ?thesis using IH aexeq by simp
    qed
  qed
qed

lemma build_tree_aex:
  assumes w: "w ∈ set vs_list"
  shows "aex (build_tree acyc_flow) w = - imbalance ! w"
proof -
  have invi: "dfs_inv acyc_flow dfs_init" by (rule dfs_init_inv)
  have stki: "ds_stk dfs_init = []" by (simp add: dfs_init_def)
  have E0: "({}::nat set) ⊆ {v ∈ set vs_list. ds_seen dfs_init ! v}" by simp
  have E0d: "({}::nat set) ∩ set vs_list = {}" by simp
  have nxt0: "ds_nxt dfs_init = card ({}::nat set)" by (simp add: dfs_init_def)
  note P1 = fold_phase1_aex[OF distinct_vs_list order_refl invi stki dfs_init_art_len finite.emptyI E0 E0d nxt0, of w]
  have aex_p1: "aex (phase1 acyc_flow dfs_init) w = (∑v←vs_list. (if w = v then - imbalance!v else if w = vcount then imbalance!v else 0))"
    using P1 aex_dfs_init unfolding phase1_def by simp
  have al_p1: "art_len (phase1 acyc_flow dfs_init)" using P1 unfolding phase1_def by simp
  have inv_p1: "dfs_inv acyc_flow (phase1 acyc_flow dfs_init)" using P1 unfolding phase1_def by simp
  have stk_p1: "ds_stk (phase1 acyc_flow dfs_init) = []" using P1 unfolding phase1_def by simp
  obtain E1 where E1: "finite E1" "E1 ⊆ {v ∈ set vs_list. ds_seen (phase1 acyc_flow dfs_init) ! v}" "ds_nxt (phase1 acyc_flow dfs_init) = card E1"
    using P1 unfolding phase1_def by blast
  have bal: "∀u ∈ set vs_list. ¬ ds_seen (phase1 acyc_flow dfs_init) ! u ⟶ imbalance!u = 0"
  proof (intro ballI impI)
    fix u assume uvs: "u ∈ set vs_list" and uns: "¬ ds_seen (phase1 acyc_flow dfs_init) ! u"
    show "imbalance!u = 0"
    proof (rule ccontr)
      assume "imbalance!u ≠ 0"
      hence "ds_seen (phase1 acyc_flow dfs_init) ! u"
        using fold_phase1_imb_seen[OF order_refl invi stki] uvs unfolding phase1_def by simp
      thus False using uns by simp
    qed
  qed
  note P2 = fold_phase2_aex[OF order_refl inv_p1 stk_p1 al_p1 E1(1) E1(2) E1(3) bal, of w]
  have aex_p2: "aex (phase2 acyc_flow (phase1 acyc_flow dfs_init)) w = aex (phase1 acyc_flow dfs_init) w"
    using P2 unfolding phase2_def by simp
  have aex_bt: "aex (build_tree acyc_flow) w = aex (phase2 acyc_flow (phase1 acyc_flow dfs_init)) w"
    by (simp add: build_tree_def Let_def aex_lsuc)
  have wnv: "w ≠ vcount" using w vs_less_vcount by fastforce
  have "(∑v←vs_list. (if w = v then - imbalance!v else if w = vcount then imbalance!v else 0))
      = (∑v←vs_list. (if v = w then - imbalance!w else 0))"
    by (rule arg_cong[where f=sum_list], rule map_cong[OF refl]) (auto simp: wnv)
  also have "… = (∑v∈set vs_list. (if v = w then - imbalance!w else 0))"
    by (rule sum_list_distinct_conv_sum_set[OF distinct_vs_list])
  also have "… = - imbalance!w" using w by simp
  finally have sumcollapse: "(∑v←vs_list. (if w = v then - imbalance!v else if w = vcount then imbalance!v else 0)) = - imbalance!w" .
  show ?thesis using aex_bt aex_p2 aex_p1 sumcollapse by simp
qed

text ‹Reindexing @{const aex} at @{const build_tree} to the augmented artificial edge-sums bridges
      the accumulator to @{thm ex_flow_all_decomp}: the artificial part of @{term v}'s augmented
      excess is @{term ‹aex (build_tree acyc_flow) v›}. Hence for every real vertex the augmented
      excess of @{const flow_all} is the acyclified-flow excess minus @{term ‹imbalance ! v›}.›

lemma aex_eq_art_part:
  "aex (build_tree acyc_flow) v
     = (∑e∈NS.delta_minus v ∩ {m..<m+Kart}. flow_all ! e) - (∑e∈NS.delta_plus v ∩ {m..<m+Kart}. flow_all ! e)"
proof -
  let ?bt = "build_tree acyc_flow"
  have nxtK: "ds_nxt ?bt = Kart" by (simp add: Kart_def)
  have Mcong: "(∑k = 0..<Kart. if ds_asnd ?bt!k=v then ds_aflw ?bt!k else 0) = (∑k = 0..<Kart. if snd_all!(m+k)=v then ds_aflw ?bt!k else 0)"
    by (rule sum.cong[OF refl]) (simp add: snd_all_art del: NS.fst_exec_eq NS.snd_exec_eq)
  have Pcong: "(∑k = 0..<Kart. if ds_afst ?bt!k=v then ds_aflw ?bt!k else 0) = (∑k = 0..<Kart. if fst_all!(m+k)=v then ds_aflw ?bt!k else 0)"
    by (rule sum.cong[OF refl]) (simp add: fst_all_art del: NS.fst_exec_eq NS.snd_exec_eq)
  have Mrestr: "(∑k = 0..<Kart. if snd_all!(m+k)=v then ds_aflw ?bt!k else 0) = (∑k∈{k. k < Kart ∧ snd_all!(m+k)=v}. ds_aflw ?bt!k)"
  proof (rule sum.mono_neutral_cong_right)
    show "finite {0..<Kart}" by simp
    show "{k. k < Kart ∧ snd_all!(m+k)=v} ⊆ {0..<Kart}" by (auto simp del: NS.fst_exec_eq NS.snd_exec_eq)
    show "∀i∈{0..<Kart} - {k. k < Kart ∧ snd_all!(m+k)=v}. (if snd_all!(m+i)=v then ds_aflw ?bt!i else 0) = 0"
    proof
      fix i assume "i ∈ {0..<Kart} - {k. k < Kart ∧ snd_all!(m+k)=v}"
      hence "¬ snd_all!(m+i)=v" by (auto simp del: NS.fst_exec_eq NS.snd_exec_eq)
      thus "(if snd_all!(m+i)=v then ds_aflw ?bt!i else 0) = 0" by (rule if_not_P)
    qed
  next
    fix x assume "x ∈ {k. k < Kart ∧ snd_all!(m+k)=v}"
    hence "snd_all!(m+x)=v" by (auto simp del: NS.fst_exec_eq NS.snd_exec_eq)
    thus "(if snd_all!(m+x)=v then ds_aflw ?bt!x else 0) = ds_aflw ?bt!x" by (rule if_P)
  qed
  have Prestr: "(∑k = 0..<Kart. if fst_all!(m+k)=v then ds_aflw ?bt!k else 0) = (∑k∈{k. k < Kart ∧ fst_all!(m+k)=v}. ds_aflw ?bt!k)"
  proof (rule sum.mono_neutral_cong_right)
    show "finite {0..<Kart}" by simp
    show "{k. k < Kart ∧ fst_all!(m+k)=v} ⊆ {0..<Kart}" by (auto simp del: NS.fst_exec_eq NS.snd_exec_eq)
    show "∀i∈{0..<Kart} - {k. k < Kart ∧ fst_all!(m+k)=v}. (if fst_all!(m+i)=v then ds_aflw ?bt!i else 0) = 0"
    proof
      fix i assume "i ∈ {0..<Kart} - {k. k < Kart ∧ fst_all!(m+k)=v}"
      hence "¬ fst_all!(m+i)=v" by (auto simp del: NS.fst_exec_eq NS.snd_exec_eq)
      thus "(if fst_all!(m+i)=v then ds_aflw ?bt!i else 0) = 0" by (rule if_not_P)
    qed
  next
    fix x assume "x ∈ {k. k < Kart ∧ fst_all!(m+k)=v}"
    hence "fst_all!(m+x)=v" by (auto simp del: NS.fst_exec_eq NS.snd_exec_eq)
    thus "(if fst_all!(m+x)=v then ds_aflw ?bt!x else 0) = ds_aflw ?bt!x" by (rule if_P)
  qed
  have "aex ?bt v = (∑k = 0..<Kart. if ds_asnd ?bt!k=v then ds_aflw ?bt!k else 0) - (∑k = 0..<Kart. if ds_afst ?bt!k=v then ds_aflw ?bt!k else 0)"
    by (simp add: aex_def nxtK sum_subtractf)
  also have "… = (∑k∈{k. k<Kart ∧ snd_all!(m+k)=v}. ds_aflw ?bt!k) - (∑k∈{k. k<Kart ∧ fst_all!(m+k)=v}. ds_aflw ?bt!k)"
    by (simp only: Mcong Mrestr Pcong Prestr)
  also have "… = (∑e∈NS.delta_minus v ∩ {m..<m+Kart}. flow_all ! e) - (∑e∈NS.delta_plus v ∩ {m..<m+Kart}. flow_all ! e)"
    by (simp only: art_reindex_minus[symmetric] art_reindex_plus[symmetric])
  finally show ?thesis .
qed

lemma ex_flow_all_real_vertex:
  assumes v: "v ∈ set vs_list"
  shows "NS.ex (h ∘ nth flow_all) v = original_network.ex (h ∘ nth acyc_flow) v - h (imbalance!v)"
proof -
  have "h ((∑e∈NS.delta_minus v ∩ {m..<m+Kart}. flow_all ! e) - (∑e∈NS.delta_plus v ∩ {m..<m+Kart}. flow_all ! e)) = h (- imbalance!v)"
    using aex_eq_art_part[of v] build_tree_aex[OF v] by simp
  thus ?thesis using ex_flow_all_decomp[of v] by simp
qed

subsection ‹@{text init_bflow}: the assembled flow is a @{term b_lookup}-flow (Some branch)›

text ‹The augmented @{const flow_all} is capacity-feasible on both branches
      and, on the @{term Some} branch, balances @{const b_lookup} at every augmented vertex: at a real
      vertex because @{const acyc_flow} preserves the frozen excess (@{thm make_acyclic_ex}) which the
      artificial edge corrects by @{term ‹imbalance ! v›}, and at the root because the imbalances sum to
      zero. Together these discharge @{text init_bflow}.›

lemma excess_is_orig_ex:
  assumes v: "v < Suc vcount"
  shows "original_network.ex (h ∘ nth flow_list) v = h (excess ! v)"
proof -
  have dm: "original_network.delta_minus v = {e ∈ {0..<m}. snd_list ! e = v}"
    by (auto simp: original_network.delta_minus_def snd_all_real)
  have dp: "original_network.delta_plus v = {e ∈ {0..<m}. fst_list ! e = v}"
    by (auto simp: original_network.delta_plus_def fst_all_real)
  have key: "⋀P. (∑e∈{e ∈ {0..<m}. P e}. h (flow_list ! e)) = h (∑e∈{0..<m}. if P e then flow_list ! e else 0)"
  proof -
    fix P :: "nat ⇒ bool"
    have "h (∑e∈{0..<m}. if P e then flow_list ! e else 0) = (∑e∈{0..<m}. h (if P e then flow_list ! e else 0))"
      by (rule h_sum)
    also have "… = (∑e∈{0..<m}. if P e then h (flow_list ! e) else 0)"
      by (rule sum.cong[OF refl]) simp
    also have "… = (∑e∈{e ∈ {0..<m}. P e}. h (flow_list ! e))"
      by (rule sum.mono_neutral_cong_right) auto
    finally show "(∑e∈{e ∈ {0..<m}. P e}. h (flow_list ! e)) = h (∑e∈{0..<m}. if P e then flow_list ! e else 0)" ..
  qed
  have "original_network.ex (h ∘ nth flow_list) v
      = (∑e∈{e ∈ {0..<m}. snd_list ! e = v}. h (flow_list ! e)) - (∑e∈{e ∈ {0..<m}. fst_list ! e = v}. h (flow_list ! e))"
    by (simp add: original_network.ex_def dm dp comp_def)
  also have "… = h (∑e∈{0..<m}. if snd_list ! e = v then flow_list ! e else 0) - h (∑e∈{0..<m}. if fst_list ! e = v then flow_list ! e else 0)"
    by (simp only: key)
  also have "… = h ((∑e∈{0..<m}. if snd_list ! e = v then flow_list ! e else 0) - (∑e∈{0..<m}. if fst_list ! e = v then flow_list ! e else 0))"
    by (simp add: h_diff)
  also have "… = h (excess ! v)" using excess_nth_sum[OF v] by simp
  finally show ?thesis .
qed

lemma orig_ex_acyc_eq_excess:
  assumes some: "acyc_flow_opt = Some f'" and v: "v < Suc vcount"
  shows "original_network.ex (h ∘ nth acyc_flow) v = h (excess ! v)"
proof -
  have vv: "vtx_invar ⦇vi_list = edged_vs_list, vi_pos = 0⦈"
    using distinct_vs_list by (simp add: vtx_invar_def edged_vs_list_def distinct_filter)
  have vab: "vtx_abstract ⦇vi_list = edged_vs_list, vi_pos = 0⦈ ⊆ original_network.𝒱"
    by (simp add: vtx_abstract_def V_orig_eq_edged)
  have ff: "length flow_list = m" using length_flow length_edges by simp
  have res: "make_acyclic flow_list = Some f'" using some by (simp add: acyc_flow_opt_def)
  have "original_network.ex (h ∘ (!) f') v = original_network.ex (h ∘ (!) flow_list) v"
    using make_acyclic_ex[OF multigraph_inv_csr ff af_cap_feasible_flow_list vv vab res] .
  moreover have "acyc_flow = f'" using some by (simp add: acyc_flow_def)
  ultimately show ?thesis using excess_is_orig_ex[OF v] by simp
qed

text ‹∗‹Pass A's excess for an arbitrary flow.›  @{const excess} is defined as the excess component of
      @{term ‹passA flow_list›} — the ∗‹frozen› input flow — but the executable pipeline runs Pass A on
      the ∗‹acyclified› flow instead.  The three lemmas below generalise @{thm excess_nth} /
      @{thm excess_is_orig_ex} from @{term flow_list} to any @{term fl} (the underlying fold lemma
      @{thm passA_fold_exc} is already flow-generic), and then close the loop: since the acyclifier
      preserves every vertex's excess (@{thm orig_ex_acyc_eq_excess}) and @{term h} is injective
      (@{thm h_eq_iff}), running Pass A on @{const acyc_flow} yields ∗‹literally› @{const excess}.
      This is what lets the imperative refinement identify its in-place excess array — computed from
      the acyclified flow — with the functional @{const imbalance}, which is anchored to
      @{const excess}.›

lemma passA_exc_len: "length (fst (snd (passA fl))) = Suc vcount"
  using sized_passA[of fl] by (cases "passA fl") (simp add: sized_def)

lemma passA_exc_nth:
  assumes v: "v < Suc vcount"
  shows "fst (snd (passA fl)) ! v =
           (∑e←[0..<m]. (if snd_list ! e = v then fl ! e else 0))
         - (∑e←[0..<m]. (if fst_list ! e = v then fl ! e else 0))"
proof -
  have sz0: "sized (replicate m InL, replicate (Suc vcount) (0::'n), csr_edges out_csr, out_lo,
                csr_edges in_csr, in_lo)"
    by (simp add: sized_def length_out_lo length_in_lo out_csr_eq in_csr_eq)
  show ?thesis
    using passA_fold_exc[OF sz0 v, where xs = "[0..<m]" and fl = fl] v
    by (simp add: passA_def del: replicate_Suc)
qed

lemma ex_is_passA_exc:
  assumes v: "v < Suc vcount"
  shows "original_network.ex (h ∘ nth fl) v = h (fst (snd (passA fl)) ! v)"
proof -
  have dm: "original_network.delta_minus v = {e ∈ {0..<m}. snd_list ! e = v}"
    by (auto simp: original_network.delta_minus_def snd_all_real)
  have dp: "original_network.delta_plus v = {e ∈ {0..<m}. fst_list ! e = v}"
    by (auto simp: original_network.delta_plus_def fst_all_real)
  have key: "⋀P. (∑e∈{e ∈ {0..<m}. P e}. h (fl ! e)) = h (∑e∈{0..<m}. if P e then fl ! e else 0)"
  proof -
    fix P :: "nat ⇒ bool"
    have "h (∑e∈{0..<m}. if P e then fl ! e else 0) = (∑e∈{0..<m}. h (if P e then fl ! e else 0))"
      by (rule h_sum)
    also have "… = (∑e∈{0..<m}. if P e then h (fl ! e) else 0)"
      by (rule sum.cong[OF refl]) simp
    also have "… = (∑e∈{e ∈ {0..<m}. P e}. h (fl ! e))"
      by (rule sum.mono_neutral_cong_right) auto
    finally show "(∑e∈{e ∈ {0..<m}. P e}. h (fl ! e)) = h (∑e∈{0..<m}. if P e then fl ! e else 0)" ..
  qed
  have "original_network.ex (h ∘ nth fl) v
      = (∑e∈{e ∈ {0..<m}. snd_list ! e = v}. h (fl ! e)) - (∑e∈{e ∈ {0..<m}. fst_list ! e = v}. h (fl ! e))"
    by (simp add: original_network.ex_def dm dp comp_def)
  also have "… = h (∑e∈{0..<m}. if snd_list ! e = v then fl ! e else 0) - h (∑e∈{0..<m}. if fst_list ! e = v then fl ! e else 0)"
    by (simp only: key)
  also have "… = h ((∑e∈{0..<m}. if snd_list ! e = v then fl ! e else 0) - (∑e∈{0..<m}. if fst_list ! e = v then fl ! e else 0))"
    by (simp add: h_diff)
  also have "… = h (fst (snd (passA fl)) ! v)"
    using passA_exc_nth[OF v] by (simp add: interv_sum_list_conv_sum_set_nat)
  finally show ?thesis .
qed

lemma passA_exc_acyc:
  assumes some: "acyc_flow_opt = Some f'"
  shows "fst (snd (passA acyc_flow)) = excess"
proof (rule nth_equalityI)
  show "length (fst (snd (passA acyc_flow))) = length excess"
    by (simp add: passA_exc_len)
next
  fix i assume "i < length (fst (snd (passA acyc_flow)))"
  hence v: "i < Suc vcount" by (simp add: passA_exc_len)
  have "h (fst (snd (passA acyc_flow)) ! i) = original_network.ex (h ∘ nth acyc_flow) i"
    by (rule ex_is_passA_exc[OF v, symmetric])
  also have "… = h (excess ! i)" by (rule orig_ex_acyc_eq_excess[OF some v])
  finally show "fst (snd (passA acyc_flow)) ! i = excess ! i" by simp
qed

lemma bflow_flow_all_real:
  assumes some: "acyc_flow_opt = Some f'" and v: "v ∈ set vs_list"
  shows "- NS.ex (h ∘ nth flow_all) v = h (b_lookup v)"
proof -
  have vlt: "v < vcount" using v vs_less_vcount by simp
  have vlt': "v < Suc vcount" using vlt by simp
  have "NS.ex (h ∘ nth flow_all) v = original_network.ex (h ∘ nth acyc_flow) v - h (imbalance!v)" by (rule ex_flow_all_real_vertex[OF v])
  also have "… = h (excess!v) - h (imbalance!v)" using orig_ex_acyc_eq_excess[OF some vlt'] by simp
  also have "… = - h (b_lookup v)" using imbalance_nth[OF vlt] by (simp add: h_add)
  finally show ?thesis by simp
qed

lemma aex_build_tree_generic:
  "aex (build_tree acyc_flow) w = (∑v←vs_list. (if w = v then - imbalance!v else if w = vcount then imbalance!v else 0))"
proof -
  have invi: "dfs_inv acyc_flow dfs_init" by (rule dfs_init_inv)
  have stki: "ds_stk dfs_init = []" by (simp add: dfs_init_def)
  have E0: "({}::nat set) ⊆ {v ∈ set vs_list. ds_seen dfs_init ! v}" by simp
  have E0d: "({}::nat set) ∩ set vs_list = {}" by simp
  have nxt0: "ds_nxt dfs_init = card ({}::nat set)" by (simp add: dfs_init_def)
  note P1 = fold_phase1_aex[OF distinct_vs_list order_refl invi stki dfs_init_art_len finite.emptyI E0 E0d nxt0, of w]
  have aex_p1: "aex (phase1 acyc_flow dfs_init) w = (∑v←vs_list. (if w = v then - imbalance!v else if w = vcount then imbalance!v else 0))"
    using P1 aex_dfs_init unfolding phase1_def by simp
  have al_p1: "art_len (phase1 acyc_flow dfs_init)" using P1 unfolding phase1_def by simp
  have inv_p1: "dfs_inv acyc_flow (phase1 acyc_flow dfs_init)" using P1 unfolding phase1_def by simp
  have stk_p1: "ds_stk (phase1 acyc_flow dfs_init) = []" using P1 unfolding phase1_def by simp
  obtain E1 where E1: "finite E1" "E1 ⊆ {v ∈ set vs_list. ds_seen (phase1 acyc_flow dfs_init) ! v}" "ds_nxt (phase1 acyc_flow dfs_init) = card E1"
    using P1 unfolding phase1_def by blast
  have bal: "∀u ∈ set vs_list. ¬ ds_seen (phase1 acyc_flow dfs_init) ! u ⟶ imbalance!u = 0"
  proof (intro ballI impI)
    fix u assume uvs: "u ∈ set vs_list" and uns: "¬ ds_seen (phase1 acyc_flow dfs_init) ! u"
    show "imbalance!u = 0"
    proof (rule ccontr)
      assume "imbalance!u ≠ 0"
      hence "ds_seen (phase1 acyc_flow dfs_init) ! u"
        using fold_phase1_imb_seen[OF order_refl invi stki] uvs unfolding phase1_def by simp
      thus False using uns by simp
    qed
  qed
  note P2 = fold_phase2_aex[OF order_refl inv_p1 stk_p1 al_p1 E1(1) E1(2) E1(3) bal, of w]
  have aex_p2: "aex (phase2 acyc_flow (phase1 acyc_flow dfs_init)) w = aex (phase1 acyc_flow dfs_init) w"
    using P2 unfolding phase2_def by simp
  have aex_bt: "aex (build_tree acyc_flow) w = aex (phase2 acyc_flow (phase1 acyc_flow dfs_init)) w"
    by (simp add: build_tree_def Let_def aex_lsuc)
  show ?thesis using aex_bt aex_p2 aex_p1 by simp
qed

lemma aex_build_tree_root: "aex (build_tree acyc_flow) vcount = (∑v←vs_list. imbalance!v)"
proof -
  have "aex (build_tree acyc_flow) vcount = (∑v←vs_list. (if vcount = v then - imbalance!v else if vcount = vcount then imbalance!v else 0))"
    by (rule aex_build_tree_generic)
  also have "… = (∑v←vs_list. imbalance!v)"
    by (rule arg_cong[where f=sum_list], rule map_cong[OF refl]) (auto dest: vs_less_vcount)
  finally show ?thesis .
qed

lemma b_lookup_nonvertex:
  assumes w: "w < Suc vcount" and wv: "w ∉ set vs_list"
  shows "b_lookup w = 0"
proof -
  have "⋀v x. (v, x) ∈ set (zip vs_list b_list) ⟹ v ≠ w"
    using wv by (auto dest: set_zip_leftD)
  hence "b_arr ! w = replicate (Suc vcount) (0::'n) ! w"
    unfolding b_arr_def by (rule foldl_scatter_miss)
  moreover have "replicate (Suc vcount) (0::'n) ! w = 0" using w by (simp add: nth_replicate del: replicate_Suc)
  ultimately show ?thesis by (simp add: b_lookup_def)
qed

lemma imbalance_nonvertex:
  assumes w: "w < Suc vcount" and wv: "w ∉ set vs_list"
  shows "imbalance ! w = 0"
proof -
  have ex0: "excess ! w = 0"
    using excess_is_orig_ex[OF w] orig_ex_notin_V[OF wv] by simp
  show ?thesis
  proof (cases "w = vcount")
    case True thus ?thesis using ex0 imbalance_root by simp
  next
    case False
    hence nlt: "w < vcount" using w by simp
    show ?thesis using imbalance_nth[OF nlt] ex0 b_lookup_nonvertex[OF w wv] by simp
  qed
qed

lemma sum_imbalance_vs_list_zero: "(∑v←vs_list. imbalance!v) = 0"
proof -
  have "(∑v←vs_list. imbalance!v) = (∑v∈set vs_list. imbalance!v)"
    by (rule sum_list_distinct_conv_sum_set[OF distinct_vs_list])
  also have "… = (∑v∈{0..<Suc vcount}. imbalance!v)"
  proof (rule sum.mono_neutral_left)
    show "finite {0..<Suc vcount}" by simp
    show "set vs_list ⊆ {0..<Suc vcount}" by (auto dest: vs_less_vcount)
    show "∀v∈{0..<Suc vcount} - set vs_list. imbalance!v = 0"
    proof (intro ballI)
      fix v assume "v ∈ {0..<Suc vcount} - set vs_list"
      hence "v < Suc vcount" "v ∉ set vs_list" by auto
      thus "imbalance!v = 0" by (rule imbalance_nonvertex)
    qed
  qed
  also have "… = 0" by (rule sum_imbalance_zero)
  finally show ?thesis .
qed

lemma vcount_notin_vs: "vcount ∉ set vs_list" using vs_less_vcount by fastforce

lemma bflow_flow_all_root: "- NS.ex (h ∘ nth flow_all) vcount = h (b_lookup vcount)"
proof -
  have "NS.ex (h ∘ nth flow_all) vcount = original_network.ex (h ∘ nth acyc_flow) vcount + h (aex (build_tree acyc_flow) vcount)"
    using ex_flow_all_decomp[of vcount] by (simp add: aex_eq_art_part[symmetric])
  also have "… = 0 + 0"
    using orig_ex_notin_V[OF vcount_notin_vs] aex_build_tree_root sum_imbalance_vs_list_zero by simp
  finally have "NS.ex (h ∘ nth flow_all) vcount = 0" by simp
  thus ?thesis using b_lookup_root by simp
qed

lemma isuflow_flow_all: "NS.isuflow (h ∘ nth flow_all)"
proof (unfold NS.isuflow_def comp_def, rule ballI)
  fix e assume e: "e ∈ {0..<m + Kart}"
  hence emK: "e < m + Kart" by simp
  show "ereal (h (nth flow_all e)) ≤ (if e < m + Kart then if cap_all ! e = - 1 then ∞ else ereal (h (cap_all ! e)) else ∞) ∧ 0 ≤ h (nth flow_all e)"
  proof (cases "e < m")
    case True
    have fe: "nth flow_all e = acyc_flow ! e" using flook[OF emK] flow_all_real[OF True] by simp
    have nn: "0 ≤ acyc_flow ! e" by (rule acyc_flow_nonneg[OF True])
    have cc: "cap_all ! e = capacity_list ! e" by (rule cap_all_real[OF True])
    show ?thesis
    proof (cases "capacity_list ! e = - 1")
      case True thus ?thesis using fe nn cc emK by simp
    next
      case False
      have "acyc_flow ! e ≤ capacity_list ! e" using acyc_flow_le_cap[OF ‹e < m› False] .
      thus ?thesis using fe nn cc False emK by simp
    qed
  next
    case False
    then obtain k where ek: "e = m + k" by (metis add.commute le_Suc_ex not_less)
    have kK: "k < Kart" using emK ek by simp
    obtain subj where subj: "subj < vcount"
      and aflw: "ds_aflw (build_tree acyc_flow) ! k = art_flow subj"
      and cap: "(ds_aest (build_tree acyc_flow) ! k = InTree ∧ ds_acap (build_tree acyc_flow) ! k = art_tree_cap subj)
              ∨ (ds_aest (build_tree acyc_flow) ! k = InU ∧ ds_acap (build_tree acyc_flow) ! k = art_flow subj)"
      using tail_edge_ok_build_tree[OF kK] by (auto simp: tail_edge_ok_def)
    have fe: "nth flow_all e = art_flow subj" using flook[OF emK] ek kK flow_all_art aflw by simp
    have ce: "cap_all ! e = ds_acap (build_tree acyc_flow) ! k" using ek kK cap_all_art by simp
    have nn: "0 ≤ art_flow subj" by (simp add: art_flow_def)
    have le: "art_flow subj ≤ ds_acap (build_tree acyc_flow) ! k"
      using cap by (auto simp: art_tree_cap_def art_flow_def)
    have cnn: "0 ≤ ds_acap (build_tree acyc_flow) ! k" using nn le by simp
    have "cap_all ! e ≠ - 1" using ce cnn by simp
    thus ?thesis using fe ce nn le emK by simp
  qed
qed

lemma NSinit_bflow:
  assumes some: "acyc_flow_opt = Some f'"
  shows "NS.isbflow (h ∘ nth flow_all) (λv. h (b_lookup v))"
proof (rule NS.isbflowI)
  show "NS.isuflow (h ∘ nth flow_all)" by (rule isuflow_flow_all)
next
  fix v assume vV: "v ∈ NS.𝒱"
  have "v = vcount ∨ v ∈ set vs_list" using vV NS_V_minus_root V_sub_vs_list Vseen_eq_V by auto
  thus "- NS.ex (h ∘ nth flow_all) v = h (b_lookup v)"
  proof
    assume "v = vcount" thus ?thesis using bflow_flow_all_root by simp
  next
    assume "v ∈ set vs_list" thus ?thesis using bflow_flow_all_real[OF some] by simp
  qed
qed








subsection ‹Acyclicity of the acyclified flow on the Some branch (architecture keystone)›

text ‹On the branch where the acyclifier returns a flow (acyc_flow_opt = Some), that flow is genuinely
      acyclic: make_acyclic_correct_unconditional certifies it, the freshly-built counting-sort CSRs
      have nothing iterated yet (csr_lo = csr_cur), and the vertex list abstracts to exactly the vertex
      set. This is the hypothesis under which the initial-basis interpretation's acyclicity-dependent
      obligations (free-edge coverage / init_partition) become provable; it is discharged at the use
      site, inside solve on the Some branch.›

lemma csr_fresh_scatter: "csr_iterated (build_csr_scatter nn key es dflt) u = {}"
  by (simp add: csr_iterated_def csr_seg_it_def build_csr_scatter_lo_sel build_csr_scatter_cur_sel)

lemma out_in_csr_fresh: "csr_iterated out_csr u = {}" "csr_iterated in_csr u = {}"
  by (simp_all add: out_csr_eq in_csr_eq csr_fresh_scatter)

lemma acyc_of_some:
  assumes some: "acyc_flow_opt = Some f'"
  shows "original_network.acyclic_flow (h ∘ nth acyc_flow)"
proof -
  have vv: "vtx_invar ⦇vi_list = edged_vs_list, vi_pos = 0⦈"
    using distinct_vs_list by (simp add: vtx_invar_def edged_vs_list_def distinct_filter)
  have vabsV: "vtx_abstract ⦇vi_list = edged_vs_list, vi_pos = 0⦈ = original_network.𝒱"
    by (simp add: vtx_abstract_def V_orig_eq_edged)
  have vit0: "vtx_iterated ⦇vi_list = edged_vs_list, vi_pos = 0⦈ = {}" by (simp add: vtx_iterated_def)
  have ff: "length flow_list = m" using length_flow length_edges by simp
  have fresh: "∀u. csr_iterated out_csr u = {} ∧ csr_iterated in_csr u = {}"
    using out_in_csr_fresh by simp
  have res: "make_acyclic flow_list = Some f'" using some by (simp add: acyc_flow_opt_def)
  have "original_network.acyclic_flow (h ∘ (!) f')"
    using make_acyclic_correct_unconditional[OF multigraph_inv_csr ff af_cap_feasible_flow_list vv vabsV vit0 fresh res] by blast
  thus ?thesis using some by (simp add: acyc_flow_def)
qed





lemma solve_none: "acyc_flow_opt = None ⟹ solve = Neg_inf_cycle" by (simp add: solve_def)

lemma NSinit_bflow_ne:
  assumes "acyc_flow_opt ≠ None" shows "NS.isbflow (h ∘ nth flow_all) (λv. h (b_lookup v))"
  using assms by (cases acyc_flow_opt) (auto intro: NSinit_bflow)

lemma NSinit_partition_ne:
  assumes ne: "acyc_flow_opt ≠ None"
  shows "NS.spanning_tree_partition vcount ((!) (ds_par (build_tree acyc_flow)) ` (NS.𝒱 - {vcount})) {e ∈ {0..<m + Kart}. state_all ! e = InL} {e ∈ {0..<m + Kart}. state_all ! e = InU}"
proof -
  obtain f' where sf: "acyc_flow_opt = Some f'" using ne by (cases acyc_flow_opt) auto
  show ?thesis by (rule NSinit_partition[OF acyc_of_some[OF sf]])
qed

text ‹Relabelling a spanning-tree partition: the tree-structure conjuncts depend only on @{term T},
      so any @{term L'} / @{term U'} that cover the same edges and stay disjoint from @{term T} and
      each other yield another valid partition. This lets the augmented (cost-folded) self-loop
      partition reuse the plain tag partition's arborescence facts.›

lemma spanning_tree_partition_relabel:
  assumes p: "NS.spanning_tree_partition r T L U"
    and cov: "T ∪ U' ∪ L' = T ∪ U ∪ L"
    and d1: "T ∩ U' = {}" and d2: "T ∩ L' = {}" and d3: "L' ∩ U' = {}"
  shows "NS.spanning_tree_partition r T L' U'"
proof -
  note pd = p[unfolded NS.spanning_tree_partition_def]
  have cov': "{0..<m + Kart} = T ∪ U' ∪ L'"
  proof -
    have "{0..<m + Kart} = T ∪ U ∪ L" using pd by simp
    thus ?thesis using cov by simp
  qed
  show ?thesis
    unfolding NS.spanning_tree_partition_def
    using cov' d1 d2 d3 pd by blast
qed

text ‹Artificial edges run between a component root and the artificial root @{const vcount}, which are
      distinct, so no artificial edge is a self-loop.›

lemma art_not_selfloop:
  assumes k: "m ≤ e" and elt: "e < m + Kart"
  shows "fst_all ! e ≠ snd_all ! e"
proof -
  obtain k' where k': "e = m + k'" and kK: "k' < Kart"
    using k elt by (metis add.commute le_Suc_ex nat_add_left_cancel_less add_diff_inverse_nat not_le)
  have tok: "tail_edge_ok (build_tree acyc_flow) k'" using kK tail_edge_ok_build_tree by simp
  then obtain subj where s1: "subj < vcount"
      and s2: "ds_afst (build_tree acyc_flow) ! k' = (if art_dir subj then subj else vcount)"
      and s3: "ds_asnd (build_tree acyc_flow) ! k' = (if art_dir subj then vcount else subj)"
    unfolding tail_edge_ok_def by auto
  have fa: "fst_all ! e = ds_afst (build_tree acyc_flow) ! k'" unfolding k' by (rule fst_all_art[OF kK])
  have sa: "snd_all ! e = ds_asnd (build_tree acyc_flow) ! k'" unfolding k' by (rule snd_all_art[OF kK])
  have neq: "subj ≠ vcount" using less_imp_neq[OF s1] .
  show ?thesis using fa sa s2 s3 neq by (cases "art_dir subj") auto
qed

text ‹‹make_acyclic_selfloop›, specialised to the acyclified flow @{const acyc_flow} of the Some
      branch: a real self-loop is emptied when its cost is non-negative and saturated when negative.›

lemma acyc_flow_selfloop:
  assumes ne: "acyc_flow_opt ≠ None" and em: "e < m" and esl: "fst_list ! e = snd_list ! e"
  shows "(0 ≤ cost_list ! e ⟶ acyc_flow ! e = 0) ∧ (cost_list ! e < 0 ⟶ acyc_flow ! e = capacity_list ! e)"
proof -
  obtain f' where sf: "acyc_flow_opt = Some f'" using ne by (cases acyc_flow_opt) auto
  have vv: "vtx_invar ⦇vi_list = edged_vs_list, vi_pos = 0⦈"
    using distinct_vs_list by (simp add: vtx_invar_def edged_vs_list_def distinct_filter)
  have vabsV: "vtx_abstract ⦇vi_list = edged_vs_list, vi_pos = 0⦈ = original_network.𝒱"
    by (simp add: vtx_abstract_def V_orig_eq_edged)
  have vit0: "vtx_iterated ⦇vi_list = edged_vs_list, vi_pos = 0⦈ = {}" by (simp add: vtx_iterated_def)
  have ff: "length flow_list = m" using length_flow length_edges by simp
  have fresh: "∀u. csr_iterated out_csr u = {} ∧ csr_iterated in_csr u = {}" using out_in_csr_fresh by simp
  have res: "make_acyclic flow_list = Some f'" using sf by (simp add: acyc_flow_opt_def)
  have af: "acyc_flow = f'" using sf by (simp add: acyc_flow_def)
  have eE: "e ∈ {0..<m}" using em by simp
  have main: "(0 ≤ cost_list ! e ⟶ f' ! e = 0) ∧ (cost_list ! e < 0 ⟶ f' ! e = capacity_list ! e)"
    using make_acyclic_selfloop[OF multigraph_inv_csr ff af_cap_feasible_flow_list vv vabsV vit0 res fresh eE] esl em by simp
  thus ?thesis using af by simp
qed

text ‹Obligation (‹init_selfloop›): a self-loop of the initial basis carries the cost-directed
      bound the acyclifier fixes — zero flow when @{term ‹0 ≤ 𝖼›}, saturation when @{term ‹𝖼 < 0›}.
      Artificial edges are not self-loops, so only the real edges contribute, discharged by
      @{thm acyc_flow_selfloop}; feasibility rules out the infinite-capacity negative case.›

lemma NSinit_selfloop:
  assumes ne: "acyc_flow_opt ≠ None"
  shows "∀e∈{0..<m + Kart}. (if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart)))) = (if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart)))) ⟶ (0 ≤ cost_all ! e ⟶ flow_all ! e = 0) ∧ (cost_all ! e < 0 ⟶ ereal (h (flow_all ! e)) = (if e < m + Kart then if cap_all ! e = - 1 then ∞ else ereal (h (cap_all ! e)) else ∞))"
proof (intro ballI impI)
  fix e assume e: "e ∈ {0..<m + Kart}"
    and sl: "(if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart)))) = (if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart))))"
  have elt: "e < m + Kart" using e by simp
  have slr: "fst_all ! e = snd_all ! e" using sl elt by argo
  have em: "e < m" using slr elt art_not_selfloop by (metis not_le)
  have flr: "fst_list ! e = snd_list ! e" using slr fst_all_real[OF em] snd_all_real[OF em] by simp
  have core: "(0 ≤ cost_list ! e ⟶ acyc_flow ! e = 0) ∧ (cost_list ! e < 0 ⟶ acyc_flow ! e = capacity_list ! e)"
    using acyc_flow_selfloop[OF ne em flr] .
  have ce: "cost_all ! e = h (cost_list ! e)" using cost_all_real[OF em] .
  have fe: "flow_all ! e = acyc_flow ! e" using flow_all_real[OF em] .
  have cae: "cap_all ! e = capacity_list ! e" using cap_all_real[OF em] .
  show "(0 ≤ cost_all ! e ⟶ flow_all ! e = 0) ∧ (cost_all ! e < 0 ⟶ ereal (h (flow_all ! e)) = (if e < m + Kart then if cap_all ! e = - 1 then ∞ else ereal (h (cap_all ! e)) else ∞))"
  proof (intro conjI impI)
    assume "0 ≤ cost_all ! e"
    thus "flow_all ! e = 0" using core ce fe by simp
  next
    assume neg: "cost_all ! e < 0"
    hence fcap: "flow_all ! e = capacity_list ! e" using core ce fe by simp
    have "0 ≤ acyc_flow ! e" using acyc_flow_nonneg[OF em] .
    hence "cap_all ! e ≠ - 1" using fcap fe cae by simp
    thus "ereal (h (flow_all ! e)) = (if e < m + Kart then if cap_all ! e = - 1 then ∞ else ereal (h (cap_all ! e)) else ∞)"
      using fcap cae elt by simp
  qed
qed

text ‹Obligation (‹init_flow_fits›) in its non-self-loop form: it follows by monotonicity from
      the full flow fit @{thm NSinit_flow_fits} (fewer edges are constrained).›

lemma NSinit_flow_fits_ns:
  "NS.flow_fits_spanning_tree_partition ((!) (ds_par (build_tree acyc_flow)) ` (NS.𝒱 - {vcount})) {e ∈ {0..<m + Kart}. (if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart)))) ≠ (if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart)))) ∧ state_all ! e = InL} {e ∈ {0..<m + Kart}. (if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart)))) ≠ (if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart)))) ∧ state_all ! e = InU} (h ∘ (!) flow_all)"
  using NSinit_flow_fits by (auto simp: NS.flow_fits_spanning_tree_partition_def comp_def)

text ‹Obligation (‹init_partition›): the augmented partition folds self-loops into @{term L} /
      @{term U} by cost. It reuses the plain tag partition's tree facts via
      @{thm spanning_tree_partition_relabel}; the cover matches because every self-loop is covered by
      the cost split, and the tree carries no self-loop (@{thm art_not_selfloop} / the graph invariant).›

lemma NSinit_partition_aug:
  assumes ne: "acyc_flow_opt ≠ None"
  shows "NS.spanning_tree_partition vcount ((!) (ds_par (build_tree acyc_flow)) ` (NS.𝒱 - {vcount})) ({e ∈ {0..<m + Kart}. (if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart)))) ≠ (if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart)))) ∧ state_all ! e = InL} ∪ NS.ns_selfloops_L) ({e ∈ {0..<m + Kart}. (if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart)))) ≠ (if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart)))) ∧ state_all ! e = InU} ∪ NS.ns_selfloops_U)"
proof -
  obtain f' where sf: "acyc_flow_opt = Some f'" using ne by (cases acyc_flow_opt) auto
  have acyc: "original_network.acyclic_flow (h ∘ nth acyc_flow)" using acyc_of_some[OF sf] .
  let ?T = "(!) (ds_par (build_tree acyc_flow)) ` (NS.𝒱 - {vcount})"
  let ?L = "{e ∈ {0..<m + Kart}. state_all ! e = InL}"
  let ?U = "{e ∈ {0..<m + Kart}. state_all ! e = InU}"
  let ?F = "λe. if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart)))"
  let ?S = "λe. if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart)))"
  let ?aL = "{e ∈ {0..<m + Kart}. ?F e ≠ ?S e ∧ state_all ! e = InL} ∪ NS.ns_selfloops_L"
  let ?aU = "{e ∈ {0..<m + Kart}. ?F e ≠ ?S e ∧ state_all ! e = InU} ∪ NS.ns_selfloops_U"
  have plain: "NS.spanning_tree_partition vcount ?T ?L ?U" using NSinit_partition[OF acyc] .
  note pd = plain[unfolded NS.spanning_tree_partition_def]
  have coverP: "{0..<m + Kart} = ?T ∪ ?U ∪ ?L" using pd by argo
  have dTU: "?T ∩ ?U = {}" using pd by blast
  have dTL: "?T ∩ ?L = {}" using pd by blast
  have slL: "NS.ns_selfloops_L = {e ∈ {0..<m + Kart}. ?F e = ?S e ∧ 0 ≤ cost_all ! e}"
    by (simp add: NS.ns_selfloops_L_def)
  have slU: "NS.ns_selfloops_U = {e ∈ {0..<m + Kart}. ?F e = ?S e ∧ cost_all ! e < 0}"
    by (simp add: NS.ns_selfloops_U_def)
  have Tnsl: "⋀d. d ∈ ?T ⟹ ?F d ≠ ?S d"
  proof -
    fix d assume d: "d ∈ ?T"
    have mem: "{?F d, ?S d} ∈ abstract_arb Sarb" using d tc_image by blast
    have dbl: "dblton_graph (abstract_arb Sarb)" using graph_invar_abstract_arb[OF arb_invar_Sarb] by simp
    obtain u v where uv: "{?F d, ?S d} = {u, v}" and une: "u ≠ v" using dbl mem unfolding dblton_graph_def by blast
    show "?F d ≠ ?S d"
    proof
      assume "?F d = ?S d"
      hence "{u, v} = {?F d}" using uv by simp
      thus False using une by blast
    qed
  qed
  ― ‹Arithmetic facts fed to @{method blast} (which cannot do them itself); @{method blast} keeps the
      @{term ?F} / @{term ?S} ‹if›-lambdas opaque, so it never diverges on @{term prod_decode}.›
  have cost_tri: "⋀x. cost_all ! x < 0 ∨ 0 ≤ cost_all ! x" by auto
  have cost_contra: "⋀x. 0 ≤ cost_all ! x ⟹ cost_all ! x < 0 ⟹ False" by simp
  show ?thesis
  proof (rule spanning_tree_partition_relabel[OF plain])
    show "?T ∪ ?aU ∪ ?aL = ?T ∪ ?U ∪ ?L" using coverP cost_tri unfolding slL slU by blast
    show "?T ∩ ?aU = {}" using dTU Tnsl unfolding slU by blast
    show "?T ∩ ?aL = {}" using dTL Tnsl unfolding slL by blast
    show "?aL ∩ ?aU = {}"
    proof (rule equals0I)
      fix x assume xin: "x ∈ ?aL ∩ ?aU"
      have xLd: "x ∈ {e ∈ {0..<m + Kart}. ?F e ≠ ?S e ∧ state_all ! e = InL} ∨ x ∈ NS.ns_selfloops_L"
        using xin by blast
      have xUd: "x ∈ {e ∈ {0..<m + Kart}. ?F e ≠ ?S e ∧ state_all ! e = InU} ∨ x ∈ NS.ns_selfloops_U"
        using xin by blast
      from xLd xUd show False
      proof (elim disjE)
        assume a: "x ∈ {e ∈ {0..<m + Kart}. ?F e ≠ ?S e ∧ state_all ! e = InL}"
          and b: "x ∈ {e ∈ {0..<m + Kart}. ?F e ≠ ?S e ∧ state_all ! e = InU}"
        have "state_all ! x = InL" using a by blast
        moreover have "state_all ! x = InU" using b by blast
        ultimately show False by simp
      next
        assume a: "x ∈ {e ∈ {0..<m + Kart}. ?F e ≠ ?S e ∧ state_all ! e = InL}"
          and b: "x ∈ NS.ns_selfloops_U"
        have "?F x ≠ ?S x" using a by blast
        moreover have "?F x = ?S x" using b unfolding slU by blast
        ultimately show False by simp
      next
        assume a: "x ∈ NS.ns_selfloops_L"
          and b: "x ∈ {e ∈ {0..<m + Kart}. ?F e ≠ ?S e ∧ state_all ! e = InU}"
        have "?F x = ?S x" using a unfolding slL by blast
        moreover have "?F x ≠ ?S x" using b by blast
        ultimately show False by simp
      next
        assume a: "x ∈ NS.ns_selfloops_L" and b: "x ∈ NS.ns_selfloops_U"
        have "0 ≤ cost_all ! x" using a unfolding slL by blast
        moreover have "cost_all ! x < 0" using b unfolding slU by blast
        ultimately show False by linarith
      qed
    qed
  qed
qed


context
  assumes some: "acyc_flow_opt ≠ None"
begin

interpretation NSinit: network_simplex_init
  where fst = "λ e. if e < m+Kart then fst_all ! e else Product_Type.fst (prod_decode (e - (m+Kart)))"
    and snd = "λ e. if e < m+Kart then snd_all ! e else Product_Type.snd (prod_decode (e - (m+Kart)))"
    and create_edge = "λ u v. (m+Kart) + prod_encode (u, v)"
    and ℰ = "{0..<m+Kart}"
    and 𝗎 = "λ e. if e < m+Kart then (if cap_all ! e = - 1 then ∞ else ereal (h (cap_all ! e))) else ∞"
    and 𝖼 = "λ e. cost_all ! e"
    and r = vcount
    and shift_pot = shift_pot_impl
    and arborescense_invar = "arb_invar vcount Varb"
    and abstract_arborescense = abstract_arb
    and get_path_pair = get_path_pair_impl
    and swap_edge = swap_edge_impl
    and flow_invar = "λxs. ∀k∈{0..<m+Kart}. k < length xs" and flow_upd = list_update and flow_lookup = nth
    and pot_invar = "λxs. ∀v∈Varb. v < length xs" and pot_upd = list_update and pot_lookup = nth
    and parent_invar = "λxs. ∀v∈Varb - {vcount}. v < length xs" and parent_upd = list_update and parent_lookup = nth
    and dir_invar = "λxs. ∀v∈Varb - {vcount}. v < length xs" and dir_upd = list_update and dir_lookup = nth
    and es_invar = "λxs. ∀k∈{0..<m+Kart}. k < length xs" and es_upd = list_update and es_lookup = nth
    and sel_invar = sel_invar_impl and sel_select = sel_select_impl
    and b = "λ v. h (b_lookup v)"
    and cap = "λ e. cap_all ! e"
    and pot_value_invar = "λ p. good_pot_val_c p ∧ pv_invar p"
    and pot_value_abstract = "pval_abstract bigM"
    and pot_value_plus = pval_plus
    and pot_value_minus = pval_minus
    and rcost_invar = rc_invar
    and rcost_abstract = "pval_abstract bigM"
    and fst_exec = "λ e. fst_all ! e"
    and snd_exec = "λ e. snd_all ! e"
    and init_flow = flow_all
    and init_pot = "ds_pot (build_tree acyc_flow)"
    and init_tree = Sarb
    and init_parent = "ds_par (build_tree acyc_flow)"
    and init_dir = "ds_dir (build_tree acyc_flow)"
    and init_edge_state = state_all
    and init_sel = init_sel
  apply unfold_locales
  apply (all ‹(rule NSinit_tree_corr NSinit_strict NSinit_pot_fits NSinit_flow_fits_ns
                     arb_invar_Sarb NSinit_sel_invar
                     NSinit_flow_invar NSinit_es_invar_len NSinit_par_invar NSinit_dir_invar
                     pot_valid_build_tree NSinit_bflow_ne[OF some] NSinit_partition_aug[OF some]
                     NSinit_selfloop[OF some])?›)
  done

lemma solve_init_state:
  "network_simplex_init_spec.init_state flow_all (ds_pot art_tree) (tree_st art_tree)
      (ds_par art_tree) (ds_dir art_tree) state_all init_sel = NSinit.init_state"
  by (simp add: NSinit.init_state_def network_simplex_init_spec.init_state_def Sarb_tree_st)

lemma solve_loop_eq:
  "NS.ns_loop_impl (network_simplex_init_spec.init_state flow_all (ds_pot art_tree) (tree_st art_tree)
      (ds_par art_tree) (ds_dir art_tree) state_all init_sel) = NS.ns_loop NSinit.init_state"
  unfolding solve_init_state
  by (rule NS.ns_loop_dom_impl_same[OF NSinit.network_simplex_correct(1)])

lemma solve_eq:
  "solve = (case acyc_flow_opt of None ⇒ Neg_inf_cycle
            | Some _ ⇒ (let s = NS.ns_loop NSinit.init_state; f = current_flow s
                        in if return s = unbounded then Neg_inf_cycle
                           else if list_all (λk. f ! k = 0) [m..<m + Kart]
                                then Optimum (take m f) else Infeasible))"
  by (simp only: solve_def solve_loop_eq Let_def)

lemma ns_loop_success:
  assumes "return (NS.ns_loop NSinit.init_state) ≠ unbounded"
  shows "return (NS.ns_loop NSinit.init_state) = success"
  using ns_loop_terminates[OF NSinit.network_simplex_correct(1)] assms by blast

lemma solve_not_negI:
  assumes Some: "acyc_flow_opt = Some f'"
    and nu: "return (NS.ns_loop NSinit.init_state) ≠ unbounded"
  shows "solve = (if list_all (λk. current_flow (NS.ns_loop NSinit.init_state) ! k = 0) [m..<m + Kart]
                  then Optimum (take m (current_flow (NS.ns_loop NSinit.init_state))) else Infeasible)"
  unfolding solve_eq Some option.simps Let_def using nu by (rule if_not_P)

lemma solve_ne_neg:
  assumes "acyc_flow_opt = Some f'" and "return (NS.ns_loop NSinit.init_state) ≠ unbounded"
  shows "solve ≠ Neg_inf_cycle"
  using solve_not_negI[OF assms] by simp

lemma solve_neg_inf:
  assumes nc: "solve = Neg_inf_cycle" shows neg_infty_cycle
proof (cases acyc_flow_opt)
  case None
  show ?thesis by (rule acyc_none_neg_cycle[OF None])
next
  case (Some f')
  show ?thesis
  proof (cases "return (NS.ns_loop NSinit.init_state) = unbounded")
    case True
    show ?thesis by (rule aug_neg_cycle_orig[OF NSinit.network_simplex_correct(2)[OF True]])
  next
    case False
    show ?thesis using solve_ne_neg[OF Some False] nc by simp
  qed
qed

lemma flow_all_len: "m ≤ length (current_flow (NS.ns_loop NSinit.init_state))"
proof -
  have "NS.ns_invar (NS.ns_loop NSinit.init_state)"
    by (rule ns_loop_invar[OF NSinit.network_simplex_correct(1) NSinit.init_state_invar])
  hence fi: "∀k∈{0..<m + Kart}. k < length (current_flow (NS.ns_loop NSinit.init_state))"
    by (simp add: NS.ns_invar_def NS.ns_invar_impl_def)
  have "m + Kart - 1 < length (current_flow (NS.ns_loop NSinit.init_state))"
    using fi Kart_pos by simp
  thus ?thesis using Kart_pos by simp
qed

theorem solve_correct_some:
  "solve = Optimum fs ⟹ length fs = m ∧ original_network.is_Opt (λv. h (b_lookup v)) (h ∘ nth fs)"
  "solve = Infeasible ⟹ ∄ f. original_network.isbflow f (λv. h (b_lookup v))"
  "solve = Neg_inf_cycle ⟹ neg_infty_cycle"
proof -
  show "solve = Neg_inf_cycle ⟹ neg_infty_cycle" by (rule solve_neg_inf)
next
  assume A: "solve = Optimum fs"
  obtain f' where Some: "acyc_flow_opt = Some f'"
    using A by (cases acyc_flow_opt) (simp_all add: solve_eq)
  have nu: "return (NS.ns_loop NSinit.init_state) ≠ unbounded"
    using A solve_eq Some by (simp add: Let_def split: if_splits)
  note eq = solve_not_negI[OF Some nu]
  have la: "list_all (λk. current_flow (NS.ns_loop NSinit.init_state) ! k = 0) [m..<m + Kart]"
    using A eq by (simp split: if_splits)
  have fs: "fs = take m (current_flow (NS.ns_loop NSinit.init_state))"
    using A eq la by simp
  have len: "length fs = m" using fs flow_all_len by simp
  have zero: "NS.ns_flow_of (NS.ns_loop NSinit.init_state) k = 0" if "m ≤ k" "k < m + Kart" for k
    using la that by (simp add: list_all_iff)
  have "original_network.is_Opt (λv. h (b_lookup v)) (NS.ns_flow_of (NS.ns_loop NSinit.init_state))"
    by (rule aug_opt_zero_art_orig_opt[OF NSinit.network_simplex_correct(3)[OF ns_loop_success[OF nu]] zero])
  hence "original_network.is_Opt (λv. h (b_lookup v)) (h ∘ nth fs)"
    using fs is_Opt_take[OF flow_all_len] by simp
  thus "length fs = m ∧ original_network.is_Opt (λv. h (b_lookup v)) (h ∘ nth fs)" using len by simp
next
  assume A: "solve = Infeasible"
  obtain f' where Some: "acyc_flow_opt = Some f'"
    using A by (cases acyc_flow_opt) (simp_all add: solve_eq)
  have nu: "return (NS.ns_loop NSinit.init_state) ≠ unbounded"
    using A solve_eq Some by (simp add: Let_def split: if_splits)
  note eq = solve_not_negI[OF Some nu]
  have "¬ list_all (λk. current_flow (NS.ns_loop NSinit.init_state) ! k = 0) [m..<m + Kart]"
    using A eq by (simp split: if_splits)
  hence nzex: "∃k. m ≤ k ∧ k < m + Kart ∧ NS.ns_flow_of (NS.ns_loop NSinit.init_state) k ≠ 0"
    by (auto simp: list_all_iff)
  have succ: "return (NS.ns_loop NSinit.init_state) = success" by (rule ns_loop_success[OF nu])
  have opt3: "NS.is_Opt (λv. h (b_lookup v)) (NS.ns_flow_of (NS.ns_loop NSinit.init_state))"
    by (rule NSinit.network_simplex_correct(3)[OF succ])
  note infd = aug_opt_nonzero_art_infeasible[OF opt3 nzex]
  show "∄ f. original_network.isbflow f (λv. h (b_lookup v))" by (fact infd)
qed

end

theorem solve_correct:
  "solve = Optimum fs ⟹ length fs = m ∧ original_network.is_Opt (λv. h (b_lookup v)) (h ∘ nth fs)"
  "solve = Infeasible ⟹ ∄ f. original_network.isbflow f (λv. h (b_lookup v))"
  "solve = Neg_inf_cycle ⟹ neg_infty_cycle"
proof -
  show "solve = Neg_inf_cycle ⟹ neg_infty_cycle"
  proof -
    assume A: "solve = Neg_inf_cycle"
    show neg_infty_cycle
    proof (cases acyc_flow_opt)
      case None thus ?thesis by (rule acyc_none_neg_cycle)
    next
      case (Some f') hence "acyc_flow_opt ≠ None" by simp
      thus ?thesis using A solve_correct_some(3) by blast
    qed
  qed
next
  assume A: "solve = Optimum fs"
  have ne: "acyc_flow_opt ≠ None" using A solve_none by auto
  show "length fs = m ∧ original_network.is_Opt (λv. h (b_lookup v)) (h ∘ nth fs)" using solve_correct_some(1)[OF ne A] .
next
  assume A: "solve = Infeasible"
  have ne: "acyc_flow_opt ≠ None" using A solve_none by auto
  show "∄ f. original_network.isbflow f (λv. h (b_lookup v))" 
    using solve_correct_some(2)[OF ne A] .
qed


end
thm initial_basis_selector.solve_correct
thm initial_basis_selector_def
end