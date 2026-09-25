section ‹An untrusted min-cost-flow oracle and its certificates›

text ‹The middle stage of the solver pipeline.  The DIMACS reduction of ‹Mincost_Solver_Reduction›
      turns an instance into the library's standard format — capacities only, non-negative flow, the
      balance met exactly, a lonely vertex only where the balance is zero — and this theory takes
      such an instance and hands it
      to an ∗‹external, untrusted› solver.  That solver returns one of the three possible verdicts
      ∗‹together with a certificate›, which a checker (to come) validates.  Only if the check fails
      does the pipeline fall back on the verified network simplex.

      The point of the arrangement is that ∗‹nothing whatever is assumed about the oracle›.  It is a
      fixed function of the right type and that is all: the type pins the ∗‹format› of what comes
      back, and every other property — that the flow has the right length, that it respects the
      capacities, that the cut is a set of vertices, that the cycle is a cycle — is the checker's job
      to establish.  In particular the proof locale below carries assumptions about the ∗‹instance›
      only, never about @{term oracle_solve}.›

theory Mincost_Oracle_Certificates
  imports Flow_Theory.Mincost_Solver_Reduction Flow_Theory.Optimality_Certification
begin

subsection ‹The instance handed to the oracle›

text ‹The instance in exactly the shape the reduction produces: the arcs are @{term ‹{0..<fi_m}›}
      and carry four parallel lists; the vertices are the names @{term ‹{1..fi_n}›} and carry one
      balance list of length @{term ‹Suc fi_n›}, indexed ∗‹by the vertex name›, whose slot
      @{term ‹0::nat›} is the reserved null sentinel.  A capacity of @{term ‹- 1›} denotes an
      uncapacitated arc; every other entry is non-negative.

      Bundling the data into a record rather than passing seven arguments keeps @{term oracle_solve}
      a one-argument function, which is what an external solver is: it can be given an instance it
      did not come from, and the checker still has to validate the answer.

      One quantity is not what a solver's entry point takes: ‹fi_n› is the largest vertex
      ∗‹name›, whereas a solver is told a node ∗‹count›.  The count is @{term ‹Suc fi_n›}, the length of
      ‹fi_bal›, because the reserved slot @{term ‹0::nat›} travels as an ordinary node --- an
      isolated one of balance ‹0›, which no arc names and which therefore costs the
      solver nothing and cannot change its verdict.  Everything else crosses the boundary as it
      stands: the four arc lists are the arc arrays, ‹fi_bal› is the balance array, and the
      certificates come back indexed the same way, the flow by arc and the potentials and the cut by
      vertex name.›

record 'n flow_instance =
  fi_n    :: nat
  fi_m    :: nat
  fi_fst  :: "nat list"
  fi_snd  :: "nat list"
  fi_cap  :: "'n list"
  fi_cost :: "'n list"
  fi_bal  :: "'n list"

subsection ‹The oracle's answer›

text ‹The three verdicts, each with the certificate that witnesses it.

      ▪ @{text OracleOptimum}: a primal-dual pair — the flow, indexed by arc, and the node
        potentials, indexed by vertex name like the balance list.  The dual is what makes the
        optimality check a single linear scan of the reduced costs rather than a search for a
        negative residual cycle.  It also carries @{text oa_mode}, the scale ‹Mn› the potentials were
        computed against: ‹n < ¦oa_mode¦› claims the cheaper dual-slack notion at that scale, anything
        smaller claims exact optimality outright.  This is a claim, checked or not depending on the
        ∗‹checker's own› mode --- see @{text checker_mode} below.
      ▪ @{text OracleInfeasible}: a cut whose demand exceeds the capacity crossing it, given as an
        ∗‹indicator over the vertices› --- one cell per vertex name, indexed like the balance list
        and like the potentials, a cell being non-zero exactly when its vertex lies in the cut.
      ▪ @{text OracleUnbounded}: a cycle, given as a list of ∗‹arc indices› — the shape
        @{const has_neg_infty_cycle} quantifies over, so that the check is its introduction rule.

      Only the potentials carry ∗‹quantities›, and only they are of the instance's numeric type: a
      potential is a number of the same kind as a capacity or a cost, and is added to them.  The
      other two certificates carry no arithmetic at all --- an arc index is a position, and a cut
      cell is a flag --- so both are @{typ nat}, and the checks that read them need the numeric type
      only for the capacities and balances they look up with them.  The solver hands the cut back in
      the buffer it fills with potentials in the optimal case, which saves it an allocation and says
      nothing about what a cut is; the boundary undoes that when it builds the answer.

      ∗‹Every verdict carries the flow›, not only the first.  In the optimal case it is the solution;
      in the other two it is where the solver stopped, and it is the input a verified procedure is
      warm-started from when the certificate is rejected --- which is the whole point of keeping it,
      since a rejected answer is otherwise worthless.  It is not a certificate: no check below reads
      it except the optimality check, which reads it as the primal half of its pair.

      None of these components is constrained here; a certificate is a ∗‹claim›, and the datatype
      only fixes what shape a claim takes.›

text ‹Two independent modes govern how an optimality claim is checked. @{text oa_mode} (below) is
      part of the certificate; @{text checker_mode} is a parameter of the checker, never of the
      certificate --- whether the caller demands the exact correctness specification
      (‹CheckerNormal›) or accepts the epsilon-slack one (‹CheckerEpsilontic›). Only the checker's
      own mode decides whether a certificate's mode is even consulted: in ‹CheckerNormal› mode it
      is ignored outright and the exact check is always run.

      @{text oa_mode} is the scale ‹Mn› the certificate's own potentials were computed against, not
      a flag: ‹n < ¦oa_mode¦› asks for the epsilon check at exactly that scale, anything smaller asks
      for the exact check. Reading it this way needs no trust in the oracle in either direction: the
      soundness theorem the epsilon check appeals to (‹optimality_from_eps_potentials› in
      ‹Optimality_Certification.thy›) is proved for ∗‹every› scale exceeding the vertex count, with
      no assumption on how the certificate was produced --- so whatever value the oracle names, a
      passing check is a proof of exact optimality, never merely of something ‹Mn›-close to it. A
      certificate naming too small a scale is not a soundness problem, only a wasted one: routed to
      ‹check_optimum› instead, exactly as ‹check_optimum_eps› would itself have rejected it via the
      same bound --- there is nothing left to protect by second-guessing the value with a
      caller-supplied floor.›

datatype checker_mode = CheckerNormal | CheckerEpsilontic

datatype 'n oracle_answer =
    OracleOptimum    (oa_flow: "'n list") (oa_pot: "'n list") (oa_mode: "'n")
  | OracleInfeasible (oa_flow: "'n list") (oa_cut: "nat list")
  | OracleUnbounded  (oa_flow: "'n list") (oa_cycle: "nat list")

text ‹What the pipeline finally reports is a different thing, and has a different type.  An oracle's
      answer is a claim with a certificate attached; a verdict is the answer itself, and carries no
      certificate at all --- either because a certificate was checked and discarded, or because the
      procedure that produced it is verified.  The optimal case keeps the flow, which is the
      solution; the other two have nothing to report beyond the verdict.›

datatype 'n solver_verdict =
    VOptimum (v_flow: "'n list")
  | VInfeasible
  | VUnbounded

subsection ‹The code locale›

text ‹Assumption-free, and therefore the locale the executable material lives in: it fixes the
      instance data, fixes the oracle, and defines the instance record that is passed to it together
      with the answer that comes back.  The reading of the format — which arcs and vertices there
      are, how a capacity is decoded, how the endpoints and the balance of a vertex are looked up —
      is defined here too, since the checker will need all of it and none of it needs an assumption.

      The embedding @{term h} into the reals is ∗‹not› a parameter here: it is a proof device with no
      executable content, exactly as in ‹initial_basis_code_spec›.›

locale mcf_oracle_spec =
  fixes fst_list      :: "nat list"
    and snd_list      :: "nat list"
    and capacity_list :: "('n :: linordered_idom) list"
    and cost_list     :: "'n list"
    and balance_list  :: "'n list"
    and m             :: nat
    and n             :: nat
    and oracle_solve  :: "'n flow_instance ⇒ 'n oracle_answer"
begin

definition orc_input :: "'n flow_instance" where
  "orc_input = ⦇ fi_n = n, fi_m = m, fi_fst = fst_list, fi_snd = snd_list,
                 fi_cap = capacity_list, fi_cost = cost_list, fi_bal = balance_list ⦈"

definition orc_answer :: "'n oracle_answer" where
  "orc_answer = oracle_solve orc_input"

text ‹Reading the format.  Arcs are the indices below @{term m} and the vertices the names
      @{term ‹{Suc 0..n}›}; neither set is materialised, the sweeps below counting instead.  These
      accessors name the format's conventions for the reader --- what a cell of each list means and
      how a capacity is decoded --- and are used where the cost of a call does not matter; the loops
      write the loads out.›

definition tail_of :: "nat ⇒ nat" where "tail_of e = fst_list ! e"

definition head_of :: "nat ⇒ nat" where "head_of e = snd_list ! e"

definition cost_of :: "nat ⇒ 'n" where "cost_of e = cost_list ! e"

text ‹An arc is uncapacitated exactly when its capacity cell holds the sentinel @{term ‹- 1›}.›

definition uncapacitated :: "nat ⇒ bool" where
  "uncapacitated e = (capacity_list ! e = - 1)"

definition cap_of :: "nat ⇒ 'n" where "cap_of e = capacity_list ! e"

text ‹The balance of a vertex, and the potential a dual certificate assigns to it: both lists are
      indexed by the vertex name, so slot @{term ‹0::nat›} of either is never consulted at a
      vertex.›

definition balance_of :: "nat ⇒ 'n" where "balance_of v = balance_list ! v"

definition pot_of :: "'n list ⇒ nat ⇒ 'n" where "pot_of pot v = pot ! v"

subsection ‹The certificate checkers›

text ‹Ported from the SML mock ‹ns_tree_benchmark/adaptor/lemon_ns_check.sml›, which fixes the
      certificate conventions the external oracle already speaks.  Every check is one sweep of the
      arcs and at most one of the vertices, in exact arithmetic.

      Two departures from the mock, both forced.  It reads the certificate arrays without ever
      checking their lengths, so a short flow, potential or cut raises rather than returning
      ∗‹false›; here the lengths are checked first, because @{const nth} past the end is not an
      error but an unspecified value, and a checker that consults one has proved nothing.  And where
      the mock tests @{term ‹cap e < 0›} for an uncapacitated arc, we test the sentinel
      @{term ‹cap e = - 1›} — the same thing on any instance satisfying the format, and the
      convention the rest of the development uses.

      ∗‹How the sweeps are written.›  A list here is an array: @{const nth} is a load and
      @{const list_update} a store, both at constant cost.  Each check is one ∗‹counted loop› --- a
      first-order recursive function carrying a cursor, a remaining count, and its accumulators as
      separate arguments --- and does all of the work for the index it is looking at.  Four things
      follow, and each of them is a thing the obvious formulation would have paid for.

      ▪ ∗‹Nothing is materialised.›  A loop over the arcs recurses on a counter; it does not fold
        over @{term ‹[0..<m]›}, which is a list of @{term m} elements that has to be built before
        the first arc is looked at.  For the same reason a sum over selected arcs accumulates in an
        argument rather than being @{const sum_list} of a @{const map} of a @{const filter}, which
        would allocate twice to add up numbers already in hand.  The only array allocated by any
        check is the one accumulator that is genuinely needed, the net out-flow.
      ▪ ∗‹Nothing is passed as a function.›  A fold takes its step as an argument and calls it
        indirectly once per index, and the step has to hand its state back as a tuple, allocated and
        taken apart again on every iteration.  A recursive function with the state spread over its
        arguments has neither cost: the calls are direct and in tail position, and the state stays
        in registers.
      ▪ ∗‹No cell is loaded twice.›  The endpoints of an arc are needed by both the reduced cost and
        the scatter, its capacity by both the bound and the slackness test; each is bound once, in a
        @{text let}, and reused.  The accessors of the previous section are not called from inside a
        loop for the same reason --- a load written out is a load, a load behind a definition is a
        call.
      ▪ ∗‹A rejection stops the loop.›  Each check returns a plain boolean and every guard is a
        conjunct in front of the recursive call, so a failure returns immediately instead of running
        the remaining indices with a dead flag --- and it returns without having allocated anything
        at all, since there is no tuple and no option to build.  The guards are ordered cheapest
        first, and the ones outside the loop are ordinary conjunctions, which the code generator
        compiles to short-circuiting tests: a length mismatch stops the check before a single index
        is touched.

      What each loop computes is spelled out by the predicates it fuses, which are kept alongside
      it: they are the specification, the loop is the implementation.

      ∗‹What the arithmetic is.›  Every number a check adds or compares --- flow, capacity, cost,
      potential, balance --- is of the instance's own type @{typ 'n}, a
      \<^class>‹linordered_idom›, the carrier the reduction and the verified solver already run on, and
      nothing here needs more than that class: sums, differences, comparisons against
      @{term ‹0::'n›} and against the sentinel @{term ‹- 1::'n›}, and no division anywhere.  So the
      checks are exact by construction, and a leaf theory that instantiates @{typ 'n} --- at
      @{typ int} for a DIMACS file, as ‹Network_Simplex_Int› does for the solver --- monomorphises
      the checker along with everything else, which is what turns the class operations into machine
      arithmetic rather than dictionary lookups.  The @{typ nat}s in a loop are the arc and vertex
      ∗‹positions› --- indices, counters, vertex names, and the cells of a cut, which are flags and
      not quantities --- so of the three certificates only the primal-dual pair is of type
      @{typ 'n}, and the checks of the other two use the numeric type solely for the capacities,
      costs and balances they look up.›

text ‹The reduced cost of an arc under a dual certificate: @{term ‹𝖼 e + π (fst e) - π (snd e)›}.›

definition rc_of :: "'n list ⇒ nat ⇒ 'n" where
  "rc_of pot e = cost_list ! e + pot ! (fst_list ! e) - pot ! (snd_list ! e)"

text ‹Primal feasibility of one arc together with complementary slackness on it: a strictly positive
      reduced cost forces the arc empty, a strictly negative one forces it saturated — and therefore
      forces it to be capacitated at all, an uncapacitated arc of negative reduced cost being exactly
      the unbounded case.›

definition arc_ok_opt :: "'n list ⇒ 'n list ⇒ nat ⇒ bool" where
  "arc_ok_opt fl pot e =
     (0 ≤ fl ! e ∧
      (¬ uncapacitated e ⟶ fl ! e ≤ capacity_list ! e) ∧
      (0 < rc_of pot e ⟶ fl ! e = 0) ∧
      (rc_of pot e < 0 ⟶ ¬ uncapacitated e ∧ fl ! e = capacity_list ! e))"

text ‹The net out-flow of every vertex, scattered in one arc sweep into a list indexed by vertex
      name.  The head is updated first and read back by the tail update, so a self-loop cancels
      instead of counting twice — the same order the reduction's pass uses.›

definition net_out :: "'n list ⇒ 'n list" where
  "net_out fl =
     fold (λe acc. let a = acc[snd_list ! e := acc ! (snd_list ! e) - fl ! e]
                   in a[fst_list ! e := a ! (fst_list ! e) + fl ! e])
          [0..<m] (replicate (Suc n) 0)"

text ‹∗‹Optimality.›  The certificate is a primal-dual pair, and the two things to be established
      about it --- that every arc is feasible and slack, and that the net out-flow is the balance ---
      are one sweep, not two: the step below decides @{const arc_ok_opt} for its arc and scatters
      that arc's flow into the accumulator @{const net_out} would have built.  Both need the
      endpoints and both need the flow, so a fused step loads each of the five cells of an arc once
      and never returns to it.  The head is written first and read back by the tail update, so a
      self-loop cancels instead of counting twice — the order @{const net_out} and the reduction's
      own pass use.

      The loads are staged rather than taken all at once, because a @{text let} is strict: the flow
      and the capacity decide primal feasibility by themselves, so they are read first, and the
      endpoints, the cost and the two potentials --- everything the dual test and the scatter need
      --- are read only once that has passed.  An accepted arc pays exactly the same loads as
      before; a rejected one pays two.

      The balance condition needs no sweep of its own: the loop ends holding the accumulator, so it
      finishes by comparing it with the balance array on the spot.  That covers the sentinel slot
      too (no arc touches vertex @{term ‹0::nat›}, so its net out-flow is @{term ‹0::'n›}, matching
      the ‹balance_sentinel› of the proof locale), and it is why the loop can return a boolean
      rather than handing an accumulator back to a caller that would have to take it apart.›

fun opt_loop :: "'n list ⇒ 'n list ⇒ nat ⇒ nat ⇒ 'n list ⇒ bool" where
  "opt_loop fl pot e 0 net = (net = balance_list)"
| "opt_loop fl pot e (Suc k) net =
     (let f = fl ! e; c = capacity_list ! e
      in 0 ≤ f ∧ (c = - 1 ∨ f ≤ c)
         ∧ (let u = fst_list ! e; v = snd_list ! e
            in (let rc = cost_list ! e + pot ! u - pot ! v
                in if 0 < rc then f = 0 else if rc < 0 then c ≠ - 1 ∧ f = c else True)
               ∧ (let net' = net[v := net ! v - f]
                  in opt_loop fl pot (Suc e) k (net'[u := net' ! u + f]))))"

definition check_optimum :: "'n list ⇒ 'n list ⇒ bool" where
  "check_optimum fl pot =
     (length fl = m ∧ length pot = Suc n ∧ opt_loop fl pot 0 m (replicate (Suc n) 0))"

text ‹∗‹ε-optimality.›  A weaker, cheaper-to-produce optimality certificate: a cost-scaling oracle's
      own potentials, at the end of its last phase, already satisfy this without the correction pass
      ‹check_optimum› would otherwise force.  Rather than the exact trichotomy — an empty arc has
      non-negative reduced cost, a saturated one non-positive, an interior one exactly zero — every
      residual arc need only clear a fixed slack of one unit once its reduced cost is scaled by a
      global factor ‹M›: ‹M · rc(e) ≥ -1› if the arc is not fully saturated (so it may still take
      flow), and ‹M · rc(e) ≤ 1› if it carries flow already (so it may still give flow back). An arc
      that is both --- carrying flow strictly inside its bounds --- has to satisfy both at once,
      pinning ‹Mn · rc(e)› to the interval ‹[-1,1]›, the direct relaxation of the exact check's ‹=0›.

      ‹Mn› is the certificate's own @{const oa_mode}, taken as-is (see the note on dispatch above):
      the soundness theorem this check appeals to (‹optimality_from_eps_potentials› in
      ‹Optimality_Certification.thy›) holds for every scale exceeding the vertex count regardless of
      its origin, so there is nothing to protect by second-guessing the value --- only the one
      condition the theorem actually needs, tested here against ‹n›, the locale's own trusted count.›

definition scaled_rc_of :: "'n ⇒ 'n list ⇒ nat ⇒ 'n" where
  "scaled_rc_of Mn pot e = Mn * cost_list ! e + pot ! (fst_list ! e) - pot ! (snd_list ! e)"

definition arc_ok_eps :: "'n ⇒ 'n list ⇒ 'n list ⇒ nat ⇒ bool" where
  "arc_ok_eps Mn fl pot e =
     (0 ≤ fl ! e ∧
      (¬ uncapacitated e ⟶ fl ! e ≤ capacity_list ! e) ∧
      (uncapacitated e ∨ fl ! e < capacity_list ! e ⟶ - 1 ≤ scaled_rc_of Mn pot e) ∧
      (0 < fl ! e ⟶ scaled_rc_of Mn pot e ≤ 1))"

fun opt_loop_eps :: "'n ⇒ 'n list ⇒ 'n list ⇒ nat ⇒ nat ⇒ 'n list ⇒ bool" where
  "opt_loop_eps Mn fl pot e 0 net = (net = balance_list)"
| "opt_loop_eps Mn fl pot e (Suc k) net =
     (let f = fl ! e; c = capacity_list ! e
      in 0 ≤ f ∧ (c = - 1 ∨ f ≤ c)
         ∧ (let u = fst_list ! e; v = snd_list ! e
            in (let rc = Mn * cost_list ! e + pot ! u - pot ! v
                in (c = - 1 ∨ f < c ⟶ - 1 ≤ rc) ∧ (0 < f ⟶ rc ≤ 1))
               ∧ (let net' = net[v := net ! v - f]
                  in opt_loop_eps Mn fl pot (Suc e) k (net'[u := net' ! u + f]))))"

definition check_optimum_eps :: "'n ⇒ 'n list ⇒ 'n list ⇒ bool" where
  "check_optimum_eps Mn fl pot =
     (length fl = m ∧ length pot = Suc n ∧ of_nat n < Mn ∧
      opt_loop_eps Mn fl pot 0 m (replicate (Suc n) 0))"

text ‹∗‹Dispatch.›  @{const oa_mode} is read as a scale, not a flag (see the note above), and the
      routing test is exactly ‹check_optimum_eps›'s own gate: ‹of_nat n < ¦oa_mode¦›. A ‹certm› too
      small to clear that gate is not sent to ‹check_optimum_eps› at all --- it would only be
      rejected there, by the same test, having proved nothing --- but routed to ‹check_optimum›
      instead, which is unconditionally sound and may well still accept it. Testing ‹¦certm¦ < 1›
      here instead would be strictly weaker: it would send every ‹certm› in ‹{1..n}› to
      ‹check_optimum_eps› only to have it bounce off the internal gate, discarding certificates whose
      flow is in fact exactly optimal for no reason. In ‹CheckerNormal› mode @{const oa_mode} is not
      even inspected: the exact check runs regardless of what the certificate claims.›

definition check_optimum_dispatch :: "checker_mode ⇒ 'n list ⇒ 'n list ⇒ 'n ⇒ bool" where
  "check_optimum_dispatch cm fl pot certm =
     (case cm of
        CheckerNormal     ⇒ check_optimum fl pot
      | CheckerEpsilontic ⇒ (if of_nat n < ¦certm¦ then check_optimum_eps ¦certm¦ fl pot
                              else check_optimum fl pot))"

text ‹∗‹Unboundedness.›  The certificate is a list of arc indices; the four conjuncts are exactly the
      premises of @{thm [source] has_neg_infty_cycleI} — non-empty, closed, inside the arc set, and
      of negative total cost with every arc uncapacitated.  The cost is summed with @{const foldr},
      in the shape @{const has_neg_infty_cycle} uses.›

definition cyc_linked :: "nat list ⇒ bool" where
  "cyc_linked cyc =
     list_all (λi. snd_list ! (cyc ! i) = fst_list ! (cyc ! ((Suc i) mod length cyc)))
              [0..<length cyc]"

text ‹All four are decided in one traversal of the cycle.  The loop carries the head of the arc
      before it: linkage is then one comparison against a value already in a register, with no
      second @{const nth} and no @{text mod} to find the successor.  Seeding that register with the
      tail of the ∗‹first› arc makes the first comparison hold trivially and turns closure into the
      same comparison after the last step, so the wrap-around is checked once, at the end, instead
      of being carried through every step.  The seed is the loop's own argument, which is why it
      also carries the running cost: the loop ends knowing everything it has to decide, and returns
      a boolean.

      This is the one certificate that is read ∗‹sequentially›, its entries being positions in the
      arc arrays rather than cells addressed by a name, and it is therefore the one that is
      consumed as a list --- pattern matching along it, not indexing into it.  Under the reading
      that a list is an array the two are the same walk; under the reading that it is a list they
      are not, indexing being a search from the front, and the arithmetic of a cursor and a count
      is saved either way.  The @{text case} also does the work @{const hd} and @{term ‹cyc ≠ []›}
      would have done, and binds the first arc once: @{term ‹e0 < m›} has to be tested before the
      seed is read, since @{term ‹fst_list ! e0›} is otherwise a load past the end.  Every other
      index is tested by the loop itself, first, before it loads anything.›

fun cyc_loop :: "nat list ⇒ nat ⇒ nat ⇒ 'n ⇒ bool" where
  "cyc_loop [] prev s tot = (prev = s ∧ tot < 0)"
| "cyc_loop (e # es) prev s tot =
     (e < m ∧ capacity_list ! e = - 1 ∧ prev = fst_list ! e
      ∧ cyc_loop es (snd_list ! e) s (tot + cost_list ! e))"

definition check_unbounded :: "nat list ⇒ bool" where
  "check_unbounded cyc =
     (case cyc of [] ⇒ False
                | e0 # _ ⇒ e0 < m ∧ (let s = fst_list ! e0 in cyc_loop cyc s s 0))"

text ‹∗‹Infeasibility.›  The certificate is the vertex set of a Gale--Hoffman violating cut: more
      must leave @{term S} than the arcs out of it can carry.  An uncapacitated arc leaving
      @{term S} makes the cut worthless, so it is rejected.

      @{term S} arrives as an indicator, one cell per vertex name --- membership is
      ‹S ! v ≠ 0›, exactly the test the solver's convention prescribes.  Two things follow, and both
      are the reason the indicator is kept rather than converted to a list of names.  Duplicates and
      out-of-range names, which a membership list would have to be screened for, cannot arise: a
      cell ∗‹is› its vertex.  And the demand is summed by sweeping the cells, in the same order and
      over the same range as the balance list, so the two node-indexed sweeps of the checker have
      the same shape.  The one thing that does have to be checked is the length: a short indicator
      would leave @{const nth} unspecified at the vertices past its end.

      The cells are @{typ nat}: they are flags, never added to anything.  The numeric type enters
      this check only through the capacities and the balances the flags select, and the arithmetic
      on those is the same @{typ 'n} everything else uses.

      The sweep includes slot @{term ‹0::nat›}, which is not a vertex.  A solver that marks it
      changes neither side of the inequality --- the slot's balance is @{term ‹0::'n›} and no arc
      touches it --- so there is nothing to reject and nothing to strip.›

definition in_cut :: "nat list ⇒ nat ⇒ bool" where
  "in_cut S v = (S ! v ≠ 0)"

definition leaves_cut :: "nat list ⇒ nat ⇒ bool" where
  "leaves_cut S e = (in_cut S (fst_list ! e) ∧ ¬ in_cut S (snd_list ! e))"

definition cut_capacity :: "nat list ⇒ 'n" where
  "cut_capacity S = sum_list (map (λe. capacity_list ! e) (filter (leaves_cut S) [0..<m]))"

text ‹The arc sweep again does both of its jobs at once: an arc that leaves @{term S} either
      disqualifies the cut, being uncapacitated, or contributes its capacity to the total — one test
      of the endpoints, one load of the capacity, and nothing is selected into a list first.  The
      capacity is loaded once and then either disqualifies the cut or is added, never both.

      The demand is the other sweep, over the cells of the indicator, accumulating instead of
      building the list of the selected balances.  It is run first and handed to the arc loop as a
      scalar, so that loop too ends in a comparison and returns a boolean; the arc loop is the one
      that can reject, and a rejection then costs nothing beyond the vertex sweep already done.›

fun demand_loop :: "nat list ⇒ nat ⇒ nat ⇒ 'n ⇒ 'n" where
  "demand_loop S v 0 acc = acc"
| "demand_loop S v (Suc k) acc =
     demand_loop S (Suc v) k (if S ! v ≠ 0 then acc + balance_list ! v else acc)"

fun cut_loop :: "nat list ⇒ nat ⇒ nat ⇒ 'n ⇒ 'n ⇒ bool" where
  "cut_loop S e 0 cap dem = (cap < dem)"
| "cut_loop S e (Suc k) cap dem =
     (if S ! (fst_list ! e) ≠ 0 ∧ S ! (snd_list ! e) = 0
      then let c = capacity_list ! e in c ≠ - 1 ∧ cut_loop S (Suc e) k (cap + c) dem
      else cut_loop S (Suc e) k cap dem)"

definition check_infeasible :: "nat list ⇒ bool" where
  "check_infeasible S =
     (length S = Suc n ∧ cut_loop S 0 m 0 (demand_loop S 0 (Suc n) 0))"

text ‹The dispatcher: each verdict is checked against its own certificate.  Nothing else about the
      answer is trusted, so a rejected certificate says nothing about the instance — only that this
      oracle run is unusable and the verified solver must be called instead.›

definition check_answer :: "'n oracle_answer ⇒ bool" where
  "check_answer a =
     (case a of OracleOptimum fl pot _ ⇒ check_optimum fl pot
              | OracleInfeasible _ S   ⇒ check_infeasible S
              | OracleUnbounded _ cyc  ⇒ check_unbounded cyc)"

text ‹∗‹The mode-aware dispatcher.› Exactly ‹check_answer›, except an ‹OracleOptimum› certificate is
      routed through ‹check_optimum_dispatch› instead of the exact check unconditionally. The other
      two verdicts have no epsilon notion, so they are untouched --- ‹cm› simply plays no part in
      their branches.›

definition check_answer_dispatch :: "checker_mode ⇒ 'n oracle_answer ⇒ bool" where
  "check_answer_dispatch cm a =
     (case a of OracleOptimum fl pot certm ⇒ check_optimum_dispatch cm fl pot certm
              | OracleInfeasible _ S       ⇒ check_infeasible S
              | OracleUnbounded _ cyc      ⇒ check_unbounded cyc)"

text ‹Screening an answer that is already in hand.  It is written as its own function, and
      ‹checked_answer› below is one application of it, so that @{const orc_answer} occurs
      ∗‹once›: the answer is the result of running the external solver, and a formulation that
      mentioned it twice --- once to check it and once to return it --- would run the solver twice.
      Keeping the two apart also lets a caller screen an answer it obtained some other way.›

definition screen :: "'n oracle_answer ⇒ 'n oracle_answer option" where
  "screen a = (if check_answer a then Some a else None)"

definition checked_answer :: "'n oracle_answer option" where
  "checked_answer = screen orc_answer"

text ‹Reporting an answer that survived the check: the certificate has done its work and is dropped,
      leaving the verdict and, where there is one, the solution.  This is where the checking layer
      ends --- @{term None} means the oracle was no use, and it is the next layer's business what to
      do about it.›

definition verdict_of :: "'n oracle_answer ⇒ 'n solver_verdict" where
  "verdict_of a = (case a of OracleOptimum fl _ _  ⇒ VOptimum fl
                           | OracleInfeasible _ _  ⇒ VInfeasible
                           | OracleUnbounded _ _   ⇒ VUnbounded)"

definition checked_verdict :: "'n solver_verdict option" where
  "checked_verdict = map_option verdict_of checked_answer"

end

subsection ‹Smoke tests›

text ‹The checkers are executable and their loops carry state across iterations, so it is worth
      pinning down what they do on instances small enough to read.  Each line is one behaviour: the
      accepted certificate, then the ways of failing it, including the ones the fusion could
      plausibly get wrong --- a self-loop, whose two updates must cancel; a rotated cycle, since the
      wrap-around is checked once at the end rather than at every step; a cut that marks the
      reserved slot, which must change nothing; and, in each case, a certificate of the wrong
      length.›

lemma opt_accept:    "mcf_oracle_spec.check_optimum [1] [2] [5::int] [3] [0,1,-1] 1 2 [1] [0,0,3]"
  and opt_selfloop:  "mcf_oracle_spec.check_optimum [1] [1] [5::int] [0] [0,0] 1 1 [3] [0,0]"
  and opt_balance:   "¬ mcf_oracle_spec.check_optimum [1] [2] [5::int] [3] [0,1,-1] 1 2 [2] [0,0,3]"
  and opt_slack:     "¬ mcf_oracle_spec.check_optimum [1] [2] [5::int] [3] [0,1,-1] 1 2 [1] [0,0,0]"
  and opt_length:    "¬ mcf_oracle_spec.check_optimum [1] [2] [5::int] [3] [0,1,-1] 1 2 [1,1] [0,0,3]"
  by(simp_all add: mcf_oracle_spec.check_optimum_def mcf_oracle_spec.opt_loop.simps
                   eval_nat_numeral)

lemma unb_accept:   "mcf_oracle_spec.check_unbounded [1,2] [2,1] [-1,-1::int] [-1,0] 2 [0,1]"
  and unb_rotated:  "mcf_oracle_spec.check_unbounded [1,2] [2,1] [-1,-1::int] [-1,0] 2 [1,0]"
  and unb_open:     "¬ mcf_oracle_spec.check_unbounded [1,2] [2,1] [-1,-1::int] [-1,0] 2 [0]"
  and unb_finite:   "¬ mcf_oracle_spec.check_unbounded [1,2] [2,1] [-1,4::int] [-1,0] 2 [0,1]"
  and unb_empty:    "¬ mcf_oracle_spec.check_unbounded [1,2] [2,1] [-1,-1::int] [-1,0] 2 []"
  and unb_range:    "¬ mcf_oracle_spec.check_unbounded [1,2] [2,1] [-1,-1::int] [-1,0] 2 [5]"
  and unb_cost:     "¬ mcf_oracle_spec.check_unbounded [1,2] [2,1] [-1,-1::int] [1,0] 2 [0,1]"
  by(simp_all add: mcf_oracle_spec.check_unbounded_def mcf_oracle_spec.cyc_loop.simps)

lemma inf_accept:   "mcf_oracle_spec.check_infeasible [1] [2] [1::int] [0,5,-5] 1 2 [0,1,0]"
  and inf_sentinel: "mcf_oracle_spec.check_infeasible [1] [2] [1::int] [0,5,-5] 1 2 [1,1,0]"
  and inf_empty:    "¬ mcf_oracle_spec.check_infeasible [1] [2] [1::int] [0,5,-5] 1 2 [0,0,0]"
  and inf_infinite: "¬ mcf_oracle_spec.check_infeasible [1] [2] [-1::int] [0,5,-5] 1 2 [0,1,0]"
  and inf_length:   "¬ mcf_oracle_spec.check_infeasible [1] [2] [1::int] [0,5,-5] 1 2 [0,1]"
  by(simp_all add: mcf_oracle_spec.check_infeasible_def mcf_oracle_spec.cut_loop.simps
                   mcf_oracle_spec.demand_loop.simps eval_nat_numeral)

subsection ‹The proof locale›

text ‹The instance format, and nothing else.  The assumptions are exactly the properties the
      reduction establishes for its output: the four arc lists are parallel and as long as the arc
      count announces, the balance list has one cell per vertex name plus the sentinel, the arc and
      vertex sets are non-empty, every endpoint is a vertex name, every capacity is non-negative or
      the uncapacitated sentinel, the sentinel slot of the balance list is zero, the balances sum to
      zero, and a vertex no arc touches has balance zero.

      The last two deserve a word, since both are consequences of the reduction rather than of the
      DIMACS input.  ∗‹The balances sum to zero› is what makes an optimality certificate possible at
      all, as ‹net_out› sums to zero over any flow whatever.  ∗‹A lonely vertex has balance zero›
      because a vertex with no arc has no incident capacity, so the reduction's range test forces
      its balance to ‹0›.  Nothing weaker would do, as the balance condition of ‹check_optimum› is a
      list equality over ∗‹all› slots and so demands ‹0› at a vertex no flow can reach.

      @{term ‹0 < n›} makes the vertex names non-empty, so that the balance list has a slot beyond
      the reserved one.  It is no restriction: the reduction's own ‹arcs_nonempty› already forces
      it, since an arc needs an endpoint.

      ∗‹There is deliberately no assumption on @{term oracle_solve}.›  It may return anything of its
      type — a flow of the wrong length, a cut that is not a set of vertices, a ``cycle'' that is not
      closed, or an answer that is simply wrong.  Soundness of the pipeline must therefore come from
      the checker alone, and that is the whole point: the oracle can be an arbitrary external
      program.›

locale mcf_oracle =
  mcf_oracle_spec where capacity_list = capacity_list +
  real_embedding where h = "h :: 'n ⇒ real"
  for capacity_list :: "('n :: linordered_idom) list" and h +
  assumes length_fst_list:  "length fst_list = m"
      and length_snd_list:  "length snd_list = m"
      and length_capacity:  "length capacity_list = m"
      and length_cost_list: "length cost_list = m"
      and length_balance:   "length balance_list = Suc n"
      and arcs_nonempty:    "0 < m"
      and nodes_nonempty:   "0 < n"
      and tail_is_vertex:   "⋀e. e < m ⟹ fst_list ! e ∈ {Suc 0..n}"
      and head_is_vertex:   "⋀e. e < m ⟹ snd_list ! e ∈ {Suc 0..n}"
      and capacity_format:  "⋀e. e < m ⟹ 0 ≤ capacity_list ! e ∨ capacity_list ! e = - 1"
      and balance_sentinel: "balance_list ! 0 = 0"
      and balance_sum_zero: "sum_list balance_list = 0"
      and isolated_zero:    "⋀v. ⟦v ∈ {Suc 0..n}; ∀ e < m. fst_list ! e ≠ v ∧ snd_list ! e ≠ v⟧ ⟹ balance_list ! v = 0"
begin

subsection ‹What the lists mean›

text ‹The instance is read as a cost-flow network, in the same way the list instantiation of the
      simplex reads its own input (‹Network_Simplex_Initial_Basis›) and the reduction reads its
      output: the arcs are the indices below @{term m}, an arc's endpoints, cost and capacity are
      looked up in the parallel lists, and the sentinel @{term ‹- 1::'n›} is decoded as @{term ∞}.
      @{term create_edge} has to return an edge for ∗‹every› pair of vertices, so it maps a pair to an
      index beyond the input, whose endpoints are recovered by @{const prod_decode} and whose
      capacity is @{term ∞}; those synthetic edges are outside @{term ‹{0..<m}›} and play no part.

      This is what gives the checkers something to be correct ∗‹about›: with the interpretation in
      place, @{const flow_network_spec.isbflow}, @{const cost_flow_spec.is_Opt},
      @{const has_neg_infty_cycle} and the whole residual-graph vocabulary of ‹Residual› and
      ‹Cost_Optimality› are available for this instance, and the soundness statements below are
      phrased in them rather than in anything invented here.›

definition cap_u :: "nat ⇒ ereal" where
  "cap_u e = (if e < m ∧ ¬ uncapacitated e then ereal (h (capacity_list ! e)) else ∞)"

definition bal :: "nat ⇒ real" where
  "bal v = h (balance_list ! v)"

lemma cap_u_nonneg: "0 ≤ cap_u e"
  using capacity_format[of e] h_nonneg
  by(auto simp add: cap_u_def uncapacitated_def zero_ereal_def)

sublocale network: cost_flow_network
  where ℰ           = "{0..<m}"
    and fst          = "λ e. if e < m then fst_list ! e else Product_Type.fst (prod_decode (e - m))"
    and snd          = "λ e. if e < m then snd_list ! e else Product_Type.snd (prod_decode (e - m))"
    and create_edge  = "λ u v. m + prod_encode (u, v)"
    and 𝗎           = cap_u
    and 𝖼           = "λ e. h (cost_list ! e)"
  by(unfold_locales) (auto simp add: arcs_nonempty cap_u_nonneg)

text ‹Incidence, endpoints and the vertex set, read off the lists.›

lemma net_delta_plus:  "network.delta_plus v  = {e. e < m ∧ fst_list ! e = v}"
  and net_delta_minus: "network.delta_minus v = {e. e < m ∧ snd_list ! e = v}"
  by(auto simp add: multigraph_spec.delta_plus_def multigraph_spec.delta_minus_def)

lemma net_make_pair: "e < m ⟹ network.make_pair e = (fst_list ! e, snd_list ! e)"
  by(simp add: multigraph_spec.make_pair_def)

lemma net_endpoints_V:
  assumes e: "e < m"
  shows "fst_list ! e ∈ network.𝒱" and "snd_list ! e ∈ network.𝒱"
proof -
  have "(fst_list ! e, snd_list ! e) ∈ network.make_pair ` {0..<m}"
    using e net_make_pair[OF e] by force
  thus "fst_list ! e ∈ network.𝒱" and "snd_list ! e ∈ network.𝒱"
    by(rule dVsI)+
qed

lemma net_V_subset: "network.𝒱 ⊆ {Suc 0..n}"
proof
  fix x assume "x ∈ network.𝒱"
  then obtain e where e: "e < m" "x = fst_list ! e ∨ x = snd_list ! e"
    by(auto simp add: dVs_def multigraph_spec.make_pair_def)
  thus "x ∈ {Suc 0..n}"
    using tail_is_vertex[of e] head_is_vertex[of e] by auto
qed

text ‹Two facts about the embedding that the sweeps need: it commutes with a finite sum, and hence
      with the @{const foldr} the cycle's cost is accumulated by.›

lemma h_sum: "finite A ⟹ h (∑ a ∈ A. g a) = (∑ a ∈ A. h (g a))"
  by(induction A rule: finite_induct) (auto simp add: h_add)

lemma h_foldr_cost:
  "foldr (λ e. (+) (h (cost_list ! e))) cyc 0 = h (foldr (λ e. (+) (cost_list ! e)) cyc 0)"
  by(induction cyc) (auto simp add: h_add)

text ‹Peeling the first index off a counted range: the shape every loop invariant below is proved
      in, since each loop consumes one index and recurses on the rest.›

lemma range_split_first:
  "{i ∈ {v..<v + Suc k}. P i} = (if P v then {v} else {}) ∪ {i ∈ {Suc v..<Suc v + k}. P i}"
  by(auto simp add: Suc_le_eq order_le_less)

subsection ‹Unboundedness: the cycle certificate is sound›

text ‹What the walk of @{const cyc_loop} establishes: every arc it passed is an arc of the instance
      and uncapacitated, the pairs it visited chain into a walk from the seed, and the cost it
      accumulated is negative.  The seed is the tail of the first arc and the walk ends there, so
      the walk is closed.›

lemma cyc_loop_props:
  "cyc_loop cyc prev s tot ⟹
     (∀ e ∈ set cyc. e < m ∧ uncapacitated e)
     ∧ cas prev (map network.make_pair cyc) s
     ∧ foldr (λ e. (+) (cost_list ! e)) cyc 0 + tot < 0"
proof(induction cyc arbitrary: prev tot)
  case Nil
  thus ?case by simp
next
  case (Cons e es)
  have step: "e < m" "uncapacitated e" "prev = fst_list ! e"
    and rest: "cyc_loop es (snd_list ! e) s (tot + cost_list ! e)"
    using Cons.prems by(auto simp add: uncapacitated_def)
  note IH = Cons.IH[OF rest]
  show ?case
    using IH step by(auto simp add: net_make_pair[OF step(1)] algebra_simps)
qed

theorem check_unbounded_sound:
  assumes "check_unbounded cyc"
  shows "has_neg_infty_cycle network.make_pair {0..<m} (λ e. h (cost_list ! e)) cap_u"
proof -
  obtain e0 es where cyc: "cyc = e0 # es"
    using assms by(cases cyc) (auto simp add: check_unbounded_def)
  have e0: "e0 < m" using assms by(simp add: check_unbounded_def cyc)
  have loop: "cyc_loop cyc (fst_list ! e0) (fst_list ! e0) 0"
    using assms by(simp add: check_unbounded_def cyc)
  note props = cyc_loop_props[OF loop]
  have sub: "set cyc ⊆ {0..<m}" using props by auto
  have inf: "cap_u e = ∞" if "e ∈ set cyc" for e
    using props that by(auto simp add: cap_u_def)
  have "(fst_list ! e0, snd_list ! e0) ∈ network.make_pair ` {0..<m}"
    using e0 net_make_pair[OF e0] by force
  hence hd_in: "fst_list ! e0 ∈ dVs (network.make_pair ` {0..<m})"
    by(rule dVsI(1))
  have "awalk (network.make_pair ` {0..<m}) (fst_list ! e0)
              (map network.make_pair cyc) (fst_list ! e0)"
    using props hd_in sub by(auto simp add: awalk_def)
  hence cw: "closed_w (network.make_pair ` {0..<m}) (map network.make_pair cyc)"
    by(auto simp add: closed_w_def cyc)
  have neg: "foldr (λ e. (+) (h (cost_list ! e))) cyc 0 < 0"
    using props by(simp add: h_foldr_cost)
  show ?thesis
  proof(rule has_neg_infty_cycleI[OF cw neg sub])
    fix e assume e: "e ∈ set cyc"
    show "cap_u e = PInfty" using inf[OF e] by simp
  qed
qed

subsection ‹Infeasibility: the cut certificate is sound›

text ‹The two sweeps, evaluated.  The vertex sweep accumulates the balances of the flagged slots;
      the arc sweep establishes that no uncapacitated arc leaves the cut and that the capacities of
      the ones that do fall short of the demand.›

lemma demand_loop_sum:
  "demand_loop S v k acc = acc + (∑ i ∈ {i ∈ {v..<v + k}. in_cut S i}. balance_list ! i)"
proof(induction k arbitrary: v acc)
  case 0
  thus ?case by simp
next
  case (Suc k)
  have "v ∉ {i ∈ {Suc v..<Suc v + k}. in_cut S i}" by auto
  thus ?case
    unfolding range_split_first using Suc.IH[of "Suc v"] by(auto simp add: in_cut_def algebra_simps)
qed

lemma cut_loop_props:
  "cut_loop S e k cap dem ⟹
     (∀ i ∈ {e..<e + k}. leaves_cut S i ⟶ ¬ uncapacitated i)
     ∧ cap + (∑ i ∈ {i ∈ {e..<e + k}. leaves_cut S i}. capacity_list ! i) < dem"
proof(induction k arbitrary: e cap)
  case 0
  thus ?case by simp
next
  case (Suc k)
  have notin: "e ∉ {i ∈ {Suc e..<Suc e + k}. leaves_cut S i}" by auto
  show ?case
  proof(cases "leaves_cut S e")
    case True
    hence fin: "¬ uncapacitated e" and rest: "cut_loop S (Suc e) k (cap + capacity_list ! e) dem"
      using Suc.prems by(auto simp add: uncapacitated_def leaves_cut_def in_cut_def Let_def)
    show ?thesis
      using Suc.IH[OF rest] True fin notin
      unfolding range_split_first by(auto simp add: algebra_simps order_le_less)
  next
    case False
    hence rest: "cut_loop S (Suc e) k cap dem"
      using Suc.prems by(auto simp add: leaves_cut_def in_cut_def)
    show ?thesis
      using Suc.IH[OF rest] False notin
      unfolding range_split_first by(auto simp add: algebra_simps order_le_less)
  qed
qed

text ‹The flagged vertices are a cut of the network in the sense of @{const multigraph_spec.Delta_plus},
      and the arcs crossing it are exactly the ones @{const leaves_cut} selects --- both endpoints of
      an arc are vertices, so an endpoint outside the flagged ∗‹vertices› is an unflagged vertex.›

lemma net_Delta_plus_cut:
  "network.Delta_plus {v ∈ network.𝒱. in_cut S v} = {e ∈ {0..<m}. leaves_cut S e}"
proof(rule set_eqI, rule iffI)
  fix e assume "e ∈ network.Delta_plus {v ∈ network.𝒱. in_cut S v}"
  hence e: "e < m" "fst_list ! e ∈ network.𝒱 ∧ in_cut S (fst_list ! e)"
           "¬ (snd_list ! e ∈ network.𝒱 ∧ in_cut S (snd_list ! e))"
    by(auto simp add: multigraph_spec.Delta_plus_def)
  show "e ∈ {e ∈ {0..<m}. leaves_cut S e}"
    using e net_endpoints_V(2)[OF e(1)] by(auto simp add: leaves_cut_def)
next
  fix e assume e: "e ∈ {e ∈ {0..<m}. leaves_cut S e}"
  hence lt: "e < m" and lc: "leaves_cut S e" by auto
  show "e ∈ network.Delta_plus {v ∈ network.𝒱. in_cut S v}"
    using lt lc net_endpoints_V(1)[OF lt]
    by(auto simp add: multigraph_spec.Delta_plus_def leaves_cut_def)
qed

text ‹A flagged slot that is not a vertex contributes nothing to the demand: slot @{term ‹0::nat›}
      carries the sentinel zero, and a name no arc mentions has balance zero by
      @{thm [source] isolated_zero}.  This is the one place the lonely-vertex assumption is used, and
      it is what lets the checker sweep the whole balance array while the theory reasons about
      @{term network.𝒱}.›

lemma cut_balance_sum:
  "(∑ i ∈ {i ∈ {0..<Suc n}. in_cut S i}. balance_list ! i)
     = (∑ v ∈ {v ∈ network.𝒱. in_cut S v}. balance_list ! v)"
proof(rule sum.mono_neutral_right, goal_cases)
  case 1 show ?case by simp
next
  case 2 show ?case using net_V_subset by auto
next
  case 3
  show ?case
  proof
    fix i assume i: "i ∈ {i ∈ {0..<Suc n}. in_cut S i} - {v ∈ network.𝒱. in_cut S v}"
    hence i': "i < Suc n" "in_cut S i" "i ∉ network.𝒱" by auto
    show "balance_list ! i = 0"
    proof(cases "i = 0")
      case True
      thus ?thesis by(simp add: balance_sentinel)
    next
      case False
      have "∀ e < m. fst_list ! e ≠ i ∧ snd_list ! e ≠ i"
        using i'(3) net_endpoints_V by auto
      thus ?thesis using i' False by(intro isolated_zero) auto
    qed
  qed
qed

text ‹Soundness is then @{thm [source] network.flow_less_cut}, the Gale--Hoffman bound of ‹Residual›:
      the balances inside a vertex set never exceed the capacity leaving it, and the certificate
      exhibits a set where they do.›

theorem check_infeasible_sound:
  assumes "check_infeasible S"
  shows "∄ f. network.isbflow f bal"
proof(rule notI, erule exE)
  fix f assume f: "network.isbflow f bal"
  define X where "X = {v ∈ network.𝒱. in_cut S v}"
  have XV: "X ⊆ network.𝒱" by(auto simp add: X_def)
  note key = network.flow_less_cut[OF f XV]
  have loop: "cut_loop S 0 m 0 (demand_loop S 0 (Suc n) 0)"
    using assms by(simp add: check_infeasible_def)
  note props = cut_loop_props[OF loop]
  have dem: "demand_loop S 0 (Suc n) 0 = (∑ v ∈ X. balance_list ! v)"
    unfolding X_def using demand_loop_sum[of S 0 "Suc n" 0] cut_balance_sum by simp
  have DX: "network.Delta_plus X = {e ∈ {0..<m}. leaves_cut S e}"
    unfolding X_def by(rule net_Delta_plus_cut)
  have less: "(∑ e ∈ network.Delta_plus X. capacity_list ! e) < (∑ v ∈ X. balance_list ! v)"
    using props dem by(simp add: DX)
  have finX: "finite X" using XV network.𝒱_finite by(auto intro: finite_subset)
  have finD: "finite (network.Delta_plus X)" by(simp add: DX)
  have cap_eq: "network.Cap X = ereal (h (∑ e ∈ network.Delta_plus X. capacity_list ! e))"
  proof -
    have "cap_u e = ereal (h (capacity_list ! e))" if "e ∈ network.Delta_plus X" for e
      using that props by(auto simp add: DX cap_u_def)
    hence "network.Cap X = (∑ e ∈ network.Delta_plus X. ereal (h (capacity_list ! e)))"
      by(auto simp add: flow_network_spec.Cap_def intro: sum.cong)
    thus ?thesis by(simp add: h_sum[OF finD])
  qed
  have bal_sum: "sum bal X = h (∑ v ∈ X. balance_list ! v)"
    by(simp add: bal_def h_sum[OF finX])
  show False
    using key less by(simp add: cap_eq bal_sum)
qed

subsection ‹Optimality: the primal-dual certificate is sound›

text ‹One step of the scatter, at one vertex.  The head is written first and read back by the tail
      update, so the two cancel at a self-loop; away from a self-loop each update lands on its own
      cell.›

lemma net_step_nth:
  "(let net' = net[v := net ! v - f] in net'[u := net' ! u + f]) ! w
     = net ! w + (if u = w then f else 0) - (if v = w then (f::'n) else 0)"
  if "u < length net" "v < length net" "w < length net"
  using that by(auto simp add: nth_list_update Let_def)

text ‹The loop invariant.  Running the arcs of a range leaves the accumulator holding, at every
      vertex, the balance minus the net out-flow of the arcs still to come --- so when the range is
      exhausted and the accumulator is the balance array, the flow's net out-flow ∗‹is› the balance.
      Alongside that, every arc of the range satisfies @{const arc_ok_opt}, the per-arc feasibility
      and slackness condition the loop fuses into the same pass.›

lemma opt_loop_props:
  "⟦opt_loop fl pot e k net; length net = Suc n; e + k ≤ m⟧ ⟹
     (∀ i ∈ {e..<e + k}. arc_ok_opt fl pot i)
     ∧ (∀ v ≤ n. balance_list ! v = net ! v
                    + (∑ i ∈ {i ∈ {e..<e + k}. fst_list ! i = v}. fl ! i)
                    - (∑ i ∈ {i ∈ {e..<e + k}. snd_list ! i = v}. fl ! i))"
proof(induction k arbitrary: e net)
  case 0
  thus ?case using length_balance by auto
next
  case (Suc k)
  have e: "e < m" using Suc.prems by simp
  have u: "fst_list ! e < length net" and v: "snd_list ! e < length net"
    using tail_is_vertex[OF e] head_is_vertex[OF e] Suc.prems(2) by auto
  have ok: "arc_ok_opt fl pot e"
    using Suc.prems(1)
    by(auto simp add: arc_ok_opt_def uncapacitated_def rc_of_def Let_def split: if_splits)
  define net' where "net' = (let nn = net[snd_list ! e := net ! (snd_list ! e) - fl ! e]
                             in nn[fst_list ! e := nn ! (fst_list ! e) + fl ! e])"
  have rest: "opt_loop fl pot (Suc e) k net'"
    using Suc.prems(1) by(auto simp add: Let_def net'_def)
  have len': "length net' = Suc n" using Suc.prems(2) by(simp add: net'_def Let_def)
  note IH = Suc.IH[OF rest len']
  have IH': "(∀ i ∈ {Suc e..<Suc e + k}. arc_ok_opt fl pot i)
             ∧ (∀ v ≤ n. balance_list ! v = net' ! v
                    + (∑ i ∈ {i ∈ {Suc e..<Suc e + k}. fst_list ! i = v}. fl ! i)
                    - (∑ i ∈ {i ∈ {Suc e..<Suc e + k}. snd_list ! i = v}. fl ! i))"
    using IH Suc.prems(3) by simp
  have net'_nth: "net' ! w = net ! w + (if fst_list ! e = w then fl ! e else 0)
                                     - (if snd_list ! e = w then fl ! e else 0)"
    if "w < length net" for w
    using net_step_nth[OF u v that] by(simp add: net'_def)
  show ?case
  proof(intro conjI ballI allI impI)
    fix i assume "i ∈ {e..<e + Suc k}"
    thus "arc_ok_opt fl pot i" using ok IH' by(cases "i = e") auto
  next
    fix w assume w: "w ≤ n"
    hence wlen: "w < length net" using Suc.prems(2) by simp
    have notin: "e ∉ {i ∈ {Suc e..<Suc e + k}. Q i}" for Q by auto
    have "balance_list ! w = net' ! w
             + (∑ i ∈ {i ∈ {Suc e..<Suc e + k}. fst_list ! i = w}. fl ! i)
             - (∑ i ∈ {i ∈ {Suc e..<Suc e + k}. snd_list ! i = w}. fl ! i)"
      using IH' w by simp
    thus "balance_list ! w = net ! w
             + (∑ i ∈ {i ∈ {e..<e + Suc k}. fst_list ! i = w}. fl ! i)
             - (∑ i ∈ {i ∈ {e..<e + Suc k}. snd_list ! i = w}. fl ! i)"
      unfolding range_split_first using notin net'_nth[OF wlen] by(auto simp add: algebra_simps)
  qed
qed

text ‹Run at the full range from a zeroed accumulator, that is what the check establishes about the
      certificate: every arc is feasible and slack, and every vertex's net out-flow is its balance.›

lemma check_optimum_flow:
  assumes "check_optimum fl pot"
  shows "⋀ i. i < m ⟹ arc_ok_opt fl pot i"
    and "⋀ v. v ≤ n ⟹ balance_list ! v = (∑ i ∈ {i ∈ {0..<m}. fst_list ! i = v}. fl ! i)
                                        - (∑ i ∈ {i ∈ {0..<m}. snd_list ! i = v}. fl ! i)"
proof -
  have loop: "opt_loop fl pot 0 m (replicate (Suc n) 0)"
    using assms by(simp add: check_optimum_def)
  have p: "(∀ i ∈ {0..<0 + m}. arc_ok_opt fl pot i)
           ∧ (∀ v ≤ n. balance_list ! v = replicate (Suc n) 0 ! v
                    + (∑ i ∈ {i ∈ {0..<0 + m}. fst_list ! i = v}. fl ! i)
                    - (∑ i ∈ {i ∈ {0..<0 + m}. snd_list ! i = v}. fl ! i))"
    by(rule opt_loop_props[OF loop]) simp_all
  show "arc_ok_opt fl pot i" if "i < m" for i using p that by simp
  show "balance_list ! v = (∑ i ∈ {i ∈ {0..<m}. fst_list ! i = v}. fl ! i)
                         - (∑ i ∈ {i ∈ {0..<m}. snd_list ! i = v}. fl ! i)" if "v ≤ n" for v
    using p that by(simp add: nth_replicate del: replicate_Suc)
qed

text ‹Hence the certified flow is a @{term b}-flow.  The capacity side is per-arc; the balance side
      is the loop's accumulator read through the embedding, the incidence sets of the network being
      exactly the index sets the loop scattered over.›

lemma check_optimum_isbflow:
  assumes ok: "check_optimum fl pot"
  shows "network.isbflow (λ e. h (fl ! e)) bal"
proof(rule flow_network_spec.isbflowI)
  show "network.isuflow (λ e. h (fl ! e))"
  proof(rule flow_network_spec.isuflowI, goal_cases)
    case (1 e)
    hence e: "e < m" by simp
    show ?case
      using check_optimum_flow(1)[OF ok e] by(cases "uncapacitated e")
                (auto simp add: arc_ok_opt_def cap_u_def uncapacitated_def)
  next
    case (2 e)
    hence e: "e < m" by simp
    show ?case
      using check_optimum_flow(1)[OF ok e] by(auto simp add: arc_ok_opt_def)
  qed
next
  fix v assume v: "v ∈ network.𝒱"
  hence vn: "v ≤ n" using net_V_subset by auto
  have fin: "finite {i. i < m ∧ Q i}" for Q by simp
  have "network.ex (λ e. h (fl ! e)) v
          = (∑ i ∈ {i. i < m ∧ snd_list ! i = v}. h (fl ! i))
            - (∑ i ∈ {i. i < m ∧ fst_list ! i = v}. h (fl ! i))"
    by(simp add: flow_network_spec.ex_def net_delta_plus net_delta_minus)
  also have "… = h ((∑ i ∈ {i. i < m ∧ snd_list ! i = v}. fl ! i)
                    - (∑ i ∈ {i. i < m ∧ fst_list ! i = v}. fl ! i))"
    by(simp add: h_sum[OF fin])
  finally show "- network.ex (λ e. h (fl ! e)) v = bal v"
    using check_optimum_flow(2)[OF ok vn] by(simp add: bal_def)
qed

text ‹The reduced cost the checker computes in @{typ 'n} is the image of the one the theory
      computes in @{typ real}, the embedding being additive.›

lemma rc_h: "e < m ⟹
   h (cost_list ! e) + h (pot ! (fst_list ! e)) - h (pot ! (snd_list ! e)) = h (rc_of pot e)"
  by(simp add: rc_of_def h_add)

text ‹Soundness is then @{thm [source] network.optimality_from_potentials} of
      ‹Optimality_Certification›: a @{term b}-flow whose dual leaves no arc violating complementary
      slackness is optimal, the criterion being that an empty arc has non-negative reduced cost, a
      saturated one non-positive, and one strictly between the bounds zero.  Each of the three is
      the contrapositive of a conjunct the checker tested: a strictly negative reduced cost forces
      an arc to be capacitated and saturated, which an empty or strictly-inner arc is not, and a
      strictly positive one forces it empty, which a saturated arc of non-zero capacity is not.›

theorem check_optimum_sound:
  assumes ok: "check_optimum fl pot"
  shows "network.is_Opt bal (λ e. h (fl ! e))"
proof(rule network.optimality_from_potentials[where π = "λ v. h (pot ! v)"], goal_cases)
  case 1
  show ?case by(rule check_optimum_isbflow[OF ok])
next
  case (2 e)
  hence e: "e < m" and z: "fl ! e = 0" and nz: "cap_u e ≠ 0" by auto
  have "¬ rc_of pot e < 0"
  proof
    assume neg: "rc_of pot e < 0"
    hence "¬ uncapacitated e" "fl ! e = capacity_list ! e"
      using check_optimum_flow(1)[OF ok e] by(auto simp add: arc_ok_opt_def)
    thus False using z nz e by(simp add: cap_u_def zero_ereal_def)
  qed
  thus ?case using e by(simp add: rc_h)
next
  case (3 e)
  hence e: "e < m" and eq: "ereal (h (fl ! e)) = cap_u e" and nz: "cap_u e ≠ 0" by auto
  have cap: "¬ uncapacitated e" using eq e by(cases "uncapacitated e") (auto simp add: cap_u_def)
  hence fe: "fl ! e = capacity_list ! e" using eq e by(simp add: cap_u_def)
  have "¬ 0 < rc_of pot e"
  proof
    assume pos: "0 < rc_of pot e"
    hence "fl ! e = 0" using check_optimum_flow(1)[OF ok e] by(auto simp add: arc_ok_opt_def)
    thus False using nz fe cap e by(simp add: cap_u_def zero_ereal_def)
  qed
  thus ?case using e by(simp add: rc_h)
next
  case (4 e)
  hence e: "e < m" and pos: "0 < h (fl ! e)" and lt: "ereal (h (fl ! e)) < cap_u e" by auto
  have "rc_of pot e = 0"
  proof(rule ccontr)
    assume "rc_of pot e ≠ 0"
    thus False
    proof(cases "0 < rc_of pot e")
      case True
      hence "fl ! e = 0" using check_optimum_flow(1)[OF ok e] by(auto simp add: arc_ok_opt_def)
      thus False using pos by simp
    next
      case False
      hence neg: "rc_of pot e < 0" using ‹rc_of pot e ≠ 0› by simp
      hence "¬ uncapacitated e" "fl ! e = capacity_list ! e"
        using check_optimum_flow(1)[OF ok e] by(auto simp add: arc_ok_opt_def)
      thus False using lt e by(simp add: cap_u_def)
    qed
  qed
  thus ?case using e by(simp add: rc_h)
qed

text ‹The three together: whatever the oracle returns, if @{const check_answer} accepts it then the
      verdict it carries is true of this instance.›

theorem check_answer_sound:
  assumes "check_answer a"
  shows "case a of OracleOptimum fl pot _ ⇒ network.is_Opt bal (λ e. h (fl ! e))
                 | OracleInfeasible _ S   ⇒ ∄ f. network.isbflow f bal
                 | OracleUnbounded _ cyc  ⇒
                     has_neg_infty_cycle network.make_pair {0..<m} (λ e. h (cost_list ! e)) cap_u"
  using assms
  by(cases a)
    (auto simp add: check_answer_def check_optimum_sound check_infeasible_sound
                    check_unbounded_sound)

text ‹The same three statements, as a property of a ∗‹verdict› rather than of a certificate: that it
      says something true about this instance.  It is what an accepted answer gives us and what a
      verified procedure is required to give us, so it is the common currency in which the pipeline
      below is stated --- and, being a predicate on the verdict alone, it does not care which of the
      two produced it.›

definition verdict_ok :: "'n solver_verdict ⇒ bool" where
  "verdict_ok r =
     (case r of VOptimum f ⇒ network.is_Opt bal (λ e. h (f ! e))
              | VInfeasible ⇒ ∄ f. network.isbflow f bal
              | VUnbounded  ⇒
                  has_neg_infty_cycle network.make_pair {0..<m} (λ e. h (cost_list ! e)) cap_u)"

lemma verdict_of_sound: "check_answer a ⟹ verdict_ok (verdict_of a)"
  using check_answer_sound[of a] by(cases a) (auto simp add: verdict_of_def verdict_ok_def)

text ‹The checking layer, complete: an accepted answer is a true verdict about this instance.  That
      is everything the checkers can deliver on their own --- and it is a genuine result on its own,
      for a caller that has no fallback and is content to be told that the oracle was no use.›

theorem checked_verdict_sound:
  assumes "checked_verdict = Some r"
  shows "verdict_ok r"
  using assms verdict_of_sound
  by(auto simp add: checked_verdict_def checked_answer_def screen_def split: if_splits)

text ‹∗‹The mode-aware verdict predicate.› Exactly ‹verdict_ok›, except a ‹VOptimum› verdict is
      judged against ‹check_optimum_dispatch_sound›'s conclusion for ‹cm› instead of unconditional
      exactness --- the two other verdicts have no epsilon notion and are untouched. This is what
      ‹decide_imp›/‹solve_imp› ultimately need to satisfy once ‹check_answer_imp› consults ‹cm›: a
      certificate accepted only because it met the weaker ‹CheckerEpsilontic› bar can no longer make
      the pipeline's overall guarantee unconditional exactness, so the guarantee itself has to become
      checker-mode-indexed too, exactly as ‹check_answer_dispatch_sound›'s already is.›

text ‹The ‹CheckerEpsilontic› branch also has to carry that ‹f› is a genuine ‹bal›-flow: the raw
      dual-slack witness alone says nothing about ‹f› being feasible at all, and a caller who later
      wants to turn the slack into exact optimality (‹optimality_from_eps_potentials›, given cost
      integrality) needs ‹bflow› as a separate hypothesis it cannot otherwise recover. ‹CheckerNormal›
      needs no such addition --- ‹is_Opt› already gives ‹bflow› for free via ‹is_Opt_def›.›

definition verdict_ok_dispatch :: "checker_mode ⇒ nat ⇒ 'n solver_verdict ⇒ bool" where
  "verdict_ok_dispatch cm M r =
     (case r of
        VOptimum f ⇒ (case cm of
                        CheckerNormal ⇒ network.is_Opt bal (λ e. h (f ! e))
                      | CheckerEpsilontic ⇒
                          network.isbflow (λ e. h (f ! e)) bal ∧
                          (∃ π. ∀ e ∈ network.𝔈. network.rcap (λ e. h (f ! e)) e > 0 ⟶
                                 network.𝔠 e + π (network.fstv e) - π (network.sndv e) ≥ - (1 / real M)))
      | VInfeasible ⇒ ∄ f. network.isbflow f bal
      | VUnbounded  ⇒ has_neg_infty_cycle network.make_pair {0..<m} (λ e. h (cost_list ! e)) cap_u)"

text ‹The cleanup's verdict is always fully exact (‹cleanup_imp_rule›'s own assumption, unconditionally),
      so it always meets the weaker bar too, for any ‹cm› and any ‹M› --- exactly the same free
      weakening ‹check_optimum_dispatch_sound›'s ‹CertExact› branch uses.›

lemma verdict_ok_imp_dispatch:
  assumes vok: "verdict_ok r" and Mpos: "0 < M"
  shows "verdict_ok_dispatch cm M r"
proof (cases r)
  case (VOptimum f)
  have opt: "network.is_Opt bal (λ e. h (f ! e))" using vok VOptimum by(simp add: verdict_ok_def)
  have bflow: "network.isbflow (λ e. h (f ! e)) bal" using opt by(simp add: network.is_Opt_def)
  have eps_nonneg: "0 ≤ 1 / real M" using Mpos by simp
  have slack: "∃ π. ∀ e ∈ network.𝔈. network.rcap (λ e. h (f ! e)) e > 0 ⟶
                 network.𝔠 e + π (network.fstv e) - π (network.sndv e) ≥ - (1 / real M)"
    using network.is_Opt_imp_eps_complementary_slack[OF bflow opt eps_nonneg] .
  show ?thesis
    using VOptimum opt bflow slack by(simp add: verdict_ok_dispatch_def split: checker_mode.splits)
next
  case VInfeasible thus ?thesis using vok by(simp add: verdict_ok_dispatch_def verdict_ok_def)
next
  case VUnbounded thus ?thesis using vok by(simp add: verdict_ok_dispatch_def verdict_ok_def)
qed

text ‹∗‹The ε-slack check, unconditionally.›  None of ‹h_of_nat›, ‹opt_loop_eps_props›,
      ‹check_optimum_eps_flow› or ‹scaled_rc_eps_h› needs ‹cost_integer› --- only the step turning a
      scaled slack bound into exact optimality (‹check_optimum_eps_sound›, in ‹mcf_oracle_eps›,
      alongside ‹check_optimum_dispatch_sound› and everything built on it) does.›

lemma h_of_nat [simp]: "h (of_nat M) = of_nat M"
  by(induction M) (simp_all add: h_add)

text ‹Exactly ‹opt_loop_props›, with ‹arc_ok_eps› in place of ‹arc_ok_opt› and ‹M› carried through
      unchanged --- it is a fixed parameter of the whole sweep, never touched inside the loop.›

lemma opt_loop_eps_props:
  "⟦opt_loop_eps Mn fl pot e k net; length net = Suc n; e + k ≤ m⟧ ⟹
     (∀ i ∈ {e..<e + k}. arc_ok_eps Mn fl pot i)
     ∧ (∀ v ≤ n. balance_list ! v = net ! v
                    + (∑ i ∈ {i ∈ {e..<e + k}. fst_list ! i = v}. fl ! i)
                    - (∑ i ∈ {i ∈ {e..<e + k}. snd_list ! i = v}. fl ! i))"
proof(induction k arbitrary: e net)
  case 0
  thus ?case using length_balance by auto
next
  case (Suc k)
  have e: "e < m" using Suc.prems by simp
  have u: "fst_list ! e < length net" and v: "snd_list ! e < length net"
    using tail_is_vertex[OF e] head_is_vertex[OF e] Suc.prems(2) by auto
  have ok: "arc_ok_eps Mn fl pot e"
    using Suc.prems(1)
    by(auto simp add: arc_ok_eps_def uncapacitated_def scaled_rc_of_def Let_def split: if_splits)
  define net' where "net' = (let nn = net[snd_list ! e := net ! (snd_list ! e) - fl ! e]
                             in nn[fst_list ! e := nn ! (fst_list ! e) + fl ! e])"
  have rest: "opt_loop_eps Mn fl pot (Suc e) k net'"
    using Suc.prems(1) by(auto simp add: Let_def net'_def)
  have len': "length net' = Suc n" using Suc.prems(2) by(simp add: net'_def Let_def)
  note IH = Suc.IH[OF rest len']
  have IH': "(∀ i ∈ {Suc e..<Suc e + k}. arc_ok_eps Mn fl pot i)
             ∧ (∀ v ≤ n. balance_list ! v = net' ! v
                    + (∑ i ∈ {i ∈ {Suc e..<Suc e + k}. fst_list ! i = v}. fl ! i)
                    - (∑ i ∈ {i ∈ {Suc e..<Suc e + k}. snd_list ! i = v}. fl ! i))"
    using IH Suc.prems(3) by simp
  have net'_nth: "net' ! w = net ! w + (if fst_list ! e = w then fl ! e else 0)
                                     - (if snd_list ! e = w then fl ! e else 0)"
    if "w < length net" for w
    using net_step_nth[OF u v that] by(simp add: net'_def)
  show ?case
  proof(intro conjI ballI allI impI)
    fix i assume "i ∈ {e..<e + Suc k}"
    thus "arc_ok_eps Mn fl pot i" using ok IH' by(cases "i = e") auto
  next
    fix w assume w: "w ≤ n"
    hence wlen: "w < length net" using Suc.prems(2) by simp
    have notin: "e ∉ {i ∈ {Suc e..<Suc e + k}. Q i}" for Q by auto
    have "balance_list ! w = net' ! w
             + (∑ i ∈ {i ∈ {Suc e..<Suc e + k}. fst_list ! i = w}. fl ! i)
             - (∑ i ∈ {i ∈ {Suc e..<Suc e + k}. snd_list ! i = w}. fl ! i)"
      using IH' w by simp
    thus "balance_list ! w = net ! w
             + (∑ i ∈ {i ∈ {e..<e + Suc k}. fst_list ! i = w}. fl ! i)
             - (∑ i ∈ {i ∈ {e..<e + Suc k}. snd_list ! i = w}. fl ! i)"
      unfolding range_split_first using notin net'_nth[OF wlen] by(auto simp add: algebra_simps)
  qed
qed

lemma check_optimum_eps_flow:
  assumes "check_optimum_eps Mn fl pot"
  shows "⋀ i. i < m ⟹ arc_ok_eps Mn fl pot i"
    and "⋀ v. v ≤ n ⟹ balance_list ! v = (∑ i ∈ {i ∈ {0..<m}. fst_list ! i = v}. fl ! i)
                                        - (∑ i ∈ {i ∈ {0..<m}. snd_list ! i = v}. fl ! i)"
proof -
  have loop: "opt_loop_eps Mn fl pot 0 m (replicate (Suc n) 0)"
    using assms by(simp add: check_optimum_eps_def)
  have p: "(∀ i ∈ {0..<0 + m}. arc_ok_eps Mn fl pot i)
           ∧ (∀ v ≤ n. balance_list ! v = replicate (Suc n) 0 ! v
                    + (∑ i ∈ {i ∈ {0..<0 + m}. fst_list ! i = v}. fl ! i)
                    - (∑ i ∈ {i ∈ {0..<0 + m}. snd_list ! i = v}. fl ! i))"
    by(rule opt_loop_eps_props[OF loop]) simp_all
  show "arc_ok_eps Mn fl pot i" if "i < m" for i using p that by simp
  show "balance_list ! v = (∑ i ∈ {i ∈ {0..<m}. fst_list ! i = v}. fl ! i)
                         - (∑ i ∈ {i ∈ {0..<m}. snd_list ! i = v}. fl ! i)" if "v ≤ n" for v
    using p that by(simp add: nth_replicate del: replicate_Suc)
qed

text ‹The scaled reduced cost the checker computes in ‹'n›, read through ‹h›, is the one
      ‹optimality_from_eps_potentials› sums over the cycle.›

lemma scaled_rc_eps_h:
  "e < m ⟹ h Mn * h (cost_list ! e) + h (pot ! (fst_list ! e)) - h (pot ! (snd_list ! e))
            = h (scaled_rc_of Mn pot e)"
  by(simp add: scaled_rc_of_def h_add h_mult)

text ‹Exactly ‹check_optimum_isbflow›: primal feasibility and the balance condition do not depend on
      which dual check accompanies them.›

lemma check_optimum_eps_isbflow:
  assumes ok: "check_optimum_eps Mn fl pot"
  shows "network.isbflow (λ e. h (fl ! e)) bal"
proof(rule flow_network_spec.isbflowI)
  show "network.isuflow (λ e. h (fl ! e))"
  proof(rule flow_network_spec.isuflowI, goal_cases)
    case (1 e)
    hence e: "e < m" by simp
    show ?case
      using check_optimum_eps_flow(1)[OF ok e] by(cases "uncapacitated e")
                (auto simp add: arc_ok_eps_def cap_u_def uncapacitated_def)
  next
    case (2 e)
    hence e: "e < m" by simp
    show ?case
      using check_optimum_eps_flow(1)[OF ok e] by(auto simp add: arc_ok_eps_def)
  qed
next
  fix v assume v: "v ∈ network.𝒱"
  hence vn: "v ≤ n" using net_V_subset by auto
  have fin: "finite {i. i < m ∧ Q i}" for Q by simp
  have "network.ex (λ e. h (fl ! e)) v
          = (∑ i ∈ {i. i < m ∧ snd_list ! i = v}. h (fl ! i))
            - (∑ i ∈ {i. i < m ∧ fst_list ! i = v}. h (fl ! i))"
    by(simp add: flow_network_spec.ex_def net_delta_plus net_delta_minus)
  also have "… = h ((∑ i ∈ {i. i < m ∧ snd_list ! i = v}. fl ! i)
                    - (∑ i ∈ {i. i < m ∧ fst_list ! i = v}. fl ! i))"
    by(simp add: h_sum[OF fin])
  finally show "- network.ex (λ e. h (fl ! e)) v = bal v"
    using check_optimum_eps_flow(2)[OF ok vn] by(simp add: bal_def)
qed

end

subsection ‹The reduction's output is an instance of that format›

text ‹The claim that the two formats agree, discharged.  Every assumption of @{locale mcf_oracle}
      is proved for the lists the reduction leaves behind, so the pipeline may hand them to the
      oracle; nothing here mentions the oracle itself.

      The reduced instance is the caller's own arrays: its arcs are the original ones, so the
      endpoints and the costs are passed through and only the capacities and the balances change.
      Its node count is therefore ‹n - 1›, the vertex names being ‹{1..<n}› without the reserved
      slot, and ‹arcs_nonempty› already forces ‹1 < n›.

      The two conditions that are not about the shape of the pass --- that the balances sum to zero,
      and that a vertex no arc touches has balance ‹0› --- are exactly what ‹red_ok› tests, and are
      unavailable without it: an infeasible instance is rejected before the oracle is reached.›

context dimacs_lists_network
begin

lemma orc_nodes: "Suc 0 < n"
  using m_pos_n[OF arcs_nonempty] by simp

lemma orc_lengths:
  "length fst_list = m" "length snd_list = m"
  "length red_upper = m" "length cost_list = m"
  "length red_balance_list = Suc (n - 1)" "0 < m"
  using length_fst_list length_snd_list length_cost_list red_upper_length
        red_balance_list_length nodes_nonempty arcs_nonempty
  by auto

text ‹Both endpoints of every arc are vertex names, unchanged from the input.›

lemma orc_endpoints:
  assumes e: "e < m"
  shows "fst_list ! e ∈ {Suc 0..n - 1}" "snd_list ! e ∈ {Suc 0..n - 1}"
  using fst_list_vertex[OF e] snd_list_vertex[OF e] orc_nodes by auto

text ‹Every reduced capacity is non-negative --- it is ‹u - l› on an arc of non-empty range and ‹0›
      otherwise --- so the uncapacitated sentinel never arises.›

lemma orc_capacity:
  assumes e: "e < m"
  shows "0 ≤ red_upper ! e ∨ red_upper ! e = - 1"
  using red_upper_orig_nonneg[OF e] by simp

text ‹The reserved slot is untouched: the pass writes only at endpoints, and those are names.›

lemma orc_sentinel: "red_balance_list ! 0 = 0"
  by(simp add: red_balance_list_def red_balance_raw_sentinel)

text ‹The balances sum to zero by ‹sum_ok›.›

lemma orc_sum_zero:
  assumes ok: "red_ok"
  shows "sum_list red_balance_list = 0"
  using sum_okD[OF ok] by(simp add: red_balance_list_def sum_ok_def)

text ‹A vertex no arc touches has balance ‹0›: its incident capacity is empty on both sides, so the
      range test of ‹bal_ok› pins the balance between ‹0› and ‹0›.›

lemma orc_isolated:
  assumes ok: "red_ok" and v: "v ∈ {Suc 0..n - 1}"
      and lonely: "⋀ e. e < m ⟹ fst_list ! e ≠ v ∧ snd_list ! e ≠ v"
  shows "red_balance_list ! v = 0"
proof -
  have vr: "v ∈ {1..<n}" using v orc_nodes by auto
  have co: "capout v = 0"
  proof -
    have "(∑ i ∈ {0..<m}. (if fst_list ! i = v then red_upper ! i else 0)) = 0"
      using lonely by(intro sum.neutral) auto
    thus ?thesis by(simp add: capout_def interv_sum_list_conv_sum_set_nat)
  qed
  have ci: "capin v = 0"
  proof -
    have "(∑ i ∈ {0..<m}. (if snd_list ! i = v then red_upper ! i else 0)) = 0"
      using lonely by(intro sum.neutral) auto
    thus ?thesis by(simp add: capin_def interv_sum_list_conv_sum_set_nat)
  qed
  have z: "red_balance_raw ! v = 0"
  proof -
    have "- capin v ≤ red_balance_raw ! v" and "red_balance_raw ! v ≤ capout v"
      using bal_okD[OF ok] vr by(auto simp add: bal_ok_def)
    thus ?thesis using co ci by linarith
  qed
  show ?thesis using z vr by(simp add: red_balance_list_nth)
qed

text ‹Hence a feasible reduced instance has the format the certifier assumes, for any oracle
      whatever --- the parameter does not occur in the assumptions.›

lemma reduced_is_oracle_instance:
  assumes ok: "red_ok"
  shows "mcf_oracle fst_list snd_list cost_list red_balance_list m (n - 1) red_upper h"
proof(unfold_locales, goal_cases)
  case (8 e) thus ?case using orc_endpoints[OF 8] by simp
next
  case (9 e) thus ?case using orc_endpoints[OF 9] by simp
next
  case (10 e) thus ?case using orc_capacity by simp
next
  case (13 v) thus ?case using orc_isolated[OF ok] by fastforce
qed (auto simp add: orc_lengths orc_sentinel orc_sum_zero[OF ok] orc_nodes)

end


subsection ‹The pipeline: check the oracle, else clean up›

text ‹The oracle alone decides nothing: a rejected certificate leaves the instance unsolved, and the
      pipeline has to fall back on something it trusts.  That something is a ∗‹verified cleanup› --- a
      procedure taking the instance and a flow and returning a verdict, warm-started from the flow
      the oracle stopped at, which is why every answer carries one.  It is a parameter here for the
      same reason the oracle is: this theory says what it must deliver, not how.

      The extension is one ‹fixes› on the code locale.  ‹decide› is the whole arrangement in a line
      --- check the certificate, take the verdict if it holds, otherwise hand the instance and the
      flow to the cleanup --- and ‹solve› applies it to the oracle's answer.  ‹orc_answer› occurs
      once, so the external solver runs once whichever branch is taken.›

text ‹∗‹ε-optimality is sound too, given integer costs.›  The one hypothesis
      ‹optimality_from_scaled_potentials› needs beyond what ‹mcf_oracle› already assumes is that arc
      costs are integers --- automatic in the concrete pipeline, where ‹'n› is ‹int› and
      ‹h = of_int›, but not provable for an arbitrary ‹real_embedding›, so it is a genuinely
      new hypothesis of a new locale rather than an addition to ‹mcf_oracle›.›

locale mcf_oracle_eps = mcf_oracle where capacity_list = capacity_list and h = h
  for capacity_list :: "('n :: linordered_idom) list" and h +
  assumes cost_integer: "⋀e. e < m ⟹ h (cost_list ! e) ∈ ℤ"
begin

text ‹‹check_optimum_eps_isbflow› and ‹scaled_rc_eps_h› now live in ‹mcf_oracle›, alongside
      ‹check_optimum_eps_flow›: none of them needs ‹cost_integer›.›
text ‹Soundness.  The primal half is ‹check_optimum_eps_isbflow›, unchanged from the exact check.
      The vertex bound is ‹net_V_subset› composed with the check's own ‹n < M› test.  Integrality of
      every residual cost reduces, by cases on the two orientations a residual arc can have, to
      ‹cost_integer› on the underlying arc (negating an integer leaves it an integer).  And the
      per-arc scaled-slack bound reduces the same way to ‹arc_ok_eps›'s two conjuncts, the case
      distinction being exactly which of a residual arc's two orientations is open: ‹F d› needs the
      arc not fully saturated, ‹B d› needs it to carry positive flow, matching ‹rcap›'s own
      case split.›

theorem check_optimum_eps_sound:
  assumes ok: "check_optimum_eps Mn fl pot"
  shows "network.is_Opt bal (λ e. h (fl ! e))"
proof(rule network.optimality_from_eps_potentials
        [where ε = "1 / h Mn" and π = "λ v. h (pot ! v) / h Mn"], goal_cases)
  case 1
  show ?case by(rule check_optimum_eps_isbflow[OF ok])
next
  case 2
  have nMn: "of_nat n < Mn" using ok by(simp add: check_optimum_eps_def)
  have Mnpos: "(0::'n) < Mn" using of_nat_0_le_iff[of n] nMn by(rule le_less_trans)
  have hMnpos: "0 < h Mn" using Mnpos by simp
  show ?case using hMnpos by simp
next
  case 3
  have nMn: "of_nat n < Mn" using ok by(simp add: check_optimum_eps_def)
  have Mnpos: "(0::'n) < Mn" using of_nat_0_le_iff[of n] nMn by(rule le_less_trans)
  have hMnpos: "0 < h Mn" using Mnpos by simp
  have card_le: "card network.𝒱 ≤ n"
  proof -
    have "card network.𝒱 ≤ card {Suc 0..n}" by(rule card_mono) (use net_V_subset in auto)
    thus ?thesis by simp
  qed
  have hnMn: "h (of_nat n) < h Mn" using nMn by (simp only: h_less_iff)
  have "real (card network.𝒱) ≤ real n" using card_le by simp
  also have "real n = h (of_nat n)" by simp
  also note hnMn
  finally show ?case using hMnpos by (simp add: field_simps)
next
  case (4 e)
  then obtain d where d: "d < m" "e = F d ∨ e = B d"
    unfolding network.𝔈_def by auto
  show ?case
    using d cost_integer[OF d(1)] by(cases "e = F d") (auto simp add: network.𝔠.simps Ints_minus)
next
  case 5
  have nMn: "of_nat n < Mn" using ok by(simp add: check_optimum_eps_def)
  have Mnpos: "(0::'n) < Mn" using of_nat_0_le_iff[of n] nMn by(rule le_less_trans)
  have hMnpos: "0 < h Mn" using Mnpos by simp
  show ?case
  proof(intro ballI impI)
    fix e assume eE: "e ∈ network.𝔈" and pos: "network.rcap (λ e. h (fl ! e)) e > 0"
    from eE obtain d where d: "d < m" "e = F d ∨ e = B d"
      unfolding network.𝔈_def by auto
    from d(2) show "network.𝔠 e + h (pot ! network.fstv e) / h Mn - h (pot ! network.sndv e) / h Mn
                      ≥ - (1 / h Mn)"
    proof
      assume eF: "e = F d"
      have "0 < cap_u d - ereal (h (fl ! d))"
        using pos eF by(simp add: network.rcap.simps)
      hence open_fwd: "uncapacitated d ∨ fl ! d < capacity_list ! d"
        using d(1) by(cases "uncapacitated d") (auto simp add: cap_u_def uncapacitated_def)
      have "- 1 ≤ scaled_rc_of Mn pot d"
        using check_optimum_eps_flow(1)[OF ok d(1)] open_fwd by(auto simp add: arc_ok_eps_def)
      hence hlb: "h (- 1) ≤ h (scaled_rc_of Mn pot d)" by(rule h_mono)
      have key: "- 1 ≤ h Mn * h (cost_list ! d) + h (pot ! (fst_list ! d)) - h (pot ! (snd_list ! d))"
        using hlb scaled_rc_eps_h[OF d(1), of Mn pot] by simp
      have divided: "- 1 / h Mn ≤ h (cost_list ! d) + h (pot ! (fst_list ! d)) / h Mn
                                      - h (pot ! (snd_list ! d)) / h Mn"
        using divide_right_mono[OF key, of "h Mn"] hMnpos
        by(simp add: add_divide_distrib diff_divide_distrib)
      thus ?thesis
        using eF d(1) by(simp add: network.𝔠.simps network.fstv.simps network.sndv.simps)
    next
      assume eB: "e = B d"
      have "0 < ereal (h (fl ! d))" using pos eB by(simp add: network.rcap.simps)
      hence open_bwd: "0 < fl ! d" by simp
      have "scaled_rc_of Mn pot d ≤ 1"
        using check_optimum_eps_flow(1)[OF ok d(1)] open_bwd by(auto simp add: arc_ok_eps_def)
      hence hub: "h (scaled_rc_of Mn pot d) ≤ h 1" by(rule h_mono)
      have keyB: "h Mn * h (cost_list ! d) + h (pot ! (fst_list ! d)) - h (pot ! (snd_list ! d)) ≤ 1"
        using hub scaled_rc_eps_h[OF d(1), of Mn pot] by simp
      have dividedB: "h (cost_list ! d) + h (pot ! (fst_list ! d)) / h Mn
                        - h (pot ! (snd_list ! d)) / h Mn ≤ 1 / h Mn"
        using divide_right_mono[OF keyB, of "h Mn"] hMnpos
        by(simp add: add_divide_distrib diff_divide_distrib)
      thus ?thesis
        using eB d(1) by(simp add: network.𝔠.simps network.fstv.simps network.sndv.simps)
    qed
  qed
qed

text ‹∗‹The uniform contract, indexed by checker mode.› ‹certm› is visible only in the hypothesis
      ‹ok› --- naming which certificate was checked --- never in the conclusion: both branches (which
      of ‹check_optimum›/‹check_optimum_eps› actually fired is decided by ‹of_nat n < ¦certm¦›, the
      same gate ‹check_optimum_dispatch› itself uses) are pushed all the way to ‹is_Opt› first, then
      weakened by ‹is_Opt_imp_eps_complementary_slack› to whatever scale ‹M› the ∗‹caller› --- not the
      certificate --- chooses. That is what keeps the conclusion's shape exactly what it was before
      ‹certm› carried a scale at all: parametrised by a freely-chosen ‹M›, with no trace of ‹certm›'s
      value in it.›

theorem check_optimum_dispatch_sound:
  assumes ok: "check_optimum_dispatch cm fl pot certm" and Mpos: "0 < M"
  shows "case cm of
           CheckerNormal ⇒ network.is_Opt bal (λ e. h (fl ! e))
         | CheckerEpsilontic ⇒
             network.isbflow (λ e. h (fl ! e)) bal ∧
             (∃ π. ∀ e ∈ network.𝔈. network.rcap (λ e. h (fl ! e)) e > 0 ⟶
                    network.𝔠 e + π (network.fstv e) - π (network.sndv e) ≥ - (1 / real M))"
proof(cases cm)
  case CheckerNormal
  hence "check_optimum fl pot" using ok by(simp add: check_optimum_dispatch_def)
  thus ?thesis using CheckerNormal by(simp add: check_optimum_sound)
next
  case CheckerEpsilontic
  have opt: "network.is_Opt bal (λ e. h (fl ! e))"
  proof(cases "of_nat n < ¦certm¦")
    case True
    hence "check_optimum_eps ¦certm¦ fl pot"
      using ok CheckerEpsilontic by(simp add: check_optimum_dispatch_def)
    thus ?thesis by(rule check_optimum_eps_sound)
  next
    case False
    hence "check_optimum fl pot" using ok CheckerEpsilontic by(simp add: check_optimum_dispatch_def)
    thus ?thesis by(rule check_optimum_sound)
  qed
  have bflow: "network.isbflow (λ e. h (fl ! e)) bal" using opt by(simp add: network.is_Opt_def)
  have eps_nonneg: "0 ≤ 1 / real M" using Mpos by simp
  have "∃ π. ∀ e ∈ network.𝔈. network.rcap (λ e. h (fl ! e)) e > 0 ⟶
                network.𝔠 e + π (network.fstv e) - π (network.sndv e) ≥ - (1 / real M)"
    using network.is_Opt_imp_eps_complementary_slack[OF bflow opt eps_nonneg] .
  thus ?thesis using CheckerEpsilontic bflow by simp
qed

text ‹The mode-aware counterpart of ‹check_answer_sound›: the same three-way case split on the
      verdict, but the ‹OracleOptimum› branch is itself checker-mode-indexed, exactly as
      ‹check_optimum_dispatch_sound› is.›

theorem check_answer_dispatch_sound:
  assumes ok: "check_answer_dispatch cm a" and Mpos: "0 < M"
  shows "case a of
           OracleOptimum fl pot certm ⇒
             (case cm of
                CheckerNormal ⇒ network.is_Opt bal (λ e. h (fl ! e))
              | CheckerEpsilontic ⇒
                  network.isbflow (λ e. h (fl ! e)) bal ∧
                  (∃ π. ∀ e ∈ network.𝔈. network.rcap (λ e. h (fl ! e)) e > 0 ⟶
                         network.𝔠 e + π (network.fstv e) - π (network.sndv e) ≥ - (1 / real M)))
         | OracleInfeasible _ S  ⇒ ∄ f. network.isbflow f bal
         | OracleUnbounded _ cyc ⇒
             has_neg_infty_cycle network.make_pair {0..<m} (λ e. h (cost_list ! e)) cap_u"
  using ok Mpos
  by(cases a)
    (auto simp add: check_answer_dispatch_def check_optimum_dispatch_sound check_infeasible_sound
                    check_unbounded_sound)

text ‹The mode-aware counterpart of ‹verdict_of_sound›, needed by ‹decide_imp_correct›/
      ‹solve_imp_correct› on the accepted-certificate path.›

lemma verdict_of_dispatch_sound:
  assumes "check_answer_dispatch cm a" and "0 < M"
  shows "verdict_ok_dispatch cm M (verdict_of a)"
  using check_answer_dispatch_sound[OF assms] assms
  by(cases a)(auto simp add: verdict_of_def verdict_ok_dispatch_def)

text ‹∗‹The DIMACS-level bridge: eps-optimality plus cost integrality gives exact optimality.›
      Exactly what ‹verdict_ok_dispatch› in ‹CheckerEpsilontic› mode is worth once ‹cost_integer›
      is available: the raw dual-slack witness carried at ‹ε = 1/M› is fed straight to
      ‹optimality_from_eps_potentials›, no scaling needed since the witness is already in ‹ε› form.
      The two non-optimal verdicts need nothing beyond unfolding, ‹verdict_ok_dispatch› being
      identical to ‹verdict_ok› on them regardless of ‹cm›.›

lemma verdict_ok_dispatch_exact:
  assumes ok: "verdict_ok_dispatch CheckerEpsilontic M r" and Mgt: "n < M"
  shows "verdict_ok r"
proof(cases r)
  case (VOptimum f)
  have bflow: "network.isbflow (λ e. h (f ! e)) bal"
    and slack: "∃ π. ∀ e ∈ network.𝔈. network.rcap (λ e. h (f ! e)) e > 0 ⟶
                  network.𝔠 e + π (network.fstv e) - π (network.sndv e) ≥ - (1 / real M)"
    using ok VOptimum by(auto simp add: verdict_ok_dispatch_def)
  obtain π where π: "∀ e ∈ network.𝔈. network.rcap (λ e. h (f ! e)) e > 0 ⟶
                  network.𝔠 e + π (network.fstv e) - π (network.sndv e) ≥ - (1 / real M)"
    using slack by blast
  have Mpos: "0 < real M" using Mgt by simp
  have eps_pos: "0 < 1 / real M" using Mpos by simp
  have card_le: "card network.𝒱 ≤ n"
  proof -
    have "card network.𝒱 ≤ card {Suc 0..n}" by(rule card_mono) (use net_V_subset in auto)
    thus ?thesis by simp
  qed
  have n_bound: "real (card network.𝒱) * (1 / real M) < 1"
  proof -
    have "real (card network.𝒱) ≤ real n" using card_le by simp
    also have "… < real M" using Mgt by simp
    finally show ?thesis using Mpos by (simp add: field_simps)
  qed
  have cost_int: "⋀e. e ∈ network.𝔈 ⟹ network.𝔠 e ∈ ℤ"
  proof -
    fix e assume "e ∈ network.𝔈"
    then obtain d where d: "d < m" "e = F d ∨ e = B d" unfolding network.𝔈_def by auto
    show "network.𝔠 e ∈ ℤ"
      using d cost_integer[OF d(1)] by(cases "e = F d") (auto simp add: network.𝔠.simps Ints_minus)
  qed
  have opt: "network.is_Opt bal (λ e. h (f ! e))"
    by(rule network.optimality_from_eps_potentials[OF bflow eps_pos n_bound cost_int π])
  thus ?thesis using VOptimum by(simp add: verdict_ok_def)
next
  case VInfeasible thus ?thesis using ok by(simp add: verdict_ok_dispatch_def verdict_ok_def)
next
  case VUnbounded thus ?thesis using ok by(simp add: verdict_ok_dispatch_def verdict_ok_def)
qed

end

locale mcf_oracle_cleanup_spec =
  mcf_oracle_spec where capacity_list = capacity_list
  for capacity_list :: "('n :: linordered_idom) list" +
  fixes cleanup :: "'n flow_instance ⇒ 'n list ⇒ 'n solver_verdict"
begin

definition decide :: "'n oracle_answer ⇒ 'n solver_verdict" where
  "decide a = (case screen a of Some b ⇒ verdict_of b
                              | None   ⇒ cleanup orc_input (oa_flow a))"

definition solve :: "'n solver_verdict" where
  "solve = decide orc_answer"

end

text ‹The proof locale adds the one thing that has to be assumed about the cleanup: that its verdict
      is true of this instance.  Nothing else --- not that it agrees with the oracle, not that it
      uses the flow it is given, not that it terminates quickly.  The flow is a warm start, and a
      warm start is a performance argument, never a correctness one.

      ∗‹Still nothing is assumed about @{term oracle_solve}.›  It remains free to return anything of
      its type; what changes is only that a rejected answer now has somewhere to go.›

locale mcf_oracle_cleanup = mcf_oracle + mcf_oracle_cleanup_spec +
  assumes cleanup_correct: "⋀ g. verdict_ok (cleanup orc_input g)"
begin

text ‹Hence the pipeline is correct, whatever the oracle does: if its certificate holds the verdict
      is its own, by the layer below; if it does not, the verdict is the cleanup's, by assumption.
      This is the statement the arrangement exists for --- an untrusted program in the fast path, a
      verified one behind it, and a proof that the answer is right either way.  Note what the two
      layers deliver: @{const checked_verdict} is an @{type option} and may be @{term None},
      @{const solve} is a verdict and always is one.›

theorem solve_correct: "verdict_ok solve"
  using verdict_of_sound cleanup_correct
  by(auto simp add: solve_def decide_def screen_def split: if_splits)

end

end
