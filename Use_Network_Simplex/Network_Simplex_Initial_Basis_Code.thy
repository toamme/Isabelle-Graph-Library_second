theory Network_Simplex_Initial_Basis_Code
  imports Network_Simplex_Final Acyclic_Flow_Instantiation "../../../AutoCorrode/iq/iq"
          "../../Set_Graphs/Graph_Algorithms/Rooted_Arborescense"
begin

text ‹This is the single ∗‹code› theory of the initial-basis construction: it collects every executable definition (the CSR builds, Pass A, the free-edge DFS builder, the augmented-network arrays, the arborescence swap, and the whole M-free entering-edge selector) into one assumption-free specification locale ‹initial_basis_code_spec›.The four downstream theories import it and add only assumptions and proofs.›

section ‹Efficient list-backed arrays and a vertex iterator›

text ‹The acyclic-flow procedure is stated over abstract data types: two @{locale abstract_array}s
      (the flow and the three-valued vertex state) and one @{locale iterable_set} (the vertices to
      scan).  We give the cheapest faithful models, meant to be read as arrays: a flow / state array
      is a plain list, looked up with @{const nth} and written with @{const list_update} — both
      ‹O(1)› once the list is a genuine array — and the vertex iterator is the vertex list
      together with a single moving cursor, so @{term current}, @{term has} and @{term move} are a
      read, a length-compare and an increment.  The set-valued fields (@{term abstract},
      @{term iterated}, @{term remaining}) are ghosts used only in the proofs and vanish at code
      generation.›

subsection ‹A list read as a total array›

text ‹The @{locale abstract_array} operations are read off a list directly: lookup is @{const nth}
      and update is @{const list_update} (‹xs[k := v]›).  The invariant records that every allowed
      key is a valid index (‹∀k∈K. k < length xs›), which is exactly what makes the
      key-restricted update law hold.›

lemma list_abstract_array:
  "abstract_array K (λxs. ∀k∈K. k < length xs) list_update nth"
proof (unfold_locales, goal_cases)
  case (1 A k v)
  then have kl: "k < length A" by blast
  show ?case
  proof (rule ext)
    fix i
    show "(A[k := v]) ! i = (((!) A)(k := v)) i"
      using kl by (cases "i = k")
        (simp_all add: nth_list_update_eq nth_list_update_neq)
  qed
next
  case (2 A k v)
  thus ?case by simp
qed

lemma nth_fun_list_update:
  assumes "k < length A"
  shows "nth (A[k := v]) = (nth A)(k := v)"
proof (rule ext)
  fix i
  show "(A[k := v]) ! i = (((!) A)(k := v)) i"
    using assms by (cases "i = k")
      (simp_all add: nth_list_update_eq nth_list_update_neq)
qed

lemma list_abstract_array_sub:
  assumes "K ⊆ D"
  shows "abstract_array K (λxs. ∀k∈D. k < length xs) list_update nth"
proof (unfold_locales, goal_cases)
  case (1 A k v)
  then have kl: "k < length A" using assms by blast
  show ?case
  proof (rule ext)
    fix i
    show "(A[k := v]) ! i = (((!) A)(k := v)) i"
      using kl by (cases "i = k")
        (simp_all add: nth_list_update_eq nth_list_update_neq)
  qed
next
  case (2 A k v)
  thus ?case by simp
qed

text ‹A length-pinned variant: when the array's length is exactly @{term n} and the key set lies in
      @{term ‹{0..<n}›}, every key is in range and @{const list_update} preserves the length. Making
      the length part of the invariant is what lets the acyclifier's invariant carry it: the flow it
      returns is then known to have length @{term m}.›

lemma list_abstract_array_len:
  assumes "K ⊆ {0..<n}"
  shows "abstract_array K (λxs. length xs = n) list_update nth"
proof (unfold_locales, goal_cases)
  case (1 A k v)
  then have kl: "k < length A" using assms by auto
  show ?case
  proof (rule ext)
    fix i
    show "(A[k := v]) ! i = (((!) A)(k := v)) i"
      using kl by (cases "i = k")
        (simp_all add: nth_list_update_eq nth_list_update_neq)
  qed
next
  case (2 A k v)
  thus ?case by simp
qed
subsection ‹The vertex list with a cursor as an iterable set›

record 'v vtx_iter = vi_list :: "'v list"  vi_pos :: nat

definition vtx_invar :: "'v vtx_iter ⇒ bool" where
  "vtx_invar V ⟷ distinct (vi_list V) ∧ vi_pos V ≤ length (vi_list V)"
definition vtx_abstract :: "'v vtx_iter ⇒ 'v set" where
  "vtx_abstract V = set (vi_list V)"
definition vtx_iterated :: "'v vtx_iter ⇒ 'v set" where
  "vtx_iterated V = set (take (vi_pos V) (vi_list V))"
definition vtx_remaining :: "'v vtx_iter ⇒ 'v set" where
  "vtx_remaining V = set (drop (vi_pos V) (vi_list V))"
definition vtx_has :: "'v vtx_iter ⇒ bool" where
  "vtx_has V ⟷ vi_pos V < length (vi_list V)"
definition vtx_current :: "'v vtx_iter ⇒ 'v" where
  "vtx_current V = vi_list V ! vi_pos V"
definition vtx_move :: "'v vtx_iter ⇒ 'v vtx_iter" where
  "vtx_move V = V⦇ vi_pos := Suc (vi_pos V) ⦈"

lemma set_take_inter_set_drop_distinct:
  "distinct xs ⟹ set (take n xs) ∩ set (drop n xs) = {}"
  by (metis append_take_drop_id distinct_append)

lemma vtx_remaining_ne_lt:
  "vtx_remaining V ≠ {} ⟹ vi_pos V < length (vi_list V)"
  by (simp add: vtx_remaining_def)

lemma vtx_iterable_set:
  "iterable_set vtx_invar vtx_abstract vtx_current vtx_has vtx_iterated vtx_remaining vtx_move"
proof (unfold_locales, goal_cases)
  case (1 S)
  then show ?case
    by (auto simp: vtx_invar_def vtx_iterated_def vtx_remaining_def
                   set_take_inter_set_drop_distinct)
next
  case (2 S)
  show ?case
    by (metis vtx_abstract_def vtx_iterated_def vtx_remaining_def
              append_take_drop_id set_append)
next
  case (3 S)
  show ?case by (auto simp: vtx_has_def vtx_remaining_def)
next
  case (4 S)
  note lt = vtx_remaining_ne_lt[OF 4(2)]
  show ?case using lt
    by (metis Cons_nth_drop_Suc list.set_intros(1) vtx_current_def vtx_remaining_def)
next
  case (5 S)
  show ?case by (simp add: vtx_abstract_def vtx_move_def)
next
  case (6 S)
  note lt = vtx_remaining_ne_lt[OF 6(2)]
  from 6(1) have dist: "distinct (vi_list S)" by (simp add: vtx_invar_def)
  show ?case using lt dist
    by (simp add: vtx_remaining_def vtx_current_def vtx_move_def)
       (metis Cons_nth_drop_Suc distinct_drop distinct.simps(2)
              Diff_insert_absorb list.simps(15))
next
  case (7 S)
  note lt = vtx_remaining_ne_lt[OF 7(2)]
  show ?case using lt
    by (simp add: vtx_iterated_def vtx_current_def vtx_move_def take_Suc_conv_app_nth)
next
  case (8 S)
  note lt = vtx_remaining_ne_lt[OF 8(2)]
  show ?case using 8(1) lt by (simp add: vtx_invar_def vtx_move_def)
qed

section ‹Array-mimicking input lists for the initial basis›

text ‹The initial-basis construction is driven by a handful of parallel lists that stand in for the
      arrays a real implementation would be handed.  ∗‹Edges are identified by their index›: the four
      edge lists all have the same length, and the ith edge has capacity @{term ‹capacity_list ! i›},
      cost @{term ‹cost_list ! i›}, tail @{term ‹fst_list ! i›}, head @{term ‹snd_list ! i›} and
      carries flow @{term ‹flow_list ! i›} (the acyclic flow to be turned into the initial basis).  The
      number of edges is @{term m}, the common length of the edge lists, so the edges are exactly the
      indices @{term ‹{0..<m}›}.  Capacities are non-negative except that @{term ‹- 1›} encodes an
      infinite capacity: it is the only negative value a capacity may take.  The
      vertices are described by two further lists of equal length: the ith vertex has ∗‹name›
      @{term ‹vs_list ! i›} and balance @{term ‹b_list ! i›}.  Vertex names are naturals; we reserve
      @{term ‹0::nat›} as a non-name (there is no node @{term ‹0›}), which later lets us use it for
      the artificial root.  The only structural consistency we demand here is that the endpoints
      mentioned by the edge lists are exactly the vertices: the union of the tails and heads is the
      vertex-name set.›

section ‹Big-M as a tagged pair, and the DFS builder state›

text ‹Design notes §2: a potential / reduced-cost value is a pair of a ∗‹tag› — an integer
      coefficient of the symbolic big constant ‹𝑀›, drawn from ‹{-2..2}› and stored
      as a five-valued datatype — and an ordinary real ‹offset›. The abstraction sends a pair
      ‹(t, o)› to ‹of_mtag t * 𝑀 + o›; with ‹𝑀› large enough (‹> 6 · Σ|c|›, chosen in
      the locale) the tag is recoverable from the abstract value, which is what discharges the
      conditional ‹pot_value_*_spec› axioms.›

datatype mtag = M_m2 | M_m1 | M_0 | M_p1 | M_p2

primrec of_mtag :: "mtag ⇒ int" where
  "of_mtag M_m2 = - 2" | "of_mtag M_m1 = - 1" | "of_mtag M_0 = 0"
| "of_mtag M_p1 = 1"   | "of_mtag M_p2 = 2"

text ‹Reconstruct a tag from an integer coefficient, clamping anything off the range @{term ‹{- 2..2}›}
      (the clamped cases never arise for admissible values, but keep the operations total).›

definition mtag_of :: "int ⇒ mtag" where
  "mtag_of i = (if i ≤ - 2 then M_m2 else if i = - 1 then M_m1 else if i = 0 then M_0
                else if i = 1 then M_p1 else M_p2)"

definition tag_add :: "mtag ⇒ mtag ⇒ mtag" where
  "tag_add a b = mtag_of (of_mtag a + of_mtag b)"

definition tag_sub :: "mtag ⇒ mtag ⇒ mtag" where
  "tag_sub a b = mtag_of (of_mtag a - of_mtag b)"
(*
definition pval_abstract :: 
"'n ⇒ mtag × ('n::linordered_idom) ⇒ real" where
  "pval_abstract M p = real_of_int (of_mtag (fst p)) * M + snd p"
*)
definition pval_plus :: "mtag × ('n::linordered_idom) ⇒
 mtag × ('n::linordered_idom) ⇒ mtag × ('n::linordered_idom)" where
  "pval_plus a b = (tag_add (fst a) (fst b), snd a + snd b)"

definition pval_minus :: "mtag × ('n::linordered_idom)
 ⇒ mtag × ('n::linordered_idom) ⇒ mtag × ('n::linordered_idom)" where
  "pval_minus a b = (tag_sub (fst a) (fst b), snd a - snd b)"

definition pval_zero :: "mtag × ('n::linordered_idom)" where "pval_zero = (M_0, 0)"
definition pval_M    ::  "mtag × ('n::linordered_idom)" where "pval_M    = (M_p1, 0)"
definition pval_negM ::  "mtag × ('n::linordered_idom)" where "pval_negM = (M_m1, 0)"

subsection ‹A dedicated potential-shift iterator over the thread›

text ‹The potential shift is realised by its ∗‹own› tail-recursive walk down the thread block of the
      pivot vertex, mirroring the imperative @{term shift_pot_imp}: at each visited node the potential
      is read, shifted by @{term g} and written back — a single fused read/arith/write, with no
      higher-order per-node callback.  The walk stops once the last successor @{const lsuc} of the
      start node has been processed (that node is the rightmost leaf of the subtree in thread order).

      To keep the ∗‹inner› loop branch-free, the @{term up} flag is tested ∗‹once›, up front: there are
      two separate loops, one that always adds (‹shift_pot_up_loop›) and one that always subtracts
      (‹shift_pot_down_loop›); ‹shift_pot_impl› picks the loop and never re-checks the flag while
      iterating.  These are fresh implementations, not the generic
      @{const iterate_root_opposed_impl}; each is proved equivalent to a @{const subtree_fold} below,
      which is all the correctness argument needs.›

partial_function (tailrec) shift_pot_up_loop ::
  "nat ndtree ⇒ nat ⇒ mtag × ('n::linordered_idom) ⇒ nat ⇒ (mtag × 'n) list ⇒ (mtag × 'n) list"
  where
  "shift_pot_up_loop S stop g u pa =
     (let pa' = pa[u := pval_plus (pa ! u) g]
      in (if u = stop then pa' else shift_pot_up_loop S stop g (the (thrd S u)) pa'))"

partial_function (tailrec) shift_pot_down_loop ::
  "nat ndtree ⇒ nat ⇒ mtag × ('n::linordered_idom) ⇒ nat ⇒ (mtag × 'n) list ⇒ (mtag × 'n) list"
  where
  "shift_pot_down_loop S stop g u pa =
     (let pa' = pa[u := pval_minus (pa ! u) g]
      in (if u = stop then pa' else shift_pot_down_loop S stop g (the (thrd S u)) pa'))"

definition shift_pot_impl ::
  "nat ndtree ⇒ nat ⇒ (mtag × ('n::linordered_idom)) list ⇒ mtag × 'n ⇒ bool ⇒ (mtag × 'n) list"
  where
  "shift_pot_impl S v pa g up =
     (if up then shift_pot_up_loop   S (lsuc S v) g v pa
            else shift_pot_down_loop S (lsuc S v) g v pa)"

text ‹Each branch-free walk agrees with a @{const subtree_fold} over the same thread block whose
      per-node step is its read/shift/write.  Proved by induction on the block prefix, unfolding both
      tail-recursions in lockstep — exactly the shape of @{thm [source] subtree_fold_follow}.›
lemma shift_pot_up_loop_subtree_fold:
  assumes ps: "parent_spec (thrd S)"
      and L: "follow (thrd S) u = bl @ stp # rest"
      and notin: "stp ∉ set bl"
  shows "shift_pot_up_loop S stp g u pa
          = subtree_fold S stp u (λx acc. acc[x := pval_plus (acc ! x) g]) pa"
  using L notin
proof (induct bl arbitrary: u pa)
  case Nil
  have "hd (follow (thrd S) u) = u" by (rule follow_hd_ps[OF ps])
  hence ustp: "u = stp" using Nil.prems(1) by simp
  show ?case
    by (subst shift_pot_up_loop.simps, subst subtree_fold.simps) (simp add: Let_def ustp)
next
  case (Cons b bs)
  have hd: "u = b" using follow_hd_ps[OF ps, of u] Cons.prems(1) by simp
  have une: "u ≠ stp" using Cons.prems(2) hd by auto
  have flu: "follow (thrd S) u = u # (bs @ stp # rest)" using Cons.prems(1) hd by simp
  have tw_ne: "thrd S u ≠ None"
  proof
    assume "thrd S u = None"
    hence "follow (thrd S) u = [u]" by (subst follow_ps_simps[OF ps]) simp
    thus False using flu by simp
  qed
  then obtain w where tw: "thrd S u = Some w" by auto
  have fw: "follow (thrd S) w = bs @ stp # rest"
    using flu tw follow_ps_simps[OF ps, of u] by simp
  have notin': "stp ∉ set bs" using Cons.prems(2) by simp
  let ?F = "λx acc. acc[x := pval_plus (acc ! x) g]"
  have lhs: "shift_pot_up_loop S stp g u pa = shift_pot_up_loop S stp g w (?F u pa)"
    using une tw by (subst shift_pot_up_loop.simps) (simp add: Let_def)
  have rhs: "subtree_fold S stp u ?F pa = subtree_fold S stp w ?F (?F u pa)"
    using une tw by (subst subtree_fold.simps) (simp add: Let_def)
  show ?case using lhs rhs Cons.hyps[OF fw notin', of "?F u pa"] by simp
qed

lemma shift_pot_down_loop_subtree_fold:
  assumes ps: "parent_spec (thrd S)"
      and L: "follow (thrd S) u = bl @ stp # rest"
      and notin: "stp ∉ set bl"
  shows "shift_pot_down_loop S stp g u pa
          = subtree_fold S stp u (λx acc. acc[x := pval_minus (acc ! x) g]) pa"
  using L notin
proof (induct bl arbitrary: u pa)
  case Nil
  have "hd (follow (thrd S) u) = u" by (rule follow_hd_ps[OF ps])
  hence ustp: "u = stp" using Nil.prems(1) by simp
  show ?case
    by (subst shift_pot_down_loop.simps, subst subtree_fold.simps) (simp add: Let_def ustp)
next
  case (Cons b bs)
  have hd: "u = b" using follow_hd_ps[OF ps, of u] Cons.prems(1) by simp
  have une: "u ≠ stp" using Cons.prems(2) hd by auto
  have flu: "follow (thrd S) u = u # (bs @ stp # rest)" using Cons.prems(1) hd by simp
  have tw_ne: "thrd S u ≠ None"
  proof
    assume "thrd S u = None"
    hence "follow (thrd S) u = [u]" by (subst follow_ps_simps[OF ps]) simp
    thus False using flu by simp
  qed
  then obtain w where tw: "thrd S u = Some w" by auto
  have fw: "follow (thrd S) w = bs @ stp # rest"
    using flu tw follow_ps_simps[OF ps, of u] by simp
  have notin': "stp ∉ set bs" using Cons.prems(2) by simp
  let ?F = "λx acc. acc[x := pval_minus (acc ! x) g]"
  have lhs: "shift_pot_down_loop S stp g u pa = shift_pot_down_loop S stp g w (?F u pa)"
    using une tw by (subst shift_pot_down_loop.simps) (simp add: Let_def)
  have rhs: "subtree_fold S stp u ?F pa = subtree_fold S stp w ?F (?F u pa)"
    using une tw by (subst subtree_fold.simps) (simp add: Let_def)
  show ?case using lhs rhs Cons.hyps[OF fw notin', of "?F u pa"] by simp
qed

text ‹The mutable state carried by the free-edge DFS builder (design notes §4/§6.1). Every field is
      an array read with @{const nth} and written with @{const list_update}; the option-valued pointer
      maps @{term prnt}/@{term thrd}/@{term rvth} use @{term ‹0::nat›} as the null sentinel (there is
      no node ‹0›). The stack @{term ds_stk} makes the recursion explicit — one frame
      @{term ‹(v, oc, ic)›} per active vertex, holding the two cursors into @{term v}'s free outgoing
      and ingoing CSR blocks — so the later array refinement has exactly the same (while-loop) shape.›

record 'n dfs_state =
  ds_seen :: "bool list"                   ― ‹visited flag (= in tree)›
  ds_prnt :: "nat list"                    ― ‹ndtree parent vertex (0 = none)›
  ds_par  :: "nat list"                    ― ‹parent edge id›
  ds_dir  :: "bool list"                   ― ‹orientation: True ⇒ edge points v → parent (up)›
  ds_pot  :: "(mtag × ('n::linordered_idom)) list"                   ― ‹potential›
  ds_thrd :: "nat list"                    ― ‹thread successor (0 = none)›
  ds_rvth :: "nat list"                    ― ‹thread predecessor (0 = none)›
  ds_lsuc :: "nat list"                    ― ‹last successor (rightmost descendant in thread)›
  ds_snum :: "nat list"                    ― ‹subtree size›
  ds_prev :: "nat"                         ― ‹last vertex emitted in preorder›
  ds_stk  :: "(nat × nat × nat) list"      ― ‹DFS stack of ‹(vertex, out-cursor, in-cursor)››
  ds_afst :: "nat list"                    ― ‹artificial-edge tails (fst / snd / capacity / flow / tag),
                                                each pre-sized to the ‹K ≤ length vs_list› bound and
                                                filled at cursor @{term ds_nxt} — an array push, no growth›
  ds_asnd :: "nat list"
  ds_acap :: "'n list"
  ds_aflw :: "'n list"
  ds_aest :: "edge_tag list"
  ds_nxt  :: "nat"                         ― ‹next artificial-edge offset; its id is ‹m + ds_nxt››

subsection ‹The selector record and the assumed tuning parameters›

text ‹The candidate shortlist is modelled as a ∗‹fixed-capacity array with a length pointer›, to
      mirror the eventual imperative store exactly: @{term sel_arr} is a backing list of constant
      length (the capacity @{term max_candidates}), @{term sel_len} is the live-prefix pointer, and
      the meaningful candidates are the first @{term sel_len} entries of @{term sel_arr} — the array
      ∗‹up to the pointer›.
      Everything past the pointer is stale.  Insertion writes at the pointer and bumps it; deletion is
      swap-with-last; both are @{const list_update} plus pointer arithmetic, so the backing list never
      changes length and no array is ever allocated after initialisation.›

record ns_sel =
  sel_cur :: nat             ― ‹block-search bookmark into the augmented arc set›
  sel_arr :: "nat list"      ― ‹fixed-capacity backing array of candidate edge ids›
  sel_len :: nat             ― ‹live-prefix pointer: candidates are the first @{term sel_len} of @{term sel_arr}›

subsection ‹M-free sign and violation tests on descriptors›

text ‹The executable path must never evaluate the symbolic constant @{term bigM}: doing so would
      reintroduce exactly the floating-point cancellation the tagged-pair descriptor exists to avoid.
      These three tests work purely on the descriptor  — the integer big-M coefficient
      @{term ‹of_mtag (fst p)›} and the ordinary part @{term ‹snd p›} — and mention no @{term M} at
      all.  ‹pval_neg› / ‹pval_pos› give the sign, and ‹viol_gt› compares
      violation magnitude (bigger coefficient first, then bigger ordinary part).  Their agreement with
      the abstraction @{term ‹pval_abstract bigM›} is a ∗‹proof-time› fact (see
      @{text pval_neg_abstract} / @{text pval_pos_abstract}), needing only the reduced-cost bound; that
      is the sole place the actual size of @{term bigM} ever matters.›

definition pval_neg :: "mtag × ('n::linordered_idom) ⇒ bool" where
  "pval_neg p ⟷ of_mtag (fst p) < 0 ∨ (of_mtag (fst p) = 0 ∧ snd p < 0)"

definition pval_pos :: "mtag × ('n::linordered_idom) ⇒ bool" where
  "pval_pos p ⟷ 0 < of_mtag (fst p) ∨ (of_mtag (fst p) = 0 ∧ 0 < snd p)"

definition viol_gt :: "mtag × ('n::linordered_idom)
 ⇒ mtag × ('n::linordered_idom) ⇒ bool" where
  "viol_gt g1 g2 ⟷
     ¦of_mtag (fst g1)¦ > ¦of_mtag (fst g2)¦
     ∨ (¦of_mtag (fst g1)¦ = ¦of_mtag (fst g2)¦ ∧ ¦snd g1¦ > ¦snd g2¦)"

text ‹The running best is carried ∗‹without an option› through the loops, as a flat
      : a ∗‹found› flag followed by the edge, its @{term in_U} flag,
      and its reduced-cost descriptor.  This is what lets ‹scan_cache› / ‹scan› thread the
      accumulator as four plain loop variables — no @{term Some} is allocated per update — the option
      surviving only at the once-per-pivot boundary of the selector, as the ADT demands.
      The sentinel ‹no_best› (∗‹found› = @{term False}) starts each scan; its edge fields are
      dummies never read while the flag is unset.›

type_synonym 'n best_cand = "bool × nat × bool × mtag × 'n"

definition no_best :: "('n::linordered_idom) best_cand" where
  "no_best = (False, 0, False, pval_zero)"

text ‹The three possible verdicts of the whole min-cost-flow solve.
      ▪ @{term ‹Optimum f›} — a minimum-cost @{term b}-flow on the ∗‹original› edges, extracted
        from the augmented optimum after every artificial edge has been driven to zero.
      ▪ @{term Infeasible} — the augmented network is optimal but still routes flow on an
        artificial edge, witnessing that no @{term b}-flow of the original network exists.
      ▪ @{term Neg_inf_cycle} — a negative infinite-capacity cycle was found (by the acyclifier
        or by the loop), so the instance is unbounded (or, with the artificial edges, infeasible);
        in either case the original problem is malformed.›

datatype 'n ns_outcome =
    Optimum "'n list"
  | Infeasible
  | Neg_inf_cycle


locale initial_basis_code_spec =
  fixes capacity_list :: "('n::linordered_idom) list"
    and cost_list     :: "'n list"
    and fst_list      :: "nat list"
    and snd_list      :: "nat list"
    and flow_list     :: "'n list"
    and m             :: "nat"
    and n             :: "nat"
    and b_list        :: "'n list"
   (* and h             :: "'n \<Rightarrow> real"*)
    and block_size     :: nat
    and min_candidates :: nat
    and max_candidates :: nat
begin

text ‹The vertices are the dense range @{term ‹{Suc 0..n}›}: every name between @{term ‹1::nat›} and
      @{term n} is a vertex, @{term ‹0::nat›} is reserved as the null sentinel, and @{term ‹Suc n›}
      (‹vcount›) is the artificial root added by the initial basis.  @{term vs_list} is no
      longer an input; it is this range, materialised once.  Vertices that carry no edge are allowed
      (their balance is assumed @{term 0} in the proof locale); the lonely-vertex guard keeps them out
      of the spanning tree.›

definition vs_list :: "nat list" where "vs_list = [Suc 0..<Suc n]"

lemma set_vs_list: "set vs_list = {Suc 0..n}"
  by (simp only: vs_list_def set_upt atLeastLessThanSuc_atLeastAtMost)
lemma length_vs_list: "length vs_list = n" by (simp add: vs_list_def)
lemma distinct_vs_list_code: "distinct vs_list" by (simp add: vs_list_def)
lemma zero_notin_vs_list: "0 ∉ set vs_list" by (simp add: vs_list_def)

text ‹The lists are read as a cost-flow specification (assumption-free): the same instantiation as the network reading in the proof locale, but only the executable structure is fixed and no multigraph axiom is discharged, so the vertex set and the edge data become available for the definitions below.›
(*
sublocale original_network: cost_flow_spec
  where ℰ           = "{0..<m}"
    and fst          = "λ e. if e < m then fst_list ! e else Product_Type.fst (prod_decode (e - m))"
    and snd          = "λ e. if e < m then snd_list ! e else Product_Type.snd (prod_decode (e - m))"
    and create_edge  = "λ u v. m + prod_encode (u, v)"
    and 𝗎           = "λ e. if e < m then (if capacity_list ! e = - 1 then ∞ else ereal (h (capacity_list ! e))) else ∞"
    and 𝖼           = "λ e. h (cost_list ! e)"
  by unfold_locales
*)

text ‹@{term vcount} is one past the largest vertex name — the common length of every vertex-indexed
      array. The vertex-max is a ∗‹left› fold: ‹fold› is tail-recursive, where the ‹foldr› it replaces
      would build a call chain as deep as @{term vs_list}. The two agree because @{term max} is
      left-commutative (‹fold_max_foldr›), so ‹vcount_foldr› below still presents the ‹foldr› view to
      the proofs. The max is computed in this one place and reused by the balance array ‹b_arr› and
      the CSR builds.›

lemma fold_max_foldr: "fold max (xs :: nat list) a = foldr max xs a"
proof -
  have "foldr max xs = fold max xs"
    by (rule foldr_fold) (simp add: fun_eq_iff max.left_commute)
  thus ?thesis by simp
qed

definition vcount :: nat where
  "vcount = Suc (fold max vs_list 0)"

lemma vcount_eq: "vcount = Suc n"
proof -
  have s: "set (0 # vs_list) = {0..n}" using set_vs_list by auto
  have m: "Max {0..n} = n" by (rule Max_eqI) auto
  have "fold max vs_list 0 = Max (set (0 # vs_list))" by (rule Max.set_eq_fold[symmetric])
  also have "… = n" using s m by simp
  finally show ?thesis by (simp add: vcount_def)
qed

lemma vcount_foldr: "vcount = Suc (foldr max vs_list 0)"
  by (simp add: vcount_def fold_max_foldr)

text ‹A list used as an array to fetch a balance by the ∗‹name› of a vertex.  We start from an
      all-zero array of length ‹Suc vcount› and scatter each pair
      @{term ‹(vs_list ! i, b_list ! i)›} into it.  Position @{term v} then holds the balance of the
      vertex named @{term v} (slot @{term ‹0::nat›} stays a dummy, as there is no node @{term ‹0›}).

      The array is one longer than the vertex names it stores.  The extra slot is the artificial root
      @{term vcount}, which the augmented network of the initial basis adds and which the scatter
      never touches, since every name in @{term vs_list} is smaller than @{term vcount}.  So its
      balance reads back as @{term ‹0::real›}, which is the value the root must have: the balances
      sum to zero (‹balance_sum_zero›), hence so do the imbalances, and the artificial
      edges carry as much flow into the root as out of it.  With the shorter array the read would run
      off the end and the root's balance would be unspecified, leaving the augmented ‹b›-flow
      obligation unprovable.›

definition b_arr :: "'n list" where
  "b_arr = foldl (λ arr (v, x). arr[v := x])
                 (replicate (Suc vcount) 0)
                 (zip vs_list b_list)"

definition b_lookup :: "nat ⇒ 'n" where
  "b_lookup v = b_arr ! v"

subsection ‹The graph as two counting-sort CSRs and the acyclic-flow procedure›

text ‹Both adjacency structures are the cache-friendly two-pass counting-sort CSR
      @{const build_csr_scatter}: the outgoing one keys each edge on its tail @{term ‹fst_list ! e›},
      the ingoing one on its head @{term ‹snd_list ! e›}.  The blocks are indexed by vertex ∗‹name›,
      so the array of blocks is sized to @{term vcount}, one past the largest name (exactly as
      @{const b_arr}); names that are not vertices index empty blocks.  Building each CSR is two
      passes over the @{term m} edges plus one scan of the @{term vcount} blocks, and every scanning
      operation the algorithm then performs is ‹O(1)›.›

text ‹The two graph CSRs are built ∗‹once› and ∗‹in parallel›: a single fused pass counts both the
      out-degrees (by tail) and in-degrees (by head), and a single fused scatter places each edge into
      both CSRs — two edge sweeps for both structures, not four. The generic ‹build_two_csr› projects
      onto the two independent ‹build_csr_scatter› builds (lemmas ‹build_two_csr_fst› / ‹build_two_csr_snd›
      below), so every existing CSR fact transfers unchanged. The acyclic-flow instance uses the two
      CSRs as its edge iterators, and the initial-basis construction reuses their block starts and
      overwrites their edge arrays in place with the free edges (§4, no rebuild, no new allocation).›

definition build_two_csr ::
  "nat ⇒ ('e ⇒ nat) ⇒ ('e ⇒ nat) ⇒ 'e list ⇒ 'e ⇒ ('e edge_csr × 'e edge_csr)" where
  "build_two_csr nn k1 k2 es dflt =
     (let cc = fold (λe (c1,c2). (c1[k1 e := Suc (c1 ! k1 e)], c2[k2 e := Suc (c2 ! k2 e)]))
                    es (replicate nn 0, replicate nn 0);
          p1 = psums 0 (fst cc); lo1 = butlast p1;
          p2 = psums 0 (snd cc); lo2 = butlast p2;
          AB = fold (λe (A,B). (scatter_body k1 e A, scatter_body k2 e B)) es
                    ((replicate (length es) dflt, lo1), (replicate (length es) dflt, lo2))
      in (edge_csr.make (fst (fst AB)) lo1 (tl p1) lo1,
          edge_csr.make (fst (snd AB)) lo2 (tl p2) lo2))"

definition two_csr :: "nat edge_csr × nat edge_csr" where
  "two_csr = build_two_csr vcount (nth fst_list) (nth snd_list) [0..<m] 0"

definition out_csr :: "nat edge_csr" where "out_csr = fst two_csr"
definition in_csr :: "nat edge_csr" where "in_csr = snd two_csr"

section ‹Initial-basis construction: the strongly-feasible spanning tree›

subsection ‹Pass A: one fused sweep — status, excess, and the free-edge CSRs›

text ‹Realising the notes' single pass: one fold over the edges records, per edge, its status
      (‹edge_state›), accumulates the excess (‹excess›), and — for a ∗‹free› (tree) edge — overwrites
      it into the two adjacency CSRs in place. We reuse the block starts of the already-built
      outgoing/ingoing CSRs (‹out_lo› / ‹in_lo›); the cursors run from those starts, so each vertex's
      free edges occupy the front of its old block, the tail becoming unused ∗‹holes›. No list is
      materialised beyond the ones the notes name.›

definition out_lo :: "nat list" where
  "out_lo = csr_lo out_csr"

definition in_lo :: "nat list" where
  "in_lo = csr_lo in_csr"

text ‹Block ∗‹ends› of the full outgoing/ingoing CSRs. A vertex whose block is empty in ∗‹both›
      structures (@{term ‹out_lo ! v = out_hi ! v ∧ in_lo ! v = in_hi ! v›}) is an endpoint of no
      edge — a ∗‹lonely› vertex. The test is two O(1) reads, so it introduces no extra sweep.›

definition out_hi :: "nat list" where
  "out_hi = csr_hi out_csr"

definition in_hi :: "nat list" where
  "in_hi = csr_hi in_csr"

definition is_lonely :: "nat ⇒ bool" where
  "is_lonely v ⟷ out_lo ! v = out_hi ! v ∧ in_lo ! v = in_hi ! v"

text ‹The edged vertices: the dense range with the edge-less (lonely) names removed.  This is the
      vertex set actually fed to the acyclifier, so its abstraction stays exactly the graph vertex
      set @{term ‹set fst_list ∪ set snd_list›}, and the lonely names — whose balance the proof
      locale assumes @{term 0} — are skipped there just as the lonely guard skips them in the
      spanning tree.›

definition edged_vs_list :: "nat list" where
  "edged_vs_list = filter (λv. ¬ is_lonely v) vs_list"

text ‹The fused step for edge @{term e}. The state is the six arrays being built: the status list,
      the excess, and the outgoing/ingoing free-CSR edge arrays with their cursors. A self-loop
      cancels in the excess (the head update is read back by the tail update).›

definition passA_step ::
  "'n list ⇒ nat ⇒ edge_tag list × 'n list × nat list × nat list × nat list × nat list
       ⇒ edge_tag list × 'n list × nat list × nat list × nat list × nat list" where
  "passA_step fl e = (λ(est, exc, oe, oc, ie, ic).
     let x = fst_list ! e; y = snd_list ! e; f = fl ! e; u = capacity_list ! e;
         st = (if f = 0 then InL else if u ≠ - 1 ∧ f = u then InU else InTree);
         exc' = (let a = exc[y := exc ! y + f] in a[x := a ! x - f])
     in if st = InTree
        then (est[e := st], exc', oe[oc ! x := e], oc[x := oc ! x + 1],
              ie[ic ! y := e], ic[y := ic ! y + 1])
        else (est[e := st], exc', oe, oc, ie, ic))"

definition passA ::
  "'n list ⇒ edge_tag list × 'n list × nat list × nat list × nat list × nat list" where
  "passA fl = fold (passA_step fl) [0..<m]
     (replicate m InL, replicate (Suc vcount) (0::'n), csr_edges out_csr, out_lo,
      csr_edges in_csr, in_lo)"

definition edge_state :: "'n list ⇒ edge_tag list" where
  "edge_state fl = (let (est, _, _, _, _, _) = passA fl in est)"

definition excess :: "'n list" where
  "excess = (let (_, exc, _, _, _, _) = passA flow_list in exc)"

definition free_out_edges :: "'n list ⇒ nat list" where
  "free_out_edges fl = (let (_, _, oe, _, _, _) = passA fl in oe)"

definition free_out_hi :: "'n list ⇒ nat list" where
  "free_out_hi fl = (let (_, _, _, oc, _, _) = passA fl in oc)"

definition free_in_edges :: "'n list ⇒ nat list" where
  "free_in_edges fl = (let (_, _, _, _, ie, _) = passA fl in ie)"

definition free_in_hi :: "'n list ⇒ nat list" where
  "free_in_hi fl = (let (_, _, _, _, _, ic) = passA fl in ic)"

subsection ‹Derived views: status and imbalance›

text ‹Vertex v's free incident edges are the CSR block: entries of ∗‹free_out_edges› from index
      ∗‹out_lo!v› up to ∗‹free_out_hi!v› (outgoing), and of ∗‹free_in_edges› from ∗‹in_lo!v› up to
      ∗‹free_in_hi!v› (ingoing) — a constant-time index range, no rescan. The DFS scans these ranges
      ∗‹by index›, so no per-vertex edge list is materialised (over all vertices they cover each free
      edge once).›

text ‹The imbalance @{term ‹imbalance ! v›} = achieved − target balance = the signed amount @{term v}'s
      artificial edge must ship toward the root (surplus positive); the root carries none. It is the
      @{const excess} array transformed ∗‹in place› (@{const excess} is spent here) — no new array.›

definition imbalance :: "'n list" where
  "imbalance = fold (λv arr. arr[v := arr ! v + b_lookup v]) [0..<vcount] excess"

subsection ‹Artificial-edge orientation and the augmented endpoints›

text ‹Each vertex @{term v} owns at most one artificial edge. It is oriented ‹v → root› (up) iff
      @{term v} is a surplus/balanced vertex, else ‹root → v› (down); it carries
      @{term ‹¦imbalance ! v¦›}. A ∗‹tree› artificial edge gets a slack ‹+ 1› toward the root when it
      points up (strong feasibility); a down one is saturated but legal (‹f > 0›). The three functions
      below are the ∗‹build-time formulas›: Phases 1 and 2 evaluate them once per artificial edge to
      fill the artificial tail of the unified augmented edge arrays (design notes §1/§5).›

definition art_dir :: "nat ⇒ bool" where
  "art_dir v ⟷ 0 ≤ imbalance ! v"

definition art_flow :: "nat ⇒ 'n" where
  "art_flow v = ¦imbalance ! v¦"

definition art_tree_cap :: "nat ⇒ 'n" where
  "art_tree_cap v = (if art_dir v then art_flow v + 1 else art_flow v)"

text ‹The augmented network's endpoints, capacity and flow are ∗‹single› length-‹m + K› arrays — the
      real part followed by the artificial tail the phases append — so the simplex loop reads
      ‹fst_all ! e›, ‹cap_all ! e› etc.\ with no ‹e < m› comparison on the executable path. These
      arrays are defined once the phase construction is in place; the earlier per-edge endpoint
      functions ‹fst_aug› / ‹snd_aug› (which branched on ‹e < m›) are therefore dropped.›

subsection ‹The free-edge DFS builder›

text ‹Design notes §4/§6.1. A single depth-first traversal of the free-edge CSRs (built by Pass A)
      grows the rooted arborescence toward @{term vcount}. The traversal is a genuine recursive
      function stepping an explicit stack — the same shape the later array refinement will have — with
      one frame @{term ‹(v, oc, ic)›} per active vertex, holding cursors into @{term v}'s free
      outgoing block ‹[out_lo ! v ..< free_out_hi ! v)› and free ingoing block
      ‹[in_lo ! v ..< free_in_hi ! v)›.›

text ‹The initial builder state: nothing visited, the root @{term vcount} seeded (its subtree size
      starts at ‹1› and the thread predecessor of the first emitted vertex will be the root).›

definition dfs_init :: "'n dfs_state" where
  "dfs_init =
     ⦇ ds_seen = replicate (Suc vcount) False,
       ds_prnt = replicate (Suc vcount) 0,
       ds_par  = replicate (Suc vcount) 0,
       ds_dir  = replicate (Suc vcount) False,
       ds_pot  = replicate (Suc vcount) pval_zero,
       ds_thrd = replicate (Suc vcount) 0,
       ds_rvth = replicate (Suc vcount) 0,
       ds_lsuc = replicate (Suc vcount) 0,
       ds_snum = (replicate (Suc vcount) 0)[vcount := 1],
       ds_prev = vcount,
       ds_stk  = [],
       ds_afst = replicate (length vs_list) 0, ds_asnd = replicate (length vs_list) 0,
       ds_acap = replicate (length vs_list) 0, ds_aflw = replicate (length vs_list) 0,
       ds_aest = replicate (length vs_list) InL,
       ds_nxt  = 0 ⦈"

text ‹Discovering a fresh vertex @{term w} from stack-top @{term v} across the free real edge
      @{term e}: finalise @{term w}'s tree fields, link it into the thread after the last emitted
      vertex @{term ‹ds_prev s›}, seed its potential to give @{term e} zero reduced cost
      (‹± cost_list ! e› by whether @{term v} is @{term e}'s tail), and push @{term w}'s
      frame. The orientation flag is ‹True› iff @{term e} points ‹w → v› (up toward the
      parent).›

definition dfs_discover :: "'n dfs_state ⇒ nat ⇒ nat ⇒ nat ⇒ 'n dfs_state" where
  "dfs_discover s v w e =
     (let sgn = (if v = fst_list ! e then (cost_list ! e) else - (cost_list ! e));
          pw  = pval_plus (ds_pot s ! v) (M_0, sgn);
          pv  = ds_prev s
      in s⦇ ds_seen := (ds_seen s)[w := True],
            ds_prnt := (ds_prnt s)[w := v],
            ds_par  := (ds_par s)[w := e],
            ds_dir  := (ds_dir s)[w := (fst_list ! e = w)],
            ds_pot  := (ds_pot s)[w := pw],
            ds_thrd := (ds_thrd s)[pv := w],
            ds_rvth := (ds_rvth s)[w := pv],
            ds_snum := (ds_snum s)[w := 1],
            ds_prev := w,
            ds_stk  := (w, out_lo ! w, in_lo ! w) # ds_stk s ⦈)"

text ‹Finishing (post-order) stack-top @{term v}: the last vertex emitted so far is the rightmost
      descendant of @{term v}'s subtree, so it is @{term v}'s ‹lsuc›; add @{term v}'s completed
      subtree size to its parent's running count and pop the frame.›

definition dfs_finish :: "'n dfs_state ⇒ nat ⇒ (nat × nat × nat) list ⇒ 'n dfs_state" where
  "dfs_finish s v rest =
     (let p = ds_prnt s ! v
      in s⦇ ds_lsuc := (ds_lsuc s)[v := ds_prev s],
            ds_snum := (ds_snum s)[p := ds_snum s ! p + ds_snum s ! v],
            ds_stk  := rest ⦈)"

text ‹The traversal itself: at the stack top scan the free outgoing block, then the free ingoing
      block, recursing into each unseen neighbour; when both are exhausted, finish the vertex.
      Termination (each real recursion either marks a fresh vertex or advances a cursor) is deferred to
      a separate measure lemma, as for ‹AF_DFS›.›

text ‹The recursion takes the four Pass-A arrays it scans — the free outgoing / ingoing edge arrays
      @{term oe} / @{term ie} and their block ends @{term oh} / @{term ih} — rather than the flow.
      This is what keeps the traversal linear.  Each of ‹free_out_edges› / ‹free_out_hi› /
      ‹free_in_edges› / ‹free_in_hi› re-runs the ∗‹whole› of @{const passA}, a fold over all @{term m}
      edges, and then keeps one of its six results; so a flow-indexed recursion would redo Pass A at
      every single DFS step, one to four times over.  Taking the arrays as arguments — they are fixed
      for the entire traversal — runs @{const passA} once, in ‹build_dfs› just below, and
      shares it across the whole descent.›

function (domintros) build_dfs_a ::
  "nat list ⇒ nat list ⇒ nat list ⇒ nat list ⇒ 'n dfs_state ⇒ 'n dfs_state" where
  "build_dfs_a oe oh ie ih s =
     (case ds_stk s of
        [] ⇒ s
      | (v, oc, ic) # rest ⇒
         if oc < oh ! v then
           (let e = oe ! oc; w = snd_list ! e;
                s1 = s⦇ ds_stk := (v, Suc oc, ic) # rest ⦈
            in build_dfs_a oe oh ie ih (if ds_seen s ! w then s1 else dfs_discover s1 v w e))
         else if ic < ih ! v then
           (let e = ie ! ic; w = fst_list ! e;
                s1 = s⦇ ds_stk := (v, oc, Suc ic) # rest ⦈
            in build_dfs_a oe oh ie ih (if ds_seen s ! w then s1 else dfs_discover s1 v w e))
         else
           build_dfs_a oe oh ie ih (dfs_finish s v rest))"
  by pat_completeness auto

text ‹The flow-indexed traversal: ∗‹one› @{const passA}, its four scanned arrays handed to the
      recursion. The domain predicate and the unfolding / induction rules of the original
      flow-indexed recursion are recovered by ‹build_dfs_dom›, ‹build_dfs_unfold› and the ‹bd_›
      wrappers, so the correctness development is unchanged.›

definition build_dfs :: "'n list ⇒ 'n dfs_state ⇒ 'n dfs_state" where
  "build_dfs fl s = (let (est, exc, oe, oh, ie, ih) = passA fl in build_dfs_a oe oh ie ih s)"

definition build_dfs_dom :: "'n list × 'n dfs_state ⇒ bool" where
  "build_dfs_dom p ⟷ build_dfs_a_dom (free_out_edges (fst p), free_out_hi (fst p),
                                       free_in_edges (fst p), free_in_hi (fst p), snd p)"

lemma build_dfs_unfold:
  "build_dfs fl s = build_dfs_a (free_out_edges fl) (free_out_hi fl) (free_in_edges fl) (free_in_hi fl) s"
  by (simp add: build_dfs_def free_out_edges_def free_out_hi_def free_in_edges_def free_in_hi_def
           split: prod.splits)

lemma build_dfs_dom_iff:
  "build_dfs_dom (fl, s) ⟷
     build_dfs_a_dom (free_out_edges fl, free_out_hi fl, free_in_edges fl, free_in_hi fl, s)"
  by (simp add: build_dfs_dom_def)

text ‹The original flow-indexed unfolding rule, recovered from the array-indexed recursion. This is
      verbatim the equation @{const build_dfs} used to be defined by, so the correctness development
      reasons about the traversal exactly as before — only the evaluation shares Pass A.›

lemma build_dfs_psimps:
  assumes "build_dfs_dom (fl, s)"
  shows "build_dfs fl s = (case ds_stk s of [] ⇒ s | (v, oc, ic) # rest ⇒ if oc < free_out_hi fl ! v then (let e = free_out_edges fl ! oc; w = snd_list ! e; s1 = s⦇ds_stk := (v, Suc oc, ic) # rest⦈ in build_dfs fl (if ds_seen s ! w then s1 else dfs_discover s1 v w e)) else if ic < free_in_hi fl ! v then (let e = free_in_edges fl ! ic; w = fst_list ! e; s1 = s⦇ds_stk := (v, oc, Suc ic) # rest⦈ in build_dfs fl (if ds_seen s ! w then s1 else dfs_discover s1 v w e)) else build_dfs fl (dfs_finish s v rest))"
  using assms unfolding build_dfs_unfold build_dfs_dom_iff by (rule build_dfs_a.psimps)
text ‹Opening a tree component at an unseen vertex @{term c}: emit @{term c}'s ∗‹tree› artificial edge
      (write its endpoints / capacity / flow into the pre-sized artificial tails at cursor
      @{term ‹ds_nxt s›}, tag @{const InTree}),
      finalise @{term c} as a child of the root @{term vcount}, seed its potential to ‹± 𝑀›
      (a down edge ‹r → c› gives ‹+ 𝑀›, an up edge ‹- 𝑀›), thread-link it, then drain its
      subtree by @{const build_dfs}. Orientation / flow / capacity are computed inline from a
      ∗‹single› @{term ‹imbalance ! c›} read (the build-time formulas @{const art_dir} /
      @{const art_flow} / @{const art_tree_cap}, unfolded to avoid re-reading @{const imbalance}).›

definition open_tree_component :: "'n list ⇒ 'n dfs_state ⇒ nat ⇒ 'n dfs_state" where
  "open_tree_component fl s c =
     (let imb = imbalance ! c; up = 0 ≤ imb; af = ¦imb¦; cp = (if up then af + 1 else af);
          pv = ds_prev s
      in build_dfs fl
           (s⦇ ds_afst := (ds_afst s)[ds_nxt s := (if up then c else vcount)],
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
               ds_stk  := [(c, out_lo ! c, in_lo ! c)] ⦈))"

text ‹Emitting a ∗‹saturated› @{term U} artificial edge for an already-seen imbalanced vertex
      @{term v} (design notes §4, last table row): it carries @{term ‹art_flow v›} at its bound
      (capacity = flow), so it is tagged @{const InU} and touches no tree field.›

definition emit_U_edge :: "'n dfs_state ⇒ nat ⇒ 'n dfs_state" where
  "emit_U_edge s v =
     (let imb = imbalance ! v; up = 0 ≤ imb; fl = ¦imb¦
      in s⦇ ds_afst := (ds_afst s)[ds_nxt s := (if up then v else vcount)],
            ds_asnd := (ds_asnd s)[ds_nxt s := (if up then vcount else v)],
            ds_acap := (ds_acap s)[ds_nxt s := fl],
            ds_aflw := (ds_aflw s)[ds_nxt s := fl],
            ds_aest := (ds_aest s)[ds_nxt s := InU],
            ds_nxt  := Suc (ds_nxt s) ⦈)"

text ‹Phase 1 — one scan of the vertices, imbalanced first: an imbalanced unseen vertex opens its
      tree component; an imbalanced already-seen vertex emits a saturated @{term U} edge; balanced
      vertices are skipped.›

definition phase1_step :: "'n list ⇒ nat ⇒ 'n dfs_state ⇒ 'n dfs_state" where
  "phase1_step fl v s =
     (if imbalance ! v = 0 then s
      else if ¬ ds_seen s ! v then open_tree_component fl s v
      else emit_U_edge s v)"

definition phase1 :: "'n list ⇒ 'n dfs_state ⇒ 'n dfs_state" where
  "phase1 fl s = fold (phase1_step fl) vs_list s"

text ‹Phase 2 — a second vertex scan opening every still-unseen (necessarily balanced) vertex as a
      flow-0 tree component. Afterwards every vertex is seen, so the thread and parent map span the
      augmented vertex set, rooted at @{term vcount}.›

definition phase2_step :: "'n list ⇒ nat ⇒ 'n dfs_state ⇒ 'n dfs_state" where
  "phase2_step fl v s = (if ds_seen s ! v ∨ is_lonely v then s else open_tree_component fl s v)"

definition phase2 :: "'n list ⇒ 'n dfs_state ⇒ 'n dfs_state" where
  "phase2 fl s = fold (phase2_step fl) vs_list s"

text ‹The finished builder: run both phases, then the one ∗‹root finalisation› the traversal cannot
      do per-frame — the root @{term vcount} is never pushed, so it is never popped and its
      @{term ds_lsuc} slot is never written. Its last successor (rightmost descendant of the whole
      tree) is the last vertex emitted, i.e.\ the final @{term ds_prev}. This is the ndtree clause
      @{term ‹lsuc S r = last P›} (I7 at @{term r}); every non-root ‹lsuc›/‹snum› was already produced
      at its pop inside @{const build_dfs}, with no extra pass.›

definition build_tree :: "'n list ⇒ 'n dfs_state" where
  "build_tree fl = (let s = phase2 fl (phase1 fl dfs_init) in s⦇ ds_lsuc := (ds_lsuc s)[vcount := ds_prev s] ⦈)"


text ‹The acyclic-flow procedure is available here as an assumption-free specification instance: the two counting-sort CSRs are its edge iterators, the flow and vertex-state arrays are lists, and fst-exec / snd-exec are the constant-time endpoint reads. Interpreting the acyclic-flow specification locale exports the executable acyclifier into this specification locale, so the acyclifier can be executed without discharging any ADT law.›

sublocale acyclic_flow_impl_spec
  where  out_current = csr_current and out_has = csr_has
    and out_move = csr_move and out_reset = csr_reset
    and in_current = csr_current and in_has = csr_has
    and in_move = csr_move and in_reset = csr_reset
    and flow_upd = list_update and flow_lookup = nth
    and st_upd = list_update and st_lookup = nth
    and current_vertex = vtx_current and has_vertex = vtx_has
    and move_on_vertex = vtx_move
    and out_arr = out_csr
    and in_arr = in_csr
    and all_vertices = "⦇ vi_list = edged_vs_list, vi_pos = 0 ⦈"
    and cap = "λ e.  capacity_list ! e "
    and cost = "λ e. cost_list ! e"
    and state_init = "replicate vcount Unseen"
    and fst_exec = "λ e. fst_list ! e"
    and snd_exec = "λ e. snd_list ! e"
  by unfold_locales


subsection ‹The acyclified flow the tree is built from›

text ‹The candidate @{term flow_list} is only capacity-complying; the strongly-feasible tree is built
      from its ∗‹acyclified› form.  @{const make_acyclic} either returns @{term None} — a negative
      infinite-capacity free cycle, i.e.\ the instance is unbounded/infeasible and no tree is built —
      or @{term ‹Some f'›} with @{term ‹f'›} acyclic, capacity-complying and of the same excesses.
      @{term acyc_flow} is that output, defaulting to @{term flow_list} on the (guarded) @{term None}
      branch so every downstream array stays total; the orchestrator ‹solve› below never uses
      it on that branch.›

definition acyc_flow_opt :: "'n list option" where
  "acyc_flow_opt = make_acyclic flow_list"

definition acyc_flow :: "'n list" where
  "acyc_flow = (case acyc_flow_opt of Some f' ⇒ f' | None ⇒ flow_list)"

subsection ‹The abstract arborescence read off the builder arrays›

text ‹The spanning-tree ADT operations act on an @{typ ‹nat ndtree›}; ‹tree_st› reads it off the
      ∗‹finished builder state› (parent / thread / reverse-thread / last-successor /
      subtree-size), with the option-pointer maps sending the null sentinel @{term ‹0::nat›} and the
      unseen vertices to @{term None}.  @{term ‹vseen_st s›} are the discovered real vertices,
      @{term ‹varb_st s›} adds the root @{term vcount}.›

text ‹The reader is indexed by the builder ∗‹state›, not by the flow, and this is what makes it
      cheap: the five pointer maps of ‹tree_st› are closures, so had each captured a flow
      @{term fl} and called @{term ‹build_tree fl›} itself, ∗‹every single pointer lookup› during
      the simplex would re-run the whole builder.  Taking the finished state as the argument means
      @{const build_tree} is run once and all five fields share that one result.  The flow-indexed
      ‹tree_of› below is just the composition, used to state the initial tree.›

definition vseen_st :: "'n dfs_state ⇒ nat set" where
  "vseen_st s = {y. y < vcount ∧ ds_seen s ! y}"

definition varb_st :: "'n dfs_state ⇒ nat set" where
  "varb_st s = insert vcount (vseen_st s)"

definition sprnt_st :: "'n dfs_state ⇒ nat ⇒ nat option" where
  "sprnt_st s v = (if v ∈ vseen_st s then Some (ds_prnt s ! v) else None)"

definition sthrd_st :: "'n dfs_state ⇒ nat ⇒ nat option" where
  "sthrd_st s v = (if v ∈ varb_st s ∧ ds_thrd s ! v ≠ 0 then Some (ds_thrd s ! v) else None)"

definition srvth_st :: "'n dfs_state ⇒ nat ⇒ nat option" where
  "srvth_st s v = (if v ∈ varb_st s ∧ ds_rvth s ! v ≠ 0 then Some (ds_rvth s ! v) else None)"

definition tree_st :: "'n dfs_state ⇒ nat ndtree" where
  "tree_st s = ⦇ prnt = sprnt_st s, thrd = sthrd_st s, rvth = srvth_st s,
                 lsuc = (λv. ds_lsuc s ! v), snum = (λv. ds_snum s ! v) ⦈"

text ‹The flow-indexed views: each is its state-indexed counterpart at the finished builder. The
      equations ‹vseen_of_eq› … ‹tree_of_eq› below recover the original one-step definitions, so the
      correctness statements are unchanged.›

definition vseen_of :: "'n list ⇒ nat set" where
  "vseen_of fl = vseen_st (build_tree fl)"

definition varb_of :: "'n list ⇒ nat set" where
  "varb_of fl = varb_st (build_tree fl)"

definition sprnt_of :: "'n list ⇒ nat ⇒ nat option" where
  "sprnt_of fl = sprnt_st (build_tree fl)"

definition sthrd_of :: "'n list ⇒ nat ⇒ nat option" where
  "sthrd_of fl = sthrd_st (build_tree fl)"

definition srvth_of :: "'n list ⇒ nat ⇒ nat option" where
  "srvth_of fl = srvth_st (build_tree fl)"

definition tree_of :: "'n list ⇒ nat ndtree" where
  "tree_of fl = tree_st (build_tree fl)"

lemma vseen_of_eq: "vseen_of fl = {y. y < vcount ∧ ds_seen (build_tree fl) ! y}"
  by (simp add: vseen_of_def vseen_st_def)

lemma varb_of_eq: "varb_of fl = insert vcount (vseen_of fl)"
  by (simp add: varb_of_def vseen_of_def varb_st_def)

lemma sprnt_of_eq:
  "sprnt_of fl v = (if v ∈ vseen_of fl then Some (ds_prnt (build_tree fl) ! v) else None)"
  by (simp add: sprnt_of_def vseen_of_def sprnt_st_def)

lemma sthrd_of_eq:
  "sthrd_of fl v = (if v ∈ varb_of fl ∧ ds_thrd (build_tree fl) ! v ≠ 0
                    then Some (ds_thrd (build_tree fl) ! v) else None)"
  by (simp add: sthrd_of_def varb_of_def sthrd_st_def)

lemma srvth_of_eq:
  "srvth_of fl v = (if v ∈ varb_of fl ∧ ds_rvth (build_tree fl) ! v ≠ 0
                    then Some (ds_rvth (build_tree fl) ! v) else None)"
  by (simp add: srvth_of_def varb_of_def srvth_st_def)

lemma tree_of_eq:
  "tree_of fl = ⦇ prnt = sprnt_of fl, thrd = sthrd_of fl, rvth = srvth_of fl,
                  lsuc = (λv. ds_lsuc (build_tree fl) ! v),
                  snum = (λv. ds_snum (build_tree fl) ! v) ⦈"
  by (simp add: tree_of_def tree_st_def sprnt_of_def sthrd_of_def srvth_of_def)


subsection ‹Augmented-network arrays and the arborescence swap›

text ‹Executable augmented-network arrays and the arborescence swap operation, built directly on
      build-tree of the acyclified flow; they need no correctness hypothesis, so they live in the
      assumption-free code-side locale. The augmented cost array cost-all is not here: its cost uses
      the symbolic Big-M and is therefore proof-only.›

text ‹‹art_tree› names the ∗‹finished builder› of the acyclified flow.  Every consumer below reads
      it — the artificial-edge count ‹Kart› and the five augmented arrays, and further down the
      initial potential / parent / direction arrays and the initial tree handed to the interpreted
      simplex.  Binding it ∗‹once› here means the builder runs once rather than once per consumer.
      Its unfolding is a simp rule, so every proof still sees @{term ‹build_tree acyc_flow›} exactly
      as before.›

definition art_tree :: "'n dfs_state" where "art_tree = build_tree acyc_flow"

declare art_tree_def[simp]

definition Kart :: nat where "Kart = ds_nxt art_tree"
definition fst_all :: "nat list" where "fst_all = fst_list @ take Kart (ds_afst art_tree)"
definition snd_all :: "nat list" where "snd_all = snd_list @ take Kart (ds_asnd art_tree)"
definition cap_all :: "'n list" where "cap_all = capacity_list @ take Kart (ds_acap art_tree)"
definition flow_all :: "'n list" where "flow_all = acyc_flow @ take Kart (ds_aflw art_tree)"
definition state_all :: "edge_tag list" where "state_all = edge_state acyc_flow @ take Kart (ds_aest art_tree)"

definition swap_edge_impl :: "'a ndtree ⇒ 'a ⇒ 'a ⇒ 'a ⇒ 'a ndtree" where
  "swap_edge_impl S x u v = update_tree S u v x (join_of (prnt S) u v)"

subsection ‹The executable entering-edge selector›

definition marc :: nat where "marc = m + Kart"

definition cost_pval :: "nat ⇒  (mtag × 'n)" where
  "cost_pval e = (if e < m then (M_0, cost_list ! e) else pval_M)"

definition red_cost :: " (mtag × 'n) list ⇒ nat ⇒  (mtag × 'n)" where
  "red_cost π e =
     pval_plus (cost_pval e)
       (pval_minus (nth π (fst_all ! e))
                   (nth π (snd_all ! e)))"

definition eligible :: "edge_tag list ⇒ (mtag × 'n) list ⇒ nat ⇒ bool" where
  "eligible es π e =
     (fst_all ! e ≠ snd_all ! e ∧
      (case nth es e of
        InTree ⇒ False
      | InL    ⇒ pval_neg (red_cost π e)
      | InU    ⇒ pval_pos (red_cost π e)))"

definition ent_in_U :: "edge_tag list ⇒ nat ⇒ bool" where
  "ent_in_U es e = (nth es e = InU)"

definition evaluate :: "edge_tag list ⇒ 
 (mtag × 'n) list ⇒ nat ⇒ bool × bool ×  (mtag × 'n)" where
  "evaluate es π e =
     (let a = fst_all ! e; d = snd_all ! e
      in if a = d
         then (False, nth es e = InU, pval_zero)
         else let t = nth es e;
                  g = pval_plus (cost_pval e) (pval_minus (π ! a) (π ! d))
              in ((case t of InTree ⇒ False | InL ⇒ pval_neg g | InU ⇒ pval_pos g), t = InU, g))"

fun better :: "'n best_cand ⇒ nat × bool ×  (mtag × 'n) 
       ⇒ 'n best_cand" where
  "better (found, be, bu, bg) (e', u', g') =
     (if ¬ found ∨ viol_gt g' bg then (True, e', u', g') else (found, be, bu, bg))"

definition bok :: "edge_tag list ⇒  (mtag × 'n) list ⇒ 'n best_cand ⇒ nat list ⇒ nat ⇒ bool" where
  "bok es pt best a len =
     (case best of (f,e,u,g) ⇒
        f ⟶ (eligible es pt e ∧ u = ent_in_U es e ∧ g = red_cost pt e ∧ e ∈ set (take len a)))"

function scan_cache ::
    "edge_tag list ⇒  (mtag × 'n) list ⇒ nat 
⇒ nat list ⇒ nat ⇒ 'n best_cand
       ⇒ nat list × nat × 'n best_cand" where
  "scan_cache es π i a len best =
     (if len ≤ i then (a, len, best)
      else
        (let e = a ! i;
             (elig, u, g) = evaluate es π e
         in if elig
            then scan_cache es π (Suc i) a len (better best (e, u, g))
            else scan_cache es π i (a[i := a ! (len - 1)]) (len - 1) best))"
  by pat_completeness auto
termination
  by (relation "measure (λ(es, π, i, a, len, best). len - i)") auto

function scan ::
    "edge_tag list ⇒  (mtag × 'n) list ⇒ nat 
⇒ nat ⇒ nat ⇒ nat ⇒ nat list ⇒ nat ⇒ 'n best_cand
       ⇒ nat × nat list × nat × 'n best_cand" where
  "scan es π mc fuel bpos cur a len best =
     (if fuel = 0 then (cur, a, len, best)
      else if max_candidates ≤ len then (cur, a, len, best)
      else if bpos = 0 ∧ min_candidates ≤ len then (cur, a, len, best)
      else
        (let bpos1 = (if bpos = 0 then block_size else bpos);
             (elig, u, g) = evaluate es π cur;
             a1    = (if elig then a[len := cur] else a);
             len1  = (if elig then Suc len else len);
             best1 = (if elig then better best (cur, u, g) else best);
             cur1  = (if cur + 1 = mc then 0 else cur + 1)
         in scan es π mc (fuel - 1) (bpos1 - 1) cur1 a1 len1 best1))"
  by pat_completeness auto
termination
  by (relation "measure (λ(es, π, mc, fuel, bpos, cur, a, len, best). fuel)") auto

definition sel_select_impl ::
    "ns_sel ⇒  (mtag × 'n) list ⇒ edge_tag list 
     ⇒ (nat × bool ×  (mtag × 'n) × ns_sel) option" where
  "sel_select_impl sel π es =
     (case scan_cache es π 0 (sel_arr sel) (sel_len sel) no_best of
        (a1, len1, (found1, e, u, g)) ⇒
          if found1
          then Some (e, u, g, sel⦇ sel_arr := a1, sel_len := len1 ⦈)
          else
            ― ‹first @{term marc} = the fixed arc count @{term mc}; second = the initial @{term fuel}›
            (case scan es π marc marc block_size (sel_cur sel) a1 len1 no_best of
               (cur', a2, len2, (found2, e2, u2, g2)) ⇒
                 if found2
                 then Some (e2, u2, g2, ⦇ sel_cur = cur', sel_arr = a2, sel_len = len2 ⦈)
                 else None))"

definition sel_invar_impl :: "ns_sel ⇒ bool" where
  "sel_invar_impl sel ⟷
     length (sel_arr sel) = max_candidates
     ∧ sel_len sel ≤ max_candidates
     ∧ (0 < marc ⟶ sel_cur sel < marc)
     ∧ set (take (sel_len sel) (sel_arr sel)) ⊆ {0..<marc}"

definition init_sel :: ns_sel where
  "init_sel = ⦇ sel_cur = 0, sel_arr = replicate max_candidates 0, sel_len = 0 ⦈"


subsection ‹The network-simplex loop on the augmented network›

text ‹The executable network-simplex specification, interpreted for the augmented network with only
      ∗‹executable› operations supplied: the endpoints / capacities are the augmented arrays, the
      spanning-tree operations are @{const get_path_pair_impl} / @{const swap_edge_impl} /
      @{const iterate_root_opposed_impl}, the entering-edge selector is @{const sel_select_impl}, and
      the potential arithmetic is @{const pval_plus} / @{const pval_minus}.  The verification-only
      parameters — the real cost @{term 𝖼}, the descriptor abstractions and the store/descriptor
      invariants — are never evaluated by @{const network_simplex_spec.ns_loop_impl}, so they are given
      trivial placeholders here; their real form appears only in the proof interpretation.›

interpretation NSc: network_simplex_init_spec
  where r = vcount
    and shift_pot = shift_pot_impl
    and get_path_pair = get_path_pair_impl
    and swap_edge = swap_edge_impl
    and flow_upd = list_update and flow_lookup = nth
    and pot_upd = list_update and pot_lookup = nth
    and parent_upd = list_update and parent_lookup = nth
    and dir_upd = list_update and dir_lookup = nth
    and es_upd = list_update and es_lookup = nth
    and sel_select = sel_select_impl
    and cap = "λ e. cap_all ! e"
    and pot_value_plus = pval_plus
    and pot_value_minus = pval_minus
    and fst_exec = "λ e. fst_all ! e"
    and snd_exec = "λ e. snd_all ! e"
    and init_flow = flow_all
    and init_pot = "ds_pot art_tree"
    and init_tree = "tree_st art_tree"
    and init_parent = "ds_par art_tree"
    and init_dir = "ds_dir art_tree"
    and init_edge_state = state_all
    and init_sel = init_sel
  by unfold_locales

text ‹The starting state @{const NSc.init_state} — the augmented flow / edge-state, the potentials, the
      abstract arborescence and the parent / direction arrays read off the builder of the acyclified
      flow, and the fresh entering-edge selector — is provided by the interpreted @{locale
      network_simplex_init_spec}, not redefined here.›

text ‹The orchestrator.  First acyclify @{term flow_list}: a @{term None} answer is a negative
      infinite-capacity cycle, reported as @{const Neg_inf_cycle}.  Otherwise build the strongly-feasible
      spanning tree and run the network-simplex loop from @{const NSc.init_state}.  Its @{const return}
      flag distinguishes an @{const unbounded} circuit (again @{const Neg_inf_cycle}) from
      @{const success} (an optimum of the ∗‹augmented› network).  On success we inspect the artificial
      edges @{term ‹[m..<m+Kart]›}: if they all carry zero flow the original network is feasible and the
      minimum-cost @{term b}-flow is the augmented flow ∗‹restricted to the original edges›
      (@{term ‹take m›}); if any artificial edge still carries flow, no @{term b}-flow exists and the
      verdict is @{const Infeasible}.›

definition solve :: "'n ns_outcome" where
  "solve =
     (let ao = acyc_flow_opt
      in case ao of
           None ⇒ Neg_inf_cycle
         | Some _ ⇒
             (let s = NSc.ns_loop_impl NSc.init_state; f = current_flow s
              in if return s = unbounded then Neg_inf_cycle
                 else if list_all (λk. f ! k = 0) [m..<m+Kart]
                      then Optimum (take m f)
                      else Infeasible))"


end

end


