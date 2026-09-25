theory Network_Simplex
  imports Flow_Theory.Spanning_Tree_Flow Acyclic_Flow Flow_Theory.Cost_Optimality
begin

text ‹❙‹Tagged variant.› Instead of the two edge sets @{term L} and @{term U} being stored as two
      separate @{locale abstract_set} values, this development keeps a single
      @{locale abstract_array} @{term edge_state} that maps every edge to a ∗‹tag› recording its
      current r\^ole in the spanning-tree structure: @{term InTree} (a tree edge), @{term InL} (at its
      lower bound, i.e. in the former set @{term L}) or @{term InU} (saturated, i.e. in the former set
      @{term U}). The abstract views @{term ns_L_of} / @{term ns_U_of} still denote the very same edge
      sets — now carved out of @{term ‹ℰ›} by the tag — so the structural reasoning is unchanged.›

datatype edge_tag = InTree | InL | InU

locale arborescense_adt =
  fixes V::"'a set"
   and r::"'a"
   and arborescense_invar::"'arbor ⇒ bool"
   and abstract_arborescense::"'arbor ⇒ 'a set set"
   and get_path_pair::"'arbor ⇒ 'a ⇒ 'a ⇒ ('a list × 'a list)"
   and swap_edge::"'arbor ⇒ 'a ⇒'a ⇒'a ⇒ 'arbor"
 assumes
   general:
    "r ∈ V"
    "⋀ T. arborescense_invar T ⟹ graph_invar (abstract_arborescense T)"
    "⋀ T x y. ⟦arborescense_invar T; x ∈ V; y ∈ V⟧  ⟹ 
          ∃! p. (walk_betw (abstract_arborescense T) y p x)
                ∧ distinct p"
    "⋀ T. arborescense_invar T ⟹ Vs (abstract_arborescense T) = V"
   and get_path_pair:
     "⋀ T p1 p2 u v. ⟦arborescense_invar T; get_path_pair T u v = (p1,p2); u ≠ v; u∈ V; v ∈ V⟧ ⟹
          ∃ a p3. walk_betw (abstract_arborescense T) u (p1 @ a # p3) r ∧
                walk_betw (abstract_arborescense T) v (p2 @ a # p3) r ∧
                distinct (p1 @ a # p3) ∧ distinct (p2 @ a # p3) ∧
                set p1 ∩ set p2 = {}"
     "⋀ T p1 p2 u v. ⟦arborescense_invar T; get_path_pair T u v = (p1,p2) ; u ≠ v; u∈ V; v ∈ V⟧ ⟹
          get_path_pair T v u = (p2,p1)"
  and swap_edge:
      "⋀ T p1 p2 p3 a u v x y. ⟦arborescense_invar T; get_path_pair T u v = (p1,p2); u ≠ v;
                           walk_betw (abstract_arborescense T) u (p1 @ a # p3) r; distinct (p1 @ a # p3);
                           (x, y) ∈ set (edges_of_vwalk (p1 @ [a])); u∈ V; v ∈ V⟧ ⟹
                           arborescense_invar (swap_edge T x u v)"
      "⋀ T p1 p2 p3 a u v x y. ⟦arborescense_invar T; get_path_pair T u v = (p1,p2); u ≠ v;
                           walk_betw (abstract_arborescense T) u (p1 @ a # p3) r; distinct (p1 @ a # p3);
                           (x, y) ∈ set (edges_of_vwalk (p1 @ [a])); u∈ V; v ∈ V⟧ ⟹
                           abstract_arborescense (swap_edge T x u v) =
                           (abstract_arborescense T - {{x, y}} ∪ {{u, v}})"

section ‹Abstract data types for the algorithm›

text ‹Vertex potentials and edge reduced costs are not stored as plain reals. We use two abstract
      \emph{real descriptors}, each abstracted to @{typ real} by a verification-only function that is
      never executed:
      ▪ a ∗‹potential descriptor› @{typ 'p} for the vertex potentials held in the potential array —
        with invariant ‹pot_value_invar›, abstraction ‹pot_value_abstract›, and the two ∗‹mixed›
        operations ‹pot_value_plus, pot_value_minus :: 'p ⇒ 'r ⇒ 'p› that shift a potential by a
        reduced cost;
      ▪ a ∗‹reduced-cost descriptor› @{typ 'r} for the value ‹γ› the selector returns — with invariant
        ‹rcost_invar› and abstraction ‹rcost_abstract›; it carries no arithmetic of its own (reduced
        costs are never combined with one another).
      The two mixed operations are specified only ∗‹conditionally› (axioms ‹pot_value_plus_spec› /
      ‹pot_value_minus_spec›): their abstraction law and invariant preservation are guaranteed only
      when the resulting real value is admissible — a signed edge-cost sum in which ∗‹at most one› edge
      touches the root ‹r› (the predicate ‹good_pot_val› below). Every potential the algorithm
      maintains is a tree-path cost sum reaching ‹r› exactly once, so the guard always holds where the
      operations are used. This split and its guard are exactly what later let us realise the
      ``big-M'' method with a pair representation ‹(m, o)› (an M-coefficient and an ordinary part)
      without numerical-stability issues: the ‹≤ 1› root-edge bound keeps ‹¦m¦ ≤ 1› and the
      edge-cost-sum bound keeps the ordinary part from overflowing, so componentwise add/subtract stay
      exact and the constant ‹M› — occurring only inside the abstraction — is chosen once and never
      explicitly computed.›

text ‹The entering-edge (pivot) rule is abstracted as a small stateful ADT: an invariant
      @{term sel_invar} and a selection function @{term sel_select}. Given the current potentials
      and the two sets @{term L} and @{term U}, the selector returns either @{term None} (no eligible
      edge — the optimality stopping condition) or @{term "Some (e, in_U, γ, sel')"}: an entering
      edge @{term e}, a flag telling whether it came from @{term U} (@{term True}) or @{term L}
      (@{term False}), a descriptor @{term γ} of its reduced cost in the abstract real type, and an
      updated selector. The behavioural specification (invariant preservation and eligibility of the
      returned edge) is added in the proof locale.›

locale edge_selector =
  fixes sel_invar :: "'selector ⇒ bool"
    and sel_select ::
      "'selector ⇒ 'parr ⇒ 'earr
         ⇒ ('edge × bool × 'r × 'selector) option"

section ‹Specification locale for the network simplex algorithm›

text ‹The specification locale conjoins the cost-flow network (@{locale cost_flow_network}, source
      of the costs @{term ‹𝖼›} and the extended-real capacities @{term ‹𝗎›}), the spanning-tree ADT
      (@{locale arborescense_adt}), and the array-/set-like stores realising the program state:
      ▪ @{term flow_lookup} — an @{locale abstract_array} mapping every edge to its current flow (a
        @{typ real});
      ▪ @{term pot_lookup} — an @{locale abstract_array} mapping every vertex to its potential,
        represented in the abstract potential-descriptor type @{typ 'p} (reduced costs use the
        separate descriptor type @{typ 'r}; see the two real-descriptor families above);
      ▪ @{term parent_lookup} — an @{locale abstract_array} over the vertices @{term ‹V - {r}›}
        giving, for each vertex, the graph edge to its predecessor on the path to the root, and
      ▪ @{term dir_lookup} — a boolean @{locale abstract_array} over @{term ‹V - {r}›} recording the
        orientation of that parent edge;
      ▪ @{term es_lookup} — an @{locale abstract_array} mapping every edge to its @{typ edge_tag}
        state: @{term InTree} (in the spanning tree), @{term InL} (zero-flow, the former @{term L}) or
        @{term InU} (saturated, the former @{term U}). The zero-flow and saturated edge sets are the
        verification-only views ‹ns_L_of› / ‹ns_U_of› carved out of @{term ‹ℰ›} by the tag.
      In addition we fix the balances @{term b} (the cost-flow network has none) and an executable
      capacity @{term cap} on the reals in which @{term ‹- 1›} plays the role of infinity, linked to
      the abstract @{term ‹𝗎›} by the assumptions ‹cap_infinite› and ‹cap_finite›. We assume the
      graph has no self-loops (‹no_self_loop›), so every entering edge has two distinct endpoints and
      hence a well-defined fundamental circuit (@{term get_path_pair} is specified only for @{term ‹u ≠ v›}).
      The assumptions
      ‹sel_select_Some› and ‹sel_select_None› specify the behaviour of the entering-edge selection;
      the repackaged rules ‹sel_select_SomeD› / ‹sel_select_NoneD› in the body are the interface the
      loop uses.›

locale network_simplex_spec =
(*  cost_flow_spec where fst = "fst :: 'edge ⇒ 'a"
  for fst +
*)
  fixes r :: "'a"
    and sel_select :: "'selector ⇒ 'parr ⇒ 'earr ⇒ ('edge × bool × 'r × 'selector) option"
    and shift_pot :: "'arbor ⇒ 'a ⇒ 'parr ⇒ 'r ⇒ bool ⇒ 'parr"
    and get_path_pair :: "'arbor ⇒ 'a ⇒ 'a ⇒ ('a list × 'a list)"
    and swap_edge :: "'arbor ⇒ 'a ⇒ 'a ⇒ 'a ⇒ 'arbor"
    and flow_upd :: "'farr ⇒ 'edge ⇒ ('n::linordered_idom) ⇒ 'farr"
    and flow_lookup :: "'farr ⇒ 'edge ⇒ 'n"
    and pot_upd :: "'parr ⇒ 'a ⇒ 'p ⇒ 'parr"
    and pot_lookup :: "'parr ⇒ 'a ⇒ 'p"
    and parent_upd :: "'pearr ⇒ 'a ⇒ 'edge ⇒ 'pearr"
    and parent_lookup :: "'pearr ⇒ 'a ⇒ 'edge"
    and dir_upd :: "'darr ⇒ 'a ⇒ bool ⇒ 'darr"
    and dir_lookup :: "'darr ⇒ 'a ⇒ bool"
    and es_upd :: "'earr ⇒ 'edge ⇒ edge_tag ⇒ 'earr"
    and es_lookup :: "'earr ⇒ 'edge ⇒ edge_tag"
    and cap :: "'edge ⇒ 'n"
    and pot_value_plus     :: "'p ⇒ 'r ⇒ 'p"
    and pot_value_minus    :: "'p ⇒ 'r ⇒ 'p"
    and fst_exec           :: "'edge ⇒ 'a"
    and snd_exec           :: "'edge ⇒ 'a"
begin
end

section ‹Program state›

text ‹The termination flag of the loop. @{term notyetterm} means the algorithm is still running,
      @{term success} that an optimum spanning tree structure has been reached, and @{term unbounded}
      that step 4 exposed an all-infinite-capacity circuit with @{term ‹γ ≠ 0›}, i.e. the instance is
      unbounded. (An @{term infeasible} value for the Big-M initialisation will be added later.)›

datatype return = notyetterm | success | unbounded
text ‹The mutable program state of the network simplex loop. It bundles the current flow and the
      vertex potentials (as array stores), the spanning tree structure — represented both abstractly
      (@{term spanning_tree}) and concretely through the @{term parent_edge} / @{term edge_dir}
      arrays that, for every non-root vertex, record the graph edge to its predecessor on the path to
      the root and that edge's orientation — the edge-state array @{term edge_state} tagging every edge
      as @{term InTree}, @{term InL} (zero-flow, i.e. L) or @{term InU} (saturated, i.e. U), the
      (stateful) entering-edge selector, and the termination flag.›

record ('farr, 'parr, 'tree, 'pearr, 'darr, 'earr, 'sel) network_simplex_state =
  current_flow  :: 'farr
  potentials    :: 'parr
  spanning_tree :: 'tree
  parent_edge   :: 'pearr
  edge_dir      :: 'darr
  edge_state    :: 'earr
  edge_sel      :: 'sel
  return        :: return

section ‹The network simplex loop›

text ‹We assemble the loop over the program state, following steps 2–6 of the algorithm. Its body
      branches on the four criteria: (i) whether the selector finds an entering edge at all
      (@{term None} — the structure is optimal); (ii) whether that edge comes from @{term L} or
      @{term U} (the @{term in_U} flag, which fixes the orientation of the fundamental circuit);
      (iii) whether the circuit's bottleneck is infinite (an unbounded negative cycle); and (iv)
      whether the entering edge is itself the bottleneck — then it merely flips between @{term L} and
      @{term U} with no tree change (@{term ns_flip}) — or a genuine tree edge leaves and a full pivot
      is performed (@{term ns_pivot}).

      Residual capacities are handled on the reals with @{term ‹- 1›} as the infinity sentinel
      (matching @{term cap}), and the fundamental circuit is never materialised — the bottleneck and
      the flow augmentation fold in place over the two vertex paths @{term get_path_pair} returns —
      so every operation is executable. The @{term parent_edge} / @{term edge_dir} arrays are
      re-parented in place after each swap (@{term reparent}). The orientation conventions — the
      first/last bottleneck tie-break, the per-side residual directions, the flow-augmentation signs,
      the leaving-edge @{term L}/@{term U} assignment, and the potential-shift sign
      @{term ‹in_U ≠ up_side›} — have all been cross-checked against LEMON's reference
      implementation; their formal verification awaits the correctness proof.›

context network_simplex_spec
begin

subsection ‹Reading the state and residual capacities›

text ‹Run the entering-edge selector on the current potentials and the two edge sets.›
definition "ns_select s = sel_select (edge_sel s) (potentials s) (edge_state s)"

text ‹Forward residual (remaining capacity) and backward residual (current flow) of a graph edge,
      as reals with @{term ‹- 1›} standing for ∞ (only the forward residual can be infinite).›
definition "res_fwd s a =
  (let c = cap a in if c = - 1 then - 1 else c - flow_lookup (current_flow s) a)"
definition "res_bwd s a = flow_lookup (current_flow s) a"

subsection ‹Parent edges and their residuals›

text ‹For a non-root vertex @{term v}: its parent graph edge, and the orientation flag. By
      convention @{term ‹par_up s v›} is @{const True} iff that edge points \emph{from} @{term v}
      \emph{to} its parent.›
definition "par_edge s v = parent_lookup (parent_edge s) v"
definition "par_up s v = dir_lookup (edge_dir s) v"

text ‹Residual of @{term v}'s parent edge when the fundamental circuit traverses it upward (child to
      parent, @{term res_up}) resp. downward (parent to child, @{term res_down}). Upward traversal is
      \emph{forward} exactly when the edge natively points to the parent.›
definition "res_up s v =
  (if par_up s v then res_fwd s (par_edge s v) else res_bwd s (par_edge s v))"
definition "res_down s v =
  (if par_up s v then res_bwd s (par_edge s v) else res_fwd s (par_edge s v))"

subsection ‹Bottleneck (in-place, over the two tree paths)›

text ‹Minimum of two residuals under the @{term ‹- 1›} = ∞ convention.›
definition "mininf (x::'n) (y::'n) =
  (if x = - 1 then y else if y = - 1 then x else min x y)"

text ‹Scan a tree path bottom-up (leaf towards the ancestor), returning the smallest residual seen
      (@{term ‹- 1›} if the path is empty or all-infinite) together with the child vertex of the
      attaining edge. @{term scan_up} is used on the ‹edge → ancestor› side and keeps the \emph{last}
      minimiser (nearest the peak, via ‹≤›); @{term scan_down} is used on the ‹ancestor → edge› side
      and keeps the \emph{first} minimiser (via ‹<›). No intermediate list is built.›
definition "scan_up s p =
  fold (λ v acc.
          case acc of (m, best) ⇒
            (let rr = res_up s v in
             if rr = - 1 then (m, best)
             else if m = - 1 then (rr, v)
             else if rr ≤ m then (rr, v)
             else (m, best)))
       p ((- 1)::'n, r)"
definition "scan_down s p =
  fold (λ v acc.
          case acc of (m, best) ⇒
            (let rr = res_down s v in
             if rr = - 1 then (m, best)
             else if m = - 1 then (rr, v)
             else if rr < m then (rr, v)
             else (m, best)))
       p ((- 1)::'n, r)"

text ‹The bottleneck of the fundamental circuit of the entering edge @{term e}, computed in place
      over the two vertex paths @{term p1}, @{term p2} (from @{term get_path_pair}, hoisted into
      @{term ns_loop} and passed in; no circuit list is materialised).
      For an edge in @{term L} (@{term ‹¬ in_U›}) flow is pushed forward and the ‹snd e› side is the
      up-path; for @{term U} the roles swap. The result is @{const None} when every arc is infinite
      (unbounded negative cycle), otherwise @{term ‹Some (δ, leaving)›} where @{term δ} is the minimum
      residual and @{term leaving} is @{const None} when the entering edge itself is the bottleneck
      (a flip), or @{term ‹Some (v, e0fwd, up_side)›} giving the leaving edge's child vertex
      @{term v}, whether its arc is forward (saturated) and whether it lies on the up-side of the
      circuit. The peak-based tie-break is realised by preferring the up-path (last), then the
      entering edge, then the down-path (first).›
definition "bottleneck s e in_U p1 p2 =
  (let up_path = (if in_U then p1 else p2);
       down_path = (if in_U then p2 else p1);
       r_e = (if in_U then res_bwd s e else res_fwd s e)
   in case scan_up s up_path of (mu, vu) ⇒
      case scan_down s down_path of (md, vd) ⇒
        (let d = mininf r_e (mininf mu md) in
         if d = - 1 then (- 1, True, r, False, False)
         else if mu ≠ - 1 ∧ mu = d then (d, False, vu, par_up s vu, True)
         else if r_e = d then (d, True, r, False, False)
         else (d, False, vd, ¬ par_up s vd, False)))"

subsection ‹State updates›

text ‹Augment the flow by @{term δ} along the fundamental circuit, in place: the entering edge, then
      the up-path (forward when its edges point to the parent), then the down-path (the opposite).
      A degenerate pivot (@{term ‹δ = 0›}, common under strong feasibility) leaves the flow untouched
      and returns it directly — no circuit rewrite — mirroring LEMON's @{text ‹if (delta > 0)›} guard
      in @{text changeFlow}. (The tree swap, potential shift and re-parenting still happen: only the
      flow update is skippable.)›
definition "augment_flow s e in_U δ p1 p2 =
  (if δ ≤ 0 then current_flow s else
   (let up_path = (if in_U then p1 else p2);
       down_path = (if in_U then p2 else p1);
       f0 = flow_upd (current_flow s) e
              (flow_lookup (current_flow s) e + (if in_U then - δ else δ));
       f1 = fold (λ v f. let a = par_edge s v in
                    flow_upd f a (flow_lookup f a + (if par_up s v then δ else - δ)))
                 up_path f0
   in fold (λ v f. let a = par_edge s v in
              flow_upd f a (flow_lookup f a + (if par_up s v then - δ else δ)))
           down_path f1))"

text ‹Shift the potentials by @{term γ} (added if @{term up}, else subtracted) over the far side of
      the cut, rooted at @{term v}. This is now a ∗‹first-order primitive› @{term shift_pot} of the
      spec locale — @{term ‹shift_pot T v pa γ up›} returns the potential store obtained from
      @{term pa} by shifting every potential in the subtree opposed to the root at @{term v} — so it
      mirrors the imperative @{term shift_pot_imp} exactly (no higher-order tree-iteration callback).
      Its behaviour is characterised in the proof locale by the assumption @{text shift_pot_spec}.›

text ‹Terminal states: optimum reached, and unbounded negative cycle found.›
definition "ns_optimal s = s ⦇ return := success ⦈"
definition "ns_unbounded_upd s = s ⦇ return := unbounded ⦈"

text ‹Degenerate pivot (the entering edge is its own bottleneck, @{term ‹e = e0›}): the tree and
      potentials are unchanged and @{term e} flips between @{term L} and @{term U}, but the flow is
      still augmented by @{term δ} along the ∗‹whole fundamental circuit› via @{const augment_flow}
      (which folds over the pre-computed paths @{term p1}, @{term p2} — no new list is built) — not
      merely on @{term e}. This mirrors KV step ⑥, which augments @{term f} by @{term δ} along
      @{term C} even when @{term ‹e = e0›} (only @{term T} and @{term π} stay fixed), and LEMON's
      @{text changeFlow}, which pushes @{term δ} around the cycle regardless of whether the tree
      changes. Updating @{term e} alone would break flow conservation whenever ‹δ = u e› is nonzero.
      The @{term ‹δ ≤ 0›} guard inside @{const augment_flow} makes the truly degenerate
      @{term ‹δ = 0›} case a pure @{term L}/@{term U} relabelling.›
definition "ns_flip s e in_U γ sel' δ p1 p2 =
  s ⦇ current_flow := augment_flow s e in_U δ p1 p2,
      edge_state := es_upd (edge_state s) e (if in_U then InL else InU),
      edge_sel := sel' ⦈"

text ‹Re-parenting after a swap. When the entering edge @{term e} replaces the leaving edge (child
      vertex @{term v}), the subtree hanging below @{term v} is re-attached to the rest of the tree
      through @{term e}. Concretely, the spine @{term P} from the far endpoint @{term ‹hd P›} up to
      @{term v} has its parent pointers \emph{reversed}: the far endpoint gets @{term e} as its new
      parent edge (pointing to the other endpoint of @{term e}, so its direction flag is
      @{term ‹hd P = fst e›}); every higher spine vertex inherits the \emph{old} parent edge of its
      predecessor, with the orientation flipped. Vertices above @{term v}, and all subtrees hanging
      off the spine, are untouched. Walked in place from @{term ‹hd P›} up to @{term v} and \emph{no
      further} — the tail of @{term P} from @{term v} towards the peak is never visited, matching
      LEMON, which walks only the stem @{text ‹u_out … u_in›}. The @{term prev} argument carries the
      previous spine vertex (whose \emph{old} orientation, read from @{term s}, is inherited), so
      there is no read-after-write.›
fun reparent_walk where
  "reparent_walk s e v first pe pup [] pd = pd"
| "reparent_walk s e v first pe pup (w # ws) pd =
     (case pd of (parr, darr) ⇒
      (let pd' = (if first
                  then (parent_upd parr w e, dir_upd darr w (w = fst_exec e))
                  else (parent_upd parr w pe, dir_upd darr w (¬ pup)))
       in if w = v then pd'
          else reparent_walk s e v False (par_edge s w) (par_up s w) ws pd'))"

definition "reparent s e P v = reparent_walk s e v True e False P (parent_edge s, edge_dir s)"

text ‹Full pivot: the entering edge @{term e} enters the tree in place of the leaving edge
      @{term ‹e0 = par_edge s v›} (child vertex @{term v}). Augment the flow along the circuit, shift
      the potentials over the far side rooted at @{term v} — the sign is derived from the processing
      direction @{term in_U} and the side @{term up_side} of the leaving edge — swap the tree edge,
      re-parent the @{term parent_edge} / @{term edge_dir} arrays along the spine @{term P} (the path
      @{term v} lies on), and move @{term e} out of its set and @{term e0} into @{term U} (if
      saturated, @{term e0fwd}) or @{term L}. The shift magnitude @{term γ} is the entering edge's
      reduced cost and the sign @{term ‹in_U ≠ up_side›} follows LEMON's @{text updatePotential}
      (@{text ‹σ = −pred_dir[u_in]·c⇩π(e)›}), positive exactly when the moved subtree contains the
      head @{term ‹snd e›}.›
definition "ns_pivot s e in_U γ sel' δ v e0fwd up_side p1 p2 =
  (let e0 = par_edge s v;
       P = (if in_U = up_side then p1 else p2);
       (parr, darr) = reparent s e P v
   in s ⦇ current_flow := augment_flow s e in_U δ p1 p2,
          potentials := shift_pot (spanning_tree s) v (potentials s) γ (in_U ≠ up_side),
          spanning_tree := swap_edge (spanning_tree s) v
                             (if in_U = up_side then fst_exec e else snd_exec e)
                             (if in_U = up_side then snd_exec e else fst_exec e),
          parent_edge := parr,
          edge_dir := darr,
          edge_state := es_upd (es_upd (edge_state s) e InTree) e0 (if e0fwd then InU else InL),
          edge_sel := sel' ⦈)"

subsection ‹The loop›

text ‹One iteration: select an entering edge; if there is none the structure is optimal; otherwise
      compute the bottleneck; if it is infinite the instance is unbounded; otherwise pivot — a flip
      when the entering edge is the bottleneck (@{term ‹leaving = None›}), a full swap otherwise —
      and recurse. Termination is not proven here (@{command function}~@{text ‹(domintros)›}); the
      executable @{command partial_function} twin will be added later.›
function (domintros) ns_loop where
"ns_loop s =
  (case ns_select s of None ⇒ ns_optimal s
     | Some (e, in_U, γ, sel') ⇒
       (let (p1, p2) = get_path_pair (spanning_tree s) (fst_exec e) (snd_exec e) in
       (case bottleneck s e in_U p1 p2 of (δ, is_flip, v, e0fwd, up_side) ⇒
         if δ = - 1 then ns_unbounded_upd s
         else if is_flip then ns_loop (ns_flip s e in_U γ sel' δ p1 p2)
         else ns_loop (ns_pivot s e in_U γ sel' δ v e0fwd up_side p1 p2))))"
  by pat_completeness auto

text ‹The executable twin: the same body with the recursive calls redirected to itself, defined as a
      @{command partial_function}~@{text ‹(tailrec)›} so that code equations are produced. It agrees
      with @{const ns_loop} on the domain (see the agreement lemma below).›

partial_function (tailrec) ns_loop_impl where
"ns_loop_impl s =
  (case ns_select s of None ⇒ ns_optimal s
     | Some (e, in_U, γ, sel') ⇒
       (let (p1, p2) = get_path_pair (spanning_tree s) (fst_exec e) (snd_exec e) in
       (case bottleneck s e in_U p1 p2 of (δ, is_flip, v, e0fwd, up_side) ⇒
         if δ = - 1 then ns_unbounded_upd s
         else if is_flip then ns_loop_impl (ns_flip s e in_U γ sel' δ p1 p2)
         else ns_loop_impl (ns_pivot s e in_U γ sel' δ v e0fwd up_side p1 p2))))"

lemmas [code] = ns_loop_impl.simps

subsection ‹Branch state-transformers and guards›

text ‹The state transformer of each recursive branch, re-deriving from @{term s} alone the values the
      loop body destructures. The two terminal branches reuse @{const ns_optimal} and
      @{const ns_unbounded_upd}.›

definition "ns_flip_upd s =
  (let (e, in_U, γ, sel') = the (ns_select s);
       (p1, p2) = get_path_pair (spanning_tree s) (fst_exec e) (snd_exec e);
       (δ, is_flip, v, e0fwd, up_side) = bottleneck s e in_U p1 p2
   in ns_flip s e in_U γ sel' δ p1 p2)"

definition "ns_pivot_upd s =
  (let (e, in_U, γ, sel') = the (ns_select s);
       (p1, p2) = get_path_pair (spanning_tree s) (fst_exec e) (snd_exec e);
       (δ, is_flip, v, e0fwd, up_side) = bottleneck s e in_U p1 p2
   in ns_pivot s e in_U γ sel' δ v e0fwd up_side p1 p2)"

text ‹The four mutually-exclusive, exhaustive branch guards.›

definition "ns_success_cond s =
  (case ns_select s of None ⇒ True | Some _ ⇒ False)"

definition "ns_unbounded_cond s =
  (case ns_select s of None ⇒ False
   | Some (e, in_U, γ, sel') ⇒
       (let (p1, p2) = get_path_pair (spanning_tree s) (fst_exec e) (snd_exec e)
        in (case bottleneck s e in_U p1 p2 of (δ, is_flip, v, e0fwd, up_side) ⇒ δ = - 1)))"

definition "ns_flip_cond s =
  (case ns_select s of None ⇒ False
   | Some (e, in_U, γ, sel') ⇒
       (let (p1, p2) = get_path_pair (spanning_tree s) (fst_exec e) (snd_exec e)
        in (case bottleneck s e in_U p1 p2 of (δ, is_flip, v, e0fwd, up_side) ⇒ δ ≠ - 1 ∧ is_flip)))"

definition "ns_pivot_cond s =
  (case ns_select s of None ⇒ False
   | Some (e, in_U, γ, sel') ⇒
       (let (p1, p2) = get_path_pair (spanning_tree s) (fst_exec e) (snd_exec e)
        in (case bottleneck s e in_U p1 p2 of (δ, is_flip, v, e0fwd, up_side) ⇒ δ ≠ - 1 ∧ ¬ is_flip)))"

end

section ‹Correctness locale for the network simplex loop›

text ‹The proof locale extends the executable specification @{locale network_simplex_spec} by
      re-imposing the cost-flow network, the spanning-tree ADT and the five array/selector
      contracts as genuine assumptions, together with the capacity encoding, the selector
      behaviour and the potential-descriptor arithmetic. All correctness reasoning lives here.›

locale network_simplex =
  cost_flow_network where fst = "fst :: 'edge ⇒ 'a"  and snd = snd+
  real_embedding where h = "h :: 'n ⇒ real" +
  network_simplex_spec where sel_select = sel_select and flow_upd = flow_upd
      and pot_upd = pot_upd and parent_upd = parent_upd and dir_upd = dir_upd
      and es_upd = es_upd +
  selector: edge_selector where sel_invar = sel_invar and sel_select = sel_select +
  arborescense_adt where V = "𝒱 :: 'a set" and r = "r :: 'a"
      and get_path_pair = get_path_pair
      and swap_edge = swap_edge +
  flow_arr: abstract_array where K = "ℰ :: 'edge set" and
      abstract_array_invar = flow_invar and abstract_array_upd = flow_upd and
      abstract_array_lookup = flow_lookup +
  pot_arr: abstract_array where K = "𝒱 :: 'a set" and
      abstract_array_invar = pot_invar and abstract_array_upd = pot_upd and
      abstract_array_lookup = pot_lookup +
  parent_arr: abstract_array where K = "𝒱 - {r} :: 'a set" and
      abstract_array_invar = parent_invar and abstract_array_upd = parent_upd and
      abstract_array_lookup = parent_lookup +
  dir_arr: abstract_array where K = "𝒱 - {r} :: 'a set" and
      abstract_array_invar = dir_invar and abstract_array_upd = dir_upd and
      abstract_array_lookup = dir_lookup +
  es_arr: abstract_array where K = "ℰ :: 'edge set" and
      abstract_array_invar = es_invar and abstract_array_upd = es_upd and
      abstract_array_lookup = es_lookup
    for fst and snd and 
        flow_invar :: "'farr ⇒ bool" and pot_invar :: "'parr ⇒ bool"
    and parent_invar :: "'pearr ⇒ bool" and dir_invar :: "'darr ⇒ bool"
    and es_invar :: "'earr ⇒ bool" and sel_invar :: "'selector ⇒ bool"
    and sel_select :: "'selector ⇒ 'parr ⇒ 'earr
                         ⇒ ('edge × bool × 'r × 'selector) option"
    and flow_upd :: "'farr ⇒ 'edge ⇒ ('n::linordered_idom) ⇒ 'farr"
    and h :: "'n ⇒ real"
    and pot_upd :: "'parr ⇒ 'a ⇒ 'p ⇒ 'parr"
    and parent_upd :: "'pearr ⇒ 'a ⇒ 'edge ⇒ 'pearr"
    and dir_upd :: "'darr ⇒ 'a ⇒ bool ⇒ 'darr"
    and es_upd :: "'earr ⇒ 'edge ⇒ edge_tag ⇒ 'earr"    and pot_value_invar :: "'p ⇒ bool" and rcost_invar :: "'r ⇒ bool"
    and pot_value_abstract :: "'p ⇒ real" and rcost_abstract :: "'r ⇒ real" +
  fixes b :: "'a ⇒ real"
  assumes fst_exec_coincide:
      "⋀ e. e ∈ ℰ ⟹ fst_exec e = fst e"
    and snd_exec_coincide:
      "⋀ e. e ∈ ℰ ⟹ snd_exec e = snd e"
    and cap_infinite:
      "⋀ e. e ∈ ℰ ⟹ (cap e = - 1) ⟷ 𝗎 e = ∞"
    and cap_finite:
      "⋀ e. ⟦e ∈ ℰ; cap e ≥ 0⟧ ⟹ 𝗎 e = ereal (h (cap e))"
    and cap_nonneg:
      "⋀ e. e ∈ ℰ ⟹ 0 ≤ cap e ∨ cap e = - 1"
    and sel_select_Some:
      "⋀ sel π es e in_U γ sel'.
         ⟦sel_invar sel; pot_invar π; ∀ v ∈ 𝒱. pot_value_invar (pot_lookup π v);
           pot_value_abstract (pot_lookup π r) = 0;
           es_invar es; sel_select sel π es = Some (e, in_U, γ, sel')⟧ ⟹
           sel_invar sel' ∧ rcost_invar γ ∧
           rcost_abstract γ
             = 𝖼 e + pot_value_abstract (pot_lookup π (fst e))
                   - pot_value_abstract (pot_lookup π (snd e)) ∧
           (if in_U then e ∈ ℰ ∧ fst e ≠ snd e ∧ es_lookup es e = InU ∧ rcost_abstract γ > 0
                    else e ∈ ℰ ∧ fst e ≠ snd e ∧ es_lookup es e = InL ∧ rcost_abstract γ < 0)"
    and sel_select_None:
      "⋀ sel π es.
         ⟦sel_invar sel; pot_invar π; ∀ v ∈ 𝒱. pot_value_invar (pot_lookup π v);
           pot_value_abstract (pot_lookup π r) = 0;
           es_invar es; sel_select sel π es = None⟧ ⟹
           (∀ e ∈ ℰ. fst e ≠ snd e ⟶ es_lookup es e = InL ⟶ 𝖼 e + pot_value_abstract (pot_lookup π (fst e))
                                      - pot_value_abstract (pot_lookup π (snd e)) ≥ 0) ∧
           (∀ e ∈ ℰ. fst e ≠ snd e ⟶ es_lookup es e = InU ⟶ 𝖼 e + pot_value_abstract (pot_lookup π (fst e))
                                      - pot_value_abstract (pot_lookup π (snd e)) ≤ 0)"
    and pot_value_plus_spec:
      "⋀ p g. ⟦pot_value_invar p; rcost_invar g;
           ∃ A D. A ⊆ ℰ ∧ D ⊆ ℰ ∧
                  card {e ∈ A ∪ D. fst e = r ∨ snd e = r} ≤ 1 ∧
                  pot_value_abstract p + rcost_abstract g = (∑ e ∈ A. 𝖼 e) - (∑ e ∈ D. 𝖼 e)⟧ ⟹
           pot_value_abstract (pot_value_plus p g) = pot_value_abstract p + rcost_abstract g ∧
           pot_value_invar (pot_value_plus p g)"
    and pot_value_minus_spec:
      "⋀ p g. ⟦pot_value_invar p; rcost_invar g;
           ∃ A D. A ⊆ ℰ ∧ D ⊆ ℰ ∧
                  card {e ∈ A ∪ D. fst e = r ∨ snd e = r} ≤ 1 ∧
                  pot_value_abstract p - rcost_abstract g = (∑ e ∈ A. 𝖼 e) - (∑ e ∈ D. 𝖼 e)⟧ ⟹
           pot_value_abstract (pot_value_minus p g) = pot_value_abstract p - rcost_abstract g ∧
           pot_value_invar (pot_value_minus p g)"
    and shift_pot_spec:
      "⋀ T v pa g up.
         ⟦arborescense_invar T; v ∈ 𝒱; pot_invar pa;
           ⋀u. u ∈ 𝒱 ⟹ pot_value_invar (pot_lookup pa u)⟧ ⟹
         ∃ xs. set xs = {x. ∃p. walk_betw (abstract_arborescense T) x p r ∧ distinct p ∧ v ∈ set p}
               ∧ distinct xs
               ∧ shift_pot T v pa g up
                   = foldr (λ x acc. pot_upd acc x
                        ((if up then pot_value_plus else pot_value_minus) (pot_lookup acc x) g)) xs pa"
begin

text ‹The executable endpoint functions @{term fst_exec} / @{term snd_exec} coincide with the
      abstract @{term fst} / @{term snd} on the edge set @{term ℰ}. Every edge the loop ever handles
      lies in @{term ℰ}, so once @{term ‹e ∈ ℰ›} is known these rewrite the executable projections
      back to the abstract ones, letting the existing proofs go through unchanged.›

lemmas fst_exec_eq[simp] = fst_exec_coincide
lemmas snd_exec_eq[simp] = snd_exec_coincide


text ‹Abstract (verification-only) view of the potentials, and the reduced cost
      @{term ‹cπ e = 𝖼 e + π (fst e) - π (snd e)›} of an edge under a potential array.›

abbreviation "abstract_pot π v ≡ pot_value_abstract (pot_lookup π v)"

definition "reduced_cost π e = 𝖼 e + abstract_pot π (fst e) - abstract_pot π (snd e)"

text ‹The guard under which the potential-descriptor arithmetic (@{term pot_value_plus} /
      @{term pot_value_minus}) is specified: a real @{term x} is \emph{admissible} when it is a signed
      sum of edge costs in which ∗‹at most one› edge touches the root @{term r}. Every potential the
      algorithm maintains is a tree-path cost sum reaching @{term r} exactly once, so this holds for
      every value fed to the descriptor operations — and it is exactly what a ``big-M'' pair
      representation ‹(m, o)› needs (the ‹≤ 1› root edge bounds the M-coefficient ‹¦m¦ ≤ 1›, and being
      a genuine edge-cost sum bounds the ordinary part ‹o›).›

definition "good_pot_val x ≡
  (∃ A D. A ⊆ ℰ ∧ D ⊆ ℰ ∧
          card {e ∈ A ∪ D. fst e = r ∨ snd e = r} ≤ 1 ∧
          x = (∑ e ∈ A. 𝖼 e) - (∑ e ∈ D. 𝖼 e))"

text ‹A potential store is \emph{valid} when its array invariant holds and every stored vertex
      potential is a well-formed element of the abstract real type.›

definition "pot_valid π ≡ pot_invar π ∧ (∀ v ∈ 𝒱. pot_value_invar (pot_lookup π v))"

text ‹The precondition under which the edge selection is specified: the selector, the potentials
      and both edge sets are well-formed.›

definition "selection_precond sel π es ≡
  sel_invar sel ∧ pot_valid π ∧ es_invar es ∧ pot_value_abstract (pot_lookup π r) = 0"

text ‹@{term ‹entering_edge π L U e in_U›} states that @{term e} is an eligible entering edge with the
      given membership flag: taken from @{term U} with strictly positive reduced cost, or from
      @{term L} with strictly negative reduced cost. @{term ‹no_entering_edge π L U›} is the negation
      over all of @{term L} and @{term U} — the optimality (stopping) condition.›

definition "entering_edge π es e in_U ≡
  (if in_U then e ∈ ℰ ∧ fst e ≠ snd e ∧ es_lookup es e = InU ∧ reduced_cost π e > 0
           else e ∈ ℰ ∧ fst e ≠ snd e ∧ es_lookup es e = InL ∧ reduced_cost π e < 0)"

definition "no_entering_edge π es ≡
  (∀ e ∈ ℰ. fst e ≠ snd e ⟶ es_lookup es e = InL ⟶ reduced_cost π e ≥ 0) ∧
  (∀ e ∈ ℰ. fst e ≠ snd e ⟶ es_lookup es e = InU ⟶ reduced_cost π e ≤ 0)"text ‹The two selection assumptions above are stated on unfolded expressions (a locale cannot refer
      to its own body definitions). The following two rules repackage them in terms of the
      predicates just introduced — this is the interface the loop and its correctness proof use.
      Whenever the selection precondition holds: a @{term ‹Some (e, in_U, γ, sel')›} result yields an
      updated selector satisfying its invariant, a well-formed descriptor @{term γ} whose value is
      exactly the reduced cost of @{term e}, and an eligible entering edge with flag @{term in_U}; a
      @{term None} result means no entering edge exists, i.e. the structure is optimal.›

lemma sel_select_SomeD:
  assumes "selection_precond sel π es" "sel_select sel π es = Some (e, in_U, γ, sel')"
  shows "sel_invar sel'" and "rcost_invar γ"
    and "rcost_abstract γ = reduced_cost π e" and "entering_edge π es e in_U"
  using sel_select_Some[of sel π es e in_U γ sel'] assms
  by (auto simp: selection_precond_def pot_valid_def reduced_cost_def entering_edge_def)

lemma sel_select_NoneD:
  assumes "selection_precond sel π es" "sel_select sel π es = None"
  shows "no_entering_edge π es"
  using sel_select_None[of sel π es] assms
  by (auto simp: selection_precond_def pot_valid_def no_entering_edge_def reduced_cost_def)

subsection ‹Introduction / elimination rules for the guards›

lemma ns_success_condE:
  assumes "ns_success_cond s" "ns_select s = None ⟹ Q"
  shows Q
  using assms by (auto simp: ns_success_cond_def split: option.splits)

lemma ns_success_condI: "ns_select s = None ⟹ ns_success_cond s"
  by (auto simp: ns_success_cond_def)

lemma ns_unbounded_condE:
  assumes "ns_unbounded_cond s"
    "⋀ e in_U γ sel' p1 p2 is_flip v e0fwd up_side.
       ⟦ns_select s = Some (e, in_U, γ, sel');
        get_path_pair (spanning_tree s) (fst_exec e) (snd_exec e) = (p1, p2);
        bottleneck s e in_U p1 p2 = (- 1, is_flip, v, e0fwd, up_side)⟧ ⟹ Q"
  shows Q
proof -
  have "ns_select s ≠ None"
    using assms(1) by (auto simp: ns_unbounded_cond_def split: option.splits)
  then obtain e in_U γ sel' where sel: "ns_select s = Some (e, in_U, γ, sel')"
    by (metis prod_cases4 option.exhaust)
  obtain p1 p2 where pp: "get_path_pair (spanning_tree s) (fst_exec e) (snd_exec e) = (p1, p2)"
    by (metis prod.exhaust)
  obtain δ is_flip v e0fwd up_side
    where bn: "bottleneck s e in_U p1 p2 = (δ, is_flip, v, e0fwd, up_side)"
    by (metis prod_cases5)
  have "δ = - 1"
    using assms(1) sel pp bn
    by (auto simp: ns_unbounded_cond_def Let_def split: prod.splits)
  with bn have "bottleneck s e in_U p1 p2 = (- 1, is_flip, v, e0fwd, up_side)" by simp
  from assms(2)[OF sel pp this] show Q .
qed

lemma ns_unbounded_condI:
  "⟦ns_select s = Some (e, in_U, γ, sel');
    get_path_pair (spanning_tree s) (fst_exec e) (snd_exec e) = (p1, p2);
    bottleneck s e in_U p1 p2 = (- 1, is_flip, v, e0fwd, up_side)⟧ ⟹ ns_unbounded_cond s"
  by (auto simp: ns_unbounded_cond_def Let_def)

lemma ns_flip_condE:
  assumes "ns_flip_cond s"
    "⋀ e in_U γ sel' p1 p2 δ v e0fwd up_side.
       ⟦ns_select s = Some (e, in_U, γ, sel');
        get_path_pair (spanning_tree s) (fst_exec e) (snd_exec e) = (p1, p2);
        bottleneck s e in_U p1 p2 = (δ, True, v, e0fwd, up_side); δ ≠ - 1⟧ ⟹ Q"
  shows Q
proof -
  have "ns_select s ≠ None"
    using assms(1) by (auto simp: ns_flip_cond_def split: option.splits)
  then obtain e in_U γ sel' where sel: "ns_select s = Some (e, in_U, γ, sel')"
    by (metis prod_cases4 option.exhaust)
  obtain p1 p2 where pp: "get_path_pair (spanning_tree s) (fst_exec e) (snd_exec e) = (p1, p2)"
    by (metis prod.exhaust)
  obtain δ is_flip v e0fwd up_side
    where bn: "bottleneck s e in_U p1 p2 = (δ, is_flip, v, e0fwd, up_side)"
    by (metis prod_cases5)
  have fl: "δ ≠ - 1 ∧ is_flip"
    using assms(1) sel pp bn
    by (auto simp: ns_flip_cond_def Let_def split: prod.splits)
  from fl have dne: "δ ≠ - 1" by simp
  from fl bn have bn': "bottleneck s e in_U p1 p2 = (δ, True, v, e0fwd, up_side)" by simp
  from assms(2)[OF sel pp bn' dne] show Q .
qed

lemma ns_flip_condI:
  "⟦ns_select s = Some (e, in_U, γ, sel');
    get_path_pair (spanning_tree s) (fst_exec e) (snd_exec e) = (p1, p2);
    bottleneck s e in_U p1 p2 = (δ, True, v, e0fwd, up_side); δ ≠ - 1⟧ ⟹ ns_flip_cond s"
  by (auto simp: ns_flip_cond_def Let_def)

lemma ns_pivot_condE:
  assumes "ns_pivot_cond s"
    "⋀ e in_U γ sel' p1 p2 δ v e0fwd up_side.
       ⟦ns_select s = Some (e, in_U, γ, sel');
        get_path_pair (spanning_tree s) (fst_exec e) (snd_exec e) = (p1, p2);
        bottleneck s e in_U p1 p2 = (δ, False, v, e0fwd, up_side); δ ≠ - 1⟧ ⟹ Q"
  shows Q
proof -
  have "ns_select s ≠ None"
    using assms(1) by (auto simp: ns_pivot_cond_def split: option.splits)
  then obtain e in_U γ sel' where sel: "ns_select s = Some (e, in_U, γ, sel')"
    by (metis prod_cases4 option.exhaust)
  obtain p1 p2 where pp: "get_path_pair (spanning_tree s) (fst_exec e) (snd_exec e) = (p1, p2)"
    by (metis prod.exhaust)
  obtain δ is_flip v e0fwd up_side
    where bn: "bottleneck s e in_U p1 p2 = (δ, is_flip, v, e0fwd, up_side)"
    by (metis prod_cases5)
  have fl: "δ ≠ - 1 ∧ ¬ is_flip"
    using assms(1) sel pp bn
    by (auto simp: ns_pivot_cond_def Let_def split: prod.splits)
  from fl have dne: "δ ≠ - 1" by simp
  from fl bn have bn': "bottleneck s e in_U p1 p2 = (δ, False, v, e0fwd, up_side)" by simp
  from assms(2)[OF sel pp bn' dne] show Q .
qed

lemma ns_pivot_condI:
  "⟦ns_select s = Some (e, in_U, γ, sel');
    get_path_pair (spanning_tree s) (fst_exec e) (snd_exec e) = (p1, p2);
    bottleneck s e in_U p1 p2 = (δ, False, v, e0fwd, up_side); δ ≠ - 1⟧ ⟹ ns_pivot_cond s"
  by (auto simp: ns_pivot_cond_def Let_def)

lemma ns_loop_cases:
  assumes "ns_success_cond s ⟹ P"
          "ns_unbounded_cond s ⟹ P"
          "ns_flip_cond s ⟹ P"
          "ns_pivot_cond s ⟹ P"
  shows P
proof -
  have "ns_success_cond s ∨ ns_unbounded_cond s ∨ ns_flip_cond s ∨ ns_pivot_cond s"
    by (auto simp: ns_success_cond_def ns_unbounded_cond_def ns_flip_cond_def ns_pivot_cond_def
             Let_def split: option.splits prod.splits)
  thus P using assms by auto
qed

subsection ‹One-step unfolding and tailored induction›

lemma ns_loop_simps:
  assumes "ns_loop_dom s"
  shows "ns_success_cond s ⟹ ns_loop s = ns_optimal s"
        "ns_unbounded_cond s ⟹ ns_loop s = ns_unbounded_upd s"
        "ns_flip_cond s ⟹ ns_loop s = ns_loop (ns_flip_upd s)"
        "ns_pivot_cond s ⟹ ns_loop s = ns_loop (ns_pivot_upd s)"
proof (goal_cases)
  case 1
  thus ?case by (auto elim!: ns_success_condE simp: ns_loop.psimps[OF assms])
next
  case 2
  show ?case
  proof (rule ns_unbounded_condE[OF 2], goal_cases)
    case (1 e in_U γ sel' p1 p2)
    thus ?case by (auto simp: ns_loop.psimps[OF assms] Let_def)
  qed
next
  case 3
  show ?case
  proof (rule ns_flip_condE[OF 3], goal_cases)
    case (1 e in_U γ sel' p1 p2 δ)
    thus ?case by (auto simp: ns_loop.psimps[OF assms] ns_flip_upd_def Let_def)
  qed
next
  case 4
  show ?case
  proof (rule ns_pivot_condE[OF 4], goal_cases)
    case (1 e in_U γ sel' p1 p2 δ v e0fwd up_side)
    thus ?case by (auto simp: ns_loop.psimps[OF assms] ns_pivot_upd_def Let_def)
  qed
qed

lemma ns_loop_induct:
  assumes "ns_loop_dom s"
    "⋀ s. ⟦ns_loop_dom s;
            ns_flip_cond s ⟹ P (ns_flip_upd s);
            ns_pivot_cond s ⟹ P (ns_pivot_upd s)⟧ ⟹ P s"
  shows "P s"
proof (rule ns_loop.pinduct[OF assms(1)], goal_cases)
  case (1 s)
  note IH = this
  show ?case
  proof (rule assms(2)[OF IH(1)], goal_cases)
    case 1
    thus ?case
      using IH(2)
      by (auto elim!: ns_flip_condE[of s] simp: ns_flip_upd_def Let_def)
  next
    case 2
    thus ?case
      using IH(3)
      by (auto elim!: ns_pivot_condE[of s] simp: ns_pivot_upd_def Let_def)
  qed
qed

subsection ‹Agreement of the executable twin with the specification loop›

lemma ns_loop_dom_impl_same:
  assumes "ns_loop_dom s"
  shows "ns_loop_impl s = ns_loop s"
proof (induction rule: ns_loop_induct[OF assms])
  case (1 s)
  note IH = this
  show ?case
  proof (cases s rule: ns_loop_cases)
    case 1
    thus ?thesis
      by (auto elim!: ns_success_condE
               simp: ns_loop_impl.simps ns_loop.psimps[OF IH(1)])
  next
    case 2
    show ?thesis
    proof (rule ns_unbounded_condE[OF 2], goal_cases)
      case (1 e in_U γ sel' p1 p2)
      thus ?case
        by (simp add: ns_loop_impl.simps ns_loop.psimps[OF IH(1)])
    qed
  next
    case 3
    show ?thesis
    proof (rule ns_flip_condE[OF 3], goal_cases)
      case (1 e in_U γ sel' p1 p2 δ)
      have "ns_loop_impl s = ns_loop_impl (ns_flip_upd s)"
        using 1 by (subst ns_loop_impl.simps) (simp add: ns_flip_upd_def)
      also have "… = ns_loop (ns_flip_upd s)" using IH(2)[OF 3] .
      also have "… = ns_loop s" using ns_loop_simps(3)[OF IH(1) 3] by simp
      finally show ?case .
    qed
  next
    case 4
    show ?thesis
    proof (rule ns_pivot_condE[OF 4], goal_cases)
      case (1 e in_U γ sel' p1 p2 δ v e0fwd up_side)
      have "ns_loop_impl s = ns_loop_impl (ns_pivot_upd s)"
        using 1 by (subst ns_loop_impl.simps) (simp add: ns_pivot_upd_def)
      also have "… = ns_loop (ns_pivot_upd s)" using IH(3)[OF 4] .
      also have "… = ns_loop s" using ns_loop_simps(4)[OF IH(1) 4] by simp
      finally show ?case .
    qed
  qed
qed

lemma ns_loop_dom_impl_cong:
  assumes "ns_loop_dom s'" "s = s'"
  shows "ns_loop_impl s = ns_loop s'"
  using ns_loop_dom_impl_same assms by auto

subsection ‹Domain introduction rules›

lemma ns_loop_dom_success: "ns_success_cond s ⟹ ns_loop_dom s"
  by (auto elim!: ns_success_condE intro: ns_loop.domintros)

lemma ns_loop_dom_unbounded: "ns_unbounded_cond s ⟹ ns_loop_dom s"
  by (auto elim!: ns_unbounded_condE intro: ns_loop.domintros)

lemma ns_loop_dom_flip:
  "⟦ns_flip_cond s; ns_loop_dom (ns_flip_upd s)⟧ ⟹ ns_loop_dom s"
  by (auto intro: ns_loop.domintros simp: ns_flip_upd_def Let_def elim!: ns_flip_condE)

lemma ns_loop_dom_pivot:
  "⟦ns_pivot_cond s; ns_loop_dom (ns_pivot_upd s)⟧ ⟹ ns_loop_dom s"
  by (auto intro: ns_loop.domintros simp: ns_pivot_upd_def Let_def elim!: ns_pivot_condE)

lemma ns_loop_simps_without_dom:
  shows "ns_success_cond s ⟹ ns_loop s = ns_optimal s"
        "ns_unbounded_cond s ⟹ ns_loop s = ns_unbounded_upd s"
  using ns_loop_dom_success ns_loop_dom_unbounded ns_loop_simps by auto

section ‹Invariants of the loop state›

text ‹Abstract (verification-only) views of a program state @{term s}: the current flow as a plain
      real-valued function on edges, the potential as a real-valued function on vertices, the tree
      edge set @{term T} as the image of the parent-edge array over the non-root vertices, and the
      two edge sets @{term L} (zero-flow) and @{term U} (saturated).›

abbreviation "ns_flow_of s ≡ h ∘ flow_lookup (current_flow s)"
abbreviation "ns_pot_of s ≡ abstract_pot (potentials s)"
abbreviation "ns_tree_edges s ≡ parent_lookup (parent_edge s) ` (𝒱 - {r})"

text ‹The zero-flow (@{term L}) and saturated (@{term U}) edge sets, carved out of @{term ‹ℰ›} by the
      @{term edge_state} tag. These are kept as ∗‹definitions› (not abbreviations) so that they behave
      as opaque sets in the downstream cardinality/finiteness reasoning — exactly like the former
      ‹set_abstract›-based views; unfold ‹ns_L_of_def› / ‹ns_U_of_def› when the tag is actually needed.›

definition "ns_L_of s = {e ∈ ℰ. fst e ≠ snd e ∧ es_lookup (edge_state s) e = InL}"
definition "ns_U_of s = {e ∈ ℰ. fst e ≠ snd e ∧ es_lookup (edge_state s) e = InU}"

text ‹Self-loops are not classified by the tag array; for the spanning-tree partition they are folded
      back into @{term L} / @{term U} by cost: a non-negative-cost self-loop (which carries zero flow)
      sits in @{term L}, a negative-cost one (saturated) in @{term U}. These sets depend only on the
      static cost and edge set, so they are the same in every state.›

definition "ns_selfloops_L = {e ∈ ℰ. fst e = snd e ∧ 0 ≤ 𝖼 e}"
definition "ns_selfloops_U = {e ∈ ℰ. fst e = snd e ∧ 𝖼 e < 0}"

text ‹❙‹(1) Data-structure invariant.› Every store of the state is well-formed: the flow, parent-edge
      and direction arrays satisfy their array invariants, the potential store is @{term pot_valid}
      (array invariant plus well-formed abstract reals at every vertex), both edge sets and the
      selector satisfy their invariants, and the abstract spanning tree is a valid arborescence. As
      the array lookups are total and the key sets are fixed statically, no domain conditions are
      needed (unlike ‹implementation_invar› for Orlin's algorithm).›

definition "ns_invar_impl s ≡
  flow_invar (current_flow s) ∧
  pot_valid (potentials s) ∧
  parent_invar (parent_edge s) ∧
  dir_invar (edge_dir s) ∧
  es_invar (edge_state s) ∧
  sel_invar (edge_sel s) ∧
  arborescense_invar (spanning_tree s)"

text ‹❙‹(A) b-flow.› The current flow is a feasible @{term b}-flow: it respects the capacity bounds
      (@{term isuflow}, i.e. ‹0 ≤ f e ≤ 𝗎 e› on ∗‹every› edge) and conserves the balances @{term b}
      at every vertex. This is the invariant that was missing from the informal list; reusing the
      library's ‹_ is _ flow› predicate rather than ‹isuflow› supplies flow conservation on top of
      global feasibility.›

definition "ns_invar_bflow s ≡ (ns_flow_of s) is b flow"

text ‹❙‹(2) Spanning tree structure.› @{term ‹(r, T, L, U)›} is a spanning tree structure: the edge
      universe @{term ‹ℰ›} splits disjointly into the tree edges, @{term L} and @{term U}, and the
      tree edges form a spanning arborescence rooted at @{term r}.›

definition "ns_invar_partition s ≡
  spanning_tree_partition r (ns_tree_edges s)
    (ns_L_of s ∪ ns_selfloops_L) (ns_U_of s ∪ ns_selfloops_U)"

text ‹❙‹(5) Flow fits the structure.› Edges in @{term L} carry zero flow and edges in @{term U} are
      saturated.›

definition "ns_invar_flow_fits s ≡
  flow_fits_spanning_tree_partition (ns_tree_edges s) (ns_L_of s) (ns_U_of s) (ns_flow_of s)"

text ‹❙‹(4) Potential fits the structure.› The root has potential @{term 0} and every tree edge has
      zero reduced cost — the library's @{const potential_fits_spanning_tree_partition}, whose
      per-edge condition ‹𝖼 e + π (fst e) - π (snd e) = 0› is exactly ‹reduced_cost π e = 0›. This
      KV-standard convention matches the selector (@{term sel_select}) and the library's optimality
      certificate in .›

definition "ns_invar_pot_fits s ≡
  potential_fits_spanning_tree_partition r (ns_tree_edges s) (ns_pot_of s)"

text ‹❙‹(3) Strict feasibility on the tree.› The strict half that, together with the capacity bounds
      already supplied by @{term ns_invar_bflow}, upgrades feasibility to ∗‹strong› feasibility: an
      upward parent edge (pointing from the vertex to its parent, @{term ‹par_up s v›}) has flow
      strictly below its capacity, and a downward parent edge has strictly positive flow.›

definition "ns_invar_strict s ≡
  (∀ v ∈ 𝒱 - {r}.
     if par_up s v
     then ereal (h (flow_lookup (current_flow s) (par_edge s v))) < 𝗎 (par_edge s v)
     else flow_lookup (current_flow s) (par_edge s v) > 0)"

text ‹The parent vertex of a non-root vertex @{term v}: the endpoint of its parent edge other than
      @{term v}, read off through the stored orientation. By convention ‹par_up s v› holds iff the
      parent edge points from @{term v} to its parent, so the parent is ‹snd (par_edge s v)› when
      ‹par_up s v› and ‹fst (par_edge s v)› otherwise.›

definition "par_vx s v = (if par_up s v then snd (par_edge s v) else fst (par_edge s v))"

text ‹❙‹(C) Edge ↔ tree-edge correspondence.› The bridge tying the concrete @{term parent_edge} and
      @{term edge_dir} arrays to the abstract spanning tree. For every non-root vertex @{term v}:
      ▪ its parent edge is a genuine graph edge, ‹par_edge s v ∈ ℰ›;
      ▪ the direction flag agrees with @{term fst}/@{term snd}: @{term v} is the tail
        (‹fst (par_edge s v) = v›) exactly when ‹par_up s v›, i.e. the edge is oriented from @{term v}
        towards its parent iff the flag says so — this is what ∗‹brings @{term par_up}, @{term edge_dir}
        and the tree together›;
      ▪ the other endpoint ‹par_vx s v› is really @{term v}'s predecessor towards the root: the unique
        simple walk from @{term v} to @{term r} in the tree starts ‹v # par_vx s v # …›.
      The final conjunct states that the undirected projection of the parent edges is exactly the
      abstract arborescence, so the array view @{term ‹ns_tree_edges s›} and @{term ‹spanning_tree s›}
      denote the same tree.›

definition "ns_invar_tree s ≡
  (∀ v ∈ 𝒱 - {r}.
     par_edge s v ∈ ℰ
   ∧ (if par_up s v then fst (par_edge s v) = v else snd (par_edge s v) = v)
   ∧ (∃ q. distinct (v # par_vx s v # q)
           ∧ walk_betw (abstract_arborescense (spanning_tree s)) v (v # par_vx s v # q) r))
  ∧ (λ e. {fst e, snd e}) ` (ns_tree_edges s) = abstract_arborescense (spanning_tree s)"

text ‹Self-loops are outside the L/U/T tag classification (the array only classifies non-self-loops);
      they are folded into the partition's @{term L} / @{term U} sets by cost. This invariant fixes their
      ∗‹flow›: a non-negative-cost self-loop carries zero flow (so it belongs, at flow 0, in the
      partition's @{term L}) and a negative-cost one is saturated (so it belongs, at flow @{term ‹𝗎 e›},
      in @{term U}). A self-loop has reduced cost equal to its plain cost (the potentials cancel) and,
      since @{const entering_edge} now requires @{term ‹fst e ≠ snd e›}, a self-loop is never entering and
      never a tree edge, so its flow never changes and the classification is trivially preserved. This is
      what the pivot ever needed the old ‹no_self_loop› axiom for, and it supplies the complementary
      slackness of self-loops to the optimality certificate.›

definition "ns_invar_selfloop s ≡
  (∀ e ∈ ℰ. fst e = snd e ⟶
       (0 ≤ 𝖼 e ⟶ ns_flow_of s e = 0)
     ∧ (𝖼 e < 0 ⟶ ereal (ns_flow_of s e) = 𝗎 e))"

text ‹The overall loop invariant is the conjunction of the eight predicates above.›

definition "ns_invar s ≡
  ns_invar_impl s ∧ ns_invar_bflow s ∧ ns_invar_partition s ∧
  ns_invar_flow_fits s ∧ ns_invar_pot_fits s ∧ ns_invar_strict s ∧ ns_invar_tree s
  ∧ ns_invar_selfloop s"

subsection ‹Introduction, elimination and destruction rules›

text ‹❙‹(1) Data-structure invariant.››

lemma ns_invar_implI:
  "⟦flow_invar (current_flow s); pot_valid (potentials s); parent_invar (parent_edge s);
    dir_invar (edge_dir s); es_invar (edge_state s);
    sel_invar (edge_sel s); arborescense_invar (spanning_tree s)⟧
   ⟹ ns_invar_impl s"
  by (simp add: ns_invar_impl_def)

lemma ns_invar_implE:
  "ns_invar_impl s ⟹
     (⟦flow_invar (current_flow s); pot_valid (potentials s); parent_invar (parent_edge s);
        dir_invar (edge_dir s); es_invar (edge_state s);
        sel_invar (edge_sel s); arborescense_invar (spanning_tree s)⟧ ⟹ P) ⟹ P"
  by (simp add: ns_invar_impl_def)

lemma ns_invar_implD:
  "ns_invar_impl s ⟹ flow_invar (current_flow s)"
  "ns_invar_impl s ⟹ pot_valid (potentials s)"
  "ns_invar_impl s ⟹ parent_invar (parent_edge s)"
  "ns_invar_impl s ⟹ dir_invar (edge_dir s)"
  "ns_invar_impl s ⟹ es_invar (edge_state s)"
  "ns_invar_impl s ⟹ sel_invar (edge_sel s)"
  "ns_invar_impl s ⟹ arborescense_invar (spanning_tree s)"
  by (simp_all add: ns_invar_impl_def)

text ‹❙‹(A) b-flow.››

lemma ns_invar_bflowI: "(ns_flow_of s) is b flow ⟹ ns_invar_bflow s"
  by (simp add: ns_invar_bflow_def)

lemma ns_invar_bflowE: "ns_invar_bflow s ⟹ ((ns_flow_of s) is b flow ⟹ P) ⟹ P"
  by (simp add: ns_invar_bflow_def)

lemma ns_invar_bflowD: "ns_invar_bflow s ⟹ (ns_flow_of s) is b flow"
  by (simp add: ns_invar_bflow_def)

text ‹❙‹(2) Spanning tree structure.››

lemma ns_invar_partitionI:
  "spanning_tree_partition r (ns_tree_edges s)
     (ns_L_of s ∪ ns_selfloops_L) (ns_U_of s ∪ ns_selfloops_U) ⟹ ns_invar_partition s"
  by (simp add: ns_invar_partition_def)

lemma ns_invar_partitionE:
  "ns_invar_partition s ⟹
     (spanning_tree_partition r (ns_tree_edges s)
        (ns_L_of s ∪ ns_selfloops_L) (ns_U_of s ∪ ns_selfloops_U) ⟹ P) ⟹ P"
  by (simp add: ns_invar_partition_def)

lemma ns_invar_partitionD:
  "ns_invar_partition s ⟹ spanning_tree_partition r (ns_tree_edges s)
     (ns_L_of s ∪ ns_selfloops_L) (ns_U_of s ∪ ns_selfloops_U)"
  by (simp add: ns_invar_partition_def)

text ‹❙‹(5) Flow fits the structure.››

lemma ns_invar_flow_fitsI:
  "flow_fits_spanning_tree_partition (ns_tree_edges s) (ns_L_of s) (ns_U_of s) (ns_flow_of s)
     ⟹ ns_invar_flow_fits s"
  by (simp add: ns_invar_flow_fits_def)

lemma ns_invar_flow_fitsE:
  "ns_invar_flow_fits s ⟹
     (flow_fits_spanning_tree_partition (ns_tree_edges s) (ns_L_of s) (ns_U_of s) (ns_flow_of s)
        ⟹ P) ⟹ P"
  by (simp add: ns_invar_flow_fits_def)

lemma ns_invar_flow_fitsD:
  "ns_invar_flow_fits s
     ⟹ flow_fits_spanning_tree_partition (ns_tree_edges s) (ns_L_of s) (ns_U_of s) (ns_flow_of s)"
  by (simp add: ns_invar_flow_fits_def)

text ‹❙‹(4) Potential fits the structure.››

lemma ns_invar_pot_fitsI:
  "potential_fits_spanning_tree_partition r (ns_tree_edges s) (ns_pot_of s) ⟹ ns_invar_pot_fits s"
  by (simp add: ns_invar_pot_fits_def)

lemma ns_invar_pot_fitsE:
  "ns_invar_pot_fits s ⟹
     (potential_fits_spanning_tree_partition r (ns_tree_edges s) (ns_pot_of s) ⟹ P) ⟹ P"
  by (simp add: ns_invar_pot_fits_def)

lemma ns_invar_pot_fitsD:
  "ns_invar_pot_fits s ⟹ potential_fits_spanning_tree_partition r (ns_tree_edges s) (ns_pot_of s)"
  by (simp add: ns_invar_pot_fits_def)

text ‹❙‹(3) Strict feasibility on the tree.› The per-vertex destruction rule yields the @{term If}
      condition; @{term ns_invar_strict_upD} / @{term ns_invar_strict_downD} project onto the two
      orientations.›

lemma ns_invar_strictI:
  assumes "⋀v. v ∈ 𝒱 - {r} ⟹
              (if par_up s v
               then ereal (h (flow_lookup (current_flow s) (par_edge s v))) < 𝗎 (par_edge s v)
               else flow_lookup (current_flow s) (par_edge s v) > 0)"
  shows "ns_invar_strict s"
  using assms by (auto simp add: ns_invar_strict_def)

lemma ns_invar_strictE:
  assumes "ns_invar_strict s"
    and "(⋀v. v ∈ 𝒱 - {r} ⟹
             (if par_up s v
              then ereal (h (flow_lookup (current_flow s) (par_edge s v))) < 𝗎 (par_edge s v)
              else flow_lookup (current_flow s) (par_edge s v) > 0)) ⟹ P"
  shows P
  using assms by (auto simp add: ns_invar_strict_def)

lemma ns_invar_strictD:
  assumes "ns_invar_strict s" "v ∈ 𝒱 - {r}"
  shows "if par_up s v
         then ereal (h (flow_lookup (current_flow s) (par_edge s v))) < 𝗎 (par_edge s v)
         else flow_lookup (current_flow s) (par_edge s v) > 0"
  using assms by (auto simp add: ns_invar_strict_def)

lemma ns_invar_strict_upD:
  assumes "ns_invar_strict s" "v ∈ 𝒱 - {r}" "par_up s v"
  shows "ereal (h (flow_lookup (current_flow s) (par_edge s v))) < 𝗎 (par_edge s v)"
  using ns_invar_strictD[OF assms(1,2)] assms(3) by simp

lemma ns_invar_strict_downD:
  assumes "ns_invar_strict s" "v ∈ 𝒱 - {r}" "¬ par_up s v"
  shows "flow_lookup (current_flow s) (par_edge s v) > 0"
  using ns_invar_strictD[OF assms(1,2)] assms(3) by simp

text ‹❙‹(C) Edge ↔ tree-edge correspondence.› @{term ns_invar_tree_vertexD} gives the per-vertex
      conjunction, @{term ns_invar_tree_edgesD} the tree-set equality; the remaining destruction
      rules project the per-vertex conjunction onto its three components.›

lemma ns_invar_treeI:
  assumes "⋀v. v ∈ 𝒱 - {r} ⟹
              par_edge s v ∈ ℰ
            ∧ (if par_up s v then fst (par_edge s v) = v else snd (par_edge s v) = v)
            ∧ (∃q. distinct (v # par_vx s v # q)
                   ∧ walk_betw (abstract_arborescense (spanning_tree s)) v (v # par_vx s v # q) r)"
    and "(λe. {fst e, snd e}) ` (ns_tree_edges s) = abstract_arborescense (spanning_tree s)"
  shows "ns_invar_tree s"
  using assms by (auto simp add: ns_invar_tree_def)

lemma ns_invar_treeE:
  assumes "ns_invar_tree s"
    and "(⟦⋀v. v ∈ 𝒱 - {r} ⟹
              par_edge s v ∈ ℰ
            ∧ (if par_up s v then fst (par_edge s v) = v else snd (par_edge s v) = v)
            ∧ (∃q. distinct (v # par_vx s v # q)
                   ∧ walk_betw (abstract_arborescense (spanning_tree s)) v (v # par_vx s v # q) r);
          (λe. {fst e, snd e}) ` (ns_tree_edges s) = abstract_arborescense (spanning_tree s)⟧ ⟹ P)"
  shows P
  using assms by (auto simp add: ns_invar_tree_def)

lemma ns_invar_tree_vertexD:
  assumes "ns_invar_tree s" "v ∈ 𝒱 - {r}"
  shows "par_edge s v ∈ ℰ
       ∧ (if par_up s v then fst (par_edge s v) = v else snd (par_edge s v) = v)
       ∧ (∃q. distinct (v # par_vx s v # q)
              ∧ walk_betw (abstract_arborescense (spanning_tree s)) v (v # par_vx s v # q) r)"
  using assms by (auto simp add: ns_invar_tree_def)

lemma ns_invar_tree_edgesD:
  "ns_invar_tree s
     ⟹ (λe. {fst e, snd e}) ` (ns_tree_edges s) = abstract_arborescense (spanning_tree s)"
  by (simp add: ns_invar_tree_def)

lemma ns_invar_tree_edgeD:
  "⟦ns_invar_tree s; v ∈ 𝒱 - {r}⟧ ⟹ par_edge s v ∈ ℰ"
  using ns_invar_tree_vertexD by blast

lemma ns_invar_tree_dirD:
  "⟦ns_invar_tree s; v ∈ 𝒱 - {r}⟧
     ⟹ (if par_up s v then fst (par_edge s v) = v else snd (par_edge s v) = v)"
  using ns_invar_tree_vertexD by blast

lemma ns_invar_tree_walkD:
  "⟦ns_invar_tree s; v ∈ 𝒱 - {r}⟧
     ⟹ (∃q. distinct (v # par_vx s v # q)
             ∧ walk_betw (abstract_arborescense (spanning_tree s)) v (v # par_vx s v # q) r)"
  using ns_invar_tree_vertexD by blast

text ‹❙‹The overall loop invariant.››

lemma ns_invarI:
  "⟦ns_invar_impl s; ns_invar_bflow s; ns_invar_partition s; ns_invar_flow_fits s;
    ns_invar_pot_fits s; ns_invar_strict s; ns_invar_tree s; ns_invar_selfloop s⟧ ⟹ ns_invar s"
  by (simp add: ns_invar_def)

lemma ns_invarE:
  "ns_invar s ⟹
     (⟦ns_invar_impl s; ns_invar_bflow s; ns_invar_partition s; ns_invar_flow_fits s;
        ns_invar_pot_fits s; ns_invar_strict s; ns_invar_tree s; ns_invar_selfloop s⟧ ⟹ P) ⟹ P"
  by (simp add: ns_invar_def)

lemma ns_invarD:
  "ns_invar s ⟹ ns_invar_impl s"
  "ns_invar s ⟹ ns_invar_bflow s"
  "ns_invar s ⟹ ns_invar_partition s"
  "ns_invar s ⟹ ns_invar_flow_fits s"
  "ns_invar s ⟹ ns_invar_pot_fits s"
  "ns_invar s ⟹ ns_invar_strict s"
  "ns_invar s ⟹ ns_invar_tree s"
  "ns_invar s ⟹ ns_invar_selfloop s"
  by (simp_all add: ns_invar_def)

end

end