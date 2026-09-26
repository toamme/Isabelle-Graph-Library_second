theory Matroid_Weighted_Intersection_Algorithm
  imports Matroid_Weighted_Intersection Matroid_Intersection_Algorithm
begin

section \<open>Weighted Matroid Intersection Algorithm\<close>

text \<open>A formalisation skeleton of Frank's primal-dual weighted matroid intersection algorithm
(Korte--Vygen, Section 13.7), following the same ADT/locale template as the unweighted
\<open>Matroid_Intersection_Algorithm\<close>.

As in the unweighted development two algorithm variants share one pair of locales:
\<^item> the \<open>plain\<close> version probes each single swap \<open>X - {x} + y\<close> via the independence oracle;
\<^item> the \<open>circuit\<close> version reads off the whole fundamental circuit at once.

The weighted algorithm additionally maintains a weight split \<open>c = c1 + c2\<close> in the state, works in the
weight-induced tight subgraph \<open>Gbar\<close> with maximum-weight endpoints \<open>Sbar\<close>, \<open>Tbar\<close>, and, when no tight
augmenting path exists, reweights on the reachable set \<open>R\<close> by \<open>\<epsilon>\<close> instead of stopping.  The
augmenting path is a \<^emph>\<open>minimum-number-of-edges\<close> (unweighted / BFS) shortest path, but sought inside
the tight subgraph \<open>Gbar\<close>; the weighting is handled by restricting the graph to tight arcs, so the
plain \<open>find_path\<close> oracle is exactly what \<open>augment_tight_path\<close> requires.

Everything is kept behind abstract data types.  In particular the two split weights (and the fixed
original weight) are values of an abstract \<^emph>\<open>weight-map\<close> type \<open>'cmap\<close>, accessed through the executable
operations \<open>c_lookup\<close> (a single weight, used for the tightness tests), \<open>c_shift\<close> (the reweighting
step) and \<open>c_zero\<close> (the zero split), together with the aggregate oracles \<open>weight_Max\<close>,
\<open>restrict_to_max\<close>, \<open>eps\<close> and \<open>weight\<close>; \<open>c_invar\<close> is the data-structure invariant and \<open>c_lookup\<close>
doubles as the abstraction to the mathematical weight function \<^typ>\<open>'a \<Rightarrow> real\<close>.  The value type is
fixed to \<^typ>\<open>real\<close>; the snapshot lemmas of \<open>Matroid_Weighted_Intersection\<close> are polymorphic over
\<^class>\<open>linordered_ab_group_add\<close> and instantiate at \<^typ>\<open>real\<close>.\<close>

subsection \<open>State\<close>

text \<open>The state carries the current common independent set \<open>wsol\<close>, the current split \<open>wc1\<close>/\<open>wc2\<close>
(both weight maps, whose lookups sum to the invariant original weight), the fixed original weight
\<open>worig\<close> (used only to compare candidate solutions), and the best-weight common independent set
\<open>wbest\<close> seen so far.\<close>

record ('sol, 'cmap) weighted_intersec_state =
  wsol  :: 'sol
  wc1   :: 'cmap
  wc2   :: 'cmap
  worig :: 'cmap
  wbest :: 'sol

lemma wsol_remove: "wsol (state \<lparr> wsol := new \<rparr>) = new"
  by auto

subsection \<open>Executable specification locale (both variants)\<close>

text \<open>Extends the unweighted spec locale, thereby reusing every graph/set ADT operation and the
unweighted \<open>compute_graph\<close>/\<open>compute_graph_circuit\<close>/\<open>augment\<close> definitions, and adds the weight-map
ADT together with the weight-specific oracles.\<close>

locale weighted_intersection_spec =
  unweighted_intersection_spec where insert = "insert :: 'a \<Rightarrow> 'vset \<Rightarrow> 'vset"
    and lookup = "lookup :: 'adjmap \<Rightarrow> 'a \<Rightarrow> 'vset option"
    and set_insert = "set_insert :: 'a \<Rightarrow> 'mset \<Rightarrow> 'mset"
    and complement = "complement :: 'mset \<Rightarrow> 'mset_red"
  for insert lookup set_insert complement +
  fixes c_lookup :: "'cmap \<Rightarrow> 'a \<Rightarrow> real"
    and c_invar :: "'cmap \<Rightarrow> bool"
    and c_shift :: "'vset \<Rightarrow> real \<Rightarrow> 'cmap \<Rightarrow> 'cmap"
    and c_zero :: "'cmap"
    and weight_Max :: "'vset \<Rightarrow> 'cmap \<Rightarrow> real"
    and restrict_to_max :: "'vset \<Rightarrow> 'cmap \<Rightarrow> 'vset"
    and reach_set :: "'vset \<Rightarrow> 'adjmap \<Rightarrow> 'vset"
    and weight :: "'cmap \<Rightarrow> 'mset \<Rightarrow> real"
    \<comment> \<open>the two set-folds with a running-\<open>min\<close> accumulator, used to \<^emph>\<open>compute\<close> \<open>\<epsilon>\<close>; they are
      \<open>inner_fold\<close>/\<open>outer_fold\<close> at the accumulator type \<^typ>\<open>real option\<close> (\<^const>\<open>None\<close> = \<open>\<infinity>\<close>)\<close>
    and eps_fold :: "'mset \<Rightarrow> ('a \<Rightarrow> real option \<Rightarrow> real option) \<Rightarrow> real option \<Rightarrow> real option"
    and eps_fold_red :: "'mset_red \<Rightarrow> ('a \<Rightarrow> real option \<Rightarrow> real option) \<Rightarrow> real option \<Rightarrow> real option"
begin

subsubsection \<open>Tight auxiliary graph -- plain version\<close>

text \<open>Like the unweighted \<open>treat1\<close>/\<open>treat2\<close>, but an arc is kept only when its endpoints have equal
weight (looked up through \<open>c_lookup\<close>), so the resulting graph abstracts to the tight subgraph
\<open>Gbar\<close>.\<close>

definition "treat1_tight y X c init_map =
  inner_fold X (\<lambda> x current_map. if weak_orcl1 y (set_delete x X) \<and> c_lookup c x = c_lookup c y
                                 then graph.add_edge current_map x y
                                 else current_map) init_map"

definition "treat2_tight y X c init_map =
  inner_fold X (\<lambda> x current_map. if weak_orcl2 y (set_delete x X) \<and> c_lookup c y = c_lookup c x
                                 then graph.add_edge current_map y x
                                 else current_map) init_map"

definition "compute_tight_graph X c1 c2 E_without_X =
  snd (snd (outer_fold E_without_X (\<lambda> y (SX, TX, current_map).
     let (SX, TX, current_map) = (if weak_orcl1 y X then (SX, TX, current_map)
                                  else (SX, TX, treat1_tight y X c1 current_map));
         (SX, TX, current_map) = (if weak_orcl2 y X then (SX, TX, current_map)
                                  else (SX, TX, treat2_tight y X c2 current_map))
     in (SX, TX, current_map)) (vset_empty, vset_empty, empty)))"

subsubsection \<open>Tight auxiliary graph -- circuit version\<close>

definition "treat1_circuit_tight y C c init_map =
  inner_fold_circuit C (\<lambda> x current_map. if c_lookup c x = c_lookup c y
                                          then graph.add_edge current_map x y
                                          else current_map) init_map"

definition "treat2_circuit_tight y C c init_map =
  inner_fold_circuit C (\<lambda> x current_map. if c_lookup c y = c_lookup c x
                                          then graph.add_edge current_map y x
                                          else current_map) init_map"

definition "compute_tight_graph_circuit X c1 c2 E_without_X =
  snd (snd (outer_fold E_without_X (\<lambda> y (SX, TX, current_map).
     let (SX, TX, current_map) = (if weak_orcl1 y X then (SX, TX, current_map)
                                  else (SX, TX, treat1_circuit_tight y (circuit1 y X) c1 current_map));
         (SX, TX, current_map) = (if weak_orcl2 y X then (SX, TX, current_map)
                                  else (SX, TX, treat2_circuit_tight y (circuit2 y X) c2 current_map))
     in (SX, TX, current_map)) (vset_empty, vset_empty, empty)))"

subsubsection \<open>Computing \<open>\<epsilon>\<close> (naive, following Frank)\<close>

text \<open>\<open>\<epsilon> = min(\<epsilon>\<^sub>1,\<epsilon>\<^sub>2,\<epsilon>\<^sub>3,\<epsilon>\<^sub>4)\<close> as a \<^typ>\<open>real option\<close> (\<^const>\<open>None\<close> = \<open>\<infinity>\<close>), computed by folding the
complement \<open>carrier - X\<close>: each \<open>y\<close> contributes its \<open>S\<close>/\<open>T\<close> endpoint gap (\<open>\<epsilon>\<^sub>3\<close>/\<open>\<epsilon>\<^sub>4\<close>) and, when \<open>y\<close> is not
addable, the gaps of its arcs crossing the boundary of \<open>R\<close> (\<open>\<epsilon>\<^sub>1\<close>/\<open>\<epsilon>\<^sub>2\<close>).  This is the \<^emph>\<open>naive\<close> version
(it examines every arc); the frontier/potential refinement is future work.  Membership \<open>y \<in>\<^sub>G R\<close> is
the \<open>O(log n)\<close> vset lookup.\<close>

definition "eps_min a v = (case a of None \<Rightarrow> Some v | Some w \<Rightarrow> Some (min w v))"

text \<open>Basic facts about the running minimum \<open>eps_min\<close>, and a generic positivity lemma for the folds
that build \<open>\<epsilon>\<close>: if the seed and every contributed gap are positive, the fold's result is positive.\<close>

lemma eps_min_le:
  fixes v :: "'b :: linorder"
  shows "eps_min a v = Some w \<Longrightarrow> w \<le> v \<and> (\<forall>u. a = Some u \<longrightarrow> w \<le> u)"
  by (cases a) (auto simp add: eps_min_def)

lemma eps_min_pos:
  "0 < v \<Longrightarrow> (\<forall>u. a = Some u \<longrightarrow> 0 < u) \<Longrightarrow> (\<forall>w. eps_min a v = Some w \<longrightarrow> 0 < w)"
  by (auto simp add: eps_min_def min_def split: option.splits)

lemma foldr_eps_pos:
  assumes "\<forall>w. a = Some w \<longrightarrow> 0 < w"
    "\<And>y acc. (\<forall>w. acc = Some w \<longrightarrow> 0 < w) \<Longrightarrow> (\<forall>w. body y acc = Some w \<longrightarrow> 0 < w)"
  shows "\<forall>w. foldr body ys a = Some w \<longrightarrow> 0 < w"
  using assms by (induction ys) auto

text \<open>\<open>eps_of A a\<close> folds a whole (finite) set of candidate gaps \<open>A\<close> into the accumulator \<open>a\<close> at once;
\<open>eps_min\<close> is its singleton case and sequential folds just union their sets. This turns any of the
\<open>compute_eps\<close> folds into the minimum of the abstract set of gaps it ranges over.\<close>

definition "eps_of A a = (if A = {} then a
   else (case a of None \<Rightarrow> Some (Min A) | Some w \<Rightarrow> Some (min w (Min A))))"

lemma eps_of_empty[simp]: "eps_of {} a = a"
  by (simp add: eps_of_def)

lemma eps_of_None: "eps_of A None = (if A = {} then None else Some (Min A))"
  by (simp add: eps_of_def)

lemma eps_of_single: "eps_min a v = eps_of {v} a"
  by (simp add: eps_of_def eps_min_def split: option.splits)

lemma eps_of_Un:
  fixes A B :: "'b :: linorder set"
  assumes "finite A" "finite B"
  shows "eps_of A (eps_of B a) = eps_of (A \<union> B) a"
proof (cases "A = {} \<or> B = {}")
  case True thus ?thesis by (auto simp add: Un_commute)
next
  case False
  hence "Min (A \<union> B) = min (Min A) (Min B)" using assms by (simp add: Min_Un)
  thus ?thesis using assms False
    by (auto simp add: eps_of_def min.assoc min.left_commute min.commute split: option.splits)
qed

lemma foldr_eps_of:
  fixes g :: "'a \<Rightarrow> 'b :: linorder"
  shows "foldr (\<lambda>x acc. if P x then eps_min acc (g x) else acc) xs a
           = eps_of (g ` {x \<in> set xs. P x}) a"
proof (induction xs)
  case (Cons x xs)
  show ?case
  proof (cases "P x")
    case True
    have set_eq: "g ` {y \<in> set (x # xs). P y} = Set.insert (g x) (g ` {y \<in> set xs. P y})"
      using True by auto
    have "foldr (\<lambda>x acc. if P x then eps_min acc (g x) else acc) (x # xs) a
            = eps_min (eps_of (g ` {y \<in> set xs. P y}) a) (g x)"
      using True Cons by simp
    also have "... = eps_of (Set.insert (g x) (g ` {y \<in> set xs. P y})) a"
      by (subst eps_of_single, subst eps_of_Un) auto
    finally show ?thesis by (simp add: set_eq[symmetric])
  next
    case False
    hence "g ` {y \<in> set (x # xs). P y} = g ` {y \<in> set xs. P y}" by auto
    thus ?thesis using False Cons by simp
  qed
qed simp

lemma foldr_eps_of_gen:
  fixes G :: "'a \<Rightarrow> 'b :: linorder set"
  assumes "\<And>y acc. body y acc = eps_of (G y) acc" "\<And>y. finite (G y)"
  shows "foldr body ys a = eps_of (\<Union>y \<in> set ys. G y) a"
proof (induction ys)
  case (Cons y ys)
  have "foldr body (y # ys) a = eps_of (G y) (foldr body ys a)"
    by (simp add: assms(1))
  also have "... = eps_of (G y) (eps_of (\<Union>z \<in> set ys. G z) a)"
    by (simp add: Cons)
  also have "... = eps_of (G y \<union> (\<Union>z \<in> set ys. G z)) a"
    using assms(2) by (subst eps_of_Un) auto
  finally show ?case by simp
qed simp

text \<open>Circuit variant: the arcs of \<open>y\<close> are read off its fundamental circuits \<open>circuit1/2 y X\<close>.\<close>
definition "compute_eps_circuit X m1 m2 R c1 c2 =
  eps_fold_red (complement X) (\<lambda> y acc.
    let acc = (if weak_orcl1 y X
               then (if y \<in>\<^sub>G R then acc else eps_min acc (m1 - c_lookup c1 y))
               else (if y \<in>\<^sub>G R then acc
                     else eps_fold_red (circuit1 y X)
                            (\<lambda> x acc. if x \<in>\<^sub>G R then eps_min acc (c_lookup c1 x - c_lookup c1 y) else acc) acc));
        acc = (if weak_orcl2 y X
               then (if y \<in>\<^sub>G R then eps_min acc (m2 - c_lookup c2 y) else acc)
               else (if y \<in>\<^sub>G R
                     then eps_fold_red (circuit2 y X)
                            (\<lambda> x acc. if x \<notin>\<^sub>G R then eps_min acc (c_lookup c2 x - c_lookup c2 y) else acc) acc
                     else acc))
    in acc) None"

text \<open>Plain variant: the arcs of \<open>y\<close> are found by probing \<open>weak_orcl\<close> over each \<open>x \<in> X\<close>.\<close>
definition "compute_eps X m1 m2 R c1 c2 =
  eps_fold_red (complement X) (\<lambda> y acc.
    let acc = (if weak_orcl1 y X
               then (if y \<in>\<^sub>G R then acc else eps_min acc (m1 - c_lookup c1 y))
               else (if y \<in>\<^sub>G R then acc
                     else eps_fold X
                            (\<lambda> x acc. if weak_orcl1 y (set_delete x X) \<and> x \<in>\<^sub>G R
                                      then eps_min acc (c_lookup c1 x - c_lookup c1 y) else acc) acc));
        acc = (if weak_orcl2 y X
               then (if y \<in>\<^sub>G R then eps_min acc (m2 - c_lookup c2 y) else acc)
               else (if y \<in>\<^sub>G R
                     then eps_fold X
                            (\<lambda> x acc. if weak_orcl2 y (set_delete x X) \<and> x \<notin>\<^sub>G R
                                      then eps_min acc (c_lookup c2 x - c_lookup c2 y) else acc) acc
                     else acc))
    in acc) None"

subsubsection \<open>Reweighting and best-so-far bookkeeping\<close>

text \<open>Step \<open>8\<close> of the algorithm: decrease \<open>c1\<close> by \<open>\<epsilon>\<close> and increase \<open>c2\<close> by \<open>\<epsilon>\<close> on the reachable
set \<open>R\<close> (keeping the split's sum -- the original weight \<open>worig\<close> -- invariant).\<close>
definition "reweight R e st =
  st \<lparr> wc1 := c_shift R (- e) (wc1 st), wc2 := c_shift R e (wc2 st) \<rparr>"

text \<open>Retain whichever of the current best and the freshly augmented set has larger original weight.\<close>
definition "keep_better st Y =
  (if weight (worig st) (wbest st) \<le> weight (worig st) Y then Y else wbest st)"

subsubsection \<open>Main loops\<close>

text \<open>One iteration: build the full auxiliary graph (for \<open>S\<close>, \<open>T\<close> and \<open>\<epsilon>\<close>) and the tight subgraph
(for reachability and the shortest tight path).  If a tight \<open>Sbar\<close>-\<open>Tbar\<close> path exists, augment;
otherwise either reweight (\<open>\<epsilon> < \<infinity>\<close>) or stop (\<open>\<epsilon> = \<infinity>\<close>, i.e. \<open>T\<close> unreachable from \<open>S\<close> in the full
graph).\<close>

function (domintros) weighted_matroid_intersection ::
  "('mset, 'cmap) weighted_intersec_state \<Rightarrow> ('mset, 'cmap) weighted_intersec_state" where
  "weighted_matroid_intersection st =
 (let X = wsol st; c1 = wc1 st; c2 = wc2 st;
      (SX, TX, G) = compute_graph X (complement X);
      SbarX = restrict_to_max SX c1;
      TbarX = restrict_to_max TX c2;
      Gtight = compute_tight_graph X c1 c2 (complement X);
      R = reach_set SbarX Gtight
  in (case find_path SbarX TbarX Gtight of
        Some p \<Rightarrow> weighted_matroid_intersection
                    (st \<lparr> wsol := augment X p, wbest := keep_better st (augment X p) \<rparr>)
      | None \<Rightarrow> (case compute_eps X (weight_Max SX c1) (weight_Max TX c2) R c1 c2 of
                   None \<Rightarrow> st
                 | Some e \<Rightarrow> weighted_matroid_intersection (reweight R e st))))"
  by pat_completeness auto

text \<open>The two recursing branches (a tight augmenting path exists, or none exists but \<open>\<epsilon> < \<infinity>\<close>) and
the terminating branch (no path and \<open>\<epsilon> = \<infinity>\<close>), following the unweighted \<open>recurse_cond\<close>/\<open>_upd\<close> pattern.\<close>

definition "weighted_augment_cond st =
 (let X = wsol st; c1 = wc1 st; c2 = wc2 st;
      (SX, TX, G) = compute_graph X (complement X);
      SbarX = restrict_to_max SX c1; TbarX = restrict_to_max TX c2;
      Gtight = compute_tight_graph X c1 c2 (complement X)
  in (case find_path SbarX TbarX Gtight of None \<Rightarrow> False | Some p \<Rightarrow> True))"

definition "weighted_reweight_cond st =
 (let X = wsol st; c1 = wc1 st; c2 = wc2 st;
      (SX, TX, G) = compute_graph X (complement X);
      SbarX = restrict_to_max SX c1; TbarX = restrict_to_max TX c2;
      Gtight = compute_tight_graph X c1 c2 (complement X);
      R = reach_set SbarX Gtight
  in (case find_path SbarX TbarX Gtight of None \<Rightarrow>
        (case compute_eps X (weight_Max SX c1) (weight_Max TX c2) R c1 c2 of
           None \<Rightarrow> False | Some e \<Rightarrow> True)
      | Some p \<Rightarrow> False))"

definition "weighted_stop_cond st =
 (let X = wsol st; c1 = wc1 st; c2 = wc2 st;
      (SX, TX, G) = compute_graph X (complement X);
      SbarX = restrict_to_max SX c1; TbarX = restrict_to_max TX c2;
      Gtight = compute_tight_graph X c1 c2 (complement X);
      R = reach_set SbarX Gtight
  in (case find_path SbarX TbarX Gtight of None \<Rightarrow>
        (case compute_eps X (weight_Max SX c1) (weight_Max TX c2) R c1 c2 of
           None \<Rightarrow> True | Some e \<Rightarrow> False)
      | Some p \<Rightarrow> False))"

definition "weighted_augment_upd st =
 (let X = wsol st; c1 = wc1 st; c2 = wc2 st;
      (SX, TX, G) = compute_graph X (complement X);
      SbarX = restrict_to_max SX c1; TbarX = restrict_to_max TX c2;
      Gtight = compute_tight_graph X c1 c2 (complement X);
      p = the (find_path SbarX TbarX Gtight)
  in st \<lparr> wsol := augment X p, wbest := keep_better st (augment X p) \<rparr>)"

definition "weighted_reweight_upd st =
 (let X = wsol st; c1 = wc1 st; c2 = wc2 st;
      (SX, TX, G) = compute_graph X (complement X);
      SbarX = restrict_to_max SX c1; TbarX = restrict_to_max TX c2;
      Gtight = compute_tight_graph X c1 c2 (complement X);
      R = reach_set SbarX Gtight;
      e = the (compute_eps X (weight_Max SX c1) (weight_Max TX c2) R c1 c2)
  in reweight R e st)"

lemma P_of_weighted_augmentI:
  "weighted_augment_cond st \<Longrightarrow>
   (\<And> SX TX G SbarX TbarX Gtight p X c1 c2.
       X = wsol st \<Longrightarrow> c1 = wc1 st \<Longrightarrow> c2 = wc2 st \<Longrightarrow>
       compute_graph X (complement X) = (SX, TX, G) \<Longrightarrow>
       SbarX = restrict_to_max SX c1 \<Longrightarrow> TbarX = restrict_to_max TX c2 \<Longrightarrow>
       Gtight = compute_tight_graph X c1 c2 (complement X) \<Longrightarrow>
       find_path SbarX TbarX Gtight = Some p \<Longrightarrow>
       P (st \<lparr> wsol := augment X p, wbest := keep_better st (augment X p) \<rparr>))
   \<Longrightarrow> P (weighted_augment_upd st)"
  unfolding weighted_augment_cond_def weighted_augment_upd_def Let_def
  apply(cases "compute_graph (wsol st) (complement (wsol st))", simp)
  subgoal for a b c
    by(cases "find_path (restrict_to_max a (wc1 st)) (restrict_to_max b (wc2 st))
                        (compute_tight_graph (wsol st) (wc1 st) (wc2 st) (complement (wsol st)))") auto
  done

lemma P_of_weighted_reweightI:
  "weighted_reweight_cond st \<Longrightarrow>
   (\<And> SX TX G SbarX TbarX Gtight R e X c1 c2.
       X = wsol st \<Longrightarrow> c1 = wc1 st \<Longrightarrow> c2 = wc2 st \<Longrightarrow>
       compute_graph X (complement X) = (SX, TX, G) \<Longrightarrow>
       SbarX = restrict_to_max SX c1 \<Longrightarrow> TbarX = restrict_to_max TX c2 \<Longrightarrow>
       Gtight = compute_tight_graph X c1 c2 (complement X) \<Longrightarrow>
       R = reach_set SbarX Gtight \<Longrightarrow>
       find_path SbarX TbarX Gtight = None \<Longrightarrow>
       compute_eps X (weight_Max SX c1) (weight_Max TX c2) R c1 c2 = Some e \<Longrightarrow>
       P (reweight R e st))
   \<Longrightarrow> P (weighted_reweight_upd st)"
  unfolding weighted_reweight_cond_def weighted_reweight_upd_def Let_def
  apply(cases "compute_graph (wsol st) (complement (wsol st))", simp)
  subgoal for a b c
    apply(cases "find_path (restrict_to_max a (wc1 st)) (restrict_to_max b (wc2 st))
                          (compute_tight_graph (wsol st) (wc1 st) (wc2 st) (complement (wsol st)))")
     apply(cases "compute_eps (wsol st) (weight_Max a (wc1 st)) (weight_Max b (wc2 st))
                    (reach_set (restrict_to_max a (wc1 st))
                       (compute_tight_graph (wsol st) (wc1 st) (wc2 st) (complement (wsol st))))
                    (wc1 st) (wc2 st)")
    by auto
  done

lemma weighted_matroid_intersection_cases:
  "(weighted_stop_cond st \<Longrightarrow> P) \<Longrightarrow>
   (weighted_augment_cond st \<Longrightarrow> P) \<Longrightarrow>
   (weighted_reweight_cond st \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding weighted_stop_cond_def weighted_augment_cond_def weighted_reweight_cond_def Let_def
  apply(cases "compute_graph (wsol st) (complement (wsol st))")
  subgoal for a b c
    apply(cases "find_path (restrict_to_max a (wc1 st)) (restrict_to_max b (wc2 st))
                          (compute_tight_graph (wsol st) (wc1 st) (wc2 st) (complement (wsol st)))")
     apply(cases "compute_eps (wsol st) (weight_Max a (wc1 st)) (weight_Max b (wc2 st))
                    (reach_set (restrict_to_max a (wc1 st))
                       (compute_tight_graph (wsol st) (wc1 st) (wc2 st) (complement (wsol st))))
                    (wc1 st) (wc2 st)")
    by auto
  done

lemma weighted_matroid_intersection_simps:
  assumes "weighted_matroid_intersection_dom st"
  shows "weighted_stop_cond st \<Longrightarrow> weighted_matroid_intersection st = st"
    and "weighted_augment_cond st \<Longrightarrow>
           weighted_matroid_intersection st = weighted_matroid_intersection (weighted_augment_upd st)"
    and "weighted_reweight_cond st \<Longrightarrow>
           weighted_matroid_intersection st = weighted_matroid_intersection (weighted_reweight_upd st)"
  by(auto intro: P_of_weighted_augmentI P_of_weighted_reweightI
      simp add: weighted_matroid_intersection.psimps[OF assms]
        weighted_stop_cond_def weighted_augment_cond_def weighted_reweight_cond_def
        weighted_augment_upd_def weighted_reweight_upd_def Let_def
      split: option.split prod.split)

lemma weighted_matroid_intersection_induct:
  assumes "weighted_matroid_intersection_dom st"
    "\<And> st. weighted_matroid_intersection_dom st \<Longrightarrow>
             (weighted_augment_cond st \<Longrightarrow> P (weighted_augment_upd st)) \<Longrightarrow>
             (weighted_reweight_cond st \<Longrightarrow> P (weighted_reweight_upd st)) \<Longrightarrow> P st"
  shows "P st"
  apply(rule weighted_matroid_intersection.pinduct[OF assms(1)])
  apply(rule assms(2)[simplified weighted_augment_cond_def weighted_reweight_cond_def
        weighted_augment_upd_def weighted_reweight_upd_def Let_def])
  by(auto simp: Let_def split: list.splits option.splits prod.splits if_splits)

partial_function (tailrec) weighted_matroid_intersection_impl ::
  "('mset, 'cmap) weighted_intersec_state \<Rightarrow> ('mset, 'cmap) weighted_intersec_state" where
  "weighted_matroid_intersection_impl st =
 (let X = wsol st; c1 = wc1 st; c2 = wc2 st;
      (SX, TX, G) = compute_graph X (complement X);
      SbarX = restrict_to_max SX c1;
      TbarX = restrict_to_max TX c2;
      Gtight = compute_tight_graph X c1 c2 (complement X);
      R = reach_set SbarX Gtight
  in (case find_path SbarX TbarX Gtight of
        Some p \<Rightarrow> weighted_matroid_intersection_impl
                    (st \<lparr> wsol := augment X p, wbest := keep_better st (augment X p) \<rparr>)
      | None \<Rightarrow> (case compute_eps X (weight_Max SX c1) (weight_Max TX c2) R c1 c2 of
                   None \<Rightarrow> st
                 | Some e \<Rightarrow> weighted_matroid_intersection_impl (reweight R e st))))"

lemma weighted_implementation_is_same:
  "weighted_matroid_intersection_dom st \<Longrightarrow>
     weighted_matroid_intersection_impl st = weighted_matroid_intersection st"
  apply(induction st rule: weighted_matroid_intersection.pinduct)
  apply(subst weighted_matroid_intersection_impl.simps)
  apply(subst weighted_matroid_intersection.psimps, simp)
  by(auto simp: Let_def split: option.splits prod.splits)

function (domintros) weighted_matroid_intersection_circuit ::
  "('mset, 'cmap) weighted_intersec_state \<Rightarrow> ('mset, 'cmap) weighted_intersec_state" where
  "weighted_matroid_intersection_circuit st =
 (let X = wsol st; c1 = wc1 st; c2 = wc2 st;
      (SX, TX, G) = compute_graph_circuit X (complement X);
      SbarX = restrict_to_max SX c1;
      TbarX = restrict_to_max TX c2;
      Gtight = compute_tight_graph_circuit X c1 c2 (complement X);
      R = reach_set SbarX Gtight
  in (case find_path SbarX TbarX Gtight of
        Some p \<Rightarrow> weighted_matroid_intersection_circuit
                    (st \<lparr> wsol := augment X p, wbest := keep_better st (augment X p) \<rparr>)
      | None \<Rightarrow> (case compute_eps_circuit X (weight_Max SX c1) (weight_Max TX c2) R c1 c2 of
                   None \<Rightarrow> st
                 | Some e \<Rightarrow> weighted_matroid_intersection_circuit (reweight R e st))))"
  by pat_completeness auto

definition "weighted_augment_cond_circuit st =
 (let X = wsol st; c1 = wc1 st; c2 = wc2 st;
      (SX, TX, G) = compute_graph_circuit X (complement X);
      SbarX = restrict_to_max SX c1; TbarX = restrict_to_max TX c2;
      Gtight = compute_tight_graph_circuit X c1 c2 (complement X)
  in (case find_path SbarX TbarX Gtight of None \<Rightarrow> False | Some p \<Rightarrow> True))"

definition "weighted_reweight_cond_circuit st =
 (let X = wsol st; c1 = wc1 st; c2 = wc2 st;
      (SX, TX, G) = compute_graph_circuit X (complement X);
      SbarX = restrict_to_max SX c1; TbarX = restrict_to_max TX c2;
      Gtight = compute_tight_graph_circuit X c1 c2 (complement X);
      R = reach_set SbarX Gtight
  in (case find_path SbarX TbarX Gtight of None \<Rightarrow>
        (case compute_eps_circuit X (weight_Max SX c1) (weight_Max TX c2) R c1 c2 of
           None \<Rightarrow> False | Some e \<Rightarrow> True)
      | Some p \<Rightarrow> False))"

definition "weighted_stop_cond_circuit st =
 (let X = wsol st; c1 = wc1 st; c2 = wc2 st;
      (SX, TX, G) = compute_graph_circuit X (complement X);
      SbarX = restrict_to_max SX c1; TbarX = restrict_to_max TX c2;
      Gtight = compute_tight_graph_circuit X c1 c2 (complement X);
      R = reach_set SbarX Gtight
  in (case find_path SbarX TbarX Gtight of None \<Rightarrow>
        (case compute_eps_circuit X (weight_Max SX c1) (weight_Max TX c2) R c1 c2 of
           None \<Rightarrow> True | Some e \<Rightarrow> False)
      | Some p \<Rightarrow> False))"

definition "weighted_augment_upd_circuit st =
 (let X = wsol st; c1 = wc1 st; c2 = wc2 st;
      (SX, TX, G) = compute_graph_circuit X (complement X);
      SbarX = restrict_to_max SX c1; TbarX = restrict_to_max TX c2;
      Gtight = compute_tight_graph_circuit X c1 c2 (complement X);
      p = the (find_path SbarX TbarX Gtight)
  in st \<lparr> wsol := augment X p, wbest := keep_better st (augment X p) \<rparr>)"

definition "weighted_reweight_upd_circuit st =
 (let X = wsol st; c1 = wc1 st; c2 = wc2 st;
      (SX, TX, G) = compute_graph_circuit X (complement X);
      SbarX = restrict_to_max SX c1; TbarX = restrict_to_max TX c2;
      Gtight = compute_tight_graph_circuit X c1 c2 (complement X);
      R = reach_set SbarX Gtight;
      e = the (compute_eps_circuit X (weight_Max SX c1) (weight_Max TX c2) R c1 c2)
  in reweight R e st)"

lemma P_of_weighted_augment_circuitI:
  "weighted_augment_cond_circuit st \<Longrightarrow>
   (\<And> SX TX G SbarX TbarX Gtight p X c1 c2.
       X = wsol st \<Longrightarrow> c1 = wc1 st \<Longrightarrow> c2 = wc2 st \<Longrightarrow>
       compute_graph_circuit X (complement X) = (SX, TX, G) \<Longrightarrow>
       SbarX = restrict_to_max SX c1 \<Longrightarrow> TbarX = restrict_to_max TX c2 \<Longrightarrow>
       Gtight = compute_tight_graph_circuit X c1 c2 (complement X) \<Longrightarrow>
       find_path SbarX TbarX Gtight = Some p \<Longrightarrow>
       P (st \<lparr> wsol := augment X p, wbest := keep_better st (augment X p) \<rparr>))
   \<Longrightarrow> P (weighted_augment_upd_circuit st)"
  unfolding weighted_augment_cond_circuit_def weighted_augment_upd_circuit_def Let_def
  apply(cases "compute_graph_circuit (wsol st) (complement (wsol st))", simp)
  subgoal for a b c
    by(cases "find_path (restrict_to_max a (wc1 st)) (restrict_to_max b (wc2 st))
                        (compute_tight_graph_circuit (wsol st) (wc1 st) (wc2 st) (complement (wsol st)))") auto
  done

lemma P_of_weighted_reweight_circuitI:
  "weighted_reweight_cond_circuit st \<Longrightarrow>
   (\<And> SX TX G SbarX TbarX Gtight R e X c1 c2.
       X = wsol st \<Longrightarrow> c1 = wc1 st \<Longrightarrow> c2 = wc2 st \<Longrightarrow>
       compute_graph_circuit X (complement X) = (SX, TX, G) \<Longrightarrow>
       SbarX = restrict_to_max SX c1 \<Longrightarrow> TbarX = restrict_to_max TX c2 \<Longrightarrow>
       Gtight = compute_tight_graph_circuit X c1 c2 (complement X) \<Longrightarrow>
       R = reach_set SbarX Gtight \<Longrightarrow>
       find_path SbarX TbarX Gtight = None \<Longrightarrow>
       compute_eps_circuit X (weight_Max SX c1) (weight_Max TX c2) R c1 c2 = Some e \<Longrightarrow>
       P (reweight R e st))
   \<Longrightarrow> P (weighted_reweight_upd_circuit st)"
  unfolding weighted_reweight_cond_circuit_def weighted_reweight_upd_circuit_def Let_def
  apply(cases "compute_graph_circuit (wsol st) (complement (wsol st))", simp)
  subgoal for a b c
    apply(cases "find_path (restrict_to_max a (wc1 st)) (restrict_to_max b (wc2 st))
                          (compute_tight_graph_circuit (wsol st) (wc1 st) (wc2 st) (complement (wsol st)))")
     apply(cases "compute_eps_circuit (wsol st) (weight_Max a (wc1 st)) (weight_Max b (wc2 st))
                    (reach_set (restrict_to_max a (wc1 st))
                       (compute_tight_graph_circuit (wsol st) (wc1 st) (wc2 st) (complement (wsol st))))
                    (wc1 st) (wc2 st)")
    by auto
  done

lemma weighted_matroid_intersection_circuit_cases:
  "(weighted_stop_cond_circuit st \<Longrightarrow> P) \<Longrightarrow>
   (weighted_augment_cond_circuit st \<Longrightarrow> P) \<Longrightarrow>
   (weighted_reweight_cond_circuit st \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding weighted_stop_cond_circuit_def weighted_augment_cond_circuit_def
    weighted_reweight_cond_circuit_def Let_def
  apply(cases "compute_graph_circuit (wsol st) (complement (wsol st))")
  subgoal for a b c
    apply(cases "find_path (restrict_to_max a (wc1 st)) (restrict_to_max b (wc2 st))
                          (compute_tight_graph_circuit (wsol st) (wc1 st) (wc2 st) (complement (wsol st)))")
     apply(cases "compute_eps_circuit (wsol st) (weight_Max a (wc1 st)) (weight_Max b (wc2 st))
                    (reach_set (restrict_to_max a (wc1 st))
                       (compute_tight_graph_circuit (wsol st) (wc1 st) (wc2 st) (complement (wsol st))))
                    (wc1 st) (wc2 st)")
    by auto
  done

lemma weighted_matroid_intersection_circuit_simps:
  assumes "weighted_matroid_intersection_circuit_dom st"
  shows "weighted_stop_cond_circuit st \<Longrightarrow> weighted_matroid_intersection_circuit st = st"
    and "weighted_augment_cond_circuit st \<Longrightarrow>
           weighted_matroid_intersection_circuit st
             = weighted_matroid_intersection_circuit (weighted_augment_upd_circuit st)"
    and "weighted_reweight_cond_circuit st \<Longrightarrow>
           weighted_matroid_intersection_circuit st
             = weighted_matroid_intersection_circuit (weighted_reweight_upd_circuit st)"
  by(auto intro: P_of_weighted_augment_circuitI P_of_weighted_reweight_circuitI
      simp add: weighted_matroid_intersection_circuit.psimps[OF assms]
        weighted_stop_cond_circuit_def weighted_augment_cond_circuit_def weighted_reweight_cond_circuit_def
        weighted_augment_upd_circuit_def weighted_reweight_upd_circuit_def Let_def
      split: option.split prod.split)

lemma weighted_matroid_intersection_circuit_induct:
  assumes "weighted_matroid_intersection_circuit_dom st"
    "\<And> st. weighted_matroid_intersection_circuit_dom st \<Longrightarrow>
             (weighted_augment_cond_circuit st \<Longrightarrow> P (weighted_augment_upd_circuit st)) \<Longrightarrow>
             (weighted_reweight_cond_circuit st \<Longrightarrow> P (weighted_reweight_upd_circuit st)) \<Longrightarrow> P st"
  shows "P st"
  apply(rule weighted_matroid_intersection_circuit.pinduct[OF assms(1)])
  apply(rule assms(2)[simplified weighted_augment_cond_circuit_def weighted_reweight_cond_circuit_def
        weighted_augment_upd_circuit_def weighted_reweight_upd_circuit_def Let_def])
  by(auto simp: Let_def split: list.splits option.splits prod.splits if_splits)

partial_function (tailrec) weighted_matroid_intersection_circuit_impl ::
  "('mset, 'cmap) weighted_intersec_state \<Rightarrow> ('mset, 'cmap) weighted_intersec_state" where
  "weighted_matroid_intersection_circuit_impl st =
 (let X = wsol st; c1 = wc1 st; c2 = wc2 st;
      (SX, TX, G) = compute_graph_circuit X (complement X);
      SbarX = restrict_to_max SX c1;
      TbarX = restrict_to_max TX c2;
      Gtight = compute_tight_graph_circuit X c1 c2 (complement X);
      R = reach_set SbarX Gtight
  in (case find_path SbarX TbarX Gtight of
        Some p \<Rightarrow> weighted_matroid_intersection_circuit_impl
                    (st \<lparr> wsol := augment X p, wbest := keep_better st (augment X p) \<rparr>)
      | None \<Rightarrow> (case compute_eps_circuit X (weight_Max SX c1) (weight_Max TX c2) R c1 c2 of
                   None \<Rightarrow> st
                 | Some e \<Rightarrow> weighted_matroid_intersection_circuit_impl (reweight R e st))))"

lemma weighted_implementation_is_same_circuit:
  "weighted_matroid_intersection_circuit_dom st \<Longrightarrow>
     weighted_matroid_intersection_circuit_impl st = weighted_matroid_intersection_circuit st"
  apply(induction st rule: weighted_matroid_intersection_circuit.pinduct)
  apply(subst weighted_matroid_intersection_circuit_impl.simps)
  apply(subst weighted_matroid_intersection_circuit.psimps, simp)
  by(auto simp: Let_def split: option.splits prod.splits)

text \<open>Initial state: \<open>X = \<emptyset>\<close> and split \<open>c1 = c\<close>, \<open>c2 = 0\<close> (the given cost map, resp. the zero map),
so the original weight is \<open>c\<close>.\<close>
definition "weighted_initial_state c =
  \<lparr> wsol = set_empty, wc1 = c, wc2 = c_zero, worig = c, wbest = set_empty \<rparr>"

lemmas [code] =
  weighted_matroid_intersection_impl.simps weighted_matroid_intersection_circuit_impl.simps
  treat1_tight_def treat2_tight_def compute_tight_graph_def
  treat1_circuit_tight_def treat2_circuit_tight_def compute_tight_graph_circuit_def
  reweight_def keep_better_def weighted_initial_state_def
  eps_min_def compute_eps_def compute_eps_circuit_def

end

subsection \<open>Proof locale (both variants)\<close>

text \<open>Merges the unweighted proof locale (which already provides the \<open>double_matroid\<close> structure and
all the graph/set ADT axioms) with the weighted executable spec, and adds the specifications of the
weight-map ADT and the weight oracles.  Every weight specification is phrased through the abstraction
\<open>c_lookup\<close>.  The weighted snapshot lemmas of \<open>Matroid_Weighted_Intersection\<close> (in particular
\<open>weighted_intersection_graph.augment_tight_path\<close>) become available by interpreting the locale
\<open>weighted_intersection_graph\<close> at the current split.\<close>

locale weighted_intersection =
  weighted_intersection_spec where insert = "insert :: 'a \<Rightarrow> 'vset \<Rightarrow> 'vset"
    and lookup = "lookup :: 'adjmap \<Rightarrow> 'a \<Rightarrow> 'vset option"
    and set_insert = "set_insert :: 'a \<Rightarrow> 'mset \<Rightarrow> 'mset"
    and find_path = "find_path :: 'vset \<Rightarrow> 'vset \<Rightarrow> 'adjmap \<Rightarrow> 'a list option"
    and t_set = vset
    and complement = "complement :: 'mset \<Rightarrow> 'mset_red"
    + double_matroid where carrier = "carrier :: 'a set"
  for insert lookup set_insert find_path carrier vset complement +
  fixes to_set_red :: "'mset_red \<Rightarrow> 'a set"
    and set_invar_red :: "'mset_red \<Rightarrow> bool"
  assumes set_insert: "\<And> S x. \<lbrakk>set_invar S; x \<in> carrier\<rbrakk> \<Longrightarrow> set_invar (set_insert x S)"
    "\<And> S x. \<lbrakk>set_invar S; x \<in> carrier\<rbrakk> \<Longrightarrow> to_set (set_insert x S) = Set.insert x (to_set S)"
  assumes set_delete: "\<And> S x. \<lbrakk>set_invar S; x \<in> carrier\<rbrakk> \<Longrightarrow> set_invar (set_delete x S)"
    "\<And> S x. \<lbrakk>set_invar S; x \<in> carrier\<rbrakk> \<Longrightarrow> to_set (set_delete x S) = (to_set S) - {x}"
  assumes set_empty: "set_invar set_empty" "to_set set_empty = {}"
  assumes weak_orcl1:
    "\<And> X x. \<lbrakk>set_invar X; to_set X \<subseteq> carrier; x \<in> carrier; x \<notin> to_set X; indep1 (to_set X)\<rbrakk>
       \<Longrightarrow> weak_orcl1 x X \<longleftrightarrow> indep1 (Set.insert x (to_set X))"
  assumes weak_orcl2:
    "\<And> X x. \<lbrakk>set_invar X; to_set X \<subseteq> carrier; x \<in> carrier; x \<notin> to_set X; indep2 (to_set X)\<rbrakk>
       \<Longrightarrow> weak_orcl2 x X \<longleftrightarrow> indep2 (Set.insert x (to_set X))"
  assumes inner_fold:
     "\<And> X f G. set_invar X \<Longrightarrow> \<exists> xs. set xs = to_set X \<and> inner_fold X f G = foldr f xs G"
  assumes inner_fold_circuit:
     "\<And> X f G. set_invar_red X
      \<Longrightarrow> \<exists> xs. set xs = to_set_red X \<and> inner_fold_circuit X f G = foldr f xs G"
  assumes outer_fold:
     "\<And> X f trip. set_invar_red X \<Longrightarrow> \<exists> xs. set xs = to_set_red X
                                           \<and> outer_fold X f trip = foldr f xs trip"
  assumes find_path:
    "\<And> G S T. \<lbrakk>graph.graph_inv G; graph.finite_graph G; graph.finite_vsets G; vset_inv S;
               vset_inv T; vset S \<subseteq> carrier; vset T \<subseteq> carrier; dVs (graph.digraph_abs G) \<subseteq> carrier\<rbrakk>
      \<Longrightarrow> find_path S T G = None \<longleftrightarrow>
           (\<nexists> p u v. (vwalk_bet (graph.digraph_abs G) u p v \<or> (p = [u] \<and> u = v)) \<and>
                       u \<in> vset S \<and> v \<in> vset T)"
    "\<And> G S T p. \<lbrakk>graph.graph_inv G; graph.finite_graph G; graph.finite_vsets G; vset_inv S;
                 vset_inv T; vset S \<subseteq> carrier; vset T \<subseteq> carrier;
                 dVs (graph.digraph_abs G) \<subseteq> carrier; find_path S T G = Some p\<rbrakk>
      \<Longrightarrow> \<exists> u v. (vwalk_bet (graph.digraph_abs G) u p v \<or> (p = [u] \<and> u = v))
                         \<and> u \<in> vset S \<and> v \<in> vset T \<and>
             (\<nexists> p'. (vwalk_bet (graph.digraph_abs G) u p' v \<or> (p' = [u] \<and> u = v))
                         \<and> length p' < length p)"
  assumes complement: "\<And> S. \<lbrakk>set_invar S; to_set S  \<subseteq> carrier\<rbrakk> \<Longrightarrow> set_invar_red (complement S)"
    "\<And> S. \<lbrakk>set_invar S; to_set S  \<subseteq> carrier\<rbrakk> \<Longrightarrow> to_set_red (complement S) = carrier - to_set S"
  assumes circuit1:
    "\<And> X y. \<lbrakk>set_invar X; indep1 (to_set X); to_set X \<subseteq> carrier; y \<in> carrier;
             \<not> indep1 (Set.insert y (to_set X))\<rbrakk>
        \<Longrightarrow> to_set_red (circuit1 y X) = matroid1.the_circuit (Set.insert y (to_set X)) - {y}"
    "\<And> X y. \<lbrakk>set_invar X; indep1 (to_set X); to_set X \<subseteq> carrier; y \<in> carrier;
              \<not> indep1 (Set.insert y (to_set X))\<rbrakk>
        \<Longrightarrow> set_invar_red (circuit1 y X)"
  assumes circuit2:
    "\<And> X y. \<lbrakk>set_invar X; indep2 (to_set X); to_set X \<subseteq> carrier; y \<in> carrier;
              \<not> indep2 (Set.insert y (to_set X))\<rbrakk>
        \<Longrightarrow> to_set_red (circuit2 y X) = matroid2.the_circuit (Set.insert y (to_set X)) - {y}"
    "\<And> X y. \<lbrakk>set_invar X; indep2 (to_set X); to_set X \<subseteq> carrier; y \<in> carrier;
              \<not> indep2 (Set.insert y (to_set X))\<rbrakk>
        \<Longrightarrow> set_invar_red (circuit2 y X)"
  \<comment> \<open>the weight-map ADT: \<open>c_lookup\<close> is both the executable lookup and the abstraction to \<^typ>\<open>'a \<Rightarrow> real\<close>\<close>
  assumes c_zero: "c_invar c_zero" "c_lookup c_zero = (\<lambda> _. 0)"
  assumes c_shift:
    "\<And> R e c. \<lbrakk>c_invar c; vset_inv R\<rbrakk> \<Longrightarrow> c_invar (c_shift R e c)"
    "\<And> R e c. \<lbrakk>c_invar c; vset_inv R\<rbrakk>
       \<Longrightarrow> c_lookup (c_shift R e c) = (\<lambda> x. if x \<in> vset R then c_lookup c x + e else c_lookup c x)"
  assumes weight_Max:
    "\<And> V c. \<lbrakk>c_invar c; vset_inv V; vset V \<noteq> {}\<rbrakk> \<Longrightarrow> weight_Max V c = Max (c_lookup c ` vset V)"
  assumes restrict_to_max:
    "\<And> V c. \<lbrakk>c_invar c; vset_inv V\<rbrakk> \<Longrightarrow> vset_inv (restrict_to_max V c)"
    "\<And> V c. \<lbrakk>c_invar c; vset_inv V\<rbrakk>
       \<Longrightarrow> vset (restrict_to_max V c) = {y \<in> vset V. c_lookup c y = Max (c_lookup c ` vset V)}"
  assumes reach_set:
    "\<And> Src G. \<lbrakk>graph.graph_inv G; vset_inv Src\<rbrakk> \<Longrightarrow> vset_inv (reach_set Src G)"
    "\<And> Src G. \<lbrakk>graph.graph_inv G; vset_inv Src\<rbrakk> \<Longrightarrow>
       vset (reach_set Src G) =
         {v. \<exists> u \<in> vset Src. u = v \<or> (\<exists> p. vwalk_bet [G]\<^sub>g u p v)}"
  assumes weight:
    "\<And> c X. \<lbrakk>c_invar c; set_invar X\<rbrakk> \<Longrightarrow> weight c X = sum (c_lookup c) (to_set X)"
  assumes eps_fold:
    "\<And> X f a. set_invar X \<Longrightarrow> \<exists> xs. set xs = to_set X \<and> eps_fold X f a = foldr f xs a"
  assumes eps_fold_red:
    "\<And> X f a. set_invar_red X \<Longrightarrow> \<exists> xs. set xs = to_set_red X \<and> eps_fold_red X f a = foldr f xs a"
begin

text \<open>\<^bold>\<open>Kept for future reference\<close> -- the abstract value that \<open>compute_eps\<close>/\<open>compute_eps_circuit\<close>
realise (Frank's \<open>\<epsilon>\<close>), which the naive algorithm now \<^emph>\<open>computes\<close> and which the \<open>eps_meaning\<close> lemma
will pin down:
\<^verbatim>\<open>compute_eps X (weight_Max SX c1) (weight_Max TX c2) R c1 c2 =
  (let d1 = c_lookup c1; d2 = c_lookup c2;
       D = {d1 x - d1 y | x y. (x,y) : A1 (to_set X) & x : vset R & y ~: vset R} Un
           {d2 x - d2 y | x y. (y,x) : A2 (to_set X) & y : vset R & x ~: vset R} Un
           {Max (d1 ` S (to_set X)) - d1 y | y. y : S (to_set X) & y ~: vset R} Un
           {Max (d2 ` T (to_set X)) - d2 y | y. y : T (to_set X) & y : vset R}
   in if D = {} then None else Some (Min D))\<close>
In the refined (potential) version \<open>\<epsilon>\<close> becomes a Dijkstra distance labelling instead.\<close>

subsubsection \<open>Reusing the unweighted development\<close>

text \<open>Since the weighted proof locale carries exactly the assumptions of the unweighted one, it is an
instance of it; interpreting it makes every unweighted lemma (\<open>compute_graph_meaning\<close>,
\<open>effect_of_augmentation\<close>, \<open>if_no_augpath_then_maximum\<close>, \<open>\<dots>\<close>) available under the \<open>U\<close> prefix.\<close>

sublocale U: unweighted_intersection
  by unfold_locales
    (fact set_insert set_delete set_empty weak_orcl1 weak_orcl2 inner_fold
       inner_fold_circuit outer_fold find_path complement circuit1 circuit2)+

subsubsection \<open>The loop invariant\<close>

text \<open>At any split \<open>(c1, c2)\<close> the ambient double matroid is a \<^locale>\<open>weighted_intersection_graph\<close>
(interpret it \<open>by unfold_locales\<close>), which supplies \<open>Gbar\<close>/\<open>Sbar\<close>/\<open>Tbar\<close> and the snapshot lemmas
\<open>augment_tight_path\<close>, \<open>tight_gap1/2\<close>, \<open>reweight_preserves_local_opt\<close>.

The loop invariant: \<open>wsol\<close> is a common independent set that is \<open>(13.5)\<close>-optimal for the split,
the split sums to the original weight, and \<open>wbest\<close> is the maximum-weight common independent set of
cardinality at most \<open>card (wsol)\<close>.\<close>

definition "w_invar s \<longleftrightarrow>
  set_invar (wsol s) \<and> to_set (wsol s) \<subseteq> carrier
  \<and> indep1 (to_set (wsol s)) \<and> indep2 (to_set (wsol s))
  \<and> c_invar (wc1 s) \<and> c_invar (wc2 s) \<and> c_invar (worig s)
  \<and> (\<forall>x\<in>carrier. c_lookup (wc1 s) x + c_lookup (wc2 s) x = c_lookup (worig s) x)
  \<and> matroid1.local_opt (c_lookup (wc1 s)) (to_set (wsol s))
  \<and> matroid2.local_opt (c_lookup (wc2 s)) (to_set (wsol s))
  \<and> set_invar (wbest s) \<and> indep1 (to_set (wbest s)) \<and> indep2 (to_set (wbest s))
  \<and> (\<forall>Y. indep1 Y \<and> indep2 Y \<and> card Y \<le> card (to_set (wsol s))
        \<longrightarrow> sum (c_lookup (worig s)) Y \<le> sum (c_lookup (worig s)) (to_set (wbest s)))"

subsubsection \<open>The tight auxiliary graph abstracts to \<open>Gbar\<close>\<close>

text \<open>Analogue of the unweighted @{thm [source] U.treat1_correct}: the tight treat step adds exactly
the tight \<open>A1\<close>-arcs.\<close>

lemma treat1_tight_correct:
  assumes "indep1 (to_set X)" "set_invar X" "y \<in> carrier - to_set X" "graph.graph_inv G"
  shows "graph.graph_inv (treat1_tight y X c G)"
    "graph.digraph_abs (treat1_tight y X c G) = graph.digraph_abs G \<union>
       {(x, y) | x. x \<in> to_set X \<and> indep1 (to_set X - {x} \<union> {y}) \<and> c_lookup c x = c_lookup c y}"
    "graph.finite_graph G \<Longrightarrow> graph.finite_graph (treat1_tight y X c G)"
    "graph.finite_vsets G \<Longrightarrow> graph.finite_vsets (treat1_tight y X c G)"
proof-
  define f where "f = (\<lambda> x current_map. if weak_orcl1 y (set_delete x X) \<and> c_lookup c x = c_lookup c y
                                         then graph.add_edge current_map x y
                                         else current_map)"
  obtain xs where xs_prop: "set xs = to_set X" True "inner_fold X f G = foldr f xs G"
    using inner_fold[OF assms(2), of f G] by auto
  have treat_is: "treat1_tight y X c G = foldr f xs G"
    by(unfold xs_prop(3)[symmetric])(simp add: treat1_tight_def f_def)
  have claim1:"graph.graph_inv (foldr f xs G)" for xs
    by(induction xs)(auto split: if_split simp add: f_def assms(4))
  thus "graph.graph_inv (treat1_tight y X c G)"
    by (simp add: treat_is)
  have X_in_Carrier: "to_set X \<subseteq> carrier "
    by (simp add: assms(1) matroid1.indep_subset_carrier)
  have independence_is:"a \<in> to_set X \<Longrightarrow>
          weak_orcl1 y (set_delete a X) = indep1 (Set.insert y (to_set X - {a}))" for a
    using X_in_Carrier  assms(1) matroid1.indep_in_subset set_delete(2)[OF  assms(2)]
      matroid1.indep_in_carrier assms(3)
    by (subst weak_orcl1)
      (fastforce simp add: weak_orcl1 assms(3) assms(2) set_delete(1) subset_eq)+
  have "set xs \<subseteq> to_set X  \<Longrightarrow>graph.digraph_abs (foldr f xs G) = graph.digraph_abs G \<union>
       {(x, y) | x. x \<in> set xs \<and> indep1 (to_set X - {x} \<union> {y}) \<and> c_lookup c x = c_lookup c y}"
    using xs_prop(2)
    apply(induction xs, simp)
    apply(subst foldr_Cons, subst o_apply)
    apply(subst f_def)
    by(auto simp add: independence_is graph.digraph_abs_insert[OF claim1])
  thus "graph.digraph_abs (treat1_tight y X c G) = graph.digraph_abs G \<union>
       {(x, y) |x. x \<in> to_set X \<and> indep1 (to_set X - {x} \<union> {y}) \<and> c_lookup c x = c_lookup c y}"
    by(simp add: treat_is xs_prop(1))
  have "set xs \<subseteq> to_set X \<Longrightarrow> graph.finite_graph G \<Longrightarrow> graph.finite_graph (foldr f xs G)"
    apply(induction xs, simp)
    apply(subst foldr_Cons, subst o_apply)
    apply(subst f_def)
    by(auto simp add: independence_is claim1 graph.finite_graph_add_edge)
  thus "graph.finite_graph G \<Longrightarrow> graph.finite_graph (treat1_tight y X c G)"
    by (simp add: treat_is xs_prop(1))
  have "set xs \<subseteq> to_set X \<Longrightarrow> graph.finite_vsets G \<Longrightarrow> graph.finite_vsets (foldr f xs G)"
    apply(induction xs, simp)
    apply(subst foldr_Cons, subst o_apply)
    apply(subst f_def)
    by(auto simp add: independence_is claim1 graph.finite_vsets_add_edge)
  thus "graph.finite_vsets G \<Longrightarrow> graph.finite_vsets (treat1_tight y X c G)"
    by (simp add: treat_is xs_prop(1))
qed

lemma treat2_tight_correct:
  assumes "indep2 (to_set X)" "set_invar X" "y \<in> carrier - to_set X" "graph.graph_inv G"
  shows "graph.graph_inv (treat2_tight y X c G)"
    "graph.digraph_abs (treat2_tight y X c G) = graph.digraph_abs G \<union>
       {(y, x) | x. x \<in> to_set X \<and> indep2 (to_set X - {x} \<union> {y}) \<and> c_lookup c y = c_lookup c x}"
    "graph.finite_graph G \<Longrightarrow> graph.finite_graph (treat2_tight y X c G)"
    "graph.finite_vsets G \<Longrightarrow> graph.finite_vsets (treat2_tight y X c G)"
proof-
  define f where "f = (\<lambda> x current_map. if weak_orcl2 y (set_delete x X) \<and> c_lookup c y = c_lookup c x
                                         then graph.add_edge current_map y x
                                         else current_map)"
  obtain xs where xs_prop: "set xs = to_set X" True "inner_fold X f G = foldr f xs G"
    using inner_fold[OF assms(2), of f G] by auto
  have treat_is: "treat2_tight y X c G = foldr f xs G"
    by(unfold xs_prop(3)[symmetric])(simp add: treat2_tight_def f_def)
  have claim1:"graph.graph_inv (foldr f xs G)" for xs
    by(induction xs)(auto split: if_split simp add: f_def assms(4))
  thus "graph.graph_inv (treat2_tight y X c G)"
    by (simp add: treat_is)
  have X_in_Carrier: "to_set X \<subseteq> carrier "
    by (simp add: assms(1) matroid2.indep_subset_carrier)
  have independence_is:"a \<in> to_set X \<Longrightarrow>
          weak_orcl2 y (set_delete a X) = indep2 (Set.insert y (to_set X - {a}))" for a
    using X_in_Carrier  assms(1) matroid2.indep_in_subset set_delete(2)[OF  assms(2)]
      matroid2.indep_in_carrier assms(3)
    by (subst weak_orcl2)
      (fastforce simp add: weak_orcl2 assms(3) assms(2) set_delete(1) subset_eq)+
  have "set xs \<subseteq> to_set X  \<Longrightarrow>graph.digraph_abs (foldr f xs G) = graph.digraph_abs G \<union>
       {(y, x) | x. x \<in> set xs \<and> indep2 (to_set X - {x} \<union> {y}) \<and> c_lookup c y = c_lookup c x}"
    using xs_prop(2)
    apply(induction xs, simp)
    apply(subst foldr_Cons, subst o_apply)
    apply(subst f_def)
    by(auto simp add: independence_is graph.digraph_abs_insert[OF claim1])
  thus "graph.digraph_abs (treat2_tight y X c G) = graph.digraph_abs G \<union>
       {(y, x) |x. x \<in> to_set X \<and> indep2 (to_set X - {x} \<union> {y}) \<and> c_lookup c y = c_lookup c x}"
    by(simp add: treat_is xs_prop(1))
  have "set xs \<subseteq> to_set X \<Longrightarrow> graph.finite_graph G \<Longrightarrow> graph.finite_graph (foldr f xs G)"
    apply(induction xs, simp)
    apply(subst foldr_Cons, subst o_apply)
    apply(subst f_def)
    by(auto simp add: independence_is claim1 graph.finite_graph_add_edge)
  thus "graph.finite_graph G \<Longrightarrow> graph.finite_graph (treat2_tight y X c G)"
    by (simp add: treat_is xs_prop(1))
  have "set xs \<subseteq> to_set X \<Longrightarrow> graph.finite_vsets G \<Longrightarrow> graph.finite_vsets (foldr f xs G)"
    apply(induction xs, simp)
    apply(subst foldr_Cons, subst o_apply)
    apply(subst f_def)
    by(auto simp add: independence_is claim1 graph.finite_vsets_add_edge)
  thus "graph.finite_vsets G \<Longrightarrow> graph.finite_vsets (treat2_tight y X c G)"
    by (simp add: treat_is xs_prop(1))
qed

text \<open>The circuit-oracle counterparts of @{thm [source] treat1_tight_correct}/@{thm [source]
treat2_tight_correct}: verbatim copies of the unweighted @{thm [source] U.treat1_circuit_correct}/
@{thm [source] U.treat2_circuit_correct} with the tightness guard \<open>c_lookup c x = c_lookup c y\<close>.\<close>

lemma treat1_circuit_tight_correct:
  assumes "set_invar_red C" "graph.graph_inv G"
  shows "graph.graph_inv (treat1_circuit_tight y C c G)"
    "graph.digraph_abs (treat1_circuit_tight y C c G) = graph.digraph_abs G \<union>
                       {(x, y) | x. x \<in> to_set_red C \<and> c_lookup c x = c_lookup c y}"
    "graph.finite_graph G \<Longrightarrow> graph.finite_graph (treat1_circuit_tight y C c G)"
    "graph.finite_vsets G \<Longrightarrow> graph.finite_vsets (treat1_circuit_tight y C c G)"
proof-
  define f where "f = (\<lambda> x current_map.  if c_lookup c x = c_lookup c y
                                          then graph.add_edge current_map x y else current_map)"
  obtain xs where xs_prop: "set xs = to_set_red C" True "inner_fold_circuit C f G = foldr f xs G"
    using inner_fold_circuit[OF assms(1), of f G] by auto
  have treat_is: "treat1_circuit_tight y C c G = foldr f xs G"
    by(unfold xs_prop(3)[symmetric])(simp add: treat1_circuit_tight_def f_def)
  have claim1:"graph.graph_inv (foldr f xs G)" for xs
    by(induction xs)(auto split: if_split simp add: f_def assms(2))
  thus "graph.graph_inv (treat1_circuit_tight y C c G)"
    by (simp add: treat_is)
  have "set xs \<subseteq> to_set_red C  \<Longrightarrow> graph.digraph_abs (foldr f xs G) = graph.digraph_abs G \<union>
                       {(x, y) | x. x \<in> set xs \<and> c_lookup c x = c_lookup c y}"
    using xs_prop(2)
    apply(induction xs, simp)
    apply(subst foldr_Cons, subst o_apply)
    apply(subst f_def)
    by(auto simp add: graph.digraph_abs_insert[OF claim1])
  thus "[treat1_circuit_tight y C c G]\<^sub>g = [G]\<^sub>g \<union> {(x, y) |x. x \<in> to_set_red C \<and> c_lookup c x = c_lookup c y}"
    by(simp add: treat_is xs_prop(1))
  have "set xs \<subseteq> to_set_red C \<Longrightarrow> graph.finite_graph G \<Longrightarrow> graph.finite_graph (foldr f xs G)"
    apply(induction xs, simp)
    apply(subst foldr_Cons, subst o_apply)
    apply(subst f_def)
    by(auto simp add: claim1 graph.finite_graph_add_edge)
  thus "graph.finite_graph G \<Longrightarrow> graph.finite_graph (treat1_circuit_tight y C c G)"
    by (simp add: treat_is xs_prop(1))
  have "set xs \<subseteq> to_set_red C \<Longrightarrow> graph.finite_vsets G \<Longrightarrow> graph.finite_vsets (foldr f xs G)"
    apply(induction xs, simp)
    apply(subst foldr_Cons, subst o_apply)
    apply(subst f_def)
    by(auto simp add: claim1 graph.finite_vsets_add_edge)
  thus "graph.finite_vsets G \<Longrightarrow> graph.finite_vsets (treat1_circuit_tight y C c G)"
    by (simp add: treat_is xs_prop(1))
qed

lemma treat2_circuit_tight_correct:
  assumes "set_invar_red C" "graph.graph_inv G"
  shows "graph.graph_inv (treat2_circuit_tight y C c G)"
    "graph.digraph_abs (treat2_circuit_tight y C c G) = graph.digraph_abs G \<union>
                       {(y, x) | x. x \<in> to_set_red C \<and> c_lookup c y = c_lookup c x}"
    "graph.finite_graph G \<Longrightarrow> graph.finite_graph (treat2_circuit_tight y C c G)"
    "graph.finite_vsets G \<Longrightarrow> graph.finite_vsets (treat2_circuit_tight y C c G)"
proof-
  define f where "f = (\<lambda> x current_map. if c_lookup c y = c_lookup c x
                                          then graph.add_edge current_map y x else current_map)"
  obtain xs where xs_prop: "set xs = to_set_red C" True "inner_fold_circuit C f G = foldr f xs G"
    using inner_fold_circuit[OF assms(1), of f G] by auto
  have treat_is: "treat2_circuit_tight y C c G = foldr f xs G"
    by(unfold xs_prop(3)[symmetric])(simp add: treat2_circuit_tight_def f_def)
  have claim1:"graph.graph_inv (foldr f xs G)" for xs
    by(induction xs)(auto split: if_split simp add: f_def assms(2))
  thus "graph.graph_inv (treat2_circuit_tight y C c G)"
    by (simp add: treat_is)
  have "set xs \<subseteq> to_set_red C  \<Longrightarrow> graph.digraph_abs (foldr f xs G) = graph.digraph_abs G \<union>
                       {(y, x) | x. x \<in> set xs \<and> c_lookup c y = c_lookup c x}"
    using xs_prop(2)
    apply(induction xs, simp)
    apply(subst foldr_Cons, subst o_apply)
    apply(subst f_def)
    by(auto simp add: graph.digraph_abs_insert[OF claim1])
  thus "[treat2_circuit_tight y C c G]\<^sub>g = [G]\<^sub>g \<union> {(y, x) |x. x \<in> to_set_red C \<and> c_lookup c y = c_lookup c x}"
    by(simp add: treat_is xs_prop(1))
  have "set xs \<subseteq> to_set_red C \<Longrightarrow> graph.finite_graph G \<Longrightarrow> graph.finite_graph (foldr f xs G)"
    apply(induction xs, simp)
    apply(subst foldr_Cons, subst o_apply)
    apply(subst f_def)
    by(auto simp add: claim1 graph.finite_graph_add_edge)
  thus "graph.finite_graph G \<Longrightarrow> graph.finite_graph (treat2_circuit_tight y C c G)"
    by (simp add: treat_is xs_prop(1))
  have "set xs \<subseteq> to_set_red C \<Longrightarrow> graph.finite_vsets G \<Longrightarrow> graph.finite_vsets (foldr f xs G)"
    apply(induction xs, simp)
    apply(subst foldr_Cons, subst o_apply)
    apply(subst f_def)
    by(auto simp add: claim1 graph.finite_vsets_add_edge)
  thus "graph.finite_vsets G \<Longrightarrow> graph.finite_vsets (treat2_circuit_tight y C c G)"
    by (simp add: treat_is xs_prop(1))
qed

text \<open>Analogue of the unweighted @{thm [source] U.compute_graph_correct} for the tight builder (the
\<open>S\<close>/\<open>T\<close> components are irrelevant here, so only the graph is described): it abstracts to the tight
arcs of \<open>A1\<close>/\<open>A2\<close>.\<close>

lemma compute_tight_graph_correct:
  assumes "indep1 (to_set X)" "indep2 (to_set X)" "set_invar X"
    "set_invar_red E_without_X" "to_set_red E_without_X \<subseteq> carrier - to_set X"
  shows "graph.graph_inv (compute_tight_graph X c1 c2 E_without_X)"
    and "graph.digraph_abs (compute_tight_graph X c1 c2 E_without_X) =
       {(x, y) |x y. y \<in> to_set_red E_without_X \<and> \<not> indep1 (Set.insert y (to_set X))
                     \<and> x \<in> to_set X \<and> indep1 (to_set X - {x} \<union> {y}) \<and> c_lookup c1 x = c_lookup c1 y}
       \<union> {(y, x) |x y. y \<in> to_set_red E_without_X \<and> \<not> indep2 (Set.insert y (to_set X))
                     \<and> x \<in> to_set X \<and> indep2 (to_set X - {x} \<union> {y}) \<and> c_lookup c2 y = c_lookup c2 x}"
    (is ?last_thesis)
    and "graph.finite_graph (compute_tight_graph X c1 c2 E_without_X)"
    and "graph.finite_vsets (compute_tight_graph X c1 c2 E_without_X)"
proof-
  define f where "f = (\<lambda> y (SX::'vset, TX::'vset, current_map).
            let (SX, TX, current_map) = (if weak_orcl1 y X then (SX, TX, current_map)
                                         else (SX, TX, treat1_tight y X c1 current_map));
                (SX, TX, current_map) = (if weak_orcl2 y X then (SX, TX, current_map)
                                         else (SX, TX, treat2_tight y X c2 current_map))
            in (SX, TX, current_map))"
  obtain xs where xs_prop: "set xs = to_set_red E_without_X" True
    "outer_fold E_without_X f (vset_empty, vset_empty, empty) = foldr f xs (vset_empty, vset_empty, empty)"
    using outer_fold[OF assms(4), of f "(vset_empty, vset_empty, empty)"] by auto
  have resulting_map_is: "compute_tight_graph X c1 c2 E_without_X =
                            snd (snd (foldr f xs (vset_empty, vset_empty, empty)))"
    using xs_prop(3)[symmetric] by(auto simp add: f_def compute_tight_graph_def)
  have graph_inv_resulting_map:
    "set xs \<subseteq> carrier - to_set X \<Longrightarrow>
       graph.graph_inv (snd (snd (foldr f xs (vset_empty, vset_empty, empty))))" for xs
    by(induction xs)
      (auto split: prod.split
        intro!: treat1_tight_correct(1)[OF assms(1,3)] treat2_tight_correct(1)[OF assms(2,3)]
        simp add: f_def graph.graph_inv_empty)
  thus "graph.graph_inv (compute_tight_graph X c1 c2 E_without_X)"
    by (simp add: assms(5) resulting_map_is xs_prop(1))
  have X_in_carrier:"to_set X \<subseteq> carrier"
    by (simp add: assms(1) matroid1.indep_subset_carrier)
  have "set xs \<subseteq> carrier - to_set X \<Longrightarrow>
     graph.digraph_abs (snd (snd (foldr f xs (vset_empty, vset_empty, empty)))) =
       {(x, y) |x y. y \<in> set xs \<and> \<not> indep1 (Set.insert y (to_set X)) \<and> x \<in> to_set X
                     \<and> indep1 (to_set X - {x} \<union> {y}) \<and> c_lookup c1 x = c_lookup c1 y}
     \<union> {(y, x) |x y. y \<in> set xs \<and> \<not> indep2 (Set.insert y (to_set X)) \<and> x \<in> to_set X
                     \<and> indep2 (to_set X - {x} \<union> {y}) \<and> c_lookup c2 y = c_lookup c2 x}"
  proof(induction xs)
    case (Cons a xs)
    show ?case
    proof(subst foldr_Cons, subst o_apply, subst f_def, unfold Let_def,
        (split prod.split, rule, rule, rule)+, goal_cases)
      case (1 x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e)
      then show ?case
      proof(cases "weak_orcl1 a X", all \<open>cases "weak_orcl2 a X"\<close>, goal_cases)
        case 1
        then show ?case
          using Cons  weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]
            weak_orcl2[OF assms(3) X_in_carrier _  _ assms(2)]
          by auto
      next
        case 2
        then show ?case
          using  graph_inv_resulting_map  Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
          by (clarsimp, subst treat2_tight_correct(2)[OF assms(2,3)])force+
      next
        case 3
        then show ?case
          using  graph_inv_resulting_map  Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
          by (clarsimp, subst treat1_tight_correct(2)[OF assms(1,3)])force+
      next
        case 4
        then show ?case
          using Cons.prems
          apply(clarsimp, subst treat2_tight_correct(2)[OF assms(2,3)], simp)
           apply(rule treat1_tight_correct(1)[OF assms(1,3)])
          using graph_inv_resulting_map[of xs]  Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
          by (subst treat1_tight_correct(2)[OF assms(1,3)]|force)+
      qed
    qed
  qed (auto simp add:  graph.digraph_abs_empty)
  thus ?last_thesis
    using assms(5) resulting_map_is xs_prop(1) by presburger
  have "set xs  \<subseteq> carrier -to_set X \<Longrightarrow>
       graph.finite_graph (snd (snd (foldr f xs (vset_empty, vset_empty, empty))))"
  proof(induction xs)
    case (Cons a xs)
    show ?case
    proof(subst foldr_Cons, subst o_apply, subst f_def, unfold Let_def,
        (split prod.split, rule, rule, rule)+, goal_cases)
      case (1 x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e)
      then show ?case
      proof(cases "weak_orcl1 a X", all \<open>cases "weak_orcl2 a X"\<close>, goal_cases)
        case 1
        then show ?case
          using Cons  weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
          by auto
      next
        case 2
        then show ?case
          using  graph_inv_resulting_map  Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
          by (clarsimp, subst treat2_tight_correct(3)[OF assms(2,3)])force+
      next
        case 3
        then show ?case
          using  graph_inv_resulting_map  Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
          by (clarsimp, subst treat1_tight_correct(3)[OF assms(1,3)])force+
      next
        case 4
        then show ?case
          using Cons.prems
          apply(clarsimp, subst treat2_tight_correct(3)[OF assms(2,3)], simp)
            apply(rule treat1_tight_correct(1)[OF assms(1,3)])
          using graph_inv_resulting_map[of xs]  Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
          by (subst treat1_tight_correct(3)[OF assms(1,3)]|force)+
      qed
    qed
  qed (auto simp add: graph.adjmap.map_empty graph.finite_graph_def)
  thus "graph.finite_graph (compute_tight_graph X c1 c2 E_without_X)"
    using  resulting_map_is xs_prop(1)  assms(5) by auto
  have "set xs  \<subseteq> carrier -to_set X \<Longrightarrow>
       graph.finite_vsets (snd (snd (foldr f xs (vset_empty, vset_empty, empty))))"
  proof(induction xs)
    case (Cons a xs)
    show ?case
    proof(subst foldr_Cons, subst o_apply, subst f_def, unfold Let_def,
        (split prod.split, rule, rule, rule)+, goal_cases)
      case (1 x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e)
      then show ?case
      proof(cases "weak_orcl1 a X", all \<open>cases "weak_orcl2 a X"\<close>, goal_cases)
        case 1
        then show ?case
          using Cons  weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
          by auto
      next
        case 2
        then show ?case
          using  graph_inv_resulting_map  Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
          by (clarsimp, subst treat2_tight_correct(4)[OF assms(2,3)])force+
      next
        case 3
        then show ?case
          using  graph_inv_resulting_map  Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
          by (clarsimp, subst treat1_tight_correct(4)[OF assms(1,3)])force+
      next
        case 4
        then show ?case
          using Cons.prems
          apply(clarsimp, subst treat2_tight_correct(4)[OF assms(2,3)], simp)
            apply(rule treat1_tight_correct(1)[OF assms(1,3)])
          using graph_inv_resulting_map[of xs]  Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
          by (subst treat1_tight_correct(4)[OF assms(1,3)]|force)+
      qed
    qed
  qed (auto simp add: graph.adjmap.map_empty graph.finite_graph_def)
  thus "graph.finite_vsets (compute_tight_graph X c1 c2 E_without_X)"
    using assms(5) resulting_map_is xs_prop(1) by force
qed

text \<open>The tight builder abstracts to Frank's tight subgraph \<open>Gbar\<close> (with the abstract split weights
\<open>c_lookup c1\<close>/\<open>c_lookup c2\<close>) --- the analogue of the unweighted @{thm [source] U.compute_graph_meaning}(3).\<close>

lemma compute_tight_graph_meaning:
  assumes "indep1 (to_set X)" "indep2 (to_set X)" "set_invar X"
    "set_invar_red E_without_X" "to_set_red E_without_X = carrier - to_set X"
  shows "graph.digraph_abs (compute_tight_graph X c1 c2 E_without_X)
           = weighted_intersection_graph.Gbar carrier indep1 indep2 (c_lookup c1) (c_lookup c2) (to_set X)"
proof-
  interpret W: weighted_intersection_graph carrier indep1 indep2 "c_lookup c1" "c_lookup c2"
    by unfold_locales
  show ?thesis
    using matroid2.indep_subset_carrier[OF assms(2)]
    by(subst compute_tight_graph_correct(2)[OF assms(1-4) _])
      (auto simp add: matroid1.circuit_extensional[OF assms(1)] insert_Diff_if
        matroid2.circuit_extensional[OF assms(2)] A1_def A2_def assms(5)
        W.Gbar_def W.Abar1_def W.Abar2_def)
qed

text \<open>Circuit-oracle twin of @{thm [source] compute_tight_graph_correct}: mirror of the unweighted
@{thm [source] U.compute_graph_circuit_correct} (again only the graph, no \<open>S\<close>/\<open>T\<close>), with the tightness
guard added to the two arc set-builders.\<close>

lemma compute_tight_graph_circuit_correct:
  assumes "indep1 (to_set X)" "indep2 (to_set X)" "set_invar X"
    "set_invar_red E_without_X" "to_set_red E_without_X \<subseteq> carrier - to_set X"
  shows "graph.graph_inv (compute_tight_graph_circuit X c1 c2 E_without_X)"
    and "graph.digraph_abs (compute_tight_graph_circuit X c1 c2 E_without_X) =
                {(x, y) |x y. y \<in> to_set_red E_without_X
                       \<and> x \<in> matroid1.the_circuit (Set.insert y (to_set X)) - {y}
                       \<and> c_lookup c1 x = c_lookup c1 y}
                \<union> {(y, x) |x y. y \<in> to_set_red E_without_X
                       \<and> x \<in> matroid2.the_circuit (Set.insert y (to_set X)) - {y}
                       \<and> c_lookup c2 y = c_lookup c2 x}"
    (is ?last_thesis)
    and "graph.finite_graph (compute_tight_graph_circuit X c1 c2 E_without_X)"
    and "graph.finite_vsets (compute_tight_graph_circuit X c1 c2 E_without_X)"
proof-
  define f where "f = (\<lambda> y (SX::'vset, TX::'vset, current_map). (
            let (SX, TX, current_map) = (if weak_orcl1 y X then (SX, TX, current_map)
                                         else (SX, TX, treat1_circuit_tight y (circuit1 y X) c1 current_map));
                (SX, TX, current_map) = (if weak_orcl2 y X then (SX, TX, current_map)
                                         else (SX, TX, treat2_circuit_tight y (circuit2 y X) c2 current_map))
            in (SX, TX, current_map)))"
  obtain xs where xs_prop: "set xs = to_set_red E_without_X" True
    "outer_fold E_without_X f (vset_empty, vset_empty, empty) = foldr f xs (vset_empty, vset_empty, empty)"
    using outer_fold[OF assms(4), of f "(vset_empty, vset_empty, empty)"] by auto
  have resulting_map_is: "compute_tight_graph_circuit X c1 c2 E_without_X =
                            snd (snd (foldr f xs (vset_empty, vset_empty, empty)))"
    using xs_prop(3)[symmetric] by(auto simp add: f_def compute_tight_graph_circuit_def)
  have X_in_carrier:"to_set X \<subseteq> carrier"
    by (simp add: assms(1) matroid1.indep_subset_carrier)
  have graph_inv_resulting_map:
    "set xs \<subseteq> carrier - to_set X \<Longrightarrow>
       graph.graph_inv (snd (snd (foldr f xs (vset_empty, vset_empty, empty))))" for xs
    by(induction xs)
      (auto split: prod.split intro!: treat2_circuit_tight_correct(1) treat1_circuit_tight_correct(1)
        simp add: X_in_carrier assms(1) assms(2) assms(3) circuit2(2) weak_orcl2 circuit1(2) weak_orcl1
        f_def graph.graph_inv_empty)
  thus "graph.graph_inv (compute_tight_graph_circuit X c1 c2 E_without_X)"
    by (simp add: assms(5) resulting_map_is xs_prop(1))
  have "set xs \<subseteq> carrier -to_set X \<Longrightarrow>
     graph.digraph_abs (snd (snd (foldr f xs (vset_empty, vset_empty, empty)))) =
       {(x, y) |x y. y \<in> set xs \<and> x \<in> matroid1.the_circuit (Set.insert y (to_set X)) - {y}
                     \<and> c_lookup c1 x = c_lookup c1 y}
     \<union> {(y, x) |x y. y \<in> set xs \<and> x \<in> matroid2.the_circuit (Set.insert y (to_set X)) - {y}
                     \<and> c_lookup c2 y = c_lookup c2 x}"
  proof(induction xs)
    case (Cons a xs)
    show ?case
    proof(subst foldr_Cons, subst o_apply, subst f_def, unfold Let_def,
        (split prod.split, rule, rule, rule)+, goal_cases)
      case (1 x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e)
      then show ?case
      proof(cases "weak_orcl1 a X", all \<open>cases "weak_orcl2 a X"\<close>, goal_cases)
        case 1
        then show ?case
          using Cons  weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
            matroid1.independent_empty_circuit  matroid2.independent_empty_circuit
          by auto
      next
        case 2
        then show ?case
          using  graph_inv_resulting_map  Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
            matroid1.independent_empty_circuit  matroid2.independent_empty_circuit
            X_in_carrier assms(2) assms(3) circuit2(2) assms(1) circuit2(1)
          apply (clarsimp,  subst treat2_circuit_tight_correct(2))
            apply (force)
           apply (metis (no_types, lifting) snd_conv)
          by(auto split: prod.split )
      next
        case 3
        then show ?case
          using  graph_inv_resulting_map  Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
            matroid1.independent_empty_circuit  matroid2.independent_empty_circuit
            X_in_carrier assms(2) assms(3) circuit1(2) assms(1) circuit1(1)
          apply (clarsimp,  subst treat1_circuit_tight_correct(2))
            apply (force)
           apply (metis (no_types, lifting) snd_conv)
          by(auto split: prod.split )
      next
        case 4
        then show ?case
          using Cons.prems X_in_carrier assms(2) assms(3) circuit2(2) weak_orcl2
          apply(clarsimp, subst treat2_circuit_tight_correct(2), simp)
           apply(rule treat1_circuit_tight_correct(1))
          using assms(1) circuit1(2)  graph_inv_resulting_map[of xs]
            Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
          by (subst treat1_circuit_tight_correct(2)| force simp add: circuit1(1) circuit2(1) assms(1,2,3))+
      qed
    qed
  qed (auto simp add:  graph.digraph_abs_empty)
  thus ?last_thesis
    using assms(5) resulting_map_is xs_prop(1) by presburger
  have "set xs  \<subseteq> carrier -to_set X \<Longrightarrow>
       graph.finite_graph (snd (snd (foldr f xs (vset_empty, vset_empty, empty))))"
  proof(induction xs)
    case (Cons a xs)
    show ?case
    proof(subst foldr_Cons, subst o_apply, subst f_def, unfold Let_def,
        (split prod.split, rule, rule, rule)+, goal_cases)
      case (1 x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e)
      then show ?case
      proof(cases "weak_orcl1 a X", all \<open>cases "weak_orcl2 a X"\<close>, goal_cases)
        case 1
        then show ?case
          using Cons  weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
          by auto
      next
        case 2
        then show ?case
          using  graph_inv_resulting_map  Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
            X_in_carrier assms(2) assms(3) circuit2(2)
          apply(clarsimp, subst treat2_circuit_tight_correct(3))
             apply (force)
            apply (metis (no_types, lifting) snd_conv)
          by(auto split: prod.split )
      next
        case 3
        then show ?case
          using  graph_inv_resulting_map  Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
            X_in_carrier assms(1) assms(3) circuit1(2)
          apply (clarsimp, subst treat1_circuit_tight_correct(3))
             apply (force)
            apply (metis (no_types, lifting) snd_conv)
          by(auto split: prod.split )
      next
        case 4
        then show ?case
          using Cons.prems
          apply(clarsimp, subst treat2_circuit_tight_correct(3))
          using   X_in_carrier assms(1) assms(3) circuit1(2)   weak_orcl1[OF  assms(3) X_in_carrier _ _ assms(1)]
            graph_inv_resulting_map Cons.IH
          by (fastforce intro!: treat1_circuit_tight_correct(1,3) circuit1(2)
              simp add: X_in_carrier assms(2) assms(3) circuit2(2) weak_orcl2)+
      qed
    qed
  qed (auto simp add: graph.adjmap.map_empty graph.finite_graph_def)
  thus "graph.finite_graph (compute_tight_graph_circuit X c1 c2 E_without_X)"
    using  resulting_map_is xs_prop(1)  assms(5) by auto
  have "set xs  \<subseteq> carrier -to_set X \<Longrightarrow>
       graph.finite_vsets (snd (snd (foldr f xs (vset_empty, vset_empty, empty))))"
  proof(induction xs)
    case (Cons a xs)
    show ?case
    proof(subst foldr_Cons, subst o_apply, subst f_def, unfold Let_def,
        (split prod.split, rule, rule, rule)+, goal_cases)
      case (1 x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e)
      then show ?case
      proof(cases "weak_orcl1 a X", all \<open>cases "weak_orcl2 a X"\<close>, goal_cases)
        case 1
        then show ?case
          using Cons  weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
          by auto
      next
        case 2
        then show ?case
          using  graph_inv_resulting_map  Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
            X_in_carrier assms(2) assms(3) circuit2(2)
          apply(clarsimp, subst treat2_circuit_tight_correct(4))
             apply (force)
            apply (metis (no_types, lifting) snd_conv)
          by(auto split: prod.split )
      next
        case 3
        then show ?case
          using  graph_inv_resulting_map  Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
            X_in_carrier assms(1) assms(3) circuit1(2)
          apply (clarsimp, subst treat1_circuit_tight_correct(4))
             apply (force)
            apply (metis (no_types, lifting) snd_conv)
          by(auto split: prod.split )
      next
        case 4
        then show ?case
          using Cons.prems
          apply(clarsimp, subst treat2_circuit_tight_correct(4))
          using   X_in_carrier assms(1) assms(3) circuit1(2)   weak_orcl1[OF  assms(3) X_in_carrier _ _ assms(1)]
            graph_inv_resulting_map Cons.IH
          by (fastforce intro!: treat1_circuit_tight_correct(1,4) circuit1(2)
              simp add: X_in_carrier assms(2) assms(3) circuit2(2) weak_orcl2)+
      qed
    qed
  qed (auto simp add: graph.adjmap.map_empty graph.finite_graph_def)
  thus "graph.finite_vsets (compute_tight_graph_circuit X c1 c2 E_without_X)"
    using  resulting_map_is xs_prop(1)  assms(5) by force
qed

lemma compute_tight_graph_circuit_meaning:
  assumes "indep1 (to_set X)" "indep2 (to_set X)" "set_invar X"
    "set_invar_red E_without_X" "to_set_red E_without_X = carrier - to_set X"
  shows "graph.digraph_abs (compute_tight_graph_circuit X c1 c2 E_without_X)
           = weighted_intersection_graph.Gbar carrier indep1 indep2 (c_lookup c1) (c_lookup c2) (to_set X)"
proof-
  interpret W: weighted_intersection_graph carrier indep1 indep2 "c_lookup c1" "c_lookup c2"
    by unfold_locales
  show ?thesis
    using matroid2.indep_subset_carrier[OF assms(2)]
    by(subst compute_tight_graph_circuit_correct(2)[OF assms(1-4) _])
      (auto simp add: matroid1.circuit_extensional[OF assms(1)] insert_Diff_if
        matroid2.circuit_extensional[OF assms(2)] A1_def A2_def assms(5)
        W.Gbar_def W.Abar1_def W.Abar2_def)
qed

text \<open>Restricting the (weight-agnostic) endpoint sets @{term "S (to_set X)"}/@{term "T (to_set X)"}
to their maximum-weight elements yields Frank's tight endpoints \<open>Sbar\<close>/\<open>Tbar\<close>.\<close>

lemma restrict_to_max_Sbar:
  assumes "c_invar c1" "vset_inv SX" "vset SX = S (to_set X)"
  shows "vset (restrict_to_max SX c1) =
           {y \<in> S (to_set X). c_lookup c1 y = Max (c_lookup c1 ` S (to_set X))}"
  by (simp add: restrict_to_max(2)[OF assms(1,2)] assms(3))

lemma restrict_to_max_Tbar:
  assumes "c_invar c2" "vset_inv TX" "vset TX = T (to_set X)"
  shows "vset (restrict_to_max TX c2) =
           {y \<in> T (to_set X). c_lookup c2 y = Max (c_lookup c2 ` T (to_set X))}"
  by (simp add: restrict_to_max(2)[OF assms(1,2)] assms(3))

text \<open>The mathematical crux of the best-so-far bound (\<open>w_invar\<close>'s last conjunct): a common independent
set that is locally optimal in \<^emph>\<open>both\<close> matroids for the split weights is of maximum original weight
among common independent sets of the same cardinality --- the greedy optimality criterion applied in
each matroid, added through the split \<open>c1 + c2 = corig\<close>.\<close>

lemma common_local_opt_max_worig:
  fixes c1 c2 corig :: "'a \<Rightarrow> real"
  assumes "indep1 X'" "indep2 X'" "matroid1.local_opt c1 X'" "matroid2.local_opt c2 X'"
    "\<forall> x \<in> carrier. c1 x + c2 x = corig x"
    "indep1 Y" "indep2 Y" "card Y = card X'"
  shows "sum corig Y \<le> sum corig X'"
proof-
  have Yc: "Y \<subseteq> carrier" and Xc: "X' \<subseteq> carrier"
    using matroid1.indep_subset_carrier assms(6,1) by auto
  have c1le: "sum c1 Y \<le> sum c1 X'"
    using matroid1.greedy_optimality[OF assms(1), THEN iffD2, OF assms(3)] assms(6,8)
    by (auto simp add: matroid1.max_weight_card_def)
  have c2le: "sum c2 Y \<le> sum c2 X'"
    using matroid2.greedy_optimality[OF assms(2), THEN iffD2, OF assms(4)] assms(7,8)
    by (auto simp add: matroid2.max_weight_card_def)
  have split: "sum corig Z = sum c1 Z + sum c2 Z" if "Z \<subseteq> carrier" for Z
  proof-
    have "sum corig Z = (\<Sum>x\<in>Z. c1 x + c2 x)"
      by (rule sum.cong[OF refl]) (use assms(5) that in auto)
    thus ?thesis by (simp add: sum.distrib)
  qed
  show ?thesis using c1le c2le split[OF Yc] split[OF Xc] by linarith
qed

text \<open>Bridging the abstract fold oracles to the \<open>eps_of\<close> characterisation: an inner \<open>eps_fold\<close> over a
conditional \<open>eps_min\<close> yields the minimum of its gap set, and an outer \<open>eps_fold_red\<close> whose body already
folds a per-element gap set yields the minimum over the union.\<close>

lemma eps_fold_is_eps_of:
  fixes g :: "'a \<Rightarrow> real"
  assumes "set_invar X"
  shows "eps_fold X (\<lambda>x acc. if P x then eps_min acc (g x) else acc) a
           = eps_of (g ` {x \<in> to_set X. P x}) a"
proof-
  obtain xs where "set xs = to_set X"
    "eps_fold X (\<lambda>x acc. if P x then eps_min acc (g x) else acc) a
       = foldr (\<lambda>x acc. if P x then eps_min acc (g x) else acc) xs a"
    using eps_fold[OF assms] by blast
  thus ?thesis by (simp add: foldr_eps_of)
qed

lemma eps_fold_red_is_eps_of_gen:
  fixes G :: "'a \<Rightarrow> real set"
  assumes "set_invar_red C" "\<And>y acc. body y acc = eps_of (G y) acc" "\<And>y. finite (G y)"
  shows "eps_fold_red C body a = eps_of (\<Union>y \<in> to_set_red C. G y) a"
proof-
  obtain ys where "set ys = to_set_red C" "eps_fold_red C body a = foldr body ys a"
    using eps_fold_red[OF assms(1)] by blast
  thus ?thesis by (simp add: foldr_eps_of_gen[OF assms(2,3)])
qed

subsubsection \<open>The computed \<open>\<epsilon>\<close> is the minimum boundary gap\<close>

text \<open>Each of the two blocks of the \<open>compute_eps\<close> body contributes exactly the set of weight gaps of
the arcs it ranges over (via @{thm [source] eps_fold_is_eps_of} for the inner probe folds).\<close>

lemma eps_block1:
  assumes "set_invar X"
  shows "(if weak_orcl1 y X then (if y \<in>\<^sub>G R then acc else eps_min acc (m1 - c_lookup c1 y))
          else (if y \<in>\<^sub>G R then acc
                else eps_fold X (\<lambda> x acc. if weak_orcl1 y (set_delete x X) \<and> x \<in>\<^sub>G R
                                 then eps_min acc (c_lookup c1 x - c_lookup c1 y) else acc) acc))
         = eps_of (if weak_orcl1 y X then (if y \<in>\<^sub>G R then {} else {m1 - c_lookup c1 y})
                   else (if y \<in>\<^sub>G R then {}
                         else (\<lambda>x. c_lookup c1 x - c_lookup c1 y) ` {x \<in> to_set X. weak_orcl1 y (set_delete x X) \<and> x \<in>\<^sub>G R})) acc"
  by (auto simp add: eps_of_single eps_fold_is_eps_of[OF assms])

lemma eps_block2:
  assumes "set_invar X"
  shows "(if weak_orcl2 y X then (if y \<in>\<^sub>G R then eps_min acc (m2 - c_lookup c2 y) else acc)
          else (if y \<in>\<^sub>G R
                then eps_fold X (\<lambda> x acc. if weak_orcl2 y (set_delete x X) \<and> x \<notin>\<^sub>G R
                                 then eps_min acc (c_lookup c2 x - c_lookup c2 y) else acc) acc
                else acc))
         = eps_of (if weak_orcl2 y X then (if y \<in>\<^sub>G R then {m2 - c_lookup c2 y} else {})
                   else (if y \<in>\<^sub>G R
                         then (\<lambda>x. c_lookup c2 x - c_lookup c2 y) ` {x \<in> to_set X. weak_orcl2 y (set_delete x X) \<and> x \<notin>\<^sub>G R}
                         else {})) acc"
  by (auto simp add: eps_of_single eps_fold_is_eps_of[OF assms])

text \<open>The gap set \<open>Dgap\<close> contributed by a single non-basis element \<open>y\<close>: the tight boundary arcs into
its two fundamental circuits, split as \<open>Dgap1\<close> (matroid 1, reachable side) and \<open>Dgap2\<close> (matroid 2).\<close>

definition "Dgap1 X R m1 c1 y =
  (if weak_orcl1 y X then (if y \<in>\<^sub>G R then {} else {m1 - c_lookup c1 y})
   else (if y \<in>\<^sub>G R then {}
         else (\<lambda>x. c_lookup c1 x - c_lookup c1 y) ` {x \<in> to_set X. weak_orcl1 y (set_delete x X) \<and> x \<in>\<^sub>G R}))"

definition "Dgap2 X R m2 c2 y =
  (if weak_orcl2 y X then (if y \<in>\<^sub>G R then {m2 - c_lookup c2 y} else {})
   else (if y \<in>\<^sub>G R
         then (\<lambda>x. c_lookup c2 x - c_lookup c2 y) ` {x \<in> to_set X. weak_orcl2 y (set_delete x X) \<and> x \<notin>\<^sub>G R}
         else {}))"

definition "Dgap X R m1 m2 c1 c2 y = Dgap1 X R m1 c1 y \<union> Dgap2 X R m2 c2 y"

lemma Dgap1_finite: "finite (to_set X) \<Longrightarrow> finite (Dgap1 X R m1 c1 y)"
  by (auto simp add: Dgap1_def)

lemma Dgap2_finite: "finite (to_set X) \<Longrightarrow> finite (Dgap2 X R m2 c2 y)"
  by (auto simp add: Dgap2_def)

lemma Dgap_finite: "finite (to_set X) \<Longrightarrow> finite (Dgap X R m1 m2 c1 c2 y)"
  by (auto simp add: Dgap_def Dgap1_finite Dgap2_finite)

lemma eps_block1':
  assumes "set_invar X"
  shows "(if weak_orcl1 y X then (if y \<in>\<^sub>G R then acc else eps_min acc (m1 - c_lookup c1 y))
          else (if y \<in>\<^sub>G R then acc
                else eps_fold X (\<lambda> x acc. if weak_orcl1 y (set_delete x X) \<and> x \<in>\<^sub>G R
                                 then eps_min acc (c_lookup c1 x - c_lookup c1 y) else acc) acc))
         = eps_of (Dgap1 X R m1 c1 y) acc"
  unfolding Dgap1_def by (rule eps_block1[OF assms])

lemma eps_block2':
  assumes "set_invar X"
  shows "(if weak_orcl2 y X then (if y \<in>\<^sub>G R then eps_min acc (m2 - c_lookup c2 y) else acc)
          else (if y \<in>\<^sub>G R
                then eps_fold X (\<lambda> x acc. if weak_orcl2 y (set_delete x X) \<and> x \<notin>\<^sub>G R
                                 then eps_min acc (c_lookup c2 x - c_lookup c2 y) else acc) acc
                else acc))
         = eps_of (Dgap2 X R m2 c2 y) acc"
  unfolding Dgap2_def by (rule eps_block2[OF assms])

text \<open>Hence \<open>compute_eps\<close> computes the minimum, over all non-basis elements, of all tight boundary gaps
(\<open>None\<close> meaning \<open>\<infinity>\<close> when no gap exists) --- the value Frank's algorithm reweights by.\<close>

lemma eps_meaning:
  assumes "set_invar X" "finite (to_set X)" "to_set X \<subseteq> carrier"
  shows "compute_eps X m1 m2 R c1 c2
           = eps_of (\<Union> y \<in> to_set_red (complement X). Dgap X R m1 m2 c1 c2 y) None"
  unfolding compute_eps_def
  apply (rule eps_fold_red_is_eps_of_gen[OF complement(1)[OF assms(1,3)]])
   apply (simp only: Let_def eps_block1'[OF assms(1)] eps_block2'[OF assms(1)]
                     eps_of_Un[OF Dgap2_finite[OF assms(2)] Dgap1_finite[OF assms(2)]])
   apply (simp add: Dgap_def Un_commute)
  apply (rule Dgap_finite[OF assms(2)])
  done

text \<open>Consequences of @{thm [source] eps_meaning}: the index set is finite, so the gap set is finite,
\<open>\<epsilon>\<close> (when defined) is its minimum, and hence a lower bound on every individual boundary gap --- the
key inequality feeding the reweighting lemma \<open>reweight_preserves_local_opt\<close>.\<close>

lemma eps_index_finite:
  assumes "set_invar X" "to_set X \<subseteq> carrier"
  shows "finite (to_set_red (complement X))"
proof -
  obtain xs where "set xs = to_set_red (complement X)"
    using eps_fold_red[OF complement(1)[OF assms]] by blast
  thus ?thesis by (metis List.finite_set)
qed

lemma eps_D_finite:
  assumes "set_invar X" "finite (to_set X)" "to_set X \<subseteq> carrier"
  shows "finite (\<Union> y \<in> to_set_red (complement X). Dgap X R m1 m2 c1 c2 y)"
  using eps_index_finite[OF assms(1,3)] Dgap_finite[OF assms(2)] by blast

lemma eps_is_Min:
  assumes "set_invar X" "finite (to_set X)" "to_set X \<subseteq> carrier"
    "compute_eps X m1 m2 R c1 c2 = Some e"
  shows "e = Min (\<Union> y \<in> to_set_red (complement X). Dgap X R m1 m2 c1 c2 y)
       \<and> (\<Union> y \<in> to_set_red (complement X). Dgap X R m1 m2 c1 c2 y) \<noteq> {}"
  using assms(4) unfolding eps_meaning[OF assms(1,2,3)] eps_of_None
  by (auto split: if_splits)

lemma eps_le_gap:
  assumes "set_invar X" "finite (to_set X)" "to_set X \<subseteq> carrier"
    "compute_eps X m1 m2 R c1 c2 = Some e"
    "y \<in> to_set_red (complement X)" "v \<in> Dgap X R m1 m2 c1 c2 y"
  shows "e \<le> v"
proof -
  have "v \<in> (\<Union> y \<in> to_set_red (complement X). Dgap X R m1 m2 c1 c2 y)"
    using assms(5,6) by blast
  thus ?thesis
    using eps_is_Min[OF assms(1-4)] eps_D_finite[OF assms(1,2,3)] by (simp add: Min_le)
qed

text \<open>Dually, \<open>\<epsilon>\<close> is \<^emph>\<open>attained\<close>: being the minimum of the (finite, nonempty) gap set, it equals some
individual boundary gap. This is what makes reweighting progress --- that gap becomes tight.\<close>

lemma eps_achieved:
  assumes "set_invar X" "to_set X \<subseteq> carrier" "indep1 (to_set X)"
    "compute_eps X m1 m2 R c1 c2 = Some e"
  shows "\<exists>y \<in> to_set_red (complement X). e \<in> Dgap X R m1 m2 c1 c2 y"
proof -
  have finX: "finite (to_set X)" using matroid1.indep_finite[OF assms(3)] .
  have mm: "e = Min (\<Union> y \<in> to_set_red (complement X). Dgap X R m1 m2 c1 c2 y)
            \<and> (\<Union> y \<in> to_set_red (complement X). Dgap X R m1 m2 c1 c2 y) \<noteq> {}"
    using eps_is_Min[OF assms(1) finX assms(2,4)] .
  have "Min (\<Union> y \<in> to_set_red (complement X). Dgap X R m1 m2 c1 c2 y)
          \<in> (\<Union> y \<in> to_set_red (complement X). Dgap X R m1 m2 c1 c2 y)"
    by (rule Min_in[OF eps_D_finite[OF assms(1) finX assms(2)] conjunct2[OF mm]])
  hence "e \<in> (\<Union> y \<in> to_set_red (complement X). Dgap X R m1 m2 c1 c2 y)"
    using conjunct1[OF mm] by simp
  thus ?thesis by blast
qed

text \<open>Two facts about the reachable set \<open>R = reach_set SbarX Gtight\<close>: it contains its source, and it is
closed under tight (\<open>Gbar\<close>) arcs. Together they force every boundary gap contributing to \<open>\<epsilon>\<close> to be
strictly positive (a zero gap is a tight boundary arc, which would enlarge \<open>R\<close> or complete a tight path).\<close>

lemma reach_set_mono:
  "graph.graph_inv G \<Longrightarrow> vset_inv Src \<Longrightarrow> vset Src \<subseteq> vset (reach_set Src G)"
  using reach_set(2) by fastforce

lemma reach_set_closed:
  assumes "graph.graph_inv G" "vset_inv Src" "x \<in> vset (reach_set Src G)" "(x, y) \<in> [G]\<^sub>g"
  shows "y \<in> vset (reach_set Src G)"
proof -
  from assms(3) reach_set(2)[OF assms(1,2)]
  obtain u where u: "u \<in> vset Src" "u = x \<or> (\<exists>p. vwalk_bet [G]\<^sub>g u p x)" by auto
  have xy: "vwalk_bet [G]\<^sub>g x [x, y] y" using assms(4) by (rule edges_are_vwalk_bet)
  have "\<exists>p. vwalk_bet [G]\<^sub>g u p y"
  proof (cases "u = x")
    case True
    show ?thesis using xy unfolding True by (intro exI)
  next
    case False
    then obtain p where "vwalk_bet [G]\<^sub>g u p x" using u(2) by blast
    from vwalk_bet_transitive[OF this xy] show ?thesis by (intro exI)
  qed
  thus ?thesis using u(1) reach_set(2)[OF assms(1,2)] by auto
qed

text \<open>The \<open>weak_orcl\<close> arc conditions occurring in \<open>Dgap\<close> characterise the auxiliary-graph arcs
\<open>A1\<close>/\<open>A2\<close> (via @{thm [source] matroid.circuit_extensional}).\<close>

lemma arc1_from_orcl:
  assumes "indep1 (to_set X)" "set_invar X" "to_set X \<subseteq> carrier" "x \<in> to_set X" "y \<in> carrier - to_set X"
    "weak_orcl1 y (set_delete x X)" "\<not> weak_orcl1 y X"
  shows "(x, y) \<in> A1 (to_set X)"
proof -
  have xy: "x \<noteq> y" using assms(4,5) by auto
  have ycarr: "y \<in> carrier" using assms(5) by auto
  have del: "to_set (set_delete x X) = to_set X - {x}"
    using set_delete(2)[OF assms(2)] assms(3,4) by auto
  have dinv: "set_invar (set_delete x X)" using set_delete(1)[OF assms(2)] assms(3,4) by auto
  have idel: "indep1 (to_set X - {x})" using assms(1) matroid1.indep_subset by auto
  have "weak_orcl1 y (set_delete x X) = indep1 (Set.insert y (to_set X - {x}))"
    using weak_orcl1[OF dinv _ ycarr _ idel[folded del]] del assms(3,5) by auto
  hence i1: "indep1 (Set.insert y (to_set X - {x}))" using assms(6) by simp
  have i2: "\<not> indep1 (Set.insert y (to_set X))"
    using assms(7) weak_orcl1[OF assms(2,3) ycarr _ assms(1)] assms(5) by auto
  have "Set.insert y (to_set X) - {x} = Set.insert y (to_set X - {x})" using xy by auto
  hence "x \<in> matroid1.the_circuit (Set.insert y (to_set X))"
    using matroid1.circuit_extensional[OF assms(1) ycarr] assms(4) i1 i2 by auto
  thus ?thesis using xy assms(5) by (auto simp add: A1_def)
qed

lemma arc2_from_orcl:
  assumes "indep2 (to_set X)" "set_invar X" "to_set X \<subseteq> carrier" "x \<in> to_set X" "y \<in> carrier - to_set X"
    "weak_orcl2 y (set_delete x X)" "\<not> weak_orcl2 y X"
  shows "(y, x) \<in> A2 (to_set X)"
proof -
  have xy: "x \<noteq> y" using assms(4,5) by auto
  have ycarr: "y \<in> carrier" using assms(5) by auto
  have del: "to_set (set_delete x X) = to_set X - {x}"
    using set_delete(2)[OF assms(2)] assms(3,4) by auto
  have dinv: "set_invar (set_delete x X)" using set_delete(1)[OF assms(2)] assms(3,4) by auto
  have idel: "indep2 (to_set X - {x})" using assms(1) matroid2.indep_subset by auto
  have "weak_orcl2 y (set_delete x X) = indep2 (Set.insert y (to_set X - {x}))"
    using weak_orcl2[OF dinv _ ycarr _ idel[folded del]] del assms(3,5) by auto
  hence i1: "indep2 (Set.insert y (to_set X - {x}))" using assms(6) by simp
  have i2: "\<not> indep2 (Set.insert y (to_set X))"
    using assms(7) weak_orcl2[OF assms(2,3) ycarr _ assms(1)] assms(5) by auto
  have "Set.insert y (to_set X) - {x} = Set.insert y (to_set X - {x})" using xy by auto
  hence "x \<in> matroid2.the_circuit (Set.insert y (to_set X))"
    using matroid2.circuit_extensional[OF assms(1) ycarr] assms(4) i1 i2 by auto
  thus ?thesis using xy assms(5) by (auto simp add: A2_def)
qed

text \<open>Frank's key fact: in the reweight branch (no tight augmenting path) the computed \<open>\<epsilon>\<close> is
\<^emph>\<open>strictly\<close> positive. Every boundary gap is \<open>\<ge> 0\<close> by local optimality, and \<open>\<noteq> 0\<close> because a zero
gap is a tight boundary arc, which --- by closure of \<open>R\<close> --- would enlarge \<open>R\<close> or complete a tight
\<open>Sbar\<close>-\<open>Tbar\<close> path, contradicting \<open>find_path = None\<close>.\<close>

lemma eps_pos:
  assumes iv1: "indep1 (to_set X)" and iv2: "indep2 (to_set X)"
    and sinv: "set_invar X" and Xc: "to_set X \<subseteq> carrier"
    and lo1: "matroid1.local_opt (c_lookup c1) (to_set X)"
    and lo2: "matroid2.local_opt (c_lookup c2) (to_set X)"
    and ci1: "c_invar c1" and ci2: "c_invar c2"
    and SXinv: "vset_inv SX" and SXis: "vset SX = S (to_set X)"
    and TXinv: "vset_inv TX" and TXis: "vset TX = T (to_set X)"
    and SbarX: "SbarX = restrict_to_max SX c1" and TbarX: "TbarX = restrict_to_max TX c2"
    and Gt_inv: "graph.graph_inv Gtight" and Gt_fg: "graph.finite_graph Gtight"
    and Gt_fv: "graph.finite_vsets Gtight"
    and Gt_dig: "graph.digraph_abs Gtight
                   = weighted_intersection_graph.Gbar carrier indep1 indep2 (c_lookup c1) (c_lookup c2) (to_set X)"
    and Rdef: "R = reach_set SbarX Gtight"
    and nopath: "find_path SbarX TbarX Gtight = None"
    and esome: "compute_eps X (weight_Max SX c1) (weight_Max TX c2) R c1 c2 = Some e"
  shows "0 < e"
proof -
  interpret W: weighted_intersection_graph carrier indep1 indep2 "c_lookup c1" "c_lookup c2"
    by unfold_locales
  define m1 where "m1 = weight_Max SX c1"
  define m2 where "m2 = weight_Max TX c2"
  have finX: "finite (to_set X)" using matroid1.indep_finite[OF iv1] .
  have compIs: "to_set_red (complement X) = carrier - to_set X" using complement(2)[OF sinv Xc] .
  have vsinvSbar: "vset_inv SbarX" using restrict_to_max(1)[OF ci1 SXinv] SbarX by simp
  have vsinvTbar: "vset_inv TbarX" using restrict_to_max(1)[OF ci2 TXinv] TbarX by simp
  have vsSbar: "vset SbarX = W.Sbar (to_set X)"
    using restrict_to_max_Sbar[OF ci1 SXinv SXis] SbarX by (simp add: W.Sbar_def)
  have vsTbar: "vset TbarX = W.Tbar (to_set X)"
    using restrict_to_max_Tbar[OF ci2 TXinv TXis] TbarX by (simp add: W.Tbar_def)
  have Sbarcarr: "vset SbarX \<subseteq> carrier"
    using vsSbar W.Sbar_subset S_in_carrier[OF iv1 iv2] by auto
  have Tbarcarr: "vset TbarX \<subseteq> carrier"
    using vsTbar W.Tbar_subset T_in_carrier[OF iv1 iv2] by auto
  have Gt_verts: "dVs (graph.digraph_abs Gtight) \<subseteq> carrier"
    using Gt_dig W.Gbar_subset dVs_A1A2_carrier[OF iv1 iv2] dVs_subset by (metis subset_trans)
  have Rinv: "vset_inv R" using reach_set(1)[OF Gt_inv vsinvSbar] Rdef by simp
  have isinR: "\<And>z. (z \<in>\<^sub>G R) = (z \<in> vset R)" using graph.vset.set.set_isin[OF Rinv] by simp
  have Sbar_R: "W.Sbar (to_set X) \<subseteq> vset R"
    using reach_set_mono[OF Gt_inv vsinvSbar] vsSbar Rdef by simp
  have Rclosed: "\<And>a b. a \<in> vset R \<Longrightarrow> (a, b) \<in> W.Gbar (to_set X) \<Longrightarrow> b \<in> vset R"
    using reach_set_closed[OF Gt_inv vsinvSbar] Gt_dig Rdef by auto
  have nopath': "\<nexists> p u v. (vwalk_bet (W.Gbar (to_set X)) u p v \<or> (p = [u] \<and> u = v))
                            \<and> u \<in> W.Sbar (to_set X) \<and> v \<in> W.Tbar (to_set X)"
    using find_path(1)[OF Gt_inv Gt_fg Gt_fv vsinvSbar vsinvTbar Sbarcarr Tbarcarr Gt_verts] nopath
    by (simp add: Gt_dig vsSbar vsTbar)
  have finS: "finite (S (to_set X))"
    using S_in_carrier[OF iv1 iv2] matroid1.carrier_finite by (auto intro: finite_subset)
  have finT: "finite (T (to_set X))"
    using T_in_carrier[OF iv1 iv2] matroid1.carrier_finite by (auto intro: finite_subset)
  \<comment> \<open>every gap contributing to \<open>\<epsilon>\<close> is strictly positive\<close>
  have all_pos: "0 < v"
    if vD: "v \<in> (\<Union> y \<in> to_set_red (complement X). Dgap X R m1 m2 c1 c2 y)" for v
  proof -
    from vD obtain y where yD: "y \<in> to_set_red (complement X)" and vy: "v \<in> Dgap X R m1 m2 c1 c2 y"
      by blast
    have yc: "y \<in> carrier - to_set X" using yD compIs by simp
    have yca: "y \<in> carrier" and ynX: "y \<notin> to_set X" using yc by auto
    from vy consider (D1) "v \<in> Dgap1 X R m1 c1 y" | (D2) "v \<in> Dgap2 X R m2 c2 y"
      by (auto simp add: Dgap_def)
    thus ?thesis
    proof cases
      case D1
      show ?thesis
      proof (cases "weak_orcl1 y X")
        case True
        hence veq: "v = m1 - c_lookup c1 y" and ynR: "y \<notin> vset R"
          using D1 isinR by (auto simp add: Dgap1_def split: if_splits)
        have yS: "y \<in> S (to_set X)"
          using True weak_orcl1[OF sinv Xc yca ynX iv1] yc by (auto simp add: S_def)
        have m1eq: "m1 = Max (c_lookup c1 ` S (to_set X))"
          using weight_Max[OF ci1 SXinv] yS SXis m1_def by auto
        have cle: "c_lookup c1 y \<le> m1" using yS finS m1eq by simp
        have "c_lookup c1 y \<noteq> m1"
        proof
          assume "c_lookup c1 y = m1"
          hence "y \<in> W.Sbar (to_set X)" using yS m1eq by (simp add: W.Sbar_def)
          thus False using Sbar_R ynR by auto
        qed
        thus ?thesis using cle veq by simp
      next
        case False
        with D1 obtain x where xX: "x \<in> to_set X" and xorcl: "weak_orcl1 y (set_delete x X)"
          and xR: "x \<in> vset R" and veq: "v = c_lookup c1 x - c_lookup c1 y"
          using isinR by (auto simp add: Dgap1_def split: if_splits)
        have ynR: "y \<notin> vset R" using D1 False isinR by (auto simp add: Dgap1_def split: if_splits)
        have arc: "(x, y) \<in> A1 (to_set X)" using arc1_from_orcl[OF iv1 sinv Xc xX yc xorcl False] .
        have cle: "c_lookup c1 y \<le> c_lookup c1 x"
          using arc lo1 yc by (auto simp add: A1_def matroid1.local_opt_def)
        have "c_lookup c1 x \<noteq> c_lookup c1 y"
        proof
          assume "c_lookup c1 x = c_lookup c1 y"
          hence "(x, y) \<in> W.Gbar (to_set X)" using arc by (simp add: W.Gbar_def W.Abar1_def)
          thus False using Rclosed xR ynR by auto
        qed
        thus ?thesis using cle veq by simp
      qed
    next
      case D2
      show ?thesis
      proof (cases "weak_orcl2 y X")
        case True
        hence veq: "v = m2 - c_lookup c2 y" and yR: "y \<in> vset R"
          using D2 isinR by (auto simp add: Dgap2_def split: if_splits)
        have yT: "y \<in> T (to_set X)"
          using True weak_orcl2[OF sinv Xc yca ynX iv2] yc by (auto simp add: T_def)
        have m2eq: "m2 = Max (c_lookup c2 ` T (to_set X))"
          using weight_Max[OF ci2 TXinv] yT TXis m2_def by auto
        have cle: "c_lookup c2 y \<le> m2" using yT finT m2eq by simp
        have "c_lookup c2 y \<noteq> m2"
        proof
          assume "c_lookup c2 y = m2"
          hence yTbar: "y \<in> W.Tbar (to_set X)" using yT m2eq by (simp add: W.Tbar_def)
          obtain u where u: "u \<in> vset SbarX" "u = y \<or> (\<exists>p. vwalk_bet (graph.digraph_abs Gtight) u p y)"
            using yR reach_set(2)[OF Gt_inv vsinvSbar] Rdef by auto
          have "\<exists>p. (vwalk_bet (W.Gbar (to_set X)) u p y \<or> (p = [u] \<and> u = y))"
            using u(2) Gt_dig by auto
          thus False using nopath' u(1) vsSbar yTbar by blast
        qed
        thus ?thesis using cle veq by simp
      next
        case False
        with D2 obtain x where xX: "x \<in> to_set X" and xorcl: "weak_orcl2 y (set_delete x X)"
          and xnR: "x \<notin> vset R" and veq: "v = c_lookup c2 x - c_lookup c2 y"
          using isinR by (auto simp add: Dgap2_def split: if_splits)
        have yR: "y \<in> vset R" using D2 False isinR by (auto simp add: Dgap2_def split: if_splits)
        have arc: "(y, x) \<in> A2 (to_set X)" using arc2_from_orcl[OF iv2 sinv Xc xX yc xorcl False] .
        have cle: "c_lookup c2 y \<le> c_lookup c2 x"
          using arc lo2 yc by (auto simp add: A2_def matroid2.local_opt_def)
        have "c_lookup c2 x \<noteq> c_lookup c2 y"
        proof
          assume "c_lookup c2 x = c_lookup c2 y"
          hence "(y, x) \<in> W.Gbar (to_set X)" using arc by (simp add: W.Gbar_def W.Abar2_def)
          thus False using Rclosed yR xnR by auto
        qed
        thus ?thesis using cle veq by simp
      qed
    qed
  qed
  have "e = Min (\<Union> y \<in> to_set_red (complement X). Dgap X R m1 m2 c1 c2 y)
      \<and> (\<Union> y \<in> to_set_red (complement X). Dgap X R m1 m2 c1 c2 y) \<noteq> {}"
    using eps_is_Min[OF sinv finX Xc] esome m1_def m2_def by simp
  thus "0 < e"
    using all_pos eps_D_finite[OF sinv finX Xc] by (simp add: Min_gr_iff)
qed

text \<open>Helpers for the reweight branch: local optimality is invariant under a global constant shift and
under agreement on \<open>carrier\<close>; the maximum \<open>S\<close>-weight is a lower bound on every basis element (dually for
\<open>T\<close>); and the arc conditions read back off \<open>A1\<close>/\<open>A2\<close> membership.\<close>

lemma local_opt1_add: "matroid1.local_opt c Y \<Longrightarrow> matroid1.local_opt (\<lambda>z. c z + k) Y"
  by (auto simp add: matroid1.local_opt_def add_right_mono)

lemma local_opt2_add: "matroid2.local_opt c Y \<Longrightarrow> matroid2.local_opt (\<lambda>z. c z + k) Y"
  by (auto simp add: matroid2.local_opt_def add_right_mono)

lemma local_opt2_cong_imp:
  assumes "to_set X \<subseteq> carrier" "\<forall>z\<in>carrier. c z = c' z" "matroid2.local_opt c (to_set X)"
  shows "matroid2.local_opt c' (to_set X)"
  unfolding matroid2.local_opt_def
proof (intro conjI ballI impI)
  fix y x assume yx: "y \<in> carrier - to_set X" "x \<in> matroid2.the_circuit (Set.insert y (to_set X)) - {y}"
  have "Set.insert y (to_set X) \<subseteq> carrier" using assms(1) yx(1) by auto
  hence xc: "x \<in> carrier" using yx(2) matroid2.the_circuit_X_in_X[of "Set.insert y (to_set X)" carrier] by auto
  have "c y \<le> c x" using assms(3) yx by (auto simp add: matroid2.local_opt_def)
  thus "c' y \<le> c' x" using assms(2) xc yx(1) by auto
next
  fix x y assume xy: "x \<in> to_set X" "y \<in> carrier - to_set X" "indep2 (Set.insert y (to_set X))"
  have "c y \<le> c x" using assms(3) xy by (auto simp add: matroid2.local_opt_def)
  thus "c' y \<le> c' x" using assms(1,2) xy by auto
qed

lemma Smax_le:
  assumes "matroid1.local_opt (c_lookup c1) (to_set X)" "indep1 (to_set X)" "indep2 (to_set X)"
    "x \<in> to_set X" "y0 \<in> S (to_set X)"
  shows "Max (c_lookup c1 ` S (to_set X)) \<le> c_lookup c1 x"
proof -
  have finS: "finite (S (to_set X))"
    using S_in_carrier[OF assms(2,3)] matroid1.carrier_finite by (auto intro: finite_subset)
  have "Max (c_lookup c1 ` S (to_set X)) \<in> c_lookup c1 ` S (to_set X)"
    using finS assms(5) by (intro Max_in) auto
  then obtain z where z: "z \<in> S (to_set X)" "c_lookup c1 z = Max (c_lookup c1 ` S (to_set X))" by auto
  have "c_lookup c1 z \<le> c_lookup c1 x"
    using assms(1,4) z(1) by (auto simp add: matroid1.local_opt_def S_def)
  thus ?thesis using z(2) by simp
qed

lemma Tmax_le:
  assumes "matroid2.local_opt (c_lookup c2) (to_set X)" "indep1 (to_set X)" "indep2 (to_set X)"
    "x \<in> to_set X" "y0 \<in> T (to_set X)"
  shows "Max (c_lookup c2 ` T (to_set X)) \<le> c_lookup c2 x"
proof -
  have finT: "finite (T (to_set X))"
    using T_in_carrier[OF assms(2,3)] matroid1.carrier_finite by (auto intro: finite_subset)
  have "Max (c_lookup c2 ` T (to_set X)) \<in> c_lookup c2 ` T (to_set X)"
    using finT assms(5) by (intro Max_in) auto
  then obtain z where z: "z \<in> T (to_set X)" "c_lookup c2 z = Max (c_lookup c2 ` T (to_set X))" by auto
  have "c_lookup c2 z \<le> c_lookup c2 x"
    using assms(1,4) z(1) by (auto simp add: matroid2.local_opt_def T_def)
  thus ?thesis using z(2) by simp
qed

lemma arc1_to_orcl:
  assumes "indep1 (to_set X)" "set_invar X" "to_set X \<subseteq> carrier" "(x, y) \<in> A1 (to_set X)"
  shows "x \<in> to_set X \<and> weak_orcl1 y (set_delete x X) \<and> \<not> weak_orcl1 y X \<and> y \<in> carrier - to_set X"
proof -
  have yc: "y \<in> carrier - to_set X" and xc: "x \<in> matroid1.the_circuit (Set.insert y (to_set X)) - {y}"
    using assms(4) by (auto simp add: A1_def)
  have ycarr: "y \<in> carrier" using yc by auto
  have subc: "Set.insert y (to_set X) \<subseteq> carrier" using assms(3) ycarr by auto
  have xins: "x \<in> Set.insert y (to_set X)"
    using xc matroid1.the_circuit_X_in_X[OF subset_refl subc] by auto
  have xy: "x \<noteq> y" using xc by auto
  have xX: "x \<in> to_set X" using xins xy by auto
  have dep: "\<not> indep1 (Set.insert y (to_set X))"
    using xc matroid1.the_circuit_non_empty_dependent by auto
  have "indep1 (Set.insert y (to_set X) - {x})"
    using xc matroid1.circuit_extensional[OF assms(1) ycarr] by auto
  hence idel: "indep1 (Set.insert y (to_set X - {x}))" using xy by (simp add: insert_Diff_if)
  have del: "to_set (set_delete x X) = to_set X - {x}" using set_delete(2)[OF assms(2)] assms(3) xX by auto
  have dinv: "set_invar (set_delete x X)" using set_delete(1)[OF assms(2)] assms(3) xX by auto
  have idelX: "indep1 (to_set X - {x})" using assms(1) matroid1.indep_subset by auto
  have "weak_orcl1 y (set_delete x X) = indep1 (Set.insert y (to_set X - {x}))"
    using weak_orcl1[OF dinv _ ycarr _ idelX[folded del]] del assms(3) yc by auto
  hence wo1: "weak_orcl1 y (set_delete x X)" using idel by simp
  have wo2: "\<not> weak_orcl1 y X"
    using weak_orcl1[OF assms(2,3) ycarr _ assms(1)] yc dep by auto
  show ?thesis using xX wo1 wo2 yc by simp
qed

lemma arc2_to_orcl:
  assumes "indep2 (to_set X)" "set_invar X" "to_set X \<subseteq> carrier" "(y, x) \<in> A2 (to_set X)"
  shows "x \<in> to_set X \<and> weak_orcl2 y (set_delete x X) \<and> \<not> weak_orcl2 y X \<and> y \<in> carrier - to_set X"
proof -
  have yc: "y \<in> carrier - to_set X" and xc: "x \<in> matroid2.the_circuit (Set.insert y (to_set X)) - {y}"
    using assms(4) by (auto simp add: A2_def)
  have ycarr: "y \<in> carrier" using yc by auto
  have subc: "Set.insert y (to_set X) \<subseteq> carrier" using assms(3) ycarr by auto
  have xins: "x \<in> Set.insert y (to_set X)"
    using xc matroid2.the_circuit_X_in_X[OF subset_refl subc] by auto
  have xy: "x \<noteq> y" using xc by auto
  have xX: "x \<in> to_set X" using xins xy by auto
  have dep: "\<not> indep2 (Set.insert y (to_set X))"
    using xc matroid2.the_circuit_non_empty_dependent by auto
  have "indep2 (Set.insert y (to_set X) - {x})"
    using xc matroid2.circuit_extensional[OF assms(1) ycarr] by auto
  hence idel: "indep2 (Set.insert y (to_set X - {x}))" using xy by (simp add: insert_Diff_if)
  have del: "to_set (set_delete x X) = to_set X - {x}" using set_delete(2)[OF assms(2)] assms(3) xX by auto
  have dinv: "set_invar (set_delete x X)" using set_delete(1)[OF assms(2)] assms(3) xX by auto
  have idelX: "indep2 (to_set X - {x})" using assms(1) matroid2.indep_subset by auto
  have "weak_orcl2 y (set_delete x X) = indep2 (Set.insert y (to_set X - {x}))"
    using weak_orcl2[OF dinv _ ycarr _ idelX[folded del]] del assms(3) yc by auto
  hence wo1: "weak_orcl2 y (set_delete x X)" using idel by simp
  have wo2: "\<not> weak_orcl2 y X"
    using weak_orcl2[OF assms(2,3) ycarr _ assms(1)] yc dep by auto
  show ?thesis using xX wo1 wo2 yc by simp
qed

lemma reach_set_carrier:
  assumes "graph.graph_inv G" "vset_inv Src" "vset Src \<subseteq> carrier" "dVs [G]\<^sub>g \<subseteq> carrier"
  shows "vset (reach_set Src G) \<subseteq> carrier"
proof
  fix v assume "v \<in> vset (reach_set Src G)"
  then obtain u where u: "u \<in> vset Src" "u = v \<or> (\<exists>p. vwalk_bet [G]\<^sub>g u p v)"
    using reach_set(2)[OF assms(1,2)] by auto
  show "v \<in> carrier"
  proof (cases "u = v")
    case True thus ?thesis using u(1) assms(3) by auto
  next
    case False
    then obtain p where "vwalk_bet [G]\<^sub>g u p v" using u(2) by auto
    hence "v \<in> dVs [G]\<^sub>g" using vwalk_bet_endpoints by fastforce
    thus ?thesis using assms(4) by auto
  qed
qed

text \<open>Reachability and shortest-path emptiness depend on a digraph only through its abstract arc set, so
two graphs with the same @{const graph.digraph_abs} (e.g. the plain and the circuit tight graph) yield the
same reachable set and the same \<open>find_path = None\<close> verdict. These bridge the two algorithm variants.\<close>

lemma reach_set_cong:
  assumes "graph.graph_inv G" "graph.graph_inv G'" "vset_inv Src" "graph.digraph_abs G = graph.digraph_abs G'"
  shows "vset (reach_set Src G) = vset (reach_set Src G')"
  using reach_set(2)[OF assms(1) assms(3)] reach_set(2)[OF assms(2) assms(3)] assms(4) by simp

lemma find_path_None_cong:
  assumes "graph.graph_inv G" "graph.finite_graph G" "graph.finite_vsets G"
    "graph.graph_inv G'" "graph.finite_graph G'" "graph.finite_vsets G'"
    "vset_inv Sv" "vset_inv Tv" "vset Sv \<subseteq> carrier" "vset Tv \<subseteq> carrier"
    "dVs (graph.digraph_abs G) \<subseteq> carrier" "graph.digraph_abs G = graph.digraph_abs G'"
  shows "(find_path Sv Tv G = None) = (find_path Sv Tv G' = None)"
  using find_path(1)[OF assms(1,2,3,7,8,9,10,11)]
        find_path(1)[OF assms(4,5,6,7,8,9,10) assms(11)[unfolded assms(12)]]
  by (simp add: assms(12))

text \<open>Reweight branch: shifting the split by the computed \<open>\<epsilon>\<close> preserves \<open>w_invar\<close>. Local optimality
survives by \<open>reweight_preserves_local_opt\<close> --- directly for matroid 1 (decrease on \<open>R\<close>),
and for matroid 2 via the complementary set \<open>carrier - R\<close> plus a global \<open>+\<epsilon>\<close> shift. The gap inequalities
feeding it come from @{thm [source] eps_le_gap} (with @{thm [source] Smax_le}/@{thm [source] Tmax_le} for
the endpoint families); the original weight \<open>worig\<close> and the solution are untouched.\<close>

lemma w_invar_reweight:
  assumes "w_invar st" "weighted_reweight_cond st"
  shows "w_invar (weighted_reweight_upd st)"
proof (rule P_of_weighted_reweightI[OF assms(2)])
  fix SX TX G SbarX TbarX Gtight R e X c1 c2
  assume df: "X = wsol st" "c1 = wc1 st" "c2 = wc2 st"
    "compute_graph X (complement X) = (SX, TX, G)"
    "SbarX = restrict_to_max SX c1" "TbarX = restrict_to_max TX c2"
    "Gtight = compute_tight_graph X c1 c2 (complement X)"
    "R = reach_set SbarX Gtight"
    "find_path SbarX TbarX Gtight = None"
    "compute_eps X (weight_Max SX c1) (weight_Max TX c2) R c1 c2 = Some e"
  interpret W: weighted_intersection_graph carrier indep1 indep2 "c_lookup c1" "c_lookup c2"
    by unfold_locales
  define m1 where "m1 = weight_Max SX c1"
  define m2 where "m2 = weight_Max TX c2"
  have facts: "set_invar (wsol st)" "to_set (wsol st) \<subseteq> carrier"
    "indep1 (to_set (wsol st))" "indep2 (to_set (wsol st))"
    "c_invar (wc1 st)" "c_invar (wc2 st)" "c_invar (worig st)"
    "\<forall>z\<in>carrier. c_lookup (wc1 st) z + c_lookup (wc2 st) z = c_lookup (worig st) z"
    "matroid1.local_opt (c_lookup (wc1 st)) (to_set (wsol st))"
    "matroid2.local_opt (c_lookup (wc2 st)) (to_set (wsol st))"
    "set_invar (wbest st)" "indep1 (to_set (wbest st))" "indep2 (to_set (wbest st))"
    "\<forall>Y. indep1 Y \<and> indep2 Y \<and> card Y \<le> card (to_set (wsol st))
       \<longrightarrow> sum (c_lookup (worig st)) Y \<le> sum (c_lookup (worig st)) (to_set (wbest st))"
    using assms(1) by (simp_all add: w_invar_def)
  have iv1: "indep1 (to_set X)" and iv2: "indep2 (to_set X)" and sinv: "set_invar X"
    and Xc: "to_set X \<subseteq> carrier" and ci1: "c_invar c1" and ci2: "c_invar c2"
    and lo1: "matroid1.local_opt (c_lookup c1) (to_set X)"
    and lo2: "matroid2.local_opt (c_lookup c2) (to_set X)"
    using facts df(1,2,3) by simp_all
  have finX: "finite (to_set X)" using matroid1.indep_finite[OF iv1] .
  have cInvComp: "set_invar_red (complement X)" using complement(1)[OF sinv Xc] .
  have compIs: "to_set_red (complement X) = carrier - to_set X" using complement(2)[OF sinv Xc] .
  note cgc = U.compute_graph_correct[OF iv1 iv2 sinv cInvComp, OF compIs[THEN equalityD1] df(4)]
  note cgm = U.compute_graph_meaning[OF iv1 iv2 sinv cInvComp compIs df(4)]
  have SXinv: "vset_inv SX" and TXinv: "vset_inv TX"
    and SXis: "vset SX = S (to_set X)" and TXis: "vset TX = T (to_set X)"
    using cgc(1,2) cgm(1,2) by simp_all
  note ctc = compute_tight_graph_correct[OF iv1 iv2 sinv cInvComp, OF compIs[THEN equalityD1]]
  have Gt_inv: "graph.graph_inv Gtight" and Gt_fg: "graph.finite_graph Gtight"
    and Gt_fv: "graph.finite_vsets Gtight"
    using ctc(1,3,4) df(7) by simp_all
  have Gt_dig: "graph.digraph_abs Gtight = W.Gbar (to_set X)"
    using compute_tight_graph_meaning[OF iv1 iv2 sinv cInvComp compIs] df(7) by simp
  have vsinvSbar: "vset_inv SbarX" using restrict_to_max(1)[OF ci1 SXinv] df(5) by simp
  have vsSbar: "vset SbarX = W.Sbar (to_set X)"
    using restrict_to_max_Sbar[OF ci1 SXinv SXis] df(5) by (simp add: W.Sbar_def)
  have Sbarcarr: "vset SbarX \<subseteq> carrier" using vsSbar W.Sbar_subset S_in_carrier[OF iv1 iv2] by auto
  have Gt_verts: "dVs (graph.digraph_abs Gtight) \<subseteq> carrier"
    using Gt_dig W.Gbar_subset dVs_A1A2_carrier[OF iv1 iv2] dVs_subset by (metis subset_trans)
  have Rinv: "vset_inv R" using reach_set(1)[OF Gt_inv vsinvSbar] df(8) by simp
  have RsubC: "vset R \<subseteq> carrier"
    using reach_set_carrier[OF Gt_inv vsinvSbar Sbarcarr Gt_verts] df(8) by simp
  have isinR: "\<And>z. (z \<in>\<^sub>G R) = (z \<in> vset R)" using graph.vset.set.set_isin[OF Rinv] by simp
  have epos: "0 < e"
    using eps_pos[OF iv1 iv2 sinv Xc lo1 lo2 ci1 ci2 SXinv SXis TXinv TXis
                     df(5) df(6) Gt_inv Gt_fg Gt_fv Gt_dig df(8) df(9) df(10)] .
  \<comment> \<open>the four gap inequalities\<close>
  have yD: "\<And>y. y \<in> carrier - to_set X \<Longrightarrow> y \<in> to_set_red (complement X)" using compIs by simp
  have gapA1: "e \<le> c_lookup c1 x - c_lookup c1 y"
    if "(x, y) \<in> A1 (to_set X)" "x \<in> vset R" "y \<notin> vset R" for x y
  proof -
    have o: "x \<in> to_set X \<and> weak_orcl1 y (set_delete x X) \<and> \<not> weak_orcl1 y X \<and> y \<in> carrier - to_set X"
      using arc1_to_orcl[OF iv1 sinv Xc that(1)] .
    have "c_lookup c1 x - c_lookup c1 y \<in> Dgap X R m1 m2 c1 c2 y"
      using o that(2,3) isinR by (auto simp add: Dgap_def Dgap1_def)
    thus ?thesis using eps_le_gap[OF sinv finX Xc df(10)[folded m1_def m2_def] yD[OF conjunct2[OF conjunct2[OF conjunct2[OF o]]]]] by simp
  qed
  have gapB1: "e \<le> c_lookup c1 x - c_lookup c1 y"
    if "x \<in> to_set X" "y \<in> S (to_set X)" "y \<notin> vset R" for x y
  proof -
    have yc: "y \<in> carrier - to_set X" and iy: "indep1 (Set.insert y (to_set X))"
      using that(2) by (auto simp add: S_def)
    have woy: "weak_orcl1 y X" using weak_orcl1[OF sinv Xc _ _ iv1] yc iy by auto
    have "m1 - c_lookup c1 y \<in> Dgap X R m1 m2 c1 c2 y"
      using woy that(3) isinR by (auto simp add: Dgap_def Dgap1_def)
    hence e_le: "e \<le> m1 - c_lookup c1 y"
      using eps_le_gap[OF sinv finX Xc df(10)[folded m1_def m2_def] yD[OF yc]] by simp
    have "m1 = Max (c_lookup c1 ` S (to_set X))"
      using weight_Max[OF ci1 SXinv] that(2) SXis m1_def by auto
    hence "m1 \<le> c_lookup c1 x" using Smax_le[OF lo1 iv1 iv2 that(1,2)] by simp
    thus ?thesis using e_le by simp
  qed
  have gapA2: "e \<le> c_lookup c2 x - c_lookup c2 y"
    if "(y, x) \<in> A2 (to_set X)" "y \<in> vset R" "x \<notin> vset R" for x y
  proof -
    have o: "x \<in> to_set X \<and> weak_orcl2 y (set_delete x X) \<and> \<not> weak_orcl2 y X \<and> y \<in> carrier - to_set X"
      using arc2_to_orcl[OF iv2 sinv Xc that(1)] .
    have "c_lookup c2 x - c_lookup c2 y \<in> Dgap X R m1 m2 c1 c2 y"
      using o that(2,3) isinR by (auto simp add: Dgap_def Dgap2_def)
    thus ?thesis using eps_le_gap[OF sinv finX Xc df(10)[folded m1_def m2_def] yD[OF conjunct2[OF conjunct2[OF conjunct2[OF o]]]]] by simp
  qed
  have gapB2: "e \<le> c_lookup c2 x - c_lookup c2 y"
    if "x \<in> to_set X" "y \<in> T (to_set X)" "y \<in> vset R" for x y
  proof -
    have yc: "y \<in> carrier - to_set X" and iy: "indep2 (Set.insert y (to_set X))"
      using that(2) by (auto simp add: T_def)
    have woy: "weak_orcl2 y X" using weak_orcl2[OF sinv Xc _ _ iv2] yc iy by auto
    have "m2 - c_lookup c2 y \<in> Dgap X R m1 m2 c1 c2 y"
      using woy that(3) isinR by (auto simp add: Dgap_def Dgap2_def)
    hence e_le: "e \<le> m2 - c_lookup c2 y"
      using eps_le_gap[OF sinv finX Xc df(10)[folded m1_def m2_def] yD[OF yc]] by simp
    have "m2 = Max (c_lookup c2 ` T (to_set X))"
      using weight_Max[OF ci2 TXinv] that(2) TXis m2_def by auto
    hence "m2 \<le> c_lookup c2 x" using Tmax_le[OF lo2 iv1 iv2 that(1,2)] by simp
    thus ?thesis using e_le by simp
  qed
  \<comment> \<open>matroid 1: decrease on \<open>R\<close>\<close>
  have lo1': "matroid1.local_opt (\<lambda>z. if z \<in> vset R then c_lookup c1 z - e else c_lookup c1 z) (to_set X)"
  proof (rule matroid1.reweight_preserves_local_opt[OF iv1 lo1 RsubC epos])
    fix y x assume A: "y \<in> carrier - to_set X" "x \<in> matroid1.the_circuit (Set.insert y (to_set X)) - {y}"
      "x \<in> vset R" "y \<notin> vset R"
    have arc: "(x, y) \<in> A1 (to_set X)" using A(1,2) by (auto simp add: A1_def)
    show "e \<le> c_lookup c1 x - c_lookup c1 y" using gapA1[OF arc A(3) A(4)] .
  next
    fix x y assume B: "x \<in> to_set X" "y \<in> carrier - to_set X" "indep1 (Set.insert y (to_set X))"
      "x \<in> vset R" "y \<notin> vset R"
    have yS: "y \<in> S (to_set X)" using B(2,3) by (auto simp add: S_def)
    show "e \<le> c_lookup c1 x - c_lookup c1 y" using gapB1[OF B(1) yS B(5)] .
  qed
  have wc1'eq: "c_lookup (c_shift R (- e) c1) = (\<lambda>z. if z \<in> vset R then c_lookup c1 z - e else c_lookup c1 z)"
    using c_shift(2)[OF ci1 Rinv] by auto
  have C9: "matroid1.local_opt (c_lookup (c_shift R (- e) c1)) (to_set X)" using lo1' wc1'eq by simp
  \<comment> \<open>matroid 2: decrease on the complement, then a global \<open>+\<epsilon>\<close> shift\<close>
  have lo_d: "matroid2.local_opt (\<lambda>z. if z \<in> carrier - vset R then c_lookup c2 z - e else c_lookup c2 z) (to_set X)"
  proof (rule matroid2.reweight_preserves_local_opt[OF iv2 lo2 Diff_subset epos])
    fix y x assume A: "y \<in> carrier - to_set X" "x \<in> matroid2.the_circuit (Set.insert y (to_set X)) - {y}"
      "x \<in> carrier - vset R" "y \<notin> carrier - vset R"
    have arc: "(y, x) \<in> A2 (to_set X)" using A(1,2) by (auto simp add: A2_def)
    have xnR: "x \<notin> vset R" using A(3) by simp
    have yR: "y \<in> vset R" using A(1,4) by simp
    show "e \<le> c_lookup c2 x - c_lookup c2 y" using gapA2[OF arc yR xnR] .
  next
    fix x y assume B: "x \<in> to_set X" "y \<in> carrier - to_set X" "indep2 (Set.insert y (to_set X))"
      "x \<in> carrier - vset R" "y \<notin> carrier - vset R"
    have yT: "y \<in> T (to_set X)" using B(2,3) by (auto simp add: T_def)
    have yR: "y \<in> vset R" using B(2,5) by simp
    show "e \<le> c_lookup c2 x - c_lookup c2 y" using gapB2[OF B(1) yT yR] .
  qed
  have lo_de: "matroid2.local_opt (\<lambda>z. (if z \<in> carrier - vset R then c_lookup c2 z - e else c_lookup c2 z) + e) (to_set X)"
    using local_opt2_add[OF lo_d] .
  have wc2'eq: "c_lookup (c_shift R e c2) = (\<lambda>z. if z \<in> vset R then c_lookup c2 z + e else c_lookup c2 z)"
    using c_shift(2)[OF ci2 Rinv] by auto
  have agree: "\<forall>z\<in>carrier. (if z \<in> carrier - vset R then c_lookup c2 z - e else c_lookup c2 z) + e
                            = c_lookup (c_shift R e c2) z"
    using RsubC by (auto simp add: wc2'eq)
  have C10: "matroid2.local_opt (c_lookup (c_shift R e c2)) (to_set X)"
    using local_opt2_cong_imp[OF Xc agree lo_de] .
  \<comment> \<open>weight-map invariants\<close>
  have C5: "c_invar (c_shift R (- e) c1)" using c_shift(1)[OF ci1 Rinv] .
  have C6: "c_invar (c_shift R e c2)" using c_shift(1)[OF ci2 Rinv] .
  have C8: "\<forall>z\<in>carrier. c_lookup (c_shift R (- e) c1) z + c_lookup (c_shift R e c2) z = c_lookup (worig st) z"
  proof
    fix z assume zc: "z \<in> carrier"
    have "c_lookup (c_shift R (- e) c1) z + c_lookup (c_shift R e c2) z = c_lookup c1 z + c_lookup c2 z"
      by (simp add: wc1'eq wc2'eq)
    also have "\<dots> = c_lookup (worig st) z" using facts(8) df(2,3) zc by simp
    finally show "c_lookup (c_shift R (- e) c1) z + c_lookup (c_shift R e c2) z = c_lookup (worig st) z" .
  qed
  show "w_invar (reweight R e st)"
    unfolding w_invar_def reweight_def
    using facts(1,2,3,4,7,11,12,13,14) C5 C6 C8 C9 C10 df(1,2,3) by simp \<comment> \<open>assemble\<close>
qed

text \<open>A walk in a digraph stays inside any vertex set closed under its arcs --- used to turn the
emptiness of the gap set (no boundary arc leaves \<open>R\<close>) into the absence of an augmenting path.\<close>

lemma walk_stays_closed:
  assumes "vwalk_bet E x p y" "x \<in> R" "\<And>a b. (a, b) \<in> E \<Longrightarrow> a \<in> R \<Longrightarrow> b \<in> R"
  shows "y \<in> R"
proof -
  have "x \<in> R \<longrightarrow> y \<in> R" using assms(1)
  proof (induction rule: induct_vwalk_bet)
    case (path1 v) thus ?case by simp
  next
    case (path2 v v' vs b) thus ?case using assms(3) by auto
  qed
  thus ?thesis using assms(2) by simp
qed

lemma weighted_stop_condE:
  "weighted_stop_cond st \<Longrightarrow>
   (\<And> SX TX G SbarX TbarX Gtight R X c1 c2.
       X = wsol st \<Longrightarrow> c1 = wc1 st \<Longrightarrow> c2 = wc2 st \<Longrightarrow>
       compute_graph X (complement X) = (SX, TX, G) \<Longrightarrow>
       SbarX = restrict_to_max SX c1 \<Longrightarrow> TbarX = restrict_to_max TX c2 \<Longrightarrow>
       Gtight = compute_tight_graph X c1 c2 (complement X) \<Longrightarrow>
       R = reach_set SbarX Gtight \<Longrightarrow>
       find_path SbarX TbarX Gtight = None \<Longrightarrow>
       compute_eps X (weight_Max SX c1) (weight_Max TX c2) R c1 c2 = None \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding weighted_stop_cond_def Let_def
  apply(cases "compute_graph (wsol st) (complement (wsol st))", simp)
  subgoal for a b c
    apply(cases "find_path (restrict_to_max a (wc1 st)) (restrict_to_max b (wc2 st))
                          (compute_tight_graph (wsol st) (wc1 st) (wc2 st) (complement (wsol st)))")
     apply(cases "compute_eps (wsol st) (weight_Max a (wc1 st)) (weight_Max b (wc2 st))
                    (reach_set (restrict_to_max a (wc1 st))
                       (compute_tight_graph (wsol st) (wc1 st) (wc2 st) (complement (wsol st))))
                    (wc1 st) (wc2 st)")
    by auto
  done

text \<open>Stop branch: when no tight path exists and \<open>\<epsilon> = \<infinity>\<close> (the gap set is empty), no boundary arc
leaves \<open>R\<close>, so \<open>R\<close> separates \<open>S\<close> from \<open>T\<close> in the full auxiliary graph --- there is no augmenting path,
hence (by @{thm [source] if_no_augpath_then_maximum}) the current solution has maximum common cardinality.
Combined with the best-so-far bound of \<open>w_invar\<close>, \<open>wbest\<close> is then of maximum original weight overall.\<close>

lemma w_invar_max_found:
  assumes "w_invar st" "weighted_stop_cond st"
  shows "indep1 (to_set (wbest st)) \<and> indep2 (to_set (wbest st))
         \<and> (\<forall>Y. indep1 Y \<and> indep2 Y \<longrightarrow>
              sum (c_lookup (worig st)) Y \<le> sum (c_lookup (worig st)) (to_set (wbest st)))"
proof (rule weighted_stop_condE[OF assms(2)])
  fix SX TX G SbarX TbarX Gtight R X c1 c2
  assume df: "X = wsol st" "c1 = wc1 st" "c2 = wc2 st"
    "compute_graph X (complement X) = (SX, TX, G)"
    "SbarX = restrict_to_max SX c1" "TbarX = restrict_to_max TX c2"
    "Gtight = compute_tight_graph X c1 c2 (complement X)"
    "R = reach_set SbarX Gtight"
    "find_path SbarX TbarX Gtight = None"
    "compute_eps X (weight_Max SX c1) (weight_Max TX c2) R c1 c2 = None"
  define m1 where "m1 = weight_Max SX c1"
  define m2 where "m2 = weight_Max TX c2"
  have facts: "set_invar (wsol st)" "to_set (wsol st) \<subseteq> carrier"
    "indep1 (to_set (wsol st))" "indep2 (to_set (wsol st))"
    "c_invar (wc1 st)" "c_invar (wc2 st)" "c_invar (worig st)"
    "\<forall>z\<in>carrier. c_lookup (wc1 st) z + c_lookup (wc2 st) z = c_lookup (worig st) z"
    "matroid1.local_opt (c_lookup (wc1 st)) (to_set (wsol st))"
    "matroid2.local_opt (c_lookup (wc2 st)) (to_set (wsol st))"
    "set_invar (wbest st)" "indep1 (to_set (wbest st))" "indep2 (to_set (wbest st))"
    "\<forall>Y. indep1 Y \<and> indep2 Y \<and> card Y \<le> card (to_set (wsol st))
       \<longrightarrow> sum (c_lookup (worig st)) Y \<le> sum (c_lookup (worig st)) (to_set (wbest st))"
    using assms(1) by (simp_all add: w_invar_def)
  have iv1: "indep1 (to_set X)" and iv2: "indep2 (to_set X)" and sinv: "set_invar X"
    and Xc: "to_set X \<subseteq> carrier" and ci1: "c_invar c1" and ci2: "c_invar c2"
    using facts df(1,2,3) by simp_all
  have finX: "finite (to_set X)" using matroid1.indep_finite[OF iv1] .
  have cInvComp: "set_invar_red (complement X)" using complement(1)[OF sinv Xc] .
  have compIs: "to_set_red (complement X) = carrier - to_set X" using complement(2)[OF sinv Xc] .
  note cgc = U.compute_graph_correct[OF iv1 iv2 sinv cInvComp, OF compIs[THEN equalityD1] df(4)]
  note cgm = U.compute_graph_meaning[OF iv1 iv2 sinv cInvComp compIs df(4)]
  have SXinv: "vset_inv SX" and SXis: "vset SX = S (to_set X)" and TXis: "vset TX = T (to_set X)"
    using cgc(1) cgm(1,2) by simp_all
  note ctc = compute_tight_graph_correct[OF iv1 iv2 sinv cInvComp, OF compIs[THEN equalityD1]]
  have Gt_inv: "graph.graph_inv Gtight" using ctc(1) df(7) by simp
  have vsinvSbar: "vset_inv SbarX" using restrict_to_max(1)[OF ci1 SXinv] df(5) by simp
  have Rinv: "vset_inv R" using reach_set(1)[OF Gt_inv vsinvSbar] df(8) by simp
  have isinR: "\<And>z. (z \<in>\<^sub>G R) = (z \<in> vset R)" using graph.vset.set.set_isin[OF Rinv] by simp
  have yD: "\<And>y. y \<in> carrier - to_set X \<Longrightarrow> y \<in> to_set_red (complement X)" using compIs by simp
  \<comment> \<open>the gap set is empty\<close>
  have D_empty: "(\<Union> y \<in> to_set_red (complement X). Dgap X R m1 m2 c1 c2 y) = {}"
    using df(10)[folded m1_def m2_def] unfolding eps_meaning[OF sinv finX Xc] eps_of_None
    by (auto split: if_splits)
  \<comment> \<open>hence \<open>R\<close> contains \<open>S\<close>, avoids \<open>T\<close>, and is closed under all auxiliary arcs\<close>
  have Ssub: "S (to_set X) \<subseteq> vset R"
  proof
    fix y assume yS: "y \<in> S (to_set X)"
    have yc: "y \<in> carrier - to_set X" and iy: "indep1 (Set.insert y (to_set X))"
      using yS by (auto simp add: S_def)
    have woy: "weak_orcl1 y X" using weak_orcl1[OF sinv Xc _ _ iv1] yc iy by auto
    show "y \<in> vset R"
    proof (rule ccontr)
      assume "y \<notin> vset R"
      hence "m1 - c_lookup c1 y \<in> Dgap X R m1 m2 c1 c2 y"
        using woy isinR by (auto simp add: Dgap_def Dgap1_def)
      thus False using D_empty yD[OF yc] by auto
    qed
  qed
  have Tdisj: "T (to_set X) \<inter> vset R = {}"
  proof (rule ccontr)
    assume "T (to_set X) \<inter> vset R \<noteq> {}"
    then obtain y where yT: "y \<in> T (to_set X)" and yR: "y \<in> vset R" by auto
    have yc: "y \<in> carrier - to_set X" and iy: "indep2 (Set.insert y (to_set X))"
      using yT by (auto simp add: T_def)
    have woy: "weak_orcl2 y X" using weak_orcl2[OF sinv Xc _ _ iv2] yc iy by auto
    have "m2 - c_lookup c2 y \<in> Dgap X R m1 m2 c1 c2 y"
      using woy yR isinR by (auto simp add: Dgap_def Dgap2_def)
    thus False using D_empty yD[OF yc] by auto
  qed
  have clA1: "\<And>x y. (x, y) \<in> A1 (to_set X) \<Longrightarrow> x \<in> vset R \<Longrightarrow> y \<in> vset R"
  proof -
    fix x y assume arc: "(x, y) \<in> A1 (to_set X)" and xR: "x \<in> vset R"
    have o: "x \<in> to_set X \<and> weak_orcl1 y (set_delete x X) \<and> \<not> weak_orcl1 y X \<and> y \<in> carrier - to_set X"
      using arc1_to_orcl[OF iv1 sinv Xc arc] .
    show "y \<in> vset R"
    proof (rule ccontr)
      assume "y \<notin> vset R"
      hence "c_lookup c1 x - c_lookup c1 y \<in> Dgap X R m1 m2 c1 c2 y"
        using o xR isinR by (auto simp add: Dgap_def Dgap1_def)
      thus False using D_empty yD[OF conjunct2[OF conjunct2[OF conjunct2[OF o]]]] by auto
    qed
  qed
  have clA2: "\<And>x y. (y, x) \<in> A2 (to_set X) \<Longrightarrow> y \<in> vset R \<Longrightarrow> x \<in> vset R"
  proof -
    fix x y assume arc: "(y, x) \<in> A2 (to_set X)" and yR: "y \<in> vset R"
    have o: "x \<in> to_set X \<and> weak_orcl2 y (set_delete x X) \<and> \<not> weak_orcl2 y X \<and> y \<in> carrier - to_set X"
      using arc2_to_orcl[OF iv2 sinv Xc arc] .
    show "x \<in> vset R"
    proof (rule ccontr)
      assume "x \<notin> vset R"
      hence "c_lookup c2 x - c_lookup c2 y \<in> Dgap X R m1 m2 c1 c2 y"
        using o yR isinR by (auto simp add: Dgap_def Dgap2_def)
      thus False using D_empty yD[OF conjunct2[OF conjunct2[OF conjunct2[OF o]]]] by auto
    qed
  qed
  have closed: "\<And>a b. (a, b) \<in> A1 (to_set X) \<union> A2 (to_set X) \<Longrightarrow> a \<in> vset R \<Longrightarrow> b \<in> vset R"
    using clA1 clA2 by auto
  \<comment> \<open>no augmenting path in the full auxiliary graph\<close>
  have noaug: "\<nexists> p x y. x \<in> S (to_set X) \<and> y \<in> T (to_set X)
                 \<and> (vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) x p y \<or> x = y)"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then obtain p x y where xy: "x \<in> S (to_set X)" "y \<in> T (to_set X)"
      "vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) x p y \<or> x = y" by auto
    have xR: "x \<in> vset R" using xy(1) Ssub by auto
    have "y \<in> vset R" using xy(3)
    proof
      assume w: "vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) x p y"
      show "y \<in> vset R" by (rule walk_stays_closed[OF w xR closed])
    next
      assume "x = y" thus "y \<in> vset R" using xR by simp
    qed
    thus False using xy(2) Tdisj by auto
  qed
  have ismax: "\<nexists> Y. indep1 Y \<and> indep2 Y \<and> card (to_set X) < card Y"
    using if_no_augpath_then_maximum(1)[OF iv1 iv2 noaug refl] .
  \<comment> \<open>the best-so-far bound of \<open>w_invar\<close> now covers every common independent set\<close>
  have le: "\<And>Y. indep1 Y \<Longrightarrow> indep2 Y \<Longrightarrow> card Y \<le> card (to_set X)"
    using ismax by (meson not_le)
  have opt: "\<forall>Y. indep1 Y \<and> indep2 Y \<longrightarrow>
                sum (c_lookup (worig st)) Y \<le> sum (c_lookup (worig st)) (to_set (wbest st))"
    using facts(14) le df(1) by auto
  show "indep1 (to_set (wbest st)) \<and> indep2 (to_set (wbest st))
         \<and> (\<forall>Y. indep1 Y \<and> indep2 Y \<longrightarrow>
              sum (c_lookup (worig st)) Y \<le> sum (c_lookup (worig st)) (to_set (wbest st)))"
    using facts(12,13) opt by blast
qed

text \<open>The invariant holds at the start: the empty solution is independent and (vacuously) locally
optimal in both matroids, the split is \<open>c\<close>/\<open>0\<close>, and no smaller-or-equal common independent set beats
the empty best.\<close>

lemma w_invar_initial:
  assumes "c_invar c"
  shows "w_invar (weighted_initial_state c)"
proof-
  have e1: "indep1 {}" and e2: "indep2 {}"
    by (simp_all add: matroid1.indep_empty matroid2.indep_empty)
  have m1: "matroid1.max_weight_card (c_lookup c) {}"
    by (auto simp add: matroid1.max_weight_card_def matroid1.indep_finite card_0_eq)
  have m2: "matroid2.max_weight_card (c_lookup c_zero) {}"
    by (auto simp add: matroid2.max_weight_card_def matroid2.indep_finite card_0_eq)
  note lo1 = matroid1.greedy_optimality[OF e1, THEN iffD1, OF m1]
  note lo2 = matroid2.greedy_optimality[OF e2, THEN iffD1, OF m2]
  show ?thesis
    unfolding w_invar_def weighted_initial_state_def
    using assms e1 e2 lo1 lo2 set_empty c_zero matroid1.indep_finite
    by (auto simp add: c_zero(2) card_0_eq set_empty(2))
qed

text \<open>Augment branch: one tight augmentation preserves \<open>w_invar\<close>.  The graph reasoning bridges the
tight \<open>find_path\<close> to a shortest \<open>Gbar\<close> path (or a single tight vertex), then \<open>augment_tight_path\<close> /
\<open>greedy_extension\<close> keep both matroids locally optimal, and @{thm [source] common_local_opt_max_worig}
maintains the best-so-far bound.\<close>

lemma w_invar_augment:
  assumes "w_invar st" "weighted_augment_cond st"
  shows "w_invar (weighted_augment_upd st)"
proof(rule P_of_weighted_augmentI[OF assms(2)])
  fix SX TX G SbarX TbarX Gtight p X c1 c2
  assume df: "X = wsol st" "c1 = wc1 st" "c2 = wc2 st"
    "compute_graph X (complement X) = (SX, TX, G)"
    "SbarX = restrict_to_max SX c1" "TbarX = restrict_to_max TX c2"
    "Gtight = compute_tight_graph X c1 c2 (complement X)"
    "find_path SbarX TbarX Gtight = Some p"
  interpret W: weighted_intersection_graph carrier indep1 indep2 "c_lookup c1" "c_lookup c2"
    by unfold_locales
  have facts: "set_invar X" "indep1 (to_set X)" "indep2 (to_set X)"
    "c_invar c1" "c_invar c2" "c_invar (worig st)"
    "\<forall>x\<in>carrier. c_lookup c1 x + c_lookup c2 x = c_lookup (worig st) x"
    "matroid1.local_opt (c_lookup c1) (to_set X)" "matroid2.local_opt (c_lookup c2) (to_set X)"
    "set_invar (wbest st)" "indep1 (to_set (wbest st))" "indep2 (to_set (wbest st))"
    "\<forall>Y. indep1 Y \<and> indep2 Y \<and> card Y \<le> card (to_set X) \<longrightarrow>
       sum (c_lookup (worig st)) Y \<le> sum (c_lookup (worig st)) (to_set (wbest st))"
    using assms(1) by (simp_all add: w_invar_def df(1,2,3))
  have Xcarr: "to_set X \<subseteq> carrier" using matroid1.indep_subset_carrier[OF facts(2)] .
  have cInvComp: "set_invar_red (complement X)" using complement(1)[OF facts(1) Xcarr] .
  have compIs: "to_set_red (complement X) = carrier - to_set X" using complement(2)[OF facts(1) Xcarr] .
  have compCarr: "to_set_red (complement X) \<subseteq> carrier - to_set X" using compIs by simp
  note cgc = U.compute_graph_correct[OF facts(2,3,1) cInvComp compCarr df(4)]
  note cgm = U.compute_graph_meaning[OF facts(2,3,1) cInvComp compIs df(4)]
  note ctc = compute_tight_graph_correct[OF facts(2,3,1) cInvComp compCarr]
  have Gt_inv: "graph.graph_inv Gtight" and Gt_fg: "graph.finite_graph Gtight"
    and Gt_fv: "graph.finite_vsets Gtight"
    using ctc(1,3,4) df(7) by simp_all
  have Gt_dig: "graph.digraph_abs Gtight = W.Gbar (to_set X)"
    using compute_tight_graph_meaning[OF facts(2,3,1) cInvComp compIs] df(7) by simp
  have vsinvSbar: "vset_inv SbarX" using restrict_to_max(1)[OF facts(4) cgc(1)] df(5) by simp
  have vsinvTbar: "vset_inv TbarX" using restrict_to_max(1)[OF facts(5) cgc(2)] df(6) by simp
  have vsSbar: "vset SbarX = W.Sbar (to_set X)"
    using restrict_to_max_Sbar[OF facts(4) cgc(1) cgm(1)] df(5) by (simp add: W.Sbar_def)
  have vsTbar: "vset TbarX = W.Tbar (to_set X)"
    using restrict_to_max_Tbar[OF facts(5) cgc(2) cgm(2)] df(6) by (simp add: W.Tbar_def)
  have Sbarcarr: "vset SbarX \<subseteq> carrier"
    using vsSbar S_in_carrier[OF facts(2,3)] by (auto simp add: W.Sbar_def)
  have Tbarcarr: "vset TbarX \<subseteq> carrier"
    using vsTbar T_in_carrier[OF facts(2,3)] by (auto simp add: W.Tbar_def)
  have Gt_verts: "dVs (graph.digraph_abs Gtight) \<subseteq> carrier"
  proof-
    have "dVs (W.Gbar (to_set X)) \<subseteq> dVs (A1 (to_set X) \<union> A2 (to_set X))"
      by (rule dVs_subset[OF W.Gbar_subset])
    thus ?thesis using Gt_dig dVs_A1A2_carrier[OF facts(2,3)] by auto
  qed
  obtain u v where p_prop:
    "vwalk_bet (W.Gbar (to_set X)) u p v \<or> (p = [u] \<and> u = v)"
    "u \<in> W.Sbar (to_set X)" "v \<in> W.Tbar (to_set X)"
    "\<nexists>q. (vwalk_bet (W.Gbar (to_set X)) u q v \<or> (q = [u] \<and> u = v)) \<and> length q < length p"
    using find_path(2)[OF Gt_inv Gt_fg Gt_fv vsinvSbar vsinvTbar Sbarcarr Tbarcarr Gt_verts df(8)]
    by (simp add: Gt_dig vsSbar vsTbar) blast
  define ev where "ev = {p ! i | i. i < length p \<and> even i}"
  define od where "od = {p ! i | i. i < length p \<and> odd i}"
  define Xp where "Xp = (to_set X \<union> ev) - od"
  have sh_gbar: "\<nexists>q. vwalk_bet (W.Gbar (to_set X)) u q v \<and> length q < length p"
    using p_prop(4) by blast
  have big: "set p \<subseteq> carrier \<and> distinct p \<and> indep1 Xp \<and> indep2 Xp
           \<and> card Xp = card (to_set X) + 1
           \<and> matroid1.local_opt (c_lookup c1) Xp \<and> matroid2.local_opt (c_lookup c2) Xp"
  proof(cases "vwalk_bet (W.Gbar (to_set X)) u p v")
    case True
    have pc: "set p \<subseteq> carrier" using vwalk_bet_in_vertices[OF True] Gt_verts Gt_dig by auto
    have dp: "distinct p" using shortest_vwalk_bet_distinct[OF True sh_gbar] .
    note atp = W.augment_tight_path[OF facts(2,3,8,9) True p_prop(2,3) sh_gbar refl]
    show ?thesis using pc dp atp by (auto simp add: Xp_def ev_def od_def)
  next
    case False
    hence su: "p = [u]" "u = v" using p_prop(1) by auto
    have uS: "u \<in> S (to_set X)" using p_prop(2) W.Sbar_subset by auto
    have uT: "u \<in> T (to_set X)" using p_prop(3) su(2) W.Tbar_subset by auto
    have unX: "u \<in> carrier - to_set X" using uS by (auto simp add: S_def)
    have i1u: "indep1 (Set.insert u (to_set X))" using uS by (auto simp add: S_def)
    have i2u: "indep2 (Set.insert u (to_set X))" using uT by (auto simp add: T_def)
    have Xp_is: "Xp = Set.insert u (to_set X)" using su by (auto simp add: Xp_def ev_def od_def)
    have mx1: "c_lookup c1 u = Max (c_lookup c1 ` {y \<in> carrier - to_set X. indep1 (Set.insert y (to_set X))})"
      using p_prop(2) by (simp add: W.Sbar_def S_def)
    have mx2: "c_lookup c2 u = Max (c_lookup c2 ` {y \<in> carrier - to_set X. indep2 (Set.insert y (to_set X))})"
      using p_prop(3) su(2) by (simp add: W.Tbar_def T_def)
    have "matroid1.local_opt (c_lookup c1) (Set.insert u (to_set X))"
      using matroid1.greedy_extension[OF facts(2,8) unX i1u mx1] .
    moreover have "matroid2.local_opt (c_lookup c2) (Set.insert u (to_set X))"
      using matroid2.greedy_extension[OF facts(3,9) unX i2u mx2] .
    moreover have "card (Set.insert u (to_set X)) = card (to_set X) + 1"
      using unX matroid1.indep_finite[OF facts(2)] by simp
    ultimately show ?thesis using i1u i2u Xp_is su unX by auto
  qed
  have pcarr: "set p \<subseteq> carrier" and distinctp: "distinct p"
    and cX1: "indep1 Xp" and cX2: "indep2 Xp" and cXcard: "card Xp = card (to_set X) + 1"
    and cXlo1: "matroid1.local_opt (c_lookup c1) Xp" and cXlo2: "matroid2.local_opt (c_lookup c2) Xp"
    using big by auto
  have Xpeq: "to_set (augment X p) = Xp"
    using U.effect_of_augmentation(2)[OF facts(1) Xcarr pcarr distinctp refl]
    by (simp add: Xp_def ev_def od_def)
  have setinvA: "set_invar (augment X p)"
    using U.effect_of_augmentation(1)[OF facts(1) Xcarr pcarr distinctp refl] .
  have t3: "indep1 (to_set (augment X p))" and t4: "indep2 (to_set (augment X p))"
    and t9: "matroid1.local_opt (c_lookup c1) (to_set (augment X p))"
    and t10: "matroid2.local_opt (c_lookup c2) (to_set (augment X p))"
    using cX1 cX2 cXlo1 cXlo2 Xpeq by simp_all
  have t2: "to_set (augment X p) \<subseteq> carrier" using matroid1.indep_subset_carrier[OF t3] .
  have setinvKB: "set_invar (keep_better st (augment X p))"
    using setinvA facts(10) by (simp add: keep_better_def)
  have i1KB: "indep1 (to_set (keep_better st (augment X p)))"
    using t3 facts(11) by (simp add: keep_better_def)
  have i2KB: "indep2 (to_set (keep_better st (augment X p)))"
    using t4 facts(12) by (simp add: keep_better_def)
  have bestbound: "sum (c_lookup (worig st)) Y
                     \<le> sum (c_lookup (worig st)) (to_set (keep_better st (augment X p)))"
    if Yh: "indep1 Y" "indep2 Y" "card Y \<le> card (to_set (augment X p))" for Y
  proof-
    have cardle: "card Y \<le> card Xp" using Yh(3) Xpeq by simp
    have wt1: "weight (worig st) (wbest st) = sum (c_lookup (worig st)) (to_set (wbest st))"
      using weight[OF facts(6,10)] .
    have wt2: "weight (worig st) (augment X p) = sum (c_lookup (worig st)) Xp"
      using weight[OF facts(6) setinvA] Xpeq by simp
    have kbset: "to_set (keep_better st (augment X p)) =
        (if sum (c_lookup (worig st)) (to_set (wbest st)) \<le> sum (c_lookup (worig st)) Xp
         then Xp else to_set (wbest st))"
      using Xpeq by (simp add: keep_better_def wt1 wt2)
    show ?thesis
    proof(cases "card Y \<le> card (to_set X)")
      case True
      have "sum (c_lookup (worig st)) Y \<le> sum (c_lookup (worig st)) (to_set (wbest st))"
        using facts(13) Yh(1,2) True by blast
      thus ?thesis using kbset by (auto split: if_splits)
    next
      case False
      have ceq: "card Y = card Xp" using cardle False cXcard by simp
      have "sum (c_lookup (worig st)) Y \<le> sum (c_lookup (worig st)) Xp"
        using common_local_opt_max_worig[OF cX1 cX2 cXlo1 cXlo2 facts(7) Yh(1,2) ceq] .
      thus ?thesis using kbset by (auto split: if_splits)
    qed
  qed
  show "w_invar (st\<lparr>wsol := augment X p, wbest := keep_better st (augment X p)\<rparr>)"
    unfolding w_invar_def
    using setinvA t2 t3 t4 facts(4,5,6,7) t9 t10 setinvKB i1KB i2KB bestbound df(2,3)
    by simp \<comment> \<open>assemble the conjuncts\<close>
qed

subsubsection \<open>The circuit oracle computes the same \<open>\<epsilon>\<close>\<close>

text \<open>The circuit variant differs only in how each element's boundary arcs are enumerated
(directly via \<open>circuit1\<close>/\<open>circuit2\<close> rather than by probing \<open>weak_orcl\<close>); both range over the same arcs,
so @{term compute_eps_circuit} equals @{term compute_eps}. This lets the whole plain-loop correctness be
reused for the circuit loop without redoing the \<open>\<epsilon>\<close> analysis.\<close>

lemma eps_fold_red_cond_is_eps_of:
  fixes g :: "'a \<Rightarrow> real"
  assumes "set_invar_red C"
  shows "eps_fold_red C (\<lambda>x acc. if P x then eps_min acc (g x) else acc) a
           = eps_of (g ` {x \<in> to_set_red C. P x}) a"
proof-
  obtain xs where "set xs = to_set_red C"
    "eps_fold_red C (\<lambda>x acc. if P x then eps_min acc (g x) else acc) a
       = foldr (\<lambda>x acc. if P x then eps_min acc (g x) else acc) xs a"
    using eps_fold_red[OF assms] by blast
  thus ?thesis by (simp add: foldr_eps_of)
qed

lemma foldr_eps_of_gen_restr:
  fixes G :: "'a \<Rightarrow> real set"
  assumes "\<And>y acc. y \<in> set ys \<Longrightarrow> body y acc = eps_of (G y) acc" "\<And>y. y \<in> set ys \<Longrightarrow> finite (G y)"
  shows "foldr body ys a = eps_of (\<Union>y \<in> set ys. G y) a"
  using assms
proof (induction ys)
  case (Cons y ys)
  have "foldr body (y # ys) a = eps_of (G y) (eps_of (\<Union>z \<in> set ys. G z) a)"
    using Cons by simp
  also have "... = eps_of (G y \<union> (\<Union>z \<in> set ys. G z)) a"
    using Cons.prems(2) by (subst eps_of_Un) auto
  finally show ?case by simp
qed simp

lemma eps_fold_red_is_eps_of_gen_restr:
  fixes G :: "'a \<Rightarrow> real set"
  assumes "set_invar_red C" "\<And>y acc. y \<in> to_set_red C \<Longrightarrow> body y acc = eps_of (G y) acc"
    "\<And>y. y \<in> to_set_red C \<Longrightarrow> finite (G y)"
  shows "eps_fold_red C body a = eps_of (\<Union>y \<in> to_set_red C. G y) a"
proof-
  obtain ys where yseq: "set ys = to_set_red C" and ef: "eps_fold_red C body a = foldr body ys a"
    using eps_fold_red[OF assms(1)] by blast
  have "foldr body ys a = eps_of (\<Union>y \<in> set ys. G y) a"
    using assms(2,3) yseq by (intro foldr_eps_of_gen_restr) auto
  thus ?thesis using ef yseq by simp
qed

lemma circuit1_arc_eq:
  assumes "indep1 (to_set X)" "set_invar X" "to_set X \<subseteq> carrier" "y \<in> carrier - to_set X" "\<not> weak_orcl1 y X"
  shows "to_set_red (circuit1 y X) = {x \<in> to_set X. weak_orcl1 y (set_delete x X)}"
proof -
  have ny: "\<not> indep1 (Set.insert y (to_set X))"
    using assms(5) weak_orcl1[OF assms(2,3) _ _ assms(1)] assms(4) by auto
  have tc: "to_set_red (circuit1 y X) = matroid1.the_circuit (Set.insert y (to_set X)) - {y}"
    using circuit1(1)[OF assms(2,1,3) _ ny] assms(4) by auto
  show ?thesis
  proof (rule set_eqI, rule iffI)
    fix x assume "x \<in> to_set_red (circuit1 y X)"
    hence "(x, y) \<in> A1 (to_set X)" using tc assms(4) by (auto simp add: A1_def)
    thus "x \<in> {x \<in> to_set X. weak_orcl1 y (set_delete x X)}" using arc1_to_orcl[OF assms(1,2,3)] by auto
  next
    fix x assume "x \<in> {x \<in> to_set X. weak_orcl1 y (set_delete x X)}"
    hence "(x, y) \<in> A1 (to_set X)" using arc1_from_orcl[OF assms(1,2,3) _ assms(4) _ assms(5)] by auto
    thus "x \<in> to_set_red (circuit1 y X)" using tc assms(4) by (auto simp add: A1_def)
  qed
qed

lemma circuit2_arc_eq:
  assumes "indep2 (to_set X)" "set_invar X" "to_set X \<subseteq> carrier" "y \<in> carrier - to_set X" "\<not> weak_orcl2 y X"
  shows "to_set_red (circuit2 y X) = {x \<in> to_set X. weak_orcl2 y (set_delete x X)}"
proof -
  have ny: "\<not> indep2 (Set.insert y (to_set X))"
    using assms(5) weak_orcl2[OF assms(2,3) _ _ assms(1)] assms(4) by auto
  have tc: "to_set_red (circuit2 y X) = matroid2.the_circuit (Set.insert y (to_set X)) - {y}"
    using circuit2(1)[OF assms(2,1,3) _ ny] assms(4) by auto
  show ?thesis
  proof (rule set_eqI, rule iffI)
    fix x assume "x \<in> to_set_red (circuit2 y X)"
    hence "(y, x) \<in> A2 (to_set X)" using tc assms(4) by (auto simp add: A2_def)
    thus "x \<in> {x \<in> to_set X. weak_orcl2 y (set_delete x X)}" using arc2_to_orcl[OF assms(1,2,3)] by auto
  next
    fix x assume "x \<in> {x \<in> to_set X. weak_orcl2 y (set_delete x X)}"
    hence "(y, x) \<in> A2 (to_set X)" using arc2_from_orcl[OF assms(1,2,3) _ assms(4) _ assms(5)] by auto
    thus "x \<in> to_set_red (circuit2 y X)" using tc assms(4) by (auto simp add: A2_def)
  qed
qed

lemma eps_block1_circ:
  assumes "indep1 (to_set X)" "set_invar X" "to_set X \<subseteq> carrier" "y \<in> carrier - to_set X"
  shows "(if weak_orcl1 y X then (if y \<in>\<^sub>G R then acc else eps_min acc (m1 - c_lookup c1 y))
          else (if y \<in>\<^sub>G R then acc
                else eps_fold_red (circuit1 y X)
                       (\<lambda>x acc. if x \<in>\<^sub>G R then eps_min acc (c_lookup c1 x - c_lookup c1 y) else acc) acc))
         = eps_of (Dgap1 X R m1 c1 y) acc"
proof (cases "weak_orcl1 y X")
  case True
  thus ?thesis by (simp add: Dgap1_def eps_of_single)
next
  case False
  have yc: "y \<in> carrier" using assms(4) by auto
  show ?thesis
  proof (cases "y \<in>\<^sub>G R")
    case True thus ?thesis using False by (simp add: Dgap1_def)
  next
    case Rfalse: False
    have ny: "\<not> indep1 (Set.insert y (to_set X))"
      using False weak_orcl1[OF assms(2,3) yc _ assms(1)] assms(4) by auto
    have "eps_fold_red (circuit1 y X)
             (\<lambda>x acc. if x \<in>\<^sub>G R then eps_min acc (c_lookup c1 x - c_lookup c1 y) else acc) acc
            = eps_of ((\<lambda>x. c_lookup c1 x - c_lookup c1 y) ` {x \<in> to_set_red (circuit1 y X). x \<in>\<^sub>G R}) acc"
      using eps_fold_red_cond_is_eps_of[OF circuit1(2)[OF assms(2,1,3) yc ny]] by simp
    also have "... = eps_of ((\<lambda>x. c_lookup c1 x - c_lookup c1 y)
                              ` {x \<in> to_set X. weak_orcl1 y (set_delete x X) \<and> x \<in>\<^sub>G R}) acc"
      by (simp add: circuit1_arc_eq[OF assms(1,2,3,4) False] conj_ac)
    finally show ?thesis using False Rfalse by (simp add: Dgap1_def)
  qed
qed

lemma eps_block2_circ:
  assumes "indep2 (to_set X)" "set_invar X" "to_set X \<subseteq> carrier" "y \<in> carrier - to_set X"
  shows "(if weak_orcl2 y X then (if y \<in>\<^sub>G R then eps_min acc (m2 - c_lookup c2 y) else acc)
          else (if y \<in>\<^sub>G R
                then eps_fold_red (circuit2 y X)
                       (\<lambda>x acc. if x \<notin>\<^sub>G R then eps_min acc (c_lookup c2 x - c_lookup c2 y) else acc) acc
                else acc))
         = eps_of (Dgap2 X R m2 c2 y) acc"
proof (cases "weak_orcl2 y X")
  case True
  thus ?thesis by (simp add: Dgap2_def eps_of_single)
next
  case False
  have yc: "y \<in> carrier" using assms(4) by auto
  show ?thesis
  proof (cases "y \<in>\<^sub>G R")
    case False thus ?thesis using \<open>\<not> weak_orcl2 y X\<close> by (simp add: Dgap2_def)
  next
    case Rtrue: True
    have ny: "\<not> indep2 (Set.insert y (to_set X))"
      using False weak_orcl2[OF assms(2,3) yc _ assms(1)] assms(4) by auto
    have "eps_fold_red (circuit2 y X)
             (\<lambda>x acc. if x \<notin>\<^sub>G R then eps_min acc (c_lookup c2 x - c_lookup c2 y) else acc) acc
            = eps_of ((\<lambda>x. c_lookup c2 x - c_lookup c2 y) ` {x \<in> to_set_red (circuit2 y X). x \<notin>\<^sub>G R}) acc"
      using eps_fold_red_cond_is_eps_of[OF circuit2(2)[OF assms(2,1,3) yc ny]] by simp
    also have "... = eps_of ((\<lambda>x. c_lookup c2 x - c_lookup c2 y)
                              ` {x \<in> to_set X. weak_orcl2 y (set_delete x X) \<and> x \<notin>\<^sub>G R}) acc"
      by (simp add: circuit2_arc_eq[OF assms(1,2,3,4) False] conj_ac)
    finally show ?thesis using False Rtrue by (simp add: Dgap2_def)
  qed
qed

lemma eps_meaning_circuit:
  assumes "indep1 (to_set X)" "indep2 (to_set X)" "set_invar X" "finite (to_set X)" "to_set X \<subseteq> carrier"
  shows "compute_eps_circuit X m1 m2 R c1 c2
           = eps_of (\<Union> y \<in> to_set_red (complement X). Dgap X R m1 m2 c1 c2 y) None"
  unfolding compute_eps_circuit_def
proof (rule eps_fold_red_is_eps_of_gen_restr[OF complement(1)[OF assms(3,5)]])
  fix y acc assume "y \<in> to_set_red (complement X)"
  hence yc: "y \<in> carrier - to_set X" using complement(2)[OF assms(3,5)] by simp
  show "(let acc = (if weak_orcl1 y X then (if y \<in>\<^sub>G R then acc else eps_min acc (m1 - c_lookup c1 y))
                    else (if y \<in>\<^sub>G R then acc
                          else eps_fold_red (circuit1 y X)
                                 (\<lambda>x acc. if x \<in>\<^sub>G R then eps_min acc (c_lookup c1 x - c_lookup c1 y) else acc) acc));
             acc = (if weak_orcl2 y X then (if y \<in>\<^sub>G R then eps_min acc (m2 - c_lookup c2 y) else acc)
                    else (if y \<in>\<^sub>G R
                          then eps_fold_red (circuit2 y X)
                                 (\<lambda>x acc. if x \<notin>\<^sub>G R then eps_min acc (c_lookup c2 x - c_lookup c2 y) else acc) acc
                          else acc))
          in acc)
        = eps_of (Dgap X R m1 m2 c1 c2 y) acc"
    by (simp only: Let_def eps_block1_circ[OF assms(1,3,5) yc] eps_block2_circ[OF assms(2,3,5) yc]
                   eps_of_Un[OF Dgap2_finite[OF assms(4)] Dgap1_finite[OF assms(4)]])
       (simp add: Dgap_def Un_commute)
next
  fix y show "finite (Dgap X R m1 m2 c1 c2 y)" using Dgap_finite[OF assms(4)] .
qed

lemma compute_eps_circuit_eq:
  assumes "indep1 (to_set X)" "indep2 (to_set X)" "set_invar X" "finite (to_set X)" "to_set X \<subseteq> carrier"
  shows "compute_eps_circuit X m1 m2 R c1 c2 = compute_eps X m1 m2 R c1 c2"
  using eps_meaning_circuit[OF assms] eps_meaning[OF assms(3,4,5)] by simp

subsubsection \<open>Termination ingredients: the reachable set grows under reweighting\<close>

text \<open>Reweighting decreases \<open>c1\<close> by \<open>\<epsilon>\<close> on \<open>R\<close>. As every \<open>S\<close>-endpoint outside \<open>R\<close> is at least \<open>\<epsilon>\<close>
below the maximum and the argmax lies in \<open>R\<close>, the new maximum is the old one minus \<open>\<epsilon>\<close> and the set of
maximisers only grows: \<open>Sbar \<subseteq> Sbar'\<close>.\<close>

lemma Sbar_mono:
  assumes "c_invar c" "vset_inv V" "vset_inv R" "finite (vset V)" "0 < e"
    and gap: "\<And>y. y \<in> vset V \<Longrightarrow> y \<notin> vset R \<Longrightarrow> c_lookup c y \<le> Max (c_lookup c ` vset V) - e"
    and sbarR: "\<And>y. y \<in> vset V \<Longrightarrow> c_lookup c y = Max (c_lookup c ` vset V) \<Longrightarrow> y \<in> vset R"
  shows "vset (restrict_to_max V c) \<subseteq> vset (restrict_to_max V (c_shift R (- e) c))"
proof -
  have cs: "c_lookup (c_shift R (- e) c) = (\<lambda>z. if z \<in> vset R then c_lookup c z - e else c_lookup c z)"
    using c_shift(2)[OF assms(1,3)] by (simp add: fun_eq_iff)
  show ?thesis
    using argmax_reweight_mono[OF assms(4,5) gap sbarR]
    unfolding restrict_to_max(2)[OF assms(1,2)]
              restrict_to_max(2)[OF c_shift(1)[OF assms(1,3)] assms(2)] cs .
qed

text \<open>A walk transfers to another digraph as long as its source lies in a set \<open>R\<close> that is closed under
the original arcs and whose out-arcs are preserved --- the tool that carries reachability from the old
tight graph to the new one.\<close>

lemma walk_transfer:
  assumes "vwalk_bet E u p v" "u \<in> R"
    "\<And>a b. (a, b) \<in> E \<Longrightarrow> a \<in> R \<Longrightarrow> b \<in> R"
    "\<And>a b. (a, b) \<in> E \<Longrightarrow> a \<in> R \<Longrightarrow> (a, b) \<in> E'"
  shows "vwalk_bet E' u p v \<or> (p = [u] \<and> u = v)"
proof -
  have "u \<in> R \<longrightarrow> vwalk_bet E' u p v \<or> (p = [u] \<and> u = v)" using assms(1)
  proof (induction rule: induct_vwalk_bet)
    case (path1 x) show ?case by auto
  next
    case (path2 x x' xs b)
    show ?case
    proof (rule impI)
      assume xR: "x \<in> R"
      have e': "(x, x') \<in> E'" using path2(1) assms(4) xR by auto
      have x'R: "x' \<in> R" using path2(1) assms(3) xR by auto
      from path2(3) x'R have "vwalk_bet E' x' (x' # xs) b \<or> (x' # xs = [x'] \<and> x' = b)" by simp
      thus "vwalk_bet E' x (x # x' # xs) b \<or> (x # x' # xs = [x] \<and> x = b)"
      proof
        assume "vwalk_bet E' x' (x' # xs) b"
        thus ?thesis using e' by (simp add: vwalk_bet2)
      next
        assume "x' # xs = [x'] \<and> x' = b"
        thus ?thesis using e' edges_are_vwalk_bet by fastforce
      qed
    qed
  qed
  thus ?thesis using assms(2) by simp
qed

text \<open>A tight arc whose endpoints lie on the same side of \<open>R\<close> stays tight after reweighting (both
endpoints shift by the same amount) --- so every tight arc used inside \<open>R\<close> survives.\<close>

lemma Gbar_preserved:
  assumes "c_invar c1" "c_invar c2" "vset_inv R"
    "(a, b) \<in> weighted_intersection_graph.Gbar carrier indep1 indep2 (c_lookup c1) (c_lookup c2) X"
    "a \<in> vset R" "b \<in> vset R"
  shows "(a, b) \<in> weighted_intersection_graph.Gbar carrier indep1 indep2
             (c_lookup (c_shift R (- e) c1)) (c_lookup (c_shift R e c2)) X"
proof -
  have cs1: "c_lookup (c_shift R (- e) c1) = (\<lambda>z. if z \<in> vset R then c_lookup c1 z - e else c_lookup c1 z)"
    using c_shift(2)[OF assms(1,3)] by (simp add: fun_eq_iff)
  have cs2: "c_lookup (c_shift R e c2) = (\<lambda>z. if z \<in> vset R then c_lookup c2 z + e else c_lookup c2 z)"
    using c_shift(2)[OF assms(2,3)] by (simp add: fun_eq_iff)
  show ?thesis
    unfolding cs1 cs2 by (rule Gbar_reweight_tight[OF assms(4) assms(5,6)])
qed

text \<open>Combining the three: every vertex reachable from the old maximiser set through the old tight
graph stays reachable through the new one. The old reachable set \<open>R\<close> is closed under the tight arcs
(\<open>closed\<close>) and those arcs survive reweighting (\<open>pres\<close>), so any witnessing walk transfers.\<close>

lemma R_mono:
  assumes "graph.graph_inv Gt" "vset_inv Sb" "graph.graph_inv Gt'" "vset_inv Sb'"
    "vset Sb \<subseteq> vset Sb'"
    and closed: "\<And>a b. (a, b) \<in> graph.digraph_abs Gt \<Longrightarrow> a \<in> vset (reach_set Sb Gt) \<Longrightarrow> b \<in> vset (reach_set Sb Gt)"
    and pres: "\<And>a b. (a, b) \<in> graph.digraph_abs Gt \<Longrightarrow> a \<in> vset (reach_set Sb Gt) \<Longrightarrow> (a, b) \<in> graph.digraph_abs Gt'"
  shows "vset (reach_set Sb Gt) \<subseteq> vset (reach_set Sb' Gt')"
proof
  fix v assume "v \<in> vset (reach_set Sb Gt)"
  then obtain u where u: "u \<in> vset Sb" "u = v \<or> (\<exists>p. vwalk_bet (graph.digraph_abs Gt) u p v)"
    using reach_set(2)[OF assms(1,2)] by auto
  have uR: "u \<in> vset (reach_set Sb Gt)" using u(1) reach_set_mono[OF assms(1,2)] by auto
  have uSb': "u \<in> vset Sb'" using u(1) assms(5) by auto
  have "u = v \<or> (\<exists>q. vwalk_bet (graph.digraph_abs Gt') u q v)"
    using u(2)
  proof
    assume "\<exists>p. vwalk_bet (graph.digraph_abs Gt) u p v"
    then obtain p where "vwalk_bet (graph.digraph_abs Gt) u p v" ..
    from walk_transfer[OF this uR closed pres] show ?thesis by auto
  qed auto
  thus "v \<in> vset (reach_set Sb' Gt')"
    using uSb' reach_set(2)[OF assms(3,4)] by auto
qed

text \<open>State-level payoff: in the reweight branch the reachable set does not shrink. The \<open>S\<close>-endpoint gap
that \<open>\<epsilon>\<close> respects (extracted from @{thm [source] eps_pos}'s machinery via @{thm [source] eps_le_gap})
feeds \<open>Sbar_mono\<close>; the tight arcs inside \<open>R\<close> are closed (@{thm [source] reach_set_closed}) and survive
(\<open>Gbar_preserved\<close>); \<open>R_mono\<close> combines them.\<close>

lemma reweight_R_mono:
  assumes iv1: "indep1 (to_set X)" and iv2: "indep2 (to_set X)"
    and sinv: "set_invar X" and Xc: "to_set X \<subseteq> carrier"
    and lo1: "matroid1.local_opt (c_lookup c1) (to_set X)"
    and lo2: "matroid2.local_opt (c_lookup c2) (to_set X)"
    and ci1: "c_invar c1" and ci2: "c_invar c2"
    and SXinv: "vset_inv SX" and SXis: "vset SX = S (to_set X)"
    and TXinv: "vset_inv TX" and TXis: "vset TX = T (to_set X)"
    and SbarX: "SbarX = restrict_to_max SX c1" and TbarX: "TbarX = restrict_to_max TX c2"
    and Gt_inv: "graph.graph_inv Gtight" and Gt_fg: "graph.finite_graph Gtight"
    and Gt_fv: "graph.finite_vsets Gtight"
    and Gt_dig: "graph.digraph_abs Gtight
                   = weighted_intersection_graph.Gbar carrier indep1 indep2 (c_lookup c1) (c_lookup c2) (to_set X)"
    and Rdef: "R = reach_set SbarX Gtight"
    and nopath: "find_path SbarX TbarX Gtight = None"
    and esome: "compute_eps X (weight_Max SX c1) (weight_Max TX c2) R c1 c2 = Some e"
  shows "vset R \<subseteq> vset (reach_set (restrict_to_max SX (c_shift R (- e) c1))
                                  (compute_tight_graph X (c_shift R (- e) c1) (c_shift R e c2) (complement X)))"
proof -
  interpret W: weighted_intersection_graph carrier indep1 indep2 "c_lookup c1" "c_lookup c2"
    by unfold_locales
  define m1 where "m1 = weight_Max SX c1"
  define m2 where "m2 = weight_Max TX c2"
  have finX: "finite (to_set X)" using matroid1.indep_finite[OF iv1] .
  have cInvComp: "set_invar_red (complement X)" using complement(1)[OF sinv Xc] .
  have compIs: "to_set_red (complement X) = carrier - to_set X" using complement(2)[OF sinv Xc] .
  have finS: "finite (S (to_set X))"
    using S_in_carrier[OF iv1 iv2] matroid1.carrier_finite by (auto intro: finite_subset)
  have vsinvSbar: "vset_inv SbarX" using restrict_to_max(1)[OF ci1 SXinv] SbarX by simp
  have vsSbar: "vset SbarX = W.Sbar (to_set X)"
    using restrict_to_max_Sbar[OF ci1 SXinv SXis] SbarX by (simp add: W.Sbar_def)
  have Rinv: "vset_inv R" using reach_set(1)[OF Gt_inv vsinvSbar] Rdef by simp
  have isinR: "\<And>z. (z \<in>\<^sub>G R) = (z \<in> vset R)" using graph.vset.set.set_isin[OF Rinv] by simp
  have Sbar_R: "W.Sbar (to_set X) \<subseteq> vset R"
    using reach_set_mono[OF Gt_inv vsinvSbar] vsSbar Rdef by simp
  have Rclosed: "\<And>a b. a \<in> vset R \<Longrightarrow> (a, b) \<in> W.Gbar (to_set X) \<Longrightarrow> b \<in> vset R"
    using reach_set_closed[OF Gt_inv vsinvSbar] Gt_dig Rdef by auto
  have epos: "0 < e"
    using eps_pos[OF iv1 iv2 sinv Xc lo1 lo2 ci1 ci2 SXinv SXis TXinv TXis
                     SbarX TbarX Gt_inv Gt_fg Gt_fv Gt_dig Rdef nopath esome] .
  have yD: "\<And>y. y \<in> carrier - to_set X \<Longrightarrow> y \<in> to_set_red (complement X)" using compIs by simp
  have sgap: "\<And>y. y \<in> vset SX \<Longrightarrow> y \<notin> vset R \<Longrightarrow> c_lookup c1 y \<le> Max (c_lookup c1 ` vset SX) - e"
  proof -
    fix y assume yS: "y \<in> vset SX" and ynR: "y \<notin> vset R"
    have ySX: "y \<in> S (to_set X)" using yS SXis by simp
    have yc: "y \<in> carrier - to_set X" and iy: "indep1 (Set.insert y (to_set X))"
      using ySX by (auto simp add: S_def)
    have woy: "weak_orcl1 y X" using weak_orcl1[OF sinv Xc _ _ iv1] yc iy by auto
    have "m1 - c_lookup c1 y \<in> Dgap X R m1 m2 c1 c2 y"
      using woy ynR isinR by (auto simp add: Dgap_def Dgap1_def)
    hence e_le: "e \<le> m1 - c_lookup c1 y"
      using eps_le_gap[OF sinv finX Xc esome[folded m1_def m2_def] yD[OF yc]] by simp
    have "m1 = Max (c_lookup c1 ` vset SX)"
      using weight_Max[OF ci1 SXinv] yS m1_def by auto
    thus "c_lookup c1 y \<le> Max (c_lookup c1 ` vset SX) - e" using e_le by simp
  qed
  have sbarR: "\<And>y. y \<in> vset SX \<Longrightarrow> c_lookup c1 y = Max (c_lookup c1 ` vset SX) \<Longrightarrow> y \<in> vset R"
  proof -
    fix y assume yS: "y \<in> vset SX" and ym: "c_lookup c1 y = Max (c_lookup c1 ` vset SX)"
    have ySX: "y \<in> S (to_set X)" using yS SXis by simp
    have "m1 = Max (c_lookup c1 ` S (to_set X))"
      using weight_Max[OF ci1 SXinv] yS SXis m1_def by auto
    hence "y \<in> W.Sbar (to_set X)" using ySX ym SXis by (simp add: W.Sbar_def)
    thus "y \<in> vset R" using Sbar_R by auto
  qed
  have finSX: "finite (vset SX)" using SXis finS by simp
  have Sbar_sub: "vset SbarX \<subseteq> vset (restrict_to_max SX (c_shift R (- e) c1))"
    unfolding SbarX by (rule Sbar_mono[OF ci1 SXinv Rinv finSX epos sgap sbarR])
  have Gt_inv': "graph.graph_inv (compute_tight_graph X (c_shift R (- e) c1) (c_shift R e c2) (complement X))"
    by (rule compute_tight_graph_correct(1)[OF iv1 iv2 sinv cInvComp compIs[THEN equalityD1]])
  have Gt_dig': "graph.digraph_abs (compute_tight_graph X (c_shift R (- e) c1) (c_shift R e c2) (complement X))
                   = weighted_intersection_graph.Gbar carrier indep1 indep2
                        (c_lookup (c_shift R (- e) c1)) (c_lookup (c_shift R e c2)) (to_set X)"
    by (rule compute_tight_graph_meaning[OF iv1 iv2 sinv cInvComp compIs])
  have vsinvSbar': "vset_inv (restrict_to_max SX (c_shift R (- e) c1))"
    by (rule restrict_to_max(1)[OF c_shift(1)[OF ci1 Rinv] SXinv])
  have closed: "\<And>a b. (a, b) \<in> graph.digraph_abs Gtight \<Longrightarrow> a \<in> vset (reach_set SbarX Gtight)
                        \<Longrightarrow> b \<in> vset (reach_set SbarX Gtight)"
    using Rclosed Gt_dig Rdef by auto
  have pres: "\<And>a b. (a, b) \<in> graph.digraph_abs Gtight \<Longrightarrow> a \<in> vset (reach_set SbarX Gtight)
                     \<Longrightarrow> (a, b) \<in> graph.digraph_abs (compute_tight_graph X (c_shift R (- e) c1) (c_shift R e c2) (complement X))"
  proof -
    fix a b assume ab: "(a, b) \<in> graph.digraph_abs Gtight" and aR: "a \<in> vset (reach_set SbarX Gtight)"
    have abG: "(a, b) \<in> W.Gbar (to_set X)" using ab Gt_dig by simp
    have aR': "a \<in> vset R" using aR Rdef by simp
    have bR: "b \<in> vset R" using Rclosed aR' abG by simp
    show "(a, b) \<in> graph.digraph_abs (compute_tight_graph X (c_shift R (- e) c1) (c_shift R e c2) (complement X))"
      unfolding Gt_dig' using Gbar_preserved[OF ci1 ci2 Rinv abG aR' bR] .
  qed
  show ?thesis
    by (rule R_mono[OF Gt_inv vsinvSbar Gt_inv' vsinvSbar' Sbar_sub closed pres, folded Rdef])
qed

text \<open>The reweight step makes strict progress: either the reachable set grows properly, or an augmenting
tight path appears in the successor state (so the next iteration augments). The \<open>\<epsilon>\<close>-realising boundary gap
(@{thm [source] eps_achieved}) becomes tight after reweighting; the four cases are the two boundary arcs
(which grow \<open>R\<close> via @{thm [source] A1_reweight_tight}/@{thm [source] A2_reweight_tight}), the \<open>S\<close>-endpoint
(grows \<open>R\<close> via @{thm [source] argmax_reweight_newmax}), and the \<open>T\<close>-endpoint (completes a tight path via
@{thm [source] argmax_reweight_keepmax}). This bounds the number of reweights between two augmentations.\<close>

lemma reweight_strict_or_path:
  assumes iv1: "indep1 (to_set X)" and iv2: "indep2 (to_set X)"
    and sinv: "set_invar X" and Xc: "to_set X \<subseteq> carrier"
    and lo1: "matroid1.local_opt (c_lookup c1) (to_set X)"
    and lo2: "matroid2.local_opt (c_lookup c2) (to_set X)"
    and ci1: "c_invar c1" and ci2: "c_invar c2"
    and SXinv: "vset_inv SX" and SXis: "vset SX = S (to_set X)"
    and TXinv: "vset_inv TX" and TXis: "vset TX = T (to_set X)"
    and SbarX: "SbarX = restrict_to_max SX c1" and TbarX: "TbarX = restrict_to_max TX c2"
    and Gt_inv: "graph.graph_inv Gtight" and Gt_fg: "graph.finite_graph Gtight"
    and Gt_fv: "graph.finite_vsets Gtight"
    and Gt_dig: "graph.digraph_abs Gtight = weighted_intersection_graph.Gbar carrier indep1 indep2 (c_lookup c1) (c_lookup c2) (to_set X)"
    and Rdef: "R = reach_set SbarX Gtight"
    and nopath: "find_path SbarX TbarX Gtight = None"
    and esome: "compute_eps X (weight_Max SX c1) (weight_Max TX c2) R c1 c2 = Some e"
  shows "vset R \<subset> vset (reach_set (restrict_to_max SX (c_shift R (- e) c1)) (compute_tight_graph X (c_shift R (- e) c1) (c_shift R e c2) (complement X)))
         \<or> find_path (restrict_to_max SX (c_shift R (- e) c1)) (restrict_to_max TX (c_shift R e c2)) (compute_tight_graph X (c_shift R (- e) c1) (c_shift R e c2) (complement X)) \<noteq> None"
proof -
  interpret W: weighted_intersection_graph carrier indep1 indep2 "c_lookup c1" "c_lookup c2" by unfold_locales
  define c1' where "c1' = c_shift R (- e) c1"
  define c2' where "c2' = c_shift R e c2"
  define Gt' where "Gt' = compute_tight_graph X c1' c2' (complement X)"
  define SbarX' where "SbarX' = restrict_to_max SX c1'"
  define TbarX' where "TbarX' = restrict_to_max TX c2'"
  define m1 where "m1 = weight_Max SX c1"
  define m2 where "m2 = weight_Max TX c2"
  interpret W': weighted_intersection_graph carrier indep1 indep2 "c_lookup c1'" "c_lookup c2'" by unfold_locales
  have finX: "finite (to_set X)" using matroid1.indep_finite[OF iv1] .
  have cInvComp: "set_invar_red (complement X)" using complement(1)[OF sinv Xc] .
  have compIs: "to_set_red (complement X) = carrier - to_set X" using complement(2)[OF sinv Xc] .
  have finS: "finite (S (to_set X))" using S_in_carrier[OF iv1 iv2] matroid1.carrier_finite by (auto intro: finite_subset)
  have finT: "finite (T (to_set X))" using T_in_carrier[OF iv1 iv2] matroid1.carrier_finite by (auto intro: finite_subset)
  have vsinvSbar: "vset_inv SbarX" using restrict_to_max(1)[OF ci1 SXinv] SbarX by simp
  have vsSbar: "vset SbarX = W.Sbar (to_set X)" using restrict_to_max_Sbar[OF ci1 SXinv SXis] SbarX by (simp add: W.Sbar_def)
  have vsinvTbar: "vset_inv TbarX" using restrict_to_max(1)[OF ci2 TXinv] TbarX by simp
  have vsTbar: "vset TbarX = W.Tbar (to_set X)" using restrict_to_max_Tbar[OF ci2 TXinv TXis] TbarX by (simp add: W.Tbar_def)
  have Sbarcarr: "vset SbarX \<subseteq> carrier" using vsSbar W.Sbar_subset S_in_carrier[OF iv1 iv2] by auto
  have Tbarcarr: "vset TbarX \<subseteq> carrier" using vsTbar W.Tbar_subset T_in_carrier[OF iv1 iv2] by auto
  have Gt_verts: "dVs (graph.digraph_abs Gtight) \<subseteq> carrier" using Gt_dig W.Gbar_subset dVs_A1A2_carrier[OF iv1 iv2] dVs_subset by (metis subset_trans)
  have Rinv: "vset_inv R" using reach_set(1)[OF Gt_inv vsinvSbar] Rdef by simp
  have isinR: "\<And>z. (z \<in>\<^sub>G R) = (z \<in> vset R)" using graph.vset.set.set_isin[OF Rinv] by simp
  have Sbar_R: "W.Sbar (to_set X) \<subseteq> vset R" using reach_set_mono[OF Gt_inv vsinvSbar] vsSbar Rdef by simp
  have Rclosed: "\<And>a b. a \<in> vset R \<Longrightarrow> (a, b) \<in> W.Gbar (to_set X) \<Longrightarrow> b \<in> vset R" using reach_set_closed[OF Gt_inv vsinvSbar] Gt_dig Rdef by auto
  have epos: "0 < e" using eps_pos[OF iv1 iv2 sinv Xc lo1 lo2 ci1 ci2 SXinv SXis TXinv TXis SbarX TbarX Gt_inv Gt_fg Gt_fv Gt_dig Rdef nopath esome] .
  have nopath': "\<nexists> p u v. (vwalk_bet (W.Gbar (to_set X)) u p v \<or> (p = [u] \<and> u = v)) \<and> u \<in> W.Sbar (to_set X) \<and> v \<in> W.Tbar (to_set X)"
    using find_path(1)[OF Gt_inv Gt_fg Gt_fv vsinvSbar vsinvTbar Sbarcarr Tbarcarr Gt_verts] nopath by (simp add: Gt_dig vsSbar vsTbar)
  have yD: "\<And>y. y \<in> carrier - to_set X \<Longrightarrow> y \<in> to_set_red (complement X)" using compIs by simp
  have ci1': "c_invar c1'" unfolding c1'_def by (rule c_shift(1)[OF ci1 Rinv])
  have ci2': "c_invar c2'" unfolding c2'_def by (rule c_shift(1)[OF ci2 Rinv])
  have cs1: "c_lookup c1' = (\<lambda>z. if z \<in> vset R then c_lookup c1 z - e else c_lookup c1 z)" unfolding c1'_def using c_shift(2)[OF ci1 Rinv] by (simp add: fun_eq_iff)
  have cs2: "c_lookup c2' = (\<lambda>z. if z \<in> vset R then c_lookup c2 z + e else c_lookup c2 z)" unfolding c2'_def using c_shift(2)[OF ci2 Rinv] by (simp add: fun_eq_iff)
  have Gt_inv': "graph.graph_inv Gt'" unfolding Gt'_def by (rule compute_tight_graph_correct(1)[OF iv1 iv2 sinv cInvComp compIs[THEN equalityD1]])
  have Gt_fg': "graph.finite_graph Gt'" unfolding Gt'_def by (rule compute_tight_graph_correct(3)[OF iv1 iv2 sinv cInvComp compIs[THEN equalityD1]])
  have Gt_fv': "graph.finite_vsets Gt'" unfolding Gt'_def by (rule compute_tight_graph_correct(4)[OF iv1 iv2 sinv cInvComp compIs[THEN equalityD1]])
  have Gt_dig': "graph.digraph_abs Gt' = weighted_intersection_graph.Gbar carrier indep1 indep2 (c_lookup c1') (c_lookup c2') (to_set X)"
    unfolding Gt'_def by (rule compute_tight_graph_meaning[OF iv1 iv2 sinv cInvComp compIs])
  have vsinvSbar': "vset_inv SbarX'" unfolding SbarX'_def by (rule restrict_to_max(1)[OF ci1' SXinv])
  have vsinvTbar': "vset_inv TbarX'" unfolding TbarX'_def by (rule restrict_to_max(1)[OF ci2' TXinv])
  have RsubR': "vset R \<subseteq> vset (reach_set SbarX' Gt')"
    unfolding SbarX'_def Gt'_def c1'_def c2'_def
    by (rule reweight_R_mono[OF iv1 iv2 sinv Xc lo1 lo2 ci1 ci2 SXinv SXis TXinv TXis SbarX TbarX Gt_inv Gt_fg Gt_fv Gt_dig Rdef nopath esome])
  have Sbar'R': "vset SbarX' \<subseteq> vset (reach_set SbarX' Gt')" by (rule reach_set_mono[OF Gt_inv' vsinvSbar'])
  have R'closed: "\<And>a b. a \<in> vset (reach_set SbarX' Gt') \<Longrightarrow> (a, b) \<in> graph.digraph_abs Gt' \<Longrightarrow> b \<in> vset (reach_set SbarX' Gt')"
    using reach_set_closed[OF Gt_inv' vsinvSbar'] by blast
  let ?strict = "vset R \<subset> vset (reach_set SbarX' Gt')"
  let ?path = "find_path SbarX' TbarX' Gt' \<noteq> None"
  have strictI: "\<And>v. v \<in> vset (reach_set SbarX' Gt') \<Longrightarrow> v \<notin> vset R \<Longrightarrow> ?strict" using RsubR' by blast
  obtain y0 where y0D: "y0 \<in> to_set_red (complement X)" and y0gap: "e \<in> Dgap X R m1 m2 c1 c2 y0"
    using eps_achieved[OF sinv Xc iv1 esome[folded m1_def m2_def]] by blast
  have y0c: "y0 \<in> carrier - to_set X" using y0D compIs by simp
  have y0ca: "y0 \<in> carrier" and y0nX: "y0 \<notin> to_set X" using y0c by auto
  show ?thesis
  proof (cases "e \<in> Dgap1 X R m1 c1 y0")
    case D1: True
    show ?thesis
    proof (cases "weak_orcl1 y0 X")
      case wo: True
      have veq: "e = m1 - c_lookup c1 y0" and y0nR: "y0 \<notin> vset R" using D1 wo isinR by (auto simp add: Dgap1_def split: if_splits)
      have y0S: "y0 \<in> S (to_set X)" using wo weak_orcl1[OF sinv Xc y0ca y0nX iv1] y0c by (auto simp add: S_def)
      have y0SX: "y0 \<in> vset SX" using y0S SXis by simp
      have m1eq: "m1 = Max (c_lookup c1 ` vset SX)" using weight_Max[OF ci1 SXinv] y0SX m1_def by auto
      have sgap: "\<And>y. y \<in> vset SX \<Longrightarrow> y \<notin> vset R \<Longrightarrow> c_lookup c1 y \<le> Max (c_lookup c1 ` vset SX) - e"
      proof -
        fix y assume yS: "y \<in> vset SX" and ynR: "y \<notin> vset R"
        have ySX: "y \<in> S (to_set X)" using yS SXis by simp
        have yc: "y \<in> carrier - to_set X" and iy: "indep1 (Set.insert y (to_set X))" using ySX by (auto simp add: S_def)
        have woy: "weak_orcl1 y X" using weak_orcl1[OF sinv Xc _ _ iv1] yc iy by auto
        have "m1 - c_lookup c1 y \<in> Dgap X R m1 m2 c1 c2 y" using woy ynR isinR by (auto simp add: Dgap_def Dgap1_def)
        hence "e \<le> m1 - c_lookup c1 y" using eps_le_gap[OF sinv finX Xc esome[folded m1_def m2_def] yD[OF yc]] by simp
        thus "c_lookup c1 y \<le> Max (c_lookup c1 ` vset SX) - e" using m1eq by simp
      qed
      have sbarR: "\<And>y. y \<in> vset SX \<Longrightarrow> c_lookup c1 y = Max (c_lookup c1 ` vset SX) \<Longrightarrow> y \<in> vset R"
      proof -
        fix y assume yS: "y \<in> vset SX" and ym: "c_lookup c1 y = Max (c_lookup c1 ` vset SX)"
        have "y \<in> W.Sbar (to_set X)" using yS SXis ym m1eq by (simp add: W.Sbar_def)
        thus "y \<in> vset R" using Sbar_R by auto
      qed
      have finSX: "finite (vset SX)" using SXis finS by simp
      have finSXne: "vset SX \<noteq> {}" using y0SX by auto
      have newmax: "Max (c_lookup c1' ` vset SX) = Max (c_lookup c1 ` vset SX) - e" unfolding cs1 by (rule argmax_reweight_newmax[OF finSX finSXne epos sgap sbarR])
      have "c_lookup c1' y0 = Max (c_lookup c1' ` vset SX)"
      proof -
        have "c_lookup c1' y0 = c_lookup c1 y0" using y0nR by (simp add: cs1)
        also have "\<dots> = Max (c_lookup c1 ` vset SX) - e" using veq m1eq by (simp add: algebra_simps)
        also have "\<dots> = Max (c_lookup c1' ` vset SX)" using newmax by simp
        finally show ?thesis .
      qed
      hence "y0 \<in> vset SbarX'" unfolding SbarX'_def using restrict_to_max(2)[OF ci1' SXinv] y0SX by simp
      hence y0reach: "y0 \<in> vset (reach_set SbarX' Gt')" using Sbar'R' by auto
      show ?thesis using strictI[OF y0reach y0nR, unfolded SbarX'_def TbarX'_def Gt'_def c1'_def c2'_def] by (rule disjI1)
    next
      case wo: False
      have y0nR: "y0 \<notin> vset R" using D1 wo isinR by (auto simp add: Dgap1_def split: if_splits)
      obtain x0 where x0X: "x0 \<in> to_set X" and x0orcl: "weak_orcl1 y0 (set_delete x0 X)"
        and x0R: "x0 \<in> vset R" and veq: "e = c_lookup c1 x0 - c_lookup c1 y0" using D1 wo isinR by (auto simp add: Dgap1_def split: if_splits)
      have arc: "(x0, y0) \<in> A1 (to_set X)" using arc1_from_orcl[OF iv1 sinv Xc x0X y0c x0orcl wo] .
      have tight: "(x0, y0) \<in> graph.digraph_abs Gt'" unfolding Gt_dig' cs1 cs2 by (rule A1_reweight_tight[OF arc x0R y0nR veq[symmetric]])
      have x0R': "x0 \<in> vset (reach_set SbarX' Gt')" using x0R RsubR' by auto
      have y0reach: "y0 \<in> vset (reach_set SbarX' Gt')" using R'closed[OF x0R' tight] .
      show ?thesis using strictI[OF y0reach y0nR, unfolded SbarX'_def TbarX'_def Gt'_def c1'_def c2'_def] by (rule disjI1)
    qed
  next
    case D1: False
    have D2: "e \<in> Dgap2 X R m2 c2 y0" using y0gap D1 by (simp add: Dgap_def)
    show ?thesis
    proof (cases "weak_orcl2 y0 X")
      case wo: True
      have veq: "e = m2 - c_lookup c2 y0" and y0R: "y0 \<in> vset R" using D2 wo isinR by (auto simp add: Dgap2_def split: if_splits)
      have y0T: "y0 \<in> T (to_set X)" using wo weak_orcl2[OF sinv Xc y0ca y0nX iv2] y0c by (auto simp add: T_def)
      have y0TX: "y0 \<in> vset TX" using y0T TXis by simp
      have m2eq: "m2 = Max (c_lookup c2 ` vset TX)" using weight_Max[OF ci2 TXinv] y0TX m2_def by auto
      have tgap: "\<And>y. y \<in> vset TX \<Longrightarrow> y \<in> vset R \<Longrightarrow> c_lookup c2 y \<le> Max (c_lookup c2 ` vset TX) - e"
      proof -
        fix y assume yT: "y \<in> vset TX" and yR: "y \<in> vset R"
        have yTX: "y \<in> T (to_set X)" using yT TXis by simp
        have yc: "y \<in> carrier - to_set X" and iy: "indep2 (Set.insert y (to_set X))" using yTX by (auto simp add: T_def)
        have woy: "weak_orcl2 y X" using weak_orcl2[OF sinv Xc _ _ iv2] yc iy by auto
        have "m2 - c_lookup c2 y \<in> Dgap X R m1 m2 c1 c2 y" using woy yR isinR by (auto simp add: Dgap_def Dgap2_def)
        hence "e \<le> m2 - c_lookup c2 y" using eps_le_gap[OF sinv finX Xc esome[folded m1_def m2_def] yD[OF yc]] by simp
        thus "c_lookup c2 y \<le> Max (c_lookup c2 ` vset TX) - e" using m2eq by simp
      qed
      have tbarNR: "\<And>y. y \<in> vset TX \<Longrightarrow> c_lookup c2 y = Max (c_lookup c2 ` vset TX) \<Longrightarrow> y \<notin> vset R"
      proof -
        fix y assume yT: "y \<in> vset TX" and ym: "c_lookup c2 y = Max (c_lookup c2 ` vset TX)"
        have yTbar: "y \<in> W.Tbar (to_set X)" using yT TXis ym m2eq by (simp add: W.Tbar_def)
        show "y \<notin> vset R"
        proof
          assume yR: "y \<in> vset R"
          obtain u where u: "u \<in> vset SbarX" "u = y \<or> (\<exists>p. vwalk_bet (graph.digraph_abs Gtight) u p y)" using yR reach_set(2)[OF Gt_inv vsinvSbar] Rdef by auto
          have "\<exists>p. (vwalk_bet (W.Gbar (to_set X)) u p y \<or> (p = [u] \<and> u = y))" using u(2) Gt_dig by auto
          thus False using nopath' u(1) vsSbar yTbar by blast
        qed
      qed
      have finTX: "finite (vset TX)" using TXis finT by simp
      have finTXne: "vset TX \<noteq> {}" using y0TX by auto
      have keepmax: "Max (c_lookup c2' ` vset TX) = Max (c_lookup c2 ` vset TX)" unfolding cs2 by (rule argmax_reweight_keepmax[OF finTX finTXne epos tgap tbarNR])
      have "c_lookup c2' y0 = Max (c_lookup c2' ` vset TX)"
      proof -
        have "c_lookup c2' y0 = c_lookup c2 y0 + e" using y0R by (simp add: cs2)
        also have "\<dots> = Max (c_lookup c2 ` vset TX)" using veq m2eq by (simp add: algebra_simps)
        also have "\<dots> = Max (c_lookup c2' ` vset TX)" using keepmax by simp
        finally show ?thesis .
      qed
      hence y0Tbar': "y0 \<in> vset TbarX'" unfolding TbarX'_def using restrict_to_max(2)[OF ci2' TXinv] y0TX by simp
      have y0R': "y0 \<in> vset (reach_set SbarX' Gt')" using y0R RsubR' by auto
      then obtain u where u: "u \<in> vset SbarX'" "u = y0 \<or> (\<exists>p. vwalk_bet (graph.digraph_abs Gt') u p y0)" using reach_set(2)[OF Gt_inv' vsinvSbar'] by auto
      have "vset SbarX' \<subseteq> vset SX" unfolding SbarX'_def restrict_to_max(2)[OF ci1' SXinv] by auto
      hence Sbarcarr': "vset SbarX' \<subseteq> carrier" using SXis S_in_carrier[OF iv1 iv2] by auto
      have "vset TbarX' \<subseteq> vset TX" unfolding TbarX'_def restrict_to_max(2)[OF ci2' TXinv] by auto
      hence Tbarcarr': "vset TbarX' \<subseteq> carrier" using TXis T_in_carrier[OF iv1 iv2] by auto
      have Gt_verts': "dVs (graph.digraph_abs Gt') \<subseteq> carrier" using Gt_dig' W'.Gbar_subset dVs_A1A2_carrier[OF iv1 iv2] dVs_subset by (metis subset_trans)
      have pth: "?path" using find_path(1)[OF Gt_inv' Gt_fg' Gt_fv' vsinvSbar' vsinvTbar' Sbarcarr' Tbarcarr' Gt_verts'] u y0Tbar' by blast
      show ?thesis using pth[unfolded SbarX'_def TbarX'_def Gt'_def c1'_def c2'_def] by (rule disjI2)
    next
      case wo: False
      have y0R: "y0 \<in> vset R" using D2 wo isinR by (auto simp add: Dgap2_def split: if_splits)
      obtain x0 where x0X: "x0 \<in> to_set X" and x0orcl: "weak_orcl2 y0 (set_delete x0 X)"
        and x0nR: "x0 \<notin> vset R" and veq: "e = c_lookup c2 x0 - c_lookup c2 y0" using D2 wo isinR by (auto simp add: Dgap2_def split: if_splits)
      have arc: "(y0, x0) \<in> A2 (to_set X)" using arc2_from_orcl[OF iv2 sinv Xc x0X y0c x0orcl wo] .
      have tight: "(y0, x0) \<in> graph.digraph_abs Gt'" unfolding Gt_dig' cs1 cs2 by (rule A2_reweight_tight[OF arc y0R x0nR veq[symmetric]])
      have y0R': "y0 \<in> vset (reach_set SbarX' Gt')" using y0R RsubR' by auto
      have x0reach: "x0 \<in> vset (reach_set SbarX' Gt')" using R'closed[OF y0R' tight] .
      show ?thesis using strictI[OF x0reach x0nR, unfolded SbarX'_def TbarX'_def Gt'_def c1'_def c2'_def] by (rule disjI1)
    qed
  qed
qed

subsubsection \<open>Termination of the loop\<close>

text \<open>The termination measure combines the two progress quantities: the common independent set \<open>wsol\<close>
grows on augmentation, and (between augmentations) the reachable set \<open>R\<close> grows on reweighting --- or a
path appears. The state-indexed \<open>R\<close> and the \<open>find_path = None\<close> flag are read off the loop's own \<open>let\<close>.\<close>

definition "wSX st = fst (compute_graph (wsol st) (complement (wsol st)))"
definition "wTX st = fst (snd (compute_graph (wsol st) (complement (wsol st))))"
definition "wGt st = compute_tight_graph (wsol st) (wc1 st) (wc2 st) (complement (wsol st))"
definition "wRverts st = vset (reach_set (restrict_to_max (wSX st) (wc1 st)) (wGt st))"
definition "wPathNone st = (find_path (restrict_to_max (wSX st) (wc1 st)) (restrict_to_max (wTX st) (wc2 st)) (wGt st) = None)"
definition "wmeasure st = (card carrier - card (to_set (wsol st))) * (2 * card carrier + 2)
                          + 2 * (card carrier - card (wRverts st)) + (if wPathNone st then 1 else 0)"

text \<open>The arithmetic of one reweight step: if the reachable set does not shrink and either strictly grows
or a path appears, the \<open>R\<close>-part of the measure strictly decreases.\<close>
lemma measure_dec_helper:
  fixes N rR rR' :: nat and pn' :: bool
  assumes "rR \<le> rR'" "rR' \<le> N" and "rR < rR' \<or> \<not> pn'"
  shows "2 * (N - rR') + (if pn' then 1 else 0) < 2 * (N - rR) + 1"
  using assms by (cases pn') auto

text \<open>Reading the state-indexed reachable set and path flag off the loop's \<open>let\<close>-bindings.\<close>
lemma wRP_state:
  assumes "X = wsol st" "c1 = wc1 st" "c2 = wc2 st"
    "compute_graph X (complement X) = (SX, TX, G)"
    "SbarX = restrict_to_max SX c1" "TbarX = restrict_to_max TX c2"
    "Gtight = compute_tight_graph X c1 c2 (complement X)"
    "R = reach_set SbarX Gtight"
  shows "wRverts st = vset R \<and> wPathNone st = (find_path SbarX TbarX Gtight = None)"
  by (simp only: wRverts_def wPathNone_def wSX_def wTX_def wGt_def
        assms(1)[symmetric] assms(2)[symmetric] assms(3)[symmetric] assms(4) prod.sel
        assms(5)[symmetric] assms(6)[symmetric] assms(7)[symmetric] assms(8)[symmetric])

text \<open>Augmentation adds exactly one element to \<open>wsol\<close> (Frank's tight augmenting path is alternating of
odd length), so the outer measure component strictly decreases.\<close>
lemma weighted_augment_card:
  assumes "w_invar st" "weighted_augment_cond st"
  shows "card (to_set (wsol (weighted_augment_upd st))) = card (to_set (wsol st)) + 1"
proof(rule P_of_weighted_augmentI[OF assms(2)])
  fix SX TX G SbarX TbarX Gtight p X c1 c2
  assume df: "X = wsol st" "c1 = wc1 st" "c2 = wc2 st"
    "compute_graph X (complement X) = (SX, TX, G)"
    "SbarX = restrict_to_max SX c1" "TbarX = restrict_to_max TX c2"
    "Gtight = compute_tight_graph X c1 c2 (complement X)"
    "find_path SbarX TbarX Gtight = Some p"
  interpret W: weighted_intersection_graph carrier indep1 indep2 "c_lookup c1" "c_lookup c2" by unfold_locales
  have facts: "set_invar X" "indep1 (to_set X)" "indep2 (to_set X)"
    "c_invar c1" "c_invar c2" "c_invar (worig st)"
    "\<forall>x\<in>carrier. c_lookup c1 x + c_lookup c2 x = c_lookup (worig st) x"
    "matroid1.local_opt (c_lookup c1) (to_set X)" "matroid2.local_opt (c_lookup c2) (to_set X)"
    "set_invar (wbest st)" "indep1 (to_set (wbest st))" "indep2 (to_set (wbest st))"
    "\<forall>Y. indep1 Y \<and> indep2 Y \<and> card Y \<le> card (to_set X) \<longrightarrow>
       sum (c_lookup (worig st)) Y \<le> sum (c_lookup (worig st)) (to_set (wbest st))"
    using assms(1) by (simp_all add: w_invar_def df(1,2,3))
  have Xcarr: "to_set X \<subseteq> carrier" using matroid1.indep_subset_carrier[OF facts(2)] .
  have cInvComp: "set_invar_red (complement X)" using complement(1)[OF facts(1) Xcarr] .
  have compIs: "to_set_red (complement X) = carrier - to_set X" using complement(2)[OF facts(1) Xcarr] .
  have compCarr: "to_set_red (complement X) \<subseteq> carrier - to_set X" using compIs by simp
  note cgc = U.compute_graph_correct[OF facts(2,3,1) cInvComp compCarr df(4)]
  note cgm = U.compute_graph_meaning[OF facts(2,3,1) cInvComp compIs df(4)]
  note ctc = compute_tight_graph_correct[OF facts(2,3,1) cInvComp compCarr]
  have Gt_inv: "graph.graph_inv Gtight" and Gt_fg: "graph.finite_graph Gtight" and Gt_fv: "graph.finite_vsets Gtight"
    using ctc(1,3,4) df(7) by simp_all
  have Gt_dig: "graph.digraph_abs Gtight = W.Gbar (to_set X)"
    using compute_tight_graph_meaning[OF facts(2,3,1) cInvComp compIs] df(7) by simp
  have vsinvSbar: "vset_inv SbarX" using restrict_to_max(1)[OF facts(4) cgc(1)] df(5) by simp
  have vsinvTbar: "vset_inv TbarX" using restrict_to_max(1)[OF facts(5) cgc(2)] df(6) by simp
  have vsSbar: "vset SbarX = W.Sbar (to_set X)" using restrict_to_max_Sbar[OF facts(4) cgc(1) cgm(1)] df(5) by (simp add: W.Sbar_def)
  have vsTbar: "vset TbarX = W.Tbar (to_set X)" using restrict_to_max_Tbar[OF facts(5) cgc(2) cgm(2)] df(6) by (simp add: W.Tbar_def)
  have Sbarcarr: "vset SbarX \<subseteq> carrier" using vsSbar S_in_carrier[OF facts(2,3)] by (auto simp add: W.Sbar_def)
  have Tbarcarr: "vset TbarX \<subseteq> carrier" using vsTbar T_in_carrier[OF facts(2,3)] by (auto simp add: W.Tbar_def)
  have Gt_verts: "dVs (graph.digraph_abs Gtight) \<subseteq> carrier"
  proof-
    have "dVs (W.Gbar (to_set X)) \<subseteq> dVs (A1 (to_set X) \<union> A2 (to_set X))" by (rule dVs_subset[OF W.Gbar_subset])
    thus ?thesis using Gt_dig dVs_A1A2_carrier[OF facts(2,3)] by auto
  qed
  obtain u v where p_prop:
    "vwalk_bet (W.Gbar (to_set X)) u p v \<or> (p = [u] \<and> u = v)"
    "u \<in> W.Sbar (to_set X)" "v \<in> W.Tbar (to_set X)"
    "\<nexists>q. (vwalk_bet (W.Gbar (to_set X)) u q v \<or> (q = [u] \<and> u = v)) \<and> length q < length p"
    using find_path(2)[OF Gt_inv Gt_fg Gt_fv vsinvSbar vsinvTbar Sbarcarr Tbarcarr Gt_verts df(8)]
    by (simp add: Gt_dig vsSbar vsTbar) blast
  define ev where "ev = {p ! i | i. i < length p \<and> even i}"
  define od where "od = {p ! i | i. i < length p \<and> odd i}"
  define Xp where "Xp = (to_set X \<union> ev) - od"
  have sh_gbar: "\<nexists>q. vwalk_bet (W.Gbar (to_set X)) u q v \<and> length q < length p" using p_prop(4) by blast
  have big: "set p \<subseteq> carrier \<and> distinct p \<and> card Xp = card (to_set X) + 1"
  proof(cases "vwalk_bet (W.Gbar (to_set X)) u p v")
    case True
    have pc: "set p \<subseteq> carrier" using vwalk_bet_in_vertices[OF True] Gt_verts Gt_dig by auto
    have dp: "distinct p" using shortest_vwalk_bet_distinct[OF True sh_gbar] .
    note atp = W.augment_tight_path[OF facts(2,3,8,9) True p_prop(2,3) sh_gbar refl]
    show ?thesis using pc dp atp by (auto simp add: Xp_def ev_def od_def)
  next
    case False
    hence su: "p = [u]" "u = v" using p_prop(1) by auto
    have uS: "u \<in> S (to_set X)" using p_prop(2) W.Sbar_subset by auto
    have unX: "u \<in> carrier - to_set X" using uS by (auto simp add: S_def)
    have Xp_is: "Xp = Set.insert u (to_set X)" using su by (auto simp add: Xp_def ev_def od_def)
    have "card (Set.insert u (to_set X)) = card (to_set X) + 1" using unX matroid1.indep_finite[OF facts(2)] by simp
    thus ?thesis using Xp_is su unX by auto
  qed
  have pcarr: "set p \<subseteq> carrier" and distinctp: "distinct p" and cXcard: "card Xp = card (to_set X) + 1" using big by auto
  have Xpeq: "to_set (augment X p) = Xp"
    using U.effect_of_augmentation(2)[OF facts(1) Xcarr pcarr distinctp refl] by (simp add: Xp_def ev_def od_def)
  show "card (to_set (wsol (st\<lparr>wsol := augment X p, wbest := keep_better st (augment X p)\<rparr>))) = card (to_set (wsol st)) + 1"
    using cXcard Xpeq df(1) by simp
qed

text \<open>Arithmetic of one augment step: the outer component drops by the block size \<open>2\<bar>carrier\<bar>+2\<close>, which
dominates the inner (reachability) component (bounded by \<open>2\<bar>carrier\<bar>+1\<close>).\<close>
lemma measure_aug_helper:
  fixes N c A Rp Rp' :: nat
  assumes "c + 1 \<le> N" "A = 2 * N + 2" "Rp' \<le> 2 * N + 1"
  shows "(N - (c + 1)) * A + Rp' < (N - c) * A + Rp"
proof -
  have "N - c = (N - (c + 1)) + 1" using assms(1) by simp
  hence "(N - c) * A = (N - (c + 1)) * A + A" by simp
  thus ?thesis using assms(2,3) by simp
qed

text \<open>The reweight step strictly decreases the measure: \<open>wsol\<close> is untouched, and the reachable set does
not shrink (@{thm [source] reweight_R_mono}) while either strictly growing or completing a path
(@{thm [source] reweight_strict_or_path}).\<close>
lemma wmeasure_reweight_dec:
  assumes "w_invar st" "weighted_reweight_cond st"
  shows "wmeasure (weighted_reweight_upd st) < wmeasure st"
proof (rule P_of_weighted_reweightI[OF assms(2)])
  fix SX TX G SbarX TbarX Gtight R e X c1 c2
  assume df: "X = wsol st" "c1 = wc1 st" "c2 = wc2 st"
    "compute_graph X (complement X) = (SX, TX, G)"
    "SbarX = restrict_to_max SX c1" "TbarX = restrict_to_max TX c2"
    "Gtight = compute_tight_graph X c1 c2 (complement X)"
    "R = reach_set SbarX Gtight"
    "find_path SbarX TbarX Gtight = None"
    "compute_eps X (weight_Max SX c1) (weight_Max TX c2) R c1 c2 = Some e"
  interpret W': weighted_intersection_graph carrier indep1 indep2 "c_lookup (c_shift R (- e) c1)" "c_lookup (c_shift R e c2)" by unfold_locales
  have facts: "set_invar (wsol st)" "to_set (wsol st) \<subseteq> carrier" "indep1 (to_set (wsol st))" "indep2 (to_set (wsol st))"
    "c_invar (wc1 st)" "c_invar (wc2 st)" "c_invar (worig st)"
    "\<forall>z\<in>carrier. c_lookup (wc1 st) z + c_lookup (wc2 st) z = c_lookup (worig st) z"
    "matroid1.local_opt (c_lookup (wc1 st)) (to_set (wsol st))" "matroid2.local_opt (c_lookup (wc2 st)) (to_set (wsol st))"
    "set_invar (wbest st)" "indep1 (to_set (wbest st))" "indep2 (to_set (wbest st))"
    "\<forall>Y. indep1 Y \<and> indep2 Y \<and> card Y \<le> card (to_set (wsol st)) \<longrightarrow> sum (c_lookup (worig st)) Y \<le> sum (c_lookup (worig st)) (to_set (wbest st))"
    using assms(1) by (simp_all add: w_invar_def)
  have iv1: "indep1 (to_set X)" and iv2: "indep2 (to_set X)" and sinv: "set_invar X" and Xc: "to_set X \<subseteq> carrier"
    and ci1: "c_invar c1" and ci2: "c_invar c2"
    and lo1: "matroid1.local_opt (c_lookup c1) (to_set X)" and lo2: "matroid2.local_opt (c_lookup c2) (to_set X)"
    using facts df(1,2,3) by simp_all
  have finX: "finite (to_set X)" using matroid1.indep_finite[OF iv1] .
  have cInvComp: "set_invar_red (complement X)" using complement(1)[OF sinv Xc] .
  have compIs: "to_set_red (complement X) = carrier - to_set X" using complement(2)[OF sinv Xc] .
  note cgc = U.compute_graph_correct[OF iv1 iv2 sinv cInvComp, OF compIs[THEN equalityD1] df(4)]
  note cgm = U.compute_graph_meaning[OF iv1 iv2 sinv cInvComp compIs df(4)]
  have SXinv: "vset_inv SX" and TXinv: "vset_inv TX" and SXis: "vset SX = S (to_set X)" and TXis: "vset TX = T (to_set X)"
    using cgc(1,2) cgm(1,2) by simp_all
  note ctc = compute_tight_graph_correct[OF iv1 iv2 sinv cInvComp, OF compIs[THEN equalityD1]]
  have Gt_inv: "graph.graph_inv Gtight" and Gt_fg: "graph.finite_graph Gtight" and Gt_fv: "graph.finite_vsets Gtight"
    using ctc(1,3,4) df(7) by simp_all
  have Gt_dig: "graph.digraph_abs Gtight = weighted_intersection_graph.Gbar carrier indep1 indep2 (c_lookup c1) (c_lookup c2) (to_set X)"
    using compute_tight_graph_meaning[OF iv1 iv2 sinv cInvComp compIs] df(7) by simp
  have vsinvSbar: "vset_inv SbarX" using restrict_to_max(1)[OF ci1 SXinv] df(5) by simp
  have Rinv: "vset_inv R" using reach_set(1)[OF Gt_inv vsinvSbar] df(8) by simp
  interpret Wm: weighted_intersection_graph carrier indep1 indep2 "c_lookup c1" "c_lookup c2" by unfold_locales
  have Sbarcarr: "vset SbarX \<subseteq> carrier"
    using restrict_to_max_Sbar[OF ci1 SXinv SXis] df(5) Wm.Sbar_subset S_in_carrier[OF iv1 iv2] by (auto simp add: Wm.Sbar_def)
  have Gt_verts: "dVs (graph.digraph_abs Gtight) \<subseteq> carrier"
    using Gt_dig Wm.Gbar_subset dVs_A1A2_carrier[OF iv1 iv2] dVs_subset by (metis subset_trans)
  have finC: "finite carrier" by (rule matroid1.carrier_finite)
  define R' where "R' = reach_set (restrict_to_max SX (c_shift R (- e) c1)) (compute_tight_graph X (c_shift R (- e) c1) (c_shift R e c2) (complement X))"
  note sop' = reweight_strict_or_path[OF iv1 iv2 sinv Xc lo1 lo2 ci1 ci2 SXinv SXis TXinv TXis df(5) df(6) Gt_inv Gt_fg Gt_fv Gt_dig df(8) df(9) df(10), folded R'_def]
  note rmono' = reweight_R_mono[OF iv1 iv2 sinv Xc lo1 lo2 ci1 ci2 SXinv SXis TXinv TXis df(5) df(6) Gt_inv Gt_fg Gt_fv Gt_dig df(8) df(9) df(10), folded R'_def]
  have ci1': "c_invar (c_shift R (- e) c1)" by (rule c_shift(1)[OF ci1 Rinv])
  have Gt_inv': "graph.graph_inv (compute_tight_graph X (c_shift R (- e) c1) (c_shift R e c2) (complement X))"
    by (rule compute_tight_graph_correct(1)[OF iv1 iv2 sinv cInvComp compIs[THEN equalityD1]])
  have vsinvSbar': "vset_inv (restrict_to_max SX (c_shift R (- e) c1))" by (rule restrict_to_max(1)[OF ci1' SXinv])
  have Sbarcarr': "vset (restrict_to_max SX (c_shift R (- e) c1)) \<subseteq> carrier"
  proof -
    have "vset (restrict_to_max SX (c_shift R (- e) c1)) \<subseteq> vset SX" unfolding restrict_to_max(2)[OF ci1' SXinv] by auto
    thus ?thesis using SXis S_in_carrier[OF iv1 iv2] by auto
  qed
  have Gt_dig': "graph.digraph_abs (compute_tight_graph X (c_shift R (- e) c1) (c_shift R e c2) (complement X)) = weighted_intersection_graph.Gbar carrier indep1 indep2 (c_lookup (c_shift R (- e) c1)) (c_lookup (c_shift R e c2)) (to_set X)"
    by (rule compute_tight_graph_meaning[OF iv1 iv2 sinv cInvComp compIs])
  have Gt_verts': "dVs (graph.digraph_abs (compute_tight_graph X (c_shift R (- e) c1) (c_shift R e c2) (complement X))) \<subseteq> carrier"
    using Gt_dig' W'.Gbar_subset dVs_A1A2_carrier[OF iv1 iv2] dVs_subset by (metis subset_trans)
  have R'subC: "vset R' \<subseteq> carrier" using reach_set_carrier[OF Gt_inv' vsinvSbar' Sbarcarr' Gt_verts'] by (simp add: R'_def)
  have wsolS: "X = wsol (reweight R e st)" using df(1) by (simp add: reweight_def)
  have c1S: "c_shift R (- e) c1 = wc1 (reweight R e st)" using df(2) by (simp add: reweight_def)
  have c2S: "c_shift R e c2 = wc2 (reweight R e st)" using df(3) by (simp add: reweight_def)
  have linkSt: "wRverts st = vset R" "wPathNone st = (find_path SbarX TbarX Gtight = None)"
    using wRP_state[OF df(1,2,3,4,5,6,7,8)] by auto
  have linkSucc: "wRverts (reweight R e st) = vset R'"
      "wPathNone (reweight R e st) = (find_path (restrict_to_max SX (c_shift R (- e) c1)) (restrict_to_max TX (c_shift R e c2)) (compute_tight_graph X (c_shift R (- e) c1) (c_shift R e c2) (complement X)) = None)"
    using wRP_state[OF wsolS c1S c2S df(4) refl refl refl R'_def] by (auto simp add: R'_def)
  have PnStTrue: "wPathNone st" using linkSt(2) df(9) by simp
  have cardRR': "card (vset R) \<le> card (vset R')" using card_mono[OF finite_subset[OF R'subC finC] rmono'] .
  have cardR'N: "card (vset R') \<le> card carrier" using card_mono[OF finC R'subC] .
  have disj: "card (vset R) < card (vset R') \<or> \<not> wPathNone (reweight R e st)"
    using sop' linkSucc(2) psubset_card_mono[OF finite_subset[OF R'subC finC]] by auto
  have m1eq: "card (to_set (wsol (reweight R e st))) = card (to_set (wsol st))" by (simp add: reweight_def)
  have e1: "wmeasure (reweight R e st) = (card carrier - card (to_set (wsol st))) * (2 * card carrier + 2) + 2 * (card carrier - card (vset R')) + (if wPathNone (reweight R e st) then 1 else 0)"
    by (simp add: wmeasure_def m1eq linkSucc(1))
  have e2: "wmeasure st = (card carrier - card (to_set (wsol st))) * (2 * card carrier + 2) + 2 * (card carrier - card (vset R)) + 1"
    by (simp add: wmeasure_def linkSt(1) PnStTrue)
  show "wmeasure (reweight R e st) < wmeasure st"
    using measure_dec_helper[OF cardRR' cardR'N disj] e1 e2 by linarith
qed

text \<open>The augment step strictly decreases the measure via the outer component (@{thm [source]
weighted_augment_card}).\<close>
lemma wmeasure_augment_dec:
  assumes "w_invar st" "weighted_augment_cond st"
  shows "wmeasure (weighted_augment_upd st) < wmeasure st"
proof -
  have finC: "finite carrier" by (rule matroid1.carrier_finite)
  have card_aug: "card (to_set (wsol (weighted_augment_upd st))) = card (to_set (wsol st)) + 1"
    by (rule weighted_augment_card[OF assms])
  have "w_invar (weighted_augment_upd st)" by (rule w_invar_augment[OF assms])
  hence "indep1 (to_set (wsol (weighted_augment_upd st)))" by (simp add: w_invar_def)
  hence sub: "to_set (wsol (weighted_augment_upd st)) \<subseteq> carrier" by (rule matroid1.indep_subset_carrier)
  have cle: "card (to_set (wsol st)) + 1 \<le> card carrier" using card_mono[OF finC sub] card_aug by simp
  have a: "2 * (card carrier - card (wRverts (weighted_augment_upd st))) \<le> 2 * card carrier" by (metis diff_le_self mult_le_mono2)
  have b: "(if wPathNone (weighted_augment_upd st) then 1 else 0) \<le> (1::nat)" by simp
  have bnd: "2 * (card carrier - card (wRverts (weighted_augment_upd st))) + (if wPathNone (weighted_augment_upd st) then 1 else 0) \<le> 2 * card carrier + 1"
    by (rule add_mono[OF a b])
  have wm_aug: "wmeasure (weighted_augment_upd st) = (card carrier - (card (to_set (wsol st)) + 1)) * (2 * card carrier + 2) + (2 * (card carrier - card (wRverts (weighted_augment_upd st))) + (if wPathNone (weighted_augment_upd st) then 1 else 0))"
    by (simp add: wmeasure_def card_aug)
  have wm_st: "wmeasure st = (card carrier - card (to_set (wsol st))) * (2 * card carrier + 2) + (2 * (card carrier - card (wRverts st)) + (if wPathNone st then 1 else 0))"
    by (simp add: wmeasure_def)
  show ?thesis
    using measure_aug_helper[OF cle refl bnd, where Rp = "2 * (card carrier - card (wRverts st)) + (if wPathNone st then 1 else 0)"] wm_aug wm_st
    by linarith
qed

text \<open>Termination: from any \<open>w_invar\<close> state the loop's domain predicate holds. Strong induction on the
measure; the two recursive calls are exactly the augment / reweight updates, each measure-decreasing.\<close>
lemma weighted_matroid_intersection_terminates:
  assumes "w_invar st" "m = wmeasure st"
  shows "weighted_matroid_intersection_dom st"
  using assms
proof (induction m arbitrary: st rule: less_induct)
  case (less m st)
  show ?case
  proof (rule weighted_matroid_intersection.domintros)
    fix a aa b xd ab ba x2
    assume "(a, aa, b) = compute_graph (wsol st) (complement (wsol st))"
      and g2: "(xd, ab, ba) = compute_graph (wsol st) (complement (wsol st))"
      and g3: "find_path (restrict_to_max xd (wc1 st)) (restrict_to_max ab (wc2 st)) (compute_tight_graph (wsol st) (wc1 st) (wc2 st) (complement (wsol st))) = None"
      and g4: "compute_eps (wsol st) (weight_Max xd (wc1 st)) (weight_Max ab (wc2 st)) (reach_set (restrict_to_max xd (wc1 st)) (compute_tight_graph (wsol st) (wc1 st) (wc2 st) (complement (wsol st)))) (wc1 st) (wc2 st) = Some x2"
    have rwcond: "weighted_reweight_cond st" using g2[symmetric] g3 g4 by (simp add: weighted_reweight_cond_def Let_def)
    have upd_eq: "reweight (reach_set (restrict_to_max xd (wc1 st)) (compute_tight_graph (wsol st) (wc1 st) (wc2 st) (complement (wsol st)))) x2 st = weighted_reweight_upd st"
      using g2[symmetric] g3 g4 by (simp add: weighted_reweight_upd_def Let_def)
    show "weighted_matroid_intersection_dom (reweight (reach_set (restrict_to_max xd (wc1 st)) (compute_tight_graph (wsol st) (wc1 st) (wc2 st) (complement (wsol st)))) x2 st)"
      unfolding upd_eq
      by (rule less.IH[OF _ w_invar_reweight[OF less.prems(1) rwcond] refl])
         (use wmeasure_reweight_dec[OF less.prems(1) rwcond] less.prems(2) in simp)
  next
    fix a aa b xd ab ba x2
    assume "(a, aa, b) = compute_graph (wsol st) (complement (wsol st))"
      and h2: "(xd, ab, ba) = compute_graph (wsol st) (complement (wsol st))"
      and h3: "find_path (restrict_to_max xd (wc1 st)) (restrict_to_max ab (wc2 st)) (compute_tight_graph (wsol st) (wc1 st) (wc2 st) (complement (wsol st))) = Some x2"
    have augcond: "weighted_augment_cond st" using h2[symmetric] h3 by (simp add: weighted_augment_cond_def Let_def)
    have upd_eq2: "st\<lparr>wsol := augment (wsol st) x2, wbest := keep_better st (augment (wsol st) x2)\<rparr> = weighted_augment_upd st"
      using h2[symmetric] h3 by (simp add: weighted_augment_upd_def Let_def)
    show "weighted_matroid_intersection_dom (st\<lparr>wsol := augment (wsol st) x2, wbest := keep_better st (augment (wsol st) x2)\<rparr>)"
      unfolding upd_eq2
      by (rule less.IH[OF _ w_invar_augment[OF less.prems(1) augcond] refl])
         (use wmeasure_augment_dec[OF less.prems(1) augcond] less.prems(2) in simp)
  qed
qed

subsubsection \<open>Partial correctness of the loop\<close>

text \<open>The original weight \<open>worig\<close> is loop-invariant (neither augmenting nor reweighting touches it),
mirroring the way the unweighted loop only grows \<open>sol\<close>.\<close>

lemma weighted_worig_preserved:
  assumes "weighted_matroid_intersection_dom st"
  shows "worig (weighted_matroid_intersection st) = worig st"
proof (induction st rule: weighted_matroid_intersection_induct)
  case 1
  show ?case by (rule assms)
next
  case (2 st)
  show ?case
  proof (cases st rule: weighted_matroid_intersection_cases)
    case 1
    show ?thesis by (simp add: weighted_matroid_intersection_simps(1)[OF "2.hyps"(1) 1])
  next
    case 2
    have wo: "worig (weighted_augment_upd st) = worig st"
      by (simp add: weighted_augment_upd_def Let_def split: prod.split)
    have "worig (weighted_matroid_intersection (weighted_augment_upd st)) = worig (weighted_augment_upd st)"
      by (rule "2.IH"(1)[OF 2])
    thus ?thesis
      by (simp add: weighted_matroid_intersection_simps(2)[OF "2.hyps"(1) 2] wo)
  next
    case 3
    have wo: "worig (weighted_reweight_upd st) = worig st"
      by (simp add: weighted_reweight_upd_def reweight_def Let_def split: prod.split)
    have "worig (weighted_matroid_intersection (weighted_reweight_upd st)) = worig (weighted_reweight_upd st)"
      by (rule "2.IH"(2)[OF 3])
    thus ?thesis
      by (simp add: weighted_matroid_intersection_simps(3)[OF "2.hyps"(1) 3] wo)
  qed
qed

text \<open>Following the unweighted @{thm [source] U.matroid_intersection_correctness_general}: over a
terminating run the invariant is maintained through every augmentation and reweighting, and the stop
branch delivers an optimal best-so-far set. Hence \<open>wbest\<close> of the result is a maximum-weight common
independent set for the loop-invariant original weight.\<close>

lemma weighted_correctness_general:
  assumes "weighted_matroid_intersection_dom st" "w_invar st"
  shows "indep1 (to_set (wbest (weighted_matroid_intersection st)))
       \<and> indep2 (to_set (wbest (weighted_matroid_intersection st)))
       \<and> (\<forall>Y. indep1 Y \<and> indep2 Y \<longrightarrow>
            sum (c_lookup (worig (weighted_matroid_intersection st))) Y
              \<le> sum (c_lookup (worig (weighted_matroid_intersection st)))
                     (to_set (wbest (weighted_matroid_intersection st))))"
  using assms(2)
proof (induction st rule: weighted_matroid_intersection_induct)
  case 1
  show ?case by (rule assms(1))
next
  case (2 st)
  show ?case
  proof (cases st rule: weighted_matroid_intersection_cases)
    case 1
    show ?thesis
      using w_invar_max_found[OF "2.prems" 1] weighted_matroid_intersection_simps(1)[OF "2.hyps"(1) 1]
      by simp
  next
    case 2
    show ?thesis
      unfolding weighted_matroid_intersection_simps(2)[OF "2.hyps"(1) 2]
      by (rule "2.IH"(1)[OF 2 w_invar_augment[OF "2.prems" 2]])
  next
    case 3
    show ?thesis
      unfolding weighted_matroid_intersection_simps(3)[OF "2.hyps"(1) 3]
      by (rule "2.IH"(2)[OF 3 w_invar_reweight[OF "2.prems" 3]])
  qed
qed

text \<open>Partial correctness at the initial state: if the run terminates, \<open>wbest\<close> is a maximum-weight
common independent set for the input cost \<open>c\<close> (the total weight being \<open>c\<close> on the initial split).\<close>

theorem weighted_matroid_intersection_partial_correct:
  assumes "c_invar c" "weighted_matroid_intersection_dom (weighted_initial_state c)"
  defines "s \<equiv> weighted_matroid_intersection (weighted_initial_state c)"
  shows "weighted_double_matroid.is_opt indep1 indep2 (c_lookup c) (to_set (wbest s))"
proof -
  interpret WDM: weighted_double_matroid carrier indep1 indep2 "c_lookup c" by unfold_locales
  have "worig s = c" using weighted_worig_preserved[OF assms(2)]
    by (simp add: s_def weighted_initial_state_def)
  hence "indep1 (to_set (wbest s)) \<and> indep2 (to_set (wbest s))
       \<and> (\<forall>Y. indep1 Y \<and> indep2 Y \<longrightarrow> sum (c_lookup c) Y \<le> sum (c_lookup c) (to_set (wbest s)))"
    using weighted_correctness_general[OF assms(2) w_invar_initial[OF assms(1)]] by (simp add: s_def)
  thus ?thesis unfolding WDM.is_opt_def by blast
qed

text \<open>Total correctness of the plain weighted algorithm: for any valid weight map the loop terminates
(@{thm [source] weighted_matroid_intersection_terminates}) and returns a maximum-weight common
independent set --- no domain hypothesis required.\<close>
theorem weighted_matroid_intersection_correct:
  assumes "c_invar c"
  defines "s \<equiv> weighted_matroid_intersection (weighted_initial_state c)"
  shows "weighted_double_matroid.is_opt indep1 indep2 (c_lookup c) (to_set (wbest s))"
proof -
  have dom: "weighted_matroid_intersection_dom (weighted_initial_state c)"
    by (rule weighted_matroid_intersection_terminates[OF w_invar_initial[OF assms(1)] refl])
  show ?thesis unfolding s_def by (rule weighted_matroid_intersection_partial_correct[OF assms(1) dom])
qed

subsubsection \<open>Circuit variant: the same correctness by the same argument\<close>

text \<open>The circuit-oracle loop preserves \<open>w_invar\<close> and returns an optimal \<open>wbest\<close> by exactly the
arguments used for the plain loop --- the tight subgraph, endpoints and \<open>\<epsilon>\<close> all abstract to the same
objects (@{thm [source] compute_tight_graph_circuit_meaning}, @{thm [source] compute_eps_circuit_eq}).\<close>

lemma w_invar_augment_circuit:
  assumes "w_invar st" "weighted_augment_cond_circuit st"
  shows "w_invar (weighted_augment_upd_circuit st)"
proof(rule P_of_weighted_augment_circuitI[OF assms(2)])
  fix SX TX G SbarX TbarX Gtight p X c1 c2
  assume df: "X = wsol st" "c1 = wc1 st" "c2 = wc2 st"
    "compute_graph_circuit X (complement X) = (SX, TX, G)"
    "SbarX = restrict_to_max SX c1" "TbarX = restrict_to_max TX c2"
    "Gtight = compute_tight_graph_circuit X c1 c2 (complement X)"
    "find_path SbarX TbarX Gtight = Some p"
  interpret W: weighted_intersection_graph carrier indep1 indep2 "c_lookup c1" "c_lookup c2"
    by unfold_locales
  have facts: "set_invar X" "indep1 (to_set X)" "indep2 (to_set X)"
    "c_invar c1" "c_invar c2" "c_invar (worig st)"
    "\<forall>x\<in>carrier. c_lookup c1 x + c_lookup c2 x = c_lookup (worig st) x"
    "matroid1.local_opt (c_lookup c1) (to_set X)" "matroid2.local_opt (c_lookup c2) (to_set X)"
    "set_invar (wbest st)" "indep1 (to_set (wbest st))" "indep2 (to_set (wbest st))"
    "\<forall>Y. indep1 Y \<and> indep2 Y \<and> card Y \<le> card (to_set X) \<longrightarrow>
       sum (c_lookup (worig st)) Y \<le> sum (c_lookup (worig st)) (to_set (wbest st))"
    using assms(1) by (simp_all add: w_invar_def df(1,2,3))
  have Xcarr: "to_set X \<subseteq> carrier" using matroid1.indep_subset_carrier[OF facts(2)] .
  have cInvComp: "set_invar_red (complement X)" using complement(1)[OF facts(1) Xcarr] .
  have compIs: "to_set_red (complement X) = carrier - to_set X" using complement(2)[OF facts(1) Xcarr] .
  have compCarr: "to_set_red (complement X) \<subseteq> carrier - to_set X" using compIs by simp
  note cgc = U.compute_graph_circuit_correct[OF facts(2,3,1) cInvComp compCarr df(4)]
  note cgm = U.compute_graph_meaning_circuit[OF facts(2,3,1) cInvComp compIs df(4)]
  note ctc = compute_tight_graph_circuit_correct[OF facts(2,3,1) cInvComp compCarr]
  have Gt_inv: "graph.graph_inv Gtight" and Gt_fg: "graph.finite_graph Gtight"
    and Gt_fv: "graph.finite_vsets Gtight"
    using ctc(1,3,4) df(7) by simp_all
  have Gt_dig: "graph.digraph_abs Gtight = W.Gbar (to_set X)"
    using compute_tight_graph_circuit_meaning[OF facts(2,3,1) cInvComp compIs] df(7) by simp
  have vsinvSbar: "vset_inv SbarX" using restrict_to_max(1)[OF facts(4) cgc(1)] df(5) by simp
  have vsinvTbar: "vset_inv TbarX" using restrict_to_max(1)[OF facts(5) cgc(2)] df(6) by simp
  have vsSbar: "vset SbarX = W.Sbar (to_set X)"
    using restrict_to_max_Sbar[OF facts(4) cgc(1) cgm(1)] df(5) by (simp add: W.Sbar_def)
  have vsTbar: "vset TbarX = W.Tbar (to_set X)"
    using restrict_to_max_Tbar[OF facts(5) cgc(2) cgm(2)] df(6) by (simp add: W.Tbar_def)
  have Sbarcarr: "vset SbarX \<subseteq> carrier"
    using vsSbar S_in_carrier[OF facts(2,3)] by (auto simp add: W.Sbar_def)
  have Tbarcarr: "vset TbarX \<subseteq> carrier"
    using vsTbar T_in_carrier[OF facts(2,3)] by (auto simp add: W.Tbar_def)
  have Gt_verts: "dVs (graph.digraph_abs Gtight) \<subseteq> carrier"
  proof-
    have "dVs (W.Gbar (to_set X)) \<subseteq> dVs (A1 (to_set X) \<union> A2 (to_set X))"
      by (rule dVs_subset[OF W.Gbar_subset])
    thus ?thesis using Gt_dig dVs_A1A2_carrier[OF facts(2,3)] by auto
  qed
  obtain u v where p_prop:
    "vwalk_bet (W.Gbar (to_set X)) u p v \<or> (p = [u] \<and> u = v)"
    "u \<in> W.Sbar (to_set X)" "v \<in> W.Tbar (to_set X)"
    "\<nexists>q. (vwalk_bet (W.Gbar (to_set X)) u q v \<or> (q = [u] \<and> u = v)) \<and> length q < length p"
    using find_path(2)[OF Gt_inv Gt_fg Gt_fv vsinvSbar vsinvTbar Sbarcarr Tbarcarr Gt_verts df(8)]
    by (simp add: Gt_dig vsSbar vsTbar) blast
  define ev where "ev = {p ! i | i. i < length p \<and> even i}"
  define od where "od = {p ! i | i. i < length p \<and> odd i}"
  define Xp where "Xp = (to_set X \<union> ev) - od"
  have sh_gbar: "\<nexists>q. vwalk_bet (W.Gbar (to_set X)) u q v \<and> length q < length p"
    using p_prop(4) by blast
  have big: "set p \<subseteq> carrier \<and> distinct p \<and> indep1 Xp \<and> indep2 Xp
           \<and> card Xp = card (to_set X) + 1
           \<and> matroid1.local_opt (c_lookup c1) Xp \<and> matroid2.local_opt (c_lookup c2) Xp"
  proof(cases "vwalk_bet (W.Gbar (to_set X)) u p v")
    case True
    have pc: "set p \<subseteq> carrier" using vwalk_bet_in_vertices[OF True] Gt_verts Gt_dig by auto
    have dp: "distinct p" using shortest_vwalk_bet_distinct[OF True sh_gbar] .
    note atp = W.augment_tight_path[OF facts(2,3,8,9) True p_prop(2,3) sh_gbar refl]
    show ?thesis using pc dp atp by (auto simp add: Xp_def ev_def od_def)
  next
    case False
    hence su: "p = [u]" "u = v" using p_prop(1) by auto
    have uS: "u \<in> S (to_set X)" using p_prop(2) W.Sbar_subset by auto
    have uT: "u \<in> T (to_set X)" using p_prop(3) su(2) W.Tbar_subset by auto
    have unX: "u \<in> carrier - to_set X" using uS by (auto simp add: S_def)
    have i1u: "indep1 (Set.insert u (to_set X))" using uS by (auto simp add: S_def)
    have i2u: "indep2 (Set.insert u (to_set X))" using uT by (auto simp add: T_def)
    have Xp_is: "Xp = Set.insert u (to_set X)" using su by (auto simp add: Xp_def ev_def od_def)
    have mx1: "c_lookup c1 u = Max (c_lookup c1 ` {y \<in> carrier - to_set X. indep1 (Set.insert y (to_set X))})"
      using p_prop(2) by (simp add: W.Sbar_def S_def)
    have mx2: "c_lookup c2 u = Max (c_lookup c2 ` {y \<in> carrier - to_set X. indep2 (Set.insert y (to_set X))})"
      using p_prop(3) su(2) by (simp add: W.Tbar_def T_def)
    have "matroid1.local_opt (c_lookup c1) (Set.insert u (to_set X))"
      using matroid1.greedy_extension[OF facts(2,8) unX i1u mx1] .
    moreover have "matroid2.local_opt (c_lookup c2) (Set.insert u (to_set X))"
      using matroid2.greedy_extension[OF facts(3,9) unX i2u mx2] .
    moreover have "card (Set.insert u (to_set X)) = card (to_set X) + 1"
      using unX matroid1.indep_finite[OF facts(2)] by simp
    ultimately show ?thesis using i1u i2u Xp_is su unX by auto
  qed
  have pcarr: "set p \<subseteq> carrier" and distinctp: "distinct p"
    and cX1: "indep1 Xp" and cX2: "indep2 Xp" and cXcard: "card Xp = card (to_set X) + 1"
    and cXlo1: "matroid1.local_opt (c_lookup c1) Xp" and cXlo2: "matroid2.local_opt (c_lookup c2) Xp"
    using big by auto
  have Xpeq: "to_set (augment X p) = Xp"
    using U.effect_of_augmentation(2)[OF facts(1) Xcarr pcarr distinctp refl]
    by (simp add: Xp_def ev_def od_def)
  have setinvA: "set_invar (augment X p)"
    using U.effect_of_augmentation(1)[OF facts(1) Xcarr pcarr distinctp refl] .
  have t3: "indep1 (to_set (augment X p))" and t4: "indep2 (to_set (augment X p))"
    and t9: "matroid1.local_opt (c_lookup c1) (to_set (augment X p))"
    and t10: "matroid2.local_opt (c_lookup c2) (to_set (augment X p))"
    using cX1 cX2 cXlo1 cXlo2 Xpeq by simp_all
  have t2: "to_set (augment X p) \<subseteq> carrier" using matroid1.indep_subset_carrier[OF t3] .
  have setinvKB: "set_invar (keep_better st (augment X p))"
    using setinvA facts(10) by (simp add: keep_better_def)
  have i1KB: "indep1 (to_set (keep_better st (augment X p)))"
    using t3 facts(11) by (simp add: keep_better_def)
  have i2KB: "indep2 (to_set (keep_better st (augment X p)))"
    using t4 facts(12) by (simp add: keep_better_def)
  have bestbound: "sum (c_lookup (worig st)) Y
                     \<le> sum (c_lookup (worig st)) (to_set (keep_better st (augment X p)))"
    if Yh: "indep1 Y" "indep2 Y" "card Y \<le> card (to_set (augment X p))" for Y
  proof-
    have cardle: "card Y \<le> card Xp" using Yh(3) Xpeq by simp
    have wt1: "weight (worig st) (wbest st) = sum (c_lookup (worig st)) (to_set (wbest st))"
      using weight[OF facts(6,10)] .
    have wt2: "weight (worig st) (augment X p) = sum (c_lookup (worig st)) Xp"
      using weight[OF facts(6) setinvA] Xpeq by simp
    have kbset: "to_set (keep_better st (augment X p)) =
        (if sum (c_lookup (worig st)) (to_set (wbest st)) \<le> sum (c_lookup (worig st)) Xp
         then Xp else to_set (wbest st))"
      using Xpeq by (simp add: keep_better_def wt1 wt2)
    show ?thesis
    proof(cases "card Y \<le> card (to_set X)")
      case True
      have "sum (c_lookup (worig st)) Y \<le> sum (c_lookup (worig st)) (to_set (wbest st))"
        using facts(13) Yh(1,2) True by blast
      thus ?thesis using kbset by (auto split: if_splits)
    next
      case False
      have ceq: "card Y = card Xp" using cardle False cXcard by simp
      have "sum (c_lookup (worig st)) Y \<le> sum (c_lookup (worig st)) Xp"
        using common_local_opt_max_worig[OF cX1 cX2 cXlo1 cXlo2 facts(7) Yh(1,2) ceq] .
      thus ?thesis using kbset by (auto split: if_splits)
    qed
  qed
  show "w_invar (st\<lparr>wsol := augment X p, wbest := keep_better st (augment X p)\<rparr>)"
    unfolding w_invar_def
    using setinvA t2 t3 t4 facts(4,5,6,7) t9 t10 setinvKB i1KB i2KB bestbound df(2,3)
    by simp
qed

lemma weighted_stop_condE_circuit:
  "weighted_stop_cond_circuit st \<Longrightarrow>
   (\<And> SX TX G SbarX TbarX Gtight R X c1 c2.
       X = wsol st \<Longrightarrow> c1 = wc1 st \<Longrightarrow> c2 = wc2 st \<Longrightarrow>
       compute_graph_circuit X (complement X) = (SX, TX, G) \<Longrightarrow>
       SbarX = restrict_to_max SX c1 \<Longrightarrow> TbarX = restrict_to_max TX c2 \<Longrightarrow>
       Gtight = compute_tight_graph_circuit X c1 c2 (complement X) \<Longrightarrow>
       R = reach_set SbarX Gtight \<Longrightarrow>
       find_path SbarX TbarX Gtight = None \<Longrightarrow>
       compute_eps_circuit X (weight_Max SX c1) (weight_Max TX c2) R c1 c2 = None \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding weighted_stop_cond_circuit_def Let_def
  apply(cases "compute_graph_circuit (wsol st) (complement (wsol st))", simp)
  subgoal for a b c
    apply(cases "find_path (restrict_to_max a (wc1 st)) (restrict_to_max b (wc2 st))
                          (compute_tight_graph_circuit (wsol st) (wc1 st) (wc2 st) (complement (wsol st)))")
     apply(cases "compute_eps_circuit (wsol st) (weight_Max a (wc1 st)) (weight_Max b (wc2 st))
                    (reach_set (restrict_to_max a (wc1 st))
                       (compute_tight_graph_circuit (wsol st) (wc1 st) (wc2 st) (complement (wsol st))))
                    (wc1 st) (wc2 st)")
    by auto
  done

lemma w_invar_max_found_circuit:
  assumes "w_invar st" "weighted_stop_cond_circuit st"
  shows "indep1 (to_set (wbest st)) \<and> indep2 (to_set (wbest st))
         \<and> (\<forall>Y. indep1 Y \<and> indep2 Y \<longrightarrow>
              sum (c_lookup (worig st)) Y \<le> sum (c_lookup (worig st)) (to_set (wbest st)))"
proof (rule weighted_stop_condE_circuit[OF assms(2)])
  fix SX TX G SbarX TbarX Gtight R X c1 c2
  assume df: "X = wsol st" "c1 = wc1 st" "c2 = wc2 st"
    "compute_graph_circuit X (complement X) = (SX, TX, G)"
    "SbarX = restrict_to_max SX c1" "TbarX = restrict_to_max TX c2"
    "Gtight = compute_tight_graph_circuit X c1 c2 (complement X)"
    "R = reach_set SbarX Gtight"
    "find_path SbarX TbarX Gtight = None"
    "compute_eps_circuit X (weight_Max SX c1) (weight_Max TX c2) R c1 c2 = None"
  define m1 where "m1 = weight_Max SX c1"
  define m2 where "m2 = weight_Max TX c2"
  have facts: "set_invar (wsol st)" "to_set (wsol st) \<subseteq> carrier"
    "indep1 (to_set (wsol st))" "indep2 (to_set (wsol st))"
    "c_invar (wc1 st)" "c_invar (wc2 st)" "c_invar (worig st)"
    "\<forall>z\<in>carrier. c_lookup (wc1 st) z + c_lookup (wc2 st) z = c_lookup (worig st) z"
    "matroid1.local_opt (c_lookup (wc1 st)) (to_set (wsol st))"
    "matroid2.local_opt (c_lookup (wc2 st)) (to_set (wsol st))"
    "set_invar (wbest st)" "indep1 (to_set (wbest st))" "indep2 (to_set (wbest st))"
    "\<forall>Y. indep1 Y \<and> indep2 Y \<and> card Y \<le> card (to_set (wsol st))
       \<longrightarrow> sum (c_lookup (worig st)) Y \<le> sum (c_lookup (worig st)) (to_set (wbest st))"
    using assms(1) by (simp_all add: w_invar_def)
  have iv1: "indep1 (to_set X)" and iv2: "indep2 (to_set X)" and sinv: "set_invar X"
    and Xc: "to_set X \<subseteq> carrier" and ci1: "c_invar c1" and ci2: "c_invar c2"
    using facts df(1,2,3) by simp_all
  have finX: "finite (to_set X)" using matroid1.indep_finite[OF iv1] .
  have cInvComp: "set_invar_red (complement X)" using complement(1)[OF sinv Xc] .
  have compIs: "to_set_red (complement X) = carrier - to_set X" using complement(2)[OF sinv Xc] .
  note cgc = U.compute_graph_circuit_correct[OF iv1 iv2 sinv cInvComp, OF compIs[THEN equalityD1] df(4)]
  note cgm = U.compute_graph_meaning_circuit[OF iv1 iv2 sinv cInvComp compIs df(4)]
  have SXinv: "vset_inv SX" and SXis: "vset SX = S (to_set X)" and TXis: "vset TX = T (to_set X)"
    using cgc(1) cgm(1,2) by simp_all
  note ctc = compute_tight_graph_circuit_correct[OF iv1 iv2 sinv cInvComp, OF compIs[THEN equalityD1]]
  have Gt_inv: "graph.graph_inv Gtight" using ctc(1) df(7) by simp
  have vsinvSbar: "vset_inv SbarX" using restrict_to_max(1)[OF ci1 SXinv] df(5) by simp
  have Rinv: "vset_inv R" using reach_set(1)[OF Gt_inv vsinvSbar] df(8) by simp
  have isinR: "\<And>z. (z \<in>\<^sub>G R) = (z \<in> vset R)" using graph.vset.set.set_isin[OF Rinv] by simp
  have yD: "\<And>y. y \<in> carrier - to_set X \<Longrightarrow> y \<in> to_set_red (complement X)" using compIs by simp
  have D_empty: "(\<Union> y \<in> to_set_red (complement X). Dgap X R m1 m2 c1 c2 y) = {}"
    using df(10)[folded m1_def m2_def] unfolding eps_meaning_circuit[OF iv1 iv2 sinv finX Xc] eps_of_None
    by (auto split: if_splits)
  have Ssub: "S (to_set X) \<subseteq> vset R"
  proof
    fix y assume yS: "y \<in> S (to_set X)"
    have yc: "y \<in> carrier - to_set X" and iy: "indep1 (Set.insert y (to_set X))"
      using yS by (auto simp add: S_def)
    have woy: "weak_orcl1 y X" using weak_orcl1[OF sinv Xc _ _ iv1] yc iy by auto
    show "y \<in> vset R"
    proof (rule ccontr)
      assume "y \<notin> vset R"
      hence "m1 - c_lookup c1 y \<in> Dgap X R m1 m2 c1 c2 y"
        using woy isinR by (auto simp add: Dgap_def Dgap1_def)
      thus False using D_empty yD[OF yc] by auto
    qed
  qed
  have Tdisj: "T (to_set X) \<inter> vset R = {}"
  proof (rule ccontr)
    assume "T (to_set X) \<inter> vset R \<noteq> {}"
    then obtain y where yT: "y \<in> T (to_set X)" and yR: "y \<in> vset R" by auto
    have yc: "y \<in> carrier - to_set X" and iy: "indep2 (Set.insert y (to_set X))"
      using yT by (auto simp add: T_def)
    have woy: "weak_orcl2 y X" using weak_orcl2[OF sinv Xc _ _ iv2] yc iy by auto
    have "m2 - c_lookup c2 y \<in> Dgap X R m1 m2 c1 c2 y"
      using woy yR isinR by (auto simp add: Dgap_def Dgap2_def)
    thus False using D_empty yD[OF yc] by auto
  qed
  have clA1: "\<And>x y. (x, y) \<in> A1 (to_set X) \<Longrightarrow> x \<in> vset R \<Longrightarrow> y \<in> vset R"
  proof -
    fix x y assume arc: "(x, y) \<in> A1 (to_set X)" and xR: "x \<in> vset R"
    have o: "x \<in> to_set X \<and> weak_orcl1 y (set_delete x X) \<and> \<not> weak_orcl1 y X \<and> y \<in> carrier - to_set X"
      using arc1_to_orcl[OF iv1 sinv Xc arc] .
    show "y \<in> vset R"
    proof (rule ccontr)
      assume "y \<notin> vset R"
      hence "c_lookup c1 x - c_lookup c1 y \<in> Dgap X R m1 m2 c1 c2 y"
        using o xR isinR by (auto simp add: Dgap_def Dgap1_def)
      thus False using D_empty yD[OF conjunct2[OF conjunct2[OF conjunct2[OF o]]]] by auto
    qed
  qed
  have clA2: "\<And>x y. (y, x) \<in> A2 (to_set X) \<Longrightarrow> y \<in> vset R \<Longrightarrow> x \<in> vset R"
  proof -
    fix x y assume arc: "(y, x) \<in> A2 (to_set X)" and yR: "y \<in> vset R"
    have o: "x \<in> to_set X \<and> weak_orcl2 y (set_delete x X) \<and> \<not> weak_orcl2 y X \<and> y \<in> carrier - to_set X"
      using arc2_to_orcl[OF iv2 sinv Xc arc] .
    show "x \<in> vset R"
    proof (rule ccontr)
      assume "x \<notin> vset R"
      hence "c_lookup c2 x - c_lookup c2 y \<in> Dgap X R m1 m2 c1 c2 y"
        using o yR isinR by (auto simp add: Dgap_def Dgap2_def)
      thus False using D_empty yD[OF conjunct2[OF conjunct2[OF conjunct2[OF o]]]] by auto
    qed
  qed
  have closed: "\<And>a b. (a, b) \<in> A1 (to_set X) \<union> A2 (to_set X) \<Longrightarrow> a \<in> vset R \<Longrightarrow> b \<in> vset R"
    using clA1 clA2 by auto
  have noaug: "\<nexists> p x y. x \<in> S (to_set X) \<and> y \<in> T (to_set X)
                 \<and> (vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) x p y \<or> x = y)"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then obtain p x y where xy: "x \<in> S (to_set X)" "y \<in> T (to_set X)"
      "vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) x p y \<or> x = y" by auto
    have xR: "x \<in> vset R" using xy(1) Ssub by auto
    have "y \<in> vset R" using xy(3)
    proof
      assume w: "vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) x p y"
      show "y \<in> vset R" by (rule walk_stays_closed[OF w xR closed])
    next
      assume "x = y" thus "y \<in> vset R" using xR by simp
    qed
    thus False using xy(2) Tdisj by auto
  qed
  have ismax: "\<nexists> Y. indep1 Y \<and> indep2 Y \<and> card (to_set X) < card Y"
    using if_no_augpath_then_maximum(1)[OF iv1 iv2 noaug refl] .
  have le: "\<And>Y. indep1 Y \<Longrightarrow> indep2 Y \<Longrightarrow> card Y \<le> card (to_set X)"
    using ismax by (meson not_le)
  have opt: "\<forall>Y. indep1 Y \<and> indep2 Y \<longrightarrow>
                sum (c_lookup (worig st)) Y \<le> sum (c_lookup (worig st)) (to_set (wbest st))"
    using facts(14) le df(1) by auto
  show "indep1 (to_set (wbest st)) \<and> indep2 (to_set (wbest st))
         \<and> (\<forall>Y. indep1 Y \<and> indep2 Y \<longrightarrow>
              sum (c_lookup (worig st)) Y \<le> sum (c_lookup (worig st)) (to_set (wbest st)))"
    using facts(12,13) opt by blast
qed

lemma w_invar_reweight_circuit:
  assumes "w_invar st" "weighted_reweight_cond_circuit st"
  shows "w_invar (weighted_reweight_upd_circuit st)"
proof (rule P_of_weighted_reweight_circuitI[OF assms(2)])
  fix SX TX G SbarX TbarX Gtight R e X c1 c2
  assume df: "X = wsol st" "c1 = wc1 st" "c2 = wc2 st"
    "compute_graph_circuit X (complement X) = (SX, TX, G)"
    "SbarX = restrict_to_max SX c1" "TbarX = restrict_to_max TX c2"
    "Gtight = compute_tight_graph_circuit X c1 c2 (complement X)"
    "R = reach_set SbarX Gtight"
    "find_path SbarX TbarX Gtight = None"
    "compute_eps_circuit X (weight_Max SX c1) (weight_Max TX c2) R c1 c2 = Some e"
  interpret W: weighted_intersection_graph carrier indep1 indep2 "c_lookup c1" "c_lookup c2"
    by unfold_locales
  define m1 where "m1 = weight_Max SX c1"
  define m2 where "m2 = weight_Max TX c2"
  have facts: "set_invar (wsol st)" "to_set (wsol st) \<subseteq> carrier"
    "indep1 (to_set (wsol st))" "indep2 (to_set (wsol st))"
    "c_invar (wc1 st)" "c_invar (wc2 st)" "c_invar (worig st)"
    "\<forall>z\<in>carrier. c_lookup (wc1 st) z + c_lookup (wc2 st) z = c_lookup (worig st) z"
    "matroid1.local_opt (c_lookup (wc1 st)) (to_set (wsol st))"
    "matroid2.local_opt (c_lookup (wc2 st)) (to_set (wsol st))"
    "set_invar (wbest st)" "indep1 (to_set (wbest st))" "indep2 (to_set (wbest st))"
    "\<forall>Y. indep1 Y \<and> indep2 Y \<and> card Y \<le> card (to_set (wsol st))
       \<longrightarrow> sum (c_lookup (worig st)) Y \<le> sum (c_lookup (worig st)) (to_set (wbest st))"
    using assms(1) by (simp_all add: w_invar_def)
  have iv1: "indep1 (to_set X)" and iv2: "indep2 (to_set X)" and sinv: "set_invar X"
    and Xc: "to_set X \<subseteq> carrier" and ci1: "c_invar c1" and ci2: "c_invar c2"
    and lo1: "matroid1.local_opt (c_lookup c1) (to_set X)"
    and lo2: "matroid2.local_opt (c_lookup c2) (to_set X)"
    using facts df(1,2,3) by simp_all
  have finX: "finite (to_set X)" using matroid1.indep_finite[OF iv1] .
  have cInvComp: "set_invar_red (complement X)" using complement(1)[OF sinv Xc] .
  have compIs: "to_set_red (complement X) = carrier - to_set X" using complement(2)[OF sinv Xc] .
  have esome': "compute_eps X (weight_Max SX c1) (weight_Max TX c2) R c1 c2 = Some e"
    using df(10) compute_eps_circuit_eq[OF iv1 iv2 sinv finX Xc] by simp
  note cgc = U.compute_graph_circuit_correct[OF iv1 iv2 sinv cInvComp, OF compIs[THEN equalityD1] df(4)]
  note cgm = U.compute_graph_meaning_circuit[OF iv1 iv2 sinv cInvComp compIs df(4)]
  have SXinv: "vset_inv SX" and TXinv: "vset_inv TX"
    and SXis: "vset SX = S (to_set X)" and TXis: "vset TX = T (to_set X)"
    using cgc(1,2) cgm(1,2) by simp_all
  note ctc = compute_tight_graph_circuit_correct[OF iv1 iv2 sinv cInvComp, OF compIs[THEN equalityD1]]
  have Gt_inv: "graph.graph_inv Gtight" and Gt_fg: "graph.finite_graph Gtight"
    and Gt_fv: "graph.finite_vsets Gtight"
    using ctc(1,3,4) df(7) by simp_all
  have Gt_dig: "graph.digraph_abs Gtight = W.Gbar (to_set X)"
    using compute_tight_graph_circuit_meaning[OF iv1 iv2 sinv cInvComp compIs] df(7) by simp
  have vsinvSbar: "vset_inv SbarX" using restrict_to_max(1)[OF ci1 SXinv] df(5) by simp
  have vsSbar: "vset SbarX = W.Sbar (to_set X)"
    using restrict_to_max_Sbar[OF ci1 SXinv SXis] df(5) by (simp add: W.Sbar_def)
  have Sbarcarr: "vset SbarX \<subseteq> carrier" using vsSbar W.Sbar_subset S_in_carrier[OF iv1 iv2] by auto
  have Gt_verts: "dVs (graph.digraph_abs Gtight) \<subseteq> carrier"
    using Gt_dig W.Gbar_subset dVs_A1A2_carrier[OF iv1 iv2] dVs_subset by (metis subset_trans)
  have Rinv: "vset_inv R" using reach_set(1)[OF Gt_inv vsinvSbar] df(8) by simp
  have RsubC: "vset R \<subseteq> carrier"
    using reach_set_carrier[OF Gt_inv vsinvSbar Sbarcarr Gt_verts] df(8) by simp
  have isinR: "\<And>z. (z \<in>\<^sub>G R) = (z \<in> vset R)" using graph.vset.set.set_isin[OF Rinv] by simp
  have epos: "0 < e"
    using eps_pos[OF iv1 iv2 sinv Xc lo1 lo2 ci1 ci2 SXinv SXis TXinv TXis
                     df(5) df(6) Gt_inv Gt_fg Gt_fv Gt_dig df(8) df(9) esome'] .
  have yD: "\<And>y. y \<in> carrier - to_set X \<Longrightarrow> y \<in> to_set_red (complement X)" using compIs by simp
  have gapA1: "e \<le> c_lookup c1 x - c_lookup c1 y"
    if "(x, y) \<in> A1 (to_set X)" "x \<in> vset R" "y \<notin> vset R" for x y
  proof -
    have o: "x \<in> to_set X \<and> weak_orcl1 y (set_delete x X) \<and> \<not> weak_orcl1 y X \<and> y \<in> carrier - to_set X"
      using arc1_to_orcl[OF iv1 sinv Xc that(1)] .
    have "c_lookup c1 x - c_lookup c1 y \<in> Dgap X R m1 m2 c1 c2 y"
      using o that(2,3) isinR by (auto simp add: Dgap_def Dgap1_def)
    thus ?thesis using eps_le_gap[OF sinv finX Xc esome'[folded m1_def m2_def] yD[OF conjunct2[OF conjunct2[OF conjunct2[OF o]]]]] by simp
  qed
  have gapB1: "e \<le> c_lookup c1 x - c_lookup c1 y"
    if "x \<in> to_set X" "y \<in> S (to_set X)" "y \<notin> vset R" for x y
  proof -
    have yc: "y \<in> carrier - to_set X" and iy: "indep1 (Set.insert y (to_set X))"
      using that(2) by (auto simp add: S_def)
    have woy: "weak_orcl1 y X" using weak_orcl1[OF sinv Xc _ _ iv1] yc iy by auto
    have "m1 - c_lookup c1 y \<in> Dgap X R m1 m2 c1 c2 y"
      using woy that(3) isinR by (auto simp add: Dgap_def Dgap1_def)
    hence e_le: "e \<le> m1 - c_lookup c1 y"
      using eps_le_gap[OF sinv finX Xc esome'[folded m1_def m2_def] yD[OF yc]] by simp
    have "m1 = Max (c_lookup c1 ` S (to_set X))"
      using weight_Max[OF ci1 SXinv] that(2) SXis m1_def by auto
    hence "m1 \<le> c_lookup c1 x" using Smax_le[OF lo1 iv1 iv2 that(1,2)] by simp
    thus ?thesis using e_le by simp
  qed
  have gapA2: "e \<le> c_lookup c2 x - c_lookup c2 y"
    if "(y, x) \<in> A2 (to_set X)" "y \<in> vset R" "x \<notin> vset R" for x y
  proof -
    have o: "x \<in> to_set X \<and> weak_orcl2 y (set_delete x X) \<and> \<not> weak_orcl2 y X \<and> y \<in> carrier - to_set X"
      using arc2_to_orcl[OF iv2 sinv Xc that(1)] .
    have "c_lookup c2 x - c_lookup c2 y \<in> Dgap X R m1 m2 c1 c2 y"
      using o that(2,3) isinR by (auto simp add: Dgap_def Dgap2_def)
    thus ?thesis using eps_le_gap[OF sinv finX Xc esome'[folded m1_def m2_def] yD[OF conjunct2[OF conjunct2[OF conjunct2[OF o]]]]] by simp
  qed
  have gapB2: "e \<le> c_lookup c2 x - c_lookup c2 y"
    if "x \<in> to_set X" "y \<in> T (to_set X)" "y \<in> vset R" for x y
  proof -
    have yc: "y \<in> carrier - to_set X" and iy: "indep2 (Set.insert y (to_set X))"
      using that(2) by (auto simp add: T_def)
    have woy: "weak_orcl2 y X" using weak_orcl2[OF sinv Xc _ _ iv2] yc iy by auto
    have "m2 - c_lookup c2 y \<in> Dgap X R m1 m2 c1 c2 y"
      using woy that(3) isinR by (auto simp add: Dgap_def Dgap2_def)
    hence e_le: "e \<le> m2 - c_lookup c2 y"
      using eps_le_gap[OF sinv finX Xc esome'[folded m1_def m2_def] yD[OF yc]] by simp
    have "m2 = Max (c_lookup c2 ` T (to_set X))"
      using weight_Max[OF ci2 TXinv] that(2) TXis m2_def by auto
    hence "m2 \<le> c_lookup c2 x" using Tmax_le[OF lo2 iv1 iv2 that(1,2)] by simp
    thus ?thesis using e_le by simp
  qed
  have lo1': "matroid1.local_opt (\<lambda>z. if z \<in> vset R then c_lookup c1 z - e else c_lookup c1 z) (to_set X)"
  proof (rule matroid1.reweight_preserves_local_opt[OF iv1 lo1 RsubC epos])
    fix y x assume A: "y \<in> carrier - to_set X" "x \<in> matroid1.the_circuit (Set.insert y (to_set X)) - {y}"
      "x \<in> vset R" "y \<notin> vset R"
    have arc: "(x, y) \<in> A1 (to_set X)" using A(1,2) by (auto simp add: A1_def)
    show "e \<le> c_lookup c1 x - c_lookup c1 y" using gapA1[OF arc A(3) A(4)] .
  next
    fix x y assume B: "x \<in> to_set X" "y \<in> carrier - to_set X" "indep1 (Set.insert y (to_set X))"
      "x \<in> vset R" "y \<notin> vset R"
    have yS: "y \<in> S (to_set X)" using B(2,3) by (auto simp add: S_def)
    show "e \<le> c_lookup c1 x - c_lookup c1 y" using gapB1[OF B(1) yS B(5)] .
  qed
  have wc1'eq: "c_lookup (c_shift R (- e) c1) = (\<lambda>z. if z \<in> vset R then c_lookup c1 z - e else c_lookup c1 z)"
    using c_shift(2)[OF ci1 Rinv] by auto
  have C9: "matroid1.local_opt (c_lookup (c_shift R (- e) c1)) (to_set X)" using lo1' wc1'eq by simp
  have lo_d: "matroid2.local_opt (\<lambda>z. if z \<in> carrier - vset R then c_lookup c2 z - e else c_lookup c2 z) (to_set X)"
  proof (rule matroid2.reweight_preserves_local_opt[OF iv2 lo2 Diff_subset epos])
    fix y x assume A: "y \<in> carrier - to_set X" "x \<in> matroid2.the_circuit (Set.insert y (to_set X)) - {y}"
      "x \<in> carrier - vset R" "y \<notin> carrier - vset R"
    have arc: "(y, x) \<in> A2 (to_set X)" using A(1,2) by (auto simp add: A2_def)
    have xnR: "x \<notin> vset R" using A(3) by simp
    have yR: "y \<in> vset R" using A(1,4) by simp
    show "e \<le> c_lookup c2 x - c_lookup c2 y" using gapA2[OF arc yR xnR] .
  next
    fix x y assume B: "x \<in> to_set X" "y \<in> carrier - to_set X" "indep2 (Set.insert y (to_set X))"
      "x \<in> carrier - vset R" "y \<notin> carrier - vset R"
    have yT: "y \<in> T (to_set X)" using B(2,3) by (auto simp add: T_def)
    have yR: "y \<in> vset R" using B(2,5) by simp
    show "e \<le> c_lookup c2 x - c_lookup c2 y" using gapB2[OF B(1) yT yR] .
  qed
  have lo_de: "matroid2.local_opt (\<lambda>z. (if z \<in> carrier - vset R then c_lookup c2 z - e else c_lookup c2 z) + e) (to_set X)"
    using local_opt2_add[OF lo_d] .
  have wc2'eq: "c_lookup (c_shift R e c2) = (\<lambda>z. if z \<in> vset R then c_lookup c2 z + e else c_lookup c2 z)"
    using c_shift(2)[OF ci2 Rinv] by auto
  have agree: "\<forall>z\<in>carrier. (if z \<in> carrier - vset R then c_lookup c2 z - e else c_lookup c2 z) + e
                            = c_lookup (c_shift R e c2) z"
    using RsubC by (auto simp add: wc2'eq)
  have C10: "matroid2.local_opt (c_lookup (c_shift R e c2)) (to_set X)"
    using local_opt2_cong_imp[OF Xc agree lo_de] .
  have C5: "c_invar (c_shift R (- e) c1)" using c_shift(1)[OF ci1 Rinv] .
  have C6: "c_invar (c_shift R e c2)" using c_shift(1)[OF ci2 Rinv] .
  have C8: "\<forall>z\<in>carrier. c_lookup (c_shift R (- e) c1) z + c_lookup (c_shift R e c2) z = c_lookup (worig st) z"
  proof
    fix z assume zc: "z \<in> carrier"
    have "c_lookup (c_shift R (- e) c1) z + c_lookup (c_shift R e c2) z = c_lookup c1 z + c_lookup c2 z"
      by (simp add: wc1'eq wc2'eq)
    also have "\<dots> = c_lookup (worig st) z" using facts(8) df(2,3) zc by simp
    finally show "c_lookup (c_shift R (- e) c1) z + c_lookup (c_shift R e c2) z = c_lookup (worig st) z" .
  qed
  show "w_invar (reweight R e st)"
    unfolding w_invar_def reweight_def
    using facts(1,2,3,4,7,11,12,13,14) C5 C6 C8 C9 C10 df(1,2,3) by simp
qed

lemma weighted_worig_preserved_circuit:
  assumes "weighted_matroid_intersection_circuit_dom st"
  shows "worig (weighted_matroid_intersection_circuit st) = worig st"
proof (induction st rule: weighted_matroid_intersection_circuit_induct)
  case 1
  show ?case by (rule assms)
next
  case (2 st)
  show ?case
  proof (cases st rule: weighted_matroid_intersection_circuit_cases)
    case 1
    show ?thesis by (simp add: weighted_matroid_intersection_circuit_simps(1)[OF "2.hyps"(1) 1])
  next
    case 2
    have wo: "worig (weighted_augment_upd_circuit st) = worig st"
      by (simp add: weighted_augment_upd_circuit_def Let_def split: prod.split)
    have "worig (weighted_matroid_intersection_circuit (weighted_augment_upd_circuit st))
            = worig (weighted_augment_upd_circuit st)"
      by (rule "2.IH"(1)[OF 2])
    thus ?thesis
      by (simp add: weighted_matroid_intersection_circuit_simps(2)[OF "2.hyps"(1) 2] wo)
  next
    case 3
    have wo: "worig (weighted_reweight_upd_circuit st) = worig st"
      by (simp add: weighted_reweight_upd_circuit_def reweight_def Let_def split: prod.split)
    have "worig (weighted_matroid_intersection_circuit (weighted_reweight_upd_circuit st))
            = worig (weighted_reweight_upd_circuit st)"
      by (rule "2.IH"(2)[OF 3])
    thus ?thesis
      by (simp add: weighted_matroid_intersection_circuit_simps(3)[OF "2.hyps"(1) 3] wo)
  qed
qed

lemma weighted_correctness_general_circuit:
  assumes "weighted_matroid_intersection_circuit_dom st" "w_invar st"
  shows "indep1 (to_set (wbest (weighted_matroid_intersection_circuit st)))
       \<and> indep2 (to_set (wbest (weighted_matroid_intersection_circuit st)))
       \<and> (\<forall>Y. indep1 Y \<and> indep2 Y \<longrightarrow>
            sum (c_lookup (worig (weighted_matroid_intersection_circuit st))) Y
              \<le> sum (c_lookup (worig (weighted_matroid_intersection_circuit st)))
                     (to_set (wbest (weighted_matroid_intersection_circuit st))))"
  using assms(2)
proof (induction st rule: weighted_matroid_intersection_circuit_induct)
  case 1
  show ?case by (rule assms(1))
next
  case (2 st)
  show ?case
  proof (cases st rule: weighted_matroid_intersection_circuit_cases)
    case 1
    show ?thesis
      using w_invar_max_found_circuit[OF "2.prems" 1]
            weighted_matroid_intersection_circuit_simps(1)[OF "2.hyps"(1) 1]
      by simp
  next
    case 2
    show ?thesis
      unfolding weighted_matroid_intersection_circuit_simps(2)[OF "2.hyps"(1) 2]
      by (rule "2.IH"(1)[OF 2 w_invar_augment_circuit[OF "2.prems" 2]])
  next
    case 3
    show ?thesis
      unfolding weighted_matroid_intersection_circuit_simps(3)[OF "2.hyps"(1) 3]
      by (rule "2.IH"(2)[OF 3 w_invar_reweight_circuit[OF "2.prems" 3]])
  qed
qed

theorem weighted_matroid_intersection_circuit_partial_correct:
  assumes "c_invar c" "weighted_matroid_intersection_circuit_dom (weighted_initial_state c)"
  defines "s \<equiv> weighted_matroid_intersection_circuit (weighted_initial_state c)"
  shows "weighted_double_matroid.is_opt indep1 indep2 (c_lookup c) (to_set (wbest s))"
proof -
  interpret WDM: weighted_double_matroid carrier indep1 indep2 "c_lookup c" by unfold_locales
  have "worig s = c" using weighted_worig_preserved_circuit[OF assms(2)]
    by (simp add: s_def weighted_initial_state_def)
  hence "indep1 (to_set (wbest s)) \<and> indep2 (to_set (wbest s))
       \<and> (\<forall>Y. indep1 Y \<and> indep2 Y \<longrightarrow> sum (c_lookup c) Y \<le> sum (c_lookup c) (to_set (wbest s)))"
    using weighted_correctness_general_circuit[OF assms(2) w_invar_initial[OF assms(1)]] by (simp add: s_def)
  thus ?thesis unfolding WDM.is_opt_def by blast
qed

subsubsection \<open>Termination of the circuit loop\<close>

text \<open>The circuit loop terminates and is totally correct by exactly the plain argument: its tight graph and
\<open>\<epsilon>\<close> abstract to the same objects (@{thm [source] compute_tight_graph_circuit_meaning}, @{thm [source]
compute_eps_circuit_eq}), and reachability/paths depend only on those (@{thm [source] reach_set_cong},
@{thm [source] find_path_None_cong}).\<close>

definition "wSX_circuit st = fst (compute_graph_circuit (wsol st) (complement (wsol st)))"
definition "wTX_circuit st = fst (snd (compute_graph_circuit (wsol st) (complement (wsol st))))"
definition "wGt_circuit st = compute_tight_graph_circuit (wsol st) (wc1 st) (wc2 st) (complement (wsol st))"
definition "wRverts_circuit st = vset (reach_set (restrict_to_max (wSX_circuit st) (wc1 st)) (wGt_circuit st))"
definition "wPathNone_circuit st = (find_path (restrict_to_max (wSX_circuit st) (wc1 st)) (restrict_to_max (wTX_circuit st) (wc2 st)) (wGt_circuit st) = None)"
definition "wmeasure_circuit st = (card carrier - card (to_set (wsol st))) * (2 * card carrier + 2)
                          + 2 * (card carrier - card (wRverts_circuit st)) + (if wPathNone_circuit st then 1 else 0)"

lemma wRP_state_circuit:
  assumes "X = wsol st" "c1 = wc1 st" "c2 = wc2 st"
    "compute_graph_circuit X (complement X) = (SX, TX, G)"
    "SbarX = restrict_to_max SX c1" "TbarX = restrict_to_max TX c2"
    "Gtight = compute_tight_graph_circuit X c1 c2 (complement X)"
    "R = reach_set SbarX Gtight"
  shows "wRverts_circuit st = vset R \<and> wPathNone_circuit st = (find_path SbarX TbarX Gtight = None)"
  by (simp only: wRverts_circuit_def wPathNone_circuit_def wSX_circuit_def wTX_circuit_def wGt_circuit_def
        assms(1)[symmetric] assms(2)[symmetric] assms(3)[symmetric] assms(4) prod.sel
        assms(5)[symmetric] assms(6)[symmetric] assms(7)[symmetric] assms(8)[symmetric])

lemma weighted_augment_card_circuit:
  assumes "w_invar st" "weighted_augment_cond_circuit st"
  shows "card (to_set (wsol (weighted_augment_upd_circuit st))) = card (to_set (wsol st)) + 1"
proof(rule P_of_weighted_augment_circuitI[OF assms(2)])
  fix SX TX G SbarX TbarX Gtight p X c1 c2
  assume df: "X = wsol st" "c1 = wc1 st" "c2 = wc2 st"
    "compute_graph_circuit X (complement X) = (SX, TX, G)"
    "SbarX = restrict_to_max SX c1" "TbarX = restrict_to_max TX c2"
    "Gtight = compute_tight_graph_circuit X c1 c2 (complement X)"
    "find_path SbarX TbarX Gtight = Some p"
  interpret W: weighted_intersection_graph carrier indep1 indep2 "c_lookup c1" "c_lookup c2" by unfold_locales
  have facts: "set_invar X" "indep1 (to_set X)" "indep2 (to_set X)"
    "c_invar c1" "c_invar c2" "c_invar (worig st)"
    "\<forall>x\<in>carrier. c_lookup c1 x + c_lookup c2 x = c_lookup (worig st) x"
    "matroid1.local_opt (c_lookup c1) (to_set X)" "matroid2.local_opt (c_lookup c2) (to_set X)"
    "set_invar (wbest st)" "indep1 (to_set (wbest st))" "indep2 (to_set (wbest st))"
    "\<forall>Y. indep1 Y \<and> indep2 Y \<and> card Y \<le> card (to_set X) \<longrightarrow>
       sum (c_lookup (worig st)) Y \<le> sum (c_lookup (worig st)) (to_set (wbest st))"
    using assms(1) by (simp_all add: w_invar_def df(1,2,3))
  have Xcarr: "to_set X \<subseteq> carrier" using matroid1.indep_subset_carrier[OF facts(2)] .
  have cInvComp: "set_invar_red (complement X)" using complement(1)[OF facts(1) Xcarr] .
  have compIs: "to_set_red (complement X) = carrier - to_set X" using complement(2)[OF facts(1) Xcarr] .
  have compCarr: "to_set_red (complement X) \<subseteq> carrier - to_set X" using compIs by simp
  note cgc = U.compute_graph_circuit_correct[OF facts(2,3,1) cInvComp compCarr df(4)]
  note cgm = U.compute_graph_meaning_circuit[OF facts(2,3,1) cInvComp compIs df(4)]
  note ctc = compute_tight_graph_circuit_correct[OF facts(2,3,1) cInvComp compCarr]
  have Gt_inv: "graph.graph_inv Gtight" and Gt_fg: "graph.finite_graph Gtight" and Gt_fv: "graph.finite_vsets Gtight"
    using ctc(1,3,4) df(7) by simp_all
  have Gt_dig: "graph.digraph_abs Gtight = W.Gbar (to_set X)"
    using compute_tight_graph_circuit_meaning[OF facts(2,3,1) cInvComp compIs] df(7) by simp
  have vsinvSbar: "vset_inv SbarX" using restrict_to_max(1)[OF facts(4) cgc(1)] df(5) by simp
  have vsinvTbar: "vset_inv TbarX" using restrict_to_max(1)[OF facts(5) cgc(2)] df(6) by simp
  have vsSbar: "vset SbarX = W.Sbar (to_set X)" using restrict_to_max_Sbar[OF facts(4) cgc(1) cgm(1)] df(5) by (simp add: W.Sbar_def)
  have vsTbar: "vset TbarX = W.Tbar (to_set X)" using restrict_to_max_Tbar[OF facts(5) cgc(2) cgm(2)] df(6) by (simp add: W.Tbar_def)
  have Sbarcarr: "vset SbarX \<subseteq> carrier" using vsSbar S_in_carrier[OF facts(2,3)] by (auto simp add: W.Sbar_def)
  have Tbarcarr: "vset TbarX \<subseteq> carrier" using vsTbar T_in_carrier[OF facts(2,3)] by (auto simp add: W.Tbar_def)
  have Gt_verts: "dVs (graph.digraph_abs Gtight) \<subseteq> carrier"
  proof-
    have "dVs (W.Gbar (to_set X)) \<subseteq> dVs (A1 (to_set X) \<union> A2 (to_set X))" by (rule dVs_subset[OF W.Gbar_subset])
    thus ?thesis using Gt_dig dVs_A1A2_carrier[OF facts(2,3)] by auto
  qed
  obtain u v where p_prop:
    "vwalk_bet (W.Gbar (to_set X)) u p v \<or> (p = [u] \<and> u = v)"
    "u \<in> W.Sbar (to_set X)" "v \<in> W.Tbar (to_set X)"
    "\<nexists>q. (vwalk_bet (W.Gbar (to_set X)) u q v \<or> (q = [u] \<and> u = v)) \<and> length q < length p"
    using find_path(2)[OF Gt_inv Gt_fg Gt_fv vsinvSbar vsinvTbar Sbarcarr Tbarcarr Gt_verts df(8)]
    by (simp add: Gt_dig vsSbar vsTbar) blast
  define ev where "ev = {p ! i | i. i < length p \<and> even i}"
  define od where "od = {p ! i | i. i < length p \<and> odd i}"
  define Xp where "Xp = (to_set X \<union> ev) - od"
  have sh_gbar: "\<nexists>q. vwalk_bet (W.Gbar (to_set X)) u q v \<and> length q < length p" using p_prop(4) by blast
  have big: "set p \<subseteq> carrier \<and> distinct p \<and> card Xp = card (to_set X) + 1"
  proof(cases "vwalk_bet (W.Gbar (to_set X)) u p v")
    case True
    have pc: "set p \<subseteq> carrier" using vwalk_bet_in_vertices[OF True] Gt_verts Gt_dig by auto
    have dp: "distinct p" using shortest_vwalk_bet_distinct[OF True sh_gbar] .
    note atp = W.augment_tight_path[OF facts(2,3,8,9) True p_prop(2,3) sh_gbar refl]
    show ?thesis using pc dp atp by (auto simp add: Xp_def ev_def od_def)
  next
    case False
    hence su: "p = [u]" "u = v" using p_prop(1) by auto
    have uS: "u \<in> S (to_set X)" using p_prop(2) W.Sbar_subset by auto
    have unX: "u \<in> carrier - to_set X" using uS by (auto simp add: S_def)
    have Xp_is: "Xp = Set.insert u (to_set X)" using su by (auto simp add: Xp_def ev_def od_def)
    have "card (Set.insert u (to_set X)) = card (to_set X) + 1" using unX matroid1.indep_finite[OF facts(2)] by simp
    thus ?thesis using Xp_is su unX by auto
  qed
  have pcarr: "set p \<subseteq> carrier" and distinctp: "distinct p" and cXcard: "card Xp = card (to_set X) + 1" using big by auto
  have Xpeq: "to_set (augment X p) = Xp"
    using U.effect_of_augmentation(2)[OF facts(1) Xcarr pcarr distinctp refl] by (simp add: Xp_def ev_def od_def)
  show "card (to_set (wsol (st\<lparr>wsol := augment X p, wbest := keep_better st (augment X p)\<rparr>))) = card (to_set (wsol st)) + 1"
    using cXcard Xpeq df(1) by simp
qed

lemma wmeasure_reweight_dec_circuit:
  assumes "w_invar st" "weighted_reweight_cond_circuit st"
  shows "wmeasure_circuit (weighted_reweight_upd_circuit st) < wmeasure_circuit st"
proof (rule P_of_weighted_reweight_circuitI[OF assms(2)])
  fix SX TX G SbarX TbarX Gtight R e X c1 c2
  assume df: "X = wsol st" "c1 = wc1 st" "c2 = wc2 st"
    "compute_graph_circuit X (complement X) = (SX, TX, G)"
    "SbarX = restrict_to_max SX c1" "TbarX = restrict_to_max TX c2"
    "Gtight = compute_tight_graph_circuit X c1 c2 (complement X)"
    "R = reach_set SbarX Gtight"
    "find_path SbarX TbarX Gtight = None"
    "compute_eps_circuit X (weight_Max SX c1) (weight_Max TX c2) R c1 c2 = Some e"
  interpret W': weighted_intersection_graph carrier indep1 indep2 "c_lookup (c_shift R (- e) c1)" "c_lookup (c_shift R e c2)" by unfold_locales
  interpret Wm: weighted_intersection_graph carrier indep1 indep2 "c_lookup c1" "c_lookup c2" by unfold_locales
  have facts: "set_invar (wsol st)" "to_set (wsol st) \<subseteq> carrier" "indep1 (to_set (wsol st))" "indep2 (to_set (wsol st))"
    "c_invar (wc1 st)" "c_invar (wc2 st)" "c_invar (worig st)"
    "\<forall>z\<in>carrier. c_lookup (wc1 st) z + c_lookup (wc2 st) z = c_lookup (worig st) z"
    "matroid1.local_opt (c_lookup (wc1 st)) (to_set (wsol st))" "matroid2.local_opt (c_lookup (wc2 st)) (to_set (wsol st))"
    "set_invar (wbest st)" "indep1 (to_set (wbest st))" "indep2 (to_set (wbest st))"
    "\<forall>Y. indep1 Y \<and> indep2 Y \<and> card Y \<le> card (to_set (wsol st)) \<longrightarrow> sum (c_lookup (worig st)) Y \<le> sum (c_lookup (worig st)) (to_set (wbest st))"
    using assms(1) by (simp_all add: w_invar_def)
  have iv1: "indep1 (to_set X)" and iv2: "indep2 (to_set X)" and sinv: "set_invar X" and Xc: "to_set X \<subseteq> carrier"
    and ci1: "c_invar c1" and ci2: "c_invar c2"
    and lo1: "matroid1.local_opt (c_lookup c1) (to_set X)" and lo2: "matroid2.local_opt (c_lookup c2) (to_set X)"
    using facts df(1,2,3) by simp_all
  have finX: "finite (to_set X)" using matroid1.indep_finite[OF iv1] .
  have cInvComp: "set_invar_red (complement X)" using complement(1)[OF sinv Xc] .
  have compIs: "to_set_red (complement X) = carrier - to_set X" using complement(2)[OF sinv Xc] .
  have esome': "compute_eps X (weight_Max SX c1) (weight_Max TX c2) R c1 c2 = Some e"
    using df(10) compute_eps_circuit_eq[OF iv1 iv2 sinv finX Xc] by simp
  note cgc = U.compute_graph_circuit_correct[OF iv1 iv2 sinv cInvComp, OF compIs[THEN equalityD1] df(4)]
  note cgm = U.compute_graph_meaning_circuit[OF iv1 iv2 sinv cInvComp compIs df(4)]
  have SXinv: "vset_inv SX" and TXinv: "vset_inv TX" and SXis: "vset SX = S (to_set X)" and TXis: "vset TX = T (to_set X)"
    using cgc(1,2) cgm(1,2) by simp_all
  note ctc = compute_tight_graph_circuit_correct[OF iv1 iv2 sinv cInvComp, OF compIs[THEN equalityD1]]
  have Gt_inv: "graph.graph_inv Gtight" and Gt_fg: "graph.finite_graph Gtight" and Gt_fv: "graph.finite_vsets Gtight"
    using ctc(1,3,4) df(7) by simp_all
  have Gt_dig: "graph.digraph_abs Gtight = weighted_intersection_graph.Gbar carrier indep1 indep2 (c_lookup c1) (c_lookup c2) (to_set X)"
    using compute_tight_graph_circuit_meaning[OF iv1 iv2 sinv cInvComp compIs] df(7) by simp
  have vsinvSbar: "vset_inv SbarX" using restrict_to_max(1)[OF ci1 SXinv] df(5) by simp
  have Rinv: "vset_inv R" using reach_set(1)[OF Gt_inv vsinvSbar] df(8) by simp
  have finC: "finite carrier" by (rule matroid1.carrier_finite)
  define Gtp' where "Gtp' = compute_tight_graph X (c_shift R (- e) c1) (c_shift R e c2) (complement X)"
  define Gtc' where "Gtc' = compute_tight_graph_circuit X (c_shift R (- e) c1) (c_shift R e c2) (complement X)"
  define Sb' where "Sb' = restrict_to_max SX (c_shift R (- e) c1)"
  define Tb' where "Tb' = restrict_to_max TX (c_shift R e c2)"
  note sop' = reweight_strict_or_path[OF iv1 iv2 sinv Xc lo1 lo2 ci1 ci2 SXinv SXis TXinv TXis df(5) df(6) Gt_inv Gt_fg Gt_fv Gt_dig df(8) df(9) esome', folded Gtp'_def Sb'_def Tb'_def]
  note rmono' = reweight_R_mono[OF iv1 iv2 sinv Xc lo1 lo2 ci1 ci2 SXinv SXis TXinv TXis df(5) df(6) Gt_inv Gt_fg Gt_fv Gt_dig df(8) df(9) esome', folded Gtp'_def Sb'_def]
  have ci1': "c_invar (c_shift R (- e) c1)" by (rule c_shift(1)[OF ci1 Rinv])
  have vsinvSb': "vset_inv Sb'" unfolding Sb'_def by (rule restrict_to_max(1)[OF ci1' SXinv])
  have vsinvTb': "vset_inv Tb'" unfolding Tb'_def by (rule restrict_to_max(1)[OF c_shift(1)[OF ci2 Rinv] TXinv])
  have Gt_inv'p: "graph.graph_inv Gtp'" unfolding Gtp'_def by (rule compute_tight_graph_correct(1)[OF iv1 iv2 sinv cInvComp compIs[THEN equalityD1]])
  have Gt_fg'p: "graph.finite_graph Gtp'" unfolding Gtp'_def by (rule compute_tight_graph_correct(3)[OF iv1 iv2 sinv cInvComp compIs[THEN equalityD1]])
  have Gt_fv'p: "graph.finite_vsets Gtp'" unfolding Gtp'_def by (rule compute_tight_graph_correct(4)[OF iv1 iv2 sinv cInvComp compIs[THEN equalityD1]])
  have Gt_dig'p: "graph.digraph_abs Gtp' = W'.Gbar (to_set X)" unfolding Gtp'_def
    using compute_tight_graph_meaning[OF iv1 iv2 sinv cInvComp compIs] by simp
  have Gt_inv'c: "graph.graph_inv Gtc'" unfolding Gtc'_def by (rule compute_tight_graph_circuit_correct(1)[OF iv1 iv2 sinv cInvComp compIs[THEN equalityD1]])
  have Gt_fg'c: "graph.finite_graph Gtc'" unfolding Gtc'_def by (rule compute_tight_graph_circuit_correct(3)[OF iv1 iv2 sinv cInvComp compIs[THEN equalityD1]])
  have Gt_fv'c: "graph.finite_vsets Gtc'" unfolding Gtc'_def by (rule compute_tight_graph_circuit_correct(4)[OF iv1 iv2 sinv cInvComp compIs[THEN equalityD1]])
  have Gt_dig'c: "graph.digraph_abs Gtc' = W'.Gbar (to_set X)" unfolding Gtc'_def
    using compute_tight_graph_circuit_meaning[OF iv1 iv2 sinv cInvComp compIs] by simp
  have digeq: "graph.digraph_abs Gtp' = graph.digraph_abs Gtc'" using Gt_dig'p Gt_dig'c by simp
  have Sbcarr': "vset Sb' \<subseteq> carrier"
  proof -
    have "vset Sb' \<subseteq> vset SX" unfolding Sb'_def restrict_to_max(2)[OF ci1' SXinv] by auto
    thus ?thesis using SXis S_in_carrier[OF iv1 iv2] by auto
  qed
  have Tbcarr': "vset Tb' \<subseteq> carrier"
  proof -
    have "vset Tb' \<subseteq> vset TX" unfolding Tb'_def restrict_to_max(2)[OF c_shift(1)[OF ci2 Rinv] TXinv] by auto
    thus ?thesis using TXis T_in_carrier[OF iv1 iv2] by auto
  qed
  have Gt_verts'p: "dVs (graph.digraph_abs Gtp') \<subseteq> carrier"
    using Gt_dig'p W'.Gbar_subset dVs_A1A2_carrier[OF iv1 iv2] dVs_subset by (metis subset_trans)
  have reachcong: "vset (reach_set Sb' Gtp') = vset (reach_set Sb' Gtc')"
    by (rule reach_set_cong[OF Gt_inv'p Gt_inv'c vsinvSb' digeq])
  have pathcong: "(find_path Sb' Tb' Gtp' = None) = (find_path Sb' Tb' Gtc' = None)"
    by (rule find_path_None_cong[OF Gt_inv'p Gt_fg'p Gt_fv'p Gt_inv'c Gt_fg'c Gt_fv'c vsinvSb' vsinvTb' Sbcarr' Tbcarr' Gt_verts'p digeq])
  have R'psubC: "vset (reach_set Sb' Gtp') \<subseteq> carrier" using reach_set_carrier[OF Gt_inv'p vsinvSb' Sbcarr' Gt_verts'p] .
  have wsolS: "X = wsol (reweight R e st)" using df(1) by (simp add: reweight_def)
  have c1S: "c_shift R (- e) c1 = wc1 (reweight R e st)" using df(2) by (simp add: reweight_def)
  have c2S: "c_shift R e c2 = wc2 (reweight R e st)" using df(3) by (simp add: reweight_def)
  have linkSt: "wRverts_circuit st = vset R" "wPathNone_circuit st = (find_path SbarX TbarX Gtight = None)"
    using wRP_state_circuit[OF df(1,2,3,4,5,6,7,8)] by auto
  have linkSucc: "wRverts_circuit (reweight R e st) = vset (reach_set Sb' Gtc')"
      "wPathNone_circuit (reweight R e st) = (find_path Sb' Tb' Gtc' = None)"
    using wRP_state_circuit[OF wsolS c1S c2S df(4) Sb'_def Tb'_def Gtc'_def refl] by auto
  have PnStTrue: "wPathNone_circuit st" using linkSt(2) df(9) by simp
  have subR': "vset R \<subseteq> vset (reach_set Sb' Gtc')" using rmono' reachcong by simp
  have cardRR': "card (vset R) \<le> card (vset (reach_set Sb' Gtc'))" using card_mono[OF finite_subset[OF R'psubC[unfolded reachcong] finC] subR'] .
  have cardR'N: "card (vset (reach_set Sb' Gtc')) \<le> card carrier" using card_mono[OF finC R'psubC[unfolded reachcong]] .
  have disj: "card (vset R) < card (vset (reach_set Sb' Gtc')) \<or> \<not> wPathNone_circuit (reweight R e st)"
    using sop' reachcong pathcong linkSucc(2) psubset_card_mono[OF finite_subset[OF R'psubC[unfolded reachcong] finC]] by auto
  have m1eq: "card (to_set (wsol (reweight R e st))) = card (to_set (wsol st))" by (simp add: reweight_def)
  have e1: "wmeasure_circuit (reweight R e st) = (card carrier - card (to_set (wsol st))) * (2 * card carrier + 2) + 2 * (card carrier - card (vset (reach_set Sb' Gtc'))) + (if wPathNone_circuit (reweight R e st) then 1 else 0)"
    by (simp add: wmeasure_circuit_def m1eq linkSucc(1))
  have e2: "wmeasure_circuit st = (card carrier - card (to_set (wsol st))) * (2 * card carrier + 2) + 2 * (card carrier - card (vset R)) + 1"
    by (simp add: wmeasure_circuit_def linkSt(1) PnStTrue)
  show "wmeasure_circuit (reweight R e st) < wmeasure_circuit st"
    using measure_dec_helper[OF cardRR' cardR'N disj] e1 e2 by linarith
qed

lemma wmeasure_augment_dec_circuit:
  assumes "w_invar st" "weighted_augment_cond_circuit st"
  shows "wmeasure_circuit (weighted_augment_upd_circuit st) < wmeasure_circuit st"
proof -
  have finC: "finite carrier" by (rule matroid1.carrier_finite)
  have card_aug: "card (to_set (wsol (weighted_augment_upd_circuit st))) = card (to_set (wsol st)) + 1"
    by (rule weighted_augment_card_circuit[OF assms])
  have "w_invar (weighted_augment_upd_circuit st)" by (rule w_invar_augment_circuit[OF assms])
  hence "indep1 (to_set (wsol (weighted_augment_upd_circuit st)))" by (simp add: w_invar_def)
  hence sub: "to_set (wsol (weighted_augment_upd_circuit st)) \<subseteq> carrier" by (rule matroid1.indep_subset_carrier)
  have cle: "card (to_set (wsol st)) + 1 \<le> card carrier" using card_mono[OF finC sub] card_aug by simp
  have a: "2 * (card carrier - card (wRverts_circuit (weighted_augment_upd_circuit st))) \<le> 2 * card carrier" by (metis diff_le_self mult_le_mono2)
  have b: "(if wPathNone_circuit (weighted_augment_upd_circuit st) then 1 else 0) \<le> (1::nat)" by simp
  have bnd: "2 * (card carrier - card (wRverts_circuit (weighted_augment_upd_circuit st))) + (if wPathNone_circuit (weighted_augment_upd_circuit st) then 1 else 0) \<le> 2 * card carrier + 1"
    by (rule add_mono[OF a b])
  have wm_aug: "wmeasure_circuit (weighted_augment_upd_circuit st) = (card carrier - (card (to_set (wsol st)) + 1)) * (2 * card carrier + 2) + (2 * (card carrier - card (wRverts_circuit (weighted_augment_upd_circuit st))) + (if wPathNone_circuit (weighted_augment_upd_circuit st) then 1 else 0))"
    by (simp add: wmeasure_circuit_def card_aug)
  have wm_st: "wmeasure_circuit st = (card carrier - card (to_set (wsol st))) * (2 * card carrier + 2) + (2 * (card carrier - card (wRverts_circuit st)) + (if wPathNone_circuit st then 1 else 0))"
    by (simp add: wmeasure_circuit_def)
  show ?thesis
    using measure_aug_helper[OF cle refl bnd, where Rp = "2 * (card carrier - card (wRverts_circuit st)) + (if wPathNone_circuit st then 1 else 0)"] wm_aug wm_st
    by linarith
qed

lemma weighted_matroid_intersection_circuit_terminates:
  assumes "w_invar st" "m = wmeasure_circuit st"
  shows "weighted_matroid_intersection_circuit_dom st"
  using assms
proof (induction m arbitrary: st rule: less_induct)
  case (less m st)
  show ?case
  proof (rule weighted_matroid_intersection_circuit.domintros)
    fix a aa b xd ab ba x2
    assume "(a, aa, b) = compute_graph_circuit (wsol st) (complement (wsol st))"
      and g2: "(xd, ab, ba) = compute_graph_circuit (wsol st) (complement (wsol st))"
      and g3: "find_path (restrict_to_max xd (wc1 st)) (restrict_to_max ab (wc2 st)) (compute_tight_graph_circuit (wsol st) (wc1 st) (wc2 st) (complement (wsol st))) = None"
      and g4: "compute_eps_circuit (wsol st) (weight_Max xd (wc1 st)) (weight_Max ab (wc2 st)) (reach_set (restrict_to_max xd (wc1 st)) (compute_tight_graph_circuit (wsol st) (wc1 st) (wc2 st) (complement (wsol st)))) (wc1 st) (wc2 st) = Some x2"
    have rwcond: "weighted_reweight_cond_circuit st" using g2[symmetric] g3 g4 by (simp add: weighted_reweight_cond_circuit_def Let_def)
    have upd_eq: "reweight (reach_set (restrict_to_max xd (wc1 st)) (compute_tight_graph_circuit (wsol st) (wc1 st) (wc2 st) (complement (wsol st)))) x2 st = weighted_reweight_upd_circuit st"
      using g2[symmetric] g3 g4 by (simp add: weighted_reweight_upd_circuit_def Let_def)
    show "weighted_matroid_intersection_circuit_dom (reweight (reach_set (restrict_to_max xd (wc1 st)) (compute_tight_graph_circuit (wsol st) (wc1 st) (wc2 st) (complement (wsol st)))) x2 st)"
      unfolding upd_eq
      by (rule less.IH[OF _ w_invar_reweight_circuit[OF less.prems(1) rwcond] refl])
         (use wmeasure_reweight_dec_circuit[OF less.prems(1) rwcond] less.prems(2) in simp)
  next
    fix a aa b xd ab ba x2
    assume "(a, aa, b) = compute_graph_circuit (wsol st) (complement (wsol st))"
      and h2: "(xd, ab, ba) = compute_graph_circuit (wsol st) (complement (wsol st))"
      and h3: "find_path (restrict_to_max xd (wc1 st)) (restrict_to_max ab (wc2 st)) (compute_tight_graph_circuit (wsol st) (wc1 st) (wc2 st) (complement (wsol st))) = Some x2"
    have augcond: "weighted_augment_cond_circuit st" using h2[symmetric] h3 by (simp add: weighted_augment_cond_circuit_def Let_def)
    have upd_eq2: "st\<lparr>wsol := augment (wsol st) x2, wbest := keep_better st (augment (wsol st) x2)\<rparr> = weighted_augment_upd_circuit st"
      using h2[symmetric] h3 by (simp add: weighted_augment_upd_circuit_def Let_def)
    show "weighted_matroid_intersection_circuit_dom (st\<lparr>wsol := augment (wsol st) x2, wbest := keep_better st (augment (wsol st) x2)\<rparr>)"
      unfolding upd_eq2
      by (rule less.IH[OF _ w_invar_augment_circuit[OF less.prems(1) augcond] refl])
         (use wmeasure_augment_dec_circuit[OF less.prems(1) augcond] less.prems(2) in simp)
  qed
qed

text \<open>Total correctness of the circuit-oracle weighted algorithm.\<close>
theorem weighted_matroid_intersection_circuit_correct:
  assumes "c_invar c"
  defines "s \<equiv> weighted_matroid_intersection_circuit (weighted_initial_state c)"
  shows "weighted_double_matroid.is_opt indep1 indep2 (c_lookup c) (to_set (wbest s))"
proof -
  have dom: "weighted_matroid_intersection_circuit_dom (weighted_initial_state c)"
    by (rule weighted_matroid_intersection_circuit_terminates[OF w_invar_initial[OF assms(1)] refl])
  show ?thesis unfolding s_def by (rule weighted_matroid_intersection_circuit_partial_correct[OF assms(1) dom])
qed

end

end
