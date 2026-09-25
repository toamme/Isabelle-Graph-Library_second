section \<open>The DIMACS Minimum Cost Flow Problem\<close>

text \<open>This theory is the place where the minimum cost flow problem as posed by the
      \emph{DIMACS Challenge: Network Flows 2.0} specification (see \<open>mincost_dimacs.pdf\<close>) is to be
      related to the min cost flow problem of the library.

      \paragraph{The instance.} An instance is a directed graph \<open>G = (V, A)\<close>, given in an ASCII
      file whose lines carry a single-character designator:
      \begin{itemize}
      \item \<open>c \<dots>\<close> --- a comment line, ignored;
      \item \<open>p min <n> <m>\<close> --- the problem line, fixing the number \<open>n\<close> of nodes and the number
            \<open>m\<close> of arcs; nodes are identified by the integers \<open>1 \<dots> n\<close>;
      \item \<open>n <v> <supply>\<close> --- a node line, present only for nodes of non-zero supply;
            the supply is the balance \<open>b v\<close> below, and a negative supply is called a demand;
      \item \<open>a <v> <w> <l> <u> <c>\<close> --- an arc line: an arc from \<open>v\<close> to \<open>w\<close> with lower bound
            \<open>l\<close>, upper bound \<open>u\<close> and per-unit cost \<open>c\<close>. Parallel arcs are allowed and may not be
            merged, since they can carry different costs.
      \end{itemize}
      All numbers occurring in an instance are integers.

      \paragraph{The problem.} Writing \<open>f\<close> for the flow, the specification asks to minimise
      \<open>\<Sum>\<^bsub>a \<in> A\<^esub> c(a) f(a)\<close> subject to
      \begin{align}        l(a) \<le> f(a) &\<le> u(a) & \<forall> a &\<in> A \\
        \textstyle\<Sum>_{x : (w,x) \<in> A} f(w,x) - \textstyle\<Sum>_{v : (v,w) \<in> A} f(v,w) &= b(w)
           & \forall w &\<in> V
      \end{align}

      \paragraph{Output.} A solution consists of a solution line \<open>s <F>\<close> carrying the cost of the
      flow found, together with one flow line \<open>f <v> <w> <x>\<close> per arc. If there is no feasible
      solution, this is reported on a comment line instead and neither solution nor flow lines
      appear.\<close>

theory Mincost_Solver_Reduction
  imports Flow_Theory.Cost_Optimality Data_Structures.Real_Embedding
begin


subsection \<open>Validity and optimality\<close>

text \<open>An instance adds two data to a cost flow network: the lower bounds \<open>l\<close> of the arc
      lines and the supplies \<^term>\<open>b\<close> of the node lines. Both are fixed by the following locale,
      which is otherwise the assumption-free \<^locale>\<open>cost_flow_spec\<close>: no finiteness, no
      non-emptiness and in particular no sign condition is needed to say what a valid flow is.

      Two deliberate generalisations over the DIMACS document:

      \begin{itemize}
      \item \emph{No assumption on the ranges.} The lower bound \<^term>\<open>l\<close> has the same type
            \<^typ>\<open>'edge \<Rightarrow> ereal\<close> as the capacity \<^term>\<open>\<u>\<close>, so the admissible interval
            \<^term>\<open>{l e..\<u> e}\<close> of an edge may be any interval of reals, including ones that are
            unbounded on either side. We require neither \<^term>\<open>0 \<le> l e\<close> nor \<^term>\<open>0 \<le> \<u> e\<close> nor
            \<^term>\<open>l e \<le> \<u> e\<close>; in particular an edge may be forced to carry negative flow, and an
            edge with an empty interval simply makes the instance infeasible. Note that this
            departs from \<open>isuflow\<close>, which builds \<open>0 \<le> f e\<close> into validity.
      \item \emph{The node set is an argument.} \<^term>\<open>\<V>\<close> is \<^term>\<open>dVs (make_pair ` \<E>)\<close> and hence
            cannot contain a vertex without incident edges, whereas a DIMACS instance may well
            declare an isolated node, even one of non-zero supply. The balance constraints are
            therefore quantified over a node set \<^term>\<open>V\<close> given as an argument, intended to be the
            set \<open>{1..n}\<close> of the problem line, which may properly contain \<^term>\<open>\<V>\<close>. It stays an
            argument rather than a further fixed parameter so that the two restriction lemmas
            below can compare different node sets.
      \end{itemize}\<close>

locale dimacs_spec = cost_flow_spec where \<E> = "\<E>::'edge set" for \<E> +
  fixes l::"'edge \<Rightarrow> ereal"
    and b::"'a \<Rightarrow> real"
begin

text \<open>Validity: constraint (1) on every edge and constraint (2) at every node of \<^term>\<open>V\<close>. Recall
      \<^term>\<open>ex\<^bsub>f\<^esub> v\<close> is the excess, i.e. inflow minus outflow, so \<^term>\<open>- (ex\<^bsub>f\<^esub> v)\<close> is the net
      outflow, which the balance fixes \<^emph>\<open>exactly\<close>: the supply of a node is neither a cap on what it
      may emit nor a floor on what it may absorb but the amount it does emit.

      This is the library's own balance clause --- \<open>isbflow\<close> of \<open>Residual\<close> reads
      \<^term>\<open>- (ex\<^bsub>f\<^esub> v) = b v\<close> at every vertex --- so the two formulations differ only in the
      capacity constraint (1), whose lower bound the library does not have. That is the whole
      content of the reduction below.\<close>

definition is_dimacs_flow :: "'a set \<Rightarrow> ('edge \<Rightarrow> real) \<Rightarrow> bool" where
"is_dimacs_flow V f \<longleftrightarrow>
   ((\<forall> e \<in> \<E>. l e \<le> ereal (f e) \<and> ereal (f e) \<le> \<u> e) \<and>
    (\<forall> v \<in> V. b v = - (ex\<^bsub>f\<^esub> v)))"

lemma is_dimacs_flowI:
  "\<lbrakk>\<And> e. e \<in> \<E> \<Longrightarrow> l e \<le> ereal (f e); \<And> e. e \<in> \<E> \<Longrightarrow> ereal (f e) \<le> \<u> e;
    \<And> v. v \<in> V \<Longrightarrow> b v = - (ex\<^bsub>f\<^esub> v)\<rbrakk>
   \<Longrightarrow> is_dimacs_flow V f"
and is_dimacs_flowE:
  "is_dimacs_flow V f \<Longrightarrow>
     (\<lbrakk>\<And> e. e \<in> \<E> \<Longrightarrow> l e \<le> ereal (f e); \<And> e. e \<in> \<E> \<Longrightarrow> ereal (f e) \<le> \<u> e;
       \<And> v. v \<in> V \<Longrightarrow> b v = - (ex\<^bsub>f\<^esub> v)\<rbrakk> \<Longrightarrow> P)
     \<Longrightarrow> P"
  by(auto simp add: is_dimacs_flow_def)

text \<open>Optimality: a valid flow of least cost, where the objective \<^term>\<open>\<C> f\<close> of the library is
      literally the DIMACS objective \<open>\<Sum>\<^bsub>a \<in> A\<^esub> c(a) f(a)\<close>.\<close>

definition is_dimacs_Opt :: "'a set \<Rightarrow> ('edge \<Rightarrow> real) \<Rightarrow> bool" where
"is_dimacs_Opt V f \<longleftrightarrow>
   (is_dimacs_flow V f \<and> (\<forall> f'. is_dimacs_flow V f' \<longrightarrow> \<C> f \<le> \<C> f'))"

lemma is_dimacs_OptI:
  "\<lbrakk>is_dimacs_flow V f; \<And> f'. is_dimacs_flow V f' \<Longrightarrow> \<C> f \<le> \<C> f'\<rbrakk> \<Longrightarrow> is_dimacs_Opt V f"
and is_dimacs_OptE:
  "is_dimacs_Opt V f \<Longrightarrow>
     (\<lbrakk>is_dimacs_flow V f; \<And> f'. is_dimacs_flow V f' \<Longrightarrow> \<C> f \<le> \<C> f'\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by(auto simp add: is_dimacs_Opt_def)

subsection \<open>Isolated nodes are harmless\<close>

text \<open>A node outside of \<^term>\<open>\<V>\<close> has no incident edge, hence zero excess.\<close>

lemma delta_plus_outside_V: "v \<notin> \<V> \<Longrightarrow> \<delta>\<^sup>+ v = {}"
and delta_minus_outside_V: "v \<notin> \<V> \<Longrightarrow> \<delta>\<^sup>- v = {}"
  by(auto simp add: delta_plus_def delta_minus_def make_pair_def dVs_def)

lemma ex_outside_V: "v \<notin> \<V> \<Longrightarrow> (ex\<^bsub>f\<^esub> v) = 0"
  by(simp add: ex_def delta_plus_outside_V delta_minus_outside_V)

text \<open>Consequently an isolated node constrains nothing \<^emph>\<open>provided its supply is zero\<close> --- and that
      proviso is now a genuine condition rather than a triviality. With the balance met exactly, an
      isolated node of non-zero supply makes the instance \<^emph>\<open>infeasible\<close>: its excess is \<open>0\<close> whatever
      the flow does, so no assignment can meet a non-zero balance there. Under the one-sided reading
      the same node constrained nothing at all, each of the two inequalities being assumed by the
      very side condition that activated it.

      So the extra nodes that the DIMACS format permits but the library cannot represent may still
      be discarded, but only against that check, and validity and optimality only ever depend on
      \<^term>\<open>V \<inter> \<V>\<close> once it has passed. The reduction below performs it --- see \<open>bal_ok\<close>, where an
      isolated node has zero incident capacity and its balance is therefore forced to \<open>0\<close>.\<close>

lemma no_dimacs_flow_if_isolated_supply:
  assumes "v \<in> V" "v \<notin> \<V>" "b v \<noteq> 0"
  shows "\<not> is_dimacs_flow V f"
  using assms by(auto elim!: is_dimacs_flowE simp add: ex_outside_V)

lemma is_dimacs_flow_restrict_V:
  assumes iso: "\<And> v. \<lbrakk>v \<in> V; v \<notin> \<V>\<rbrakk> \<Longrightarrow> b v = 0"
  shows "is_dimacs_flow V f = is_dimacs_flow (V \<inter> \<V>) f"
proof
  assume "is_dimacs_flow V f"
  thus "is_dimacs_flow (V \<inter> \<V>) f"
    by(auto elim!: is_dimacs_flowE intro!: is_dimacs_flowI)
next
  assume asm: "is_dimacs_flow (V \<inter> \<V>) f"
  show "is_dimacs_flow V f"
  proof(rule is_dimacs_flowI)
    fix e assume "e \<in> \<E>"
    thus "l e \<le> ereal (f e)"
      using asm by(auto elim!: is_dimacs_flowE)
  next
    fix e assume "e \<in> \<E>"
    thus "ereal (f e) \<le> \<u> e"
      using asm by(auto elim!: is_dimacs_flowE)
  next
    fix v assume v: "v \<in> V"
    show "b v = - (ex\<^bsub>f\<^esub> v)"
    proof(cases "v \<in> \<V>")
      case True
      thus ?thesis using v asm by(auto elim!: is_dimacs_flowE)
    next
      case False
      show ?thesis using iso[OF v False] ex_outside_V[OF False] by simp
    qed
  qed
qed

text \<open>Beware that \<open>is_dimacs_flow_restrict_V\<close> must not be used as a rewrite rule, nor with
      \<open>intro\<close>: its right hand side is again an instance of its left hand side, so the simplifier
      would keep producing \<^term>\<open>V \<inter> \<V> \<inter> \<V>\<close>, and \<open>intro\<close> would keep re-applying the rule to
      its own subgoal. Below it is therefore only ever applied once, via \<open>rule\<close>.\<close>

lemma is_dimacs_Opt_restrict_V:
  assumes iso: "\<And> v. \<lbrakk>v \<in> V; v \<notin> \<V>\<rbrakk> \<Longrightarrow> b v = 0"
  shows "is_dimacs_Opt V f = is_dimacs_Opt (V \<inter> \<V>) f"
  using is_dimacs_flow_restrict_V[OF iso] by(simp add: is_dimacs_Opt_def)

end

subsection \<open>Instances with finite data\<close>

text \<open>The locale above is more permissive than a DIMACS instance in two respects that matter.

      First, \<^term>\<open>\<E>\<close> may be infinite, and a \<^const>\<open>sum\<close> over an infinite set is \<open>0\<close> in
      Isabelle/HOL, so \<^term>\<open>\<C> f\<close> would collapse to \<open>0\<close> for every \<^term>\<open>f\<close> and every valid flow
      would count as optimal. A real instance names its number of arcs on the problem line, so
      \<^term>\<open>finite \<E>\<close> is available.

      Second, the bounds were generalised to \<^typ>\<open>ereal\<close>, whereas a DIMACS instance gives integers
      in \<open>[-2\<^sup>3\<^sup>1, 2\<^sup>3\<^sup>1 - 1]\<close>. Infinite bounds are what allows an instance to admit valid flows of
      unbounded cost, so that no optimum exists and neither of the two output cases of the format
      applies. Ruling them out restores the dichotomy between an optimal solution and
      infeasibility.

      Since \<open>l\<close> is fixed by \<^locale>\<open>dimacs_spec\<close>, the finiteness assumption covers both bounds
      of the admissible interval.\<close>

locale dimacs_network = dimacs_spec where \<E> = "\<E>::'edge set" for \<E> +
  assumes finite_E: "finite \<E>"
      and u_finite: "\<And> e. e \<in> \<E> \<Longrightarrow> \<bar>\<u> e\<bar> \<noteq> \<infinity>"
      and l_finite: "\<And> e. e \<in> \<E> \<Longrightarrow> \<bar>l e\<bar> \<noteq> \<infinity>"

subsection \<open>The instance as lists\<close>

text \<open>The parsed form of an instance, in the style of \<open>initial_basis_code_spec\<close> of the theory
      \<open>Network_Simplex_Initial_Basis_Code\<close> (named rather than referenced, as that theory is not
      imported here): the arc lines become five parallel lists indexed by the arc number, and the
      node lines become one list indexed by the node number.

      \<^term>\<open>fst_list\<close> and \<^term>\<open>snd_list\<close> hold the tail and head of each arc as a natural number,
      \<^term>\<open>lower\<close> and \<^term>\<open>upper\<close> its two capacity bounds and \<^term>\<open>cost_list\<close> its per-unit
      cost, the last three entries \<open>l\<close>, \<open>u\<close>, \<open>c\<close> of an arc line. Those five are parallel, so a
      well-formed instance gives them the common length \<^term>\<open>m\<close>, whereas \<^term>\<open>balance_list\<close> is
      indexed by nodes and has length \<^term>\<open>n\<close> instead.

      The two counts \<^term>\<open>m\<close> and \<^term>\<open>n\<close> of the problem line are fixed alongside the data rather
      than recovered as \<^term>\<open>length fst_list\<close> and \<^term>\<open>length balance_list\<close>, as
      \<open>initial_basis_code_spec\<close> also does with its \<open>m\<close>. That they \emph{are} those lengths is still
      not assumed: the locale only fixes the data, and well-formedness is to be required where it is
      actually needed. Everything below is therefore driven by \<^term>\<open>m\<close> and \<^term>\<open>n\<close>, never by a
      list's length, so the sizes it produces are the ones the problem line announces.

      The numeric type \<^typ>\<open>'n\<close> is a \<^class>\<open>linordered_idom\<close> rather than \<^typ>\<open>real\<close>, as in the
      executable network simplex, so that an instance can be read at \<^typ>\<open>int\<close> --- which is what
      the DIMACS format actually provides --- and mapped into the reals only where the proofs need
      it.\<close>

locale dimacs_lists =
  fixes fst_list     :: "nat list"
    and snd_list     :: "nat list"
    and lower        :: "('n::linordered_idom) list"
    and upper        :: "'n list"
    and cost_list    :: "'n list"
    and balance_list :: "'n list"
    and m            :: nat
    and n            :: nat
begin

text \<open>Vertices are the \emph{positions} of \<^term>\<open>balance_list\<close>, i.e. \<open>{0..<n}\<close>, and arcs the
      positions of \<^term>\<open>fst_list\<close>. A DIMACS instance names its nodes \<open>1 \<dots> n\<close>, so it is read with a
      \<^term>\<open>balance_list\<close> of length \<open>n+1\<close> whose slot \<open>0\<close> is a dummy of balance \<open>0\<close>, exactly as
      \<open>b_arr\<close> of \<open>Network_Simplex_Initial_Basis_Code\<close> does.\<close>

subsection \<open>Reduction to the standard format\<close>

text \<open>The target is the shape the library's \<open>isbflow\<close> and \<open>is_Opt\<close> take: capacities only (no lower
      bounds), non-negative flow, the balance met \emph{exactly} at every vertex, and a vertex set
      that is \<open>dVs\<close> of the arcs, so no vertex may be lonely. Since the DIMACS balance is now met
      exactly as well, only \emph{one} thing has to go: the lower bounds.

      \paragraph{Lower bounds: the substitution \<open>g e = f e - l e\<close>.} This is \<open>isbflow_lb_iff\<close> of
      \<open>Capacity_Balance_Reductions\<close>: capacities shrink to \<open>u e - l e\<close> and balances shift by the
      excess of \<open>l\<close>, i.e. \<open>b v + ex\<^bsub>l\<^esub> v\<close>. Undoing it is one pass adding \<open>l e\<close> back, so the
      answer is read off the reduced flow with no bookkeeping beyond that.

      \paragraph{Lonely vertices.} No vertex receives an arc it did not already have, so a vertex
      carrying no original arc stays \emph{isolated} in the reduced network and is therefore not in
      \<open>\<V>\<close>, which is \<open>dVs\<close> of the arcs. That is why the balance conditions are quantified over the
      node set given as an \emph{argument} rather than over \<open>\<V>\<close>. Such a vertex constrains nothing
      in the reduced instance, so its DIMACS constraint has to be discharged elsewhere: it has no
      incident capacity at all, hence \<open>bal_ok\<close> forces its balance to \<open>0\<close> --- which is exactly the
      condition \<open>is_dimacs_flow_restrict_V\<close> needs, and the reason the range test below is not
      merely a bit-budget device but part of the reduction's correctness.

      Cost changes by the constant \<open>\<Sum> e < m. c e * l e\<close> under the substitution, so an optimum is
      preserved and \<^term>\<open>cost_shift\<close> below is what has to be added back to the objective value
      reported for the reduced instance.\<close>

text \<open>Vertex \<open>0\<close> is not a DIMACS node --- the format reserves \<open>1 \<dots> n\<close> --- so \<open>balance_list\<close>
      carries one cell more than there are nodes and its slot \<open>0\<close> is ignored.\<close>

text \<open>The reduced instance has exactly the original arcs: there is no slack block and no dummy, so
      the arc count is \<open>m\<close>, the write index is the read index, and the pass is a straight map over
      \<open>[0..<m]\<close>, position by position. The endpoints and the costs are passed through unchanged, so
      only two arrays are rewritten: the capacities and the balances.

      One fused pass builds both, each input position read once: a step shrinks the range of its
      arc, scatters its lower bound onto its two endpoints and accumulates the cost shift. The head
      is updated first and read back by the tail update, so a self-loop cancels.

      An arc with \<open>upper ! e < lower ! e\<close> has an empty range and makes the instance infeasible.
      Rather than assume this away, the pass \<^emph>\<open>detects\<close> it: such an arc gets capacity \<open>0\<close> and the
      flag \<open>red_ok_arcs\<close> is cleared. So the capacity written is non-negative unconditionally, and
      the reduced instance agrees with the original exactly when \<open>red_ok_arcs\<close> holds. When it fails
      the original is infeasible outright.\<close>

definition red_step ::
  "nat \<Rightarrow> 'n list \<times> 'n list \<times> 'n \<times> bool \<Rightarrow> 'n list \<times> 'n list \<times> 'n \<times> bool" where
  "red_step = (\<lambda> i (us, bal, sh, ok).
     let x = fst_list ! i; y = snd_list ! i;
         li = lower ! i; ui = upper ! i; ci = cost_list ! i;
         a = bal[y := bal ! y + li]
     in (us[i := (if li \<le> ui then ui - li else 0)], a[x := a ! x - li], sh + ci * li,
         ok \<and> li \<le> ui))"

text \<open>Every capacity the pass emits is non-negative: the shrunk range \<open>u - l\<close> of an arc that has
      one and \<open>0\<close> for an arc of empty range. Nothing is uncapacitated any more --- that was the
      slack arcs' privilege --- which is what makes the solver's unboundedness verdict unreachable,
      see \<open>reduced_no_neg_infty_cycle\<close>.\<close>

definition red_upper_at :: "nat \<Rightarrow> 'n" where
  "red_upper_at i = (if lower ! i \<le> upper ! i then upper ! i - lower ! i else 0)"

text \<open>The balance array the pass starts from: the parsed balances, with the reserved slot \<open>0\<close> forced
      to \<open>0\<close>. The arc steps then scatter the lower bounds onto it, so the emitted balance of a
      vertex is \<open>b v + ex\<^bsub>l\<^esub> v\<close> in one array and one pass.\<close>

definition red_bal_init :: "'n list" where
  "red_bal_init = balance_list[0 := 0]"

definition red_init :: "'n list \<times> 'n list \<times> 'n \<times> bool" where
  "red_init = (replicate m 0, red_bal_init, 0, True)"

definition red_pass :: "'n list \<times> 'n list \<times> 'n \<times> bool" where
  "red_pass = fold red_step [0..<m] red_init"

definition red_upper :: "'n list" where
  "red_upper = (let (us, _, _, _) = red_pass in us)"

definition red_balance_raw :: "'n list" where
  "red_balance_raw = (let (_, bal, _, _) = red_pass in bal)"

definition cost_shift :: "'n" where
  "cost_shift = (let (_, _, sh, _) = red_pass in sh)"

definition red_ok_arcs :: bool where
  "red_ok_arcs = (let (_, _, _, ok) = red_pass in ok)"

text \<open>Reading the answer back. The reduced flow \<^term>\<open>gs\<close> is indexed by the original arcs in the
      original order, so undoing the substitution \<open>g = f - l\<close> is one pass adding the lower bound
      back at each position.

      The objective moves by the constant the substitution removed, so the cost of \<^term>\<open>gs\<close> in the
      reduced instance plus \<^term>\<open>cost_shift\<close> is the DIMACS solution value \<open>s <F>\<close>. The flow lines
      \<open>f <v> <w> <x>\<close> are then \<^term>\<open>fst_list ! e\<close>, \<^term>\<open>snd_list ! e\<close> and \<^term>\<open>orig_flow gs ! e\<close>.\<close>

definition orig_flow :: "'n list \<Rightarrow> 'n list" where
  "orig_flow gs = map (\<lambda> e. gs ! e + lower ! e) [0..<m]"

text \<open>The DIMACS solution value \<open>s <F>\<close>, taken on the recovered flow, so that \<^term>\<open>cost_shift\<close> is
      not needed to report it --- it stays for relating the two objectives in the proofs.\<close>

definition orig_cost :: "'n list \<Rightarrow> 'n" where
  "orig_cost fs = fold (\<lambda> e s. s + cost_list ! e * fs ! e) [0..<m] 0"

text \<open>The two arrays the pass writes, position by position. Projections keep the statements
      first-order, so the step lemmas chain through the fold as plain rewrites: a step leaves every
      index but its own alone, writes the intended value at its own, and never changes a length.\<close>

definition rp_us where "rp_us st = fst st"
definition rp_bal where "rp_bal st = fst (snd st)"

lemma rp_projs [simp]:
  "rp_us (us, bal, sh, ok) = us"
  "rp_bal (us, bal, sh, ok) = bal"
  by(simp_all add: rp_us_def rp_bal_def)

lemma red_step_arc_length [simp]:
  "length (rp_us (red_step i st)) = length (rp_us st)"
  "length (rp_bal (red_step i st)) = length (rp_bal st)"
  by(simp_all add: red_step_def Let_def rp_us_def rp_bal_def split: prod.splits)

lemma red_fold_length [simp]:
  "length (rp_us (fold red_step es st)) = length (rp_us st)"
  "length (rp_bal (fold red_step es st)) = length (rp_bal st)"
  by(induction es arbitrary: st) simp_all

text \<open>A step writes the capacity array at its own index, and at the value that index is meant to
      carry: read position and write position coincide, so no cursor has to be tracked through the
      fold.\<close>

lemma red_step_arc_upd:
  "rp_us (red_step i (us, bal, sh, ok)) = us[i := red_upper_at i]"
  by(simp add: red_step_def Let_def red_upper_at_def)

lemma red_step_arc_nth:
  assumes "i < length us"
  shows "rp_us (red_step i (us, bal, sh, ok)) ! j = (if j = i then red_upper_at j else us ! j)"
  using assms by(simp add: red_step_arc_upd nth_list_update)

text \<open>A step leaves every other position alone, whether or not its own is inside the array.\<close>

lemma red_step_arc_other:
  assumes "i \<noteq> j"
  shows "rp_us (red_step i st) ! j = rp_us st ! j"
proof -
  obtain us bal sh ok where st: "st = (us, bal, sh, ok)" by(cases st) auto
  show ?thesis
    using assms by(auto simp: st red_step_arc_upd nth_list_update_neq)
qed

lemma red_fold_arc_notin:
  "(\<And>i. i \<in> set es \<Longrightarrow> i \<noteq> j) \<Longrightarrow> rp_us (fold red_step es st) ! j = rp_us st ! j"
proof(induction es arbitrary: st)
  case (Cons a es)
  have a: "a \<noteq> j" using Cons.prems by simp
  show ?case
    using Cons.IH[of "red_step a st"] Cons.prems red_step_arc_other[OF a, of st] by simp
qed simp

text \<open>Hence every reduced arc gets its intended capacity: the step for its own index writes it, and
      distinctness of the index list keeps any later step from overwriting it.\<close>

lemma red_fold_arc_in:
  "\<lbrakk>distinct es; j \<in> set es; length (rp_us st) = m; j < m\<rbrakk>
   \<Longrightarrow> rp_us (fold red_step es st) ! j = red_upper_at j"
proof(induction es arbitrary: st)
  case (Cons a es)
  obtain us bal sh ok where st: "st = (us, bal, sh, ok)" by(cases st) auto
  have len: "length us = m" using Cons.prems by(simp add: st)
  have step_len: "length (rp_us (red_step a st)) = m" using len by(simp add: st)
  show ?case
  proof(cases "a = j")
    case True
    have hit: "rp_us (red_step a st) ! j = red_upper_at j"
      using red_step_arc_nth[of a us bal sh ok j] len True Cons.prems(4) by(simp add: st)
    have rest: "\<And>i. i \<in> set es \<Longrightarrow> i \<noteq> j" using Cons.prems(1) True by auto
    show ?thesis
      using hit red_fold_arc_notin[of es j "red_step a st"] rest by simp
  next
    case False
    hence j: "j \<in> set es" using Cons.prems(2) by simp
    show ?thesis
      using Cons.IH[of "red_step a st"] Cons.prems(1,4) j step_len by simp
  qed
qed simp

lemma red_upper_length: "length red_upper = m"
proof -
  obtain us bal sh ok where f: "fold red_step [0..<m] red_init = (us, bal, sh, ok)"
    by(cases "fold red_step [0..<m] red_init") auto
  have "length (rp_us (fold red_step [0..<m] red_init)) = length (rp_us red_init)"
    by simp
  moreover have "length (rp_us red_init) = m"
    by(simp add: red_init_def)
  ultimately show ?thesis
    by(simp add: red_upper_def red_pass_def f)
qed

text \<open>The characterisation itself: every position of the capacity array reads back the shrunk range
      of its arc.\<close>

lemma red_arc_nth:
  assumes "i < m"
  shows "red_upper ! i = red_upper_at i"
proof -
  obtain us bal sh ok where f: "fold red_step [0..<m] red_init = (us, bal, sh, ok)"
    by(cases "fold red_step [0..<m] red_init") auto
  have lists: "red_upper = us"
    by(simp add: red_upper_def red_pass_def f)
  have "rp_us (fold red_step [0..<m] red_init) ! i = red_upper_at i"
    using red_fold_arc_in[where es = "[0..<m]" and j = i and st = red_init] assms
    by(simp add: red_init_def)
  thus ?thesis
    by(simp add: lists f)
qed

text \<open>The balance array is not written once per index but accumulated by every step, so its
      characterisation is a sum over the arcs processed so far rather than a per-index read. An arc
      adds its lower bound at its head and subtracts it at its tail --- the head first, so a
      self-loop cancels.\<close>

definition bal_step_at :: "nat \<Rightarrow> nat \<Rightarrow> 'n" where
  "bal_step_at i v = (if snd_list ! i = v then lower ! i else 0)
                     - (if fst_list ! i = v then lower ! i else 0)"

lemma red_step_bal_nth:
  assumes "v < length bal" "fst_list ! i < length bal" "snd_list ! i < length bal"
  shows "rp_bal (red_step i (us, bal, sh, ok)) ! v = bal ! v + bal_step_at i v"
  using assms
  by(auto simp add: red_step_def Let_def bal_step_at_def nth_list_update)

lemma red_fold_bal_nth:
  "\<lbrakk>v < length (rp_bal st);
    \<And> i. i \<in> set es \<Longrightarrow> fst_list ! i < length (rp_bal st);
    \<And> i. i \<in> set es \<Longrightarrow> snd_list ! i < length (rp_bal st)\<rbrakk>
   \<Longrightarrow> rp_bal (fold red_step es st) ! v
         = rp_bal st ! v + sum_list (map (\<lambda> i. bal_step_at i v) es)"
proof(induction es arbitrary: st)
  case (Cons a es)
  obtain us bal sh ok where st: "st = (us, bal, sh, ok)" by(cases st) auto
  have step: "rp_bal (red_step a st) ! v = bal ! v + bal_step_at a v"
    using red_step_bal_nth[of v bal a us sh ok] Cons.prems by(simp add: st)
  have "rp_bal (fold red_step es (red_step a st)) ! v
          = rp_bal (red_step a st) ! v + sum_list (map (\<lambda> i. bal_step_at i v) es)"
    using Cons.prems Cons.IH[of "red_step a st"] by(simp add: st)
  thus ?case
    using step by(simp add: st)
qed simp

lemma red_bal_init_length: "length (rp_bal red_init) = length balance_list"
  by(simp add: red_init_def red_bal_init_def)

lemma red_balance_raw_length_raw: "length red_balance_raw = length balance_list"
proof -
  obtain us bal sh ok where f: "fold red_step [0..<m] red_init = (us, bal, sh, ok)"
    by(cases "fold red_step [0..<m] red_init") auto
  have "length (rp_bal (fold red_step [0..<m] red_init)) = length (rp_bal red_init)"
    by simp
  thus ?thesis
    using red_bal_init_length by(simp add: red_balance_raw_def red_pass_def f)
qed

lemma red_step_ok:
  "(case red_step i (us, bal, sh, ok) of (_, _, _, ok') \<Rightarrow> ok') = (ok \<and> lower ! i \<le> upper ! i)"
  by(auto simp add: red_step_def Let_def)

lemma red_ok_fold:
  "(case fold red_step es (us, bal, sh, ok) of (_, _, _, ok') \<Rightarrow> ok')
   = (ok \<and> (\<forall> i \<in> set es. lower ! i \<le> upper ! i))"
proof(induction es arbitrary: us bal sh ok)
  case (Cons a es)
  obtain us' bal' sh' ok' where
    step: "red_step a (us, bal, sh, ok) = (us', bal', sh', ok')"
    by(cases "red_step a (us, bal, sh, ok)") auto
  have ok': "ok' = (ok \<and> lower ! a \<le> upper ! a)"
    using red_step_ok[of a us bal sh ok] by(simp add: step)
  show ?case
    by(auto simp add: step ok' Cons.IH)
qed simp

lemma red_ok_arcs_iff: "red_ok_arcs = (\<forall> e < m. lower ! e \<le> upper ! e)"
proof -
  obtain us bal sh ok where f: "fold red_step [0..<m] red_init = (us, bal, sh, ok)"
    by(cases "fold red_step [0..<m] red_init") auto
  have one: "red_ok_arcs = ok"
    by(simp add: red_ok_arcs_def red_pass_def f)
  have two: "ok = (\<forall> i \<in> set [0..<m]. lower ! i \<le> upper ! i)"
    using red_ok_fold[of "[0..<m]" "replicate m 0" red_bal_init 0 True] f
    by(simp add: red_init_def)
  show ?thesis
    using one two by auto
qed
end

subsection \<open>The two networks\<close>

text \<open>The lists only become a flow problem once their entries are read as reals, which is what the
      embedding \<^term>\<open>h\<close> of \<^locale>\<open>real_embedding\<close> does: the executable data live in \<^typ>\<open>'n\<close> ---
      \<^typ>\<open>int\<close> for a DIMACS file --- and the specification lives in \<^typ>\<open>real\<close>.

      The assumptions are the shape of a parsed instance and nothing else: the arc lists have the
      length the problem line announces, every endpoint names a node, and \<^term>\<open>balance_list\<close> has at
      least its reserved slot \<open>0\<close>. No bound is restricted; in particular \<^term>\<open>upper ! e < lower ! e\<close>
      stays legal input and is reported through \<^term>\<open>red_ok_arcs\<close>.

      \<^term>\<open>0 < m\<close> is what the standard format demands and the reduction can no longer supply: the
      arcs are passed through unchanged, so an instance without arcs would reduce to one without
      arcs, which is no \<^locale>\<open>multigraph\<close>. An arc-less instance is feasible exactly when every
      balance is \<open>0\<close>, at cost \<open>0\<close>, and is settled by inspection before the reduction is reached;
      see \<open>DIMACS_Solver\<close>.\<close>

locale dimacs_lists_network =
  dimacs_lists where lower = "lower :: ('n::linordered_idom) list" +
  real_embedding where h = "h :: 'n \<Rightarrow> real"
  for lower h +
  assumes length_fst_list:     "length fst_list = m"
      and length_snd_list:     "length snd_list = m"
      and length_lower:        "length lower = m"
      and length_upper:        "length upper = m"
      and length_cost_list:    "length cost_list = m"
      and length_balance_list: "length balance_list = n"
      and arcs_nonempty:       "0 < m"
      and nodes_nonempty:      "0 < n"
      and fst_list_vertex:     "\<And> e. e < m \<Longrightarrow> fst_list ! e \<in> {1..<n}"
      and snd_list_vertex:     "\<And> e. e < m \<Longrightarrow> snd_list ! e \<in> {1..<n}"
begin

lemma h_nonneg: "0 \<le> x \<Longrightarrow> 0 \<le> h x"
  by (metis h_le_iff h_zero)

text \<open>The capacity of a reduced arc. Every entry the pass emits is non-negative, so an arc in range
      is read as the image under \<open>h\<close> of its entry; edges outside \<open>{0..<m}\<close> are given \<open>\<infinity>\<close>, since
      \<open>u_non_neg\<close> ranges over the whole edge type.\<close>

definition red_u :: "nat \<Rightarrow> ereal" where
  "red_u e = (if e < m \<and> 0 \<le> red_upper ! e then ereal (h (red_upper ! e)) else \<infinity>)"

lemma red_u_nonneg: "0 \<le> red_u e"
  by(auto simp add: red_u_def h_nonneg zero_ereal_def)

lemma red_u_finite: "\<lbrakk>e < m; 0 \<le> red_upper ! e\<rbrakk> \<Longrightarrow> red_u e = ereal (h (red_upper ! e))"
and red_u_infty: "\<not> (e < m \<and> 0 \<le> red_upper ! e) \<Longrightarrow> red_u e = \<infinity>"
  by(auto simp add: red_u_def)

text \<open>The balance array of a real node. Only here do the endpoint assumptions enter: they are what
      places every scatter inside the array, so nothing written by an arc is lost off the end.\<close>

lemma red_balance_raw_length: "length red_balance_raw = n"
  using red_balance_raw_length_raw length_balance_list by simp

lemma red_bal_init_nth:
  "v \<in> {1..<n} \<Longrightarrow> red_bal_init ! v = balance_list ! v"
  and red_bal_init_sentinel: "red_bal_init ! 0 = 0"
  using nodes_nonempty length_balance_list
  by(auto simp add: red_bal_init_def)

lemma red_balance_raw_nth:
  assumes "v < n"
  shows "red_balance_raw ! v
           = red_bal_init ! v + sum_list (map (\<lambda> i. bal_step_at i v) [0..<m])"
proof -
  obtain us bal sh ok where
    f: "fold red_step [0..<m] red_init = (us, bal, sh, ok)"
    by(cases "fold red_step [0..<m] red_init") auto
  have b1: "fst_list ! i < n" if "i < m" for i
    using fst_list_vertex[of i] that by auto
  have b2: "snd_list ! i < n" if "i < m" for i
    using snd_list_vertex[of i] that by auto
  have len: "length (rp_bal red_init) = n"
    using red_bal_init_length length_balance_list by simp
  have "rp_bal (fold red_step [0..<m] red_init) ! v
          = rp_bal red_init ! v + sum_list (map (\<lambda> i. bal_step_at i v) [0..<m])"
  proof(rule red_fold_bal_nth)
    show "v < length (rp_bal red_init)" using assms len by simp
  next
    fix i assume "i \<in> set [0..<m]"
    thus "fst_list ! i < length (rp_bal red_init)" using b1 len by simp
  next
    fix i assume "i \<in> set [0..<m]"
    thus "snd_list ! i < length (rp_bal red_init)" using b2 len by simp
  qed
  moreover have "rp_bal red_init = red_bal_init"
    by(simp add: red_init_def)
  ultimately have "bal ! v = red_bal_init ! v + sum_list (map (\<lambda> i. bal_step_at i v) [0..<m])"
    by(simp add: f)
  thus ?thesis
    by(simp add: red_balance_raw_def red_pass_def f)
qed

text \<open>No arc touches the sentinel slot \<open>0\<close>, so it keeps the \<open>0\<close> the pass starts from.\<close>

lemma bal_step_at_sentinel: "i < m \<Longrightarrow> bal_step_at i 0 = 0"
  using fst_list_vertex[of i] snd_list_vertex[of i] by(auto simp add: bal_step_at_def)

lemma red_balance_raw_sentinel: "red_balance_raw ! 0 = 0"
proof -
  have r: "sum_list (replicate k (0::'n)) = 0" for k
    by(induction k) simp_all
  have "map (\<lambda> i. bal_step_at i 0) [0..<m] = replicate m 0"
    by(rule nth_equalityI) (auto simp add: bal_step_at_sentinel)
  hence z: "sum_list (map (\<lambda> i. bal_step_at i 0) [0..<m]) = 0" by(simp add: r)
  show ?thesis
    using red_balance_raw_nth[of 0] nodes_nonempty red_bal_init_sentinel z by simp
qed

text \<open>The DIMACS instance keeps the \emph{spec} locale: its bounds carry no sign condition, so it is
      no \<^locale>\<open>flow_network\<close>, which is exactly what \<^locale>\<open>dimacs_spec\<close> was built to avoid.\<close>

sublocale original_network: dimacs_spec
  where \<E>           = "{0..<m}"
    and fst          = "\<lambda> e. if e < m then fst_list ! e
                             else Product_Type.fst (prod_decode (e - m))"
    and snd          = "\<lambda> e. if e < m then snd_list ! e
                             else Product_Type.snd (prod_decode (e - m))"
    and create_edge  = "\<lambda> u v. m + prod_encode (u, v)"
    and \<u>           = "\<lambda> e. ereal (h (upper ! e))"
    and \<c>           = "\<lambda> e. h (cost_list ! e)"
    and l            = "\<lambda> e. ereal (h (lower ! e))"
    and b            = "\<lambda> v. h (balance_list ! v)"
  by unfold_locales

text \<open>The transformed instance gets the \emph{proof} locale: its capacities \<^term>\<open>red_u\<close> are
      non-negative for every edge and its edge set is non-empty by \<^term>\<open>0 < m\<close>, so all of
      \<^locale>\<open>cost_flow_network\<close> is available. Its arcs are the original ones, endpoints and costs
      included; only the capacities differ, and there are no lower bounds left.\<close>

sublocale reduced_network: cost_flow_network
  where \<E>           = "{0..<m}"
    and fst          = "\<lambda> e. if e < m then fst_list ! e
                             else Product_Type.fst (prod_decode (e - m))"
    and snd          = "\<lambda> e. if e < m then snd_list ! e
                             else Product_Type.snd (prod_decode (e - m))"
    and create_edge  = "\<lambda> u v. m + prod_encode (u, v)"
    and \<u>           = red_u
    and \<c>           = "\<lambda> e. h (cost_list ! e)"
  by(unfold_locales) (auto simp add: arcs_nonempty red_u_nonneg)

subsection \<open>Capacity incident at a vertex\<close>

text \<open>The reduced capacity leaving and entering a vertex. Both are read off \<open>red_upper\<close>, whose entry
      at an arc is \<open>u - l\<close>, or \<open>0\<close> on an arc of empty range --- which also clears \<open>red_ok_arcs\<close>.\<close>

definition capout :: "nat \<Rightarrow> 'n" where
  "capout v = sum_list (map (\<lambda> e. if fst_list ! e = v then red_upper ! e else 0) [0..<m])"

definition capin :: "nat \<Rightarrow> 'n" where
  "capin v = sum_list (map (\<lambda> e. if snd_list ! e = v then red_upper ! e else 0) [0..<m])"

lemma red_upper_orig_nonneg: "e < m \<Longrightarrow> 0 \<le> red_upper ! e"
  using red_arc_nth[of e] by (simp add: red_upper_at_def)

text \<open>Read through the embedding, each is the sum over the arcs leaving (entering) the vertex. This
      is the only place the \<open>sum_list\<close> / \<open>sum\<close> and \<open>h\<close>-distribution bookkeeping happens.\<close>

lemma capout_sum: "h (capout v) = (\<Sum> e \<in> {e. e < m \<and> fst_list ! e = v}. h (red_upper ! e))"
proof -
  have "h (capout v) = (\<Sum> e \<in> {0..<m}. h (if fst_list ! e = v then red_upper ! e else 0))"
    by(simp add: capout_def h_sum interv_sum_list_conv_sum_set_nat)
  also have "\<dots> = (\<Sum> e \<in> {0..<m}. if fst_list ! e = v then h (red_upper ! e) else 0)"
    by(rule sum.cong) auto
  also have "\<dots> = (\<Sum> e \<in> {0..<m} \<inter> {e. fst_list ! e = v}. h (red_upper ! e))"
    by(subst sum.inter_restrict) auto
  also have "\<dots> = (\<Sum> e \<in> {e. e < m \<and> fst_list ! e = v}. h (red_upper ! e))"
    by(rule sum.cong) auto
  finally show ?thesis .
qed

lemma capin_sum: "h (capin v) = (\<Sum> e \<in> {e. e < m \<and> snd_list ! e = v}. h (red_upper ! e))"
proof -
  have "h (capin v) = (\<Sum> e \<in> {0..<m}. h (if snd_list ! e = v then red_upper ! e else 0))"
    by(simp add: capin_def h_sum interv_sum_list_conv_sum_set_nat)
  also have "\<dots> = (\<Sum> e \<in> {0..<m}. if snd_list ! e = v then h (red_upper ! e) else 0)"
    by(rule sum.cong) auto
  also have "\<dots> = (\<Sum> e \<in> {0..<m} \<inter> {e. snd_list ! e = v}. h (red_upper ! e))"
    by(subst sum.inter_restrict) auto
  also have "\<dots> = (\<Sum> e \<in> {e. e < m \<and> snd_list ! e = v}. h (red_upper ! e))"
    by(rule sum.cong) auto
  finally show ?thesis .
qed

subsection \<open>The net out-flow of a vertex on the original arcs\<close>

text \<open>The quantity the balance constraint fixes.\<close>

definition net_out :: "(nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real" where
  "net_out g v = (\<Sum> e \<in> {e. e < m \<and> fst_list ! e = v}. g e)
               - (\<Sum> e \<in> {e. e < m \<and> snd_list ! e = v}. g e)"

subsection \<open>The bound: capacity alone confines the net out-flow\<close>

text \<open>This is the entire mathematical content of the change. Everything below is a one-line
      consequence of it.\<close>

lemma net_out_bounds:
  assumes lo: "\<And> e. e < m \<Longrightarrow> 0 \<le> g e"
      and hi: "\<And> e. e < m \<Longrightarrow> g e \<le> h (red_upper ! e)"
  shows "net_out g v \<le> h (capout v)"
    and "- h (capin v) \<le> net_out g v"
proof -
  have o1: "(\<Sum> e \<in> {e. e < m \<and> fst_list ! e = v}. g e) \<le> h (capout v)"
    unfolding capout_sum by(rule sum_mono) (auto simp add: hi)
  have o2: "0 \<le> (\<Sum> e \<in> {e. e < m \<and> fst_list ! e = v}. g e)"
    by(rule sum_nonneg) (auto simp add: lo)
  have i1: "(\<Sum> e \<in> {e. e < m \<and> snd_list ! e = v}. g e) \<le> h (capin v)"
    unfolding capin_sum by(rule sum_mono) (auto simp add: hi)
  have i2: "0 \<le> (\<Sum> e \<in> {e. e < m \<and> snd_list ! e = v}. g e)"
    by(rule sum_nonneg) (auto simp add: lo)
  from o1 i2 show "net_out g v \<le> h (capout v)" by(simp add: net_out_def)
  from o2 i1 show "- h (capin v) \<le> net_out g v" by(simp add: net_out_def)
qed

subsection \<open>The balance a vertex can meet\<close>

text \<open>With the net out-flow pinned to the balance, neither bound may move: all that is available is
      the range test --- and it is a genuine test, a required net out-flow outside the incident
      capacity being unachievable.\<close>

lemma net_out_confined:
  assumes "\<And> e. e < m \<Longrightarrow> 0 \<le> g e" "\<And> e. e < m \<Longrightarrow> g e \<le> h (red_upper ! e)"
      and "net_out g v = bnd"
  shows "- h (capin v) \<le> bnd" "bnd \<le> h (capout v)"
  using net_out_bounds(1)[OF assms(1,2), of v] net_out_bounds(2)[OF assms(1,2), of v] assms(3)
  by auto

subsection \<open>Total capacity\<close>

text \<open>The identity that makes the exercise worthwhile: every arc contributes its capacity to the
      out-capacity of exactly one vertex --- its tail --- so the out-capacities sum to the total
      capacity of the instance, and likewise the in-capacities via the heads.\<close>

definition total_cap :: "'n" where
  "total_cap = sum_list (map (\<lambda> e. red_upper ! e) [0..<m])"

lemma sum_cap_aux:
  assumes "\<And> e. e < m \<Longrightarrow> idx ! e \<in> {1..<n}"
  shows "(\<Sum> v \<in> {1..<n}. \<Sum> e \<in> {0..<m}. if idx ! e = v then red_upper ! e else 0) = total_cap"
proof -
  have "(\<Sum> v \<in> {1..<n}. \<Sum> e \<in> {0..<m}. if idx ! e = v then red_upper ! e else 0)
          = (\<Sum> e \<in> {0..<m}. \<Sum> v \<in> {1..<n}. if idx ! e = v then red_upper ! e else 0)"
    by(rule sum.swap)
  also have "\<dots> = (\<Sum> e \<in> {0..<m}. red_upper ! e)"
  proof(rule sum.cong[OF refl])
    fix e assume "e \<in> {0..<m}"
    hence "idx ! e \<in> {1..<n}" using assms by simp
    thus "(\<Sum> v \<in> {1..<n}. if idx ! e = v then red_upper ! e else 0) = red_upper ! e"
      by(simp add: sum.delta')
  qed
  also have "\<dots> = total_cap"
    by(simp add: total_cap_def interv_sum_list_conv_sum_set_nat)
  finally show ?thesis .
qed

lemma sum_capout: "(\<Sum> v \<in> {1..<n}. capout v) = total_cap"
  and sum_capin: "(\<Sum> v \<in> {1..<n}. capin v) = total_cap"
  using sum_cap_aux[of fst_list] sum_cap_aux[of snd_list] fst_list_vertex snd_list_vertex
  by(simp_all add: capout_def capin_def interv_sum_list_conv_sum_set_nat)

lemma capout_nonneg: "0 \<le> capout v" and capin_nonneg: "0 \<le> capin v"
  by(auto simp add: capout_def capin_def red_upper_orig_nonneg
          intro!: sum_list_nonneg split: if_splits)



subsection \<open>The balance array the reduction emits\<close>

text \<open>What the pass wrote is what is emitted: slot \<open>0\<close> carries \<open>0\<close>, a real vertex its shifted
      balance. The flag adds two tests to the arc check: the range test at each vertex, and that the
      emitted balances total \<open>0\<close>, which the equality semantics no longer arranges by construction.\<close>

definition red_balance_list :: "'n list" where
  "red_balance_list = red_balance_raw"

definition bal_ok :: bool where
  "bal_ok = (\<forall> v \<in> {1..<n}. - capin v \<le> red_balance_raw ! v \<and> red_balance_raw ! v \<le> capout v)"

definition sum_ok :: bool where
  "sum_ok = (sum_list red_balance_raw = 0)"

definition red_ok :: bool where
  "red_ok = (red_ok_arcs \<and> bal_ok \<and> sum_ok)"

lemma red_ok_arcsD: "red_ok \<Longrightarrow> red_ok_arcs"
  by(simp add: red_ok_def)

lemma bal_okD: "red_ok \<Longrightarrow> bal_ok"
  by(simp add: red_ok_def)

lemma sum_okD: "red_ok \<Longrightarrow> sum_ok"
  by(simp add: red_ok_def)

lemma red_balance_list_length: "length red_balance_list = n"
  by(simp add: red_balance_list_def red_balance_raw_length)

lemma red_balance_list_nth: "v < n \<Longrightarrow> red_balance_list ! v = red_balance_raw ! v"
  by(simp add: red_balance_list_def)

lemma total_cap_nonneg: "0 \<le> total_cap"
  by(auto simp add: total_cap_def red_upper_orig_nonneg intro!: sum_list_nonneg)

text \<open>\<^bold>\<open>What the test delivers.\<close> Every entry of the emitted balance array lies within the total
      capacity of the instance, which is the statement the marshalling guard needs.\<close>

theorem red_balance_list_bounded:
  assumes ok: "red_ok" and v: "v < n"
  shows "- total_cap \<le> red_balance_list ! v \<and> red_balance_list ! v \<le> total_cap"
proof -
  have bok: "bal_ok" using ok by(simp add: red_ok_def)
  consider (z) "v = 0" | (r) "v \<in> {1..<n}"
    using v by fastforce
  thus ?thesis
  proof cases
    case z
    thus ?thesis
      using total_cap_nonneg v by(simp add: red_balance_list_nth red_balance_raw_sentinel)
  next
    case r
    have lo: "- capin v \<le> red_balance_raw ! v" and up: "red_balance_raw ! v \<le> capout v"
      using bok r by(auto simp add: bal_ok_def)
    have mo: "capout v \<le> (\<Sum> w \<in> {1..<n}. capout w)"
      by(rule member_le_sum[OF r _ finite_atLeastLessThan]) (simp add: capout_nonneg)
    have mi: "capin v \<le> (\<Sum> w \<in> {1..<n}. capin w)"
      by(rule member_le_sum[OF r _ finite_atLeastLessThan]) (simp add: capin_nonneg)
    have co: "capout v \<le> total_cap" by(metis mo sum_capout)
    have ci: "- total_cap \<le> - capin v" using mi sum_capin by(metis neg_le_iff_le)
    have "red_balance_raw ! v \<le> total_cap" using up co by(rule order_trans)
    moreover have "- total_cap \<le> red_balance_raw ! v" using ci lo by(rule order_trans)
    ultimately show ?thesis using v by(simp add: red_balance_list_nth)
  qed
qed
definition red_b :: "nat \<Rightarrow> real" where
  "red_b v = h (red_balance_list ! v)"

subsection \<open>Incidence in the reduced network\<close>

text \<open>Both networks have the same arcs, so they share the whole graph layer --- incidence, vertices
      and endpoints are those of the original instance, and \<open>orig_delta\<close> below serves for both.\<close>

subsection \<open>The immediate infeasibility check\<close>

text \<open>(1) When the flag is down, some arc has an empty range, and no assignment can lie in it. The
      node set \<open>V\<close> plays no part: the obstruction is the capacity constraint alone.\<close>

lemma no_dimacs_flow_if_not_red_ok_arcs:
  assumes "\<not> red_ok_arcs"
  shows "\<not> original_network.is_dimacs_flow V f"
proof
  assume flow: "original_network.is_dimacs_flow V f"
  obtain e where e: "e < m" "\<not> lower ! e \<le> upper ! e"
    using assms by(auto simp add: red_ok_arcs_iff)
  have le: "h (lower ! e) \<le> f e" "f e \<le> h (upper ! e)"
    using flow e by(auto elim!: original_network.is_dimacs_flowE)
  have "h (lower ! e) \<le> h (upper ! e)"
    using le by(rule order_trans)
  thus False using e by simp
qed

lemma no_dimacs_Opt_if_not_red_ok_arcs:
  "\<not> red_ok_arcs \<Longrightarrow> \<not> original_network.is_dimacs_Opt V f"
  using no_dimacs_flow_if_not_red_ok_arcs by(auto elim!: original_network.is_dimacs_OptE)

subsection \<open>The emitted balance of a vertex\<close>

lemma bal_arc_part:
  "sum_list (map (\<lambda> i. bal_step_at i v) [0..<m])
     = (\<Sum> e \<in> {e. e < m \<and> snd_list ! e = v}. lower ! e)
       - (\<Sum> e \<in> {e. e < m \<and> fst_list ! e = v}. lower ! e)"
proof -
  have "sum_list (map (\<lambda> i. bal_step_at i v) [0..<m]) = (\<Sum> i \<in> {0..<m}. bal_step_at i v)"
    by(simp add: interv_sum_list_conv_sum_set_nat)
  also have "\<dots> = (\<Sum> i \<in> {0..<m}. (if snd_list ! i = v then lower ! i else 0))
                  - (\<Sum> i \<in> {0..<m}. (if fst_list ! i = v then lower ! i else 0))"
    by(simp add: bal_step_at_def sum_subtractf)
  also have "(\<Sum> i \<in> {0..<m}. (if snd_list ! i = v then lower ! i else 0))
               = (\<Sum> e \<in> {e. e < m \<and> snd_list ! e = v}. lower ! e)"
    by(subst sum.inter_filter[symmetric]) (auto intro: sum.cong)
  also have "(\<Sum> i \<in> {0..<m}. (if fst_list ! i = v then lower ! i else 0))
               = (\<Sum> e \<in> {e. e < m \<and> fst_list ! e = v}. lower ! e)"
    by(subst sum.inter_filter[symmetric]) (auto intro: sum.cong)
  finally show ?thesis .
qed

lemma red_balance_raw_value:
  assumes "v \<in> {1..<n}"
  shows "red_balance_raw ! v
           = balance_list ! v
             + (\<Sum> e \<in> {e. e < m \<and> snd_list ! e = v}. lower ! e)
             - (\<Sum> e \<in> {e. e < m \<and> fst_list ! e = v}. lower ! e)"
proof -
  have "red_balance_raw ! v = red_bal_init ! v + sum_list (map (\<lambda> i. bal_step_at i v) [0..<m])"
    using assms by(intro red_balance_raw_nth) auto
  thus ?thesis
    using assms by(simp add: bal_arc_part red_bal_init_nth)
qed
subsection \<open>From a DIMACS flow to a reduced b-flow\<close>

text \<open>The forward map subtracts the lower bound on an arc.\<close>

lemma orig_delta:
  "original_network.delta_plus v = {e. e < m \<and> fst_list ! e = v}"
  "original_network.delta_minus v = {e. e < m \<and> snd_list ! e = v}"
  by(auto simp add: multigraph_spec.delta_plus_def multigraph_spec.delta_minus_def)

text \<open>Every original arc has both endpoints among the real nodes, so summing an arc quantity over
      the heads, or over the tails, of all nodes counts each arc exactly once.\<close>

lemma sum_over_snd:
  "(\<Sum> v \<in> {1..<n}. \<Sum> e \<in> {e. e < m \<and> snd_list ! e = v}. g e) = (\<Sum> e \<in> {0..<m}. g e)"
proof -
  have "(\<Sum> v \<in> {1..<n}. \<Sum> e \<in> {e. e < m \<and> snd_list ! e = v}. g e)
          = sum g (\<Union> v \<in> {1..<n}. {e. e < m \<and> snd_list ! e = v})"
    by(subst sum.UNION_disjoint) auto
  moreover have "(\<Union> v \<in> {1..<n}. {e. e < m \<and> snd_list ! e = v}) = {0..<m}"
    using snd_list_vertex by auto
  ultimately show ?thesis by simp
qed

lemma sum_over_fst:
  "(\<Sum> v \<in> {1..<n}. \<Sum> e \<in> {e. e < m \<and> fst_list ! e = v}. g e) = (\<Sum> e \<in> {0..<m}. g e)"
proof -
  have "(\<Sum> v \<in> {1..<n}. \<Sum> e \<in> {e. e < m \<and> fst_list ! e = v}. g e)
          = sum g (\<Union> v \<in> {1..<n}. {e. e < m \<and> fst_list ! e = v})"
    by(subst sum.UNION_disjoint) auto
  moreover have "(\<Union> v \<in> {1..<n}. {e. e < m \<and> fst_list ! e = v}) = {0..<m}"
    using fst_list_vertex by auto
  ultimately show ?thesis by simp
qed

text \<open>Hence the excesses of the DIMACS instance sum to zero over the real nodes --- what a flow
      leaves at one node it enters at another.\<close>

lemma orig_ex_sum_zero: "(\<Sum> v \<in> {1..<n}. original_network.ex f v) = 0"
proof -
  have "(\<Sum> v \<in> {1..<n}. original_network.ex f v)
          = (\<Sum> v \<in> {1..<n}. \<Sum> e \<in> {e. e < m \<and> snd_list ! e = v}. f e)
            - (\<Sum> v \<in> {1..<n}. \<Sum> e \<in> {e. e < m \<and> fst_list ! e = v}. f e)"
    by(simp add: flow_network_spec.ex_def orig_delta sum_subtractf)  also have "\<dots> = 0"
    using sum_over_snd[of f] sum_over_fst[of f] by simp
  finally show ?thesis .
qed

text \<open>The emitted balances total the parsed ones: what an arc adds at its head it subtracts at its
      tail, so the scattered lower bounds cancel.\<close>

lemma red_balance_raw_sum_inner:
  "sum_list red_balance_raw = (\<Sum> v \<in> {1..<n}. red_balance_raw ! v)"
proof -
  have nn: "0 < n" by(rule nodes_nonempty)
  have s: "{0..<n} = insert 0 {1..<n}" using nn by auto
  have a: "(0::nat) \<notin> {1..<n}" by auto
  have "sum_list red_balance_raw = (\<Sum> i \<in> {0..<n}. red_balance_raw ! i)"
    by(simp add: sum_list_sum_nth red_balance_raw_length atLeast0LessThan)
  also have "\<dots> = red_balance_raw ! 0 + (\<Sum> v \<in> {1..<n}. red_balance_raw ! v)"
    unfolding s by(subst sum.insert[OF _ a]) auto
  finally show ?thesis
    using red_balance_raw_sentinel by simp
qed

lemma red_balance_raw_sum: "sum_list red_balance_raw = (\<Sum> v \<in> {1..<n}. balance_list ! v)"
proof -
  have inner: "(\<Sum> v \<in> {1..<n}. red_balance_raw ! v) = (\<Sum> v \<in> {1..<n}. balance_list ! v)"
  proof -
    have "(\<Sum> v \<in> {1..<n}. red_balance_raw ! v)
            = (\<Sum> v \<in> {1..<n}. balance_list ! v
                 + (\<Sum> e \<in> {e. e < m \<and> snd_list ! e = v}. lower ! e)
                 - (\<Sum> e \<in> {e. e < m \<and> fst_list ! e = v}. lower ! e))"
      by(rule sum.cong) (simp_all add: red_balance_raw_value)
    also have "\<dots> = (\<Sum> v \<in> {1..<n}. balance_list ! v)
                    + (\<Sum> v \<in> {1..<n}. \<Sum> e \<in> {e. e < m \<and> snd_list ! e = v}. lower ! e)
                    - (\<Sum> v \<in> {1..<n}. \<Sum> e \<in> {e. e < m \<and> fst_list ! e = v}. lower ! e)"
      by(simp add: sum.distrib sum_subtractf)
    finally show ?thesis
      using sum_over_snd[of "\<lambda> e. lower ! e"] sum_over_fst[of "\<lambda> e. lower ! e"] by simp
  qed
  show ?thesis using red_balance_raw_sum_inner inner by simp
qed
text \<open>\<^term>\<open>n = 0\<close> forces \<^term>\<open>m = 0\<close>, since an arc would need an endpoint in the empty set
      \<^term>\<open>{1..<n}\<close>.\<close>

lemma m_pos_n: "0 < m \<Longrightarrow> 1 < n"
  using fst_list_vertex[of 0] by auto

text \<open>Only the real nodes occur in the reduced instance.\<close>

lemma red_V_subset: "original_network.\<V> \<subseteq> {1..<n}"
proof
  fix x assume "x \<in> original_network.\<V>"
  then obtain e where e: "e < m" "x = fst_list ! e \<or> x = snd_list ! e"
    by(auto simp add: dVs_def multigraph_spec.make_pair_def)
  thus "x \<in> {1..<n}"
    using fst_list_vertex[of e] snd_list_vertex[of e] by auto
qed

text \<open>The embedding is additive, so it commutes with a finite sum.\<close>

lemma h_sum: "finite S \<Longrightarrow> h (\<Sum> e \<in> S. g e) = (\<Sum> e \<in> S. h (g e))"
  by(induction S rule: finite_induct) (auto simp add: h_add)

lemma red_b_raw:
  assumes "v \<in> {1..<n}"
  shows "h (red_balance_raw ! v) = h (balance_list ! v)
                   + (\<Sum> e \<in> {e. e < m \<and> snd_list ! e = v}. h (lower ! e))
                   - (\<Sum> e \<in> {e. e < m \<and> fst_list ! e = v}. h (lower ! e))"
  using red_balance_raw_value[OF assms] by(simp add: h_sum h_add)

lemma red_b_real:
  assumes "v \<in> {1..<n}"
  shows "red_b v = h (red_balance_raw ! v)"
  using assms by(simp add: red_b_def red_balance_list_nth)

text \<open>The forward map: subtract the lower bound on an arc.\<close>

definition red_of :: "(nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real" where
  "red_of f e = (if e < m then f e - h (lower ! e) else 0)"

lemma red_of_orig: "e < m \<Longrightarrow> red_of f e = f e - h (lower ! e)"
  by(simp add: red_of_def)

lemma red_of_balance:
  assumes flow: "original_network.is_dimacs_flow {1..<n} f"
      and v: "v \<in> {1..<n}"
  shows "- reduced_network.ex (red_of f) v = red_b v"
proof -
  have dp: "original_network.delta_plus v = {e. e < m \<and> fst_list ! e = v}"
    by(rule orig_delta(1))
  have dm: "original_network.delta_minus v = {e. e < m \<and> snd_list ! e = v}"
    by(rule orig_delta(2))
  have sum_out: "(\<Sum> e \<in> {e. e < m \<and> fst_list ! e = v}. red_of f e)
                   = (\<Sum> e \<in> {e. e < m \<and> fst_list ! e = v}. f e)
                     - (\<Sum> e \<in> {e. e < m \<and> fst_list ! e = v}. h (lower ! e))"
    by(simp add: red_of_orig sum_subtractf)
  have sum_in: "(\<Sum> e \<in> {e. e < m \<and> snd_list ! e = v}. red_of f e)
                   = (\<Sum> e \<in> {e. e < m \<and> snd_list ! e = v}. f e)
                     - (\<Sum> e \<in> {e. e < m \<and> snd_list ! e = v}. h (lower ! e))"
    by(simp add: red_of_orig sum_subtractf)
  have exf: "original_network.ex f v
               = (\<Sum> e \<in> {e. e < m \<and> snd_list ! e = v}. f e)
                 - (\<Sum> e \<in> {e. e < m \<and> fst_list ! e = v}. f e)"
    by(simp add: flow_network_spec.ex_def orig_delta)
  have bal: "h (balance_list ! v) = - original_network.ex f v"
    using flow v by(auto elim!: original_network.is_dimacs_flowE)
  have "- reduced_network.ex (red_of f) v
          = (\<Sum> e \<in> {e. e < m \<and> fst_list ! e = v}. red_of f e)
            - (\<Sum> e \<in> {e. e < m \<and> snd_list ! e = v}. red_of f e)"
    by(simp add: flow_network_spec.ex_def dp dm)
  also have "\<dots> = red_b v"
    using red_b_real[OF v] red_b_raw[OF v] exf sum_out sum_in bal by simp
  finally show ?thesis .
qed

text \<open>The capacities: an arc carries the shrunk range of its bounds.\<close>

lemma red_upper_orig:
  assumes "red_ok_arcs" "e < m"
  shows "red_upper ! e = upper ! e - lower ! e"
  using red_arc_nth[of e] assms red_ok_arcs_iff by(auto simp add: red_upper_at_def)

lemma red_u_orig:
  assumes "red_ok_arcs" "e < m"
  shows "red_u e = ereal (h (upper ! e) - h (lower ! e))"
proof -
  have "0 \<le> red_upper ! e"
    using red_upper_orig[OF assms] assms red_ok_arcs_iff by simp
  thus ?thesis
    using assms by(simp add: red_u_def red_upper_orig[OF assms])
qed

text \<open>The constraints of a DIMACS flow, in the concrete reading of the list instance.\<close>

lemma dimacs_flow_bounds:
  assumes "original_network.is_dimacs_flow {1..<n} f"
  shows "e < m \<Longrightarrow> h (lower ! e) \<le> f e"
    and "e < m \<Longrightarrow> f e \<le> h (upper ! e)"
    and "v \<in> {1..<n} \<Longrightarrow> - original_network.ex f v = h (balance_list ! v)"
  using assms by(auto elim!: original_network.is_dimacs_flowE)

lemma red_of_nonneg_orig:
  assumes flow: "original_network.is_dimacs_flow {1..<n} f" and e: "e < m"
  shows "0 \<le> red_of f e"
  using dimacs_flow_bounds(1)[OF flow e] e by(simp add: red_of_orig)

lemma red_of_le_red_upper:
  assumes ok: "red_ok_arcs" and flow: "original_network.is_dimacs_flow {1..<n} f" and e: "e < m"
  shows "red_of f e \<le> h (red_upper ! e)"
  using dimacs_flow_bounds(2)[OF flow e] by(simp add: red_of_orig e red_upper_orig[OF ok e] h_diff)

text \<open>The net out-flow of the forward map is the shifted balance itself, which is what the range
      test compares against the incident capacities.\<close>

lemma net_out_red_of:
  assumes v: "v \<in> {1..<n}"
  shows "net_out (red_of f) v
           = h (red_balance_raw ! v) - (h (balance_list ! v) + original_network.ex f v)"
proof -
  have sum_out: "(\<Sum> e \<in> {e. e < m \<and> fst_list ! e = v}. red_of f e)
                   = (\<Sum> e \<in> {e. e < m \<and> fst_list ! e = v}. f e)
                     - (\<Sum> e \<in> {e. e < m \<and> fst_list ! e = v}. h (lower ! e))"
    by(simp add: red_of_orig sum_subtractf)
  have sum_in: "(\<Sum> e \<in> {e. e < m \<and> snd_list ! e = v}. red_of f e)
                   = (\<Sum> e \<in> {e. e < m \<and> snd_list ! e = v}. f e)
                     - (\<Sum> e \<in> {e. e < m \<and> snd_list ! e = v}. h (lower ! e))"
    by(simp add: red_of_orig sum_subtractf)
  have exf: "original_network.ex f v
               = (\<Sum> e \<in> {e. e < m \<and> snd_list ! e = v}. f e)
                 - (\<Sum> e \<in> {e. e < m \<and> fst_list ! e = v}. f e)"
    by(simp add: flow_network_spec.ex_def orig_delta)
  show ?thesis
    using sum_out sum_in exf red_b_raw[OF v] by(simp add: net_out_def)
qed

lemma red_of_nonneg:
  assumes flow: "original_network.is_dimacs_flow {1..<n} f" and e: "e < m"
  shows "0 \<le> red_of f e"
  by(rule red_of_nonneg_orig[OF flow e])

subsection \<open>The forward map is a reduced b-flow\<close>

lemma red_of_le_u:
  assumes ok: "red_ok_arcs" and flow: "original_network.is_dimacs_flow {1..<n} f" and e: "e < m"
  shows "ereal (red_of f e) \<le> red_u e"
  using red_u_orig[OF ok e] dimacs_flow_bounds(2)[OF flow e] e by(simp add: red_of_orig)

lemma red_of_isuflow:
  assumes ok: "red_ok_arcs" and flow: "original_network.is_dimacs_flow {1..<n} f"
  shows "reduced_network.isuflow (red_of f)"
  using red_of_le_u[OF ok flow] red_of_nonneg[OF flow]
  by(auto simp add: flow_network_spec.isuflow_def)

lemma red_of_isbflow:
  assumes ok: "red_ok_arcs" and flow: "original_network.is_dimacs_flow {1..<n} f"
  shows "reduced_network.isbflow (red_of f) red_b"
proof(rule flow_network_spec.isbflowI)
  show "reduced_network.isuflow (red_of f)" by(rule red_of_isuflow[OF ok flow])
next
  fix v assume "v \<in> original_network.\<V>"
  hence "v \<in> {1..<n}" using red_V_subset by auto
  thus "- reduced_network.ex (red_of f) v = red_b v"
    by(simp add: red_of_balance[OF flow])
qed

subsection \<open>The inverse map is a DIMACS flow\<close>

text \<open>Undoing the substitution: \<open>orig_of g e = g e + l e\<close> on the original arcs.\<close>

definition orig_of :: "(nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real" where
  "orig_of g e = g e + h (lower ! e)"

lemma orig_of_ex:
  assumes v: "v \<in> {1..<n}" and bal: "- reduced_network.ex g v = red_b v"
  shows "- original_network.ex (orig_of g) v = h (balance_list ! v)"
proof -
  have dp: "original_network.delta_plus v = {e. e < m \<and> fst_list ! e = v}"
    by(rule orig_delta(1))
  have dm: "original_network.delta_minus v = {e. e < m \<and> snd_list ! e = v}"
    by(rule orig_delta(2))
  have sum_out: "(\<Sum> e \<in> {e. e < m \<and> fst_list ! e = v}. orig_of g e)
                   = (\<Sum> e \<in> {e. e < m \<and> fst_list ! e = v}. g e)
                     + (\<Sum> e \<in> {e. e < m \<and> fst_list ! e = v}. h (lower ! e))"
    by(simp add: orig_of_def sum.distrib)
  have sum_in: "(\<Sum> e \<in> {e. e < m \<and> snd_list ! e = v}. orig_of g e)
                   = (\<Sum> e \<in> {e. e < m \<and> snd_list ! e = v}. g e)
                     + (\<Sum> e \<in> {e. e < m \<and> snd_list ! e = v}. h (lower ! e))"
    by(simp add: orig_of_def sum.distrib)
  have exo: "- original_network.ex (orig_of g) v
               = (\<Sum> e \<in> {e. e < m \<and> fst_list ! e = v}. orig_of g e)
                 - (\<Sum> e \<in> {e. e < m \<and> snd_list ! e = v}. orig_of g e)"
    by(simp add: flow_network_spec.ex_def orig_delta)
  have red: "(\<Sum> e \<in> {e. e < m \<and> fst_list ! e = v}. g e)
               - (\<Sum> e \<in> {e. e < m \<and> snd_list ! e = v}. g e) = red_b v"
    using bal by(simp add: flow_network_spec.ex_def dp dm)
  show ?thesis
    using exo sum_out sum_in red red_b_real[OF v] red_b_raw[OF v] by simp
qed

text \<open>A real node whose arcs are all absent is not a vertex of the reduced instance at all. Its
      incident capacity is \<open>0\<close>, so the range test has forced its balance to \<open>0\<close> and the b-flow
      condition holds at it for free.\<close>

lemma red_delta_empty_outside:
  assumes "v \<notin> original_network.\<V>"
  shows "original_network.delta_plus v = {}" "original_network.delta_minus v = {}"
  using assms reduced_network.fst_E_V reduced_network.snd_E_V
  by(auto simp add: multigraph_spec.delta_plus_def multigraph_spec.delta_minus_def)

lemma red_balance_outside:
  assumes ok: "bal_ok" and v: "v \<in> {1..<n}" and out: "v \<notin> original_network.\<V>"
  shows "- reduced_network.ex g v = red_b v"
proof -
  have dp: "original_network.delta_plus v = {}" and dm: "original_network.delta_minus v = {}"
    by(rule red_delta_empty_outside[OF out])+
  have o1: "\<And> e. e < m \<Longrightarrow> fst_list ! e \<noteq> v" using orig_delta(1)[of v] dp by auto
  have o2: "\<And> e. e < m \<Longrightarrow> snd_list ! e \<noteq> v" using orig_delta(2)[of v] dm by auto
  have co: "capout v = 0"
  proof -
    have "(\<Sum> i \<in> {0..<m}. (if fst_list ! i = v then red_upper ! i else 0)) = 0"
      using o1 by(intro sum.neutral) auto
    thus ?thesis by(simp add: capout_def interv_sum_list_conv_sum_set_nat)
  qed
  have ci: "capin v = 0"
  proof -
    have "(\<Sum> i \<in> {0..<m}. (if snd_list ! i = v then red_upper ! i else 0)) = 0"
      using o2 by(intro sum.neutral) auto
    thus ?thesis by(simp add: capin_def interv_sum_list_conv_sum_set_nat)
  qed
  have z: "red_balance_raw ! v = 0"
  proof -
    have "- capin v \<le> red_balance_raw ! v" and "red_balance_raw ! v \<le> capout v"
      using ok v by(auto simp add: bal_ok_def)
    thus ?thesis using co ci by linarith
  qed
  show ?thesis
    using red_b_real[OF v] z by(simp add: flow_network_spec.ex_def dp dm h_zero)
qed

lemma bflow_facts:
  assumes ok: "bal_ok" and bf: "reduced_network.isbflow g red_b"
  shows "e < m \<Longrightarrow> 0 \<le> g e"
    and "e < m \<Longrightarrow> ereal (g e) \<le> red_u e"
    and "v \<in> {1..<n} \<Longrightarrow> - reduced_network.ex g v = red_b v"
  using bf red_balance_outside[OF ok]
  by(auto elim!: flow_network_spec.isbflowE simp add: flow_network_spec.isuflow_def)

lemma orig_of_is_dimacs_flow:
  assumes ok: "red_ok" and bf: "reduced_network.isbflow g red_b"
  shows "original_network.is_dimacs_flow {1..<n} (orig_of g)"
proof(rule original_network.is_dimacs_flowI)
  have arcs: "red_ok_arcs" and bal: "bal_ok" using ok by(simp_all add: red_ok_def)
  fix e assume "e \<in> {0..<m}"
  hence e: "e < m" by simp
  show "ereal (h (lower ! e)) \<le> ereal (orig_of g e)"
    using bflow_facts(1)[OF bal bf] e by(simp add: orig_of_def)
next
  have arcs: "red_ok_arcs" and bal: "bal_ok" using ok by(simp_all add: red_ok_def)
  fix e assume "e \<in> {0..<m}"
  hence e: "e < m" by simp
  hence "ereal (g e) \<le> red_u e" by(rule bflow_facts(2)[OF bal bf])
  hence "ereal (g e) \<le> ereal (h (upper ! e) - h (lower ! e))"
    using red_u_orig[OF arcs e] by simp
  thus "ereal (orig_of g e) \<le> ereal (h (upper ! e))"
    by(simp add: orig_of_def)
next
  have bal: "bal_ok" using ok by(simp add: red_ok_def)
  fix v assume v: "v \<in> {1..<n}"
  show "h (balance_list ! v) = - original_network.ex (orig_of g) v"
    using orig_of_ex[OF v bflow_facts(3)[OF bal bf v]] by simp
qed

subsection \<open>The objective moves by a constant\<close>

text \<open>Only the original arcs cost anything, and the substitution \<open>g = f - l\<close> shifts the objective
      by the fixed amount \<^term>\<open>cost_K\<close>, so an optimum is preserved in both directions.\<close>

lemma C_orig: "original_network.\<C> f = (\<Sum> e \<in> {0..<m}. h (cost_list ! e) * f e)"
  by(simp add: cost_flow_spec.\<C>_def mult.commute)

lemma C_reduced_orig_arcs: "reduced_network.\<C> g = (\<Sum> e \<in> {0..<m}. h (cost_list ! e) * g e)"
  by(simp add: cost_flow_spec.\<C>_def mult.commute)

definition cost_K :: real where
  "cost_K = (\<Sum> e \<in> {0..<m}. h (cost_list ! e) * h (lower ! e))"

lemma C_red_of: "reduced_network.\<C> (red_of f) = original_network.\<C> f - cost_K"
proof -
  have "reduced_network.\<C> (red_of f) = (\<Sum> e \<in> {0..<m}. h (cost_list ! e) * (f e - h (lower ! e)))"
    by(subst C_reduced_orig_arcs, rule sum.cong) (auto simp add: red_of_orig)
  also have "\<dots> = (\<Sum> e \<in> {0..<m}. h (cost_list ! e) * f e)
                    - (\<Sum> e \<in> {0..<m}. h (cost_list ! e) * h (lower ! e))"
    by(simp add: right_diff_distrib sum_subtractf)
  finally show ?thesis by(simp add: C_orig cost_K_def)
qed

lemma C_orig_of: "original_network.\<C> (orig_of g) = reduced_network.\<C> g + cost_K"
proof -
  have "original_network.\<C> (orig_of g) = (\<Sum> e \<in> {0..<m}. h (cost_list ! e) * (g e + h (lower ! e)))"
    by(subst C_orig, rule sum.cong) (auto simp add: orig_of_def)
  also have "\<dots> = (\<Sum> e \<in> {0..<m}. h (cost_list ! e) * g e)
                    + (\<Sum> e \<in> {0..<m}. h (cost_list ! e) * h (lower ! e))"
    by(simp add: distrib_left sum.distrib)
  finally show ?thesis by(simp add: C_reduced_orig_arcs cost_K_def)
qed

text \<open>The recovered flow \<^term>\<open>\<lambda> e. h (orig_flow gs ! e)\<close> is exactly \<^term>\<open>orig_of\<close> of the reduced
      flow on the original arcs, and validity depends only on those.\<close>

lemma orig_flow_nth: "e < m \<Longrightarrow> h (orig_flow gs ! e) = orig_of (\<lambda> e. h (gs ! e)) e"
  by(simp add: orig_flow_def orig_of_def h_add)

lemma is_dimacs_flow_cong:
  assumes eq: "\<And>e. e < m \<Longrightarrow> f e = f' e" and flow: "original_network.is_dimacs_flow V f"
  shows "original_network.is_dimacs_flow V f'"
proof -
  have ex: "original_network.ex f' v = original_network.ex f v" for v
    using eq by(auto simp add: flow_network_spec.ex_def orig_delta intro: sum.cong)
  show ?thesis
    using flow eq ex by(auto elim!: original_network.is_dimacs_flowE
                             intro!: original_network.is_dimacs_flowI)
qed

subsection \<open>The three verdicts --- final statements\<close>

text \<open>The three theorems the pipeline needs, one per verdict the solver can return. Lemma (1) is
      \<open>no_dimacs_flow_if_not_red_ok_arcs\<close> above; theorem (2) is proved here from the two maps and the
      cost identity, and theorem (3) after \<open>reduced_no_neg_infty_cycle\<close>, on which its first
      disjunct rests.

      The reduced flow arrives as a list \<^term>\<open>gs\<close> indexed by the reduced arcs and is read as the
      real-valued flow \<^term>\<open>\<lambda> e. h (gs ! e)\<close>; the recovered DIMACS flow is
      \<^term>\<open>\<lambda> e. h (orig_flow gs ! e)\<close>, which on \<^term>\<open>{0..<m}\<close> is \<^term>\<open>\<lambda> e. h (gs ! e + lower ! e)\<close>
      --- the substitution \<open>g = f - l\<close> undone.\<close>

text \<open>(2) A solved reduced instance yields a DIMACS optimum, provided the immediate check passed.\<close>

theorem orig_flow_is_dimacs_Opt:
  assumes ok: "red_ok"
      and opt: "reduced_network.is_Opt red_b (\<lambda> e. h (gs ! e))"
  shows "original_network.is_dimacs_Opt {1..<n} (\<lambda> e. h (orig_flow gs ! e))"
proof(rule original_network.is_dimacs_OptI)
  have bf: "reduced_network.isbflow (\<lambda> e. h (gs ! e)) red_b"
    using opt by(auto elim!: cost_flow_spec.is_OptE)
  have flow: "original_network.is_dimacs_flow {1..<n} (orig_of (\<lambda> e. h (gs ! e)))"
    by(rule orig_of_is_dimacs_flow[OF ok bf])
  show "original_network.is_dimacs_flow {1..<n} (\<lambda> e. h (orig_flow gs ! e))"
    by(rule is_dimacs_flow_cong[OF _ flow]) (simp add: orig_flow_nth)
next
  fix f' assume f': "original_network.is_dimacs_flow {1..<n} f'"
  have "reduced_network.isbflow (red_of f') red_b" by(rule red_of_isbflow[OF red_ok_arcsD[OF ok] f'])
  hence "reduced_network.\<C> (\<lambda> e. h (gs ! e)) \<le> reduced_network.\<C> (red_of f')"
    using opt by(auto elim!: cost_flow_spec.is_OptE)
  hence "original_network.\<C> (orig_of (\<lambda> e. h (gs ! e))) \<le> original_network.\<C> f'"
    using C_orig_of[of "\<lambda> e. h (gs ! e)"] C_red_of[of f'] by simp
  moreover have "original_network.\<C> (\<lambda> e. h (orig_flow gs ! e))
                   = original_network.\<C> (orig_of (\<lambda> e. h (gs ! e)))"
    by(rule cost_flow_spec.flow_costs_cong) (simp add: orig_flow_nth)
  ultimately show "original_network.\<C> (\<lambda> e. h (orig_flow gs ! e)) \<le> original_network.\<C> f'"
    by simp
qed
text \<open>No reduced arc is uncapacitated any more: every arc gets the shrunk range of its bounds.\<close>

lemma red_u_finite_in_range:
  assumes "e < m"
  shows "red_u e \<noteq> \<infinity>"
proof -
  have "red_upper ! e = red_upper_at e"
    using assms red_arc_nth by auto
  hence "0 \<le> red_upper ! e"
    by(auto simp add: red_upper_at_def)
  thus ?thesis using assms by(simp add: red_u_def)
qed

text \<open>Hence the solver's unboundedness verdict cannot fire: a negative cycle of infinite capacity
      would have to use an arc of infinite capacity, and there is none.\<close>

lemma reduced_no_neg_infty_cycle:
  "\<not> has_neg_infty_cycle original_network.make_pair {0..<m}
        (\<lambda> e. h (cost_list ! e)) red_u"
proof(rule not_has_neg_infty_cycleI, goal_cases)
  case (1 D)
  have ne: "D \<noteq> []"
    using 1(1) by(auto simp add: closed_w_def)
  then obtain e where e: "e \<in> set D" by(cases D) auto
  have "e < m" using e 1(3) by auto
  thus ?case using red_u_finite_in_range 1(4)[OF e] by simp
qed


text \<open>(3) A reduced instance that the solver rejects --- either as unbounded or as infeasible ---
      means the original was infeasible, again provided the immediate check passed. The first
      disjunct is discharged outright by \<open>reduced_no_neg_infty_cycle\<close>, so only the second carries
      content: a DIMACS flow would map forward to a reduced b-flow, contradicting its absence.\<close>

theorem original_infeasible_if_reduced_fails:
  assumes ok: "red_ok_arcs"
      and fail: "has_neg_infty_cycle original_network.make_pair {0..<m}
                   (\<lambda> e. h (cost_list ! e)) red_u
                 \<or> (\<nexists> g. reduced_network.isbflow g red_b)"
  shows "\<not> original_network.is_dimacs_flow {1..<n} f"
proof
  assume flow: "original_network.is_dimacs_flow {1..<n} f"
  have "reduced_network.isbflow (red_of f) red_b" by(rule red_of_isbflow[OF ok flow])
  hence "\<exists> g. reduced_network.isbflow g red_b" by auto
  thus False using fail reduced_no_neg_infty_cycle by simp
qed

text \<open>(4) An out-of-range balance is a proof that the instance is infeasible: a net out-flow outside
      the capacity incident at the vertex cannot be met. Rejecting on \<open>\<not> bal_ok\<close> therefore loses no
      solutions, and it is what leaves \<open>red_balance_list_bounded\<close> in force for every instance the
      solver sees.\<close>

theorem no_dimacs_flow_if_not_bal_ok:
  assumes ok: "red_ok_arcs" and bad: "\<not> bal_ok"
  shows "\<not> original_network.is_dimacs_flow {1..<n} f"
proof
  assume flow: "original_network.is_dimacs_flow {1..<n} f"
  have lo: "\<And> e. e < m \<Longrightarrow> 0 \<le> red_of f e" by(rule red_of_nonneg_orig[OF flow])
  have hi: "\<And> e. e < m \<Longrightarrow> red_of f e \<le> h (red_upper ! e)" by(rule red_of_le_red_upper[OF ok flow])
  obtain v where v: "v \<in> {1..<n}"
    and viol: "\<not> (- capin v \<le> red_balance_raw ! v \<and> red_balance_raw ! v \<le> capout v)"
    using bad by(auto simp add: bal_ok_def)
  have eq: "net_out (red_of f) v = h (red_balance_raw ! v)"
    using net_out_red_of[OF v] dimacs_flow_bounds(3)[OF flow v] by simp
  have up: "net_out (red_of f) v \<le> h (capout v)" by(rule net_out_bounds(1)[OF lo hi])
  have dn: "- h (capin v) \<le> net_out (red_of f) v" by(rule net_out_bounds(2)[OF lo hi])
  show False
  proof(cases "- capin v \<le> red_balance_raw ! v")
    case True
    hence "capout v < red_balance_raw ! v" using viol by simp
    hence "h (capout v) < h (red_balance_raw ! v)" by(simp add: h_less_iff)
    thus False using up eq by simp
  next
    case False
    hence "red_balance_raw ! v < - capin v" by simp
    hence "h (red_balance_raw ! v) < - h (capin v)" by(simp add: h_less_iff[symmetric] h_uminus)
    thus False using dn eq by simp
  qed
qed

text \<open>(5) Balances that do not total \<open>0\<close> are a proof that the instance is infeasible: what a flow
      leaves at one vertex it enters at another, so the demands must cancel. Under the two-sided
      reading a remainder could be absorbed; under equality there is nothing to absorb it.\<close>

theorem no_dimacs_flow_if_not_sum_ok:
  assumes bad: "\<not> sum_ok"
  shows "\<not> original_network.is_dimacs_flow {1..<n} f"
proof
  assume flow: "original_network.is_dimacs_flow {1..<n} f"
  have hb: "(\<Sum> v \<in> {1..<n}. h (balance_list ! v)) = (\<Sum> v \<in> {1..<n}. - original_network.ex f v)"
    by(rule sum.cong) (simp_all add: dimacs_flow_bounds(3)[OF flow])
  have z: "(\<Sum> v \<in> {1..<n}. - original_network.ex f v) = 0"
    using orig_ex_sum_zero[of f] by(simp add: sum_negf)
  have "h (\<Sum> v \<in> {1..<n}. balance_list ! v) = (\<Sum> v \<in> {1..<n}. h (balance_list ! v))"
    by(rule h_sum) simp
  hence "(\<Sum> v \<in> {1..<n}. balance_list ! v) = 0" using hb z by simp
  thus False using bad by(simp add: sum_ok_def red_balance_raw_sum)
qed

text \<open>All three immediate checks together. \<^const>\<open>red_ok\<close> is what the pass computes, and failing it
      is a verdict, not a defeat: the original instance has no DIMACS flow at all.\<close>

theorem no_dimacs_flow_if_not_red_ok:
  assumes bad: "\<not> red_ok"
  shows "\<not> original_network.is_dimacs_flow {1..<n} f"
  using bad no_dimacs_flow_if_not_red_ok_arcs no_dimacs_flow_if_not_bal_ok
        no_dimacs_flow_if_not_sum_ok
  by(cases "red_ok_arcs") (auto simp add: red_ok_def)


theorem no_dimacs_Opt_if_not_red_ok:
  "\<not> red_ok \<Longrightarrow> \<not> original_network.is_dimacs_Opt {1..<n} f"
  using no_dimacs_flow_if_not_red_ok by(auto elim!: original_network.is_dimacs_OptE)

end

end

