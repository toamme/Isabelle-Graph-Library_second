
theory Network_Simplex_Instantiation_Refinement
  imports "../Network_Simplex_Initial_Basis_Selector"
          Network_Simplex_Refinement
          Acyclic_Flow_Refinement
          "../Rooted_Arborescense/Rooted_Arborescense_Refinement"
begin

section \<open>Imperative refinement of the orchestrator @{const initial_basis_code_spec.solve}\<close>

text \<open>This theory assembles the imperative counterpart of the top-level functional orchestrator
      @{const initial_basis_code_spec.solve}.  The functional program

      \<^item> acyclifies the input flow (@{const initial_basis_code_spec.acyc_flow_opt}); a @{term None}
        answer is a negative infinite-capacity cycle;
      \<^item> otherwise builds the strongly-feasible spanning tree, runs the network-simplex loop
        (\<open>NSc.ns_loop_impl\<close> from \<open>NSc.init_state\<close>) and, on a bounded optimum of the augmented
        network, reads the verdict off the artificial edges @{term \<open>[m..<m + Kart]\<close>}.

      The imperative version reuses the two big already-verified refinements — \<open>make_acyclic_imp\<close>
      (see \<open>make_acyclic_imp_rule\<close>) and \<open>ns_loop_imp\<close> (see \<open>ns_loop_imp_rule\<close>) — and glues them with a
      materialisation step and a final artificial-edge scan.  All stores are @{class heap} arrays;
      arrays are reused across phases (the acyclifier's DFS stacks and CSR blocks are handed on as
      the network-simplex path buffers and spanning-tree scaffold once the acyclifier no longer
      needs them).\<close>

subsection \<open>The three-valued solution flag\<close>

text \<open>The imperative orchestrator returns only a status flag; the optimum flow — when one exists —
      is left in the first @{term m} cells of the flow array.  The flag mirrors the three shapes of
      the functional @{typ \<open>'n ns_outcome\<close>}: @{const Optimum} \<mapsto> @{term OptimalF},
      @{const Infeasible} \<mapsto> @{term InfeasibleF}, @{const Neg_inf_cycle} \<mapsto> @{term NegInfCycleF}.\<close>

datatype solve_status = OptimalF | InfeasibleF | NegInfCycleF

text \<open>Abstraction from a functional outcome to the flag it corresponds to.\<close>
fun status_of :: "'n ns_outcome \<Rightarrow> solve_status" where
  "status_of (Optimum _)   = OptimalF"
| "status_of Infeasible    = InfeasibleF"
| "status_of Neg_inf_cycle = NegInfCycleF"

subsection \<open>The artificial-edge scan\<close>

text \<open>The concrete counterpart of @{term \<open>list_all (\<lambda>k. f ! k = 0) [m..<m + Kart]\<close>}: walk the flow
      array over the artificial index range @{term \<open>[i..<hi]\<close>} and report whether every artificial
      edge carries zero flow.  Purely a read loop over one array; no allocation.\<close>

partial_function (heap) scan_art_imp ::
  "('n::{heap,zero}) array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool Heap"
  where
  "scan_art_imp fa i hi =
     (if hi \<le> i then return True
      else do { v \<leftarrow> Array.nth fa i;
                if v = 0 then scan_art_imp fa (Suc i) hi else return False })"

text \<open>@{const scan_art_imp} computes exactly the functional test
      @{term \<open>list_all (\<lambda>k. xs ! k = 0) [i..<hi]\<close>} on the array contents, leaving the array
      untouched.  By induction on the remaining length @{term \<open>hi - i\<close>}, unfolding the fixpoint one
      step per iteration.\<close>

lemma scan_art_imp_rule:
  "hi \<le> length xs \<Longrightarrow>
   <fa \<mapsto>\<^sub>a xs> scan_art_imp fa i hi
   <\<lambda>b. fa \<mapsto>\<^sub>a xs * \<up>(b = list_all (\<lambda>k. xs ! k = 0) [i..<hi])>"
proof (induction "hi - i" arbitrary: i)
  case 0
  hence "hi \<le> i" by simp
  thus ?case by (subst scan_art_imp.simps) sep_auto
next
  case (Suc d)
  from Suc.hyps(2) have il: "i < hi" by simp
  hence il2: "i < length xs" using Suc.prems by simp
  have du: "d = hi - Suc i" using Suc.hyps(2) by simp
  have IH: "<fa \<mapsto>\<^sub>a xs> scan_art_imp fa (Suc i) hi
             <\<lambda>b. fa \<mapsto>\<^sub>a xs * \<up>(b = list_all (\<lambda>k. xs ! k = 0) [Suc i..<hi])>"
    using Suc.hyps(1)[OF du Suc.prems] .
  have split: "list_all (\<lambda>k. xs ! k = 0) [i..<hi]
             = (xs ! i = 0 \<and> list_all (\<lambda>k. xs ! k = 0) [Suc i..<hi])"
    using il by (simp add: upt_conv_Cons)
  show ?case
    by (subst scan_art_imp.simps)
       (sep_auto simp: split il2 heap: IH)
qed

section \<open>Concrete imperative data structures\<close>

text \<open>The functional program models every store as a \<^emph>\<open>list read as an array\<close> and every iterator by
      a record with a moving cursor.  Here we give the genuine mutable-array counterparts, each a
      plain top-level Heap program that \<^emph>\<open>exactly refines\<close> its functional operation, so that the two
      abstract refinement locales (the acyclifier and the network-simplex loop) can be instantiated
      at them.  Nothing here lives in a locale; the refinement obligations are discharged later in
      the proof locale of @{const initial_basis_code_spec.solve}.\<close>

subsection \<open>Flow / vertex-state stores — plain arrays\<close>

text \<open>The abstract-array model uses @{const nth} for lookup and @{const list_update} for update; the
      mutable counterparts are @{const Array.nth} and @{term \<open>\<lambda>a i x. Array.upd i x a\<close>}, with the
      store assertion the standard @{term \<open>(\<mapsto>\<^sub>a)\<close>}.  No wrapper is needed: the array primitives are
      used directly when instantiating.\<close>

subsection \<open>The CSR edge iterator\<close>

text \<open>A @{typ \<open>'e edge_csr\<close>} is four lists — @{const csr_edges}, @{const csr_lo}, @{const csr_hi}
      and the \<^emph>\<open>mutable\<close> cursor @{const csr_cur}; only the cursor is written (by @{const csr_move} /
      @{const csr_reset}).  Its mutable form is four arrays; the cursor array is the only one ever
      updated.  The vertex count @{const csr_n} is the cursor array's length.\<close>

type_synonym 'e csr_imp = "'e array \<times> nat array \<times> nat array \<times> nat array"

definition csr_assn :: "'e::heap edge_csr \<Rightarrow> 'e csr_imp \<Rightarrow> assn" where
  "csr_assn C h =
     (case h of (ea, la, ha, ca) \<Rightarrow>
        ea \<mapsto>\<^sub>a csr_edges C * la \<mapsto>\<^sub>a csr_lo C * ha \<mapsto>\<^sub>a csr_hi C * ca \<mapsto>\<^sub>a csr_cur C)"

text \<open>@{const csr_has}: the cursor of the (real) vertex @{term v} is still below its upper bound.  No
      defensive bound test: the iterator operations are only ever called on real vertices
      (@{term \<open>v < csr_n C\<close>} is guaranteed by the caller's invariant), so the reads are always in
      range.\<close>
definition csr_has_imp :: "'e::heap csr_imp \<Rightarrow> nat \<Rightarrow> bool Heap" where
  "csr_has_imp h v =
     (case h of (ea, la, ha, ca) \<Rightarrow>
        do { c \<leftarrow> Array.nth ca v; hh \<leftarrow> Array.nth ha v; return (c < hh) })"

text \<open>@{const csr_current}: the edge under the cursor.  Called only when the remaining region is
      non-empty, i.e. @{term \<open>v < csr_n C\<close>} and @{term \<open>csr_cur C ! v < csr_hi C ! v\<close>} with
      @{term \<open>csr_hi C ! v \<le> length (csr_edges C)\<close>}, so both reads are in range.\<close>
definition csr_current_imp :: "'e::heap csr_imp \<Rightarrow> nat \<Rightarrow> 'e Heap" where
  "csr_current_imp h v =
     (case h of (ea, la, ha, ca) \<Rightarrow>
        do { c \<leftarrow> Array.nth ca v; Array.nth ea c })"

text \<open>@{const csr_move}: advance the cursor of @{term v} by one.  Called only when the remaining
      region is non-empty (@{term \<open>v < csr_n C\<close>} and @{term \<open>csr_cur C ! v < csr_hi C ! v\<close>}), so the
      cursor read/write is in range and the advance is unconditional — no bound or exhaustion test.\<close>
definition csr_move_imp :: "'e::heap csr_imp \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "csr_move_imp h v =
     (case h of (ea, la, ha, ca) \<Rightarrow>
        do { c \<leftarrow> Array.nth ca v; _ \<leftarrow> Array.upd v (Suc c) ca; return () })"

text \<open>@{const csr_reset}: rewind the cursor of the (real) vertex @{term v} to its lower bound
      @{term \<open>csr_lo C ! v\<close>}; @{term \<open>v < csr_n C\<close>} guarantees the reads are in range.\<close>
definition csr_reset_imp :: "'e::heap csr_imp \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "csr_reset_imp h v =
     (case h of (ea, la, ha, ca) \<Rightarrow>
        do { l \<leftarrow> Array.nth la v; _ \<leftarrow> Array.upd v l ca; return () })"

subsection \<open>The vertex iterator\<close>

text \<open>A @{typ \<open>'v vtx_iter\<close>} is an immutable vertex list @{const vi_list} with a \<^emph>\<open>mutable\<close> cursor
      @{const vi_pos}; only the cursor moves (@{const vtx_move}).  Its mutable form is an array and a
      reference.\<close>

type_synonym 'v vtx_imp = "'v array \<times> nat ref"

definition vtx_assn :: "'v::heap vtx_iter \<Rightarrow> 'v vtx_imp \<Rightarrow> assn" where
  "vtx_assn V h = (case h of (la, pr) \<Rightarrow> la \<mapsto>\<^sub>a vi_list V * pr \<mapsto>\<^sub>r vi_pos V)"

text \<open>@{const vtx_has}: the cursor has not reached the end of the vertex list.\<close>
definition vtx_has_imp :: "'v::heap vtx_imp \<Rightarrow> bool Heap" where
  "vtx_has_imp h = (case h of (la, pr) \<Rightarrow>
     do { n \<leftarrow> Array.len la; p \<leftarrow> Ref.lookup pr; return (p < n) })"

text \<open>@{const vtx_current}: the vertex under the cursor.  Called only when the remaining region is
      non-empty, i.e. @{term \<open>vi_pos V < length (vi_list V)\<close>}, so the read is in range.\<close>
definition vtx_current_imp :: "'v::heap vtx_imp \<Rightarrow> 'v Heap" where
  "vtx_current_imp h = (case h of (la, pr) \<Rightarrow>
     do { p \<leftarrow> Ref.lookup pr; Array.nth la p })"

text \<open>@{const vtx_move}: advance the cursor by one.\<close>
definition vtx_move_imp :: "'v::heap vtx_imp \<Rightarrow> unit Heap" where
  "vtx_move_imp h = (case h of (la, pr) \<Rightarrow>
     do { p \<leftarrow> Ref.lookup pr; Ref.update pr (Suc p) })"

subsection \<open>Refinement of the concrete operations to their functional models\<close>

text \<open>Each concrete Heap program above satisfies exactly the Hoare triple that the abstract
      refinement locales assume for the corresponding functional operation.  These are the
      obligations later fed to the instantiation.\<close>

lemma csr_has_imp_rule:
  "\<lbrakk>csr_invar C; v < csr_n C\<rbrakk> \<Longrightarrow>
   <csr_assn C h> csr_has_imp h v <\<lambda>r. csr_assn C h * \<up>(r = csr_has C v)>"
  by (cases h)
     (sep_auto simp: csr_assn_def csr_has_imp_def csr_has_def csr_n_def csr_invar_def)

lemma csr_current_imp_rule:
  "\<lbrakk>csr_invar C; v < csr_n C; csr_cur C ! v < csr_hi C ! v\<rbrakk> \<Longrightarrow>
   <csr_assn C h> csr_current_imp h v <\<lambda>r. csr_assn C h * \<up>(r = csr_current C v)>"
  by (cases h)
     (sep_auto simp: csr_assn_def csr_current_imp_def csr_current_def csr_n_def csr_invar_def)

lemma csr_move_imp_rule:
  "\<lbrakk>csr_invar C; v < csr_n C; csr_cur C ! v < csr_hi C ! v\<rbrakk> \<Longrightarrow>
   <csr_assn C h> csr_move_imp h v <\<lambda>_. csr_assn (csr_move C v) h>"
  by (cases h)
     (sep_auto simp: csr_assn_def csr_move_imp_def csr_move_def csr_n_def csr_invar_def)

lemma csr_reset_imp_rule:
  "\<lbrakk>csr_invar C; v < csr_n C\<rbrakk> \<Longrightarrow>
   <csr_assn C h> csr_reset_imp h v <\<lambda>_. csr_assn (csr_reset C v) h>"
  by (cases h)
     (sep_auto simp: csr_assn_def csr_reset_imp_def csr_reset_def csr_n_def csr_invar_def)

lemma vtx_has_imp_rule:
  "<vtx_assn V h> vtx_has_imp h <\<lambda>r. vtx_assn V h * \<up>(r = vtx_has V)>"
  by (cases h) (sep_auto simp: vtx_assn_def vtx_has_imp_def vtx_has_def)

lemma vtx_current_imp_rule:
  "vi_pos V < length (vi_list V) \<Longrightarrow>
   <vtx_assn V h> vtx_current_imp h <\<lambda>r. vtx_assn V h * \<up>(r = vtx_current V)>"
  by (cases h) (sep_auto simp: vtx_assn_def vtx_current_imp_def vtx_current_def)

lemma vtx_move_imp_rule:
  "<vtx_assn V h> vtx_move_imp h <\<lambda>_. vtx_assn (vtx_move V) h>"
  by (cases h) (sep_auto simp: vtx_assn_def vtx_move_imp_def vtx_move_def)

subsection \<open>Plain array update returning unit\<close>

text \<open>The abstract-array update @{const list_update} refines to an in-place @{const Array.upd} whose
      returned handle is dropped, so the result type is @{typ \<open>unit Heap\<close>} — matching the
      @{text \<open>_upd_imp\<close>} shape both refinement locales fix.\<close>
definition arr_upd :: "'a::heap array \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> unit Heap" where
  "arr_upd a i x = do { _ \<leftarrow> Array.upd i x a; return () }"

section \<open>Heap instances for the datatypes stored in arrays\<close>

text \<open>The state / edge-tag / potential-tag datatypes are held in mutable arrays, so they must be
      @{class heap} (i.e. @{class countable} and @{class typerep}).  They are finite enumerations, so
      the instances are immediate.\<close>

instance vertex_state :: countable by countable_datatype
instance vertex_state :: heap ..
instance edge_tag :: countable by countable_datatype
instance edge_tag :: heap ..
instance mtag :: countable by countable_datatype
instance mtag :: heap ..

section \<open>Instantiating the imperative acyclifier\<close>

text \<open>The imperative acyclifier is defined in the assumption-free specification locale
      @{locale acyclic_flow_impl_refine}, which fixes only the manipulating \<^emph>\<open>functions\<close> — no
      assumptions and no fixed arrays.  We turn it into \<^emph>\<open>actual code\<close> by a @{command
      global_interpretation}: the store / iterator functions are the concrete array-manipulating
      programs built above, and the four per-edge reads are array look-ups closing over the \<^emph>\<open>four
      graph arrays\<close>, which the \<open>for\<close> clause makes \<^emph>\<open>parameters\<close> of the generated constant.
      The interpretation is provable outright (no assumptions), and @{term make_acyclic_prog} is the
      resulting executable, taking @{term cap_arr}, @{term cost_arr}, @{term fst_arr}, @{term snd_arr}
      (via \<open>for\<close>) and the eight store handles as arguments — every array handed in.\<close>

global_interpretation acyc: acyclic_flow_impl_refine
  where out_current_imp = csr_current_imp and out_has_imp = csr_has_imp
    and out_move_imp = csr_move_imp and out_reset_imp = csr_reset_imp
    and in_current_imp = csr_current_imp and in_has_imp = csr_has_imp
    and in_move_imp = csr_move_imp and in_reset_imp = csr_reset_imp
    and flow_upd_imp = arr_upd and flow_lookup_imp = Array.nth
    and st_upd_imp = arr_upd and st_lookup_imp = Array.nth
    and current_vertex_imp = vtx_current_imp and has_vertex_imp = vtx_has_imp
    and move_on_vertex_imp = vtx_move_imp
    and cap_imp  = "\<lambda>e. Array.nth cap_arr  e" and cost_imp = "\<lambda>e. Array.nth cost_arr e"
    and fst_exec_imp = "\<lambda>e. Array.nth fst_arr e" and snd_exec_imp = "\<lambda>e. Array.nth snd_arr e"
  for cap_arr cost_arr fst_arr snd_arr
  defines make_acyclic_prog = acyc.make_acyclic_imp
  by unfold_locales

text \<open>Register the recursive Heap sub-programs' fixpoint equations as code equations (the
      @{command partial_function} @{text simps}), so the acyclifier is code-generatable — the same
      discipline as \<open>DFS_imperative.simps\<close> in the imperative-DFS template.\<close>
lemmas [code] =
  acyclic_flow_impl_refine.af_rooms_imp_def
  acyclic_flow_impl_refine.af_delta_cost_imp_def
  acyclic_flow_impl_refine.af_min_imp_def
  acyclic_flow_impl_refine.af_push_arc_imp_def
  acyclic_flow_impl_refine.af_saturated_imp_def
  acyclic_flow_impl_refine.af_cancel_seg_imp_def
  acyclic_flow_impl_refine.af_reset_imp_def
  acyclic_flow_impl_refine.af_selfloop_handle_imp_def
  acyclic_flow_impl_refine.af_close_cycle_imp_def
  acyclic_flow_impl_refine.af_push_vertex_imp_def
  acyclic_flow_impl_refine.af_handle_imp_def
  acyclic_flow_impl_refine.af_dfs_start_imp_def
  acyclic_flow_impl_refine.af_impl_state_init_def
  acyclic_flow_impl_refine.af_scan_imp.simps
  acyclic_flow_impl_refine.af_push_imp.simps
  acyclic_flow_impl_refine.af_reset_unsee_seg_imp.simps
  acyclic_flow_impl_refine.AF_DFS_imp.simps
  acyclic_flow_impl_refine.AF_outer_imp.simps

export_code make_acyclic_prog checking SML_imp
export_code make_acyclic_prog in SML module_name Acyclifier

section \<open>Instantiating the imperative network-simplex loop\<close>

text \<open>The imperative loop \<open>ns_loop_imp\<close> is defined in the assumption-free specification locale
      @{locale network_simplex_impl_spec}, which fixes the manipulating \<^emph>\<open>functions\<close>: the
      entering-edge selector, the three spanning-tree operations (subtree potential-shift,
      fundamental-circuit path search, tree-edge swap) and the flow / potential / parent / direction /
      edge-state store reads and writes.  We build the concrete functions here and turn the loop into
      \<^emph>\<open>actual code\<close> by a @{command global_interpretation}, as for the acyclifier.  The spanning-tree
      primitives are the already-verified imperative ports @{const update_tree_imp},
      @{const get_path_pair_imp}, @{const iterate_root_opposed_imp} of \<open>Rooted_Arborescense_Refinement\<close>;
      the network-simplex operations are thin compositions of them.  No arrays are allocated — every
      store is a fixed function and the graph arrays / tuning constants remain
      @{command global_interpretation} parameters, allocated only in the final orchestrator.\<close>

subsection \<open>The three spanning-tree operations, on @{typ ndtree_impl}\<close>

text \<open>The join (apex / LCA) of @{term u} and @{term v}: the two pointers converge upward, the one with
      the smaller subtree size (@{const snum_impl}) climbing to its parent, until they meet — the
      imperative counterpart of @{const join_of}.  This mirrors the convergence of
      @{const join_paths_loop_imp} but keeps only the meeting vertex.\<close>
partial_function (heap) join_of_imp :: "ndtree_impl \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "join_of_imp Ti u v =
     (if u = v then return u
      else do { snu \<leftarrow> Array.nth (snum_impl Ti) u;
                snv \<leftarrow> Array.nth (snum_impl Ti) v;
                (if snu \<le> snv
                 then do { pu \<leftarrow> Array.nth (prnt_impl Ti) u; join_of_imp Ti pu v }
                 else do { pv \<leftarrow> Array.nth (prnt_impl Ti) v; join_of_imp Ti u pv }) })"

text \<open>The snum-driven climb refines the functional @{const join_of}: for any common ancestor @{term j}
      of @{term cu} and @{term cv} whose strictly-below prefixes are disjoint, @{const join_of_imp}
      returns @{term j}.  Proved by strong induction on the combined remaining root-path length, the
      exact skeleton of @{thm join_paths_loop_imp_rule} but tracking only the meeting vertex.\<close>
lemma join_of_imp_rule:
  assumes inv: "arb_invar r V S"
  shows "cu \<in> V \<Longrightarrow> cv \<in> V \<Longrightarrow> j \<in> set (follow (prnt S) cu) \<Longrightarrow> j \<in> set (follow (prnt S) cv) \<Longrightarrow>
    set (takeWhile (\<lambda>x. x \<noteq> j) (follow (prnt S) cu)) \<inter> set (takeWhile (\<lambda>x. x \<noteq> j) (follow (prnt S) cv)) = {} \<Longrightarrow>
    <ndtree_assn V S Ti> join_of_imp Ti cu cv <\<lambda>res. ndtree_assn V S Ti * \<up>(res = j)>"
proof -
  have rinv: "rooted_arborescense_invar r V (prnt S)" using inv unfolding arb_invar_def by simp
  have ps: "parent_spec (prnt S)" by (rule rooted_arborescense_invar_parent_spec[OF rinv])
  define W where "W = (\<lambda>x. takeWhile (\<lambda>y. y \<noteq> j) (follow (prnt S) x))"
  { fix N cu cv
    have "length (follow (prnt S) cu) + length (follow (prnt S) cv) = N \<Longrightarrow> cu \<in> V \<Longrightarrow> cv \<in> V \<Longrightarrow>
          j \<in> set (follow (prnt S) cu) \<Longrightarrow> j \<in> set (follow (prnt S) cv) \<Longrightarrow> set (W cu) \<inter> set (W cv) = {} \<Longrightarrow>
          <ndtree_assn V S Ti> join_of_imp Ti cu cv <\<lambda>res. ndtree_assn V S Ti * \<up>(res = j)>"
    proof (induct N arbitrary: cu cv rule: less_induct)
      case (less N cu cv)
      note eqN = less.prems(1) and cuV = less.prems(2) and cvV = less.prems(3) and jcu = less.prems(4)
        and jcv = less.prems(5) and disj = less.prems(6)
      have jV: "j \<in> V" using follow_subset_V[OF rinv cuV] jcu by auto
      show ?case
      proof (cases "cu = cv")
        case True
        note eqcc = True
        have cuj: "cu = j"
        proof (rule ccontr)
          assume cune: "cu \<noteq> j"
          have "cu \<in> set (W cu)"
          proof -
            have ne: "follow (prnt S) cu \<noteq> []" by (rule follow_ne_ps[OF ps])
            have hd: "hd (follow (prnt S) cu) = cu" by (rule follow_hd_ps[OF ps])
            show ?thesis using ne hd cune by (cases "follow (prnt S) cu") (auto simp: W_def)
          qed
          moreover have "cu \<in> set (W cv)" using eqcc calculation by simp
          ultimately show False using disj by auto
        qed
        show ?thesis using eqcc cuj by (subst join_of_imp.simps) sep_auto
      next
        case False
        note cune_cv = False
        show ?thesis
        proof (cases "snum S cu \<le> snum S cv")
          case True
          note le = True
          have cune: "cu \<noteq> j"
          proof (rule ccontr)
            assume "\<not> cu \<noteq> j" hence cj: "cu = j" by simp
            have cvne: "cv \<noteq> j" using cune_cv cj by auto
            have "snum S cv < snum S j" using snum_proper_anc_lt[OF inv jV jcv] cvne by simp
            thus False using le cj by simp
          qed
          obtain w where Pw: "prnt S cu = Some w" and fcu: "follow (prnt S) cu = cu # follow (prnt S) w"
            and jcw: "j \<in> set (follow (prnt S) w)" using follow_cons_of_anc[OF ps jcu cune] by auto
          have Wcu: "W cu = cu # W w" using fcu cune by (simp add: W_def)
          have wmem: "w \<in> set (follow (prnt S) cu)" using fcu follow_hd_ps[OF ps, of w] follow_ne_ps[OF ps, of w]
            by (metis hd_in_set list.set_intros(2))
          have wV: "w \<in> V" using follow_subset_V[OF rinv cuV] wmem by auto
          have disj': "set (W w) \<inter> set (W cv) = {}" using disj Wcu by auto
          have lenlt: "length (follow (prnt S) w) + length (follow (prnt S) cv) < N" using eqN fcu by simp
          note IH2 = less.hyps[OF lenlt refl wV cvV jcw jcv disj']
          have poeq: "nat_of_opt (prnt S cu) = w" using Pw by simp
          show ?thesis
            apply (subst join_of_imp.simps)
            apply (sep_auto simp: cune_cv le cuV cvV poeq heap: IH2)
            done
        next
          case False
          note notle = False
          have cvne: "cv \<noteq> j"
          proof (rule ccontr)
            assume "\<not> cv \<noteq> j" hence cj: "cv = j" by simp
            have cune: "cu \<noteq> j" using cune_cv cj by auto
            have "snum S cu < snum S j" using snum_proper_anc_lt[OF inv jV jcu] cune by simp
            thus False using notle cj by simp
          qed
          obtain w where Pw: "prnt S cv = Some w" and fcv: "follow (prnt S) cv = cv # follow (prnt S) w"
            and jcw: "j \<in> set (follow (prnt S) w)" using follow_cons_of_anc[OF ps jcv cvne] by auto
          have Wcv: "W cv = cv # W w" using fcv cvne by (simp add: W_def)
          have wmem: "w \<in> set (follow (prnt S) cv)" using fcv follow_hd_ps[OF ps, of w] follow_ne_ps[OF ps, of w]
            by (metis hd_in_set list.set_intros(2))
          have wV: "w \<in> V" using follow_subset_V[OF rinv cvV] wmem by auto
          have disj': "set (W cu) \<inter> set (W w) = {}" using disj Wcv by auto
          have lenlt: "length (follow (prnt S) cu) + length (follow (prnt S) w) < N" using eqN fcv by simp
          note IH2 = less.hyps[OF lenlt refl cuV wV jcu jcw disj']
          have poeq: "nat_of_opt (prnt S cv) = w" using Pw by simp
          show ?thesis
            apply (subst join_of_imp.simps)
            apply (sep_auto simp: cune_cv notle cuV cvV poeq heap: IH2)
            done
        qed
      qed
    qed }
  note gen = this[unfolded W_def]
  show "cu \<in> V \<Longrightarrow> cv \<in> V \<Longrightarrow> j \<in> set (follow (prnt S) cu) \<Longrightarrow> j \<in> set (follow (prnt S) cv) \<Longrightarrow>
    set (takeWhile (\<lambda>x. x \<noteq> j) (follow (prnt S) cu)) \<inter> set (takeWhile (\<lambda>x. x \<noteq> j) (follow (prnt S) cv)) = {} \<Longrightarrow>
    <ndtree_assn V S Ti> join_of_imp Ti cu cv <\<lambda>res. ndtree_assn V S Ti * \<up>(res = j)>"
    by (rule gen[OF refl])
qed

text \<open>Specialised to the deepest common ancestor: @{const join_of_imp} returns exactly
      @{term \<open>join_of (prnt S) u v\<close>}.  The common-ancestor side conditions of @{thm join_of_imp_rule}
      are the @{thm join_of_mem} membership and @{thm join_takeWhile_disjoint} disjointness at the join.\<close>
lemma join_of_imp_correct:
  assumes inv: "arb_invar r V S" and uV: "u \<in> V" and vV: "v \<in> V"
  shows "<ndtree_assn V S Ti> join_of_imp Ti u v
           <\<lambda>res. ndtree_assn V S Ti * \<up>(res = join_of (prnt S) u v)>"
proof -
  have rinv: "rooted_arborescense_invar r V (prnt S)" using inv unfolding arb_invar_def by simp
  have ps: "parent_spec (prnt S)" by (rule rooted_arborescense_invar_parent_spec[OF rinv])
  have lst: "last (follow (prnt S) u) = last (follow (prnt S) v)"
    using follow_last_root[OF inv uV] follow_last_root[OF inv vV] by simp
  have ju: "join_of (prnt S) u v \<in> set (follow (prnt S) u)" using join_of_mem(1)[OF ps lst] .
  have jv: "join_of (prnt S) u v \<in> set (follow (prnt S) v)" using join_of_mem(2)[OF ps lst] .
  have disjj: "set (takeWhile (\<lambda>x. x \<noteq> join_of (prnt S) u v) (follow (prnt S) u))
              \<inter> set (takeWhile (\<lambda>x. x \<noteq> join_of (prnt S) u v) (follow (prnt S) v)) = {}"
    using join_takeWhile_disjoint[OF inv uV vV refl] .
  show ?thesis by (rule join_of_imp_rule[OF inv uV vV ju jv disjj])
qed
text \<open>The functional \<open>swap_edge_impl S x u v = update_tree S u v x (join_of (prnt S) u v)\<close>,
      imperatively: compute the join of the entering edge's endpoints and hand it to
      @{const update_tree_imp}.\<close>
definition ns_swap_edge_imp :: "ndtree_impl \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "ns_swap_edge_imp Ti x u v = do { j \<leftarrow> join_of_imp Ti u v; update_tree_imp Ti u v x j }"

text \<open>The functional \<open>get_path_pair_impl\<close>, imperatively: the verified @{const get_path_pair_imp} with
      the two caller path arrays moved after the endpoints, to match the fixed operation's argument
      order.\<close>
definition ns_get_path_pair_imp ::
  "ndtree_impl \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> (nat \<times> nat) Heap" where
  "ns_get_path_pair_imp Ti u v a1 a2 = get_path_pair_imp Ti a1 a2 u v"

text \<open>The functional \<open>shift_pot_impl\<close>, imperatively: fold the read/shift/write of the potential cell
      over the subtree of @{term v} opposed to the root, via the verified
      @{const iterate_root_opposed_imp}.  The sign of the shift is chosen by @{term up} (add on the
      up-side, subtract on the down-side).  The accumulator is the unused unit — the potential array is
      mutated in place.\<close>
definition ns_shift_pot_imp ::
  "ndtree_impl \<Rightarrow> nat \<Rightarrow> (mtag \<times> 'n::{heap,linordered_idom}) array \<Rightarrow> (mtag \<times> 'n) \<Rightarrow> bool \<Rightarrow> unit Heap" where
  "ns_shift_pot_imp Ti v pa g up =
     iterate_root_opposed_imp Ti v
       (\<lambda>x (_::unit). do { p \<leftarrow> Array.nth pa x;
                           _ \<leftarrow> Array.upd x (if up then pval_plus p g else pval_minus p g) pa;
                           return () }) ()"

subsection \<open>The entering-edge selector, imperatively\<close>

text \<open>The M-free block-search selector, ported to the Heap monad.  The candidate cache becomes a
      @{typ \<open>nat array\<close>}, and the bookmark / live-length become @{typ \<open>nat ref\<close>}s; the running best is
      carried as the pure flat @{typ \<open>'n best_cand\<close>}.  Everything else (the reduced-cost descriptor
      arithmetic, the eligibility and violation tests) is the same M-free pure code as the functional
      selector — the pure @{const initial_basis_code_spec.better} is reused directly — so the
      executable counterparts of \<open>cost_pval\<close> / \<open>evaluate\<close> / \<open>scan_cache\<close> / \<open>scan\<close> differ only in
      reading their inputs from arrays.  The tuning constants (@{term m}, the arc count, the block
      size, the min / max candidate counts) and the three graph arrays (endpoints, cost) stay
      parameters, fixed only in the orchestrator.\<close>

type_synonym ns_sel_imp = "nat array \<times> nat ref \<times> nat ref"

text \<open>The functional \<open>cost_pval\<close>: the plain cost of an original edge (tag @{term M_0}), or the
      artificial cost @{const pval_M} for an artificial edge @{term \<open>e \<ge> m\<close>}.\<close>
definition cost_pval_imp :: "nat \<Rightarrow> 'n::{heap,linordered_idom} array \<Rightarrow> nat \<Rightarrow> (mtag \<times> 'n) Heap" where
  "cost_pval_imp m cost_arr e =
     (if e < m then do { c \<leftarrow> Array.nth cost_arr e; return (M_0, c) } else return pval_M)"

text \<open>The functional \<open>evaluate\<close>: read the edge tag and endpoints once; a self-loop is ineligible
      without pricing; otherwise assemble the reduced-cost descriptor once and test its sign M-free.\<close>
definition evaluate_imp ::
  "nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> 'n::{heap,linordered_idom} array \<Rightarrow> edge_tag array
   \<Rightarrow> (mtag \<times> 'n) array \<Rightarrow> nat \<Rightarrow> (bool \<times> bool \<times> (mtag \<times> 'n)) Heap" where
  "evaluate_imp m fst_arr snd_arr cost_arr es pt e =
     do { a \<leftarrow> Array.nth fst_arr e; d \<leftarrow> Array.nth snd_arr e; t \<leftarrow> Array.nth es e;
          if a = d then return (False, t = InU, pval_zero)
          else do { cp \<leftarrow> cost_pval_imp m cost_arr e;
                    pa \<leftarrow> Array.nth pt a; pd \<leftarrow> Array.nth pt d;
                    (let g = pval_plus cp (pval_minus pa pd)
                     in return ((case t of InTree \<Rightarrow> False | InL \<Rightarrow> pval_neg g | InU \<Rightarrow> pval_pos g),
                                t = InU, g)) } }"

text \<open>Minor iteration (the functional \<open>scan_cache\<close>): one pass over the live prefix @{term \<open>[0..<len]\<close>}
      of the cache array; a still-eligible entry is priced once and offered to the running best (index
      advances), a dud is deleted by swap-with-last (write @{term \<open>sarr ! (len-1)\<close>} into slot @{term i},
      drop the length, do not advance).  Returns the shrunk length and the best; the array is mutated in
      place.\<close>
partial_function (heap) scan_cache_imp ::
  "nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> 'n::{heap,linordered_idom} array \<Rightarrow> edge_tag array
   \<Rightarrow> (mtag \<times> 'n) array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'n best_cand \<Rightarrow> (nat \<times> 'n best_cand) Heap" where
  "scan_cache_imp m fst_arr snd_arr cost_arr es pt sarr i len best =
     (if len \<le> i then return (len, best)
      else do {
        e \<leftarrow> Array.nth sarr i;
        (elig, u, g) \<leftarrow> evaluate_imp m fst_arr snd_arr cost_arr es pt e;
        (if elig
         then scan_cache_imp m fst_arr snd_arr cost_arr es pt sarr (Suc i) len
                (initial_basis_code_spec.better best (e, u, g))
         else do { lst \<leftarrow> Array.nth sarr (len - 1);
                   _ \<leftarrow> arr_upd sarr i lst;
                   scan_cache_imp m fst_arr snd_arr cost_arr es pt sarr i (len - 1) best }) })"

text \<open>Major iteration (the functional \<open>scan\<close>): the wrap-around block sweep from the bookmark
      @{term cur}, at most @{term fuel} arcs, stopping when the cache reaches the max candidate count or
      a whole block has been scanned and at least the min candidate count is held.  An eligible arc is
      pushed at the length pointer.  Returns the advanced bookmark, the new length and the best; the
      cache array is mutated in place.\<close>
partial_function (heap) scan_imp ::
  "nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> 'n::{heap,linordered_idom} array
   \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> edge_tag array \<Rightarrow> (mtag \<times> 'n) array \<Rightarrow> nat array
   \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'n best_cand \<Rightarrow> (nat \<times> nat \<times> 'n best_cand) Heap" where
  "scan_imp m fst_arr snd_arr cost_arr min_c max_c block_size mc es pt sarr fuel bpos cur len best =
     (if fuel = 0 then return (cur, len, best)
      else if max_c \<le> len then return (cur, len, best)
      else if bpos = 0 \<and> min_c \<le> len then return (cur, len, best)
      else do {
        (elig, u, g) \<leftarrow> evaluate_imp m fst_arr snd_arr cost_arr es pt cur;
        _ \<leftarrow> (if elig then arr_upd sarr len cur else return ());
        (let bpos1 = (if bpos = 0 then block_size else bpos);
             len1  = (if elig then Suc len else len);
             best1 = (if elig then initial_basis_code_spec.better best (cur, u, g) else best);
             cur1  = (if cur + 1 = mc then 0 else cur + 1)
         in scan_imp m fst_arr snd_arr cost_arr min_c max_c block_size mc es pt sarr
                     (fuel - 1) (bpos1 - 1) cur1 len1 best1) })"

text \<open>The functional \<open>sel_select_impl\<close>, imperatively: minor iteration first; if it finds an entering
      edge, commit the shrunk length and return it; otherwise a major iteration, committing bookmark and
      length on success, @{term None} (optimal) otherwise.  The state triple is mutated in place, so the
      returned tuple drops the selector — exactly the \<^emph>\<open>_imp\<close> discipline.\<close>
definition ns_sel_select_imp ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> 'n::{heap,linordered_idom} array
   \<Rightarrow> ns_sel_imp \<Rightarrow> (mtag \<times> 'n) array \<Rightarrow> edge_tag array
   \<Rightarrow> (nat \<times> bool \<times> (mtag \<times> 'n)) option Heap" where
  "ns_sel_select_imp m mc block_size min_c max_c fst_arr snd_arr cost_arr sel pt es =
     (let sarr = fst sel; cref = fst (snd sel); lref = snd (snd sel)
      in do {
        len0 \<leftarrow> Ref.lookup lref;
        (len1, b1) \<leftarrow> scan_cache_imp m fst_arr snd_arr cost_arr es pt sarr 0 len0 no_best;
        (case b1 of (found1, e1, u1, g1) \<Rightarrow>
           if found1 then do { _ \<leftarrow> Ref.update lref len1; return (Some (e1, u1, g1)) }
           else do {
             cur0 \<leftarrow> Ref.lookup cref;
             (cur2, len2, b2) \<leftarrow> scan_imp m fst_arr snd_arr cost_arr min_c max_c block_size mc
                                          es pt sarr mc block_size cur0 len1 no_best;
             (case b2 of (found2, e2, u2, g2) \<Rightarrow>
                if found2 then do { _ \<leftarrow> Ref.update cref cur2; _ \<leftarrow> Ref.update lref len2;
                                    return (Some (e2, u2, g2)) }
                else return None) }) })"

subsection \<open>The @{command global_interpretation}\<close>

text \<open>The store reads are @{const Array.nth}, the store writes @{const arr_upd}; the two path buffers
      are plain @{typ \<open>nat array\<close>}s.  The selector, the three tree operations and the endpoint /
      capacity reads are the concrete functions above.  The graph arrays and the selector's tuning
      constants become parameters via \<open>for\<close>; @{term ns_loop_prog} is the resulting executable loop.\<close>

global_interpretation ns: network_simplex_impl_spec
  where r = r
    and sel_select_imp =
          "ns_sel_select_imp m marc_c block_c minc_c maxc_c fst_arr snd_arr cost_arr"
    and shift_pot_imp = ns_shift_pot_imp
    and get_path_pair_imp = ns_get_path_pair_imp
    and swap_edge_imp = ns_swap_edge_imp
    and flow_upd_imp = arr_upd and flow_lookup_imp = Array.nth
    and parent_upd_imp = arr_upd and parent_lookup_imp = Array.nth
    and dir_upd_imp = arr_upd and dir_lookup_imp = Array.nth
    and es_upd_imp = arr_upd and es_lookup_imp = Array.nth
    and cap_imp = "Array.nth cap_arr"
    and fst_exec_imp = "Array.nth fst_arr"
    and snd_exec_imp = "Array.nth snd_arr"
  for r m marc_c block_c minc_c maxc_c fst_arr snd_arr cost_arr cap_arr
  defines ns_loop_prog = ns.ns_loop_imp
  by unfold_locales

section \<open>Materialising the strongly-feasible initial basis\<close>

text \<open>The imperative port of the functional builder \<open>build_tree\<close> / \<open>art_tree\<close> of
      \<open>Network_Simplex_Initial_Basis_Code\<close>: a genuine array program that, from the acyclified flow left
      in the flow array, fills the augmented edge arrays (the artificial tail @{term \<open>[m..<m+Kart]\<close>})
      and the strongly-feasible spanning tree — the very @{typ ndtree_impl}, parent / direction /
      potential arrays and edge-state array the network-simplex loop then mutates.  Following the
      functional code, \<^emph>\<open>arrays are reused, not reallocated\<close>: the acyclifier's two counting-sort CSRs
      become the free-edge CSRs in place (Pass A keeps their block starts @{const csr_lo} and
      overwrites the edge arrays / cursors with the free edges at the front of each block), the excess
      accumulator is transformed in place into the imbalance, and the DFS stack reuses the acyclifier's
      three stack arrays.\<close>

subsection \<open>Pass A: the fused free-edge CSR sweep, in place\<close>

text \<open>The functional \<open>passA_step\<close> as a Heap loop over the edge range @{term \<open>[e..<hi]\<close>}.  For each edge
      it writes the edge tag into the (augmented) edge-state array, accumulates the excess (head then
      tail, so a self-loop cancels), and — for a \<^emph>\<open>free\<close> edge (tag @{const InTree}) — appends the edge
      to the front of its endpoints' outgoing / ingoing free blocks, bumping the two cursor arrays.  The
      edge arrays @{term oe} / @{term ie} and cursors @{term oc} / @{term ic} are the acyclifier's CSR
      edge / cursor arrays, overwritten in place; the block starts stay untouched, so afterwards the
      free block of @{term v} is the half-open index range \<open>csr_lo ! v\<close> up to \<open>oc ! v\<close>.\<close>
partial_function (heap) passA_imp ::
  "'n::{heap,linordered_idom} array \<Rightarrow> 'n array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> edge_tag array \<Rightarrow> 'n array
   \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "passA_imp fl cap_arr fst_arr snd_arr es_arr exc_arr oe_arr oc_arr ie_arr ic_arr e hi =
     (if hi \<le> e then return ()
      else do {
        x \<leftarrow> Array.nth fst_arr e; y \<leftarrow> Array.nth snd_arr e;
        f \<leftarrow> Array.nth fl e; u \<leftarrow> Array.nth cap_arr e;
        (let st = (if f = 0 then InL else if u \<noteq> - 1 \<and> f = u then InU else InTree)
         in do {
           _ \<leftarrow> arr_upd es_arr e st;
           ey \<leftarrow> Array.nth exc_arr y; _ \<leftarrow> arr_upd exc_arr y (ey + f);
           ex \<leftarrow> Array.nth exc_arr x; _ \<leftarrow> arr_upd exc_arr x (ex - f);
           _ \<leftarrow> (if st = InTree
                then do { ox \<leftarrow> Array.nth oc_arr x; _ \<leftarrow> arr_upd oe_arr ox e; _ \<leftarrow> arr_upd oc_arr x (Suc ox);
                          iy \<leftarrow> Array.nth ic_arr y; _ \<leftarrow> arr_upd ie_arr iy e; arr_upd ic_arr y (Suc iy) }
                else return ());
           passA_imp fl cap_arr fst_arr snd_arr es_arr exc_arr oe_arr oc_arr ie_arr ic_arr (Suc e) hi }) })"

subsection \<open>Imbalance: the excess transformed in place\<close>

text \<open>The functional \<open>imbalance = fold (\<lambda>v arr. arr[v := arr ! v + b_lookup v]) [0..<vcount] excess\<close>:
      add each vertex's target balance to its achieved excess, in place on the (reused) excess array.\<close>
partial_function (heap) imbalance_imp ::
  "'n::{heap,linordered_idom} array \<Rightarrow> 'n array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "imbalance_imp exc_arr b_arr v vcount =
     (if vcount \<le> v then return ()
      else do { e \<leftarrow> Array.nth exc_arr v; bb \<leftarrow> Array.nth b_arr v;
                _ \<leftarrow> arr_upd exc_arr v (e + bb);
                imbalance_imp exc_arr b_arr (Suc v) vcount })"

subsection \<open>The imperative builder state\<close>

text \<open>The mutable counterpart of the functional @{typ \<open>'n dfs_state\<close>}: a bundle of the array / reference
      handles the DFS builder mutates.  The five spanning-tree maps live in the @{typ ndtree_impl}
      @{term di_tree} (whose arrays \<^emph>\<open>are\<close> the network-simplex loop's tree, filled here); the parent /
      direction / potential / edge-state arrays are likewise the loop's own stores.  The artificial
      edges are written \<^emph>\<open>directly into the augmented endpoint / capacity / flow / edge-state arrays\<close>
      at index @{term \<open>m + k\<close>} (no separate artificial arrays), so @{term di_fst} \<dots> @{term di_es} are
      the length-\<open>m + K\<close> augmented arrays.  The free-edge CSRs @{term di_oe} / @{term di_olo} /
      @{term di_ohi} (and the ingoing triple) are the acyclifier's repurposed CSR arrays; the DFS stack
      of @{term \<open>(v, oc, ic)\<close>} frames is the three arrays @{term di_sv} / @{term di_soc} / @{term di_sic}
      with the fill pointer @{term di_sp}.\<close>

record 'n dfs_imp =
  di_seen :: "bool array"          \<comment> \<open>visited flag\<close>
  di_tree :: "ndtree_impl"         \<comment> \<open>prnt / thrd / rvth / lsuc / snum (the loop's tree)\<close>
  di_par  :: "nat array"           \<comment> \<open>parent edge id\<close>
  di_dir  :: "bool array"          \<comment> \<open>parent-edge orientation\<close>
  di_pot  :: "(mtag \<times> 'n) array"   \<comment> \<open>potential\<close>
  di_fst  :: "nat array"           \<comment> \<open>augmented edge tails (fst); artificial writes at \<open>m + k\<close>\<close>
  di_snd  :: "nat array"           \<comment> \<open>augmented edge heads (snd)\<close>
  di_cap  :: "'n array"            \<comment> \<open>augmented capacities\<close>
  di_cost :: "'n array"            \<comment> \<open>edge costs (original block; the \<plusminus> cost seed)\<close>
  di_flow :: "'n array"            \<comment> \<open>augmented flow\<close>
  di_es   :: "edge_tag array"      \<comment> \<open>augmented edge-state tags\<close>
  di_oe   :: "nat array"           \<comment> \<open>free outgoing CSR edges\<close>
  di_olo  :: "nat array"           \<comment> \<open>outgoing block starts (\<open>csr_lo\<close>)\<close>
  di_ohi  :: "nat array"           \<comment> \<open>free outgoing block ends (post-Pass-A cursors)\<close>
  di_ie   :: "nat array"           \<comment> \<open>free ingoing CSR edges\<close>
  di_ilo  :: "nat array"           \<comment> \<open>ingoing block starts\<close>
  di_ihi  :: "nat array"           \<comment> \<open>free ingoing block ends\<close>
  di_sv   :: "nat array"           \<comment> \<open>DFS stack: frame vertices\<close>
  di_soc  :: "nat array"           \<comment> \<open>DFS stack: frame out-cursors\<close>
  di_sic  :: "nat array"           \<comment> \<open>DFS stack: frame in-cursors\<close>
  di_sp   :: "nat ref"             \<comment> \<open>DFS stack fill pointer\<close>
  di_prev :: "nat ref"             \<comment> \<open>last vertex emitted in preorder\<close>
  di_nxt  :: "nat ref"             \<comment> \<open>next artificial-edge offset (id = \<open>m + di_nxt\<close>)\<close>

subsection \<open>Discovering and finishing a vertex\<close>

text \<open>The functional @{term dfs_discover}: finalise the fresh child @{term w} reached from @{term v}
      across free real edge @{term e} — seed its tree fields, thread-link it after the last emitted
      vertex, give @{term e} zero reduced cost (\<open>\<plusminus> cost\<close> by whether @{term v} is @{term e}'s tail), and
      push its frame @{term \<open>(w, out_lo ! w, in_lo ! w)\<close>}.\<close>
definition dfs_discover_imp :: "'n::{heap,linordered_idom} dfs_imp \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "dfs_discover_imp st v w e =
     do {
       fe \<leftarrow> Array.nth (di_fst st) e;
       ce \<leftarrow> Array.nth (di_cost st) e;
       pv \<leftarrow> Ref.lookup (di_prev st);
       potv \<leftarrow> Array.nth (di_pot st) v;
       (let sgn = (if v = fe then ce else - ce);
            pw  = pval_plus potv (M_0, sgn)
        in do {
          _ \<leftarrow> arr_upd (di_seen st) w True;
          _ \<leftarrow> arr_upd (prnt_impl (di_tree st)) w v;
          _ \<leftarrow> arr_upd (di_par st) w e;
          _ \<leftarrow> arr_upd (di_dir st) w (fe = w);
          _ \<leftarrow> arr_upd (di_pot st) w pw;
          _ \<leftarrow> arr_upd (thrd_impl (di_tree st)) pv w;
          _ \<leftarrow> arr_upd (rvth_impl (di_tree st)) w pv;
          _ \<leftarrow> arr_upd (snum_impl (di_tree st)) w 1;
          _ \<leftarrow> Ref.update (di_prev st) w;
          olo \<leftarrow> Array.nth (di_olo st) w;
          ilo \<leftarrow> Array.nth (di_ilo st) w;
          sp \<leftarrow> Ref.lookup (di_sp st);
          _ \<leftarrow> arr_upd (di_sv st) sp w;
          _ \<leftarrow> arr_upd (di_soc st) sp olo;
          _ \<leftarrow> arr_upd (di_sic st) sp ilo;
          Ref.update (di_sp st) (Suc sp) }) }"

text \<open>The functional @{term dfs_finish}: on popping @{term v} (post-order) the last vertex emitted is
      its rightmost descendant, so it is @{term v}'s \<open>lsuc\<close>; add @{term v}'s completed subtree size to
      its parent's and pop the frame.\<close>
definition dfs_finish_imp :: "'n::{heap,linordered_idom} dfs_imp \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "dfs_finish_imp st v =
     do { p \<leftarrow> Array.nth (prnt_impl (di_tree st)) v;
          pv \<leftarrow> Ref.lookup (di_prev st);
          _ \<leftarrow> arr_upd (lsuc_impl (di_tree st)) v pv;
          snp \<leftarrow> Array.nth (snum_impl (di_tree st)) p;
          snv \<leftarrow> Array.nth (snum_impl (di_tree st)) v;
          _ \<leftarrow> arr_upd (snum_impl (di_tree st)) p (snp + snv);
          sp \<leftarrow> Ref.lookup (di_sp st);
          Ref.update (di_sp st) (sp - 1) }"

subsection \<open>The depth-first traversal\<close>

text \<open>The functional @{term build_dfs_a} on the reused stack arrays: at the stack top scan the free
      outgoing block, then the free ingoing block, recursing into each unseen neighbour (advancing the
      frame cursor first, then discovering); when both blocks are exhausted, finish the vertex.  The
      neighbour across an outgoing edge @{term e} is @{term \<open>snd_list ! e\<close>}, across an ingoing edge
      @{term \<open>fst_list ! e\<close>}.\<close>
partial_function (heap) build_dfs_a_imp ::
  "'n::{heap,linordered_idom} dfs_imp \<Rightarrow> unit Heap" where
  "build_dfs_a_imp st =
     do {
       sp \<leftarrow> Ref.lookup (di_sp st);
       (if sp = 0 then return ()
        else (let top = sp - 1 in do {
          v  \<leftarrow> Array.nth (di_sv st) top;
          oc \<leftarrow> Array.nth (di_soc st) top;
          oh \<leftarrow> Array.nth (di_ohi st) v;
          (if oc < oh
           then do {
             e \<leftarrow> Array.nth (di_oe st) oc;
             w \<leftarrow> Array.nth (di_snd st) e;
             _ \<leftarrow> arr_upd (di_soc st) top (Suc oc);
             sw \<leftarrow> Array.nth (di_seen st) w;
             _ \<leftarrow> (if sw then return () else dfs_discover_imp st v w e);
             build_dfs_a_imp st }
           else do {
             ic \<leftarrow> Array.nth (di_sic st) top;
             ih \<leftarrow> Array.nth (di_ihi st) v;
             (if ic < ih
              then do {
                e \<leftarrow> Array.nth (di_ie st) ic;
                w \<leftarrow> Array.nth (di_fst st) e;
                _ \<leftarrow> arr_upd (di_sic st) top (Suc ic);
                sw \<leftarrow> Array.nth (di_seen st) w;
                _ \<leftarrow> (if sw then return () else dfs_discover_imp st v w e);
                build_dfs_a_imp st }
              else do {
                _ \<leftarrow> dfs_finish_imp st v;
                build_dfs_a_imp st }) }) })) }"

subsection \<open>Opening tree components and emitting artificial edges\<close>

text \<open>The functional @{term open_tree_component}: open an unseen imbalanced (Phase 1) or balanced
      (Phase 2) vertex @{term c} as a child of the root.  Emit @{term c}'s \<^emph>\<open>tree\<close> artificial edge —
      written directly into the augmented arrays at index @{term \<open>m + k\<close>} and tagged @{const InTree} —
      finalise @{term c}'s tree fields, seed its potential to \<open>\<plusminus> 𝑀\<close>, thread-link it, then drain its
      subtree with @{const build_dfs_a_imp}.  Orientation / flow / capacity come from the one
      @{term \<open>imb_arr ! c\<close>} read (the imbalance array): up (\<open>c \<rightarrow> root\<close>) iff @{term \<open>0 \<le> imb\<close>}, flow
      @{term \<open>\<bar>imb\<bar>\<close>}, a tree edge getting a \<open>+ 1\<close> slack toward the root when it points up.\<close>
definition open_tree_component_imp ::
  "'n::{heap,linordered_idom} dfs_imp \<Rightarrow> 'n array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "open_tree_component_imp st imb_arr m vcount c =
     do {
       imb \<leftarrow> Array.nth imb_arr c;
       nxt \<leftarrow> Ref.lookup (di_nxt st);
       pv  \<leftarrow> Ref.lookup (di_prev st);
       (let up = 0 \<le> imb; af = \<bar>imb\<bar>; cp = (if up then af + 1 else af); aidx = m + nxt
        in do {
          _ \<leftarrow> arr_upd (di_fst st) aidx (if up then c else vcount);
          _ \<leftarrow> arr_upd (di_snd st) aidx (if up then vcount else c);
          _ \<leftarrow> arr_upd (di_cap st) aidx cp;
          _ \<leftarrow> arr_upd (di_flow st) aidx af;
          _ \<leftarrow> arr_upd (di_es st) aidx InTree;
          _ \<leftarrow> Ref.update (di_nxt st) (Suc nxt);
          _ \<leftarrow> arr_upd (di_seen st) c True;
          _ \<leftarrow> arr_upd (prnt_impl (di_tree st)) c vcount;
          _ \<leftarrow> arr_upd (di_par st) c aidx;
          _ \<leftarrow> arr_upd (di_dir st) c up;
          _ \<leftarrow> arr_upd (di_pot st) c (if up then pval_negM else pval_M);
          _ \<leftarrow> arr_upd (thrd_impl (di_tree st)) pv c;
          _ \<leftarrow> arr_upd (rvth_impl (di_tree st)) c pv;
          _ \<leftarrow> arr_upd (snum_impl (di_tree st)) c 1;
          _ \<leftarrow> Ref.update (di_prev st) c;
          olo \<leftarrow> Array.nth (di_olo st) c;
          ilo \<leftarrow> Array.nth (di_ilo st) c;
          _ \<leftarrow> arr_upd (di_sv st) 0 c;
          _ \<leftarrow> arr_upd (di_soc st) 0 olo;
          _ \<leftarrow> arr_upd (di_sic st) 0 ilo;
          _ \<leftarrow> Ref.update (di_sp st) 1;
          build_dfs_a_imp st }) }"

text \<open>The functional @{term emit_U_edge}: a \<^emph>\<open>saturated\<close> @{term U} artificial edge for an already-seen
      imbalanced vertex @{term v} — capacity equal to its flow @{term \<open>\<bar>imb\<bar>\<close>}, tagged @{const InU},
      touching no tree field.\<close>
definition emit_U_edge_imp ::
  "'n::{heap,linordered_idom} dfs_imp \<Rightarrow> 'n array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "emit_U_edge_imp st imb_arr m vcount v =
     do {
       imb \<leftarrow> Array.nth imb_arr v;
       nxt \<leftarrow> Ref.lookup (di_nxt st);
       (let up = 0 \<le> imb; fl = \<bar>imb\<bar>; aidx = m + nxt
        in do {
          _ \<leftarrow> arr_upd (di_fst st) aidx (if up then v else vcount);
          _ \<leftarrow> arr_upd (di_snd st) aidx (if up then vcount else v);
          _ \<leftarrow> arr_upd (di_cap st) aidx fl;
          _ \<leftarrow> arr_upd (di_flow st) aidx fl;
          _ \<leftarrow> arr_upd (di_es st) aidx InU;
          Ref.update (di_nxt st) (Suc nxt) }) }"

subsection \<open>The two vertex scans\<close>

text \<open>The functional @{term phase1_step}: an imbalanced unseen vertex opens its tree component, an
      imbalanced already-seen vertex emits a saturated @{term U} edge, a balanced vertex is skipped.\<close>
definition phase1_step_imp ::
  "'n::{heap,linordered_idom} dfs_imp \<Rightarrow> 'n array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "phase1_step_imp st imb_arr m vcount v =
     do { imb \<leftarrow> Array.nth imb_arr v;
          (if imb = 0 then return ()
           else do { sv \<leftarrow> Array.nth (di_seen st) v;
                     (if sv then emit_U_edge_imp st imb_arr m vcount v
                      else open_tree_component_imp st imb_arr m vcount v) }) }"

text \<open>@{term phase1}: the fused first scan of the vertices @{term \<open>vs_list = [1..n]\<close>}.\<close>
partial_function (heap) phase1_imp ::
  "'n::{heap,linordered_idom} dfs_imp \<Rightarrow> 'n array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "phase1_imp st imb_arr m vcount v n =
     (if n < v then return ()
      else do { _ \<leftarrow> phase1_step_imp st imb_arr m vcount v;
                phase1_imp st imb_arr m vcount (Suc v) n })"

text \<open>The functional @{term phase2_step}: open every still-unseen, \<^emph>\<open>non-lonely\<close> (hence balanced)
      vertex as a flow-0 tree component.  A vertex is lonely when it is an endpoint of no edge — both
      its \<^emph>\<open>full\<close> outgoing and ingoing blocks are empty; those full block-ends are the acyclifier's
      original @{const csr_hi} arrays @{term ofh} / @{term ifh}, untouched by Pass A (which only rewrote
      the cursors into the free block-ends).\<close>
definition phase2_step_imp ::
  "'n::{heap,linordered_idom} dfs_imp \<Rightarrow> 'n array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "phase2_step_imp st imb_arr ofh ifh m vcount v =
     do { sv \<leftarrow> Array.nth (di_seen st) v;
          (if sv then return ()
           else do { olo \<leftarrow> Array.nth (di_olo st) v; ohi \<leftarrow> Array.nth ofh v;
                     ilo \<leftarrow> Array.nth (di_ilo st) v; ihi \<leftarrow> Array.nth ifh v;
                     (if olo = ohi \<and> ilo = ihi then return ()
                      else open_tree_component_imp st imb_arr m vcount v) }) }"

text \<open>@{term phase2}: the second scan opening every remaining balanced vertex.\<close>
partial_function (heap) phase2_imp ::
  "'n::{heap,linordered_idom} dfs_imp \<Rightarrow> 'n array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "phase2_imp st imb_arr ofh ifh m vcount v n =
     (if n < v then return ()
      else do { _ \<leftarrow> phase2_step_imp st imb_arr ofh ifh m vcount v;
                phase2_imp st imb_arr ofh ifh m vcount (Suc v) n })"

subsection \<open>The finished builder\<close>

text \<open>The functional @{term build_tree}: seed the root (subtree size @{term 1}, last-emitted vertex the
      root @{term vcount}, empty stack, no artificial edges yet), run both phases, then the one root
      finalisation the traversal cannot do per-frame — the root is never popped, so its \<open>lsuc\<close>
      (rightmost descendant of the whole tree) is the final last-emitted vertex.  The vertex-indexed
      arrays are assumed freshly zeroed by the orchestrator (parents / edges / thread pointers @{term 0},
      directions @{term False}, potentials @{const pval_zero}, sizes @{term 0}); this seeds only the
      root-specific cells and the three references.\<close>
definition build_tree_imp ::
  "'n::{heap,linordered_idom} dfs_imp \<Rightarrow> 'n array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "build_tree_imp st imb_arr ofh ifh m vcount n =
     do {
       _ \<leftarrow> arr_upd (snum_impl (di_tree st)) vcount 1;
       _ \<leftarrow> Ref.update (di_prev st) vcount;
       _ \<leftarrow> Ref.update (di_nxt st) 0;
       _ \<leftarrow> Ref.update (di_sp st) 0;
       _ \<leftarrow> phase1_imp st imb_arr m vcount 1 n;
       _ \<leftarrow> phase2_imp st imb_arr ofh ifh m vcount 1 n;
       pv \<leftarrow> Ref.lookup (di_prev st);
       arr_upd (lsuc_impl (di_tree st)) vcount pv }"

text \<open>The flat-array DFS stack: @{term di_sv} / @{term di_soc} / @{term di_sic} hold the frames in
      index order @{term \<open>[0..<sp]\<close>} with the fill pointer @{term \<open>sp = di_sp\<close>}; the functional
      @{const ds_stk} is that prefix \<^emph>\<open>reversed\<close> — its head is the array top at index @{term \<open>sp - 1\<close>}.
      \<open>dfs_discover\<close> pushes (a write at @{term sp}, bump) and \<open>dfs_finish\<close> pops (just a
      pointer decrement — the popped slot stays but is invisible above @{term sp}).\<close>
definition stk_rel :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<times> nat) list \<Rightarrow> bool" where
  "stk_rel svl socl sicl sp stk \<longleftrightarrow>
     sp \<le> length svl \<and> sp \<le> length socl \<and> sp \<le> length sicl \<and>
     stk = rev (map (\<lambda>i. (svl ! i, socl ! i, sicl ! i)) [0..<sp])"

lemma stk_rel_push:
  assumes "stk_rel svl socl sicl sp stk" "sp < length svl" "sp < length socl" "sp < length sicl"
  shows "stk_rel (svl[sp := v]) (socl[sp := oc]) (sicl[sp := ic]) (Suc sp) ((v, oc, ic) # stk)"
proof -
  have "map (\<lambda>i. (svl[sp := v] ! i, socl[sp := oc] ! i, sicl[sp := ic] ! i)) [0..<sp]
      = map (\<lambda>i. (svl ! i, socl ! i, sicl ! i)) [0..<sp]"
    by (rule map_cong) (auto simp: nth_list_update)
  thus ?thesis using assms unfolding stk_rel_def by (auto simp: upt_Suc_append)
qed

lemma stk_rel_top:
  assumes "stk_rel svl socl sicl (Suc sp) stk"
  shows "stk = (svl ! sp, socl ! sp, sicl ! sp) # rev (map (\<lambda>i. (svl ! i, socl ! i, sicl ! i)) [0..<sp])"
  using assms unfolding stk_rel_def by (simp add: upt_Suc_append)

lemma stk_rel_pop:
  assumes "stk_rel svl socl sicl (Suc sp) ((v, oc, ic) # rest)"
  shows "stk_rel svl socl sicl sp rest"
  using assms unfolding stk_rel_def by (simp add: upt_Suc_append)

lemma stk_rel_len: "stk_rel svl socl sicl sp stk \<Longrightarrow> length stk = sp"
  unfolding stk_rel_def by simp

lemma stk_rel_nil [simp]: "stk_rel svl socl sicl sp [] \<longleftrightarrow> sp = 0"
  by (auto simp: stk_rel_def)

lemma stk_rel_pop':
  assumes "stk_rel svl socl sicl sp (f # rest)"
  shows "0 < sp \<and> stk_rel svl socl sicl (sp - 1) rest"
proof -
  have "length (f # rest) = sp" using stk_rel_len[OF assms] .
  hence sp: "sp = Suc (sp - 1)" and pos: "0 < sp" by auto
  obtain a b c where f: "f = (a, b, c)" by (cases f)
  have "stk_rel svl socl sicl (sp - 1) rest"
    using assms sp f stk_rel_pop[of svl socl sicl "sp - 1" a b c rest] by simp
  thus ?thesis using pos by simp
qed

text \<open>Reading the \<^emph>\<open>top\<close> frame of a non-empty flat stack: the fill pointer is one past the frame index
      @{term \<open>length rest\<close>}, the three arrays hold the head @{term \<open>(v, oc, ic)\<close>} there, that index is in
      range, and dropping it leaves the tail related to @{term rest}.  This is what the DFS-loop
      refinement reads at each recursive step (@{const build_dfs_a_imp} takes the top at @{term \<open>sp - 1\<close>}).\<close>
lemma stk_rel_hd:
  assumes "stk_rel svl socl sicl sp ((v,oc,ic)#rest)"
  shows "sp = Suc (length rest) \<and> svl!(length rest)=v \<and> socl!(length rest)=oc \<and> sicl!(length rest)=ic
         \<and> length rest < length svl \<and> length rest < length socl \<and> length rest < length sicl
         \<and> stk_rel svl socl sicl (length rest) rest"
proof -
  have sp: "sp = Suc (length rest)" using stk_rel_len[OF assms] by simp
  have top: "((v,oc,ic)#rest) = (svl ! (length rest), socl ! (length rest), sicl ! (length rest))
               # rev (map (\<lambda>i. (svl ! i, socl ! i, sicl ! i)) [0..<length rest])"
    using stk_rel_top[of svl socl sicl "length rest" "(v,oc,ic)#rest"] assms sp by simp
  have hd: "svl!(length rest)=v" "socl!(length rest)=oc" "sicl!(length rest)=ic"
    using top by simp_all
  have pop: "stk_rel svl socl sicl (length rest) rest"
    using stk_rel_pop'[OF assms] sp by simp
  have lens: "length rest < length svl" "length rest < length socl" "length rest < length sicl"
    using assms sp unfolding stk_rel_def by auto
  show ?thesis using sp hd pop lens by blast
qed

text \<open>A decomposition rewrite for a non-empty flat stack: exposes the top frame values, the fill
      pointer, the in-range indices and the tail relation as an explicit conjunction — used to resolve
      the DFS-loop reads by simplification.\<close>
lemma stk_rel_cons_simp:
  "stk_rel svl socl sicl sp ((v,oc,ic)#rest) \<longleftrightarrow>
     (sp = Suc (length rest) \<and> svl!(length rest)=v \<and> socl!(length rest)=oc \<and> sicl!(length rest)=ic
      \<and> length rest < length svl \<and> length rest < length socl \<and> length rest < length sicl
      \<and> stk_rel svl socl sicl (length rest) rest)"
proof
  assume "stk_rel svl socl sicl sp ((v,oc,ic)#rest)"
  thus "sp = Suc (length rest) \<and> svl!(length rest)=v \<and> socl!(length rest)=oc \<and> sicl!(length rest)=ic
      \<and> length rest < length svl \<and> length rest < length socl \<and> length rest < length sicl
      \<and> stk_rel svl socl sicl (length rest) rest"
    using stk_rel_hd by blast
next
  assume R: "sp = Suc (length rest) \<and> svl!(length rest)=v \<and> socl!(length rest)=oc \<and> sicl!(length rest)=ic
      \<and> length rest < length svl \<and> length rest < length socl \<and> length rest < length sicl
      \<and> stk_rel svl socl sicl (length rest) rest"
  hence "(v,oc,ic)#rest = rev (map (\<lambda>i. (svl ! i, socl ! i, sicl ! i)) [0..<sp])"
    unfolding stk_rel_def by (simp add: upt_Suc_append)
  thus "stk_rel svl socl sicl sp ((v,oc,ic)#rest)"
    using R unfolding stk_rel_def by simp
qed

text \<open>Updating a stack array at an index at or above the current depth leaves the frame relation of the
      tail untouched (the read positions are all strictly below).  The two variants target the
      out-cursor array (@{term socl}) and the in-cursor array (@{term sicl}) — the two the DFS loop
      bumps in place.\<close>
lemma stk_rel_upd_ge:
  assumes "stk_rel svl socl sicl sp' rest" "sp' \<le> i"
  shows "stk_rel svl (list_update socl i x) sicl sp' rest"
proof -
  have j: "(list_update socl i x)!j = socl!j" if "j < sp'" for j
  proof -
    have "j \<noteq> i" using that assms(2) by linarith
    thus ?thesis by (simp add: nth_list_update_neq)
  qed
  have "map (\<lambda>j. (svl!j, (list_update socl i x)!j, sicl!j)) [0..<sp'] = map (\<lambda>j. (svl!j, socl!j, sicl!j)) [0..<sp']"
    by (rule map_cong) (auto simp: j)
  thus ?thesis using assms unfolding stk_rel_def by simp
qed

lemma stk_rel_upd_ge_sic:
  assumes "stk_rel svl socl sicl sp' rest" "sp' \<le> i"
  shows "stk_rel svl socl (list_update sicl i x) sp' rest"
proof -
  have j: "(list_update sicl i x)!j = sicl!j" if "j < sp'" for j
  proof -
    have "j \<noteq> i" using that assms(2) by linarith
    thus ?thesis by (simp add: nth_list_update_neq)
  qed
  have "map (\<lambda>j. (svl!j, socl!j, (list_update sicl i x)!j)) [0..<sp'] = map (\<lambda>j. (svl!j, socl!j, sicl!j)) [0..<sp']"
    by (rule map_cong) (auto simp: j)
  thus ?thesis using assms unfolding stk_rel_def by simp
qed

section \<open>Building the two adjacency CSRs by counting sort\<close>

text \<open>The imperative port of the functional \<open>build_two_csr\<close> / \<open>build_csr_scatter\<close>: the standard
      two-pass counting sort.  Each CSR keys every edge on an endpoint (the outgoing CSR on
      @{term \<open>fst_list ! e\<close>}, the ingoing on @{term \<open>snd_list ! e\<close>}), counts the per-vertex degrees,
      turns the counts into block starts by a prefix sum, and scatters each edge into its block.  The
      block-start array @{term lo}, the block-end array @{term hi} and the (scattered) edge array
      @{term edges} are exactly the fields of a @{typ \<open>nat edge_csr\<close>}; the cursor @{term cur} is left at
      the block starts, ready for iteration.\<close>

text \<open>Fill a prefix of an array with a constant (used to zero the count array before reuse).\<close>
partial_function (heap) arr_fill_imp :: "'a::heap array \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "arr_fill_imp a x v nn =
     (if nn \<le> v then return () else do { _ \<leftarrow> arr_upd a v x; arr_fill_imp a x (Suc v) nn })"

text \<open>Copy a prefix of one array into another (used to reset the cursor array to the block starts).\<close>
partial_function (heap) arr_copy_imp :: "'a::heap array \<Rightarrow> 'a array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "arr_copy_imp src dst v nn =
     (if nn \<le> v then return ()
      else do { x \<leftarrow> Array.nth src v; _ \<leftarrow> arr_upd dst v x; arr_copy_imp src dst (Suc v) nn })"

subsection \<open>Refinement rules for the generic array loops\<close>

text \<open>A single in-place write refines a list update; @{const arr_fill_imp} and @{const arr_copy_imp}
      then refine the corresponding range operations on the abstract list.\<close>

lemma arr_upd_rule [sep_heap_rules]:
  "i < length xs \<Longrightarrow> <a \<mapsto>\<^sub>a xs> arr_upd a i x <\<lambda>_. a \<mapsto>\<^sub>a list_update xs i x>"
  unfolding arr_upd_def by sep_auto

lemma fill_eq_aux:
  assumes "v < nn" "nn \<le> length xs"
  shows "take (Suc v) (list_update xs v x) @ replicate (nn - Suc v) x @ drop nn (list_update xs v x)
       = take v xs @ replicate (nn - v) x @ drop nn xs"
proof -
  have a: "take (Suc v) (list_update xs v x) = take v xs @ [x]"
    using assms by (simp add: take_update_swap take_Suc_conv_app_nth list_update_append)
  have b: "drop nn (list_update xs v x) = drop nn xs"
    using assms by (simp add: drop_update_cancel)
  have c: "replicate (nn - v) x = x # replicate (nn - Suc v) x"
    by (simp add: Suc_diff_Suc[OF assms(1), symmetric])
  show ?thesis by (simp only: a b c append.assoc append_Cons append_Nil)
qed

lemma arr_fill_imp_rule:
  "v \<le> nn \<Longrightarrow> nn \<le> length xs \<Longrightarrow>
   <a \<mapsto>\<^sub>a xs> arr_fill_imp a x v nn
   <\<lambda>_. a \<mapsto>\<^sub>a (take v xs @ replicate (nn - v) x @ drop nn xs)>"
proof (induction "nn - v" arbitrary: v xs)
  case 0
  then have "nn = v" by simp
  then show ?case by (subst arr_fill_imp.simps) sep_auto
next
  case (Suc d)
  from Suc.hyps(2) Suc.prems have vn: "v < nn" by simp
  have d': "d = nn - Suc v" using Suc.hyps(2) by simp
  have len': "nn \<le> length (list_update xs v x)" using Suc.prems by simp
  have step: "<a \<mapsto>\<^sub>a list_update xs v x> arr_fill_imp a x (Suc v) nn
              <\<lambda>_. a \<mapsto>\<^sub>a (take (Suc v) (list_update xs v x) @ replicate (nn - Suc v) x @ drop nn (list_update xs v x))>"
    using Suc.hyps(1)[OF d' _ len'] vn by simp
  have eq: "(take (Suc v) xs)[v := x] @ replicate (nn - Suc v) x @ drop nn xs
            = take v xs @ replicate (nn - v) x @ drop nn xs"
  proof -
    have a: "(take (Suc v) xs)[v := x] = take v xs @ [x]"
      using vn Suc.prems(2) by (simp add: take_Suc_conv_app_nth list_update_append)
    have c: "replicate (nn - v) x = x # replicate (nn - Suc v) x"
      by (simp add: Suc_diff_Suc[OF vn, symmetric])
    show ?thesis by (simp only: a c append.assoc append_Cons append_Nil)
  qed
  show ?case
    using vn Suc.prems(2)
    apply (subst arr_fill_imp.simps)
    by (sep_auto heap: step simp: eq)
qed

lemma arr_copy_imp_rule:
  "v \<le> nn \<Longrightarrow> nn \<le> length xs \<Longrightarrow> nn \<le> length ys \<Longrightarrow>
   <src \<mapsto>\<^sub>a xs * dst \<mapsto>\<^sub>a ys> arr_copy_imp src dst v nn
   <\<lambda>_. src \<mapsto>\<^sub>a xs * dst \<mapsto>\<^sub>a (take v ys @ take (nn - v) (drop v xs) @ drop nn ys)>"
proof (induction "nn - v" arbitrary: v ys)
  case 0
  then have "nn = v" by simp
  then show ?case by (subst arr_copy_imp.simps) sep_auto
next
  case (Suc d)
  from Suc.hyps(2) Suc.prems have vn: "v < nn" by simp
  have vx: "v < length xs" using vn Suc.prems(2) by simp
  have d': "d = nn - Suc v" using Suc.hyps(2) by simp
  have lenys': "nn \<le> length (list_update ys v (xs ! v))" using Suc.prems(3) by simp
  have step: "<src \<mapsto>\<^sub>a xs * dst \<mapsto>\<^sub>a list_update ys v (xs ! v)> arr_copy_imp src dst (Suc v) nn
              <\<lambda>_. src \<mapsto>\<^sub>a xs * dst \<mapsto>\<^sub>a (take (Suc v) (list_update ys v (xs ! v))
                        @ take (nn - Suc v) (drop (Suc v) xs) @ drop nn (list_update ys v (xs ! v)))>"
    using Suc.hyps(1)[OF d' _ Suc.prems(2) lenys'] vn by simp
  have eq: "(take (Suc v) ys)[v := xs ! v] @ take (nn - Suc v) (drop (Suc v) xs) @ drop nn ys
            = take v ys @ take (nn - v) (drop v xs) @ drop nn ys"
  proof -
    have a: "(take (Suc v) ys)[v := xs ! v] = take v ys @ [xs ! v]"
      using vn Suc.prems(3) by (simp add: take_Suc_conv_app_nth list_update_append)
    have c: "take (nn - v) (drop v xs) = xs ! v # take (nn - Suc v) (drop (Suc v) xs)"
      by (simp only: Cons_nth_drop_Suc[OF vx, symmetric] Suc_diff_Suc[OF vn, symmetric] take_Suc_Cons)
    show ?thesis by (simp only: a c append.assoc append_Cons append_Nil)
  qed
  show ?case
    using vn Suc.prems(2,3)
    apply (subst arr_copy_imp.simps)
    by (sep_auto heap: step simp: eq)
qed

text \<open>Counting pass: increment the degree of each edge's key vertex.\<close>
partial_function (heap) csr_count_imp :: "nat array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "csr_count_imp key_arr c e hi =
     (if hi \<le> e then return ()
      else do { k \<leftarrow> Array.nth key_arr e; ck \<leftarrow> Array.nth c k; _ \<leftarrow> arr_upd c k (Suc ck);
                csr_count_imp key_arr c (Suc e) hi })"

text \<open>Prefix-sum pass: turn the degree counts into block starts (@{term lo}) and ends (@{term hi}),
      seeding the cursor at the starts.\<close>
partial_function (heap) csr_psum_imp ::
  "nat array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "csr_psum_imp c lo hi cur v acc nn =
     (if nn \<le> v then return ()
      else do { cv \<leftarrow> Array.nth c v;
                _ \<leftarrow> arr_upd lo v acc; _ \<leftarrow> arr_upd cur v acc; _ \<leftarrow> arr_upd hi v (acc + cv);
                csr_psum_imp c lo hi cur (Suc v) (acc + cv) nn })"

text \<open>Scatter pass: place each edge into its block at the running cursor, bumping the cursor.\<close>
partial_function (heap) csr_scatter_imp :: "nat array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "csr_scatter_imp key_arr edges cur e hi =
     (if hi \<le> e then return ()
      else do { k \<leftarrow> Array.nth key_arr e; p \<leftarrow> Array.nth cur k; _ \<leftarrow> arr_upd edges p e; _ \<leftarrow> arr_upd cur k (Suc p);
                csr_scatter_imp key_arr edges cur (Suc e) hi })"

text \<open>Build one CSR keyed by @{term key_arr}: count the degrees (the count array @{term c} must be
      pre-zeroed by the caller — freshly allocated for the first build, explicitly re-zeroed for later
      ones, so no redundant zeroing pass), prefix-sum into @{term lo} / @{term hi} / @{term cur},
      scatter into @{term edges}, then reset the cursor to the block starts.  @{term m} edges,
      @{term nn} vertex names.\<close>
definition build_csr_imp ::
  "nat array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "build_csr_imp key_arr c lo hi cur edges m nn =
     do { _ \<leftarrow> csr_count_imp key_arr c 0 m;
          _ \<leftarrow> csr_psum_imp c lo hi cur 0 0 nn;
          _ \<leftarrow> csr_scatter_imp key_arr edges cur 0 m;
          arr_copy_imp lo cur 0 nn }"

subsection \<open>Refinement rules for the CSR builder loops\<close>

text \<open>The counting pass refines the histogram fold: each key in @{term \<open>[e..<hi]\<close>} bumps its bucket.\<close>
lemma csr_count_imp_rule:
  "e \<le> hi \<Longrightarrow> hi \<le> length keys \<Longrightarrow> (\<forall>i\<in>{e..<hi}. keys ! i < length c0) \<Longrightarrow>
   <ka \<mapsto>\<^sub>a keys * ca \<mapsto>\<^sub>a c0> csr_count_imp ka ca e hi
   <\<lambda>_. ka \<mapsto>\<^sub>a keys * ca \<mapsto>\<^sub>a fold (\<lambda>i cc. cc[keys ! i := Suc (cc ! (keys ! i))]) [e..<hi] c0>"
proof (induction "hi - e" arbitrary: e c0)
  case 0
  then have "hi = e" by simp
  then show ?case by (subst csr_count_imp.simps) sep_auto
next
  case (Suc d)
  from Suc.hyps(2) Suc.prems have eh: "e < hi" by simp
  then have esh: "Suc e \<le> hi" by simp
  have ke: "keys ! e < length c0" using Suc.prems(3) eh by simp
  have ekeys: "e < length keys" using eh Suc.prems(2) by simp
  have d': "d = hi - Suc e" using Suc.hyps(2) by simp
  have len1: "\<forall>i\<in>{Suc e..<hi}. keys ! i < length (c0[keys ! e := Suc (c0 ! (keys ! e))])"
    using Suc.prems(3) by simp
  have step: "<ka \<mapsto>\<^sub>a keys * ca \<mapsto>\<^sub>a c0[keys ! e := Suc (c0 ! (keys ! e))]> csr_count_imp ka ca (Suc e) hi
              <\<lambda>_. ka \<mapsto>\<^sub>a keys * ca \<mapsto>\<^sub>a fold (\<lambda>i cc. cc[keys ! i := Suc (cc ! (keys ! i))]) [Suc e..<hi] (c0[keys ! e := Suc (c0 ! (keys ! e))])>"
    using Suc.hyps(1)[OF d' esh Suc.prems(2) len1] by simp
  have foldeq: "fold (\<lambda>i cc. cc[keys ! i := Suc (cc ! (keys ! i))]) [e..<hi] c0
              = fold (\<lambda>i cc. cc[keys ! i := Suc (cc ! (keys ! i))]) [Suc e..<hi] (c0[keys ! e := Suc (c0 ! (keys ! e))])"
    using eh by (simp add: upt_conv_Cons)
  show ?case
    using eh ke ekeys
    apply (subst csr_count_imp.simps)
    by (sep_auto heap: step simp: foldeq)
qed

text \<open>Helpers about the running prefix-sum @{const psums}.\<close>
lemma psums_ne [simp]: "psums acc xs \<noteq> []" by (cases xs) auto
lemma psums_Cons_drop: "v < length cs \<Longrightarrow> psums acc (drop v cs) = acc # psums (acc + cs ! v) (drop (Suc v) cs)"
  by (metis Cons_nth_drop_Suc psums.simps(2))
lemma psums_hd_tl: "psums a xs = a # tl (psums a xs)" by (cases xs) auto

text \<open>The prefix-sum pass refines @{const psums}: it fills @{term lo}/@{term cur} with the block
      starts @{term \<open>butlast (psums 0 cs)\<close>} and @{term hi} with the block ends @{term \<open>tl (psums 0 cs)\<close>}.\<close>
lemma csr_psum_imp_rule:
  "v \<le> nn \<Longrightarrow> length cs = nn \<Longrightarrow> length lo0 = nn \<Longrightarrow> length hi0 = nn \<Longrightarrow> length cur0 = nn \<Longrightarrow>
   <c \<mapsto>\<^sub>a cs * la \<mapsto>\<^sub>a lo0 * ha \<mapsto>\<^sub>a hi0 * cua \<mapsto>\<^sub>a cur0>
     csr_psum_imp c la ha cua v acc nn
   <\<lambda>_. c \<mapsto>\<^sub>a cs
        * la \<mapsto>\<^sub>a (take v lo0 @ butlast (psums acc (drop v cs)))
        * ha \<mapsto>\<^sub>a (take v hi0 @ tl (psums acc (drop v cs)))
        * cua \<mapsto>\<^sub>a (take v cur0 @ butlast (psums acc (drop v cs)))>"
proof (induction "nn - v" arbitrary: v acc lo0 hi0 cur0)
  case 0
  then have vn: "v = nn" by simp
  show ?case using 0 vn
    by (subst csr_psum_imp.simps) (sep_auto simp: psums_length)
next
  case (Suc d)
  from Suc.hyps(2) Suc.prems(1) have vn: "v < nn" by simp
  have vlen: "v < length cs" using vn Suc.prems(2) by simp
  have d': "d = nn - Suc v" using Suc.hyps(2) by simp
  let ?P = "psums (acc + cs ! v) (drop (Suc v) cs)"
  have step: "<c \<mapsto>\<^sub>a cs * la \<mapsto>\<^sub>a lo0[v := acc] * ha \<mapsto>\<^sub>a hi0[v := acc + cs ! v] * cua \<mapsto>\<^sub>a cur0[v := acc]>
     csr_psum_imp c la ha cua (Suc v) (acc + cs ! v) nn
   <\<lambda>_. c \<mapsto>\<^sub>a cs
        * la \<mapsto>\<^sub>a (take (Suc v) (lo0[v := acc]) @ butlast ?P)
        * ha \<mapsto>\<^sub>a (take (Suc v) (hi0[v := acc + cs ! v]) @ tl ?P)
        * cua \<mapsto>\<^sub>a (take (Suc v) (cur0[v := acc]) @ butlast ?P)>"
    using Suc.hyps(1)[OF d' _ Suc.prems(2), of "lo0[v := acc]" "hi0[v := acc + cs ! v]" "cur0[v := acc]" "acc + cs ! v"] vn Suc.prems(3,4,5) by simp
  have pd: "psums acc (drop v cs) = acc # ?P" by (rule psums_Cons_drop[OF vlen])
  have la_eq: "(take (Suc v) lo0)[v := acc] @ butlast ?P = take v lo0 @ butlast (psums acc (drop v cs))"
    using vn Suc.prems(3) by (simp add: pd take_Suc_conv_app_nth list_update_append)
  have cu_eq: "(take (Suc v) cur0)[v := acc] @ butlast ?P = take v cur0 @ butlast (psums acc (drop v cs))"
    using vn Suc.prems(5) by (simp add: pd take_Suc_conv_app_nth list_update_append)
  have hi_eq: "(take (Suc v) hi0)[v := acc + cs ! v] @ tl ?P = take v hi0 @ tl (psums acc (drop v cs))"
    using vn Suc.prems(4) by (simp add: pd take_Suc_conv_app_nth list_update_append psums_hd_tl[symmetric])
  show ?case
    using vn vlen Suc.prems(2,3,4,5)
    apply (subst csr_psum_imp.simps)
    by (sep_auto heap: step simp: la_eq cu_eq hi_eq)
qed

text \<open>Memory-safety of the scatter: under the scatter invariant @{const sc_inv}, the running cursor
      of the next edge is still inside its block (below @{term \<open>length es\<close>}).  This is exactly the
      @{text pos_lt} step inside @{thm [source] sc_inv_step}, lifted out.\<close>
lemma sc_inv_pos_lt:
  assumes valid: "\<forall>x\<in>set es. key x < n"
      and split: "es = dn @ e # rest"
      and inv: "sc_inv n key es ed ps dn"
    shows "ps ! key e < length es"
proof -
  have wn: "key e < n" using valid split by auto
  have psw: "ps ! key e = sc_lo n key es (key e) + length (filter (\<lambda>x. key x = key e) dn)"
    using inv wn by (simp add: sc_inv_def)
  have cntw_lt: "length (filter (\<lambda>x. key x = key e) dn) < ct n key es ! (key e)"
    using split wn by (auto simp: ct_nth)
  have "ps ! key e < sc_lo n key es (key e) + ct n key es ! (key e)" using psw cntw_lt by simp
  also have "\<dots> = sc_lo n key es (Suc (key e))" using wn by (simp add: sc_lo_Suc)
  also have "\<dots> \<le> length es" using valid wn by (simp add: sc_lo_le_length)
  finally show ?thesis .
qed

lemma upt_split3: "e < m \<Longrightarrow> [0..<m] = [0..<e] @ e # [Suc e..<m]"
  by (metis le0 less_imp_le_nat upt_add_eq_append upt_conv_Cons le_add_diff_inverse)
lemma upt_snoc_e: "[0..<e] @ [e] = [0..<Suc e]" by simp

text \<open>The scatter pass refines @{const scatter_body}: placing each edge @{term e} at its block cursor
      @{term \<open>ps ! (keys ! e)\<close>} and bumping that cursor.  @{const sc_inv} (threaded via
      @{thm [source] sc_inv_step}) both drives the fold and guarantees every write is in range.\<close>
lemma csr_scatter_imp_rule:
  "e \<le> hi \<Longrightarrow> hi \<le> m \<Longrightarrow> m \<le> length keys \<Longrightarrow> length ed0 = m \<Longrightarrow> length ps0 = n \<Longrightarrow> (\<forall>i<m. keys ! i < n) \<Longrightarrow>
   sc_inv n (nth keys) [0..<m] ed0 ps0 [0..<e] \<Longrightarrow>
   <ka \<mapsto>\<^sub>a keys * ea \<mapsto>\<^sub>a ed0 * cua \<mapsto>\<^sub>a ps0>
     csr_scatter_imp ka ea cua e hi
   <\<lambda>_. ka \<mapsto>\<^sub>a keys
        * ea \<mapsto>\<^sub>a fst (fold (scatter_body (nth keys)) [e..<hi] (ed0, ps0))
        * cua \<mapsto>\<^sub>a snd (fold (scatter_body (nth keys)) [e..<hi] (ed0, ps0))>"
proof (induction "hi - e" arbitrary: e ed0 ps0)
  case 0
  then have "hi = e" by simp
  then show ?case by (subst csr_scatter_imp.simps) sep_auto
next
  case (Suc d)
  from Suc.hyps(2) Suc.prems(1) have eh: "e < hi" by simp
  hence em: "e < m" using Suc.prems(2) by simp
  have ekeys: "e < length keys" using em Suc.prems(3) by simp
  have ken: "keys ! e < n" using em Suc.prems(6) by simp
  have d': "d = hi - Suc e" using Suc.hyps(2) by simp
  have esh: "Suc e \<le> hi" using eh by simp
  have lps: "length ps0 = n" by (rule Suc.prems(5))
  have valid: "\<forall>x\<in>set [0..<m]. (nth keys) x < n" using Suc.prems(6) by simp
  have split: "[0..<m] = [0..<e] @ e # [Suc e..<m]" by (rule upt_split3[OF em])
  have led: "length ed0 = length ([0..<m]::nat list)" using Suc.prems(4) by simp
  have poslt: "ps0 ! (keys ! e) < m"
    using sc_inv_pos_lt[OF valid split Suc.prems(7)] by simp
  have inv': "sc_inv n (nth keys) [0..<m] (ed0[ps0 ! (keys ! e) := e]) (ps0[keys ! e := Suc (ps0 ! (keys ! e))]) [0..<Suc e]"
    using sc_inv_step[OF valid split led lps Suc.prems(7)] by (simp only: upt_snoc_e)
  have led': "length (ed0[ps0 ! (keys ! e) := e]) = m" using Suc.prems(4) by simp
  have lps': "length (ps0[keys ! e := Suc (ps0 ! (keys ! e))]) = n" using lps by simp
  have step: "<ka \<mapsto>\<^sub>a keys * ea \<mapsto>\<^sub>a ed0[ps0 ! (keys ! e) := e] * cua \<mapsto>\<^sub>a ps0[keys ! e := Suc (ps0 ! (keys ! e))]>
     csr_scatter_imp ka ea cua (Suc e) hi
   <\<lambda>_. ka \<mapsto>\<^sub>a keys
        * ea \<mapsto>\<^sub>a fst (fold (scatter_body (nth keys)) [Suc e..<hi] (ed0[ps0 ! (keys ! e) := e], ps0[keys ! e := Suc (ps0 ! (keys ! e))]))
        * cua \<mapsto>\<^sub>a snd (fold (scatter_body (nth keys)) [Suc e..<hi] (ed0[ps0 ! (keys ! e) := e], ps0[keys ! e := Suc (ps0 ! (keys ! e))]))>"
    by (rule Suc.hyps(1)[OF d' esh Suc.prems(2) Suc.prems(3) led' lps' Suc.prems(6) inv'])
  have foldeq: "fold (scatter_body (nth keys)) [e..<hi] (ed0, ps0)
              = fold (scatter_body (nth keys)) [Suc e..<hi] (ed0[ps0 ! (keys ! e) := e], ps0[keys ! e := Suc (ps0 ! (keys ! e))])"
    using eh by (simp add: upt_conv_Cons scatter_body_def)
  show ?case
    using eh em ekeys ken poslt lps Suc.prems(4)
    apply (subst csr_scatter_imp.simps)
    by (sep_auto heap: step simp: foldeq)
qed

text \<open>The whole CSR build refines the functional constructor: count (@{const ct}) \<rightarrow> prefix-sum
      (@{const psums}) \<rightarrow> scatter (@{const scatter_edges}) \<rightarrow> reset the cursor to the block starts.\<close>
lemma fold_scatter_snd_length: "length (snd (fold (scatter_body key) es st)) = length (snd st)"
  by (induction es arbitrary: st) (auto simp: scatter_body_def split: prod.splits)

lemma build_csr_imp_rule:
  assumes mk: "m \<le> length keys" and kn: "\<forall>i<m. keys ! i < nn"
  shows "<ka \<mapsto>\<^sub>a keys * c \<mapsto>\<^sub>a replicate nn (0::nat) * lo \<mapsto>\<^sub>a replicate nn (0::nat) * hi \<mapsto>\<^sub>a replicate nn (0::nat) * cur \<mapsto>\<^sub>a replicate nn (0::nat) * ea \<mapsto>\<^sub>a replicate m (0::nat)>
     build_csr_imp ka c lo hi cur ea m nn
   <\<lambda>_. ka \<mapsto>\<^sub>a keys * c \<mapsto>\<^sub>a ct nn (nth keys) [0..<m]
        * lo \<mapsto>\<^sub>a butlast (psums 0 (ct nn (nth keys) [0..<m]))
        * hi \<mapsto>\<^sub>a tl (psums 0 (ct nn (nth keys) [0..<m]))
        * cur \<mapsto>\<^sub>a butlast (psums 0 (ct nn (nth keys) [0..<m]))
        * ea \<mapsto>\<^sub>a scatter_edges nn (nth keys) [0..<m] 0>"
proof -
  let ?ct = "ct nn (nth keys) [0..<m]"
  let ?lo = "butlast (psums 0 ?ct)"
  have si: "sc_inv nn (nth keys) [0..<m] (replicate m 0) ?lo [0..<0]"
    using scatter_init_inv[of nn "nth keys" "[0..<m]" 0] by simp
  have p1: "<ka \<mapsto>\<^sub>a keys * c \<mapsto>\<^sub>a replicate nn 0> csr_count_imp ka c 0 m <\<lambda>_. ka \<mapsto>\<^sub>a keys * c \<mapsto>\<^sub>a ?ct>"
  proof -
    have "<ka \<mapsto>\<^sub>a keys * c \<mapsto>\<^sub>a replicate nn 0> csr_count_imp ka c 0 m
          <\<lambda>_. ka \<mapsto>\<^sub>a keys * c \<mapsto>\<^sub>a fold (\<lambda>i cc. cc[keys ! i := Suc (cc ! (keys ! i))]) [0..<m] (replicate nn 0)>"
      by (rule csr_count_imp_rule) (use mk kn in auto)
    thus ?thesis by (simp add: ct_def)
  qed
  have p2: "<c \<mapsto>\<^sub>a ?ct * lo \<mapsto>\<^sub>a replicate nn 0 * hi \<mapsto>\<^sub>a replicate nn 0 * cur \<mapsto>\<^sub>a replicate nn 0>
              csr_psum_imp c lo hi cur 0 0 nn
            <\<lambda>_. c \<mapsto>\<^sub>a ?ct * lo \<mapsto>\<^sub>a ?lo * hi \<mapsto>\<^sub>a tl (psums 0 ?ct) * cur \<mapsto>\<^sub>a ?lo>"
    using csr_psum_imp_rule[of 0 nn ?ct "replicate nn 0" "replicate nn 0" "replicate nn 0" c lo hi cur 0]
    by simp
  have p3: "<ka \<mapsto>\<^sub>a keys * ea \<mapsto>\<^sub>a replicate m 0 * cur \<mapsto>\<^sub>a ?lo>
              csr_scatter_imp ka ea cur 0 m
            <\<lambda>_. ka \<mapsto>\<^sub>a keys * ea \<mapsto>\<^sub>a scatter_edges nn (nth keys) [0..<m] 0
                 * cur \<mapsto>\<^sub>a snd (fold (scatter_body (nth keys)) [0..<m] (replicate m 0, ?lo))>"
    using csr_scatter_imp_rule[of 0 m m keys "replicate m 0" ?lo nn ka ea cur] mk kn si
    by (simp add: scatter_edges_def psums_length)
  have p4: "\<And>ys. length ys = nn \<Longrightarrow> <lo \<mapsto>\<^sub>a ?lo * cur \<mapsto>\<^sub>a ys> arr_copy_imp lo cur 0 nn <\<lambda>_. lo \<mapsto>\<^sub>a ?lo * cur \<mapsto>\<^sub>a ?lo>"
  proof -
    fix ys :: "nat list" assume l: "length ys = nn"
    show "<lo \<mapsto>\<^sub>a ?lo * cur \<mapsto>\<^sub>a ys> arr_copy_imp lo cur 0 nn <\<lambda>_. lo \<mapsto>\<^sub>a ?lo * cur \<mapsto>\<^sub>a ?lo>"
      using arr_copy_imp_rule[of 0 nn ?lo ys lo cur] l by (simp add: psums_length)
  qed
  show ?thesis
    unfolding build_csr_imp_def
    by (sep_auto heap: p1 p2 p3 p4 simp: fold_scatter_snd_length psums_length)
qed

section \<open>The orchestrator\<close>

text \<open>The imperative counterpart of the functional @{const initial_basis_code_spec.edged_vs_list}: the
      dense vertex range @{term \<open>[1..n]\<close>} with the \<^emph>\<open>lonely\<close> names (endpoints of no edge — both full
      blocks empty) removed.  The acyclifier iterates exactly these.  We count them, then fill an
      exactly-sized array (so the iterator's length matches the abstraction).\<close>
partial_function (heap) count_edged_imp ::
  "nat array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "count_edged_imp olo ohi ilo ihi v n acc =
     (if n < v then return acc
      else do { ol \<leftarrow> Array.nth olo v; oh \<leftarrow> Array.nth ohi v; il \<leftarrow> Array.nth ilo v; ih \<leftarrow> Array.nth ihi v;
                count_edged_imp olo ohi ilo ihi (Suc v) n (if ol = oh \<and> il = ih then acc else Suc acc) })"

partial_function (heap) fill_edged_imp ::
  "nat array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "fill_edged_imp vl olo ohi ilo ihi v n j =
     (if n < v then return ()
      else do { ol \<leftarrow> Array.nth olo v; oh \<leftarrow> Array.nth ohi v; il \<leftarrow> Array.nth ilo v; ih \<leftarrow> Array.nth ihi v;
                (if ol = oh \<and> il = ih then fill_edged_imp vl olo ohi ilo ihi (Suc v) n j
                 else do { _ \<leftarrow> arr_upd vl j v; fill_edged_imp vl olo ohi ilo ihi (Suc v) n (Suc j) }) })"

text \<open>The functional list the two loops compute: the non-lonely vertices of @{term \<open>[v..n]\<close>} (a vertex
      is \<^emph>\<open>lonely\<close> when both its CSR blocks are empty, @{term \<open>ol!v = oh!v \<and> il!v = ih!v\<close>}).  Kept as a
      plain @{const filter}, but wrapped in an \<open>edged_lst\<close> constant so the loop refinements can
      carry it \<^emph>\<open>opaquely\<close> (otherwise \<open>sep_auto\<close> peels the range and explodes).\<close>
definition edged_lst :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "edged_lst ol oh il ih v n = filter (\<lambda>w. \<not> (ol ! w = oh ! w \<and> il ! w = ih ! w)) [v..<Suc n]"

lemma edged_lst_Cons:
  assumes "v \<le> n"
  shows "edged_lst ol oh il ih v n
       = (if ol ! v = oh ! v \<and> il ! v = ih ! v then [] else [v]) @ edged_lst ol oh il ih (Suc v) n"
proof -
  have vsn: "v < Suc n" using assms by simp
  show ?thesis unfolding edged_lst_def by (subst upt_conv_Cons[OF vsn]) simp
qed

lemma edged_lst_empty: "n < v \<Longrightarrow> edged_lst ol oh il ih v n = []"
  by (simp add: edged_lst_def)

text \<open>@{const count_edged_imp} counts the non-lonely vertices — the length of \<open>edged_lst\<close>.\<close>
lemma count_edged_imp_rule:
  "v \<le> Suc n \<Longrightarrow> Suc n \<le> length ol \<Longrightarrow> Suc n \<le> length oh \<Longrightarrow> Suc n \<le> length il \<Longrightarrow> Suc n \<le> length ih \<Longrightarrow>
   <olo \<mapsto>\<^sub>a ol * ohi \<mapsto>\<^sub>a oh * ilo \<mapsto>\<^sub>a il * ihi \<mapsto>\<^sub>a ih>
     count_edged_imp olo ohi ilo ihi v n acc
   <\<lambda>r. olo \<mapsto>\<^sub>a ol * ohi \<mapsto>\<^sub>a oh * ilo \<mapsto>\<^sub>a il * ihi \<mapsto>\<^sub>a ih
        * \<up>(r = acc + length (edged_lst ol oh il ih v n))>"
proof (induction "Suc n - v" arbitrary: v acc)
  case 0
  then have vg: "n < v" by simp
  then show ?case by (subst count_edged_imp.simps) (sep_auto simp: edged_lst_empty[OF vg])
next
  case (Suc d)
  from Suc.hyps(2) Suc.prems(1) have vn: "v \<le> n" by simp
  from vn have vl: "v < length ol" "v < length oh" "v < length il" "v < length ih"
    using Suc.prems(2,3,4,5) by auto
  have d': "d = Suc n - Suc v" using Suc.hyps(2) by simp
  have step: "<olo \<mapsto>\<^sub>a ol * ohi \<mapsto>\<^sub>a oh * ilo \<mapsto>\<^sub>a il * ihi \<mapsto>\<^sub>a ih>
     count_edged_imp olo ohi ilo ihi (Suc v) n (if ol ! v = oh ! v \<and> il ! v = ih ! v then acc else Suc acc)
   <\<lambda>r. olo \<mapsto>\<^sub>a ol * ohi \<mapsto>\<^sub>a oh * ilo \<mapsto>\<^sub>a il * ihi \<mapsto>\<^sub>a ih
        * \<up>(r = (if ol ! v = oh ! v \<and> il ! v = ih ! v then acc else Suc acc)
                + length (edged_lst ol oh il ih (Suc v) n))>"
    by (rule Suc.hyps(1)[OF d' _ Suc.prems(2,3,4,5)]) (use vn in simp)
  have feq: "acc + length (edged_lst ol oh il ih v n)
           = (if ol ! v = oh ! v \<and> il ! v = ih ! v then acc else Suc acc) + length (edged_lst ol oh il ih (Suc v) n)"
    by (simp add: edged_lst_Cons[OF vn])
  show ?case
    using vl vn
    apply (subst count_edged_imp.simps)
    by (sep_auto heap: step simp: feq)
qed

text \<open>@{const fill_edged_imp} writes the non-lonely vertices — @{term \<open>edged_lst ol oh il ih v n\<close>} —
      into \<open>vl\<close> starting at index @{term j}, leaving the rest of the array untouched.  Proved \<^emph>\<open>without\<close> an Isar
      case-split on lonely/non-lonely: splitting makes @{method sep_auto} explore the unreachable
      branch (whose recursive call has no rule) and loop; giving it the general induction hypothesis as
      the heap rule instead lets it discharge both branches' preconditions from the \<open>if\<close>-guard.\<close>
lemma fill_edged_imp_rule:
  "v \<le> Suc n \<Longrightarrow> Suc n \<le> length ol \<Longrightarrow> Suc n \<le> length oh \<Longrightarrow> Suc n \<le> length il \<Longrightarrow> Suc n \<le> length ih \<Longrightarrow>
   j + length (edged_lst ol oh il ih v n) \<le> length vlst \<Longrightarrow>
   <va \<mapsto>\<^sub>a vlst * olo \<mapsto>\<^sub>a ol * ohi \<mapsto>\<^sub>a oh * ilo \<mapsto>\<^sub>a il * ihi \<mapsto>\<^sub>a ih>
     fill_edged_imp va olo ohi ilo ihi v n j
   <\<lambda>_. va \<mapsto>\<^sub>a (take j vlst @ edged_lst ol oh il ih v n @ drop (j + length (edged_lst ol oh il ih v n)) vlst)
        * olo \<mapsto>\<^sub>a ol * ohi \<mapsto>\<^sub>a oh * ilo \<mapsto>\<^sub>a il * ihi \<mapsto>\<^sub>a ih>"
proof (induction "Suc n - v" arbitrary: v j vlst)
  case 0
  then have vg: "n < v" by simp
  then show ?case by (subst fill_edged_imp.simps) (sep_auto simp: edged_lst_empty[OF vg])
next
  case (Suc d)
  from Suc.hyps(2) Suc.prems(1) have vn: "v \<le> n" by simp
  hence nnv: "\<not> n < v" by simp
  from vn have vl: "v < length ol" "v < length oh" "v < length il" "v < length ih"
    using Suc.prems(2,3,4,5) by auto
  have d': "d = Suc n - Suc v" using Suc.hyps(2) by simp
  note ec = edged_lst_Cons[OF vn]
  show ?case
    using vl nnv Suc.prems(2,3,4,5,6)
    apply (subst fill_edged_imp.simps)
    by (sep_auto heap: Suc.hyps(1)[OF d']
                 simp: ec take_Suc_conv_app_nth list_update_append drop_update_cancel)
qed

section \<open>Bridging the built CSRs to the functional @{const initial_basis_code_spec.out_csr} / @{const initial_basis_code_spec.in_csr}\<close>

text \<open>The functional @{const initial_basis_code_spec.build_two_csr} folds a \<^emph>\<open>pair\<close> of counters / edge
      arrays in one pass; projecting to a component is an ordinary fold fusion.  With it, the outgoing
      / ingoing CSRs the imperative builder produces (keyed on @{term fst_list} / @{term snd_list}) are
      literally @{const initial_basis_code_spec.out_csr} / @{const initial_basis_code_spec.in_csr}.\<close>

lemma fold_pair_fst: "fst (fold (\<lambda>e (x,y). (f e x, g e y)) es st) = fold f es (fst st)"
  by (induction es arbitrary: st) (auto split: prod.splits)
lemma fold_pair_snd: "snd (fold (\<lambda>e (x,y). (f e x, g e y)) es st) = fold g es (snd st)"
  by (induction es arbitrary: st) (auto split: prod.splits)

context initial_basis_code_spec
begin

lemma out_csr_lo: "csr_lo out_csr = butlast (psums 0 (ct vcount ((!) fst_list) [0..<m]))"
  by (simp add: out_csr_def two_csr_def build_two_csr_def Let_def fold_pair_fst ct_def[symmetric] edge_csr.make_def)
lemma out_csr_hi: "csr_hi out_csr = tl (psums 0 (ct vcount ((!) fst_list) [0..<m]))"
  by (simp add: out_csr_def two_csr_def build_two_csr_def Let_def fold_pair_fst ct_def[symmetric] edge_csr.make_def)
lemma out_csr_cur: "csr_cur out_csr = butlast (psums 0 (ct vcount ((!) fst_list) [0..<m]))"
  by (simp add: out_csr_def two_csr_def build_two_csr_def Let_def fold_pair_fst ct_def[symmetric] edge_csr.make_def)
lemma out_csr_edges: "csr_edges out_csr = scatter_edges vcount ((!) fst_list) [0..<m] 0"
  by (simp add: out_csr_def two_csr_def build_two_csr_def Let_def fold_pair_fst ct_def[symmetric] scatter_edges_def edge_csr.make_def)

lemma in_csr_lo: "csr_lo in_csr = butlast (psums 0 (ct vcount ((!) snd_list) [0..<m]))"
  by (simp add: in_csr_def two_csr_def build_two_csr_def Let_def fold_pair_snd ct_def[symmetric] edge_csr.make_def)
lemma in_csr_hi: "csr_hi in_csr = tl (psums 0 (ct vcount ((!) snd_list) [0..<m]))"
  by (simp add: in_csr_def two_csr_def build_two_csr_def Let_def fold_pair_snd ct_def[symmetric] edge_csr.make_def)
lemma in_csr_cur: "csr_cur in_csr = butlast (psums 0 (ct vcount ((!) snd_list) [0..<m]))"
  by (simp add: in_csr_def two_csr_def build_two_csr_def Let_def fold_pair_snd ct_def[symmetric] edge_csr.make_def)
lemma in_csr_edges: "csr_edges in_csr = scatter_edges vcount ((!) snd_list) [0..<m] 0"
  by (simp add: in_csr_def two_csr_def build_two_csr_def Let_def fold_pair_snd ct_def[symmetric] scatter_edges_def edge_csr.make_def)

text \<open>Hence the two imperative CSR builds establish the abstract @{const csr_assn} of the outgoing /
      ingoing CSRs — exactly the graph assertion the acyclifier refinement consumes.\<close>
lemma build_csr_out_rule:
  assumes "m \<le> length fst_list" "\<forall>i<m. fst_list ! i < vcount"
  shows "<ka \<mapsto>\<^sub>a fst_list * c \<mapsto>\<^sub>a replicate vcount 0 * o_lo \<mapsto>\<^sub>a replicate vcount 0 * o_hi \<mapsto>\<^sub>a replicate vcount 0 * o_cur \<mapsto>\<^sub>a replicate vcount 0 * o_edges \<mapsto>\<^sub>a replicate m 0>
     build_csr_imp ka c o_lo o_hi o_cur o_edges m vcount
   <\<lambda>_. ka \<mapsto>\<^sub>a fst_list * c \<mapsto>\<^sub>a ct vcount ((!) fst_list) [0..<m] * csr_assn out_csr (o_edges, o_lo, o_hi, o_cur)>"
  by (sep_auto heap: build_csr_imp_rule[OF assms]
               simp: csr_assn_def out_csr_edges out_csr_lo out_csr_hi out_csr_cur)

lemma build_csr_in_rule:
  assumes "m \<le> length snd_list" "\<forall>i<m. snd_list ! i < vcount"
  shows "<ka \<mapsto>\<^sub>a snd_list * c \<mapsto>\<^sub>a replicate vcount 0 * i_lo \<mapsto>\<^sub>a replicate vcount 0 * i_hi \<mapsto>\<^sub>a replicate vcount 0 * i_cur \<mapsto>\<^sub>a replicate vcount 0 * i_edges \<mapsto>\<^sub>a replicate m 0>
     build_csr_imp ka c i_lo i_hi i_cur i_edges m vcount
   <\<lambda>_. ka \<mapsto>\<^sub>a snd_list * c \<mapsto>\<^sub>a ct vcount ((!) snd_list) [0..<m] * csr_assn in_csr (i_edges, i_lo, i_hi, i_cur)>"
  by (sep_auto heap: build_csr_imp_rule[OF assms]
               simp: csr_assn_def in_csr_edges in_csr_lo in_csr_hi in_csr_cur)

text \<open>The edged-vertex loops compute exactly @{const edged_vs_list}: @{const edged_lst} on the CSR
      block boundaries (@{term out_lo} \<dots> @{term in_hi}) is the non-lonely filter of @{term vs_list}.\<close>
lemma edged_lst_eq_vs_list: "edged_lst out_lo out_hi in_lo in_hi (Suc 0) n = edged_vs_list"
  by (simp add: edged_lst_def edged_vs_list_def is_lonely_def vs_list_def)

end

text \<open>The imperative refinement of the functional orchestrator @{const initial_basis_code_spec.solve}.
      All working arrays are allocated \<^emph>\<open>once\<close> here and threaded through the phases, reusing memory
      wherever the functional code does: the two CSRs are built once and repurposed by Pass A; the
      acyclifier's DFS stacks @{term vst} / @{term est} are handed on as the tree-builder's stack and
      then as the network-simplex path buffers.  The augmented endpoint / capacity / flow / edge-state
      arrays have length @{term \<open>m + n\<close>} (the artificial-edge count @{term Kart} is at most @{term n});
      their first @{term m} cells are copied from the input.

      The phases: build the CSRs; acyclify the flow (an @{term unbounded} answer is a negative
      infinite-capacity cycle, @{term NegInfCycleF}); reset the cursors and run Pass A + the imbalance
      transform; build the strongly-feasible spanning tree; run the network-simplex loop (an
      @{term unbounded} verdict is again @{term NegInfCycleF}); on a bounded optimum inspect the
      artificial edges @{term \<open>[m..<m + Kart]\<close>} — all-zero means the minimum-cost @{term b}-flow is left
      in the first @{term m} flow cells (@{term OptimalF}), otherwise the instance is infeasible
      (@{term InfeasibleF}).\<close>
definition solve_imp ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat
   \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> 'n::{heap,linordered_idom} array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array
   \<Rightarrow> solve_status Heap" where
  "solve_imp n m block_size min_cand max_cand in_fst in_snd in_cap in_cost in_flow in_b =
     (let vcount = Suc n; V = Suc vcount; mn = m + n
      in do {
        fst_arr  \<leftarrow> Array.new mn 0;   _ \<leftarrow> arr_copy_imp in_fst  fst_arr  0 m;
        snd_arr  \<leftarrow> Array.new mn 0;   _ \<leftarrow> arr_copy_imp in_snd  snd_arr  0 m;
        cap_arr  \<leftarrow> Array.new mn 0;   _ \<leftarrow> arr_copy_imp in_cap  cap_arr  0 m;
        flow_arr \<leftarrow> Array.new mn 0;   _ \<leftarrow> arr_copy_imp in_flow flow_arr 0 m;
        es_arr   \<leftarrow> Array.new mn InL;
        pot_arr \<leftarrow> Array.new V pval_zero;
        prnt \<leftarrow> Array.new V 0; thrd \<leftarrow> Array.new V 0; rvth \<leftarrow> Array.new V 0;
        lsuc \<leftarrow> Array.new V 0; snum \<leftarrow> Array.new V 0; aux \<leftarrow> Array.new V 0;
        par \<leftarrow> Array.new V 0; dir \<leftarrow> Array.new V False;
        state_arr \<leftarrow> Array.new V Unseen; exc_arr \<leftarrow> Array.new V 0;
        cnt \<leftarrow> Array.new V 0;
        o_edges \<leftarrow> Array.new m 0; o_lo \<leftarrow> Array.new vcount 0; o_hi \<leftarrow> Array.new vcount 0; o_cur \<leftarrow> Array.new vcount 0;
        i_edges \<leftarrow> Array.new m 0; i_lo \<leftarrow> Array.new vcount 0; i_hi \<leftarrow> Array.new vcount 0; i_cur \<leftarrow> Array.new vcount 0;
        vst \<leftarrow> Array.new V 0; est \<leftarrow> Array.new V 0; dst \<leftarrow> Array.new V False;
        \<comment> \<open>@{term cnt} is freshly zeroed by @{term \<open>Array.new V 0\<close>}, so the first CSR build needs no
             zeroing pass; only the second build re-zeroes it.\<close>
        _ \<leftarrow> build_csr_imp fst_arr cnt o_lo o_hi o_cur o_edges m vcount;
        _ \<leftarrow> arr_fill_imp cnt 0 0 vcount;
        _ \<leftarrow> build_csr_imp snd_arr cnt i_lo i_hi i_cur i_edges m vcount;
        k \<leftarrow> count_edged_imp o_lo o_hi i_lo i_hi 1 n 0;
        vl \<leftarrow> Array.new k 0;
        _ \<leftarrow> fill_edged_imp vl o_lo o_hi i_lo i_hi 1 n 0;
        pr \<leftarrow> ref 0;
        ubd \<leftarrow> make_acyclic_prog cap_arr in_cost fst_arr snd_arr flow_arr state_arr
                (o_edges, o_lo, o_hi, o_cur) (i_edges, i_lo, i_hi, i_cur) (vl, pr) vst est dst;
        (if ubd then return NegInfCycleF
         else do {
           _ \<leftarrow> arr_copy_imp o_lo o_cur 0 vcount;
           _ \<leftarrow> arr_copy_imp i_lo i_cur 0 vcount;
           _ \<leftarrow> passA_imp flow_arr cap_arr fst_arr snd_arr es_arr exc_arr o_edges o_cur i_edges i_cur 0 m;
           _ \<leftarrow> imbalance_imp exc_arr in_b 0 vcount;
           \<comment> \<open>Reuse the acyclifier's (now dead) DFS stack @{term dst} as the tree-builder's ``seen''
              array; it must be all-@{term False} for the build.  Likewise @{term cnt} (dead since the
              CSR build) becomes the DFS in-cursor stack @{term di_sic} — no reset needed there, as every
              stack slot is written before it is read.\<close>
           _ \<leftarrow> arr_fill_imp dst False 0 V;
           sp_ref \<leftarrow> ref 0; prev_ref \<leftarrow> ref 0; nxt_ref \<leftarrow> ref 0;
           (let tree = \<lparr> prnt_impl = prnt, thrd_impl = thrd, rvth_impl = rvth,
                         lsuc_impl = lsuc, snum_impl = snum, aux_impl = aux \<rparr>;
                st = \<lparr> di_seen = dst, di_tree = tree, di_par = par, di_dir = dir, di_pot = pot_arr,
                      di_fst = fst_arr, di_snd = snd_arr, di_cap = cap_arr, di_cost = in_cost,
                      di_flow = flow_arr, di_es = es_arr, di_oe = o_edges, di_olo = o_lo, di_ohi = o_cur,
                      di_ie = i_edges, di_ilo = i_lo, di_ihi = i_cur, di_sv = vst, di_soc = est,
                      di_sic = cnt, di_sp = sp_ref, di_prev = prev_ref, di_nxt = nxt_ref \<rparr>
            in do {
              _ \<leftarrow> build_tree_imp st exc_arr o_hi i_hi m vcount n;
              Kart \<leftarrow> Ref.lookup nxt_ref;
              (let marc = m + Kart
               in do {
                 sel_arr \<leftarrow> Array.new max_cand 0; scur \<leftarrow> ref 0; slen \<leftarrow> ref 0;
                 (let state = ns_impl_state.make flow_arr pot_arr tree par dir es_arr
                                (sel_arr, scur, slen) vst est
                  in do {
                    res \<leftarrow> ns_loop_prog vcount m marc block_size min_cand max_cand
                                        fst_arr snd_arr in_cost cap_arr state;
                    (if res = Network_Simplex.unbounded then return NegInfCycleF
                     else do {
                       allz \<leftarrow> scan_art_imp flow_arr m marc;
                       (if allz
                        then do { _ \<leftarrow> arr_copy_imp flow_arr in_flow 0 m; return OptimalF }
                        else return InfeasibleF) }) }) }) }) }) })"

section \<open>Code generation for the whole solver\<close>

text \<open>Register the fixpoint equations of every recursive Heap sub-program the solver reaches: the
      materialisation / CSR loops of this theory, the abstract network-simplex loop of
      @{locale network_simplex_impl_spec}, and the arborescence-refinement loops.  The acyclifier's
      equations were registered above.  With these, @{const solve_imp} generates as self-contained
      imperative SML.\<close>

lemmas [code] =
  ns_loop_prog_def
  scan_art_imp.simps join_of_imp.simps scan_cache_imp.simps scan_imp.simps
  passA_imp.simps imbalance_imp.simps build_dfs_a_imp.simps phase1_imp.simps phase2_imp.simps
  arr_fill_imp.simps arr_copy_imp.simps csr_count_imp.simps csr_psum_imp.simps csr_scatter_imp.simps
  count_edged_imp.simps fill_edged_imp.simps
  initial_basis_code_spec.better.simps
  network_simplex_impl_spec.ns_select_imp_def network_simplex_impl_spec.res_fwd_imp_def
  network_simplex_impl_spec.res_bwd_imp_def network_simplex_impl_spec.par_edge_imp_def
  network_simplex_impl_spec.par_up_imp_def network_simplex_impl_spec.res_up_imp_def
  network_simplex_impl_spec.res_down_imp_def network_simplex_impl_spec.mininf_imp_def
  network_simplex_impl_spec.scan_up_loop_imp.simps network_simplex_impl_spec.scan_down_loop_imp.simps
  network_simplex_impl_spec.scan_up_imp_def network_simplex_impl_spec.scan_down_imp_def
  network_simplex_impl_spec.bottleneck_imp_def network_simplex_impl_spec.aug_loop_imp.simps
  network_simplex_impl_spec.augment_flow_imp_def network_simplex_impl_spec.ns_flip_imp_def
  network_simplex_impl_spec.reparent_walk_imp.simps network_simplex_impl_spec.reparent_imp_def
  network_simplex_impl_spec.ns_pivot_imp_def network_simplex_impl_spec.ns_loop_imp.simps
  stem_loop_imp.simps dirty_pass_imp.simps stem_num_loop_imp.simps
  fused_vin_loop_imp.simps fused_vout_loop_imp.simps join_paths_loop_imp.simps subtree_fold_imp.simps

export_code solve_imp checking SML_imp


(* \<midarrow>\<midarrow>\<midarrow> Example / demonstration programs (kept for reference; commented out) \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>

text \<open>A tiny sample run, in the style of the imperative-DFS example: two vertices \<open>0,1\<close> and one edge
      \<open>0 \<rightarrow> 1\<close> carrying flow \<open>3 \<le> 5\<close>.  There is no cycle, so the acyclifier returns @{term False}
      (bounded) and leaves the flow unchanged at \<open>[3]\<close>.  We assemble the arrays inside the Heap
      monad, run @{const make_acyclic_prog}, freeze the flow, and evaluate the whole run on the empty
      heap.\<close>

definition af_sample :: "(bool \<times> int list) Heap" where
  "af_sample = do {
     cap_arr   \<leftarrow> Array.of_list [5::int];
     cost_arr  \<leftarrow> Array.of_list [1::int];
     fst_arr   \<leftarrow> Array.of_list [0::nat];
     snd_arr   \<leftarrow> Array.of_list [1::nat];
     flow_arr  \<leftarrow> Array.of_list [3::int];
     state_arr \<leftarrow> Array.of_list [Unseen, Unseen];
     oe \<leftarrow> Array.of_list [0::nat]; olo \<leftarrow> Array.of_list [0::nat, 1];
     ohi \<leftarrow> Array.of_list [1::nat, 1]; ocur \<leftarrow> Array.of_list [0::nat, 1];
     ie \<leftarrow> Array.of_list [0::nat]; ilo \<leftarrow> Array.of_list [0::nat, 0];
     ihi \<leftarrow> Array.of_list [0::nat, 1]; icur \<leftarrow> Array.of_list [0::nat, 0];
     vl \<leftarrow> Array.of_list [0::nat, 1]; pr \<leftarrow> ref (0::nat);
     vst \<leftarrow> Array.of_list [0::nat, 0]; est \<leftarrow> Array.of_list [0::nat, 0];
     dst \<leftarrow> Array.of_list [False, False];
     ubd \<leftarrow> make_acyclic_prog cap_arr cost_arr fst_arr snd_arr flow_arr state_arr
             (oe, olo, ohi, ocur) (ie, ilo, ihi, icur) (vl, pr) vst est dst;
     f \<leftarrow> Array.freeze flow_arr;
     return (ubd, f) }"

text \<open>Running the exported code: @{term af_sample} is generated as an SML function \<open>unit \<Rightarrow> \<dots>\<close> (the
      native Imperative-HOL Heap model), so applying it to \<open>()\<close> actually executes it on a real
      mutable heap and returns the pair \<open>(unbounded-flag, resulting flow)\<close> — expected \<open>(false, [3])\<close>.\<close>

ML_val \<open>
  val (ubd, f) = @{code af_sample} ();
  writeln ("acyclifier sample run: unbounded = " ^ @{make_string} ubd
           ^ ", flow = " ^ @{make_string} f)
\<close>

text \<open>A CSR sample: vertex \<open>0\<close> owns the edge ids \<open>[10, 20]\<close>, vertex \<open>1\<close> owns \<open>[30]\<close>.  We read the
      current edge of vertex \<open>0\<close> (its \<^emph>\<open>next\<close>, i.e. first unconsumed, edge — expected \<open>10\<close>), advance
      its cursor with @{const csr_move_imp}, read the new current edge (\<open>20\<close>), and finally ask
      @{const csr_has_imp} whether vertex \<open>0\<close> still has an unconsumed edge (cursor \<open>1 < 2\<close> \<Rightarrow>
      @{term True}).\<close>

definition csr_sample :: "(nat \<times> nat \<times> bool) Heap" where
  "csr_sample = do {
     oe   \<leftarrow> Array.of_list [10, 20, 30 :: nat];
     olo  \<leftarrow> Array.of_list [0, 2 :: nat];
     ohi  \<leftarrow> Array.of_list [2, 3 :: nat];
     ocur \<leftarrow> Array.of_list [0, 2 :: nat];
     e1 \<leftarrow> csr_current_imp (oe, olo, ohi, ocur) 0;
     _  \<leftarrow> csr_move_imp    (oe, olo, ohi, ocur) 0;
     e2 \<leftarrow> csr_current_imp (oe, olo, ohi, ocur) 0;
     h  \<leftarrow> csr_has_imp     (oe, olo, ohi, ocur) 0;
     return (e1, e2, h) }"

ML_val \<open>
  val (e1, (e2, h)) = @{code csr_sample} ();
  writeln ("csr sample run: current edge of v0 = " ^ @{make_string} e1
           ^ ", after one move = " ^ @{make_string} e2
           ^ ", still has edge = " ^ @{make_string} h)
\<close>

text \<open>A \<^emph>\<open>cyclic\<close> flow, acyclified.  Three vertices \<open>0,1,2\<close> and a directed triangle
      \<open>0 \<rightarrow>\<^sup>0 1 \<rightarrow>\<^sup>1 2 \<rightarrow>\<^sup>2 0\<close> carrying flow \<open>[3, 5, 4]\<close>, all within capacity \<open>10\<close> at unit cost.  The
      flow's support is the whole cycle, so it is \<^emph>\<open>not\<close> acyclic.  @{const make_acyclic_prog} cancels
      the cycle — pushing the bottleneck \<open>3\<close> around it (reducing cost) — leaving an acyclic flow with
      the same vertex excesses (expected \<open>[0, 2, 1]\<close>), and reports @{term False} (bounded).\<close>

definition af_cycle_sample :: "(bool \<times> int list) Heap" where
  "af_cycle_sample = do {
     cap_arr   \<leftarrow> Array.of_list [10, 10, 10 :: int];
     cost_arr  \<leftarrow> Array.of_list [1, 1, 1 :: int];
     fst_arr   \<leftarrow> Array.of_list [0, 1, 2 :: nat];
     snd_arr   \<leftarrow> Array.of_list [1, 2, 0 :: nat];
     flow_arr  \<leftarrow> Array.of_list [3, 5, 4 :: int];
     state_arr \<leftarrow> Array.of_list [Unseen, Unseen, Unseen];
     oe \<leftarrow> Array.of_list [0, 1, 2 :: nat]; olo \<leftarrow> Array.of_list [0, 1, 2 :: nat];
     ohi \<leftarrow> Array.of_list [1, 2, 3 :: nat]; ocur \<leftarrow> Array.of_list [0, 1, 2 :: nat];
     ie \<leftarrow> Array.of_list [2, 0, 1 :: nat]; ilo \<leftarrow> Array.of_list [0, 1, 2 :: nat];
     ihi \<leftarrow> Array.of_list [1, 2, 3 :: nat]; icur \<leftarrow> Array.of_list [0, 1, 2 :: nat];
     vl \<leftarrow> Array.of_list [0, 1, 2 :: nat]; pr \<leftarrow> ref (0::nat);
     vst \<leftarrow> Array.of_list [0, 0, 0 :: nat]; est \<leftarrow> Array.of_list [0, 0, 0 :: nat];
     dst \<leftarrow> Array.of_list [False, False, False];
     ubd \<leftarrow> make_acyclic_prog cap_arr cost_arr fst_arr snd_arr flow_arr state_arr
             (oe, olo, ohi, ocur) (ie, ilo, ihi, icur) (vl, pr) vst est dst;
     f \<leftarrow> Array.freeze flow_arr;
     return (ubd, f) }"

ML_val \<open>
  val (ubd, f) = @{code af_cycle_sample} ();
  writeln ("cyclic acyclify: unbounded = " ^ @{make_string} ubd
           ^ ", acyclified flow = " ^ @{make_string} f)
\<close>

\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)

section \<open>Correctness of the imperative orchestrator\<close>

text \<open>The functional selector locale @{locale initial_basis_selector} fixes its value type only as
      @{class linordered_idom}, but the imperative @{const solve_imp} stores those values in
      @{typ \<open>'n array\<close>}s, which additionally requires @{class heap}.  A locale's fixed type parameter
      cannot be re-sorted after the fact, so we introduce the thin extension
      \<open>initial_basis_selector_heap\<close>: it \<^emph>\<open>is\<close> @{locale initial_basis_selector} — inheriting
      \<open>solve\<close>, @{thm [source] initial_basis_selector.solve_correct} and all the input lists —
      but re-declares @{typ 'n} at the stronger sort @{class heap} \<inter> @{class linordered_idom}.  All of
      this lives in the present theory; the functional development is untouched.

      Inside it the final refinement statement is a single Hoare triple: run on six input arrays
      holding the locale-fixed input lists, @{const solve_imp} returns the same verdict as the
      functional \<open>solve\<close> (under @{const status_of}), leaves the five read-only input arrays
      untouched, and — on @{const OptimalF} — leaves the minimum-cost @{term b}-flow in the first
      @{term m} cells of the flow array.  Composed with @{thm [source] initial_basis_selector.solve_correct}
      it certifies the executable solver end-to-end.\<close>

locale initial_basis_selector_heap =
  initial_basis_selector where capacity_list = capacity_list and h = h
  for capacity_list :: "('n :: {heap, linordered_idom}) list" and h :: "'n \<Rightarrow> real"
begin

subsection \<open>Layer (c): the imperative acyclifier refines @{const make_acyclic}\<close>

text \<open>The concrete assertions relating the functional stores to their imperative arrays.  The flow and
      vertex-state arrays are over-allocated (the flow array carries @{term n} spare artificial-edge
      cells, the state array one spare root cell), so the assertions pad the abstract list with an
      existential remainder; the graph assertion additionally pins the CSR vertex count to
      @{term vcount}, which is exactly the information the \<^emph>\<open>unguarded\<close> imperative iterator reads need
      (a vertex \<open>v \<in> \<V>\<close> satisfies \<open>v < vcount\<close>, which equals \<open>csr_n G\<close>).\<close>

definition flow_assn_m :: "'n list \<Rightarrow> 'n array \<Rightarrow> assn" where
  "flow_assn_m fl ha = (\<exists>\<^sub>A r. ha \<mapsto>\<^sub>a (fl @ r) * \<up>(length r = n))"

definition state_assn_v :: "vertex_state list \<Rightarrow> vertex_state array \<Rightarrow> assn" where
  "state_assn_v st ha = (\<exists>\<^sub>A r. ha \<mapsto>\<^sub>a (st @ r) * \<up>(length r = Suc 0))"

definition graph_assn_c :: "nat edge_csr \<Rightarrow> nat csr_imp \<Rightarrow> assn" where
  "graph_assn_c C ha = csr_assn C ha * \<up>(csr_n C = vcount)"

text \<open>A remaining region is nonempty exactly when the vertex is in range and its cursor is below its
      upper bound; this bridges the abstract @{term \<open>csr_remaining C v \<noteq> {}\<close>} premise of the
      current / move iterator laws to the concrete bounds their imperative reads need.\<close>
lemma csr_rem_bounds:
  "csr_remaining C v \<noteq> {} \<Longrightarrow> v < csr_n C \<and> csr_cur C ! v < csr_hi C ! v"
  by (auto simp: csr_remaining_def csr_seg_rm_def split: if_splits)

lemma vtx_rem_pos:
  assumes "vtx_remaining Vit \<noteq> {}"
  shows "vi_pos Vit < length (vi_list Vit)"
proof -
  have "drop (vi_pos Vit) (vi_list Vit) \<noteq> []"
    using assms by (auto simp: vtx_remaining_def)
  thus ?thesis by (metis drop_eq_Nil not_le)
qed

text \<open>The nineteen per-operation Hoare triples that the acyclifier refinement locale assumes, each
      proved for the concrete arrays.  The flow / state store reads and writes are plain array
      operations on the padded assertions; the CSR iterator reads use @{thm [source] graph_assn_c_def}
      to recover the vertex-count bound; the vertex-iterator reads use @{thm [source] vtx_rem_pos}.\<close>

lemma flow_lookup_rule_c:
  "\<lbrakk>length Fl = m; e \<in> {0..<m}\<rbrakk> \<Longrightarrow>
   <flow_assn_m Fl fh> Array.nth fh e <\<lambda>r. flow_assn_m Fl fh * \<up>(r = Fl ! e)>"
  unfolding flow_assn_m_def by (sep_auto simp: nth_append)

lemma flow_upd_rule_c:
  "\<lbrakk>length Fl = m; e \<in> {0..<m}\<rbrakk> \<Longrightarrow>
   <flow_assn_m Fl fh> arr_upd fh e w <\<lambda>_. flow_assn_m (Fl[e := w]) fh>"
  unfolding flow_assn_m_def arr_upd_def by (sep_auto simp: list_update_append)

lemma state_lookup_rule_c:
  "\<lbrakk>\<forall>v\<in>original_network.\<V>. v < length St; v \<in> original_network.\<V>\<rbrakk> \<Longrightarrow>
   <state_assn_v St sh> Array.nth sh v <\<lambda>r. state_assn_v St sh * \<up>(r = St ! v)>"
  unfolding state_assn_v_def by (sep_auto simp: nth_append)

lemma state_upd_rule_c:
  "\<lbrakk>\<forall>v\<in>original_network.\<V>. v < length St; v \<in> original_network.\<V>\<rbrakk> \<Longrightarrow>
   <state_assn_v St sh> arr_upd sh v q <\<lambda>_. state_assn_v (St[v := q]) sh>"
  unfolding state_assn_v_def arr_upd_def by (sep_auto simp: list_update_append)

lemma csr_has_rule_c:
  assumes "csr_invar G" "v \<in> original_network.\<V>"
  shows "<graph_assn_c G gh> csr_has_imp gh v <\<lambda>r. graph_assn_c G gh * \<up>(r = csr_has G v)>"
proof -
  have "v < vcount" using assms(2) by (rule V_lt_vcount)
  thus ?thesis unfolding graph_assn_c_def by (sep_auto heap: csr_has_imp_rule[OF assms(1)])
qed

lemma csr_reset_rule_c:
  assumes "csr_invar G" "v \<in> original_network.\<V>"
  shows "<graph_assn_c G gh> csr_reset_imp gh v <\<lambda>_. graph_assn_c (csr_reset G v) gh>"
proof -
  have "v < vcount" using assms(2) by (rule V_lt_vcount)
  thus ?thesis unfolding graph_assn_c_def by (sep_auto heap: csr_reset_imp_rule[OF assms(1)])
qed

lemma csr_current_rule_c:
  assumes "csr_invar G" "v \<in> original_network.\<V>" "csr_remaining G v \<noteq> {}"
  shows "<graph_assn_c G gh> csr_current_imp gh v <\<lambda>r. graph_assn_c G gh * \<up>(r = csr_current G v)>"
proof -
  have b: "v < csr_n G" "csr_cur G ! v < csr_hi G ! v" using csr_rem_bounds[OF assms(3)] by auto
  show ?thesis unfolding graph_assn_c_def by (sep_auto heap: csr_current_imp_rule[OF assms(1) b])
qed

lemma csr_move_rule_c:
  assumes "csr_invar G" "v \<in> original_network.\<V>" "csr_remaining G v \<noteq> {}"
  shows "<graph_assn_c G gh> csr_move_imp gh v <\<lambda>_. graph_assn_c (csr_move G v) gh>"
proof -
  have b: "v < csr_n G" "csr_cur G ! v < csr_hi G ! v" using csr_rem_bounds[OF assms(3)] by auto
  show ?thesis unfolding graph_assn_c_def by (sep_auto heap: csr_move_imp_rule[OF assms(1) b])
qed

lemma vtx_has_rule_c:
  "vtx_invar Vit \<Longrightarrow> <vtx_assn Vit vh> vtx_has_imp vh <\<lambda>r. vtx_assn Vit vh * \<up>(r = vtx_has Vit)>"
  by (sep_auto heap: vtx_has_imp_rule)

lemma vtx_move_rule_c:
  "\<lbrakk>vtx_invar Vit; vtx_remaining Vit \<noteq> {}\<rbrakk> \<Longrightarrow> <vtx_assn Vit vh> vtx_move_imp vh <\<lambda>_. vtx_assn (vtx_move Vit) vh>"
  by (sep_auto heap: vtx_move_imp_rule)

lemma vtx_current_rule_c:
  assumes "vtx_invar Vit" "vtx_remaining Vit \<noteq> {}"
  shows "<vtx_assn Vit vh> vtx_current_imp vh <\<lambda>r. vtx_assn Vit vh * \<up>(r = vtx_current Vit)>"
  using vtx_rem_pos[OF assms(2)] by (sep_auto heap: vtx_current_imp_rule)

text \<open>\<^emph>\<open>Layer (c) target.\<close>  Interpreting the acyclifier refinement proof locale at the concrete
      CSR / array / vertex operations turns @{thm [source] acyclic_flow_impl_refine_proof.make_acyclic_imp_rule}
      into a Hoare triple for the executable @{const make_acyclic_prog}: it leaves the flow array holding
      the functional @{const make_acyclic} result and returns @{term True} exactly on the unbounded
      (@{term None}) verdict.  The functional @{locale acyclic_flow_impl} half of the locale is discharged
      automatically from the standing sublocale; only the nineteen imperative refinement triples remain,
      supplied by the lemmas above and the four per-edge reads below.\<close>
lemma make_acyclic_prog_rule:
  fixes cap_arr cost_arr :: "'n array" and fst_arr snd_arr :: "nat array"
    and fh :: "'n array" and sh :: "vertex_state array" and oh ih :: "nat csr_imp"
    and vih :: "nat vtx_imp" and vst est :: "nat array" and dst :: "bool array"
    and cl co :: "'n list" and fla sla :: "nat list" and f0 :: "'n list"
    and vs0 es0 :: "nat list" and ds0 :: "bool list"
  assumes cl_len: "m \<le> length cl" and cl_eq: "\<And>e. e < m \<Longrightarrow> cl ! e = capacity_list ! e"
      and co_len: "m \<le> length co" and co_eq: "\<And>e. e < m \<Longrightarrow> co ! e = cost_list ! e"
      and fla_len: "m \<le> length fla" and fla_eq: "\<And>e. e < m \<Longrightarrow> fla ! e = fst_list ! e"
      and sla_len: "m \<le> length sla" and sla_eq: "\<And>e. e < m \<Longrightarrow> sla ! e = snd_list ! e"
      and ff: "length f0 = m" and feas: "af_cap_feasible f0"
      and cvs: "card original_network.\<V> \<le> length vs0"
      and ces: "card original_network.\<V> \<le> length es0"
      and cds: "card original_network.\<V> \<le> length ds0"
  shows "<flow_assn_m f0 fh * state_assn_v (replicate vcount Unseen) sh * graph_assn_c out_csr oh *
          graph_assn_c in_csr ih * vtx_assn \<lparr>vi_list = edged_vs_list, vi_pos = 0\<rparr> vih *
          (cap_arr \<mapsto>\<^sub>a cl * cost_arr \<mapsto>\<^sub>a co * fst_arr \<mapsto>\<^sub>a fla * snd_arr \<mapsto>\<^sub>a sla) *
          vst \<mapsto>\<^sub>a vs0 * est \<mapsto>\<^sub>a es0 * dst \<mapsto>\<^sub>a ds0>
         make_acyclic_prog cap_arr cost_arr fst_arr snd_arr fh sh oh ih vih vst est dst
        <\<lambda>r. \<exists>\<^sub>A f' C_o C_i. flow_assn_m f' fh *
             graph_assn_c C_o oh * graph_assn_c C_i ih *
             (cap_arr \<mapsto>\<^sub>a cl * cost_arr \<mapsto>\<^sub>a co * fst_arr \<mapsto>\<^sub>a fla * snd_arr \<mapsto>\<^sub>a sla) *
             (\<exists>\<^sub>A vl el dl. vst \<mapsto>\<^sub>a vl * est \<mapsto>\<^sub>a el * dst \<mapsto>\<^sub>a dl *
                \<up>(card original_network.\<V> \<le> length vl \<and> card original_network.\<V> \<le> length el \<and> card original_network.\<V> \<le> length dl \<and>
                  length vl = length vs0 \<and> length el = length es0 \<and> length dl = length ds0)) *
             true *
             \<up>(csr_edges C_o = csr_edges out_csr \<and> csr_lo C_o = csr_lo out_csr \<and> csr_hi C_o = csr_hi out_csr \<and> csr_n C_o = vcount \<and>
               csr_edges C_i = csr_edges in_csr \<and> csr_lo C_i = csr_lo in_csr \<and> csr_hi C_i = csr_hi in_csr \<and> csr_n C_i = vcount \<and>
               (r \<longleftrightarrow> make_acyclic f0 = None) \<and> (make_acyclic f0 = None \<or> make_acyclic f0 = Some f'))>"
proof -
  have capr: "e \<in> {0..<m} \<Longrightarrow> <cap_arr \<mapsto>\<^sub>a cl * cost_arr \<mapsto>\<^sub>a co * fst_arr \<mapsto>\<^sub>a fla * snd_arr \<mapsto>\<^sub>a sla>
      Array.nth cap_arr e
    <\<lambda>r. (cap_arr \<mapsto>\<^sub>a cl * cost_arr \<mapsto>\<^sub>a co * fst_arr \<mapsto>\<^sub>a fla * snd_arr \<mapsto>\<^sub>a sla) * \<up>(r = capacity_list ! e)>" for e
    using cl_len cl_eq by sep_auto
  have costr: "e \<in> {0..<m} \<Longrightarrow> <cap_arr \<mapsto>\<^sub>a cl * cost_arr \<mapsto>\<^sub>a co * fst_arr \<mapsto>\<^sub>a fla * snd_arr \<mapsto>\<^sub>a sla>
      Array.nth cost_arr e
    <\<lambda>r. (cap_arr \<mapsto>\<^sub>a cl * cost_arr \<mapsto>\<^sub>a co * fst_arr \<mapsto>\<^sub>a fla * snd_arr \<mapsto>\<^sub>a sla) * \<up>(r = cost_list ! e)>" for e
    using co_len co_eq by sep_auto
  have fstr: "e \<in> {0..<m} \<Longrightarrow> <cap_arr \<mapsto>\<^sub>a cl * cost_arr \<mapsto>\<^sub>a co * fst_arr \<mapsto>\<^sub>a fla * snd_arr \<mapsto>\<^sub>a sla>
      Array.nth fst_arr e
    <\<lambda>r. (cap_arr \<mapsto>\<^sub>a cl * cost_arr \<mapsto>\<^sub>a co * fst_arr \<mapsto>\<^sub>a fla * snd_arr \<mapsto>\<^sub>a sla) * \<up>(r = fst_list ! e)>" for e
    using fla_len fla_eq by sep_auto
  have sndr: "e \<in> {0..<m} \<Longrightarrow> <cap_arr \<mapsto>\<^sub>a cl * cost_arr \<mapsto>\<^sub>a co * fst_arr \<mapsto>\<^sub>a fla * snd_arr \<mapsto>\<^sub>a sla>
      Array.nth snd_arr e
    <\<lambda>r. (cap_arr \<mapsto>\<^sub>a cl * cost_arr \<mapsto>\<^sub>a co * fst_arr \<mapsto>\<^sub>a fla * snd_arr \<mapsto>\<^sub>a sla) * \<up>(r = snd_list ! e)>" for e
    using sla_len sla_eq by sep_auto
  interpret acycR: acyclic_flow_impl_refine_proof
    where fst = "\<lambda>e. if e < m then fst_list ! e else Product_Type.fst (prod_decode (e - m))"
      and snd = "\<lambda>e. if e < m then snd_list ! e else Product_Type.snd (prod_decode (e - m))"
      and \<E> = "{0..<m}"
      and create_edge = "\<lambda>u v. m + prod_encode (u, v)"
      and \<u> = "\<lambda>e. if e < m then (if capacity_list ! e = - 1 then \<infinity> else ereal (h (capacity_list ! e))) else \<infinity>"
      and \<c> = "\<lambda>e. h (cost_list ! e)"
      and out_invar = csr_invar and out_abstract = csr_abstract and out_current = csr_current
      and out_has = csr_has and out_iterated = csr_iterated and out_remaining = csr_remaining
      and out_move = csr_move and out_reset = csr_reset
      and in_invar = csr_invar and in_abstract = csr_abstract and in_current = csr_current
      and in_has = csr_has and in_iterated = csr_iterated and in_remaining = csr_remaining
      and in_move = csr_move and in_reset = csr_reset
      and flow_invar = "\<lambda>xs. length xs = m" and flow_upd = list_update and flow_lookup = nth
      and st_invar = "\<lambda>xs. \<forall>v\<in>original_network.\<V>. v < length xs" and st_upd = list_update and st_lookup = nth
      and vit_invar = vtx_invar and vit_abstract = vtx_abstract and current_vertex = vtx_current
      and has_vertex = vtx_has and vit_iterated = vtx_iterated and vit_remaining = vtx_remaining
      and move_on_vertex = vtx_move
      and out_arr = out_csr and in_arr = in_csr
      and all_vertices = "\<lparr> vi_list = edged_vs_list, vi_pos = 0 \<rparr>"
      and cap = "\<lambda>e. capacity_list ! e" and cost = "\<lambda>e. cost_list ! e" and h = "h :: 'n \<Rightarrow> real"
      and state_init = "replicate vcount Unseen"
      and fst_exec = "\<lambda>e. fst_list ! e" and snd_exec = "\<lambda>e. snd_list ! e"
      and out_current_imp = csr_current_imp and out_has_imp = csr_has_imp
      and out_move_imp = csr_move_imp and out_reset_imp = csr_reset_imp
      and in_current_imp = csr_current_imp and in_has_imp = csr_has_imp
      and in_move_imp = csr_move_imp and in_reset_imp = csr_reset_imp
      and flow_upd_imp = arr_upd and flow_lookup_imp = Array.nth
      and st_upd_imp = arr_upd and st_lookup_imp = Array.nth
      and current_vertex_imp = vtx_current_imp and has_vertex_imp = vtx_has_imp
      and move_on_vertex_imp = vtx_move_imp
      and cap_imp = "\<lambda>e. Array.nth cap_arr e" and cost_imp = "\<lambda>e. Array.nth cost_arr e"
      and fst_exec_imp = "\<lambda>e. Array.nth fst_arr e" and snd_exec_imp = "\<lambda>e. Array.nth snd_arr e"
      and flow_assn = flow_assn_m and state_assn = state_assn_v
      and graph_assn = graph_assn_c and vit_assn = vtx_assn
      and rd = "cap_arr \<mapsto>\<^sub>a cl * cost_arr \<mapsto>\<^sub>a co * fst_arr \<mapsto>\<^sub>a fla * snd_arr \<mapsto>\<^sub>a sla"
      and Lvst = "length vs0" and Lest = "length es0" and Ldst = "length ds0"
    apply intro_locales
    apply (rule acyclic_flow_impl_refine_proof_axioms.intro)
    apply (rule flow_lookup_rule_c; assumption)
    apply (rule flow_upd_rule_c; assumption)
    apply (rule state_lookup_rule_c; assumption)
    apply (rule state_upd_rule_c; assumption)
    apply (rule csr_has_rule_c; assumption)
    apply (rule csr_current_rule_c; assumption)
    apply (rule csr_move_rule_c; assumption)
    apply (rule csr_reset_rule_c; assumption)
    apply (rule csr_has_rule_c; assumption)
    apply (rule csr_current_rule_c; assumption)
    apply (rule csr_move_rule_c; assumption)
    apply (rule csr_reset_rule_c; assumption)
    apply (rule vtx_has_rule_c; assumption)
    apply (rule vtx_current_rule_c; assumption)
    apply (rule vtx_move_rule_c; assumption)
    apply (rule capr; assumption)
    apply (rule costr; assumption)
    apply (rule fstr; assumption)
    apply (rule sndr; assumption)
    done
  have vv: "vtx_invar \<lparr>vi_list = edged_vs_list, vi_pos = 0\<rparr>"
    by (simp add: vtx_invar_def distinct_edged_vs_list)
  have vab: "vtx_abstract \<lparr>vi_list = edged_vs_list, vi_pos = 0\<rparr> \<subseteq> original_network.\<V>"
    by (simp add: vtx_abstract_def V_orig_eq_edged)
  have cno: "csr_n out_csr = vcount" by (simp add: csr_n_def out_csr_cur psums_length)
  have cni: "csr_n in_csr = vcount" by (simp add: csr_n_def in_csr_cur psums_length)
  show ?thesis
    unfolding make_acyclic_prog_def
    apply (rule ht_cons_post_prec[OF acycR.make_acyclic_imp_rule[OF multigraph_inv_csr ff feas vv vab cvs ces cds refl refl refl]])
    apply (sep_auto simp:
      acycR.AF_outer_out_result_proj[where proj = csr_edges, OF csr_move_selectors(1) csr_reset_selectors(1) multigraph_inv_csr ff feas vv vab]
      acycR.AF_outer_out_result_proj[where proj = csr_lo, OF csr_move_selectors(2) csr_reset_selectors(2) multigraph_inv_csr ff feas vv vab]
      acycR.AF_outer_out_result_proj[where proj = csr_hi, OF csr_move_selectors(3) csr_reset_selectors(3) multigraph_inv_csr ff feas vv vab]
      acycR.AF_outer_out_result_proj[where proj = csr_n, OF csr_move_selectors(4) csr_reset_selectors(4) multigraph_inv_csr ff feas vv vab]
      acycR.AF_outer_in_result_proj[where proj = csr_edges, OF csr_move_selectors(1) csr_reset_selectors(1) multigraph_inv_csr ff feas vv vab]
      acycR.AF_outer_in_result_proj[where proj = csr_lo, OF csr_move_selectors(2) csr_reset_selectors(2) multigraph_inv_csr ff feas vv vab]
      acycR.AF_outer_in_result_proj[where proj = csr_hi, OF csr_move_selectors(3) csr_reset_selectors(3) multigraph_inv_csr ff feas vv vab]
      acycR.AF_outer_in_result_proj[where proj = csr_n, OF csr_move_selectors(4) csr_reset_selectors(4) multigraph_inv_csr ff feas vv vab]
      cno cni)
    done
qed

subsection \<open>Layer (d): the in-place imbalance transform refines @{const imbalance}\<close>

text \<open>Running @{const imbalance_imp} over \<open>[v..<vcount]\<close> adds each vertex's balance-array entry to its
      excess cell, exactly the functional @{const imbalance} fold.  The balance array is a parameter
      here (@{term bl}); at the call site it holds the vertex-indexed balances and the agreement
      \<open>bl ! w = b_arr ! w\<close> is supplied then.\<close>
lemma imbalance_imp_rule:
  "\<lbrakk>v \<le> vcount; vcount \<le> length exc0; \<forall>w<vcount. w < length bl\<rbrakk> \<Longrightarrow>
   <exc_arr \<mapsto>\<^sub>a exc0 * ba \<mapsto>\<^sub>a bl>
    imbalance_imp exc_arr ba v vcount
   <\<lambda>_. exc_arr \<mapsto>\<^sub>a (fold (\<lambda>w a. a[w := a ! w + bl ! w]) [v..<vcount] exc0) * ba \<mapsto>\<^sub>a bl>"
proof (induction "vcount - v" arbitrary: v exc0)
  case 0
  thus ?case by (subst imbalance_imp.simps) sep_auto
next
  case (Suc k)
  have vlt: "v < vcount" using Suc.hyps(2) by simp
  have kv: "k = vcount - Suc v" using Suc.hyps(2) by simp
  have nvcv: "\<not> vcount \<le> v" using vlt by simp
  have vex: "v < length exc0" using Suc.prems(2) vlt by simp
  have vbl: "v < length bl" using Suc.prems(3) vlt by simp
  have suc_le: "Suc v \<le> vcount" using vlt by simp
  have vc_le: "vcount \<le> length (exc0[v := exc0 ! v + bl ! v])" using Suc.prems(2) by simp
  note ih = Suc.hyps(1)[OF kv suc_le vc_le Suc.prems(3)]
  have foldeq: "fold (\<lambda>w a. a[w := a ! w + bl ! w]) [v..<vcount] exc0
              = fold (\<lambda>w a. a[w := a ! w + bl ! w]) [Suc v..<vcount] (exc0[v := exc0 ! v + bl ! v])"
    by (simp add: upt_conv_Cons[OF vlt])
  show ?case
    apply (subst imbalance_imp.simps)
    apply (simp only: if_not_P[OF nvcv])
    apply (sep_auto heap: ih simp: foldeq vex vbl)
    done
qed

lemma passA_imp_rule:
  fixes fl_arr cap_arr :: "'n array" and fst_arr snd_arr :: "nat array"
    and es_arr :: "edge_tag array" and exc_arr :: "'n array"
    and oe_arr oc_arr ie_arr ic_arr :: "nat array"
    and fla cla :: "'n list" and flla slla :: "nat list"
    and e :: nat and est :: "edge_tag list" and exc :: "'n list"
    and oe oc ie ic :: "nat list"
  assumes e_le: "e \<le> m"
    and fla_len: "m \<le> length fla" and cla_len: "m \<le> length cla"
    and flla_len: "m \<le> length flla" and slla_len: "m \<le> length slla"
    and cap_eq: "\<And>i. i < m \<Longrightarrow> cla ! i = capacity_list ! i"
    and fst_eq: "\<And>i. i < m \<Longrightarrow> flla ! i = fst_list ! i"
    and snd_eq: "\<And>i. i < m \<Longrightarrow> slla ! i = snd_list ! i"
    and s_eq: "(est, exc, oe, oc, ie, ic) = fold (passA_step fla) [0..<e]
                 (replicate m InL, replicate (Suc vcount) 0, csr_edges out_csr, out_lo, csr_edges in_csr, in_lo)"
  shows "<fl_arr \<mapsto>\<^sub>a fla * cap_arr \<mapsto>\<^sub>a cla * fst_arr \<mapsto>\<^sub>a flla * snd_arr \<mapsto>\<^sub>a slla *
          es_arr \<mapsto>\<^sub>a est * exc_arr \<mapsto>\<^sub>a exc * oe_arr \<mapsto>\<^sub>a oe * oc_arr \<mapsto>\<^sub>a oc * ie_arr \<mapsto>\<^sub>a ie * ic_arr \<mapsto>\<^sub>a ic>
         passA_imp fl_arr cap_arr fst_arr snd_arr es_arr exc_arr oe_arr oc_arr ie_arr ic_arr e m
        <\<lambda>_. fl_arr \<mapsto>\<^sub>a fla * cap_arr \<mapsto>\<^sub>a cla * fst_arr \<mapsto>\<^sub>a flla * snd_arr \<mapsto>\<^sub>a slla *
             es_arr \<mapsto>\<^sub>a fst (passA fla) * exc_arr \<mapsto>\<^sub>a fst (snd (passA fla)) *
             oe_arr \<mapsto>\<^sub>a fst (snd (snd (passA fla))) * oc_arr \<mapsto>\<^sub>a fst (snd (snd (snd (passA fla)))) *
             ie_arr \<mapsto>\<^sub>a fst (snd (snd (snd (snd (passA fla))))) * ic_arr \<mapsto>\<^sub>a snd (snd (snd (snd (snd (passA fla)))))>"
proof -
  have sized_init: "sized (replicate m InL, replicate (Suc vcount) (0::'n), csr_edges out_csr, out_lo, csr_edges in_csr, in_lo)"
    by (simp add: sized_def length_out_lo length_in_lo out_csr_eq in_csr_eq)
  have sized_fold: "sized s0 \<Longrightarrow> sized (fold (passA_step fla) xs s0)" for s0 xs
  proof (induct xs arbitrary: s0)
    case Nil thus ?case by simp
  next
    case (Cons a xs) thus ?case by (simp add: passA_step_sized)
  qed
  from e_le s_eq show ?thesis
  proof (induction "m - e" arbitrary: e est exc oe oc ie ic)
    case 0
    have em: "e = m" using "0.hyps" "0.prems"(1) by simp
    have s0: "(est, exc, oe, oc, ie, ic) = passA fla" using "0.prems"(2) em by (simp add: passA_def)
    show ?case unfolding em by (subst passA_imp.simps) (sep_auto simp: s0[symmetric])
  next
    case (Suc d)
    have em: "e < m" using Suc.hyps(2) Suc.prems(1) by simp
    have sized_s: "sized (est, exc, oe, oc, ie, ic)" using Suc.prems(2) sized_fold[OF sized_init] by simp
    have lens: "length est = m" "length exc = Suc vcount" "length oe = m" "length oc = vcount" "length ie = m" "length ic = vcount"
      using sized_s by (auto simp: sized_def)
    have xe: "flla ! e = fst_list ! e" using fst_eq em by simp
    have ye: "slla ! e = snd_list ! e" using snd_eq em by simp
    have ue: "cla ! e = capacity_list ! e" using cap_eq em by simp
    have xvc: "fst_list ! e < vcount" using fst_list_nth_vertex[OF em] vs_less_vcount by simp
    have yvc: "snd_list ! e < vcount" using snd_list_nth_vertex[OF em] vs_less_vcount by simp
    have oc_val: "oc ! (fst_list ! e) = out_lo ! (fst_list ! e) + length (filter (\<lambda>e'. classify fla e' = InTree \<and> fst_list ! e' = fst_list ! e) [0..<e])"
    proof -
      have "oc = fst (snd (snd (snd (fold (passA_step fla) [0..<e] (replicate m InL, replicate (Suc vcount) 0, csr_edges out_csr, out_lo, csr_edges in_csr, in_lo)))))"
        using Suc.prems(2)[symmetric] by simp
      thus ?thesis using passA_fold_oc_count[OF sized_init xvc, where fl=fla and xs="[0..<e]"] by simp
    qed
    have ic_val: "ic ! (snd_list ! e) = in_lo ! (snd_list ! e) + length (filter (\<lambda>e'. classify fla e' = InTree \<and> snd_list ! e' = snd_list ! e) [0..<e])"
    proof -
      have "ic = snd (snd (snd (snd (snd (fold (passA_step fla) [0..<e] (replicate m InL, replicate (Suc vcount) 0, csr_edges out_csr, out_lo, csr_edges in_csr, in_lo))))))"
        using Suc.prems(2)[symmetric] by simp
      thus ?thesis using passA_fold_ic_count[OF sized_init yvc, where fl=fla and xs="[0..<e]"] by simp
    qed
    have oc_lt: "classify fla e = InTree \<Longrightarrow> oc ! (fst_list ! e) < m"
    proof -
      assume it: "classify fla e = InTree"
      let ?P = "\<lambda>e'. classify fla e' = InTree \<and> fst_list ! e' = fst_list ! e"
      have split: "[0..<m] = [0..<e] @ [e..<m]" using em by (simp add: upt_append)
      have ne: "filter ?P [e..<m] \<noteq> []" using it em by (simp add: filter_empty_conv) (metis atLeastLessThan_iff le_refl)
      have "length (filter ?P [0..<e]) < length (filter ?P [0..<m])" using split ne by (simp add: filter_append)
      hence "oc ! (fst_list ! e) < out_lo ! (fst_list ! e) + length (filter ?P [0..<m])" using oc_val by simp
      also have "... = free_out_hi fla ! (fst_list ! e)" using free_out_hi_count[OF xvc] by simp
      also have "... \<le> m" using free_out_hi_le_m[OF xvc] .
      finally show "oc ! (fst_list ! e) < m" .
    qed
    have ic_lt: "classify fla e = InTree \<Longrightarrow> ic ! (snd_list ! e) < m"
    proof -
      assume it: "classify fla e = InTree"
      let ?Q = "\<lambda>e'. classify fla e' = InTree \<and> snd_list ! e' = snd_list ! e"
      have split: "[0..<m] = [0..<e] @ [e..<m]" using em by (simp add: upt_append)
      have ne: "filter ?Q [e..<m] \<noteq> []" using it em by (simp add: filter_empty_conv) (metis atLeastLessThan_iff le_refl)
      have "length (filter ?Q [0..<e]) < length (filter ?Q [0..<m])" using split ne by (simp add: filter_append)
      hence "ic ! (snd_list ! e) < in_lo ! (snd_list ! e) + length (filter ?Q [0..<m])" using ic_val by simp
      also have "... = free_in_hi fla ! (snd_list ! e)" using free_in_hi_count[OF yvc] by simp
      also have "... \<le> m" using free_in_hi_le_m[OF yvc] .
      finally show "ic ! (snd_list ! e) < m" .
    qed
    have dse: "d = m - Suc e" using Suc.hyps(2) em by simp
    have sse: "Suc e \<le> m" using em by simp
    have step: "<fl_arr \<mapsto>\<^sub>a fla * cap_arr \<mapsto>\<^sub>a cla * fst_arr \<mapsto>\<^sub>a flla * snd_arr \<mapsto>\<^sub>a slla *
        es_arr \<mapsto>\<^sub>a fst (passA_step fla e (est, exc, oe, oc, ie, ic)) *
        exc_arr \<mapsto>\<^sub>a fst (snd (passA_step fla e (est, exc, oe, oc, ie, ic))) *
        oe_arr \<mapsto>\<^sub>a fst (snd (snd (passA_step fla e (est, exc, oe, oc, ie, ic)))) *
        oc_arr \<mapsto>\<^sub>a fst (snd (snd (snd (passA_step fla e (est, exc, oe, oc, ie, ic))))) *
        ie_arr \<mapsto>\<^sub>a fst (snd (snd (snd (snd (passA_step fla e (est, exc, oe, oc, ie, ic)))))) *
        ic_arr \<mapsto>\<^sub>a snd (snd (snd (snd (snd (passA_step fla e (est, exc, oe, oc, ie, ic))))))>
       passA_imp fl_arr cap_arr fst_arr snd_arr es_arr exc_arr oe_arr oc_arr ie_arr ic_arr (Suc e) m
      <\<lambda>_. fl_arr \<mapsto>\<^sub>a fla * cap_arr \<mapsto>\<^sub>a cla * fst_arr \<mapsto>\<^sub>a flla * snd_arr \<mapsto>\<^sub>a slla *
        es_arr \<mapsto>\<^sub>a fst (passA fla) * exc_arr \<mapsto>\<^sub>a fst (snd (passA fla)) *
        oe_arr \<mapsto>\<^sub>a fst (snd (snd (passA fla))) * oc_arr \<mapsto>\<^sub>a fst (snd (snd (snd (passA fla)))) *
        ie_arr \<mapsto>\<^sub>a fst (snd (snd (snd (snd (passA fla))))) * ic_arr \<mapsto>\<^sub>a snd (snd (snd (snd (snd (passA fla)))))>"
      by (rule Suc.hyps(1)[OF dse sse]) (simp add: Suc.prems(2))
    have nme: "\<not> m \<le> e" using em by simp
    have eb: "e < length flla" "e < length slla" "e < length fla" "e < length cla" "e < length est"
      using em flla_len slla_len fla_len cla_len lens(1) by auto
    show ?case
    proof (cases "classify fla e = InTree")
      case True
      have st_val: "(if fla ! e = 0 then InL else if cla ! e \<noteq> - 1 \<and> fla ! e = cla ! e then InU else InTree) = InTree"
      proof -
        have "(if fla ! e = 0 then InL else if cla ! e \<noteq> - 1 \<and> fla ! e = cla ! e then InU else InTree) = classify fla e"
          using ue by (simp add: classify_def)
        thus ?thesis using True by simp
      qed
      have ps_es: "fst (passA_step fla e (est, exc, oe, oc, ie, ic)) = est[e := InTree]"
        using True by (simp add: passA_step_fst)
      have ps_oe: "fst (snd (snd (passA_step fla e (est, exc, oe, oc, ie, ic)))) = oe[oc ! (fst_list ! e) := e]"
        using True by (simp add: passA_step_oe)
      have ps_oc: "fst (snd (snd (snd (passA_step fla e (est, exc, oe, oc, ie, ic))))) = oc[fst_list ! e := Suc (oc ! (fst_list ! e))]"
        using True by (simp add: passA_step_oc)
      have ps_ie: "fst (snd (snd (snd (snd (passA_step fla e (est, exc, oe, oc, ie, ic)))))) = ie[ic ! (snd_list ! e) := e]"
        using True by (simp add: passA_step_ie)
      have ps_ic: "snd (snd (snd (snd (snd (passA_step fla e (est, exc, oe, oc, ie, ic)))))) = ic[snd_list ! e := Suc (ic ! (snd_list ! e))]"
        using True by (simp add: passA_step_ic)
      have ps_exc: "fst (snd (passA_step fla e (est, exc, oe, oc, ie, ic))) =
          exc[snd_list ! e := exc ! (snd_list ! e) + fla ! e,
              fst_list ! e := exc[snd_list ! e := exc ! (snd_list ! e) + fla ! e] ! (fst_list ! e) - fla ! e]"
        by (simp add: passA_step_exc Let_def)
      have step': "<fl_arr \<mapsto>\<^sub>a fla * cap_arr \<mapsto>\<^sub>a cla * fst_arr \<mapsto>\<^sub>a flla * snd_arr \<mapsto>\<^sub>a slla *
          es_arr \<mapsto>\<^sub>a est[e := InTree] *
          exc_arr \<mapsto>\<^sub>a exc[snd_list ! e := exc ! (snd_list ! e) + fla ! e,
              fst_list ! e := exc[snd_list ! e := exc ! (snd_list ! e) + fla ! e] ! (fst_list ! e) - fla ! e] *
          oe_arr \<mapsto>\<^sub>a oe[oc ! (fst_list ! e) := e] *
          oc_arr \<mapsto>\<^sub>a oc[fst_list ! e := Suc (oc ! (fst_list ! e))] *
          ie_arr \<mapsto>\<^sub>a ie[ic ! (snd_list ! e) := e] *
          ic_arr \<mapsto>\<^sub>a ic[snd_list ! e := Suc (ic ! (snd_list ! e))]>
         passA_imp fl_arr cap_arr fst_arr snd_arr es_arr exc_arr oe_arr oc_arr ie_arr ic_arr (Suc e) m
        <\<lambda>_. fl_arr \<mapsto>\<^sub>a fla * cap_arr \<mapsto>\<^sub>a cla * fst_arr \<mapsto>\<^sub>a flla * snd_arr \<mapsto>\<^sub>a slla *
          es_arr \<mapsto>\<^sub>a fst (passA fla) * exc_arr \<mapsto>\<^sub>a fst (snd (passA fla)) *
          oe_arr \<mapsto>\<^sub>a fst (snd (snd (passA fla))) * oc_arr \<mapsto>\<^sub>a fst (snd (snd (snd (passA fla)))) *
          ie_arr \<mapsto>\<^sub>a fst (snd (snd (snd (snd (passA fla))))) * ic_arr \<mapsto>\<^sub>a snd (snd (snd (snd (snd (passA fla)))))>"
        using step by (simp only: ps_es ps_exc ps_oe ps_oc ps_ie ps_ic)
      have step'': "<fl_arr \<mapsto>\<^sub>a fla * cap_arr \<mapsto>\<^sub>a cla * fst_arr \<mapsto>\<^sub>a flla * snd_arr \<mapsto>\<^sub>a slla *
          es_arr \<mapsto>\<^sub>a est[e := InTree] *
          exc_arr \<mapsto>\<^sub>a exc[slla ! e := exc ! (slla ! e) + fla ! e,
              flla ! e := exc[slla ! e := exc ! (slla ! e) + fla ! e] ! (flla ! e) - fla ! e] *
          oe_arr \<mapsto>\<^sub>a oe[oc ! (flla ! e) := e] *
          oc_arr \<mapsto>\<^sub>a oc[flla ! e := Suc (oc ! (flla ! e))] *
          ie_arr \<mapsto>\<^sub>a ie[ic ! (slla ! e) := e] *
          ic_arr \<mapsto>\<^sub>a ic[slla ! e := Suc (ic ! (slla ! e))]>
         passA_imp fl_arr cap_arr fst_arr snd_arr es_arr exc_arr oe_arr oc_arr ie_arr ic_arr (Suc e) m
        <\<lambda>_. fl_arr \<mapsto>\<^sub>a fla * cap_arr \<mapsto>\<^sub>a cla * fst_arr \<mapsto>\<^sub>a flla * snd_arr \<mapsto>\<^sub>a slla *
          es_arr \<mapsto>\<^sub>a fst (passA fla) * exc_arr \<mapsto>\<^sub>a fst (snd (passA fla)) *
          oe_arr \<mapsto>\<^sub>a fst (snd (snd (passA fla))) * oc_arr \<mapsto>\<^sub>a fst (snd (snd (snd (passA fla)))) *
          ie_arr \<mapsto>\<^sub>a fst (snd (snd (snd (snd (passA fla))))) * ic_arr \<mapsto>\<^sub>a snd (snd (snd (snd (snd (passA fla)))))>"
        using step' by (simp only: xe[symmetric] ye[symmetric])
      have exlv: "slla ! e < Suc vcount" "flla ! e < Suc vcount" using yvc xvc ye xe by simp_all
      have vbv: "flla ! e < vcount" "slla ! e < vcount" using xvc yvc xe ye by simp_all
      have exl_f: "flla ! e < length exc" "slla ! e < length exc" using xvc yvc lens(2) xe ye by simp_all
      have vb_f: "flla ! e < length oc" "slla ! e < length ic" using xvc yvc lens(4) lens(6) xe ye by simp_all
      have scb_f: "oc ! (flla ! e) < length oe" "ic ! (slla ! e) < length ie"
        using oc_lt ic_lt lens(3) lens(5) True xe ye by simp_all
      have scb_v: "oc ! (flla ! e) < m" "ic ! (slla ! e) < m"
        using scb_f lens(3) lens(5) xe ye by simp_all
      show ?thesis
        apply (subst passA_imp.simps)
        apply (simp only: nme if_False Let_def)
        apply (sep_auto heap: step'' simp: em st_val eb exlv exl_f vb_f vbv scb_f scb_v lens)
        done
    next
      case False
      have st_valF: "(if fla ! e = 0 then InL else if cla ! e \<noteq> - 1 \<and> fla ! e = cla ! e then InU else InTree) = classify fla e"
        using ue by (simp add: classify_def)
      have psF: "fst (passA_step fla e (est, exc, oe, oc, ie, ic)) = est[e := classify fla e]"
               "fst (snd (snd (passA_step fla e (est, exc, oe, oc, ie, ic)))) = oe"
               "fst (snd (snd (snd (passA_step fla e (est, exc, oe, oc, ie, ic))))) = oc"
               "fst (snd (snd (snd (snd (passA_step fla e (est, exc, oe, oc, ie, ic)))))) = ie"
               "snd (snd (snd (snd (snd (passA_step fla e (est, exc, oe, oc, ie, ic)))))) = ic"
        using False by (simp_all add: passA_step_fst passA_step_oe passA_step_oc passA_step_ie passA_step_ic)
      have psF_exc: "fst (snd (passA_step fla e (est, exc, oe, oc, ie, ic))) =
          exc[slla ! e := exc ! (slla ! e) + fla ! e,
              flla ! e := exc[slla ! e := exc ! (slla ! e) + fla ! e] ! (flla ! e) - fla ! e]"
        by (simp add: passA_step_exc Let_def xe ye)
      have step_F: "<fl_arr \<mapsto>\<^sub>a fla * cap_arr \<mapsto>\<^sub>a cla * fst_arr \<mapsto>\<^sub>a flla * snd_arr \<mapsto>\<^sub>a slla *
          es_arr \<mapsto>\<^sub>a est[e := classify fla e] *
          exc_arr \<mapsto>\<^sub>a exc[slla ! e := exc ! (slla ! e) + fla ! e,
              flla ! e := exc[slla ! e := exc ! (slla ! e) + fla ! e] ! (flla ! e) - fla ! e] *
          oe_arr \<mapsto>\<^sub>a oe * oc_arr \<mapsto>\<^sub>a oc * ie_arr \<mapsto>\<^sub>a ie * ic_arr \<mapsto>\<^sub>a ic>
         passA_imp fl_arr cap_arr fst_arr snd_arr es_arr exc_arr oe_arr oc_arr ie_arr ic_arr (Suc e) m
        <\<lambda>_. fl_arr \<mapsto>\<^sub>a fla * cap_arr \<mapsto>\<^sub>a cla * fst_arr \<mapsto>\<^sub>a flla * snd_arr \<mapsto>\<^sub>a slla *
          es_arr \<mapsto>\<^sub>a fst (passA fla) * exc_arr \<mapsto>\<^sub>a fst (snd (passA fla)) *
          oe_arr \<mapsto>\<^sub>a fst (snd (snd (passA fla))) * oc_arr \<mapsto>\<^sub>a fst (snd (snd (snd (passA fla)))) *
          ie_arr \<mapsto>\<^sub>a fst (snd (snd (snd (snd (passA fla))))) * ic_arr \<mapsto>\<^sub>a snd (snd (snd (snd (snd (passA fla)))))>"
        using step by (simp only: psF(1) psF_exc psF(2) psF(3) psF(4) psF(5))
      have exl_f: "flla ! e < length exc" "slla ! e < length exc" using xvc yvc lens(2) xe ye by simp_all
      have exlv: "slla ! e < Suc vcount" "flla ! e < Suc vcount" using yvc xvc ye xe by simp_all
      show ?thesis
        apply (subst passA_imp.simps)
        apply (simp only: nme if_False Let_def)
        apply (sep_auto heap: step_F simp: em st_valF False eb exlv exl_f lens)
        done
    qed
  qed
qed

subsection \<open>Layer (d.5): the depth-first spanning-tree builder refines @{const build_dfs_a}\<close>

text \<open>The DFS state relation: the imperative @{typ \<open>'n dfs_imp\<close>} record of array / reference handles
      against the functional @{typ \<open>'n dfs_state\<close>}.  The augmented edge arrays @{term di_fst} /
      @{term di_snd} (and @{term di_cap} / @{term di_flow} / @{term di_es}) are wider than
      the real block, so they are existential with their real prefix pinned — @{term di_fst} /
      @{term di_snd} to @{term fst_list} / @{term snd_list}, @{term di_cap} to @{term capacity_list},
      and @{term di_flow} to the parameter @{term fl0} (the real-edge flow the tree builder must carry
      through to the network-simplex loop); the four scanned arrays @{term di_oe} / @{term di_ohi} /
      @{term di_ie} / @{term di_ihi} are the traversal's fixed arguments @{term oe} / @{term oh} /
      @{term ie} / @{term ih}, and the block-start reads @{term di_olo} / @{term di_ilo} are the
      acyclifier CSRs @{term out_lo} / @{term in_lo}.  The DFS stack lives in the three fixed-capacity
      arrays @{term di_sv} / @{term di_soc} / @{term di_sic} (each of length @{term \<open>Suc vcount\<close>}, the
      per-vertex allocation) with fill pointer @{term di_sp}, related to @{const ds_stk} by
      @{const stk_rel}.\<close>
definition dfs_rel :: "'n list \<Rightarrow> edge_tag list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> 'n dfs_imp \<Rightarrow> 'n dfs_state \<Rightarrow> assn" where
  "dfs_rel fl0 es0 oe oh ie ih st s =
     (\<exists>\<^sub>A fsta snda capa flowa esa auxa svl socl sicl sp.
        di_seen st \<mapsto>\<^sub>a ds_seen s *
        prnt_impl (di_tree st) \<mapsto>\<^sub>a ds_prnt s *
        thrd_impl (di_tree st) \<mapsto>\<^sub>a ds_thrd s *
        rvth_impl (di_tree st) \<mapsto>\<^sub>a ds_rvth s *
        lsuc_impl (di_tree st) \<mapsto>\<^sub>a ds_lsuc s *
        snum_impl (di_tree st) \<mapsto>\<^sub>a ds_snum s *
        aux_impl (di_tree st) \<mapsto>\<^sub>a auxa *
        di_par st \<mapsto>\<^sub>a ds_par s *
        di_dir st \<mapsto>\<^sub>a ds_dir s *
        di_pot st \<mapsto>\<^sub>a ds_pot s *
        di_fst st \<mapsto>\<^sub>a fsta * di_snd st \<mapsto>\<^sub>a snda * di_cap st \<mapsto>\<^sub>a capa *
        di_cost st \<mapsto>\<^sub>a cost_list * di_flow st \<mapsto>\<^sub>a flowa * di_es st \<mapsto>\<^sub>a esa *
        di_oe st \<mapsto>\<^sub>a oe * di_olo st \<mapsto>\<^sub>a out_lo * di_ohi st \<mapsto>\<^sub>a oh *
        di_ie st \<mapsto>\<^sub>a ie * di_ilo st \<mapsto>\<^sub>a in_lo * di_ihi st \<mapsto>\<^sub>a ih *
        di_sv st \<mapsto>\<^sub>a svl * di_soc st \<mapsto>\<^sub>a socl * di_sic st \<mapsto>\<^sub>a sicl * di_sp st \<mapsto>\<^sub>r sp *
        di_prev st \<mapsto>\<^sub>r ds_prev s * di_nxt st \<mapsto>\<^sub>r ds_nxt s *
        \<up>(stk_rel svl socl sicl sp (ds_stk s) \<and>
          length svl = Suc vcount \<and> length socl = Suc vcount \<and> length sicl = Suc vcount \<and>
          m \<le> length fsta \<and> m \<le> length snda \<and>
          (\<forall>e<m. fsta ! e = fst_list ! e) \<and> (\<forall>e<m. snda ! e = snd_list ! e) \<and>
          (\<forall>e<m. flowa ! e = fl0 ! e) \<and> (\<forall>e<m. capa ! e = capacity_list ! e) \<and>
          (\<forall>e<m. esa ! e = es0 ! e) \<and> length auxa = Suc vcount \<and>
          m + length (ds_afst s) \<le> length fsta \<and> m + length (ds_asnd s) \<le> length snda \<and>
          m + length (ds_acap s) \<le> length capa \<and> m + length (ds_aflw s) \<le> length flowa \<and>
          m + length (ds_aest s) \<le> length esa \<and>
          (\<forall>k<ds_nxt s. fsta ! (m+k) = ds_afst s ! k) \<and> (\<forall>k<ds_nxt s. snda ! (m+k) = ds_asnd s ! k) \<and>
          (\<forall>k<ds_nxt s. capa ! (m+k) = ds_acap s ! k) \<and> (\<forall>k<ds_nxt s. flowa ! (m+k) = ds_aflw s ! k) \<and>
          (\<forall>k<ds_nxt s. esa ! (m+k) = ds_aest s ! k)))"

text \<open>Finishing (popping) a fully-scanned stack-top @{term v}: a straight run of array writes
      (@{term ds_lsuc}, the parent's @{term ds_snum}) and a fill-pointer decrement.  The stack arrays are
      not touched — the popped slot merely falls above @{term \<open>sp - 1\<close>}, exactly @{thm stk_rel_pop'}.\<close>
lemma dfs_finish_imp_rule:
  assumes stk: "ds_stk s = (v, oc, ic) # rest"
    and vlt: "v < length (ds_prnt s)" "v < length (ds_lsuc s)" "v < length (ds_snum s)"
    and plt: "ds_prnt s ! v < length (ds_snum s)"
  shows "<dfs_rel fl0 es0 oe oh ie ih st s>
           dfs_finish_imp st v
         <\<lambda>_. dfs_rel fl0 es0 oe oh ie ih st (dfs_finish s v rest)>"
  unfolding dfs_rel_def dfs_finish_imp_def dfs_finish_def Let_def
  apply (sep_auto simp: vlt plt stk)
  subgoal for fsta snda capa flowa esa auxa svl socl sicl sp a b
    using stk_rel_pop'[of svl socl sicl sp "(v,oc,ic)" rest]
    by sep_auto
  done

text \<open>Discovering a fresh vertex @{term w} from stack-top @{term v} across the free real edge @{term e}:
      finalise @{term w}'s tree fields, thread-link it after @{term \<open>ds_prev s\<close>}, seed its potential
      (\<open>\<plusminus> cost_list ! e\<close> by whether @{term v} is @{term e}'s tail), then push its frame
      @{term \<open>(w, out_lo ! w, in_lo ! w)\<close>} — a write at the fill pointer plus a bump, exactly
      @{thm stk_rel_push}.  The single case split is on @{term \<open>v = fst_list ! e\<close>} (the potential seed's
      sign); every array bound is a caller obligation, and the stack-space bound is
      @{term \<open>length (ds_stk s) < Suc vcount\<close>}.\<close>
lemma dfs_discover_imp_rule:
  assumes elt: "e < m"
    and wlt: "w < length (ds_seen s)" "w < length (ds_prnt s)" "w < length (ds_par s)"
             "w < length (ds_dir s)" "w < length (ds_pot s)" "w < length (ds_rvth s)"
             "w < length (ds_snum s)"
    and vlt: "v < length (ds_pot s)"
    and pvlt: "ds_prev s < length (ds_thrd s)"
    and wvc: "w < vcount"
    and depth: "length (ds_stk s) < Suc vcount"
  shows "<dfs_rel fl0 es0 oe oh ie ih st s>
           dfs_discover_imp st v w e
         <\<lambda>_. dfs_rel fl0 es0 oe oh ie ih st (dfs_discover s v w e)>"
  (*nasty refinement proof that takes ages to process*)
  unfolding dfs_rel_def dfs_discover_imp_def dfs_discover_def Let_def
  apply (sep_auto simp: elt wlt vlt pvlt wvc depth length_out_lo length_in_lo length_cost_list_m)
  apply (metis depth stk_rel_len)   
  apply (meson elt add_leD1 less_le_trans)
  apply (sep_auto simp: elt wlt vlt pvlt wvc depth length_out_lo length_in_lo length_cost_list_m)
   apply (metis depth stk_rel_len)
   apply (frule stk_rel_len)
   apply (sep_auto simp: depth stk_rel_push)
  apply (frule stk_rel_len)
   apply (sep_auto simp: depth length_out_lo length_in_lo stk_rel_push)
   apply (rule pvlt)
  apply (frule stk_rel_len)
  apply (sep_auto simp: wlt vlt pvlt wvc depth length_out_lo length_in_lo stk_rel_push)
  done

text \<open>The DFS-loop refinement invariant.  Beyond @{const dfs_wf} (stack vertices are real, seen array
      sized) and @{const dfs_sized} (all vertex arrays sized), the loop needs: the stack frames carry
      \<^emph>\<open>distinct\<close> vertices (so the flat stack never overflows its @{term \<open>Suc vcount\<close>} capacity — the
      depth is at most @{term vcount}), every stacked vertex is already seen (so a freshly discovered
      neighbour is genuinely new, preserving distinctness), and the \<open>prev\<close> pointer / all parent entries
      are valid vertex names.  Each conjunct is preserved by the three call-updates @{const bd_upd1} /
      @{const bd_upd2} / @{const bd_upd3}.\<close>
definition dref_inv :: "'n dfs_state \<Rightarrow> bool" where
  "dref_inv s \<longleftrightarrow> distinct (map (\<lambda>(v,oc,ic). v) (ds_stk s))
     \<and> (\<forall>(v,oc,ic)\<in>set (ds_stk s). ds_seen s ! v)
     \<and> ds_prev s < Suc vcount
     \<and> (\<forall>v<Suc vcount. ds_prnt s ! v < Suc vcount)"

text \<open>Distinct stack frames whose vertices are all below @{term vcount} number at most @{term vcount} — the
      depth bound that keeps the flat DFS stack within its @{term \<open>Suc vcount\<close>} allocation.\<close>
lemma stk_depth_le:
  assumes "distinct (map (\<lambda>(v,oc,ic). v) xs)" and "\<forall>(v,oc,ic)\<in>set xs. v < vcount"
  shows "length xs \<le> vcount"
proof -
  have "length xs = card (set (map (\<lambda>(v,oc,ic). v) xs))"
    using distinct_card[OF assms(1)] by simp
  also have "... \<le> card {0..<vcount}"
    apply (rule card_mono, simp)
    using assms(2) by (auto split: prod.splits)
  finally show ?thesis by simp
qed

lemma bd_upd1_dref:
  assumes inv: "dref_inv s" and wf: "dfs_wf s" and sz: "dfs_sized s" and c: "bd_call1_conds fl s"
  shows "dref_inv (bd_upd1 fl s)"
proof -
  from c obtain v oc ic rest where stk: "ds_stk s = (v,oc,ic)#rest" and oclt: "oc < free_out_hi fl ! v"
    by (auto simp: bd_call1_conds_def split: list.splits prod.splits)
  from wf stk have vlt: "v < vcount" and olo: "out_lo ! v \<le> oc" by (auto simp: dfs_wf_def)
  from sz have lens: "length (ds_seen s) = Suc vcount" "length (ds_prnt s) = Suc vcount"
    by (auto simp: dfs_sized_def)
  let ?e = "free_out_edges fl ! oc" let ?w = "snd_list ! ?e"
  have wlt: "?w < vcount" using Hout_valid[OF vlt olo oclt] .
  from inv have dist: "distinct (map (\<lambda>(v,oc,ic). v) (ds_stk s))"
    and seen: "\<forall>(v,oc,ic)\<in>set (ds_stk s). ds_seen s ! v"
    and prnt: "\<forall>v<Suc vcount. ds_prnt s ! v < Suc vcount" by (auto simp: dref_inv_def)
  show ?thesis
  proof (cases "ds_seen s ! ?w")
    case True
    thus ?thesis using inv stk by (auto simp: dref_inv_def bd_upd1_def Let_def)
  next
    case False
    have wnotin: "?w \<notin> set (map (\<lambda>(v,oc,ic). v) (ds_stk s))"
      using False seen by (auto split: prod.splits)
    have eq: "bd_upd1 fl s = dfs_discover (s\<lparr>ds_stk := (v, Suc oc, ic) # rest\<rparr>) v ?w ?e"
      using stk False by (simp add: bd_upd1_def Let_def)
    show ?thesis unfolding eq
      using wnotin dist seen prnt vlt wlt stk lens
      by (auto simp: dref_inv_def dfs_discover_def Let_def nth_list_update split: prod.splits if_splits)
  qed
qed

lemma bd_upd2_dref:
  assumes inv: "dref_inv s" and wf: "dfs_wf s" and sz: "dfs_sized s" and c: "bd_call2_conds fl s"
  shows "dref_inv (bd_upd2 fl s)"
proof -
  from c obtain v oc ic rest where stk: "ds_stk s = (v,oc,ic)#rest" and iclt: "ic < free_in_hi fl ! v"
    by (auto simp: bd_call2_conds_def split: list.splits prod.splits)
  from wf stk have vlt: "v < vcount" and ilo: "in_lo ! v \<le> ic" by (auto simp: dfs_wf_def)
  from sz have lens: "length (ds_seen s) = Suc vcount" "length (ds_prnt s) = Suc vcount"
    by (auto simp: dfs_sized_def)
  let ?e = "free_in_edges fl ! ic" let ?w = "fst_list ! ?e"
  have wlt: "?w < vcount" using Hin_valid[OF vlt ilo iclt] .
  from inv have dist: "distinct (map (\<lambda>(v,oc,ic). v) (ds_stk s))"
    and seen: "\<forall>(v,oc,ic)\<in>set (ds_stk s). ds_seen s ! v"
    and prnt: "\<forall>v<Suc vcount. ds_prnt s ! v < Suc vcount" by (auto simp: dref_inv_def)
  show ?thesis
  proof (cases "ds_seen s ! ?w")
    case True
    thus ?thesis using inv stk by (auto simp: dref_inv_def bd_upd2_def Let_def)
  next
    case False
    have wnotin: "?w \<notin> set (map (\<lambda>(v,oc,ic). v) (ds_stk s))"
      using False seen by (auto split: prod.splits)
    have eq: "bd_upd2 fl s = dfs_discover (s\<lparr>ds_stk := (v, oc, Suc ic) # rest\<rparr>) v ?w ?e"
      using stk False by (simp add: bd_upd2_def Let_def)
    show ?thesis unfolding eq
      using wnotin dist seen prnt vlt wlt stk lens
      by (auto simp: dref_inv_def dfs_discover_def Let_def nth_list_update split: prod.splits if_splits)
  qed
qed

lemma bd_upd3_dref:
  assumes "dref_inv s" "bd_call3_conds fl s"
  shows "dref_inv (bd_upd3 s)"
proof -
  from assms(2) obtain v oc ic rest where stk: "ds_stk s = (v,oc,ic)#rest"
    by (auto simp: bd_call3_conds_def split: list.splits prod.splits)
  show ?thesis using assms(1) stk
    by (auto simp: dref_inv_def bd_upd3_def dfs_finish_def Let_def)
qed

text \<open>The empty-stack (return) case: when @{term \<open>ds_stk s = []\<close>} the flat fill pointer is @{term 0}
      (@{thm stk_rel_nil}), so @{const build_dfs_a_imp} reads it, takes the @{term \<open>sp = 0\<close>} branch and
      returns, leaving the state relation untouched.\<close>
lemma build_dfs_a_imp_ret:
  assumes "ds_stk s = []"
  shows "<dfs_rel fl0 es0 oe oh ie ih st s> build_dfs_a_imp st <\<lambda>_. dfs_rel fl0 es0 oe oh ie ih st s>"
  apply (subst build_dfs_a_imp.simps)
  unfolding dfs_rel_def
  apply (sep_auto simp: assms)
  done

text \<open>Field-exposure reads: each recovers one field out of the folded @{const dfs_rel} while framing the
      rest, so the loop body's array / reference reads compose with the folded discovery and finishing
      triples.  The three stack reads use @{thm stk_rel_cons_simp} to pin the top-frame values.\<close>
lemma dfs_rel_sp:
  "<dfs_rel fl0 es0 oe oh ie ih st s> Ref.lookup (di_sp st) <\<lambda>r. dfs_rel fl0 es0 oe oh ie ih st s * \<up>(r = length (ds_stk s))>"
  unfolding dfs_rel_def
  apply (sep_auto)
  apply (subgoal_tac "sp = length (ds_stk s)")
   apply (sep_auto)
  apply (metis stk_rel_len)
  done

lemma dfs_rel_sv:
  assumes "ds_stk s = (v,oc,ic)#rest"
  shows "<dfs_rel fl0 es0 oe oh ie ih st s> Array.nth (di_sv st) (length rest) <\<lambda>r. dfs_rel fl0 es0 oe oh ie ih st s * \<up>(r = v)>"
  unfolding dfs_rel_def by (sep_auto simp: assms stk_rel_cons_simp)

lemma dfs_rel_soc:
  assumes "ds_stk s = (v,oc,ic)#rest"
  shows "<dfs_rel fl0 es0 oe oh ie ih st s> Array.nth (di_soc st) (length rest) <\<lambda>r. dfs_rel fl0 es0 oe oh ie ih st s * \<up>(r = oc)>"
  unfolding dfs_rel_def by (sep_auto simp: assms stk_rel_cons_simp)

lemma dfs_rel_sic:
  assumes "ds_stk s = (v,oc,ic)#rest"
  shows "<dfs_rel fl0 es0 oe oh ie ih st s> Array.nth (di_sic st) (length rest) <\<lambda>r. dfs_rel fl0 es0 oe oh ie ih st s * \<up>(r = ic)>"
  unfolding dfs_rel_def by (sep_auto simp: assms stk_rel_cons_simp)

lemma dfs_rel_ohi:
  assumes "v < length oh"
  shows "<dfs_rel fl0 es0 oe oh ie ih st s> Array.nth (di_ohi st) v <\<lambda>r. dfs_rel fl0 es0 oe oh ie ih st s * \<up>(r = oh!v)>"
  unfolding dfs_rel_def by (sep_auto simp: assms)

lemma dfs_rel_ihi:
  assumes "v < length ih"
  shows "<dfs_rel fl0 es0 oe oh ie ih st s> Array.nth (di_ihi st) v <\<lambda>r. dfs_rel fl0 es0 oe oh ie ih st s * \<up>(r = ih!v)>"
  unfolding dfs_rel_def by (sep_auto simp: assms)

lemma dfs_rel_oe:
  assumes "oc < length oe"
  shows "<dfs_rel fl0 es0 oe oh ie ih st s> Array.nth (di_oe st) oc <\<lambda>r. dfs_rel fl0 es0 oe oh ie ih st s * \<up>(r = oe!oc)>"
  unfolding dfs_rel_def by (sep_auto simp: assms)

lemma dfs_rel_ie:
  assumes "ic < length ie"
  shows "<dfs_rel fl0 es0 oe oh ie ih st s> Array.nth (di_ie st) ic <\<lambda>r. dfs_rel fl0 es0 oe oh ie ih st s * \<up>(r = ie!ic)>"
  unfolding dfs_rel_def by (sep_auto simp: assms)

lemma dfs_rel_snd:
  assumes "e < m"
  shows "<dfs_rel fl0 es0 oe oh ie ih st s> Array.nth (di_snd st) e <\<lambda>r. dfs_rel fl0 es0 oe oh ie ih st s * \<up>(r = snd_list!e)>"
  unfolding dfs_rel_def
  by (sep_auto simp: assms)

lemma dfs_rel_fst:
  assumes "e < m"
  shows "<dfs_rel fl0 es0 oe oh ie ih st s> Array.nth (di_fst st) e <\<lambda>r. dfs_rel fl0 es0 oe oh ie ih st s * \<up>(r = fst_list!e)>"
  unfolding dfs_rel_def
  by (sep_auto simp: assms)

lemma dfs_rel_seen:
  assumes "w < length (ds_seen s)"
  shows "<dfs_rel fl0 es0 oe oh ie ih st s> Array.nth (di_seen st) w <\<lambda>r. dfs_rel fl0 es0 oe oh ie ih st s * \<up>(r = ds_seen s ! w)>"
  unfolding dfs_rel_def by (sep_auto simp: assms)

text \<open>The two in-place cursor bumps: writing @{term \<open>Suc oc\<close>} / @{term \<open>Suc ic\<close>} at the top frame index
      advances that frame's out- / in-cursor, turning the relation of @{term s} into that of the
      single-cursor-advanced state (@{thm stk_rel_upd_ge} / @{thm stk_rel_upd_ge_sic}).\<close>
lemma dfs_rel_bump_soc:
  assumes "ds_stk s = (v,oc,ic)#rest"
  shows "<dfs_rel fl0 es0 oe oh ie ih st s> arr_upd (di_soc st) (length rest) (Suc oc)
         <\<lambda>_. dfs_rel fl0 es0 oe oh ie ih st (s\<lparr>ds_stk := (v, Suc oc, ic) # rest\<rparr>)>"
  unfolding dfs_rel_def
  by (sep_auto simp: assms stk_rel_cons_simp nth_list_update stk_rel_upd_ge)

lemma dfs_rel_bump_sic:
  assumes "ds_stk s = (v,oc,ic)#rest"
  shows "<dfs_rel fl0 es0 oe oh ie ih st s> arr_upd (di_sic st) (length rest) (Suc ic)
         <\<lambda>_. dfs_rel fl0 es0 oe oh ie ih st (s\<lparr>ds_stk := (v, oc, Suc ic) # rest\<rparr>)>"
  unfolding dfs_rel_def
  by (sep_auto simp: assms stk_rel_cons_simp nth_list_update stk_rel_upd_ge_sic)

text \<open>The four recursive-step lemmas of the DFS loop, one per call condition of @{const build_dfs_a}: an
      outgoing / ingoing free edge to a fresh (@{text unseen}) or already discovered (@{text seen})
      neighbour, and the vertex-finishing step.  Each drives @{const build_dfs_a_imp}'s body one
      iteration through the field-exposure reads to the recursive call, which the induction hypothesis
      (@{term IH}) discharges.\<close>
lemma call1_seen:
  assumes stk: "ds_stk s = (v,oc,ic)#rest" and oclt: "oc < free_out_hi fl ! v"
    and vlt: "v < vcount" and olo: "out_lo ! v \<le> oc"
    and seen: "ds_seen s ! (snd_list ! (free_out_edges fl ! oc))"
    and sz: "dfs_sized s"
    and IH: "<dfs_rel fl0 es0 (free_out_edges fl)(free_out_hi fl)(free_in_edges fl)(free_in_hi fl) st (s\<lparr>ds_stk := (v, Suc oc, ic) # rest\<rparr>)>
               build_dfs_a_imp st
             <\<lambda>_. dfs_rel fl0 es0 (free_out_edges fl)(free_out_hi fl)(free_in_edges fl)(free_in_hi fl) st (build_dfs fl (s\<lparr>ds_stk := (v, Suc oc, ic) # rest\<rparr>))>"
  shows "<dfs_rel fl0 es0 (free_out_edges fl)(free_out_hi fl)(free_in_edges fl)(free_in_hi fl) st s>
           build_dfs_a_imp st
         <\<lambda>_. dfs_rel fl0 es0 (free_out_edges fl)(free_out_hi fl)(free_in_edges fl)(free_in_hi fl) st (build_dfs fl (s\<lparr>ds_stk := (v, Suc oc, ic) # rest\<rparr>))>"
proof -
  have elt: "free_out_edges fl ! oc < m" using free_out_edge_fst[OF vlt olo oclt] by simp
  have ocm0: "oc < m" using oclt free_out_hi_le_m[OF vlt] by (meson less_le_trans)
  have ocm: "oc < length (free_out_edges fl)" using ocm0 length_free_out_edges by simp
  have wvc': "snd_list ! (free_out_edges fl ! oc) < Suc vcount" using Hout_valid[OF vlt olo oclt] by simp
  from sz have lseen: "length (ds_seen s) = Suc vcount" by (simp add: dfs_sized_def)
  show ?thesis
    apply (subst build_dfs_a_imp.simps)
    apply (sep_auto
        heap: dfs_rel_sp dfs_rel_sv dfs_rel_soc dfs_rel_ohi dfs_rel_oe dfs_rel_snd dfs_rel_bump_soc dfs_rel_seen IH
        simp: stk vlt olo oclt seen elt ocm ocm0 wvc' lseen length_free_out_hi)
    done
qed

lemma call1_unseen:
  assumes stk: "ds_stk s = (v,oc,ic)#rest" and oclt: "oc < free_out_hi fl ! v"
    and vlt: "v < vcount" and olo: "out_lo ! v \<le> oc"
    and unseen: "\<not> ds_seen s ! (snd_list ! (free_out_edges fl ! oc))"
    and sz: "dfs_sized s" and wf: "dfs_wf s" and dref: "dref_inv s"
    and IH: "<dfs_rel fl0 es0 (free_out_edges fl)(free_out_hi fl)(free_in_edges fl)(free_in_hi fl) st (bd_upd1 fl s)>
               build_dfs_a_imp st
             <\<lambda>_. dfs_rel fl0 es0 (free_out_edges fl)(free_out_hi fl)(free_in_edges fl)(free_in_hi fl) st (build_dfs fl (bd_upd1 fl s))>"
  shows "<dfs_rel fl0 es0 (free_out_edges fl)(free_out_hi fl)(free_in_edges fl)(free_in_hi fl) st s>
           build_dfs_a_imp st
         <\<lambda>_. dfs_rel fl0 es0 (free_out_edges fl)(free_out_hi fl)(free_in_edges fl)(free_in_hi fl) st (build_dfs fl (bd_upd1 fl s))>"
proof -
  define e where "e = free_out_edges fl ! oc"
  define w where "w = snd_list ! e"
  have elt: "e < m" unfolding e_def using free_out_edge_fst[OF vlt olo oclt] by simp
  have ocm0: "oc < m" using oclt free_out_hi_le_m[OF vlt] by (meson less_le_trans)
  have ocm: "oc < length (free_out_edges fl)" using ocm0 length_free_out_edges by simp
  have wvc: "w < vcount" unfolding w_def e_def using Hout_valid[OF vlt olo oclt] .
  have wvc': "w < Suc vcount" using wvc by simp
  have vsuc: "v < Suc vcount" using vlt by simp
  from sz have lens: "length (ds_seen s) = Suc vcount" "length (ds_prnt s) = Suc vcount"
    "length (ds_par s) = Suc vcount" "length (ds_dir s) = Suc vcount" "length (ds_pot s) = Suc vcount"
    "length (ds_thrd s) = Suc vcount" "length (ds_rvth s) = Suc vcount" "length (ds_snum s) = Suc vcount"
    by (simp_all add: dfs_sized_def)
  have dist: "distinct (map (\<lambda>(v,oc,ic).v) (ds_stk s))" using dref by (simp add: dref_inv_def)
  have vts: "\<forall>(v,oc,ic)\<in>set (ds_stk s). v < vcount" using wf by (auto simp: dfs_wf_def)
  have dpth1: "Suc (length rest) < Suc vcount" using stk_depth_le[OF dist vts] stk by simp
  have dpth2: "length rest < vcount" using dpth1 by simp
  have pvlt: "ds_prev s < Suc vcount" using dref by (simp add: dref_inv_def)
  have bu: "bd_upd1 fl s = dfs_discover (s\<lparr>ds_stk := (v, Suc oc, ic) # rest\<rparr>) v w e"
    using stk unseen by (simp add: bd_upd1_def Let_def e_def w_def)
  have unseen': "\<not> ds_seen s ! w" unfolding w_def e_def using unseen .
  note disc = dfs_discover_imp_rule[where st=st and s="s\<lparr>ds_stk := (v, Suc oc, ic) # rest\<rparr>" and v=v and w=w and e=e]
  show ?thesis
    unfolding bu
    apply (subst build_dfs_a_imp.simps)
    apply (sep_auto
        heap: dfs_rel_sp dfs_rel_sv dfs_rel_soc dfs_rel_ohi dfs_rel_oe dfs_rel_snd dfs_rel_bump_soc dfs_rel_seen disc IH[unfolded bu]
        simp: stk vlt olo oclt unseen unseen' elt ocm ocm0 wvc wvc' vsuc lens dpth1 dpth2 pvlt e_def[symmetric] w_def[symmetric] length_free_out_hi)
    done
qed

lemma call2_seen:
  assumes stk: "ds_stk s = (v,oc,ic)#rest"
    and ocge: "\<not> oc < free_out_hi fl ! v" and iclt: "ic < free_in_hi fl ! v"
    and vlt: "v < vcount" and ilo: "in_lo ! v \<le> ic"
    and seen: "ds_seen s ! (fst_list ! (free_in_edges fl ! ic))"
    and sz: "dfs_sized s"
    and IH: "<dfs_rel fl0 es0 (free_out_edges fl)(free_out_hi fl)(free_in_edges fl)(free_in_hi fl) st (s\<lparr>ds_stk := (v, oc, Suc ic) # rest\<rparr>)>
               build_dfs_a_imp st
             <\<lambda>_. dfs_rel fl0 es0 (free_out_edges fl)(free_out_hi fl)(free_in_edges fl)(free_in_hi fl) st (build_dfs fl (s\<lparr>ds_stk := (v, oc, Suc ic) # rest\<rparr>))>"
  shows "<dfs_rel fl0 es0 (free_out_edges fl)(free_out_hi fl)(free_in_edges fl)(free_in_hi fl) st s>
           build_dfs_a_imp st
         <\<lambda>_. dfs_rel fl0 es0 (free_out_edges fl)(free_out_hi fl)(free_in_edges fl)(free_in_hi fl) st (build_dfs fl (s\<lparr>ds_stk := (v, oc, Suc ic) # rest\<rparr>))>"
proof -
  have elt: "free_in_edges fl ! ic < m" using free_in_edge_snd[OF vlt ilo iclt] by simp
  have icm0: "ic < m" using iclt free_in_hi_le_m[OF vlt] by (meson less_le_trans)
  have icm: "ic < length (free_in_edges fl)" using icm0 length_free_in_edges by simp
  have wvc': "fst_list ! (free_in_edges fl ! ic) < Suc vcount" using Hin_valid[OF vlt ilo iclt] by simp
  from sz have lseen: "length (ds_seen s) = Suc vcount" by (simp add: dfs_sized_def)
  show ?thesis
    apply (subst build_dfs_a_imp.simps)
    apply (sep_auto
        heap: dfs_rel_sp dfs_rel_sv dfs_rel_soc dfs_rel_ohi dfs_rel_sic dfs_rel_ihi dfs_rel_ie dfs_rel_fst dfs_rel_bump_sic dfs_rel_seen IH
        simp: stk vlt ilo ocge iclt seen elt icm icm0 wvc' lseen length_free_out_hi length_free_in_hi)
    done
qed

lemma call2_unseen:
  assumes stk: "ds_stk s = (v,oc,ic)#rest"
    and ocge: "\<not> oc < free_out_hi fl ! v" and iclt: "ic < free_in_hi fl ! v"
    and vlt: "v < vcount" and ilo: "in_lo ! v \<le> ic"
    and unseen: "\<not> ds_seen s ! (fst_list ! (free_in_edges fl ! ic))"
    and sz: "dfs_sized s" and wf: "dfs_wf s" and dref: "dref_inv s"
    and IH: "<dfs_rel fl0 es0 (free_out_edges fl)(free_out_hi fl)(free_in_edges fl)(free_in_hi fl) st (bd_upd2 fl s)>
               build_dfs_a_imp st
             <\<lambda>_. dfs_rel fl0 es0 (free_out_edges fl)(free_out_hi fl)(free_in_edges fl)(free_in_hi fl) st (build_dfs fl (bd_upd2 fl s))>"
  shows "<dfs_rel fl0 es0 (free_out_edges fl)(free_out_hi fl)(free_in_edges fl)(free_in_hi fl) st s>
           build_dfs_a_imp st
         <\<lambda>_. dfs_rel fl0 es0 (free_out_edges fl)(free_out_hi fl)(free_in_edges fl)(free_in_hi fl) st (build_dfs fl (bd_upd2 fl s))>"
proof -
  define e where "e = free_in_edges fl ! ic"
  define w where "w = fst_list ! e"
  have elt: "e < m" unfolding e_def using free_in_edge_snd[OF vlt ilo iclt] by simp
  have icm0: "ic < m" using iclt free_in_hi_le_m[OF vlt] by (meson less_le_trans)
  have icm: "ic < length (free_in_edges fl)" using icm0 length_free_in_edges by simp
  have wvc: "w < vcount" unfolding w_def e_def using Hin_valid[OF vlt ilo iclt] .
  have wvc': "w < Suc vcount" using wvc by simp
  have vsuc: "v < Suc vcount" using vlt by simp
  from sz have lens: "length (ds_seen s) = Suc vcount" "length (ds_prnt s) = Suc vcount"
    "length (ds_par s) = Suc vcount" "length (ds_dir s) = Suc vcount" "length (ds_pot s) = Suc vcount"
    "length (ds_thrd s) = Suc vcount" "length (ds_rvth s) = Suc vcount" "length (ds_snum s) = Suc vcount"
    by (simp_all add: dfs_sized_def)
  have dist: "distinct (map (\<lambda>(v,oc,ic).v) (ds_stk s))" using dref by (simp add: dref_inv_def)
  have vts: "\<forall>(v,oc,ic)\<in>set (ds_stk s). v < vcount" using wf by (auto simp: dfs_wf_def)
  have dpth1: "Suc (length rest) < Suc vcount" using stk_depth_le[OF dist vts] stk by simp
  have dpth2: "length rest < vcount" using dpth1 by simp
  have pvlt: "ds_prev s < Suc vcount" using dref by (simp add: dref_inv_def)
  have bu: "bd_upd2 fl s = dfs_discover (s\<lparr>ds_stk := (v, oc, Suc ic) # rest\<rparr>) v w e"
    using stk unseen by (simp add: bd_upd2_def Let_def e_def w_def)
  have unseen': "\<not> ds_seen s ! w" unfolding w_def e_def using unseen .
  note disc = dfs_discover_imp_rule[where st=st and s="s\<lparr>ds_stk := (v, oc, Suc ic) # rest\<rparr>" and v=v and w=w and e=e]
  show ?thesis
    unfolding bu
    apply (subst build_dfs_a_imp.simps)
    apply (sep_auto
        heap: dfs_rel_sp dfs_rel_sv dfs_rel_soc dfs_rel_ohi dfs_rel_sic dfs_rel_ihi dfs_rel_ie dfs_rel_fst dfs_rel_bump_sic dfs_rel_seen disc IH[unfolded bu]
        simp: stk vlt ilo ocge iclt unseen unseen' elt icm icm0 wvc wvc' vsuc lens dpth1 dpth2 pvlt e_def[symmetric] w_def[symmetric] length_free_out_hi length_free_in_hi)
    done
qed

lemma call3_step:
  assumes stk: "ds_stk s = (v,oc,ic)#rest"
    and ocge: "\<not> oc < free_out_hi fl ! v" and icge: "\<not> ic < free_in_hi fl ! v"
    and vlt: "v < vcount"
    and sz: "dfs_sized s" and dref: "dref_inv s"
    and IH: "<dfs_rel fl0 es0 (free_out_edges fl)(free_out_hi fl)(free_in_edges fl)(free_in_hi fl) st (bd_upd3 s)>
               build_dfs_a_imp st
             <\<lambda>_. dfs_rel fl0 es0 (free_out_edges fl)(free_out_hi fl)(free_in_edges fl)(free_in_hi fl) st (build_dfs fl (bd_upd3 s))>"
  shows "<dfs_rel fl0 es0 (free_out_edges fl)(free_out_hi fl)(free_in_edges fl)(free_in_hi fl) st s>
           build_dfs_a_imp st
         <\<lambda>_. dfs_rel fl0 es0 (free_out_edges fl)(free_out_hi fl)(free_in_edges fl)(free_in_hi fl) st (build_dfs fl (bd_upd3 s))>"
proof -
  have vsuc: "v < Suc vcount" using vlt by simp
  from sz have lens: "length (ds_prnt s) = Suc vcount" "length (ds_lsuc s) = Suc vcount"
    "length (ds_snum s) = Suc vcount" by (simp_all add: dfs_sized_def)
  have plt: "ds_prnt s ! v < Suc vcount" using dref vsuc by (simp add: dref_inv_def)
  have bu: "bd_upd3 s = dfs_finish s v rest" using stk by (simp add: bd_upd3_def)
  note fin = dfs_finish_imp_rule[where st=st and s=s and v=v and oc=oc and ic=ic and rest=rest]
  show ?thesis
    unfolding bu
    apply (subst build_dfs_a_imp.simps)
    apply (sep_auto
        heap: dfs_rel_sp dfs_rel_sv dfs_rel_soc dfs_rel_ohi dfs_rel_sic dfs_rel_ihi fin IH[unfolded bu]
        simp: stk vlt vsuc ocge icge lens plt length_free_out_hi length_free_in_hi)
    done
qed

text \<open>\<^emph>\<open>Layer (d.5) target.\<close>  The imperative free-edge traversal @{const build_dfs_a_imp} refines the
      functional @{const build_dfs}: by domain induction over the recursion (@{thm bd_induct}), each call
      condition dispatched to its step lemma with the invariants @{const dfs_wf} / @{const dfs_sized} /
      @{const dref_inv} carried and re-established by the @{text bd_upd} preservation lemmas.\<close>
lemma build_dfs_a_imp_rule:
  assumes dom: "build_dfs_dom (fl, s)" and "dfs_wf s" "dfs_sized s" "dref_inv s"
  shows "<dfs_rel fl0 es0 (free_out_edges fl)(free_out_hi fl)(free_in_edges fl)(free_in_hi fl) st s>
      build_dfs_a_imp st
    <\<lambda>_. dfs_rel fl0 es0 (free_out_edges fl)(free_out_hi fl)(free_in_edges fl)(free_in_hi fl) st (build_dfs fl s)>"
  using assms(2-4)
proof (induct rule: bd_induct[OF dom])
  case IH: (1 fl s)
  note IH1 = IH(2) and IH2 = IH(3) and IH3 = IH(4)
  note wf = IH(5) and sz = IH(6) and dref = IH(7)
  show ?case
  proof (rule bd_cases[where s=s and fl=fl])
    assume c: "bd_call1_conds fl s"
    then obtain v oc ic rest where stk: "ds_stk s = (v,oc,ic)#rest" and oclt: "oc < free_out_hi fl ! v"
      by (auto simp: bd_call1_conds_def split: list.splits prod.splits)
    from wf stk have vlt: "v < vcount" and olo: "out_lo ! v \<le> oc" by (auto simp: dfs_wf_def)
    have IH1': "<dfs_rel fl0 es0 (free_out_edges fl)(free_out_hi fl)(free_in_edges fl)(free_in_hi fl) st (bd_upd1 fl s)>
                  build_dfs_a_imp st
                <\<lambda>_. dfs_rel fl0 es0 (free_out_edges fl)(free_out_hi fl)(free_in_edges fl)(free_in_hi fl) st (build_dfs fl (bd_upd1 fl s))>"
      using IH1[OF c bd_upd1_wf[OF Hout_valid wf c] bd_upd1_sized[OF sz c] bd_upd1_dref[OF dref wf sz c]] .
    show ?thesis
    proof (cases "ds_seen s ! (snd_list ! (free_out_edges fl ! oc))")
      case True
      have s1: "bd_upd1 fl s = s\<lparr>ds_stk := (v, Suc oc, ic) # rest\<rparr>" using stk True by (simp add: bd_upd1_def Let_def)
      show ?thesis unfolding bd_simps(1)[OF IH(1) c] s1
        using call1_seen[OF stk oclt vlt olo True sz IH1'[unfolded s1]] .
    next
      case False
      show ?thesis unfolding bd_simps(1)[OF IH(1) c]
        using call1_unseen[OF stk oclt vlt olo False sz wf dref IH1'] .
    qed
  next
    assume c: "bd_call2_conds fl s"
    then obtain v oc ic rest where stk: "ds_stk s = (v,oc,ic)#rest"
        and ocge: "\<not> oc < free_out_hi fl ! v" and iclt: "ic < free_in_hi fl ! v"
      by (auto simp: bd_call2_conds_def split: list.splits prod.splits)
    from wf stk have vlt: "v < vcount" and ilo: "in_lo ! v \<le> ic" by (auto simp: dfs_wf_def)
    have IH2': "<dfs_rel fl0 es0 (free_out_edges fl)(free_out_hi fl)(free_in_edges fl)(free_in_hi fl) st (bd_upd2 fl s)>
                  build_dfs_a_imp st
                <\<lambda>_. dfs_rel fl0 es0 (free_out_edges fl)(free_out_hi fl)(free_in_edges fl)(free_in_hi fl) st (build_dfs fl (bd_upd2 fl s))>"
      using IH2[OF c bd_upd2_wf[OF Hin_valid wf c] bd_upd2_sized[OF sz c] bd_upd2_dref[OF dref wf sz c]] .
    show ?thesis
    proof (cases "ds_seen s ! (fst_list ! (free_in_edges fl ! ic))")
      case True
      have s1: "bd_upd2 fl s = s\<lparr>ds_stk := (v, oc, Suc ic) # rest\<rparr>" using stk True by (simp add: bd_upd2_def Let_def)
      show ?thesis unfolding bd_simps(2)[OF IH(1) c] s1
        using call2_seen[OF stk ocge iclt vlt ilo True sz IH2'[unfolded s1]] .
    next
      case False
      show ?thesis unfolding bd_simps(2)[OF IH(1) c]
        using call2_unseen[OF stk ocge iclt vlt ilo False sz wf dref IH2'] .
    qed
  next
    assume c: "bd_call3_conds fl s"
    then obtain v oc ic rest where stk: "ds_stk s = (v,oc,ic)#rest"
        and ocge: "\<not> oc < free_out_hi fl ! v" and icge: "\<not> ic < free_in_hi fl ! v"
      by (auto simp: bd_call3_conds_def split: list.splits prod.splits)
    from wf stk have vlt: "v < vcount" by (auto simp: dfs_wf_def)
    have IH3': "<dfs_rel fl0 es0 (free_out_edges fl)(free_out_hi fl)(free_in_edges fl)(free_in_hi fl) st (bd_upd3 s)>
                  build_dfs_a_imp st
                <\<lambda>_. dfs_rel fl0 es0 (free_out_edges fl)(free_out_hi fl)(free_in_edges fl)(free_in_hi fl) st (build_dfs fl (bd_upd3 s))>"
      using IH3[OF c bd_upd3_wf[OF wf c] bd_upd3_sized[OF sz c] bd_upd3_dref[OF dref c]] .
    show ?thesis unfolding bd_simps(3)[OF IH(1) c]
      using call3_step[OF stk ocge icge vlt sz dref IH3'] .
  next
    assume c: "bd_ret_conds s"
    show ?thesis
      using build_dfs_a_imp_ret[of s] c bd_simps(4)[OF IH(1) c]
      by (simp add: bd_ret_conds_def)
  qed
qed

subsection \<open>Layer (d.6): the artificial-edge writers refine @{const open_tree_component} / @{const emit_U_edge}\<close>

text \<open>Writing one artificial-edge field at index @{term \<open>m + ds_nxt s\<close>} refines the functional
      list-update of @{const ds_afst} at @{term \<open>ds_nxt s\<close>}: the write lands past the real block, so the
      real-prefix pins and the already-emitted artificial entries (indices @{term \<open>k < ds_nxt s\<close>}) are
      untouched.\<close>
lemma dfs_rel_afst:
  assumes "ds_nxt s < length (ds_afst s)"
  shows "<dfs_rel fl0 es0 oe oh ie ih st s> arr_upd (di_fst st) (m + ds_nxt s) x
         <\<lambda>_. dfs_rel fl0 es0 oe oh ie ih st (s\<lparr>ds_afst := list_update (ds_afst s) (ds_nxt s) x\<rparr>)>"
  unfolding dfs_rel_def
  apply (sep_auto simp: assms nth_list_update)
   apply (meson assms add_strict_left_mono less_le_trans)
  apply (sep_auto simp: assms nth_list_update)
  done

text \<open>The whole artificial-edge emission: the five field writes at @{term \<open>m + ds_nxt s\<close>} followed by the
      @{const di_nxt} bump refine appending one edge to the five artificial arrays and advancing
      @{const ds_nxt}.  The bump extends the artificial invariant to the new index @{term \<open>ds_nxt s\<close>},
      whose entry is exactly the value just written into each array.  The write-position bounds hold
      because each augmented array is at least @{term \<open>m + length (ds_afst s)\<close>} long and @{term \<open>ds_nxt s\<close>}
      is in range.\<close>
lemma dfs_rel_emit_art:
  assumes af: "ds_nxt s < length (ds_afst s)" and asd: "ds_nxt s < length (ds_asnd s)"
    and ac: "ds_nxt s < length (ds_acap s)" and afl: "ds_nxt s < length (ds_aflw s)"
    and ae: "ds_nxt s < length (ds_aest s)"
  shows "<dfs_rel fl0 es0 oe oh ie ih st s>
           do { _ \<leftarrow> arr_upd (di_fst st) (m + ds_nxt s) xf;
                _ \<leftarrow> arr_upd (di_snd st) (m + ds_nxt s) xs;
                _ \<leftarrow> arr_upd (di_cap st) (m + ds_nxt s) xc;
                _ \<leftarrow> arr_upd (di_flow st) (m + ds_nxt s) xw;
                _ \<leftarrow> arr_upd (di_es st) (m + ds_nxt s) xe;
                Ref.update (di_nxt st) (Suc (ds_nxt s)) }
         <\<lambda>_. dfs_rel fl0 es0 oe oh ie ih st
                (s\<lparr> ds_afst := list_update (ds_afst s) (ds_nxt s) xf,
                    ds_asnd := list_update (ds_asnd s) (ds_nxt s) xs,
                    ds_acap := list_update (ds_acap s) (ds_nxt s) xc,
                    ds_aflw := list_update (ds_aflw s) (ds_nxt s) xw,
                    ds_aest := list_update (ds_aest s) (ds_nxt s) xe,
                    ds_nxt := Suc (ds_nxt s) \<rparr>)>"
  unfolding dfs_rel_def
  apply (sep_auto simp: nth_list_update less_Suc_eq)
   apply (meson af add_strict_left_mono less_le_trans)
  apply (sep_auto simp: nth_list_update less_Suc_eq)
   apply (meson asd add_strict_left_mono less_le_trans)
  apply (sep_auto simp: nth_list_update less_Suc_eq)
   apply (meson ac add_strict_left_mono less_le_trans)
  apply (sep_auto simp: nth_list_update less_Suc_eq)
   apply (meson afl add_strict_left_mono less_le_trans)
  apply (sep_auto simp: nth_list_update less_Suc_eq)
   apply (meson ae add_strict_left_mono less_le_trans)
  apply (sep_auto simp: nth_list_update less_Suc_eq af asd ac afl ae)
  apply (subgoal_tac "m + ds_nxt s < length fsta \<and> m + ds_nxt s < length snda \<and> m + ds_nxt s < length capa \<and> m + ds_nxt s < length flowa \<and> m + ds_nxt s < length esa")
   apply (sep_auto simp: nth_list_update)
  apply (thin_tac "_ \<Turnstile> _", meson af add_strict_left_mono less_le_trans)
  apply (thin_tac "_ \<Turnstile> _", meson asd add_strict_left_mono less_le_trans)
  apply (thin_tac "_ \<Turnstile> _", meson ac add_strict_left_mono less_le_trans)
  apply (thin_tac "_ \<Turnstile> _", meson afl add_strict_left_mono less_le_trans)
  apply (thin_tac "_ \<Turnstile> _", meson ae add_strict_left_mono less_le_trans)
  done

text \<open>Finalising the opened vertex @{term c}'s tree fields (parent @{term \<open>m + nxt\<close>}, potential seed
      @{term pot_c}, thread link after the previous vertex @{term pv}) — nine straight vertex-array
      writes that leave the artificial region and the stack untouched.\<close>
lemma dfs_rel_open_fields:
  assumes "c < length (ds_seen s)" "c < length (ds_prnt s)" "c < length (ds_par s)" "c < length (ds_dir s)"
    "c < length (ds_pot s)" "pv < length (ds_thrd s)" "c < length (ds_rvth s)" "c < length (ds_snum s)"
  shows "<dfs_rel fl0 es0 oe oh ie ih st s>
           do { _ \<leftarrow> arr_upd (di_seen st) c True;
                _ \<leftarrow> arr_upd (prnt_impl (di_tree st)) c vcount;
                _ \<leftarrow> arr_upd (di_par st) c aidx;
                _ \<leftarrow> arr_upd (di_dir st) c up;
                _ \<leftarrow> arr_upd (di_pot st) c pot_c;
                _ \<leftarrow> arr_upd (thrd_impl (di_tree st)) pv c;
                _ \<leftarrow> arr_upd (rvth_impl (di_tree st)) c pv;
                _ \<leftarrow> arr_upd (snum_impl (di_tree st)) c 1;
                Ref.update (di_prev st) c }
         <\<lambda>_. dfs_rel fl0 es0 oe oh ie ih st
                (s\<lparr> ds_seen := list_update (ds_seen s) c True, ds_prnt := list_update (ds_prnt s) c vcount,
                    ds_par := list_update (ds_par s) c aidx, ds_dir := list_update (ds_dir s) c up,
                    ds_pot := list_update (ds_pot s) c pot_c, ds_thrd := list_update (ds_thrd s) pv c,
                    ds_rvth := list_update (ds_rvth s) c pv, ds_snum := list_update (ds_snum s) c 1,
                    ds_prev := c \<rparr>)>"
  unfolding dfs_rel_def
  apply (sep_auto simp: assms)
  done

text \<open>Seeding the DFS with a single root frame @{term \<open>(c, olo, ilo)\<close>}: three writes at index @{term 0}
      and setting the fill pointer to @{term 1} establish the single-frame stack \<open>[(c, olo, ilo)]\<close>.\<close>
lemma dfs_rel_seed_stack:
  "<dfs_rel fl0 es0 oe oh ie ih st s>
     do { _ \<leftarrow> arr_upd (di_sv st) 0 c; _ \<leftarrow> arr_upd (di_soc st) 0 olo;
          _ \<leftarrow> arr_upd (di_sic st) 0 ilo; Ref.update (di_sp st) 1 }
   <\<lambda>_. dfs_rel fl0 es0 oe oh ie ih st (s\<lparr>ds_stk := [(c, olo, ilo)]\<rparr>)>"
  unfolding dfs_rel_def
  apply (sep_auto simp: stk_rel_cons_simp nth_list_update stk_rel_nil)
  done

text \<open>Framed reads of the two references and the two CSR block-start arrays the opener consults.\<close>
lemma dfs_rel_rd_nxt:
  "<dfs_rel fl0 es0 oe oh ie ih st s> Ref.lookup (di_nxt st) <\<lambda>r. dfs_rel fl0 es0 oe oh ie ih st s * \<up>(r = ds_nxt s)>"
  unfolding dfs_rel_def by sep_auto

lemma dfs_rel_rd_prev:
  "<dfs_rel fl0 es0 oe oh ie ih st s> Ref.lookup (di_prev st) <\<lambda>r. dfs_rel fl0 es0 oe oh ie ih st s * \<up>(r = ds_prev s)>"
  unfolding dfs_rel_def by sep_auto

lemma dfs_rel_olo:
  assumes "c < length out_lo"
  shows "<dfs_rel fl0 es0 oe oh ie ih st s> Array.nth (di_olo st) c <\<lambda>r. dfs_rel fl0 es0 oe oh ie ih st s * \<up>(r = out_lo!c)>"
  unfolding dfs_rel_def by (sep_auto simp: assms)

lemma dfs_rel_ilo:
  assumes "c < length in_lo"
  shows "<dfs_rel fl0 es0 oe oh ie ih st s> Array.nth (di_ilo st) c <\<lambda>r. dfs_rel fl0 es0 oe oh ie ih st s * \<up>(r = in_lo!c)>"
  unfolding dfs_rel_def by (sep_auto simp: assms)

text \<open>The pre-DFS state @{const open_tree_component} hands to @{const build_dfs}: the opened vertex
      @{term c}'s artificial tree edge written at slot @{term \<open>ds_nxt s\<close>}, its tree fields set, and the
      DFS seeded with the single root frame.  Naming it lets the imperative opener's refinement target
      @{term \<open>build_dfs fl (otc_pre fl s c)\<close>} and reuse @{thm build_dfs_a_imp_rule}.\<close>
definition otc_pre :: "'n list \<Rightarrow> 'n dfs_state \<Rightarrow> nat \<Rightarrow> 'n dfs_state" where
  "otc_pre fl s c =
     (let imb = imbalance ! c; up = 0 \<le> imb; af = \<bar>imb\<bar>; cp = (if up then af + 1 else af); pv = ds_prev s
      in s\<lparr> ds_afst := list_update (ds_afst s) (ds_nxt s) (if up then c else vcount),
            ds_asnd := list_update (ds_asnd s) (ds_nxt s) (if up then vcount else c),
            ds_acap := list_update (ds_acap s) (ds_nxt s) cp,
            ds_aflw := list_update (ds_aflw s) (ds_nxt s) af,
            ds_aest := list_update (ds_aest s) (ds_nxt s) InTree,
            ds_nxt  := Suc (ds_nxt s),
            ds_seen := list_update (ds_seen s) c True,
            ds_prnt := list_update (ds_prnt s) c vcount,
            ds_par  := list_update (ds_par s) c (m + ds_nxt s),
            ds_dir  := list_update (ds_dir s) c up,
            ds_pot  := list_update (ds_pot s) c (if up then pval_negM else pval_M),
            ds_thrd := list_update (ds_thrd s) pv c,
            ds_rvth := list_update (ds_rvth s) c pv,
            ds_snum := list_update (ds_snum s) c 1,
            ds_prev := c,
            ds_stk  := [(c, out_lo ! c, in_lo ! c)] \<rparr>)"

lemma open_tree_component_eq_pre: "open_tree_component fl s c = build_dfs fl (otc_pre fl s c)"
  by (simp add: open_tree_component_def otc_pre_def Let_def)

text \<open>The imperative opener refines @{const open_tree_component}.  After the framed read of the
      imbalance array it writes @{term c}'s artificial tree edge into the augmented arrays at index
      @{term \<open>m + ds_nxt s\<close>}, bumps @{const ds_nxt}, finalises @{term c}'s tree fields, seeds the DFS
      with the single root frame and drains the subtree with @{const build_dfs_a_imp}.  The whole write
      phase reassembles the DFS state into @{term \<open>otc_pre fl s c\<close>}, from which @{thm build_dfs_a_imp_rule}
      yields @{term \<open>build_dfs fl (otc_pre fl s c)\<close>} \<open>=\<close> @{const open_tree_component} (@{thm
      open_tree_component_eq_pre}).  We split on the orientation (\<open>up\<close> iff @{term \<open>0 \<le> imbalance ! c\<close>})
      so the reduced program writes stay in step with the @{const otc_pre} record fields, and use
      @{thm wlp_apply_ht} to fold the reassembled unfolded state back into the folded
      @{const build_dfs_a_imp} precondition.\<close>
lemma open_tree_component_imp_rule:
  assumes cimb: "c < length imbalance" and cvc: "c < vcount"
    and la1: "ds_nxt s < length (ds_afst s)" and la2: "ds_nxt s < length (ds_asnd s)"
    and la3: "ds_nxt s < length (ds_acap s)" and la4: "ds_nxt s < length (ds_aflw s)"
    and la5: "ds_nxt s < length (ds_aest s)"
    and lv1: "c < length (ds_seen s)" and lv2: "c < length (ds_prnt s)"
    and lv3: "c < length (ds_par s)" and lv4: "c < length (ds_dir s)"
    and lv5: "c < length (ds_pot s)" and lv6: "ds_prev s < length (ds_thrd s)"
    and lv7: "c < length (ds_rvth s)" and lv8: "c < length (ds_snum s)"
    and lc1: "c < length out_lo" and lc2: "c < length in_lo"
    and dom'': "build_dfs_dom (fl, otc_pre fl s c)"
    and wf'': "dfs_wf (otc_pre fl s c)" and sz'': "dfs_sized (otc_pre fl s c)"
    and dref'': "dref_inv (otc_pre fl s c)"
  shows "<dfs_rel fl0 es0 (free_out_edges fl) (free_out_hi fl) (free_in_edges fl) (free_in_hi fl) st s * imb_arr \<mapsto>\<^sub>a imbalance>
           open_tree_component_imp st imb_arr m vcount c
         <\<lambda>_. dfs_rel fl0 es0 (free_out_edges fl) (free_out_hi fl) (free_in_edges fl) (free_in_hi fl) st (open_tree_component fl s c) * imb_arr \<mapsto>\<^sub>a imbalance>"
proof (cases "0 \<le> imbalance ! c")
  case True
  show ?thesis
    unfolding open_tree_component_eq_pre open_tree_component_imp_def Let_def dfs_rel_def
    apply (sep_auto heap: build_dfs_a_imp_rule[OF dom'' wf'' sz'' dref'', unfolded dfs_rel_def] 
                    simp: cimb True)
    using  la1 apply simp
    apply (sep_auto heap: build_dfs_a_imp_rule[OF dom'' wf'' sz'' dref'', unfolded dfs_rel_def] 
                    simp: cvc True cimb la1 la2 la3 la4 la5 lv1 lv2 lv3 lv4 lv5 lv6 lv7 lv8 lc1 lc2 otc_pre_def)
    using la2 apply simp 
     apply (sep_auto heap: build_dfs_a_imp_rule[OF dom'' wf'' sz'' dref'', unfolded dfs_rel_def] 
                     simp: cvc True cimb la1 la2 la3 la4 la5 lv1 lv2 lv3 lv4 lv5 lv6 lv7 lv8 lc1 lc2 otc_pre_def)
    using cvc la3 apply simp 
     apply (sep_auto heap: build_dfs_a_imp_rule[OF dom'' wf'' sz'' dref'', unfolded dfs_rel_def] 
                     simp: cvc True cimb la1 la2 la3 la4 la5 lv1 lv2 lv3 lv4 lv5 lv6 lv7 lv8 lc1 lc2 otc_pre_def)
    using la4 apply simp 
     apply (sep_auto heap: build_dfs_a_imp_rule[OF dom'' wf'' sz'' dref'', unfolded dfs_rel_def] 
                     simp: cvc True cimb la1 la2 la3 la4 la5 lv1 lv2 lv3 lv4 lv5 lv6 lv7 lv8 lc1 lc2 otc_pre_def)
    using la5 apply fastforce
     apply (sep_auto heap: build_dfs_a_imp_rule[OF dom'' wf'' sz'' dref'', unfolded dfs_rel_def] 
                     simp: cvc True cimb la1 la2 la3 la4 la5 lv1 lv2 lv3 lv4 lv5 lv6 lv7 lv8 lc1 lc2 otc_pre_def)
    apply (sep_auto heap: build_dfs_a_imp_rule[OF dom'' wf'' sz'' dref'', unfolded dfs_rel_def otc_pre_def Let_def] simp: True cvc lv1 lv2 lv3 lv4 lv5 lv6 lv7 lv8 la1 la2 la3 la4 la5 nth_list_update less_Suc_eq stk_rel_cons_simp stk_rel_nil Let_def)
    apply (rule wlp_apply_ht[OF _ _ build_dfs_a_imp_rule[OF dom'' wf'' sz'' dref''], where F="imb_arr \<mapsto>\<^sub>a imbalance * true"])
      apply assumption
     apply (sep_auto simp: dfs_rel_def otc_pre_def Let_def True cvc lv1 lv2 lv3 lv4 lv5 lv6 lv7 lv8 la1 la2 la3 la4 la5 nth_list_update length_list_update stk_rel_cons_simp stk_rel_nil)
    apply (subgoal_tac "m + ds_nxt s < length fsta \<and> m + ds_nxt s < length snda \<and> m + ds_nxt s < length capa \<and> m + ds_nxt s < length flowa \<and> m + ds_nxt s < length esa")
     prefer 2 apply (intro conjI; meson add_strict_left_mono less_le_trans la1 la2 la3 la4 la5)
    apply (sep_auto simp: nth_list_update stk_rel_cons_simp stk_rel_nil)
    apply (sep_auto simp: dfs_rel_def otc_pre_def Let_def True)
    done
next
  case False
  show ?thesis
    unfolding open_tree_component_eq_pre open_tree_component_imp_def Let_def dfs_rel_def
    apply (sep_auto heap: build_dfs_a_imp_rule[OF dom'' wf'' sz'' dref'', unfolded dfs_rel_def] simp: cimb False)
    using la1 apply fastforce 
    apply (sep_auto heap: build_dfs_a_imp_rule[OF dom'' wf'' sz'' dref'', unfolded dfs_rel_def] simp: cvc False cimb la1 la2 la3 la4 la5 lv1 lv2 lv3 lv4 lv5 lv6 lv7 lv8 lc1 lc2 otc_pre_def)
    using la2 apply fastforce 
    apply (sep_auto heap: build_dfs_a_imp_rule[OF dom'' wf'' sz'' dref'', unfolded dfs_rel_def] simp: cvc False cimb la1 la2 la3 la4 la5 lv1 lv2 lv3 lv4 lv5 lv6 lv7 lv8 lc1 lc2 otc_pre_def)
    using la3 apply fastforce 
    apply (sep_auto heap: build_dfs_a_imp_rule[OF dom'' wf'' sz'' dref'', unfolded dfs_rel_def] simp: cvc False cimb la1 la2 la3 la4 la5 lv1 lv2 lv3 lv4 lv5 lv6 lv7 lv8 lc1 lc2 otc_pre_def)
    using la4 apply simp 
    apply (sep_auto heap: build_dfs_a_imp_rule[OF dom'' wf'' sz'' dref'', unfolded dfs_rel_def] simp: cvc False cimb la1 la2 la3 la4 la5 lv1 lv2 lv3 lv4 lv5 lv6 lv7 lv8 lc1 lc2 otc_pre_def)
    using la5 apply fastforce 
    apply (sep_auto heap: build_dfs_a_imp_rule[OF dom'' wf'' sz'' dref'', unfolded dfs_rel_def] simp: cvc False cimb la1 la2 la3 la4 la5 lv1 lv2 lv3 lv4 lv5 lv6 lv7 lv8 lc1 lc2 otc_pre_def)
    apply (rule wlp_apply_ht[OF _ _ build_dfs_a_imp_rule[OF dom'' wf'' sz'' dref''], where F="imb_arr \<mapsto>\<^sub>a imbalance * true"])
      apply assumption
     apply (subgoal_tac "m + ds_nxt s < length fsta \<and> m + ds_nxt s < length snda \<and> m + ds_nxt s < length capa \<and> m + ds_nxt s < length flowa \<and> m + ds_nxt s < length esa")
      prefer 2 apply (intro conjI; meson add_strict_left_mono less_le_trans la1 la2 la3 la4 la5)
     apply (sep_auto simp: dfs_rel_def otc_pre_def Let_def False cvc lv1 lv2 lv3 lv4 lv5 lv6 lv7 lv8 la1 la2 la3 la4 la5 nth_list_update stk_rel_cons_simp stk_rel_nil)
    done
qed

text \<open>The imperative @{const emit_U_edge_imp} refines @{const emit_U_edge}: for an already-seen
      imbalanced vertex @{term v} it writes one saturated @{term U} artificial edge into the augmented
      arrays at index @{term \<open>m + ds_nxt s\<close>} and bumps @{const ds_nxt}, touching no tree or stack field.
      As it ends at the @{const ds_nxt} bump (no @{const build_dfs_a_imp} tail) the write phase reassembles
      directly into @{term \<open>emit_U_edge s v\<close>}, so the proof closes with a single fold-in entailment per
      orientation case (no @{thm wlp_apply_ht} needed).\<close>
lemma emit_U_edge_imp_rule:
  assumes cimb: "v < length imbalance" and cvc: "v < vcount"
    and la1: "ds_nxt s < length (ds_afst s)" and la2: "ds_nxt s < length (ds_asnd s)"
    and la3: "ds_nxt s < length (ds_acap s)" and la4: "ds_nxt s < length (ds_aflw s)"
    and la5: "ds_nxt s < length (ds_aest s)"
  shows "<dfs_rel fl0 es0 (free_out_edges fl) (free_out_hi fl) (free_in_edges fl) (free_in_hi fl) st s * imb_arr \<mapsto>\<^sub>a imbalance>
           emit_U_edge_imp st imb_arr m vcount v
         <\<lambda>_. dfs_rel fl0 es0 (free_out_edges fl) (free_out_hi fl) (free_in_edges fl) (free_in_hi fl) st (emit_U_edge s v) * imb_arr \<mapsto>\<^sub>a imbalance>"
proof (cases "0 \<le> imbalance ! v")
  case True
  show ?thesis
    unfolding emit_U_edge_imp_def emit_U_edge_def Let_def dfs_rel_def
    apply (sep_auto simp: cimb True nth_list_update)
    using la1 apply simp
    apply (subgoal_tac "m + ds_nxt s < length fsta \<and> m + ds_nxt s < length snda \<and> m + ds_nxt s < length capa \<and> m + ds_nxt s < length flowa \<and> m + ds_nxt s < length esa")
     prefer 2 apply (intro conjI; meson add_strict_left_mono less_le_trans la1 la2 la3 la4 la5)
    apply (sep_auto simp: True nth_list_update la1 la2 la3 la4 la5)
    done
next
  case False
  show ?thesis
    unfolding emit_U_edge_imp_def emit_U_edge_def Let_def dfs_rel_def
    apply (sep_auto simp: cimb False nth_list_update)
    using la1 apply fastforce
    apply (subgoal_tac "m + ds_nxt s < length fsta \<and> m + ds_nxt s < length snda \<and> m + ds_nxt s < length capa \<and> m + ds_nxt s < length flowa \<and> m + ds_nxt s < length esa")
     prefer 2 apply (intro conjI; meson add_strict_left_mono less_le_trans la1 la2 la3 la4 la5)
    apply (sep_auto simp: False nth_list_update la1 la2 la3 la4 la5)
    done
qed

subsection \<open>Layer (d.7): functional invariant preservation for the vertex scans\<close>

text \<open>The two phase scans repeatedly open tree components and emit artificial edges; to invoke the
      imperative rules for those operations we must discharge, at every vertex, the well-formedness
      (@{const dfs_wf}), sizedness (@{const dfs_sized}), reference (@{const dref_inv}) invariants of the
      pre-DFS state, and a counting bound guaranteeing room in the artificial arrays.  The whole DFS loop
      @{const build_dfs} preserves the three invariants (per-step lemmas @{thm bd_upd1_wf} etc.) and
      leaves @{const ds_nxt} and the five artificial arrays untouched (it only writes the seen / tree /
      stack fields).  Opening a component is @{const build_dfs} of the seeded @{const otc_pre} state, so
      it preserves the invariants and bumps @{const ds_nxt} by exactly one; emitting a @{term U} edge is a
      single record update with the same effect.  A @{const phase1_step} does at most one of these.\<close>

lemma build_dfs_wsd:
  assumes "build_dfs_dom (fl, s)" "dfs_wf s" "dfs_sized s" "dref_inv s"
  shows "dfs_wf (build_dfs fl s) \<and> dfs_sized (build_dfs fl s) \<and> dref_inv (build_dfs fl s)"
  using assms(2-4)
proof (induct rule: bd_induct[OF assms(1)])
  case IH: (1 fl s)
  show ?case
  proof (rule bd_cases[where s = s and fl = fl])
    assume c: "bd_call1_conds fl s"
    show ?case unfolding bd_simps(1)[OF IH(1) c]
      by (rule IH(2)[OF c bd_upd1_wf[OF Hout_valid IH(5) c] bd_upd1_sized[OF IH(6) c]
                        bd_upd1_dref[OF IH(7) IH(5) IH(6) c]])
  next
    assume c: "bd_call2_conds fl s"
    show ?case unfolding bd_simps(2)[OF IH(1) c]
      by (rule IH(3)[OF c bd_upd2_wf[OF Hin_valid IH(5) c] bd_upd2_sized[OF IH(6) c]
                        bd_upd2_dref[OF IH(7) IH(5) IH(6) c]])
  next
    assume c: "bd_call3_conds fl s"
    show ?case unfolding bd_simps(3)[OF IH(1) c]
      by (rule IH(4)[OF c bd_upd3_wf[OF IH(5) c] bd_upd3_sized[OF IH(6) c]
                        bd_upd3_dref[OF IH(7) c]])
  next
    assume c: "bd_ret_conds s"
    show ?case unfolding bd_simps(4)[OF IH(1) c] using IH(5) IH(6) IH(7) by simp
  qed
qed

lemma bd_upd1_nxt: "bd_call1_conds fl s \<Longrightarrow> ds_nxt (bd_upd1 fl s) = ds_nxt s"
  by (auto simp: bd_upd1_def bd_call1_conds_def dfs_discover_def Let_def split: prod.splits list.splits if_splits)
lemma bd_upd2_nxt: "bd_call2_conds fl s \<Longrightarrow> ds_nxt (bd_upd2 fl s) = ds_nxt s"
  by (auto simp: bd_upd2_def bd_call2_conds_def dfs_discover_def Let_def split: prod.splits list.splits if_splits)
lemma bd_upd3_nxt: "bd_call3_conds fl s \<Longrightarrow> ds_nxt (bd_upd3 s) = ds_nxt s"
  by (auto simp: bd_upd3_def bd_call3_conds_def dfs_finish_def Let_def split: prod.splits list.splits if_splits)

lemma build_dfs_nxt:
  assumes "build_dfs_dom (fl, s)" shows "ds_nxt (build_dfs fl s) = ds_nxt s"
proof (induct rule: bd_induct[OF assms])
  case IH: (1 fl s)
  show ?case
  proof (rule bd_cases[where s = s and fl = fl])
    assume c: "bd_call1_conds fl s"
    show ?case unfolding bd_simps(1)[OF IH(1) c] using IH(2)[OF c] by (simp add: bd_upd1_nxt[OF c])
  next
    assume c: "bd_call2_conds fl s"
    show ?case unfolding bd_simps(2)[OF IH(1) c] using IH(3)[OF c] by (simp add: bd_upd2_nxt[OF c])
  next
    assume c: "bd_call3_conds fl s"
    show ?case unfolding bd_simps(3)[OF IH(1) c] using IH(4)[OF c] by (simp add: bd_upd3_nxt[OF c])
  next
    assume c: "bd_ret_conds s"
    show ?case unfolding bd_simps(4)[OF IH(1) c] by simp
  qed
qed

lemma bd_upd1_arts: "bd_call1_conds fl s \<Longrightarrow> ds_afst (bd_upd1 fl s) = ds_afst s \<and> ds_asnd (bd_upd1 fl s) = ds_asnd s \<and> ds_acap (bd_upd1 fl s) = ds_acap s \<and> ds_aflw (bd_upd1 fl s) = ds_aflw s \<and> ds_aest (bd_upd1 fl s) = ds_aest s"
  by (auto simp: bd_upd1_def bd_call1_conds_def dfs_discover_def Let_def split: prod.splits list.splits if_splits)
lemma bd_upd2_arts: "bd_call2_conds fl s \<Longrightarrow> ds_afst (bd_upd2 fl s) = ds_afst s \<and> ds_asnd (bd_upd2 fl s) = ds_asnd s \<and> ds_acap (bd_upd2 fl s) = ds_acap s \<and> ds_aflw (bd_upd2 fl s) = ds_aflw s \<and> ds_aest (bd_upd2 fl s) = ds_aest s"
  by (auto simp: bd_upd2_def bd_call2_conds_def dfs_discover_def Let_def split: prod.splits list.splits if_splits)
lemma bd_upd3_arts: "bd_call3_conds fl s \<Longrightarrow> ds_afst (bd_upd3 s) = ds_afst s \<and> ds_asnd (bd_upd3 s) = ds_asnd s \<and> ds_acap (bd_upd3 s) = ds_acap s \<and> ds_aflw (bd_upd3 s) = ds_aflw s \<and> ds_aest (bd_upd3 s) = ds_aest s"
  by (auto simp: bd_upd3_def bd_call3_conds_def dfs_finish_def Let_def split: prod.splits list.splits if_splits)

lemma build_dfs_arts:
  assumes "build_dfs_dom (fl, s)"
  shows "ds_afst (build_dfs fl s) = ds_afst s \<and> ds_asnd (build_dfs fl s) = ds_asnd s \<and> ds_acap (build_dfs fl s) = ds_acap s \<and> ds_aflw (build_dfs fl s) = ds_aflw s \<and> ds_aest (build_dfs fl s) = ds_aest s"
proof (induct rule: bd_induct[OF assms])
  case IH: (1 fl s)
  show ?case
  proof (rule bd_cases[where s = s and fl = fl])
    assume c: "bd_call1_conds fl s"
    show ?case unfolding bd_simps(1)[OF IH(1) c] using IH(2)[OF c] bd_upd1_arts[OF c] by simp
  next
    assume c: "bd_call2_conds fl s"
    show ?case unfolding bd_simps(2)[OF IH(1) c] using IH(3)[OF c] bd_upd2_arts[OF c] by simp
  next
    assume c: "bd_call3_conds fl s"
    show ?case unfolding bd_simps(3)[OF IH(1) c] using IH(4)[OF c] bd_upd3_arts[OF c] by simp
  next
    assume c: "bd_ret_conds s"
    show ?case unfolding bd_simps(4)[OF IH(1) c] by simp
  qed
qed

lemma otc_pre_sized: "dfs_sized s \<Longrightarrow> dfs_sized (otc_pre fl s c)"
  by (simp add: dfs_sized_def otc_pre_def Let_def)
lemma otc_pre_wf:
  assumes "dfs_wf s" "dfs_sized s" "c < vcount"
  shows "dfs_wf (otc_pre fl s c)"
  using assms by (auto simp: dfs_wf_def otc_pre_def Let_def dfs_sized_def)
lemma otc_pre_dref:
  assumes "dref_inv s" "dfs_sized s" "c < vcount"
  shows "dref_inv (otc_pre fl s c)"
  using assms by (auto simp: dref_inv_def otc_pre_def Let_def dfs_sized_def nth_list_update split: if_splits)

lemma open_tree_component_wsd:
  assumes "dfs_wf s" "dfs_sized s" "dref_inv s" "c < vcount"
  shows "dfs_wf (open_tree_component fl s c) \<and> dfs_sized (open_tree_component fl s c) \<and> dref_inv (open_tree_component fl s c)"
proof -
  have wf: "dfs_wf (otc_pre fl s c)" using otc_pre_wf[OF assms(1,2,4)] .
  have dom: "build_dfs_dom (fl, otc_pre fl s c)" using build_dfs_dom_wf'[OF wf] .
  show ?thesis unfolding open_tree_component_eq_pre
    using build_dfs_wsd[OF dom wf otc_pre_sized[OF assms(2)] otc_pre_dref[OF assms(3,2,4)]] .
qed

lemma open_tree_component_nxt:
  assumes "dfs_wf s" "dfs_sized s" "c < vcount"
  shows "ds_nxt (open_tree_component fl s c) = Suc (ds_nxt s)"
proof -
  have dom: "build_dfs_dom (fl, otc_pre fl s c)" using build_dfs_dom_wf'[OF otc_pre_wf[OF assms]] .
  show ?thesis unfolding open_tree_component_eq_pre build_dfs_nxt[OF dom] by (simp add: otc_pre_def Let_def)
qed

lemma open_tree_component_arts_len:
  assumes "dfs_wf s" "dfs_sized s" "c < vcount"
  shows "length (ds_afst (open_tree_component fl s c)) = length (ds_afst s) \<and>
         length (ds_asnd (open_tree_component fl s c)) = length (ds_asnd s) \<and>
         length (ds_acap (open_tree_component fl s c)) = length (ds_acap s) \<and>
         length (ds_aflw (open_tree_component fl s c)) = length (ds_aflw s) \<and>
         length (ds_aest (open_tree_component fl s c)) = length (ds_aest s)"
proof -
  have dom: "build_dfs_dom (fl, otc_pre fl s c)" using build_dfs_dom_wf'[OF otc_pre_wf[OF assms]] .
  show ?thesis unfolding open_tree_component_eq_pre
    using build_dfs_arts[OF dom] by (simp add: otc_pre_def Let_def)
qed

lemma emit_U_edge_wsd:
  assumes "dfs_wf s" "dfs_sized s" "dref_inv s"
  shows "dfs_wf (emit_U_edge s v) \<and> dfs_sized (emit_U_edge s v) \<and> dref_inv (emit_U_edge s v)"
  using assms by (simp add: dfs_wf_def dfs_sized_def dref_inv_def emit_U_edge_def Let_def)
lemma emit_U_edge_nxt: "ds_nxt (emit_U_edge s v) = Suc (ds_nxt s)"
  by (simp add: emit_U_edge_def Let_def)
lemma emit_U_edge_arts_len:
  "length (ds_afst (emit_U_edge s v)) = length (ds_afst s) \<and>
   length (ds_asnd (emit_U_edge s v)) = length (ds_asnd s) \<and>
   length (ds_acap (emit_U_edge s v)) = length (ds_acap s) \<and>
   length (ds_aflw (emit_U_edge s v)) = length (ds_aflw s) \<and>
   length (ds_aest (emit_U_edge s v)) = length (ds_aest s)"
  by (simp add: emit_U_edge_def Let_def)

lemma phase1_step_wsd:
  assumes "dfs_wf s" "dfs_sized s" "dref_inv s" "v < vcount"
  shows "dfs_wf (phase1_step fl v s) \<and> dfs_sized (phase1_step fl v s) \<and> dref_inv (phase1_step fl v s)"
  using assms open_tree_component_wsd[OF assms(1,2,3,4)] emit_U_edge_wsd[OF assms(1,2,3)]
  by (auto simp: phase1_step_def)
lemma phase1_step_nxt_le:
  assumes "dfs_wf s" "dfs_sized s" "v < vcount"
  shows "ds_nxt (phase1_step fl v s) \<le> Suc (ds_nxt s)"
  using open_tree_component_nxt[OF assms] emit_U_edge_nxt
  by (auto simp: phase1_step_def)
lemma phase1_step_arts_len:
  assumes "dfs_wf s" "dfs_sized s" "v < vcount"
  shows "length (ds_afst (phase1_step fl v s)) = length (ds_afst s) \<and>
         length (ds_asnd (phase1_step fl v s)) = length (ds_asnd s) \<and>
         length (ds_acap (phase1_step fl v s)) = length (ds_acap s) \<and>
         length (ds_aflw (phase1_step fl v s)) = length (ds_aflw s) \<and>
         length (ds_aest (phase1_step fl v s)) = length (ds_aest s)"
  using open_tree_component_arts_len[OF assms] emit_U_edge_arts_len
  by (auto simp: phase1_step_def)

text \<open>One @{const phase1_step}: read the imbalance, then either skip (balanced), emit a @{term U} edge
      (imbalanced, already seen) or open a tree component (imbalanced, unseen).  We sequence the read with
      @{thm ht_bind} so the read value is available to decide the branch, then let @{term sep_auto} pick
      the matching operation rule; the invariant preconditions (@{const dfs_wf} / @{const dfs_sized} /
      @{const dref_inv} of @{term s}, the vertex bounds from @{const dfs_sized}, the @{const otc_pre}
      obligations, and the artificial-array room @{term la1}--@{term la5}) are discharged from the
      assumptions.\<close>
lemma phase1_step_imp_rule:
  assumes wf: "dfs_wf s" and sz: "dfs_sized s" and dref: "dref_inv s" and vc: "v < vcount"
    and vim: "v < length imbalance"
    and la1: "ds_nxt s < length (ds_afst s)" and la2: "ds_nxt s < length (ds_asnd s)"
    and la3: "ds_nxt s < length (ds_acap s)" and la4: "ds_nxt s < length (ds_aflw s)"
    and la5: "ds_nxt s < length (ds_aest s)"
    and lc1: "v < length out_lo" and lc2: "v < length in_lo"
  shows "<dfs_rel fl0 es0 (free_out_edges fl) (free_out_hi fl) (free_in_edges fl) (free_in_hi fl) st s * imb_arr \<mapsto>\<^sub>a imbalance>
           phase1_step_imp st imb_arr m vcount v
         <\<lambda>_. dfs_rel fl0 es0 (free_out_edges fl) (free_out_hi fl) (free_in_edges fl) (free_in_hi fl) st (phase1_step fl v s) * imb_arr \<mapsto>\<^sub>a imbalance>"
proof -
  have lv1: "v < length (ds_seen s)" and lv2: "v < length (ds_prnt s)" and lv3: "v < length (ds_par s)"
    and lv4: "v < length (ds_dir s)" and lv5: "v < length (ds_pot s)" and lv7: "v < length (ds_rvth s)"
    and lv8: "v < length (ds_snum s)" using sz vc by (auto simp: dfs_sized_def)
  have lv6: "ds_prev s < length (ds_thrd s)" using sz dref by (simp add: dfs_sized_def dref_inv_def)
  have wf'': "dfs_wf (otc_pre fl s v)" using otc_pre_wf[OF wf sz vc] .
  have sz'': "dfs_sized (otc_pre fl s v)" using otc_pre_sized[OF sz] .
  have dref'': "dref_inv (otc_pre fl s v)" using otc_pre_dref[OF dref sz vc] .
  have dom'': "build_dfs_dom (fl, otc_pre fl s v)" using build_dfs_dom_wf'[OF wf''] .
  show ?thesis unfolding phase1_step_imp_def
    apply (rule ht_bind[where R="\<lambda>imb. dfs_rel fl0 es0 (free_out_edges fl) (free_out_hi fl) (free_in_edges fl) (free_in_hi fl) st s * imb_arr \<mapsto>\<^sub>a imbalance * \<up>(imb = imbalance ! v)"])
    by (sep_auto simp: phase1_step_def
        heap: dfs_rel_seen[OF lv1]
              emit_U_edge_imp_rule[OF vim vc la1 la2 la3 la4 la5]
              open_tree_component_imp_rule[OF vim vc la1 la2 la3 la4 la5 lv1 lv2 lv3 lv4 lv5 lv6 lv7 lv8 lc1 lc2 dom'' wf'' sz'' dref''])
qed

text \<open>The whole first scan @{const phase1_imp} refines the functional fold @{term \<open>fold (phase1_step fl)
      [v..<Suc n]\<close>}, by induction on the number of remaining vertices @{term \<open>Suc n - v\<close>}.  The threaded
      invariant is @{const dfs_wf} / @{const dfs_sized} / @{const dref_inv} together with a counting bound
      guaranteeing there is room for every remaining vertex's artificial edge:
      @{term \<open>ds_nxt s + (Suc n - v) \<le> length (ds_afst s)\<close>} (and likewise for the other four artificial
      arrays).  Each @{const phase1_step} bumps @{const ds_nxt} by at most one and preserves the array
      lengths (@{thm phase1_step_nxt_le}, @{thm phase1_step_arts_len}), so the bound is maintained; at every
      vertex it yields @{term \<open>ds_nxt s < length (ds_afst s)\<close>} since @{term \<open>Suc n - v \<ge> 1\<close>}.\<close>
lemma phase1_imp_rule:
  assumes "dfs_wf s" "dfs_sized s" "dref_inv s"
    and "ds_nxt s + (Suc n - v) \<le> length (ds_afst s)"
    and "ds_nxt s + (Suc n - v) \<le> length (ds_asnd s)"
    and "ds_nxt s + (Suc n - v) \<le> length (ds_acap s)"
    and "ds_nxt s + (Suc n - v) \<le> length (ds_aflw s)"
    and "ds_nxt s + (Suc n - v) \<le> length (ds_aest s)"
    and "n < vcount" "Suc vcount \<le> length imbalance" "vcount \<le> length out_lo" "vcount \<le> length in_lo"
  shows "<dfs_rel fl0 es0 (free_out_edges fl) (free_out_hi fl) (free_in_edges fl) (free_in_hi fl) st s * imb_arr \<mapsto>\<^sub>a imbalance>
           phase1_imp st imb_arr m vcount v n
         <\<lambda>_. dfs_rel fl0 es0 (free_out_edges fl) (free_out_hi fl) (free_in_edges fl) (free_in_hi fl) st (fold (phase1_step fl) [v..<Suc n] s) * imb_arr \<mapsto>\<^sub>a imbalance>"
  using assms
proof (induction "Suc n - v" arbitrary: v s)
  case 0
  then have nv: "n < v" by linarith
  have empt: "[v..<Suc n] = []" using nv by simp
  show ?case by (subst phase1_imp.simps) (simp only: if_P[OF nv] empt, sep_auto)
next
  case (Suc k)
  have vn: "v \<le> n" using Suc.hyps(2) by linarith
  have nnv: "\<not> n < v" using vn by simp
  have snv: "Suc n - v = Suc k" using Suc.hyps(2) by simp
  have kk: "k = Suc n - Suc v" using snv by simp
  have vvc: "v < vcount" using vn Suc.prems(9) by (simp add: le_less_trans)
  have vim: "v < length imbalance" using vvc Suc.prems(10) by simp
  have lc1: "v < length out_lo" using vvc Suc.prems(11) by simp
  have lc2: "v < length in_lo" using vvc Suc.prems(12) by simp
  have la1: "ds_nxt s < length (ds_afst s)" using Suc.prems(4) snv by simp
  have la2: "ds_nxt s < length (ds_asnd s)" using Suc.prems(5) snv by simp
  have la3: "ds_nxt s < length (ds_acap s)" using Suc.prems(6) snv by simp
  have la4: "ds_nxt s < length (ds_aflw s)" using Suc.prems(7) snv by simp
  have la5: "ds_nxt s < length (ds_aest s)" using Suc.prems(8) snv by simp
  have nxt': "ds_nxt (phase1_step fl v s) \<le> Suc (ds_nxt s)" using phase1_step_nxt_le[OF Suc.prems(1,2) vvc] .
  have len': "length (ds_afst (phase1_step fl v s)) = length (ds_afst s) \<and> length (ds_asnd (phase1_step fl v s)) = length (ds_asnd s) \<and> length (ds_acap (phase1_step fl v s)) = length (ds_acap s) \<and> length (ds_aflw (phase1_step fl v s)) = length (ds_aflw s) \<and> length (ds_aest (phase1_step fl v s)) = length (ds_aest s)"
    using phase1_step_arts_len[OF Suc.prems(1,2) vvc] .
  have cnt1: "ds_nxt (phase1_step fl v s) + (Suc n - Suc v) \<le> length (ds_afst (phase1_step fl v s))" using nxt' len' Suc.prems(4) snv kk by linarith
  have cnt2: "ds_nxt (phase1_step fl v s) + (Suc n - Suc v) \<le> length (ds_asnd (phase1_step fl v s))" using nxt' len' Suc.prems(5) snv kk by linarith
  have cnt3: "ds_nxt (phase1_step fl v s) + (Suc n - Suc v) \<le> length (ds_acap (phase1_step fl v s))" using nxt' len' Suc.prems(6) snv kk by linarith
  have cnt4: "ds_nxt (phase1_step fl v s) + (Suc n - Suc v) \<le> length (ds_aflw (phase1_step fl v s))" using nxt' len' Suc.prems(7) snv kk by linarith
  have cnt5: "ds_nxt (phase1_step fl v s) + (Suc n - Suc v) \<le> length (ds_aest (phase1_step fl v s))" using nxt' len' Suc.prems(8) snv kk by linarith
  have wsd': "dfs_wf (phase1_step fl v s) \<and> dfs_sized (phase1_step fl v s) \<and> dref_inv (phase1_step fl v s)" using phase1_step_wsd[OF Suc.prems(1,2,3) vvc] .
  have foldeq: "fold (phase1_step fl) [v..<Suc n] s = fold (phase1_step fl) [Suc v..<Suc n] (phase1_step fl v s)"
    using vn by (subst upt_conv_Cons) auto
  have IH: "<dfs_rel fl0 es0 (free_out_edges fl) (free_out_hi fl) (free_in_edges fl) (free_in_hi fl) st (phase1_step fl v s) * imb_arr \<mapsto>\<^sub>a imbalance>
              phase1_imp st imb_arr m vcount (Suc v) n
            <\<lambda>_. dfs_rel fl0 es0 (free_out_edges fl) (free_out_hi fl) (free_in_edges fl) (free_in_hi fl) st (fold (phase1_step fl) [Suc v..<Suc n] (phase1_step fl v s)) * imb_arr \<mapsto>\<^sub>a imbalance>"
    by (rule Suc.hyps(1)[OF kk conjunct1[OF wsd'] conjunct1[OF conjunct2[OF wsd']] conjunct2[OF conjunct2[OF wsd']] cnt1 cnt2 cnt3 cnt4 cnt5 Suc.prems(9) Suc.prems(10) Suc.prems(11) Suc.prems(12)])
  show ?case
    apply (subst phase1_imp.simps)
    apply (simp only: if_not_P[OF nnv] foldeq)
    apply (sep_auto heap: phase1_step_imp_rule[OF Suc.prems(1,2,3) vvc vim la1 la2 la3 la4 la5 lc1 lc2] IH)
    done
qed

text \<open>Phase 2 mirrors phase 1 but only ever opens components (for still-unseen, non-lonely — hence
      balanced — vertices), so its per-step preservation and effect lemmas follow directly from those of
      @{const open_tree_component}.\<close>
lemma phase2_step_wsd:
  assumes "dfs_wf s" "dfs_sized s" "dref_inv s" "v < vcount"
  shows "dfs_wf (phase2_step fl v s) \<and> dfs_sized (phase2_step fl v s) \<and> dref_inv (phase2_step fl v s)"
  using assms open_tree_component_wsd[OF assms(1,2,3,4)] by (auto simp: phase2_step_def)
lemma phase2_step_nxt_le:
  assumes "dfs_wf s" "dfs_sized s" "v < vcount"
  shows "ds_nxt (phase2_step fl v s) \<le> Suc (ds_nxt s)"
  using open_tree_component_nxt[OF assms] by (auto simp: phase2_step_def)
lemma phase2_step_arts_len:
  assumes "dfs_wf s" "dfs_sized s" "v < vcount"
  shows "length (ds_afst (phase2_step fl v s)) = length (ds_afst s) \<and>
         length (ds_asnd (phase2_step fl v s)) = length (ds_asnd s) \<and>
         length (ds_acap (phase2_step fl v s)) = length (ds_acap s) \<and>
         length (ds_aflw (phase2_step fl v s)) = length (ds_aflw s) \<and>
         length (ds_aest (phase2_step fl v s)) = length (ds_aest s)"
  using open_tree_component_arts_len[OF assms] by (auto simp: phase2_step_def)

text \<open>A @{const phase2_step}: read whether the vertex is already seen, and its full outgoing / ingoing
      block bounds (from the framed @{term ofh} / @{term ifh} arrays holding @{const out_hi} / @{const
      in_hi}); a seen or lonely vertex is skipped, an unseen non-lonely one opens its component.  As in
      phase 1 a single @{thm ht_bind} on the first read makes the remainder a clean triple that @{term
      sep_auto} discharges via the framed field reads and @{thm open_tree_component_imp_rule}.\<close>
lemma phase2_step_imp_rule:
  assumes wf: "dfs_wf s" and sz: "dfs_sized s" and dref: "dref_inv s" and vc: "v < vcount"
    and vim: "v < length imbalance"
    and la1: "ds_nxt s < length (ds_afst s)" and la2: "ds_nxt s < length (ds_asnd s)"
    and la3: "ds_nxt s < length (ds_acap s)" and la4: "ds_nxt s < length (ds_aflw s)"
    and la5: "ds_nxt s < length (ds_aest s)"
    and lc1: "v < length out_lo" and lc2: "v < length in_lo"
    and loh: "v < length out_hi" and lih: "v < length in_hi"
  shows "<dfs_rel fl0 es0 (free_out_edges fl) (free_out_hi fl) (free_in_edges fl) (free_in_hi fl) st s * imb_arr \<mapsto>\<^sub>a imbalance * ofh_arr \<mapsto>\<^sub>a out_hi * ifh_arr \<mapsto>\<^sub>a in_hi>
           phase2_step_imp st imb_arr ofh_arr ifh_arr m vcount v
         <\<lambda>_. dfs_rel fl0 es0 (free_out_edges fl) (free_out_hi fl) (free_in_edges fl) (free_in_hi fl) st (phase2_step fl v s) * imb_arr \<mapsto>\<^sub>a imbalance * ofh_arr \<mapsto>\<^sub>a out_hi * ifh_arr \<mapsto>\<^sub>a in_hi>"
proof -
  have lv1: "v < length (ds_seen s)" and lv2: "v < length (ds_prnt s)" and lv3: "v < length (ds_par s)"
    and lv4: "v < length (ds_dir s)" and lv5: "v < length (ds_pot s)" and lv7: "v < length (ds_rvth s)"
    and lv8: "v < length (ds_snum s)" using sz vc by (auto simp: dfs_sized_def)
  have lv6: "ds_prev s < length (ds_thrd s)" using sz dref by (simp add: dfs_sized_def dref_inv_def)
  have wf'': "dfs_wf (otc_pre fl s v)" using otc_pre_wf[OF wf sz vc] .
  have sz'': "dfs_sized (otc_pre fl s v)" using otc_pre_sized[OF sz] .
  have dref'': "dref_inv (otc_pre fl s v)" using otc_pre_dref[OF dref sz vc] .
  have dom'': "build_dfs_dom (fl, otc_pre fl s v)" using build_dfs_dom_wf'[OF wf''] .
  show ?thesis unfolding phase2_step_imp_def
    apply (rule ht_bind[where R="\<lambda>sv. dfs_rel fl0 es0 (free_out_edges fl) (free_out_hi fl) (free_in_edges fl) (free_in_hi fl) st s * imb_arr \<mapsto>\<^sub>a imbalance * ofh_arr \<mapsto>\<^sub>a out_hi * ifh_arr \<mapsto>\<^sub>a in_hi * \<up>(sv = ds_seen s ! v)"])
     prefer 2
     apply (sep_auto simp: phase2_step_def is_lonely_def loh lih
        heap: dfs_rel_olo[OF lc1] dfs_rel_ilo[OF lc2]
              open_tree_component_imp_rule[OF vim vc la1 la2 la3 la4 la5 lv1 lv2 lv3 lv4 lv5 lv6 lv7 lv8 lc1 lc2 dom'' wf'' sz'' dref''])
    apply (sep_auto heap: dfs_rel_seen[OF lv1])
    done
qed

text \<open>Composable counting helpers for phase 2.  Unlike phase 1 (which always starts from the freshly
      seeded \<open>ds_nxt = 0\<close>), phase 2 runs on top of the artificial edges already emitted by phase 1,
      so a per-step bound \<open>ds_nxt s + (Suc n - v) \<le> length \<dots>\<close> would over-count (it counts every
      remaining vertex once more, on top of phase 1).  We instead thread the exact, composable bound
      \<open>ds_nxt (fold (phase2_step fl) [v..<Suc n] s) \<le> length \<dots>\<close>: it is preserved trivially along the
      fold and it is discharged for @{const build_tree} by the functional @{thm build_tree_nxt_le}.  A step
      only writes an artificial edge when it actually opens a component (\<open>\<not> ds_seen s ! v \<and> \<not> is_lonely v\<close>),
      so its in-bounds premise is needed only under that guard — supplied here by monotonicity of \<open>ds_nxt\<close>.\<close>

lemma phase2_step_nxt_ge:
  assumes "dfs_wf s" "dfs_sized s" "v < vcount"
  shows "ds_nxt s \<le> ds_nxt (phase2_step fl v s)"
  using open_tree_component_nxt[OF assms] by (auto simp: phase2_step_def)

lemma phase2_step_nxt_open:
  assumes "\<not> ds_seen s ! v" "\<not> is_lonely v" "dfs_wf s" "dfs_sized s" "v < vcount"
  shows "ds_nxt (phase2_step fl v s) = Suc (ds_nxt s)"
  using open_tree_component_nxt[OF assms(3,4,5)] assms(1,2) by (simp add: phase2_step_def)

lemma fold_phase2_step_nxt_mono:
  assumes "dfs_wf s" "dfs_sized s" "dref_inv s" "\<forall>w\<in>set xs. w < vcount"
  shows "ds_nxt s \<le> ds_nxt (fold (phase2_step fl) xs s)"
  using assms
proof (induction xs arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons w ws)
  have wvc: "w < vcount" using Cons.prems(4) by simp
  have ge: "ds_nxt s \<le> ds_nxt (phase2_step fl w s)" using phase2_step_nxt_ge[OF Cons.prems(1,2) wvc] .
  have wsd: "dfs_wf (phase2_step fl w s) \<and> dfs_sized (phase2_step fl w s) \<and> dref_inv (phase2_step fl w s)"
    using phase2_step_wsd[OF Cons.prems(1,2,3) wvc] .
  have "ds_nxt (phase2_step fl w s) \<le> ds_nxt (fold (phase2_step fl) ws (phase2_step fl w s))"
    using Cons.IH[OF conjunct1[OF wsd] conjunct1[OF conjunct2[OF wsd]] conjunct2[OF conjunct2[OF wsd]]] Cons.prems(4) by simp
  thus ?case using ge by simp
qed

text \<open>A skipped vertex (already seen, or lonely) leaves the state untouched: the imperative
      @{const phase2_step_imp} then only reads and returns, needing no artificial-array space.\<close>
lemma phase2_step_imp_skip:
  assumes wf: "dfs_wf s" and sz: "dfs_sized s" and vc: "v < vcount"
    and skip: "ds_seen s ! v \<or> is_lonely v"
    and lc1: "v < length out_lo" and lc2: "v < length in_lo"
    and loh: "v < length out_hi" and lih: "v < length in_hi"
  shows "<dfs_rel fl0 es0 (free_out_edges fl) (free_out_hi fl) (free_in_edges fl) (free_in_hi fl) st s * imb_arr \<mapsto>\<^sub>a imbalance * ofh_arr \<mapsto>\<^sub>a out_hi * ifh_arr \<mapsto>\<^sub>a in_hi>
           phase2_step_imp st imb_arr ofh_arr ifh_arr m vcount v
         <\<lambda>_. dfs_rel fl0 es0 (free_out_edges fl) (free_out_hi fl) (free_in_edges fl) (free_in_hi fl) st s * imb_arr \<mapsto>\<^sub>a imbalance * ofh_arr \<mapsto>\<^sub>a out_hi * ifh_arr \<mapsto>\<^sub>a in_hi>"
proof -
  have lv1: "v < length (ds_seen s)" using sz vc by (auto simp: dfs_sized_def)
  show ?thesis
  proof (cases "ds_seen s ! v")
    case True
    show ?thesis unfolding phase2_step_imp_def
      apply (rule ht_bind[where R="\<lambda>sv. dfs_rel fl0 es0 (free_out_edges fl) (free_out_hi fl) (free_in_edges fl) (free_in_hi fl) st s * imb_arr \<mapsto>\<^sub>a imbalance * ofh_arr \<mapsto>\<^sub>a out_hi * ifh_arr \<mapsto>\<^sub>a in_hi * \<up>(sv = ds_seen s ! v)"])
       prefer 2
       apply (sep_auto simp: True)
      apply (sep_auto simp: True heap: dfs_rel_seen[OF lv1])
      done
  next
    case False
    with skip have il: "out_lo ! v = out_hi ! v \<and> in_lo ! v = in_hi ! v" by (simp add: is_lonely_def)
    show ?thesis unfolding phase2_step_imp_def
      apply (rule ht_bind[where R="\<lambda>sv. dfs_rel fl0 es0 (free_out_edges fl) (free_out_hi fl) (free_in_edges fl) (free_in_hi fl) st s * imb_arr \<mapsto>\<^sub>a imbalance * ofh_arr \<mapsto>\<^sub>a out_hi * ifh_arr \<mapsto>\<^sub>a in_hi * \<up>(sv = ds_seen s ! v)"])
       prefer 2
       apply (sep_auto simp: False il loh lih heap: dfs_rel_olo[OF lc1] dfs_rel_ilo[OF lc2])
      apply (sep_auto simp: False heap: dfs_rel_seen[OF lv1])
      done
  qed
qed

text \<open>The combined phase-2 step rule: dispatch to @{thm phase2_step_imp_rule} on an opening vertex
      (where its in-bounds premises hold under the guard) and to @{thm phase2_step_imp_skip} otherwise.\<close>
lemma phase2_step_imp_combined:
  assumes wf: "dfs_wf s" and sz: "dfs_sized s" and dref: "dref_inv s" and vc: "v < vcount"
    and vim: "v < length imbalance"
    and gla1: "\<not> ds_seen s ! v \<and> \<not> is_lonely v \<Longrightarrow> ds_nxt s < length (ds_afst s)"
    and gla2: "\<not> ds_seen s ! v \<and> \<not> is_lonely v \<Longrightarrow> ds_nxt s < length (ds_asnd s)"
    and gla3: "\<not> ds_seen s ! v \<and> \<not> is_lonely v \<Longrightarrow> ds_nxt s < length (ds_acap s)"
    and gla4: "\<not> ds_seen s ! v \<and> \<not> is_lonely v \<Longrightarrow> ds_nxt s < length (ds_aflw s)"
    and gla5: "\<not> ds_seen s ! v \<and> \<not> is_lonely v \<Longrightarrow> ds_nxt s < length (ds_aest s)"
    and lc1: "v < length out_lo" and lc2: "v < length in_lo"
    and loh: "v < length out_hi" and lih: "v < length in_hi"
  shows "<dfs_rel fl0 es0 (free_out_edges fl) (free_out_hi fl) (free_in_edges fl) (free_in_hi fl) st s * imb_arr \<mapsto>\<^sub>a imbalance * ofh_arr \<mapsto>\<^sub>a out_hi * ifh_arr \<mapsto>\<^sub>a in_hi>
           phase2_step_imp st imb_arr ofh_arr ifh_arr m vcount v
         <\<lambda>_. dfs_rel fl0 es0 (free_out_edges fl) (free_out_hi fl) (free_in_edges fl) (free_in_hi fl) st (phase2_step fl v s) * imb_arr \<mapsto>\<^sub>a imbalance * ofh_arr \<mapsto>\<^sub>a out_hi * ifh_arr \<mapsto>\<^sub>a in_hi>"
proof (cases "ds_seen s ! v \<or> is_lonely v")
  case True
  have pss: "phase2_step fl v s = s" using True by (auto simp: phase2_step_def)
  show ?thesis unfolding pss using phase2_step_imp_skip[OF wf sz vc True lc1 lc2 loh lih] .
next
  case False
  hence op1: "\<not> ds_seen s ! v" and op2: "\<not> is_lonely v" by auto
  have la1: "ds_nxt s < length (ds_afst s)" using gla1 op1 op2 by simp
  have la2: "ds_nxt s < length (ds_asnd s)" using gla2 op1 op2 by simp
  have la3: "ds_nxt s < length (ds_acap s)" using gla3 op1 op2 by simp
  have la4: "ds_nxt s < length (ds_aflw s)" using gla4 op1 op2 by simp
  have la5: "ds_nxt s < length (ds_aest s)" using gla5 op1 op2 by simp
  show ?thesis using phase2_step_imp_rule[OF wf sz dref vc vim la1 la2 la3 la4 la5 lc1 lc2 loh lih] .
qed

text \<open>The whole second scan @{const phase2_imp} refines \<open>fold (phase2_step fl) [v..<Suc n] s\<close> by an
      induction on \<open>Suc n - v\<close>, threading the composable \<open>ds_nxt (fold \<dots>) \<le> length \<dots>\<close> bound
      above and dispatching each vertex through @{thm phase2_step_imp_combined}; it frames the two
      @{const out_hi} / @{const in_hi} arrays.\<close>
lemma phase2_imp_rule:
  assumes "dfs_wf s" "dfs_sized s" "dref_inv s"
    and "ds_nxt (fold (phase2_step fl) [v..<Suc n] s) \<le> length (ds_afst s)"
    and "ds_nxt (fold (phase2_step fl) [v..<Suc n] s) \<le> length (ds_asnd s)"
    and "ds_nxt (fold (phase2_step fl) [v..<Suc n] s) \<le> length (ds_acap s)"
    and "ds_nxt (fold (phase2_step fl) [v..<Suc n] s) \<le> length (ds_aflw s)"
    and "ds_nxt (fold (phase2_step fl) [v..<Suc n] s) \<le> length (ds_aest s)"
    and "n < vcount" "vcount \<le> length imbalance" "vcount \<le> length out_lo" "vcount \<le> length in_lo"
    and "vcount \<le> length out_hi" "vcount \<le> length in_hi"
  shows "<dfs_rel fl0 es0 (free_out_edges fl) (free_out_hi fl) (free_in_edges fl) (free_in_hi fl) st s * imb_arr \<mapsto>\<^sub>a imbalance * ofh_arr \<mapsto>\<^sub>a out_hi * ifh_arr \<mapsto>\<^sub>a in_hi>
           phase2_imp st imb_arr ofh_arr ifh_arr m vcount v n
         <\<lambda>_. dfs_rel fl0 es0 (free_out_edges fl) (free_out_hi fl) (free_in_edges fl) (free_in_hi fl) st (fold (phase2_step fl) [v..<Suc n] s) * imb_arr \<mapsto>\<^sub>a imbalance * ofh_arr \<mapsto>\<^sub>a out_hi * ifh_arr \<mapsto>\<^sub>a in_hi>"
  using assms
proof (induction "Suc n - v" arbitrary: v s)
  case 0
  then have nv: "n < v" by linarith
  have empt: "[v..<Suc n] = []" using nv by simp
  show ?case by (subst phase2_imp.simps) (simp only: if_P[OF nv] empt, sep_auto)
next
  case (Suc k)
  have vn: "v \<le> n" using Suc.hyps(2) by linarith
  have nnv: "\<not> n < v" using vn by simp
  have snv: "Suc n - v = Suc k" using Suc.hyps(2) by simp
  have kk: "k = Suc n - Suc v" using snv by simp
  have vvc: "v < vcount" using vn Suc.prems(9) by (simp add: le_less_trans)
  have vim: "v < length imbalance" using vvc Suc.prems(10) by simp
  have lc1: "v < length out_lo" using vvc Suc.prems(11) by simp
  have lc2: "v < length in_lo" using vvc Suc.prems(12) by simp
  have loh: "v < length out_hi" using vvc Suc.prems(13) by simp
  have lih: "v < length in_hi" using vvc Suc.prems(14) by simp
  have wsd': "dfs_wf (phase2_step fl v s) \<and> dfs_sized (phase2_step fl v s) \<and> dref_inv (phase2_step fl v s)" using phase2_step_wsd[OF Suc.prems(1,2,3) vvc] .
  have le1: "length (ds_afst (phase2_step fl v s)) = length (ds_afst s)"
   and le2: "length (ds_asnd (phase2_step fl v s)) = length (ds_asnd s)"
   and le3: "length (ds_acap (phase2_step fl v s)) = length (ds_acap s)"
   and le4: "length (ds_aflw (phase2_step fl v s)) = length (ds_aflw s)"
   and le5: "length (ds_aest (phase2_step fl v s)) = length (ds_aest s)"
    using phase2_step_arts_len[OF Suc.prems(1,2) vvc] by auto
  have foldeq: "fold (phase2_step fl) [v..<Suc n] s = fold (phase2_step fl) [Suc v..<Suc n] (phase2_step fl v s)"
    using vn by (subst upt_conv_Cons) auto
  have allvc: "\<forall>w\<in>set [Suc v..<Suc n]. w < vcount" using Suc.prems(9) by auto
  have mono: "ds_nxt (phase2_step fl v s) \<le> ds_nxt (fold (phase2_step fl) [Suc v..<Suc n] (phase2_step fl v s))"
    using fold_phase2_step_nxt_mono[OF conjunct1[OF wsd'] conjunct1[OF conjunct2[OF wsd']] conjunct2[OF conjunct2[OF wsd']] allvc] .
  have ff1': "ds_nxt (fold (phase2_step fl) [Suc v..<Suc n] (phase2_step fl v s)) \<le> length (ds_afst (phase2_step fl v s))" using Suc.prems(4) by (simp only: foldeq le1)
  have ff2': "ds_nxt (fold (phase2_step fl) [Suc v..<Suc n] (phase2_step fl v s)) \<le> length (ds_asnd (phase2_step fl v s))" using Suc.prems(5) by (simp only: foldeq le2)
  have ff3': "ds_nxt (fold (phase2_step fl) [Suc v..<Suc n] (phase2_step fl v s)) \<le> length (ds_acap (phase2_step fl v s))" using Suc.prems(6) by (simp only: foldeq le3)
  have ff4': "ds_nxt (fold (phase2_step fl) [Suc v..<Suc n] (phase2_step fl v s)) \<le> length (ds_aflw (phase2_step fl v s))" using Suc.prems(7) by (simp only: foldeq le4)
  have ff5': "ds_nxt (fold (phase2_step fl) [Suc v..<Suc n] (phase2_step fl v s)) \<le> length (ds_aest (phase2_step fl v s))" using Suc.prems(8) by (simp only: foldeq le5)
  have gla1: "\<not> ds_seen s ! v \<and> \<not> is_lonely v \<Longrightarrow> ds_nxt s < length (ds_afst s)"
  proof -
    assume op: "\<not> ds_seen s ! v \<and> \<not> is_lonely v"
    have "Suc (ds_nxt s) = ds_nxt (phase2_step fl v s)" using phase2_step_nxt_open[OF conjunct1[OF op] conjunct2[OF op] Suc.prems(1,2) vvc] by simp
    with mono ff1' le1 show "ds_nxt s < length (ds_afst s)" by linarith
  qed
  have gla2: "\<not> ds_seen s ! v \<and> \<not> is_lonely v \<Longrightarrow> ds_nxt s < length (ds_asnd s)"
  proof -
    assume op: "\<not> ds_seen s ! v \<and> \<not> is_lonely v"
    have "Suc (ds_nxt s) = ds_nxt (phase2_step fl v s)" using phase2_step_nxt_open[OF conjunct1[OF op] conjunct2[OF op] Suc.prems(1,2) vvc] by simp
    with mono ff2' le2 show "ds_nxt s < length (ds_asnd s)" by linarith
  qed
  have gla3: "\<not> ds_seen s ! v \<and> \<not> is_lonely v \<Longrightarrow> ds_nxt s < length (ds_acap s)"
  proof -
    assume op: "\<not> ds_seen s ! v \<and> \<not> is_lonely v"
    have "Suc (ds_nxt s) = ds_nxt (phase2_step fl v s)" using phase2_step_nxt_open[OF conjunct1[OF op] conjunct2[OF op] Suc.prems(1,2) vvc] by simp
    with mono ff3' le3 show "ds_nxt s < length (ds_acap s)" by linarith
  qed
  have gla4: "\<not> ds_seen s ! v \<and> \<not> is_lonely v \<Longrightarrow> ds_nxt s < length (ds_aflw s)"
  proof -
    assume op: "\<not> ds_seen s ! v \<and> \<not> is_lonely v"
    have "Suc (ds_nxt s) = ds_nxt (phase2_step fl v s)" using phase2_step_nxt_open[OF conjunct1[OF op] conjunct2[OF op] Suc.prems(1,2) vvc] by simp
    with mono ff4' le4 show "ds_nxt s < length (ds_aflw s)" by linarith
  qed
  have gla5: "\<not> ds_seen s ! v \<and> \<not> is_lonely v \<Longrightarrow> ds_nxt s < length (ds_aest s)"
  proof -
    assume op: "\<not> ds_seen s ! v \<and> \<not> is_lonely v"
    have "Suc (ds_nxt s) = ds_nxt (phase2_step fl v s)" using phase2_step_nxt_open[OF conjunct1[OF op] conjunct2[OF op] Suc.prems(1,2) vvc] by simp
    with mono ff5' le5 show "ds_nxt s < length (ds_aest s)" by linarith
  qed
  have IH: "<dfs_rel fl0 es0 (free_out_edges fl) (free_out_hi fl) (free_in_edges fl) (free_in_hi fl) st (phase2_step fl v s) * imb_arr \<mapsto>\<^sub>a imbalance * ofh_arr \<mapsto>\<^sub>a out_hi * ifh_arr \<mapsto>\<^sub>a in_hi>
              phase2_imp st imb_arr ofh_arr ifh_arr m vcount (Suc v) n
            <\<lambda>_. dfs_rel fl0 es0 (free_out_edges fl) (free_out_hi fl) (free_in_edges fl) (free_in_hi fl) st (fold (phase2_step fl) [Suc v..<Suc n] (phase2_step fl v s)) * imb_arr \<mapsto>\<^sub>a imbalance * ofh_arr \<mapsto>\<^sub>a out_hi * ifh_arr \<mapsto>\<^sub>a in_hi>"
    by (rule Suc.hyps(1)[OF kk conjunct1[OF wsd'] conjunct1[OF conjunct2[OF wsd']] conjunct2[OF conjunct2[OF wsd']] ff1' ff2' ff3' ff4' ff5' Suc.prems(9) Suc.prems(10) Suc.prems(11) Suc.prems(12) Suc.prems(13) Suc.prems(14)])
  show ?case
    apply (subst phase2_imp.simps)
    apply (simp only: if_not_P[OF nnv] foldeq)
    apply (sep_auto heap: phase2_step_imp_combined[OF Suc.prems(1,2,3) vvc vim gla1 gla2 gla3 gla4 gla5 lc1 lc2 loh lih] IH)
    done
qed

subsection \<open>Layer (d.8): assembling @{const build_tree_imp}\<close>

text \<open>Single-field @{const dfs_rel} updates for the four state fields the tree-builder seeds before its
      two scans (@{term ds_snum} / @{term ds_prev} / @{term ds_nxt} / the DFS stack) and for the final
      @{term ds_lsuc} write, plus a @{term ds_prev} read.  Setting @{term ds_nxt} to @{term 0} makes the
      artificial-edge counting conditions of @{const dfs_rel} vacuous; setting the fill pointer to
      @{term 0} empties the abstract stack.\<close>
lemma dfs_rel_prev_upd:
  "<dfs_rel fl0 es0 oe oh ie ih st s> Ref.update (di_prev st) p <\<lambda>_. dfs_rel fl0 es0 oe oh ie ih st (s\<lparr>ds_prev := p\<rparr>)>"
  unfolding dfs_rel_def by sep_auto

lemma dfs_rel_snum_upd:
  assumes "i < length (ds_snum s)"
  shows "<dfs_rel fl0 es0 oe oh ie ih st s> arr_upd (snum_impl (di_tree st)) i x <\<lambda>_. dfs_rel fl0 es0 oe oh ie ih st (s\<lparr>ds_snum := (ds_snum s)[i := x]\<rparr>)>"
  unfolding dfs_rel_def by (sep_auto simp: assms)

lemma dfs_rel_nxt_upd0:
  "<dfs_rel fl0 es0 oe oh ie ih st s> Ref.update (di_nxt st) 0 <\<lambda>_. dfs_rel fl0 es0 oe oh ie ih st (s\<lparr>ds_nxt := 0\<rparr>)>"
  unfolding dfs_rel_def by sep_auto

lemma dfs_rel_sp_upd0:
  "<dfs_rel fl0 es0 oe oh ie ih st s> Ref.update (di_sp st) 0 <\<lambda>_. dfs_rel fl0 es0 oe oh ie ih st (s\<lparr>ds_stk := []\<rparr>)>"
  unfolding dfs_rel_def by (sep_auto simp: stk_rel_def)

lemma dfs_rel_prev_get:
  "<dfs_rel fl0 es0 oe oh ie ih st s> Ref.lookup (di_prev st) <\<lambda>r. dfs_rel fl0 es0 oe oh ie ih st s * \<up>(r = ds_prev s)>"
  unfolding dfs_rel_def by sep_auto

lemma dfs_rel_lsuc_upd:
  assumes "i < length (ds_lsuc s)"
  shows "<dfs_rel fl0 es0 oe oh ie ih st s> arr_upd (lsuc_impl (di_tree st)) i x <\<lambda>_. dfs_rel fl0 es0 oe oh ie ih st (s\<lparr>ds_lsuc := (ds_lsuc s)[i := x]\<rparr>)>"
  unfolding dfs_rel_def by (sep_auto simp: assms)

text \<open>The seed state @{const dfs_init} satisfies the two DFS-loop invariants that are not already
      @{thm dfs_init_sized}: its stack is empty (so @{const dfs_wf} / @{const dref_inv} hold trivially)
      and every parent entry is @{term 0}.\<close>
lemma dfs_wf_dfs_init: "dfs_wf dfs_init"
  by (simp add: dfs_wf_def dfs_init_def)

lemma dref_inv_dfs_init: "dref_inv dfs_init"
  by (simp add: dref_inv_def dfs_init_def nth_replicate del: replicate_Suc)

text \<open>Both scans preserve the three DFS-loop invariants along the whole vertex fold (each step does, by
      @{thm phase1_step_wsd} / @{thm phase2_step_wsd}).\<close>
lemma fold_phase1_step_wsd:
  assumes "dfs_wf s" "dfs_sized s" "dref_inv s" "\<forall>w\<in>set xs. w < vcount"
  shows "dfs_wf (fold (phase1_step fl) xs s) \<and> dfs_sized (fold (phase1_step fl) xs s) \<and> dref_inv (fold (phase1_step fl) xs s)"
  using assms
proof (induction xs arbitrary: s)
  case Nil then show ?case by simp
next
  case (Cons w ws)
  have wvc: "w < vcount" using Cons.prems(4) by simp
  have wsd: "dfs_wf (phase1_step fl w s) \<and> dfs_sized (phase1_step fl w s) \<and> dref_inv (phase1_step fl w s)"
    using phase1_step_wsd[OF Cons.prems(1,2,3) wvc] .
  show ?case using Cons.IH[OF conjunct1[OF wsd] conjunct1[OF conjunct2[OF wsd]] conjunct2[OF conjunct2[OF wsd]]] Cons.prems(4) by simp
qed

lemma fold_phase2_step_wsd:
  assumes "dfs_wf s" "dfs_sized s" "dref_inv s" "\<forall>w\<in>set xs. w < vcount"
  shows "dfs_wf (fold (phase2_step fl) xs s) \<and> dfs_sized (fold (phase2_step fl) xs s) \<and> dref_inv (fold (phase2_step fl) xs s)"
  using assms
proof (induction xs arbitrary: s)
  case Nil then show ?case by simp
next
  case (Cons w ws)
  have wvc: "w < vcount" using Cons.prems(4) by simp
  have wsd: "dfs_wf (phase2_step fl w s) \<and> dfs_sized (phase2_step fl w s) \<and> dref_inv (phase2_step fl w s)"
    using phase2_step_wsd[OF Cons.prems(1,2,3) wvc] .
  show ?case using Cons.IH[OF conjunct1[OF wsd] conjunct1[OF conjunct2[OF wsd]] conjunct2[OF conjunct2[OF wsd]]] Cons.prems(4) by simp
qed

text \<open>The tree builder @{const build_tree_imp} refines the functional @{const build_tree}: it seeds the
      four root fields (@{term ds_snum} at @{term vcount}, @{term ds_prev}, @{term ds_nxt}, the stack) —
      each write is idempotent on @{const dfs_init} — then runs the two scans and the final @{term ds_lsuc}
      write.  Since @{const build_tree} starts phase 1 from @{const dfs_init} (where @{term ds_nxt} is
      @{term 0}), the phase-1 in-bounds bound is the trivial \<open>0 + n \<le> n\<close>; the composable phase-2 bound is
      @{thm build_tree_nxt_le}.  The two scans are sequenced with @{thm wlp_apply_ht} (a plain
      @{method sep_auto} does not fire a rule whose precondition has two heap conjuncts, \<open>dfs_rel \<dots> \<^emph> imb\<close>,
      on a bare @{const wlp} goal), framing the @{const out_hi} / @{const in_hi} arrays across phase 1.\<close>
lemma build_tree_imp_rule:
  assumes nvc: "n < vcount" and lim: "Suc vcount \<le> length imbalance"
    and lol: "vcount \<le> length out_lo" and lil: "vcount \<le> length in_lo"
    and loh: "vcount \<le> length out_hi" and lih: "vcount \<le> length in_hi"
  shows "<dfs_rel fl0 es0 (free_out_edges acyc_flow) (free_out_hi acyc_flow) (free_in_edges acyc_flow) (free_in_hi acyc_flow) st dfs_init * imb_arr \<mapsto>\<^sub>a imbalance * ofh_arr \<mapsto>\<^sub>a out_hi * ifh_arr \<mapsto>\<^sub>a in_hi>
           build_tree_imp st imb_arr ofh_arr ifh_arr m vcount n
         <\<lambda>_. dfs_rel fl0 es0 (free_out_edges acyc_flow) (free_out_hi acyc_flow) (free_in_edges acyc_flow) (free_in_hi acyc_flow) st (build_tree acyc_flow) * imb_arr \<mapsto>\<^sub>a imbalance * ofh_arr \<mapsto>\<^sub>a out_hi * ifh_arr \<mapsto>\<^sub>a in_hi>"
proof -
  have allvc: "\<forall>w\<in>set vs_list. w < vcount" using nvc by (auto simp: vs_list_def)
  have pre0: "dfs_inv acyc_flow dfs_init \<and> ds_stk dfs_init = []" using dfs_init_inv by (simp add: dfs_init_def)
  have wsd1: "dfs_wf (phase1 acyc_flow dfs_init) \<and> dfs_sized (phase1 acyc_flow dfs_init) \<and> dref_inv (phase1 acyc_flow dfs_init)"
    using fold_phase1_step_wsd[OF dfs_wf_dfs_init dfs_init_sized dref_inv_dfs_init allvc] by (simp add: phase1_def)
  have a1: "art_len (phase1 acyc_flow dfs_init)" using phase1_art_len[OF pre0 dfs_init_art_len] .
  have p1a: "length (ds_afst (phase1 acyc_flow dfs_init)) = length vs_list \<and> length (ds_asnd (phase1 acyc_flow dfs_init)) = length vs_list \<and> length (ds_acap (phase1 acyc_flow dfs_init)) = length vs_list \<and> length (ds_aflw (phase1 acyc_flow dfs_init)) = length vs_list \<and> length (ds_aest (phase1 acyc_flow dfs_init)) = length vs_list"
    using a1 by (simp add: art_len_def)
  have bt_nxt: "ds_nxt (build_tree acyc_flow) = ds_nxt (phase2 acyc_flow (phase1 acyc_flow dfs_init))" by (simp add: build_tree_def Let_def)
  have nxt_le: "ds_nxt (phase2 acyc_flow (phase1 acyc_flow dfs_init)) \<le> length vs_list" using build_tree_nxt_le bt_nxt by simp
  have phase1_fold_eq: "fold (phase1_step acyc_flow) [Suc 0..<Suc n] dfs_init = phase1 acyc_flow dfs_init" by (simp add: phase1_def vs_list_def)
  have phase2_fold_eq: "fold (phase2_step acyc_flow) [Suc 0..<Suc n] (phase1 acyc_flow dfs_init) = phase2 acyc_flow (phase1 acyc_flow dfs_init)" by (simp add: phase2_def vs_list_def)
  have f1: "ds_nxt (fold (phase2_step acyc_flow) [Suc 0..<Suc n] (phase1 acyc_flow dfs_init)) \<le> length (ds_afst (phase1 acyc_flow dfs_init))" using nxt_le p1a unfolding phase2_fold_eq by simp
  have f2: "ds_nxt (fold (phase2_step acyc_flow) [Suc 0..<Suc n] (phase1 acyc_flow dfs_init)) \<le> length (ds_asnd (phase1 acyc_flow dfs_init))" using nxt_le p1a unfolding phase2_fold_eq by simp
  have f3: "ds_nxt (fold (phase2_step acyc_flow) [Suc 0..<Suc n] (phase1 acyc_flow dfs_init)) \<le> length (ds_acap (phase1 acyc_flow dfs_init))" using nxt_le p1a unfolding phase2_fold_eq by simp
  have f4: "ds_nxt (fold (phase2_step acyc_flow) [Suc 0..<Suc n] (phase1 acyc_flow dfs_init)) \<le> length (ds_aflw (phase1 acyc_flow dfs_init))" using nxt_le p1a unfolding phase2_fold_eq by simp
  have f5: "ds_nxt (fold (phase2_step acyc_flow) [Suc 0..<Suc n] (phase1 acyc_flow dfs_init)) \<le> length (ds_aest (phase1 acyc_flow dfs_init))" using nxt_le p1a unfolding phase2_fold_eq by simp
  have lim2: "vcount \<le> length imbalance" using lim by simp
  have c1: "ds_nxt dfs_init + (Suc n - Suc 0) \<le> length (ds_afst dfs_init)" by (simp add: dfs_init_def length_vs_list)
  have c2: "ds_nxt dfs_init + (Suc n - Suc 0) \<le> length (ds_asnd dfs_init)" by (simp add: dfs_init_def length_vs_list)
  have c3: "ds_nxt dfs_init + (Suc n - Suc 0) \<le> length (ds_acap dfs_init)" by (simp add: dfs_init_def length_vs_list)
  have c4: "ds_nxt dfs_init + (Suc n - Suc 0) \<le> length (ds_aflw dfs_init)" by (simp add: dfs_init_def length_vs_list)
  have c5: "ds_nxt dfs_init + (Suc n - Suc 0) \<le> length (ds_aest dfs_init)" by (simp add: dfs_init_def length_vs_list)
  have szp2: "dfs_sized (phase2 acyc_flow (phase1 acyc_flow dfs_init))"
    using fold_phase2_step_wsd[OF conjunct1[OF wsd1] conjunct1[OF conjunct2[OF wsd1]] conjunct2[OF conjunct2[OF wsd1]] allvc] by (simp add: phase2_def)
  have lsuc_len: "vcount < length (ds_lsuc (phase2 acyc_flow (phase1 acyc_flow dfs_init)))" using szp2 by (simp add: dfs_sized_def)
  have bt_eq: "(phase2 acyc_flow (phase1 acyc_flow dfs_init))\<lparr>ds_lsuc := (ds_lsuc (phase2 acyc_flow (phase1 acyc_flow dfs_init)))[vcount := ds_prev (phase2 acyc_flow (phase1 acyc_flow dfs_init))]\<rparr> = build_tree acyc_flow"
    by (simp add: build_tree_def Let_def)
  have snum_len: "vcount < length (ds_snum dfs_init)" by (simp add: dfs_init_def del: replicate_Suc)
  have idall: "dfs_init\<lparr>ds_snum := (ds_snum dfs_init)[vcount := Suc 0], ds_prev := vcount, ds_nxt := 0, ds_stk := []\<rparr> = dfs_init"
    by (simp add: dfs_init_def list_update_overwrite del: replicate_Suc)
  have phase1_triple: "<dfs_rel fl0 es0 (free_out_edges acyc_flow) (free_out_hi acyc_flow) (free_in_edges acyc_flow) (free_in_hi acyc_flow) st dfs_init * imb_arr \<mapsto>\<^sub>a imbalance> phase1_imp st imb_arr m vcount (Suc 0) n <\<lambda>_. dfs_rel fl0 es0 (free_out_edges acyc_flow) (free_out_hi acyc_flow) (free_in_edges acyc_flow) (free_in_hi acyc_flow) st (phase1 acyc_flow dfs_init) * imb_arr \<mapsto>\<^sub>a imbalance>"
    by (rule phase1_imp_rule[where fl=acyc_flow, OF dfs_wf_dfs_init dfs_init_sized dref_inv_dfs_init c1 c2 c3 c4 c5 nvc lim lol lil, unfolded phase1_fold_eq])
  have phase2_triple: "<dfs_rel fl0 es0 (free_out_edges acyc_flow) (free_out_hi acyc_flow) (free_in_edges acyc_flow) (free_in_hi acyc_flow) st (phase1 acyc_flow dfs_init) * imb_arr \<mapsto>\<^sub>a imbalance * ofh_arr \<mapsto>\<^sub>a out_hi * ifh_arr \<mapsto>\<^sub>a in_hi> phase2_imp st imb_arr ofh_arr ifh_arr m vcount (Suc 0) n <\<lambda>_. dfs_rel fl0 es0 (free_out_edges acyc_flow) (free_out_hi acyc_flow) (free_in_edges acyc_flow) (free_in_hi acyc_flow) st (phase2 acyc_flow (phase1 acyc_flow dfs_init)) * imb_arr \<mapsto>\<^sub>a imbalance * ofh_arr \<mapsto>\<^sub>a out_hi * ifh_arr \<mapsto>\<^sub>a in_hi>"
    by (rule phase2_imp_rule[where fl=acyc_flow, OF conjunct1[OF wsd1] conjunct1[OF conjunct2[OF wsd1]] conjunct2[OF conjunct2[OF wsd1]] f1 f2 f3 f4 f5 nvc lim2 lol lil loh lih, unfolded phase2_fold_eq])
  show ?thesis
    unfolding build_tree_imp_def
    apply (sep_auto heap: dfs_rel_snum_upd[OF snum_len] dfs_rel_prev_upd dfs_rel_nxt_upd0 dfs_rel_sp_upd0 simp: idall)
    apply (rule wlp_apply_ht[OF _ _ phase1_triple, where F="ofh_arr \<mapsto>\<^sub>a out_hi * ifh_arr \<mapsto>\<^sub>a in_hi * true"])
      apply assumption
     apply sep_auto
    apply (rule wlp_apply_ht[OF _ _ phase2_triple, where F="true"])
      apply assumption
     apply sep_auto
    apply (sep_auto heap: dfs_rel_prev_get dfs_rel_lsuc_upd[OF lsuc_len] simp: bt_eq)
    done
qed

subsection \<open>Layer (e): the concrete spanning-tree operations refine the arborescence ADT\<close>

text \<open>The three tree operations the network-simplex loop calls — @{const ns_swap_edge_imp},
      @{const ns_get_path_pair_imp}, @{const ns_shift_pot_imp} — are ported from the verified
      @{typ ndtree_impl} primitives of \<open>Rooted_Arborescense_Refinement\<close>.  Their imperative Hoare rules
      here match, one-for-one, the abstract @{locale arborescense_adt} axioms that
      @{locale network_simplex_impl_refine} assumes (with @{const ndtree_assn} for the tree assertion and
      the inherited @{const arb_invar} / @{const abstract_arb} / @{const get_path_pair_impl} /
      @{const swap_edge_impl} for the abstract side), so they discharge those axioms in the Layer (e)
      interpretation.\<close>

text \<open>A fill-pointer never overruns its array: if the prefix @{term \<open>take n zs\<close>} equals a list of
      length @{term n}, then @{term \<open>n \<le> length zs\<close>}.\<close>
lemma take_len_bound: "take n zs = ws \<Longrightarrow> length ws = n \<Longrightarrow> n \<le> length zs"
  by (metis length_take min.bounded_iff order_refl)

text \<open>Tree-edge swap: compute the join of the entering edge's endpoints (@{thm join_of_imp_correct}) and
      hand it to @{const update_tree_imp}.  The abstract swap-edge preconditions (a fundamental-circuit
      walk through the entering edge) are exactly those of @{thm swap_edge_axiom1}; we reuse its
      derivation to place @{term x} on @{term u}'s root-path below the join (@{text xfu}), off the root
      (@{text xnr}), with the join itself in the tree (@{text jnV}) — the premises of
      @{thm update_tree_imp_rule}.\<close>
lemma ns_swap_edge_imp_rule:
  assumes inv: "arb_invar rt Vt S" and gp: "get_path_pair_impl S u v = (p1, p2)"
    and une: "u \<noteq> v" and wu: "walk_betw (abstract_arb S) u (p1 @ a # p3) rt"
    and dist: "distinct (p1 @ a # p3)" and em: "(x, y) \<in> set (edges_of_vwalk (p1 @ [a]))"
    and uV: "u \<in> Vt" and vV: "v \<in> Vt"
  shows "<ndtree_assn Vt S Ti> ns_swap_edge_imp Ti x u v
           <\<lambda>_. ndtree_assn Vt (swap_edge_impl S x u v) Ti>"
proof -
  have rinv: "rooted_arborescense_invar rt Vt (prnt S)" using inv unfolding arb_invar_def by simp
  have ps: "parent_spec (prnt S)" by (rule rooted_arborescense_invar_parent_spec[OF rinv])
  have wfu: "p1 @ a # p3 = follow (prnt S) u" by (rule unique_walk_to_root[OF inv uV wu dist])
  define j where "j = join_of (prnt S) u v"
  have fu_split: "follow (prnt S) u = p1 @ follow (prnt S) j"
    using get_path_pair_impl_correct(1)[OF inv uV vV gp] by (simp add: j_def)
  have p1ne: "p1 \<noteq> []"
  proof (rule ccontr)
    assume "\<not> p1 \<noteq> []" hence "p1 = []" by simp
    hence "edges_of_vwalk (p1 @ [a]) = []" by simp
    thus False using em by simp
  qed
  have ev_dec: "edges_of_vwalk (p1 @ [a]) = edges_of_vwalk p1 @ [(last p1, a)]"
    using edges_of_vwalk_append_3[OF p1ne, of "[a]"] p1ne by simp
  have xp1: "x \<in> set p1"
  proof -
    from em ev_dec have "(x, y) \<in> set (edges_of_vwalk p1) \<or> (x, y) = (last p1, a)" by auto
    thus ?thesis
    proof
      assume "(x, y) \<in> set (edges_of_vwalk p1)" thus ?thesis using v_in_edge_in_vwalk by fast
    next
      assume "(x, y) = (last p1, a)" thus ?thesis using p1ne last_in_set by auto
    qed
  qed
  have xfu: "x \<in> set (follow (prnt S) u)" using xp1 wfu by (metis Un_iff set_append)
  have fjne: "follow (prnt S) j \<noteq> []" by (rule follow_ne_ps[OF ps])
  have jinfj: "j \<in> set (follow (prnt S) j)" using fjne follow_hd_ps[OF ps, of j] by (metis hd_in_set)
  have jfu: "j \<in> set (follow (prnt S) u)" using fu_split jinfj by simp
  have jnV: "j \<in> Vt" using follow_subset_V[OF rinv uV] jfu by auto
  have du: "distinct (follow (prnt S) u)" by (rule follow_distinct_ps[OF ps])
  have disjp1fj: "set p1 \<inter> set (follow (prnt S) j) = {}"
    using du fu_split by (simp add: distinct_append)
  have rinfj: "rt \<in> set (follow (prnt S) j)"
    using follow_last_root[OF inv jnV] fjne by (metis last_in_set)
  have xnr: "x \<noteq> rt" using xp1 rinfj disjp1fj by auto
  have jnV': "join_of (prnt S) u v \<in> Vt" using jnV j_def by simp
  show ?thesis
    unfolding ns_swap_edge_imp_def swap_edge_impl_def
    apply (rule ht_bind[OF join_of_imp_correct[OF inv uV vV]])
    apply (sep_auto heap: update_tree_imp_rule[OF inv uV vV xfu jnV' xnr])
    done
qed

text \<open>Fundamental-circuit path search: the verified @{const get_path_pair_imp} with the two caller path
      arrays moved after the endpoints.  The two arrays hold a longest tree path (@{term \<open>card Vt - 1\<close>}
      entries), the fill pointers are @{term \<open>length p1\<close>} / @{term \<open>length p2\<close>}, and the array prefixes
      become the functional branch paths @{term \<open>get_path_pair_impl S u v\<close>}.  The two length bounds
      @{term \<open>length p_i \<le> length l_i\<close>} follow from @{thm take_len_bound}; the final existential is
      introduced explicitly (@{thm ent_ex_postI}) since @{method sep_auto}'s entailment solver loops on
      the framed @{term true}.\<close>
lemma ns_get_path_pair_imp_rule:
  assumes inv: "arb_invar rt Vt S" and une: "u \<noteq> v" and uV: "u \<in> Vt" and vV: "v \<in> Vt"
    and l1: "card Vt - 1 \<le> length xs1" and l2: "card Vt - 1 \<le> length xs2"
  shows "<ndtree_assn Vt S Ti * a1 \<mapsto>\<^sub>a xs1 * a2 \<mapsto>\<^sub>a xs2>
           ns_get_path_pair_imp Ti u v a1 a2
         <\<lambda>(ptr1, ptr2). \<exists>\<^sub>A l1' l2'. ndtree_assn Vt S Ti * a1 \<mapsto>\<^sub>a l1' * a2 \<mapsto>\<^sub>a l2' *
             \<up>(length l1' = length xs1 \<and> length l2' = length xs2 \<and>
               ptr1 \<le> length l1' \<and> ptr2 \<le> length l2' \<and>
               (take ptr1 l1', take ptr2 l2') = get_path_pair_impl S u v)>"
proof -
  obtain p1 p2 where pp: "get_path_pair_impl S u v = (p1, p2)"
    by (cases "get_path_pair_impl S u v") auto
  have len1: "card Vt \<le> Suc (length xs1)" using l1 by linarith
  have len2: "card Vt \<le> Suc (length xs2)" using l2 by linarith
  show ?thesis
    unfolding ns_get_path_pair_imp_def
    apply (sep_auto heap: get_path_pair_imp_rule[OF inv uV vV len1 len2 pp] simp: pp)
    subgoal premises prems for a b ys1 ys2
    proof -
      have b1: "length p1 \<le> length ys1"
        using prems(4) by (metis length_take min.bounded_iff order_refl)
      have b2: "length p2 \<le> length ys2"
        using prems(5) by (metis length_take min.bounded_iff order_refl)
      have cond: "length ys1 = length xs1 \<and> length ys2 = length xs2 \<and>
                  length p1 \<le> length ys1 \<and> length p2 \<le> length ys2 \<and>
                  take (length p1) ys1 = p1 \<and> take (length p2) ys2 = p2"
        using prems(2) prems(3) prems(4) prems(5) b1 b2 by blast
      have ent: "ndtree_assn Vt S Ti * a1 \<mapsto>\<^sub>a ys1 * a2 \<mapsto>\<^sub>a ys2 * true
                 \<Longrightarrow>\<^sub>A (\<exists>\<^sub>A l1' l2'. ndtree_assn Vt S Ti * a1 \<mapsto>\<^sub>a l1' * a2 \<mapsto>\<^sub>a l2' * true *
                     \<up>(length l1' = length xs1 \<and> length l2' = length xs2 \<and>
                       length p1 \<le> length l1' \<and> length p2 \<le> length l2' \<and>
                       take (length p1) l1' = p1 \<and> take (length p2) l2' = p2))"
        apply (rule ent_ex_postI[where x = ys1], rule ent_ex_postI[where x = ys2])
        apply (subst ent_pure_post_iff)
        apply (intro conjI)
         apply (rule ent_refl)
        using cond apply blast
        done
      show ?thesis by (rule entailsD[OF ent prems(1)])
    qed
    done
qed

text \<open>Functional bridge: the branch-free potential walk @{const shift_pot_impl} is a subtree fold over
      the thread block opposed to the root — i.e. @{const iterate_root_opposed_impl} with the per-node
      read/shift/write step.  The block decomposition (@{thm block_props}) supplies the
      \<open>follow (thrd S) v = bl @ lsuc S v # rest\<close> split with \<open>lsuc S v \<notin> set bl\<close> that
      @{thm shift_pot_up_loop_subtree_fold} / @{thm shift_pot_down_loop_subtree_fold} need.\<close>
lemma shift_pot_impl_iterate:
  assumes inv: "arb_invar rt Vt S" and vV: "v \<in> Vt"
  shows "shift_pot_impl S v pl g up
       = iterate_root_opposed_impl S v
           (\<lambda>x acc. acc[x := if up then pval_plus (acc ! x) g else pval_minus (acc ! x) g]) pl"
proof -
  have pst: "parent_spec (thrd S)" using inv unfolding arb_invar_def by simp
  have bne: "block S v \<noteq> []" by (rule block_props(2)[OF inv vV])
  have blast': "last (block S v) = lsuc S v" by (rule block_props(3)[OF inv vV])
  have decomp: "follow (thrd S) v
                  = block S v @ (case thrd S (lsuc S v) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd S) w)"
    by (rule block_props(1)[OF inv vV])
  define bl where "bl = butlast (block S v)"
  have blk: "block S v = bl @ [lsuc S v]"
    unfolding bl_def using append_butlast_last_id[OF bne] blast' by simp
  define rest where "rest = (case thrd S (lsuc S v) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd S) w)"
  have L: "follow (thrd S) v = bl @ (lsuc S v) # rest" using decomp blk rest_def by simp
  have distf: "distinct (follow (thrd S) v)" by (rule follow_distinct_ps[OF pst])
  have notin: "lsuc S v \<notin> set bl" using distf L by (auto simp: distinct_append)
  show ?thesis
  proof (cases up)
    case True
    have "shift_pot_impl S v pl g up = shift_pot_up_loop S (lsuc S v) g v pl"
      by (simp add: shift_pot_impl_def True)
    also have "\<dots> = subtree_fold S (lsuc S v) v (\<lambda>x acc. acc[x := pval_plus (acc ! x) g]) pl"
      by (rule shift_pot_up_loop_subtree_fold[OF pst L notin])
    also have "\<dots> = iterate_root_opposed_impl S v
                     (\<lambda>x acc. acc[x := if up then pval_plus (acc ! x) g else pval_minus (acc ! x) g]) pl"
      by (simp add: iterate_root_opposed_impl_def True)
    finally show ?thesis .
  next
    case False
    have "shift_pot_impl S v pl g up = shift_pot_down_loop S (lsuc S v) g v pl"
      by (simp add: shift_pot_impl_def False)
    also have "\<dots> = subtree_fold S (lsuc S v) v (\<lambda>x acc. acc[x := pval_minus (acc ! x) g]) pl"
      by (rule shift_pot_down_loop_subtree_fold[OF pst L notin])
    also have "\<dots> = iterate_root_opposed_impl S v
                     (\<lambda>x acc. acc[x := if up then pval_plus (acc ! x) g else pval_minus (acc ! x) g]) pl"
      by (simp add: iterate_root_opposed_impl_def False)
    finally show ?thesis .
  qed
qed

text \<open>Potential shift: the subtree-fold refinement @{thm iterate_root_opposed_imp_rule} instantiated at
      the read/shift/write per-node step, with the array-length invariant @{term \<open>\<forall>w\<in>Vt. w < length acc\<close>}
      carried in the fold relation @{term R} (so every visited @{term \<open>x \<in> Vt\<close>} is in range).  The
      resulting functional value @{term \<open>iterate_root_opposed_impl S v f pl\<close>} is @{const shift_pot_impl}
      by @{thm shift_pot_impl_iterate}.\<close>
lemma ns_shift_pot_imp_rule:
  assumes inv: "arb_invar rt Vt S" and vV: "v \<in> Vt" and pinv: "\<forall>w\<in>Vt. w < length pl"
  shows "<ndtree_assn Vt S Ti * pa \<mapsto>\<^sub>a pl>
           ns_shift_pot_imp Ti v pa g up
         <\<lambda>_. ndtree_assn Vt S Ti * pa \<mapsto>\<^sub>a shift_pot_impl S v pl g up>"
proof -
  define f where "f = (\<lambda>x acc. acc[x := if up then pval_plus (acc ! x) g else pval_minus (acc ! x) g])"
  define R where "R = (\<lambda>(_::unit) acc. pa \<mapsto>\<^sub>a acc * \<up>(\<forall>w\<in>Vt. w < length acc))"
  have fi: "\<And>x a. x \<in> Vt \<Longrightarrow>
             <R () a>
               (\<lambda>x (_::unit). do { p \<leftarrow> Array.nth pa x;
                                   _ \<leftarrow> Array.upd x (if up then pval_plus p g else pval_minus p g) pa;
                                   return () }) x ()
             <\<lambda>_. R () (f x a)>"
  proof -
    fix x a assume xV: "x \<in> Vt"
    show "<R () a>
            (\<lambda>x (_::unit). do { p \<leftarrow> Array.nth pa x;
                                _ \<leftarrow> Array.upd x (if up then pval_plus p g else pval_minus p g) pa;
                                return () }) x ()
          <\<lambda>_. R () (f x a)>"
      unfolding R_def f_def by (sep_auto simp: xV)
  qed
  have main: "<ndtree_assn Vt S Ti * R () pl>
                ns_shift_pot_imp Ti v pa g up
              <\<lambda>_. ndtree_assn Vt S Ti * R () (iterate_root_opposed_impl S v f pl)>"
    unfolding ns_shift_pot_imp_def
    apply (rule iterate_root_opposed_imp_rule[where R = R and f = f and ai = "()"])
      apply (rule inv)
     apply (rule vV)
    apply (rule fi)
    apply assumption
    done
  have R_pl: "ndtree_assn Vt S Ti * pa \<mapsto>\<^sub>a pl \<Longrightarrow>\<^sub>A ndtree_assn Vt S Ti * R () pl"
    unfolding R_def using pinv by sep_auto
  have R_res: "\<And>u. ndtree_assn Vt S Ti * R () (iterate_root_opposed_impl S v f pl)
              \<Longrightarrow>\<^sub>A ndtree_assn Vt S Ti * pa \<mapsto>\<^sub>a shift_pot_impl S v pl g up"
    unfolding R_def shift_pot_impl_iterate[OF inv vV] f_def[symmetric] by sep_auto
  show ?thesis
    by (rule ht_cons_prec[OF R_pl R_res main])
qed

subsection \<open>Layer (e): the entering-edge selector refines @{const sel_select_impl}\<close>

text \<open>The cost part of a reduced-cost descriptor: a real cost cell @{term \<open>(M_0, cost_list ! e)\<close>} for a
      genuine edge (@{term \<open>e < m\<close>}), the big-M unit @{const pval_M} for an artificial one.  Reads the
      cost array only on the genuine branch, exactly where @{const cost_pval} does.\<close>
lemma cost_pval_imp_rule:
  assumes ce: "e < m \<Longrightarrow> e < length col \<and> col ! e = cost_list ! e"
  shows "<cost_arr \<mapsto>\<^sub>a col> cost_pval_imp m cost_arr e
           <\<lambda>r. cost_arr \<mapsto>\<^sub>a col * \<up>(r = cost_pval e)>"
  unfolding cost_pval_imp_def cost_pval_def
  using ce by (cases "e < m") sep_auto+

text \<open>One-arc pricing: @{const evaluate_imp} reads the two endpoints (@{term \<open>fst_all ! e\<close>} /
      @{term \<open>snd_all ! e\<close>}), the edge tag and — off a self-loop — the reduced cost, exactly the
      functional @{const evaluate}.  A self-loop is ineligible without pricing; otherwise the M-free sign
      test on the assembled descriptor gives eligibility, alongside the @{term \<open>InU\<close>} flag and the
      descriptor itself.\<close>
lemma evaluate_imp_rule:
  assumes fae: "e < length fstl" and sae: "e < length sndl"
    and cvce: "e < m \<Longrightarrow> e < length col \<and> col ! e = cost_list ! e"
    and esle: "e < length esl"
    and pa: "fst_all ! e < length \<pi>" and pd: "snd_all ! e < length \<pi>"
    and fok: "fstl ! e = fst_all ! e" and sok: "sndl ! e = snd_all ! e"
  shows "<fst_arr \<mapsto>\<^sub>a fstl * snd_arr \<mapsto>\<^sub>a sndl * cost_arr \<mapsto>\<^sub>a col * es_arr \<mapsto>\<^sub>a esl * pt \<mapsto>\<^sub>a \<pi>>
           evaluate_imp m fst_arr snd_arr cost_arr es_arr pt e
         <\<lambda>r. fst_arr \<mapsto>\<^sub>a fstl * snd_arr \<mapsto>\<^sub>a sndl * cost_arr \<mapsto>\<^sub>a col * es_arr \<mapsto>\<^sub>a esl * pt \<mapsto>\<^sub>a \<pi>
              * \<up>(r = evaluate esl \<pi> e)>"
  unfolding evaluate_imp_def evaluate_def Let_def
  using fae sae esle pa pd
  by (sep_auto simp: fok sok split: edge_tag.splits heap: cost_pval_imp_rule[OF cvce])

text \<open>Minor iteration: one pass over the live cache prefix @{term \<open>[i..<len]\<close>}, pricing each entry with
      @{const evaluate_imp}, keeping the eligible ones (advancing @{term i} and the running best) and
      deleting duds by swap-with-last.  Refines @{const scan_cache}: the imperative returns the final
      length / best while the cache array is left holding the functional result array.  Structural
      induction on the measure @{term \<open>len - i\<close>}, mirroring the fold-refinement style: one
      @{method sep_auto} with @{text \<open>split: if_splits\<close>} over the single functional unfolding \<open>scu\<close>,
      with both recursive calls discharged by the induction hypothesis.\<close>
lemma scan_cache_imp_rule:
  assumes "i \<le> len" and "len \<le> length a"
    and "\<And>e. e \<in> set (take len a) \<Longrightarrow>
        e < length fstl \<and> e < length sndl \<and> e < length esl \<and>
        (e < m \<longrightarrow> e < length col \<and> col ! e = cost_list ! e) \<and>
        fstl ! e = fst_all ! e \<and> sndl ! e = snd_all ! e \<and>
        fst_all ! e < length \<pi> \<and> snd_all ! e < length \<pi>"
  shows "<sarr \<mapsto>\<^sub>a a * es_arr \<mapsto>\<^sub>a esl * pt \<mapsto>\<^sub>a \<pi> * fst_arr \<mapsto>\<^sub>a fstl * snd_arr \<mapsto>\<^sub>a sndl * cost_arr \<mapsto>\<^sub>a col>
           scan_cache_imp m fst_arr snd_arr cost_arr es_arr pt sarr i len best
         <\<lambda>r. case scan_cache esl \<pi> i a len best of (a', rl, rb) \<Rightarrow>
                sarr \<mapsto>\<^sub>a a' * es_arr \<mapsto>\<^sub>a esl * pt \<mapsto>\<^sub>a \<pi> * fst_arr \<mapsto>\<^sub>a fstl
                * snd_arr \<mapsto>\<^sub>a sndl * cost_arr \<mapsto>\<^sub>a col * \<up>(r = (rl, rb))>"
  using assms
proof (induction "len - i" arbitrary: i len a best rule: less_induct)
  case less
  have mem_take: "\<And>j. j < len \<Longrightarrow> a ! j \<in> set (take len a)"
  proof -
    fix j assume j: "j < len"
    have "j < length (take len a)" using j less.prems(2) by simp
    hence "take len a ! j \<in> set (take len a)" by (rule nth_mem)
    thus "a ! j \<in> set (take len a)" using j by (simp add: nth_take)
  qed
  show ?case
  proof (cases "len \<le> i")
    case True
    show ?thesis
      by (subst scan_cache_imp.simps, subst scan_cache.simps) (sep_auto simp: True)
  next
    case False
    note lenF = False
    hence ilt: "i < len" by simp
    have iltl: "i < length a" using ilt less.prems(2) by simp
    have lenl: "len - 1 < length a" using ilt less.prems(2) by simp
    obtain elig u g where ev: "evaluate esl \<pi> (a ! i) = (elig, u, g)"
      by (cases "evaluate esl \<pi> (a ! i)") auto
    note eok = less.prems(3)[OF mem_take[OF ilt]]
    have eok1: "a ! i < length fstl" and eok2: "a ! i < length sndl"
      and eok3: "a ! i < length esl"
      and eok4: "a ! i < m \<Longrightarrow> a ! i < length col \<and> col ! (a ! i) = cost_list ! (a ! i)"
      and eokf: "fstl ! (a ! i) = fst_all ! (a ! i)" and eoks: "sndl ! (a ! i) = snd_all ! (a ! i)"
      and eok5: "fst_all ! (a ! i) < length \<pi>" and eok6: "snd_all ! (a ! i) < length \<pi>"
      using eok by auto
    note evr = evaluate_imp_rule[OF eok1 eok2 eok4 eok3 eok5 eok6 eokf eoks]
    have pref: "set (take (len - 1) a) \<subseteq> set (take len a)"
    proof -
      have "take (len - 1) a = take (len - 1) (take len a)" by (simp add: take_take)
      moreover have "set (take (len - 1) (take len a)) \<subseteq> set (take len a)" by (rule set_take_subset)
      ultimately show ?thesis by simp
    qed
    have sub: "set (take (len - 1) (a[i := a ! (len - 1)])) \<subseteq> set (take len a)"
    proof -
      have "set (take (len - 1) (a[i := a ! (len - 1)])) = set ((take (len - 1) a)[i := a ! (len - 1)])"
        by (simp add: take_update_swap)
      also have "\<dots> \<subseteq> insert (a ! (len - 1)) (set (take (len - 1) a))"
        by (rule set_update_subset_insert)
      also have "\<dots> \<subseteq> set (take len a)"
        using pref mem_take[of "len - 1"] ilt by auto
      finally show ?thesis .
    qed
    have m1: "len - Suc i < len - i" using ilt by simp
    have sle: "Suc i \<le> len" using ilt by simp
    \<comment> \<open>@{term best} is left schematic so the entering-edge tuple @{term g}, which @{method sep_auto}
        splits into a pair, still unifies through the induction hypothesis.\<close>
    note IH_elig = less.hyps[of len "Suc i" a, OF m1 sle less.prems(2) less.prems(3)]
    have m2: "len - 1 - i < len - i" using ilt by simp
    have ile: "i \<le> len - 1" using ilt by simp
    have lla2: "len - 1 \<le> length (a[i := a ! (len - 1)])" using less.prems(2) by simp
    have eok2': "\<And>e. e \<in> set (take (len - 1) (a[i := a ! (len - 1)])) \<Longrightarrow>
        e < length fstl \<and> e < length sndl \<and> e < length esl \<and>
        (e < m \<longrightarrow> e < length col \<and> col ! e = cost_list ! e) \<and>
        fstl ! e = fst_all ! e \<and> sndl ! e = snd_all ! e \<and>
        fst_all ! e < length \<pi> \<and> snd_all ! e < length \<pi>"
      using less.prems(3) sub by blast
    note IH_dud = less.hyps[of "len - 1" i "a[i := a ! (len - 1)]" best, OF m2 ile lla2 eok2']
    show ?thesis
      apply (subst scan_cache_imp.simps)
      apply (sep_auto simp: lenF ev iltl lenl lenl[unfolded One_nat_def] Let_def
                       split: if_splits heap: evr IH_elig IH_dud)
      done
  qed
qed


text \<open>Major iteration: the wrap-around block sweep from the bookmark @{term cur}, pricing each arc and
      pushing eligible ones at the length pointer, stopping on exhausted fuel, a full cache, or a
      completed block with the minimum met.  Refines @{const scan}; the cache array holds the functional
      result array.  Structural induction on the fuel; the arc-validity invariant @{term arc_ok} is
      constant (all arcs \<open>< mc\<close>) and @{term cur} stays in range by @{thm wrap_lt}.\<close>
lemma scan_imp_rule:
  assumes arc_ok: "\<And>e. e < mc \<Longrightarrow> e < length fstl \<and> e < length sndl \<and> e < length esl \<and>
        (e < m \<longrightarrow> e < length col \<and> col ! e = cost_list ! e) \<and> fstl ! e = fst_all ! e \<and> sndl ! e = snd_all ! e \<and> fst_all ! e < length \<pi> \<and> snd_all ! e < length \<pi>"
    and mcpos: "0 < mc"
  shows "cur < mc \<Longrightarrow> len \<le> max_candidates \<Longrightarrow> max_candidates \<le> length a \<Longrightarrow>
    <sarr \<mapsto>\<^sub>a a * es_arr \<mapsto>\<^sub>a esl * pt \<mapsto>\<^sub>a \<pi> * fst_arr \<mapsto>\<^sub>a fstl * snd_arr \<mapsto>\<^sub>a sndl * cost_arr \<mapsto>\<^sub>a col>
      scan_imp m fst_arr snd_arr cost_arr min_candidates max_candidates block_size mc es_arr pt sarr
               fuel bpos cur len best
    <\<lambda>r. case scan esl \<pi> mc fuel bpos cur a len best of (cur', a', len', rb) \<Rightarrow>
           sarr \<mapsto>\<^sub>a a' * es_arr \<mapsto>\<^sub>a esl * pt \<mapsto>\<^sub>a \<pi> * fst_arr \<mapsto>\<^sub>a fstl * snd_arr \<mapsto>\<^sub>a sndl * cost_arr \<mapsto>\<^sub>a col
           * \<up>(r = (cur', len', rb))>"
proof (induction fuel arbitrary: bpos cur len a best rule: less_induct)
  case (less fuel)
  note cur_mc = less.prems(1) and len_mc = less.prems(2) and lena = less.prems(3)
  show ?case
  proof (cases "fuel = 0 \<or> max_candidates \<le> len \<or> (bpos = 0 \<and> min_candidates \<le> len)")
    case True
    have imp_eq: "scan_imp m fst_arr snd_arr cost_arr min_candidates max_candidates block_size mc
                    es_arr pt sarr fuel bpos cur len best = Heap_Monad.return (cur, len, best)"
      using True by (subst scan_imp.simps) auto
    have fun_eq: "scan esl \<pi> mc fuel bpos cur a len best = (cur, a, len, best)"
      using True by (subst scan.simps) auto
    show ?thesis unfolding imp_eq fun_eq by sep_auto
  next
    case False
    hence g1: "fuel \<noteq> 0" and g2: "\<not> max_candidates \<le> len"
      and g3: "\<not> (bpos = 0 \<and> min_candidates \<le> len)" by auto
    have lla: "len < length a" using g2 len_mc lena by simp
    note aok = arc_ok[OF cur_mc]
    have aok1: "cur < length fstl" and aok2: "cur < length sndl" and aok3: "cur < length esl"
      and aok4: "cur < m \<Longrightarrow> cur < length col \<and> col ! cur = cost_list ! cur"
      and aokf: "fstl ! cur = fst_all ! cur" and aoks: "sndl ! cur = snd_all ! cur"
      and aok5: "fst_all ! cur < length \<pi>" and aok6: "snd_all ! cur < length \<pi>"
      using aok by auto
    note evr = evaluate_imp_rule[OF aok1 aok2 aok4 aok3 aok5 aok6 aokf aoks]
    obtain elig u g where ev: "evaluate esl \<pi> cur = (elig, u, g)"
      by (cases "evaluate esl \<pi> cur") auto
    have m1: "fuel - 1 < fuel" using g1 by simp
    have suclen_mc: "Suc len \<le> max_candidates" using g2 len_mc by simp
    have lena_upd: "max_candidates \<le> length (a[len := cur])" using lena by simp
    \<comment> \<open>Keep the wrap-around @{term cur1} and block-reset @{term bpos1} \<^emph>\<open>opaque\<close> (as defined
        constants), so the simplifier does not split their ifs and break the induction-hypothesis
        match; the ifs are folded into the program by \<open>cur1_def[symmetric]\<close> / \<open>bpos1_def[symmetric]\<close>.
        The IHs are unfolded past @{thm One_nat_def} so their \<open>fuel - 1\<close> matches the \<open>fuel - Suc 0\<close>
        the simplifier produces.  @{term best} stays schematic for the split entering-edge tuple.\<close>
    define cur1 where "cur1 = (if cur + 1 = mc then 0 else cur + 1)"
    define bpos1 where "bpos1 = (if bpos = 0 then block_size else bpos)"
    have cur1_mc: "cur1 < mc" unfolding cur1_def by (rule wrap_lt[OF mcpos cur_mc])
    note IH_elig = less.IH[OF m1 cur1_mc suclen_mc lena_upd]
    note IH_nelig = less.IH[OF m1 cur1_mc len_mc lena]
    have scu: "scan esl \<pi> mc fuel bpos cur a len best
                 = scan esl \<pi> mc (fuel - 1) (bpos1 - 1) cur1 (if elig then a[len := cur] else a)
                        (if elig then Suc len else len) (if elig then better best (cur, u, g) else best)"
      unfolding cur1_def bpos1_def by (subst scan.simps) (simp add: g1 g2 g3 ev Let_def)
    show ?thesis
      supply scan.simps[simp del]
      apply (subst scan_imp.simps)
      apply (simp only: if_not_P[OF g1] if_not_P[OF g2] if_not_P[OF g3]
                        cur1_def[symmetric] bpos1_def[symmetric])
      apply (sep_auto simp: ev lla lla[unfolded One_nat_def] Let_def scu
                       split: if_splits heap: evr IH_elig IH_nelig)
      apply (sep_auto simp: Let_def scu ev
                       heap: IH_elig[unfolded One_nat_def] IH_nelig[unfolded One_nat_def])+
      done
  qed
qed


subsection \<open>Layer (e): the entering-edge selector assembles the two scans\<close>

text \<open>The selector state relation: the fixed-capacity backing array, the block bookmark and the
      live-prefix pointer of the functional @{typ ns_sel} record are held by the array @{term sarr} and
      the two references @{term cref} / @{term lref}.\<close>
definition sel_assn_ns :: "ns_sel \<Rightarrow> ns_sel_imp \<Rightarrow> assn" where
  "sel_assn_ns sel s = (case s of (sarr, cref, lref) \<Rightarrow>
     sarr \<mapsto>\<^sub>a sel_arr sel * cref \<mapsto>\<^sub>r sel_cur sel * lref \<mapsto>\<^sub>r sel_len sel)"

text \<open>@{const ns_sel_select_imp} refines @{const sel_select_impl}: minor iteration over the cache
      (@{const scan_cache_imp}), and on failure a major block sweep (@{const scan_imp}), committing the
      pointers on a hit.  On @{term None} the cache has been rearranged (stale candidates pruned), so the
      store now represents \<^emph>\<open>some\<close> selector — exactly the existential the weakened ADT axiom demands.\<close>
lemma ns_sel_select_imp_rule:
  assumes inv: "sel_invar_impl sel" and mcpos: "0 < marc"
    and arc_ok: "\<And>e. e < marc \<Longrightarrow> e < length fstl \<and> e < length sndl \<and> e < length esl \<and>
        (e < m \<longrightarrow> e < length col \<and> col ! e = cost_list ! e) \<and> fstl ! e = fst_all ! e \<and> sndl ! e = snd_all ! e \<and> fst_all ! e < length \<pi> \<and> snd_all ! e < length \<pi>"
  shows "<sel_assn_ns sel (sarr, cref, lref) * es_arr \<mapsto>\<^sub>a esl * pt \<mapsto>\<^sub>a \<pi>
          * fst_arr \<mapsto>\<^sub>a fstl * snd_arr \<mapsto>\<^sub>a sndl * cost_arr \<mapsto>\<^sub>a col>
           ns_sel_select_imp m marc block_size min_candidates max_candidates fst_arr snd_arr cost_arr
                             (sarr, cref, lref) pt es_arr
         <\<lambda>res. es_arr \<mapsto>\<^sub>a esl * pt \<mapsto>\<^sub>a \<pi> * fst_arr \<mapsto>\<^sub>a fstl * snd_arr \<mapsto>\<^sub>a sndl * cost_arr \<mapsto>\<^sub>a col
            * (case sel_select_impl sel \<pi> esl of
                 None \<Rightarrow> (\<exists>\<^sub>A ss. sel_assn_ns ss (sarr, cref, lref)) * \<up>(res = None)
               | Some (e, in_U, \<gamma>, sel') \<Rightarrow>
                   sel_assn_ns sel' (sarr, cref, lref) * \<up>(res = Some (e, in_U, \<gamma>)))>"
proof -
  from inv have larr: "length (sel_arr sel) = max_candidates"
    and lenmax: "sel_len sel \<le> max_candidates"
    and curlt: "0 < marc \<longrightarrow> sel_cur sel < marc"
    and rng: "set (take (sel_len sel) (sel_arr sel)) \<subseteq> {0..<marc}"
    by (auto simp: sel_invar_impl_def)
  have curm: "sel_cur sel < marc" using curlt mcpos by simp
  have lenl: "sel_len sel \<le> length (sel_arr sel)" using lenmax larr by simp
  \<comment> \<open>Each cached candidate is a genuine arc \<open>< marc\<close>, so the arc-validity invariant applies.\<close>
  have eok_cache: "\<And>e. e \<in> set (take (sel_len sel) (sel_arr sel)) \<Longrightarrow>
      e < length fstl \<and> e < length sndl \<and> e < length esl \<and>
      (e < m \<longrightarrow> e < length col \<and> col ! e = cost_list ! e) \<and> fstl ! e = fst_all ! e \<and> sndl ! e = snd_all ! e \<and> fst_all ! e < length \<pi> \<and> snd_all ! e < length \<pi>"
  proof -
    fix e assume "e \<in> set (take (sel_len sel) (sel_arr sel))"
    hence "e < marc" using rng by auto
    thus "e < length fstl \<and> e < length sndl \<and> e < length esl \<and>
      (e < m \<longrightarrow> e < length col \<and> col ! e = cost_list ! e) \<and> fstl ! e = fst_all ! e \<and> sndl ! e = snd_all ! e \<and> fst_all ! e < length \<pi> \<and> snd_all ! e < length \<pi>"
      by (rule arc_ok)
  qed
  note scr = scan_cache_imp_rule[OF le0 lenl eok_cache]
  obtain a1 len1 b1 where sc: "scan_cache esl \<pi> 0 (sel_arr sel) (sel_len sel) no_best = (a1, len1, b1)"
    by (cases "scan_cache esl \<pi> 0 (sel_arr sel) (sel_len sel) no_best") auto
  \<comment> \<open>@{const scan_cache} preserves the array length and shrinks the pointer, so the major sweep's
      preconditions (\<open>len1 \<le> max_candidates\<close>, \<open>max_candidates \<le> length a1\<close>) hold.\<close>
  have sc_spec: "length a1 = length (sel_arr sel) \<and> len1 \<le> sel_len sel"
    using scan_cache_spec[OF le0 lenl bok_no_best, of esl \<pi>] sc by simp
  have a1_max: "max_candidates \<le> length a1" using sc_spec larr by simp
  have len1_max: "len1 \<le> max_candidates" using sc_spec lenmax by simp
  note scim = scan_imp_rule[OF arc_ok mcpos curm len1_max a1_max]
  show ?thesis
    supply scan_cache.simps[simp del] scan.simps[simp del]
    unfolding ns_sel_select_imp_def sel_assn_ns_def sel_select_impl_def
    apply (sep_auto simp: sc split: prod.splits if_splits heap: scr scim)
    \<comment> \<open>The @{term None} / @{term None} case: the store now holds the pruned cache @{term aa}, which is
        the selector \<open>sel\<lparr>sel_arr := aa\<rparr>\<close> — the existential witness.\<close>
    subgoal premises prems for x1 aa ab ac ad ae af ba x1a ag ah ai bb found1 a b found2
      apply (rule entailsD[OF _ prems(7)])
      apply (rule ent_ex_postI[where x = "sel\<lparr>sel_arr := aa\<rparr>"])
      apply sep_auto
      done
    done
qed


subsection \<open>Layer (e): the network-simplex loop refines the functional loop\<close>

text \<open>The five array-backed stores of the loop state — flow, potentials, parent edge, parent direction,
      edge tags — are plain \<open>\<mapsto>\<^sub>a\<close> points-to assertions (the functional value \<^emph>\<open>is\<close> the array
      contents; unlike the acyclifier there is no over-allocated remainder here, since the loop operates
      on the full augmented edge / vertex ranges).  The spanning tree uses @{const ndtree_assn}, the
      selector @{const sel_assn_ns}.\<close>
definition flow_assn_ns :: "'n list \<Rightarrow> 'n array \<Rightarrow> assn" where
  "flow_assn_ns fl fh = fh \<mapsto>\<^sub>a fl"
definition pot_assn_ns :: "(mtag \<times> 'n) list \<Rightarrow> (mtag \<times> 'n) array \<Rightarrow> assn" where
  "pot_assn_ns pl ph = ph \<mapsto>\<^sub>a pl"
definition parent_assn_ns :: "nat list \<Rightarrow> nat array \<Rightarrow> assn" where
  "parent_assn_ns pe ph = ph \<mapsto>\<^sub>a pe"
definition dir_assn_ns :: "bool list \<Rightarrow> bool array \<Rightarrow> assn" where
  "dir_assn_ns d dh = dh \<mapsto>\<^sub>a d"
definition es_assn_ns :: "edge_tag list \<Rightarrow> edge_tag array \<Rightarrow> assn" where
  "es_assn_ns el eh = eh \<mapsto>\<^sub>a el"

text \<open>Re-establish the functional network-simplex interpretation at the augmented graph (the \<open>NS\<close> of
      \<open>Network_Simplex_Initial_Basis_Selector\<close> is local to its own context and not inherited here); the
      thirty-odd structural / arborescence / potential-value axioms are discharged exactly as there.\<close>
interpretation NS: network_simplex
  where fst = "\<lambda> e. if e < m+Kart then fst_all ! e else Product_Type.fst (prod_decode (e - (m+Kart)))"
    and snd = "\<lambda> e. if e < m+Kart then snd_all ! e else Product_Type.snd (prod_decode (e - (m+Kart)))"
    and create_edge = "\<lambda> u v. (m+Kart) + prod_encode (u, v)"
    and \<E> = "{0..<m+Kart}"
    and \<u> = "\<lambda> e. if e < m+Kart then (if cap_all ! e = - 1 then \<infinity> else ereal (h (cap_all ! e))) else \<infinity>"
    and \<c> = "\<lambda> e. cost_all ! e"
    and r = vcount
    and shift_pot = shift_pot_impl
    and arborescense_invar = "arb_invar vcount Varb"
    and abstract_arborescense = abstract_arb
    and get_path_pair = get_path_pair_impl
    and swap_edge = swap_edge_impl
    and flow_invar = "\<lambda>xs. \<forall>k\<in>{0..<m+Kart}. k < length xs" and flow_upd = list_update and flow_lookup = nth
    and pot_invar = "\<lambda>xs. \<forall>v\<in>Varb. v < length xs" and pot_upd = list_update and pot_lookup = nth
    and parent_invar = "\<lambda>xs. \<forall>v\<in>Varb - {vcount}. v < length xs" and parent_upd = list_update and parent_lookup = nth
    and dir_invar = "\<lambda>xs. \<forall>v\<in>Varb - {vcount}. v < length xs" and dir_upd = list_update and dir_lookup = nth
    and es_invar = "\<lambda>xs. \<forall>k\<in>{0..<m+Kart}. k < length xs" and es_upd = list_update and es_lookup = nth
    and sel_invar = sel_invar_impl and sel_select = sel_select_impl
    and b = "\<lambda> v. h (b_lookup v)"
    and cap = "\<lambda> e. cap_all ! e"
    and pot_value_invar = "\<lambda> p. good_pot_val_c p \<and> pv_invar p"
    and pot_value_abstract = "pval_abstract bigM"
    and pot_value_plus = pval_plus
    and pot_value_minus = pval_minus
    and rcost_invar = rc_invar
    and rcost_abstract = "pval_abstract bigM"
    and fst_exec = "\<lambda> e. fst_all ! e"
    and snd_exec = "\<lambda> e. snd_all ! e"
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
  subgoal by (auto simp: NSg_verts_Varb nth_fun_list_update)
  subgoal by (auto simp: NSg_verts_Varb nth_fun_list_update)
  subgoal by (auto simp: NSg_verts_Varb nth_fun_list_update)
  subgoal by (auto simp: NSg_verts_Varb nth_fun_list_update)
  subgoal by (auto simp: NSg_verts_Varb nth_fun_list_update)
  subgoal by (auto simp: NSg_verts_Varb nth_fun_list_update)
  subgoal by (auto simp: NSg_verts_Varb nth_fun_list_update)
  subgoal by (auto simp: NSg_verts_Varb nth_fun_list_update)
  subgoal by (auto simp: NSg_verts_Varb nth_fun_list_update)
  subgoal by (auto simp: NSg_verts_Varb nth_fun_list_update)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal using cap_all_nonneg by auto
  subgoal premises p for sel \<pi> es e in_U \<gamma> sel'
  proof -
    have ok: "pot_ok \<pi>" using p(3)[simplified NSg_verts_Varb] p(4) by (simp add: pot_ok_def)
    show ?thesis using sel_select_impl_Some_final[OF p(1) ok p(6)] by (auto simp: rcabs_def marc_def)
  qed
  subgoal premises p for sel \<pi> es
  proof -
    have ok: "pot_ok \<pi>" using p(3)[simplified NSg_verts_Varb] p(4) by (simp add: pot_ok_def)
    show ?thesis using sel_select_impl_None_final[OF p(1) ok p(6)] by (auto simp: rcabs_def marc_def)
  qed
  subgoal premises p for p g
  proof -
    have pv: "pv_invar p" and gc: "good_pot_val_c p" using p(1) by auto
    have rc: "rc_invar g" using p(2) .
    have cert: "\<exists>A D. A \<subseteq> {0..<m+Kart} \<and> D \<subseteq> {0..<m+Kart} \<and> card {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount} \<le> 1 \<and> pval_abstract bigM p + pval_abstract bigM g = sum ((!) cost_all) A - sum ((!) cost_all) D"
    proof -
      from p(3) obtain A D where AD: "A \<subseteq> {0..<m+Kart}" "D \<subseteq> {0..<m+Kart}"
        "card {e \<in> A \<union> D. (if e < m+Kart then fst_all ! e else fst (prod_decode (e - (m+Kart)))) = vcount \<or> (if e < m+Kart then snd_all ! e else snd (prod_decode (e - (m+Kart)))) = vcount} \<le> 1"
        "pval_abstract bigM p + pval_abstract bigM g = sum ((!) cost_all) A - sum ((!) cost_all) D" by (elim exE conjE)
      have SE: "{e \<in> A \<union> D. (if e < m+Kart then fst_all ! e else fst (prod_decode (e - (m+Kart)))) = vcount \<or> (if e < m+Kart then snd_all ! e else snd (prod_decode (e - (m+Kart)))) = vcount} = {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount}"
        using AD(1,2) by auto
      have "card {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount} \<le> 1" using AD(3) SE by simp
      thus ?thesis using AD(1,2,4) by (intro exI[of _ A] exI[of _ D]) auto
    qed
    show ?thesis using pot_plus_faithful[OF pv rc cert] good_pot_val_c_plus[OF pv rc cert] by simp
  qed
  subgoal premises p for p g
  proof -
    have pv: "pv_invar p" and gc: "good_pot_val_c p" using p(1) by auto
    have rc: "rc_invar g" using p(2) .
    have cert: "\<exists>A D. A \<subseteq> {0..<m+Kart} \<and> D \<subseteq> {0..<m+Kart} \<and> card {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount} \<le> 1 \<and> pval_abstract bigM p - pval_abstract bigM g = sum ((!) cost_all) A - sum ((!) cost_all) D"
    proof -
      from p(3) obtain A D where AD: "A \<subseteq> {0..<m+Kart}" "D \<subseteq> {0..<m+Kart}"
        "card {e \<in> A \<union> D. (if e < m+Kart then fst_all ! e else fst (prod_decode (e - (m+Kart)))) = vcount \<or> (if e < m+Kart then snd_all ! e else snd (prod_decode (e - (m+Kart)))) = vcount} \<le> 1"
        "pval_abstract bigM p - pval_abstract bigM g = sum ((!) cost_all) A - sum ((!) cost_all) D" by (elim exE conjE)
      have SE: "{e \<in> A \<union> D. (if e < m+Kart then fst_all ! e else fst (prod_decode (e - (m+Kart)))) = vcount \<or> (if e < m+Kart then snd_all ! e else snd (prod_decode (e - (m+Kart)))) = vcount} = {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount}"
        using AD(1,2) by auto
      have "card {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount} \<le> 1" using AD(3) SE by simp
      thus ?thesis using AD(1,2,4) by (intro exI[of _ A] exI[of _ D]) auto
    qed
    show ?thesis using pot_minus_faithful[OF pv rc cert] good_pot_val_c_minus[OF pv rc cert] by simp
  qed
  subgoal premises p by (rule shift_pot_impl_spec[OF p(1) p(2)[simplified NSg_verts_Varb]])
  done

text \<open>Reading one array out of a larger separation-logic frame, without the frame-inference blow-up
      @{method sep_auto} suffers when several concrete @{term \<open>(\<mapsto>\<^sub>a)\<close>} conjuncts are present.\<close>
lemma arr_read_framed:
  fixes F :: assn
  assumes "i < length xs"
  shows "<a \<mapsto>\<^sub>a xs * F> Array.nth a i <\<lambda>r. a \<mapsto>\<^sub>a xs * F * \<up>(r = xs ! i)>"
  by (rule ht_cons_post[OF ht_frame[OF nth_rule]]) sep_auto

text \<open>The whole network-simplex loop, run on the materialised imperative state, refines the functional
      @{term \<open>NS.ns_loop\<close>}.  It instantiates @{locale network_simplex_impl_refine} at the concrete
      per-store operations (array reads / writes and the four proven tree / selector refinement rules),
      re-using the theory-level @{term NS} interpretation for the functional half; @{term ns_loop_prog}
      is definitionally \<open>nsR.ns_loop_imp\<close>.  The materialisation length bounds are hypotheses,
      discharged later by the tree builder.\<close>
lemma ns_loop_prog_rule:
  fixes fst_arr snd_arr :: "nat array" and cap_arr cost_arr :: "'n array"
    and s :: "(_, _, _, _, _, _, _) network_simplex_state"
    and si :: "(_, _, _, _, _, _, _, _) ns_impl_state"
  assumes lenf: "marc \<le> length fst_all" and lens: "marc \<le> length snd_all"
    and lenc: "marc \<le> length cap_all" and lenco: "m \<le> length cost_list"
    and lenfl: "marc \<le> length fstl" and lensl: "marc \<le> length sndl" and lencl: "marc \<le> length capl"
    and fstok: "\<And>e. e < marc \<Longrightarrow> fstl ! e = fst_all ! e" and sndok: "\<And>e. e < marc \<Longrightarrow> sndl ! e = snd_all ! e"
    and capok: "\<And>e. e < marc \<Longrightarrow> capl ! e = cap_all ! e"
    and inv: "NS.ns_invar s"
  shows
   "<(cap_arr \<mapsto>\<^sub>a capl * cost_arr \<mapsto>\<^sub>a cost_list * fst_arr \<mapsto>\<^sub>a fstl * snd_arr \<mapsto>\<^sub>a sndl) *
     flow_assn_ns   (network_simplex_state.current_flow s)  (ns_impl_state.iflow si)   *
     pot_assn_ns    (network_simplex_state.potentials s)    (ns_impl_state.ipot si)     *
     ndtree_assn Varb (network_simplex_state.spanning_tree s) (ns_impl_state.itree si)  *
     parent_assn_ns (network_simplex_state.parent_edge s)   (ns_impl_state.iparent si)  *
     dir_assn_ns    (network_simplex_state.edge_dir s)      (ns_impl_state.idir si)     *
     es_assn_ns     (network_simplex_state.edge_state s)    (ns_impl_state.iestate si)  *
     sel_assn_ns    (network_simplex_state.edge_sel s)      (ns_impl_state.isel si)     *
     (\<exists>\<^sub>A l1 l2. ns_impl_state.ipath1 si \<mapsto>\<^sub>a l1 * ns_impl_state.ipath2 si \<mapsto>\<^sub>a l2 *
        \<up>(card Varb - 1 \<le> length l1 \<and> card Varb - 1 \<le> length l2))>
      ns_loop_prog vcount m marc block_size min_candidates max_candidates
                   fst_arr snd_arr cost_arr cap_arr si
    <\<lambda>res. (cap_arr \<mapsto>\<^sub>a capl * cost_arr \<mapsto>\<^sub>a cost_list * fst_arr \<mapsto>\<^sub>a fstl * snd_arr \<mapsto>\<^sub>a sndl) *
     flow_assn_ns   (network_simplex_state.current_flow (NS.ns_loop s))  (ns_impl_state.iflow si)   *
     pot_assn_ns    (network_simplex_state.potentials (NS.ns_loop s))    (ns_impl_state.ipot si)     *
     ndtree_assn Varb (network_simplex_state.spanning_tree (NS.ns_loop s)) (ns_impl_state.itree si)  *
     parent_assn_ns (network_simplex_state.parent_edge (NS.ns_loop s))   (ns_impl_state.iparent si)  *
     dir_assn_ns    (network_simplex_state.edge_dir (NS.ns_loop s))      (ns_impl_state.idir si)     *
     es_assn_ns     (network_simplex_state.edge_state (NS.ns_loop s))    (ns_impl_state.iestate si)  *
     (\<exists>\<^sub>A ss. sel_assn_ns ss (ns_impl_state.isel si)) *
     (\<exists>\<^sub>A l1 l2. ns_impl_state.ipath1 si \<mapsto>\<^sub>a l1 * ns_impl_state.ipath2 si \<mapsto>\<^sub>a l2 *
        \<up>(card Varb - 1 \<le> length l1 \<and> card Varb - 1 \<le> length l2)) *
     \<up>(res = network_simplex_state.return (NS.ns_loop s))>"
proof -
  interpret nsR: network_simplex_impl_refine
      where fst = "\<lambda> e. if e < m+Kart then fst_all ! e else Product_Type.fst (prod_decode (e - (m+Kart)))"
        and snd = "\<lambda> e. if e < m+Kart then snd_all ! e else Product_Type.snd (prod_decode (e - (m+Kart)))"
        and create_edge = "\<lambda> u v. (m+Kart) + prod_encode (u, v)"
        and \<E> = "{0..<m+Kart}"
        and \<u> = "\<lambda> e. if e < m+Kart then (if cap_all ! e = - 1 then \<infinity> else ereal (h (cap_all ! e))) else \<infinity>"
        and \<c> = "\<lambda> e. cost_all ! e"
        and r = vcount
        and shift_pot = shift_pot_impl
        and arborescense_invar = "arb_invar vcount Varb"
        and abstract_arborescense = abstract_arb
        and get_path_pair = get_path_pair_impl
        and swap_edge = swap_edge_impl
        and flow_invar = "\<lambda>xs. \<forall>k\<in>{0..<m+Kart}. k < length xs" and flow_upd = list_update and flow_lookup = nth
        and pot_invar = "\<lambda>xs. \<forall>v\<in>Varb. v < length xs" and pot_upd = list_update and pot_lookup = nth
        and parent_invar = "\<lambda>xs. \<forall>v\<in>Varb - {vcount}. v < length xs" and parent_upd = list_update and parent_lookup = nth
        and dir_invar = "\<lambda>xs. \<forall>v\<in>Varb - {vcount}. v < length xs" and dir_upd = list_update and dir_lookup = nth
        and es_invar = "\<lambda>xs. \<forall>k\<in>{0..<m+Kart}. k < length xs" and es_upd = list_update and es_lookup = nth
        and sel_invar = sel_invar_impl and sel_select = sel_select_impl
        and b = "\<lambda> v. h (b_lookup v)"
        and cap = "\<lambda> e. cap_all ! e"
        and pot_value_invar = "\<lambda> p. good_pot_val_c p \<and> pv_invar p"
        and pot_value_abstract = "pval_abstract bigM"
        and pot_value_plus = pval_plus
        and pot_value_minus = pval_minus
        and rcost_invar = rc_invar
        and rcost_abstract = "pval_abstract bigM"
        and fst_exec = "\<lambda> e. fst_all ! e"
        and snd_exec = "\<lambda> e. snd_all ! e"
        and flow_lookup_imp = Array.nth and flow_upd_imp = arr_upd
        and parent_lookup_imp = Array.nth and parent_upd_imp = arr_upd
        and dir_lookup_imp = Array.nth and dir_upd_imp = arr_upd
        and es_lookup_imp = Array.nth and es_upd_imp = arr_upd
        and sel_select_imp = "ns_sel_select_imp m marc block_size min_candidates max_candidates fst_arr snd_arr cost_arr"
        and shift_pot_imp = ns_shift_pot_imp and get_path_pair_imp = ns_get_path_pair_imp and swap_edge_imp = ns_swap_edge_imp
        and cap_imp = "Array.nth cap_arr" and fst_exec_imp = "Array.nth fst_arr" and snd_exec_imp = "Array.nth snd_arr"
        and flow_assn = flow_assn_ns and pot_assn = pot_assn_ns and tree_assn = "ndtree_assn Varb"
        and parent_assn = parent_assn_ns and dir_assn = dir_assn_ns and es_assn = es_assn_ns and sel_assn = sel_assn_ns
        and rd = "cap_arr \<mapsto>\<^sub>a capl * cost_arr \<mapsto>\<^sub>a cost_list * fst_arr \<mapsto>\<^sub>a fstl * snd_arr \<mapsto>\<^sub>a sndl"
    apply intro_locales
    apply (rule network_simplex_impl_refine_axioms.intro)
    apply (unfold NSg_verts_Varb flow_assn_ns_def es_assn_ns_def parent_assn_ns_def dir_assn_ns_def pot_assn_ns_def)
    apply (sep_auto heap: ns_shift_pot_imp_rule ns_get_path_pair_imp_rule ns_swap_edge_imp_rule)
    defer 1
      apply (rule ns_get_path_pair_imp_rule; assumption)
     apply (rule ns_swap_edge_imp_rule; assumption)
    subgoal premises pr for e
      proof -
        have emc: "e < marc" using pr by (simp add: marc_def)
        have lt: "e < length capl" using emc lencl by simp
        have ce: "capl ! e = cap_all ! e" using capok[OF emc] .
        show ?thesis
          apply (rule ht_cons_pre[OF _ ht_cons_post[OF arr_read_framed[OF lt,
                   where a=cap_arr and F="cost_arr \<mapsto>\<^sub>a cost_list * fst_arr \<mapsto>\<^sub>a fstl * snd_arr \<mapsto>\<^sub>a sndl"]]])
          apply (sep_auto simp: ce)
          done
      qed
    subgoal premises pr for e
      proof -
        have emc: "e < marc" using pr by (simp add: marc_def)
        have lt: "e < length fstl" using emc lenfl by simp
        have fe: "fstl ! e = fst_all ! e" using fstok[OF emc] .
        show ?thesis
          apply (rule ht_cons_pre[OF _ ht_cons_post[OF arr_read_framed[OF lt,
                   where a=fst_arr and F="cap_arr \<mapsto>\<^sub>a capl * cost_arr \<mapsto>\<^sub>a cost_list * snd_arr \<mapsto>\<^sub>a sndl"]]])
          apply (sep_auto simp: fe)
          done
      qed
    subgoal premises pr for e
      proof -
        have emc: "e < marc" using pr by (simp add: marc_def)
        have lt: "e < length sndl" using emc lensl by simp
        have se: "sndl ! e = snd_all ! e" using sndok[OF emc] .
        show ?thesis
          apply (rule ht_cons_pre[OF _ ht_cons_post[OF arr_read_framed[OF lt,
                   where a=snd_arr and F="cap_arr \<mapsto>\<^sub>a capl * cost_arr \<mapsto>\<^sub>a cost_list * fst_arr \<mapsto>\<^sub>a fstl"]]])
          apply (sep_auto simp: se)
          done
      qed
    subgoal premises pr for Sel \<pi> Es a aa b poth esh ab ba
      proof -
        have mcpos: "0 < marc" using num_edges_gtr_0 by (simp add: marc_def)
        have arc_ok: "\<And>e'. e' < marc \<Longrightarrow> e' < length fstl \<and> e' < length sndl \<and> e' < length Es \<and>
            (e' < m \<longrightarrow> e' < length cost_list \<and> cost_list ! e' = cost_list ! e') \<and>
            fstl ! e' = fst_all ! e' \<and> sndl ! e' = snd_all ! e' \<and>
            fst_all ! e' < length \<pi> \<and> snd_all ! e' < length \<pi>"
        proof -
          fix e' assume e': "e' < marc"
          from e' lenfl lensl have a1: "e' < length fstl" "e' < length sndl" by auto
          from e' pr(3) have a2: "e' < length Es" by (auto simp: marc_def)
          from lenco have a3: "e' < m \<longrightarrow> e' < length cost_list" by auto
          from fstok[OF e'] sndok[OF e'] have af: "fstl ! e' = fst_all ! e'" "sndl ! e' = snd_all ! e'" by auto
          from endpt_in_Varb[OF e'] pr(2) have a4: "fst_all ! e' < length \<pi>" "snd_all ! e' < length \<pi>" by auto
          from a1 a2 a3 af a4 show "e' < length fstl \<and> e' < length sndl \<and> e' < length Es \<and>
              (e' < m \<longrightarrow> e' < length cost_list \<and> cost_list ! e' = cost_list ! e') \<and>
              fstl ! e' = fst_all ! e' \<and> sndl ! e' = snd_all ! e' \<and>
              fst_all ! e' < length \<pi> \<and> snd_all ! e' < length \<pi>" by blast
        qed
        have triple: "<sel_assn_ns Sel (a, aa, b) * poth \<mapsto>\<^sub>a \<pi> * esh \<mapsto>\<^sub>a Es * cap_arr \<mapsto>\<^sub>a capl *
                        cost_arr \<mapsto>\<^sub>a cost_list * fst_arr \<mapsto>\<^sub>a fstl * snd_arr \<mapsto>\<^sub>a sndl>
            ns_sel_select_imp m marc block_size min_candidates max_candidates fst_arr snd_arr cost_arr (a, aa, b) poth esh
          <\<lambda>res. poth \<mapsto>\<^sub>a \<pi> * esh \<mapsto>\<^sub>a Es * cap_arr \<mapsto>\<^sub>a capl * cost_arr \<mapsto>\<^sub>a cost_list *
                 fst_arr \<mapsto>\<^sub>a fstl * snd_arr \<mapsto>\<^sub>a sndl *
                 (case sel_select_impl Sel \<pi> Es of None \<Rightarrow> (\<exists>\<^sub>A ss. sel_assn_ns ss (a, aa, b)) * \<up>(res = None)
                   | Some (e, in_U, \<gamma>, sel') \<Rightarrow> sel_assn_ns sel' (a, aa, b) * \<up>(res = Some (e, in_U, \<gamma>)))>"
          by (sep_auto heap: ns_sel_select_imp_rule[OF pr(1) mcpos arc_ok])
        show ?thesis using hoare_triple_wlpD[OF triple pr(4)] by (simp only: ex_assn_move_out)
      qed
    done
  show ?thesis
    using nsR.ns_loop_imp_correct[OF inv]
    by (simp only: ns_loop_prog_def nsR.ns_rel_def nsR.ns_rel_weak_def NSg_verts_Varb)
qed

text \<open>Foundational facts for the capstone: the root name @{term vcount} is above every input vertex,
      and the freshly built spanning tree is fully sized (all nine per-vertex arrays have length
      @{term \<open>Suc vcount\<close>}), which the tree / potential / parent / dir bridges below all need.\<close>
lemma n_less_vcount: "n < vcount"
  unfolding vcount_def vs_list_def by (induction n) auto

lemma vs_list_lt_vcount: "\<forall>w\<in>set vs_list. w < vcount"
  using n_less_vcount by (auto simp: set_vs_list)

lemma bt_sized: "dfs_sized (build_tree acyc_flow)"
proof -
  have wsd1: "dfs_wf (phase1 acyc_flow dfs_init) \<and> dfs_sized (phase1 acyc_flow dfs_init) \<and> dref_inv (phase1 acyc_flow dfs_init)"
    using fold_phase1_step_wsd[OF dfs_wf_dfs_init dfs_init_sized dref_inv_dfs_init vs_list_lt_vcount] by (simp add: phase1_def)
  have szp2: "dfs_sized (phase2 acyc_flow (phase1 acyc_flow dfs_init))"
    using fold_phase2_step_wsd[OF conjunct1[OF wsd1] conjunct1[OF conjunct2[OF wsd1]] conjunct2[OF conjunct2[OF wsd1]] vs_list_lt_vcount] by (simp add: phase2_def)
  show ?thesis using szp2 by (simp add: build_tree_def dfs_sized_def Let_def)
qed

text \<open>The domain/range structural conditions of @{const Sarb} that the @{const ndtree_assn} tree bridge
      needs, extracted from @{thm arb_invar_Sarb}: every parent / thread / reverse-thread entry, and every
      last-successor, stays inside the vertex set @{term Varb}.  The @{term \<open>ran (prnt Sarb) \<subseteq> Varb\<close>} case
      goes through the parent-edge set's @{const dVs} (= @{term Varb} by @{thm dVs_Sprnt}); its membership
      is hand-written (@{method auto} / @{method blast} diverge on the shadowed-binder comprehension).\<close>
lemma Sarb_struct:
  shows Sarb_prnt_dom: "dom (prnt Sarb) \<subseteq> Varb" and Sarb_prnt_ran: "ran (prnt Sarb) \<subseteq> Varb"
    and Sarb_thrd_dom: "dom (thrd Sarb) \<subseteq> Varb" and Sarb_rvth_dom: "dom (rvth Sarb) \<subseteq> Varb"
    and Sarb_thrd_ran: "ran (thrd Sarb) \<subseteq> Varb" and Sarb_rvth_ran: "ran (rvth Sarb) \<subseteq> Varb"
    and Sarb_lsuc_in: "\<forall>v\<in>Varb. lsuc Sarb v \<in> Varb"
proof -
  note ai = arb_invar_Sarb[unfolded arb_invar_def]
  from ai have raiP: "rooted_arborescense_invar vcount Varb (prnt Sarb)"
    and dtE: "dom (thrd Sarb) = Varb - {lsuc Sarb vcount}"
    and drE: "dom (rvth Sarb) = Varb - {vcount}"
    and bijE: "\<forall>v v'. (thrd Sarb v = Some v') = (rvth Sarb v' = Some v)"
    and linE: "\<forall>v\<in>Varb. lsuc Sarb v \<in> Varb" by blast+
  from raiP have dpE: "dom (prnt Sarb) = Varb - {vcount}"
    and dvsE: "dVs {(y,x) |x y. Some x = prnt Sarb y} = Varb"
    by (auto simp: rooted_arborescense_invar_def)
  show "dom (prnt Sarb) \<subseteq> Varb" using dpE by auto
  show "ran (prnt Sarb) \<subseteq> Varb"
  proof (rule subsetI)
    fix z assume "z \<in> ran (prnt Sarb)"
    then obtain w where w: "prnt Sarb w = Some z" by (auto simp: ran_def)
    have mem: "(w, z) \<in> {(y,x) |x y. Some x = prnt Sarb y}"
      apply (rule CollectI) apply (rule exI[of _ z]) apply (rule exI[of _ w]) apply (simp add: w) done
    have "z \<in> snd ` {(y,x) |x y. Some x = prnt Sarb y}" using mem by (rule rev_image_eqI) simp
    hence "z \<in> dVs {(y,x) |x y. Some x = prnt Sarb y}" by (simp add: dVs_eq)
    thus "z \<in> Varb" using dvsE by simp
  qed
  show "dom (thrd Sarb) \<subseteq> Varb" using dtE by auto
  show "dom (rvth Sarb) \<subseteq> Varb" using drE by auto
  show "ran (thrd Sarb) \<subseteq> Varb" using bijE drE by (fastforce simp: ran_def dom_def)
  show "ran (rvth Sarb) \<subseteq> Varb" using bijE dtE by (fastforce simp: ran_def dom_def)
  show "\<forall>v\<in>Varb. lsuc Sarb v \<in> Varb" using linE .
qed

text \<open>The root vertex @{term vcount} is never discovered by the DFS traversal, so its parent slot
      @{term \<open>ds_prnt s ! vcount\<close>} is preserved by every state transformer and stays at its
      @{const dfs_init} value @{term 0}.  This is the parent-map root clause the ndtree bridge
      consumes.  The single-frame steps @{const bd_upd1} / @{const bd_upd2} only ever discover a
      vertex @{term \<open>w < vcount\<close>} (via @{thm Hout_valid} / @{thm Hin_valid}), and @{const bd_upd3}
      (@{const dfs_finish}) touches no parent slot; @{const otc_pre} writes the parent slot of a
      vertex @{term \<open>c::nat\<close>} with @{term \<open>c < vcount\<close>}, never the root slot.\<close>

lemma bd_upd1_prnt_vcount: "\<And>fl s. dfs_wf s \<Longrightarrow> bd_call1_conds fl s \<Longrightarrow> ds_prnt (bd_upd1 fl s) ! vcount = ds_prnt s ! vcount"
proof -
  fix fl s assume wf: "dfs_wf s" and c: "bd_call1_conds fl s"
  from c obtain v oc ic rest where stk: "ds_stk s = (v,oc,ic) # rest" and oclt: "oc < free_out_hi fl ! v"
    by (auto simp: bd_call1_conds_def split: list.splits prod.splits)
  from wf stk have vlt: "v < vcount" and olo: "out_lo ! v \<le> oc" by (auto simp: dfs_wf_def)
  let ?e = "free_out_edges fl ! oc" let ?w = "snd_list ! ?e"
  have wvc: "?w < vcount" using Hout_valid[OF vlt olo oclt] .
  have upd: "bd_upd1 fl s = (if ds_seen s ! ?w then s\<lparr>ds_stk := (v, Suc oc, ic) # rest\<rparr> else dfs_discover (s\<lparr>ds_stk := (v, Suc oc, ic) # rest\<rparr>) v ?w ?e)"
    using stk by (simp add: bd_upd1_def Let_def)
  show "ds_prnt (bd_upd1 fl s) ! vcount = ds_prnt s ! vcount"
  proof (cases "ds_seen s ! ?w")
    case True thus ?thesis using upd by simp
  next
    case False
    have "vcount \<noteq> ?w" using wvc by simp
    thus ?thesis using upd False by (simp add: dfs_discover_def Let_def nth_list_update_neq)
  qed
qed

lemma bd_upd2_prnt_vcount: "\<And>fl s. dfs_wf s \<Longrightarrow> bd_call2_conds fl s \<Longrightarrow> ds_prnt (bd_upd2 fl s) ! vcount = ds_prnt s ! vcount"
proof -
  fix fl s assume wf: "dfs_wf s" and c: "bd_call2_conds fl s"
  from c obtain v oc ic rest where stk: "ds_stk s = (v,oc,ic) # rest" and iclt: "ic < free_in_hi fl ! v"
    by (auto simp: bd_call2_conds_def split: list.splits prod.splits)
  from wf stk have vlt: "v < vcount" and ilo: "in_lo ! v \<le> ic" by (auto simp: dfs_wf_def)
  let ?e = "free_in_edges fl ! ic" let ?w = "fst_list ! ?e"
  have wvc: "?w < vcount" using Hin_valid[OF vlt ilo iclt] .
  have upd: "bd_upd2 fl s = (if ds_seen s ! ?w then s\<lparr>ds_stk := (v, oc, Suc ic) # rest\<rparr> else dfs_discover (s\<lparr>ds_stk := (v, oc, Suc ic) # rest\<rparr>) v ?w ?e)"
    using stk by (simp add: bd_upd2_def Let_def)
  show "ds_prnt (bd_upd2 fl s) ! vcount = ds_prnt s ! vcount"
  proof (cases "ds_seen s ! ?w")
    case True thus ?thesis using upd by simp
  next
    case False
    have "vcount \<noteq> ?w" using wvc by simp
    thus ?thesis using upd False by (simp add: dfs_discover_def Let_def nth_list_update_neq)
  qed
qed

lemma bd_upd3_prnt_vcount: "\<And>s. ds_stk s \<noteq> [] \<Longrightarrow> ds_prnt (bd_upd3 s) ! vcount = ds_prnt s ! vcount"
  by (auto simp: bd_upd3_def dfs_finish_def Let_def split: list.splits prod.splits)

lemma build_dfs_prnt_vcount: "\<And>fl s. build_dfs_dom (fl, s) \<Longrightarrow> dfs_inv fl s \<Longrightarrow> ds_prnt (build_dfs fl s) ! vcount = ds_prnt s ! vcount"
proof -
  fix fl s assume dom: "build_dfs_dom (fl, s)" and inv0: "dfs_inv fl s"
  have "dfs_inv fl s \<longrightarrow> ds_prnt (build_dfs fl s) ! vcount = ds_prnt s ! vcount"
  proof (induct rule: bd_induct[OF dom])
    case IH: (1 fl s)
    show ?case
    proof (intro impI)
      assume inv: "dfs_inv fl s"
      have wf: "dfs_wf s" using inv by (simp add: dfs_inv_def)
      show "ds_prnt (build_dfs fl s) ! vcount = ds_prnt s ! vcount"
      proof (rule bd_cases[where fl = fl and s = s])
        assume c: "bd_call1_conds fl s"
        have fr: "ds_prnt (bd_upd1 fl s) ! vcount = ds_prnt s ! vcount" by (rule bd_upd1_prnt_vcount[OF wf c])
        have "build_dfs fl s = build_dfs fl (bd_upd1 fl s)" using IH(1) c by (rule bd_simps(1))
        thus ?thesis using IH(2)[OF c] bd_upd1_inv[OF inv c] fr by simp
      next
        assume c: "bd_call2_conds fl s"
        have fr: "ds_prnt (bd_upd2 fl s) ! vcount = ds_prnt s ! vcount" by (rule bd_upd2_prnt_vcount[OF wf c])
        have "build_dfs fl s = build_dfs fl (bd_upd2 fl s)" using IH(1) c by (rule bd_simps(2))
        thus ?thesis using IH(3)[OF c] bd_upd2_inv[OF inv c] fr by simp
      next
        assume c: "bd_call3_conds fl s"
        have ne: "ds_stk s \<noteq> []" using c by (auto simp: bd_call3_conds_def split: list.splits prod.splits)
        have fr: "ds_prnt (bd_upd3 s) ! vcount = ds_prnt s ! vcount" by (rule bd_upd3_prnt_vcount[OF ne])
        have "build_dfs fl s = build_dfs fl (bd_upd3 s)" using IH(1) c by (rule bd_simps(3))
        thus ?thesis using IH(4)[OF c] bd_upd3_inv[OF inv c] fr by simp
      next
        assume c: "bd_ret_conds s"
        have "build_dfs fl s = s" using IH(1) c by (rule bd_simps(4))
        thus ?thesis by simp
      qed
    qed
  qed
  thus "ds_prnt (build_dfs fl s) ! vcount = ds_prnt s ! vcount" using inv0 by simp
qed

lemma otc_pre_inv: "\<And>fl s c. dfs_inv fl s \<Longrightarrow> c < vcount \<Longrightarrow> \<not> ds_seen s ! c \<Longrightarrow> c \<noteq> 0 \<Longrightarrow> ds_stk s = [] \<Longrightarrow> dfs_inv fl (otc_pre fl s c)"
proof -
  fix fl s c assume inv: "dfs_inv fl s" and c: "c < vcount" and unseen: "\<not> ds_seen s ! c" and cnz: "c \<noteq> 0" and stke: "ds_stk s = []"
  show "dfs_inv fl (otc_pre fl s c)"
    unfolding otc_pre_def Let_def dfs_inv_def
    apply (intro conjI)
    subgoal using inv c by (auto simp: dfs_inv_def dfs_wf_def dfs_sized_def tree_seen_inv_def nth_list_update)
    subgoal using inv c by (auto simp: dfs_inv_def dfs_wf_def dfs_sized_def tree_seen_inv_def nth_list_update)
    subgoal using inv c by (auto simp: dfs_inv_def dfs_wf_def dfs_sized_def tree_seen_inv_def nth_list_update)
    subgoal apply (rule thread_inv_upd[where s = s and w = c]) using inv c unseen cnz by (auto simp: dfs_inv_def dfs_sized_def)
    subgoal using inv c by (auto simp: dfs_inv_def dfs_sized_def par_edge_inv_def nth_list_update)
    subgoal apply (rule pot_inv_seed[where s = s and c = c]) using inv c unseen by (auto simp: dfs_inv_def dfs_sized_def nth_list_update)
    subgoal using inv c by (auto simp: dfs_inv_def dfs_sized_def root_pot_inv_def nth_list_update)
    subgoal using inv c by (auto simp: dfs_inv_def dfs_sized_def stk_prnt_inv_def nth_list_update)
    subgoal apply (rule emit_ord_inv_seed[where s = s and c = c]) using inv c unseen by (auto simp: dfs_inv_def dfs_sized_def)
    subgoal apply (rule snum_inv_seed[where s = s and c = c]) using inv c unseen stke by (auto simp: dfs_inv_def dfs_sized_def)
    subgoal apply (rule lsuc_inv_seed[where s = s and c = c]) using inv c unseen stke by (auto simp: dfs_inv_def dfs_sized_def)
    done
qed

lemma open_tree_component_prnt_vcount: "\<And>fl s c. dfs_inv fl s \<Longrightarrow> c < vcount \<Longrightarrow> \<not> ds_seen s ! c \<Longrightarrow> c \<noteq> 0 \<Longrightarrow> ds_stk s = [] \<Longrightarrow> ds_prnt (open_tree_component fl s c) ! vcount = ds_prnt s ! vcount"
proof -
  fix fl s c assume inv: "dfs_inv fl s" and c: "c < vcount" and unseen: "\<not> ds_seen s ! c" and cnz: "c \<noteq> 0" and stke: "ds_stk s = []"
  have iotc: "dfs_inv fl (otc_pre fl s c)" using otc_pre_inv[OF inv c unseen cnz stke] .
  have wf: "dfs_wf (otc_pre fl s c)" using iotc by (simp add: dfs_inv_def)
  have dom: "build_dfs_dom (fl, otc_pre fl s c)" using build_dfs_dom_wf'[OF wf] .
  have "ds_prnt (build_dfs fl (otc_pre fl s c)) ! vcount = ds_prnt (otc_pre fl s c) ! vcount"
    using build_dfs_prnt_vcount[OF dom iotc] .
  also have "... = ds_prnt s ! vcount" using c by (simp add: otc_pre_def Let_def nth_list_update_neq)
  finally show "ds_prnt (open_tree_component fl s c) ! vcount = ds_prnt s ! vcount"
    by (simp add: open_tree_component_eq_pre)
qed

lemma phase1_step_prnt_vcount: "\<And>fl v s. v \<in> set vs_list \<Longrightarrow> dfs_inv fl s \<Longrightarrow> ds_stk s = [] \<Longrightarrow> ds_prnt (phase1_step fl v s) ! vcount = ds_prnt s ! vcount"
proof -
  fix fl v s assume vin: "v \<in> set vs_list" and inv: "dfs_inv fl s" and stke: "ds_stk s = []"
  show "ds_prnt (phase1_step fl v s) ! vcount = ds_prnt s ! vcount"
  proof (cases "imbalance ! v = 0")
    case True thus ?thesis by (simp add: phase1_step_def)
  next
    case nz: False
    show ?thesis
    proof (cases "ds_seen s ! v")
      case True thus ?thesis using nz by (simp add: phase1_step_def emit_U_edge_def Let_def)
    next
      case False
      have vlt: "v < vcount" using vs_less_vcount[OF vin] .
      have vnz: "v \<noteq> 0" using vin no_zero_node by metis
      have "ds_prnt (open_tree_component fl s v) ! vcount = ds_prnt s ! vcount"
        using open_tree_component_prnt_vcount[OF inv vlt False vnz stke] .
      thus ?thesis using nz False by (simp add: phase1_step_def)
    qed
  qed
qed

lemma phase2_step_prnt_vcount: "\<And>fl v s. v \<in> set vs_list \<Longrightarrow> dfs_inv fl s \<Longrightarrow> ds_stk s = [] \<Longrightarrow> ds_prnt (phase2_step fl v s) ! vcount = ds_prnt s ! vcount"
proof -
  fix fl v s assume vin: "v \<in> set vs_list" and inv: "dfs_inv fl s" and stke: "ds_stk s = []"
  show "ds_prnt (phase2_step fl v s) ! vcount = ds_prnt s ! vcount"
  proof (cases "ds_seen s ! v \<or> is_lonely v")
    case True thus ?thesis by (simp add: phase2_step_def)
  next
    case False
    hence ns: "\<not> ds_seen s ! v" by auto
    have vlt: "v < vcount" using vs_less_vcount[OF vin] .
    have vnz: "v \<noteq> 0" using vin no_zero_node by metis
    have "ds_prnt (open_tree_component fl s v) ! vcount = ds_prnt s ! vcount"
      using open_tree_component_prnt_vcount[OF inv vlt ns vnz stke] .
    thus ?thesis using False by (simp add: phase2_step_def)
  qed
qed

lemma phase1_prnt_vcount: "\<And>fl s. dfs_inv fl s \<Longrightarrow> ds_stk s = [] \<Longrightarrow> ds_prnt (phase1 fl s) ! vcount = ds_prnt s ! vcount"
proof -
  fix fl s assume inv: "dfs_inv fl s" and stke: "ds_stk s = []"
  have "dfs_inv fl (phase1 fl s) \<and> ds_stk (phase1 fl s) = [] \<and> ds_prnt (phase1 fl s) ! vcount = ds_prnt s ! vcount"
    unfolding phase1_def
    apply (rule fold_invariant[where Q = "\<lambda>v. v \<in> set vs_list" and P = "\<lambda>t. dfs_inv fl t \<and> ds_stk t = [] \<and> ds_prnt t ! vcount = ds_prnt s ! vcount"])
      apply simp
     apply (simp add: inv stke)
    subgoal for x t
      using phase1_step_inv[of x fl t] phase1_step_prnt_vcount[of x fl t] by auto
    done
  thus "ds_prnt (phase1 fl s) ! vcount = ds_prnt s ! vcount" by simp
qed

lemma phase2_prnt_vcount: "\<And>fl s. dfs_inv fl s \<Longrightarrow> ds_stk s = [] \<Longrightarrow> ds_prnt (phase2 fl s) ! vcount = ds_prnt s ! vcount"
proof -
  fix fl s assume inv: "dfs_inv fl s" and stke: "ds_stk s = []"
  have "dfs_inv fl (phase2 fl s) \<and> ds_stk (phase2 fl s) = [] \<and> ds_prnt (phase2 fl s) ! vcount = ds_prnt s ! vcount"
    unfolding phase2_def
    apply (rule fold_invariant[where Q = "\<lambda>v. v \<in> set vs_list" and P = "\<lambda>t. dfs_inv fl t \<and> ds_stk t = [] \<and> ds_prnt t ! vcount = ds_prnt s ! vcount"])
      apply simp
     apply (simp add: inv stke)
    subgoal for x t
      using phase2_step_inv[of x fl t] phase2_step_prnt_vcount[of x fl t] by auto
    done
  thus "ds_prnt (phase2 fl s) ! vcount = ds_prnt s ! vcount" by simp
qed

lemma build_tree_root_prnt: "ds_prnt (build_tree fl) ! vcount = 0"
proof -
  have i0: "dfs_inv fl dfs_init \<and> ds_stk dfs_init = []" using dfs_init_inv by (simp add: dfs_init_def)
  have p1: "dfs_inv fl (phase1 fl dfs_init) \<and> ds_stk (phase1 fl dfs_init) = []" using phase1_inv[OF i0] .
  have "ds_prnt (phase2 fl (phase1 fl dfs_init)) ! vcount = ds_prnt (phase1 fl dfs_init) ! vcount"
    using phase2_prnt_vcount[OF conjunct1[OF p1] conjunct2[OF p1]] .
  also have "... = ds_prnt dfs_init ! vcount"
    using phase1_prnt_vcount[OF conjunct1[OF i0] conjunct2[OF i0]] .
  also have "... = 0" by (simp add: dfs_init_def del: replicate_Suc)
  finally have core: "ds_prnt (phase2 fl (phase1 fl dfs_init)) ! vcount = 0" .
  show "ds_prnt (build_tree fl) ! vcount = 0"
    unfolding build_tree_def Let_def using core by simp
qed

text \<open>Layer 1 of the network-simplex loop's padding-coupling lemma: the concrete entering-edge
      selector reads @{term edge_state} only at arc indices in @{term \<open>{0..<marc}\<close>}.  Hence
      @{const evaluate}, @{const scan_cache}, @{const scan} and @{const sel_select_impl} give the same
      result on two edge-state lists that agree on @{term \<open>{0..<marc}\<close>} — the invariant a padded
      @{term \<open>state_all @ replicate (n - Kart) InL\<close>} needs so the loop is insensitive to the inert tail.\<close>

lemma evaluate_es_cong:
  "\<And>(es::edge_tag list) (es'::edge_tag list) (\<pi>::(mtag\<times>'n) list) e. es ! e = es' ! e \<Longrightarrow> evaluate es \<pi> e = evaluate es' \<pi> e"
proof -
  fix es es' :: "edge_tag list" and \<pi> :: "(mtag\<times>'n) list" and e
  assume eq: "es ! e = es' ! e"
  show "evaluate es \<pi> e = evaluate es' \<pi> e" unfolding evaluate_def eq ..
qed

lemma scan_cache_es_cong: "\<And>(es::edge_tag list) (es'::edge_tag list) (\<pi>::(mtag\<times>'n) list) i a len best.
     len \<le> length a \<Longrightarrow> (\<forall>j<len. a ! j < marc) \<Longrightarrow> (\<forall>k<marc. es ! k = es' ! k) \<Longrightarrow>
     scan_cache es \<pi> i a len best = scan_cache es' \<pi> i a len best"
proof -
  fix es es' :: "edge_tag list" and \<pi> :: "(mtag \<times> 'n) list" and i a len best
  show "len \<le> length a \<Longrightarrow> (\<forall>j<len. a ! j < marc) \<Longrightarrow> (\<forall>k<marc. es ! k = es' ! k) \<Longrightarrow>
        scan_cache es \<pi> i a len best = scan_cache es' \<pi> i a len best"
  proof (induction es \<pi> i a len best rule: scan_cache.induct)
    case (1 es \<pi> i a len best)
    note IHe = 1(1) and IHn = 1(2) and prA = 1(3) and prB = 1(4) and prC = 1(5)
    show ?case
    proof (cases "len \<le> i")
      case True
      thus ?thesis by (subst scan_cache.simps, subst (2) scan_cache.simps) simp
    next
      case False
      hence ilt: "i < len" by simp
      have emarc: "a ! i < marc" using prB ilt by blast
      have ev: "evaluate es \<pi> (a ! i) = evaluate es' \<pi> (a ! i)"
        by (rule evaluate_es_cong) (rule prC[rule_format, OF emarc])
      obtain elig u g where eveq: "evaluate es \<pi> (a ! i) = (elig, u, g)"
        by (cases "evaluate es \<pi> (a ! i)") auto
      show ?thesis
      proof (cases elig)
        case True
        have L: "scan_cache es \<pi> i a len best = scan_cache es \<pi> (Suc i) a len (better best (a ! i, u, g))"
          using False eveq True by (subst scan_cache.simps) (simp add: Let_def)
        have R: "scan_cache es' \<pi> i a len best = scan_cache es' \<pi> (Suc i) a len (better best (a ! i, u, g))"
          using False eveq ev True by (subst scan_cache.simps) (simp add: Let_def)
        show ?thesis using L R IHe[OF False refl eveq[symmetric] refl refl True prA prB prC] by simp
      next
        case False
        note nelig = this
        have L: "scan_cache es \<pi> i a len best = scan_cache es \<pi> i (a[i := a ! (len - 1)]) (len - 1) best"
          using \<open>\<not> len \<le> i\<close> eveq nelig by (subst scan_cache.simps) (simp add: Let_def)
        have R: "scan_cache es' \<pi> i a len best = scan_cache es' \<pi> i (a[i := a ! (len - 1)]) (len - 1) best"
          using \<open>\<not> len \<le> i\<close> eveq ev nelig by (subst scan_cache.simps) (simp add: Let_def)
        have p1: "len - 1 \<le> length (a[i := a ! (len - 1)])" using prA by simp
        have ial: "i < length a" using prA ilt by simp
        have lpos: "0 < len" using ilt by simp
        have l1m: "a ! (len - 1) < marc" using prB[rule_format, of "len - 1"] lpos by simp
        have p2: "\<forall>j<len - 1. a[i := a ! (len - 1)] ! j < marc"
        proof (intro allI impI)
          fix j assume j: "j < len - 1"
          show "a[i := a ! (len - 1)] ! j < marc"
          proof (cases "j = i")
            case True thus ?thesis using l1m ial by (simp add: nth_list_update)
          next
            case False
            have "a[i := a ! (len - 1)] ! j = a ! j" using False by (simp add: nth_list_update_neq)
            thus ?thesis using prB j by simp
          qed
        qed
        show ?thesis using L R IHn[OF \<open>\<not> len \<le> i\<close> refl eveq[symmetric] refl refl nelig p1 p2 prC] by simp
      qed
    qed
  qed
qed

lemma scan_es_cong: "\<And>(es::edge_tag list) (es'::edge_tag list) (\<pi>::(mtag\<times>'n) list) mc fuel bpos cur a len best.
     mc = marc \<Longrightarrow> 0 < marc \<Longrightarrow> cur < marc \<Longrightarrow> (\<forall>k<marc. es ! k = es' ! k) \<Longrightarrow>
     scan es \<pi> mc fuel bpos cur a len best = scan es' \<pi> mc fuel bpos cur a len best"
proof -
  fix es es' :: "edge_tag list" and \<pi> :: "(mtag \<times> 'n) list" and mc fuel bpos cur a len best
  show "mc = marc \<Longrightarrow> 0 < marc \<Longrightarrow> cur < marc \<Longrightarrow> (\<forall>k<marc. es ! k = es' ! k) \<Longrightarrow>
        scan es \<pi> mc fuel bpos cur a len best = scan es' \<pi> mc fuel bpos cur a len best"
  proof (induction fuel arbitrary: bpos cur a len best)
    case 0
    thus ?case by (subst scan.simps, subst (2) scan.simps) simp
  next
    case (Suc f)
    note prMc = Suc.prems(1) and prPos = Suc.prems(2) and prCur = Suc.prems(3) and prC = Suc.prems(4)
    show ?case
    proof (cases "max_candidates \<le> len")
      case True thus ?thesis by (subst scan.simps, subst (2) scan.simps) simp
    next
      case False note nmax = this
      show ?thesis
      proof (cases "bpos = 0 \<and> min_candidates \<le> len")
        case True thus ?thesis using nmax by (subst scan.simps, subst (2) scan.simps) simp
      next
        case False note nb = this
        have nmax': "(max_candidates \<le> len) = False" using nmax by simp
        have nb': "(bpos = 0 \<and> min_candidates \<le> len) = False" using nb by simp
        have ev: "evaluate es \<pi> cur = evaluate es' \<pi> cur"
          by (rule evaluate_es_cong) (rule prC[rule_format, OF prCur])
        obtain elig u g where eveq: "evaluate es \<pi> cur = (elig, u, g)" by (cases "evaluate es \<pi> cur") auto
        have eveq': "evaluate es' \<pi> cur = (elig, u, g)" using ev eveq by simp
        define bpos1 where "bpos1 = (if bpos = 0 then block_size else bpos)"
        define a1 where "a1 = (if elig then a[len := cur] else a)"
        define len1 where "len1 = (if elig then Suc len else len)"
        define best1 where "best1 = (if elig then better best (cur, u, g) else best)"
        define cur1 where "cur1 = (if cur + 1 = mc then 0 else cur + 1)"
        have L: "scan es \<pi> mc (Suc f) bpos cur a len best = scan es \<pi> mc f (bpos1 - 1) cur1 a1 len1 best1"
          supply scan.simps[simp del]
          by (subst scan.simps) (simp add: Let_def nmax' nb' eveq bpos1_def a1_def len1_def best1_def cur1_def)
        have R: "scan es' \<pi> mc (Suc f) bpos cur a len best = scan es' \<pi> mc f (bpos1 - 1) cur1 a1 len1 best1"
          supply scan.simps[simp del]
          by (subst scan.simps) (simp add: Let_def nmax' nb' eveq' bpos1_def a1_def len1_def best1_def cur1_def)
        have cur1m: "cur1 < marc" using prCur prMc prPos by (auto simp: cur1_def)
        have rec: "scan es \<pi> mc f (bpos1 - 1) cur1 a1 len1 best1 = scan es' \<pi> mc f (bpos1 - 1) cur1 a1 len1 best1"
          by (rule Suc.IH[OF prMc prPos cur1m prC])
        show ?thesis using L R rec by simp
      qed
    qed
  qed
qed

text \<open>The entering-edge selector as a whole reads @{term edge_state} only through @{const scan_cache}
      and @{const scan}, both confined to arcs below @{term marc} by @{const sel_invar_impl}, so its
      result is unchanged on edge-state lists agreeing on @{term \<open>{0..<marc}\<close>}.\<close>

lemma sel_select_impl_es_cong:
  assumes inv: "sel_invar_impl sel" and mpos: "0 < marc" and agr: "\<forall>k<marc. es ! k = es' ! k"
  shows "sel_select_impl sel \<pi> es = sel_select_impl sel \<pi> es'"
proof -
  have inv': "length (sel_arr sel) = max_candidates \<and> sel_len sel \<le> max_candidates \<and>
              (0 < marc \<longrightarrow> sel_cur sel < marc) \<and> set (take (sel_len sel) (sel_arr sel)) \<subseteq> {0..<marc}"
    using inv by (simp add: sel_invar_impl_def)
  have larr: "sel_len sel \<le> length (sel_arr sel)" using inv' by simp
  have cur: "sel_cur sel < marc" using inv' mpos by simp
  have rng: "set (take (sel_len sel) (sel_arr sel)) \<subseteq> {0..<marc}" using inv' by simp
  have idx: "\<forall>j<sel_len sel. sel_arr sel ! j < marc"
  proof (intro allI impI)
    fix j assume j: "j < sel_len sel"
    have "j < length (take (sel_len sel) (sel_arr sel))" using j larr by (simp add: min_def)
    hence "take (sel_len sel) (sel_arr sel) ! j \<in> set (take (sel_len sel) (sel_arr sel))" by (rule nth_mem)
    moreover have "take (sel_len sel) (sel_arr sel) ! j = sel_arr sel ! j" using j by simp
    ultimately show "sel_arr sel ! j < marc" using rng by auto
  qed
  have SC: "scan_cache es \<pi> 0 (sel_arr sel) (sel_len sel) no_best
            = scan_cache es' \<pi> 0 (sel_arr sel) (sel_len sel) no_best"
    by (rule scan_cache_es_cong[OF larr idx agr])
  obtain a1 len1 found1 e1 u1 g1
    where sc: "scan_cache es' \<pi> 0 (sel_arr sel) (sel_len sel) no_best = (a1, len1, found1, e1, u1, g1)"
    by (cases "scan_cache es' \<pi> 0 (sel_arr sel) (sel_len sel) no_best") auto
  have SE: "scan es \<pi> marc marc block_size (sel_cur sel) a1 len1 no_best
            = scan es' \<pi> marc marc block_size (sel_cur sel) a1 len1 no_best"
    by (rule scan_es_cong[OF refl mpos cur agr])
  show ?thesis
    unfolding sel_select_impl_def SC sc by (simp add: SE del: scan.simps)
qed

text \<open>Layer 2: the coupling relation @{term ns_couple} between two loop states that differ only in an
      inert tail of the flow / edge-state arrays (the indices at or above @{term marc}); all other fields are
      equal, flow and edge-state agree on @{term \<open>{0..<marc}\<close>}, and both satisfy @{const NS.ns_invar}.
      Under it the entering-edge selection agrees (@{thm sel_select_impl_es_cong}).\<close>

definition ns_couple where
  "ns_couple s s' \<longleftrightarrow>
     network_simplex_state.potentials s = network_simplex_state.potentials s' \<and>
     network_simplex_state.spanning_tree s = network_simplex_state.spanning_tree s' \<and>
     network_simplex_state.parent_edge s = network_simplex_state.parent_edge s' \<and>
     network_simplex_state.edge_dir s = network_simplex_state.edge_dir s' \<and>
     network_simplex_state.edge_sel s = network_simplex_state.edge_sel s' \<and>
     network_simplex_state.return s = network_simplex_state.return s' \<and>
     (\<forall>e<marc. network_simplex_state.current_flow s ! e = network_simplex_state.current_flow s' ! e) \<and>
     (\<forall>e<marc. network_simplex_state.edge_state s ! e = network_simplex_state.edge_state s' ! e) \<and>
     NS.ns_invar s \<and> NS.ns_invar s'"

lemma ns_select_cong:
  assumes cpl: "ns_couple s s'" and mpos: "0 < marc"
  shows "NS.ns_select s = NS.ns_select s'"
proof -
  have pot: "network_simplex_state.potentials s = network_simplex_state.potentials s'"
   and sel: "network_simplex_state.edge_sel s = network_simplex_state.edge_sel s'"
   and es: "\<forall>e<marc. network_simplex_state.edge_state s ! e = network_simplex_state.edge_state s' ! e"
   and inv: "NS.ns_invar s" using cpl by (auto simp: ns_couple_def)
  have si: "sel_invar_impl (network_simplex_state.edge_sel s)"
    using NS.ns_invar_implD(6)[OF NS.ns_invarD(1)[OF inv]] .
  have cong: "sel_select_impl (network_simplex_state.edge_sel s) (network_simplex_state.potentials s) (network_simplex_state.edge_state s)
            = sel_select_impl (network_simplex_state.edge_sel s) (network_simplex_state.potentials s) (network_simplex_state.edge_state s')"
    by (rule sel_select_impl_es_cong[OF si mpos es])
  have "NS.ns_select s = sel_select_impl (network_simplex_state.edge_sel s) (network_simplex_state.potentials s) (network_simplex_state.edge_state s')"
    unfolding NS.ns_select_def by (rule cong)
  also have "... = NS.ns_select s'" unfolding NS.ns_select_def by (simp add: pot sel)
  finally show ?thesis .
qed

text \<open>Layer 3 (part a): residual congruences. Under the coupling relation, the forward and backward
      residuals agree at any real arc, and the parent-edge residuals agree at any tree vertex.\<close>

lemma res_fwd_cong:
  assumes "ns_couple s s'" and "a < marc"
  shows "NS.res_fwd s a = NS.res_fwd s' a"
proof -
  have "network_simplex_state.current_flow s ! a = network_simplex_state.current_flow s' ! a"
    using assms by (auto simp: ns_couple_def)
  thus ?thesis by (simp add: NS.res_fwd_def Let_def)
qed

lemma res_bwd_cong:
  assumes "ns_couple s s'" and "a < marc"
  shows "NS.res_bwd s a = NS.res_bwd s' a"
proof -
  have "network_simplex_state.current_flow s ! a = network_simplex_state.current_flow s' ! a"
    using assms by (auto simp: ns_couple_def)
  thus ?thesis by (simp add: NS.res_bwd_def)
qed

lemma res_up_cong:
  assumes cpl: "ns_couple s s'" and pe: "NS.par_edge s v < marc"
  shows "NS.res_up s v = NS.res_up s' v"
proof -
  have peq: "NS.par_edge s v = NS.par_edge s' v" using cpl by (simp add: NS.par_edge_def ns_couple_def)
  have ueq: "NS.par_up s v = NS.par_up s' v" using cpl by (simp add: NS.par_up_def ns_couple_def)
  have F: "NS.res_fwd s (NS.par_edge s v) = NS.res_fwd s' (NS.par_edge s v)" using res_fwd_cong[OF cpl pe] .
  have B: "NS.res_bwd s (NS.par_edge s v) = NS.res_bwd s' (NS.par_edge s v)" using res_bwd_cong[OF cpl pe] .
  show ?thesis
  proof (cases "NS.par_up s v")
    case True thus ?thesis using ueq F peq by (simp add: NS.res_up_def)
  next
    case False thus ?thesis using ueq B peq by (simp add: NS.res_up_def)
  qed
qed

lemma res_down_cong:
  assumes cpl: "ns_couple s s'" and pe: "NS.par_edge s v < marc"
  shows "NS.res_down s v = NS.res_down s' v"
proof -
  have peq: "NS.par_edge s v = NS.par_edge s' v" using cpl by (simp add: NS.par_edge_def ns_couple_def)
  have ueq: "NS.par_up s v = NS.par_up s' v" using cpl by (simp add: NS.par_up_def ns_couple_def)
  have F: "NS.res_fwd s (NS.par_edge s v) = NS.res_fwd s' (NS.par_edge s v)" using res_fwd_cong[OF cpl pe] .
  have B: "NS.res_bwd s (NS.par_edge s v) = NS.res_bwd s' (NS.par_edge s v)" using res_bwd_cong[OF cpl pe] .
  show ?thesis
  proof (cases "NS.par_up s v")
    case True thus ?thesis using ueq B peq by (simp add: NS.res_down_def)
  next
    case False thus ?thesis using ueq F peq by (simp add: NS.res_down_def)
  qed
qed
text \<open>Layer 3 (part b): the two tree-path scans agree under the coupling, since every path vertex is a
      non-root tree vertex (@{thm NS.get_path_pair_verts}) whose parent edge is a real arc, so the
      per-vertex residuals coincide (@{thm res_up_cong} / @{thm res_down_cong}); the folds then agree
      by @{thm fold_cong}.\<close>

lemma scan_up_cong:
  assumes cpl: "ns_couple s s'" and pe: "\<forall>v\<in>set p. NS.par_edge s v < marc"
  shows "NS.scan_up s p = NS.scan_up s' p"
  unfolding NS.scan_up_def
proof (rule fold_cong[OF refl refl])
  fix x assume xp: "x \<in> set p"
  have "NS.res_up s x = NS.res_up s' x" using res_up_cong[OF cpl] pe xp by blast
  thus "(\<lambda>(m, best). let rr = NS.res_up s x in if rr = - 1 then (m, best) else if m = - 1 then (rr, x) else if rr \<le> m then (rr, x) else (m, best))
      = (\<lambda>(m, best). let rr = NS.res_up s' x in if rr = - 1 then (m, best) else if m = - 1 then (rr, x) else if rr \<le> m then (rr, x) else (m, best))"
    by simp
qed

lemma scan_down_cong:
  assumes cpl: "ns_couple s s'" and pe: "\<forall>v\<in>set p. NS.par_edge s v < marc"
  shows "NS.scan_down s p = NS.scan_down s' p"
  unfolding NS.scan_down_def
proof (rule fold_cong[OF refl refl])
  fix x assume xp: "x \<in> set p"
  have "NS.res_down s x = NS.res_down s' x" using res_down_cong[OF cpl] pe xp by blast
  thus "(\<lambda>(m, best). let rr = NS.res_down s x in if rr = - 1 then (m, best) else if m = - 1 then (rr, x) else if rr < m then (rr, x) else (m, best))
      = (\<lambda>(m, best). let rr = NS.res_down s' x in if rr = - 1 then (m, best) else if m = - 1 then (rr, x) else if rr < m then (rr, x) else (m, best))"
    by simp
qed
text \<open>Layer 3 (part b, cont.): the bottleneck agrees under the coupling — it is a function of the two
      scans, the entering-edge residual, and the (equal) direction flags.\<close>

lemma bottleneck_cong:
  assumes cpl: "ns_couple s s'" and eE: "e < marc"
    and up1: "\<forall>v\<in>set p1. NS.par_edge s v < marc" and up2: "\<forall>v\<in>set p2. NS.par_edge s v < marc"
  shows "NS.bottleneck s e in_U p1 p2 = NS.bottleneck s' e in_U p1 p2"
proof -
  have suc: "NS.scan_up s (if in_U then p1 else p2) = NS.scan_up s' (if in_U then p1 else p2)"
    using scan_up_cong[OF cpl] up1 up2 by (cases in_U) auto
  have sdc: "NS.scan_down s (if in_U then p2 else p1) = NS.scan_down s' (if in_U then p2 else p1)"
    using scan_down_cong[OF cpl] up1 up2 by (cases in_U) auto
  have rfe: "NS.res_fwd s e = NS.res_fwd s' e" using res_fwd_cong[OF cpl eE] .
  have rbe: "NS.res_bwd s e = NS.res_bwd s' e" using res_bwd_cong[OF cpl eE] .
  have pu: "NS.par_up s = NS.par_up s'" using cpl by (simp add: NS.par_up_def ns_couple_def fun_eq_iff)
  show ?thesis
    unfolding NS.bottleneck_def Let_def suc sdc rfe rbe pu by simp
qed
text \<open>Layer 3 (part b, cont.): the augmented flow agrees on the real arcs. Reusing
      @{thm NS.augment_flow_lookup_char} on each side, the per-arc formula depends only on the input
      flow at that arc (equal on the real arcs) and the tree structure (parent edges / directions,
      which are equal), so the outputs coincide there.\<close>

lemma augment_flow_cong:
  assumes cpl: "ns_couple s s'" and eE: "e < marc" and d0: "0 \<le> \<delta>" and am: "a < marc"
    and up1: "\<forall>v\<in>set p1. NS.par_edge s v < marc" and up2: "\<forall>v\<in>set p2. NS.par_edge s v < marc"
  shows "NS.augment_flow s e in_U \<delta> p1 p2 ! a = NS.augment_flow s' e in_U \<delta> p1 p2 ! a"
proof -
  have inv: "NS.ns_invar s" and inv': "NS.ns_invar s'" using cpl by (auto simp: ns_couple_def)
  have fis: "\<forall>k\<in>{0..<m + Kart}. k < length (network_simplex_state.current_flow s)"
    using NS.ns_invar_implD(1)[OF NS.ns_invarD(1)[OF inv]] .
  have fis': "\<forall>k\<in>{0..<m + Kart}. k < length (network_simplex_state.current_flow s')"
    using NS.ns_invar_implD(1)[OF NS.ns_invarD(1)[OF inv']] .
  have eE': "e \<in> {0..<m+Kart}" using eE by (simp add: marc_def)
  have peq: "\<And>w. NS.par_edge s w = NS.par_edge s' w" using cpl by (simp add: NS.par_edge_def ns_couple_def)
  have pueq: "\<And>w. NS.par_up s w = NS.par_up s' w" using cpl by (simp add: NS.par_up_def ns_couple_def)
  have pu1: "\<forall>w\<in>set (if in_U then p1 else p2). NS.par_edge s w \<in> {0..<m+Kart}"
    using up1 up2 by (cases in_U) (auto simp: marc_def)
  have pu2: "\<forall>w\<in>set (if in_U then p2 else p1). NS.par_edge s w \<in> {0..<m+Kart}"
    using up1 up2 by (cases in_U) (auto simp: marc_def)
  have pu1': "\<forall>w\<in>set (if in_U then p1 else p2). NS.par_edge s' w \<in> {0..<m+Kart}" using pu1 peq by simp
  have pu2': "\<forall>w\<in>set (if in_U then p2 else p1). NS.par_edge s' w \<in> {0..<m+Kart}" using pu2 peq by simp
  have fa: "network_simplex_state.current_flow s ! a = network_simplex_state.current_flow s' ! a"
    using cpl am by (auto simp: ns_couple_def)
  show ?thesis
    using NS.augment_flow_lookup_char[OF fis d0 eE' pu1 pu2, of a]
          NS.augment_flow_lookup_char[OF fis' d0 eE' pu1' pu2', of a]
    apply (simp add: fa)
    apply (intro conjI impI arg_cong2[where f = "(+)"] arg_cong[where f = sum_list] map_cong[OF refl])
    apply (auto simp: peq pueq)
    done
qed
text \<open>Layer 4: under the coupling and a @{term Some} selection, the bottleneck agrees — the entering
      edge is a real arc and both tree paths consist of non-root tree vertices, so @{thm bottleneck_cong}
      applies.\<close>

lemma couple_Some_bn:
  assumes cpl: "ns_couple s s'" and mpos: "0 < marc"
    and sel: "NS.ns_select s = Some (e, in_U, \<gamma>, sel')"
    and pp: "get_path_pair_impl (network_simplex_state.spanning_tree s) (fst_all ! e) (snd_all ! e) = (p1, p2)"
  shows "NS.bottleneck s e in_U p1 p2 = NS.bottleneck s' e in_U p1 p2"
proof -
  have inv: "NS.ns_invar s" using cpl by (simp add: ns_couple_def)
  have eE: "e \<in> {0..<m + Kart}" using NS.ns_select_SomeD(2)[OF inv sel] .
  have emarc: "e < marc" using eE by (simp add: marc_def)
  note ne = NS.entering_not_selfloop[OF inv sel]
  have emc: "e < m + Kart" using eE by simp
  have pp': "get_path_pair_impl (network_simplex_state.spanning_tree s)
               (if e < m + Kart then fst_all ! e else Product_Type.fst (prod_decode (e - (m + Kart))))
               (if e < m + Kart then snd_all ! e else Product_Type.snd (prod_decode (e - (m + Kart)))) = (p1, p2)"
    by (simp only: if_P[OF emc] pp)
  have tree: "NS.ns_invar_tree s" using NS.ns_invarD(7)[OF inv] .
  have up1E: "\<forall>v\<in>set p1. NS.par_edge s v \<in> {0..<m + Kart}"
  proof (rule ballI)
    fix v assume v: "v \<in> set p1"
    from subsetD[OF NS.get_path_pair_verts(1)[OF inv eE ne pp'] v]
    show "NS.par_edge s v \<in> {0..<m + Kart}" by (rule NS.ns_invar_tree_edgeD[OF tree])
  qed
  have up2E: "\<forall>v\<in>set p2. NS.par_edge s v \<in> {0..<m + Kart}"
  proof (rule ballI)
    fix v assume v: "v \<in> set p2"
    from subsetD[OF NS.get_path_pair_verts(2)[OF inv eE ne pp'] v]
    show "NS.par_edge s v \<in> {0..<m + Kart}" by (rule NS.ns_invar_tree_edgeD[OF tree])
  qed
  have up1: "\<forall>v\<in>set p1. NS.par_edge s v < marc" using up1E by (simp add: marc_def)
  have up2: "\<forall>v\<in>set p2. NS.par_edge s v < marc" using up2E by (simp add: marc_def)
  show ?thesis by (rule bottleneck_cong[OF cpl emarc up1 up2])
qed
text \<open>Layer 4: the four branch guards agree under the coupling (entering-edge selection agrees by
      @{thm ns_select_cong}; the paths by tree-equality; the bottleneck by @{thm couple_Some_bn}).\<close>

lemma ns_success_cond_cong:
  assumes cpl: "ns_couple s s'" and mpos: "0 < marc"
  shows "NS.ns_success_cond s = NS.ns_success_cond s'"
  unfolding NS.ns_success_cond_def ns_select_cong[OF cpl mpos] ..

lemma ns_unbounded_cond_cong:
  assumes cpl: "ns_couple s s'" and mpos: "0 < marc"
  shows "NS.ns_unbounded_cond s = NS.ns_unbounded_cond s'"
proof (cases "NS.ns_select s")
  case None thus ?thesis by (simp add: NS.ns_unbounded_cond_def ns_select_cong[OF cpl mpos])
next
  case (Some a)
  obtain e in_U \<gamma> sel' where a: "a = (e, in_U, \<gamma>, sel')" by (cases a) auto
  obtain p1 p2 where pp: "get_path_pair_impl (network_simplex_state.spanning_tree s) (fst_all ! e) (snd_all ! e) = (p1, p2)"
    by (cases "get_path_pair_impl (network_simplex_state.spanning_tree s) (fst_all ! e) (snd_all ! e)") auto
  have sel: "NS.ns_select s = Some (e, in_U, \<gamma>, sel')" using Some a by simp
  have sel': "NS.ns_select s' = Some (e, in_U, \<gamma>, sel')" using sel ns_select_cong[OF cpl mpos] by simp
  have bn: "NS.bottleneck s e in_U p1 p2 = NS.bottleneck s' e in_U p1 p2" using couple_Some_bn[OF cpl mpos sel pp] .
  have teq: "network_simplex_state.spanning_tree s = network_simplex_state.spanning_tree s'" using cpl by (simp add: ns_couple_def)
  show ?thesis unfolding NS.ns_unbounded_cond_def sel sel' by (simp add: pp bn teq[symmetric] Let_def)
qed

lemma ns_flip_cond_cong:
  assumes cpl: "ns_couple s s'" and mpos: "0 < marc"
  shows "NS.ns_flip_cond s = NS.ns_flip_cond s'"
proof (cases "NS.ns_select s")
  case None thus ?thesis by (simp add: NS.ns_flip_cond_def ns_select_cong[OF cpl mpos])
next
  case (Some a)
  obtain e in_U \<gamma> sel' where a: "a = (e, in_U, \<gamma>, sel')" by (cases a) auto
  obtain p1 p2 where pp: "get_path_pair_impl (network_simplex_state.spanning_tree s) (fst_all ! e) (snd_all ! e) = (p1, p2)"
    by (cases "get_path_pair_impl (network_simplex_state.spanning_tree s) (fst_all ! e) (snd_all ! e)") auto
  have sel: "NS.ns_select s = Some (e, in_U, \<gamma>, sel')" using Some a by simp
  have sel': "NS.ns_select s' = Some (e, in_U, \<gamma>, sel')" using sel ns_select_cong[OF cpl mpos] by simp
  have bn: "NS.bottleneck s e in_U p1 p2 = NS.bottleneck s' e in_U p1 p2" using couple_Some_bn[OF cpl mpos sel pp] .
  have teq: "network_simplex_state.spanning_tree s = network_simplex_state.spanning_tree s'" using cpl by (simp add: ns_couple_def)
  show ?thesis unfolding NS.ns_flip_cond_def sel sel' by (simp add: pp bn teq[symmetric] Let_def)
qed

lemma ns_pivot_cond_cong:
  assumes cpl: "ns_couple s s'" and mpos: "0 < marc"
  shows "NS.ns_pivot_cond s = NS.ns_pivot_cond s'"
proof (cases "NS.ns_select s")
  case None thus ?thesis by (simp add: NS.ns_pivot_cond_def ns_select_cong[OF cpl mpos])
next
  case (Some a)
  obtain e in_U \<gamma> sel' where a: "a = (e, in_U, \<gamma>, sel')" by (cases a) auto
  obtain p1 p2 where pp: "get_path_pair_impl (network_simplex_state.spanning_tree s) (fst_all ! e) (snd_all ! e) = (p1, p2)"
    by (cases "get_path_pair_impl (network_simplex_state.spanning_tree s) (fst_all ! e) (snd_all ! e)") auto
  have sel: "NS.ns_select s = Some (e, in_U, \<gamma>, sel')" using Some a by simp
  have sel': "NS.ns_select s' = Some (e, in_U, \<gamma>, sel')" using sel ns_select_cong[OF cpl mpos] by simp
  have bn: "NS.bottleneck s e in_U p1 p2 = NS.bottleneck s' e in_U p1 p2" using couple_Some_bn[OF cpl mpos sel pp] .
  have teq: "network_simplex_state.spanning_tree s = network_simplex_state.spanning_tree s'" using cpl by (simp add: ns_couple_def)
  show ?thesis unfolding NS.ns_pivot_cond_def sel sel' by (simp add: pp bn teq[symmetric] Let_def)
qed

text \<open>Re-parenting depends on the source state @{term s} only through @{term \<open>NS.par_edge s\<close>} and
      @{term \<open>NS.par_up s\<close>} (read along the spine); hence coupled states — which share
      @{term parent_edge} and @{term edge_dir}, and therefore @{term par_edge}/@{term par_up} — produce
      the identical re-parented arrays.\<close>
lemma reparent_walk_cong:
  assumes "\<And>w. NS.par_edge s w = NS.par_edge s' w" and "\<And>w. NS.par_up s w = NS.par_up s' w"
  shows "NS.reparent_walk s e v first pe pup ws pd = NS.reparent_walk s' e v first pe pup ws pd"
  using assms by (induction ws arbitrary: first pe pup pd) (auto simp: assms Let_def split: prod.splits if_splits)

lemma reparent_cong:
  assumes pe: "network_simplex_state.parent_edge s = network_simplex_state.parent_edge s'"
    and de: "network_simplex_state.edge_dir s = network_simplex_state.edge_dir s'"
  shows "NS.reparent s e P v = NS.reparent s' e P v"
proof -
  have peq: "\<And>w. NS.par_edge s w = NS.par_edge s' w" using pe by (simp add: NS.par_edge_def)
  have pueq: "\<And>w. NS.par_up s w = NS.par_up s' w" using de by (simp add: NS.par_up_def)
  show ?thesis unfolding NS.reparent_def pe de by (rule reparent_walk_cong[OF peq pueq])
qed

text \<open>Layer 4: the flip step preserves the coupling. On a flip, only @{term current_flow},
      @{term edge_state} and @{term edge_sel} change: the flow update agrees on @{term \<open>{0..<marc}\<close>}
      by @{thm augment_flow_cong} (using @{thm couple_Some_bn} to transfer the selection/bottleneck),
      the edge-state update by @{term list_update} pointwise, and both states stay invariant by
      @{thm NS.ns_flip_preservation}.\<close>
lemma ns_flip_upd_couple:
  assumes cpl: "ns_couple s s'" and mpos: "0 < marc" and cond: "NS.ns_flip_cond s"
  shows "ns_couple (NS.ns_flip_upd s) (NS.ns_flip_upd s')"
proof -
  have inv: "NS.ns_invar s" and inv': "NS.ns_invar s'" using cpl by (auto simp: ns_couple_def)
  have cond': "NS.ns_flip_cond s'" using ns_flip_cond_cong[OF cpl mpos] cond by simp
  from cond obtain e in_U \<gamma> sel' p1 p2 \<delta> v e0fwd up_side where
    sel: "NS.ns_select s = Some (e, in_U, \<gamma>, sel')" and
    ppx: "get_path_pair_impl (network_simplex_state.spanning_tree s) (fst_all ! e) (snd_all ! e) = (p1, p2)" and
    bn: "NS.bottleneck s e in_U p1 p2 = (\<delta>, True, v, e0fwd, up_side)" and dne: "\<delta> \<noteq> - 1"
    by (rule NS.ns_flip_condE)
  have sel': "NS.ns_select s' = Some (e, in_U, \<gamma>, sel')" using sel ns_select_cong[OF cpl mpos] by simp
  have teq: "network_simplex_state.spanning_tree s = network_simplex_state.spanning_tree s'" using cpl by (simp add: ns_couple_def)
  have bnc: "NS.bottleneck s e in_U p1 p2 = NS.bottleneck s' e in_U p1 p2" using couple_Some_bn[OF cpl mpos sel ppx] .
  have ppx': "get_path_pair_impl (network_simplex_state.spanning_tree s') (fst_all ! e) (snd_all ! e) = (p1, p2)" using ppx teq by simp
  have bn': "NS.bottleneck s' e in_U p1 p2 = (\<delta>, True, v, e0fwd, up_side)" using bnc bn by simp
  have flipeq: "NS.ns_flip_upd s = NS.ns_flip s e in_U \<gamma> sel' \<delta> p1 p2" by (simp add: NS.ns_flip_upd_def sel ppx bn)
  have flipeq': "NS.ns_flip_upd s' = NS.ns_flip s' e in_U \<gamma> sel' \<delta> p1 p2" by (simp add: NS.ns_flip_upd_def sel' ppx' bn')
  have eE: "e \<in> {0..<m + Kart}" using NS.ns_select_SomeD(2)[OF inv sel] .
  have emarc: "e < marc" using eE by (simp add: marc_def)
  have emc: "e < m + Kart" using eE by simp
  note ne = NS.entering_not_selfloop[OF inv sel]
  have ppf: "get_path_pair_impl (network_simplex_state.spanning_tree s)
               (if e < m + Kart then fst_all ! e else Product_Type.fst (prod_decode (e - (m + Kart))))
               (if e < m + Kart then snd_all ! e else Product_Type.snd (prod_decode (e - (m + Kart)))) = (p1, p2)"
    by (simp only: if_P[OF emc] ppx)
  have d0: "0 \<le> \<delta>" using NS.bottleneck_delta_bounds(1)[OF inv sel ppf bn dne] .
  have tree: "NS.ns_invar_tree s" using NS.ns_invarD(7)[OF inv] .
  have up1: "\<forall>v\<in>set p1. NS.par_edge s v < marc"
  proof (rule ballI)
    fix v assume v: "v \<in> set p1"
    from subsetD[OF NS.get_path_pair_verts(1)[OF inv eE ne ppf] v]
    have "NS.par_edge s v \<in> {0..<m + Kart}" by (rule NS.ns_invar_tree_edgeD[OF tree])
    thus "NS.par_edge s v < marc" by (simp add: marc_def)
  qed
  have up2: "\<forall>v\<in>set p2. NS.par_edge s v < marc"
  proof (rule ballI)
    fix v assume v: "v \<in> set p2"
    from subsetD[OF NS.get_path_pair_verts(2)[OF inv eE ne ppf] v]
    have "NS.par_edge s v \<in> {0..<m + Kart}" by (rule NS.ns_invar_tree_edgeD[OF tree])
    thus "NS.par_edge s v < marc" by (simp add: marc_def)
  qed
  have esl: "\<forall>k\<in>{0..<m + Kart}. k < length (network_simplex_state.edge_state s)"
    using NS.ns_invar_implD(5)[OF NS.ns_invarD(1)[OF inv]] .
  have esl': "\<forall>k\<in>{0..<m + Kart}. k < length (network_simplex_state.edge_state s')"
    using NS.ns_invar_implD(5)[OF NS.ns_invarD(1)[OF inv']] .
  have eles: "e < length (network_simplex_state.edge_state s)" using esl emc by simp
  have eles': "e < length (network_simplex_state.edge_state s')" using esl' emc by simp
  have esagree: "\<And>a. a < marc \<Longrightarrow> network_simplex_state.edge_state s ! a = network_simplex_state.edge_state s' ! a"
    using cpl by (simp add: ns_couple_def)
  have esupd: "\<And>a. a < marc \<Longrightarrow> (network_simplex_state.edge_state s)[e := (if in_U then InL else InU)] ! a = (network_simplex_state.edge_state s')[e := (if in_U then InL else InU)] ! a"
    by (auto simp: nth_list_update eles eles' esagree)
  have aug: "\<And>a. a < marc \<Longrightarrow> NS.augment_flow s e in_U \<delta> p1 p2 ! a = NS.augment_flow s' e in_U \<delta> p1 p2 ! a"
    by (rule augment_flow_cong[OF cpl emarc d0 _ up1 up2])
  have invf: "NS.ns_invar (NS.ns_flip s e in_U \<gamma> sel' \<delta> p1 p2)"
    using NS.ns_flip_preservation[OF inv cond] flipeq by simp
  have invf': "NS.ns_invar (NS.ns_flip s' e in_U \<gamma> sel' \<delta> p1 p2)"
    using NS.ns_flip_preservation[OF inv' cond'] flipeq' by simp
  show ?thesis
    unfolding flipeq flipeq' ns_couple_def
    apply (intro conjI)
    subgoal by (simp add: NS.ns_flip_def cpl[unfolded ns_couple_def])
    subgoal by (simp add: NS.ns_flip_def teq)
    subgoal by (simp add: NS.ns_flip_def cpl[unfolded ns_couple_def])
    subgoal by (simp add: NS.ns_flip_def cpl[unfolded ns_couple_def])
    subgoal by (simp add: NS.ns_flip_def)
    subgoal by (simp add: NS.ns_flip_def cpl[unfolded ns_couple_def])
    subgoal by (simp add: NS.ns_flip_def aug)
    subgoal by (simp add: NS.ns_flip_def esupd)
    subgoal by (rule invf)
    subgoal by (rule invf')
    done
qed

text \<open>Layer 4: the pivot step preserves the coupling. A full pivot rewrites seven fields; the
      potential/tree/parent/dir arrays are pure functions of the shared @{term spanning_tree},
      @{term potentials}, @{term parent_edge}, @{term edge_dir} (the last via @{thm reparent_cong}),
      hence are literally equal; the flow agrees on @{term \<open>{0..<marc}\<close>} by @{thm augment_flow_cong}
      and the two edge-state updates (at @{term e} and the leaving arc @{term \<open>NS.par_edge s v\<close>},
      both in @{term \<open>{0..<m+Kart}\<close>}) by @{term list_update} pointwise; both states stay invariant by
      @{thm NS.ns_pivot_preservation}.\<close>
lemma ns_pivot_upd_couple:
  assumes cpl: "ns_couple s s'" and mpos: "0 < marc" and cond: "NS.ns_pivot_cond s"
  shows "ns_couple (NS.ns_pivot_upd s) (NS.ns_pivot_upd s')"
proof -
  have inv: "NS.ns_invar s" and inv': "NS.ns_invar s'" using cpl by (auto simp: ns_couple_def)
  have cond': "NS.ns_pivot_cond s'" using ns_pivot_cond_cong[OF cpl mpos] cond by simp
  from cond obtain e in_U \<gamma> sel' p1 p2 \<delta> v e0fwd up_side where
    sel: "NS.ns_select s = Some (e, in_U, \<gamma>, sel')" and
    ppx: "get_path_pair_impl (network_simplex_state.spanning_tree s) (fst_all ! e) (snd_all ! e) = (p1, p2)" and
    bn: "NS.bottleneck s e in_U p1 p2 = (\<delta>, False, v, e0fwd, up_side)" and dne: "\<delta> \<noteq> - 1"
    by (rule NS.ns_pivot_condE)
  have poteq: "network_simplex_state.potentials s = network_simplex_state.potentials s'"
    using cpl by (simp add: ns_couple_def)
  have teq: "network_simplex_state.spanning_tree s = network_simplex_state.spanning_tree s'"
    using cpl by (simp add: ns_couple_def)
  have pareq: "network_simplex_state.parent_edge s = network_simplex_state.parent_edge s'"
    using cpl by (simp add: ns_couple_def)
  have direq: "network_simplex_state.edge_dir s = network_simplex_state.edge_dir s'"
    using cpl by (simp add: ns_couple_def)
  have reteq: "network_simplex_state.return s = network_simplex_state.return s'"
    using cpl by (simp add: ns_couple_def)
  have sel': "NS.ns_select s' = Some (e, in_U, \<gamma>, sel')" using sel ns_select_cong[OF cpl mpos] by simp
  have bnc: "NS.bottleneck s e in_U p1 p2 = NS.bottleneck s' e in_U p1 p2" using couple_Some_bn[OF cpl mpos sel ppx] .
  have ppx': "get_path_pair_impl (network_simplex_state.spanning_tree s') (fst_all ! e) (snd_all ! e) = (p1, p2)" using ppx teq by simp
  have bn': "NS.bottleneck s' e in_U p1 p2 = (\<delta>, False, v, e0fwd, up_side)" using bnc bn by simp
  have eE: "e \<in> {0..<m + Kart}" using NS.ns_select_SomeD(2)[OF inv sel] .
  have emarc: "e < marc" using eE by (simp add: marc_def)
  have emc: "e < m + Kart" using eE by simp
  note ne = NS.entering_not_selfloop[OF inv sel]
  have ppf: "get_path_pair_impl (network_simplex_state.spanning_tree s)
               (if e < m + Kart then fst_all ! e else Product_Type.fst (prod_decode (e - (m + Kart))))
               (if e < m + Kart then snd_all ! e else Product_Type.snd (prod_decode (e - (m + Kart)))) = (p1, p2)"
    by (simp only: if_P[OF emc] ppx)
  have tree: "NS.ns_invar_tree s" using NS.ns_invarD(7)[OF inv] .
  have vVr: "v \<in> NS.\<V> - {vcount}" using NS.bottleneck_pivot_facts(2)[OF inv sel ppf bn] .
  have d0: "0 \<le> \<delta>" using NS.bottleneck_pivot_facts(5)[OF inv sel ppf bn] .
  have e0E: "NS.par_edge s v \<in> {0..<m + Kart}" using NS.ns_invar_tree_edgeD[OF tree vVr] .
  have e0marc: "NS.par_edge s v < marc" using e0E by (simp add: marc_def)
  have e0eq: "NS.par_edge s v = NS.par_edge s' v" using pareq by (simp add: NS.par_edge_def)
  have up1: "\<forall>w\<in>set p1. NS.par_edge s w < marc"
  proof (rule ballI)
    fix w assume w: "w \<in> set p1"
    from subsetD[OF NS.get_path_pair_verts(1)[OF inv eE ne ppf] w]
    have "NS.par_edge s w \<in> {0..<m + Kart}" by (rule NS.ns_invar_tree_edgeD[OF tree])
    thus "NS.par_edge s w < marc" by (simp add: marc_def)
  qed
  have up2: "\<forall>w\<in>set p2. NS.par_edge s w < marc"
  proof (rule ballI)
    fix w assume w: "w \<in> set p2"
    from subsetD[OF NS.get_path_pair_verts(2)[OF inv eE ne ppf] w]
    have "NS.par_edge s w \<in> {0..<m + Kart}" by (rule NS.ns_invar_tree_edgeD[OF tree])
    thus "NS.par_edge s w < marc" by (simp add: marc_def)
  qed
  define P where "P = (if in_U = up_side then p1 else p2)"
  obtain parr darr where rp: "NS.reparent s e P v = (parr, darr)" by (cases "NS.reparent s e P v")
  have rp': "NS.reparent s' e P v = (parr, darr)" using rp reparent_cong[OF pareq direq] by simp
  have piveq: "NS.ns_pivot_upd s = NS.ns_pivot s e in_U \<gamma> sel' \<delta> v e0fwd up_side p1 p2"
    by (simp add: NS.ns_pivot_upd_def sel ppx bn)
  have piveq': "NS.ns_pivot_upd s' = NS.ns_pivot s' e in_U \<gamma> sel' \<delta> v e0fwd up_side p1 p2"
    by (simp add: NS.ns_pivot_upd_def sel' ppx' bn')
  let ?s2 = "NS.ns_pivot s e in_U \<gamma> sel' \<delta> v e0fwd up_side p1 p2"
  let ?t2 = "NS.ns_pivot s' e in_U \<gamma> sel' \<delta> v e0fwd up_side p1 p2"
  have aug: "\<And>a. a < marc \<Longrightarrow> NS.augment_flow s e in_U \<delta> p1 p2 ! a = NS.augment_flow s' e in_U \<delta> p1 p2 ! a"
    by (rule augment_flow_cong[OF cpl emarc d0 _ up1 up2])
  have esagree: "\<And>a. a < marc \<Longrightarrow> network_simplex_state.edge_state s ! a = network_simplex_state.edge_state s' ! a"
    using cpl by (simp add: ns_couple_def)
  have esl: "\<forall>k\<in>{0..<m + Kart}. k < length (network_simplex_state.edge_state s)"
    using NS.ns_invar_implD(5)[OF NS.ns_invarD(1)[OF inv]] .
  have esl': "\<forall>k\<in>{0..<m + Kart}. k < length (network_simplex_state.edge_state s')"
    using NS.ns_invar_implD(5)[OF NS.ns_invarD(1)[OF inv']] .
  have eles: "e < length (network_simplex_state.edge_state s)" using esl emc by simp
  have eles': "e < length (network_simplex_state.edge_state s')" using esl' emc by simp
  have e0les: "NS.par_edge s v < length (network_simplex_state.edge_state s)" using esl e0E by simp
  have e0les': "NS.par_edge s v < length (network_simplex_state.edge_state s')" using esl' e0E e0eq by simp
  have esupd2: "\<And>a. a < marc \<Longrightarrow>
      (network_simplex_state.edge_state s)[e := InTree, NS.par_edge s v := (if e0fwd then InU else InL)] ! a
    = (network_simplex_state.edge_state s')[e := InTree, NS.par_edge s' v := (if e0fwd then InU else InL)] ! a"
    by (auto simp: e0eq[symmetric] nth_list_update eles eles' e0les e0les' esagree)
  have invf: "NS.ns_invar ?s2" using NS.ns_pivot_preservation(1)[OF inv cond] piveq by simp
  have invf': "NS.ns_invar ?t2" using NS.ns_pivot_preservation(1)[OF inv' cond'] piveq' by simp
  show ?thesis
    unfolding piveq piveq' ns_couple_def
    apply (intro conjI)
    subgoal by (simp add: NS.ns_pivot_def Let_def rp rp' teq poteq flip: P_def split: prod.split)
    subgoal by (simp add: NS.ns_pivot_def Let_def rp rp' teq flip: P_def split: prod.split)
    subgoal by (simp add: NS.ns_pivot_def Let_def rp rp' flip: P_def split: prod.split)
    subgoal by (simp add: NS.ns_pivot_def Let_def rp rp' flip: P_def split: prod.split)
    subgoal by (simp add: NS.ns_pivot_def Let_def rp rp' flip: P_def split: prod.split)
    subgoal by (simp add: NS.ns_pivot_def Let_def rp rp' reteq flip: P_def split: prod.split)
    subgoal by (simp add: NS.ns_pivot_def Let_def rp rp' aug flip: P_def split: prod.split)
    subgoal by (simp add: NS.ns_pivot_def Let_def rp rp' esupd2 flip: P_def split: prod.split)
    subgoal by (rule invf)
    subgoal by (rule invf')
    done
qed

text \<open>@{term ns_invar} does not mention the @{term return} field, so it is invariant under the
      terminal flag writes (mirrors @{thm initial_basis_selector.ns_invar_ret}).  The
       must disable the self-referential @{thm NS.fst_exec_eq}/@{thm NS.snd_exec_eq}
      to avoid the known rewrite loop.\<close>
lemma ns_invar_ret: "NS.ns_invar (s\<lparr>network_simplex_state.return := r\<rparr>) = NS.ns_invar s"
  by (simp del: NS.fst_exec_eq NS.snd_exec_eq
           add: NS.ns_invar_def NS.ns_invar_impl_def NS.ns_invar_bflow_def NS.ns_invar_partition_def
                NS.ns_invar_flow_fits_def NS.ns_invar_pot_fits_def NS.ns_invar_strict_def
                NS.ns_invar_tree_def NS.ns_invar_selfloop_def NS.ns_L_of_def NS.ns_U_of_def
                NS.par_edge_def NS.par_up_def NS.par_vx_def)

text \<open>Layer 4: the two terminal branches (optimum / unbounded) only set the @{term return} flag, so
      they trivially preserve the coupling.\<close>
lemma ns_optimal_couple:
  assumes cpl: "ns_couple s s'"
  shows "ns_couple (NS.ns_optimal s) (NS.ns_optimal s')"
  using cpl by (simp add: ns_couple_def NS.ns_optimal_def ns_invar_ret)

lemma ns_unbounded_couple:
  assumes cpl: "ns_couple s s'"
  shows "ns_couple (NS.ns_unbounded_upd s) (NS.ns_unbounded_upd s')"
  using cpl by (simp add: ns_couple_def NS.ns_unbounded_upd_def ns_invar_ret)

text \<open>Layer 5: the whole loop preserves the coupling and transfers termination.  By the tailored
      loop induction, the two terminal branches close by the terminal couplings, and the flip/pivot
      branches thread the coupling through one step and apply the induction hypothesis, transferring
      the domain condition back through @{thm NS.ns_loop_dom_flip}/@{thm NS.ns_loop_dom_pivot}.\<close>
lemma ns_loop_couple:
  assumes dom: "NS.ns_loop_dom s" and mpos: "0 < marc"
  shows "ns_couple s s' \<Longrightarrow> NS.ns_loop_dom s' \<and> ns_couple (NS.ns_loop s) (NS.ns_loop s')"
proof (induction arbitrary: s' rule: NS.ns_loop_induct[OF dom])
  case (1 s)
  note IH = this
  show ?case
  proof (cases s rule: NS.ns_loop_cases)
    case 1
    have cond': "NS.ns_success_cond s'" using ns_success_cond_cong[OF IH(4) mpos] 1 by simp
    have doms': "NS.ns_loop_dom s'" by (rule NS.ns_loop_dom_success[OF cond'])
    show ?thesis using doms' ns_optimal_couple[OF IH(4)]
      by (simp add: NS.ns_loop_simps(1)[OF IH(1) 1] NS.ns_loop_simps(1)[OF doms' cond'])
  next
    case 2
    have cond': "NS.ns_unbounded_cond s'" using ns_unbounded_cond_cong[OF IH(4) mpos] 2 by simp
    have doms': "NS.ns_loop_dom s'" by (rule NS.ns_loop_dom_unbounded[OF cond'])
    show ?thesis using doms' ns_unbounded_couple[OF IH(4)]
      by (simp add: NS.ns_loop_simps(2)[OF IH(1) 2] NS.ns_loop_simps(2)[OF doms' cond'])
  next
    case 3
    have cond': "NS.ns_flip_cond s'" using ns_flip_cond_cong[OF IH(4) mpos] 3 by simp
    have cplf: "ns_couple (NS.ns_flip_upd s) (NS.ns_flip_upd s')"
      by (rule ns_flip_upd_couple[OF IH(4) mpos 3])
    have rec: "NS.ns_loop_dom (NS.ns_flip_upd s') \<and>
               ns_couple (NS.ns_loop (NS.ns_flip_upd s)) (NS.ns_loop (NS.ns_flip_upd s'))"
      by (rule IH(2)[OF 3 cplf])
    have doms': "NS.ns_loop_dom s'" by (rule NS.ns_loop_dom_flip[OF cond' conjunct1[OF rec]])
    show ?thesis using doms' conjunct2[OF rec]
      by (simp add: NS.ns_loop_simps(3)[OF IH(1) 3] NS.ns_loop_simps(3)[OF doms' cond'])
  next
    case 4
    have cond': "NS.ns_pivot_cond s'" using ns_pivot_cond_cong[OF IH(4) mpos] 4 by simp
    have cplf: "ns_couple (NS.ns_pivot_upd s) (NS.ns_pivot_upd s')"
      by (rule ns_pivot_upd_couple[OF IH(4) mpos 4])
    have rec: "NS.ns_loop_dom (NS.ns_pivot_upd s') \<and>
               ns_couple (NS.ns_loop (NS.ns_pivot_upd s)) (NS.ns_loop (NS.ns_pivot_upd s'))"
      by (rule IH(3)[OF 4 cplf])
    have doms': "NS.ns_loop_dom s'" by (rule NS.ns_loop_dom_pivot[OF cond' conjunct1[OF rec]])
    show ?thesis using doms' conjunct2[OF rec]
      by (simp add: NS.ns_loop_simps(4)[OF IH(1) 4] NS.ns_loop_simps(4)[OF doms' cond'])
  qed
qed

text \<open>Padding invariance: the loop invariant @{const NS.ns_invar} depends on the flow and edge-state
      stores only through their values at the real edge universe @{term \<open>{0..<m+Kart}\<close>} (and the length
      bound).  Hence extending / overwriting either store outside that range — as the imperative solver
      does, allocating length @{term \<open>m+n\<close>} arrays and using only the first @{term \<open>m+Kart\<close>} cells —
      preserves the invariant.  Each of the eight conjuncts is transported: the b-flow via
      @{thm NS.isbflow_cong}, the two partition sets via their set-builder shape over the edge range, the
      flow-fit on the L / U sets (both subsets of the edge range), strong feasibility on the tree parent edges
      (@{thm NS.ns_invar_tree_edgeD} places them in @{term \<E>}), and the self-loop fit which quantifies
      over @{term \<E>}.  The self-referential @{thm NS.fst_exec_eq}/@{thm NS.snd_exec_eq} must be disabled
      throughout to avoid the known rewrite loop.\<close>
lemma ns_invar_flow_es_cong:
  assumes inv: "NS.ns_invar s"
    and flen: "\<forall>k\<in>{0..<m+Kart}. k < length fl"
    and eslen: "\<forall>k\<in>{0..<m+Kart}. k < length es"
    and fag: "\<And>k. k < m+Kart \<Longrightarrow> fl ! k = current_flow s ! k"
    and eag: "\<And>k. k < m+Kart \<Longrightarrow> es ! k = network_simplex_state.edge_state s ! k"
  shows "NS.ns_invar (s\<lparr>current_flow := fl, network_simplex_state.edge_state := es\<rparr>)"
proof -
  define s2 where "s2 = (s\<lparr>current_flow := fl, network_simplex_state.edge_state := es\<rparr>)"
  have cf2: "current_flow s2 = fl" by (simp add: s2_def)
  have es2: "network_simplex_state.edge_state s2 = es"
    and pe2: "parent_edge s2 = parent_edge s" and ed2: "edge_dir s2 = edge_dir s"
    and pot2: "potentials s2 = potentials s"
    and tr2: "network_simplex_state.spanning_tree s2 = network_simplex_state.spanning_tree s"
    and sel2: "edge_sel s2 = edge_sel s" by (simp_all add: s2_def)
  have pared: "\<And>v. NS.par_edge s2 v = NS.par_edge s v"
    by (simp add: NS.par_edge_def pe2 del: NS.fst_exec_eq NS.snd_exec_eq)
  have parup: "\<And>v. NS.par_up s2 v = NS.par_up s v"
    by (simp add: NS.par_up_def ed2 del: NS.fst_exec_eq NS.snd_exec_eq)
  have parvx: "\<And>v. NS.par_vx s2 v = NS.par_vx s v"
    by (simp add: NS.par_vx_def pared parup del: NS.fst_exec_eq NS.snd_exec_eq)
  have flowE: "\<And>e. e \<in> {0..<m+Kart} \<Longrightarrow> NS.ns_flow_of s2 e = NS.ns_flow_of s e"
    using fag by (auto simp: cf2)
  have esE: "\<And>e. e \<in> {0..<m+Kart} \<Longrightarrow> network_simplex_state.edge_state s2 ! e = network_simplex_state.edge_state s ! e"
    using eag by (auto simp: es2)
  have LsubE: "NS.ns_L_of s \<subseteq> {0..<m+Kart}" unfolding NS.ns_L_of_def by blast
  have UsubE: "NS.ns_U_of s \<subseteq> {0..<m+Kart}" unfolding NS.ns_U_of_def by blast
  have Leq: "NS.ns_L_of s2 = NS.ns_L_of s"
    using esE by (auto simp: NS.ns_L_of_def simp del: NS.fst_exec_eq NS.snd_exec_eq)
  have Ueq: "NS.ns_U_of s2 = NS.ns_U_of s"
    using esE by (auto simp: NS.ns_U_of_def simp del: NS.fst_exec_eq NS.snd_exec_eq)
  have impl2: "NS.ns_invar_impl s2"
    unfolding NS.ns_invar_impl_def
    using flen eslen NS.ns_invar_implD(2,3,4,6,7)[OF NS.ns_invarD(1)[OF inv]]
    by (simp add: cf2 es2 pot2 pe2 ed2 sel2 tr2 del: NS.fst_exec_eq NS.snd_exec_eq)
  have bflow2: "NS.ns_invar_bflow s2"
    unfolding NS.ns_invar_bflow_def
    apply (rule NS.isbflow_cong[OF _ refl NS.ns_invarD(2)[OF inv, unfolded NS.ns_invar_bflow_def]])
    by (auto simp: cf2 fag)
  have part2: "NS.ns_invar_partition s2"
    using NS.ns_invarD(3)[OF inv]
    by (simp add: NS.ns_invar_partition_def pe2 Leq Ueq del: NS.fst_exec_eq NS.snd_exec_eq)
  have fits2: "NS.ns_invar_flow_fits s2"
    unfolding NS.ns_invar_flow_fits_def NS.flow_fits_spanning_tree_partition_def Leq Ueq
    apply (intro conjI ballI)
    subgoal for e using flowE[of e] LsubE NS.ns_invarD(4)[OF inv]
      by (force simp add: NS.ns_invar_flow_fits_def NS.flow_fits_spanning_tree_partition_def
                simp del: NS.fst_exec_eq NS.snd_exec_eq)
    subgoal for e using flowE[of e] UsubE NS.ns_invarD(4)[OF inv]
      by (force simp add: NS.ns_invar_flow_fits_def NS.flow_fits_spanning_tree_partition_def
                simp del: NS.fst_exec_eq NS.snd_exec_eq)
    done
  have pot_fits2: "NS.ns_invar_pot_fits s2"
    using NS.ns_invarD(5)[OF inv]
    by (simp add: NS.ns_invar_pot_fits_def pe2 pot2 del: NS.fst_exec_eq NS.snd_exec_eq)
  have strict2: "NS.ns_invar_strict s2"
    unfolding NS.ns_invar_strict_def pared parup cf2
    apply (intro ballI)
    subgoal premises p for v
    proof -
      have pE: "NS.par_edge s v \<in> {0..<m+Kart}" using NS.ns_invar_tree_edgeD[OF NS.ns_invarD(7)[OF inv] p] .
      have fl_eq: "fl ! NS.par_edge s v = current_flow s ! NS.par_edge s v" using fag pE by simp
      show ?thesis using NS.ns_invarD(6)[OF inv] p
        by (simp add: NS.ns_invar_strict_def fl_eq del: NS.fst_exec_eq NS.snd_exec_eq)
    qed
    done
  have tree2: "NS.ns_invar_tree s2"
    using NS.ns_invarD(7)[OF inv]
    by (simp only: NS.ns_invar_tree_def NS.par_edge_def NS.par_up_def NS.par_vx_def pe2 ed2 tr2) blast
  have self2: "NS.ns_invar_selfloop s2"
    using NS.ns_invarD(8)[OF inv] flowE
    by (auto simp: NS.ns_invar_selfloop_def simp del: NS.fst_exec_eq NS.snd_exec_eq)
  show ?thesis
    unfolding s2_def[symmetric] NS.ns_invar_def
    using impl2 bflow2 part2 fits2 pot_fits2 strict2 tree2 self2 by blast
qed

text \<open>The padded state couples with its base: overwriting the flow / edge-state stores outside the
      real edge range @{term \<open>{0..<m+Kart}\<close>} yields a state standing in the coupling relation
      @{const ns_couple} with the original.  Combined with @{thm ns_loop_couple} this transports the
      whole loop from the imperative padded state to the functional initial basis.\<close>
lemma ns_pad_couple:
  assumes inv0: "NS.ns_invar s0"
    and flen: "\<forall>k\<in>{0..<m+Kart}. k < length fl" and eslen: "\<forall>k\<in>{0..<m+Kart}. k < length es"
    and fag: "\<And>k. k < m+Kart \<Longrightarrow> fl ! k = current_flow s0 ! k"
    and eag: "\<And>k. k < m+Kart \<Longrightarrow> es ! k = network_simplex_state.edge_state s0 ! k"
  shows "ns_couple (s0\<lparr>current_flow := fl, network_simplex_state.edge_state := es\<rparr>) s0"
proof -
  have inv2: "NS.ns_invar (s0\<lparr>current_flow := fl, network_simplex_state.edge_state := es\<rparr>)"
    by (rule ns_invar_flow_es_cong[OF inv0 flen eslen fag eag])
  show ?thesis
    unfolding ns_couple_def
    using inv0 inv2 by (auto simp: marc_def fag eag simp del: NS.fst_exec_eq NS.snd_exec_eq)
qed

text \<open>The coupling relation is symmetric (every conjunct of @{const ns_couple} is).\<close>
lemma ns_couple_sym: "ns_couple s s' \<Longrightarrow> ns_couple s' s"
  unfolding ns_couple_def by (auto simp del: NS.fst_exec_eq NS.snd_exec_eq)

text \<open>The whole-loop padding transfer, packaged for the capstone: running @{const NS.ns_loop} from a
      padded state agrees with running it from the base state — same termination, same terminal
      @{term return} verdict, and the two flows agree on the real edge range @{term \<open>{0..<marc}\<close>}.
      Instantiated later at @{term s0} = the functional initial basis.\<close>
lemma ns_loop_pad_transfer:
  assumes dom0: "NS.ns_loop_dom s0" and mpos: "0 < marc" and inv0: "NS.ns_invar s0"
    and flen: "\<forall>k\<in>{0..<m+Kart}. k < length fl" and eslen: "\<forall>k\<in>{0..<m+Kart}. k < length es"
    and fag: "\<And>k. k < m+Kart \<Longrightarrow> fl ! k = current_flow s0 ! k"
    and eag: "\<And>k. k < m+Kart \<Longrightarrow> es ! k = network_simplex_state.edge_state s0 ! k"
  shows "NS.ns_loop_dom (s0\<lparr>current_flow := fl, network_simplex_state.edge_state := es\<rparr>)
       \<and> network_simplex_state.return (NS.ns_loop (s0\<lparr>current_flow := fl, network_simplex_state.edge_state := es\<rparr>))
           = network_simplex_state.return (NS.ns_loop s0)
       \<and> (\<forall>e<marc. current_flow (NS.ns_loop (s0\<lparr>current_flow := fl, network_simplex_state.edge_state := es\<rparr>)) ! e
                   = current_flow (NS.ns_loop s0) ! e)"
proof -
  have cpl: "ns_couple s0 (s0\<lparr>current_flow := fl, network_simplex_state.edge_state := es\<rparr>)"
    by (rule ns_couple_sym[OF ns_pad_couple[OF inv0 flen eslen fag eag]])
  from ns_loop_couple[OF dom0 mpos, of "s0\<lparr>current_flow := fl, network_simplex_state.edge_state := es\<rparr>"] cpl
  have D: "NS.ns_loop_dom (s0\<lparr>current_flow := fl, network_simplex_state.edge_state := es\<rparr>)"
    and C: "ns_couple (NS.ns_loop s0) (NS.ns_loop (s0\<lparr>current_flow := fl, network_simplex_state.edge_state := es\<rparr>))"
    by blast+
  from C show ?thesis using D by (auto simp: ns_couple_def)
qed

text \<open>Functional core of the capstone.  When the acyclifier succeeds, the functional verdict
      @{const solve} is exactly the verdict read off @{term \<open>NS.ns_loop sp\<close>} for the padded initial
      basis @{term sp}: same @{term return}, same artificial-edge zero test on @{term \<open>[m..<m+Kart]\<close>},
      same optimal flow prefix @{term \<open>take m\<close>}.  The proof re-interprets @{locale network_simplex_init}
      at the concrete basis (discharged by the inherited \<open>NSinit_*\<close> obligations), turning
      @{const NS.ns_loop_impl} into @{const NS.ns_loop} via @{thm NS.ns_loop_dom_impl_same}, and pads
      through @{thm ns_loop_pad_transfer}; the @{term \<open>take m\<close>} branch uses the loop-invariant length
      bounds from @{thm ns_loop_invar}.\<close>
lemma solve_via_padded:
  assumes some: "acyc_flow_opt \<noteq> None" and mpos: "0 < marc"
    and flen: "\<forall>k\<in>{0..<m+Kart}. k < length fl" and eslen: "\<forall>k\<in>{0..<m+Kart}. k < length es"
    and fag: "\<And>k. k < m+Kart \<Longrightarrow> fl ! k = flow_all ! k"
    and eag: "\<And>k. k < m+Kart \<Longrightarrow> es ! k = state_all ! k"
  defines "sp \<equiv> (network_simplex_init_spec.init_state flow_all (ds_pot art_tree) (tree_st art_tree)
                   (ds_par art_tree) (ds_dir art_tree) state_all init_sel)
                 \<lparr>current_flow := fl, network_simplex_state.edge_state := es\<rparr>"
  shows "NS.ns_loop_dom sp \<and> NS.ns_invar sp
       \<and> solve = (if network_simplex_state.return (NS.ns_loop sp) = unbounded then Neg_inf_cycle
                  else if list_all (\<lambda>k. current_flow (NS.ns_loop sp) ! k = 0) [m..<m+Kart]
                       then Optimum (take m (current_flow (NS.ns_loop sp))) else Infeasible)"
proof -
  from some obtain f' where sf: "acyc_flow_opt = Some f'" by auto
  interpret NSinit: network_simplex_init
    where fst = "\<lambda> e. if e < m+Kart then fst_all ! e else Product_Type.fst (prod_decode (e - (m+Kart)))"
      and snd = "\<lambda> e. if e < m+Kart then snd_all ! e else Product_Type.snd (prod_decode (e - (m+Kart)))"
      and create_edge = "\<lambda> u v. (m+Kart) + prod_encode (u, v)"
      and \<E> = "{0..<m+Kart}"
      and \<u> = "\<lambda> e. if e < m+Kart then (if cap_all ! e = - 1 then \<infinity> else ereal (h (cap_all ! e))) else \<infinity>"
      and \<c> = "\<lambda> e. cost_all ! e"
      and r = vcount
      and shift_pot = shift_pot_impl
      and arborescense_invar = "arb_invar vcount Varb"
      and abstract_arborescense = abstract_arb
      and get_path_pair = get_path_pair_impl
      and swap_edge = swap_edge_impl
      and flow_invar = "\<lambda>xs. \<forall>k\<in>{0..<m+Kart}. k < length xs" and flow_upd = list_update and flow_lookup = nth
      and pot_invar = "\<lambda>xs. \<forall>v\<in>Varb. v < length xs" and pot_upd = list_update and pot_lookup = nth
      and parent_invar = "\<lambda>xs. \<forall>v\<in>Varb - {vcount}. v < length xs" and parent_upd = list_update and parent_lookup = nth
      and dir_invar = "\<lambda>xs. \<forall>v\<in>Varb - {vcount}. v < length xs" and dir_upd = list_update and dir_lookup = nth
      and es_invar = "\<lambda>xs. \<forall>k\<in>{0..<m+Kart}. k < length xs" and es_upd = list_update and es_lookup = nth
      and sel_invar = sel_invar_impl and sel_select = sel_select_impl
      and b = "\<lambda> v. h (b_lookup v)"
      and cap = "\<lambda> e. cap_all ! e"
      and pot_value_invar = "\<lambda> p. good_pot_val_c p \<and> pv_invar p"
      and pot_value_abstract = "pval_abstract bigM"
      and pot_value_plus = pval_plus
      and pot_value_minus = pval_minus
      and rcost_invar = rc_invar
      and rcost_abstract = "pval_abstract bigM"
      and fst_exec = "\<lambda> e. fst_all ! e"
      and snd_exec = "\<lambda> e. snd_all ! e"
      and init_flow = flow_all
      and init_pot = "ds_pot (build_tree acyc_flow)"
      and init_tree = Sarb
      and init_parent = "ds_par (build_tree acyc_flow)"
      and init_dir = "ds_dir (build_tree acyc_flow)"
      and init_edge_state = state_all
      and init_sel = init_sel
    apply unfold_locales
    apply (all \<open>(rule NSinit_tree_corr NSinit_strict NSinit_pot_fits NSinit_flow_fits_ns
                       arb_invar_Sarb NSinit_sel_invar
                       NSinit_flow_invar NSinit_es_invar_len NSinit_par_invar NSinit_dir_invar
                       pot_valid_build_tree NSinit_bflow_ne[OF some] NSinit_partition_aug[OF some]
                       NSinit_selfloop[OF some])?\<close>)
    done
  define I where "I = network_simplex_init_spec.init_state flow_all (ds_pot art_tree) (tree_st art_tree)
                        (ds_par art_tree) (ds_dir art_tree) state_all init_sel"
  have eqst: "I = NSinit.init_state"
    unfolding I_def by (simp add: NSinit.init_state_def network_simplex_init_spec.init_state_def Sarb_tree_st art_tree_def)
  have inv0: "NS.ns_invar I" unfolding eqst by (rule NSinit.init_state_invar)
  have dom0: "NS.ns_loop_dom I" unfolding eqst by (rule NSinit.network_simplex_correct(1))
  have cf0: "current_flow I = flow_all" and es0: "network_simplex_state.edge_state I = state_all"
    unfolding I_def by (simp_all add: network_simplex_init_spec.init_state_def)
  have fag': "\<And>k. k < m+Kart \<Longrightarrow> fl ! k = current_flow I ! k" using fag by (simp add: cf0)
  have eag': "\<And>k. k < m+Kart \<Longrightarrow> es ! k = network_simplex_state.edge_state I ! k" using eag by (simp add: es0)
  have sp_eq: "sp = I\<lparr>current_flow := fl, network_simplex_state.edge_state := es\<rparr>"
    unfolding sp_def I_def ..
  note T = ns_loop_pad_transfer[OF dom0 mpos inv0 flen eslen fag' eag']
  from T have Dsp: "NS.ns_loop_dom sp"
    and Rsp: "network_simplex_state.return (NS.ns_loop sp) = network_simplex_state.return (NS.ns_loop I)"
    and Fsp: "\<forall>e<marc. current_flow (NS.ns_loop sp) ! e = current_flow (NS.ns_loop I) ! e"
    unfolding sp_eq by auto
  have implsame: "NS.ns_loop_impl I = NS.ns_loop I" by (rule NS.ns_loop_dom_impl_same[OF dom0])
  have invI: "NS.ns_invar (NS.ns_loop I)" by (rule ns_loop_invar[OF dom0 inv0])
  have invsp0: "NS.ns_invar sp" unfolding sp_eq
    by (rule ns_invar_flow_es_cong[OF inv0 flen eslen fag' eag'])
  have invsp: "NS.ns_invar (NS.ns_loop sp)"
    using ns_loop_invar[OF Dsp[unfolded sp_eq] ns_invar_flow_es_cong[OF inv0 flen eslen fag' eag']]
    unfolding sp_eq by simp
  have fiI: "\<forall>k\<in>{0..<m+Kart}. k < length (current_flow (NS.ns_loop I))"
    using NS.ns_invar_implD(1)[OF NS.ns_invarD(1)[OF invI]] .
  have fisp: "\<forall>k\<in>{0..<m+Kart}. k < length (current_flow (NS.ns_loop sp))"
    using NS.ns_invar_implD(1)[OF NS.ns_invarD(1)[OF invsp]] .
  have lenI: "m \<le> length (current_flow (NS.ns_loop I))" using fiI mpos by (auto simp: marc_def)
  have lensp: "m \<le> length (current_flow (NS.ns_loop sp))" using fisp mpos by (auto simp: marc_def)
  have Fk: "\<And>k. k < m+Kart \<Longrightarrow> current_flow (NS.ns_loop_impl I) ! k = current_flow (NS.ns_loop sp) ! k"
    using Fsp implsame by (auto simp: marc_def)
  have r_eq: "network_simplex_state.return (NS.ns_loop_impl I) = network_simplex_state.return (NS.ns_loop sp)"
    using implsame Rsp by simp
  have la_eq: "list_all (\<lambda>k. current_flow (NS.ns_loop_impl I) ! k = 0) [m..<m+Kart]
             = list_all (\<lambda>k. current_flow (NS.ns_loop sp) ! k = 0) [m..<m+Kart]"
    using Fk by (auto simp: list_all_iff)
  have lenIimpl: "m \<le> length (current_flow (NS.ns_loop_impl I))" using lenI implsame by simp
  have tm_eq: "take m (current_flow (NS.ns_loop_impl I)) = take m (current_flow (NS.ns_loop sp))"
    by (rule nth_take_lemma[OF lenIimpl lensp]) (use Fk in auto)
  have solveE1: "solve = (if network_simplex_state.return (NS.ns_loop_impl I) = unbounded then Neg_inf_cycle
                  else if list_all (\<lambda>k. current_flow (NS.ns_loop_impl I) ! k = 0) [m..<m+Kart]
                       then Optimum (take m (current_flow (NS.ns_loop_impl I))) else Infeasible)"
    unfolding I_def by (simp add: solve_def sf)
  show ?thesis
    using Dsp invsp0 solveE1 r_eq la_eq tm_eq by simp
qed

text \<open>CSR-build congruences: the count and scatter phases read the key array only at the edge indices
      @{term \<open>[0..<m]\<close>}, so they are insensitive to how the key array is padded beyond @{term m}.  This
      lets the padded working arrays of @{const solve_imp} (length @{term \<open>m+n\<close>}) feed the clean
      @{const out_csr} / @{const in_csr} builders (which are phrased for the exact-length inputs).\<close>
lemma ct_key_cong: "(\<forall>e\<in>set es. key e = key' e) \<Longrightarrow> ct nn key es = ct nn key' es"
  unfolding ct_def by (rule fold_cong[OF refl refl]) auto

lemma scatter_edges_key_cong:
  assumes "\<forall>e\<in>set es. key e = key' e"
  shows "scatter_edges nn key es dflt = scatter_edges nn key' es dflt"
proof -
  have ct: "ct nn key es = ct nn key' es" using ct_key_cong[OF assms] .
  have fld: "fold (scatter_body key) es st = fold (scatter_body key') es st" for st
  proof (rule fold_cong[OF refl refl])
    fix e assume "e \<in> set es"
    hence "key e = key' e" using assms by simp
    thus "scatter_body key e = scatter_body key' e" by (simp add: scatter_body_def)
  qed
  show ?thesis unfolding scatter_edges_def ct by (simp add: fld)
qed

text \<open>The padded outgoing / ingoing CSR builders: @{const build_csr_imp} on any key array agreeing with
      @{term fst_list} / @{term snd_list} on @{term \<open>[0..<m]\<close>} establishes @{const csr_assn} of the
      abstract @{const out_csr} / @{const in_csr} (generalises @{thm build_csr_out_rule} to padded keys).\<close>
lemma build_csr_out_pad_rule:
  assumes lk: "m \<le> length keys" and bd: "\<forall>i<m. keys ! i < vcount" and ag: "\<forall>i<m. keys ! i = fst_list ! i"
  shows "<ka \<mapsto>\<^sub>a keys * c \<mapsto>\<^sub>a replicate vcount 0 * o_lo \<mapsto>\<^sub>a replicate vcount 0 * o_hi \<mapsto>\<^sub>a replicate vcount 0 * o_cur \<mapsto>\<^sub>a replicate vcount 0 * o_edges \<mapsto>\<^sub>a replicate m 0>
     build_csr_imp ka c o_lo o_hi o_cur o_edges m vcount
   <\<lambda>_. ka \<mapsto>\<^sub>a keys * c \<mapsto>\<^sub>a ct vcount ((!) fst_list) [0..<m] * csr_assn out_csr (o_edges, o_lo, o_hi, o_cur)>"
proof -
  have ctc: "ct vcount ((!) keys) [0..<m] = ct vcount ((!) fst_list) [0..<m]"
    by (rule ct_key_cong) (use ag in auto)
  have scc: "scatter_edges vcount ((!) keys) [0..<m] 0 = scatter_edges vcount ((!) fst_list) [0..<m] 0"
    by (rule scatter_edges_key_cong) (use ag in auto)
  show ?thesis
    apply (sep_auto heap: build_csr_imp_rule[OF lk bd] simp: csr_assn_def out_csr_edges out_csr_lo out_csr_hi out_csr_cur)
    apply (simp add: ctc scc star_aci)
    done
qed

lemma build_csr_in_pad_rule:
  assumes lk: "m \<le> length keys" and bd: "\<forall>i<m. keys ! i < vcount" and ag: "\<forall>i<m. keys ! i = snd_list ! i"
  shows "<ka \<mapsto>\<^sub>a keys * c \<mapsto>\<^sub>a replicate vcount 0 * i_lo \<mapsto>\<^sub>a replicate vcount 0 * i_hi \<mapsto>\<^sub>a replicate vcount 0 * i_cur \<mapsto>\<^sub>a replicate vcount 0 * i_edges \<mapsto>\<^sub>a replicate m 0>
     build_csr_imp ka c i_lo i_hi i_cur i_edges m vcount
   <\<lambda>_. ka \<mapsto>\<^sub>a keys * c \<mapsto>\<^sub>a ct vcount ((!) snd_list) [0..<m] * csr_assn in_csr (i_edges, i_lo, i_hi, i_cur)>"
proof -
  have ctc: "ct vcount ((!) keys) [0..<m] = ct vcount ((!) snd_list) [0..<m]"
    by (rule ct_key_cong) (use ag in auto)
  have scc: "scatter_edges vcount ((!) keys) [0..<m] 0 = scatter_edges vcount ((!) snd_list) [0..<m] 0"
    by (rule scatter_edges_key_cong) (use ag in auto)
  show ?thesis
    apply (sep_auto heap: build_csr_imp_rule[OF lk bd] simp: csr_assn_def in_csr_edges in_csr_lo in_csr_hi in_csr_cur)
    apply (simp add: ctc scc star_aci)
    done
qed

text \<open>The built CSRs have the vertex-count size that @{const graph_assn_c} demands, so @{const csr_assn}
      of @{const out_csr} / @{const in_csr} upgrades to @{const graph_assn_c}.\<close>
lemma csr_n_out_csr: "csr_n out_csr = vcount"
  by (simp add: csr_n_def out_csr_cur psums_length)
lemma csr_n_in_csr: "csr_n in_csr = vcount"
  by (simp add: csr_n_def in_csr_cur psums_length)

text \<open>Pass A reads the flow only at the real edges @{term \<open>[0..<m]\<close>}, so it is insensitive to the
      padding of the working flow array beyond @{term m}: running it on @{term \<open>acyc_flow @ (padding)\<close>}
      gives the same result — hence the same @{const free_out_edges} / @{const free_out_hi} /
      @{const free_in_edges} / @{const free_in_hi} / @{const edge_state} — as on @{const acyc_flow}.\<close>
lemma passA_flow_cong:
  assumes "\<forall>e<m. fl ! e = fl' ! e" shows "passA fl = passA fl'"
  unfolding passA_def
proof (rule fold_cong[OF refl refl])
  fix e assume "e \<in> set [0..<m]"
  hence "fl ! e = fl' ! e" using assms by simp
  thus "passA_step fl e = passA_step fl' e" by (simp add: passA_step_def)
qed

text \<open>The count / prefix-sum passes read the count array only on @{term \<open>[0..<nn]\<close>}, so they tolerate an
      \<^emph>\<open>over-long\<close> count array — as arises when @{const solve_imp} reuses the length-@{term \<open>Suc vcount\<close>}
      array @{term cnt} (later the DFS stack @{term di_sic}) as the CSR builder's count store.\<close>
lemma fold_upd_take:
  "take nn (fold (\<lambda>i cc. cc[key i := Suc (cc ! key i)]) es xs)
     = fold (\<lambda>i cc. cc[key i := Suc (cc ! key i)]) es (take nn xs)"
proof (induction es arbitrary: xs)
  case Nil thus ?case by simp
next
  case (Cons e es)
  have "take nn (xs[key e := Suc (xs ! key e)]) = (take nn xs)[key e := Suc (take nn xs ! key e)]"
  proof (cases "key e < nn")
    case True thus ?thesis by (simp add: take_update_swap)
  next
    case False
    hence "length (take nn xs) \<le> key e" by (simp add: min_def)
    thus ?thesis by (simp add: take_update_swap list_update_beyond)
  qed
  thus ?case using Cons.IH[of "xs[key e := Suc (xs ! key e)]"] by simp
qed

lemma count_fold_length: "length (fold (\<lambda>i cc. cc[key i := Suc (cc ! key i)]) es xs) = length xs"
  by (induction es arbitrary: xs) auto

lemma csr_psum_imp_over:
  "v \<le> nn \<Longrightarrow> nn \<le> length cs \<Longrightarrow> length lo0 = nn \<Longrightarrow> length hi0 = nn \<Longrightarrow> length cur0 = nn \<Longrightarrow>
   <c \<mapsto>\<^sub>a cs * la \<mapsto>\<^sub>a lo0 * ha \<mapsto>\<^sub>a hi0 * cua \<mapsto>\<^sub>a cur0>
     csr_psum_imp c la ha cua v acc nn
   <\<lambda>_. c \<mapsto>\<^sub>a cs
        * la \<mapsto>\<^sub>a (take v lo0 @ butlast (psums acc (drop v (take nn cs))))
        * ha \<mapsto>\<^sub>a (take v hi0 @ tl (psums acc (drop v (take nn cs))))
        * cua \<mapsto>\<^sub>a (take v cur0 @ butlast (psums acc (drop v (take nn cs))))>"
proof (induction "nn - v" arbitrary: v acc lo0 hi0 cur0)
  case 0
  then have vn: "v = nn" by simp
  show ?case using 0 vn
    by (subst csr_psum_imp.simps) (sep_auto simp: psums_length)
next
  case (Suc d)
  from Suc.hyps(2) Suc.prems(1) have vn: "v < nn" by simp
  have vlen: "v < length cs" using vn Suc.prems(2) by simp
  have vt: "v < length (take nn cs)" using vn Suc.prems(2) by simp
  have csv: "cs ! v = take nn cs ! v" using vn by simp
  have d': "d = nn - Suc v" using Suc.hyps(2) by simp
  let ?P = "psums (acc + cs ! v) (drop (Suc v) (take nn cs))"
  have step: "<c \<mapsto>\<^sub>a cs * la \<mapsto>\<^sub>a lo0[v := acc] * ha \<mapsto>\<^sub>a hi0[v := acc + cs ! v] * cua \<mapsto>\<^sub>a cur0[v := acc]>
     csr_psum_imp c la ha cua (Suc v) (acc + cs ! v) nn
   <\<lambda>_. c \<mapsto>\<^sub>a cs
        * la \<mapsto>\<^sub>a (take (Suc v) (lo0[v := acc]) @ butlast ?P)
        * ha \<mapsto>\<^sub>a (take (Suc v) (hi0[v := acc + cs ! v]) @ tl ?P)
        * cua \<mapsto>\<^sub>a (take (Suc v) (cur0[v := acc]) @ butlast ?P)>"
    using Suc.hyps(1)[OF d' _ Suc.prems(2), of "lo0[v := acc]" "hi0[v := acc + cs ! v]" "cur0[v := acc]" "acc + cs ! v"] vn Suc.prems(3,4,5) by simp
  have pd: "psums acc (drop v (take nn cs)) = acc # ?P" using psums_Cons_drop[OF vt] csv by simp
  have la_eq: "(take (Suc v) lo0)[v := acc] @ butlast ?P = take v lo0 @ butlast (psums acc (drop v (take nn cs)))"
    using vn Suc.prems(3) by (simp add: pd take_Suc_conv_app_nth list_update_append)
  have cu_eq: "(take (Suc v) cur0)[v := acc] @ butlast ?P = take v cur0 @ butlast (psums acc (drop v (take nn cs)))"
    using vn Suc.prems(5) by (simp add: pd take_Suc_conv_app_nth list_update_append)
  have hi_eq: "(take (Suc v) hi0)[v := acc + cs ! v] @ tl ?P = take v hi0 @ tl (psums acc (drop v (take nn cs)))"
    using vn Suc.prems(4) by (simp add: pd take_Suc_conv_app_nth list_update_append psums_hd_tl[symmetric])
  show ?case
    using vn vlen Suc.prems(2,3,4,5)
    apply (subst csr_psum_imp.simps)
    by (sep_auto heap: step simp: la_eq cu_eq hi_eq)
qed

lemma build_csr_imp_over_c:
  assumes mk: "m \<le> length keys" and kn: "\<forall>i<m. keys ! i < nn" and lc: "nn \<le> lenc"
  shows "<ka \<mapsto>\<^sub>a keys * c \<mapsto>\<^sub>a replicate lenc (0::nat) * lo \<mapsto>\<^sub>a replicate nn (0::nat) * hi \<mapsto>\<^sub>a replicate nn (0::nat) * cur \<mapsto>\<^sub>a replicate nn (0::nat) * ea \<mapsto>\<^sub>a replicate m (0::nat)>
     build_csr_imp ka c lo hi cur ea m nn
   <\<lambda>_. ka \<mapsto>\<^sub>a keys * c \<mapsto>\<^sub>a fold (\<lambda>i cc. cc[keys ! i := Suc (cc ! (keys ! i))]) [0..<m] (replicate lenc 0)
        * lo \<mapsto>\<^sub>a butlast (psums 0 (ct nn (nth keys) [0..<m]))
        * hi \<mapsto>\<^sub>a tl (psums 0 (ct nn (nth keys) [0..<m]))
        * cur \<mapsto>\<^sub>a butlast (psums 0 (ct nn (nth keys) [0..<m]))
        * ea \<mapsto>\<^sub>a scatter_edges nn (nth keys) [0..<m] 0>"
proof -
  let ?ct = "ct nn (nth keys) [0..<m]"
  let ?lo = "butlast (psums 0 ?ct)"
  let ?cto = "fold (\<lambda>i cc. cc[keys ! i := Suc (cc ! (keys ! i))]) [0..<m] (replicate lenc 0)"
  have takeq: "take nn ?cto = ?ct"
    using fold_upd_take[of nn "(!) keys" "[0..<m]" "replicate lenc 0"] lc by (simp add: ct_def min_def)
  have lenq: "nn \<le> length ?cto" using lc by (simp add: count_fold_length)
  have si: "sc_inv nn (nth keys) [0..<m] (replicate m 0) ?lo [0..<0]"
    using scatter_init_inv[of nn "nth keys" "[0..<m]" 0] by simp
  have p1: "<ka \<mapsto>\<^sub>a keys * c \<mapsto>\<^sub>a replicate lenc 0> csr_count_imp ka c 0 m <\<lambda>_. ka \<mapsto>\<^sub>a keys * c \<mapsto>\<^sub>a ?cto>"
    by (rule csr_count_imp_rule) (use mk kn lc in auto)
  have p2: "<c \<mapsto>\<^sub>a ?cto * lo \<mapsto>\<^sub>a replicate nn 0 * hi \<mapsto>\<^sub>a replicate nn 0 * cur \<mapsto>\<^sub>a replicate nn 0>
              csr_psum_imp c lo hi cur 0 0 nn
            <\<lambda>_. c \<mapsto>\<^sub>a ?cto * lo \<mapsto>\<^sub>a ?lo * hi \<mapsto>\<^sub>a tl (psums 0 ?ct) * cur \<mapsto>\<^sub>a ?lo>"
    using csr_psum_imp_over[of 0 nn ?cto "replicate nn 0" "replicate nn 0" "replicate nn 0" c lo hi cur 0] lenq takeq
    by simp
  have p3: "<ka \<mapsto>\<^sub>a keys * ea \<mapsto>\<^sub>a replicate m 0 * cur \<mapsto>\<^sub>a ?lo>
              csr_scatter_imp ka ea cur 0 m
            <\<lambda>_. ka \<mapsto>\<^sub>a keys * ea \<mapsto>\<^sub>a scatter_edges nn (nth keys) [0..<m] 0
                 * cur \<mapsto>\<^sub>a snd (fold (scatter_body (nth keys)) [0..<m] (replicate m 0, ?lo))>"
    using csr_scatter_imp_rule[of 0 m m keys "replicate m 0" ?lo nn ka ea cur] mk kn si
    by (simp add: scatter_edges_def psums_length)
  have p4: "\<And>ys. length ys = nn \<Longrightarrow> <lo \<mapsto>\<^sub>a ?lo * cur \<mapsto>\<^sub>a ys> arr_copy_imp lo cur 0 nn <\<lambda>_. lo \<mapsto>\<^sub>a ?lo * cur \<mapsto>\<^sub>a ?lo>"
  proof -
    fix ys :: "nat list" assume l: "length ys = nn"
    show "<lo \<mapsto>\<^sub>a ?lo * cur \<mapsto>\<^sub>a ys> arr_copy_imp lo cur 0 nn <\<lambda>_. lo \<mapsto>\<^sub>a ?lo * cur \<mapsto>\<^sub>a ?lo>"
      using arr_copy_imp_rule[of 0 nn ?lo ys lo cur] l by (simp add: psums_length)
  qed
  show ?thesis
    unfolding build_csr_imp_def
    by (sep_auto heap: p1 p2 p3 p4 simp: fold_scatter_snd_length psums_length)
qed

text \<open>Combined padded builders: an over-long key array (agreeing with @{term fst_list}/@{term snd_list}
      on @{term \<open>[0..<m]\<close>}) and an over-long count array still establish @{const csr_assn} of
      @{const out_csr}/@{const in_csr} — exactly the shape @{const solve_imp} produces.\<close>
lemma build_csr_out_pad_over_c:
  assumes mk: "m \<le> length keys" and bd: "\<forall>i<m. keys ! i < vcount" and ag: "\<forall>i<m. keys ! i = fst_list ! i" and lc: "vcount \<le> lenc"
  shows "<ka \<mapsto>\<^sub>a keys * c \<mapsto>\<^sub>a replicate lenc 0 * o_lo \<mapsto>\<^sub>a replicate vcount 0 * o_hi \<mapsto>\<^sub>a replicate vcount 0 * o_cur \<mapsto>\<^sub>a replicate vcount 0 * o_edges \<mapsto>\<^sub>a replicate m 0>
     build_csr_imp ka c o_lo o_hi o_cur o_edges m vcount
   <\<lambda>_. ka \<mapsto>\<^sub>a keys * c \<mapsto>\<^sub>a fold (\<lambda>i cc. cc[keys ! i := Suc (cc ! (keys ! i))]) [0..<m] (replicate lenc 0) * csr_assn out_csr (o_edges, o_lo, o_hi, o_cur)>"
proof -
  have ctc: "ct vcount ((!) keys) [0..<m] = ct vcount ((!) fst_list) [0..<m]"
    by (rule ct_key_cong) (use ag in auto)
  have scc: "scatter_edges vcount ((!) keys) [0..<m] 0 = scatter_edges vcount ((!) fst_list) [0..<m] 0"
    by (rule scatter_edges_key_cong) (use ag in auto)
  show ?thesis
    apply (sep_auto heap: build_csr_imp_over_c[OF mk bd lc] simp: csr_assn_def out_csr_edges out_csr_lo out_csr_hi out_csr_cur)
    apply (simp add: ctc scc star_aci)
    done
qed

lemma build_csr_in_pad_over_c:
  assumes mk: "m \<le> length keys" and bd: "\<forall>i<m. keys ! i < vcount" and ag: "\<forall>i<m. keys ! i = snd_list ! i" and lc: "vcount \<le> lenc"
  shows "<ka \<mapsto>\<^sub>a keys * c \<mapsto>\<^sub>a replicate lenc 0 * i_lo \<mapsto>\<^sub>a replicate vcount 0 * i_hi \<mapsto>\<^sub>a replicate vcount 0 * i_cur \<mapsto>\<^sub>a replicate vcount 0 * i_edges \<mapsto>\<^sub>a replicate m 0>
     build_csr_imp ka c i_lo i_hi i_cur i_edges m vcount
   <\<lambda>_. ka \<mapsto>\<^sub>a keys * c \<mapsto>\<^sub>a fold (\<lambda>i cc. cc[keys ! i := Suc (cc ! (keys ! i))]) [0..<m] (replicate lenc 0) * csr_assn in_csr (i_edges, i_lo, i_hi, i_cur)>"
proof -
  have ctc: "ct vcount ((!) keys) [0..<m] = ct vcount ((!) snd_list) [0..<m]"
    by (rule ct_key_cong) (use ag in auto)
  have scc: "scatter_edges vcount ((!) keys) [0..<m] 0 = scatter_edges vcount ((!) snd_list) [0..<m] 0"
    by (rule scatter_edges_key_cong) (use ag in auto)
  show ?thesis
    apply (sep_auto heap: build_csr_imp_over_c[OF mk bd lc] simp: csr_assn_def in_csr_edges in_csr_lo in_csr_hi in_csr_cur)
    apply (simp add: ctc scc star_aci)
    done
qed

text \<open>Exit-bridge core: the six tree arrays produced by @{const build_tree} realise the abstract
      arborescence @{const Sarb} as an @{const ndtree_assn} over @{term Varb}.  The domain / range
      structure comes from @{thm Sarb_struct}; the per-vertex value correspondence from
      @{thm Sarb_sel} together with the @{const Sprnt} / @{const Sthrd} / @{const Srvth} definitions
      (the root's parent slot is @{term 0} by @{thm build_tree_root_prnt}); the length bounds from
      @{thm bt_sized}.  The auxiliary array is unconstrained apart from its length.\<close>
lemma ndtree_assn_Sarb:
  assumes la: "Suc vcount \<le> length auxa"
  shows "prnt_impl Ti \<mapsto>\<^sub>a ds_prnt (build_tree acyc_flow) * thrd_impl Ti \<mapsto>\<^sub>a ds_thrd (build_tree acyc_flow) *
   rvth_impl Ti \<mapsto>\<^sub>a ds_rvth (build_tree acyc_flow) * lsuc_impl Ti \<mapsto>\<^sub>a ds_lsuc (build_tree acyc_flow) *
   snum_impl Ti \<mapsto>\<^sub>a ds_snum (build_tree acyc_flow) * aux_impl Ti \<mapsto>\<^sub>a auxa
   \<Longrightarrow>\<^sub>A ndtree_assn Varb Sarb Ti"
proof -
  note lens = bt_sized[unfolded dfs_sized_def]
  have vsub: "Varb \<subseteq> {0..<Suc vcount}" by (auto simp: Varb_def Vseen_def)
  have vaux: "Varb \<subseteq> {0..<length auxa}" using vsub la by auto
  have prnt_cond: "\<forall>v\<in>Varb. (\<forall>u. prnt Sarb v = Some u \<longrightarrow> ds_prnt (build_tree acyc_flow) ! v = u) \<and> (prnt Sarb v = None \<longrightarrow> ds_prnt (build_tree acyc_flow) ! v = 0)"
    by (auto simp: Sarb_sel Sprnt_def build_tree_root_prnt Varb_def Vseen_def)
  have thrd_cond: "\<forall>v\<in>Varb. (\<forall>u. thrd Sarb v = Some u \<longrightarrow> ds_thrd (build_tree acyc_flow) ! v = u) \<and> (thrd Sarb v = None \<longrightarrow> ds_thrd (build_tree acyc_flow) ! v = 0)"
    by (auto simp: Sarb_sel Sthrd_def)
  have rvth_cond: "\<forall>v\<in>Varb. (\<forall>u. rvth Sarb v = Some u \<longrightarrow> ds_rvth (build_tree acyc_flow) ! v = u) \<and> (rvth Sarb v = None \<longrightarrow> ds_rvth (build_tree acyc_flow) ! v = 0)"
    by (auto simp: Sarb_sel Srvth_def)
  have ls_cond: "\<forall>v\<in>Varb. lsuc Sarb v = ds_lsuc (build_tree acyc_flow) ! v \<and> snum Sarb v = ds_snum (build_tree acyc_flow) ! v"
    by (simp add: Sarb_sel)
  have lsuc_in: "\<forall>v\<in>Varb. ds_lsuc (build_tree acyc_flow) ! v \<in> Varb" using Sarb_lsuc_in by (simp add: Sarb_sel)
  show ?thesis
    unfolding ndtree_assn_def
    apply (rule ent_ex_postI[where x="ds_prnt (build_tree acyc_flow)"])
    apply (rule ent_ex_postI[where x="ds_thrd (build_tree acyc_flow)"])
    apply (rule ent_ex_postI[where x="ds_rvth (build_tree acyc_flow)"])
    apply (rule ent_ex_postI[where x="ds_lsuc (build_tree acyc_flow)"])
    apply (rule ent_ex_postI[where x="ds_snum (build_tree acyc_flow)"])
    apply (rule ent_ex_postI[where x="auxa"])
    apply (sep_auto simp: zero_notin_Varb Sarb_struct vsub vaux lens prnt_cond thrd_cond rvth_cond ls_cond lsuc_in)
    done
qed

text \<open>@{const solve_imp} hands the tree builder freshly-allocated arrays, so the DFS state's
      @{term ds_snum} is all-zero and @{term ds_prev} is @{term 0} — one short of @{const dfs_init}
      (which seeds the snum entry at the root to @{term \<open>1::nat\<close>} and @{term ds_prev} to @{term vcount}).  The tree builder itself
      performs exactly those seed writes as its first action, so it also refines @{const build_tree} from
      this \<^emph>\<open>raw\<close> pre-seed state \<open>dfs_raw\<close>.\<close>
definition dfs_raw :: "'n dfs_state" where
  "dfs_raw = dfs_init\<lparr>ds_snum := replicate (Suc vcount) 0, ds_prev := 0\<rparr>"

lemma raw_seed:
  "dfs_raw\<lparr>ds_snum := (ds_snum dfs_raw)[vcount := Suc 0], ds_prev := vcount, ds_nxt := 0, ds_stk := []\<rparr> = dfs_init"
  by (simp add: dfs_raw_def dfs_init_def)

lemma build_tree_imp_raw_rule:
  assumes nvc: "n < vcount" and lim: "Suc vcount \<le> length imbalance"
    and lol: "vcount \<le> length out_lo" and lil: "vcount \<le> length in_lo"
    and loh: "vcount \<le> length out_hi" and lih: "vcount \<le> length in_hi"
  shows "<dfs_rel fl0 es0 (free_out_edges acyc_flow) (free_out_hi acyc_flow) (free_in_edges acyc_flow) (free_in_hi acyc_flow) st dfs_raw * imb_arr \<mapsto>\<^sub>a imbalance * ofh_arr \<mapsto>\<^sub>a out_hi * ifh_arr \<mapsto>\<^sub>a in_hi>
           build_tree_imp st imb_arr ofh_arr ifh_arr m vcount n
         <\<lambda>_. dfs_rel fl0 es0 (free_out_edges acyc_flow) (free_out_hi acyc_flow) (free_in_edges acyc_flow) (free_in_hi acyc_flow) st (build_tree acyc_flow) * imb_arr \<mapsto>\<^sub>a imbalance * ofh_arr \<mapsto>\<^sub>a out_hi * ifh_arr \<mapsto>\<^sub>a in_hi>"
proof -
  have allvc: "\<forall>w\<in>set vs_list. w < vcount" using nvc by (auto simp: vs_list_def)
  have pre0: "dfs_inv acyc_flow dfs_init \<and> ds_stk dfs_init = []" using dfs_init_inv by (simp add: dfs_init_def)
  have wsd1: "dfs_wf (phase1 acyc_flow dfs_init) \<and> dfs_sized (phase1 acyc_flow dfs_init) \<and> dref_inv (phase1 acyc_flow dfs_init)"
    using fold_phase1_step_wsd[OF dfs_wf_dfs_init dfs_init_sized dref_inv_dfs_init allvc] by (simp add: phase1_def)
  have a1: "art_len (phase1 acyc_flow dfs_init)" using phase1_art_len[OF pre0 dfs_init_art_len] .
  have p1a: "length (ds_afst (phase1 acyc_flow dfs_init)) = length vs_list \<and> length (ds_asnd (phase1 acyc_flow dfs_init)) = length vs_list \<and> length (ds_acap (phase1 acyc_flow dfs_init)) = length vs_list \<and> length (ds_aflw (phase1 acyc_flow dfs_init)) = length vs_list \<and> length (ds_aest (phase1 acyc_flow dfs_init)) = length vs_list"
    using a1 by (simp add: art_len_def)
  have bt_nxt: "ds_nxt (build_tree acyc_flow) = ds_nxt (phase2 acyc_flow (phase1 acyc_flow dfs_init))" by (simp add: build_tree_def Let_def)
  have nxt_le: "ds_nxt (phase2 acyc_flow (phase1 acyc_flow dfs_init)) \<le> length vs_list" using build_tree_nxt_le bt_nxt by simp
  have phase1_fold_eq: "fold (phase1_step acyc_flow) [Suc 0..<Suc n] dfs_init = phase1 acyc_flow dfs_init" by (simp add: phase1_def vs_list_def)
  have phase2_fold_eq: "fold (phase2_step acyc_flow) [Suc 0..<Suc n] (phase1 acyc_flow dfs_init) = phase2 acyc_flow (phase1 acyc_flow dfs_init)" by (simp add: phase2_def vs_list_def)
  have f1: "ds_nxt (fold (phase2_step acyc_flow) [Suc 0..<Suc n] (phase1 acyc_flow dfs_init)) \<le> length (ds_afst (phase1 acyc_flow dfs_init))" using nxt_le p1a unfolding phase2_fold_eq by simp
  have f2: "ds_nxt (fold (phase2_step acyc_flow) [Suc 0..<Suc n] (phase1 acyc_flow dfs_init)) \<le> length (ds_asnd (phase1 acyc_flow dfs_init))" using nxt_le p1a unfolding phase2_fold_eq by simp
  have f3: "ds_nxt (fold (phase2_step acyc_flow) [Suc 0..<Suc n] (phase1 acyc_flow dfs_init)) \<le> length (ds_acap (phase1 acyc_flow dfs_init))" using nxt_le p1a unfolding phase2_fold_eq by simp
  have f4: "ds_nxt (fold (phase2_step acyc_flow) [Suc 0..<Suc n] (phase1 acyc_flow dfs_init)) \<le> length (ds_aflw (phase1 acyc_flow dfs_init))" using nxt_le p1a unfolding phase2_fold_eq by simp
  have f5: "ds_nxt (fold (phase2_step acyc_flow) [Suc 0..<Suc n] (phase1 acyc_flow dfs_init)) \<le> length (ds_aest (phase1 acyc_flow dfs_init))" using nxt_le p1a unfolding phase2_fold_eq by simp
  have lim2: "vcount \<le> length imbalance" using lim by simp
  have c1: "ds_nxt dfs_init + (Suc n - Suc 0) \<le> length (ds_afst dfs_init)" by (simp add: dfs_init_def length_vs_list)
  have c2: "ds_nxt dfs_init + (Suc n - Suc 0) \<le> length (ds_asnd dfs_init)" by (simp add: dfs_init_def length_vs_list)
  have c3: "ds_nxt dfs_init + (Suc n - Suc 0) \<le> length (ds_acap dfs_init)" by (simp add: dfs_init_def length_vs_list)
  have c4: "ds_nxt dfs_init + (Suc n - Suc 0) \<le> length (ds_aflw dfs_init)" by (simp add: dfs_init_def length_vs_list)
  have c5: "ds_nxt dfs_init + (Suc n - Suc 0) \<le> length (ds_aest dfs_init)" by (simp add: dfs_init_def length_vs_list)
  have szp2: "dfs_sized (phase2 acyc_flow (phase1 acyc_flow dfs_init))"
    using fold_phase2_step_wsd[OF conjunct1[OF wsd1] conjunct1[OF conjunct2[OF wsd1]] conjunct2[OF conjunct2[OF wsd1]] allvc] by (simp add: phase2_def)
  have lsuc_len: "vcount < length (ds_lsuc (phase2 acyc_flow (phase1 acyc_flow dfs_init)))" using szp2 by (simp add: dfs_sized_def)
  have bt_eq: "(phase2 acyc_flow (phase1 acyc_flow dfs_init))\<lparr>ds_lsuc := (ds_lsuc (phase2 acyc_flow (phase1 acyc_flow dfs_init)))[vcount := ds_prev (phase2 acyc_flow (phase1 acyc_flow dfs_init))]\<rparr> = build_tree acyc_flow"
    by (simp add: build_tree_def Let_def)
  have snum_len_raw: "vcount < length (ds_snum dfs_raw)" by (simp add: dfs_raw_def del: replicate_Suc)
  have phase1_triple: "<dfs_rel fl0 es0 (free_out_edges acyc_flow) (free_out_hi acyc_flow) (free_in_edges acyc_flow) (free_in_hi acyc_flow) st dfs_init * imb_arr \<mapsto>\<^sub>a imbalance> phase1_imp st imb_arr m vcount (Suc 0) n <\<lambda>_. dfs_rel fl0 es0 (free_out_edges acyc_flow) (free_out_hi acyc_flow) (free_in_edges acyc_flow) (free_in_hi acyc_flow) st (phase1 acyc_flow dfs_init) * imb_arr \<mapsto>\<^sub>a imbalance>"
    by (rule phase1_imp_rule[where fl=acyc_flow, OF dfs_wf_dfs_init dfs_init_sized dref_inv_dfs_init c1 c2 c3 c4 c5 nvc lim lol lil, unfolded phase1_fold_eq])
  have phase2_triple: "<dfs_rel fl0 es0 (free_out_edges acyc_flow) (free_out_hi acyc_flow) (free_in_edges acyc_flow) (free_in_hi acyc_flow) st (phase1 acyc_flow dfs_init) * imb_arr \<mapsto>\<^sub>a imbalance * ofh_arr \<mapsto>\<^sub>a out_hi * ifh_arr \<mapsto>\<^sub>a in_hi> phase2_imp st imb_arr ofh_arr ifh_arr m vcount (Suc 0) n <\<lambda>_. dfs_rel fl0 es0 (free_out_edges acyc_flow) (free_out_hi acyc_flow) (free_in_edges acyc_flow) (free_in_hi acyc_flow) st (phase2 acyc_flow (phase1 acyc_flow dfs_init)) * imb_arr \<mapsto>\<^sub>a imbalance * ofh_arr \<mapsto>\<^sub>a out_hi * ifh_arr \<mapsto>\<^sub>a in_hi>"
    by (rule phase2_imp_rule[where fl=acyc_flow, OF conjunct1[OF wsd1] conjunct1[OF conjunct2[OF wsd1]] conjunct2[OF conjunct2[OF wsd1]] f1 f2 f3 f4 f5 nvc lim2 lol lil loh lih, unfolded phase2_fold_eq])
  show ?thesis
    unfolding build_tree_imp_def
    apply (sep_auto heap: dfs_rel_snum_upd[OF snum_len_raw] dfs_rel_prev_upd dfs_rel_nxt_upd0 dfs_rel_sp_upd0 simp: raw_seed)
    apply (rule wlp_apply_ht[OF _ _ phase1_triple, where F="ofh_arr \<mapsto>\<^sub>a out_hi * ifh_arr \<mapsto>\<^sub>a in_hi * true"])
      apply assumption
     apply sep_auto
    apply (rule wlp_apply_ht[OF _ _ phase2_triple, where F="true"])
      apply assumption
     apply sep_auto
    apply (sep_auto heap: dfs_rel_prev_get dfs_rel_lsuc_upd[OF lsuc_len] simp: bt_eq)
    done
qed

text \<open>Monolith support: the padded input arrays agree with the functional lists on the real edge range,
      and the fst-count fold leaves the artificial-root slot @{term \<open>Suc n\<close>} at @{term 0} (so the shared
      count array @{term cnt} is fully re-zeroed by @{const solve_imp}'s @{const arr_fill_imp} between the
      two CSR builds).\<close>
lemma fst_pad_keys: "\<forall>i<m. (fst_list @ replicate n 0) ! i = fst_list ! i" by (auto simp: nth_append length_fst_list_m)
lemma snd_pad_keys: "\<forall>i<m. (snd_list @ replicate n 0) ! i = snd_list ! i" by (auto simp: nth_append length_snd_list_m)
lemma fst_pad_bd: "\<forall>i<m. (fst_list @ replicate n 0) ! i < vcount" using keys_fst_lt fst_pad_keys by auto
lemma snd_pad_bd: "\<forall>i<m. (snd_list @ replicate n 0) ! i < vcount" using keys_snd_lt snd_pad_keys by auto
lemma fst_pad_mk: "m \<le> length (fst_list @ replicate n 0)" by (simp add: length_fst_list_m)
lemma snd_pad_mk: "m \<le> length (snd_list @ replicate n 0)" by (simp add: length_snd_list_m)
lemma vcount_le_V: "vcount \<le> Suc (Suc n)" by (simp add: vcount_eq)

lemma fold_upd_nth_other:
  "\<forall>i\<in>set es. key i \<noteq> j \<Longrightarrow> (fold (\<lambda>i cc. cc[key i := Suc (cc ! (key i))]) es xs) ! j = xs ! j"
  by (induction es arbitrary: xs) (auto simp: nth_list_update_neq)

lemma fst_cto_vcount:
  "(fold (\<lambda>i cc. cc[fst_list ! i := Suc (cc ! (fst_list ! i))]) [0..<m] (replicate (Suc (Suc n)) 0)) ! (Suc n) = 0"
proof -
  have "\<forall>i\<in>set [0..<m]. fst_list ! i \<noteq> Suc n" using keys_fst_lt by (auto simp: vcount_eq)
  from fold_upd_nth_other[OF this, of "replicate (Suc (Suc n)) 0"] show ?thesis by (simp del: replicate_Suc)
qed

text \<open>CSR count-array reset: after building the out-CSR the count array holds the fst-degrees; the
      subsequent @{const arr_fill_imp} zeroes indices @{term \<open>[0..<vcount]\<close>} and the reserved root
      cell @{term vcount} is already @{term 0} (no real edge points at the root), so the array is
      back to @{term \<open>replicate (Suc (Suc n)) 0\<close>} — ready to build the in-CSR.\<close>
lemma arr_fill_to_replicate:
  assumes len: "length ys = Suc NN" and lastx: "ys ! NN = x"
  shows "take 0 ys @ replicate (NN - 0) x @ drop NN ys = replicate (Suc NN) x"
proof -
  have "drop NN ys = [ys ! NN]" using Cons_nth_drop_Suc[of NN ys] len by simp
  then show ?thesis using lastx by (simp add: replicate_append_same)
qed

lemma fst_cto_pad_len:
  "length (fold (\<lambda>i cc. list_update cc ((fst_list @ replicate n 0) ! i)
                          (Suc (cc ! ((fst_list @ replicate n 0) ! i)))) [0..<m] (0 # 0 # replicate n 0))
   = Suc (Suc n)"
  by (simp add: count_fold_length)

lemma fst_cto_pad_nth:
  "(fold (\<lambda>i cc. list_update cc ((fst_list @ replicate n 0) ! i)
                   (Suc (cc ! ((fst_list @ replicate n 0) ! i)))) [0..<m] (0 # 0 # replicate n 0)) ! (Suc n)
   = 0"
proof -
  have nkey: "\<forall>i\<in>set [0..<m]. (fst_list @ replicate n 0) ! i \<noteq> Suc n"
    using fst_pad_bd by (auto simp: vcount_eq)
  have e1: "(fold (\<lambda>i cc. list_update cc ((fst_list @ replicate n 0) ! i)
                   (Suc (cc ! ((fst_list @ replicate n 0) ! i)))) [0..<m] (0 # 0 # replicate n 0)) ! (Suc n)
          = (0 # 0 # replicate n 0) ! Suc n"
    by (rule fold_upd_nth_other[OF nkey])
  have x0: "(0 # 0 # replicate n 0) ! Suc n = 0"
  proof -
    have "Suc n < length (0 # 0 # replicate n 0)" by simp
    then have m: "(0 # 0 # replicate n 0) ! Suc n \<in> set (0 # 0 # replicate n 0)" by (rule nth_mem)
    have "set (0 # 0 # replicate n 0) \<subseteq> {0}" by auto
    with m show ?thesis by auto
  qed
  show ?thesis by (simp only: e1 x0)
qed

lemma fst_cto_pad_drop:
  "drop (Suc n) (fold (\<lambda>i cc. list_update cc ((fst_list @ replicate n 0) ! i)
                        (Suc (cc ! ((fst_list @ replicate n 0) ! i)))) [0..<m] (0 # 0 # replicate n 0)) = [0]"
proof -
  let ?F = "fold (\<lambda>i cc. list_update cc ((fst_list @ replicate n 0) ! i)
                        (Suc (cc ! ((fst_list @ replicate n 0) ! i)))) [0..<m] (0 # 0 # replicate n 0)"
  have "drop (Suc n) ?F = [?F ! (Suc n)]"
    using Cons_nth_drop_Suc[of "Suc n" ?F] fst_cto_pad_len by simp
  then show ?thesis using fst_cto_pad_nth by simp
qed

text \<open>The acyclifier phase of @{const solve_imp}, packaged as one Hoare triple over the concrete
      padded arrays it operates on.  It folds the raw stores into the abstract assertions the
      acyclifier refinement consumes (@{const flow_assn_m} / @{const state_assn_v} /
      @{const graph_assn_c} / @{const vtx_assn}) and discharges the multigraph side-conditions, so the
      capstone can apply it as a black box: the boolean verdict tracks @{term \<open>make_acyclic flow_list = None\<close>}.\<close>
lemma make_acyclic_solve_triple:
  "<fh \<mapsto>\<^sub>a (take m flow_list @ replicate n 0) * sh \<mapsto>\<^sub>a (Unseen # Unseen # replicate n Unseen) *
    oe \<mapsto>\<^sub>a csr_edges out_csr * olo \<mapsto>\<^sub>a csr_lo out_csr * ohi \<mapsto>\<^sub>a csr_hi out_csr * ocur \<mapsto>\<^sub>a csr_cur out_csr *
    ie \<mapsto>\<^sub>a csr_edges in_csr * ilo \<mapsto>\<^sub>a csr_lo in_csr * ihi \<mapsto>\<^sub>a csr_hi in_csr * icur \<mapsto>\<^sub>a csr_cur in_csr *
    vl \<mapsto>\<^sub>a edged_vs_list * pr \<mapsto>\<^sub>r 0 *
    cap_arr \<mapsto>\<^sub>a (capacity_list @ replicate n 0) * cost_arr \<mapsto>\<^sub>a cost_list *
    fst_arr \<mapsto>\<^sub>a (fst_list @ replicate n 0) * snd_arr \<mapsto>\<^sub>a (snd_list @ replicate n 0) *
    vst \<mapsto>\<^sub>a (0 # 0 # replicate n 0) * est \<mapsto>\<^sub>a (0 # 0 # replicate n 0) * dst \<mapsto>\<^sub>a (False # False # replicate n False)>
   make_acyclic_prog cap_arr cost_arr fst_arr snd_arr fh sh (oe, olo, ohi, ocur) (ie, ilo, ihi, icur) (vl, pr) vst est dst
   <\<lambda>r. \<exists>\<^sub>A f' cur_o cur_i. flow_assn_m f' fh *
        oe \<mapsto>\<^sub>a csr_edges out_csr * olo \<mapsto>\<^sub>a csr_lo out_csr * ohi \<mapsto>\<^sub>a csr_hi out_csr * ocur \<mapsto>\<^sub>a cur_o *
        ie \<mapsto>\<^sub>a csr_edges in_csr * ilo \<mapsto>\<^sub>a csr_lo in_csr * ihi \<mapsto>\<^sub>a csr_hi in_csr * icur \<mapsto>\<^sub>a cur_i *
        (cap_arr \<mapsto>\<^sub>a (capacity_list @ replicate n 0) * cost_arr \<mapsto>\<^sub>a cost_list *
         fst_arr \<mapsto>\<^sub>a (fst_list @ replicate n 0) * snd_arr \<mapsto>\<^sub>a (snd_list @ replicate n 0)) *
        (\<exists>\<^sub>A vl' el' dl'. vst \<mapsto>\<^sub>a vl' * est \<mapsto>\<^sub>a el' * dst \<mapsto>\<^sub>a dl' *
           \<up>(card original_network.\<V> \<le> length vl' \<and> card original_network.\<V> \<le> length el' \<and> card original_network.\<V> \<le> length dl' \<and>
             length vl' = Suc vcount \<and> length el' = Suc vcount \<and> length dl' = Suc vcount)) *
        true *
        \<up>(length cur_o = vcount \<and> length cur_i = vcount \<and> (r \<longleftrightarrow> make_acyclic flow_list = None) \<and> (make_acyclic flow_list = None \<or> make_acyclic flow_list = Some f'))>"
proof -
  have lf: "length flow_list = m" by (simp add: length_flow length_edges)
  have cardn: "card original_network.\<V> \<le> Suc (Suc n)"
  proof -
    have "card original_network.\<V> \<le> card (set vs_list)" using card_mono[OF finite_set V_sub_vs_list] .
    also have "\<dots> \<le> length vs_list" by (rule card_length)
    also have "\<dots> = n" by (rule length_vs_list)
    finally show ?thesis by simp
  qed
  have cardv: "card original_network.\<V> \<le> length (0 # 0 # replicate n (0::nat))" using cardn by simp
  have cardb: "card original_network.\<V> \<le> length (False # False # replicate n False)" using cardn by simp
  have cl_len: "m \<le> length (capacity_list @ replicate n 0)" by (simp add: length_edges)
  have cl_eq: "\<And>e. e < m \<Longrightarrow> (capacity_list @ replicate n 0) ! e = capacity_list ! e"
    by (simp add: nth_append length_edges)
  have co_len: "m \<le> length cost_list" by (simp add: length_cost_list_m)
  have co_eq: "\<And>e. e < m \<Longrightarrow> cost_list ! e = cost_list ! e" by simp
  have fla_len: "m \<le> length (fst_list @ replicate n 0)" by (simp add: length_fst_list_m)
  have fla_eq: "\<And>e. e < m \<Longrightarrow> (fst_list @ replicate n 0) ! e = fst_list ! e"
    by (simp add: nth_append length_fst_list_m)
  have sla_len: "m \<le> length (snd_list @ replicate n 0)" by (simp add: length_snd_list_m)
  have sla_eq: "\<And>e. e < m \<Longrightarrow> (snd_list @ replicate n 0) ! e = snd_list ! e"
    by (simp add: nth_append length_snd_list_m)
  have ent: "fh \<mapsto>\<^sub>a (take m flow_list @ replicate n 0) * sh \<mapsto>\<^sub>a (Unseen # Unseen # replicate n Unseen) *
    oe \<mapsto>\<^sub>a csr_edges out_csr * olo \<mapsto>\<^sub>a csr_lo out_csr * ohi \<mapsto>\<^sub>a csr_hi out_csr * ocur \<mapsto>\<^sub>a csr_cur out_csr *
    ie \<mapsto>\<^sub>a csr_edges in_csr * ilo \<mapsto>\<^sub>a csr_lo in_csr * ihi \<mapsto>\<^sub>a csr_hi in_csr * icur \<mapsto>\<^sub>a csr_cur in_csr *
    vl \<mapsto>\<^sub>a edged_vs_list * pr \<mapsto>\<^sub>r 0 *
    cap_arr \<mapsto>\<^sub>a (capacity_list @ replicate n 0) * cost_arr \<mapsto>\<^sub>a cost_list *
    fst_arr \<mapsto>\<^sub>a (fst_list @ replicate n 0) * snd_arr \<mapsto>\<^sub>a (snd_list @ replicate n 0) *
    vst \<mapsto>\<^sub>a (0 # 0 # replicate n 0) * est \<mapsto>\<^sub>a (0 # 0 # replicate n 0) * dst \<mapsto>\<^sub>a (False # False # replicate n False)
    \<Longrightarrow>\<^sub>A
    flow_assn_m flow_list fh * state_assn_v (replicate vcount Unseen) sh *
    graph_assn_c out_csr (oe, olo, ohi, ocur) * graph_assn_c in_csr (ie, ilo, ihi, icur) *
    vtx_assn \<lparr>vi_list = edged_vs_list, vi_pos = 0\<rparr> (vl, pr) *
    (cap_arr \<mapsto>\<^sub>a (capacity_list @ replicate n 0) * cost_arr \<mapsto>\<^sub>a cost_list *
     fst_arr \<mapsto>\<^sub>a (fst_list @ replicate n 0) * snd_arr \<mapsto>\<^sub>a (snd_list @ replicate n 0)) *
    vst \<mapsto>\<^sub>a (0 # 0 # replicate n 0) * est \<mapsto>\<^sub>a (0 # 0 # replicate n 0) * dst \<mapsto>\<^sub>a (False # False # replicate n False)"
    unfolding flow_assn_m_def state_assn_v_def graph_assn_c_def vtx_assn_def csr_assn_def
    apply (simp add: csr_n_out_csr csr_n_in_csr lf)
    apply (rule ent_ex_postI[where x = "[Unseen]"])
    apply (rule ent_ex_postI[where x = "replicate n 0"])
    apply (sep_auto simp: vcount_eq replicate_append_same)
    done
  show ?thesis
    apply (rule ht_cons_pre[OF ent])
    apply (rule ht_cons_post_prec[OF make_acyclic_prog_rule[OF cl_len cl_eq co_len co_eq fla_len fla_eq sla_len sla_eq lf af_cap_feasible_flow_list cardv cardv cardb]])
    apply (sep_auto simp: graph_assn_c_def csr_assn_def csr_n_def vcount_eq)
    done
qed
text \<open>The arborescence lives inside @{term \<open>{0..<Suc vcount}\<close>}, so the two path buffers the
      network-simplex loop demands (each of length at least @{term \<open>card Varb - 1\<close>}) are covered by the
      DFS stack arrays, whose length is @{term \<open>Suc vcount\<close>}.\<close>
lemma card_Varb_le: "card Varb \<le> Suc vcount"
proof -
  have "Varb \<subseteq> {0..<Suc vcount}" by (auto simp: Varb_def Vseen_def)
  from card_mono[OF _ this] show ?thesis by simp
qed

text \<open>Exit bridge: the raw arrays the tree builder leaves behind — which are literally the components
      of the imperative DFS state — satisfy the precondition @{thm [source] ns_loop_prog_rule} demands.
      The six tree arrays become @{const ndtree_assn} via @{thm ndtree_assn_Sarb}; the flow / potential /
      parent / direction / edge-tag stores are already the loop's own assertions (they are plain
      points-to); the freshly allocated selector triple is @{const init_sel}; and the two DFS stack
      arrays serve as the loop's path buffers.\<close>
lemma ns_pre_ent:
  assumes laux: "Suc vcount \<le> length auxa"
    and lp1: "card Varb - 1 \<le> length svl" and lp2: "card Varb - 1 \<le> length socl"
  shows
  "prnt_impl Ti \<mapsto>\<^sub>a ds_prnt (build_tree acyc_flow) * thrd_impl Ti \<mapsto>\<^sub>a ds_thrd (build_tree acyc_flow) *
   rvth_impl Ti \<mapsto>\<^sub>a ds_rvth (build_tree acyc_flow) * lsuc_impl Ti \<mapsto>\<^sub>a ds_lsuc (build_tree acyc_flow) *
   snum_impl Ti \<mapsto>\<^sub>a ds_snum (build_tree acyc_flow) * aux_impl Ti \<mapsto>\<^sub>a auxa *
   fa \<mapsto>\<^sub>a flowa * pa \<mapsto>\<^sub>a ds_pot (build_tree acyc_flow) *
   pare \<mapsto>\<^sub>a ds_par (build_tree acyc_flow) * dire \<mapsto>\<^sub>a ds_dir (build_tree acyc_flow) *
   esaa \<mapsto>\<^sub>a esa * sarr \<mapsto>\<^sub>a replicate max_candidates 0 * cref \<mapsto>\<^sub>r 0 * lref \<mapsto>\<^sub>r 0 *
   p1 \<mapsto>\<^sub>a svl * p2 \<mapsto>\<^sub>a socl
   \<Longrightarrow>\<^sub>A flow_assn_ns flowa fa * pot_assn_ns (ds_pot (build_tree acyc_flow)) pa *
       ndtree_assn Varb Sarb Ti *
       parent_assn_ns (ds_par (build_tree acyc_flow)) pare *
       dir_assn_ns (ds_dir (build_tree acyc_flow)) dire * es_assn_ns esa esaa *
       sel_assn_ns init_sel (sarr, cref, lref) *
       (\<exists>\<^sub>A l1 l2. p1 \<mapsto>\<^sub>a l1 * p2 \<mapsto>\<^sub>a l2 * \<up>(card Varb - 1 \<le> length l1 \<and> card Varb - 1 \<le> length l2))"
  unfolding flow_assn_ns_def pot_assn_ns_def parent_assn_ns_def dir_assn_ns_def
            es_assn_ns_def sel_assn_ns_def init_sel_def
  apply (rule ent_frame_fwdI[OF _ ndtree_assn_Sarb[OF laux],
      where F="fa \<mapsto>\<^sub>a flowa * pa \<mapsto>\<^sub>a ds_pot (build_tree acyc_flow) *
               pare \<mapsto>\<^sub>a ds_par (build_tree acyc_flow) * dire \<mapsto>\<^sub>a ds_dir (build_tree acyc_flow) *
               esaa \<mapsto>\<^sub>a esa * sarr \<mapsto>\<^sub>a replicate max_candidates 0 * cref \<mapsto>\<^sub>r 0 * lref \<mapsto>\<^sub>r 0 *
               p1 \<mapsto>\<^sub>a svl * p2 \<mapsto>\<^sub>a socl"])
   apply sep_auto
  apply (rule ent_ex_postI[where x=svl])
  apply (rule ent_ex_postI[where x=socl])
  apply (sep_auto simp: lp1[unfolded One_nat_def] lp2[unfolded One_nat_def])
  done

text \<open>The network-simplex phase of @{const solve_imp}, packaged as one Hoare triple over the raw arrays
      the tree builder leaves behind.  It bridges into @{thm [source] ns_loop_prog_rule} via
      @{thm ns_pre_ent} and reads the functional verdict off @{thm solve_via_padded}: on exit the flow
      array holds a list whose @{term m}-prefix is the optimum whenever @{const solve} says so, and the
      returned flag decides the three verdicts.  The padded stores are related to the augmented
      @{const flow_all} / @{const state_all} on the real range @{term \<open>{0..<m+Kart}\<close>}, which is exactly
      what the tree builder's @{const dfs_rel} guarantees.\<close>
lemma ns_phase_core:
  assumes some: "acyc_flow_opt \<noteq> None" and mpos: "0 < marc"
    and lf: "marc \<le> length fsta" and ls: "marc \<le> length snda" and lc: "marc \<le> length capa"
    and af: "\<And>e. e < marc \<Longrightarrow> fsta ! e = fst_all ! e"
    and as: "\<And>e. e < marc \<Longrightarrow> snda ! e = snd_all ! e"
    and ac: "\<And>e. e < marc \<Longrightarrow> capa ! e = cap_all ! e"
    and flen: "\<forall>k\<in>{0..<m+Kart}. k < length flowa" and fag: "\<And>k. k < m+Kart \<Longrightarrow> flowa ! k = flow_all ! k"
    and eslen: "\<forall>k\<in>{0..<m+Kart}. k < length esa" and eag: "\<And>k. k < m+Kart \<Longrightarrow> esa ! k = state_all ! k"
    and laux: "Suc vcount \<le> length auxa"
    and lsv: "card Varb - 1 \<le> length svl" and lsoc: "card Varb - 1 \<le> length socl"
    and LF: "marc \<le> length fst_all" and LS: "marc \<le> length snd_all" and LC: "marc \<le> length cap_all"
  shows
  "<(cap_arr \<mapsto>\<^sub>a capa * cost_arr \<mapsto>\<^sub>a cost_list * fst_arr \<mapsto>\<^sub>a fsta * snd_arr \<mapsto>\<^sub>a snda) *
    (prnt_impl Ti \<mapsto>\<^sub>a ds_prnt (build_tree acyc_flow) * thrd_impl Ti \<mapsto>\<^sub>a ds_thrd (build_tree acyc_flow) *
     rvth_impl Ti \<mapsto>\<^sub>a ds_rvth (build_tree acyc_flow) * lsuc_impl Ti \<mapsto>\<^sub>a ds_lsuc (build_tree acyc_flow) *
     snum_impl Ti \<mapsto>\<^sub>a ds_snum (build_tree acyc_flow) * aux_impl Ti \<mapsto>\<^sub>a auxa *
     fa \<mapsto>\<^sub>a flowa * pa \<mapsto>\<^sub>a ds_pot (build_tree acyc_flow) *
     pare \<mapsto>\<^sub>a ds_par (build_tree acyc_flow) * dire \<mapsto>\<^sub>a ds_dir (build_tree acyc_flow) *
     esaa \<mapsto>\<^sub>a esa * sarr \<mapsto>\<^sub>a replicate max_candidates 0 * cref \<mapsto>\<^sub>r 0 * lref \<mapsto>\<^sub>r 0 *
     p1 \<mapsto>\<^sub>a svl * p2 \<mapsto>\<^sub>a socl)>
    ns_loop_prog vcount m marc block_size min_candidates max_candidates fst_arr snd_arr cost_arr cap_arr
      (ns_impl_state.make fa pa Ti pare dire esaa (sarr, cref, lref) p1 p2)
   <\<lambda>res. (\<exists>\<^sub>A fl'. fa \<mapsto>\<^sub>a fl' * cost_arr \<mapsto>\<^sub>a cost_list *
            \<up>(marc \<le> length fl' \<and>
              solve = (if res = Network_Simplex.unbounded then Neg_inf_cycle
                       else if list_all (\<lambda>k. fl' ! k = 0) [m..<marc]
                            then Optimum (take m fl') else Infeasible))) * true>"
proof -
  define sp where "sp = (network_simplex_init_spec.init_state flow_all (ds_pot art_tree) (tree_st art_tree)
                   (ds_par art_tree) (ds_dir art_tree) state_all init_sel)
                 \<lparr>current_flow := flowa, network_simplex_state.edge_state := esa\<rparr>"
  have LCO: "m \<le> length cost_list" by (simp add: length_cost_list_m)
  note T = solve_via_padded[OF some mpos flen eslen fag eag]
  have D: "NS.ns_loop_dom sp" and Inv: "NS.ns_invar sp"
    and SOLVE: "solve = (if network_simplex_state.return (NS.ns_loop sp) = unbounded then Neg_inf_cycle
                  else if list_all (\<lambda>k. current_flow (NS.ns_loop sp) ! k = 0) [m..<m+Kart]
                       then Optimum (take m (current_flow (NS.ns_loop sp))) else Infeasible)"
    using T unfolding sp_def by auto
  have invsp: "NS.ns_invar (NS.ns_loop sp)" by (rule ns_loop_invar[OF D Inv])
  have fisp: "\<forall>k\<in>{0..<m+Kart}. k < length (current_flow (NS.ns_loop sp))"
    using NS.ns_invar_implD(1)[OF NS.ns_invarD(1)[OF invsp]] .
  have lensp: "marc \<le> length (current_flow (NS.ns_loop sp))"
  proof -
    have "marc - 1 < length (current_flow (NS.ns_loop sp))" using fisp mpos by (auto simp: marc_def)
    thus ?thesis using mpos by simp
  qed
  note selred = sp_def network_simplex_init_spec.init_state_def art_tree_def
                Sarb_tree_st[symmetric, unfolded art_tree_def] ns_impl_state.make_def
                flow_assn_ns_def pot_assn_ns_def parent_assn_ns_def dir_assn_ns_def
                es_assn_ns_def sel_assn_ns_def init_sel_def
  show ?thesis
    apply (rule ht_cons_post_prec[OF ht_cons_pre[OF _
             ns_loop_prog_rule[where s = sp
               and si = "ns_impl_state.make fa pa Ti pare dire esaa (sarr, cref, lref) p1 p2",
               OF LF LS LC LCO lf ls lc af as ac Inv]]])
     apply (simp add: selred)
     apply (rule ent_ex_postI[where x=svl], rule ent_ex_postI[where x=socl])
     apply (rule ent_frame_fwdI[OF _ ndtree_assn_Sarb[OF laux],
         where F="cap_arr \<mapsto>\<^sub>a capa * cost_arr \<mapsto>\<^sub>a cost_list * fst_arr \<mapsto>\<^sub>a fsta * snd_arr \<mapsto>\<^sub>a snda *
                  fa \<mapsto>\<^sub>a flowa * pa \<mapsto>\<^sub>a ds_pot (build_tree acyc_flow) *
                  pare \<mapsto>\<^sub>a ds_par (build_tree acyc_flow) * dire \<mapsto>\<^sub>a ds_dir (build_tree acyc_flow) *
                  esaa \<mapsto>\<^sub>a esa * sarr \<mapsto>\<^sub>a replicate max_candidates 0 * cref \<mapsto>\<^sub>r 0 * lref \<mapsto>\<^sub>r 0 *
                  p1 \<mapsto>\<^sub>a svl * p2 \<mapsto>\<^sub>a socl"])
      apply sep_auto
     apply (sep_auto simp: lsv[unfolded One_nat_def] lsoc[unfolded One_nat_def])
    apply (rule ent_ex_preI)+
    apply (rule ent_ex_postI[of _ _ "current_flow (NS.ns_loop sp)"])
    apply (sep_auto simp: ns_impl_state.make_def flow_assn_ns_def lensp[unfolded marc_def] SOLVE marc_def)
    done
qed

text \<open>Agreement transfer, once for all four augmented arrays: a padded working array that matches the
      \<^emph>\<open>real\<close> input list below @{term m} and the builder's \<^emph>\<open>artificial tail\<close> above it agrees with the
      augmented list @{term \<open>xl @ take Kart xt\<close>} on the whole arc range @{term \<open>{0..<marc}\<close>}.  Applied
      with @{term xl}/@{term xt} instantiated to @{term fst_list}/@{term \<open>ds_afst art_tree\<close>} and the
      corresponding pairs for @{const snd_all}, @{const cap_all}, @{const flow_all}, @{const state_all}.\<close>
lemma agree_marc:
  assumes a1: "\<forall>e<m. xa ! e = xl ! e" and a2: "\<forall>k<Kart. xa ! (m+k) = xt ! k"
      and len: "length xl = m" and kt: "Kart \<le> length xt"
  shows "\<forall>e<marc. xa ! e = (xl @ take Kart xt) ! e"
proof (intro allI impI)
  fix e assume "e < marc"
  hence e: "e < m + Kart" by (simp add: marc_def)
  show "xa ! e = (xl @ take Kart xt) ! e"
  proof (cases "e < m")
    case True thus ?thesis using a1 len by (simp add: nth_append)
  next
    case False
    hence me: "e = m + (e - m)" by simp
    have kK: "e - m < Kart" using e False by simp
    have l1: "xa ! e = xt ! (e - m)" using a2 kK me by metis
    have l2: "(xl @ take Kart xt) ! e = take Kart xt ! (e - m)" using False len by (simp add: nth_append)
    have l3: "take Kart xt ! (e - m) = xt ! (e - m)" using kK kt by simp
    show ?thesis using l1 l2 l3 by simp
  qed
qed

text \<open>The network-simplex phase over the \<^emph>\<open>tree builder's own\<close> state relation: exactly the shape
      @{thm [source] build_tree_imp_raw_rule} hands back.  Unfolding @{const dfs_rel} exposes the ten
      working lists and the pure conjunct block; @{thm agree_marc} turns the ``real prefix + artificial
      tail'' agreements into agreement with the augmented @{const fst_all} / @{const snd_all} /
      @{const cap_all} / @{const flow_all} / @{const state_all} on all of @{term \<open>{0..<marc}\<close>}, and the
      DFS scratch stores that the simplex loop does not touch travel through as a frame.\<close>
lemma ns_phase_triple:
  assumes some: "acyc_flow_opt \<noteq> None" and mpos: "0 < marc"
  shows
  "<sarr \<mapsto>\<^sub>a replicate max_candidates 0 * cref \<mapsto>\<^sub>r 0 * lref \<mapsto>\<^sub>r 0 *
    dfs_rel acyc_flow (edge_state acyc_flow) (free_out_edges acyc_flow) (free_out_hi acyc_flow)
      (free_in_edges acyc_flow) (free_in_hi acyc_flow) st (build_tree acyc_flow)>
    ns_loop_prog vcount m marc block_size min_candidates max_candidates
      (di_fst st) (di_snd st) (di_cost st) (di_cap st)
      (ns_impl_state.make (di_flow st) (di_pot st) (di_tree st) (di_par st) (di_dir st) (di_es st)
                          (sarr, cref, lref) (di_sv st) (di_soc st))
   <\<lambda>res. (\<exists>\<^sub>A fl'. di_flow st \<mapsto>\<^sub>a fl' * di_cost st \<mapsto>\<^sub>a cost_list *
            \<up>(marc \<le> length fl' \<and>
              solve = (if res = Network_Simplex.unbounded then Neg_inf_cycle
                       else if list_all (\<lambda>k. fl' ! k = 0) [m..<marc]
                            then Optimum (take m fl') else Infeasible))) * true>"
  unfolding dfs_rel_def
  apply (simp only: ex_assn_move_out)
  apply (rule ht_exEI)+
  apply (simp only: mult.assoc[symmetric])
  apply (rule ht_extract_pre_pure(1))
  apply (erule conjE)+
  subgoal premises P for fsta snda capa flowa esa auxa svl socl sicl sp
  proof -
    have Kdef: "Kart = ds_nxt (build_tree acyc_flow)" by (simp add: Kart_def art_tree_def)
    have KA: "Kart \<le> length (ds_afst (build_tree acyc_flow))" using Kart_le len_afst_bt by simp
    have KB: "Kart \<le> length (ds_asnd (build_tree acyc_flow))" using Kart_le len_asnd_bt by simp
    have KC: "Kart \<le> length (ds_acap (build_tree acyc_flow))" using Kart_le len_acap_bt by simp
    have KD: "Kart \<le> length (ds_aflw (build_tree acyc_flow))" using Kart_le len_aflw_bt by simp
    have KE: "Kart \<le> length (ds_aest (build_tree acyc_flow))" using Kart_le len_aest_bt by simp
    have lf: "marc \<le> length fsta" using P(13) KA by (simp add: marc_def)
    have ls: "marc \<le> length snda" using P(14) KB by (simp add: marc_def)
    have lc: "marc \<le> length capa" using P(15) KC by (simp add: marc_def)
    have af: "\<forall>e<marc. fsta ! e = fst_all ! e"
      using agree_marc[OF P(7) P(18)[folded Kdef] length_fst_list_m KA]
      by (simp add: fst_all_def art_tree_def)
    have as: "\<forall>e<marc. snda ! e = snd_all ! e"
      using agree_marc[OF P(8) P(19)[folded Kdef] length_snd_list_m KB]
      by (simp add: snd_all_def art_tree_def)
    have ac: "\<forall>e<marc. capa ! e = cap_all ! e"
      using agree_marc[OF P(10) P(20)[folded Kdef] length_edges KC]
      by (simp add: cap_all_def art_tree_def)
    have afl: "\<forall>e<marc. flowa ! e = flow_all ! e"
      using agree_marc[OF P(9) P(21)[folded Kdef] length_acyc_flow KD]
      by (simp add: flow_all_def art_tree_def)
    have aes: "\<forall>e<marc. esa ! e = state_all ! e"
      using agree_marc[OF P(11) P(22)[folded Kdef] length_edge_state KE]
      by (simp add: state_all_def art_tree_def)
    have flen: "\<forall>k\<in>{0..<m+Kart}. k < length flowa" using P(16) KD by auto
    have eslen: "\<forall>k\<in>{0..<m+Kart}. k < length esa" using P(17) KE by auto
    have laux: "Suc vcount \<le> length auxa" using P(12) by simp
    have lsv: "card Varb - 1 \<le> length svl" using P(2) card_Varb_le by simp
    have lsoc: "card Varb - 1 \<le> length socl" using P(3) card_Varb_le by simp
    have LF: "marc \<le> length fst_all" by (simp add: marc_def)
    have LS: "marc \<le> length snd_all" by (simp add: marc_def)
    have LC: "marc \<le> length cap_all" by (simp add: marc_def)
    note CORE = ns_phase_core[OF some mpos lf ls lc af[rule_format] as[rule_format] ac[rule_format]
          flen afl[rule_format, unfolded marc_def] eslen aes[rule_format, unfolded marc_def]
          laux lsv lsoc LF LS LC]
    show ?thesis
      apply (rule ht_cons_post_prec[OF ht_cons_pre[OF _ ht_frame[OF CORE,
          where R="di_seen st \<mapsto>\<^sub>a ds_seen (build_tree acyc_flow) *
                   di_oe st \<mapsto>\<^sub>a free_out_edges acyc_flow * di_olo st \<mapsto>\<^sub>a out_lo *
                   di_ohi st \<mapsto>\<^sub>a free_out_hi acyc_flow * di_ie st \<mapsto>\<^sub>a free_in_edges acyc_flow *
                   di_ilo st \<mapsto>\<^sub>a in_lo * di_ihi st \<mapsto>\<^sub>a free_in_hi acyc_flow *
                   di_sic st \<mapsto>\<^sub>a sicl * di_sp st \<mapsto>\<^sub>r sp *
                   di_prev st \<mapsto>\<^sub>r ds_prev (build_tree acyc_flow) *
                   di_nxt st \<mapsto>\<^sub>r ds_nxt (build_tree acyc_flow)"]]])
      apply sep_auto
      done
  qed
  done

text \<open>The tail of @{const solve_imp}: read the loop's verdict, and on a bounded optimum scan the
      artificial range @{term \<open>[m..<marc]\<close>} — all-zero means the @{term b}-flow is the first @{term m}
      cells, which are copied back into the caller's flow array.  The three branches deliver exactly
      @{term \<open>status_of solve\<close>}, and on @{const Optimum} the copied prefix is the optimal flow.\<close>
lemma ns_tail_triple:
  assumes lfl: "marc \<le> length fl'"
    and SV: "solve = (if res = Network_Simplex.unbounded then Neg_inf_cycle else if list_all (\<lambda>k. fl' ! k = 0) [m..<marc] then Optimum (take m fl') else Infeasible)"
    and lfs: "m \<le> length fs0"
  shows "<fa \<mapsto>\<^sub>a fl' * in_flow \<mapsto>\<^sub>a fs0> (if res = Network_Simplex.unbounded then return NegInfCycleF else do { allz \<leftarrow> scan_art_imp fa m marc; (if allz then do { _ \<leftarrow> arr_copy_imp fa in_flow 0 m; return OptimalF } else return InfeasibleF) }) <\<lambda>r. \<exists>\<^sub>A fs'. in_flow \<mapsto>\<^sub>a fs' * \<up>(r = status_of solve \<and> (\<forall>fs. solve = Optimum fs \<longrightarrow> take m fs' = fs)) * true>"
proof -
  have mfl: "m \<le> length fl'" using lfl by (simp add: marc_def)
  show ?thesis
  proof (cases "res = Network_Simplex.unbounded")
    case True
    hence sv: "solve = Neg_inf_cycle" using SV by simp
    show ?thesis using True by (sep_auto simp: sv)
  next
    case False
    have sv: "solve = (if list_all (\<lambda>k. fl' ! k = 0) [m..<marc] then Optimum (take m fl') else Infeasible)" using SV False by simp
    show ?thesis
      apply (simp only: if_not_P[OF False])
      apply (sep_auto heap: scan_art_imp_rule[OF lfl] arr_copy_imp_rule simp: sv mfl lfs)
      done
  qed
qed

text \<open>The tail again, but with the \<^emph>\<open>garbage\<close> predicate already in the precondition, so that it matches
      the postcondition of the loop phase verbatim — this is what lets the two compose by a bare
      @{thm [source] ht_bind}, with no frame and no re-association.\<close>
lemma ns_tail_triple2:
  assumes lfl: "marc \<le> length fl'"
    and SV: "solve = (if res = Network_Simplex.unbounded then Neg_inf_cycle else if list_all (\<lambda>k. fl' ! k = 0) [m..<marc] then Optimum (take m fl') else Infeasible)"
    and lfs: "m \<le> length fs0"
  shows "<fa \<mapsto>\<^sub>a fl' * in_flow \<mapsto>\<^sub>a fs0 * true> (if res = Network_Simplex.unbounded then return NegInfCycleF else do { allz \<leftarrow> scan_art_imp fa m marc; (if allz then do { _ \<leftarrow> arr_copy_imp fa in_flow 0 m; return OptimalF } else return InfeasibleF) }) <\<lambda>r. \<exists>\<^sub>A fs'. in_flow \<mapsto>\<^sub>a fs' * \<up>(r = status_of solve \<and> (\<forall>fs. solve = Optimum fs \<longrightarrow> take m fs' = fs)) * true>"
proof -
  have mfl: "m \<le> length fl'" using lfl by (simp add: marc_def)
  show ?thesis
  proof (cases "res = Network_Simplex.unbounded")
    case True
    hence sv: "solve = Neg_inf_cycle" using SV by simp
    show ?thesis using True by (sep_auto simp: sv)
  next
    case False
    have sv: "solve = (if list_all (\<lambda>k. fl' ! k = 0) [m..<marc] then Optimum (take m fl') else Infeasible)" using SV False by simp
    show ?thesis
      apply (simp only: if_not_P[OF False])
      apply (sep_auto heap: scan_art_imp_rule[OF lfl] arr_copy_imp_rule simp: sv mfl lfs)
      done
  qed
qed

text \<open>The loop phase, reshaped for composition: the caller's flow array @{term in_flow} is threaded
      through untouched and the pure conjunct is moved \<^emph>\<open>last\<close>, so that stripping the existential and
      extracting the pure part leaves @{thm [source] ns_tail_triple2}'s precondition (plus the cost
      array, which @{const ns_loop_prog} also returns unchanged — the capstone's postcondition asserts
      that the caller's cost array still holds the cost list on exit, and since @{const solve_imp}
      passes it in \<^emph>\<open>uncopied\<close> it must not be dropped into the garbage predicate anywhere along the
      chain).\<close>
lemma ns_phase_triple':
  assumes some: "acyc_flow_opt \<noteq> None" and mpos: "0 < marc"
  shows "<sarr \<mapsto>\<^sub>a replicate max_candidates 0 * cref \<mapsto>\<^sub>r 0 * lref \<mapsto>\<^sub>r 0 * dfs_rel acyc_flow (edge_state acyc_flow) (free_out_edges acyc_flow) (free_out_hi acyc_flow) (free_in_edges acyc_flow) (free_in_hi acyc_flow) st (build_tree acyc_flow) * in_flow \<mapsto>\<^sub>a fs0> ns_loop_prog vcount m marc block_size min_candidates max_candidates (di_fst st) (di_snd st) (di_cost st) (di_cap st) (ns_impl_state.make (di_flow st) (di_pot st) (di_tree st) (di_par st) (di_dir st) (di_es st) (sarr, cref, lref) (di_sv st) (di_soc st)) <\<lambda>res. \<exists>\<^sub>A fl'. di_flow st \<mapsto>\<^sub>a fl' * di_cost st \<mapsto>\<^sub>a cost_list * in_flow \<mapsto>\<^sub>a fs0 * true * \<up>(marc \<le> length fl' \<and> solve = (if res = Network_Simplex.unbounded then Neg_inf_cycle else if list_all (\<lambda>k. fl' ! k = 0) [m..<marc] then Optimum (take m fl') else Infeasible))>"
  apply (rule ht_cons_post_prec[OF ht_frame[OF ns_phase_triple[OF some mpos], where R="in_flow \<mapsto>\<^sub>a fs0"]])
  apply sep_auto
  done

text \<open>Everything @{const solve_imp} does after the spanning tree is built: run the network-simplex
      loop and dispatch on its verdict.  The two phases compose by @{thm [source] ht_bind} alone.\<close>
lemma ns_after_tree:
  assumes some: "acyc_flow_opt \<noteq> None" and mpos: "0 < marc" and lfs: "m \<le> length fs0"
  shows "<sarr \<mapsto>\<^sub>a replicate max_candidates 0 * cref \<mapsto>\<^sub>r 0 * lref \<mapsto>\<^sub>r 0 * dfs_rel acyc_flow (edge_state acyc_flow) (free_out_edges acyc_flow) (free_out_hi acyc_flow) (free_in_edges acyc_flow) (free_in_hi acyc_flow) st (build_tree acyc_flow) * in_flow \<mapsto>\<^sub>a fs0> do { res \<leftarrow> ns_loop_prog vcount m marc block_size min_candidates max_candidates (di_fst st) (di_snd st) (di_cost st) (di_cap st) (ns_impl_state.make (di_flow st) (di_pot st) (di_tree st) (di_par st) (di_dir st) (di_es st) (sarr, cref, lref) (di_sv st) (di_soc st)); (if res = Network_Simplex.unbounded then return NegInfCycleF else do { allz \<leftarrow> scan_art_imp (di_flow st) m marc; (if allz then do { _ \<leftarrow> arr_copy_imp (di_flow st) in_flow 0 m; return OptimalF } else return InfeasibleF) }) } <\<lambda>r. \<exists>\<^sub>A fs'. in_flow \<mapsto>\<^sub>a fs' * \<up>(r = status_of solve \<and> (\<forall>fs. solve = Optimum fs \<longrightarrow> take m fs' = fs)) * true>"
  apply (rule ht_bind[OF ns_phase_triple'[OF some mpos]])
  apply (rule ht_exEI)
  apply (rule ht_extract_pre_pure(1))
  apply (erule conjE)
  apply (rule ht_cons_pre[OF _ ns_tail_triple2[OF _ _ lfs]])
    apply sep_auto
  done

text \<open>Block \<^emph>\<open>ends\<close> have the same length as the block \<^emph>\<open>starts\<close>: both are read off the one prefix-sum
      list, as its @{const tl} and its @{const butlast} respectively.\<close>
lemma length_out_hi: "length out_hi = vcount"
proof -
  have "length out_hi = length out_lo" by (simp add: out_hi_def out_lo_def out_csr_hi out_csr_lo)
  thus ?thesis by (simp add: length_out_lo)
qed

lemma length_in_hi: "length in_hi = vcount"
proof -
  have "length in_hi = length in_lo" by (simp add: in_hi_def in_lo_def in_csr_hi in_csr_lo)
  thus ?thesis by (simp add: length_in_lo)
qed

text \<open>The edged-vertex phase of @{const solve_imp}: count the non-lonely vertices, allocate an
      exactly-sized array and fill it.  Together the two loops materialise @{const edged_vs_list} —
      the vertex iterator the acyclifier consumes — leaving the four CSR block-boundary arrays
      untouched.\<close>
lemma edged_build_triple:
  "<olo \<mapsto>\<^sub>a out_lo * ohi \<mapsto>\<^sub>a out_hi * ilo \<mapsto>\<^sub>a in_lo * ihi \<mapsto>\<^sub>a in_hi> do { k \<leftarrow> count_edged_imp olo ohi ilo ihi 1 n 0; vl \<leftarrow> Array.new k 0; _ \<leftarrow> fill_edged_imp vl olo ohi ilo ihi 1 n 0; return vl } <\<lambda>vl. vl \<mapsto>\<^sub>a edged_vs_list * olo \<mapsto>\<^sub>a out_lo * ohi \<mapsto>\<^sub>a out_hi * ilo \<mapsto>\<^sub>a in_lo * ihi \<mapsto>\<^sub>a in_hi>"
proof -
  have l1: "Suc n \<le> length out_lo" by (simp add: length_out_lo vcount_eq)
  have l2: "Suc n \<le> length out_hi" by (simp add: length_out_hi vcount_eq)
  have l3: "Suc n \<le> length in_lo" by (simp add: length_in_lo vcount_eq)
  have l4: "Suc n \<le> length in_hi" by (simp add: length_in_hi vcount_eq)
  have v1: "(1::nat) \<le> Suc n" by simp
  show ?thesis
    apply (sep_auto heap: count_edged_imp_rule[OF v1 l1 l2 l3 l4] fill_edged_imp_rule[OF v1 l1 l2 l3 l4] simp: edged_lst_eq_vs_list)
    done
qed

text \<open>The CSR-building phase of @{const solve_imp}, as one triple: build the outgoing CSR keyed on the
      padded @{term fst_list} array, re-zero the shared count array, then build the ingoing CSR keyed on
      the padded @{term snd_list} array.  The reset is exactly what @{thm fst_cto_pad_drop} makes
      possible — after the first build the count array's reserved root cell is still @{term 0}, so
      filling @{term \<open>[0..<vcount]\<close>} restores it to all-zero for the second build.  The two padded key
      arrays are returned untouched and the count array is left as garbage.\<close>
lemma csr_build_triple:
  "<fa \<mapsto>\<^sub>a (fst_list @ replicate n 0) * sa \<mapsto>\<^sub>a (snd_list @ replicate n 0) * c \<mapsto>\<^sub>a (0 # 0 # replicate n 0) * o_lo \<mapsto>\<^sub>a replicate vcount 0 * o_hi \<mapsto>\<^sub>a replicate vcount 0 * o_cur \<mapsto>\<^sub>a replicate vcount 0 * o_edges \<mapsto>\<^sub>a replicate m 0 * i_lo \<mapsto>\<^sub>a replicate vcount 0 * i_hi \<mapsto>\<^sub>a replicate vcount 0 * i_cur \<mapsto>\<^sub>a replicate vcount 0 * i_edges \<mapsto>\<^sub>a replicate m 0> do { _ \<leftarrow> build_csr_imp fa c o_lo o_hi o_cur o_edges m vcount; _ \<leftarrow> arr_fill_imp c 0 0 vcount; build_csr_imp sa c i_lo i_hi i_cur i_edges m vcount } <\<lambda>_. fa \<mapsto>\<^sub>a (fst_list @ replicate n 0) * sa \<mapsto>\<^sub>a (snd_list @ replicate n 0) * (\<exists>\<^sub>A cl. c \<mapsto>\<^sub>a cl) * csr_assn out_csr (o_edges, o_lo, o_hi, o_cur) * csr_assn in_csr (i_edges, i_lo, i_hi, i_cur)>"
proof -
  have LC: "vcount \<le> Suc vcount" by simp
  have rep: "(0 # 0 # replicate n 0) = replicate (Suc vcount) (0::nat)" by (simp add: vcount_eq)
  note OUT = build_csr_out_pad_over_c[OF fst_pad_mk fst_pad_bd fst_pad_keys LC, where c = c, unfolded rep[symmetric]]
  note IN = build_csr_in_pad_over_c[OF snd_pad_mk snd_pad_bd snd_pad_keys LC, where c = c, unfolded rep[symmetric]]
  have LEN: "vcount \<le> length (fold (\<lambda>i cc. cc[(fst_list @ replicate n 0) ! i := Suc (cc ! ((fst_list @ replicate n 0) ! i))]) [0..<m] (0 # 0 # replicate n 0))"
    using fst_cto_pad_len by (simp add: vcount_eq)
  have RES: "replicate vcount 0 @ drop vcount (fold (\<lambda>i cc. cc[(fst_list @ replicate n 0) ! i := Suc (cc ! ((fst_list @ replicate n 0) ! i))]) [0..<m] (0 # 0 # replicate n 0)) = 0 # 0 # replicate n 0"
    using fst_cto_pad_drop by (simp add: vcount_eq replicate_append_same)
  show ?thesis
    apply (sep_auto heap: OUT arr_fill_imp_rule IN simp: RES LEN)
    done
qed

text \<open>Monolith glue, part 1: the shapes @{const solve_imp}'s freshly allocated arrays actually have.
      @{term \<open>Array.new (Suc vcount) x\<close>} yields @{term \<open>x # replicate vcount x\<close>}, so the count-array
      facts of @{thm [source] csr_build_triple} are restated in that form, and the four CSR
      block-boundary lists are named (@{const csr_cur} coincides with @{const csr_lo} on a freshly
      built CSR).\<close>
lemma cto_pad_drop': "drop vcount (fold (\<lambda>i cc. cc[(fst_list @ replicate n 0) ! i := Suc (cc ! ((fst_list @ replicate n 0) ! i))]) [0..<m] (0 # replicate vcount 0)) = [0]"
  using fst_cto_pad_drop by (simp add: vcount_eq)

lemma cto_pad_len': "length (fold (\<lambda>i cc. cc[(fst_list @ replicate n 0) ! i := Suc (cc ! ((fst_list @ replicate n 0) ! i))]) [0..<m] (0 # replicate vcount 0)) = Suc vcount"
  by (simp add: count_fold_length)

lemma csr_lo_out: "csr_lo out_csr = out_lo" by (simp add: out_lo_def)
lemma csr_hi_out: "csr_hi out_csr = out_hi" by (simp add: out_hi_def)
lemma csr_cur_out: "csr_cur out_csr = out_lo" by (simp add: out_lo_def out_csr_cur out_csr_lo)
lemma csr_lo_in: "csr_lo in_csr = in_lo" by (simp add: in_lo_def)
lemma csr_hi_in: "csr_hi in_csr = in_hi" by (simp add: in_hi_def)
lemma csr_cur_in: "csr_cur in_csr = in_lo" by (simp add: in_lo_def in_csr_cur in_csr_lo)

lemma edg_l1: "Suc n \<le> length out_lo" by (simp add: length_out_lo vcount_eq)
lemma edg_l2: "Suc n \<le> length out_hi" by (simp add: length_out_hi vcount_eq)
lemma edg_l3: "Suc n \<le> length in_lo" by (simp add: length_in_lo vcount_eq)
lemma edg_l4: "Suc n \<le> length in_hi" by (simp add: length_in_hi vcount_eq)
lemma edg_v1: "(Suc 0::nat) \<le> Suc n" by simp

text \<open>Pass A over an \<^emph>\<open>over-long\<close> edge-state array: @{const solve_imp} allocates @{term es_arr} with
      the augmented length @{term \<open>m + n\<close>} (it must later hold the artificial edges' tags), whereas
      @{thm [source] passA_imp_rule} is phrased for the exact-length store.  The loop writes only
      inside @{term \<open>[0..<m]\<close>}, so a fixed suffix @{term pad} rides along untouched.\<close>
lemma passA_imp_pad_rule:
  fixes fl_arr cap_arr :: "'n array" and fst_arr snd_arr :: "nat array"
    and es_arr :: "edge_tag array" and exc_arr :: "'n array"
    and oe_arr oc_arr ie_arr ic_arr :: "nat array"
    and fla cla :: "'n list" and flla slla :: "nat list"
    and e :: nat and est pad :: "edge_tag list" and exc :: "'n list"
    and oe oc ie ic :: "nat list"
  assumes e_le: "e \<le> m"
    and fla_len: "m \<le> length fla" and cla_len: "m \<le> length cla"
    and flla_len: "m \<le> length flla" and slla_len: "m \<le> length slla"
    and cap_eq: "\<And>i. i < m \<Longrightarrow> cla ! i = capacity_list ! i"
    and fst_eq: "\<And>i. i < m \<Longrightarrow> flla ! i = fst_list ! i"
    and snd_eq: "\<And>i. i < m \<Longrightarrow> slla ! i = snd_list ! i"
    and s_eq: "(est, exc, oe, oc, ie, ic) = fold (passA_step fla) [0..<e] (replicate m InL, replicate (Suc vcount) 0, csr_edges out_csr, out_lo, csr_edges in_csr, in_lo)"
  shows "<fl_arr \<mapsto>\<^sub>a fla * cap_arr \<mapsto>\<^sub>a cla * fst_arr \<mapsto>\<^sub>a flla * snd_arr \<mapsto>\<^sub>a slla * es_arr \<mapsto>\<^sub>a (est @ pad) * exc_arr \<mapsto>\<^sub>a exc * oe_arr \<mapsto>\<^sub>a oe * oc_arr \<mapsto>\<^sub>a oc * ie_arr \<mapsto>\<^sub>a ie * ic_arr \<mapsto>\<^sub>a ic> passA_imp fl_arr cap_arr fst_arr snd_arr es_arr exc_arr oe_arr oc_arr ie_arr ic_arr e m <\<lambda>_. fl_arr \<mapsto>\<^sub>a fla * cap_arr \<mapsto>\<^sub>a cla * fst_arr \<mapsto>\<^sub>a flla * snd_arr \<mapsto>\<^sub>a slla * es_arr \<mapsto>\<^sub>a (fst (passA fla) @ pad) * exc_arr \<mapsto>\<^sub>a fst (snd (passA fla)) * oe_arr \<mapsto>\<^sub>a fst (snd (snd (passA fla))) * oc_arr \<mapsto>\<^sub>a fst (snd (snd (snd (passA fla)))) * ie_arr \<mapsto>\<^sub>a fst (snd (snd (snd (snd (passA fla))))) * ic_arr \<mapsto>\<^sub>a snd (snd (snd (snd (snd (passA fla)))))>"
proof -
  have sized_init: "sized (replicate m InL, replicate (Suc vcount) (0::'n), csr_edges out_csr, out_lo, csr_edges in_csr, in_lo)"
    by (simp add: sized_def length_out_lo length_in_lo out_csr_eq in_csr_eq)
  have sized_fold: "sized s0 \<Longrightarrow> sized (fold (passA_step fla) xs s0)" for s0 xs
  proof (induct xs arbitrary: s0)
    case Nil thus ?case by simp
  next
    case (Cons a xs) thus ?case by (simp add: passA_step_sized)
  qed
  from e_le s_eq show ?thesis
  proof (induction "m - e" arbitrary: e est exc oe oc ie ic)
    case 0
    have em: "e = m" using "0.hyps" "0.prems"(1) by simp
    have s0: "(est, exc, oe, oc, ie, ic) = passA fla" using "0.prems"(2) em by (simp add: passA_def)
    show ?case unfolding em by (subst passA_imp.simps) (sep_auto simp: s0[symmetric])
  next
    case (Suc d)
    have em: "e < m" using Suc.hyps(2) Suc.prems(1) by simp
    have sized_s: "sized (est, exc, oe, oc, ie, ic)" using Suc.prems(2) sized_fold[OF sized_init] by simp
    have lens: "length est = m" "length exc = Suc vcount" "length oe = m" "length oc = vcount" "length ie = m" "length ic = vcount"
      using sized_s by (auto simp: sized_def)
    have xe: "flla ! e = fst_list ! e" using fst_eq em by simp
    have ye: "slla ! e = snd_list ! e" using snd_eq em by simp
    have ue: "cla ! e = capacity_list ! e" using cap_eq em by simp
    have xvc: "fst_list ! e < vcount" using fst_list_nth_vertex[OF em] vs_less_vcount by simp
    have yvc: "snd_list ! e < vcount" using snd_list_nth_vertex[OF em] vs_less_vcount by simp
    have oc_val: "oc ! (fst_list ! e) = out_lo ! (fst_list ! e) + length (filter (\<lambda>e'. classify fla e' = InTree \<and> fst_list ! e' = fst_list ! e) [0..<e])"
    proof -
      have "oc = fst (snd (snd (snd (fold (passA_step fla) [0..<e] (replicate m InL, replicate (Suc vcount) 0, csr_edges out_csr, out_lo, csr_edges in_csr, in_lo)))))"
        using Suc.prems(2)[symmetric] by simp
      thus ?thesis using passA_fold_oc_count[OF sized_init xvc, where fl=fla and xs="[0..<e]"] by simp
    qed
    have ic_val: "ic ! (snd_list ! e) = in_lo ! (snd_list ! e) + length (filter (\<lambda>e'. classify fla e' = InTree \<and> snd_list ! e' = snd_list ! e) [0..<e])"
    proof -
      have "ic = snd (snd (snd (snd (snd (fold (passA_step fla) [0..<e] (replicate m InL, replicate (Suc vcount) 0, csr_edges out_csr, out_lo, csr_edges in_csr, in_lo))))))"
        using Suc.prems(2)[symmetric] by simp
      thus ?thesis using passA_fold_ic_count[OF sized_init yvc, where fl=fla and xs="[0..<e]"] by simp
    qed
    have oc_lt: "classify fla e = InTree \<Longrightarrow> oc ! (fst_list ! e) < m"
    proof -
      assume it: "classify fla e = InTree"
      let ?P = "\<lambda>e'. classify fla e' = InTree \<and> fst_list ! e' = fst_list ! e"
      have split: "[0..<m] = [0..<e] @ [e..<m]" using em by (simp add: upt_append)
      have ne: "filter ?P [e..<m] \<noteq> []" using it em by (simp add: filter_empty_conv) (metis atLeastLessThan_iff le_refl)
      have "length (filter ?P [0..<e]) < length (filter ?P [0..<m])" using split ne by (simp add: filter_append)
      hence "oc ! (fst_list ! e) < out_lo ! (fst_list ! e) + length (filter ?P [0..<m])" using oc_val by simp
      also have "... = free_out_hi fla ! (fst_list ! e)" using free_out_hi_count[OF xvc] by simp
      also have "... \<le> m" using free_out_hi_le_m[OF xvc] .
      finally show "oc ! (fst_list ! e) < m" .
    qed
    have ic_lt: "classify fla e = InTree \<Longrightarrow> ic ! (snd_list ! e) < m"
    proof -
      assume it: "classify fla e = InTree"
      let ?Q = "\<lambda>e'. classify fla e' = InTree \<and> snd_list ! e' = snd_list ! e"
      have split: "[0..<m] = [0..<e] @ [e..<m]" using em by (simp add: upt_append)
      have ne: "filter ?Q [e..<m] \<noteq> []" using it em by (simp add: filter_empty_conv) (metis atLeastLessThan_iff le_refl)
      have "length (filter ?Q [0..<e]) < length (filter ?Q [0..<m])" using split ne by (simp add: filter_append)
      hence "ic ! (snd_list ! e) < in_lo ! (snd_list ! e) + length (filter ?Q [0..<m])" using ic_val by simp
      also have "... = free_in_hi fla ! (snd_list ! e)" using free_in_hi_count[OF yvc] by simp
      also have "... \<le> m" using free_in_hi_le_m[OF yvc] .
      finally show "ic ! (snd_list ! e) < m" .
    qed
    have dse: "d = m - Suc e" using Suc.hyps(2) em by simp
    have sse: "Suc e \<le> m" using em by simp
    have step: "<fl_arr \<mapsto>\<^sub>a fla * cap_arr \<mapsto>\<^sub>a cla * fst_arr \<mapsto>\<^sub>a flla * snd_arr \<mapsto>\<^sub>a slla * es_arr \<mapsto>\<^sub>a (fst (passA_step fla e (est, exc, oe, oc, ie, ic)) @ pad) * exc_arr \<mapsto>\<^sub>a fst (snd (passA_step fla e (est, exc, oe, oc, ie, ic))) * oe_arr \<mapsto>\<^sub>a fst (snd (snd (passA_step fla e (est, exc, oe, oc, ie, ic)))) * oc_arr \<mapsto>\<^sub>a fst (snd (snd (snd (passA_step fla e (est, exc, oe, oc, ie, ic))))) * ie_arr \<mapsto>\<^sub>a fst (snd (snd (snd (snd (passA_step fla e (est, exc, oe, oc, ie, ic)))))) * ic_arr \<mapsto>\<^sub>a snd (snd (snd (snd (snd (passA_step fla e (est, exc, oe, oc, ie, ic))))))> passA_imp fl_arr cap_arr fst_arr snd_arr es_arr exc_arr oe_arr oc_arr ie_arr ic_arr (Suc e) m <\<lambda>_. fl_arr \<mapsto>\<^sub>a fla * cap_arr \<mapsto>\<^sub>a cla * fst_arr \<mapsto>\<^sub>a flla * snd_arr \<mapsto>\<^sub>a slla * es_arr \<mapsto>\<^sub>a (fst (passA fla) @ pad) * exc_arr \<mapsto>\<^sub>a fst (snd (passA fla)) * oe_arr \<mapsto>\<^sub>a fst (snd (snd (passA fla))) * oc_arr \<mapsto>\<^sub>a fst (snd (snd (snd (passA fla)))) * ie_arr \<mapsto>\<^sub>a fst (snd (snd (snd (snd (passA fla))))) * ic_arr \<mapsto>\<^sub>a snd (snd (snd (snd (snd (passA fla)))))>"
      by (rule Suc.hyps(1)[OF dse sse]) (simp add: Suc.prems(2))
    have nme: "\<not> m \<le> e" using em by simp
    have eb: "e < length flla" "e < length slla" "e < length fla" "e < length cla" "e < length est"
      using em flla_len slla_len fla_len cla_len lens(1) by auto
    have ebp: "e < length (est @ pad)" using eb(5) by simp
    have ebm: "e < m + length pad" using em by simp
    have updp: "\<And>x. est[e := x] @ pad = (est @ pad)[e := x]" using eb(5) by (simp add: list_update_append)
    show ?case
    proof (cases "classify fla e = InTree")
      case True
      have st_val: "(if fla ! e = 0 then InL else if cla ! e \<noteq> - 1 \<and> fla ! e = cla ! e then InU else InTree) = InTree"
      proof -
        have "(if fla ! e = 0 then InL else if cla ! e \<noteq> - 1 \<and> fla ! e = cla ! e then InU else InTree) = classify fla e"
          using ue by (simp add: classify_def)
        thus ?thesis using True by simp
      qed
      have ps_es: "fst (passA_step fla e (est, exc, oe, oc, ie, ic)) = est[e := InTree]"
        using True by (simp add: passA_step_fst)
      have ps_oe: "fst (snd (snd (passA_step fla e (est, exc, oe, oc, ie, ic)))) = oe[oc ! (fst_list ! e) := e]"
        using True by (simp add: passA_step_oe)
      have ps_oc: "fst (snd (snd (snd (passA_step fla e (est, exc, oe, oc, ie, ic))))) = oc[fst_list ! e := Suc (oc ! (fst_list ! e))]"
        using True by (simp add: passA_step_oc)
      have ps_ie: "fst (snd (snd (snd (snd (passA_step fla e (est, exc, oe, oc, ie, ic)))))) = ie[ic ! (snd_list ! e) := e]"
        using True by (simp add: passA_step_ie)
      have ps_ic: "snd (snd (snd (snd (snd (passA_step fla e (est, exc, oe, oc, ie, ic)))))) = ic[snd_list ! e := Suc (ic ! (snd_list ! e))]"
        using True by (simp add: passA_step_ic)
      have ps_exc: "fst (snd (passA_step fla e (est, exc, oe, oc, ie, ic))) = exc[snd_list ! e := exc ! (snd_list ! e) + fla ! e, fst_list ! e := exc[snd_list ! e := exc ! (snd_list ! e) + fla ! e] ! (fst_list ! e) - fla ! e]"
        by (simp add: passA_step_exc Let_def)
      have step': "<fl_arr \<mapsto>\<^sub>a fla * cap_arr \<mapsto>\<^sub>a cla * fst_arr \<mapsto>\<^sub>a flla * snd_arr \<mapsto>\<^sub>a slla * es_arr \<mapsto>\<^sub>a (est @ pad)[e := InTree] * exc_arr \<mapsto>\<^sub>a exc[snd_list ! e := exc ! (snd_list ! e) + fla ! e, fst_list ! e := exc[snd_list ! e := exc ! (snd_list ! e) + fla ! e] ! (fst_list ! e) - fla ! e] * oe_arr \<mapsto>\<^sub>a oe[oc ! (fst_list ! e) := e] * oc_arr \<mapsto>\<^sub>a oc[fst_list ! e := Suc (oc ! (fst_list ! e))] * ie_arr \<mapsto>\<^sub>a ie[ic ! (snd_list ! e) := e] * ic_arr \<mapsto>\<^sub>a ic[snd_list ! e := Suc (ic ! (snd_list ! e))]> passA_imp fl_arr cap_arr fst_arr snd_arr es_arr exc_arr oe_arr oc_arr ie_arr ic_arr (Suc e) m <\<lambda>_. fl_arr \<mapsto>\<^sub>a fla * cap_arr \<mapsto>\<^sub>a cla * fst_arr \<mapsto>\<^sub>a flla * snd_arr \<mapsto>\<^sub>a slla * es_arr \<mapsto>\<^sub>a (fst (passA fla) @ pad) * exc_arr \<mapsto>\<^sub>a fst (snd (passA fla)) * oe_arr \<mapsto>\<^sub>a fst (snd (snd (passA fla))) * oc_arr \<mapsto>\<^sub>a fst (snd (snd (snd (passA fla)))) * ie_arr \<mapsto>\<^sub>a fst (snd (snd (snd (snd (passA fla))))) * ic_arr \<mapsto>\<^sub>a snd (snd (snd (snd (snd (passA fla)))))>"
        using step by (simp only: ps_es ps_exc ps_oe ps_oc ps_ie ps_ic updp)
      have step'': "<fl_arr \<mapsto>\<^sub>a fla * cap_arr \<mapsto>\<^sub>a cla * fst_arr \<mapsto>\<^sub>a flla * snd_arr \<mapsto>\<^sub>a slla * es_arr \<mapsto>\<^sub>a (est @ pad)[e := InTree] * exc_arr \<mapsto>\<^sub>a exc[slla ! e := exc ! (slla ! e) + fla ! e, flla ! e := exc[slla ! e := exc ! (slla ! e) + fla ! e] ! (flla ! e) - fla ! e] * oe_arr \<mapsto>\<^sub>a oe[oc ! (flla ! e) := e] * oc_arr \<mapsto>\<^sub>a oc[flla ! e := Suc (oc ! (flla ! e))] * ie_arr \<mapsto>\<^sub>a ie[ic ! (slla ! e) := e] * ic_arr \<mapsto>\<^sub>a ic[slla ! e := Suc (ic ! (slla ! e))]> passA_imp fl_arr cap_arr fst_arr snd_arr es_arr exc_arr oe_arr oc_arr ie_arr ic_arr (Suc e) m <\<lambda>_. fl_arr \<mapsto>\<^sub>a fla * cap_arr \<mapsto>\<^sub>a cla * fst_arr \<mapsto>\<^sub>a flla * snd_arr \<mapsto>\<^sub>a slla * es_arr \<mapsto>\<^sub>a (fst (passA fla) @ pad) * exc_arr \<mapsto>\<^sub>a fst (snd (passA fla)) * oe_arr \<mapsto>\<^sub>a fst (snd (snd (passA fla))) * oc_arr \<mapsto>\<^sub>a fst (snd (snd (snd (passA fla)))) * ie_arr \<mapsto>\<^sub>a fst (snd (snd (snd (snd (passA fla))))) * ic_arr \<mapsto>\<^sub>a snd (snd (snd (snd (snd (passA fla)))))>"
        using step' by (simp only: xe[symmetric] ye[symmetric])
      have exlv: "slla ! e < Suc vcount" "flla ! e < Suc vcount" using yvc xvc ye xe by simp_all
      have vbv: "flla ! e < vcount" "slla ! e < vcount" using xvc yvc xe ye by simp_all
      have exl_f: "flla ! e < length exc" "slla ! e < length exc" using xvc yvc lens(2) xe ye by simp_all
      have vb_f: "flla ! e < length oc" "slla ! e < length ic" using xvc yvc lens(4) lens(6) xe ye by simp_all
      have scb_f: "oc ! (flla ! e) < length oe" "ic ! (slla ! e) < length ie"
        using oc_lt ic_lt lens(3) lens(5) True xe ye by simp_all
      have scb_v: "oc ! (flla ! e) < m" "ic ! (slla ! e) < m"
        using scb_f lens(3) lens(5) xe ye by simp_all
      show ?thesis
        apply (subst passA_imp.simps)
        apply (simp only: nme if_False Let_def)
        apply (sep_auto heap: step'' simp: em st_val eb ebp ebm exlv exl_f vb_f vbv scb_f scb_v lens)
        done
    next
      case False
      have st_valF: "(if fla ! e = 0 then InL else if cla ! e \<noteq> - 1 \<and> fla ! e = cla ! e then InU else InTree) = classify fla e"
        using ue by (simp add: classify_def)
      have psF: "fst (passA_step fla e (est, exc, oe, oc, ie, ic)) = est[e := classify fla e]"
               "fst (snd (snd (passA_step fla e (est, exc, oe, oc, ie, ic)))) = oe"
               "fst (snd (snd (snd (passA_step fla e (est, exc, oe, oc, ie, ic))))) = oc"
               "fst (snd (snd (snd (snd (passA_step fla e (est, exc, oe, oc, ie, ic)))))) = ie"
               "snd (snd (snd (snd (snd (passA_step fla e (est, exc, oe, oc, ie, ic)))))) = ic"
        using False by (simp_all add: passA_step_fst passA_step_oe passA_step_oc passA_step_ie passA_step_ic)
      have psF_exc: "fst (snd (passA_step fla e (est, exc, oe, oc, ie, ic))) = exc[slla ! e := exc ! (slla ! e) + fla ! e, flla ! e := exc[slla ! e := exc ! (slla ! e) + fla ! e] ! (flla ! e) - fla ! e]"
        by (simp add: passA_step_exc Let_def xe ye)
      have step_F: "<fl_arr \<mapsto>\<^sub>a fla * cap_arr \<mapsto>\<^sub>a cla * fst_arr \<mapsto>\<^sub>a flla * snd_arr \<mapsto>\<^sub>a slla * es_arr \<mapsto>\<^sub>a (est @ pad)[e := classify fla e] * exc_arr \<mapsto>\<^sub>a exc[slla ! e := exc ! (slla ! e) + fla ! e, flla ! e := exc[slla ! e := exc ! (slla ! e) + fla ! e] ! (flla ! e) - fla ! e] * oe_arr \<mapsto>\<^sub>a oe * oc_arr \<mapsto>\<^sub>a oc * ie_arr \<mapsto>\<^sub>a ie * ic_arr \<mapsto>\<^sub>a ic> passA_imp fl_arr cap_arr fst_arr snd_arr es_arr exc_arr oe_arr oc_arr ie_arr ic_arr (Suc e) m <\<lambda>_. fl_arr \<mapsto>\<^sub>a fla * cap_arr \<mapsto>\<^sub>a cla * fst_arr \<mapsto>\<^sub>a flla * snd_arr \<mapsto>\<^sub>a slla * es_arr \<mapsto>\<^sub>a (fst (passA fla) @ pad) * exc_arr \<mapsto>\<^sub>a fst (snd (passA fla)) * oe_arr \<mapsto>\<^sub>a fst (snd (snd (passA fla))) * oc_arr \<mapsto>\<^sub>a fst (snd (snd (snd (passA fla)))) * ie_arr \<mapsto>\<^sub>a fst (snd (snd (snd (snd (passA fla))))) * ic_arr \<mapsto>\<^sub>a snd (snd (snd (snd (snd (passA fla)))))>"
        using step by (simp only: psF(1) psF_exc psF(2) psF(3) psF(4) psF(5) updp)
      have exl_f: "flla ! e < length exc" "slla ! e < length exc" using xvc yvc lens(2) xe ye by simp_all
      have exlv: "slla ! e < Suc vcount" "flla ! e < Suc vcount" using yvc xvc ye xe by simp_all
      show ?thesis
        apply (subst passA_imp.simps)
        apply (simp only: nme if_False Let_def)
        apply (sep_auto heap: step_F simp: em st_valF False eb ebp ebm exlv exl_f lens)
        done
    qed
  qed
qed

text \<open>Applying a \<^emph>\<open>multi-command\<close> Hoare triple inside a weakest-precondition goal: the standard
      @{thm [source] wlp_apply_ht} demands that the triple cover the \<^emph>\<open>whole\<close> remaining program, and
      \<open>sep_auto\<close> always decomposes down to the leftmost atomic command.  Splitting off the
      bind first (@{thm [source] decon_bind}) lets a block triple be applied to a \<^emph>\<open>prefix\<close> of the
      program, with the rest of the program handled by the continuation premise.\<close>
lemma wlp_apply_ht_bind:
  assumes hh: "hp \<Turnstile> Pp" and ent: "Pp \<Longrightarrow>\<^sub>A Pq * Fr" and T: "<Pq> c <Qq>"
    and K: "\<And>hq r. hq \<Turnstile> Qq r * Fr * true \<Longrightarrow> wlp (g r) Qr hq"
  shows "wlp (c \<bind> g) Qr hp"
  by (rule decon_bind, rule wlp_apply_ht[OF hh ent T], rule K)

text \<open>Monolith glue, part 2: Pass A's six outputs as plain projections of @{const passA}, its
      insensitivity to the flow array's padding, and the two @{const excess} facts the imbalance
      transform needs.\<close>
lemma passA_sel:
  "edge_state fl = fst (passA fl)"
  "free_out_edges fl = fst (snd (snd (passA fl)))"
  "free_out_hi fl = fst (snd (snd (snd (passA fl))))"
  "free_in_edges fl = fst (snd (snd (snd (snd (passA fl)))))"
  "free_in_hi fl = snd (snd (snd (snd (snd (passA fl)))))"
  by (simp_all add: edge_state_def free_out_edges_def free_out_hi_def free_in_edges_def free_in_hi_def split_beta)

lemma passA_acyc_pad: "length rst = n \<Longrightarrow> passA (acyc_flow @ rst) = passA acyc_flow"
  by (rule passA_flow_cong) (auto simp: nth_append)

lemma imbalance_fold_b_arr: "fold (\<lambda>w a. a[w := a ! w + b_arr ! w]) [0..<vcount] excess = imbalance"
  by (simp add: imbalance_def b_lookup_def)

lemma length_excess: "length excess = Suc vcount"
  using passA_exc_len[of flow_list] by (simp add: excess_def split_beta)

text \<open>Segment (F) of @{const solve_imp}: reset the two CSR cursors, run Pass A on the \<^emph>\<open>acyclified\<close>
      flow array, fold the balances into the excess array, and re-zero the (now dead) acyclifier DFS
      stack for reuse as the tree builder's ``seen'' array.  Afterwards every store holds exactly the
      functional value the tree builder consumes: @{const edge_state} / @{const imbalance} /
      @{const free_out_edges} / @{const free_out_hi} / @{const free_in_edges} / @{const free_in_hi}
      of @{const acyc_flow}.  The edge-state array keeps its artificial-edge padding (@{thm [source]
      passA_imp_pad_rule}) and the flow array its @{term n} spare cells (@{thm [source]
      passA_acyc_pad}).\<close>
lemma passA_phase_triple:
  fixes fl_arr cap_arr exc_arr ba :: "'n array" and fsta snda olo ocur ilo icur oea iea :: "nat array"
    and es_arr :: "edge_tag array" and dsta :: "bool array"
  assumes some: "acyc_flow_opt = Some f'" and mfla: "m \<le> length fla"
    and agfla: "\<forall>e<m. fla ! e = acyc_flow ! e"
    and lco: "length co = vcount" and lci: "length ci = vcount" and ldl: "length dl = Suc vcount"
  shows "<fl_arr \<mapsto>\<^sub>a fla * cap_arr \<mapsto>\<^sub>a (capacity_list @ replicate n 0) * fsta \<mapsto>\<^sub>a (fst_list @ replicate n 0) * snda \<mapsto>\<^sub>a (snd_list @ replicate n 0) * es_arr \<mapsto>\<^sub>a replicate (m + n) InL * exc_arr \<mapsto>\<^sub>a (0 # replicate vcount 0) * oea \<mapsto>\<^sub>a csr_edges out_csr * olo \<mapsto>\<^sub>a out_lo * ocur \<mapsto>\<^sub>a co * iea \<mapsto>\<^sub>a csr_edges in_csr * ilo \<mapsto>\<^sub>a in_lo * icur \<mapsto>\<^sub>a ci * ba \<mapsto>\<^sub>a b_arr * dsta \<mapsto>\<^sub>a dl> do { _ \<leftarrow> arr_copy_imp olo ocur 0 vcount; _ \<leftarrow> arr_copy_imp ilo icur 0 vcount; _ \<leftarrow> passA_imp fl_arr cap_arr fsta snda es_arr exc_arr oea ocur iea icur 0 m; _ \<leftarrow> imbalance_imp exc_arr ba 0 vcount; arr_fill_imp dsta False 0 (Suc vcount) } <\<lambda>_. fl_arr \<mapsto>\<^sub>a fla * cap_arr \<mapsto>\<^sub>a (capacity_list @ replicate n 0) * fsta \<mapsto>\<^sub>a (fst_list @ replicate n 0) * snda \<mapsto>\<^sub>a (snd_list @ replicate n 0) * es_arr \<mapsto>\<^sub>a (edge_state acyc_flow @ replicate n InL) * exc_arr \<mapsto>\<^sub>a imbalance * oea \<mapsto>\<^sub>a free_out_edges acyc_flow * olo \<mapsto>\<^sub>a out_lo * ocur \<mapsto>\<^sub>a free_out_hi acyc_flow * iea \<mapsto>\<^sub>a free_in_edges acyc_flow * ilo \<mapsto>\<^sub>a in_lo * icur \<mapsto>\<^sub>a free_in_hi acyc_flow * ba \<mapsto>\<^sub>a b_arr * dsta \<mapsto>\<^sub>a replicate (Suc vcount) False>"
proof -
  have rep_es: "replicate (m + n) InL = replicate m InL @ replicate n InL" by (simp add: replicate_add)
  have pfl: "passA fla = passA acyc_flow" by (rule passA_flow_cong) (use agfla in auto)
  have caplen: "m \<le> length (capacity_list @ replicate n 0)" by (simp add: length_edges)
  have capeq: "\<And>i. i < m \<Longrightarrow> (capacity_list @ replicate n 0) ! i = capacity_list ! i" by (simp add: nth_append length_edges)
  have s0: "(replicate m InL, (0::'n) # replicate vcount 0, csr_edges out_csr, out_lo, csr_edges in_csr, in_lo) = fold (passA_step fla) [0..<0] (replicate m InL, replicate (Suc vcount) (0::'n), csr_edges out_csr, out_lo, csr_edges in_csr, in_lo)" by simp
  note PA = passA_imp_pad_rule[OF le0 mfla caplen fst_pad_mk snd_pad_mk capeq fst_pad_keys[rule_format] snd_pad_keys[rule_format] s0, where pad = "replicate n InL"]
  have E1: "fst (passA fla) = edge_state acyc_flow" using pfl passA_sel(1) by simp
  have E2: "fst (snd (passA fla)) = excess" using pfl passA_exc_acyc[OF some] by simp
  have E3: "fst (snd (snd (passA fla))) = free_out_edges acyc_flow" using pfl passA_sel(2) by simp
  have E4: "fst (snd (snd (snd (passA fla)))) = free_out_hi acyc_flow" using pfl passA_sel(3) by simp
  have E5: "fst (snd (snd (snd (snd (passA fla))))) = free_in_edges acyc_flow" using pfl passA_sel(4) by simp
  have E6: "snd (snd (snd (snd (snd (passA fla))))) = free_in_hi acyc_flow" using pfl passA_sel(5) by simp
  have IMB: "<exc_arr \<mapsto>\<^sub>a excess * ba \<mapsto>\<^sub>a b_arr> imbalance_imp exc_arr ba 0 vcount <\<lambda>_. exc_arr \<mapsto>\<^sub>a imbalance * ba \<mapsto>\<^sub>a b_arr>"
    using imbalance_imp_rule[of 0 excess b_arr exc_arr ba] by (simp add: length_excess length_b_arr imbalance_fold_b_arr)
  show ?thesis
    apply (simp only: rep_es)
    apply (sep_auto heap: arr_copy_imp_rule PA IMB arr_fill_imp_rule simp: length_out_lo length_in_lo lco lci ldl E1 E2 E3 E4 E5 E6)
    done
qed

text \<open>Segment (F)'s exit bridge: the raw stores segment (F) leaves behind — together with the three
      freshly allocated references — \<^emph>\<open>are\<close> the tree builder's state relation at the pre-seed state
      @{const dfs_raw}.  Every tree field is a fresh all-zero / all-@{term False} array of length
      @{term \<open>Suc vcount\<close>}; the augmented endpoint / capacity / flow / edge-state arrays carry their
      real prefix plus @{term n} spare artificial cells; and the empty DFS stack is the fill pointer
      @{term 0} (@{thm stk_rel_nil}).\<close>
lemma dfs_rel_raw_intro:
  fixes prnt thrd rvth lsuc snum auxa par sv soc sic olo ocur ilo icur oea iea fsta snda :: "nat array"
    and dira dsta :: "bool array" and fl_arr cap_arr cost_arr :: "'n array"
    and es_arr :: "edge_tag array" and spr pvr nxr :: "nat ref"
  assumes mfla: "m + n \<le> length fla" and agfla: "\<forall>e<m. fla ! e = acyc_flow ! e"
    and laux: "length aux0 = Suc vcount"
    and lsvl: "length svl = Suc vcount" and lsocl: "length socl = Suc vcount" and lsicl: "length sicl = Suc vcount"
  shows "dsta \<mapsto>\<^sub>a replicate (Suc vcount) False * prnt \<mapsto>\<^sub>a (0 # replicate vcount 0) * thrd \<mapsto>\<^sub>a (0 # replicate vcount 0) * rvth \<mapsto>\<^sub>a (0 # replicate vcount 0) * lsuc \<mapsto>\<^sub>a (0 # replicate vcount 0) * snum \<mapsto>\<^sub>a (0 # replicate vcount 0) * auxa \<mapsto>\<^sub>a aux0 * par \<mapsto>\<^sub>a (0 # replicate vcount 0) * dira \<mapsto>\<^sub>a (False # replicate vcount False) * pot \<mapsto>\<^sub>a (pval_zero # replicate vcount pval_zero) * fsta \<mapsto>\<^sub>a (fst_list @ replicate n 0) * snda \<mapsto>\<^sub>a (snd_list @ replicate n 0) * cap_arr \<mapsto>\<^sub>a (capacity_list @ replicate n 0) * cost_arr \<mapsto>\<^sub>a cost_list * fl_arr \<mapsto>\<^sub>a fla * es_arr \<mapsto>\<^sub>a (edge_state acyc_flow @ replicate n InL) * oea \<mapsto>\<^sub>a free_out_edges acyc_flow * olo \<mapsto>\<^sub>a out_lo * ocur \<mapsto>\<^sub>a free_out_hi acyc_flow * iea \<mapsto>\<^sub>a free_in_edges acyc_flow * ilo \<mapsto>\<^sub>a in_lo * icur \<mapsto>\<^sub>a free_in_hi acyc_flow * sv \<mapsto>\<^sub>a svl * soc \<mapsto>\<^sub>a socl * sic \<mapsto>\<^sub>a sicl * spr \<mapsto>\<^sub>r 0 * pvr \<mapsto>\<^sub>r 0 * nxr \<mapsto>\<^sub>r 0 \<Longrightarrow>\<^sub>A dfs_rel acyc_flow (edge_state acyc_flow) (free_out_edges acyc_flow) (free_out_hi acyc_flow) (free_in_edges acyc_flow) (free_in_hi acyc_flow) \<lparr>di_seen = dsta, di_tree = \<lparr>prnt_impl = prnt, thrd_impl = thrd, rvth_impl = rvth, lsuc_impl = lsuc, snum_impl = snum, aux_impl = auxa\<rparr>, di_par = par, di_dir = dira, di_pot = pot, di_fst = fsta, di_snd = snda, di_cap = cap_arr, di_cost = cost_arr, di_flow = fl_arr, di_es = es_arr, di_oe = oea, di_olo = olo, di_ohi = ocur, di_ie = iea, di_ilo = ilo, di_ihi = icur, di_sv = sv, di_soc = soc, di_sic = sic, di_sp = spr, di_prev = pvr, di_nxt = nxr\<rparr> dfs_raw"
  unfolding dfs_rel_def dfs_raw_def dfs_init_def
  apply (rule ent_ex_postI[of _ _ "fst_list @ replicate n 0"])
  apply (rule ent_ex_postI[of _ _ "snd_list @ replicate n 0"])
  apply (rule ent_ex_postI[of _ _ "capacity_list @ replicate n 0"])
  apply (rule ent_ex_postI[of _ _ "fla"])
  apply (rule ent_ex_postI[of _ _ "edge_state acyc_flow @ replicate n InL"])
  apply (rule ent_ex_postI[of _ _ "aux0"])
  apply (rule ent_ex_postI[of _ _ "svl"])
  apply (rule ent_ex_postI[of _ _ "socl"])
  apply (rule ent_ex_postI[of _ _ "sicl"])
  apply (rule ent_ex_postI[of _ _ "0::nat"])
  apply (sep_auto simp: laux lsvl lsocl lsicl mfla agfla length_vs_list length_fst_list_m length_snd_list_m length_edges nth_append)
  done

text \<open>The acyclifier's flow assertion, weakened to exactly what the tree builder needs: a store of
      at least the augmented length whose real-edge prefix is @{const acyc_flow}.  Extracting \<^emph>\<open>this\<close>
      pure part (rather than @{const flow_assn_m}'s @{term \<open>length r = n\<close>}) is what keeps an equation
      on the locale parameter @{term n} out of the proof context — with one there, every subsequent
      @{text sep_auto} substitutes @{term n} away and unfolds the whole locale.\<close>
lemma flow_assn_m_pad:
  assumes some: "acyc_flow_opt = Some f'"
  shows "flow_assn_m f' fh \<Longrightarrow>\<^sub>A (\<exists>\<^sub>A fla. fh \<mapsto>\<^sub>a fla * \<up>(m + n \<le> length fla \<and> (\<forall>e<m. fla ! e = acyc_flow ! e)))"
proof -
  have acy: "acyc_flow = f'" using some by (simp add: acyc_flow_def)
  show ?thesis
    unfolding flow_assn_m_def
    apply (rule ent_ex_preI)
    apply (rule ent_ex_postI[of _ _ "f' @ x" for x])
    apply (sep_auto simp: acy[symmetric] nth_append)
    done
qed

text \<open>Shape bridges for the capstone: the acyclifier phase restated in exactly the array shapes the
      allocation block leaves behind, so that @{text sep_auto}'s (purely syntactic) frame inference
      can apply it without a hand-supplied frame.\<close>
lemma take_flow_all: "take m flow_list = flow_list" by (simp add: length_flow length_edges)
lemma rep0_V: "(0::nat) # 0 # replicate n 0 = 0 # replicate vcount 0" by (simp add: vcount_eq)
lemma repU_V: "Unseen # Unseen # replicate n Unseen = Unseen # replicate vcount Unseen" by (simp add: vcount_eq)
lemma repF_V: "False # False # replicate n False = False # replicate vcount False" by (simp add: vcount_eq)

lemmas make_acyclic_solve_triple' =
  make_acyclic_solve_triple[unfolded take_flow_all rep0_V repU_V repF_V
    csr_lo_out csr_hi_out csr_cur_out csr_lo_in csr_hi_in csr_cur_in]

text \<open>The six side conditions of @{thm [source] build_tree_imp_raw_rule}, discharged once: the
      imbalance array is @{term \<open>Suc vcount\<close>} long (the excess array it overwrites in place is), and
      the four CSR block-boundary lists are @{term vcount} long.\<close>
lemma length_fold_upd: "length (fold (\<lambda>v arr. arr[v := f v arr]) xs ys) = length ys"
  by (induction xs arbitrary: ys) auto

lemma length_imbalance: "length imbalance = Suc vcount"
  by (simp add: imbalance_def length_excess length_fold_upd)

lemma nvc_lt: "n < vcount" by (simp add: vcount_eq)
lemma repSF: "replicate (Suc vcount) False = False # replicate vcount False" by simp
lemma lrep0: "length ((0::nat) # replicate vcount 0) = Suc vcount" by simp
lemma lim_ge: "Suc vcount \<le> length imbalance" by (simp add: length_imbalance)
lemma lol_ge: "vcount \<le> length out_lo" by (simp add: length_out_lo)
lemma lil_ge: "vcount \<le> length in_lo" by (simp add: length_in_lo)
lemma loh_ge: "vcount \<le> length out_hi" by (simp add: length_out_hi)
lemma lih_ge: "vcount \<le> length in_hi" by (simp add: length_in_hi)

lemmas build_tree_raw' = build_tree_imp_raw_rule[OF nvc_lt lim_ge lol_ge lil_ge loh_ge lih_ge]

text \<open>Two rules restated with the state record's \<^emph>\<open>components\<close> as separate parameters plus defining
      equations.  In @{const solve_imp} the DFS state record is built from array / reference
      variables that are \<^emph>\<open>bound by the program itself\<close> (the three @{term \<open>ref 0\<close>} allocations), so a
      rule whose program mentions @{term \<open>di_nxt st\<close>} can never be unified against the program's
      @{term \<open>Ref.lookup nxt_ref\<close>}: higher-order unification would have to invert a record selector.
      Taking the component as a parameter and discharging @{term \<open>di_nxt st = nx\<close>} \<^emph>\<open>afterwards\<close> — once
      the enclosing entailment has pinned @{term st} from the heap — sidesteps this.\<close>
lemma dfs_rel_rd_nxt2:
  assumes "di_nxt st = nx"
  shows "<dfs_rel fl0 es0 oe oh ie ih st s> Ref.lookup nx <\<lambda>r. dfs_rel fl0 es0 oe oh ie ih st s * \<up>(r = ds_nxt s)>"
  using dfs_rel_rd_nxt[of fl0 es0 oe oh ie ih st s] assms by simp

lemma ns_phase_triple2:
  assumes some: "acyc_flow_opt \<noteq> None" and mpos: "0 < marc"
    and e1: "di_fst st = a1" and e2: "di_snd st = a2" and e3: "di_cost st = a3" and e4: "di_cap st = a4"
    and e5: "di_flow st = a5" and e6: "di_pot st = a6" and e7: "di_tree st = a7" and e8: "di_par st = a8"
    and e9: "di_dir st = a9" and e10: "di_es st = a10" and e11: "di_sv st = a11" and e12: "di_soc st = a12"
  shows "<sarr \<mapsto>\<^sub>a replicate max_candidates 0 * cref \<mapsto>\<^sub>r 0 * lref \<mapsto>\<^sub>r 0 * dfs_rel acyc_flow (edge_state acyc_flow) (free_out_edges acyc_flow) (free_out_hi acyc_flow) (free_in_edges acyc_flow) (free_in_hi acyc_flow) st (build_tree acyc_flow) * ofl \<mapsto>\<^sub>a fs0> ns_loop_prog vcount m marc block_size min_candidates max_candidates a1 a2 a3 a4 (ns_impl_state.make a5 a6 a7 a8 a9 a10 (sarr, cref, lref) a11 a12) <\<lambda>res. \<exists>\<^sub>A fl'. a5 \<mapsto>\<^sub>a fl' * a3 \<mapsto>\<^sub>a cost_list * ofl \<mapsto>\<^sub>a fs0 * true * \<up>(marc \<le> length fl' \<and> solve = (if res = Network_Simplex.unbounded then Neg_inf_cycle else if list_all (\<lambda>k. fl' ! k = 0) [m..<marc] then Optimum (take m fl') else Infeasible))>"
  using ns_phase_triple'[OF some mpos, where st = st and sarr = sarr and cref = cref and lref = lref]
  by (simp only: e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12)

lemma marc_eq: "marc = m + ds_nxt (build_tree acyc_flow)" by (simp add: marc_def Kart_def art_tree_def)
lemma marc_pos: "0 < marc" using num_edges_gtr_0 by (simp add: marc_def)
lemma some_ne: "acyc_flow_opt = Some f' \<Longrightarrow> acyc_flow_opt \<noteq> None" by simp

text \<open>The \<^emph>\<open>else\<close> branch of @{const solve_imp} — Pass A, the imbalance transform, the tree builder, the
      network-simplex loop and the verdict tail — as one Hoare triple over the raw arrays that the
      allocation and acyclifier phases leave behind.

      Two points of technique.  First, the precondition keeps the acyclifier's @{const flow_assn_m}
      \<^emph>\<open>last\<close>, and the proof immediately weakens it with @{thm [source] flow_assn_m_pad}: extracting
      @{const flow_assn_m}'s own pure part would put the equation @{term \<open>length r = n\<close>} into the
      context, after which every @{method sep_auto} substitutes @{term n} away and unfolds the whole
      locale.  Second, @{method sep_auto} always decomposes a goal down to its \<^emph>\<open>leftmost atomic\<close>
      command, so a block triple can never be applied to an already-decomposed goal; instead each
      block is spliced in by re-associating the binds (four @{method subst} of
      @{thm [source] bind_bind}, matching the five commands of @{thm [source] passA_phase_triple})
      and then applying @{thm [source] ht_bind} / @{thm [source] wlp_apply_ht} with an explicit frame.
      In the @{thm [source] ent_frame_fwdI} step the two premises must be discharged \<^emph>\<open>out of order\<close>
      (\<open>prefer\<close>): all seven tree arrays hold the same list and all three references hold
      @{term \<open>0::nat\<close>}, so solving the forward entailment first lets frame inference pick a wrong
      assignment of arrays to record slots, whereas the other order pins the record from the goal.\<close>
lemma solve_tail_triple:
  fixes fl_arr cap_arr cost_arr exc_arr ba outfl :: "'n array"
    and fsta snda olo ocur ohi ilo icur ihi oea iea pra tha rva lsa sna aua paa sva soa sia :: "nat array"
    and dira dsta :: "bool array" and es_arr :: "edge_tag array"
  assumes some: "acyc_flow_opt = Some f'"
    and lco: "length co = vcount" and lci: "length ci = vcount" and ldl: "length dl = Suc vcount"
    and lvl: "length vl0 = Suc vcount" and lel: "length el0 = Suc vcount" and lcnt: "length cntl = Suc vcount"
    and lfs: "m \<le> length fs0"
  shows "<oea \<mapsto>\<^sub>a csr_edges out_csr * olo \<mapsto>\<^sub>a out_lo * ohi \<mapsto>\<^sub>a out_hi * ocur \<mapsto>\<^sub>a co * iea \<mapsto>\<^sub>a csr_edges in_csr * ilo \<mapsto>\<^sub>a in_lo * ihi \<mapsto>\<^sub>a in_hi * icur \<mapsto>\<^sub>a ci * cap_arr \<mapsto>\<^sub>a (capacity_list @ replicate n 0) * cost_arr \<mapsto>\<^sub>a cost_list * fsta \<mapsto>\<^sub>a (fst_list @ replicate n 0) * snda \<mapsto>\<^sub>a (snd_list @ replicate n 0) * sva \<mapsto>\<^sub>a vl0 * soa \<mapsto>\<^sub>a el0 * dsta \<mapsto>\<^sub>a dl * sia \<mapsto>\<^sub>a cntl * exc_arr \<mapsto>\<^sub>a (0 # replicate vcount 0) * dira \<mapsto>\<^sub>a (False # replicate vcount False) * paa \<mapsto>\<^sub>a (0 # replicate vcount 0) * aua \<mapsto>\<^sub>a (0 # replicate vcount 0) * sna \<mapsto>\<^sub>a (0 # replicate vcount 0) * lsa \<mapsto>\<^sub>a (0 # replicate vcount 0) * rva \<mapsto>\<^sub>a (0 # replicate vcount 0) * tha \<mapsto>\<^sub>a (0 # replicate vcount 0) * pra \<mapsto>\<^sub>a (0 # replicate vcount 0) * poa \<mapsto>\<^sub>a (pval_zero # replicate vcount pval_zero) * es_arr \<mapsto>\<^sub>a replicate (m + n) InL * outfl \<mapsto>\<^sub>a fs0 * ba \<mapsto>\<^sub>a b_arr * flow_assn_m f' fl_arr> arr_copy_imp olo ocur 0 vcount \<bind> (\<lambda>_. arr_copy_imp ilo icur 0 vcount \<bind> (\<lambda>_. passA_imp fl_arr cap_arr fsta snda es_arr exc_arr oea ocur iea icur 0 m \<bind> (\<lambda>_. imbalance_imp exc_arr ba 0 vcount \<bind> (\<lambda>_. arr_fill_imp dsta False 0 (Suc vcount) \<bind> (\<lambda>_. ref 0 \<bind> (\<lambda>sp_ref. ref 0 \<bind> (\<lambda>prev_ref. ref 0 \<bind> (\<lambda>nxt_ref. build_tree_imp \<lparr>di_seen = dsta, di_tree = \<lparr>prnt_impl = pra, thrd_impl = tha, rvth_impl = rva, lsuc_impl = lsa, snum_impl = sna, aux_impl = aua\<rparr>, di_par = paa, di_dir = dira, di_pot = poa, di_fst = fsta, di_snd = snda, di_cap = cap_arr, di_cost = cost_arr, di_flow = fl_arr, di_es = es_arr, di_oe = oea, di_olo = olo, di_ohi = ocur, di_ie = iea, di_ilo = ilo, di_ihi = icur, di_sv = sva, di_soc = soa, di_sic = sia, di_sp = sp_ref, di_prev = prev_ref, di_nxt = nxt_ref\<rparr> exc_arr ohi ihi m vcount n \<bind> (\<lambda>_. Ref.lookup nxt_ref \<bind> (\<lambda>Kart. Array.new max_candidates 0 \<bind> (\<lambda>sel_arr. ref 0 \<bind> (\<lambda>scur. ref 0 \<bind> (\<lambda>slen. ns_loop_prog vcount m (m + Kart) block_size min_candidates max_candidates fsta snda cost_arr cap_arr (ns_impl_state.make fl_arr poa \<lparr>prnt_impl = pra, thrd_impl = tha, rvth_impl = rva, lsuc_impl = lsa, snum_impl = sna, aux_impl = aua\<rparr> paa dira es_arr (sel_arr, scur, slen) sva soa) \<bind> (\<lambda>res. if res = Network_Simplex.unbounded then Heap_Monad.return NegInfCycleF else scan_art_imp fl_arr m (m + Kart) \<bind> (\<lambda>allz. if allz then arr_copy_imp fl_arr outfl 0 m \<bind> (\<lambda>_. Heap_Monad.return OptimalF) else Heap_Monad.return InfeasibleF))))))))))))))) <\<lambda>r. \<exists>\<^sub>A fs'. outfl \<mapsto>\<^sub>a fs' * cost_arr \<mapsto>\<^sub>a cost_list * ba \<mapsto>\<^sub>a b_arr * \<up>(r = status_of solve \<and> length fs' = length fs0 \<and> (\<forall>fs. solve = Optimum fs \<longrightarrow> take m fs' = fs)) * true>"
  apply (rule ht_cons_pre[OF ent_star_mono[OF ent_refl flow_assn_m_pad[OF some]]])
  apply (simp only: ex_assn_move_out)
  apply (rule ht_exEI)
  apply (simp only: mult.assoc[symmetric])
  apply (rule ht_extract_pre_pure(1))
  subgoal premises pre for fla
  proof -
    have mfla: "m \<le> length fla" using pre by simp
    have agfla: "\<forall>e<m. fla ! e = acyc_flow ! e" using pre by simp
    have mnfla: "m + n \<le> length fla" using pre by simp
    note PA = passA_phase_triple[OF some mfla agfla lco lci ldl, unfolded bind_bind[symmetric]]
    note DR = dfs_rel_raw_intro[OF mnfla agfla lrep0 lvl lel lcnt, unfolded repSF]
    show ?thesis
      apply (subst bind_bind[symmetric])
      apply (subst bind_bind[symmetric])
      apply (subst bind_bind[symmetric])
      apply (subst bind_bind[symmetric])
      apply (rule ht_bind[OF ht_cons_pre[OF _ ht_frame[OF PA, where R = "cost_arr \<mapsto>\<^sub>a cost_list * sva \<mapsto>\<^sub>a vl0 * soa \<mapsto>\<^sub>a el0 * sia \<mapsto>\<^sub>a cntl * dira \<mapsto>\<^sub>a (False # replicate vcount False) * paa \<mapsto>\<^sub>a (0 # replicate vcount 0) * aua \<mapsto>\<^sub>a (0 # replicate vcount 0) * sna \<mapsto>\<^sub>a (0 # replicate vcount 0) * lsa \<mapsto>\<^sub>a (0 # replicate vcount 0) * rva \<mapsto>\<^sub>a (0 # replicate vcount 0) * tha \<mapsto>\<^sub>a (0 # replicate vcount 0) * pra \<mapsto>\<^sub>a (0 # replicate vcount 0) * poa \<mapsto>\<^sub>a (pval_zero # replicate vcount pval_zero) * ohi \<mapsto>\<^sub>a out_hi * ihi \<mapsto>\<^sub>a in_hi * outfl \<mapsto>\<^sub>a fs0"]]])
       apply sep_auto
      apply (rule wlp_apply_ht[OF _ _ build_tree_raw', where F = "ba \<mapsto>\<^sub>a b_arr * outfl \<mapsto>\<^sub>a fs0 * true"])
        apply assumption
       apply (rule ent_frame_fwdI[OF _ DR, where F = "exc_arr \<mapsto>\<^sub>a imbalance * ohi \<mapsto>\<^sub>a out_hi * ihi \<mapsto>\<^sub>a in_hi * ba \<mapsto>\<^sub>a b_arr * outfl \<mapsto>\<^sub>a fs0 * true"])
        prefer 2
        apply sep_auto
      apply (rule wlp_apply_ht[OF _ _ dfs_rel_rd_nxt2, where F = "exc_arr \<mapsto>\<^sub>a imbalance * ohi \<mapsto>\<^sub>a out_hi * ihi \<mapsto>\<^sub>a in_hi * ba \<mapsto>\<^sub>a b_arr * outfl \<mapsto>\<^sub>a fs0 * true"])
         apply assumption
        apply sep_auto
      apply (rule wlp_apply_ht[OF _ _ ns_phase_triple2[OF some_ne[OF some] marc_pos, unfolded marc_eq, where ofl = outfl], where F = "exc_arr \<mapsto>\<^sub>a imbalance * ohi \<mapsto>\<^sub>a out_hi * ihi \<mapsto>\<^sub>a in_hi * ba \<mapsto>\<^sub>a b_arr * true"])
        apply assumption
       apply sep_auto
       apply (sep_auto heap: scan_art_imp_rule arr_copy_imp_rule simp: lfs)
      done
  qed
  done

text \<open>\<^emph>\<open>Total correctness of the whole solver.\<close>  @{const solve_imp} — allocation and padding of the six
      input arrays, the two CSR builds, the edged-vertex materialisation, the acyclifier, Pass A, the
      spanning-tree build, the network-simplex loop and the verdict tail — returns exactly
      @{term \<open>status_of solve\<close>}, and on @{const Optimum} the caller's flow array holds the optimal
      @{term b}-flow in its first @{term m} cells.

      The script walks the program phase by phase.  Each @{method sep_auto} consumes one phase; the
      rules are pre-instantiated (@{thm [source] make_acyclic_solve_triple'} and friends) so that frame
      inference — which is purely \<^emph>\<open>syntactic\<close> — finds the frame without any hand-supplied
      @{text \<open>where F = \<dots>\<close>}.  The acyclifier splits the proof in two: its @{const None} verdict is the
      infinite-cycle branch, closed outright, and its @{term \<open>Some f'\<close>} verdict is the whole rest of the
      solver, which is @{thm [source] solve_tail_triple}.\<close>
theorem solve_imp_correct:
  "<in_fst \<mapsto>\<^sub>a fst_list * in_snd \<mapsto>\<^sub>a snd_list * in_cap \<mapsto>\<^sub>a capacity_list *
    in_cost \<mapsto>\<^sub>a cost_list * in_flow \<mapsto>\<^sub>a flow_list * in_b \<mapsto>\<^sub>a b_arr>
     solve_imp n m block_size min_candidates max_candidates
               in_fst in_snd in_cap in_cost in_flow in_b
   <\<lambda>r. \<exists>\<^sub>A fs'. in_fst \<mapsto>\<^sub>a fst_list * in_snd \<mapsto>\<^sub>a snd_list * in_cap \<mapsto>\<^sub>a capacity_list *
                in_cost \<mapsto>\<^sub>a cost_list * in_flow \<mapsto>\<^sub>a fs' * in_b \<mapsto>\<^sub>a b_arr *
                \<up>(r = status_of solve \<and> length fs' = m \<and>
                  (\<forall>fs. solve = Optimum fs \<longrightarrow> take m fs' = fs)) * true>"
  unfolding solve_imp_def Let_def
  apply (simp only: vcount_eq[symmetric])
  apply (sep_auto heap: arr_copy_imp_rule
           simp: length_fst_list_m length_snd_list_m length_edges length_flow)
  apply (sep_auto heap: build_csr_out_pad_over_c[OF fst_pad_mk fst_pad_bd fst_pad_keys
                          le_SucI[OF order_refl], simplified])
  apply (sep_auto heap: arr_fill_imp_rule simp: cto_pad_len' cto_pad_drop' replicate_append_same)
  apply (sep_auto heap: build_csr_in_pad_over_c[OF snd_pad_mk snd_pad_bd snd_pad_keys
                          le_SucI[OF order_refl], simplified])
  apply (simp only: csr_assn_def prod.case csr_lo_out csr_hi_out csr_cur_out
                    csr_lo_in csr_hi_in csr_cur_in)
  apply (sep_auto heap: count_edged_imp_rule[OF edg_v1 edg_l1 edg_l2 edg_l3 edg_l4]
                        fill_edged_imp_rule[OF edg_v1 edg_l1 edg_l2 edg_l3 edg_l4]
                  simp: edged_lst_eq_vs_list)
  apply (sep_auto heap: make_acyclic_solve_triple')
  subgoal by (sep_auto simp: acyc_flow_opt_def solve_none length_flow length_edges)
  apply (rule wlp_apply_ht[OF _ _ solve_tail_triple,
           where F = "in_fst \<mapsto>\<^sub>a fst_list * in_snd \<mapsto>\<^sub>a snd_list * in_cap \<mapsto>\<^sub>a capacity_list * true"])
   apply assumption
  apply sep_auto
  prefer 9
  apply (sep_auto simp: length_flow length_edges)
  apply (simp_all add: acyc_flow_opt_def count_fold_length length_flow length_edges)
  done

subsection \<open>The specification of @{const solve_imp}, free of the functional implementation\<close>

text \<open>@{thm [source] solve_imp_correct} still mentions the functional @{const solve}.  Composing it with
      @{thm [source] solve_correct} — the three verdicts of the functional solver, stated against the
      input network @{term original_network} — removes that reference: what remains is a statement
      relating the imperative program's \<^emph>\<open>returned flag and flow array\<close> directly to the
      minimum-cost-flow problem the input lists describe.

      The composition also has to eliminate the two \<^emph>\<open>derived\<close> balance constants, so that the balances
      in the specification are read off the caller's own @{term b_list}.  @{const b_arr} is the scatter
      of @{term b_list} into a @{term \<open>Suc vcount\<close>}-slot array at the vertex names @{term vs_list} —
      which, the names being the dense range @{term \<open>[Suc 0..<Suc n]\<close>}, is just @{term b_list} framed by
      the null-sentinel slot and the artificial-root slot.\<close>
lemma b_arr_eq: "b_arr = 0 # b_list @ [0]"
proof -
  have lb: "length b_list = n" by (rule length_b)
  have lvs: "length vs_list = n" by (rule length_vs_list)
  have dz: "distinct (map fst (zip vs_list b_list))"
    using distinct_vs_list_code by (simp add: lvs lb)
  have lenA: "length b_arr = Suc (Suc n)" by (simp add: length_b_arr vcount_eq)
  have zl: "\<And>v x. (v, x) \<in> set (zip vs_list b_list) \<Longrightarrow> v \<in> {Suc 0..n}"
    by (auto simp: set_vs_list[symmetric] dest: set_zip_leftD)
  show ?thesis
  proof (rule nth_equalityI)
    show "length b_arr = length (0 # b_list @ [0])" using lenA lb by simp
  next
    fix i assume "i < length b_arr"
    hence iv: "i < Suc (Suc n)" using lenA by simp
    show "b_arr ! i = (0 # b_list @ [0]) ! i"
    proof (cases i)
      case 0
      have r0: "replicate (Suc vcount) (0::'n) ! 0 = 0" by (simp add: vcount_eq del: replicate_Suc)
      have "b_arr ! 0 = replicate (Suc vcount) (0::'n) ! 0"
        unfolding b_arr_def by (rule foldl_scatter_miss) (use zl in force)
      thus ?thesis using 0 r0 by simp
    next
      case (Suc j)
      show ?thesis
      proof (cases "j < n")
        case True
        note jl = True
        have n1: "zip vs_list b_list ! j = (vs_list ! j, b_list ! j)" using jl lvs lb by simp
        have n2: "j < length (zip vs_list b_list)" using jl lvs lb by simp
        have nvs: "vs_list ! j = Suc j" using jl by (simp add: vs_list_def del: upt_Suc)
        have mem: "(Suc j, b_list ! j) \<in> set (zip vs_list b_list)"
          using nth_mem[OF n2] n1 nvs by simp
        have lt: "Suc j < length (replicate (Suc vcount) (0::'n))" using jl by (simp add: vcount_eq)
        have "b_arr ! (Suc j) = b_list ! j"
          unfolding b_arr_def by (rule foldl_scatter_hit[OF dz mem lt])
        thus ?thesis using Suc jl lb by (simp add: nth_append)
      next
        case False
        hence jn: "j = n" using iv Suc by simp
        have r0: "replicate (Suc vcount) (0::'n) ! (Suc n) = 0"
          by (simp add: vcount_eq del: replicate_Suc)
        have "b_arr ! (Suc n) = replicate (Suc vcount) (0::'n) ! (Suc n)"
          unfolding b_arr_def by (rule foldl_scatter_miss) (use zl in force)
        hence z: "b_arr ! (Suc n) = 0" using r0 by simp
        thus ?thesis using Suc jn lb by (simp add: nth_append)
      qed
    qed
  qed
qed

text \<open>Hence, at every vertex of the input network — the vertices are edge endpoints, so they lie in
      @{term \<open>{Suc 0..n}\<close>} — the balance @{const b_lookup} reads is the entry of @{term \<open>0 # b_list\<close>}
      at that vertex \<^emph>\<open>name\<close>.  This is the functional mirror of what the code does: the caller passes
      the array @{term \<open>0 # b_list @ [0]\<close>} and the program indexes it by the vertex name, slot
      @{term \<open>0::nat\<close>} being the null sentinel and slot @{term \<open>Suc n\<close>} the artificial root.  (The
      input list @{term b_list} is itself indexed from @{term \<open>0::nat\<close>}, its entry @{term i} being the
      balance of vertex @{term \<open>Suc i\<close>} — the convention @{thm [source] isolated_zero} already uses;
      prefixing the sentinel slot absorbs that shift.)  The balance function only ever occurs applied
      to vertices — \<open>isbflow\<close> constrains it on @{term \<open>original_network.\<V>\<close>} alone — so the two agree
      wherever it matters and may be exchanged inside \<open>isbflow\<close> and \<open>is_Opt\<close>.\<close>
lemma b_lookup_V:
  assumes "v \<in> original_network.\<V>" shows "b_lookup v = (0 # b_list) ! v"
proof -
  have "v \<in> set vs_list" using assms V_sub_vs_list by blast
  hence v: "v \<le> n" by (auto simp: set_vs_list)
  have lb: "length b_list = n" by (rule length_b)
  have key: "(0 # b_list @ [0]) ! v = (0 # b_list) ! v"
  proof (cases v)
    case 0 thus ?thesis by simp
  next
    case (Suc k)
    hence kn: "k < n" using v by simp
    thus ?thesis using Suc lb by (simp add: nth_append)
  qed
  show ?thesis by (simp add: b_lookup_def b_arr_eq key)
qed

lemma isbflow_cong_b:
  "original_network.isbflow f (\<lambda>v. h (b_lookup v))
   = original_network.isbflow f (\<lambda>v. h ((0 # b_list) ! v))"
  by (auto simp: original_network.isbflow_def b_lookup_V)

lemma is_Opt_cong_b:
  "original_network.is_Opt (\<lambda>v. h (b_lookup v)) f
   = original_network.is_Opt (\<lambda>v. h ((0 # b_list) ! v)) f"
  by (auto simp: original_network.is_Opt_def original_network.isbflow_def b_lookup_V)

text \<open>The pure part of the composition.\<close>
lemma solve_verdict_transfer:
  assumes r: "r = status_of solve" and len: "length fs' = m"
      and tk: "\<forall>fs. solve = Optimum fs \<longrightarrow> take m fs' = fs"
  shows "(case r of
            OptimalF \<Rightarrow> original_network.is_Opt (\<lambda>v. h ((0 # b_list) ! v)) (h \<circ> nth fs')
          | InfeasibleF \<Rightarrow> \<nexists>f. original_network.isbflow f (\<lambda>v. h ((0 # b_list) ! v))
          | NegInfCycleF \<Rightarrow> neg_infty_cycle)"
proof (cases solve)
  case (Optimum fs)
  have e: "fs' = fs" using tk Optimum len by (simp add: take_all)
  show ?thesis using r Optimum e solve_correct(1)[OF Optimum] is_Opt_cong_b by simp
next
  case Infeasible
  thus ?thesis using r solve_correct(2) isbflow_cong_b by simp
next
  case Neg_inf_cycle
  thus ?thesis using r solve_correct(3) by simp
qed

text \<open>Monotonicity of the pure assertion.  The final entailment must \<^emph>\<open>not\<close> be left to
      @{method sep_auto}: its @{method clarsimp} would orient the conjunct @{term \<open>length fs' = m\<close>} the
      wrong way and substitute the locale parameter @{term m} away, unfolding every locale
      abbreviation — @{const solve} would become \<open>initial_basis_code_spec.solve capacity_list \<dots>
      (length fs') \<dots>\<close> — and leaving an unprovable goal.  Splitting the entailment with
      @{thm [source] ent_star_mono} keeps the equation out of the simplifier's hands.\<close>
lemma ent_pure_mono: "(P \<Longrightarrow> Q) \<Longrightarrow> \<up>P \<Longrightarrow>\<^sub>A \<up>Q"
  by (cases P) (auto simp: entails_def)

text \<open>\<^emph>\<open>The specification of the imperative solver.\<close>  The caller supplies the six input arrays — the
      balance array being @{term b_list} framed by the sentinel and root slots — and gets back a flow
      array of exactly @{term m} entries: on @{const OptimalF} a minimum-cost @{term b}-flow of the
      input network, on @{const InfeasibleF} the information that no @{term b}-flow exists at all, and
      on @{const NegInfCycleF} that the network has a negative cycle of infinite capacity, so no
      minimum exists.  The five read-only input arrays come back unchanged.  Apart from
      @{const solve_imp} itself, nothing in this statement refers to the implementation: the balances
      are read directly off the caller's @{term b_list}.\<close>
corollary solve_imp_spec:
  "<in_fst \<mapsto>\<^sub>a fst_list * in_snd \<mapsto>\<^sub>a snd_list * in_cap \<mapsto>\<^sub>a capacity_list *
    in_cost \<mapsto>\<^sub>a cost_list * in_flow \<mapsto>\<^sub>a flow_list * in_b \<mapsto>\<^sub>a (0 # b_list @ [0])>
     solve_imp n m block_size min_candidates max_candidates
               in_fst in_snd in_cap in_cost in_flow in_b
   <\<lambda>r. \<exists>\<^sub>A fs'. in_fst \<mapsto>\<^sub>a fst_list * in_snd \<mapsto>\<^sub>a snd_list * in_cap \<mapsto>\<^sub>a capacity_list *
                in_cost \<mapsto>\<^sub>a cost_list * in_flow \<mapsto>\<^sub>a fs' * in_b \<mapsto>\<^sub>a (0 # b_list @ [0]) *
                \<up>(length fs' = m \<and>
                  (case r of
                     OptimalF \<Rightarrow> original_network.is_Opt (\<lambda>v. h ((0 # b_list) ! v)) (h \<circ> nth fs')
                   | InfeasibleF \<Rightarrow> \<nexists>f. original_network.isbflow f (\<lambda>v. h ((0 # b_list) ! v))
                   | NegInfCycleF \<Rightarrow> neg_infty_cycle)) * true>"
  apply (simp only: b_arr_eq[symmetric])
  apply (rule ht_cons_post_prec[OF solve_imp_correct])
  apply (rule ent_ex_preI)
  apply (rule ent_ex_postI)
  apply (rule ent_star_mono[OF ent_star_mono[OF ent_refl ent_pure_mono] ent_refl])
  apply (elim conjE)
  apply (rule conjI)
   apply assumption
  apply (rule solve_verdict_transfer; assumption)
  done
end

section \<open>A worked example: 10 vertices, 40 edges\<close>

text \<open>A random well-formed min-cost-flow instance meeting the locale conditions: vertices @{term \<open>1::nat\<close>}
      \<dots> @{term \<open>10::nat\<close>} (name @{term \<open>0::nat\<close>} is the reserved null sentinel), 40 directed edges whose
      first ten form a Hamiltonian cycle so \<^emph>\<open>every vertex is incident to an edge\<close> (no lonely vertex)
      and the graph is connected; capacities / costs in \<open>[1, 50]\<close>; the initial flow is random but
      \<^emph>\<open>capacity-complying\<close> (\<open>0 \<le> f \<le> cap\<close>); and the balances (index @{term \<open>1::nat\<close>}\<dots>@{term \<open>10::nat\<close>},
      with the sentinel and root slots @{term 0}) lie in \<open>[-50, 50]\<close> and \<^emph>\<open>sum to zero\<close> (flow
      conservation).  The selector is tuned with block size @{term \<open>10::nat\<close>}, min / max candidates
      @{term \<open>4::nat\<close>} / @{term \<open>16::nat\<close>}.  The optimum @{term b}-flow, if one exists, is written back
      into the first @{term \<open>40::nat\<close>} cells of the input flow array, which we freeze and return
      alongside the status flag.\<close>

definition solve_sample :: "(solve_status \<times> int list) Heap" where
  "solve_sample = do {
     in_fst  \<leftarrow> Array.of_list
       [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 10, 6, 7, 10, 8, 7, 10, 3, 1,
        9, 6, 8, 5, 8, 4, 4, 8, 1, 7, 7, 7, 7, 4, 4, 8, 4, 1, 9, 6 :: nat];
     in_snd  \<leftarrow> Array.of_list
       [2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 2, 10, 2, 8, 9, 4, 8, 8, 2,
        8, 7, 9, 4, 1, 9, 9, 7, 9, 2, 5, 1, 6, 10, 5, 9, 10, 5, 5, 5 :: nat];
     in_cap  \<leftarrow> Array.of_list
       [42, 24, 40, 5, 36, 29, 29, 32, 46, 24, 13, 50, 17, 13, 45, 4, 9, 39, 30, 18,
        28, 21, 50, 16, 10, 25, 48, 32, 26, 37, 24, 1, 33, 2, 34, 50, 33, 45, 48, 39 :: int];
     in_cost \<leftarrow> Array.of_list
       [47, 6, 33, 4, 13, 19, 37, 20, 39, 43, 22, 16, 24, 33, 32, 11, 28, 49, 2, 47,
        15, 22, 1, 25, 25, 28, 3, 6, 7, 47, 39, 40, 8, 41, 50, 42, 7, 20, 20, 10 :: int];
     in_flow \<leftarrow> Array.of_list
       [10, 8, 16, 5, 23, 15, 16, 16, 32, 4, 2, 8, 2, 10, 35, 2, 3, 37, 4, 9,
        0, 10, 31, 1, 2, 22, 12, 25, 6, 37, 8, 1, 32, 2, 21, 15, 29, 13, 31, 10 :: int];
     in_b    \<leftarrow> Array.of_list
       [0, 10, (- 6), (- 24), (- 16), 21, (- 14), 7, 8, 17, (- 3), 0 :: int];
     status \<leftarrow> solve_imp 10 40 10 4 16 in_fst in_snd in_cap in_cost in_flow in_b;
     f \<leftarrow> Array.freeze in_flow;
     return (status, f) }"

text \<open>The instance is kept as a sanity check on the shape of the interface; it is not run here, so
      loading this theory stays free of code compilation.  The solver that is actually generated is
      \<open>dimacs_solve_prog\<close> of \<open>DIMACS_Solver\<close>, whose exported SML sits next to it.\<close>

end
