theory Quadratic_Blossom_Search
  imports
    Blossom_Executable.Blossom_Forest_Spec
    Blossom_Executable.Alternating_Forest_Contraction
    Blossom_Executable.Find_Aug_Path_Subprocedures
    Data_Structures.Bounded_Queue_Specs
    Data_Structures.Bounded_Stack_Specs
    Data_Structures.Fixed_Univ_Map_Specs
    Data_Structures.Fixed_Univ_Set_Specs
    Data_Structures.Iterable_Set_Specs
    Data_Structures.UnionFind_Representative_Specs
begin

provenance ai_human

named_theorems call_cond_elims
named_theorems call_cond_intros
named_theorems ret_holds_intros
named_theorems invar_props_intros
named_theorems invar_props_elims
named_theorems invar_holds_intros
named_theorems state_rel_intros
named_theorems state_rel_holds_intros
named_theorems termination_intros

section "Ordered observations of the existing blossom forest"

text "This draft extends the merge interface by an ordered observation. The two additional
  laws must be discharged by the existing implementation before an executable instantiation.
  They do not add matching assumptions to the blossom forest."

locale Blossom_Forest_Ordered =
  blossom_forest_merge_spec where collect_elems = collect_elems and merge = merge
  for collect_elems :: "'hierarchy \<Rightarrow> 'v \<Rightarrow> 'v set"
    and merge :: "'hierarchy \<Rightarrow> 'v list \<Rightarrow> 'v \<Rightarrow> 'hierarchy" +
  fixes children :: "'hierarchy \<Rightarrow> 'v \<Rightarrow> 'v list"
  assumes children_merge:
    "blossom_forest_merge_precond H cs b \<Longrightarrow> children (merge H cs b) b = cs"
    "\<lbrakk>blossom_forest_merge_precond H cs b; a \<in> all_ids H\<rbrakk>
      \<Longrightarrow> children (merge H cs b) a = children H a"

section "Cached observations of the blossom hierarchy"

locale Blossom_Routing =
  Bases: fixed_univ_map K base_invar base_update base_lookup +
  Links: fixed_univ_map K link_invar link_update link_lookup
  for K :: "'v set"
    and base_invar :: "'bases \<Rightarrow> bool"
    and base_update :: "'bases \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'bases"
    and base_lookup :: "'bases \<Rightarrow> 'v \<Rightarrow> 'v"
    and link_invar :: "'links \<Rightarrow> bool"
    and link_update :: "'links \<Rightarrow> 'v \<Rightarrow> ('v \<times> nat) \<Rightarrow> 'links"
    and link_lookup :: "'links \<Rightarrow> 'v \<Rightarrow> ('v \<times> nat)"
begin

definition "initial_bases D vs = foldl (\<lambda>D v. base_update D v v) D vs"

definition "record_parents N cs b =
  snd (foldl (\<lambda>(i, N) c. (Suc i, link_update N c (b, i)))
    (0, N) cs)"

text "A child receives its parent and cycle position when it is merged. The base of a
  new blossom is read from its first child. These maps cache observations of the
  ordered hierarchy. Root parents and leaf hints are never read. Only a newly created
  blossom needs its hint cleared; the supplied leaf entries may retain arbitrary values."

end

section "The search state"

datatype 'v Quadratic_Blossom_Search_status =
    Quadratic_Searching
  | Quadratic_Exhausted
  | Quadratic_Path "'v list" "('v \<times> 'v) list"

record ('v, 'forest, 'mate, 'hierarchy, 'queue, 'uf, 'owners, 'cursor, 'edges, 'bases, 'links)
    Quadratic_Blossom_Search_state =
  qbs_forest :: 'forest
  qbs_matching :: 'mate
  qbs_hierarchy :: 'hierarchy
  qbs_queue :: 'queue
  qbs_current :: 'v
  qbs_component :: 'v
  qbs_components :: 'uf
  qbs_owners :: 'owners
  qbs_neighbours :: 'cursor
  qbs_forest_edges :: 'edges
  qbs_cycle_edges :: 'edges
  qbs_bases :: 'bases
  qbs_parents :: 'links
  qbs_hints :: 'links
  qbs_fresh :: 'queue
  qbs_status :: "'v Quadratic_Blossom_Search_status"

section "The ADT composition"

locale Quadratic_Blossom_Search =
  Graph: Pair_Graph_Specs_Read_Only
    where insert = adj_insert and isin = adj_isin and t_set = adj_abstract
      and sel = adj_choose and vset_empty = adj_empty and vset_delete = adj_delete
      and vset_inv = adj_invar and lookup = graph_lookup and adjmap_inv = graph_invar +
  Fset: fixed_univ_set K fset_invar fset_abstract fset_empty fset_insert fset_delete fset_isin +
  Forest: alternating_forest_ordinary_extension_spec
    where evens = forest_evens and odds = forest_odds and roots = forest_roots
      and get_path = forest_path and abstract_forest = forest_abstract
      and forest_invar = forest_invar and vset_invar = fset_invar
      and vset_to_set = fset_abstract and vset_empty = fset_empty and forest_univ = K
      and empty_forest = forest_empty and extend_forest_even_unclassified = forest_extend +
  Contract: alternating_forest_fork_contraction_spec
    where evens = forest_evens and odds = forest_odds and roots = forest_roots
      and get_path = forest_path and abstract_forest = forest_abstract
      and forest_invar = forest_invar and vset_invar = fset_invar
      and vset_to_set = fset_abstract and K = K and contract_fork = forest_contract +
  Mate: blossom_matching
    where K = K and nil = nil and empty_matching = mate_empty and matching_invar = mate_invar
      and lookup_partner = "\<lambda>M v. if v \<in> K \<and> mate_partner M v \<noteq> nil
        then Some (mate_partner M v) else None" and get_partner = mate_partner
      and augment = mate_augment and matching_abstract = mate_abstract
      and contract_path = mate_contract and expand_path_at_matched = mate_expand
      and add_alternatingly = mate_add +
  Hierarchy: Blossom_Forest_Ordered
    where all_ids = hierarchy_ids and universe = hierarchy_universe
      and collect_elems = hierarchy_members and max_ids = hierarchy_tops
      and blossom_forest_invar = hierarchy_invar and laminar_abstract = hierarchy_abstract
      and compound = hierarchy_compound and blossom_edges = hierarchy_edges
      and merge = hierarchy_merge and children = hierarchy_children +
  Work: bounded_queue cap queue_invar queue_abstract queue_empty queue_push queue_pop queue_is_empty +
  Components: fixed_univ_union_find K uf_invar uf_representative uf_find uf_union uf_reset +
  Owners: fixed_univ_map K owner_invar owner_update owner_lookup +
  Edges: fixed_univ_map K edge_invar edge_update edge_lookup +
  Routing: Blossom_Routing K base_invar base_update base_lookup link_invar link_update link_lookup +
  Neighbours: indexed_iterable_set
    where K = V0 and idx_invar = cursor_invar and idx_abstract = cursor_abstract
      and idx_current = cursor_current and idx_has = cursor_has
      and idx_iterated = cursor_iterated and idx_remaining = cursor_remaining
      and idx_move = cursor_move and idx_reset = cursor_reset
  for K V0 :: "'v set"
    and nil :: 'v
    and graph_lookup :: "'graph \<Rightarrow> 'v \<Rightarrow> 'adjset option"
    and adj_insert :: "'v \<Rightarrow> 'adjset \<Rightarrow> 'adjset"
    and adj_isin :: "'adjset \<Rightarrow> 'v \<Rightarrow> bool"
    and adj_abstract :: "'adjset \<Rightarrow> 'v set"
    and adj_choose :: "'adjset \<Rightarrow> 'v"
    and adj_empty :: 'adjset
    and adj_delete :: "'v \<Rightarrow> 'adjset \<Rightarrow> 'adjset"
    and adj_invar :: "'adjset \<Rightarrow> bool"
    and graph_invar :: "'graph \<Rightarrow> bool"
    and fset_invar :: "'vset \<Rightarrow> bool"
    and fset_abstract :: "'vset \<Rightarrow> 'v set"
    and fset_empty :: 'vset
    and fset_insert :: "'v \<Rightarrow> 'vset \<Rightarrow> 'vset"
    and fset_delete :: "'v \<Rightarrow> 'vset \<Rightarrow> 'vset"
    and fset_isin :: "'vset \<Rightarrow> 'v \<Rightarrow> bool"
    and forest_evens forest_odds forest_roots :: "'forest \<Rightarrow> 'vset"
    and forest_path :: "'forest \<Rightarrow> 'v \<Rightarrow> 'v list"
    and forest_abstract :: "'forest \<Rightarrow> 'v set set"
    and forest_invar :: "'v set set \<Rightarrow> 'forest \<Rightarrow> bool"
    and forest_empty :: "'vset \<Rightarrow> 'forest"
    and forest_extend :: "'forest \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'forest"
    and forest_contract :: "'forest \<Rightarrow> 'v list \<Rightarrow> 'v list \<Rightarrow> 'v \<Rightarrow> 'forest"
    and mate_empty :: 'mate
    and mate_invar :: "'v set set \<Rightarrow> 'mate \<Rightarrow> bool"
    and mate_partner :: "'mate \<Rightarrow> 'v \<Rightarrow> 'v"
    and mate_augment :: "'mate \<Rightarrow> 'v list \<Rightarrow> 'mate"
    and mate_abstract :: "'mate \<Rightarrow> 'v set set"
    and mate_contract :: "'mate \<Rightarrow> 'v list \<Rightarrow> 'v \<Rightarrow> 'mate"
    and mate_expand :: "'mate \<Rightarrow> 'v list \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'mate"
    and mate_add :: "'mate \<Rightarrow> 'v list \<Rightarrow> 'mate"
    and hierarchy_ids hierarchy_tops :: "'hierarchy \<Rightarrow> 'v set"
    and hierarchy_universe :: "'hierarchy \<Rightarrow> 'v set"
    and hierarchy_members :: "'hierarchy \<Rightarrow> 'v \<Rightarrow> 'v set"
    and hierarchy_invar :: "'hierarchy \<Rightarrow> bool"
    and hierarchy_abstract :: "'hierarchy \<Rightarrow> 'v set set"
    and hierarchy_compound :: "'hierarchy \<Rightarrow> 'v \<Rightarrow> bool"
    and hierarchy_edges :: "'hierarchy \<Rightarrow> 'v set set"
    and hierarchy_merge :: "'hierarchy \<Rightarrow> 'v list \<Rightarrow> 'v \<Rightarrow> 'hierarchy"
    and hierarchy_children :: "'hierarchy \<Rightarrow> 'v \<Rightarrow> 'v list"
    and cap :: nat
    and queue_invar :: "'queue \<Rightarrow> bool"
    and queue_abstract :: "'queue \<Rightarrow> 'v list"
    and queue_empty :: 'queue
    and queue_push :: "'queue \<Rightarrow> 'v \<Rightarrow> 'queue"
    and queue_pop :: "'queue \<Rightarrow> 'v \<times> 'queue"
    and queue_is_empty :: "'queue \<Rightarrow> bool"
    and uf_invar :: "'uf \<Rightarrow> bool"
    and uf_representative :: "'uf \<Rightarrow> 'v \<Rightarrow> 'v"
    and uf_find :: "'uf \<Rightarrow> 'v \<Rightarrow> 'v \<times> 'uf"
    and uf_union :: "'uf \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'uf"
    and uf_reset :: "'uf \<Rightarrow> 'uf"
    and owner_invar :: "'owners \<Rightarrow> bool"
    and owner_update :: "'owners \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'owners"
    and owner_lookup :: "'owners \<Rightarrow> 'v \<Rightarrow> 'v"
    and edge_invar :: "'edges \<Rightarrow> bool"
    and edge_update :: "'edges \<Rightarrow> 'v \<Rightarrow> ('v \<times> 'v) \<Rightarrow> 'edges"
    and edge_lookup :: "'edges \<Rightarrow> 'v \<Rightarrow> ('v \<times> 'v)"
    and cursor_invar :: "'cursor \<Rightarrow> bool"
    and cursor_abstract cursor_iterated cursor_remaining :: "'cursor \<Rightarrow> 'v \<Rightarrow> 'v set"
    and cursor_current :: "'cursor \<Rightarrow> 'v \<Rightarrow> 'v"
    and cursor_has :: "'cursor \<Rightarrow> 'v \<Rightarrow> bool"
    and cursor_move cursor_reset :: "'cursor \<Rightarrow> 'v \<Rightarrow> 'cursor"
    and base_invar :: "'bases \<Rightarrow> bool"
    and base_update :: "'bases \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'bases"
    and base_lookup :: "'bases \<Rightarrow> 'v \<Rightarrow> 'v"
    and link_invar :: "'links \<Rightarrow> bool"
    and link_update :: "'links \<Rightarrow> 'v \<Rightarrow> ('v \<times> nat) \<Rightarrow> 'links"
    and link_lookup :: "'links \<Rightarrow> 'v \<Rightarrow> ('v \<times> nat)" +
  fixes G :: 'graph and vs :: "'v list" and M0 :: 'mate
begin

subsection "Public observations and input conditions"

definition "input_graph = {{u, v} | u v. (u, v) \<in> Graph.digraph_abs G}"

definition "input_axioms C \<longleftrightarrow>
  distinct vs \<and> set vs = V0 \<and> V0 \<subseteq> K \<and> nil \<notin> K \<and> length vs \<le> cap \<and>
  Graph.graph_inv G \<and> Graph.finite_graph G \<and> Graph.finite_vsets G \<and>
  dVs (Graph.digraph_abs G) \<subseteq> V0 \<and>
  (\<forall>u v. (u, v) \<in> Graph.digraph_abs G \<longrightarrow> (v, u) \<in> Graph.digraph_abs G) \<and>
  (\<forall>u. (u, u) \<notin> Graph.digraph_abs G) \<and>
  mate_invar input_graph M0 \<and> cursor_invar C \<and>
  (\<forall>u \<in> V0. cursor_abstract C u = adj_abstract (Graph.neighbourhood G u))"

abbreviation "representative state u \<equiv>
  owner_lookup (qbs_owners state) (uf_representative (qbs_components state) u)"
abbreviation "even_ids state \<equiv> fset_abstract (forest_evens (qbs_forest state))"
abbreviation "odd_ids state \<equiv> fset_abstract (forest_odds (qbs_forest state))"
abbreviation "active_ids state \<equiv> hierarchy_tops (qbs_hierarchy state)"
abbreviation "current_vertices state \<equiv> if qbs_current state = nil then {} else {qbs_current state}"

definition "quotient_graph state =
  {{representative state u, representative state v} | u v.
    {u, v} \<in> input_graph \<and> representative state u \<noteq> representative state v}"

definition "effectively_even state = {u \<in> V0. representative state u \<in> even_ids state}"


subsection "Scheduling original vertices"

definition "enqueue_vertex state u =
  state \<lparr>qbs_queue := queue_push (qbs_queue state) u\<rparr>"

definition "initial_frontier =
  foldl (\<lambda>(S, Q) v. if mate_partner M0 v = nil
    then (fset_insert v S, queue_push Q v) else (S, Q)) (fset_empty, queue_empty) vs"

definition "initial_state U L C H P B D N J fresh =
  (let (S, Q) = initial_frontier in \<lparr>
    qbs_forest = forest_empty S,
    qbs_matching = M0, qbs_hierarchy = H,
    qbs_queue = Q, qbs_current = nil, qbs_component = nil,
    qbs_components = uf_reset U,
    qbs_owners = foldl (\<lambda>L v. owner_update L v v) L vs,
    qbs_neighbours = foldl cursor_reset C vs,
    qbs_forest_edges = P,
    qbs_cycle_edges = B, qbs_bases = Routing.initial_bases D vs,
    qbs_parents = N, qbs_hints = J,
    qbs_fresh = fresh, qbs_status = Quadratic_Searching\<rparr>)"

definition "initial_axioms U L C H P B D N J fresh \<longleftrightarrow>
  input_axioms C \<and> uf_invar U \<and> owner_invar L \<and> edge_invar P \<and> edge_invar B \<and>
  base_invar D \<and> link_invar N \<and> link_invar J \<and>
  hierarchy_invar H \<and> hierarchy_ids H = V0 \<and> hierarchy_tops H = V0 \<and>
  hierarchy_universe H = V0 \<and>
  (\<forall>v \<in> V0. hierarchy_members H v = {v} \<and> hierarchy_children H v = []) \<and>
  queue_invar fresh \<and> distinct (queue_abstract fresh) \<and>
  set (queue_abstract fresh) \<subseteq> K - V0 \<and> length vs div 2 \<le> length (queue_abstract fresh)"

subsection "Original edge witnesses"

abbreviation "forest_edge state v \<equiv> edge_lookup (qbs_forest_edges state) v"

definition "rootward_edges state p = map (forest_edge state) (butlast p)"

definition "outward_edges state p =
  map (\<lambda>v. case forest_edge state v of (x, y) \<Rightarrow> (y, x)) (tl p)"

definition "finish_search state u v p q =
  (let r = rev p in state \<lparr>qbs_status := Quadratic_Path (r @ q)
    (outward_edges state r @ [(u, v)] @ rootward_edges state q)\<rparr>)"

text "The annotation indexed by a non-root forest vertex realises its edge toward the root.
  Unclassified components are singleton original vertices throughout this search. Therefore
  the matching edge introduced by ordinary extension has original endpoints y and z."

definition "extend_search state u v x y =
  (let z = mate_partner (qbs_matching state) y;
       P = edge_update (edge_update (qbs_forest_edges state) y (v, u)) z (z, y)
   in enqueue_vertex (state \<lparr>
     qbs_forest := forest_extend (qbs_forest state) x y z, qbs_forest_edges := P\<rparr>) z)"

subsection "Contraction through the existing ADTs"

definition "process_cycle state cs k edge b =
  (let (_, next) = foldl (\<lambda>(i, next) c.
       let witness = (if Suc i < k then
             case forest_edge state (cs ! Suc i) of (x, y) \<Rightarrow> (y, x)
           else if Suc i = k then edge else forest_edge state c);
           next = (if fset_isin (forest_odds (qbs_forest state)) c
             then enqueue_vertex next c else next)
       in (Suc i, next \<lparr>
         qbs_components := uf_union (qbs_components next) b c,
         qbs_cycle_edges := edge_update (qbs_cycle_edges next) c witness,
         qbs_parents := link_update (qbs_parents next) c (b, i)\<rparr>)) (0, state) cs;
       (r, U) = uf_find (qbs_components next) b
   in next \<lparr>qbs_components := U, qbs_owners := owner_update (qbs_owners next) r b\<rparr>)"

text "The common-suffix procedure returns the two prefixes in base-first order. Their union
  gives the cycle children, while the scanned edge joins the two tips. The original cycle
  edge leaving a child is stored at that child's ID, which is used as a child only once.
  One pass schedules old odd children, unions components, and records parent positions and
  cycle witnesses. Before the bridge the witness points away from the root; after it the
  witness points toward the root. No separate edge sequence is constructed."

definition "contract_search state u v p q =
  (let (c1, c2) = longest_disj_sfx (rev p) (rev q);
       r2 = rev c2; cs = c1 @ butlast r2;
       (b, fresh) = queue_pop (qbs_fresh state);
       P = edge_update (qbs_forest_edges state) b
             (edge_lookup (qbs_forest_edges state) (hd c1))
   in (process_cycle state cs (length c1) (u, v) b) \<lparr>
     qbs_forest := forest_contract (qbs_forest state) (rev c1) r2 b,
     qbs_matching := mate_contract (qbs_matching state) cs b,
     qbs_hierarchy := hierarchy_merge (qbs_hierarchy state) cs b,
     qbs_component := b,
     qbs_forest_edges := P,
     qbs_bases := base_update (qbs_bases state) b (base_lookup (qbs_bases state) (hd cs)),
     qbs_hints := link_update (qbs_hints state) b (nil, 0), qbs_fresh := fresh\<rparr>)"

subsection "A single search step"

definition "start_scan state =
  (let (u, Q) = queue_pop (qbs_queue state);
       (r, U) = uf_find (qbs_components state) u
   in state \<lparr>qbs_queue := Q, qbs_current := u,
     qbs_component := owner_lookup (qbs_owners state) r, qbs_components := U\<rparr>)"

definition "resolve_target state v =
  (let (r, U) = uf_find (qbs_components state) v
   in (owner_lookup (qbs_owners state) r, U))"

lemma resolve_target_correct:
  assumes "uf_invar (qbs_components state)" "v \<in> K"
  shows "fst (resolve_target state v) = representative state v"
    "uf_invar (snd (resolve_target state v))"
    "w \<in> K \<Longrightarrow> uf_representative (snd (resolve_target state v)) w =
      uf_representative (qbs_components state) w"
  using assms
  by(auto simp: resolve_target_def case_prod_beta Let_def
      Components.find_result Components.find_representatives Components.find_invar)

text "Each dequeued original vertex resolves its component once. Scanning uses the cached
  source and one stateful find for the target. A contraction replaces the cached source
  by the fresh blossom ID. Union roots remain independent of these logical IDs."

definition "search_step state =
  (if qbs_current state = nil then
     if queue_is_empty (qbs_queue state) then state \<lparr>qbs_status := Quadratic_Exhausted\<rparr>
     else start_scan state
   else let u = qbs_current state in
     if \<not> cursor_has (qbs_neighbours state) u then state \<lparr>qbs_current := nil\<rparr>
     else let v = cursor_current (qbs_neighbours state) u;
              x = qbs_component state; (y, U) = resolve_target state v;
              next = state \<lparr>qbs_components := U,
                qbs_neighbours := cursor_move (qbs_neighbours state) u\<rparr>
          in if x = y \<or> fset_isin (forest_odds (qbs_forest state)) y then next
             else if \<not> fset_isin (forest_evens (qbs_forest state)) y
                  then extend_search next u v x y
             else let p = forest_path (qbs_forest state) x;
                      q = forest_path (qbs_forest state) y
                  in if last p \<noteq> last q then finish_search next u v p q
                     else contract_search next u v p q)"

subsection "Search branches"

abbreviation "scanned_vertex state \<equiv> qbs_current state"

abbreviation "scanned_neighbour state \<equiv> cursor_current (qbs_neighbours state) (qbs_current state)"

abbreviation "scanned_target state \<equiv> resolve_target state (scanned_neighbour state)"

abbreviation "source_component state \<equiv> qbs_component state"

abbreviation "target_component state \<equiv> fst (scanned_target state)"

definition "scanning_edge state \<longleftrightarrow>
  qbs_status state = Quadratic_Searching \<and>
  qbs_current state \<noteq> nil \<and>
  cursor_has (qbs_neighbours state) (scanned_vertex state)"

definition "Quadratic_Blossom_Search_call_1_conds state \<longleftrightarrow>
  qbs_status state = Quadratic_Searching \<and>
  qbs_current state = nil \<and>
  queue_is_empty (qbs_queue state)"

lemmas Quadratic_Blossom_Search_call_1_conds[call_cond_elims] =
  Quadratic_Blossom_Search_call_1_conds_def[THEN iffD1, elim_format,
    unfolded atomize_conjL[symmetric]]

lemmas Quadratic_Blossom_Search_call_1_condsI[call_cond_intros] =
  Quadratic_Blossom_Search_call_1_conds_def[THEN iffD2,
    unfolded atomize_conjL[symmetric]]

definition "Quadratic_Blossom_Search_call_2_conds state \<longleftrightarrow>
  qbs_status state = Quadratic_Searching \<and>
  qbs_current state = nil \<and>
  \<not> queue_is_empty (qbs_queue state)"

lemmas Quadratic_Blossom_Search_call_2_conds[call_cond_elims] =
  Quadratic_Blossom_Search_call_2_conds_def[THEN iffD1, elim_format,
    unfolded atomize_conjL[symmetric]]

lemmas Quadratic_Blossom_Search_call_2_condsI[call_cond_intros] =
  Quadratic_Blossom_Search_call_2_conds_def[THEN iffD2,
    unfolded atomize_conjL[symmetric]]

definition "Quadratic_Blossom_Search_call_3_conds state \<longleftrightarrow>
  qbs_status state = Quadratic_Searching \<and>
  qbs_current state \<noteq> nil \<and>
  \<not> cursor_has (qbs_neighbours state) (scanned_vertex state)"

lemmas Quadratic_Blossom_Search_call_3_conds[call_cond_elims] =
  Quadratic_Blossom_Search_call_3_conds_def[THEN iffD1, elim_format,
    unfolded atomize_conjL[symmetric]]

lemmas Quadratic_Blossom_Search_call_3_condsI[call_cond_intros] =
  Quadratic_Blossom_Search_call_3_conds_def[THEN iffD2,
    unfolded atomize_conjL[symmetric]]

definition "Quadratic_Blossom_Search_call_4_conds state \<longleftrightarrow>
  scanning_edge state \<and>
  (source_component state = target_component state \<or>
      fset_isin (forest_odds (qbs_forest state)) (target_component state))"

lemmas Quadratic_Blossom_Search_call_4_conds[call_cond_elims] =
  Quadratic_Blossom_Search_call_4_conds_def[THEN iffD1, elim_format,
    unfolded atomize_conjL[symmetric]]

lemmas Quadratic_Blossom_Search_call_4_condsI[call_cond_intros] =
  Quadratic_Blossom_Search_call_4_conds_def[THEN iffD2,
    unfolded atomize_conjL[symmetric]]

definition "Quadratic_Blossom_Search_call_5_conds state \<longleftrightarrow>
  scanning_edge state \<and>
  source_component state \<noteq> target_component state \<and>
  \<not> fset_isin (forest_odds (qbs_forest state)) (target_component state) \<and>
  \<not> fset_isin (forest_evens (qbs_forest state)) (target_component state)"

lemmas Quadratic_Blossom_Search_call_5_conds[call_cond_elims] =
  Quadratic_Blossom_Search_call_5_conds_def[THEN iffD1, elim_format,
    unfolded atomize_conjL[symmetric]]

lemmas Quadratic_Blossom_Search_call_5_condsI[call_cond_intros] =
  Quadratic_Blossom_Search_call_5_conds_def[THEN iffD2,
    unfolded atomize_conjL[symmetric]]

definition "Quadratic_Blossom_Search_call_6_conds state \<longleftrightarrow>
  scanning_edge state \<and>
  source_component state \<noteq> target_component state \<and>
  \<not> fset_isin (forest_odds (qbs_forest state)) (target_component state) \<and>
  fset_isin (forest_evens (qbs_forest state)) (target_component state) \<and>
  \<not> (last (forest_path (qbs_forest state) (source_component state)) =
      last (forest_path (qbs_forest state) (target_component state)))"

lemmas Quadratic_Blossom_Search_call_6_conds[call_cond_elims] =
  Quadratic_Blossom_Search_call_6_conds_def[THEN iffD1, elim_format,
    unfolded atomize_conjL[symmetric]]

lemmas Quadratic_Blossom_Search_call_6_condsI[call_cond_intros] =
  Quadratic_Blossom_Search_call_6_conds_def[THEN iffD2,
    unfolded atomize_conjL[symmetric]]

definition "Quadratic_Blossom_Search_call_7_conds state \<longleftrightarrow>
  scanning_edge state \<and>
  source_component state \<noteq> target_component state \<and>
  \<not> fset_isin (forest_odds (qbs_forest state)) (target_component state) \<and>
  fset_isin (forest_evens (qbs_forest state)) (target_component state) \<and>
  last (forest_path (qbs_forest state) (source_component state)) =
      last (forest_path (qbs_forest state) (target_component state))"

lemmas Quadratic_Blossom_Search_call_7_conds[call_cond_elims] =
  Quadratic_Blossom_Search_call_7_conds_def[THEN iffD1, elim_format,
    unfolded atomize_conjL[symmetric]]

lemmas Quadratic_Blossom_Search_call_7_condsI[call_cond_intros] =
  Quadratic_Blossom_Search_call_7_conds_def[THEN iffD2,
    unfolded atomize_conjL[symmetric]]

definition "Quadratic_Blossom_Search_ret_1_conds state \<longleftrightarrow>
  qbs_status state = Quadratic_Exhausted"

lemmas Quadratic_Blossom_Search_ret_1_conds[call_cond_elims] =
  Quadratic_Blossom_Search_ret_1_conds_def[THEN iffD1, elim_format,
    unfolded atomize_conjL[symmetric]]

lemmas Quadratic_Blossom_Search_ret_1_condsI[call_cond_intros] =
  Quadratic_Blossom_Search_ret_1_conds_def[THEN iffD2,
    unfolded atomize_conjL[symmetric]]

definition "Quadratic_Blossom_Search_ret_2_conds state \<longleftrightarrow>
  (\<exists>p es. qbs_status state = Quadratic_Path p es)"

lemmas Quadratic_Blossom_Search_ret_2_conds[call_cond_elims] =
  Quadratic_Blossom_Search_ret_2_conds_def[THEN iffD1, elim_format,
    unfolded atomize_conjL[symmetric]]

lemmas Quadratic_Blossom_Search_ret_2_condsI[call_cond_intros] =
  Quadratic_Blossom_Search_ret_2_conds_def[THEN iffD2,
    unfolded atomize_conjL[symmetric]]

definition "Quadratic_Blossom_Search_upd1 state =
  state \<lparr>qbs_status := Quadratic_Exhausted\<rparr>"

definition "Quadratic_Blossom_Search_upd2 state = start_scan state"

definition "Quadratic_Blossom_Search_upd3 state =
  state \<lparr>qbs_current := nil\<rparr>"

definition "Quadratic_Blossom_Search_upd4 state =
  state \<lparr>qbs_components := snd (scanned_target state),
    qbs_neighbours := cursor_move (qbs_neighbours state) (scanned_vertex state)\<rparr>"

definition "Quadratic_Blossom_Search_upd5 state =
  extend_search (Quadratic_Blossom_Search_upd4 state)
    (scanned_vertex state) (scanned_neighbour state) (source_component state) (target_component state)"

definition "Quadratic_Blossom_Search_upd6 state =
  finish_search (Quadratic_Blossom_Search_upd4 state)
    (scanned_vertex state) (scanned_neighbour state)
    (forest_path (qbs_forest state) (source_component state))
    (forest_path (qbs_forest state) (target_component state))"

definition "Quadratic_Blossom_Search_upd7 state =
  contract_search (Quadratic_Blossom_Search_upd4 state)
    (scanned_vertex state) (scanned_neighbour state)
    (forest_path (qbs_forest state) (source_component state))
    (forest_path (qbs_forest state) (target_component state))"

definition "Quadratic_Blossom_Search_ret1 state = state"

definition "Quadratic_Blossom_Search_ret2 state = state"

lemmas Quadratic_Blossom_Search_branch_defs =
  Quadratic_Blossom_Search_call_1_conds_def
  Quadratic_Blossom_Search_call_2_conds_def
  Quadratic_Blossom_Search_call_3_conds_def
  Quadratic_Blossom_Search_call_4_conds_def
  Quadratic_Blossom_Search_call_5_conds_def
  Quadratic_Blossom_Search_call_6_conds_def
  Quadratic_Blossom_Search_call_7_conds_def
  Quadratic_Blossom_Search_ret_1_conds_def
  Quadratic_Blossom_Search_ret_2_conds_def
  Quadratic_Blossom_Search_upd1_def
  Quadratic_Blossom_Search_upd2_def
  Quadratic_Blossom_Search_upd3_def
  Quadratic_Blossom_Search_upd4_def
  Quadratic_Blossom_Search_upd5_def
  Quadratic_Blossom_Search_upd6_def
  Quadratic_Blossom_Search_upd7_def
  Quadratic_Blossom_Search_ret1_def
  Quadratic_Blossom_Search_ret2_def
  scanning_edge_def

function (domintros) Quadratic_Blossom_Search ::
  "('v, 'forest, 'mate, 'hierarchy, 'queue, 'uf, 'owners, 'cursor, 'edges, 'bases, 'links)
    Quadratic_Blossom_Search_state \<Rightarrow>
   ('v, 'forest, 'mate, 'hierarchy, 'queue, 'uf, 'owners, 'cursor, 'edges, 'bases, 'links)
    Quadratic_Blossom_Search_state" where
  "Quadratic_Blossom_Search state =
    (if qbs_status state = Quadratic_Searching
     then Quadratic_Blossom_Search (search_step state)
     else state)"
  by pat_completeness auto

partial_function (tailrec) Quadratic_Blossom_Search_impl ::
  "('v, 'forest, 'mate, 'hierarchy, 'queue, 'uf, 'owners, 'cursor, 'edges, 'bases, 'links)
    Quadratic_Blossom_Search_state \<Rightarrow>
   ('v, 'forest, 'mate, 'hierarchy, 'queue, 'uf, 'owners, 'cursor, 'edges, 'bases, 'links)
    Quadratic_Blossom_Search_state" where
  "Quadratic_Blossom_Search_impl state =
    (if qbs_status state = Quadratic_Searching
     then Quadratic_Blossom_Search_impl (search_step state)
     else state)"

lemma Quadratic_Blossom_Search_impl_same:
  "Quadratic_Blossom_Search_dom state \<Longrightarrow>
    Quadratic_Blossom_Search_impl state = Quadratic_Blossom_Search state"
  by(induction rule: Quadratic_Blossom_Search.pinduct)
    (subst Quadratic_Blossom_Search_impl.simps, subst Quadratic_Blossom_Search.psimps, auto)

lemma Quadratic_Blossom_Search_cases:
  "\<lbrakk>Quadratic_Blossom_Search_call_1_conds state \<Longrightarrow> P;
    Quadratic_Blossom_Search_call_2_conds state \<Longrightarrow> P;
    Quadratic_Blossom_Search_call_3_conds state \<Longrightarrow> P;
    Quadratic_Blossom_Search_call_4_conds state \<Longrightarrow> P;
    Quadratic_Blossom_Search_call_5_conds state \<Longrightarrow> P;
    Quadratic_Blossom_Search_call_6_conds state \<Longrightarrow> P;
    Quadratic_Blossom_Search_call_7_conds state \<Longrightarrow> P;
    Quadratic_Blossom_Search_ret_1_conds state \<Longrightarrow> P;
    Quadratic_Blossom_Search_ret_2_conds state \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(cases "qbs_status state";
      fastforce simp: Quadratic_Blossom_Search_branch_defs)

lemma Quadratic_Blossom_Search_step_simps:
  "Quadratic_Blossom_Search_call_1_conds state \<Longrightarrow>
    search_step state = Quadratic_Blossom_Search_upd1 state"
  "Quadratic_Blossom_Search_call_2_conds state \<Longrightarrow>
    search_step state = Quadratic_Blossom_Search_upd2 state"
  "Quadratic_Blossom_Search_call_3_conds state \<Longrightarrow>
    search_step state = Quadratic_Blossom_Search_upd3 state"
  "Quadratic_Blossom_Search_call_4_conds state \<Longrightarrow>
    search_step state = Quadratic_Blossom_Search_upd4 state"
  "Quadratic_Blossom_Search_call_5_conds state \<Longrightarrow>
    search_step state = Quadratic_Blossom_Search_upd5 state"
  "Quadratic_Blossom_Search_call_6_conds state \<Longrightarrow>
    search_step state = Quadratic_Blossom_Search_upd6 state"
  "Quadratic_Blossom_Search_call_7_conds state \<Longrightarrow>
    search_step state = Quadratic_Blossom_Search_upd7 state"
  by(fastforce simp: Quadratic_Blossom_Search_branch_defs search_step_def Let_def split: prod.splits)+

lemma Quadratic_Blossom_Search_simps:
  assumes "Quadratic_Blossom_Search_dom state"
  shows
    "Quadratic_Blossom_Search_call_1_conds state \<Longrightarrow>
      Quadratic_Blossom_Search state = Quadratic_Blossom_Search (Quadratic_Blossom_Search_upd1 state)"
    "Quadratic_Blossom_Search_call_2_conds state \<Longrightarrow>
      Quadratic_Blossom_Search state = Quadratic_Blossom_Search (Quadratic_Blossom_Search_upd2 state)"
    "Quadratic_Blossom_Search_call_3_conds state \<Longrightarrow>
      Quadratic_Blossom_Search state = Quadratic_Blossom_Search (Quadratic_Blossom_Search_upd3 state)"
    "Quadratic_Blossom_Search_call_4_conds state \<Longrightarrow>
      Quadratic_Blossom_Search state = Quadratic_Blossom_Search (Quadratic_Blossom_Search_upd4 state)"
    "Quadratic_Blossom_Search_call_5_conds state \<Longrightarrow>
      Quadratic_Blossom_Search state = Quadratic_Blossom_Search (Quadratic_Blossom_Search_upd5 state)"
    "Quadratic_Blossom_Search_call_6_conds state \<Longrightarrow>
      Quadratic_Blossom_Search state = Quadratic_Blossom_Search (Quadratic_Blossom_Search_upd6 state)"
    "Quadratic_Blossom_Search_call_7_conds state \<Longrightarrow>
      Quadratic_Blossom_Search state = Quadratic_Blossom_Search (Quadratic_Blossom_Search_upd7 state)"
    "Quadratic_Blossom_Search_ret_1_conds state \<Longrightarrow>
      Quadratic_Blossom_Search state = Quadratic_Blossom_Search_ret1 state"
    "Quadratic_Blossom_Search_ret_2_conds state \<Longrightarrow>
      Quadratic_Blossom_Search state = Quadratic_Blossom_Search_ret2 state"
  by(auto simp: Quadratic_Blossom_Search.psimps[OF assms]
      Quadratic_Blossom_Search_step_simps[symmetric] scanning_edge_def
      Quadratic_Blossom_Search_ret1_def Quadratic_Blossom_Search_ret2_def
      elim!: call_cond_elims)

lemma Quadratic_Blossom_Search_induct:
  assumes "Quadratic_Blossom_Search_dom state"
    "\<And>s. \<lbrakk>Quadratic_Blossom_Search_dom s;
    Quadratic_Blossom_Search_call_1_conds s \<Longrightarrow> P (Quadratic_Blossom_Search_upd1 s);
    Quadratic_Blossom_Search_call_2_conds s \<Longrightarrow> P (Quadratic_Blossom_Search_upd2 s);
    Quadratic_Blossom_Search_call_3_conds s \<Longrightarrow> P (Quadratic_Blossom_Search_upd3 s);
    Quadratic_Blossom_Search_call_4_conds s \<Longrightarrow> P (Quadratic_Blossom_Search_upd4 s);
    Quadratic_Blossom_Search_call_5_conds s \<Longrightarrow> P (Quadratic_Blossom_Search_upd5 s);
    Quadratic_Blossom_Search_call_6_conds s \<Longrightarrow> P (Quadratic_Blossom_Search_upd6 s);
    Quadratic_Blossom_Search_call_7_conds s \<Longrightarrow> P (Quadratic_Blossom_Search_upd7 s)\<rbrakk> \<Longrightarrow> P s"
  shows "P state"
  using assms(1)
proof(induction rule: Quadratic_Blossom_Search.pinduct)
  case IH: (1 state)
  show ?case
    by(rule assms(2))
      (insert IH, auto simp: Quadratic_Blossom_Search_step_simps[symmetric] scanning_edge_def
        elim!: call_cond_elims)
qed

lemma Quadratic_Blossom_Search_domintros:
  "\<lbrakk>Quadratic_Blossom_Search_call_1_conds state \<Longrightarrow>
      Quadratic_Blossom_Search_dom (Quadratic_Blossom_Search_upd1 state);
    Quadratic_Blossom_Search_call_2_conds state \<Longrightarrow>
      Quadratic_Blossom_Search_dom (Quadratic_Blossom_Search_upd2 state);
    Quadratic_Blossom_Search_call_3_conds state \<Longrightarrow>
      Quadratic_Blossom_Search_dom (Quadratic_Blossom_Search_upd3 state);
    Quadratic_Blossom_Search_call_4_conds state \<Longrightarrow>
      Quadratic_Blossom_Search_dom (Quadratic_Blossom_Search_upd4 state);
    Quadratic_Blossom_Search_call_5_conds state \<Longrightarrow>
      Quadratic_Blossom_Search_dom (Quadratic_Blossom_Search_upd5 state);
    Quadratic_Blossom_Search_call_6_conds state \<Longrightarrow>
      Quadratic_Blossom_Search_dom (Quadratic_Blossom_Search_upd6 state);
    Quadratic_Blossom_Search_call_7_conds state \<Longrightarrow>
      Quadratic_Blossom_Search_dom (Quadratic_Blossom_Search_upd7 state)\<rbrakk> \<Longrightarrow> Quadratic_Blossom_Search_dom state"
  by(rule Quadratic_Blossom_Search.domintros,
      rule Quadratic_Blossom_Search_cases[where state = state])
    (auto simp: Quadratic_Blossom_Search_step_simps scanning_edge_def elim!: call_cond_elims)

lemma Quadratic_Blossom_Search_ret[ret_holds_intros]:
  assumes "Quadratic_Blossom_Search_dom state"
  shows "Quadratic_Blossom_Search_ret_1_conds (Quadratic_Blossom_Search state) \<or>
    Quadratic_Blossom_Search_ret_2_conds (Quadratic_Blossom_Search state)"
proof(induction rule: Quadratic_Blossom_Search_induct[OF assms])
  case IH: (1 state)
  show ?case
    by(rule Quadratic_Blossom_Search_cases[where state = state])
      (insert IH, auto simp: Quadratic_Blossom_Search_simps Quadratic_Blossom_Search_ret1_def Quadratic_Blossom_Search_ret2_def)
qed

subsection "Search invariants"

definition "invar_adts state \<longleftrightarrow>
  queue_invar (qbs_queue state) \<and> queue_invar (qbs_fresh state) \<and>
  uf_invar (qbs_components state) \<and> owner_invar (qbs_owners state) \<and>
  cursor_invar (qbs_neighbours state) \<and>
  edge_invar (qbs_forest_edges state) \<and> link_invar (qbs_hints state)"

definition "invar_forest state \<longleftrightarrow>
  mate_invar (quotient_graph state) (qbs_matching state) \<and>
  forest_invar (mate_abstract (qbs_matching state)) (qbs_forest state) \<and>
  forest_abstract (qbs_forest state) \<subseteq> quotient_graph state \<and>
  even_ids state \<union> odd_ids state \<subseteq> active_ids state \<and>
  fset_abstract (forest_roots (qbs_forest state)) =
    active_ids state - Vs (mate_abstract (qbs_matching state))"

definition "invar_matching_projection state \<longleftrightarrow>
  mate_abstract (qbs_matching state) =
    {{representative state u, representative state v} | u v.
      {u, v} \<in> mate_abstract M0 \<and> representative state u \<noteq> representative state v}"

definition "invar_representatives state \<longleftrightarrow>
  hierarchy_ids (qbs_hierarchy state) \<subseteq> K \<and>
  hierarchy_universe (qbs_hierarchy state) = V0 \<and>
  (\<forall>u \<in> V0. representative state u \<in> active_ids state) \<and>
  (\<forall>b \<in> active_ids state.
    hierarchy_members (qbs_hierarchy state) b = {u \<in> V0. representative state u = b}) \<and>
  (\<forall>b \<in> active_ids state - even_ids state.
    hierarchy_members (qbs_hierarchy state) b = {b})"

definition "invar_components state \<longleftrightarrow>
  (\<forall>c \<in> hierarchy_ids (qbs_hierarchy state).
    uf_representative (qbs_components state) c \<in> hierarchy_ids (qbs_hierarchy state)) \<and>
  (\<forall>c \<in> K - hierarchy_ids (qbs_hierarchy state). uf_representative (qbs_components state) c = c) \<and>
  (\<forall>c \<in> hierarchy_ids (qbs_hierarchy state). \<forall>u \<in> hierarchy_members (qbs_hierarchy state) c.
    uf_representative (qbs_components state) u = uf_representative (qbs_components state) c)"

lemmas invar_components_props[invar_props_elims] =
  invar_components_def[THEN iffD1, elim_format, unfolded atomize_conjL[symmetric]]

lemmas invar_components_intro[invar_props_intros] =
  invar_components_def[THEN iffD2, unfolded atomize_conjL[symmetric]]

definition "invar_neighbours state \<longleftrightarrow>
  (\<forall>u \<in> V0. cursor_abstract (qbs_neighbours state) u =
    adj_abstract (Graph.neighbourhood G u))"

definition "invar_current state \<longleftrightarrow>
  (qbs_current state \<noteq> nil \<longrightarrow> qbs_component state = representative state (qbs_current state))"

lemmas invar_current_props[invar_props_elims] =
  invar_current_def[THEN iffD1, elim_format]

lemmas invar_current_intro[invar_props_intros] = invar_current_def[THEN iffD2]

definition "invar_queue state \<longleftrightarrow>
  distinct (queue_abstract (qbs_queue state)) \<and>
  set (queue_abstract (qbs_queue state)) \<subseteq> effectively_even state \<and>
  current_vertices state \<subseteq> effectively_even state - set (queue_abstract (qbs_queue state)) \<and>
  (\<forall>u \<in> set (queue_abstract (qbs_queue state)) \<union> (V0 - effectively_even state).
    cursor_iterated (qbs_neighbours state) u = {}) \<and>
  (\<forall>u \<in> effectively_even state -
    (set (queue_abstract (qbs_queue state)) \<union> current_vertices state).
    cursor_remaining (qbs_neighbours state) u = {})"

definition "pending_arcs state =
  {(u, v). u \<in> effectively_even state \<and> v \<in> cursor_remaining (qbs_neighbours state) u}"

definition "invar_scanned state \<longleftrightarrow>
  (case qbs_status state of Quadratic_Path p es \<Rightarrow> True | _ \<Rightarrow>
   (\<forall>u \<in> V0. \<forall>v \<in> V0.
    {u, v} \<in> input_graph \<and> representative state u \<noteq> representative state v \<and>
    representative state u \<in> even_ids state \<and> representative state v \<notin> odd_ids state
    \<longrightarrow> (u, v) \<in> pending_arcs state \<or>
      (representative state v \<in> even_ids state \<and> (v, u) \<in> pending_arcs state)))"

definition "invar_fresh state \<longleftrightarrow>
  distinct (queue_abstract (qbs_fresh state)) \<and>
  set (queue_abstract (qbs_fresh state)) \<subseteq> K - hierarchy_ids (qbs_hierarchy state) \<and>
  card (active_ids state) div 2 \<le> length (queue_abstract (qbs_fresh state))"

definition "search_phase_measure state =
  (if qbs_status state = Quadratic_Searching then (1::nat) else 0)"

definition "search_edges_measure state =
  (\<Sum>u\<in>V0. card (cursor_remaining (qbs_neighbours state) u))"

definition "search_queue_measure state =
  length vs - card (effectively_even state) + length (queue_abstract (qbs_queue state))"

definition "search_scan_measure state =
  (if qbs_current state = nil then 0 else (1::nat))"

definition "Quadratic_Blossom_Search_term_rel' =
  search_phase_measure <*mlex*>
  search_edges_measure <*mlex*>
  search_queue_measure <*mlex*>
  search_scan_measure <*mlex*> {}"

definition "invar_recovering_path state p es \<longleftrightarrow>
  graph_augmenting_path (quotient_graph state) (mate_abstract (qbs_matching state)) p \<and>
  Suc (length es) = length p \<and>
  (\<forall>i < length es. let (u, v) = es ! i in
    {u, v} \<in> input_graph \<and> representative state u = p ! i \<and>
    representative state v = p ! Suc i \<and>
    ({u, v} \<in> mate_abstract M0 \<longleftrightarrow> {p ! i, p ! Suc i} \<in> mate_abstract (qbs_matching state)))"

abbreviation "edge_witness state e xy \<equiv>
  {fst e, snd e} \<in> input_graph \<and>
  representative state (fst e) = fst xy \<and> representative state (snd e) = snd xy \<and>
  ({fst e, snd e} \<in> mate_abstract M0 \<longleftrightarrow> {fst xy, snd xy} \<in> mate_abstract (qbs_matching state))"

definition "invar_annotations state \<longleftrightarrow>
  (\<forall>a \<in> even_ids state. \<forall>x z.
    {a,x} \<in> mate_abstract (qbs_matching state) \<and>
    {x,z} \<in> forest_abstract (qbs_forest state) \<and> z \<in> even_ids state \<and> z \<noteq> a \<longrightarrow>
    edge_witness state (forest_edge state a) (a,x) \<and>
    edge_witness state (forest_edge state x) (x,z))"

definition "invar_hierarchy_size state \<longleftrightarrow>
  V0 \<subseteq> hierarchy_ids (qbs_hierarchy state) \<and>
  2 * card (hierarchy_ids (qbs_hierarchy state) - V0) +
    card (active_ids state) \<le> length vs"

definition "invar_existence state \<longleftrightarrow>
  ((\<exists>p. graph_augmenting_path input_graph (mate_abstract M0) p) \<longleftrightarrow>
    (\<exists>p. graph_augmenting_path (quotient_graph state) (mate_abstract (qbs_matching state)) p))"

definition "invar_result state \<longleftrightarrow>
  (case qbs_status state of Quadratic_Path p es \<Rightarrow> invar_recovering_path state p es
    | _ \<Rightarrow> True)"

definition "state_rel_exploration before after \<longleftrightarrow>
  effectively_even before \<subseteq> effectively_even after \<and>
  (\<forall>u \<in> V0. cursor_remaining (qbs_neighbours after) u \<subseteq>
    cursor_remaining (qbs_neighbours before) u) \<and>
  hierarchy_ids (qbs_hierarchy before) \<subseteq> hierarchy_ids (qbs_hierarchy after)"

lemmas state_rel_exploration_props =
  state_rel_exploration_def[THEN iffD1, elim_format, unfolded atomize_conjL[symmetric]]

lemmas state_rel_exploration_intro[state_rel_intros] =
  state_rel_exploration_def[THEN iffD2, unfolded atomize_conjL[symmetric]]

definition "search_result_spec state \<longleftrightarrow>
  (case qbs_status state of
     Quadratic_Searching \<Rightarrow> False
   | Quadratic_Exhausted \<Rightarrow> \<not> (\<exists>p. graph_augmenting_path input_graph (mate_abstract M0) p)
   | Quadratic_Path p es \<Rightarrow> invar_recovering_path state p es)"

subsection "Invariant interfaces"

lemmas invar_adts_props[invar_props_elims] =
  invar_adts_def[THEN iffD1, elim_format, unfolded atomize_conjL[symmetric]]

lemmas invar_adts_intro[invar_props_intros] =
  invar_adts_def[THEN iffD2, unfolded atomize_conjL[symmetric]]

lemmas invar_forest_props[invar_props_elims] =
  invar_forest_def[THEN iffD1, elim_format, unfolded atomize_conjL[symmetric]]

lemmas invar_forest_intro[invar_props_intros] =
  invar_forest_def[THEN iffD2, unfolded atomize_conjL[symmetric]]

lemmas invar_matching_projection_props[invar_props_elims] =
  invar_matching_projection_def[THEN iffD1, elim_format, unfolded atomize_conjL[symmetric]]

lemmas invar_matching_projection_intro[invar_props_intros] =
  invar_matching_projection_def[THEN iffD2, unfolded atomize_conjL[symmetric]]

lemmas invar_representatives_props[invar_props_elims] =
  invar_representatives_def[THEN iffD1, elim_format, unfolded atomize_conjL[symmetric]]

lemmas invar_representatives_intro[invar_props_intros] =
  invar_representatives_def[THEN iffD2, unfolded atomize_conjL[symmetric]]

lemmas invar_neighbours_props[invar_props_elims] =
  invar_neighbours_def[THEN iffD1, elim_format, unfolded atomize_conjL[symmetric]]

lemmas invar_neighbours_intro[invar_props_intros] =
  invar_neighbours_def[THEN iffD2, unfolded atomize_conjL[symmetric]]

lemmas invar_queue_props[invar_props_elims] =
  invar_queue_def[THEN iffD1, elim_format, unfolded atomize_conjL[symmetric]]

lemmas invar_queue_intro[invar_props_intros] =
  invar_queue_def[THEN iffD2, unfolded atomize_conjL[symmetric]]

lemmas invar_scanned_props[invar_props_elims] =
  invar_scanned_def[THEN iffD1, elim_format, unfolded atomize_conjL[symmetric]]

lemmas invar_scanned_intro[invar_props_intros] =
  invar_scanned_def[THEN iffD2, unfolded atomize_conjL[symmetric]]

lemmas invar_fresh_props[invar_props_elims] =
  invar_fresh_def[THEN iffD1, elim_format, unfolded atomize_conjL[symmetric]]

lemmas invar_fresh_intro[invar_props_intros] =
  invar_fresh_def[THEN iffD2, unfolded atomize_conjL[symmetric]]

lemmas invar_annotations_props[invar_props_elims] =
  invar_annotations_def[THEN iffD1, elim_format, unfolded atomize_conjL[symmetric]]

lemmas invar_annotations_intro[invar_props_intros] =
  invar_annotations_def[THEN iffD2, unfolded atomize_conjL[symmetric]]

lemmas invar_hierarchy_size_props[invar_props_elims] =
  invar_hierarchy_size_def[THEN iffD1, elim_format, unfolded atomize_conjL[symmetric]]

lemmas invar_hierarchy_size_intro[invar_props_intros] =
  invar_hierarchy_size_def[THEN iffD2, unfolded atomize_conjL[symmetric]]

lemmas invar_existence_props[invar_props_elims] =
  invar_existence_def[THEN iffD1, elim_format, unfolded atomize_conjL[symmetric]]

lemmas invar_existence_intro[invar_props_intros] =
  invar_existence_def[THEN iffD2, unfolded atomize_conjL[symmetric]]

lemmas invar_result_props[invar_props_elims] =
  invar_result_def[THEN iffD1, elim_format, unfolded atomize_conjL[symmetric]]

lemmas invar_result_intro[invar_props_intros] =
  invar_result_def[THEN iffD2, unfolded atomize_conjL[symmetric]]

text "The measure and invariant observations are proof-only. Termination from the initial
  state, preservation of the invariants, annotation correctness, and the ordered blossom
  reconstruction invariant remain to be proved. No correctness theorem is assumed for the
  search loop. The executable twin is related to the recursive definition only on its domain.
  The leading measure component accounts for the final step that records a terminal status."

end

section "Path recovery through the ordered blossom hierarchy"

datatype 'v Quadratic_Blossom_Search_Recovery_task =
    Quadratic_Visit 'v 'v 'v
  | Quadratic_Cycle 'v nat nat bool 'v 'v

record ('v, 'links) Cache_Route_state =
  cache_current :: 'v
  cache_hints :: 'links

record ('v, 'tasks, 'links, 'output) Blossom_Path_Recovery_state =
  qbr_path :: "'v list"
  qbr_crossings :: "('v \<times> 'v) list"
  qbr_entry :: 'v
  qbr_tasks :: 'tasks
  qbr_hints :: 'links
  qbr_output :: 'output
  qbr_length :: nat

text "A visit carries a component and its original attachment vertices. Cycle frames retain
  their positions while a child is expanded. Parent walks cache the route at every ancestor,
  so a nested visit reuses the decisions already made for its attachment. Bases and parent
  positions are recorded during merging; recovery needs no preliminary hierarchy traversal.
  The task stack and the maps are supplied workspaces."

locale Blossom_Path_Recovery =
  Tasks: bounded_stack task_cap task_invar task_abstract task_empty task_push task_pop
    task_top task_is_empty +
  Routing: Blossom_Routing K base_invar base_update base_lookup link_invar link_update link_lookup +
  Output: fixed_univ_map "{..<output_cap}" output_invar output_update output_lookup
  for task_cap output_cap :: nat
    and K :: "'v set"
    and nil :: 'v
    and task_invar :: "'tasks \<Rightarrow> bool"
    and task_abstract :: "'tasks \<Rightarrow> 'v Quadratic_Blossom_Search_Recovery_task list"
    and task_empty :: 'tasks
    and task_push :: "'tasks \<Rightarrow> 'v Quadratic_Blossom_Search_Recovery_task \<Rightarrow> 'tasks"
    and task_pop :: "'tasks \<Rightarrow> 'tasks"
    and task_top :: "'tasks \<Rightarrow> 'v Quadratic_Blossom_Search_Recovery_task"
    and task_is_empty :: "'tasks \<Rightarrow> bool"
    and base_invar :: "'bases \<Rightarrow> bool"
    and base_update :: "'bases \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'bases"
    and base_lookup :: "'bases \<Rightarrow> 'v \<Rightarrow> 'v"
    and link_invar :: "'links \<Rightarrow> bool"
    and link_update :: "'links \<Rightarrow> 'v \<Rightarrow> ('v \<times> nat) \<Rightarrow> 'links"
    and link_lookup :: "'links \<Rightarrow> 'v \<Rightarrow> ('v \<times> nat)"
    and output_invar :: "'output \<Rightarrow> bool"
    and output_update :: "'output \<Rightarrow> nat \<Rightarrow> 'v \<Rightarrow> 'output"
    and output_lookup :: "'output \<Rightarrow> nat \<Rightarrow> 'v" +
  fixes hierarchy_children :: "'hierarchy \<Rightarrow> 'v \<Rightarrow> 'v list"
    and edge_lookup :: "'edges \<Rightarrow> 'v \<Rightarrow> ('v \<times> 'v)"
begin

context fixes H :: 'hierarchy and B :: 'edges and D :: 'bases and N :: 'links begin

subsection "Caching the route to an attachment"

context fixes target root :: 'v begin

definition "Cache_Route_call_1_conds state \<longleftrightarrow> cache_current state \<noteq> root"

definition "Cache_Route_ret_1_conds state \<longleftrightarrow> \<not> Cache_Route_call_1_conds state"

definition "Cache_Route_upd1 state = (let (parent, i) = link_lookup N (cache_current state)
   in state \<lparr>cache_current := parent,
     cache_hints := link_update (cache_hints state) parent (target, i)\<rparr>)"

definition "Cache_Route_ret1 state = state"

function (domintros) Cache_Route :: "('v, 'links) Cache_Route_state \<Rightarrow> ('v, 'links) Cache_Route_state" where
  "Cache_Route state =
    (if Cache_Route_call_1_conds state then Cache_Route (Cache_Route_upd1 state)
     else Cache_Route_ret1 state)"
  by pat_completeness auto

partial_function (tailrec) Cache_Route_impl :: "('v, 'links) Cache_Route_state \<Rightarrow> ('v, 'links) Cache_Route_state" where
  "Cache_Route_impl state =
    (if Cache_Route_call_1_conds state then Cache_Route_impl (Cache_Route_upd1 state)
     else Cache_Route_ret1 state)"

lemmas [code] = Cache_Route_impl.simps[unfolded
  Cache_Route_call_1_conds_def Cache_Route_upd1_def Cache_Route_ret1_def]

lemma Cache_Route_impl_same:
  "Cache_Route_dom state \<Longrightarrow> Cache_Route_impl state = Cache_Route state"
  by(induction rule: Cache_Route.pinduct)
    (subst Cache_Route_impl.simps, subst Cache_Route.psimps, auto)

lemmas Cache_Route_call_1_conds[call_cond_elims] =
  Cache_Route_call_1_conds_def[THEN iffD1, elim_format,
    unfolded atomize_conjL[symmetric]]

lemmas Cache_Route_call_1_condsI[call_cond_intros] =
  Cache_Route_call_1_conds_def[THEN iffD2,
    unfolded atomize_conjL[symmetric]]

lemmas Cache_Route_ret_1_conds[call_cond_elims] =
  Cache_Route_ret_1_conds_def[unfolded Cache_Route_call_1_conds_def not_not,
    THEN iffD1, elim_format,
    unfolded atomize_conjL[symmetric]]

lemmas Cache_Route_ret_1_condsI[call_cond_intros] =
  Cache_Route_ret_1_conds_def[unfolded Cache_Route_call_1_conds_def not_not,
    THEN iffD2,
    unfolded atomize_conjL[symmetric]]

lemma Cache_Route_cases:
  "\<lbrakk>Cache_Route_call_1_conds state \<Longrightarrow> P; Cache_Route_ret_1_conds state \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(auto simp: Cache_Route_ret_1_conds_def)

lemma Cache_Route_simps:
  "\<lbrakk>Cache_Route_dom state; Cache_Route_call_1_conds state\<rbrakk> \<Longrightarrow>
    Cache_Route state = Cache_Route (Cache_Route_upd1 state)"
  "\<lbrakk>Cache_Route_dom state; Cache_Route_ret_1_conds state\<rbrakk> \<Longrightarrow>
    Cache_Route state = Cache_Route_ret1 state"
  by(auto simp: Cache_Route.psimps Cache_Route_ret_1_conds_def)

lemma Cache_Route_induct:
  "\<lbrakk>Cache_Route_dom state;
    \<And>s. \<lbrakk>Cache_Route_dom s; Cache_Route_call_1_conds s \<Longrightarrow> P (Cache_Route_upd1 s)\<rbrakk> \<Longrightarrow> P s\<rbrakk> \<Longrightarrow> P state"
  by(induction rule: Cache_Route.pinduct) auto

lemma Cache_Route_domintros:
  "(Cache_Route_call_1_conds state \<Longrightarrow> Cache_Route_dom (Cache_Route_upd1 state)) \<Longrightarrow> Cache_Route_dom state"
  by(rule Cache_Route.domintros) auto

lemma Cache_Route_ret[ret_holds_intros]:
  assumes "Cache_Route_dom state"
  shows "Cache_Route_ret_1_conds (Cache_Route state)"
proof(induction rule: Cache_Route_induct[OF assms])
  case IH: (1 state)
  show ?case
    by(rule Cache_Route_cases[where state = state])
      (insert IH, auto simp: Cache_Route_simps Cache_Route_ret1_def)
qed

definition "cache_route J =
  (if fst (link_lookup J root) = target then J
   else cache_hints (Cache_Route_impl \<lparr>cache_current = target, cache_hints = J\<rparr>))"

end

subsection "Visits and suspended cycle traversals"

definition "emit_vertex v state = state \<lparr>
  qbr_output := output_update (qbr_output state) (qbr_length state) v,
  qbr_length := Suc (qbr_length state)\<rparr>"

definition "visit_step b a z state =
  (if a = z then emit_vertex a state
   else let from_base = (a = base_lookup D b);
            target = (if from_base then z else a);
            J = cache_route target b (qbr_hints state);
            i = snd (link_lookup J b);
            first = (if from_base then 0 else i);
            last = (if from_base then i else 0)
        in state \<lparr>qbr_hints := J,
          qbr_tasks := task_push (qbr_tasks state)
            (Quadratic_Cycle b first last (even i = from_base) a z)\<rparr>)"

definition "cycle_step b i j forward a z state =
  (let cs = hierarchy_children H b; c = cs ! i in
   if i = j then state \<lparr>qbr_tasks := task_push (qbr_tasks state) (Quadratic_Visit c a z)\<rparr>
   else let k = (if forward then if Suc i = length cs then 0 else Suc i
                 else if i = 0 then length cs - 1 else i - 1);
            d = cs ! k;
            (u, v) = (if forward then edge_lookup B c
                      else case edge_lookup B d of (x, y) \<Rightarrow> (y, x))
        in state \<lparr>qbr_tasks := task_push
          (task_push (qbr_tasks state) (Quadratic_Cycle b k j forward v z))
          (Quadratic_Visit c a u)\<rparr>)"

text "An even child position uses the forward route from the base child. An odd position
  uses the backward route. Reversing a visit reverses that direction. A cycle frame suspends
  traversal while its current child is expanded. Equal attachments emit one original vertex,
  including the zero-length route through a nested base child."

definition "next_component state =
  (let b = hd (qbr_path state);
       a = (if qbr_entry state = nil then base_lookup D b else qbr_entry state);
       z = (case qbr_crossings state of [] \<Rightarrow> base_lookup D b | e # es \<Rightarrow> fst e);
       next = (case qbr_crossings state of [] \<Rightarrow> nil | e # es \<Rightarrow> snd e)
   in state \<lparr>qbr_path := tl (qbr_path state), qbr_crossings := tl (qbr_crossings state),
     qbr_entry := next, qbr_tasks := task_push (qbr_tasks state) (Quadratic_Visit b a z)\<rparr>)"

definition "recovery_step state =
  (if task_is_empty (qbr_tasks state) then next_component state
   else let task = task_top (qbr_tasks state);
            next = state \<lparr>qbr_tasks := task_pop (qbr_tasks state)\<rparr>
        in case task of
             Quadratic_Visit b a z \<Rightarrow> visit_step b a z next
           | Quadratic_Cycle b i j forward a z \<Rightarrow> cycle_step b i j forward a z next)"

definition "recovery_done state \<longleftrightarrow> qbr_path state = [] \<and> task_is_empty (qbr_tasks state)"

definition "Blossom_Path_Recovery_call_1_conds state \<longleftrightarrow> \<not> recovery_done state"

definition "Blossom_Path_Recovery_ret_1_conds state \<longleftrightarrow> \<not> Blossom_Path_Recovery_call_1_conds state"

definition "Blossom_Path_Recovery_upd1 state = recovery_step state"

definition "Blossom_Path_Recovery_ret1 state = state"

function (domintros) Blossom_Path_Recovery ::
  "('v, 'tasks, 'links, 'output) Blossom_Path_Recovery_state \<Rightarrow>
    ('v, 'tasks, 'links, 'output) Blossom_Path_Recovery_state" where
  "Blossom_Path_Recovery state =
    (if Blossom_Path_Recovery_call_1_conds state then Blossom_Path_Recovery (Blossom_Path_Recovery_upd1 state)
     else Blossom_Path_Recovery_ret1 state)"
  by pat_completeness auto

partial_function (tailrec) Blossom_Path_Recovery_impl ::
  "('v, 'tasks, 'links, 'output) Blossom_Path_Recovery_state \<Rightarrow>
    ('v, 'tasks, 'links, 'output) Blossom_Path_Recovery_state" where
  "Blossom_Path_Recovery_impl state =
    (if Blossom_Path_Recovery_call_1_conds state then Blossom_Path_Recovery_impl (Blossom_Path_Recovery_upd1 state)
     else Blossom_Path_Recovery_ret1 state)"

lemmas [code] = Blossom_Path_Recovery_impl.simps[unfolded
  Blossom_Path_Recovery_call_1_conds_def Blossom_Path_Recovery_upd1_def Blossom_Path_Recovery_ret1_def
  recovery_done_def recovery_step_def visit_step_def cycle_step_def next_component_def
  emit_vertex_def cache_route_def]

lemma Blossom_Path_Recovery_impl_same:
  "Blossom_Path_Recovery_dom state \<Longrightarrow> Blossom_Path_Recovery_impl state = Blossom_Path_Recovery state"
  by(induction rule: Blossom_Path_Recovery.pinduct)
    (subst Blossom_Path_Recovery_impl.simps, subst Blossom_Path_Recovery.psimps, auto)

lemmas Blossom_Path_Recovery_call_1_conds[call_cond_elims] =
  Blossom_Path_Recovery_call_1_conds_def[THEN iffD1, elim_format,
    unfolded atomize_conjL[symmetric]]

lemmas Blossom_Path_Recovery_call_1_condsI[call_cond_intros] =
  Blossom_Path_Recovery_call_1_conds_def[THEN iffD2,
    unfolded atomize_conjL[symmetric]]

lemmas Blossom_Path_Recovery_ret_1_conds[call_cond_elims] =
  Blossom_Path_Recovery_ret_1_conds_def[unfolded Blossom_Path_Recovery_call_1_conds_def not_not,
    THEN iffD1, elim_format,
    unfolded atomize_conjL[symmetric]]

lemmas Blossom_Path_Recovery_ret_1_condsI[call_cond_intros] =
  Blossom_Path_Recovery_ret_1_conds_def[unfolded Blossom_Path_Recovery_call_1_conds_def not_not,
    THEN iffD2,
    unfolded atomize_conjL[symmetric]]

lemma Blossom_Path_Recovery_cases:
  "\<lbrakk>Blossom_Path_Recovery_call_1_conds state \<Longrightarrow> P; Blossom_Path_Recovery_ret_1_conds state \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(auto simp: Blossom_Path_Recovery_ret_1_conds_def)

lemma Blossom_Path_Recovery_simps:
  "\<lbrakk>Blossom_Path_Recovery_dom state; Blossom_Path_Recovery_call_1_conds state\<rbrakk> \<Longrightarrow>
    Blossom_Path_Recovery state = Blossom_Path_Recovery (Blossom_Path_Recovery_upd1 state)"
  "\<lbrakk>Blossom_Path_Recovery_dom state; Blossom_Path_Recovery_ret_1_conds state\<rbrakk> \<Longrightarrow>
    Blossom_Path_Recovery state = Blossom_Path_Recovery_ret1 state"
  by(auto simp: Blossom_Path_Recovery.psimps Blossom_Path_Recovery_ret_1_conds_def)

lemma Blossom_Path_Recovery_induct:
  "\<lbrakk>Blossom_Path_Recovery_dom state;
    \<And>s. \<lbrakk>Blossom_Path_Recovery_dom s;
      Blossom_Path_Recovery_call_1_conds s \<Longrightarrow> P (Blossom_Path_Recovery_upd1 s)\<rbrakk> \<Longrightarrow> P s\<rbrakk> \<Longrightarrow> P state"
  by(induction rule: Blossom_Path_Recovery.pinduct) auto

lemma Blossom_Path_Recovery_domintros:
  "(Blossom_Path_Recovery_call_1_conds state \<Longrightarrow> Blossom_Path_Recovery_dom (Blossom_Path_Recovery_upd1 state)) \<Longrightarrow>
    Blossom_Path_Recovery_dom state"
  by(rule Blossom_Path_Recovery.domintros) auto

lemma Blossom_Path_Recovery_ret[ret_holds_intros]:
  assumes "Blossom_Path_Recovery_dom state"
  shows "Blossom_Path_Recovery_ret_1_conds (Blossom_Path_Recovery state)"
proof(induction rule: Blossom_Path_Recovery_induct[OF assms])
  case IH: (1 state)
  show ?case
    by(rule Blossom_Path_Recovery_cases[where state = state])
      (insert IH, auto simp: Blossom_Path_Recovery_simps Blossom_Path_Recovery_ret1_def)
qed

definition "initial_recovery p es T J out =
  \<lparr>qbr_path = p, qbr_crossings = es, qbr_entry = nil, qbr_tasks = T,
    qbr_hints = J, qbr_output = out, qbr_length = 0\<rparr>"

definition "lift_path p es T J out = Blossom_Path_Recovery_impl (initial_recovery p es T J out)"

definition "recovered_path state = map (output_lookup (qbr_output state)) [0..<qbr_length state]"

end

definition "invar_recovery_adts state \<longleftrightarrow>
  task_invar (qbr_tasks state) \<and>
  output_invar (qbr_output state) \<and>
  qbr_length state \<le> output_cap"

lemmas invar_recovery_adts_props[invar_props_elims] =
  invar_recovery_adts_def[THEN iffD1, elim_format, unfolded atomize_conjL[symmetric]]

lemmas invar_recovery_adts_intro[invar_props_intros] =
  invar_recovery_adts_def[THEN iffD2, unfolded atomize_conjL[symmetric]]

end

locale Quadratic_Blossom_Search_Lifting =
  Quadratic_Blossom_Search
    where hierarchy_merge = hierarchy_merge and edge_lookup = edge_lookup
      and base_lookup = base_lookup and link_lookup = link_lookup +
  Recovery: Blossom_Path_Recovery
    where hierarchy_children = hierarchy_children and edge_lookup = edge_lookup
      and K = K and nil = nil and base_invar = base_invar and base_update = base_update and base_lookup = base_lookup
      and link_invar = link_invar and link_update = link_update and link_lookup = link_lookup
  for hierarchy_merge :: "'hierarchy \<Rightarrow> 'v list \<Rightarrow> 'v \<Rightarrow> 'hierarchy"
    and edge_lookup :: "'edges \<Rightarrow> 'v \<Rightarrow> ('v \<times> 'v)"
    and base_lookup :: "'bases \<Rightarrow> 'v \<Rightarrow> 'v"
    and link_lookup :: "'links \<Rightarrow> 'v \<Rightarrow> ('v \<times> nat)"
begin

context fixes H :: 'hierarchy and B :: 'edges and D :: 'bases and N :: 'links begin

subsection "Recovering invariants and workspace conditions"

definition "hierarchy_relation =
  {(c, b). b \<in> hierarchy_ids H \<and> c \<in> set (hierarchy_children H b)}"

definition "hierarchy_size b = card (hierarchy_members H b)"

abbreviation "original_base b \<equiv> base_lookup D b"

definition "route_ancestors b target =
  {c \<in> hierarchy_ids H. (target, c) \<in> trancl hierarchy_relation \<and>
    (c, b) \<in> rtrancl hierarchy_relation}"

definition "route_cached b target J \<longleftrightarrow>
  (\<forall>c \<in> route_ancestors b target. fst (link_lookup J c) = target)"

definition "Cache_Route_term_rel' = inv_image (converse hierarchy_relation) cache_current"

definition "recovery_tree \<longleftrightarrow>
  finite (hierarchy_ids H) \<and>
  wf hierarchy_relation \<and>
  (\<forall>b \<in> hierarchy_ids H. let cs = hierarchy_children H b in
    if cs = [] then b \<in> V0 \<and> hierarchy_members H b = {b}
    else distinct cs \<and> odd (length cs) \<and> 3 \<le> length cs \<and> set cs \<subseteq> hierarchy_ids H \<and>
      hierarchy_members H b = \<Union> (hierarchy_members H ` set cs) \<and>
      pairwise (\<lambda>c d. hierarchy_members H c \<inter> hierarchy_members H d = {}) (set cs))"

definition "invar_navigation \<longleftrightarrow>
  base_invar D \<and>
  link_invar N \<and>
  (\<forall>b \<in> hierarchy_ids H. original_base b \<in> hierarchy_members H b \<and>
    (if hierarchy_children H b = [] then original_base b = b
     else original_base b = original_base (hd (hierarchy_children H b)))) \<and>
  (\<forall>b \<in> hierarchy_ids H. \<forall>i < length (hierarchy_children H b).
    link_lookup N (hierarchy_children H b ! i) = (b, i))"

lemmas invar_navigation_props[invar_props_elims] =
  invar_navigation_def[THEN iffD1, elim_format, unfolded atomize_conjL[symmetric]]

lemmas invar_navigation_intro[invar_props_intros] =
  invar_navigation_def[THEN iffD2, unfolded atomize_conjL[symmetric]]

definition "invar_recovering_structure \<longleftrightarrow>
  hierarchy_invar H \<and> edge_invar B \<and> recovery_tree \<and> invar_navigation \<and>
  (\<forall>b \<in> hierarchy_ids H.
    Vs {e \<in> mate_abstract M0. e \<subseteq> hierarchy_members H b} =
      hierarchy_members H b - {original_base b}) \<and>
  (\<forall>b \<in> hierarchy_ids H. let cs = hierarchy_children H b in
    \<forall>i < length cs. let c = cs ! i; d = cs ! (Suc i mod length cs);
                        (u, v) = edge_lookup B c
                   in u \<in> hierarchy_members H c \<and>
                     v \<in> hierarchy_members H d \<and> {u, v} \<in> input_graph \<and>
                     ({u, v} \<in> mate_abstract M0 \<longleftrightarrow> odd i))"

text "The pending visits, ancestor sets, routes, and measures below are proof-only. They describe
  the remaining work through public hierarchy observations and the abstract stack contents;
  the executable loop does not construct these sets or lists."

definition "cycle_indices b i j forward =
  (let n = length (hierarchy_children H b);
       distance = (if forward then (j + n - i) mod n else (i + n - j) mod n)
   in if n = 0 then map (\<lambda>k. if forward then i + k else i - k) [0..<Suc distance]
      else take (Suc distance)
        (if forward then rotate i [0..<n] else rev (rotate (Suc i) [0..<n])))"

definition "cycle_edge c d forward =
  (if forward then edge_lookup B c
   else case edge_lookup B d of (u, v) \<Rightarrow> (v, u))"

definition "cycle_visits b i j forward a z =
  (let cs = hierarchy_children H b; route = cycle_indices b i j forward;
       crossing = (\<lambda>k. cycle_edge (cs ! (route ! k)) (cs ! (route ! Suc k)) forward)
   in map (\<lambda>k. (cs ! (route ! k),
       if k = 0 then a else snd (crossing (k - 1)),
       if Suc k = length route then z else fst (crossing k))) [0..<length route])"

definition "task_visits task =
  (case task of Quadratic_Visit b a z \<Rightarrow> [(b, a, z)]
   | Quadratic_Cycle b i j forward a z \<Rightarrow> cycle_visits b i j forward a z)"

definition "quotient_visits state =
  map (\<lambda>i. let b = qbr_path state ! i in (b,
    if i = 0 then (if qbr_entry state = nil then original_base b else qbr_entry state)
      else snd (qbr_crossings state ! (i - 1)),
    if i < length (qbr_crossings state) then fst (qbr_crossings state ! i)
      else original_base b)) [0..<length (qbr_path state)]"

definition "pending_visits state =
  concat (map task_visits (task_abstract (qbr_tasks state))) @ quotient_visits state"

definition "pending_members state = \<Union> (hierarchy_members H ` set (map fst (pending_visits state)))"

definition "visit_admissible b a z \<longleftrightarrow>
  b \<in> hierarchy_ids H \<and> a \<in> hierarchy_members H b \<and> z \<in> hierarchy_members H b \<and>
  (a = original_base b \<or> z = original_base b)"

definition "visit_route b a z p \<longleftrightarrow>
  visit_admissible b a z \<and> p \<noteq> [] \<and> hd p = a \<and> last p = z \<and> distinct p \<and>
  set p \<subseteq> hierarchy_members H b \<and> odd (length p) \<and> set (edges_of_path p) \<subseteq> input_graph \<and>
  (if a = original_base b then alt_path (mate_abstract M0) p else rev_alt_path (mate_abstract M0) p)"

definition "task_admissible task \<longleftrightarrow>
  (case task of Quadratic_Visit b a z \<Rightarrow> visit_admissible b a z
   | Quadratic_Cycle b i j forward a z \<Rightarrow>
       b \<in> hierarchy_ids H \<and> i < length (hierarchy_children H b) \<and> j < length (hierarchy_children H b) \<and>
       list_all (\<lambda>(c, x, y). visit_admissible c x y) (cycle_visits b i j forward a z))"

definition "task_measure task =
  sum_list (map (\<lambda>(b, a, z). 4 * hierarchy_size b - 2) (task_visits task)) +
  (case task of Quadratic_Visit b a z \<Rightarrow> 0
   | Quadratic_Cycle b i j forward a z \<Rightarrow> length (cycle_indices b i j forward))"

definition "recovery_measure state =
  sum_list (map task_measure (task_abstract (qbr_tasks state))) +
  sum_list (map (\<lambda>b. Suc (4 * hierarchy_size b - 2)) (qbr_path state))"

definition "Blossom_Path_Recovery_term_rel' = measure recovery_measure"

subsection "Recovery invariants"

definition "invar_route_cache J \<longleftrightarrow>
  link_invar J \<and>
  (\<forall>b \<in> hierarchy_ids H. hierarchy_children H b \<noteq> [] \<and> fst (link_lookup J b) \<noteq> nil \<longrightarrow>
    snd (link_lookup J b) < length (hierarchy_children H b) \<and>
    fst (link_lookup J b) \<in> hierarchy_members H (hierarchy_children H b ! snd (link_lookup J b)))"

lemmas invar_route_cache_props[invar_props_elims] =
  invar_route_cache_def[THEN iffD1, elim_format, unfolded atomize_conjL[symmetric]]

lemmas invar_route_cache_intro[invar_props_intros] =
  invar_route_cache_def[THEN iffD2, unfolded atomize_conjL[symmetric]]

definition "invar_cache_route b target state \<longleftrightarrow>
  b \<in> hierarchy_ids H \<and>
  target \<in> hierarchy_members H b \<and>
  cache_current state \<in> hierarchy_ids H \<and>
  (target, cache_current state) \<in> rtrancl hierarchy_relation \<and>
  (cache_current state, b) \<in> rtrancl hierarchy_relation \<and>
  invar_route_cache (cache_hints state) \<and>
  route_cached (cache_current state) target (cache_hints state)"

lemmas invar_cache_route_props[invar_props_elims] =
  invar_cache_route_def[THEN iffD1, elim_format, unfolded atomize_conjL[symmetric]]

lemmas invar_cache_route_intro[invar_props_intros] =
  invar_cache_route_def[THEN iffD2, unfolded atomize_conjL[symmetric]]

definition "invar_recovery_alignment state \<longleftrightarrow>
  length (qbr_crossings state) = length (qbr_path state) - 1 \<and>
  (\<forall>e \<in> set (qbr_crossings state). snd e \<noteq> nil)"

lemmas invar_recovery_alignment_props[invar_props_elims] =
  invar_recovery_alignment_def[THEN iffD1, elim_format, unfolded atomize_conjL[symmetric]]

lemmas invar_recovery_alignment_intro[invar_props_intros] =
  invar_recovery_alignment_def[THEN iffD2, unfolded atomize_conjL[symmetric]]

definition "invar_recovery_tasks state \<longleftrightarrow>
  list_all task_admissible (task_abstract (qbr_tasks state)) \<and>
  list_all (\<lambda>(b, a, z). visit_admissible b a z) (pending_visits state) \<and>
  length (task_abstract (qbr_tasks state)) \<le> card (hierarchy_ids H)"

lemmas invar_recovery_tasks_props[invar_props_elims] =
  invar_recovery_tasks_def[THEN iffD1, elim_format, unfolded atomize_conjL[symmetric]]

lemmas invar_recovery_tasks_intro[invar_props_intros] =
  invar_recovery_tasks_def[THEN iffD2, unfolded atomize_conjL[symmetric]]

definition "invar_recovery_disjoint state \<longleftrightarrow>
  distinct (Recovery.recovered_path state) \<and>
  distinct (map fst (pending_visits state)) \<and>
  pairwise (\<lambda>c d. hierarchy_members H c \<inter> hierarchy_members H d = {})
    (set (map fst (pending_visits state))) \<and>
  set (Recovery.recovered_path state) \<subseteq> V0 \<and>
  set (Recovery.recovered_path state) \<inter> pending_members state = {}"

lemmas invar_recovery_disjoint_props[invar_props_elims] =
  invar_recovery_disjoint_def[THEN iffD1, elim_format, unfolded atomize_conjL[symmetric]]

lemmas invar_recovery_disjoint_intro[invar_props_intros] =
  invar_recovery_disjoint_def[THEN iffD2, unfolded atomize_conjL[symmetric]]

definition "invar_recovery_completion state \<longleftrightarrow>
  (\<forall>paths. list_all2 (\<lambda>(b, a, z) p. visit_route b a z p) (pending_visits state) paths \<longrightarrow>
    graph_augmenting_path input_graph (mate_abstract M0)
      (Recovery.recovered_path state @ concat paths))"

lemmas invar_recovery_completion_props[invar_props_elims] =
  invar_recovery_completion_def[THEN iffD1, elim_format, unfolded atomize_conjL[symmetric]]

lemmas invar_recovery_completion_intro[invar_props_intros] =
  invar_recovery_completion_def[THEN iffD2, unfolded atomize_conjL[symmetric]]

definition "visit_target b a z = (if a = original_base b then z else a)"

definition "invar_recovery_routing state \<longleftrightarrow>
  invar_route_cache (qbr_hints state) \<and>
  (\<forall>c \<in> hierarchy_ids H. hierarchy_children H c \<noteq> [] \<and> fst (link_lookup (qbr_hints state) c) \<noteq> nil \<longrightarrow>
    route_cached c (fst (link_lookup (qbr_hints state) c)) (qbr_hints state)) \<and>
  (\<forall>b a z. (b,a,z) \<in> set (pending_visits state) \<and> a \<noteq> z \<longrightarrow>
    (\<forall>c \<in> hierarchy_ids H. hierarchy_children H c \<noteq> [] \<and>
      (c,b) \<in> rtrancl hierarchy_relation \<and> fst (link_lookup (qbr_hints state) c) \<noteq> nil \<longrightarrow>
      fst (link_lookup (qbr_hints state) c) = visit_target b a z))"

lemmas invar_recovery_routing_props[invar_props_elims] =
  invar_recovery_routing_def[THEN iffD1, elim_format, unfolded atomize_conjL[symmetric]]

lemmas invar_recovery_routing_intro[invar_props_intros] =
  invar_recovery_routing_def[THEN iffD2, unfolded atomize_conjL[symmetric]]

definition "invar_recovery state \<longleftrightarrow>
  invar_recovering_structure \<and>
  Recovery.invar_recovery_adts state \<and>
  invar_recovery_alignment state \<and>
  invar_recovery_tasks state \<and>
  invar_recovery_disjoint state \<and>
  invar_recovery_completion state \<and>
  invar_recovery_routing state"

lemmas invar_recovery_props[invar_props_elims] =
  invar_recovery_def[THEN iffD1, elim_format, unfolded atomize_conjL[symmetric]]

lemmas invar_recovery_intro[invar_props_intros] =
  invar_recovery_def[THEN iffD2, unfolded atomize_conjL[symmetric]]

definition "recovery_workspaces T out \<longleftrightarrow>
  task_invar T \<and> task_abstract T = [] \<and> output_invar out \<and> length vs \<le> output_cap \<and>
  Suc (card (hierarchy_ids H)) \<le> task_cap"

end

definition "recovery_precond state T out \<longleftrightarrow>
  invar_representatives state \<and>
  invar_recovering_structure (qbs_hierarchy state) (qbs_cycle_edges state)
    (qbs_bases state) (qbs_parents state) \<and>
  link_invar (qbs_hints state) \<and>
  (\<forall>b \<in> hierarchy_ids (qbs_hierarchy state). hierarchy_children (qbs_hierarchy state) b \<noteq> [] \<longrightarrow>
    fst (link_lookup (qbs_hints state) b) = nil) \<and>
  recovery_workspaces (qbs_hierarchy state) T out \<and>
  (case qbs_status state of Quadratic_Path p es \<Rightarrow> invar_recovering_path state p es
   | _ \<Rightarrow> False)"

text "The navigation maps are maintained during search through fixed-universe map ADTs.
  Recovery follows parent links on a cache miss and retains the child position at every
  ancestor reached. Subsequent nested visits use these cached positions. No preprocessing
  traversal or descendant-set construction is executed. The companion preservation theory proves
  the recovering invariants, cache compatibility, visit uniqueness, termination, capacities and
  correctness. Operation bounds remain to be proved."

definition "invar_search state \<longleftrightarrow>
  invar_adts state \<and>
  invar_forest state \<and>
  invar_matching_projection state \<and>
  invar_representatives state \<and>
  invar_components state \<and>
  invar_neighbours state \<and> invar_current state \<and>
  invar_queue state \<and>
  invar_scanned state \<and>
  invar_fresh state \<and>
  invar_annotations state \<and>
  invar_hierarchy_size state \<and>
  invar_existence state \<and>
  invar_result state \<and>
  invar_recovering_structure (qbs_hierarchy state) (qbs_cycle_edges state)
    (qbs_bases state) (qbs_parents state) \<and>
  (\<forall>b \<in> hierarchy_ids (qbs_hierarchy state). hierarchy_children (qbs_hierarchy state) b \<noteq> [] \<longrightarrow>
    fst (link_lookup (qbs_hints state) b) = nil)"

lemmas invar_search_props[invar_props_elims] =
  invar_search_def[THEN iffD1, elim_format, unfolded atomize_conjL[symmetric]]

lemmas invar_search_intro[invar_props_intros] =
  invar_search_def[THEN iffD2, unfolded atomize_conjL[symmetric]]

definition "initial_recovery_axioms T out \<longleftrightarrow>
  task_invar T \<and> task_abstract T = [] \<and> output_invar out \<and> length vs \<le> output_cap \<and>
  Suc (length vs + length vs div 2) \<le> task_cap"

subsection "Combining search and recovery"

definition "result_path state T out =
  (case qbs_status state of Quadratic_Path p es \<Rightarrow>
     Recovery.lift_path (qbs_hierarchy state) (qbs_cycle_edges state)
       (qbs_bases state) (qbs_parents state) p es T (qbs_hints state) out
   | _ \<Rightarrow> Recovery.initial_recovery [] [] T (qbs_hints state) out)"

definition "Quadratic_Blossom_Search_run U L C H P B D N J fresh T out =
  result_path (Quadratic_Blossom_Search_impl (initial_state U L C H P B D N J fresh)) T out"

definition "augmenting_path_result_spec result \<longleftrightarrow>
  (if qbr_length result = 0 then \<not> (\<exists>p. graph_augmenting_path input_graph (mate_abstract M0) p)
   else graph_augmenting_path input_graph (mate_abstract M0) (Recovery.recovered_path result))"

end

section "Initial inputs and workspaces"

locale Quadratic_Blossom_Search_thms = Quadratic_Blossom_Search_Lifting +
  fixes U0 L0 C0 H0 P0 B0 D0 N0 J0 fresh0 T0 out0
  assumes initial_axioms: "initial_axioms U0 L0 C0 H0 P0 B0 D0 N0 J0 fresh0"
    and initial_recovery_axioms: "initial_recovery_axioms T0 out0"
begin

abbreviation "initial_search_state \<equiv> initial_state U0 L0 C0 H0 P0 B0 D0 N0 J0 fresh0"

text "The supplied hierarchy initially consists of the singleton input vertices. The
  initializer resets union-find and adjacency cursors, names the singleton components,
  forms the unmatched roots and their queue in one pass. Input conditions and workspace capacities are
  assumptions here. The companion preservation theory proves preservation, termination and
  correctness of the returned path."

lemma initial_inputs:
  "input_axioms C0" "uf_invar U0" "owner_invar L0" "edge_invar P0" "edge_invar B0"
  "base_invar D0" "link_invar N0" "link_invar J0"
  "hierarchy_invar H0" "hierarchy_ids H0 = V0" "hierarchy_tops H0 = V0"
  "hierarchy_universe H0 = V0"
  "\<forall>v \<in> V0. hierarchy_members H0 v = {v} \<and> hierarchy_children H0 v = []"
  "queue_invar fresh0" "distinct (queue_abstract fresh0)"
  "set (queue_abstract fresh0) \<subseteq> K - V0"
  "length vs div 2 \<le> length (queue_abstract fresh0)"
  using initial_axioms
  by(auto simp: initial_axioms_def)

lemma initial_workspaces:
  "task_invar T0" "task_abstract T0 = []"
  "output_invar out0" "length vs \<le> output_cap"
  "Suc (length vs + length vs div 2) \<le> task_cap"
  using initial_recovery_axioms
  by(auto simp: initial_recovery_axioms_def)

end


end
