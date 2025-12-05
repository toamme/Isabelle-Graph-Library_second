theory Hungarian_Method_Instantiation
  imports  Primal_Dual_Path_Search Alternating_Forest_Executable Ordered_Map_Heap
Naive_Primal_Dual "HOL-Library.Rewrite"
Matching_Augmentation_Executable
Hungarian_Method_Top_Loop
(*Graph_Algorithms_Dev.DFS_Example
 "HOL-Library.Product_Lexorder"*)
begin
hide_const R
term R

text \<open>Let's instantiate the path search\<close>

global_interpretation pd_path_search_spec: primal_dual_path_search_spec
  (*the graph*)
  where G = G
   and left = left
   and right = right
   and buddy = buddy
   and edge_costs = edge_costs
   and right_neighbs = right_neighbs
  (*the forest*)
   and evens = evens
   and odds = odds
   and abstract_forest = "abstract_forest parent_lookup"
   and get_path = "get_path parent_lookup"
   and extend_forest_even_unclassified = 
     "extend_forest_even_unclassified parent_upd vset_insert 
          origin_upd origin_lookup" 
   and empty_forest = 
      "empty_forest parent_empty vset_empty to_list origin_empty origin_upd"
  (*the heap*)
   and heap_insert = queue_insert
   and heap_decrease_key = queue_decrease_key
   and heap_empty = queue_empty
   and heap_extract_min = queue_extract_min
  (*the potential*)
   and initial_pot = initial_pot
   and potential_lookup = potential_lookup
   and potential_upd = potential_upd
  (*missed change in potential*)
   and missed_lookup = missed_lookup
   and missed_empty = missed_empty
   and missed_upd = missed_upd
  (*best even neighbour map*)
   and ben_upd = ben_upd
   and ben_lookup = ben_lookup
   and ben_empty = ben_empty
  (*sets of vertices*)
   and vset_isin= vset_isin
   and to_list = to_list
   and vset_to_set = vset_to_set
   and vset_insert = vset_insert
   and vset_empty = vset_empty
 for (*the graph*) G left right buddy edge_costs right_neighbs
     (*the forest*) parent_lookup  parent_upd parent_empty
                    origin_upd origin_lookup origin_empty 
     (*the potential*) initial_pot potential_lookup potential_upd
     (*missed change in potential*) missed_lookup missed_empty missed_upd
     (*best even neighbour map*) ben_upd ben_lookup ben_empty
     (*sets of vertices*) vset_isin to_list vset_to_set vset_insert vset_empty

defines search_path = pd_path_search_spec.search_path
  and search_path_loop_impl = pd_path_search_spec.search_path_loop_impl
  and new_potential = pd_path_search_spec.new_potential
  and w\<^sub>\<pi>=pd_path_search_spec.w\<^sub>\<pi>
  and path_search_initial_state = pd_path_search_spec.initial_state
  and unmatched_lefts= pd_path_search_spec.unmatched_lefts
  and init_best_even_neighbour = pd_path_search_spec.init_best_even_neighbour
  and update_best_even_neighbours = pd_path_search_spec.update_best_even_neighbours
  and update_best_even_neighbour = pd_path_search_spec.update_best_even_neighbour
  and path_search_forest_roots = pd_path_search_spec.forest_roots
  done

(*manual fix of "partially applied constant on left hand side of equation"*)
lemmas [code] = pd_path_search_spec.search_path_def[folded search_path_def  path_search_initial_state_def]
                pd_path_search_spec.initial_state_def[folded path_search_initial_state_def]

(*hide_const RBT_Set.insert*)
                
locale path_search_instantiated_correct = 
  fixes G::"('v::linorder) set set"
    and edge_costs::"'v \<Rightarrow> 'v \<Rightarrow> real"
    and left::'vset
    and right::'vset
    and in_G::"'v \<Rightarrow> 'v \<Rightarrow> bool"
    and right_neighbs::"'v \<Rightarrow> 'vset"

    and buddy::"'v \<Rightarrow> 'v option"

   and potential_upd::"'potential \<Rightarrow> 'v \<Rightarrow> real \<Rightarrow> 'potential"
   and potential_lookup::"'potential \<Rightarrow> 'v \<Rightarrow> real option"
   and potential_invar::"'potential \<Rightarrow> bool"
   and initial_pot::"'potential"

   and ben_empty::'ben
   and ben_lookup::"'ben \<Rightarrow> 'v \<Rightarrow> 'v option"
   and ben_upd::"'ben \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'ben"
   and ben_invar::"'ben \<Rightarrow> bool"

   and missed_empty::'miss
   and missed_lookup::"'miss \<Rightarrow> 'v \<Rightarrow> real option"
   and missed_upd::"'miss \<Rightarrow> 'v \<Rightarrow> real \<Rightarrow> 'miss"
   and missed_invar::"'miss \<Rightarrow> bool"

   and to_list::"'vset \<Rightarrow> 'v list"
   and vset_to_set::"'vset \<Rightarrow> 'v set"
   and vset_isin::"'v \<Rightarrow> 'vset \<Rightarrow> bool"
   and vset_empty::"'vset"
   and vset_insert::"'v \<Rightarrow> 'vset \<Rightarrow> 'vset"
   and vset_invar::"'vset \<Rightarrow> bool"

   and parent_empty::'parent
    and   parent_upd::"'v\<Rightarrow>'v\<Rightarrow>'parent\<Rightarrow>'parent"
    and   parent_lookup::"'parent \<Rightarrow> 'v \<Rightarrow> 'v option"
    and   parent_delete::"'v \<Rightarrow> 'parent \<Rightarrow>'parent"
    and   parent_invar::"'parent \<Rightarrow> bool"

and   origin_empty::'origin
and   origin_upd::"'v\<Rightarrow>'v\<Rightarrow>'origin\<Rightarrow>'origin"
and   origin_lookup::"'origin \<Rightarrow> 'v \<Rightarrow> 'v option"
and   origin_invar::"'origin \<Rightarrow> bool"

assumes G: "bipartite G (vset_to_set left) (vset_to_set right)"
           "\<And> u v. in_G u v \<longleftrightarrow> {u, v} \<in> G"
           "vset_invar left" "vset_invar right"

           "\<And> v. v \<in> vset_to_set left \<Longrightarrow> vset_invar (right_neighbs v)"
           "\<And> v. v \<in> vset_to_set left \<Longrightarrow> vset_to_set (right_neighbs v) = {u | u. {v, u} \<in> G}"
           "\<And> u v. {u, v} \<in> G \<Longrightarrow> edge_costs u v = edge_costs v u"
           "\<And> u v. {u, v} \<in> G \<Longrightarrow> abstract_real_map (potential_lookup initial_pot) u 
                                 + abstract_real_map (potential_lookup initial_pot) v 
                                  \<le> edge_costs u v"
  
and matching: "\<And> u v. buddy u = Some v \<Longrightarrow> buddy v = Some u"
              "graph_matching G {{u, v} | u v. buddy u = Some v}"
              "\<And> u v. {u, v} \<in> {{u, v} | u v. buddy u = Some v} 
           \<Longrightarrow> abstract_real_map (potential_lookup initial_pot) u 
                                 + abstract_real_map (potential_lookup initial_pot) v 
                                  = edge_costs u v"
and potential:
 "potential_invar initial_pot"
 "\<And> pot x s. potential_invar pot \<Longrightarrow> potential_invar (potential_upd pot x s)"
 "\<And> pot x s. potential_invar pot \<Longrightarrow> potential_lookup (potential_upd pot x s) =
                (potential_lookup pot)(x \<mapsto> s)"
and best_even_neighbour:
 "ben_invar ben_empty"
  "\<And> ben x s. ben_invar ben \<Longrightarrow> ben_invar (ben_upd ben x s)"
  "\<And> ben x s. ben_invar ben \<Longrightarrow> ben_lookup (ben_upd ben x s) =
                (ben_lookup ben)(x \<mapsto> s)"
  "\<And> x. ben_lookup ben_empty x = None"
and vset:
 "vset_invar vset_empty" "vset_to_set vset_empty = {}"
 "\<And> V v. vset_invar V \<Longrightarrow> vset_invar (vset_insert v V)"
 "\<And> V v. vset_invar V \<Longrightarrow> vset_to_set (vset_insert v V) = insert v (vset_to_set V)"
 "\<And> V v. vset_invar V \<Longrightarrow> vset_isin v V \<longleftrightarrow> v \<in> vset_to_set V"
 "\<And> V vs. \<lbrakk>vset_invar V; to_list V = vs\<rbrakk> \<Longrightarrow> distinct vs"
 "\<And> V vs. \<lbrakk>vset_invar V; to_list V = vs\<rbrakk> \<Longrightarrow> set vs = vset_to_set V"
and missed:
 "missed_invar missed_empty" "\<And> x. missed_lookup missed_empty x= None"
  "\<And> missed x s. missed_invar missed \<Longrightarrow> missed_invar (missed_upd missed x s)"
  "\<And> missed x s. missed_invar missed \<Longrightarrow> missed_lookup (missed_upd missed x s) =
                (missed_lookup missed)(x \<mapsto> s)"
  "\<And> x. missed_lookup missed_empty x = None"
and potential_in_G:
"dom (potential_lookup initial_pot) \<subseteq> vset_to_set left \<union> vset_to_set right"
    and parent:
    "parent_invar parent_empty"
    "parent_lookup parent_empty = (\<lambda> x. None)"
    "\<And> par x s. parent_invar par \<Longrightarrow> parent_invar (parent_upd x s par)"
    "\<And> par x s. parent_invar par \<Longrightarrow> parent_lookup (parent_upd x s par) =
                (parent_lookup par)(x \<mapsto> s)"
    and origin:
    "origin_invar origin_empty"
    "origin_lookup origin_empty = (\<lambda> x. None)"
    "\<And> par x s. origin_invar par \<Longrightarrow> origin_invar (origin_upd x s par)"
    "\<And> par x s. origin_invar par \<Longrightarrow> origin_lookup (origin_upd x s par) =
                (origin_lookup par)(x \<mapsto> s)"
and buddies:
 "buddy_invar buddy_empty"
  "\<And> buddy u v. buddy_invar buddy \<Longrightarrow> buddy_invar (buddy_upd  u v buddy)"
  "\<And> buddy u v. buddy_invar buddy \<Longrightarrow> buddy_lookup (buddy_upd  u v buddy) =
                (buddy_lookup buddy)(u \<mapsto> v)"
  "\<And> u. buddy_lookup buddy_empty u = None"
begin

interpretation fmnlp: forest_manipulation
  where vset_flatten = to_list
  using vset(1-5) vset (6-7)[OF _ refl]
  by(auto intro!: forest_manipulation.intro parent origin)

abbreviation "forest_invar == fmnlp.forest_invar"

interpretation  satisfied_simple:
 alternating_forest_spec evens odds "get_path parent_lookup" "abstract_forest parent_lookup"
     forest_invar roots vset_invar vset_to_set
  unfolding abstract_forest_def get_path_def
  apply(intro alternating_forest_spec.intro 
      fmnlp.simple_invariant_consequences)
  using fmnlp.complex_invariant_consequences(1,2) 
  by(auto simp add: fmnlp.get_path_correct(1,2,3,4,5))

interpretation fe_spec: 
     alternating_forest_ordinary_extension_spec vset_invar vset_to_set evens odds
     "get_path parent_lookup" "abstract_forest parent_lookup" forest_invar roots vset_empty
     "extend_forest_even_unclassified parent_upd vset_insert origin_upd origin_lookup"
     "empty_forest parent_empty vset_empty to_list origin_empty origin_upd"
  apply(intro alternating_forest_ordinary_extension_spec.intro
      satisfied_simple.alternating_forest_spec_axioms
      alternating_forest_ordinary_extension_spec_axioms.intro)
  by (simp_all add:  fmnlp.extension_main_preservation fmnlp.satisfied_simple_extension_precond_same
      fmnlp.extension_abstract_is fmnlp.extension_evens fmnlp.extension_odds fmnlp.extension_roots 
      fmnlp.empty_forest_correctess  extend_forest_even_unclassified_def 
      abstract_forest_def empty_forest_def )

interpretation pd_path_search: primal_dual_path_search
  (*the graph*)
  where G = G
   and left = left
   and right = right
   and buddy = buddy
   and edge_costs = edge_costs
   and right_neighbs = right_neighbs
  (*the forest*)
   and evens = evens
   and odds = odds
   and abstract_forest = "abstract_forest parent_lookup"
   and get_path = "get_path parent_lookup"
   and extend_forest_even_unclassified = 
     "extend_forest_even_unclassified parent_upd vset_insert 
          origin_upd origin_lookup" 
   and empty_forest = 
      "empty_forest parent_empty vset_empty to_list origin_empty origin_upd"
   and roots = roots
   and forest_invar = forest_invar
  (*the heap*)
   and heap_insert = queue_insert
   and heap_decrease_key = queue_decrease_key
   and heap_empty = queue_empty
   and heap_extract_min = queue_extract_min
   and heap_invar = queue_invar
   and heap_abstract = queue_abstract
  (*the potential*)
   and initial_pot = initial_pot
   and potential_lookup = potential_lookup
   and potential_upd = potential_upd
  (*missed change in potential*)
   and missed_lookup = missed_lookup
   and missed_empty = missed_empty
   and missed_upd = missed_upd
  (*best even neighbour map*)
   and ben_upd = ben_upd
   and ben_lookup = ben_lookup
   and ben_empty = ben_empty
  (*sets of vertices*)
   and vset_isin= vset_isin
   and to_list = to_list
   and vset_to_set = vset_to_set
   and vset_insert = vset_insert
   and vset_empty = vset_empty
proof(rule primal_dual_path_search.intro, goal_cases)
  case 1
  thus ?case
    using fe_spec.alternating_forest_ordinary_extension_spec_axioms
    by simp
next
  case 2
  thus ?case
    using key_value_queue_spec_satisfied.key_value_queue_axioms by simp
next
  case 3
  thus ?case
    apply(intro primal_dual_path_search_axioms.intro G potential 
            best_even_neighbour vset(1-5) missed  potential_in_G)+
    using matching(2) vset(7)
    by (fastforce intro: matching(1,3) vset(6)
               simp add: pd_path_search_spec.\<M>_def) +   
qed

lemmas search_path_correct = pd_path_search.search_path_correct
end
(*hide_const nbs*)
locale build_init_potential_spec =
  fixes vs::"'v list"
  and   neighbs::"'v \<Rightarrow> 'vset option"
  and   to_list::"'vset \<Rightarrow> 'v list"
  and   vset_to_set::"'vset \<Rightarrow> 'v set"
  and   vset_invar::"'vset \<Rightarrow> bool"
  and   edge_costs::"'v \<Rightarrow> 'v \<Rightarrow> real"
  and   empty_potential::'potential
  and   potential_upd::"'potential \<Rightarrow> 'v \<Rightarrow> real  \<Rightarrow> 'potential"
  and   potential_lookup::"'potential \<Rightarrow> 'v \<Rightarrow> real option"
  and   potential_invar::"'potential \<Rightarrow> bool"
begin

definition "init_potential = 
  foldl (\<lambda> \<pi> u. case neighbs u of None \<Rightarrow> \<pi>
                | Some nbs \<Rightarrow>
             foldl (\<lambda> \<pi> v. (case potential_lookup \<pi> u of
                               None \<Rightarrow> potential_upd  \<pi> u (edge_costs u v)
                              | Some r \<Rightarrow> if r \<le> edge_costs u v then \<pi>
                                          else potential_upd  \<pi> u (edge_costs u v)))
                  \<pi> (to_list nbs))
        empty_potential vs"

lemmas [code] = init_potential_def
end

global_interpretation build_init_pot: build_init_potential_spec
  where potential_lookup = potential_lookup 
and potential_upd = potential_upd
and empty_potential = empty_potential
and edge_costs = edge_costs
and to_list = to_list 
and neighbs = neighbs 
and vs = vs
for potential_lookup potential_upd empty_potential
    edge_costs to_list neighbs vs
  defines init_potential = build_init_pot.init_potential
  done

locale build_init_potential = 
build_init_potential_spec+
assumes vs_distinct: "distinct vs"
and neighbs: "\<And> v N. \<lbrakk> v \<in> set vs; neighbs v = Some N\<rbrakk> \<Longrightarrow> vset_invar N"
and vset: "\<And> S. vset_invar S \<Longrightarrow> distinct (to_list S)"
          "\<And> S. vset_invar S \<Longrightarrow> vset_to_set S = set (to_list S)"
and potential:
     "potential_invar empty_potential"
     "potential_lookup empty_potential = (\<lambda> v. None)"
     "\<And> p v r. potential_invar p \<Longrightarrow> potential_invar (potential_upd p v r)"
     "\<And> p v r. potential_invar p \<Longrightarrow>
        potential_lookup (potential_upd p v r) = (potential_lookup p)(v \<mapsto> r)"
begin

definition "less_than_edgs_bet p E = 
           (\<forall> e \<in> E. p (fst e) \<le> edge_costs (fst e) (snd e))" 


lemma less_than_edgs_bet_empty: "less_than_edgs_bet p {}"
  by(auto simp add: less_than_edgs_bet_def)

lemma init_potential_props:
   "potential_invar init_potential"
   "\<And> u v N. \<lbrakk>u \<in> set vs; neighbs u = Some N; v \<in> vset_to_set N\<rbrakk> \<Longrightarrow>
            abstract_real_map (potential_lookup init_potential) u \<le> edge_costs u v"
   "dom (potential_lookup init_potential) = 
    { v| v x. v \<in> set vs \<and> neighbs v \<noteq> None \<and>
           vset_to_set (the (neighbs v)) \<noteq> {}}"
proof-
  define inner_f where "inner_f = (\<lambda> u \<pi> v. (case potential_lookup \<pi> u of
                               None \<Rightarrow> potential_upd  \<pi> u (edge_costs u v)
                              | Some r \<Rightarrow> if r \<le> edge_costs u v then \<pi>
                                          else potential_upd  \<pi> u (edge_costs u v)))"
  define outer_f where "outer_f = (\<lambda> \<pi> u. case neighbs u of None \<Rightarrow> \<pi>
                | Some nbs \<Rightarrow> foldl (inner_f u) \<pi> (to_list nbs))"
  have inner_f_invar_pres: "potential_invar \<pi> \<Longrightarrow> potential_invar (inner_f u \<pi> v)" for u \<pi> v
    by(auto simp add: inner_f_def potential(3) split: option.split)
  have inner_f_prop_pres: 
   "less_than_edgs_bet (abstract_real_map (potential_lookup (inner_f u \<pi> v)))
           (insert (u, v) E)"
    "fst ` (insert (u, v) E) = dom (potential_lookup (inner_f u \<pi> v))"
   if "less_than_edgs_bet (abstract_real_map (potential_lookup \<pi>)) E" 
      "potential_invar \<pi>" 
      "fst ` E = dom (potential_lookup \<pi>)"for E \<pi> u v
    using  that 
      by(auto simp add: inner_f_def less_than_edgs_bet_def abstract_real_map_def
           potential(4) split: option.split)
    have inner_fold_invar_pres:
     "potential_invar (foldl (inner_f u) \<pi> xs)"
     if "potential_invar \<pi>" for u \<pi> xs
    proof-
      define ys where "ys = rev xs"
      show ?thesis
        using that
      unfolding foldl_conv_foldr ys_def[symmetric]
      by(induction ys)
        (auto intro!: inner_f_invar_pres)
  qed
  have inner_fold_props_pres:
      "less_than_edgs_bet (abstract_real_map (potential_lookup (foldl (inner_f u) \<pi> xs)))
           (E \<union> {(u, v) | v. v \<in> set xs})" (is ?rslt1)
    "fst `  (E \<union> {(u, v) | v. v \<in> set xs}) = dom (potential_lookup (foldl (inner_f u) \<pi> xs))" (is ?rslt2)
    if "less_than_edgs_bet (abstract_real_map (potential_lookup \<pi>)) E" 
      "potential_invar \<pi>" 
      "fst ` E = dom (potential_lookup \<pi>)"
    for u \<pi> xs E
  proof-
      define ys where "ys = rev xs"
      have  "?rslt1 \<and>?rslt2"
        using that 
        unfolding foldl_conv_foldr ys_def[symmetric] set_rev[of xs, symmetric]
      proof(induction ys)
        case Nil
        then show ?case by auto
      next
        case (Cons y ys)
        note IH_applied = conjunct1[OF Cons(1)[OF Cons(2,3,4)]] 
                          conjunct2[OF Cons(1)[OF Cons(2,3,4)]]
        note potential_now = inner_fold_invar_pres[OF Cons(3), of u "rev ys",
                                simplified foldl_conv_foldr rev_rev_ident]
        note inner_f_props_applied = inner_f_prop_pres[OF 
                      IH_applied(1) potential_now IH_applied(2)] 

        show ?case 
        proof(rule, goal_cases)
          case 1
          show ?case
            apply (subst foldr_Cons o_apply)+
            apply(rule rev_iffD2[OF inner_f_props_applied(1)[of u y]])
            apply(rule arg_cong[of "_ ::_ set"])
            by auto
        next
          case 2
           show ?case
            apply (subst foldr_Cons o_apply inner_f_props_applied(2)[symmetric])+         
             by force
         qed
       qed
       thus ?rslt1 ?rslt2 
         by auto
     qed
     let ?new_es = "{(u, v) | u v. u \<in> set vs \<and> neighbs u \<noteq> None \<and> v \<in> vset_to_set (the (neighbs u))}"
     have outer_iteration_pres:
      "potential_invar (foldl outer_f \<pi> vs)" (is ?rslt0)
      "less_than_edgs_bet (abstract_real_map (potential_lookup (foldl outer_f \<pi> vs)))
           (E \<union> ?new_es)" (is ?rslt1)
    "fst `  (E \<union> ?new_es) = dom (potential_lookup (foldl outer_f \<pi> vs))" (is ?rslt2)
    if "less_than_edgs_bet (abstract_real_map (potential_lookup \<pi>)) E" 
      "potential_invar \<pi>" 
      "fst ` E = dom (potential_lookup \<pi>)"
    for \<pi> E 
     proof-
       define vvs where "vvs = rev vs"
       have vvs_in_vs: "set vvs \<subseteq> set vs"
         by(auto simp add: vvs_def)
       have "?rslt0 \<and> ?rslt1 \<and> ?rslt2"
         using that
         unfolding foldl_conv_foldr vvs_def[symmetric] set_rev[of vs, symmetric]
         using vvs_in_vs
       proof(induction vvs)
         case Nil
         then show ?case by auto
       next
         case (Cons u vvs)
         hence vvs_in_vs: "set vvs \<subseteq> set vs" by auto
         note IH_applied_all = Cons(1)[OF Cons(2,3,4) vvs_in_vs]
         note IH_applied = conjunct1[OF IH_applied_all]
                           conjunct1[OF conjunct2[OF IH_applied_all]]
                           conjunct2[OF conjunct2[OF IH_applied_all]]
         show ?case
           apply(subst foldr_Cons o_apply)+ 
           apply(subst outer_f_def, subst (3) outer_f_def, subst (5) outer_f_def)
         proof(cases "neighbs u", goal_cases)
           case 1
           note one = this
           show ?case 
             apply(subst 1 option.case(1))+
           proof(rule conjI[OF IH_applied(1)], rule, goal_cases)
             case 1
             show ?case
               apply(rule rev_iffD2[OF IH_applied(2)])
               apply(rule arg_cong[of "_ ::_ set"])
               using one by auto
           next
             case 2
             show ?case
               using one
               by(subst IH_applied(3)[symmetric]) auto
           qed
         next
           case (2 N)
           note two = this
           have vset_invar_N:"vset_invar N"
             using "2" neighbs Cons.prems(4) by auto
           show ?case 
             apply(subst 2 option.cases(2))+
             proof(rule, goal_cases)
             case 1
             show ?case
               apply(rule rev_iffD2[OF inner_fold_invar_pres[OF IH_applied(1)]])
               by auto
           next
             case 2
             show ?case
             proof(rule, goal_cases)
               case 1
               show ?case
                 apply(rule rev_iffD2[OF inner_fold_props_pres(1)[OF 
                           IH_applied(2,1,3), of u "to_list (the (neighbs u))"]])
                 apply(subst two option.sel)+
                 apply(rule arg_cong[of "_ ::_ set"])
                 using two vset(2)[OF  vset_invar_N] 
                 by auto
             next 
               case 2
               show ?case
                 apply(subst inner_fold_props_pres(2)[OF IH_applied(2,1,3),
 of u "to_list (the (neighbs u))", symmetric, simplified  
        two  option.sel vset(2)[OF vset_invar_N]])
                 using two vset(2)[OF  vset_invar_N] 
                 by auto
             qed
           qed
         qed
       qed
    
       thus ?rslt0 ?rslt1 ?rslt2 
         by auto
     qed
     note final_props =  outer_iteration_pres[OF less_than_edgs_bet_empty potential(1),
                simplified potential(2), simplified]
     have init_pot_is: "init_potential = foldl outer_f empty_potential vs"
       by(subst init_potential_def outer_f_def inner_f_def)+ simp
     show  "potential_invar init_potential"
   "\<And> u v N. \<lbrakk>u \<in> set vs; neighbs u = Some N; v \<in> vset_to_set N\<rbrakk> \<Longrightarrow>
            abstract_real_map (potential_lookup init_potential) u \<le> edge_costs u v"
      "dom (potential_lookup init_potential) = 
      { v | v x. v \<in> set vs \<and> neighbs v \<noteq> None \<and>
           vset_to_set (the (neighbs v)) \<noteq> {}}"
       using final_props(1,2)
       by(force simp add: init_pot_is final_props(3)[symmetric]
                          less_than_edgs_bet_def)+
   qed
end

hide_const left

definition "default_neighb D neighbs = (\<lambda> v. (case neighbs v of None \<Rightarrow> D
                                                | Some N \<Rightarrow> N))"
thm hungarian_loop_spec.hungarian_def
global_interpretation hungarian_top_loop:
hungarian_loop_spec
where path_search = "\<lambda> M P. search_path left (buddy_lookup M)
                    (edge_costs::('a::linorder) \<Rightarrow> 'a \<Rightarrow> real) 
                     (default_neighb vset_empty right_neighbs) parent_lookup
                     parent_upd parent_empty  origin_upd origin_lookup origin_empty P 
                     potential_lookup potential_upd missed_lookup  missed_empty missed_upd 
                     ben_upd ben_lookup ben_empty to_list vset_insert vset_empty"
and edge_costs = "(\<lambda> e. edge_costs (pick_one e) (pick_another e))"
and init_potential = "init_potential potential_lookup potential_upd
                          empty_potential edge_costs to_list right_neighbs (to_list left)"
and potential_abstract = "(\<lambda> \<pi> v. abstract_real_map (potential_lookup \<pi>) v)"
and potential_invar = potential_invar
and empty_matching = empty_buddies
and matching_invar = "matching_invar buddy_lookup buddy_invar G"
and augment = "matching_augment_impl buddy_upd"
and matching_abstract = "matching_abstract buddy_lookup"
and card_L = "length (to_list left)"
and card_R = "length (to_list right)"
and G = G
for 
     (*the graph*) G left right buddy edge_costs right_neighbs
     (*the matching*) empty_buddies buddy_lookup buddy_upd buddy_invar
     (*the forest*) parent_lookup  parent_upd parent_empty
                    origin_upd origin_lookup origin_empty 
     (*the potential*) initial_pot potential_lookup potential_upd empty_potential
                       potential_invar
     (*missed change in potential*) missed_lookup missed_empty missed_upd
     (*best even neighbour map*) ben_upd ben_lookup ben_empty
     (*sets of vertices*) vset_isin to_list vset_to_set vset_insert vset_empty
   defines hungarian = hungarian_top_loop.hungarian
   and initial_state =hungarian_top_loop.initial_state
   and hungarianl_loop_impl = hungarian_top_loop.hungarian_loop_impl
   
  done
(*
thm hungarian_def

definition "edges_and_costs = [(0::nat, 1::nat, 1::real), (0,3, -10), 
(0,5, 2/3), (0,7, 1/87), (2,5, -12), (2,9, 100), (2,1, 2.5), (4,5, 2+1/7), 
(4,3, -1.3), (4,7, 2.4),
   (6,1, 1.8+1/9), (6,9, 2000000000), (8, 9, 10000), (8,1, 6.2), (0, 9, -100),
 (2, 7, -100), (2,3,-40), (2,9,-100), (4,9, -100)]"

definition "edges = zip (map fst edges_and_costs) (map (fst o snd) edges_and_costs)"

definition "c_list = zip (zip (map fst edges_and_costs)  (map (fst o snd) edges_and_costs)) 
                   (map (snd o snd) edges_and_costs)"

definition "c_impl = foldr (\<lambda> xy tree.
              update (prod.swap (prod.fst xy)) (prod.snd xy)
              ( update (prod.fst xy) (prod.snd xy) tree))
              c_list Leaf"

definition "weights = (\<lambda> u v. abstract_real_map (lookup c_impl) (u, v))"

definition "bipartite_test = filter odd (map fst edges) @ filter even (map snd edges)"
value bipartite_test

definition "G = a_graph edges"
hide_const right

definition "left = foldr (\<lambda> x tree. RBT.insert x tree) (map fst edges_and_costs) Leaf"
definition "right = foldr (\<lambda> x tree. RBT.insert x tree) (map (fst o snd) edges_and_costs) Leaf"
thm hungarian_def

definition "final_matching = hungarian left right weights (lookup G) empty lookup update lookup update empty
update lookup empty lookup (\<lambda> T n v. update n v T) empty lookup empty 
 (\<lambda> T n v. update n v T) (\<lambda> T n v. update n v T) lookup empty inorder RBT.insert empty"

value "final_matching"

value "inorder (the final_matching)"
*)

locale hungarian_method_together_correct = 
  fixes G::"('v::linorder) set set"
    and edge_costs::"'v \<Rightarrow> 'v \<Rightarrow> real"
    and left::'vset
    and right::'vset
    and right_neighbs::"'v \<Rightarrow> 'vset option"

   and potential_upd::"'potential \<Rightarrow> 'v \<Rightarrow> real \<Rightarrow> 'potential"
   and potential_lookup::"'potential \<Rightarrow> 'v \<Rightarrow> real option"
   and potential_invar::"'potential \<Rightarrow> bool"
   and potential_empty::"'potential"

   and ben_empty::'ben
   and ben_lookup::"'ben \<Rightarrow> 'v \<Rightarrow> 'v option"
   and ben_upd::"'ben \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'ben"
   and ben_invar::"'ben \<Rightarrow> bool"

   and missed_empty::'miss
   and missed_lookup::"'miss \<Rightarrow> 'v \<Rightarrow> real option"
   and missed_upd::"'miss \<Rightarrow> 'v \<Rightarrow> real \<Rightarrow> 'miss"
   and missed_invar::"'miss \<Rightarrow> bool"

   and to_list::"'vset \<Rightarrow> 'v list"
   and vset_to_set::"'vset \<Rightarrow> 'v set"
   and vset_isin::"'v \<Rightarrow> 'vset \<Rightarrow> bool"
   and vset_empty::"'vset"
   and vset_insert::"'v \<Rightarrow> 'vset \<Rightarrow> 'vset"
   and vset_invar::"'vset \<Rightarrow> bool"

   and parent_empty::'parent
    and   parent_upd::"'v\<Rightarrow>'v\<Rightarrow>'parent\<Rightarrow>'parent"
    and   parent_lookup::"'parent \<Rightarrow> 'v \<Rightarrow> 'v option"
    and   parent_delete::"'v \<Rightarrow> 'parent \<Rightarrow>'parent"
    and   parent_invar::"'parent \<Rightarrow> bool"

and   origin_empty::'origin
and   origin_upd::"'v\<Rightarrow>'v\<Rightarrow>'origin\<Rightarrow>'origin"
and   origin_lookup::"'origin \<Rightarrow> 'v \<Rightarrow> 'v option"
and   origin_invar::"'origin \<Rightarrow> bool"


and buddy_empty::'buddy
   and  buddy_upd::"'v \<Rightarrow> 'v \<Rightarrow> 'buddy \<Rightarrow> 'buddy"
   and  buddy_lookup::"'buddy \<Rightarrow> 'v \<Rightarrow> 'v option"
   and  buddy_invar::"'buddy \<Rightarrow> bool"

assumes G: "bipartite G (vset_to_set left) (vset_to_set right)"
           "vset_invar left" "vset_invar right"
           "(vset_to_set left) \<union> (vset_to_set right) \<subseteq> Vs G"

           "\<And> v N. \<lbrakk>v \<in> vset_to_set left;right_neighbs v= Some N\<rbrakk> 
                 \<Longrightarrow> vset_invar N"
           "\<And> v .  v \<in> vset_to_set left 
                     \<Longrightarrow> \<exists> N .right_neighbs v= Some N \<and>
                            vset_to_set N = {u | u. {v, u} \<in> G}"
           "\<And> u v. {u, v} \<in> G \<Longrightarrow> edge_costs u v = edge_costs v u"
and potential:
 "potential_invar potential_empty"
 "potential_lookup potential_empty = (\<lambda> v. None)"
 "\<And> pot x s. potential_invar pot \<Longrightarrow> potential_invar (potential_upd pot x s)"
 "\<And> pot x s. potential_invar pot \<Longrightarrow> potential_lookup (potential_upd pot x s) =
                (potential_lookup pot)(x \<mapsto> s)"
and best_even_neighbour:
 "ben_invar ben_empty"
  "\<And> ben x s. ben_invar ben \<Longrightarrow> ben_invar (ben_upd ben x s)"
  "\<And> ben x s. ben_invar ben \<Longrightarrow> ben_lookup (ben_upd ben x s) =
                (ben_lookup ben)(x \<mapsto> s)"
  "\<And> x. ben_lookup ben_empty x = None"
and vset:
 "vset_invar vset_empty" "vset_to_set vset_empty = {}"
 "\<And> V v. vset_invar V \<Longrightarrow> vset_invar (vset_insert v V)"
 "\<And> V v. vset_invar V \<Longrightarrow> vset_to_set (vset_insert v V) = insert v (vset_to_set V)"
 "\<And> V v. vset_invar V \<Longrightarrow> vset_isin v V \<longleftrightarrow> v \<in> vset_to_set V"
 "\<And> V vs. \<lbrakk>vset_invar V; to_list V = vs\<rbrakk> \<Longrightarrow> distinct vs"
 "\<And> V vs. \<lbrakk>vset_invar V; to_list V = vs\<rbrakk> \<Longrightarrow> set vs = vset_to_set V"
and missed:
 "missed_invar missed_empty" "\<And> x. missed_lookup missed_empty x= None"
  "\<And> missed x s. missed_invar missed \<Longrightarrow> missed_invar (missed_upd missed x s)"
  "\<And> missed x s. missed_invar missed \<Longrightarrow> missed_lookup (missed_upd missed x s) =
                (missed_lookup missed)(x \<mapsto> s)"
  "\<And> x. missed_lookup missed_empty x = None"
    and parent:
    "parent_invar parent_empty"
    "parent_lookup parent_empty = (\<lambda> x. None)"
    "\<And> par x s. parent_invar par \<Longrightarrow> parent_invar (parent_upd x s par)"
    "\<And> par x s. parent_invar par \<Longrightarrow> parent_lookup (parent_upd x s par) =
                (parent_lookup par)(x \<mapsto> s)"
    and origin:
    "origin_invar origin_empty"
    "origin_lookup origin_empty = (\<lambda> x. None)"
    "\<And> par x s. origin_invar par \<Longrightarrow> origin_invar (origin_upd x s par)"
    "\<And> par x s. origin_invar par \<Longrightarrow> origin_lookup (origin_upd x s par) =
                (origin_lookup par)(x \<mapsto> s)"
and buddies:
 "buddy_invar buddy_empty"
  "\<And> buddy u v. buddy_invar buddy \<Longrightarrow> buddy_invar (buddy_upd  u v buddy)"
  "\<And> buddy u v. buddy_invar buddy \<Longrightarrow> buddy_lookup (buddy_upd  u v buddy) =
                (buddy_lookup buddy)(u \<mapsto> v)"
  "\<And> u. buddy_lookup buddy_empty u = None"
begin

interpretation fmnlp: forest_manipulation
  where vset_flatten = to_list
  using vset(1-5) vset (6-7)[OF _ refl]
  by(auto intro!: forest_manipulation.intro parent origin)

abbreviation "forest_invar == fmnlp.forest_invar"
abbreviation "L \<equiv> vset_to_set left"
abbreviation "R \<equiv> vset_to_set right"
abbreviation "init_potential_here \<equiv> init_potential potential_lookup potential_upd
                          potential_empty edge_costs to_list right_neighbs (to_list left)"

interpretation build_init_pot_thms: build_init_potential
  where potential_lookup = potential_lookup 
and potential_upd = potential_upd
and empty_potential = potential_empty
and edge_costs = edge_costs
and to_list = to_list 
and neighbs =  right_neighbs
and vs = "to_list left"
  using vset(7)[OF G(2) refl]  G(2,5)
  by(auto intro!: build_init_potential.intro vset(6)[OF G(2) refl]
        simp add: vset potential)

lemma init_potential_def': 
"build_init_pot_thms.init_potential = init_potential_here"
  by(simp add: build_init_potential_spec.init_potential_def
               init_potential_def )

lemmas init_potential_props=
  build_init_pot_thms.init_potential_props[unfolded init_potential_def']

interpretation  satisfied_simple:
 alternating_forest_spec evens odds "get_path parent_lookup" "abstract_forest parent_lookup"
     forest_invar roots vset_invar vset_to_set
  unfolding abstract_forest_def get_path_def
  apply(intro alternating_forest_spec.intro 
      fmnlp.simple_invariant_consequences)
  using fmnlp.complex_invariant_consequences(1,2) 
  by(auto simp add: fmnlp.get_path_correct(1,2,3,4,5))

abbreviation "\<ww> \<equiv> (\<lambda> e. edge_costs (pick_one e) (pick_another e))"

lemma w_is_edge_costs: 
  assumes"{u, v} \<in> G" 
  shows  "\<ww> {u, v} = edge_costs u v"
proof-
  have "u \<noteq> v"
    by(rule bipartite_edgeE[OF assms G(1)])
      (auto simp add: doubleton_eq_iff)
  thus ?thesis
    using  pick_one_and_another_props(3)[of "{u, v}", OF exI[of _ u]]
    by(auto  simp add: doubleton_eq_iff  G(7)[OF assms])
qed

lemma feasible_init:
"feasible_min_perfect_dual G \<ww>
     (abstract_real_map (potential_lookup init_potential_here))"
proof(rule feasible_min_perfect_dualI, goal_cases)
  case (1 e u v)
  then obtain u' v' where u'v':  "e = {u', v'}" "u' \<in> L" "v' \<in> R" 
    using G(1)
    by (auto elim!: bipartite_edgeE)
  hence "v' \<notin> L" "u' \<notin> R" "u' \<noteq> v'" 
    using G(4) bipartite_vertex(2)[OF _ G(1)] by auto
  hence pot_v_0:"abstract_real_map (potential_lookup init_potential_here) v' = 0"
    using init_potential_props(3)
    by(auto intro!: abstract_real_map_outside_dom dest: domI
          simp add: build_init_pot_thms.vset(2)[OF G(2)])
   have f_of_uv:"(f::_ \<Rightarrow> real) u +  f v = f u' + f v'" for f
    using 1(2) u'v'(1)
    by(auto simp add: doubleton_eq_iff)
  obtain U where neighbsU: "right_neighbs u' = Some U" 
    using u'v'  G(6) by auto
  hence v'_in_U: "v' \<in> vset_to_set U"
    using "1"(1) G(6) u'v'(1,2) by force
  show ?case 
    using 1(1)
    by(auto intro!: feasible_min_perfect_dualI v'_in_U
                       init_potential_props(2) neighbsU
          simp add: u'v' w_is_edge_costs f_of_uv pot_v_0 vset(7)[OF G(2) refl])
qed

interpretation fe_spec: 
     alternating_forest_ordinary_extension_spec vset_invar vset_to_set evens odds
     "get_path parent_lookup" "abstract_forest parent_lookup" forest_invar roots vset_empty
     "extend_forest_even_unclassified parent_upd vset_insert origin_upd origin_lookup"
     "empty_forest parent_empty vset_empty to_list origin_empty origin_upd"
  apply(intro alternating_forest_ordinary_extension_spec.intro
      satisfied_simple.alternating_forest_spec_axioms
      alternating_forest_ordinary_extension_spec_axioms.intro)
  by (simp_all add:  fmnlp.extension_main_preservation fmnlp.satisfied_simple_extension_precond_same
      fmnlp.extension_abstract_is fmnlp.extension_evens fmnlp.extension_odds fmnlp.extension_roots 
      fmnlp.empty_forest_correctess  extend_forest_even_unclassified_def 
      abstract_forest_def empty_forest_def)

interpretation matching_augmentation_thms:
  matching_augmentation buddy_empty buddy_upd buddy_lookup buddy_invar
  by(auto intro!: matching_augmentation.intro buddies)

lemmas augmentation_correct =
 matching_augmentation_thms.augmentation_correct
 [folded matching_invar_def matching_abstract_def matching_augment_impl_def]

lemmas matching_invarD = aug_a_matching.invar_matchingD
   [of buddy_lookup buddy_invar G,
    folded matching_invar_def matching_abstract_def]

lemmas empty_matching_props =
matching_augmentation_thms.empty_matching_props
[folded matching_invar_def matching_abstract_def]

abbreviation "potential_invar' \<equiv> 
\<lambda> \<pi> . potential_invar \<pi> \<and> dom (potential_lookup \<pi>) \<subseteq> Vs G"

abbreviation "path_search_precond \<equiv>
    hungarian_loop_spec.path_search_precond
        (\<lambda>\<pi>. abstract_real_map (potential_lookup \<pi>)) potential_invar'
        (matching_invar buddy_lookup buddy_invar G)
        (matching_abstract buddy_lookup) \<ww> G"

abbreviation "search_path_here \<equiv>
   (\<lambda> M \<pi>. search_path left (buddy_lookup M) edge_costs
        (default_neighb vset_empty right_neighbs) parent_lookup parent_upd
        parent_empty origin_upd origin_lookup origin_empty \<pi> potential_lookup
        potential_upd missed_lookup missed_empty missed_upd ben_upd ben_lookup
        ben_empty to_list vset_insert vset_empty)"

abbreviation "symmetric_buddies \<equiv> 
matching_augmentation_spec.symmetric_buddies buddy_lookup"

abbreviation "good_search_result \<equiv>  
hungarian_top_loop.good_search_result potential_lookup potential_invar'
        buddy_lookup edge_costs G"

interpretation hungarian_top_loop:
hungarian_loop
where path_search = "\<lambda> m p. search_path left (buddy_lookup m)
                      edge_costs
                     (default_neighb vset_empty right_neighbs) parent_lookup
                     parent_upd parent_empty  origin_upd origin_lookup origin_empty p 
                     potential_lookup potential_upd missed_lookup  missed_empty missed_upd 
                     ben_upd ben_lookup ben_empty to_list vset_insert vset_empty"
and edge_costs = \<ww>
and init_potential = "init_potential_here"
and potential_abstract = "(\<lambda> \<pi> v. abstract_real_map (potential_lookup \<pi>) v)"
and potential_invar = potential_invar'
and empty_matching = buddy_empty
and matching_invar = "matching_invar buddy_lookup buddy_invar G"
and augment = "matching_augment_impl buddy_upd"
and matching_abstract = "matching_abstract buddy_lookup"
and card_L = "length (to_list left)"
and card_R = "length (to_list right)"
and G = G
and L = L
and R = R
proof(rule hungarian_loop.intro, goal_cases)
  case 1
  then show ?case 
    using G(1) by simp
next
  case 2
  then show ?case 
    using vset(6,7)[OF G(2) refl] distinct_card by fastforce
next
  case 3
  then show ?case 
    using vset(6,7)[OF G(3) refl] distinct_card by fastforce
next
  case 4
  then show ?case 
    using vset(7)[OF G(2) refl, symmetric] by simp
next
  case 5
  then show ?case 
    using vset(7)[OF G(3) refl, symmetric] by simp
next
  case 6
  then show ?case 
    using G(4) by simp
next
  case 7
  then show ?case
    using init_potential_props(1,3) G(4) build_init_pot_thms.vset(2)[OF G(2)] 
    by auto
next
  case 8
  then show ?case 
    using feasible_init by simp
next
  case (9 M)
  then show ?case 
    using matching_invarD by simp
next
  case 10
  then show ?case 
    using empty_matching_props by simp
next
  case 11
  then show ?case 
    using empty_matching_props by simp
next
  case (12 M p)
  then show ?case 
    using augmentation_correct by simp
next
  case (13 M p)
  then show ?case 
    using augmentation_correct by simp
next
  fix M \<pi> B \<pi>'
  assume asm: "path_search_precond M \<pi>"
  note path_search_precondD = hungarian_loop_spec.path_search_precondD[OF asm]
  note symmetric_buddiesD = aug_a_matching.symmetric_buddiesD[of buddy_lookup]
  have \<M>_is: "pd_path_search_spec.\<M> (buddy_lookup M) =
             matching_abstract buddy_lookup M" 
    by(force simp add: matching_abstract_def pd_path_search_spec.\<M>_def
              matching_augmentation_spec.\<M>_def doubleton_eq_iff) 

  interpret pd_path_search: primal_dual_path_search
  (*the graph*)
  where G = G
   and left = left
   and right = right
   and buddy = "buddy_lookup M"
   and edge_costs = edge_costs
   and right_neighbs = "default_neighb vset_empty right_neighbs"
  (*the forest*)
   and evens = evens
   and odds = odds
   and abstract_forest = "abstract_forest parent_lookup"
   and get_path = "get_path parent_lookup"
   and extend_forest_even_unclassified = 
     "extend_forest_even_unclassified parent_upd vset_insert 
          origin_upd origin_lookup" 
   and empty_forest = 
      "empty_forest parent_empty vset_empty to_list origin_empty origin_upd"
   and roots = roots
   and forest_invar = forest_invar
  (*the heap*)
   and heap_insert = queue_insert
   and heap_decrease_key = queue_decrease_key
   and heap_empty = queue_empty
   and heap_extract_min = queue_extract_min
   and heap_invar = queue_invar
   and heap_abstract = queue_abstract
  (*the potential*)
   and initial_pot = \<pi>
   and potential_lookup = potential_lookup
   and potential_upd = potential_upd
  (*missed change in potential*)
   and missed_lookup = missed_lookup
   and missed_empty = missed_empty
   and missed_upd = missed_upd
  (*best even neighbour map*)
   and ben_upd = ben_upd
   and ben_lookup = ben_lookup
   and ben_empty = ben_empty
  (*sets of vertices*)
   and vset_isin= vset_isin
   and to_list = to_list
   and vset_to_set = vset_to_set
   and vset_insert = vset_insert
   and vset_empty = vset_empty
proof(rule primal_dual_path_search.intro, goal_cases)
  case 1
  thus ?case
    using fe_spec.alternating_forest_ordinary_extension_spec_axioms
    by simp
next
  case 2
  thus ?case
    using key_value_queue_spec_satisfied.key_value_queue_axioms by simp
next
  case 3
  have help1:
     "v \<in> L \<Longrightarrow> vset_invar (default_neighb vset_empty right_neighbs v)" for v
    by(auto simp add: default_neighb_def split: option.split
               intro: vset G)
  have help2: "v \<in> L \<Longrightarrow>
         vset_to_set (default_neighb vset_empty right_neighbs v) = 
          {u | u. {v, u} \<in> G}" for v
    using G(6)
    by(fastforce simp add: default_neighb_def vset(2) split: option.split)
  have help3: "{u, v} \<in> G \<Longrightarrow>
           abstract_real_map (potential_lookup \<pi>) u +
           abstract_real_map (potential_lookup \<pi>) v
           \<le> edge_costs u v" for u v
    using feasible_min_perfect_dualD path_search_precondD(5) w_is_edge_costs
    by fastforce
  have help4: "{u, v} \<in> matching_abstract buddy_lookup M \<Longrightarrow>
           abstract_real_map (potential_lookup \<pi>) u +
           abstract_real_map (potential_lookup \<pi>) v =
           edge_costs u v" for u v
    by(auto dest!: set_mp[OF path_search_precondD(4)]
         simp add: tight_subgraph_def doubleton_eq_iff
                   w_is_edge_costs \<M>_is G(7))
  have help5: "dom (potential_lookup \<pi>) \<subseteq> L \<union> R"
    using path_search_precondD(2)  G(1) bipartite_vs_subset by blast
  note help6 = symmetric_buddiesD[OF 
      matching_invarD(2)[OF path_search_precondD(1)]]
  show ?case
    apply(rule primal_dual_path_search_axioms.intro G(1,2,3,7) help1 help2
               help3 | assumption)+
    by(unfold \<M>_is help6| intro help4 conjunct1[OF path_search_precondD(2)]
             potential best_even_neighbour vset missed help5
             path_search_precondD(3)[simplified aug_a_matching.\<M>_def]
        | assumption)+
qed
  have search_path_is:
    "pd_path_search.search_path = search_path_here M \<pi>"
    by (simp add: search_path_def)
  note search_path_correct = pd_path_search.search_path_correct[unfolded search_path_is]
 
  show "search_path_here M \<pi> = Dual_Unbounded \<Longrightarrow>
       \<exists>\<pi>'. feasible_min_perfect_dual G \<ww> \<pi>' \<and> B < sum \<pi>' (L \<union> R)"
  proof(goal_cases)
    case 1
    obtain \<pi>' where pi':
           "\<And> u v. {u, v} \<in> G \<Longrightarrow> \<pi>' u + \<pi>' v \<le> \<w> u v"
           "B+1 \<le> sum \<pi>' (pd_path_search.L \<union> pd_path_search.R)"
      using search_path_correct(2)[OF 1, of "B+1"] by auto
    show ?case
      using pi'(2)
      by(auto intro!: exI[of _ \<pi>'] feasible_min_perfect_dualI pi'(1)
            simp add: w_is_edge_costs)
  qed

  show "search_path_here M \<pi> = Lefts_Matched \<Longrightarrow>
           L \<subseteq> Vs (matching_abstract buddy_lookup M)"
    using search_path_correct(1) by(simp add: \<M>_is)

  show "search_path_here M \<pi> = Next_Iteration p \<pi>'
         \<Longrightarrow> good_search_result M \<pi>' p" for p
  proof(goal_cases)
    case 1
    note search_path_in_this_case =
            search_path_correct(3-)[OF 1, unfolded \<M>_is]
    show ?case
    proof(rule hungarian_top_loop.good_search_resultI, goal_cases)
      case 1
      then show ?case 
        using search_path_in_this_case(5,6) G(4) by blast
    next
      case 2
      show ?case
      proof(rule, goal_cases)
        case (1 e)
        then obtain u v where uv: "e = {u, v}" "{u, v} \<in> G"
          using  G(1) bipartite_edgeE[OF _  G(1)] path_search_precondD(3)
          by blast
        show ?case
          using  search_path_in_this_case(2)[OF 1[unfolded uv(1)]]
          by(auto simp add: tight_subgraph_def uv w_is_edge_costs
                    intro!: exI[of "\<lambda> u. \<exists> v. _ u v" u] exI[of "\<lambda> u. _ u \<and> _ u" v])
      qed
    next
      case 3
      show ?case 
      proof(rule feasible_min_perfect_dualI, goal_cases)
        case (1 e u v)
        then show ?case 
          using search_path_in_this_case(1)
          by(auto simp add: w_is_edge_costs)
      qed
    next
      case 4
      show ?case 
      proof(rule, goal_cases)
        case (1 e)
        hence "e \<in> G" 
          using search_path_in_this_case(4)
          by (auto dest: path_edges_subset)
        then obtain u v where uv: "e = {u, v}" "{u, v} \<in> G" "u \<noteq> v"
          using  G(1) bipartite_edgeE[OF _  G(1), of e] by blast
        show ?case
          using  search_path_in_this_case(3)[OF 1[unfolded uv(1)]]
          by(auto simp add: tight_subgraph_def uv w_is_edge_costs
                    intro!: exI[of "\<lambda> u. \<exists> v. _ u v" u] exI[of "\<lambda> u. _ u \<and> _ u" v])
      qed
    next
      case 5
      then show ?case 
        using search_path_in_this_case(4) by simp
    qed
  qed
qed

lemmas hungarian_correctness = hungarian_top_loop.hungarian_correctness
  [folded hungarian_def]
end

end