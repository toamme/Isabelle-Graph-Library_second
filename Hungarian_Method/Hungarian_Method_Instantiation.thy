theory Hungarian_Method_Instantiation
  imports  Primal_Dual_Path_Search Alternating_Forest_Executable Ordered_Map_Heap
Naive_Primal_Dual "HOL-Library.Rewrite"
Matching_Augmentation_Executable
Hungarian_Method_Top_Loop
begin

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
lemmas [code] = pd_path_search_spec.search_path_def[folded search_path_def]
                pd_path_search_spec.initial_state_def[folded path_search_initial_state_def]
                
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
and neighbs: "\<And> v N. neighbs v = Some N \<Longrightarrow> vset_invar N"
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
       have "?rslt0 \<and> ?rslt1 \<and> ?rslt2"
         using that
         unfolding foldl_conv_foldr vvs_def[symmetric] set_rev[of vs, symmetric]
       proof(induction vvs)
         case Nil
         then show ?case by auto
       next
         case (Cons u vvs)
         note IH_applied_all = Cons(1)[OF Cons(2,3,4)]
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
             using "2" neighbs by auto
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

thm matching_augment_impl_def
global_interpretation hungarian:
hungarian_loop_spec
where path_search = "\<lambda> M P. search_path left (\<lambda> M. buddy_lookup M)
                    (edge_costs::('a::linorder) \<Rightarrow> 'a \<Rightarrow> real) right_neighbs parent_lookup
                     parent_upd parent_empty  origin_upd origin_lookup origin_empty P 
                     potential_lookup potential_upd missed_lookup  missed_empty missed_upd 
                     ben_upd ben_lookup ben_empty to_list vset_insert vset_empty"
and edge_costs = "(\<lambda> e. edge_costs (pick_one e) (pick_another e))"
and init_potential = "init_potential potential_lookup potential_upd
                          empty_potential edge_costs to_list neighbs vs"
and potential_abstract = "(\<lambda> \<pi> v. abstract_real_map (potential_lookup \<pi>) v)"
and potential_invar = potential_invar
and empty_matching = empty_buddies
and matching_invar = buddy_invar
and augment = "matching_augment_impl buddy_upd"
and matching_abstract = "matching_abstract buddy_lookup"
for 
     (*the graph*) G left right buddy edge_costs right_neighbs
     (*the forest*) parent_lookup  parent_upd parent_empty
                    origin_upd origin_lookup origin_empty 
     (*the potential*) initial_pot potential_lookup potential_upd
     (*missed change in potential*) missed_lookup missed_empty missed_upd
     (*best even neighbour map*) ben_upd ben_lookup ben_empty
     (*sets of vertices*) vset_isin to_list vset_to_set vset_insert vset_empty
  done

end