theory Primal_Dual_Path_Search
  imports Berge_Lemma.Berge Flow_Theory.Arith_Lemmas "HOL-Data_Structures.Set_Specs"
"HOL-Data_Structures.Map_Specs"
RANKING.More_Graph
begin
(*TODO MOVE*)
lemma pair_eq_fst_snd_eq:
      "(a, b) = c \<Longrightarrow> a = fst c"
      "(a, b) = c \<Longrightarrow> b = snd c"
  by auto

lemma walk_reflexive_cong: "\<lbrakk>u \<in> Vs G; u = u'; u' = u''\<rbrakk> \<Longrightarrow> walk_betw G u [u'] u''"
  using walk_reflexive by simp

lemma bipartite_even_and_odd_walk:
  assumes "bipartite G X Y" "x \<in> X"
          "walk_betw G x p y"
    shows "odd (length p) \<Longrightarrow> y \<in> X"
          "even (length p) \<Longrightarrow> y \<in> Y"
proof-
  have "(odd (length p) \<longrightarrow> y \<in> X) \<and> (even (length p) \<longrightarrow> y \<in> Y)"
    using assms(3)
  proof(induction p arbitrary: y rule: rev_induct)
    case Nil
    then show ?case by(simp add: walk_betw_def)
  next
    case (snoc x' xs)
    note IH = this
    show ?case 
    proof(cases "even (length (xs@[x]))")
      case True
      hence odd: "odd (length xs)" by simp
      have "\<exists> y'. walk_betw G x xs y' \<and> {y', y} \<in> G"
        using odd snoc(2) path_2[of G y] path_suff[of G _ "[_, y]"] snoc.prems[simplified walk_betw_def] 
        by(cases xs rule: rev_cases)
          (auto intro!: exI[of _ "last xs"] walk_reflexive_cong simp add: walk_pref)
      then obtain y' where y':"walk_betw G x xs y'" "{y', y} \<in> G"
        by auto
      moreover hence "y' \<in> X" 
        using snoc(1) odd by simp
      ultimately have "y \<in> Y"
        using assms(1) bipartite_edgeD(1) by fastforce
      thus ?thesis
        using True by fastforce
    next
      case False
      show ?thesis
      proof(cases xs rule: rev_cases)
        case Nil
        hence "y = x" 
          using IH(2) snoc.prems[simplified walk_betw_def]  
          by auto
        then show ?thesis 
          by (simp add: assms(2) local.Nil)
      next
        case (snoc list a)
      hence even: "even (length xs)"using False  by simp
      have "\<exists> y'. (walk_betw G x xs y' \<and> {y', y} \<in> G)"
        using IH(2)  path_suff[of G _ "[_, y]"] 
             snoc.prems[simplified walk_betw_def] 
        by(auto intro!: exI[of _ a] simp add: snoc walk_pref)
      then obtain y' where y':"walk_betw G x xs y'" "{y', y} \<in> G"
        by auto
      moreover hence "y' \<in> Y" 
        using IH(1) even by simp
      ultimately have "y \<in> X"
        using assms(1) bipartite_edgeD(2) by fastforce
      thus ?thesis
        using False by fastforce
    qed
  qed
qed
  thus  "odd (length p) \<Longrightarrow> y \<in> X" "even (length p) \<Longrightarrow> y \<in> Y" 
    by auto
qed

lemma finite_G_finite_f_of_edge_verts:
"finite G \<Longrightarrow> finite {f x y | x y. {x, y} \<in> G}"
proof(induction G rule: finite_induct)
  case (insert e F)
  show ?case 
  proof(cases "\<exists> x y. e = {x, y}")
    case True
    then obtain x y where "e = {x, y}" by auto
    hence "{f x y | x y. {x, y} \<in> insert e F} = 
           {f x y | x y. {x, y} \<in> F} \<union> {f x y, f y x}" 
      by (auto simp add: doubleton_eq_iff)
    then show ?thesis 
      using insert by simp
  next
    case False
  hence "{f x y | x y. {x, y} \<in> insert e F} = 
           {f x y | x y. {x, y} \<in> F}" by auto
  then show ?thesis
    using insert by simp
  qed
qed simp
 

lemma add_non_min_element_Min:
"finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> y \<le> x \<Longrightarrow> y \<in> A\<Longrightarrow> B = insert x A \<Longrightarrow> Min B = Min A"
  by (metis Min.boundedE Min.insert_not_elem insert_absorb min_def order_antisym)
(*TOTO MOVE*)
lemma conj_intro:"\<lbrakk>P1;P2;P3;P4;P5;P6\<rbrakk> \<Longrightarrow> P1 \<and> P2 \<and> P3 \<and> P4 \<and> P5 \<and>P6" for P1 P2 P3 P4 P5 P6
      by simp
lemma conjD:"P1 \<and> P2 \<and> P3 \<and> P4 \<and> P5 \<and>P6 \<Longrightarrow> P1"
               "P1 \<and> P2 \<and> P3 \<and> P4 \<and> P5 \<and>P6 \<Longrightarrow> P2"
               "P1 \<and> P2 \<and> P3 \<and> P4 \<and> P5 \<and>P6 \<Longrightarrow> P3"
               "P1 \<and> P2 \<and> P3 \<and> P4 \<and> P5 \<and>P6 \<Longrightarrow> P4"
               "P1 \<and> P2 \<and> P3 \<and> P4 \<and> P5 \<and>P6  \<Longrightarrow> P5"
                "P1 \<and> P2 \<and> P3 \<and> P4 \<and> P5 \<and>P6  \<Longrightarrow> P6"for P1 P2 P3 P4 P5 P6
      by auto
(*
definition semibipartite :: "'a graph \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "semibipartite G X Y  = ( X \<inter> Y = {} \<and> (\<forall>e \<in> G. \<not> e \<subseteq> X))"
*)
record ('forest, 'ben, 'heap, 'miss, 'v) hungarian_search_state = 
forest::'forest
best_even_neighbour::'ben
heap::'heap
missed::'miss
acc::real
augpath::"('v list) option"
(*
datatype ('v, 'seen, 'forest) path_or_forest = Path "'v list"
  | Forest 'seen 'forest
*)
locale primal_dual_path_search_spec = 
  fixes G::"'v set set"
    and edge_costs::"'v \<Rightarrow> 'v \<Rightarrow> real"
    and left::'vset
    and right::'vset
    and in_G::"'v \<Rightarrow> 'v \<Rightarrow> bool"
    and right_neighbs::"'v \<Rightarrow> 'vset"

    and buddy::"'v \<Rightarrow> 'v option"

    and extend_forest_even_unclassified::
        "'forest \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'forest"
    and evens::"'forest \<Rightarrow> 'vset"
    and odds::"'forest \<Rightarrow> 'vset"
    and get_path::"'forest \<Rightarrow> 'v \<Rightarrow> 'v list"
    and abstract_forest::"'forest \<Rightarrow> 'v set set"
    and empty_forest::"'vset \<Rightarrow> 'forest"
    and forest_invar::"'v set set \<Rightarrow> 'forest \<Rightarrow> bool"
    and roots::"'forest \<Rightarrow> 'vset"

   and potential_upd::"'potential \<Rightarrow> 'v \<Rightarrow> real \<Rightarrow> 'potential"
   and potential_lookup::"'potential \<Rightarrow> 'v \<Rightarrow> real option"
   and potential_invar::"'potential \<Rightarrow> bool"
   and initial_pot::"'potential"

   and ben_empty::'ben
   and ben_lookup::"'ben \<Rightarrow> 'v \<Rightarrow> 'v option"
   and ben_upd::"'ben \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'ben"
   and ben_invar::"'ben \<Rightarrow> bool"

   and heap_empty::'heap
   and heap_extract_min::"'heap \<Rightarrow> ('heap \<times> 'v option)"
   and heap_decrease_key::"'heap \<Rightarrow> 'v \<Rightarrow> real \<Rightarrow> 'heap"
   and heap_insert::"'heap \<Rightarrow> 'v \<Rightarrow> real \<Rightarrow> 'heap"
   and heap_invar::"'heap \<Rightarrow> bool"
   and heap_abstract::"'heap \<Rightarrow> ('v \<times> real) set"

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
begin

notation edge_costs ("\<w>")

abbreviation "aevens state \<equiv> vset_to_set (evens (forest state))"
abbreviation "aodds state \<equiv> vset_to_set (odds (forest state))"
abbreviation "missed_at state v \<equiv> abstract_real_map (missed_lookup (missed state)) v"
abbreviation "\<pi> v \<equiv> abstract_real_map (potential_lookup initial_pot) v"
abbreviation "\<F> state \<equiv> abstract_forest (forest state)"
abbreviation "L  \<equiv> vset_to_set left"
abbreviation "R  \<equiv> vset_to_set right"

definition "\<M> = {{u, v} | u v. Some v = buddy u}"

definition "w\<^sub>\<pi> u v = edge_costs u v - \<pi> u - \<pi> v"

definition "invar_basic state= 
  (forest_invar \<M> (forest state) \<and>
    ben_invar (best_even_neighbour state) \<and>
    heap_invar (heap state) \<and>
    missed_invar (missed state) \<and>
    \<F> state \<subseteq> G \<and>
    dom (ben_lookup (best_even_neighbour state)) \<subseteq> Vs G \<and>
    dom (missed_lookup (missed state)) \<subseteq> Vs G \<and>
     fst ` heap_abstract (heap state) \<subseteq> Vs G \<and>
     aevens state \<subseteq> L \<and> aodds state \<subseteq> R)"

lemma invar_basicE:
"invar_basic state \<Longrightarrow>
(\<lbrakk>forest_invar \<M> (forest state);
  ben_invar (best_even_neighbour state);
  heap_invar (heap state);
  missed_invar (missed state);\<F> state \<subseteq> G;
  dom (ben_lookup (best_even_neighbour state)) \<subseteq> Vs G;
  dom (missed_lookup (missed state)) \<subseteq> Vs G;
  fst ` heap_abstract (heap state) \<subseteq> Vs G;
  aevens state \<subseteq> L; aodds state \<subseteq> R\<rbrakk> 
 \<Longrightarrow> P)
\<Longrightarrow> P"
and invar_basicI:
"\<lbrakk>forest_invar \<M> (forest state);
  ben_invar (best_even_neighbour state);
  heap_invar (heap state);
  missed_invar (missed state);\<F> state \<subseteq> G;
  dom (ben_lookup (best_even_neighbour state)) \<subseteq> Vs G;
  dom (missed_lookup (missed state)) \<subseteq> Vs G;
  fst ` heap_abstract (heap state) \<subseteq> Vs G;
  aevens state \<subseteq> L; aodds state \<subseteq> R\<rbrakk> 
 \<Longrightarrow> invar_basic state"
and invar_basicD:
"invar_basic state \<Longrightarrow> forest_invar \<M> (forest state)"
"invar_basic state \<Longrightarrow> ben_invar (best_even_neighbour state)"
"invar_basic state \<Longrightarrow> heap_invar (heap state)"
"invar_basic state \<Longrightarrow> missed_invar (missed state)"
"invar_basic state \<Longrightarrow> \<F> state \<subseteq> G"
"invar_basic state \<Longrightarrow> dom (ben_lookup (best_even_neighbour state)) \<subseteq> Vs G"
"invar_basic state \<Longrightarrow> dom (missed_lookup (missed state)) \<subseteq> Vs G"
"invar_basic state \<Longrightarrow> fst ` heap_abstract (heap state) \<subseteq> Vs G"
"invar_basic state \<Longrightarrow> aevens state \<subseteq> L"
"invar_basic state \<Longrightarrow> aodds state \<subseteq> R"
  by(auto simp add: invar_basic_def)

definition working_potential ("\<pi>\<^sup>*") where
"\<pi>\<^sup>* state v =
        (if vset_isin v (evens (forest state)) then 
           \<pi> v + acc state - missed_at state v
         else if vset_isin v (odds (forest state)) then 
           \<pi> v - acc state + missed_at state v
         else \<pi> v)"

definition "invar_feasible_potential state =
            (\<forall> u v. {u, v} \<in> G \<longrightarrow>
               edge_costs u v \<ge> \<pi>\<^sup>* state u + \<pi>\<^sup>* state v)"

lemma invar_feasible_potentialE:
"invar_feasible_potential state \<Longrightarrow>
((\<And> u v. {u, v} \<in> G \<Longrightarrow>
               edge_costs u v \<ge> \<pi>\<^sup>* state u + \<pi>\<^sup>* state v) \<Longrightarrow> P)
\<Longrightarrow> P"
and invar_feasible_potentialI:
"(\<And> u v. {u, v} \<in> G \<Longrightarrow>
               edge_costs u v \<ge> \<pi>\<^sup>* state u + \<pi>\<^sup>* state v) 
\<Longrightarrow> invar_feasible_potential state"
and invar_feasible_potentialD:
"\<lbrakk>invar_feasible_potential state;  {u, v} \<in> G\<rbrakk>
   \<Longrightarrow> edge_costs u v \<ge> \<pi>\<^sup>* state u + \<pi>\<^sup>* state v"
  by (auto simp add: invar_feasible_potential_def)

definition "invar_forest_tight state = 
            (\<forall> e \<in> \<F> state.
               \<exists> u v. edge_costs u v = \<pi>\<^sup>* state u + \<pi>\<^sup>* state v)"

lemma invar_forest_tightE:
"invar_forest_tight state \<Longrightarrow>
 ((\<And> e. e \<in> \<F> state \<Longrightarrow>
               \<exists> u v. edge_costs u v = \<pi>\<^sup>* state u + \<pi>\<^sup>* state v) \<Longrightarrow> P)
\<Longrightarrow> P"
and invar_forest_tightI:
"(\<And> e. e \<in> \<F> state \<Longrightarrow>
               \<exists> u v. edge_costs u v = \<pi>\<^sup>* state u + \<pi>\<^sup>* state v)
 \<Longrightarrow> invar_forest_tight state"
and invar_forest_tightD:
"\<lbrakk>invar_forest_tight state;  e \<in> \<F> state\<rbrakk> 
  \<Longrightarrow> \<exists> u v. edge_costs u v = \<pi>\<^sup>* state u + \<pi>\<^sup>* state v"
  by(auto simp add: invar_forest_tight_def)

definition "invar_matching_tight state = 
            (\<forall> u v. {u, v} \<in> \<M> \<longrightarrow>
               edge_costs u v = \<pi>\<^sup>* state u + \<pi>\<^sup>* state v)"

lemma invar_matching_tightE:
"invar_matching_tight state \<Longrightarrow>
((\<And> u v. {u, v} \<in> \<M> \<Longrightarrow>
               edge_costs u v = \<pi>\<^sup>* state u + \<pi>\<^sup>* state v) \<Longrightarrow> P)
\<Longrightarrow> P"
and invar_matching_tightI:
"(\<And> u v. {u, v} \<in> \<M> \<Longrightarrow>
               edge_costs u v = \<pi>\<^sup>* state u + \<pi>\<^sup>* state v)
 \<Longrightarrow> invar_matching_tight state"
and invar_matching_tightD:
"\<lbrakk>invar_matching_tight state; {u, v} \<in> \<M>\<rbrakk> \<Longrightarrow>
               edge_costs u v = \<pi>\<^sup>* state u + \<pi>\<^sup>* state v"
  by(auto simp add: invar_matching_tight_def)

definition "invar_best_even_neighbour_heap state =
  (heap_abstract (heap state) = 
   {(r, k) | r k. r \<in> Vs G - aevens state - aodds state \<and>
                  (\<exists> l. k = w\<^sub>\<pi> l r + missed_at state l \<and>
                       ben_lookup (best_even_neighbour state) r = Some l)})"

lemma invar_best_even_neighbour_heapE:
"invar_best_even_neighbour_heap state \<Longrightarrow>
(heap_abstract (heap state) = 
   {(r, k) | r k. r \<in> Vs G - aevens state - aodds state \<and>
                  (\<exists> l. k = w\<^sub>\<pi> l r + missed_at state l \<and>
                       ben_lookup (best_even_neighbour state) r = Some l)}
 \<Longrightarrow> P)
\<Longrightarrow>P"
and invar_best_even_neighbour_heapI:
"heap_abstract (heap state) = 
   {(r, k) | r k. r \<in> Vs G - aevens state - aodds state \<and>
                 (\<exists> l. k = w\<^sub>\<pi> l r + missed_at state l \<and>
                       ben_lookup (best_even_neighbour state) r = Some l)}
 \<Longrightarrow> invar_best_even_neighbour_heap state"
and invar_best_even_neighbour_heapD:
"invar_best_even_neighbour_heap state \<Longrightarrow>
heap_abstract (heap state) = 
   {(r, k) | r k. r \<in> Vs G - aevens state - aodds state \<and>
                  (\<exists> l. k = w\<^sub>\<pi> l r + missed_at state l \<and>
                       ben_lookup (best_even_neighbour state) r = Some l)}"
  by(auto simp add: invar_best_even_neighbour_heap_def)

definition "invar_best_even_neighbour_map state = 
     (\<forall> r \<in> Vs G - aevens state - aodds state.
           ((\<nexists> l. l \<in> aevens state \<and> {l, r} \<in> G) 
                  \<longrightarrow> ben_lookup (best_even_neighbour state) r = None)
          \<and>((\<exists> l. l \<in> aevens state \<and> {l, r} \<in> G)
                  \<longrightarrow> (\<exists> l. ben_lookup (best_even_neighbour state) r = Some l \<and>
                            {r, l} \<in> G  \<and>  l \<in> aevens state \<and>
                            w\<^sub>\<pi> l r + missed_at state l = 
                            Min {w\<^sub>\<pi> l r + missed_at state l | l. 
                                   l \<in> aevens state \<and> {l, r} \<in> G})))"

lemma invar_best_even_neighbour_mapE:
"invar_best_even_neighbour_map state \<Longrightarrow>
(\<lbrakk>(\<And> r. \<lbrakk> r \<in> Vs G; r \<notin>  aevens state; r \<notin> aodds state;
         \<nexists> l. l \<in> aevens state \<and> {l, r} \<in> G \<rbrakk> 
      \<Longrightarrow> ben_lookup (best_even_neighbour state) r = None);
  (\<And> r. \<lbrakk> r \<in> Vs G; r \<notin>  aevens state; r \<notin> aodds state;
         \<exists> l. l \<in> aevens state \<and> {l, r} \<in> G \<rbrakk> 
      \<Longrightarrow> (\<exists> l. ben_lookup (best_even_neighbour state) r = Some l \<and>
                            {r, l} \<in> G  \<and>  l \<in> aevens state \<and>
                            w\<^sub>\<pi> l r + missed_at state l = 
                            Min {w\<^sub>\<pi> l r + missed_at state l | l. 
                                   l \<in> aevens state \<and> {l, r} \<in> G}))\<rbrakk>
  \<Longrightarrow> P)
\<Longrightarrow> P"
and invar_best_even_neighbour_mapI:
"\<lbrakk>(\<And> r. \<lbrakk> r \<in> Vs G; r \<notin>  aevens state; r \<notin> aodds state;
         \<nexists> l. l \<in> aevens state \<and> {l, r} \<in> G \<rbrakk> 
      \<Longrightarrow> ben_lookup (best_even_neighbour state) r = None);
  (\<And> r. \<lbrakk> r \<in> Vs G; r \<notin>  aevens state; r \<notin> aodds state;
         \<exists> l. l \<in> aevens state \<and> {l, r} \<in> G \<rbrakk> 
      \<Longrightarrow> (\<exists> l. ben_lookup (best_even_neighbour state) r = Some l \<and>
                            {r, l} \<in> G  \<and>  l \<in> aevens state \<and>
                            w\<^sub>\<pi> l r + missed_at state l = 
                            Min {w\<^sub>\<pi> l r + missed_at state l | l. 
                                   l \<in> aevens state \<and> {l, r} \<in> G}))\<rbrakk>
  \<Longrightarrow> invar_best_even_neighbour_map state"
and invar_best_even_neighbour_mapD:
"\<lbrakk>invar_best_even_neighbour_map state ; r \<in> Vs G; 
  r \<notin>  aevens state; r \<notin> aodds state; \<nexists> l. l \<in> aevens state \<and> {l, r} \<in> G \<rbrakk> 
      \<Longrightarrow> ben_lookup (best_even_neighbour state) r = None"
"\<lbrakk>invar_best_even_neighbour_map state; r \<in> Vs G; 
  r \<notin>  aevens state; r \<notin> aodds state;\<exists> l. l \<in> aevens state \<and> {l, r} \<in> G \<rbrakk> 
      \<Longrightarrow> (\<exists> l. ben_lookup (best_even_neighbour state) r = Some l \<and>
                            {r, l} \<in> G  \<and>  l \<in> aevens state \<and>
                            w\<^sub>\<pi> l r + missed_at state l = 
                            Min {w\<^sub>\<pi> l r + missed_at state l | l. 
                                   l \<in> aevens state \<and> {l, r} \<in> G})"
  by(auto simp add: invar_best_even_neighbour_map_def)

definition "edge_slack pot x y = 
    edge_costs x y - pot x - pot y"

(*definition "add_to_pot pot x val = 
           (case potential_lookup pot x of 
             None \<Rightarrow> potential_upd pot x val 
             | Some val' \<Rightarrow> potential_upd pot x (val + val'))"*)
(*
definition "best_even_neighbour_ereal_costs ben off r = (
            case (ben_lookup ben r) of None \<Rightarrow> PInfty|
             Some l \<Rightarrow> w\<^sub>\<pi> l r - off)"*)
(*
definition "best_even_neighbour_costs ben v = snd (the (ben_lookup ben v))"
*)(*
lemma best_even_neighbour_real_and_ereal_costs:
 "(ben_lookup ben v) \<noteq> None \<Longrightarrow>
  best_even_neighbour_ereal_costs ben v = best_even_neighbour_costs ben v"
  by(auto simp add: best_even_neighbour_ereal_costs_def
                    best_even_neighbour_costs_def
        split: option.split)
*)
definition "update_best_even_neighbour off ben queue l =
   foldl 
       (\<lambda> (ben, queue) r. 
                (case ben_lookup ben r of None \<Rightarrow>
                     (ben_upd ben r l, heap_insert queue r (w\<^sub>\<pi> l r + off l)) |
                 Some l' \<Rightarrow>
                 if w\<^sub>\<pi> l r + off l < w\<^sub>\<pi> l' r + off l'
                 then (ben_upd ben r l, heap_decrease_key queue r (w\<^sub>\<pi> l r + off l))
                 else (ben, queue)))
                   (ben, queue) 
        (to_list (right_neighbs l))"

definition "update_best_even_neighbours off ben queue new_evens =
  foldl 
    (\<lambda> ben_queue r. update_best_even_neighbour off (fst ben_queue) (snd ben_queue) r) 
  (ben, queue) new_evens"
(*
definition "find_next_edge ben queue= 
             (foldl (\<lambda> result v. 
                 if vset_isin v odd_verts then result
                 else
                  (case ben_lookup ben v of None \<Rightarrow> result
                     | Some (e, sl) => 
                     (case result of None \<Rightarrow> Some (e, v, sl)
                         | Some (x, y, \<epsilon>) \<Rightarrow> 
                             (if sl < \<epsilon> then Some (e, v, sl)
                                 else Some (x, y, \<epsilon>))))
                    ) None (to_list right))"
*)
definition "unmatched_lefts = filter (\<lambda> v. if buddy v = None then True else False) (to_list left)"
definition "forest_roots = foldl (\<lambda> vset v. vset_insert v vset) vset_empty unmatched_lefts"
definition "init_best_even_neighbour = 
   update_best_even_neighbours (\<lambda> x. 0) ben_empty heap_empty unmatched_lefts"

definition "initial_state = 
 \<lparr>forest= empty_forest forest_roots, 
  best_even_neighbour= fst (init_best_even_neighbour),
  heap = snd (init_best_even_neighbour),
  missed = missed_empty,
  acc = 0,
  augpath = None\<rparr>"
(*
definition "change_potential pot \<epsilon> even_verts odd_verts =
            (foldl (\<lambda> pot v. add_to_pot pot v \<epsilon>) 
               (foldl (\<lambda> pot v. add_to_pot pot v \<epsilon>) pot odd_verts)
             even_verts)"
*)
function (domintros) search_path::
  " ('forest, 'ben, 'heap, 'miss, 'v) hungarian_search_state \<Rightarrow>
   ('forest, 'ben, 'heap, 'miss, 'v) hungarian_search_state" where
"search_path state = 
  (let F = forest state;
       ben = best_even_neighbour state;
       missed_\<epsilon> = missed_at state;
       (queue, heap_min) = heap_extract_min (heap state)
   in (case heap_min of
          None \<Rightarrow> state \<lparr>augpath:=None\<rparr> |
          Some r \<Rightarrow>
            (let l = the (ben_lookup ben r);
                 acc' = w\<^sub>\<pi> l r + missed_\<epsilon> l
             in
             (case buddy r of 
                 None \<Rightarrow>
                    state \<lparr> acc := acc',
                            augpath:= Some (rev (get_path F l) @[r]) \<rparr>|
                 Some l' \<Rightarrow>
                     (let missed' = missed_upd (
                                    missed_upd (missed state) r acc') 
                                                l' acc';
                          (ben', queue') = update_best_even_neighbour 
                                           (abstract_real_map (missed_lookup missed'))
                                           ben queue l';
                          F'= extend_forest_even_unclassified F l r l' 
                      in  
                    search_path (state \<lparr> forest:= F', 
                            best_even_neighbour:=ben',
                            heap:=queue',
                            missed:=missed',
                            acc:= acc' \<rparr>)
             )))))"
  by pat_completeness auto

definition "search_path_fail_cond state = 
  (let (queue, heap_min) = heap_extract_min (heap state)
   in (case heap_min of None \<Rightarrow> True|
                        Some r \<Rightarrow> False))"

lemma search_path_fail_condE:
"search_path_fail_cond state \<Longrightarrow>
(\<And> queue heap_min. 
    \<lbrakk> (queue, heap_min) = heap_extract_min (heap state); heap_min = None\<rbrakk> \<Longrightarrow> P)
\<Longrightarrow> P"
  apply(cases "heap_extract_min (heap state)")
  apply(all \<open>cases "snd (heap_extract_min (heap state))"\<close>)
  by(auto simp add: search_path_fail_cond_def)

definition "search_path_succ_cond state = 
  (let (queue, heap_min) = heap_extract_min (heap state)
   in (case heap_min of
          None \<Rightarrow> False|
          Some r \<Rightarrow> (case buddy r of 
                        None \<Rightarrow> True|
                        Some l' \<Rightarrow> False )))"

lemma search_path_succ_condE:
"search_path_succ_cond state \<Longrightarrow>
(\<And> queue heap_min r. 
    \<lbrakk> (queue, heap_min) = heap_extract_min (heap state); 
        heap_min = Some r; buddy r = None\<rbrakk> \<Longrightarrow> P)
\<Longrightarrow> P"
  apply(cases "heap_extract_min (heap state)")
  apply(all \<open>cases "snd (heap_extract_min (heap state))"\<close>)
  apply(all \<open>cases "buddy (the (snd (heap_extract_min (heap state))))"\<close>)
  by(auto simp add: search_path_succ_cond_def)

definition "search_path_cont_cond state = 
  (let (queue, heap_min) = heap_extract_min (heap state)
   in (case heap_min of None \<Rightarrow> False|
                        Some r \<Rightarrow> (case buddy r of None \<Rightarrow> False|
                                                   Some l' \<Rightarrow> True)))"

lemma search_path_cont_condE:
"search_path_cont_cond state \<Longrightarrow>
(\<And> queue heap_min r l'. 
    \<lbrakk>  heap_extract_min (heap state) = (queue, heap_min); 
        heap_min = Some r; buddy r = Some l'\<rbrakk> \<Longrightarrow> P)
\<Longrightarrow> P"
  apply(cases "heap_extract_min (heap state)")
  apply(all \<open>cases "snd (heap_extract_min (heap state))"\<close>)
  apply(all \<open>cases "buddy (the (snd (heap_extract_min (heap state))))"\<close>)
  by(auto simp add: search_path_cont_cond_def)

lemma search_path_cases:
  assumes "search_path_fail_cond state \<Longrightarrow> P"
          "search_path_succ_cond state \<Longrightarrow> P"
          "search_path_cont_cond state \<Longrightarrow> P"
    shows P
  using assms
  apply(cases "heap_extract_min (heap state)")
  apply(all \<open>cases "snd (heap_extract_min (heap state))"\<close>)
  apply(all \<open>cases "buddy (the (snd (heap_extract_min (heap state))))"\<close>)
  by(auto simp add: search_path_fail_cond_def
                    search_path_succ_cond_def search_path_cont_cond_def)

definition "search_path_fail_upd state = state \<lparr>augpath:=None\<rparr>"

definition "search_path_succ_upd state = 
  (let F = forest state;
       ben = best_even_neighbour state;
       missed_\<epsilon> = missed_at state;
       (queue, heap_min) = heap_extract_min (heap state);
       r = the heap_min;
       l = the (ben_lookup ben r);
       acc' = w\<^sub>\<pi> l r + missed_\<epsilon> l
    in state \<lparr> acc := acc', augpath:= Some (rev (get_path F l) @[r]) \<rparr>)"

definition "search_path_cont_upd state = 
  (let F = forest state;
       ben = best_even_neighbour state;
       missed_\<epsilon> = missed_at state;
       (queue, heap_min) = heap_extract_min (heap state);
       r = the heap_min;
       l = the (ben_lookup ben r);
        acc' = w\<^sub>\<pi> l r + missed_\<epsilon> l;
       l' =  the (buddy r);
       missed' = missed_upd (missed_upd (missed state) r acc') 
                                                l' acc';
       (ben', queue') = update_best_even_neighbour 
                 (abstract_real_map (missed_lookup missed'))ben queue l';
       F'= extend_forest_even_unclassified F l r l' 
    in state \<lparr> forest:= F', best_even_neighbour:=ben',
              heap:=queue', missed:=missed', acc:= acc' \<rparr>)"
 
lemma search_path_simps:
  "search_path_fail_cond state \<Longrightarrow> search_path state = search_path_fail_upd state"
  "search_path_succ_cond state \<Longrightarrow> search_path state = search_path_succ_upd state"
  "\<lbrakk>search_path_dom state; search_path_cont_cond state\<rbrakk> \<Longrightarrow>
   search_path state = search_path (search_path_cont_upd state)"
proof(goal_cases)
  case 1
  show ?case 
    apply(subst search_path.psimps)
    apply(all \<open>cases "heap_extract_min (heap state)"\<close>)
    apply(all \<open>cases "snd (heap_extract_min (heap state))"\<close>)
    using 1
    by(auto intro: search_path.domintros
             simp add: search_path_fail_cond_def search_path_fail_upd_def)
next
  case 2
  show ?case
    apply(subst search_path.psimps)
    apply(all \<open>cases "heap_extract_min (heap state)"\<close>)
    apply(all \<open>cases "snd (heap_extract_min (heap state))"\<close>)
    apply(all \<open>cases "buddy (the (snd (heap_extract_min (heap state))))"\<close>)
    using 2
    by(auto intro: search_path.domintros
             simp add: search_path_succ_cond_def search_path_succ_upd_def)
next
  case 3
  show ?case 
    apply(subst search_path.psimps[OF 3(1)])
    apply(all \<open>cases "heap_extract_min (heap state)"\<close>)
    apply(all \<open>cases "snd (heap_extract_min (heap state))"\<close>)
    apply(all \<open>cases "buddy (the (snd (heap_extract_min (heap state))))"\<close>)
    using 3
    by(auto simp add: search_path_cont_cond_def search_path_cont_upd_def Let_def
               split: option.split prod.split)
qed

lemma search_path_induct:
  assumes "search_path_dom state"
           "\<And> state. \<lbrakk>search_path_dom state;
                      search_path_cont_cond state \<Longrightarrow> P (search_path_cont_upd state)\<rbrakk>
                     \<Longrightarrow> P state"
  shows "P state"
proof(induction rule: search_path.pinduct[OF assms(1)])
  case (1 state)
  note IH = this
  show ?case 
  proof(cases state rule: search_path_cases, goal_cases)
    case 1
    then show ?case
     by(auto elim!:  search_path_fail_condE
            intro!: assms(2)[OF IH(1)]
          simp add: search_path_cont_cond_def)
  next
    case 2
    then show ?case 
     by(auto elim!:  search_path_succ_condE
            intro!: assms(2)[OF IH(1)] 
          simp add: search_path_cont_cond_def)
  next
    case 3
    show ?case 
      apply(rule assms(2)[OF IH(1)])
      using 3 assms(2)
      by(auto intro!: IH(2)
               elim!: search_path_cont_condE
            simp add: search_path_cont_upd_def Let_def 
               split: option.split prod.split)
  qed
qed

partial_function (tailrec) search_path_impl::
  " ('forest, 'ben, 'heap, 'miss, 'v) hungarian_search_state \<Rightarrow>
   ('forest, 'ben, 'heap, 'miss, 'v) hungarian_search_state" where
"search_path_impl state = 
  (let F = forest state;
       ben = best_even_neighbour state;
       missed_\<epsilon> = missed_at state;
       (queue, heap_min) = heap_extract_min (heap state)
   in (case heap_min of
          None \<Rightarrow> state \<lparr>augpath:=None\<rparr> |
          Some r \<Rightarrow>
            (let l = the (ben_lookup ben r);
                 acc' = w\<^sub>\<pi> l r + missed_\<epsilon> l
             in
             (case buddy r of 
                 None \<Rightarrow>
                    state \<lparr> acc := acc',
                            augpath:= Some (rev (get_path F l) @[r]) \<rparr>|
                 Some l' \<Rightarrow>
                     (let missed' = missed_upd (
                                    missed_upd (missed state) r acc') 
                                                l' acc';
                          (ben', queue') = update_best_even_neighbour 
                                           (abstract_real_map (missed_lookup missed'))
                                           ben queue l';
                          F'= extend_forest_even_unclassified F l r l' 
                      in  
            search_path_impl (state \<lparr> forest:= F', 
                            best_even_neighbour:=ben',
                            heap:=queue',
                            missed:=missed',
                            acc:= acc' \<rparr>)
             )))))"

lemma search_path_impl_same:
  assumes "search_path_dom state"
  shows "search_path_impl state = search_path state"
  apply(induction rule: search_path.pinduct[OF assms])
  apply(subst search_path.psimps, simp)
  apply(subst search_path_impl.simps)
  by (auto simp add: Let_def split: if_split option.split prod.split)

definition "forest_extension_precond F M x y z =
      (forest_invar M F \<and> x \<in> vset_to_set (evens F) \<and>
        {y, z} \<inter> (vset_to_set (evens F) \<union> vset_to_set (odds F)) = {} \<and>
        {x, y} \<notin> M \<and> {y, z} \<in> M)"

lemma forest_extension_precondI:
"\<lbrakk>forest_invar M F; x \<in> vset_to_set (evens F);
  {y, z} \<inter> (vset_to_set (evens F) \<union> vset_to_set (odds F)) = {};
  {x, y} \<notin> M; {y, z} \<in> M\<rbrakk>
\<Longrightarrow>forest_extension_precond F M x y z "
  by(auto simp add: forest_extension_precond_def)
end


locale primal_dual_path_search =
        primal_dual_path_search_spec 
      where G = "G::'v set set" 
      and   left = "left::'vset"
      and empty_forest="empty_forest::'vset \<Rightarrow> 'forest"
      and initial_pot = "initial_pot::'pot"
      and ben_empty="ben_empty::'ben"
    for G left empty_forest initial_pot ben_empty
+
assumes G: "bipartite G L R"
           "\<And> u v. in_G u v \<longleftrightarrow> {u, v} \<in> G"
           "vset_invar left" "vset_invar right"
           "\<And> v. v \<in> vset_to_set left \<Longrightarrow> vset_invar (right_neighbs v)"
           "\<And> v. v \<in> vset_to_set left \<Longrightarrow> vset_to_set (right_neighbs v) = {u | u. {v, u} \<in> G}"
           "\<And> u v. {u, v} \<in> G \<Longrightarrow> edge_costs u v = edge_costs v u"
           "\<And> u v. {u, v} \<in> G \<Longrightarrow> \<pi> u + \<pi> v \<le> \<w> u v"
and matching: "\<And> u v. buddy u = Some v \<Longrightarrow> buddy v = Some u"
              "graph_matching G {{u, v} | u v. buddy u = Some v}"
              "\<And> u v. {u, v} \<in> \<M> \<Longrightarrow> \<pi> u + \<pi> v = \<w> u v"
and forest_extend: "\<And> F M x y z. forest_extension_precond F M x y z
      \<Longrightarrow> forest_invar M (extend_forest_even_unclassified F x y z)"
   "\<And> F M x y z. forest_extension_precond F M x y z
      \<Longrightarrow> abstract_forest (extend_forest_even_unclassified F x y z) =
          abstract_forest F \<union> {{x, y}, {y, z}}"
   "\<And> F M x y z. forest_extension_precond F M x y z
      \<Longrightarrow> vset_to_set (evens (extend_forest_even_unclassified F x y z)) =
          insert z (vset_to_set (evens F))"
   "\<And> F M x y z. forest_extension_precond F M x y z
      \<Longrightarrow> vset_to_set (odds (extend_forest_even_unclassified F x y z)) =
          insert y (vset_to_set (odds F))"
   "\<And> F M x y z. forest_extension_precond F M x y z
      \<Longrightarrow> vset_to_set (roots (extend_forest_even_unclassified F x y z)) =
          vset_to_set (roots F)"
and evens_and_odds:
 "\<And> F M. forest_invar M F\<Longrightarrow> vset_invar (evens F)"
 "\<And> F M. forest_invar M F\<Longrightarrow> vset_invar (odds F)"
 "\<And> F M. forest_invar M F
      \<Longrightarrow> vset_to_set (evens F) \<union> vset_to_set (odds F) = 
          vset_to_set (roots F) \<union> Vs (abstract_forest F)"
  "\<And> F M. forest_invar M F\<Longrightarrow> 
       (vset_to_set (evens F))\<inter>(vset_to_set (odds F)) = {}"
and finite_forest:
 "\<And> F M. forest_invar M F\<Longrightarrow> finite (vset_to_set (evens F))"
 "\<And> F M. forest_invar M F\<Longrightarrow> finite (vset_to_set (odds F))"
 "\<And> F M. forest_invar M F\<Longrightarrow> finite (abstract_forest F)"
and roots:
   "\<And> F M. forest_invar M F \<Longrightarrow> vset_invar (roots F)" 
   "\<And> F M. forest_invar M F \<Longrightarrow> vset_to_set (roots F) \<subseteq> vset_to_set (evens F)" 
and empty_forest:
    "\<And> R. evens (empty_forest R) = R"
    "\<And> R. odds (empty_forest R) = vset_empty"
    "\<And> R. abstract_forest (empty_forest R) = {}"
    "\<And> R. \<lbrakk>matching M; vset_invar R; vset_to_set R \<inter> Vs M = {}; 
           finite (vset_to_set R); vset_to_set R \<noteq> {}\<rbrakk>
          \<Longrightarrow> forest_invar M (empty_forest R)"
and get_path:
    "\<And> F M v p. \<lbrakk>forest_invar M F; v \<in> vset_to_set (evens F); p = get_path F v\<rbrakk> \<Longrightarrow>
           alt_path M (rev p) \<and> odd (length p) \<and>
           last p \<in> vset_to_set (roots F) \<and>
           walk_betw (abstract_forest F) v p (last p)"
and higher_forest_properties:
    "\<And> F M. forest_invar M F\<Longrightarrow> 
       card (vset_to_set (evens F)) > card (vset_to_set (odds F))"
    "\<And> F M u v. \<lbrakk>forest_invar M F; {u, v} \<in> M\<rbrakk>\<Longrightarrow>
        {u, v} \<in> abstract_forest F \<or> 
          {u, v} \<inter> (Vs (abstract_forest F) \<union> vset_to_set (roots F)) = {}"
    "\<And> F M u v. \<lbrakk>forest_invar M F; {u, v} \<in> abstract_forest F\<rbrakk>\<Longrightarrow>
               u \<in> vset_to_set (evens F) \<longleftrightarrow> v \<in> vset_to_set (odds F)"
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
and heap:
 "heap_invar heap_empty"
 "\<And> H. heap_invar H \<Longrightarrow> heap_invar (fst (heap_extract_min H))"
 "\<And> H x k. \<lbrakk>heap_invar H; \<nexists> k. (x, k) \<in> (heap_abstract H)\<rbrakk> 
          \<Longrightarrow> heap_invar (heap_insert H x k)"
 "\<And> H x k k'. \<lbrakk>heap_invar H; (x, k') \<in>  (heap_abstract H); k < k'\<rbrakk> 
          \<Longrightarrow> heap_invar (heap_decrease_key H x k)"

 "\<And> H x.  \<lbrakk>heap_invar H; Some x = snd (heap_extract_min H)\<rbrakk> \<Longrightarrow>
           \<exists> k. ((x, k) \<in> heap_abstract H \<and> 
                (\<forall> x' k'. (x', k') \<in> heap_abstract H \<longrightarrow> k \<le> k'))"
 "\<And> H.  \<lbrakk>heap_invar H; None = snd (heap_extract_min H)\<rbrakk> \<Longrightarrow>
            heap_abstract H = {}"
 "\<And> H x k k'. \<lbrakk>heap_invar H; (x, k) \<in> heap_abstract H; (x, k') \<in> heap_abstract H\<rbrakk>
                  \<Longrightarrow> k = k'"

 "\<And> H x k.  \<lbrakk>heap_invar H; Some x = snd (heap_extract_min H); (x, k) \<in> heap_abstract H\<rbrakk> \<Longrightarrow>
           heap_abstract (fst (heap_extract_min H)) =  heap_abstract H - {(x, k)}"
 "\<And> H x k k'.  \<lbrakk>heap_invar H;  (x, k) \<in> heap_abstract H; k' < k\<rbrakk> \<Longrightarrow>
           heap_abstract (heap_decrease_key H x k') =
           heap_abstract H - {(x, k)} \<union> {(x, k')}"
 "\<And> H x k.  \<lbrakk>heap_invar H; \<nexists> k. (x, k) \<in> heap_abstract H\<rbrakk> \<Longrightarrow>
           heap_abstract (heap_insert H x k) = heap_abstract H  \<union> {(x, k)}"
 "heap_abstract heap_empty = {}"
and missed:
 "missed_invar missed_empty" "\<And> x. missed_lookup missed_empty x= None"
  "\<And> missed x s. missed_invar missed \<Longrightarrow> missed_invar (missed_upd missed x s)"
  "\<And> missed x s. missed_invar missed \<Longrightarrow> missed_lookup (missed_upd missed x s) =
                (missed_lookup missed)(x \<mapsto> s)"
  "\<And> x. missed_lookup missed_empty x = None"
begin

lemma w\<^sub>\<pi>_symmetric: "{u, v} \<in> G \<Longrightarrow> w\<^sub>\<pi> u v = w\<^sub>\<pi> v u"
  by(auto simp add: w\<^sub>\<pi>_def intro: G(7))

lemma w\<^sub>\<pi>_non_neg: "{u, v} \<in> G \<Longrightarrow> w\<^sub>\<pi> u v \<ge> 0"
  using G(8) w\<^sub>\<pi>_def by fastforce

lemma update_best_even_neighbour_correct:
  assumes "ben_invar ben" "heap_invar queue" "l \<in> L"
          "\<And> r k. (r, k) \<in> heap_abstract queue \<longrightarrow>
          (\<exists> l. ben_lookup ben r = Some l \<and> k = w\<^sub>\<pi> l r + off l)"
          "\<And> r l'. ben_lookup ben r = Some l' \<and> (\<nexists> k. (r, k) \<in> heap_abstract queue) \<longrightarrow>
             off l \<ge> w\<^sub>\<pi> l' r + off l'"
          "(ben', queue') = update_best_even_neighbour off ben queue l"
 shows "ben_invar ben'" (is ?thesis1) "heap_invar queue'" (is ?thesis2)
       "\<And> r k.  (r, k) \<in> heap_abstract queue' \<Longrightarrow> 
        \<exists> l. ben_lookup ben' r = Some l \<and> k = w\<^sub>\<pi> l r + off l"
        "\<And> r l'. ben_lookup ben' r = Some l' \<and> (\<nexists> k. (r, k) \<in> heap_abstract queue') \<Longrightarrow>
             off l \<ge> w\<^sub>\<pi> l' r + off l'"
      "ben_lookup ben' = (\<lambda> r. if r \<notin> vset_to_set (right_neighbs l) then ben_lookup ben r
                               else if ben_lookup ben r = None 
                                    then Some l
                               else if w\<^sub>\<pi> l r + off l < 
                                      w\<^sub>\<pi> (the (ben_lookup ben r)) r + off (the (ben_lookup ben r))
                                    then Some l
                                else ben_lookup ben r)" (is ?thesis3)
      "heap_abstract queue' = 
       heap_abstract queue
       - {(r, k) | r k. r \<in> vset_to_set (right_neighbs l)}
       \<union> {(r, min (w\<^sub>\<pi> l r + off l) 
                  (w\<^sub>\<pi> (the (ben_lookup ben r)) r + off (the (ben_lookup ben r))))
          | r. r \<in> vset_to_set (right_neighbs l) \<and> r \<in> fst ` (heap_abstract queue)}
       \<union> { (r, w\<^sub>\<pi> l r + off l) 
          | r . r \<in> vset_to_set (right_neighbs l) \<and> ben_lookup ben r = None}" (is ?thesis4)
proof-
  define f where "f = (\<lambda> (ben, queue) r.
     case ben_lookup ben r of
     None \<Rightarrow> (ben_upd ben r l, heap_insert queue r (w\<^sub>\<pi> l r + off l))
     | Some l' \<Rightarrow>
         if w\<^sub>\<pi> l r + off l < w\<^sub>\<pi> l' r + off l'
         then (ben_upd ben r l, heap_decrease_key queue r (w\<^sub>\<pi> l r + off l))
         else (ben, queue))"
  define rs where "rs = rev (to_list (right_neighbs l))"
  have rs_props: "distinct rs" "set rs = vset_to_set (right_neighbs l)"
    using vset(6)[of "right_neighbs l"] G(5) assms(3)
          vset(7)[of "right_neighbs l", OF _ refl]
    by (auto simp add: rs_def)
  have news_in_G:"{{l, r} | r. r \<in> set rs} \<subseteq> G" 
    unfolding rs_props G(6)[OF assms(3)] by blast
  have induction:"?thesis1 \<and> ?thesis2 \<and>
        (\<forall> r k.  (r, k) \<in> heap_abstract queue' \<longrightarrow> 
               (\<exists> l. ben_lookup ben' r = Some l \<and> k = w\<^sub>\<pi> l r + off l)) \<and>
        (\<forall> r l'. ben_lookup ben' r = Some l' \<and> (\<nexists> k. (r, k) \<in> heap_abstract queue') \<longrightarrow>
             off l \<ge> w\<^sub>\<pi> l' r + off l')
           \<and> ?thesis3 \<and> ?thesis4"
    using assms(1,2,4,5,6) rs_props(1)  news_in_G
    unfolding update_best_even_neighbour_def foldl_conv_foldr
    unfolding rs_def[symmetric] rs_props(2)[symmetric] f_def[symmetric]
  proof(induction rs arbitrary: queue ben queue' ben')
    case Nil
    thus ?case
      by simp
  next
    case (Cons r rs)
    define ben_before where "ben_before = (fst (foldr (\<lambda>x y. f y x) rs (ben, queue)))"
    define queue_before where "queue_before = (snd (foldr (\<lambda>x y. f y x) rs (ben, queue)))"
    have state_before_is: "(ben_before, queue_before) = foldr (\<lambda>x y. f y x) rs (ben, queue)"
      by(simp add: ben_before_def queue_before_def)
    have ben'_is: "ben' = (fst (f (ben_before, queue_before) r))"
                  "queue' = (snd (f (ben_before, queue_before) r))"
      using Cons.prems(5) 
      by (simp add: split_pairs ben_before_def queue_before_def)+
    have distinct_rs: "distinct rs" using Cons(7) by auto
  have news_in_G:"{{l, r} | r. r \<in> set rs} \<subseteq> G"
    using Cons.prems(7) by auto
  have pos_new_e:" w\<^sub>\<pi> l r \<ge> 0" 
          using Cons.prems(7) w\<^sub>\<pi>_non_neg[of l r] by auto
    note IH_applied_all = Cons(1)[OF Cons(2,3,4,5) state_before_is 
             distinct_rs news_in_G]
    note IH_applied = conjD(1)[OF IH_applied_all]
                      conjD(2)[OF IH_applied_all]
                      mp[OF spec[OF spec[OF conjD(3)[OF IH_applied_all]]]]
                      mp[OF spec[OF spec[OF conjD(4)[OF IH_applied_all]]]]
                      conjD(5)[OF IH_applied_all]
                       conjD(6)[OF IH_applied_all]
    show ?case 
      unfolding ben'_is
    proof(rule conj_intro, goal_cases)
      case 1
      then show ?case
        using IH_applied
        by(auto split: option.split 
               intro!: best_even_neighbour(2) 
             simp add: f_def)
    next
      case 2
      have helper: "ben_lookup ben r = Some x2 \<Longrightarrow>
          w\<^sub>\<pi> l r + off l < w\<^sub>\<pi> x2 r + off x2 \<Longrightarrow>
          (r, w\<^sub>\<pi> x2 r + off x2) \<in> heap_abstract queue_before" for x2
      proof(rule ccontr, goal_cases)
        case 1
        hence "(r, k) \<in> heap_abstract queue_before \<Longrightarrow> False" for k
          using Cons.prems(6) IH_applied(3)[of r k] IH_applied(5) by simp
        hence "\<nexists> k. (r, k) \<in> heap_abstract queue_before" by auto
        hence "off l \<ge> w\<^sub>\<pi> x2 r + off x2"
          using "1"(1) Cons.prems(6) IH_applied_all by auto
        thus ?case
          using "1"(2) pos_new_e by simp
      qed
      from 2 show ?case 
        using IH_applied(1,2) IH_applied(3) Cons.prems(3)[of r] IH_applied(4)[of r]
        by(auto split: option.split 
               intro!: heap(3,4) helper 
                 dest: IH_applied(3)
             simp add: f_def IH_applied(5))
    next
      case 3
      then show ?case
      proof(cases "ben_lookup ben_before r")
        case None
        hence not_in_heap_before:"\<nexists>k. (r, k) \<in> heap_abstract queue_before" 
          using IH_applied(3) by force
        show ?thesis 
        using IH_applied(1,2,3) not_in_heap_before
        by(auto simp add: f_def best_even_neighbour(3) None 
                          heap(10)[OF IH_applied(2) not_in_heap_before])
      next
        case (Some l')
        hence in_heap_before: "w\<^sub>\<pi> l r + off l < w\<^sub>\<pi> l' r + off l' \<Longrightarrow> 
            (r, w\<^sub>\<pi> l' r + off l') \<in> heap_abstract queue_before"
          using IH_applied(4)[of r l'] IH_applied(3)[of r] pos_new_e by force
        show ?thesis 
        using IH_applied(1,2,3) heap(9,7)[OF IH_applied(2) in_heap_before]
        by(auto simp add: f_def best_even_neighbour(3) Some)
    qed
    next
      case 4
      then show ?case 
      proof(cases "ben_lookup ben_before r")
        case None
        hence not_in_heap_before:"\<nexists>k. (r, k) \<in> heap_abstract queue_before" 
          using IH_applied(3) by force
        show ?thesis 
        using IH_applied(1,2)
        by(auto simp add: f_def best_even_neighbour(3) None 
                          heap(10)[OF IH_applied(2) not_in_heap_before] 
                  intro!: IH_applied(4))
      next
        case (Some l')
        hence in_heap_before: "w\<^sub>\<pi> l r + off l < w\<^sub>\<pi> l' r + off l' 
              \<Longrightarrow>  (r, w\<^sub>\<pi> l' r + off l') \<in> heap_abstract queue_before"
         using IH_applied(4)[of r l'] IH_applied(3)[of r] pos_new_e by force
        show ?thesis 
        using IH_applied(1,2,3)
        by(auto simp add: f_def best_even_neighbour(3) Some
                          heap(9)[OF IH_applied(2) in_heap_before]
                  intro!: IH_applied(4))
     qed
    next
      case 5
      show ?case
      proof(cases "ben_lookup ben_before r")
        case None
        hence not_in_heap_before:"\<nexists>k. (r, k) \<in> heap_abstract queue_before" 
          using IH_applied(3) by force
        show ?thesis 
        using IH_applied(1,2)
        by(auto simp add: f_def best_even_neighbour(3) None IH_applied(5))
      next
        case (Some l')
        hence in_heap_before: "w\<^sub>\<pi> l r + off l < w\<^sub>\<pi> l' r + off l' 
             \<Longrightarrow> (r, w\<^sub>\<pi> l' r + off l') \<in> heap_abstract queue_before"
          using IH_applied(4)[of r l'] IH_applied(3)[of r] pos_new_e by force
        show ?thesis 
        using IH_applied(1,2,3)
        by(auto simp add: f_def best_even_neighbour(3) Some IH_applied(5)
                          heap(9)[OF IH_applied(2) in_heap_before])
    qed
  next
    case 6
     have ben_before_r_is:"ben_lookup ben_before r = ben_lookup ben r"
          using Cons.prems(6) IH_applied(5) by auto
    have Collect_Cons: "{f x | x. x \<in> set (y#ys)}
              = insert ( f y) {f x | x. x \<in> set ys}"
          for f y ys by auto
      show ?case
      proof(cases "ben_lookup ben_before r")
        case None
        hence not_in_heap_before:"\<nexists>k. (r, k) \<in> heap_abstract queue_before" 
          using IH_applied(3) by force
        show ?thesis 
          unfolding Collect_Cons
          using None ben_before_r_is Cons.prems(3)[of r]
          by (auto simp add: f_def  None  IH_applied(6) 
                             heap(10)[OF IH_applied(2) not_in_heap_before] )
      next
        case (Some l')
        hence in_heap_before: 
        "w\<^sub>\<pi> l r + off l < w\<^sub>\<pi> l' r + off l' \<Longrightarrow> (r, w\<^sub>\<pi> l' r + off l') \<in> heap_abstract queue_before"
          using IH_applied(4)[of r l'] IH_applied(3)[of r] pos_new_e by force
        have if_not_P2:"ben_lookup ben r \<noteq> None"
          using Some ben_before_r_is by auto
        have ben_of_r_is_l':"(the (ben_lookup ben r)) = l'" 
          using Some ben_before_r_is by auto
        have helper1: " (r, k) \<in> heap_abstract queue \<Longrightarrow> k = w\<^sub>\<pi> l' r + off l'" for k
            using Some ben_before_r_is Cons.prems(3)[of r] Cons.prems(2,4)
            by(auto intro: heap(7))
        show ?thesis
          unfolding Collect_Cons f_def split Some option.case(2)
        proof(cases "w\<^sub>\<pi> l r + off l < w\<^sub>\<pi> l' r + off l'", goal_cases)
          case 1
          have helpers2: "(r, w\<^sub>\<pi> l r + off l) \<in> heap_abstract queue" False
            if "w\<^sub>\<pi> l r + off l < w\<^sub>\<pi> l' r + off l'" "r \<notin> fst ` heap_abstract queue"
               "ben_lookup ben r = Some l'"
            using that Cons.prems(4) image_iff pos_new_e helper1 by fastforce+
          have helpers3: "k = w\<^sub>\<pi> (the (ben_lookup ben r)) r + off (the (ben_lookup ben r))"
            if "l' = the (ben_lookup ben r)" "(r, k) \<in> heap_abstract queue" for k
            using that  Cons.prems(4) image_iff pos_new_e helper1 by fastforce
          have helpers4: " k = w\<^sub>\<pi> l' r + off l'"
            if"(r, k) \<in> heap_abstract queue" for k
          using that  Cons.prems(4) image_iff pos_new_e helper1 by fastforce
        from 1 show ?case 
            unfolding if_P[OF 1] snd_conv if_not_P[OF if_not_P2] ben_of_r_is_l'
                      heap(9)[OF IH_applied(2) in_heap_before[OF 1] 1]   
                      IH_applied(6)
            using  ben_of_r_is_l' helpers2 helpers3 helpers4 by auto
        next
          case 2
          thus ?case
            using Cons.prems(3,4,7) helper1 if_not_P2 Some ben_before_r_is
            unfolding if_not_P[OF 2] snd_conv if_not_P[OF if_not_P2] ben_of_r_is_l'
                      IH_applied(6)
            by (auto simp add: rev_image_eqI)
        qed
      qed
    qed
  qed
  show ?thesis1 ?thesis2
    using conjD(1,2)[OF induction]
    by simp+
  show ?thesis3 
    using conjD(5)[OF induction] by simp
  show ?thesis4
    using conjD(6)[OF induction] by simp
  show"\<And> r k. (r, k) \<in> heap_abstract queue'
         \<Longrightarrow> \<exists>l. ben_lookup ben' r = Some l \<and> k = w\<^sub>\<pi> l r + off l"
    using conjD(3)[OF induction] by auto
  show "\<And> r l'. ben_lookup ben' r = Some l' \<and> (\<nexists>k. (r, k) \<in> heap_abstract queue') \<Longrightarrow>
        w\<^sub>\<pi> l' r + off l' \<le> off l"
    using conjD(4)[OF induction] by auto
qed

lemma update_best_even_neighbours_correct:
  assumes "ben_invar ben" "heap_invar queue" "set ls \<subseteq> L"
          "\<And> r k. (r, k) \<in> heap_abstract queue \<longrightarrow>
          (\<exists> l. ben_lookup ben r = Some l \<and> k = w\<^sub>\<pi> l r + off l)"
          "\<And> r l' l. ben_lookup ben r = Some l' \<and> (\<nexists> k. (r, k) \<in> heap_abstract queue)  \<longrightarrow>
             off l \<ge> w\<^sub>\<pi> l' r + off l'"
          "(ben', queue') = update_best_even_neighbour off ben queue l"
 defines "conn_min \<equiv> (\<lambda> r.
     Min ((if ben_lookup ben r \<noteq> None 
          then {w\<^sub>\<pi> (the (ben_lookup ben r)) r + off (the (ben_lookup ben r))}
          else {}) \<union> 
          {w\<^sub>\<pi> l r + off l | l. l \<in> set ls \<and> r \<in> vset_to_set (right_neighbs l) }))"
 shows "ben_invar ben'" (is ?thesis1) "heap_invar queue'" (is ?thesis2)
       "\<And> r k. (r, k) \<in> heap_abstract queue' \<Longrightarrow>
         (\<exists> l. ben_lookup ben' r = Some l \<and> k = w\<^sub>\<pi> l r + off l)"
       "\<And> r l'. ben_lookup ben' r = Some l' \<and> (\<nexists> k. (r, k) \<in> heap_abstract queue) \<Longrightarrow>
             off l \<ge> w\<^sub>\<pi> l' r + off l'"
       "\<And> r. r \<notin> \<Union> {vset_to_set (right_neighbs l)| l. l \<in> set ls} 
                 \<Longrightarrow> ben_lookup ben' r = ben_lookup ben r"
       "\<And> r. r \<in> \<Union> {vset_to_set (right_neighbs l)| l. l \<in> set ls} 
                 \<Longrightarrow> \<exists> l. ((l \<in> set ls \<and> r \<in> vset_to_set (right_neighbs l))
                            \<or> Some l = ben_lookup ben r) 
                          \<and> w\<^sub>\<pi> l r + off l = conn_min r \<and> ben_lookup ben' r = Some l"
      "heap_abstract queue' = 
       heap_abstract queue
           - {(r, k) | r k l. r \<in> vset_to_set (right_neighbs l) \<and>l \<in> set ls}
           \<union> {(r, w\<^sub>\<pi> ll r + off ll) | r l ll. r \<in> vset_to_set (right_neighbs l) \<and> 
                                         l \<in> set ls \<and> Some ll = ben_lookup ben' r}"
               (is ?thesis4)
proof-
  define ls' where "ls' = rev ls"
  have set_ls_is:"set ls = set ls'"
    by(auto simp add: ls'_def)
  have "?thesis1 \<and> ?thesis2 \<and>
       (\<forall> r k. (r, k) \<in> heap_abstract queue' \<longrightarrow> 
          (\<exists> l. ben_lookup ben' r = Some l \<and> k = w\<^sub>\<pi> l r + off l)) \<and>
       (\<forall> r l. ben_lookup ben' r = Some l \<longrightarrow> (r, w\<^sub>\<pi> l r + off l) \<in> heap_abstract queue') \<and>
       (\<forall> r.  r \<notin> \<Union> {vset_to_set (right_neighbs l)| l. l \<in> set ls} \<longrightarrow> 
         ben_lookup ben' r = ben_lookup ben r) \<and>
       (\<forall> r \<in> \<Union> {vset_to_set (right_neighbs l)| l. l \<in> set ls}.  
         \<exists>l. ((l \<in> set ls \<and> r \<in> vset_to_set (right_neighbs l))
                  \<or> Some l = ben_lookup ben r) \<and> 
             w\<^sub>\<pi> l r + off l = conn_min r \<and> ben_lookup ben' r = Some l) \<and>
       ?thesis4"
    using assms(1-6) meta_eq_to_obj_eq[OF assms(7)]
    unfolding update_best_even_neighbours_def foldl_conv_foldr
              ls'_def[symmetric] set_ls_is
  proof(induction ls' arbitrary: ben' queue' queue ben conn_min)
    case (Cons l ls)
    have ls_in_L: "set ls \<subseteq> L"
      using Cons(4) by auto
    define result where "result = 
      foldr (\<lambda>x y. update_best_even_neighbour off (fst y) (snd y) x) ls (ben, queue)"
    define ben_before where "ben_before = 
     fst result"
    define queue_before where "queue_before = 
     snd result"
    have result_is: "(fst result, snd result) = result"
      by auto
    define conn_min_before where "conn_min_before =
       (\<lambda>r. Min ((if ben_lookup ben r \<noteq> None
            then {w\<^sub>\<pi> (the (ben_lookup ben r)) r + off (the (ben_lookup ben r))}
            else {}) \<union>
           {w\<^sub>\<pi> l r + off l | l. (l \<in> set ls \<and> r \<in> vset_to_set (right_neighbs l))}))"

    note IH_applied_all =
       Cons(1)[OF Cons(2,3) ls_in_L Cons(5,6), simplified result_def[symmetric], 
            OF result_is conn_min_before_def]
    note IH_applied = conjD(1)[OF IH_applied_all]
                      conjD(2)[OF IH_applied_all]
                      spec[OF spec[OF conjD(3)[OF IH_applied_all]]]
                      spec[OF spec[OF conjD(4)[OF IH_applied_all]]]
                      conjD(5)[OF IH_applied_all]
                      conjunct1[OF conjD(6)[OF IH_applied_all]]
                      conjunct2[OF conjD(6)[OF IH_applied_all]]
    thm Cons(7)
    thm Cons(7)[simplified foldr_Cons o_apply]
    have l_in_L: "l \<in> L" 
      using Cons(4) by simp
    have queue'_heap': "(ben', queue') = 
          update_best_even_neighbour off (fst result) (snd result) l"
      by(auto simp add: result_def Cons(7))
    note single_update = update_best_even_neighbour_correct[OF
            IH_applied(1,2) l_in_L IH_applied(3,4) queue'_heap']
    show ?case 
    proof(rule conj_intro, goal_cases)
      case 1
      then show ?case 
        using single_update(1) by simp
    next
      case 2
      then show ?case
        using single_update(2) by simp
    next
      case 3
      then show ?case 
        using single_update(3) by simp
    next
      case 4
      then show ?case 
        using  single_update(4) by simp
    next
      case 5
      then show ?case 
        using IH_applied(5) single_update(5) by fastforce
    next
      case 6
      show ?case 
      proof(rule, rule ballI, goal_cases)
        case (1 r)
        note one = this
        show ?case 
          unfolding single_update(5) 
        proof(cases "r \<notin> vset_to_set (right_neighbs l)", goal_cases)
          case 1
          hence old_conn_min: "conn_min r =  conn_min_before r"
            by(auto intro: arg_cong[of _ _ Min] 
                 simp add: Cons.prems(7) conn_min_before_def )
          obtain l where l: "( (l \<in> set ls \<and> r \<in> vset_to_set (right_neighbs l)) \<or> Some l = ben_lookup ben r)"
           "w\<^sub>\<pi> l r + off l = conn_min_before r \<and> ben_lookup (fst result) r = Some l"
            using 1 one IH_applied(6) by auto
          show ?case
            using l 1
            by(auto intro!: exI[of _ l] simp add:  old_conn_min)
        next
          case 2
          note two = this
          show ?case
            unfolding if_not_P[OF 2]
          proof(cases "ben_lookup (fst result) r", goal_cases)
            case 1
            hence r_not_previously:
                "r \<notin> \<Union> {vset_to_set (right_neighbs l)| l. l \<in> set ls}"
              using IH_applied_all by blast
            hence init_None:"\<not> (ben_lookup ben r \<noteq> None)" 
              using IH_applied(5)
              using "1" by presburger 
            show ?case
              unfolding Cons.prems(7)  if_P[OF 1] if_not_P[OF init_None]
              apply(rule exI[of _ l] )
              apply(rule forw_subst[of _ "{w\<^sub>\<pi> l r + off l}"])
              using  r_not_previously two
              by auto
          next
            case (2 ll)
            have "\<exists>l. ((l \<in> set ls \<and> r \<in> vset_to_set (right_neighbs l)) \<or> Some l = ben_lookup ben r) \<and>
              w\<^sub>\<pi> l r + off l = conn_min_before r \<and> ben_lookup (fst result) r = Some l"
              apply(cases "r \<in> \<Union> {vset_to_set (right_neighbs l)| l. l \<in> set ls}")
              subgoal
                using IH_applied(6) by auto
              subgoal
                apply(rule exI[of _ ll])
                unfolding conn_min_before_def
              apply(rule forw_subst[of _ "{w\<^sub>\<pi> ll r + off ll}"])
              using  two IH_applied(5) 2
              by(auto intro!:  exI[of _ "the (ben_lookup ben r)"])
            done
          hence ll_props: "((ll \<in> set ls \<and> r \<in> vset_to_set (right_neighbs ll)) \<or> Some ll = ben_lookup ben r)"
              "w\<^sub>\<pi> ll r + off ll = conn_min_before r" 
              "ben_lookup (fst result) r = Some ll"
            using 2 by auto
          have conn_min_is: "conn_min r = min (w\<^sub>\<pi> l r + off l) (conn_min_before r)"
            using ll_props
            unfolding Cons.prems(7) conn_min_before_def
            apply(subst linorder_class.Min_insert[symmetric])
              defer defer
              apply(rule arg_cong[of _ _ Min])
            using IH_applied(5) two by auto
          show ?case
            using 2 two ll_props(1)
            by (auto simp add: "2" ll_props(1,2) conn_min_is)+
        qed
      qed
      next
        case 2
        have queue'_is:"heap_abstract queue' =
             heap_abstract (snd result) 
               - {(r, k) | r k. r \<in> vset_to_set (right_neighbs l)} \<union>
               {(r, w\<^sub>\<pi> ll r + off ll) | r ll. r \<in> vset_to_set (right_neighbs l) \<and>
                     Some ll = ben_lookup ben' r}" 
        proof(rule set_eqI, rule, goal_cases)
          case (1 queue_entry)
          then show ?case 
          proof(cases  queue_entry, goal_cases)
            case (1 r' k)
            have helper: False if 
               "\<And> ll. k = w\<^sub>\<pi> ll r' + off ll \<Longrightarrow> Some ll \<noteq> ben_lookup ben' r'"
              "(r', k) =
               (if ben_lookup (fst result) r = None then (r, w\<^sub>\<pi> l r + off l)
                else if w\<^sub>\<pi> l r + off l
                  < w\<^sub>\<pi> (the (ben_lookup (fst result) r)) r +
                    off (the (ben_lookup (fst result) r))
                   then (r, w\<^sub>\<pi> l r + off l)
                   else (r, w\<^sub>\<pi> (the (ben_lookup (fst result) r)) r +
                        off (the (ben_lookup (fst result) r))))"
               "r' \<in> vset_to_set (right_neighbs l)" for r
              using that
              apply(cases "ben_lookup (fst result) r = None") 
              apply( all \<open>cases "w\<^sub>\<pi> l r + off l
                    < w\<^sub>\<pi> (the (ben_lookup (fst result) r)) r +
                        off (the (ben_lookup (fst result) r))"\<close>)
              by(force simp add: single_update(5))+
            from 1 show ?thesis  
             unfolding single_update(6) 
             by auto (auto intro: helper simp add: single_update(5))
         qed
       qed (force simp add: single_update(5,6))       
       show ?case 
         unfolding  queue'_is  IH_applied(7)
         unfolding Un_Diff  Un_assoc
       proof(rule arg_cong2[where f = union], goal_cases)
         case 2
         have helper: "r \<in> vset_to_set (right_neighbs l)"
           if "\<And> la lla. \<lbrakk>r \<in> vset_to_set (right_neighbs la);
                              w\<^sub>\<pi> ll r + off ll = w\<^sub>\<pi> lla r + off lla\<rbrakk>\<Longrightarrow>
                   la \<noteq> l \<and> la \<notin> set ls \<or> Some lla \<noteq> ben_lookup ben' r"
             "r \<in> vset_to_set (right_neighbs la)" "la \<in> set ls"
             " Some ll = ben_lookup (fst result) r" for r ll la
             using that
             by(cases "r \<notin> vset_to_set (right_neighbs l)") 
               (auto simp add: single_update(5))
           show ?case
             using single_update(5) 
             by (fastforce intro: helper)
         qed auto
       qed
     qed
   qed auto
   thus  "\<And> r k. (r, k) \<in> heap_abstract queue' \<Longrightarrow> ben_lookup ben' r \<noteq> None" 
        ?thesis1 ?thesis2 ?thesis4       
        "\<And> r l. ben_lookup ben' r = Some l \<Longrightarrow> (r, w\<^sub>\<pi> l r + off l) \<in> heap_abstract queue'"
        "\<And> r. r \<notin> \<Union> {vset_to_set (right_neighbs l)| l. l \<in> set ls} 
                 \<Longrightarrow> ben_lookup ben' r = ben_lookup ben r"
        "\<And> r. r \<in> \<Union> {vset_to_set (right_neighbs l)| l. l \<in> set ls} 
                 \<Longrightarrow> \<exists> l. ((l \<in> set ls \<and> r \<in> vset_to_set (right_neighbs l))
                             \<or> Some l = ben_lookup ben r) 
                          \<and> w\<^sub>\<pi> l r + off l = conn_min r \<and> ben_lookup ben' r = Some l"
    by (fast, auto)
 qed
(*TODO MOVE*)
lemma matchingI:
  "(\<And>e1 e2. \<lbrakk>e1 \<in> M; e2 \<in> M; e1 \<noteq> e2\<rbrakk> \<Longrightarrow> e1 \<inter> e2 = {}) \<Longrightarrow> matching M"
  by (auto simp: matching_def)

lemma \<M>_is_matching: "matching \<M>"
proof(rule matchingI, rule ccontr, goal_cases)
  case (1 e1 e2)
  obtain u v where uv: "buddy u = Some v" "e1 ={u, v}"
    using 1(1) by(force simp add: \<M>_def doubleton_eq_iff)
  obtain u' v' where u'v': "buddy u' = Some v'" "e2 ={u', v'}"
    using 1(2) by(force simp add: \<M>_def doubleton_eq_iff)
  have more_buddies: "buddy v = Some u" "buddy v' =  Some u'"
    using matching(1) uv(1) u'v'(1) by blast+
  then show ?case 
    using uv u'v' more_buddies 1(3,4)
    by auto
qed

lemma one_buddy_no_buddy_false: 
"\<lbrakk>Some v = buddy u;  None = buddy v\<rbrakk> \<Longrightarrow> False"
  using  matching(1)[of u v] by simp

lemma unmatched_lefts:
 "set (unmatched_lefts) = L - Vs \<M>"
 "length (unmatched_lefts) = card (L - Vs \<M>)"
proof-
  show  "set (unmatched_lefts) = L - Vs \<M>"
  proof(rule, all \<open>rule\<close>, goal_cases)
    case (1 x)
    then show ?case 
  using vset(6,7)[OF G(3) refl] 
  by(cases "buddy x")
    (auto elim!: vs_member_elim 
      intro: one_buddy_no_buddy_false 
      simp add: unmatched_lefts_def \<M>_def)
  next
    case (2 x)
    then show ?case 
    using vset(6,7)[OF G(3) refl] vs_member_intro[of "x" "{x, the (buddy x)}" \<M>]
    by(cases "buddy x")
      (fastforce intro: one_buddy_no_buddy_false 
      simp add: unmatched_lefts_def \<M>_def doubleton_eq_iff)+ 
qed
  thus "length unmatched_lefts = card (L - Vs \<M>)"
    using  distinct_card[of unmatched_lefts] distinct_filter[of unmatched_lefts]
           vset(6)[OF G(3) refl]
    by(auto simp add: unmatched_lefts_def) 
qed  

lemma unmatched_lefts_in_L: "set unmatched_lefts \<subseteq> L"
  using unmatched_lefts by simp

lemma to_list_left_is_L:"set (to_list left) = L"
  using G(3) vset(7) by blast

lemma M_verts_by_buddy:
 "x \<in> Vs \<M> \<Longrightarrow> buddy x \<noteq> None"
 "buddy x \<noteq> None \<Longrightarrow> x \<in> Vs \<M>"
proof(goal_cases)
  case 1
  then show ?case  
  using vset(6,7)[OF G(3) refl] 
  by(cases "buddy x")
    (auto elim!: vs_member_elim 
      intro: one_buddy_no_buddy_false 
      simp add: unmatched_lefts_def \<M>_def)
next
  case 2
  then obtain y where "buddy x = Some y"
    by auto
  hence "{x, y} \<in> \<M>"
    by(auto simp add: \<M>_def intro: exI[of _ x])
  then show ?case 
    by blast 
qed

lemma finite_G: "finite G" 
  by (metis G(1,4) List.finite_set finite_parts_bipartite_graph_invar graph_invar_finite
      to_list_left_is_L vset(7))

context
  assumes there_are_unmatched_lefts: "L -  Vs \<M> \<noteq> {}"
begin

lemma forest_roots:
"vset_invar forest_roots"
"vset_to_set forest_roots = L - Vs \<M>"
"vset_to_set forest_roots \<noteq> {}"
"finite (vset_to_set forest_roots)"
"vset_to_set forest_roots \<inter> Vs \<M> = {}"
proof-
  define vs where "vs = rev unmatched_lefts"
  have helper:
      "vset_invar (foldl (\<lambda>vset v. vset_insert v vset) vset_empty unmatched_lefts) \<and>
       vset_to_set (foldl (\<lambda>vset v. vset_insert v vset) vset_empty unmatched_lefts) = 
       set unmatched_lefts"
    unfolding foldl_conv_foldr vs_def[symmetric]
              set_rev[of unmatched_lefts, symmetric]
    by(induction vs)
      (auto simp add: vset(1-4))
  thus ths1and2:"vset_invar forest_roots" "vset_to_set forest_roots = L - Vs \<M>"
    using   M_verts_by_buddy
    by(force simp add: forest_roots_def unmatched_lefts_def 
                       conjunct2[OF helper, simplified unmatched_lefts_def] 
                       to_list_left_is_L[symmetric])+
  thus "vset_to_set forest_roots \<noteq> {}"
    using there_are_unmatched_lefts by auto
  show "finite (vset_to_set forest_roots)" 
    by (simp add: forest_roots_def helper)
  show "vset_to_set forest_roots \<inter> Vs \<M> = {}" 
    by (simp add: inf.commute ths1and2(2))
qed

lemmas props_of_init_heap_and_ben = 
update_best_even_neighbours_correct[OF best_even_neighbour(1) heap(1)
 unmatched_lefts_in_L, simplified best_even_neighbour heap(11),
 of "\<lambda> x. 0", simplified, folded init_best_even_neighbour_def]

lemma invars_init:
"invar_basic initial_state"
"invar_feasible_potential initial_state"
"invar_forest_tight initial_state"
"invar_matching_tight initial_state"
"invar_best_even_neighbour_heap initial_state"
"invar_best_even_neighbour_map initial_state"
proof(goal_cases)
  case 1
    have helper:"dom (ben_lookup (best_even_neighbour initial_state)) =
        {r | r l. r \<in> vset_to_set (right_neighbs l) \<and> l \<in> set unmatched_lefts}"
    proof(rule set_eqI, goal_cases)
      case (1 x)
      then show ?case 
      using  props_of_init_heap_and_ben(5,6)[OF surjective_pairing[symmetric], of x] 
      by (auto simp add: initial_state_def)+
     qed
  show ?case 
  proof(rule  invar_basicI, goal_cases)
    case 1
    then show ?case 
    using forest_roots
    by(auto intro!: empty_forest(4) 
          simp add: initial_state_def  \<M>_is_matching) 
  next
    case 2
    then show ?case  
    by(simp add: initial_state_def 
                 props_of_init_heap_and_ben(1,2)[OF surjective_pairing[symmetric]])     
  next
    case 3
    then show ?case 
    by(simp add: initial_state_def 
                 props_of_init_heap_and_ben(1,2)[OF surjective_pairing[symmetric]])
  next
    case 4
    then show ?case 
      by (simp add: initial_state_def missed(1))
  next
    case 5
    then show ?case 
      by (simp add: empty_forest(3) initial_state_def)
  next
    case 6
     show ?case 
       using G(6) unmatched_lefts_in_L
       by(auto simp add: helper)
  next
    case 7
     show ?case 
       by (simp add: domIff missed(2) primal_dual_path_search_spec.initial_state_def
           subset_iff)
  next
    case 8
    have helper:"fst ` heap_abstract (heap initial_state) =
        {r | r l. r \<in> vset_to_set (right_neighbs l) \<and> l \<in> set unmatched_lefts}"
    proof(rule, all \<open>rule\<close>, goal_cases)
      case (1 x)
      then show ?case 
        by(auto simp add: initial_state_def
            props_of_init_heap_and_ben(7)[OF surjective_pairing[symmetric]])
    next
      case (2 x)
      then obtain l where l: "l \<in> set unmatched_lefts" "x \<in> vset_to_set (right_neighbs l)"
        by blast
       obtain l where l: "l \<in> set unmatched_lefts" "x \<in> vset_to_set (right_neighbs l)"
              "ben_lookup (fst init_best_even_neighbour) x = Some l"
         using props_of_init_heap_and_ben(6)[OF surjective_pairing[symmetric], of x] l
                by blast
        then show ?case
            by(auto simp add: initial_state_def
               props_of_init_heap_and_ben(7)[OF surjective_pairing[symmetric]]
              intro!: image_eqI[of _ _ "(x, w\<^sub>\<pi> l x)"])
        qed
     show ?case 
       using G(6) unmatched_lefts_in_L
       by(auto simp add: helper)
   next
     case 9
     show ?case
       by(auto simp add: initial_state_def empty_forest(1) forest_roots(2))
   next
     case 10
     show ?case
       by (simp add: empty_forest(2) initial_state_def vset(2))
   qed
next
  case 2
  then show ?case 
    using G(8)
    by(auto intro!: invar_feasible_potentialI
          simp add:  initial_state_def working_potential_def missed(2) 
         abstract_real_map_def)
next
  case 3
  then show ?case 
    by(auto intro!: invar_forest_tightI
          simp add:  initial_state_def empty_forest(3))
next
  case 4
  then show ?case
    using matching(3)
    by(auto intro!: invar_matching_tightI
          simp add:  initial_state_def empty_forest(3)
                     working_potential_def empty_forest(1,2) missed(2)
                     abstract_real_map_def)
next
  case 5
  have help1: "(a, b) \<in> heap_abstract (snd init_best_even_neighbour) 
                  \<Longrightarrow> a \<in> Vs G" for a b
    by (auto intro: edges_are_Vs_2 
          simp add: G(6)[OF set_mp[OF unmatched_lefts_in_L]]
                    props_of_init_heap_and_ben(7)[OF surjective_pairing[symmetric]])
  have help2: "\<lbrakk>(a, b) \<in> heap_abstract (snd init_best_even_neighbour);
                a \<in> vset_to_set forest_roots\<rbrakk> \<Longrightarrow> False" for a b
    by(auto simp add: props_of_init_heap_and_ben(7)[OF surjective_pairing[symmetric]]
                      forest_roots(2) unmatched_lefts G(6) 
                dest: bipartite_edgeD(1)[OF _ G(1)])
  have help3: "(a, b) \<in> heap_abstract (snd init_best_even_neighbour) \<Longrightarrow>
           \<exists>l. b = w\<^sub>\<pi> l a \<and> ben_lookup (fst init_best_even_neighbour) a = Some l"
    for a b
    by(auto simp add: props_of_init_heap_and_ben(7)[OF surjective_pairing[symmetric]]
                      forest_roots(2) unmatched_lefts)
  have help4:"(a, w\<^sub>\<pi> l a) \<in> heap_abstract (snd init_best_even_neighbour)" 
    if "a \<in> Vs G" "a \<notin> vset_to_set forest_roots"
       "ben_lookup (fst init_best_even_neighbour) a = Some l" for a l
    using that
          props_of_init_heap_and_ben(5)[OF surjective_pairing[symmetric], of a]
    by(auto simp add: props_of_init_heap_and_ben(7)[OF surjective_pairing[symmetric]]
                      forest_roots(2) unmatched_lefts)
  show ?case 
    by(auto intro!: help1 help2 help3 help4 invar_best_even_neighbour_heapI
         simp add: initial_state_def missed(2) abstract_real_map_def
                   empty_forest(1,2) vset(2))
next
  case 6
  have helper1: False if
        "r \<in> Vs G"" r \<notin> vset_to_set forest_roots"
        "\<forall>l. l \<in> vset_to_set forest_roots \<longrightarrow> {l, r} \<notin> G"
        "r \<in> vset_to_set (right_neighbs l)" "l \<in> set unmatched_lefts" for r l
    using that by(simp add: G(6) forest_roots(2) unmatched_lefts(1))
  have helper2: "\<exists>l. ben_lookup (fst init_best_even_neighbour) r = Some l \<and>
               {r, l} \<in> G \<and> l \<in> vset_to_set forest_roots\<and>
               w\<^sub>\<pi> l r =
               Min {(w\<^sub>\<pi> l r) | l. l \<in> vset_to_set forest_roots \<and> {l, r} \<in> G}"
    if  "r \<in> Vs G" "r \<notin> vset_to_set forest_roots"
        "l \<in> vset_to_set forest_roots" "{l, r} \<in> G" for l r
  proof-
    have first_step:
     "\<exists>x. (\<exists>l. x = vset_to_set (right_neighbs l) \<and> l \<in> set unmatched_lefts) \<and> r \<in> x"
      using that unmatched_lefts(1) forest_roots(2)
      by(auto intro!: exI[of _ "vset_to_set (right_neighbs l)"] exI[of _ l]
             simp add:  G(6))
    then obtain l' where l': "l' \<in> set unmatched_lefts"
        "r \<in> vset_to_set (right_neighbs l')"
        "w\<^sub>\<pi> l' r =
        Min {w\<^sub>\<pi> l r | l. l \<in> set unmatched_lefts \<and> r \<in> vset_to_set (right_neighbs l)}"
        "ben_lookup (fst init_best_even_neighbour) r = Some l'"
      using props_of_init_heap_and_ben(6)[OF surjective_pairing[symmetric], of r] 
      by auto     
    then show ?thesis
      using G(6) forest_roots(2) unmatched_lefts(1)
      by (auto intro!: arg_cong[of _ _ Min] simp add: insert_commute)
   qed
   show ?case 
     by(force intro: invar_best_even_neighbour_mapI helper1 helper2
                     props_of_init_heap_and_ben(5)[OF surjective_pairing[symmetric]]
         simp add: initial_state_def missed(2) abstract_real_map_def
                   empty_forest(1,2) vset(2))
 qed
(*
lemma assumes "invar_basic state"
  shows "aevens state \<subseteq> L"
proof(rule, goal_cases)
  case (1 x)
  have "odd (length (get_path (forest state) x))"
       "last (get_path (forest state) x) \<in> vset_to_set (roots (forest state))"
       "walk_betw (\<F> state) x (get_path (forest state) x) (last (get_path (forest state) x))"
    using get_path[of \<M> "forest state" x, OF _ 1 refl] assms
    by(auto elim: invar_basicE)
  moreover hence "last (get_path (forest state) x) \<in> L"
    using assms apply(auto elim!: invar_basicE)

    
  thm bipartite_even_and_odd_walk(1)
  find_theorems bipartite 
  then show ?case 
    find_theorems evens get_path
next
  case 2
  then show ?case sorry
qed
*)
lemma invar_pres_one_step:
  assumes "search_path_cont_cond state"
          "invar_basic state"
          "invar_feasible_potential state"
          "invar_forest_tight state"
          "invar_matching_tight state"
          "invar_best_even_neighbour_heap state"
          "invar_best_even_neighbour_map state"
    shows "invar_basic (search_path_cont_upd state)"
          "invar_feasible_potential (search_path_cont_upd state)"
          "invar_forest_tight (search_path_cont_upd state)"
          "invar_matching_tight (search_path_cont_upd state)"
          "invar_best_even_neighbour_heap (search_path_cont_upd state)"
          "invar_best_even_neighbour_map (search_path_cont_upd state)"
proof-
define F where "F = forest state"
define ben where "ben = best_even_neighbour state"
  define missed_\<epsilon> where  "missed_\<epsilon> = missed_at state"
  obtain queue heap_min where queue_heap_min_def:
      " (queue, heap_min) = heap_extract_min (heap state)"
    by(cases "heap_extract_min (heap state)") auto
  obtain r where r_def: "heap_min = Some r"
   using queue_heap_min_def assms(1)
   by(auto elim: search_path_cont_condE)
  define l where "l = the (ben_lookup ben r)"
  define acc' where "acc' = w\<^sub>\<pi> l r + missed_\<epsilon> l"
  obtain l' where l'_def: "buddy r = Some l'"
   using queue_heap_min_def assms(1)
   by(auto elim: search_path_cont_condE simp add: r_def)
define missed' where "missed' = missed_upd (
                                    missed_upd (missed state) r acc') 
                                                l' acc'"
  obtain ben' queue' where ben'_queue'_def:
   "(ben', queue') = update_best_even_neighbour 
                                           (abstract_real_map (missed_lookup missed'))
                                           ben queue l'"
    using prod.collapse by blast
  define F' where "F'= extend_forest_even_unclassified F l r l'"
    define state' where "state' = state \<lparr> forest:= F', 
                            best_even_neighbour:=ben',
                            heap:=queue',
                            missed:=missed',
                            acc:= acc' \<rparr>"
    have upd_state_is_state':"search_path_cont_upd state =  state'"
      using ben'_queue'_def r_def l'_def queue_heap_min_def
     by(auto simp add: search_path_cont_upd_def state'_def Let_def
                       F'_def  missed'_def acc'_def l_def ben_def missed_\<epsilon>_def F_def
                split: option.split prod.split)
   obtain k where k: "(r, k) \<in> heap_abstract (heap state)"
        "\<And> x' k'. (x', k') \<in> heap_abstract (heap state) \<Longrightarrow> k \<le> k'"
     using r_def  pair_eq_fst_snd_eq[OF queue_heap_min_def]
           heap(5)[of "heap state" r] assms(2)
     by(auto elim!: invar_basicE)
   have r_unclassified: "r \<in> Vs G - aevens state - aodds state"
     using assms(6) k
     by (auto elim: invar_best_even_neighbour_heapE)
   have r_l_props: "{r, l} \<in> G" "l \<in> aevens state"
        "w\<^sub>\<pi> l r + missed_at state l =
         Min {w\<^sub>\<pi> l r + missed_at state l| l. l \<in> aevens state \<and> {l, r} \<in> G}"
     using assms(6,7) r_unclassified r_def  k(1) 
     by(fastforce elim!: invar_best_even_neighbour_mapE 
                    dest: invar_best_even_neighbour_heapD 
                simp add: l_def ben_def)+
   have k_is: "k = w\<^sub>\<pi> l r + missed_at state l"
     using assms(6) ben_def k(1) l_def
     by(fastforce dest: invar_best_even_neighbour_heapD)
   have r_l'_in_M:"{r, l'} \<in> \<M>"
     using \<M>_def l'_def by fastforce
   have l'_not_even:"l' \<in> vset_to_set (evens F) \<Longrightarrow> False"
   proof(goal_cases)
     case 1
     hence "{r, l'} \<in> abstract_forest F"
       using assms(2) evens_and_odds(3)[of \<M> F]  roots(2)[of \<M> F] higher_forest_properties(2)[OF  _ r_l'_in_M, of F] 
       by(auto elim!: invar_basicE dest!: 
            simp add: F_def)
     hence "r \<in> aevens state \<union> aodds state"
       using  assms(2) 1
       by(auto elim!: invar_basicE 
            simp add: F_def higher_forest_properties(3)  insert_commute)
     thus False
       using r_unclassified by blast
   qed
   have l'_not_even_or_odd:
      "l' \<in> vset_to_set (evens F) \<union>  vset_to_set (odds F) \<Longrightarrow> False"
   proof(goal_cases)
     case 1
     hence "{r, l'} \<in> abstract_forest F"
       using assms(2) evens_and_odds(3)[of \<M> F]  roots(2)[of \<M> F] higher_forest_properties(2)[OF  _ r_l'_in_M, of F] 
       by(auto elim!: invar_basicE dest!: 
            simp add: F_def)
     hence "r \<in> aevens state \<union> aodds state"
       using  assms(2) 1 higher_forest_properties(3)[of \<M> F]
       by(force elim!: invar_basicE 
            simp add: F_def   insert_commute)
     thus False
       using r_unclassified by blast
   qed
    have r_not_even_or_odd:
      "r \<in> vset_to_set (evens F) \<union>  vset_to_set (odds F) \<Longrightarrow> False"
   proof(goal_cases)
     case 1
     hence "{r, l'} \<in> abstract_forest F"
       using assms(2) evens_and_odds(3)[of \<M> F]  roots(2)[of \<M> F] higher_forest_properties(2)[OF  _ r_l'_in_M, of F] 
       by(auto elim!: invar_basicE dest!: 
            simp add: F_def)
     hence "r \<in> aevens state \<union> aodds state"
       using  assms(2) 1 higher_forest_properties(3)[of \<M> F]
       by(force elim!: invar_basicE 
            simp add: F_def   insert_commute)
     thus False
       using r_unclassified by blast
   qed
   have l_r_not_in_M:"{l, r} \<in> \<M> \<Longrightarrow> False" 
     using r_l_props(2) assms(2) higher_forest_properties(2,3)[of \<M> F l r] 
           r_not_even_or_odd evens_and_odds(3)[of \<M> F]
     by(auto elim!: invar_basicE simp add: F_def)
   have l_in_L:"l \<in> L"
     using  assms(2) r_l_props(2)
     by(auto elim!: invar_basicE)
   hence r_in_R: "r \<in> R"
     using G(1) bipartite_edgeD(3) l_in_L r_l_props(1) by fastforce
   moreover have r_l'_in_G:"{r, l'} \<in> G"
     using l'_def matching(2) by blast
   ultimately have l'_in_L: "l' \<in> L" 
     using   bipartite_edgeD(2)[OF _ G(1)]
     by(auto simp add: insert_commute)
   have queue'_is: "heap_abstract (fst (heap_extract_min (heap state))) =
         heap_abstract (heap state) - {(r, w\<^sub>\<pi> l r + missed_at state l)}"
     using assms(2) k(1) k_is
     by(intro heap(8))
       (auto elim!: invar_basicE 
          simp add: r_def[symmetric] pair_eq_fst_snd_eq[OF queue_heap_min_def])
   have forest_extension_precond: "forest_extension_precond F \<M> l r l'"
     using l'_not_even_or_odd r_not_even_or_odd l_r_not_in_M
     by(auto intro: forest_extension_precondI  
          simp add: F_def assms(2) invar_basicD(1) r_l_props(2)  r_l'_in_M)
   have update_best_even_neighbour_conditions:
        "ben_invar ben" "heap_invar queue" "l' \<in> L"
        "\<And>r k. (r, k) \<in> heap_abstract queue \<longrightarrow> ben_lookup ben r \<noteq> None"
        "\<And>r l. ben_lookup ben r = Some l \<longrightarrow>
          (r, w\<^sub>\<pi> l r + abstract_real_map (missed_lookup missed') l)
          \<in> heap_abstract queue"
   proof(goal_cases)
     case 1
     then show ?case 
      using assms(2) ben_def invar_basicD(2) by blast
   next
     case 2
     then show ?case 
       using heap(2)[OF invar_basicD(3)[OF  assms(2)]] queue_heap_min_def[symmetric] 
       by simp
   next
     case 3
     then show ?case 
       using l'_in_L by simp
   next
     case (4 rr k)
     then show ?case 
     using assms(2,6,7) 
     by(auto elim!: invar_best_even_neighbour_heapE
                    invar_best_even_neighbour_mapE invar_basicE
          simp add: ben_def pair_eq_fst_snd_eq[OF queue_heap_min_def] queue'_is)
     case (5 rr ll)
     show ?case 
     proof(rule, goal_cases)
       case 1
       hence "(rr, w\<^sub>\<pi> ll rr + abstract_real_map 
         (missed_lookup (missed state)) ll) \<in> heap_abstract queue"
     using assms(2,6,7) 
     apply(auto elim!: invar_best_even_neighbour_heapE
                    invar_best_even_neighbour_mapE invar_basicE
          simp add: ben_def pair_eq_fst_snd_eq[OF queue_heap_min_def] queue'_is missed'_def)
        apply blast
     
     
   qed
     using assms(2) ben_def invar_basicD(2) apply bla st
        apply (met is assms(2) fst_eqD heap(2) invar_basicD(3) queue_heap_min_def)
     using l'_in_L apply simp
     using assms(6,7)
     apply(au to elim!: invar_best_even_neighbour_heapE
invar_best_even_neighbour_mapE invar_basicE)
     sledgehammer
     by simp
   show "invar_basic (search_path_cont_upd state)"
     unfolding upd_state_is_state'
   proof(rule invar_basicI, goal_cases )
     case 1
     then show ?case 
       by(auto intro!: forest_extend(1) 
            simp add: state'_def F'_def forest_extension_precond)
   next
     case 2

     then show ?case
       using ben'_queue'_def
       apply(auto simp add: state'_def)
       using update_best_even_neighbour_correct(1)[OF _ _ _ _ _ ben'_queue'_def]
       find_theorems update_best_even_neighbour ben_invar
   next
     case 3
     then show ?case sorry
   next
     case 4
     then show ?case sorry
   next
     case 5
     then show ?case sorry
   next
     case 6
     then show ?case sorry
   next
     case 7
     then show ?case sorry
   next
     case 8
     then show ?case sorry
   qed



lemma add_to_pot_correct:
  assumes "potential_invar pot"
  shows   "potential_invar (add_to_pot pot x val)"
          "abstract_real_map (potential_lookup (add_to_pot pot x val)) =
          (\<lambda> y. abstract_real_map (potential_lookup pot) y + (if x = y then val else 0))"
           "abstract_real_map (potential_lookup (add_to_pot pot x val)) =
          (\<lambda> y. (if x = y then abstract_real_map (potential_lookup pot) y + val 
                          else abstract_real_map (potential_lookup pot) y))"
  using assms
  by(auto simp add: add_to_pot_def abstract_real_map_def potential(3) 
          split: option.split
          intro!: ext 
           intro: potential(2))

lemma update_best_even_neighbour_correct:
  assumes "ben_invar ben"
  shows   "ben_invar (update_best_even_neighbour pot ben l)" (is ?thesis1)
          "ben_lookup  (update_best_even_neighbour pot ben l) x = None \<Longrightarrow>
           ben_lookup ben x = None \<and> 
           \<not> (x \<in> vset_to_set right \<and> {l, x} \<in> G \<and> 
                  edge_slack pot l x \<le> best_even_neighbour_costs ben x)"
           (is "?asm2 \<Longrightarrow> ?thesis2")
          "ben_lookup  (update_best_even_neighbour pot ben l) x = Some (y, sl) \<Longrightarrow>
           {x, y} \<in> G \<and> slack pot x y = sl \<and> 
           (\<forall> y' sl'. (({x, y'} \<in> G \<and> sl' = slack pot x y') \<or>
                        ben_lookup ben x = Some (y', sl')) \<longrightarrow> sl \<le> sl')"
           (is "?asm3 \<Longrightarrow> ?thesis3")
proof-
  define f where "f =  (\<lambda> r ben. if in_G l r
                 then (if ereal (edge_slack pot l r)
                            < best_even_neighbour_ereal_costs ben r
                       then ben_upd ben r (l, edge_slack pot l r)
                       else ben)
                 else ben)"
  define rs where "rs = rev (to_list right)"
  have to_list_right: "rev (to_list right) = rs" "distinct rs" "vset_to_set right = set rs"
    using vset(6)[of right] by(auto simp add: rs_def G(4) intro!:vset(5))
  have invar_one_step: "ben_invar ben \<Longrightarrow> ben_invar (f r ben)" for r ben
      apply(subst f_def)
      by(auto intro: best_even_neighbour(2))
  have invar_iterated: "ben_invar ben \<Longrightarrow> ben_invar (foldr f rs ben)" for rs ben
  proof(induction rs arbitrary: ben)
    case (Cons a rs)
    show ?case 
      apply(subst foldr_Cons)
      apply(subst o_apply)
      by(auto simp add: Cons(2) intro!: Cons(1) invar_one_step best_even_neighbour(2))
  qed simp
  show ?thesis1
    unfolding update_best_even_neighbour_def foldl_conv_foldr
       f_def[symmetric] 
    by(auto intro: invar_iterated assms)
  have non_none_stays_non_none:
     "\<lbrakk>ben_invar ben; ben_lookup ben x \<noteq> None\<rbrakk> \<Longrightarrow> ben_lookup (f rs ben) x \<noteq> None" for rs ben x
      apply(subst  f_def)
      by(auto split: if_split 
           simp add:  best_even_neighbour(3)
             intro!: best_even_neighbour(2))
  have non_none_stays_non_none_list:
     "\<lbrakk>ben_invar ben; ben_lookup ben x \<noteq> None\<rbrakk> \<Longrightarrow> ben_lookup (foldr f rs ben) x \<noteq> None" for rs ben x
  proof(induction rs arbitrary: ben)
    case (Cons a rs)
    show ?case
      apply(subst foldr_Cons)
      apply(subst o_apply)
      apply(rule non_none_stays_non_none)
       apply (simp add: Cons.prems(1) invar_iterated)
      by (simp add: Cons.IH Cons.prems(1,2))
  qed simp

  have None_one_step: 
    " ben_lookup ben x = None"
       "x = a \<Longrightarrow> \<not> ({l, x} \<in> G \<and> edge_slack pot l x \<le> best_even_neighbour_costs ben x)" if 
    "ben_invar ben""ben_lookup (f a ben) x = None"for ben a x
    using that
    apply(all \<open>cases "in_G l a"\<close>)
    apply(all \<open>cases "ereal (edge_slack pot l a) < best_even_neighbour_ereal_costs ben a"\<close>)
    apply(all \<open>cases "x = a"\<close>)
    by(auto simp add: f_def best_even_neighbour(3) G(2) best_even_neighbour_ereal_costs_def)
  have same_costs_not_in: "\<lbrakk> ben_invar ben; a \<notin> set rs; distinct rs\<rbrakk> 
 \<Longrightarrow> best_even_neighbour_costs (foldr f rs ben) a = 
     best_even_neighbour_costs ben a" for a ben
  proof(induction rs)
    case (Cons r rs)
    hence "best_even_neighbour_costs (ben_upd (foldr f rs ben) r (l, edge_slack pot l r)) a
           = best_even_neighbour_costs  (foldr f rs ben) a"
      by(auto simp add: best_even_neighbour_costs_def best_even_neighbour(3)  invar_iterated[OF Cons(2), of rs])

    show ?case 
    apply(subst foldr_Cons, subst o_apply)
      apply(subst f_def)
      apply(cases "a = r")
      using Cons(3)
       apply(auto split: if_split option.split)



    find_theorems ben_upd ben_lookup

  show  "?asm2 \<Longrightarrow> ?thesis2"
 unfolding update_best_even_neighbour_def foldl_conv_foldr
       f_def[symmetric] to_list_right(1,3)
  using assms 
proof(induction rs arbitrary: ben)
  case (Cons a rs)
  have ex_unfold:"\<not> (x \<in> set (a # rs) \<and> {l, x} \<in> G \<and>
        edge_slack pot l x \<le> best_even_neighbour_costs ben x) \<longleftrightarrow>
       (\<not> (x \<in> set rs \<and> {l, x} \<in> G \<and>
        edge_slack pot l x \<le> best_even_neighbour_costs ben x) \<and>
          (x = a \<longrightarrow> \<not> ({l, x} \<in> G \<and> 
              edge_slack pot l x \<le> best_even_neighbour_costs ben x)))"
    by auto
  have ben_invar_later: "ben_invar ((foldr f rs ben) )"
    by (simp add: assms invar_iterated Cons(3))
 (* have lookup_after_f_None: "ben_lookup (f a ben) x = None"
    unfolding f_def
    apply(auto simp add: best_even_neighbour(3) Cons(3) best_even_neighbour_ereal_costs_def 
split: if_split option.split)





    using non_none_stays_non_none_list[of ben x "a#rs"]
    using Cons.prems(1,2) ben_invar_later
           best_even_neighbour(3)
        fun_upd_other map_upd_Some_unfold
None_one_step(1)[of "foldr f rs ben" a x]

   
    unfolding f_def best_even_neighbour_ereal_costs_def  comp_apply  foldr_Cons 
 
    


    by (smt (verit, ccfv_SIG))*)
  show ?case 
    unfolding  ex_unfold 
    unfolding conj_assoc[symmetric]
    apply rule
    subgoal
       unfolding conj_assoc
      apply(rule Cons(1))
      using Cons(2)
      by (auto intro: None_one_step(1) ben_invar_later Cons(3))
    subgoal
      unfolding conj_assoc
      apply rule
      using None_one_step(2)[of "foldr f rs ben" a x]
      apply (simp add: Cons.prems(2))
    
      apply (smt (verit) Cons.prems(1)
          \<open>ben_lookup ben x = None \<and> \<not> ((x \<in> set rs \<and> {l, x} \<in> G) \<and> edge_slack pot l x \<le> best_even_neighbour_costs ben x)\<close>
          ben_invar_later best_even_neighbour(3) comp_apply f_def foldr_Cons fun_upd_def
          not_Some_eq primal_dual_path_search_spec.best_even_neighbour_ereal_costs_def)
      by simp
    done
qed auto


      apply(rule Suc(1))
      subgoal
        using Suc(2)[simplified rs_is(1)]
        apply(subst (asm) foldl_Cons)
        apply(subst (asm) (2) f_def)
        apply(all \<open>cases "in_G a r"\<close>)
        apply(all \<open>cases "ereal (edge_slack pot a r) < best_even_neighbour_ereal_costs ben r"\<close>)
           apply auto
        term fold

    unfolding 
    using conjunct1[OF Suc(1), of ben]
    unfolding foldl_Cons
    using non_none_stays_non_none
    using conjunct1[OF Suc(1), of ben]

    using non_none_stays_non_none[of]
       apply(au to simp add: f_def)
    using non_none_stays_non_none
    
   
qed auto

    find_theorems to_list

















  oops

    and best_even_neighb_empty::"'ben"
    and best_even_neighb_upd::"'ben \<Rightarrow> 'v \<Rightarrow> ('v \<times> real) \<Rightarrow> 'ben"
    and best_even_neighb_lookup::"'ben \<Rightarrow> 'v \<Rightarrow> ('v \<times> real)"

   and vset_empty::'vset
   and vset_insert::"'v \<Rightarrow> 'vset \<Rightarrow>'vset"
   and vset_invar::"'vset \<Rightarrow> bool"
   and vset_set::"'vset \<Rightarrow> 'v set"
   and vset_diff::"'vset \<Rightarrow> 'vset \<Rightarrow> 'vset"
   and vset_inter::"'vset \<Rightarrow> 'vset \<Rightarrow> 'vset"
   and g_neighb::"'gimpl \<Rightarrow> 'v \<Rightarrow> 'vset option"
   and g_add_edge::"'gimpl \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'gimpl"
   and g_empty::"'gimpl"
   and forest_abstract::"'forest \<Rightarrow> 'v set set"
   and forest_invar::"'forest \<Rightarrow> bool"
   and empty_forest::"'forest"
   and slack_empty::'slack
   and slack_lookup::"'slack \<Rightarrow> 'v \<Rightarrow> (real \<times> 'vset ) option"
   and slack_upd::"'v \<Rightarrow> (real \<times> 'vset) \<Rightarrow> 'slack \<Rightarrow> 'slack"
   and slack_invar::"'slack \<Rightarrow> bool"
   and potential_upd::"'potential \<Rightarrow> 'v \<Rightarrow> real \<Rightarrow> 'potential"
   and potential_lookup::"'potential \<Rightarrow> 'v \<Rightarrow> real option"
   and potential_invar::"'potential \<Rightarrow> bool"
   and initial_pot::"'potential"
   and edge_costs::"'v \<Rightarrow> 'v \<Rightarrow> real"
   and left::'vset
   and right::'vset
   and right_neighbs::"'v \<Rightarrow> 'vset option"
   (*and iterate_vset_slack::"('v \<Rightarrow> 'slack \<Rightarrow> 'slack) \<Rightarrow> 'vset \<Rightarrow> 'slack \<Rightarrow> 'slack"*)
   and vset_flatten::"'vset \<Rightarrow> 'v list"

begin

definition "right_neighb_abstract v = (case right_neighbs v of None \<Rightarrow> {}
                                       | Some vs \<Rightarrow> vset_set vs)"

lemma reight_neighb_abstract_applied:
 "right_neighbs v = None \<Longrightarrow> right_neighb_abstract v = {}"
 "right_neighbs v =  Some vs \<Longrightarrow> right_neighb_abstract v = vset_set vs"
  by(auto simp add: right_neighb_abstract_def)

definition "edge_slack pot x y = 
    edge_costs x y 
     - abstract_real_map (potential_lookup pot) x
     - abstract_real_map (potential_lookup pot) y"

definition "add_to_pot pot x val = 
           (case potential_lookup pot x of 
             None \<Rightarrow> potential_upd pot x val 
             | Some val' \<Rightarrow> potential_upd pot x (val + val'))"

(*
definition "initial_slack pot = 
   iterate_vset_slack
    (\<lambda> u slacks. case right_neighbs u of None => slacks
               |  Some vs \<Rightarrow> 
      iterate_vset_slack
        (\<lambda> v slacks. case slack_lookup slacks v of 
             None \<Rightarrow> slack_upd slacks v
            (edge_slack pot u v) (vset_insert u vset_empty)
             | Some (svalue, tights) \<Rightarrow>
              (let uvsvalue = edge_slack pot u v in
               (if uvsvalue < svalue then
                  slack_upd slacks v
                  (edge_slack pot u v) (vset_insert u vset_empty)
                else if uvsvalue =  svalue then
                  slack_upd slacks v svalue
                   (vset_insert u tights)
                else slacks)))
                vs slacks)
             left slack_empty"
*)
term arg_max
definition "new_slacks slacks pot new_left = 
   foldr
    (\<lambda> u slacks. case right_neighbs u of None => slacks
               |  Some vs \<Rightarrow> 
      foldr
        (\<lambda> v slacks. case slack_lookup slacks v of 
             None \<Rightarrow> slack_upd  v
            ((edge_slack pot u v), (vset_insert u vset_empty)) slacks
             | Some (svalue, tights) \<Rightarrow>
              (let uvsvalue = edge_slack pot u v in
               (if uvsvalue < svalue then
                  slack_upd v (uvsvalue, (vset_insert u vset_empty))  slacks 
                else if uvsvalue =  svalue then
                  slack_upd  v (svalue, (vset_insert u tights)) slacks
                else slacks)))
                (vset_flatten vs) slacks)
             (vset_flatten new_left) slacks"

definition "abstract_min_slack slck = 
            (\<lambda> v. (case slack_lookup slck v of 
                   None \<Rightarrow> PInfty
                   | Some (sl, vs) \<Rightarrow> sl))"

definition "abstract_min_slack_edges slck = 
            (\<lambda> u. (case slack_lookup slck u of 
                   None \<Rightarrow> {}
                   | Some (sl, vs) \<Rightarrow> {(u, v) | v. v \<in> vset_set vs}))"

definition "new_tights slacks rights= 
            (foldr
            (\<lambda> u (sl, edges). 
                (case slack_lookup slacks u of None \<Rightarrow> (sl, edges)
                | Some (sla, vs) \<Rightarrow>
                  if sla > sl then (sl, edges)
                  else if sla = sl then 
                  (sl, foldr (\<lambda> v edges. (u, v)#edges) (vset_flatten vs) edges)
                  else (sla, foldr (\<lambda> v edges. (u, v)#edges) (vset_flatten vs) [])
            )                  
            ) (vset_flatten rights) (PInfty, []))"

definition "initial_state = 
\<lparr>new_to_left_seen= left,
forest=empty_forest,
seen = left,
slack = slack_empty,
potential = initial_pot,
tight_graph = g_empty\<rparr>"


function (domintros) primal_dual_path_search::
"('forest, 'vset, 'slack, 'potential, 'gimpl) primal_dual_state \<Rightarrow>
('v list \<times> 'potential) option" where
"primal_dual_path_search state =
(let F = forest state; Z = seen state; newZleft = new_to_left_seen state;
     pot = potential state; slacks = slack state;
     new_slack = new_slacks slacks pot newZleft;
     Gt = tight_graph state;
     (\<epsilon>, new_tight_edges) = new_tights new_slack (vset_diff right Z)
in ( if \<epsilon> = PInfty then None
     else (let new_pot1 = foldr (\<lambda> v p. add_to_pot p v (real_of_ereal \<epsilon>)) 
                                 (vset_flatten (vset_inter Z left)) pot;
                 new_pot2 = foldr (\<lambda> v p. add_to_pot p v (- real_of_ereal \<epsilon>)) 
                                 (vset_flatten (vset_inter Z right)) new_pot1;
                 Gt' = foldr (\<lambda> e G. g_add_edge G (fst e) (snd e))
                     new_tight_edges Gt;
               newF = get_path_or_extend_forest Gt' Z newZleft F buddy
           in (case newF of 
                    Path P \<Rightarrow> Some (P, new_pot2)
                  | Forest newZ F' => 
                      let newZleft' = vset_inter (vset_diff newZ Z) left;
                          state' = state \<lparr>new_to_left_seen := newZleft', forest := F', seen := newZ,
                                          slack := new_slack, potential := new_pot2, tight_graph :=Gt' \<rparr>
                       in primal_dual_path_search state'))))"
  by pat_completeness auto


end

locale primal_dual_path_search_reasoning = primal_dual_path_search_spec +
vset_set_specs: Set2 vset_empty vset_delete vset_isin vset_set vset_invar vset_insert
vset_union vset_inter vset_diff +
slack_map: Map slack_empty slack_upd slack_del slack_lookup slack_invar
for vset_delete vset_isin vset_union slack_del
+
assumes vset_flatten: "vset_invar vs \<Longrightarrow> set (vset_flatten vs) = vset_set vs"
                      "vset_invar vs \<Longrightarrow> distinct (vset_flatten vs)"
and    reight_neighbs: "\<And> vs. right_neighbs v = Some vs \<Longrightarrow> vset_invar vs"
begin

lemma abstract_min_slack_upd:
"slack_invar slacks \<Longrightarrow>
   abstract_min_slack (slack_upd v (val, vs) slacks) = 
    (\<lambda> u. if u = v then val else abstract_min_slack slacks u)"
  by(auto intro!: ext 
        simp add: abstract_min_slack_def  slack_map.map_update 
           split: option.split)

lemma abstract_min_slack_edges_upd:
"slack_invar slacks \<Longrightarrow>
   abstract_min_slack_edges (slack_upd v (val, vs) slacks) = 
    (\<lambda> v'. if v' = v then {(v, u) | u. u \<in> vset_set vs} else abstract_min_slack_edges slacks v')"
  apply(auto intro!: ext 
        simp add: abstract_min_slack_edges_def slack_map.map_update  
       simp only: abstract_min_slack_edges_def
           split: option.split if_split)
       apply (simp add: slack_map.map_update)+
   apply (metis (lifting) emptyE option.distinct(1) option.simps(4))
  by (smt (verit, ccfv_threshold) case_prod_conv map_upd_Some_unfold mem_Collect_eq option.simps(5)
      slack_map.map_update)


definition "good_slacks sf A B slcks = 
    ((\<forall> v \<in> B. (abstract_min_slack slcks v = 
          Inf {ereal (sf u v) | u. v \<in> right_neighb_abstract u \<and> u \<in> A}) \<and>
          (abstract_min_slack_edges slcks v = 
          {(v, u) | u. is_arg_min (\<lambda> u. sf u v) (\<lambda> u. v \<in> right_neighb_abstract u \<and> u \<in> A) u}))
     \<and> finite A \<and> finite B)"


lemma good_slacksI:
"(\<And> v. v \<in> B \<Longrightarrow> (abstract_min_slack slcks v = 
          Inf {ereal (sf u v) | u. v \<in> right_neighb_abstract u \<and> u \<in> A})) \<Longrightarrow>
 (\<And> v. v \<in> B \<Longrightarrow>
          (abstract_min_slack_edges slcks v = 
          {(v, u) | u. is_arg_min (\<lambda> u. sf u v) (\<lambda> u. v \<in> right_neighb_abstract u \<and> u \<in> A) u})) 
\<Longrightarrow> finite A \<Longrightarrow> finite B 
\<Longrightarrow> good_slacks sf A B slcks"
and good_slacksI':
"(\<And> v. v \<in> B \<Longrightarrow> (abstract_min_slack slcks v = 
          Inf {ereal (sf u v) | u. v \<in> right_neighb_abstract u \<and> u \<in> A}) \<and>
           (abstract_min_slack_edges slcks v = 
          {(v, u) | u. is_arg_min (\<lambda> u. sf u v) (\<lambda> u. v \<in> right_neighb_abstract u \<and> u \<in> A) u}))
 \<Longrightarrow>finite A \<Longrightarrow> finite B  
\<Longrightarrow> good_slacks sf A B slcks"
and good_slacksE:
"good_slacks sf A B slcks \<Longrightarrow>
 ((\<And> v. v \<in> B \<Longrightarrow> (abstract_min_slack slcks v = 
          Inf {ereal (sf u v) | u. v \<in> right_neighb_abstract u \<and> u \<in> A})) \<Longrightarrow>
 (\<And> v. v \<in> B \<Longrightarrow>
          (abstract_min_slack_edges slcks v = 
          {(v, u) | u. is_arg_min (\<lambda> u. sf u v) (\<lambda> u. v \<in> right_neighb_abstract u \<and> u \<in> A) u})) 
\<Longrightarrow>finite A \<Longrightarrow> finite B \<Longrightarrow> P) \<Longrightarrow> P"
and good_slacksD:
"good_slacks sf A B slcks \<Longrightarrow>
  v \<in> B \<Longrightarrow> abstract_min_slack slcks v = 
          Inf {ereal (sf u v) | u. v \<in> right_neighb_abstract u \<and> u \<in> A}"
"good_slacks sf A B slcks \<Longrightarrow>
  v \<in> B \<Longrightarrow> abstract_min_slack_edges slcks v = 
          {(v, u) | u. is_arg_min (\<lambda> u. sf u v) (\<lambda> u. v \<in> right_neighb_abstract u \<and> u \<in> A) u}"
"good_slacks sf A B slcks \<Longrightarrow> finite A" "good_slacks sf A B slcks \<Longrightarrow> finite B"
  by(auto simp add: good_slacks_def)

definition "good_slacks_general sf A B E slcks = 
    ((\<forall> v \<in> B. (abstract_min_slack slcks v = 
          Inf {ereal (sf u v) | u. (u, v) \<in> E \<and> u \<in> A}) \<and>
          (abstract_min_slack_edges slcks v = 
          {(v, u) | u. is_arg_min (\<lambda> u. sf u v) (\<lambda> u. (u, v) \<in> E \<and> u \<in> A) u}))
     \<and> finite A \<and> finite B \<and> fst ` E \<subseteq> A)"

lemma good_slacks_generalI:
"(\<And> v. v \<in> B \<Longrightarrow> (abstract_min_slack slcks v = 
          Inf {ereal (sf u v) | u. (u, v) \<in> E \<and> u \<in> A})) \<Longrightarrow>
 (\<And> v. v \<in> B \<Longrightarrow>
          (abstract_min_slack_edges slcks v = 
          {(v, u) | u. is_arg_min (\<lambda> u. sf u v) (\<lambda> u. (u, v) \<in> E \<and> u \<in> A) u})) 
\<Longrightarrow> finite A \<Longrightarrow> finite B  \<Longrightarrow> fst ` E \<subseteq> A
\<Longrightarrow> good_slacks_general sf A B E slcks"
and good_slacks_generalI':
"(\<And> v. v \<in> B \<Longrightarrow> (abstract_min_slack slcks v = 
          Inf {ereal (sf u v) | u. (u, v) \<in> E \<and> u \<in> A}) \<and>
           (abstract_min_slack_edges slcks v = 
          {(v, u) | u. is_arg_min (\<lambda> u. sf u v) (\<lambda> u. (u, v) \<in> E \<and> u \<in> A) u}))
 \<Longrightarrow>finite A \<Longrightarrow> finite B  \<Longrightarrow> fst ` E \<subseteq> A
\<Longrightarrow> good_slacks_general sf A B E slcks"
and good_slacks_generalE:
"good_slacks_general sf A B E slcks \<Longrightarrow>
 ((\<And> v. v \<in> B \<Longrightarrow> (abstract_min_slack slcks v = 
          Inf {ereal (sf u v) | u. (u, v) \<in> E \<and> u \<in> A})) \<Longrightarrow>
 (\<And> v. v \<in> B \<Longrightarrow>
          (abstract_min_slack_edges slcks v = 
          {(v, u) | u. is_arg_min (\<lambda> u. sf u v) (\<lambda> u. (u, v) \<in> E \<and> u \<in> A) u})) 
\<Longrightarrow>finite A \<Longrightarrow> finite B \<Longrightarrow> fst ` E \<subseteq> A\<Longrightarrow> P) \<Longrightarrow> P"
and good_slacks_generalD:
"good_slacks_general sf A B E slcks \<Longrightarrow>
  v \<in> B \<Longrightarrow> abstract_min_slack slcks v = 
          Inf {ereal (sf u v) | u. (u, v) \<in> E \<and> u \<in> A}"
"good_slacks_general sf A B E slcks \<Longrightarrow>
  v \<in> B \<Longrightarrow> abstract_min_slack_edges slcks v = 
          {(v, u) | u. is_arg_min (\<lambda> u. sf u v) (\<lambda> u. (u, v) \<in> E \<and> u \<in> A) u}"
"good_slacks_general sf A B E slcks \<Longrightarrow> finite A"
 "good_slacks_general sf A B E slcks \<Longrightarrow> finite B"
"good_slacks_general sf A B E slacks \<Longrightarrow> fst ` E \<subseteq> A"
  by(auto simp add: good_slacks_general_def)

lemma good_slacks_general_extended_lonely_left:
"good_slacks_general sf A B E slcks \<Longrightarrow> \<nexists> b. (a, b) \<in> E \<Longrightarrow>
good_slacks_general sf (insert a A) B E slcks"
  by(auto intro!: good_slacks_generalI arg_cong[of _ _  Inf]
                  arg_cong[of _ _  "\<lambda> x. is_arg_min _ x _"]
         elim!: good_slacks_generalE
      simp add: is_arg_min_def)

lemma good_slacks_good_slacks_general: 
"good_slacks sf A B slcks \<Longrightarrow> 
  good_slacks_general sf A B {(u, v) | u v. v \<in> right_neighb_abstract u \<and> u \<in> A} slcks"
"good_slacks_general sf A B {(u, v) | u v. v \<in> right_neighb_abstract u \<and> u \<in> A} slcks
 \<Longrightarrow> good_slacks sf A B slcks"
"good_slacks sf A B slcks \<longleftrightarrow>
    good_slacks_general sf A B {(u, v) | u v. v \<in> right_neighb_abstract u \<and> u \<in> A} slcks"
  by(auto intro!: good_slacks_generalI  good_slacksI
           elim!: good_slacksE good_slacks_generalE)


(*TODO MOVE*)
lemma P_of_min_E: "P (min (a::real) b) \<Longrightarrow>(a \<le> b \<Longrightarrow> P a \<Longrightarrow> Q) \<Longrightarrow> (a \<ge> b \<Longrightarrow> P b \<Longrightarrow> Q) \<Longrightarrow> Q"
  by(cases "a \<le> b") auto

definition "slack_basic_invar slacks = (slack_invar slacks \<and> 
                 (\<forall> v sl vs. slack_lookup slacks v = Some (sl, vs) \<longrightarrow> vset_invar vs))"

lemma slack_basic_invarE:
"slack_basic_invar slacks \<Longrightarrow>
(slack_invar slacks \<Longrightarrow>
 (\<And> v sl vs. slack_lookup slacks v = Some (sl, vs) \<Longrightarrow> vset_invar vs) \<Longrightarrow> P) \<Longrightarrow> P "
and slack_basic_invarI: "slack_invar slacks \<Longrightarrow>
 (\<And> v sl vs. slack_lookup slacks v = Some (sl, vs) \<Longrightarrow> vset_invar vs) 
\<Longrightarrow>  slack_basic_invar slacks"
and slack_basic_invarD:
"slack_basic_invar slacks \<Longrightarrow> slack_invar slacks"
"slack_basic_invar slacks \<Longrightarrow>  slack_lookup slacks v = Some (sl, vs) \<Longrightarrow> vset_invar vs"
  by(auto simp add: slack_basic_invar_def)

(*TODO MOVE*)
lemma P_of_minI:"((a::('z::linorder)) \<le> b \<Longrightarrow> P a) \<Longrightarrow> (b \<le> a \<Longrightarrow> P b) \<Longrightarrow> P (min a b)"
  by(cases "a \<le> b") auto

lemma new_slack_good_slacks_pres:
  assumes "slack_basic_invar slacks" "vset_invar new_left"
      and "good_slacks (\<lambda> u v. edge_slack pot u v) A B slacks"
          "A \<inter> vset_set new_left = {}"
  shows   "good_slacks (\<lambda> u v. edge_slack pot u v) (A \<union> vset_set new_left)
           B (new_slacks slacks pot new_left)"
          "slack_basic_invar (new_slacks slacks pot new_left)"
          "dom (slack_lookup (new_slacks slacks pot new_left)) = 
           dom (slack_lookup slacks) \<union> \<Union> (right_neighb_abstract ` vset_set new_left)"
proof-
  note new_left_flattened = vset_flatten[OF assms(2)]
  define flat_new_left where "flat_new_left = vset_flatten new_left"
  define inner where "inner  = (\<lambda>u v slacks.
                    case slack_lookup slacks v of
                    None \<Rightarrow> slack_upd v ((edge_slack pot u v), (vset_insert u vset_empty)) slacks
                    | Some (svalue, tights) \<Rightarrow>
                        let uvsvalue = edge_slack pot u v
                        in if uvsvalue < svalue
                           then slack_upd v (uvsvalue, (vset_insert u vset_empty)) slacks
                           else if uvsvalue = svalue
                                then slack_upd v (svalue, (vset_insert u tights)) slacks
                            else slacks)"
  define outer where "outer = (\<lambda>u slacks.
                case right_neighbs u of None \<Rightarrow> slacks
                | Some vs \<Rightarrow> foldr (inner u) (vset_flatten vs) slacks)"
  have effect_inner:"good_slacks_general (edge_slack pot) (insert u A) B (insert (u, v) E)
     (inner u v slacks) \<and>
      slack_basic_invar (inner u v slacks) \<and>
      dom (slack_lookup (inner u v slacks)) =
      insert v (dom (slack_lookup slacks))" 
    if "slack_basic_invar slacks"  "good_slacks_general (edge_slack pot) A B E slacks"
     for u v A B E slacks
    proof(rule conjI[OF _ conjI], goal_cases)
      case 1
      note one = this
      then show ?case 
      proof(rule  good_slacks_generalI', goal_cases)
        case (1 va)
        note one' = this
        show ?case
        proof(cases "va = v")
          case True
          show ?thesis 
        proof(cases "slack_lookup slacks v")
          case None
          have helper1: "(\<And> u. (u, v) \<in> E \<Longrightarrow> u \<notin> A) \<Longrightarrow>
                  ereal (edge_slack pot u v) =
                  min (ereal (edge_slack pot u v))
                   (min (Inf {uu. uu = ereal (edge_slack pot u v) \<and> (u, v) \<in> E})
                   (Inf {ereal (edge_slack pot ua v) |ua. (ua = u \<or> (ua, v) \<in> E) \<and> ua \<in> A}))" 
          apply(rule P_of_minI)
          apply simp
          apply(rule P_of_minI)
          by (auto simp add: Inf_less_iff less_eq_ereal_def)
        show ?thesis 
          using good_slacks_generalD(1,2)[OF that(2) one', symmetric] one' True
          by(auto simp add: inner_def None  (*set_is_on_v*) abstract_min_slack_def
                  abstract_min_slack_edges_def is_arg_min_def   vset_set_specs.set_empty
                  abstract_min_slack_upd[OF slack_basic_invarD(1)[OF that(1)]] True
                  abstract_min_slack_edges_upd[OF slack_basic_invarD(1)[OF that(1)]]
                  vset_set_specs.set_insert[OF vset_set_specs.invar_empty] 
                              slack_map.map_update[OF slack_basic_invarD(1)[OF that(1)]]
                  Inf_eq_PInfty conj_disj_distribL ex_disj_distrib Collect_disj_eq 
                  complete_lattice_class.Inf_union_distrib 
                  intro!: helper1)
      next
        case (Some vs)
        then show ?thesis 
        proof(cases vs, goal_cases)
          case (1 sl vs) (*TODO generalise and move*)
          have inf_ereal_find_inf:"Inf {ereal (edge_slack pot u v) |u. v \<in> right_neighb_abstract u \<and> u \<in> A} = ereal sl
                \<Longrightarrow> \<exists> u. v \<in> right_neighb_abstract u \<and> u \<in> A \<and> sl = (edge_slack pot u v)"
          proof(cases "\<exists> u. v \<in> right_neighb_abstract u \<and> u \<in> A", goal_cases)
            case 1
            have " ereal sl \<in> {ereal (edge_slack pot u v) |u. v \<in> right_neighb_abstract u \<and> u \<in> A}"
              unfolding 1(1)[symmetric]
              apply(subst complete_linorder_class.Min_Inf[symmetric])
              using good_slacks_generalD(3)[OF that(2)] 1(2) 
              by(intro linorder_class.Min_in | simp)+
            thus ?case by auto
          next
            case 2
            hence emp:"{ereal (edge_slack pot u v) |u. v \<in> right_neighb_abstract u \<and> u \<in> A} =  {}" by auto
            show ?case
              using 2(1)[simplified emp] 
              by(simp add: complete_lattice_class.Inf_empty top_ereal_def)
          qed
          have help1: 
        "\<lbrakk>Inf {ereal (edge_slack pot u v) |u. v \<in> right_neighb_abstract u \<and> u \<in> A} =
          ereal (edge_slack pot ua v); v \<in> right_neighb_abstract y;
            edge_slack pot y v < edge_slack pot ua v; y \<in> A \<rbrakk> \<Longrightarrow> False" 
        and help3: 
         " \<lbrakk>Inf {ereal (edge_slack pot u v) |u. v \<in> right_neighb_abstract u \<and> u \<in> A} =
            ereal (edge_slack pot ua v); edge_slack pot u v < edge_slack pot ua v;
            v \<in> right_neighb_abstract y; edge_slack pot y v < edge_slack pot u v;
             y \<in> A ; v \<in> right_neighb_abstract u\<rbrakk> \<Longrightarrow> False"
        for ua y
            by (smt (verit, del_insts) Inf_less_iff less_ereal.simps(1) mem_Collect_eq)+
          have help2:
          "\<lbrakk> {(v, va) |va. va \<in> vset_set vs} =
           {(v, u) |u. v \<in> right_neighb_abstract u \<and> u \<in> A \<and>
           (\<forall>y. y \<in> A \<longrightarrow> v \<in> right_neighb_abstract y \<longrightarrow> \<not> edge_slack pot y v < edge_slack pot u v)};
            v \<in> right_neighb_abstract uaa ;  \<forall>y. v \<in> right_neighb_abstract y \<longrightarrow>
           y \<noteq> u \<and> y \<notin> A \<or> \<not> edge_slack pot y v < edge_slack pot uaa v ; uaa \<in> A ; uaa \<notin> vset_set vs\<rbrakk>
             \<Longrightarrow> uaa = u" for ua uaa
            by (smt (verit) mem_Collect_eq prod.inject) 
          have help4:
            "\<lbrakk>Inf {ereal (edge_slack pot u v) |u. v \<in> right_neighb_abstract u \<and> u \<in> A} =
               ereal (edge_slack pot ua v); edge_slack pot u v < edge_slack pot ua v;
               v \<in> right_neighb_abstract uaa ; \<forall>y. v \<in> right_neighb_abstract y \<longrightarrow>
               y \<noteq> u \<and> y \<notin> A \<or> \<not> edge_slack pot y v < edge_slack pot uaa v;
              uaa \<in> A; v \<in> right_neighb_abstract u \<rbrakk> \<Longrightarrow> uaa = u" for ua uaa
            by (smt (verit, ccfv_SIG) Inf_less_iff less_ereal.simps(1) mem_Collect_eq)
          have help1: 
        "Inf {ereal (edge_slack pot u v) |u. (u, v) \<in> E \<and> u \<in> A} = ereal (edge_slack pot u v) \<Longrightarrow>
          ereal (edge_slack pot u v) =
          Inf {ereal (edge_slack pot ua v) |ua. (ua = u \<or> (ua, v) \<in> E) \<and> (ua = u \<or> ua \<in> A)}" 
            by (smt (verit, del_insts) Inf_less_iff linorder_cases mem_Collect_eq order_less_irrefl)
          have help2: 
           " Inf {ereal (edge_slack pot u v) |u. (u, v) \<in> E \<and> u \<in> A} = ereal (edge_slack pot u v) \<Longrightarrow>
              edge_slack pot y v < edge_slack pot u v \<Longrightarrow> (y, v) \<in> E \<Longrightarrow> y \<in> A \<Longrightarrow> False" for y
            by (smt (verit, ccfv_threshold) Inf_less_iff less_ereal.simps(1) mem_Collect_eq)
          have help3: 
            "{(v, va) |va. va \<in> vset_set vs} =
              {(v, u) |u.
              (u, v) \<in> E \<and>
              u \<in> A \<and> (\<forall>y. y \<in> A \<longrightarrow> (y, v) \<in> E \<longrightarrow> \<not> edge_slack pot y v < edge_slack pot u v)} \<Longrightarrow>
              va \<in> vset_set vs \<Longrightarrow> (va, v) \<notin> E \<Longrightarrow> va = u" for va
            by blast
          have help4:
            " {(v, va) |va. va \<in> vset_set vs} =
             {(v, u) |u.
           (u, v) \<in> E \<and>
             u \<in> A \<and> (\<forall>y. y \<in> A \<longrightarrow> (y, v) \<in> E \<longrightarrow> \<not> edge_slack pot y v < edge_slack pot u v)} \<Longrightarrow>  
             va \<in> vset_set vs \<Longrightarrow> va \<notin> A \<Longrightarrow> va = u" for va
            by blast
          have help5: False
            if a1: "Inf {ereal (edge_slack pot u v) |u. (u, v) \<in> E \<and> u \<in> A} = ereal (edge_slack pot u v)"
        and a2: "{(v, va) |va. va \<in> vset_set vs} = {(v, u) |u. (u, v) \<in> E \<and> u \<in> A \<and> (\<forall>y. y \<in> A \<longrightarrow> (y, v) \<in> E \<longrightarrow> \<not> edge_slack pot y v < edge_slack pot u v)}"
        and a3: "sl = edge_slack pot u v"
        and a4: "vaa \<in> vset_set vs"
        and  a5: "edge_slack pot u v < edge_slack pot vaa v" for vaa
       proof -
        have "\<forall>e E. (Inf E < (e::ereal) \<or> (\<forall>ea. \<not> ea < e \<or> ea \<notin> E)) \<and> ((\<exists>ea<e. ea \<in> E) \<or> \<not> Inf E < e)"
          by (metis (no_types) Inf_less_iff)
        then obtain ee :: "ereal \<Rightarrow> ereal set \<Rightarrow> ereal" and eea :: "ereal \<Rightarrow> ereal set \<Rightarrow> ereal" where
          f6: "\<forall>e E. (Inf E < e \<or> (\<forall>ea. \<not> ea < e \<or> ea \<notin> E)) \<and> (ee e E < e \<and> ee e E \<in> E \<or> \<not> Inf E < e)"
          by moura
        obtain aa :: "ereal \<Rightarrow> 'a" and aaa :: "ereal \<Rightarrow> 'a" where
          f7: "\<forall>e. (aa e \<in> A \<and> (aa e, v) \<in> E \<and> ereal (edge_slack pot (aa e) v) = e \<or> (\<forall>a. e \<noteq> ereal (edge_slack pot a v) \<or> (a, v) \<notin> E \<or> a \<notin> A)) \<and> ((\<exists>a. e = ereal (edge_slack pot a v) \<and> (a, v) \<in> E \<and> a \<in> A) \<or> (\<forall>a. a \<notin> A \<or> (a, v) \<notin> E \<or> ereal (edge_slack pot a v) \<noteq> e))"
          by moura
        have f8: "Inf {ereal (edge_slack pot a v) |a. (a, v) \<in> E \<and> a \<in> A} = ereal sl"
          using a3 a1 by fastforce
        have f9: "ereal sl < ereal (edge_slack pot vaa v)"
          using a5 a3 less_ereal.simps(1) by blast
        have f10: "\<exists>a. (v, vaa) = (v, a) \<and> (a, v) \<in> E \<and> a \<in> A \<and> (\<forall>aa. aa \<in> A \<longrightarrow> (aa, v) \<in> E \<longrightarrow> \<not> edge_slack pot aa v < edge_slack pot a v)"
          using a4 a2 by blast
        have "\<forall>e. (\<exists>a. ee e {ereal (edge_slack pot a v) |a. (a, v) \<in> E \<and> a \<in> A} = ereal (edge_slack pot a v) \<and> (a, v) \<in> E \<and> a \<in> A) \<or> \<not> ereal sl < e"
          using f8 f6 by (smt (z3) mem_Collect_eq)
        then have f11: "\<exists>a. ee (ereal (edge_slack pot vaa v)) {ereal (edge_slack pot a v) |a. (a, v) \<in> E \<and> a \<in> A} = ereal (edge_slack pot a v) \<and> (a, v) \<in> E \<and> a \<in> A"
          using f9 by meson
        have f12: "\<forall>e a ab. aa e \<notin> A \<or> (\<forall>aa. (a, ab) \<noteq> (v, aa) \<or> (aa, v) \<notin> E \<or> aa \<notin> A \<or> (\<exists>a. a \<in> A \<and> (a, v) \<in> E \<and> edge_slack pot a v < edge_slack pot aa v)) \<or> (aa e, v) \<notin> E \<or> (\<forall>a. e \<noteq> ereal (edge_slack pot a v) \<or> (a, v) \<notin> E \<or> a \<notin> A) \<or> (\<forall>aa. (a, ab) \<noteq> (v, aa) \<or> (aa, v) \<notin> E \<or> aa \<notin> A \<or> (\<exists>a. a \<in> A \<and> (a, v) \<in> E \<and> edge_slack pot a v < edge_slack pot aa v)) \<or> \<not> e < ereal (edge_slack pot ab v)"
          by (metis (no_types) less_ereal.simps(1) prod.inject)
        have f13: "(aa (ee (ereal (edge_slack pot vaa v)) {ereal (edge_slack pot a v) |a. (a, v) \<in> E \<and> a \<in> A}), v) \<in> E"
          using f11 f7 by blast
        have "aa (ee (ereal (edge_slack pot vaa v)) {ereal (edge_slack pot a v) |a. (a, v) \<in> E \<and> a \<in> A}) \<in> A"
          using f11 f7 by blast
        then show False
          using f13 f12 f11 f10 f9 f8 f6 by (smt (z3))
      qed
      have help6: " va \<in> vset_set vs \<Longrightarrow>
          edge_slack pot u v < edge_slack pot va v \<Longrightarrow>
          (\<And>vaa. vaa \<in> vset_set vs \<Longrightarrow> edge_slack pot u v < edge_slack pot vaa v \<Longrightarrow> False) \<Longrightarrow> False" for va
        by blast 
      have help7:" Inf {ereal (edge_slack pot u v) |u. (u, v) \<in> E \<and> u \<in> A} = ereal sl \<Longrightarrow>
         edge_slack pot u v < sl \<Longrightarrow>
         ereal (edge_slack pot u v) =
         Inf {ereal (edge_slack pot ua v) |ua. (ua = u \<or> (ua, v) \<in> E) \<and> (ua = u \<or> ua \<in> A)}"
        by (smt (verit, ccfv_threshold) Inf_less_iff less_ereal.simps(1) linorder_cases mem_Collect_eq
            order_less_irrefl)
      have help8: "
         Inf {ereal (edge_slack pot u v) |u. (u, v) \<in> E \<and> u \<in> A} = ereal sl \<Longrightarrow> 
         edge_slack pot u v < sl \<Longrightarrow>
         edge_slack pot y v < edge_slack pot u v \<Longrightarrow> (y, v) \<in> E \<Longrightarrow> y \<in> A \<Longrightarrow> False" for y
        by (smt (verit, best) Inf_less_iff less_ereal.simps(1) mem_Collect_eq)
      have help9: "
          Inf {ereal (edge_slack pot u v) |u. (u, v) \<in> E \<and> u \<in> A} = ereal sl \<Longrightarrow>
          edge_slack pot u v < sl \<Longrightarrow>
          \<forall>y. y \<noteq> u \<and> (y, v) \<notin> E \<or> y \<noteq> u \<and> y \<notin> A \<or> \<not> edge_slack pot y v < edge_slack pot ua v \<Longrightarrow>
          (ua, v) \<in> E \<Longrightarrow> ua \<in> A \<Longrightarrow> ua = u" for ua
         by (smt (verit, best) Inf_less_iff less_ereal.simps(1) mem_Collect_eq)
       have help10: "Inf {ereal (edge_slack pot u v) |u. (u, v) \<in> E \<and> u \<in> A} = ereal sl \<Longrightarrow>
                     \<not> edge_slack pot u v < sl \<Longrightarrow>
              ereal sl = Inf {ereal (edge_slack pot ua v) |ua. (ua = u \<or> (ua, v) \<in> E) \<and> (ua = u \<or> ua \<in> A)}"
         by (smt (z3) Inf_less_iff less_ereal.simps(1) linorder_cases mem_Collect_eq
            order_less_irrefl)
       have help11: "
          Inf {ereal (edge_slack pot u v) |u. (u, v) \<in> E \<and> u \<in> A} = ereal sl \<Longrightarrow>
          \<not> edge_slack pot u v < sl \<Longrightarrow>
          \<forall>y. y \<in> A \<longrightarrow> (y, v) \<in> E \<longrightarrow> \<not> edge_slack pot y v < edge_slack pot ua v \<Longrightarrow>
          edge_slack pot u v < edge_slack pot ua v \<Longrightarrow> False" for ua
         by (smt (verit, ccfv_SIG) Inf_less_iff less_ereal.simps(1) mem_Collect_eq)
       have help12: 
    "Inf {ereal (edge_slack pot u v) |u. (u, v) \<in> E \<and> u \<in> A} = ereal sl \<Longrightarrow>
    edge_slack pot u v \<noteq> sl \<Longrightarrow> \<not> edge_slack pot u v < sl \<Longrightarrow>
    \<forall>y. y \<noteq> u \<and> (y, v) \<notin> E \<or> y \<noteq> u \<and> y \<notin> A \<or> \<not> edge_slack pot y v < edge_slack pot u v \<Longrightarrow>
    (u, v) \<in> E"
         by(smt (verit, best) Inf_less_iff less_ereal.simps(1) mem_Collect_eq)
       have help13:
    "Inf {ereal (edge_slack pot u v) |u. (u, v) \<in> E \<and> u \<in> A} = ereal sl \<Longrightarrow>
      edge_slack pot u v \<noteq> sl \<Longrightarrow>
     \<not> edge_slack pot u v < sl \<Longrightarrow>
      \<forall>y. y \<noteq> u \<and> (y, v) \<notin> E \<or> y \<noteq> u \<and> y \<notin> A \<or> \<not> edge_slack pot y v < edge_slack pot u v \<Longrightarrow> u \<in> A"
         by (smt (verit, best) Inf_less_iff less_ereal.simps(1) mem_Collect_eq)
 
        from 1  show ?case
          using good_slacks_generalD(1,2)[OF that(2), of v, symmetric] one'  inf_ereal_find_inf 
                help3 help5 
          by(auto simp add: inner_def  abstract_min_slack_def
                  abstract_min_slack_edges_def is_arg_min_def  vset_set_specs.set_empty
                  abstract_min_slack_upd[OF slack_basic_invarD(1)[OF that(1)]] True
                  abstract_min_slack_edges_upd[OF slack_basic_invarD(1)[OF that(1)]]
                  vset_set_specs.set_insert[OF vset_set_specs.invar_empty] 
                              slack_map.map_update[OF slack_basic_invarD(1)[OF that(1)]] Let_def
                  vset_set_specs.set_insert[OF slack_basic_invarD(2)[OF that(1)]]
                  eq_commute[of _ "{(v, va) |va. va \<in> vset_set vs}"]
              intro: help1 help2 help8 help9 help3 help13  help12 help10 help7 help11,
              insert help4 help6 help11, auto) force+
    qed
  qed
next
  case False
  note false = this
  show ?thesis
   proof(cases "slack_lookup slacks va", all \<open>cases "slack_lookup slacks v"\<close>, goal_cases)
     case 1
     have a1:"abstract_min_slack slacks va =
        Inf {ereal (edge_slack pot ua va) |ua. (ua, va) \<in>  E \<and> ua \<in>  A}"
       using good_slacks_generalD(1) one' that(2) by blast
     hence a2:"\<nexists> ua. (ua, va) \<in>  E \<and> ua \<in>  A" 
       by(force simp add: abstract_min_slack_def 1 Inf_eq_PInfty dest!: sym[of \<infinity>])
     have a5:"{ereal (edge_slack pot ua va) |ua. (ua, va) \<in> E \<and> (ua = u \<or> ua \<in> A)} = 
          {ereal (edge_slack pot ua va) |ua. (ua, va) \<in> E \<and> ( ua \<in> A)}"
       using a2 good_slacks_generalD(5)[OF that(2)] by auto
     show ?case
       using false a2 a5 a1
       by(auto simp add: abstract_min_slack_def inner_def Let_def 1
           abstract_min_slack_edges_def slack_map.map_update[OF slack_basic_invarD(1)[OF that(1)]]
           is_arg_min_def)
   next
     case (2 a)
     then obtain vs sl where a_split:"a = (sl, vs)" by (cases a) auto
     have a1:"abstract_min_slack slacks va =
        Inf {ereal (edge_slack pot ua va) |ua. (ua, va) \<in>  E \<and> ua \<in>  A}"
       using good_slacks_generalD(1) one' that(2) by blast
     hence a2:"\<nexists> ua. (ua, va) \<in>  E \<and> ua \<in>  A" 
       by(force simp add: abstract_min_slack_def 2 Inf_eq_PInfty dest!: sym[of \<infinity>])
     have a5:"{ereal (edge_slack pot ua va) |ua. (ua, va) \<in> E \<and> (ua = u \<or> ua \<in> A)} = 
          {ereal (edge_slack pot ua va) |ua. (ua, va) \<in> E \<and> ( ua \<in> A)}"
       using a2 good_slacks_generalD(5)[OF that(2)] by auto
     then show ?case 
       using false a2 a5 a1
       by(auto simp add: abstract_min_slack_def inner_def Let_def a_split 2
           abstract_min_slack_edges_def slack_map.map_update[OF slack_basic_invarD(1)[OF that(1)]]
           is_arg_min_def)
   next
     case (3 a)
     then obtain vs sl where a_split:"a = (sl, vs)" by (cases a) auto
     have a1:"abstract_min_slack slacks va =
        Inf {ereal (edge_slack pot ua va) |ua. (ua, va) \<in>  E \<and> ua \<in>  A}"
             "abstract_min_slack_edges slacks va =
            {(va, u) |u. is_arg_min (\<lambda>u. edge_slack pot u va) (\<lambda>u. (u, va) \<in> E \<and> u \<in> A) u}"
       using good_slacks_generalD(1,2)[OF that(2) one'] by auto
     have a2: "{ereal (edge_slack pot ua va) |ua. (ua, va) \<in> E \<and> (ua = u \<or> ua \<in> A)} = 
               {ereal (edge_slack pot ua va) |ua. (ua, va) \<in> E \<and>  ua \<in> A}
              \<union> (if (u, va) \<in> E then {(ereal (edge_slack pot u va))} else {})"
       by auto
     have a3: "Inf {ereal (edge_slack pot ua va) |ua. (ua, va) \<in> E \<and> (ua = u \<or> ua \<in> A)}
               = (if (u, va) \<in> E then
                  min  (ereal (edge_slack pot u va))
                       (Inf {ereal (edge_slack pot ua va) |ua. (ua, va) \<in> E \<and> ua \<in> A})              
                 else Inf {ereal (edge_slack pot ua va) |ua. (ua, va) \<in> E \<and> ua \<in> A})"
       by(auto simp add: a2)
     have a4: "Inf {ereal (edge_slack pot ua va) |ua. (ua, va) \<in> E \<and> (ua = u \<or> ua \<in> A)} =
    min (ereal (edge_slack pot u va))
     (Inf {ereal (edge_slack pot ua va) |ua. (ua, va) \<in> E \<and> ua \<in> A}) \<Longrightarrow>
    \<forall>x\<in>E. fst x \<in> A \<Longrightarrow>
    Inf {ereal (edge_slack pot ua va) |ua. (ua, va) \<in> E \<and> ua \<in> A} =
    min (ereal (edge_slack pot u va)) (Inf {ereal (edge_slack pot u va) |u. (u, va) \<in> E \<and> u \<in> A})"
     by (smt (verit, ccfv_threshold) Collect_cong fst_conv)
     show ?case 
       using false a1 a3 good_slacks_generalD(5)[OF  that(2)] a_split a4
       by(force simp add: abstract_min_slack_def inner_def Let_def a_split 3
           abstract_min_slack_edges_def slack_map.map_update[OF slack_basic_invarD(1)[OF that(1)]]
           is_arg_min_def image_subset_iff) 
   next
     case (4 a aa)
     then obtain vs sl where a_split:"a = (sl, vs)" by (cases a) auto
     from 4 obtain avs asl where aa_split:"aa = (asl, avs)" by (cases aa) auto
     have a1:"abstract_min_slack slacks va =
        Inf {ereal (edge_slack pot ua va) |ua. (ua, va) \<in>  E \<and> ua \<in>  A}"
             "abstract_min_slack_edges slacks va =
            {(va, u) |u. is_arg_min (\<lambda>u. edge_slack pot u va) (\<lambda>u. (u, va) \<in> E \<and> u \<in> A) u}"
       using good_slacks_generalD(1,2)[OF that(2) one'] by auto
     have a2: "{ereal (edge_slack pot ua va) |ua. (ua, va) \<in> E \<and> (ua = u \<or> ua \<in> A)} = 
               {ereal (edge_slack pot ua va) |ua. (ua, va) \<in> E \<and>  ua \<in> A}
              \<union> (if (u, va) \<in> E then {(ereal (edge_slack pot u va))} else {})"
       by auto
     have a3: "Inf {ereal (edge_slack pot ua va) |ua. (ua, va) \<in> E \<and> (ua = u \<or> ua \<in> A)}
               = (if (u, va) \<in> E then
                  min  (ereal (edge_slack pot u va))
                       (Inf {ereal (edge_slack pot ua va) |ua. (ua, va) \<in> E \<and> ua \<in> A})              
                 else Inf {ereal (edge_slack pot ua va) |ua. (ua, va) \<in> E \<and> ua \<in> A})"
       by(auto simp add: a2)
     have a4: "Inf {ereal (edge_slack pot ua va) |ua. (ua, va) \<in> E \<and> (ua = u \<or> ua \<in> A)} =
    min (ereal (edge_slack pot u va))
     (Inf {ereal (edge_slack pot ua va) |ua. (ua, va) \<in> E \<and> ua \<in> A}) \<Longrightarrow>
    \<forall>x\<in>E. fst x \<in> A \<Longrightarrow>
    Inf {ereal (edge_slack pot ua va) |ua. (ua, va) \<in> E \<and> ua \<in> A} =
    min (ereal (edge_slack pot u va)) (Inf {ereal (edge_slack pot u va) |u. (u, va) \<in> E \<and> u \<in> A})"
     by (smt (verit, ccfv_threshold) Collect_cong fst_conv)
     show ?case 
       using false a1 a3 good_slacks_generalD(5)[OF  that(2)] a_split a4 aa_split
       by(force simp add: abstract_min_slack_def inner_def Let_def a_split 4
           abstract_min_slack_edges_def slack_map.map_update[OF slack_basic_invarD(1)[OF that(1)]]
           is_arg_min_def image_subset_iff  ) 
   qed
 qed 
next
  case 2
  show ?case
    using good_slacks_generalD(3) that(2) by auto
next
  case 3
  show ?case
    using good_slacks_generalD(4) that(2) by auto
next
  case 4
  show ?case
    using good_slacks_general_def that(2) by auto
qed
  show "slack_basic_invar (inner u v slacks)"
       "dom (slack_lookup (inner u v slacks)) = insert v (dom (slack_lookup slacks))"
   using slack_basic_invarD[OF that(1)]
   by(auto intro!: slack_basic_invarI slack_map.invar_update 
         simp add: inner_def Let_def  slack_map.map_update if_split[of "\<lambda> x. x = Some (_, _)"]
                  vset_set_specs.invar_insert vset_set_specs.invar_empty
       split: option.split prod.split)
qed
  have effect_inner_iterated:
     "good_slacks_general (edge_slack pot) (insert u A) B ({ (u, v) | v. v \<in> set vs} \<union> E)
     (foldr (inner u) vs slacks) \<and>
      slack_basic_invar (foldr (inner u) vs slacks) \<and>
      dom (slack_lookup (foldr (inner u) vs slacks)) =
      set vs \<union> (dom (slack_lookup slacks))" 
     if "slack_basic_invar slacks"  "good_slacks_general (edge_slack pot) A B E slacks"
        "\<nexists> v. (u, v) \<in> E"
    for u vs A B E slacks
    using that(1,2)
    proof(induction vs)
      case (Cons v vs)
      note IH = this
      have set_simpl:"{(u, va) |va. va = v \<or> va \<in> set vs} \<union> E = 
            insert (u, v) ({(u, va) |va. va \<in> set vs} \<union> E)" by auto
      have u_insert_double: "insert u A = insert u (insert u A)" by auto
      have "good_slacks_general (edge_slack pot) (insert u A) B
     ({(u, va) |va. va \<in> set (v # vs)} \<union> E) (foldr (inner u) (v # vs) slacks)"
      proof(cases vs)
        case Nil
        then show ?thesis 
          using Cons(2,3)
          by (auto intro!: conjunct1[OF effect_inner] simp add:  set_simpl)
      next
        case (Cons a list)
        show ?thesis 
         apply(simp add:  set_simpl)
         apply(subst u_insert_double)
         using IH(2,3)  IH(1)[OF IH(2,3)] Cons
         by (intro conjunct1[OF effect_inner]) auto
     qed
     moreover have "slack_basic_invar (foldr (inner u) (v # vs) slacks)"
      proof(cases vs)
        case Nil
        then show ?thesis 
          using Cons(2,3)
          by (auto intro!: conjunct1[OF conjunct2[OF effect_inner]] simp add:  set_simpl)
      next
        case (Cons a list)
        show ?thesis 
         using IH(2,3)  IH(1)[OF IH(2,3)] Cons
         by (auto intro: conjunct1[OF conjunct2[OF effect_inner]]) 
     qed
     moreover have "dom (slack_lookup (foldr (inner u) (v # vs) slacks))
                       = set (v # vs) \<union> dom (slack_lookup slacks)"
      proof(cases vs)
        case Nil
        then show ?thesis 
          using Cons(2,3)
          by (auto intro!: conjunct2[OF conjunct2[OF effect_inner]] simp add:  set_simpl)
      next
        case (Cons a list)
        show ?thesis 
         using IH(2,3) IH(1)[OF IH(2,3)] Cons conjunct2[OF conjunct2[OF effect_inner]] 
         by force
     qed
     ultimately show ?case by simp  
   next
     case Nil
     thus ?case
       using that(3)
       by(auto intro!: good_slacks_general_extended_lonely_left)
   qed
  have effect_outer:
     "good_slacks_general (edge_slack pot) (insert u A)
              B ({ (u, v) | v. v \<in> right_neighb_abstract u} \<union> E)
     (outer u slacks) \<and>
      slack_basic_invar (outer u slacks) \<and>
      dom (slack_lookup (outer u slacks)) =
      right_neighb_abstract u \<union> (dom (slack_lookup slacks))" 
     if "slack_basic_invar slacks"  "good_slacks_general (edge_slack pot) A B E slacks"
        "\<nexists> v. (u, v) \<in> E"
    for u A B E slacks
    unfolding outer_def
  proof(cases "right_neighbs u", goal_cases)
    case 1
     then show ?case
     using effect_inner_iterated[OF that(1,2), of u] reight_neighbs vset_flatten(1)
     by(auto simp add: outer_def that right_neighb_abstract_def  
          good_slacks_general_extended_lonely_left split: option.split)
    next
      case (2 vs)
      show ?case
        using effect_inner_iterated[OF that(1,2), of u]
              vset_flatten(1)[OF reight_neighbs[OF 2], symmetric]
        by(auto simp add: outer_def that right_neighb_abstract_def 2 split: option.split)
    qed
  have effect_outer_iterated:
     "good_slacks_general (edge_slack pot) (set vs \<union> A)
              B ({ (u, v) | u v. u \<in> set vs \<and> v \<in> right_neighb_abstract u} \<union> E)
     (foldr outer vs slacks) \<and>
      slack_basic_invar (foldr outer vs slacks) \<and>
      dom (slack_lookup (foldr outer vs slacks)) =
      \<Union> (right_neighb_abstract ` (set vs)) \<union> (dom (slack_lookup slacks))" 
     if "slack_basic_invar slacks"  "good_slacks_general (edge_slack pot) A B E slacks"
        "\<And> u. u \<in> set vs \<Longrightarrow> \<nexists> v . (u, v) \<in> E" "distinct vs"    for  A B E slacks vs 
    using that
    proof(induction vs)
      case (Cons v vs)
      note IH = this
      have no_v_edge_vs: "(\<And>u. u \<in> set vs \<Longrightarrow> \<nexists>v. (u, v) \<in> E)" 
        using IH(4) by auto
      have distinct_vs: "distinct vs"
        using IH(5) by auto
      have set_simpl:"{(u, va). (u = v \<or> u \<in> set vs) \<and> va \<in> right_neighb_abstract u} \<union> E
            = { (v, va) | va. va \<in> right_neighb_abstract v} \<union> 
              ({(u, va). u \<in> set vs \<and> va \<in> right_neighb_abstract u} \<union> E)" by auto
      have big_u_simp: "\<Union> (right_neighb_abstract ` set (v # vs)) = 
                       (right_neighb_abstract v) \<union> \<Union> (right_neighb_abstract ` set vs)"
        by auto
      have "good_slacks_general (edge_slack pot) (set (v # vs) \<union> A) B
             ({(u, va) |u va. u \<in> set (v # vs) \<and> va \<in> right_neighb_abstract u} \<union> E)
             (foldr outer (v # vs) slacks)"
        using  IH(1)[OF IH(2,3) no_v_edge_vs distinct_vs, simplified]  IH(4,5) 
        by (auto intro!: conjunct1[OF effect_outer] simp add:  set_simpl)
      moreover have "slack_basic_invar (foldr outer (v # vs) slacks)"
        using  IH(1)[OF IH(2,3) no_v_edge_vs distinct_vs, simplified]  IH(4,5) 
        by (auto intro!: conjunct1[OF conjunct2[OF effect_outer]])    
     moreover have "dom (slack_lookup (foldr outer (v # vs) slacks)) =
           \<Union> (right_neighb_abstract ` set (v # vs)) \<union> dom (slack_lookup slacks)"
       apply(simp add: big_u_simp)
       apply(subst conjunct2[OF conjunct2[OF effect_outer]])
        using  IH(1)[OF IH(2,3) no_v_edge_vs distinct_vs, simplified]  IH(4,5) 
        by auto
     ultimately show ?case by simp  
   qed simp
   have pairs_set_split:"{(u, v) |u v. v \<in> right_neighb_abstract u \<and> u \<in> set flat_new_left \<union> A} = 
      {(u, v) |u v. u \<in> set flat_new_left \<and> v \<in> right_neighb_abstract u} \<union>
      {(u, v) |u v. v \<in> right_neighb_abstract u \<and> u \<in> A}"
     by auto
  have  "good_slacks (\<lambda> u v. edge_slack pot u v) (A \<union> vset_set new_left)
           B (new_slacks slacks pot new_left) \<and>
           slack_basic_invar (new_slacks slacks pot new_left) \<and>
           dom (slack_lookup (new_slacks slacks pot new_left)) = 
           dom (slack_lookup slacks) \<union> \<Union> (right_neighb_abstract ` vset_set new_left)"
    using new_left_flattened(2)  assms(3,4)
    unfolding new_slacks_def new_left_flattened(1)[symmetric] flat_new_left_def[symmetric]
              fun_cong[OF inner_def, symmetric] outer_def[symmetric] Un_commute[of _ "\<Union> _"]
              Un_commute[of _ "set _"] 
              pairs_set_split good_slacks_good_slacks_general(3)
    by(intro effect_outer_iterated[OF assms(1), of A B _ flat_new_left]) auto
  thus "good_slacks (edge_slack pot) (A \<union> vset_set new_left) B (new_slacks slacks pot new_left)"
       " slack_basic_invar (new_slacks slacks pot new_left)"
       "dom (slack_lookup (new_slacks slacks pot new_left)) =
       dom (slack_lookup slacks) \<union> \<Union> (right_neighb_abstract ` vset_set new_left)"
    by auto
qed
