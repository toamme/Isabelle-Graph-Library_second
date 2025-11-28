theory Primal_Dual_Path_Search
  imports Berge_Lemma.Berge Flow_Theory.Arith_Lemmas "HOL-Data_Structures.Set_Specs"
"HOL-Data_Structures.Map_Specs"
RANKING.More_Graph  Alternating_Forest_Spec Key_Value_Queue_Spec
begin
(*TODO MOVE*)

lemma pair_eq_fst_snd_eq:
      "(a, b) = c \<Longrightarrow> a = fst c"
      "(a, b) = c \<Longrightarrow> b = snd c"
  by auto

(*TODO MOVE*)
lemma matchingI:
  "(\<And>e1 e2. \<lbrakk>e1 \<in> M; e2 \<in> M; e1 \<noteq> e2\<rbrakk> \<Longrightarrow> e1 \<inter> e2 = {}) \<Longrightarrow> matching M"
  by (auto simp: matching_def)

(*TODO MOVE*)
lemma P_of_minI: 
"((a::real) \<le> b \<Longrightarrow> P a) \<Longrightarrow> (b \<le> a \<Longrightarrow> P b) \<Longrightarrow> P (min a b)"
and P_of_minE: 
"P (min a b) \<Longrightarrow>
 (\<lbrakk>(a::real) \<le> b; P a\<rbrakk> \<Longrightarrow> Q) \<Longrightarrow>
 (\<lbrakk>b \<le> a; P b\<rbrakk> \<Longrightarrow> Q) \<Longrightarrow> Q"
and P_of_minI_strict1: 
"((a::real) < b \<Longrightarrow> P a) \<Longrightarrow> (b \<le> a \<Longrightarrow> P b) \<Longrightarrow> P (min a b)"
and P_of_minE_strict2: 
"P (min a b) \<Longrightarrow>
 (\<lbrakk>(a::real) \<le> b; P a\<rbrakk> \<Longrightarrow> Q) \<Longrightarrow>
 (\<lbrakk>b < a; P b\<rbrakk> \<Longrightarrow> Q) \<Longrightarrow> Q"
for P a b
    apply linarith+
  by (smt (verit, best))+

lemma abstract_real_map_fun_upd:
"abstract_real_map (f(a \<mapsto> b)) = 
(\<lambda> x. if x = a then b 
      else abstract_real_map f x)"
  by(auto simp add: abstract_real_map_def)

lemma matching_augmenting_pathI:
 "\<lbrakk>length p \<ge> 2; alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path p);
     hd p \<notin> Vs M; last p \<notin> Vs M\<rbrakk>
   \<Longrightarrow> matching_augmenting_path M p"
  by(auto simp add: matching_augmenting_path_def)

lemma in_image_with_fst_eq: "a \<in> fst ` A \<longleftrightarrow> (\<exists> b. (a, b) \<in> A)" 
  by force

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

lemma finite_double_image_of_pairs_in_set_of_sets:
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

section \<open>Path Search for Hungarian Method\<close>

subsection \<open>Defining the Function and Setup for Reasoning\<close>

record ('forest, 'ben, 'heap, 'miss, 'v) hungarian_search_state = 
forest::'forest
best_even_neighbour::'ben
heap::'heap
missed::'miss
acc::real
augpath::"('v list) option"

datatype ('v, 'pot) path_search_result = 
  Dual_Unbounded | Lefts_Matched | Next_Iteration "'v list" 'pot

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

definition working_potential ("\<pi>\<^sup>*") where
"\<pi>\<^sup>* state v =
        (if vset_isin v (evens (forest state)) then 
           \<pi> v + acc state - missed_at state v
         else if vset_isin v (odds (forest state)) then 
           \<pi> v - acc state + missed_at state v
         else \<pi> v)"

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

function (domintros) search_path_loop::
  "('forest, 'ben, 'heap, 'miss, 'v) hungarian_search_state \<Rightarrow>
   ('forest, 'ben, 'heap, 'miss, 'v) hungarian_search_state" where
"search_path_loop state = 
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
                            augpath:= Some (r # get_path F l) \<rparr>|
                 Some l' \<Rightarrow>
                     (let missed' = missed_upd (
                                    missed_upd (missed state) r acc') 
                                                l' acc';
                          (ben', queue') = update_best_even_neighbour 
                                           (abstract_real_map (missed_lookup missed'))
                                           ben queue l';
                          F'= extend_forest_even_unclassified F l r l' 
                      in  
                    search_path_loop (state \<lparr> forest:= F', 
                            best_even_neighbour:=ben',
                            heap:=queue',
                            missed:=missed',
                            acc:= acc' \<rparr>)
             )))))"
  by pat_completeness auto

definition "search_path_loop_fail_cond state = 
  (let (queue, heap_min) = heap_extract_min (heap state)
   in (case heap_min of None \<Rightarrow> True|
                        Some r \<Rightarrow> False))"

lemma search_path_loop_fail_condE:
"search_path_loop_fail_cond state \<Longrightarrow>
(\<And> queue heap_min. 
    \<lbrakk> (queue, heap_min) = heap_extract_min (heap state); heap_min = None\<rbrakk> \<Longrightarrow> P)
\<Longrightarrow> P"
  apply(cases "heap_extract_min (heap state)")
  apply(all \<open>cases "snd (heap_extract_min (heap state))"\<close>)
  by(auto simp add: search_path_loop_fail_cond_def)

definition "search_path_loop_succ_cond state = 
  (let (queue, heap_min) = heap_extract_min (heap state)
   in (case heap_min of
          None \<Rightarrow> False|
          Some r \<Rightarrow> (case buddy r of 
                        None \<Rightarrow> True|
                        Some l' \<Rightarrow> False )))"

lemma search_path_loop_succ_condE:
"search_path_loop_succ_cond state \<Longrightarrow>
(\<And> queue heap_min r. 
    \<lbrakk> (queue, heap_min) = heap_extract_min (heap state); 
        heap_min = Some r; buddy r = None\<rbrakk> \<Longrightarrow> P)
\<Longrightarrow> P"
  apply(cases "heap_extract_min (heap state)")
  apply(all \<open>cases "snd (heap_extract_min (heap state))"\<close>)
  apply(all \<open>cases "buddy (the (snd (heap_extract_min (heap state))))"\<close>)
  by(auto simp add: search_path_loop_succ_cond_def)

definition "search_path_loop_cont_cond state = 
  (let (queue, heap_min) = heap_extract_min (heap state)
   in (case heap_min of None \<Rightarrow> False|
                        Some r \<Rightarrow> (case buddy r of None \<Rightarrow> False|
                                                   Some l' \<Rightarrow> True)))"

lemma search_path_loop_cont_condE:
"search_path_loop_cont_cond state \<Longrightarrow>
(\<And> queue heap_min r l'. 
    \<lbrakk>  heap_extract_min (heap state) = (queue, heap_min); 
        heap_min = Some r; buddy r = Some l'\<rbrakk> \<Longrightarrow> P)
\<Longrightarrow> P"
  apply(cases "heap_extract_min (heap state)")
  apply(all \<open>cases "snd (heap_extract_min (heap state))"\<close>)
  apply(all \<open>cases "buddy (the (snd (heap_extract_min (heap state))))"\<close>)
  by(auto simp add: search_path_loop_cont_cond_def)

lemma search_path_loop_cases:
  assumes "search_path_loop_fail_cond state \<Longrightarrow> P"
          "search_path_loop_succ_cond state \<Longrightarrow> P"
          "search_path_loop_cont_cond state \<Longrightarrow> P"
    shows P
  using assms
  apply(cases "heap_extract_min (heap state)")
  apply(all \<open>cases "snd (heap_extract_min (heap state))"\<close>)
  apply(all \<open>cases "buddy (the (snd (heap_extract_min (heap state))))"\<close>)
  by(auto simp add: search_path_loop_fail_cond_def
                    search_path_loop_succ_cond_def search_path_loop_cont_cond_def)

definition "search_path_loop_fail_upd state = state \<lparr>augpath:=None\<rparr>"

definition "search_path_loop_succ_upd state = 
  (let F = forest state;
       ben = best_even_neighbour state;
       missed_\<epsilon> = missed_at state;
       (queue, heap_min) = heap_extract_min (heap state);
       r = the heap_min;
       l = the (ben_lookup ben r);
       acc' = w\<^sub>\<pi> l r + missed_\<epsilon> l
    in state \<lparr> acc := acc', augpath:= Some (r # get_path F l) \<rparr>)"

definition "search_path_loop_cont_upd state = 
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
 
lemma search_path_loop_simps:
  "search_path_loop_fail_cond state \<Longrightarrow> search_path_loop state = search_path_loop_fail_upd state"
  "search_path_loop_succ_cond state \<Longrightarrow> search_path_loop state = search_path_loop_succ_upd state"
  "\<lbrakk>search_path_loop_dom state; search_path_loop_cont_cond state\<rbrakk> \<Longrightarrow>
   search_path_loop state = search_path_loop (search_path_loop_cont_upd state)"
proof(goal_cases)
  case 1
  show ?case 
    apply(subst search_path_loop.psimps)
    apply(all \<open>cases "heap_extract_min (heap state)"\<close>)
    apply(all \<open>cases "snd (heap_extract_min (heap state))"\<close>)
    using 1
    by(auto intro: search_path_loop.domintros
             simp add: search_path_loop_fail_cond_def search_path_loop_fail_upd_def)
next
  case 2
  show ?case
    apply(subst search_path_loop.psimps)
    apply(all \<open>cases "heap_extract_min (heap state)"\<close>)
    apply(all \<open>cases "snd (heap_extract_min (heap state))"\<close>)
    apply(all \<open>cases "buddy (the (snd (heap_extract_min (heap state))))"\<close>)
    using 2
    by(auto intro: search_path_loop.domintros
             simp add: search_path_loop_succ_cond_def search_path_loop_succ_upd_def)
next
  case 3
  show ?case 
    apply(subst search_path_loop.psimps[OF 3(1)])
    apply(all \<open>cases "heap_extract_min (heap state)"\<close>)
    apply(all \<open>cases "snd (heap_extract_min (heap state))"\<close>)
    apply(all \<open>cases "buddy (the (snd (heap_extract_min (heap state))))"\<close>)
    using 3
    by(auto simp add: search_path_loop_cont_cond_def search_path_loop_cont_upd_def Let_def
               split: option.split prod.split)
qed

lemma search_path_loop_induct:
  assumes "search_path_loop_dom state"
           "\<And> state. \<lbrakk>search_path_loop_dom state;
                      search_path_loop_cont_cond state \<Longrightarrow> P (search_path_loop_cont_upd state)\<rbrakk>
                     \<Longrightarrow> P state"
  shows "P state"
proof(induction rule: search_path_loop.pinduct[OF assms(1)])
  case (1 state)
  note IH = this
  show ?case 
  proof(cases state rule: search_path_loop_cases, goal_cases)
    case 1
    then show ?case
     by(auto elim!:  search_path_loop_fail_condE
            intro!: assms(2)[OF IH(1)]
          simp add: search_path_loop_cont_cond_def)
  next
    case 2
    then show ?case 
     by(auto elim!:  search_path_loop_succ_condE
            intro!: assms(2)[OF IH(1)] 
          simp add: search_path_loop_cont_cond_def)
  next
    case 3
    show ?case 
      apply(rule assms(2)[OF IH(1)])
      using 3 assms(2)
      by(auto intro!: IH(2)
               elim!: search_path_loop_cont_condE
            simp add: search_path_loop_cont_upd_def Let_def 
               split: option.split prod.split)
  qed
qed

lemma search_path_loop_domintros:
  "search_path_loop_fail_cond state \<Longrightarrow> search_path_loop_dom state"
  "search_path_loop_succ_cond state \<Longrightarrow> search_path_loop_dom state"
  "\<lbrakk>search_path_loop_cont_cond state; search_path_loop_dom (search_path_loop_cont_upd state)\<rbrakk> \<Longrightarrow>
   search_path_loop_dom state"
proof(goal_cases)
  case 1
  show ?case 
    apply(rule search_path_loop.domintros)
    apply(all \<open>cases "heap_extract_min (heap state)"\<close>)
    apply(all \<open>cases "snd (heap_extract_min (heap state))"\<close>)
    using 1
    by(auto intro: search_path_loop.domintros
             simp add: search_path_loop_fail_cond_def search_path_loop_fail_upd_def)
next
  case 2
  show ?case
    apply(rule search_path_loop.domintros)
    apply(all \<open>cases "heap_extract_min (heap state)"\<close>)
    apply(all \<open>cases "snd (heap_extract_min (heap state))"\<close>)
    apply(all \<open>cases "buddy (the (snd (heap_extract_min (heap state))))"\<close>)
    using 2
    by(auto intro: search_path_loop.domintros
             simp add: search_path_loop_succ_cond_def search_path_loop_succ_upd_def)
next
  case 3
  show ?case 
    apply(rule search_path_loop.domintros)
    apply(all \<open>cases "heap_extract_min (heap state)"\<close>)
    apply(all \<open>cases "snd (heap_extract_min (heap state))"\<close>)
    apply(all \<open>cases "buddy (the (snd (heap_extract_min (heap state))))"\<close>)
    using 3
    by(auto simp add: search_path_loop_cont_cond_def search_path_loop_cont_upd_def Let_def prod.split
               split: option.split prod.split)
qed

partial_function (tailrec) search_path_loop_impl::
  "('forest, 'ben, 'heap, 'miss, 'v) hungarian_search_state \<Rightarrow>
   ('forest, 'ben, 'heap, 'miss, 'v) hungarian_search_state" where
"search_path_loop_impl state = 
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
                            augpath:= Some (r # get_path F l) \<rparr>|
                 Some l' \<Rightarrow>
                     (let missed' = missed_upd (
                                    missed_upd (missed state) r acc') 
                                                l' acc';
                          (ben', queue') = update_best_even_neighbour 
                                           (abstract_real_map (missed_lookup missed'))
                                           ben queue l';
                          F'= extend_forest_even_unclassified F l r l' 
                      in  
            search_path_loop_impl (state \<lparr> forest:= F', 
                            best_even_neighbour:=ben',
                            heap:=queue',
                            missed:=missed',
                            acc:= acc' \<rparr>)
             )))))"

definition "new_potential state = 
(foldl (\<lambda> p v. potential_upd p v (\<pi> v - acc state + missed_at state v))
   (foldl (\<lambda> p v. potential_upd p v (\<pi> v + acc state - missed_at state v)) 
      initial_pot (to_list (evens (forest state))))
 (to_list (odds (forest state))))"

definition "search_path = 
(if unmatched_lefts = [] then Lefts_Matched
else (let final_state = search_path_loop_impl initial_state
      in (case augpath final_state of 
               None \<Rightarrow> Dual_Unbounded 
              | Some p \<Rightarrow> Next_Iteration p (new_potential final_state))))"

lemma search_path_loop_impl_same:
  assumes "search_path_loop_dom state"
  shows "search_path_loop_impl state = search_path_loop state"
  apply(induction rule: search_path_loop.pinduct[OF assms])
  apply(subst search_path_loop.psimps, simp)
  apply(subst search_path_loop_impl.simps)
  by (auto simp add: Let_def split: if_split option.split prod.split)

end

subsection \<open>Locale for Proofs\<close>


locale primal_dual_path_search =

 primal_dual_path_search_spec 
      where G = "G::'v set set" 
      and   left = "left::'vset"
      and empty_forest="empty_forest::'vset \<Rightarrow> 'forest"
      and initial_pot = "initial_pot::'pot"
      and ben_empty="ben_empty::'ben"
      and extend_forest_even_unclassified = extend_forest_even_unclassified
      and evens = evens and odds = odds and get_path = get_path
      and abstract_forest = abstract_forest
      and forest_invar = forest_invar
      and roots = roots +

 alternating_forest_ordinary_extension_spec 
      where extend_forest_even_unclassified = extend_forest_even_unclassified
      and  evens = evens and odds = odds and get_path = get_path
      and abstract_forest = abstract_forest
      and forest_invar = forest_invar
      and roots = roots and empty_forest = empty_forest +

  key_value_queue heap_empty heap_extract_min heap_decrease_key heap_insert
      heap_invar heap_abstract 

    for G left  initial_pot ben_empty
    and evens::"'forest \<Rightarrow> 'vset"
    and odds::"'forest \<Rightarrow> 'vset"
    and get_path::"'forest \<Rightarrow> 'v \<Rightarrow> 'v list"
    and abstract_forest::"'forest \<Rightarrow> 'v set set"
    and forest_invar::"'v set set \<Rightarrow> 'forest \<Rightarrow> bool"
    and roots::"'forest \<Rightarrow> 'vset" 
    and extend_forest_even_unclassified::
        "'forest \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'forest"
    and empty_forest::"'vset \<Rightarrow> 'forest" +

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
"dom (potential_lookup initial_pot) \<subseteq> L \<union> R"
begin

subsection \<open>Misc about the Graph\<close>

lemma w\<^sub>\<pi>_symmetric: "{u, v} \<in> G \<Longrightarrow> w\<^sub>\<pi> u v = w\<^sub>\<pi> v u"
  by(auto simp add: w\<^sub>\<pi>_def intro: G(7))

lemma w\<^sub>\<pi>_non_neg: "{u, v} \<in> G \<Longrightarrow> w\<^sub>\<pi> u v \<ge> 0"
  using G(8) w\<^sub>\<pi>_def by fastforce

lemma finite_L: "finite L" and finite_R: "finite R"
  using vset(7)[OF G(3) refl, symmetric] vset(7)[OF G(4) refl, symmetric]
  by simp+

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

subsection \<open>Setting Up Invariants\<close>

definition "invar_basic state= 
  (forest_invar \<M> (forest state) \<and>
    ben_invar (best_even_neighbour state) \<and>
    heap_invar (heap state) \<and>
    missed_invar (missed state) \<and>
    \<F> state \<subseteq> G \<and>
    dom (ben_lookup (best_even_neighbour state)) \<subseteq> Vs G \<and>
    dom (missed_lookup (missed state)) \<subseteq> Vs G \<and>
     fst ` heap_abstract (heap state) \<subseteq> Vs G \<and>
     aevens state \<subseteq> L \<and> aodds state \<subseteq> R \<and>
    {l | l r. ben_lookup (best_even_neighbour state) r = Some l} \<subseteq> aevens state \<and>
    aodds state \<subseteq> dom (ben_lookup (best_even_neighbour state)))"

lemma invar_basicE:
"invar_basic state \<Longrightarrow>
(\<lbrakk>forest_invar \<M> (forest state);
  ben_invar (best_even_neighbour state);
  heap_invar (heap state);
  missed_invar (missed state);\<F> state \<subseteq> G;
  dom (ben_lookup (best_even_neighbour state)) \<subseteq> Vs G;
  dom (missed_lookup (missed state)) \<subseteq> Vs G;
  fst ` heap_abstract (heap state) \<subseteq> Vs G;
  aevens state \<subseteq> L; aodds state \<subseteq> R;
  {l | l r. ben_lookup (best_even_neighbour state) r = Some l} \<subseteq> aevens state;
  aodds state \<subseteq> dom (ben_lookup (best_even_neighbour state))\<rbrakk> 
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
  aevens state \<subseteq> L; aodds state \<subseteq> R;
  {l | l r. ben_lookup (best_even_neighbour state) r = Some l} \<subseteq> aevens state;
  aodds state \<subseteq> dom (ben_lookup (best_even_neighbour state))\<rbrakk> 
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
"invar_basic state \<Longrightarrow> {l | l r. ben_lookup (best_even_neighbour state) r = Some l} \<subseteq> aevens state"
"invar_basic state \<Longrightarrow> aodds state \<subseteq> dom (ben_lookup (best_even_neighbour state))"
  by(auto simp add: invar_basic_def)

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
            (\<forall> u v.  {u, v} \<in> \<F> state \<longrightarrow> edge_costs u v = \<pi>\<^sup>* state u + \<pi>\<^sup>* state v)"

lemma invar_forest_tightE:
"invar_forest_tight state \<Longrightarrow>
 ((\<And> u v. {u, v} \<in> \<F> state \<Longrightarrow>edge_costs u v = \<pi>\<^sup>* state u + \<pi>\<^sup>* state v) \<Longrightarrow> P)
\<Longrightarrow> P"
and invar_forest_tightI:
"(\<And> u v. {u, v} \<in> \<F> state \<Longrightarrow> edge_costs u v = \<pi>\<^sup>* state u + \<pi>\<^sup>* state v)
 \<Longrightarrow> invar_forest_tight state"
and invar_forest_tightD:
"\<lbrakk>invar_forest_tight state; {u, v} \<in> \<F> state\<rbrakk> 
  \<Longrightarrow> edge_costs u v = \<pi>\<^sup>* state u + \<pi>\<^sup>* state v"
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
  \<and> ((\<exists> l. l \<in> aevens state \<and> {l, r} \<in> G)
         \<longrightarrow> (\<exists> l. ben_lookup (best_even_neighbour state) r = Some l \<and>
                   {r, l} \<in> G  \<and>  l \<in> aevens state \<and>
                   w\<^sub>\<pi> l r + missed_at state l = 
                   Min {w\<^sub>\<pi> l r + missed_at state l | l. l \<in> aevens state \<and> {l, r} \<in> G})))"

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

definition "invar_out_of_heap state =
   (\<forall> r l. ben_lookup (best_even_neighbour state) r = Some l
             \<and> (\<nexists> k. (r, k) \<in> heap_abstract (heap state)) \<longrightarrow>
            (\<forall> kr \<in> heap_abstract (heap state). snd kr  
               \<ge> w\<^sub>\<pi> l r + missed_at state l))"

lemma invar_out_of_heapD:
"\<lbrakk>invar_out_of_heap state;
 ben_lookup (best_even_neighbour state) r = Some l;
  \<nexists> k. (r, k) \<in> heap_abstract (heap state);
   kr \<in> heap_abstract (heap state)\<rbrakk> \<Longrightarrow>
   snd kr  \<ge> w\<^sub>\<pi> l r + missed_at state l"
and invar_out_of_heapI:
"(\<And> r l kr. \<lbrakk>ben_lookup (best_even_neighbour state) r = Some l;
  \<nexists> k. (r, k) \<in> heap_abstract (heap state);
   kr \<in> heap_abstract (heap state)\<rbrakk> \<Longrightarrow>
   snd kr  \<ge> w\<^sub>\<pi> l r + missed_at state l)
\<Longrightarrow> invar_out_of_heap state"
  by(auto simp add: invar_out_of_heap_def)

subsection \<open>Manipulation of Heap and Best Even Neighbours\<close>

lemmas heap =  
 queue_empty(1)
 queue_extract_min(1)
 queue_insert(1)
 queue_decrease_key(1)
 queue_extract_min(2,3)
 key_for_element_unique
 queue_extract_min(4)
 queue_decrease_key(2)
 queue_insert(2)
 queue_empty(2)

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
          "(ben', queue') = update_best_even_neighbours off ben queue ls"
 defines "conn_min \<equiv> (\<lambda> r.
     Min ((if ben_lookup ben r \<noteq> None
          then {w\<^sub>\<pi> (the (ben_lookup ben r)) r + off (the (ben_lookup ben r))}
          else {}) \<union> 
          {w\<^sub>\<pi> l r + off l | l. l \<in> set ls \<and> r \<in> vset_to_set (right_neighbs l)}))"
 shows "ben_invar ben'" (is ?thesis1) "heap_invar queue'" (is ?thesis2)
       "\<And> r k. (r, k) \<in> heap_abstract queue' \<Longrightarrow>
         (\<exists> l. ben_lookup ben' r = Some l \<and> k = w\<^sub>\<pi> l r + off l)"
       "\<And> r l' l. ben_lookup ben' r = Some l' \<and> (\<nexists> k. (r, k) \<in> heap_abstract queue') \<Longrightarrow>
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
           \<union> {(r, w\<^sub>\<pi> ll r + off ll) | r l ll. 
               r \<in> vset_to_set (right_neighbs l) \<and> 
               l \<in> set ls \<and> Some ll = ben_lookup ben' r \<and>
               (r \<in> fst ` (heap_abstract queue) \<or> ben_lookup ben r = None)}"
               (is ?thesis4)
proof-
  define ls' where "ls' = rev ls"
  have set_ls_is:"set ls = set ls'"
    by(auto simp add: ls'_def)
  have "?thesis1 \<and> ?thesis2 \<and>
       (\<forall> r k. (r, k) \<in> heap_abstract queue' \<longrightarrow> 
          (\<exists> l. ben_lookup ben' r = Some l \<and> k = w\<^sub>\<pi> l r + off l)) \<and>
       (\<forall> l r l'.  ben_lookup ben' r = Some l' \<and> (\<nexists> k. (r, k) \<in> heap_abstract queue')\<longrightarrow>
             off l \<ge> w\<^sub>\<pi> l' r + off l') \<and>
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
       Cons(1)[OF Cons(2,3) ls_in_L Cons(5,6), simplified result_def[symmetric],OF
         result_is conn_min_before_def]
    note IH_applied = conjD(1)[OF IH_applied_all]
                      conjD(2)[OF IH_applied_all]
                      spec[OF spec[OF conjD(3)[OF IH_applied_all]]]
                      spec[OF spec[OF spec[OF conjD(4)[OF IH_applied_all]]]]
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
      show ?case 
      proof(rule, rule, rule, rule, goal_cases)
        case (1 l1 r1 l'1)
        show ?case 
        proof (cases "l1 = l")
          case True
          then show ?thesis 
           using single_update(4)[of r1 l'1] 1 by simp
        next
          case False
          have helper1: "y = l'1"
            if "r1 \<in> vset_to_set (right_neighbs l)"
               "ben_lookup (fst result) r1 = Some y"
               "(if w\<^sub>\<pi> l r1 + off l < w\<^sub>\<pi> y r1 + off y then Some l
               else ben_lookup (fst result) r1) = Some l'1" 
                "r1 \<notin> fst ` heap_abstract (snd result)" for y
             apply(cases "w\<^sub>\<pi> l r1 + off l < w\<^sub>\<pi> y r1 + off y")
             using G(6)[OF l_in_L] IH_applied(4)[of r1 y l] that
                  w\<^sub>\<pi>_non_neg[of l r1] 
             by force+
           have helper2: False 
             if "r1 \<in> vset_to_set (right_neighbs l'1)"
                "ben_lookup (fst result) r1 = None"
                "l = l'1" "\<forall>k. (r1, k) \<notin> heap_abstract queue'"
             using single_update(6) that by blast
          from False have "ben_lookup (fst result) r1 = Some l'1" 
            using 1 unfolding single_update(5)
            apply(cases "r1 \<notin> vset_to_set (right_neighbs l)")
            apply(all \<open>cases \<open>ben_lookup (fst result) r1 = None\<close>\<close>)
            by(auto simp add: single_update(6) intro: helper1 helper2)
          moreover have "(\<nexists>k. (r1, k) \<in> heap_abstract (snd result))"
           using 1 unfolding single_update(5)
            apply(cases "r1 \<notin> vset_to_set (right_neighbs l)")
            apply(all \<open>cases \<open>ben_lookup (fst result) r1 = None\<close>\<close>)
            by(auto simp add: single_update(6) rev_image_eqI)
          ultimately show ?thesis 
            using IH_applied(4)[of r1 l'1 l1] by simp
        qed
      qed
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
              using IH_applied_all
              by fastforce
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
                     Some ll = ben_lookup ben' r \<and>
               (r \<in> fst ` heap_abstract (snd result) 
                   \<or> ben_lookup (fst result) r = None)}" 
        proof(rule set_eqI, rule, goal_cases)
          case (1 queue_entry)
          then show ?case 
          proof(cases  queue_entry, goal_cases)
            case (1 r' k)
            have helper1: "(r', w\<^sub>\<pi> l r' + off l) \<in> heap_abstract (snd result)"
              if "queue_entry = (r', w\<^sub>\<pi> l r' + off l)"  
                 " \<forall>ll. Some ll =
              (if ben_lookup (fst result) r' = None then Some l
               else if w\<^sub>\<pi> l r' + off l
                       < w\<^sub>\<pi> (the (ben_lookup (fst result) r')) r' +
                         off (the (ben_lookup (fst result) r'))
                    then Some l else ben_lookup (fst result) r') \<longrightarrow>
              w\<^sub>\<pi> l r' + off l = w\<^sub>\<pi> ll r' + off ll \<longrightarrow>
              r' \<notin> fst ` heap_abstract (snd result) \<and>
              (\<exists>y. ben_lookup (fst result) r' = Some y)"
             "r' \<in> vset_to_set (right_neighbs l)"
             "(r', b) \<in> heap_abstract (snd result)" for b
              using  "1"(1)  single_update(3,5) that
              by force
            have helper2: False
              if "\<forall>ll. Some ll =
              (if ben_lookup (fst result) r' = None then Some l
               else if w\<^sub>\<pi> l r' + off l
                       < w\<^sub>\<pi> (the (ben_lookup (fst result) r')) r' +
                         off (the (ben_lookup (fst result) r'))
                    then Some l else ben_lookup (fst result) r') \<longrightarrow>
              w\<^sub>\<pi> l r' + off l = w\<^sub>\<pi> ll r' + off ll \<longrightarrow>
              r' \<notin> fst ` heap_abstract (snd result) \<and>
              (\<exists>y. ben_lookup (fst result) r' = Some y)"
             "(r', b) \<in> heap_abstract (snd result)"
             " w\<^sub>\<pi> l r' + off l
              \<le> w\<^sub>\<pi> (the (ben_lookup (fst result) r')) r' +
            off (the (ben_lookup (fst result) r'))" for b
              apply(cases "ben_lookup (fst result) r' = None")
               apply (all \<open>cases "w\<^sub>\<pi> l r' + off l < w\<^sub>\<pi> (the (ben_lookup (fst result) r')) r'
                                            + off (the (ben_lookup (fst result) r'))"\<close>)
              using  that
              by force+
            have helper3: False
              if "\<forall>ll. Some ll =
              (if ben_lookup (fst result) r' = None then Some l
               else if w\<^sub>\<pi> l r' + off l
                       < w\<^sub>\<pi> (the (ben_lookup (fst result) r')) r' +
                         off (the (ben_lookup (fst result) r'))
                    then Some l else ben_lookup (fst result) r') \<longrightarrow>
              w\<^sub>\<pi> (the (ben_lookup (fst result) r')) r' +
              off (the (ben_lookup (fst result) r')) =
              w\<^sub>\<pi> ll r' + off ll \<longrightarrow>
              r' \<notin> fst ` heap_abstract (snd result) \<and>
              (\<exists>y. ben_lookup (fst result) r' = Some y)"
         "(r', b) \<in> heap_abstract (snd result)"
         "w\<^sub>\<pi> (the (ben_lookup (fst result) r')) r' +
         off (the (ben_lookup (fst result) r'))
         \<le> w\<^sub>\<pi> l r' + off l" for b
            using  that IH_applied(3)
              by (force simp add: if_split)+
            from 1 show ?thesis  
               using IH_applied(3)
             unfolding single_update(6) 
             by(force intro!: helper1 
                       intro: helper2 helper3 
                    simp add: single_update(5)
                      intro!: P_of_minI[of  _ _ "\<lambda> x. (r', x) \<in> heap_abstract (snd result)"]
                       elim!: P_of_minE[of "\<lambda> x. k = x"])
         qed
       qed (auto simp add: single_update(5,6) rev_image_eqI if_split)       
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
           proof(rule, all \<open>rule\<close>, goal_cases)
             case (1 rk)
             show ?case 
             proof(rule UnE[OF 1], goal_cases)
               case 1
               then show ?case 
                 by (force simp add:  single_update(5))
             next
               case 2
               then obtain r ll where rll:"rk = (r, w\<^sub>\<pi> ll r + off ll)"
                                      "r \<in> vset_to_set (right_neighbs l)"
                                      "Some ll = ben_lookup ben' r"
                 "r \<in> fst `
                (heap_abstract queue -
                {(r, k) | r k l. r \<in> vset_to_set (right_neighbs l) \<and> l \<in> set ls} \<union>
                { (r, w\<^sub>\<pi> ll r + off ll) | r ll l. 
                      r \<in> vset_to_set (right_neighbs l) \<and>
                      l \<in> set ls \<and>
                      Some ll = ben_lookup (fst result) r \<and>
                      (r \<in> fst ` heap_abstract queue \<or> ben_lookup ben r = None)})
                \<or>  ben_lookup (fst result) r = None"
                 by blast
               have helper: "\<lbrakk>ben_lookup (fst result) r = Some y;
                   ben_lookup ben r = Some ya\<rbrakk> \<Longrightarrow> \<exists>x\<in>heap_abstract queue. r = fst x" 
                 "\<lbrakk>ben_lookup (fst result) r = None; ben_lookup ben r = Some y\<rbrakk> \<Longrightarrow> \<exists>x\<in>heap_abstract queue. r = fst x"
                 for y ya
                 using IH_applied rll(4) 
                 by fastforce+
               show ?case 
                 unfolding if_split image_iff  single_update(5)
                 apply(rule CollectI)
                 apply(rule exI[of _ r])
                 apply(rule exI[of _ l])
                 apply(rule exI[of _ ll])
                 by(auto simp add: rll  single_update(5) intro: helper)
             qed
           next
             case (2 rk)
             then obtain r la ll where rk: "rk = (r, w\<^sub>\<pi> ll r + off ll)"
             "r \<in> vset_to_set (right_neighbs la)"
             "la \<in> set (l # ls)"
             "Some ll = ben_lookup ben' r"
             "(r \<in> fst ` heap_abstract queue \<or> ben_lookup ben r = None)"
               by auto
             show ?case 
             proof(cases "la = l")
               case True
               have helper: 
            "\<lbrakk>ben_lookup ben r = None; ben_lookup (fst result) r = Some y\<rbrakk> \<Longrightarrow>
             \<exists>b. (r, b) \<in> heap_abstract queue \<and>
             (\<forall>l. r \<in> vset_to_set (right_neighbs l) \<longrightarrow> l \<notin> set ls) \<or>
             b = w\<^sub>\<pi> y r + off y \<and> (\<exists>l. r \<in> vset_to_set (right_neighbs l) \<and> l \<in> set ls)" for y
                 using IH_applied(5) by force
               from True show ?thesis 
                 using rk 
                 unfolding single_update(5)
                 by (auto intro: helper simp add: image_iff Diff_iff Bex_def)+
             next
               case False
               then show ?thesis 
               using rk 
               unfolding single_update(5) if_split
               apply(cases "r \<notin> vset_to_set (right_neighbs l)")
                apply(all \<open>cases "ben_lookup (fst result) r = None"\<close>)
               by(auto simp add: image_iff Bex_def)+
             qed
           qed
         qed auto
       qed
     qed
   qed auto
   thus ?thesis1 ?thesis2 ?thesis4       
        "\<And> r. r \<notin> \<Union> {vset_to_set (right_neighbs l)| l. l \<in> set ls} 
                 \<Longrightarrow> ben_lookup ben' r = ben_lookup ben r"
        "\<And> r. r \<in> \<Union> {vset_to_set (right_neighbs l)| l. l \<in> set ls} 
                 \<Longrightarrow> \<exists> l. ((l \<in> set ls \<and> r \<in> vset_to_set (right_neighbs l))
                             \<or> Some l = ben_lookup ben r) 
                          \<and> w\<^sub>\<pi> l r + off l = conn_min r \<and> ben_lookup ben' r = Some l"
        "\<And> r k. (r, k) \<in> heap_abstract queue' \<Longrightarrow>
         (\<exists> l. ben_lookup ben' r = Some l \<and> k = w\<^sub>\<pi> l r + off l)"
       "\<And> r l' l. ben_lookup ben' r = Some l' \<and> (\<nexists> k. (r, k) \<in> heap_abstract queue') \<Longrightarrow>
             off l \<ge> w\<^sub>\<pi> l' r + off l'"
    by auto
qed

subsection \<open>Invariant Preservation\<close>

lemma invar_pres_one_step:
  assumes "search_path_loop_cont_cond state"
    "invar_basic state"
    "invar_feasible_potential state"
    "invar_forest_tight state"
    "invar_matching_tight state"
    "invar_best_even_neighbour_heap state"
    "invar_best_even_neighbour_map state"
    "invar_out_of_heap state"
  shows "invar_basic (search_path_loop_cont_upd state)"
    "invar_feasible_potential (search_path_loop_cont_upd state)"
    "invar_forest_tight (search_path_loop_cont_upd state)"
    "invar_matching_tight (search_path_loop_cont_upd state)"
    "invar_best_even_neighbour_heap (search_path_loop_cont_upd state)"
    "invar_best_even_neighbour_map (search_path_loop_cont_upd state)"
    "invar_out_of_heap (search_path_loop_cont_upd state)"
    "card (aevens (search_path_loop_cont_upd state) \<union>
                 aodds (search_path_loop_cont_upd state)) = 
        card (aevens state \<union> aodds state)+2"
proof-
  define F where "F = forest state"
  define ben where "ben = best_even_neighbour state"
  define missed_\<epsilon> where  "missed_\<epsilon> = missed_at state"
  obtain queue heap_min where queue_heap_min_def:
    " (queue, heap_min) = heap_extract_min (heap state)"
    by(cases "heap_extract_min (heap state)") auto
  obtain r where r_def: "heap_min = Some r"
    using queue_heap_min_def assms(1)
    by(auto elim: search_path_loop_cont_condE)
  define l where "l = the (ben_lookup ben r)"
  define acc' where "acc' = w\<^sub>\<pi> l r + missed_\<epsilon> l"
  obtain l' where l'_def: "buddy r = Some l'"
    using queue_heap_min_def assms(1)
    by(auto elim: search_path_loop_cont_condE simp add: r_def)
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
  have upd_state_is_state':"search_path_loop_cont_upd state =  state'"
    using ben'_queue'_def r_def l'_def queue_heap_min_def
    by(auto simp add: search_path_loop_cont_upd_def state'_def Let_def
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
      using   1 higher_forest_properties(3)[of \<M> F]
      by(force intro: invar_basicE[OF assms(2)] 
          simp add: F_def   insert_commute)
    thus False
      using r_unclassified by blast
  qed
  have r_not_even_or_odd:
    "r \<in> vset_to_set (evens F) \<union>  vset_to_set (odds F) \<Longrightarrow> False"
    using F_def r_unclassified by fastforce
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
  have ben_l'_None:"ben_lookup ben l' = None"
    using  bipartite_edgeD(1)[OF _ G(1)] edges_are_Vs_2[OF r_l'_in_G] 
      l'_in_L l'_not_even_or_odd  r_l'_in_G assms(2)
    by (auto elim!: invar_basicE 
        intro!: invar_best_even_neighbour_mapD(1)[OF assms(7), of l']
        simp add: ben_def F_def)
  have l'_not_a_ben: "ben_lookup ben rr = Some l' \<Longrightarrow> False" for rr 
    using F_def assms(2)  l'_not_even 
    by(force elim!: invar_basicE simp add:  ben_def) 
  have queue'_is: "heap_abstract (fst (heap_extract_min (heap state))) =
         heap_abstract (heap state) - {(r, w\<^sub>\<pi> l r + missed_at state l)}"
    using assms(2) k(1) k_is
    by(intro heap(8))
      (auto elim!: invar_basicE 
        simp add: r_def[symmetric] pair_eq_fst_snd_eq[OF queue_heap_min_def])
  note basic_invars = invar_basicD[OF assms(2)]
  have "r \<noteq> l" "l \<noteq> l'" "r \<noteq> l'"
    using r_l_props(2) r_unclassified  bipartite_edgeD(2)[OF r_l'_in_G  G(1)] r_in_R 
          F_def l'_not_even by auto
  hence forest_extension_precond: "forest_extension_precond F \<M> l r l'"
    using l'_not_even_or_odd r_not_even_or_odd l_r_not_in_M 
    by(auto intro!: forest_extension_precondI  \<M>_is_matching
        simp add: F_def assms(2) invar_basicD(1) r_l_props(2)  r_l'_in_M)
  have missed'_is: "abstract_real_map (missed_lookup missed') = 
                    (\<lambda> x. if x = r \<or> x = l' then acc' else missed_at state x)"
    using invar_basicD(4)[OF assms(2)]
    by(auto simp add: missed'_def acc'_def abstract_real_map_def missed(3,4))
  have queue_props: "heap_invar queue" 
    "heap_abstract queue = heap_abstract (heap state) - {(r, acc')}"
    "\<And> r' k'. (r', k') \<in> heap_abstract (heap state) \<Longrightarrow> acc' \<le> k'"
    using invar_basicD(3)[OF assms(2)] heap(2)[of "heap state"] k(2) k_is 
    by (auto simp add: pair_eq_fst_snd_eq[OF queue_heap_min_def] missed_\<epsilon>_def  acc'_def   queue'_is )
  have update_best_even_neighbour_conditions:
    "ben_invar ben" "heap_invar queue" "l' \<in> L"
    "\<And>r k. (r, k) \<in> heap_abstract queue \<longrightarrow>  
            (\<exists>l. ben_lookup ben r = Some l \<and>
             k = w\<^sub>\<pi> l r + abstract_real_map (missed_lookup missed') l)"
    "\<And>r l'a. ben_lookup ben r = Some l'a \<and> (\<nexists>k. (r, k) \<in> heap_abstract queue) \<longrightarrow>
                 w\<^sub>\<pi> l'a r + abstract_real_map (missed_lookup missed') l'a
                \<le> abstract_real_map (missed_lookup missed') l'"
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
      using l'_not_even r_not_even_or_odd 
            invar_best_even_neighbour_mapD[OF assms(7), of rr]
      by(fastforce intro: exI[of _ "the (ben_lookup (best_even_neighbour state) rr)"]
                simp add: ben_def pair_eq_fst_snd_eq[OF queue_heap_min_def] F_def
                          queue'_is missed'_is invar_best_even_neighbour_heapD[OF assms(6)])
  next
    case (5 rr ll)
    show ?case 
    proof(rule, goal_cases)
      case 1
      note One = this
      hence h1:"r \<noteq> ll"
        using assms(2)  r_not_even_or_odd 
        by(force elim!: invar_basicE simp add: ben_def F_def)
      have h2: "ll \<noteq> l'"
        using l'_not_a_ben 1 by blast
      have cases:"(\<nexists>k. (rr, k) \<in> heap_abstract (heap state)) \<or> rr = r"
        using 1 unfolding queue_props(2) by blast
      have ll_ben_of_rr_old:"ben_lookup (best_even_neighbour state) rr = Some ll" 
        using One ben_def by fastforce
      show ?case
        unfolding missed'_is
        apply(subst (2) if_P,  simp)
        apply(subst if_not_P)
        using h1 h2 apply simp
      proof(cases rule: disjE[OF cases], goal_cases)
        case 1
        note one = this
        have "kr\<in>heap_abstract (heap state) \<Longrightarrow> w\<^sub>\<pi> ll rr + missed_at state ll \<le> snd kr" for kr
          using invar_out_of_heapD[OF assms(8) ll_ben_of_rr_old 1] by simp
        moreover have "(r, w\<^sub>\<pi> l r + missed_at state l) \<in> heap_abstract (heap state)"
          using k(1) k_is by blast
        ultimately show ?case 
          by(auto simp add: acc'_def missed_\<epsilon>_def)
      next
        case 2
        hence "w\<^sub>\<pi> ll rr + missed_at state ll = acc'"
          using One acc'_def l_def missed_\<epsilon>_def by auto
        thus ?case by blast
      qed
    qed
  qed 
  note after_ben_update = update_best_even_neighbour_correct[OF
      update_best_even_neighbour_conditions ben'_queue'_def]
  have F'_is: "abstract_forest F' = abstract_forest F \<union> {{l, r}, {r, l'}}"
    "vset_to_set (evens F') = insert l' (vset_to_set (evens F))"
    "vset_to_set (odds F') = insert r (vset_to_set (odds F))"
    "vset_invar (evens F')"  "vset_invar (odds F')"
    "forest_invar \<M> F'"
    using F'_def forest_extend(1,2,3,4)[OF forest_extension_precond] 
      evens_and_odds(1,2) by force+
  show invar_basic_step: "invar_basic (search_path_loop_cont_upd state)"
    unfolding upd_state_is_state'
  proof(rule invar_basicI, goal_cases )
    case 1
    then show ?case 
      by(auto intro!: forest_extend(1) 
          simp add: state'_def F'_def forest_extension_precond)
  next
    case 2
    then show ?case
      using after_ben_update(1)
      by(auto simp add: state'_def)
  next
    case 3
    then show ?case 
      by (simp add: after_ben_update(2) state'_def)
  next
    case 4
    then show ?case
      by (simp add: assms(2) invar_basicD(4) missed'_def missed(3) state'_def)
  next
    case 5
    then show ?case
      using assms(2)
      by(auto elim: invar_basicE 
          simp add: state'_def F'_is(1) edge_commute r_l_props(1) r_l'_in_G F_def)
  next
    case 6
    then show ?case 
    proof(rule, goal_cases)
      case (1 x)
      thus ?case
        using assms(2)
        apply(cases \<open>ben_lookup (best_even_neighbour state) x = None\<close>)
         apply(all \<open>cases "x \<notin> vset_to_set (right_neighbs l')"\<close>)
        by(auto elim!: invar_basicE 
            simp add: state'_def after_ben_update(5) ben_def G(6) 
            edges_are_Vs_2 l'_in_L)
    qed
  next
    case 7
    then show ?case 
      using assms(2) r_unclassified edges_are_Vs_2[OF r_l'_in_G]
      by(force elim!: invar_basicE
          simp add: state'_def missed'_def missed(3,4) if_split[of "\<lambda> x. x = Some _"])
  next
    case 8
    then show ?case 
    proof(rule, goal_cases)
      case (1 x)
      then obtain k where "(x, k) \<in> heap_abstract queue \<or> x \<in> vset_to_set (right_neighbs l')" 
        by(fastforce simp add: state'_def  after_ben_update(6))
      thus ?case 
        using assms(2) G(6) l'_in_L
        by(auto elim!: invar_basicE simp add: queue_props(2))
    qed
  next
    case 9
    show ?case
      using assms(2) l'_in_L
      by(auto elim!: invar_basicE simp add: state'_def F'_is F_def)
  next
    case 10
    show ?case
      using assms(2) r_in_R
      by(auto elim!: invar_basicE simp add: state'_def F'_is F_def)
  next
    case 11
    show ?case
      using assms(2)
      by(auto elim!: invar_basicE 
          simp add: F_def ben_def F'_is state'_def after_ben_update(5))+
  next
    case 12 
    show ?case 
      using r_l'_in_G basic_invars(12)
      by(auto simp add: state'_def F'_is F_def ben_def after_ben_update(5) G(6)[OF  l'_in_L] insert_commute)
  qed
  have F_invar:"forest_invar \<M> (forest state)" "vset_invar (evens (forest state))"
    "vset_invar (odds (forest state))"
    using assms(2) by(auto elim!: invar_basicE intro: evens_and_odds)

  show "invar_feasible_potential (search_path_loop_cont_upd state)"
    unfolding upd_state_is_state'
  proof(rule invar_feasible_potentialI, goal_cases)
    case (1 u v)
    then obtain u' v' where u'v': "{u', v'} = {u, v}" "u' \<in> L" "v' \<in> R"  "{u', v'} \<in> G"
      using G(1) by(force elim!: bipartite_edgeE)
    have u'v'_cases: P 
      if "\<lbrakk>u' \<in> insert l (aevens state); v' \<in> insert r (aodds state)\<rbrakk> \<Longrightarrow> P"
        "\<lbrakk>u' \<notin> insert l (aevens state); v' \<in> insert r (aodds state)\<rbrakk> \<Longrightarrow> P"
        "\<lbrakk>u' \<in> insert l (aevens state); v' \<notin> insert r (aodds state)\<rbrakk> \<Longrightarrow> P"
        "\<lbrakk>u' \<notin> insert l (aevens state); v' \<notin> insert r (aodds state)\<rbrakk> \<Longrightarrow> P" for P
      using that by blast
    have "\<pi>\<^sup>* state' u' + \<pi>\<^sup>* state' v' \<le> \<w> u' v'"
    proof(rule u'v'_cases, goal_cases)
      case 1
      have simple_step1: "\<pi> l + (\<pi> v' + missed_at state v') \<le> \<w> l v' + missed_at state l"
        if "u' = l" "v' \<notin> aevens state"
          "v' \<in> aodds state"
          "l \<in> aevens state"
        using invar_feasible_potentialD[OF assms(3) u'v'(4)] that
        by(simp add: working_potential_def vset(5)[OF F_invar(2)] 
            vset(5)[OF F_invar(3)])
      have simple_step2: "\<pi> u' + (\<pi> v' + missed_at state v') \<le> \<w> u' v' + missed_at state u'"
        if  "v' \<notin> aevens state" "u' \<in> aevens state""v' \<in> aodds state"
        using invar_feasible_potentialD[OF assms(3) u'v'(4)] that
        by(simp add: working_potential_def vset(5)[OF F_invar(2)] 
            vset(5)[OF F_invar(3)])
      have hard_step: "\<w> l r + (\<pi> u' + missed_at state l) \<le> \<w> u' r + (\<pi> l + missed_at state u')"
        if "v' = r" "u' \<in> aevens state " 
      proof-
        have "w\<^sub>\<pi> l r + missed_at state l \<le> w\<^sub>\<pi> u' r + missed_at state u'"
          using F_invar(1) finite_forest(1) that u'v'(4) 
          by(auto intro!: linorder_class.Min.coboundedI exI[of _ u'] simp add: r_l_props(3))
        then show ?thesis
          using that
          by(auto simp add: w\<^sub>\<pi>_def)
      qed
      from 1 show ?case using G(8)[OF  u'v'(4)]  
        using l'_not_even l'_not_even_or_odd r_l_props(2) r_not_even_or_odd 
          evens_and_odds(4)[OF F_invar(1)] 
          bipartite_edgeD(2)[OF r_l'_in_G G(1) r_in_R] r_in_R 
        by(auto intro: simple_step1 simple_step2 hard_step 
            simp add: algebra_simps missed'_is F_def missed_\<epsilon>_def acc'_def w\<^sub>\<pi>_def 
            F'_is(2,3) vset(5)[OF F'_is(4)] vset(5)[OF F'_is(5)] vset(5)[OF F_invar(2)] 
            vset(5)[OF F_invar(3)] state'_def working_potential_def)
    next
      case 2
      have helper1: "\<pi> l' + (\<pi> v' + missed_at state v') \<le> \<w> l' v' + (missed_at state l + w\<^sub>\<pi> l r)"
        if  "l \<in> aevens state" "(r \<in> aevens state \<or> r \<in> aodds state \<Longrightarrow> False)"
          "l' \<notin> aevens state" "v' \<in> aodds state" "u' = l'"
          "l' \<notin> aodds state" "v' \<notin> aevens state"
        using invar_feasible_potentialD[OF assms(3)  r_l_props(1)] that
          invar_feasible_potentialD[OF assms(3) u'v'(4)] r_l_props(1) u'v'(4)   
        by(auto simp add: w\<^sub>\<pi>_def working_potential_def vset(5)[OF F_invar(2)] 
            vset(5)[OF F_invar(3)]  if_split[of "\<lambda> x. x + _ \<le> \<w> _ _"] G(7))
      have helper2: "\<pi> u' + (\<pi> v' + missed_at state v') \<le> \<w> u' v' + (missed_at state l + w\<^sub>\<pi> l r)"
        if "l \<in> aevens state" "r \<in> aevens state \<or> r \<in> aodds state \<Longrightarrow> False"
          "u' \<notin> aevens state" "v' \<in> aodds state" "u' \<notin> aodds state" 
          "v' \<notin> aevens state"
        using invar_feasible_potentialD[OF assms(3)  r_l_props(1)] that
          invar_feasible_potentialD[OF assms(3) u'v'(4)] r_l_props(1) u'v'(4)   
        by(auto simp add: w\<^sub>\<pi>_def working_potential_def vset(5)[OF F_invar(2)] 
            vset(5)[OF F_invar(3)]  if_split[of "\<lambda> x. x + _ \<le> \<w> _ _"] G(7))
      from 2 show ?case 
        using  r_l_props(2) r_not_even_or_odd evens_and_odds(4)[OF F_invar(1)] 
          r_in_R G(8)[OF u'v'(4)] invar_basicD(10)[OF assms(2)]
          bipartite_edgeD(4)[OF u'v'(4) G(1)] 
        by (auto intro: helper1 helper2 
            simp add: missed_\<epsilon>_def acc'_def F_def vset(5)[OF F'_is(4)]
            state'_def working_potential_def  vset(5)[OF F'_is(5)]
            vset(5)[OF F_invar(2)] vset(5)[OF F_invar(3)] F'_is(2,3) 
            missed'_is algebra_simps)
    next
      case 3
      have  helper1: "\<w> l r + (\<pi> u' + (\<pi> v' + missed_at state l))
                       \<le> \<w> u' v' + (\<pi> l + (\<pi> r + missed_at state u'))"
        if "v' \<notin> aodds state" "v' \<notin> aevens state" "u' \<in> aevens state"
      proof-
        note That = that
        obtain lu where lu: "Some lu = ben_lookup (best_even_neighbour state) v'"
          "{v', lu} \<in> G"
          "lu \<in> aevens state"
          "w\<^sub>\<pi> lu v' + missed_at state lu =
               Min {w\<^sub>\<pi> l v' + missed_at state l | l. l \<in> aevens state \<and> {l, v'} \<in> G}"
          using That edges_are_Vs_2
            invar_best_even_neighbour_mapD(2)[OF assms(7), of v'] u'v'(4) 
          by force
        have "w\<^sub>\<pi> lu v' + missed_at state lu \<le> w\<^sub>\<pi> u' v' + missed_at state u'"
          using F_invar(1) finite_forest(1) that u'v'(4) 
          by(auto intro!: linorder_class.Min.coboundedI exI[of _ u'] 
              simp add: lu(4))
        moreover have "w\<^sub>\<pi> l r + missed_at state l \<le> w\<^sub>\<pi> lu v' + missed_at state lu"
          using lu(1) insert_commute u'v'(4) That 
          by(intro k(2)[simplified k_is, of v'])
            (auto simp add: invar_best_even_neighbour_heapD[OF assms(6)])
        ultimately show ?thesis
          by(auto simp add: w\<^sub>\<pi>_def)
      qed
      from 3 show ?case             
        using l'_not_even r_l_props(2) r_not_even_or_odd l'_in_L u'v'(2)
          evens_and_odds(4)[OF F_invar(1)]  bipartite_edgeD(3)[OF  u'v'(4) G(1)]
          invar_basicD(9)[OF assms(2)]  helper1 
        by (auto simp add: state'_def working_potential_def vset(5)[OF F'_is(5)] 
            vset(5)[OF F'_is(4)] F'_is(2,3) missed_\<epsilon>_def acc'_def 
            F_def missed'_is algebra_simps w\<^sub>\<pi>_def)
    next
      case 4
      have "\<pi>\<^sup>* state' u' = \<pi>\<^sup>* state u'" 
        using 4 r_unclassified  l'_not_even_or_odd invar_basicD(10)[OF assms(2)] bipartite_edgeD(2)[OF u'v'(4) G(1)]
          u'v'(3)
        by(auto simp add: state'_def working_potential_def vset(5)[OF F'_is(5)] 
            vset(5)[OF F'_is(4)] F'_is(2,3) missed'_is 
            vset(5)[OF F_invar(2)] vset(5)[OF F_invar(3)] F_def)
      moreover have "\<pi>\<^sup>* state' v' = \<pi>\<^sup>* state v'" 
        using 4 invar_basicD(9,10)[OF assms(2)] u'v'(3) bipartite_vertex(1)[OF _ G(1)]
          edges_are_Vs_2[OF u'v'(4)]
        by(auto simp add: state'_def working_potential_def vset(5)[OF F'_is(5)] 
            vset(5)[OF F'_is(4)] F'_is(2,3) missed'_is 
            vset(5)[OF F_invar(2)] vset(5)[OF F_invar(3)] F_def)
      ultimately show ?case 
        using assms(3) u'v'(4)
        by(auto elim!: invar_feasible_potentialE)
    qed
    thus ?case
      using G(7)[OF u'v'(4)] u'v'(1)
      by(auto simp add: doubleton_eq_iff)
  qed
  show "invar_forest_tight (search_path_loop_cont_upd state)"
    unfolding upd_state_is_state'
  proof(rule invar_forest_tightI, goal_cases)
    case (1 u v)
    hence "{u, v} \<in> abstract_forest F \<union> {{l, r}, {r, l'}}"
      by(auto simp add: state'_def F'_is(1))
    moreover have "{u, v} \<in> abstract_forest F \<Longrightarrow> ?case"
    proof(goal_cases)
      case 1
      then obtain u' v' where u'v':"u' \<in> aevens state" "v' \<in> aodds state"
        "{u, v} = {u', v'}"
        using edges_are_Vs[of u v "abstract_forest F"]
          evens_and_odds(3)[OF  basic_invars(1)] edges_are_Vs[of v u "abstract_forest F"]
          higher_forest_properties(3)[OF  basic_invars(1), of u v] 
        unfolding F_def by blast
      have "\<w> u' v' = \<pi>\<^sup>* state' u' + \<pi>\<^sup>* state' v'"
        using l'_not_even u'v'(1,2) r_unclassified l'_not_even_or_odd 1
          evens_and_odds(4)[OF basic_invars(1)] invar_forest_tightD[OF assms(4), of u' v']
        by(auto simp add: state'_def  working_potential_def vset(5)[OF F'_is(5)] 
            vset(5)[OF F'_is(4)] F'_is(2,3) missed'_is 
            vset(5)[OF F_invar(2)] vset(5)[OF F_invar(3)] F_def u'v'(3))
      thus ?case 
        using "1" F_def G(7)[of u v] basic_invars(5) 
          u'v'(3)
        by(auto simp add: doubleton_eq_iff)
    qed
    moreover have "\<w> l r = \<pi>\<^sup>* state' l + \<pi>\<^sup>* state' r"
      using l'_not_even  r_unclassified  r_l_props(2)
        bipartite_edgeD(1)[OF r_l'_in_G G(1)] l'_in_L
      by(auto simp add: state'_def  working_potential_def  vset(5)[OF F'_is(4)]
          F'_is(2,3) missed'_is  F_def missed_\<epsilon>_def acc'_def w\<^sub>\<pi>_def)
    moreover have "\<w> l' r = \<pi>\<^sup>* state' l' + \<pi>\<^sup>* state' r"
      using bipartite_edgeD(1)[OF r_l'_in_G G(1)] l'_in_L
      by(auto simp add: state'_def  working_potential_def missed'_is F_def missed_\<epsilon>_def
          acc'_def w\<^sub>\<pi>_def edge_commute matching(3) r_l'_in_M)
    ultimately show ?case 
      by (auto simp add: doubleton_eq_iff G(7) r_l_props(1) r_l'_in_G)
  qed
  show "invar_matching_tight (search_path_loop_cont_upd state)"
    unfolding upd_state_is_state'
  proof(rule invar_matching_tightI, goal_cases)
    case (1 u v)
    note uv_in_M = this
    show ?case
    proof(cases "{u, v} \<inter> Vs (abstract_forest F) = {}")
      case True
      hence no_inter:"{u, v} \<inter> (aevens state \<union> aodds state) = {}" 
        using edges_are_Vs_2 evens_and_odds(3)[OF F_invar(1)]
          higher_forest_properties(2)[OF F_invar(1), of u v] uv_in_M 
        by (auto simp add: F_def)
      have "\<pi>\<^sup>* state' u = \<pi>\<^sup>* state u" "\<pi>\<^sup>* state' v = \<pi>\<^sup>* state v"
        using F_def l'_not_even r_unclassified l'_not_even_or_odd no_inter
        by(auto simp add: state'_def  working_potential_def vset(5)[OF F'_is(5)] 
            vset(5)[OF F'_is(4)] F'_is(2,3) missed'_is 
            vset(5)[OF F_invar(2)] vset(5)[OF F_invar(3)] F_def )
      thus ?thesis 
        using assms(5) invar_matching_tightD uv_in_M 
        by auto
    next
      case False
      then obtain u' v' where u'v': "{u, v} = {u', v'}" "u' \<in> aevens state" "v' \<in> aodds state"
        apply(cases rule: disjE[OF higher_forest_properties(2)[OF
                basic_invars(1) uv_in_M]])
        using evens_and_odds(3)[OF basic_invars(1)] uv_in_M
          higher_forest_properties(3)[OF basic_invars(1)]
        by(unfold F_def) blast+
      have v'_not_even: "v' \<notin> aevens state" 
        using basic_invars(1) evens_and_odds(4) u'v'(3) by fastforce
      show ?thesis 
        unfolding state'_def  working_potential_def
        using matching(3)[OF r_l'_in_M]  l'_not_even_or_odd u'v'(1,2,3)  v'_not_even r_not_even_or_odd  evens_and_odds(4)[OF basic_invars(1)]
          invar_matching_tightD[OF assms(5)  uv_in_M]
        by auto (force simp add:  working_potential_def vset(5)[OF F_invar(2)] 
            vset(5)[OF F_invar(3)] F_def  missed'_is missed_\<epsilon>_def
            vset(5)[OF F'_is(5)]  vset(5)[OF F'_is(4)] F'_is(2,3))+
    qed
  qed
  show invar_best_even_neighbour_heap_step: 
    "invar_best_even_neighbour_heap (search_path_loop_cont_upd state)"
    unfolding upd_state_is_state'
  proof(rule invar_best_even_neighbour_heapI, goal_cases)
    case 1
    show ?case 
    proof(rule, all \<open>rule\<close>, goal_cases)
      case (1 rk)
      obtain rr kk where rk: "rk = (rr, kk)" by(cases rk) auto
      note queue'_is_that = after_ben_update(6)[simplified queue_props(2)]
      note 1 = 1[simplified state'_def, simplified]
      show ?case
      proof(cases rule: UnE[OF 1[simplified queue'_is_that], simplified  rk])
        case 1
        show ?thesis 
        proof(cases rule: UnE[OF 1])
          case 1
          then obtain ll where ll: "rr \<in> Vs G - aevens state - aodds state"
            "kk = w\<^sub>\<pi> ll rr + missed_at state ll"
            "ben_lookup (best_even_neighbour state) rr = Some ll" 
            using invar_best_even_neighbour_heapD[OF assms(6)]
            by auto
          have "rr \<in> Vs G - aevens state' - aodds state'" 
            using ll ben_l'_None 1
            by(auto simp add: ben_def state'_def F'_is(2,3) F_def missed_\<epsilon>_def  acc'_def l_def)
          moreover have " kk = w\<^sub>\<pi> ll rr + missed_at state' ll"
            using ll 1 update_best_even_neighbour_conditions(4)[of rr kk] 
            by(auto simp add: state'_def missed_\<epsilon>_def  l_def
                missed'_is acc'_def queue_props(2) ben_def)
          moreover have "ben_lookup (best_even_neighbour state') rr = Some ll"
            using ll 1
            by(auto simp add: state'_def  missed_\<epsilon>_def  l_def missed'_is ben_def
                after_ben_update(5))
          ultimately show ?thesis
            by(simp add: rk) 
        next
          case 2
          hence rk_props:
            "kk = min (w\<^sub>\<pi> l' rr + abstract_real_map (missed_lookup missed') l')
                 (w\<^sub>\<pi> (the (ben_lookup ben rr)) rr +
                 abstract_real_map (missed_lookup missed') (the (ben_lookup ben rr)))"
            "rr \<in> vset_to_set (right_neighbs l')"
            "rr \<in> fst ` (heap_abstract (heap state) - {(r, acc')})" by auto
          obtain k_old where k_old: "(rr, k_old) \<in> heap_abstract (heap state) - {(r, acc')}"
            using rk_props(3) by force
          have "rr \<in> Vs G - aevens state' - aodds state'"
            using  ben_l'_None k_old basic_invars(8) 
              update_best_even_neighbour_conditions(4)[of rr k_old]
            by(auto simp add: ben_def state'_def F'_is(2,3) image_subset_iff
                F_def missed_\<epsilon>_def  acc'_def l_def queue_props(2) 
                invar_best_even_neighbour_heapD[OF assms(6)])
          moreover have "(\<exists>l. kk = w\<^sub>\<pi> l rr +  missed_at state' l \<and>
                         ben_lookup (best_even_neighbour state') rr = Some l)"
            unfolding rk_props(1)
          proof(rule P_of_minI_strict1, goal_cases)
            case 1
            have "ben_lookup (best_even_neighbour state') rr = Some l'" 
              using rk_props(2) 1 by(auto simp add: state'_def after_ben_update(5))  
            then show ?case 
              by(auto simp add: state'_def)
          next
            case 2
            hence "ben_lookup (best_even_neighbour state') rr = 
                   ben_lookup (best_even_neighbour state) rr "
              using rk_props(2) update_best_even_neighbour_conditions(4)[of rr k_old] k_old 
              by(auto simp add: state'_def after_ben_update(5) queue_props(2) ben_def)
            then show ?case 
              using l'_not_a_ben rk_props(2)
              by (auto simp add: state'_def  after_ben_update(5) ben_def if_split[of "\<lambda> x. x = _  rr"])
          qed
          ultimately show ?thesis 
            by(simp add: rk)
        qed
      next
        case 2
        hence rr_kk_props: "kk = w\<^sub>\<pi> l' rr + abstract_real_map (missed_lookup missed') l'"
          "rr \<in> vset_to_set (right_neighbs l')" "ben_lookup ben rr = None"
          by auto
        have "rr \<in> Vs G - aevens state' - aodds state'" 
          using   basic_invars(9) rr_kk_props  G(6)[OF l'_in_L]
            bipartite_edgeD(1)[of rr l', OF _ G(1)] l'_in_L basic_invars(12)
            rr_kk_props(2)  edge_commute[of l' rr] invar_best_even_neighbour_mapD[OF assms(7), of rr]
            r_l_props(1,2) r_unclassified edge_commute[of rr]
          by(auto simp add: ben_def state'_def F'_is(2,3) F_def  
              invar_best_even_neighbour_heapD[OF assms(6)] ) force
        moreover have "ben_lookup ben' rr = Some l'"
          by(auto simp add: after_ben_update(5) rr_kk_props(2,3))
        ultimately show ?thesis 
          by (auto intro!: exI[of _ l']simp add: rk rr_kk_props(1) state'_def)   
      qed
    next
      case (2 rk)
      then obtain rr kk ll where rr_kk_ll:
        "rk = (rr, kk)"
        "rr \<in> Vs G - aevens state - aodds state - {r, l'}"
        "kk = w\<^sub>\<pi> ll rr + abstract_real_map (missed_lookup missed') ll"
        "ben_lookup ben' rr = Some ll" 
        by (auto simp add: state'_def F'_is(2,3) F_def)
      have "(rr, w\<^sub>\<pi> ll rr + abstract_real_map (missed_lookup missed') ll) \<in> heap_abstract queue'"
      proof(rule if_E[of "\<lambda> x. x = Some ll", OF
            rr_kk_ll(4)[simplified after_ben_update(5)]], goal_cases)
        case 1
        then show ?case 
          using invar_basicD(11)[OF assms(2)] r_not_even_or_odd
            l'_not_a_ben[of rr] rr_kk_ll(2)
          by (auto simp add: after_ben_update(6) queue_props(2) missed'_is acc'_def missed_\<epsilon>_def 
              ben_def F_def  invar_best_even_neighbour_heapD[OF assms(6)])
      next
        case 2
        note Two = this
        show ?case 
        proof(rule if_E[of "\<lambda> x. x = Some ll", OF 2(2)], goal_cases)
          case 1
          then show ?case 
            using Two(1)
            by (auto simp add: after_ben_update(6)) 
        next
          case 2
          note two = this
          show ?case 
          proof(rule if_E[of "\<lambda> x. x = Some ll", OF 2(2)], goal_cases)
            case 1
            then show ?case 
              using invar_basicD(11)[OF assms(2)] r_not_even_or_odd
                l'_not_a_ben[of rr] rr_kk_ll(1-4) two Two 1
              by (auto simp add: after_ben_update(6) queue_props(2) missed'_is
                  acc'_def missed_\<epsilon>_def ben_def F_def 
                  invar_best_even_neighbour_heapD[OF assms(6)]
                  if_split[of "\<lambda> x. _ < _ + x"  "_ = r \<or> _ = ll"] ) force+
          next
            case 2
            then show ?case
              using invar_basicD(11)[OF assms(2)] r_not_even_or_odd
                l'_not_a_ben[of rr] rr_kk_ll(1-4) 
              by (auto simp add: after_ben_update(6) queue_props(2) missed'_is
                  acc'_def missed_\<epsilon>_def ben_def F_def 
                  invar_best_even_neighbour_heapD[OF assms(6)]) force
          qed
        qed
      qed
      thus ?case
        by(auto simp add: state'_def rr_kk_ll(1,3))
    qed
  qed
  show invar_best_even_neighbour_map_step:
    "invar_best_even_neighbour_map (search_path_loop_cont_upd state)"
    unfolding upd_state_is_state'
  proof(rule invar_best_even_neighbour_mapI, goal_cases)
    case (1 rr)
    then show ?case 
      using invar_best_even_neighbour_mapD(1)[OF assms(7), of rr]
      by(auto simp add: state'_def F'_is(2,3) after_ben_update(5)
          G(6)[OF l'_in_L] missed'_is F_def ben_def)
  next
    case (2 rr)
    note two = this
    show ?case 
    proof(cases "{l', rr} \<in> G")
      case True
      hence rr_in_ngbhd_l':"\<not> rr \<notin> vset_to_set (right_neighbs l')"
        by (simp add: G(6) l'_in_L)
      note true = True
      show ?thesis 
      proof(cases "ben_lookup ben rr = None")
        case True
        have "w\<^sub>\<pi> l' rr + abstract_real_map (missed_lookup missed') l' =
             Min {w\<^sub>\<pi> l rr + abstract_real_map (missed_lookup missed') l | 
             l .(l = l' \<or> l \<in> vset_to_set (evens F)) \<and> {l, rr} \<in> G}"
        proof(rule linorder_class.Min_eqI[symmetric], goal_cases)
          case 1
          then show ?case 
            by(rule rev_finite_subset[of "{w\<^sub>\<pi> l rr + abstract_real_map
                      (missed_lookup missed') l | l rr. {l, rr} \<in> G}"])
                  (auto simp add: finite_G finite_double_image_of_pairs_in_set_of_sets)
        next
          case (2 y)
          have "\<nexists>l. l \<in> aevens state \<and> {l, rr} \<in> G"
            using invar_best_even_neighbour_mapD(2)[OF assms(7), of rr] True true
              basic_invars(12,9) bipartite_edgeD(1)[of l' rr, OF _ G(1)]
              edges_are_Vs_2[of l' rr G]  l'_in_L
            by(auto simp add: ben_def)
          thus ?case 
            using  r_unclassified 2 2
            by(auto simp add: missed'_is F_def)
        next
          case 3
          then show ?case 
            by (auto intro!: exI[of _ l'] simp add: true)
        qed   
        thus ?thesis 
          using True rr_in_ngbhd_l'
          by(auto intro!: exI[of _ l'] 
              simp add: state'_def  after_ben_update(5) edge_commute true F'_is(2))
      next
        case False
        note false = this
        note rr_in_G = two(1)
        moreover have "rr \<notin> aevens state" "rr \<notin> aodds state"  
          using two by (auto simp add: state'_def F'_is(2,3) F_def)
        moreover hence there_is_l:"\<exists>l. l \<in> aevens state \<and> {l, rr} \<in> G" 
          using two(4)
          using invar_best_even_neighbour_mapD(1)[OF assms(7), of rr] True 
            false rr_in_G
          by(force simp add: ben_def)  
        ultimately obtain ll where ll: 
          "ben_lookup (best_even_neighbour state) rr = Some ll"
          "{rr, ll} \<in> G" "ll \<in> aevens state"
          "w\<^sub>\<pi> ll rr + missed_at state ll =
                             Min {w\<^sub>\<pi> l rr + missed_at state l | 
                            l . l \<in> aevens state \<and> {l, rr} \<in> G}"
          using invar_best_even_neighbour_mapD(2)[OF assms(7), of rr] by blast
        have Min_set_is: "{w\<^sub>\<pi> l rr + abstract_real_map (missed_lookup missed') l
               | l. (l = l' \<or> l \<in> vset_to_set (evens F))\<and> {l, rr} \<in> G}
                 = insert (w\<^sub>\<pi> l' rr + abstract_real_map (missed_lookup missed') l')
                   {w\<^sub>\<pi> l rr + missed_at state l | l . l \<in> aevens state \<and> {l, rr} \<in> G}"
          using r_unclassified true l'_not_even by(force simp add: missed'_is F_def)            
        show ?thesis
        proof(cases "w\<^sub>\<pi> l' rr + abstract_real_map (missed_lookup missed') l'
            < w\<^sub>\<pi> (the (ben_lookup ben rr)) rr +
              abstract_real_map (missed_lookup missed') (the (ben_lookup ben rr))")
          case True
          have "w\<^sub>\<pi> l' rr + abstract_real_map (missed_lookup missed') l' =
             Min {w\<^sub>\<pi> l rr + abstract_real_map (missed_lookup missed') l | 
             l .(l = l' \<or> l \<in> vset_to_set (evens F)) \<and> {l, rr} \<in> G}"
          proof(rule linorder_class.Min_eqI[symmetric], goal_cases)
            case 1
            then show ?case 
              by(rule rev_finite_subset[of "{w\<^sub>\<pi> l rr + abstract_real_map
                      (missed_lookup missed') l | l rr. {l, rr} \<in> G}"])
                    (auto simp add: finite_G finite_double_image_of_pairs_in_set_of_sets)
          next
            case (2 y)
            have new_min_is: "w\<^sub>\<pi> l' rr + abstract_real_map (missed_lookup missed') l' = 
                  min (w\<^sub>\<pi> ll rr + missed_at state ll) (w\<^sub>\<pi> l' rr + abstract_real_map (missed_lookup missed') l')"
              using True ll(3,1) l'_not_a_ben[of rr] 
                r_not_even_or_odd
              by(cases "ll = r", all \<open>cases "ll = l'"\<close>)
                (auto simp add: ben_def  missed'_is F_def)
            have "y \<ge> Min {w\<^sub>\<pi> l rr + abstract_real_map (missed_lookup missed') l
               | l. (l = l' \<or> l \<in> vset_to_set (evens F))\<and> {l, rr} \<in> G}" 
              apply(rule linorder_class.Min.coboundedI)
              apply(rule rev_finite_subset[of "{w\<^sub>\<pi> l rr + abstract_real_map
                      (missed_lookup missed') l | l rr. {l, rr} \<in> G}"])
              using 2
              by(auto intro: rev_finite_subset[of "{w\<^sub>\<pi> l rr + abstract_real_map
                      (missed_lookup missed') l | l rr. {l, rr} \<in> G}"] 
                  simp add: finite_G finite_double_image_of_pairs_in_set_of_sets)
            thus ?case 
              apply(subst new_min_is)
              unfolding ll(4) Min_set_is 
              apply(subst (asm) linorder_class.Min_insert)
              apply(rule rev_finite_subset[of "{w\<^sub>\<pi> l rr + missed_at state l | l rr. {l, rr} \<in> G}"])
              by(auto simp add: finite_G finite_double_image_of_pairs_in_set_of_sets there_is_l)
          next
            case 3
            then show ?case 
              by (auto intro!: exI[of _ l'] simp add: true)
          qed   
          thus ?thesis
            using True false rr_in_ngbhd_l'
            by(auto intro!: exI[of _ l'] 
                simp add: state'_def  after_ben_update(5)  edge_commute true F'_is(2))  
        next
          case False
          have "w\<^sub>\<pi> ll rr + abstract_real_map (missed_lookup missed') ll =
             Min { w\<^sub>\<pi> l rr + abstract_real_map (missed_lookup missed') l
                  | l. (l = l' \<or> l \<in> vset_to_set (evens F)) \<and> {l, rr} \<in> G}"
            unfolding Min_set_is
            apply(subst linorder_class.Min_insert)
            apply(rule rev_finite_subset[of "{w\<^sub>\<pi> l rr + missed_at state l | l rr. {l, rr} \<in> G}"])
            using False  r_not_even_or_odd ll(1,3)  l'_not_even
            by(auto simp add: finite_G finite_double_image_of_pairs_in_set_of_sets
                              there_is_l ll(4)[symmetric] missed'_is F_def ben_def)
          thus ?thesis 
            using False false  rr_in_ngbhd_l'
            by(auto intro!: exI[of _ ll] 
                simp add: state'_def after_ben_update(5) ll(1-3) ben_def F'_is(2) F_def)
        qed
      qed
    next
      case False
      note rr_in_G = two(1)
      moreover have "rr \<notin> aevens state" "rr \<notin> aodds state"  
        using two by (auto simp add: state'_def F'_is(2,3) F_def)
      moreover hence there_is_l:"\<exists>l. l \<in> aevens state \<and> {l, rr} \<in> G" 
        using two(4) False  rr_in_G
        by(auto simp add: ben_def state'_def F'_is(2) F_def)  
      ultimately obtain ll where ll: 
        "ben_lookup (best_even_neighbour state) rr = Some ll"
        "{rr, ll} \<in> G" "ll \<in> aevens state"
        "w\<^sub>\<pi> ll rr + missed_at state ll =
                             Min {w\<^sub>\<pi> l rr + missed_at state l | 
                            l . l \<in> aevens state \<and> {l, rr} \<in> G}"
        using invar_best_even_neighbour_mapD(2)[OF assms(7), of rr] by blast
      have same_ben:"ben_lookup ben' rr = ben_lookup ben rr"
        by (simp add: False G(6) after_ben_update(5) l'_in_L)
      have same_ben_value: "w\<^sub>\<pi> ll rr + abstract_real_map (missed_lookup missed') ll = 
                                   w\<^sub>\<pi> ll rr + missed_at state ll"
        using ll(3) r_unclassified l'_not_even 
        by(auto simp add: missed'_is F_def)
      have Min_set_is: 
        "{w\<^sub>\<pi> l rr + abstract_real_map (missed_lookup missed') l 
             | l. (l = l' \<or> l \<in> aevens state) \<and> {l, rr} \<in>G} = 
            {w\<^sub>\<pi> l rr + missed_at state l | l . l \<in> aevens state \<and> {l, rr} \<in> G}"
        using False r_unclassified  by(auto simp add: missed'_is)
      show ?thesis
        using ll
        by(auto intro: exI[of _ ll] 
             simp add: ben_def F_def F'_is same_ben_value same_ben  state'_def Min_set_is)
    qed
  qed

  have Some_l_is: "ben_lookup ben r = Some l" 
    using  ben_def edge_commute invar_best_even_neighbour_mapD[OF assms(7)] l_def
      r_l_props(1,2) r_unclassified by fastforce
  show "invar_out_of_heap (search_path_loop_cont_upd state)"
    unfolding upd_state_is_state'
  proof(rule invar_out_of_heapI, goal_cases)
    case (1 rr ll kr)
    note one = this[simplified state'_def, simplified]
    have new_potential_key_leq_missed_l':
      "w\<^sub>\<pi> ll rr + abstract_real_map (missed_lookup missed') ll
                 \<le> abstract_real_map (missed_lookup missed') l'"
      using after_ben_update(4)[of rr ll] one(1,2) by auto     
    from one have rr_prop:"rr = r \<or> (\<nexists>k. (rr, k) \<in> heap_abstract (heap state))"
      by(auto simp add: queue_props(2) after_ben_update(6) 
          in_image_with_fst_eq)
    obtain kr1 kr2 lkr where kr_split: "kr = (kr1, kr2)"
      "kr1 \<in> Vs G - aevens state' - aodds state'"
      "kr2 = w\<^sub>\<pi> lkr kr1 + missed_at state' lkr"
      "ben_lookup ben' kr1 = Some lkr"
      using invar_best_even_neighbour_heapD[OF invar_best_even_neighbour_heap_step]
        one(3)
      by(auto simp add: state'_def upd_state_is_state')
    have kr1_further_props:
      "{kr1, lkr} \<in> G" "lkr \<in> aevens state'"
      using invar_best_even_neighbour_mapD[OF invar_best_even_neighbour_map_step, of kr1]
        kr_split
      by(auto simp add: state'_def upd_state_is_state')
    have missed_at_lkr_new_is:"missed_at state' lkr = 
               (if lkr = l' then w\<^sub>\<pi> l r + missed_at state l else  missed_at state lkr)"
      using invar_basicD(9)[OF invar_basic_step]
        bipartite_edgeD(1)[OF r_l'_in_G G(1)]
        kr1_further_props(2) l'_in_L 
      by(auto simp add: state'_def missed'_is  upd_state_is_state' acc'_def missed_\<epsilon>_def)
    have missed_at_l'_is: "missed_at state' l' =  w\<^sub>\<pi> l r + missed_at state l"
      by(auto simp add: state'_def missed'_is acc'_def missed_\<epsilon>_def)
    note one' = 1(3)[simplified kr_split(1), simplified state'_def, simplified]
    note kr1_kr2_in = one'[simplified after_ben_update(6) queue_props(2)]
    have "abstract_real_map (missed_lookup missed') l' \<le> kr2"
    proof(rule UnE[OF kr1_kr2_in], goal_cases)
      case 1
      show ?case 
      proof(rule UnE[OF 1], goal_cases)
        case 1
        show ?case
          using missed_at_l'_is  kr1_further_props(1) w\<^sub>\<pi>_non_neg[of lkr kr1] 
            "1" k(2) k_is kr_split(3) 
          by (auto simp add: missed_at_lkr_new_is  kr_split(3) state'_def insert_commute)
      next
        case 2
        hence kr_more_props: "kr1 \<in> vset_to_set (right_neighbs l')"
          "kr1 \<in> fst ` heap_abstract (heap state)" "kr1 \<noteq> r"
          "kr2 = min (w\<^sub>\<pi> l' kr1 + abstract_real_map (missed_lookup missed') l')
                       (w\<^sub>\<pi> (the (ben_lookup ben kr1)) kr1 +
                        abstract_real_map (missed_lookup missed') (the (ben_lookup ben kr1)))" 
          using  basic_invars(3) heap(7) k(1) k_is
          by(auto simp add: missed_\<epsilon>_def acc'_def)
        show ?case
        proof(rule P_of_minE_strict2[of "\<lambda> x. kr2 = x", OF kr_more_props(4)], goal_cases)
          case 1
          then show ?case 
            using G(6) kr_more_props(1) l'_in_L w\<^sub>\<pi>_non_neg by force
        next
          case 2
          hence "(kr1, kr2) \<in> heap_abstract (heap state)"
            using kr_more_props(2,3) queue_props(2) update_best_even_neighbour_conditions(4)
            by fastforce
          then show ?case 
            using k(1) k(2)[of kr1 kr2]
            by(simp add: acc'_def missed_\<epsilon>_def  k_is missed'_is)
        qed
      qed
    next
      case 2
      hence kr_more_props: "kr1 \<in> vset_to_set (right_neighbs l')"
        "ben_lookup ben kr1 = None"
        "kr2 = w\<^sub>\<pi> l' kr1 + abstract_real_map (missed_lookup missed') l'" 
        using  basic_invars(3) heap(7) k(1) k_is
        by(auto simp add: missed_\<epsilon>_def acc'_def)
      then show ?case 
        using after_ben_update(5) kr1_further_props(1) kr_split(4) w\<^sub>\<pi>_non_neg w\<^sub>\<pi>_symmetric
        by force
    qed
    thus ?case
      using missed_at_l'_is new_potential_key_leq_missed_l'
      by(auto simp add: state'_def kr_split(1))
  qed
  have "2 + card (aevens state \<union> aodds state) =
          card ({r, l'} \<union> (vset_to_set (evens F) \<union> vset_to_set (odds F)))"
    using basic_invars(1) finite_forest(1,2)evens_and_odds(4)[OF F'_is(6)]
      l'_not_even_or_odd r_not_even_or_odd 
    by(subst (2) card_Un_disjoint)(auto simp add: F_def F'_is(2,3))
  thus "card (aevens (search_path_loop_cont_upd state) \<union> aodds (search_path_loop_cont_upd state)) =
    card (aevens state \<union> aodds state) + 2"
    by(auto simp add: upd_state_is_state' state'_def F'_is(2,3))
qed

subsection \<open>Termination\<close>

lemma search_path_loop_term_gen_induct:
  assumes  
    "remaining = card L + card R - card (aevens state \<union> aodds state)"
    "invar_basic state"
    "invar_feasible_potential state"
    "invar_forest_tight state"
    "invar_matching_tight state"
    "invar_best_even_neighbour_heap state"
    "invar_best_even_neighbour_map state"
    "invar_out_of_heap state"
  shows "search_path_loop_dom state"
  using assms
proof(induction remaining arbitrary: state rule: less_induct)
  case (less remaining)
  show ?case 
  proof(cases state rule: search_path_loop_cases)
    case 3
    have decrease: "(card (aevens state \<union> aodds state)) +2 \<le> card L + card R"
      unfolding invar_pres_one_step(8)[OF 3 less(3-9), symmetric]
      using  invar_basicD(9,10)[OF invar_pres_one_step(1)[OF 3 less(3-9)]] finite_L finite_R
      by (auto intro:  order.trans[OF card_Un_le] simp add: add_le_mono card_mono)
    show ?thesis 
      using decrease  
      by(intro search_path_loop_domintros(3)[OF 3])
        (auto intro: less(1)[of "card L + card R 
            - Suc (Suc (card (aevens state \<union> aodds state)))"] 
           simp add: invar_pres_one_step[OF 3 less(3-9)] less(2))
  qed (auto intro: search_path_loop_domintros(1,2))
qed

lemmas search_path_loop_term_gen = search_path_loop_term_gen_induct[OF refl]

subsection \<open>Unbounded Dual\<close>

lemma search_path_loop_fail_cond_dual_unbounded:
  assumes "search_path_loop_fail_cond state"
    "invar_basic state"
    "invar_feasible_potential state"
    "invar_best_even_neighbour_heap state"
    "invar_best_even_neighbour_map state"
  shows "\<exists> p. (\<forall> u v. {u, v} \<in> G \<longrightarrow> edge_costs u v \<ge> p u +  p v)
               \<and> sum p (L \<union> R) \<ge> bound"
proof-
  obtain queue heap_min where queue_heap_min_def:
    " (queue, heap_min) = heap_extract_min (heap state)"
    by(cases "heap_extract_min (heap state)") auto
  have empty_heap:  "heap_abstract (heap state) = {}" "heap_min = None"
    using queue_heap_min_def[symmetric] assms(1,2) invar_basicD(3)
    by(auto elim!: search_path_loop_fail_condE intro!: heap(6))
  have no_even_non_odd_edge: False
    if asms: "l \<in> aevens state" "{l, r} \<in> G" "r \<notin> aodds state" for l r
  proof-
    have l_in_L: "l \<in> L" 
      using assms(2) invar_basicD(9) that(1) by blast
    hence r_not_even: "r \<notin> aevens state" 
      using G(1)  bipartite_edgeD(1) invar_basicD[OF assms(2)] that(2) by fast
    have r_in_G: "r \<in> Vs G"
      by (auto intro: edges_are_Vs_2 that(2))
    obtain l' where "ben_lookup (best_even_neighbour state) r = Some l'"
      using invar_best_even_neighbour_mapD(2)[OF assms(5) r_in_G r_not_even asms(3)] asms(1,2) 
      by blast
    hence "(r, w\<^sub>\<pi> l' r + missed_at state l') \<in> heap_abstract (heap state)"
      using invar_best_even_neighbour_heapD[OF assms(4)]  r_not_even r_in_G asms(3) by blast
    thus False 
      using empty_heap(1) by blast
  qed
  define \<epsilon> where "\<epsilon> = \<bar> sum (\<pi>\<^sup>* state) (L \<union> R) \<bar> + \<bar>bound\<bar>"
  define p where "p = (\<lambda> x. if x \<in> aevens state then \<pi>\<^sup>* state x + \<epsilon>
                             else if x \<in> aodds state then \<pi>\<^sup>* state x - \<epsilon>
                             else \<pi>\<^sup>* state x)"
  have odds_in_G:"aodds state \<subseteq> Vs G" 
    using  bipartite_vertex(1)[OF _ G(1)] insert_absorb
      insert_subset invar_basicD(6,9,10,12)[OF assms(2)]
    by auto
  have evens_odds_disjoint: "aodds state \<inter> aevens state = {}" 
    using assms(2) evens_and_odds(4) invar_basic_def by blast
  have pos_eps: "\<epsilon> \<ge> 0"
    by(auto simp add: \<epsilon>_def)
  have p_feasible:"{u, v} \<in> G \<Longrightarrow> p u + p v \<le> \<w> u v" for u v
    using evens_odds_disjoint  invar_feasible_potentialD[OF assms(3), of u v] pos_eps
      no_even_non_odd_edge[of v u]
    by(auto simp add: p_def insert_commute dest:  no_even_non_odd_edge)
  moreover have "bound \<le> sum p (L \<union> R)"
  proof-
    have sum1:"sum p  (L \<union> R) = sum p (aevens state) + sum p (L \<union> R - aevens state)"
      using finite_forest(1)[OF invar_basicD(1)[OF assms(2)]]  invar_basicD(9)[OF assms(2)]
      by(subst comm_monoid_add_class.sum.union_disjoint[of 
            A "B - A" for A B, simplified, symmetric])
        (auto intro!: arg_cong[of  _ _ "sum p"] simp add: finite_L finite_R)
    have sum2: "sum p (L \<union> R - aevens state) = 
               sum p (aodds state) + sum p (L \<union> R - aevens state - aodds state)"
      using finite_forest(2)[OF invar_basicD(1)[OF assms(2)]]  invar_basicD(10)[OF assms(2)]
        evens_odds_disjoint
      by(subst comm_monoid_add_class.sum.union_disjoint[of 
            A "B - A" for A B, simplified, symmetric])
        (auto intro!: arg_cong[of  _ _ "sum p"] simp add: finite_L finite_R)
    have sum3: "sum p (aevens state) = \<epsilon> * card (aevens state) + sum (\<pi>\<^sup>* state) (aevens state)"
      by(auto simp add:  p_def sum_cong[of _ _ "\<lambda> x. \<pi>\<^sup>* state x + \<epsilon>"] comm_monoid_add_class.sum.distrib)
    have sum4: "sum p (aodds state) = - \<epsilon> * card (aodds state) + sum (\<pi>\<^sup>* state) (aodds state)"
      using evens_odds_disjoint
      by(subst  sum_cong[of _ _ "\<lambda> x. \<pi>\<^sup>* state x - \<epsilon>"])
        (auto simp add: p_def sum_subtractf)
    have sum5: "sum p (L \<union> R - aevens state - aodds state) = 
               sum (\<pi>\<^sup>* state) (L \<union> R - aevens state - aodds state)"
      by(subst p_def sum_cong[of _ _ "\<pi>\<^sup>* state"]) simp+
    have card_diff: " card (aevens state) >  card (aodds state)"
      using invar_basicD(1)[OF assms(2)] higher_forest_properties(1) by blast
    have sum6:"sum (\<pi>\<^sup>* state) (L \<union> R) = sum (\<pi>\<^sup>* state) (aevens state) + sum (\<pi>\<^sup>* state) (L \<union> R - aevens state)"
      using finite_forest(1)[OF invar_basicD(1)[OF assms(2)]]  invar_basicD(9)[OF assms(2)]
      by(subst comm_monoid_add_class.sum.union_disjoint[of 
            A "B - A" for A B, simplified, symmetric])
        (auto intro!: arg_cong[of  _ _ "sum (\<pi>\<^sup>* state)"] simp add: finite_L finite_R)
    have sum7: "sum (\<pi>\<^sup>* state) (L \<union> R - aevens state) = 
               sum (\<pi>\<^sup>* state) (aodds state) + sum (\<pi>\<^sup>* state) (L \<union> R - aevens state - aodds state)"
      using finite_forest(2)[OF invar_basicD(1)[OF assms(2)]]  invar_basicD(10)[OF assms(2)]
        evens_odds_disjoint
      by(subst comm_monoid_add_class.sum.union_disjoint[of 
            A "B - A" for A B, simplified, symmetric])
        (auto intro!: arg_cong[of  _ _ "sum (\<pi>\<^sup>* state)"] simp add: finite_L finite_R)     
    have "\<epsilon> \<noteq> 0 \<Longrightarrow> 
             \<epsilon> * (1 + real (card (aodds state))) \<le> \<epsilon> * real (card (aevens state))"
      using card_diff pos_eps
      by(auto simp add: linordered_ring_strict_class.mult_le_cancel_left_pos)
    hence sum_p_bigger_than_sum_pi_state:
      "sum p (L \<union> R)\<ge> \<epsilon> + sum (\<pi>\<^sup>* state) (L \<union> R)"
      by(cases "\<epsilon> = 0")
        (auto simp add: sum1 sum2 sum3 sum4 sum5 sum6 sum7 algebra_simps)
    thus ?thesis
      by(auto simp add: \<epsilon>_def)
  qed
  ultimately show ?thesis 
    by auto
qed

lemma augpath_None_gen_unbounded_dual:
  assumes "invar_basic state"
    "invar_feasible_potential state"
    "invar_forest_tight state"
    "invar_matching_tight state"
    "invar_best_even_neighbour_heap state"
    "invar_best_even_neighbour_map state"
    "invar_out_of_heap state"
    "augpath (search_path_loop state) = None"
  shows "\<exists> p.  (\<forall> u v. {u, v} \<in> G \<longrightarrow> edge_costs u v \<ge> p u +  p v)
             \<and> sum p (L \<union> R) \<ge> bound"
  using assms
proof(induction state rule: search_path_loop_induct, goal_cases)
  case 1
  then show ?case
    by (simp add: assms(1,2,3,4,5,6,7) search_path_loop_term_gen)
next
  case (2 state)
  note IH = this
  show ?case 
  proof(cases state rule: search_path_loop_cases)
    case 1
    then show ?thesis 
      using search_path_loop_fail_cond_dual_unbounded IH(3-9) 
      by auto
  next
    case 2
   show ?thesis 
     using IH(10) 2
     by(auto simp add: search_path_loop_simps(2)[OF 2] search_path_loop_succ_upd_def Let_def
                elim!: search_path_loop_succ_condE 
                dest!: sym[of _ "heap_extract_min (heap state)"]) 
  next
    case 3
    show ?thesis 
      using IH(10) 
      by(auto intro!: IH(2) 3  invar_pres_one_step IH(1,3-9)
           simp add: search_path_loop_simps(3)[OF IH(1) 3])
  qed
qed

subsection \<open>Tight Augmenting Path and Potential\<close>

lemma search_path_loop_succ_cond_valid_result:
  assumes "search_path_loop_succ_cond state"
    "invar_basic state"
    "invar_feasible_potential state"
    "invar_forest_tight state"
    "invar_matching_tight state"
    "invar_best_even_neighbour_heap state"
    "invar_best_even_neighbour_map state"
    "state' = (search_path_loop_succ_upd state)"
  shows "invar_feasible_potential state'"
        "invar_matching_tight state'"
      "augpath state' \<noteq> None"
      "\<forall> e \<in> set (edges_of_path (the (augpath state'))).
          \<exists> u v. e = {u, v} \<and> \<w> u v = \<pi>\<^sup>* state' u + \<pi>\<^sup>* state' v"
      "graph_augmenting_path G \<M> (the (augpath state'))"
      "forest_invar \<M> (forest state')"
proof-
  define F where "F = forest state"
  define ben where "ben = best_even_neighbour state"
  define missed_\<epsilon> where  "missed_\<epsilon> = missed_at state"
  obtain queue heap_min where queue_heap_min_def:
    " (queue, heap_min) = heap_extract_min (heap state)"
    by(cases "heap_extract_min (heap state)") auto
  obtain r where r_def: "heap_min = Some r"
    using queue_heap_min_def assms(1)
    by(auto elim!: search_path_loop_succ_condE 
        dest: sym[of _ "heap_extract_min (heap state)"])
  define l where "l = the (ben_lookup ben r)"
  define acc' where "acc' = w\<^sub>\<pi> l r + missed_\<epsilon> l"
  define p where "p = r # get_path F l"
  have state'_def: "state' = state \<lparr> acc:= acc', augpath:= Some p \<rparr>"
    by(simp add: assms(8) search_path_loop_succ_upd_def queue_heap_min_def[symmetric] 
        Let_def acc'_def r_def F_def missed_\<epsilon>_def l_def ben_def p_def)

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
  have r_not_even_or_odd:
    "r \<in> vset_to_set (evens F) \<union>  vset_to_set (odds F) \<Longrightarrow> False" 
    using F_def r_unclassified by blast
  have l_r_not_in_M:"{l, r} \<in> \<M> \<Longrightarrow> False" 
    using r_l_props(2) assms(2) higher_forest_properties(2,3)[of \<M> F l r] 
      r_not_even_or_odd evens_and_odds(3)[of \<M> F]
    by(auto elim!: invar_basicE simp add: F_def)
  have l_in_L:"l \<in> L"
    using  assms(2) r_l_props(2)
    by(auto elim!: invar_basicE)
  hence r_in_R: "r \<in> R"
    using G(1) bipartite_edgeD(3) l_in_L r_l_props(1) by fastforce
  have queue'_is: "heap_abstract (fst (heap_extract_min (heap state))) =
         heap_abstract (heap state) - {(r, w\<^sub>\<pi> l r + missed_at state l)}"
    using assms(2) k(1) k_is
    by(intro heap(8))
      (auto elim!: invar_basicE 
        simp add: r_def[symmetric] pair_eq_fst_snd_eq[OF queue_heap_min_def])
  note basic_invars = invar_basicD[OF assms(2)]
  have r_neither_even_nor_odd: "r \<in> aevens state = False" "r \<in> aodds state = False" 
    using r_unclassified by blast+
  have "buddy r = None"
    using assms(1) sym[OF queue_heap_min_def]
    by(auto elim!:  search_path_loop_succ_condE
        simp add: r_def)
  hence r_unmatched:"r \<notin> Vs \<M>"
    using M_verts_by_buddy(1)[of r] by blast
  have feasibility_hard_case: 
    "w\<^sub>\<pi> l r + missed_at state l \<le>  w\<^sub>\<pi> v u + missed_at state v"
    if asms:"u \<notin> aodds state" "v \<notin> aodds state"
      "u \<notin> aevens state" "v \<in> aevens state" "{u, v} \<in> G" for u v
  proof-
    have u_in_G_unclassified: "u \<in> Vs G - aevens state - aodds state"
      using edges_are_Vs that(1,3,5) by auto
    then obtain v' where u_v'_props: 
      "ben_lookup (best_even_neighbour state) u = Some v'"
      "{u, v'} \<in> G" "v' \<in> aevens state"
      "w\<^sub>\<pi> v' u + missed_at state v' =
         Min {w\<^sub>\<pi> l u + missed_at state l| l. l \<in> aevens state \<and> {l, u} \<in> G}"
      using invar_best_even_neighbour_mapD(2)[OF assms(7), of u] asms(4,5)
      by(auto simp add: insert_commute[of u v])
    have u'v'_better: "w\<^sub>\<pi> v' u + missed_at state v' \<le> w\<^sub>\<pi> v u + missed_at state v"
      using asms(4,5)
      by(auto intro!: linorder_class.Min.coboundedI finite_subset[of 
            "{ _  l u | l. l \<in> _ \<and> {l, u} \<in> G}"  "{ _  l u | l u. {l, u} \<in> G}"]
          exI[of "\<lambda> l. _" v]
          simp add: u_v'_props(4) finite_G finite_double_image_of_pairs_in_set_of_sets
                    insert_commute)
    have "(u, w\<^sub>\<pi> v' u + missed_at state v') \<in> heap_abstract (heap state)" 
      using invar_best_even_neighbour_heapD[OF assms(6)] u_in_G_unclassified
        u_v'_props(1) 
      by auto
    hence "w\<^sub>\<pi> v' u + missed_at state v' \<ge> w\<^sub>\<pi> l r + missed_at state l"
      using k(2) k_is by auto
    thus ?thesis
      using u'v'_better by simp
  qed

  show "invar_feasible_potential state'"
    unfolding state'_def
  proof(rule invar_feasible_potentialI, goal_cases)
    case (1 u v)
    note evens_odds = evens_and_odds(1,2,4)[OF  basic_invars(1)]
    note fsbl_uv = invar_feasible_potentialD[OF assms(3) 1]
    note fsbl_lr = invar_feasible_potentialD[OF assms(3)  r_l_props(1)]
    note hard_cases = feasibility_hard_case[OF _ _ _ _ 1]
      feasibility_hard_case[OF _ _ _ _ edge_commute[OF 1]]
    show ?case 
      using evens_odds(3) basic_invars(10) bipartite_edgeD(4)[OF 1 G(1)]
        fsbl_uv G(7)[OF r_l_props(1)]
        fsbl_lr  r_l_props(2) r_not_even_or_odd bipartite_edgeD(3)[OF 1 G(1)] 
        basic_invars(9) G(7)[OF 1] hard_cases
      by(auto simp add: working_potential_def acc'_def missed_\<epsilon>_def
          vset(5)[OF evens_odds(1)] vset(5)[OF evens_odds(2)] F_def 
          w\<^sub>\<pi>_def r_neither_even_nor_odd) 
  qed

  show "augpath state' \<noteq> None"
    by(auto simp add: state'_def)
  have the_path_is:"the (augpath state') = p" 
    by(auto simp add: state'_def)
  have p_pref_props: "rev_alt_path \<M> (get_path F l)"
    "odd (length (get_path F l))"
    "last (get_path F l)
                    \<in> vset_to_set (roots F)"
    "walk_betw (abstract_forest F) l (get_path F l) (last (get_path F l)) \<or> get_path F l = [l]"
    "distinct (get_path F l)"
    using get_path[OF basic_invars(1) r_l_props(2)]
    by(auto simp add: p_def F_def)
  have get_path_split_off_first:"get_path F l = hd (get_path F l)# tl (get_path F l)"
    and get_path_non_empty: "get_path F l \<noteq> []"
    and get_path_length: "length (get_path F l) \<ge> 1"
    using p_pref_props(2) by(all \<open>cases "get_path F l"\<close>) auto 
  have hd_get_path:"(hd (get_path F l)) = l" 
    using p_pref_props(4)
    by (auto intro: walk_between_nonempty_pathD(3))
  have edges_of_p_are:"edges_of_path p = {r, l}#edges_of_path (get_path F l)"
    using get_path_split_off_first  hd_get_path p_def 
    by (metis edges_of_path.simps(3))
  show "\<forall>e\<in>set (edges_of_path (the (augpath state'))).
       \<exists>u v. e = {u, v} \<and> \<w> u v = \<pi>\<^sup>* state' u + \<pi>\<^sup>* state' v "
  proof(rule, goal_cases)
    case (1 e)
    hence one: "e \<in> set (edges_of_path (get_path F l)) \<or> e = {l, r}" 
      using edges_of_p_are by(auto simp add: state'_def p_def)
    show ?case 
    proof(cases rule: disjE[OF one], goal_cases)
      case 1
      hence e_in_F:"e \<in> abstract_forest F" 
        using p_pref_props(4) path_ball_edges by(auto simp add: walk_betw_def)
      moreover then obtain u v where e_is: "e = {u, v}"
        using "1" in_edges_of_path_split by blast
      ultimately have uv_in_G:"{u, v} \<in> G" 
        using  F_def invar_basicD[OF assms(2)] by blast
      note evens_odds = evens_and_odds(1,2,4)[OF  basic_invars(1)]
      have "\<pi>\<^sup>* state' u + \<pi>\<^sup>* state' v = \<w> u v"
        using invar_forest_tightD[OF assms(4), of u v] e_in_F evens_odds(3) 
          higher_forest_properties(3)[OF basic_invars(1), of v u]
          higher_forest_properties(3)[OF basic_invars(1), of u v]
        by(auto simp add: working_potential_def 
            vset(5)[OF evens_odds(1)] vset(5)[OF evens_odds(2)] F_def 
            insert_commute e_is state'_def) 
      thus ?case
        using e_is by fastforce
    next
      case 2
      note evens_odds = evens_and_odds(1,2,4)[OF  basic_invars(1)]
      have "\<w> l r = \<pi>\<^sup>* state' l + \<pi>\<^sup>* state' r"
        using evens_odds(1,2,3) r_neither_even_nor_odd(1) r_l_props(2)
        by(auto simp add: state'_def acc'_def working_potential_def missed_\<epsilon>_def vset(5)
            r_neither_even_nor_odd(2)  w\<^sub>\<pi>_def)
      thus ?case 
        using 2 by blast
    qed
  qed
  have F_invar:"forest_invar \<M> (forest state)" "vset_invar (evens (forest state))"
    "vset_invar (odds (forest state))"
    using assms(2) by(auto elim!: invar_basicE intro: evens_and_odds)
  show "invar_matching_tight state'"
    unfolding state'_def
  proof(rule invar_matching_tightI, goal_cases)
    case (1 u v)
    note uv_in_M = this
    show ?case
    proof(cases "{u, v} \<inter> Vs (abstract_forest F) = {}")
      case True
      hence no_inter:"{u, v} \<inter> (aevens state \<union> aodds state) = {}" 
        using edges_are_Vs_2 evens_and_odds(3)[OF F_invar(1)]
          higher_forest_properties(2)[OF F_invar(1), of u v] uv_in_M 
        by (auto simp add: F_def)
      have "\<pi>\<^sup>* state' u = \<pi>\<^sup>* state u" "\<pi>\<^sup>* state' v = \<pi>\<^sup>* state v"
        using F_def r_unclassified  no_inter
        by(auto simp add: state'_def  working_potential_def 
            vset(5)[OF F_invar(2)] vset(5)[OF F_invar(3)] F_def )
      thus ?thesis 
        using  invar_matching_tightD[OF assms(5) uv_in_M ] no_inter
        by(auto simp add: working_potential_def acc'_def 
            vset(5)[OF F_invar(2)]  vset(5)[OF F_invar(3)])
    next
      case False
      then obtain u' v' where u'v': "{u, v} = {u', v'}" "u' \<in> aevens state" "v' \<in> aodds state"
        apply(cases rule: disjE[OF higher_forest_properties(2)[OF
                basic_invars(1) uv_in_M]])
        using evens_and_odds(3)[OF basic_invars(1)] uv_in_M
          higher_forest_properties(3)[OF basic_invars(1)]
        by(unfold F_def) blast+
      have v'_not_even: "v' \<notin> aevens state" 
        using basic_invars(1) evens_and_odds(4) u'v'(3) by fastforce
      show ?thesis 
        unfolding state'_def  working_potential_def
        using  u'v'(1,2,3)  v'_not_even r_not_even_or_odd  evens_and_odds(4)[OF basic_invars(1)]
          invar_matching_tightD[OF assms(5)  uv_in_M]
        by auto (force simp add:  working_potential_def vset(5)[OF F_invar(2)] 
            vset(5)[OF F_invar(3)] F_def   missed_\<epsilon>_def)+
    qed
  qed
    have path_in_F:"set (get_path F l) \<subseteq> Vs (abstract_forest F) \<union> (vset_to_set (roots F))"
      using  p_pref_props(3,4) by (auto dest: walk_in_Vs) 
  have "path G p"
    unfolding p_def
  proof(cases rule: disjE[OF p_pref_props(4)], goal_cases)
    case 1
    have path_in_F:"set (get_path F l) \<subseteq> Vs (abstract_forest F)"
      using 1  by (auto dest: walk_in_Vs)
    show ?case 
    apply(rule  path.path2[of r l G "tl (get_path F l)", 
          simplified get_path_split_off_first[simplified  hd_get_path, symmetric]])
    using r_l_props(1) 1 invar_basicD(5)[OF assms(2)]
    by(auto intro!:  path_subset[of "abstract_forest F" _ G]
        simp add: p_def walk_betw_def F_def)
  next
    case 2
    then show ?case 
      by (auto intro: edges_are_Vs_2 r_l_props(1))
  qed
  moreover have  "distinct p"
    using  path_in_F basic_invars(1) evens_and_odds(3) r_not_even_or_odd p_pref_props(5)
    by(auto simp add: p_def F_def)
  moreover have "matching_augmenting_path \<M> p"
  proof(rule matching_augmenting_pathI, goal_cases)
    case 1
    then show ?case 
      using get_path_length
      by(auto simp add: p_def)
  next
    case 2
    then show ?case 
      by(auto simp add: edges_of_p_are alt_list_step insert_commute p_pref_props(1)
          intro: l_r_not_in_M)
  next
    case 3
    then show ?case 
      using r_unmatched
      by(auto simp add: p_def)
  next
    case 4
    show ?case
      using get_path_non_empty p_pref_props(3) roots(3)[OF basic_invars(1)]
      by(auto simp add: p_def F_def)
  qed
  ultimately show "graph_augmenting_path G \<M> (the (augpath state'))"
    by(auto simp add: state'_def)
  show "forest_invar \<M> (forest state')"
    using assms(2)
    by(auto simp add: state'_def dest: invar_basicD)
qed

lemma augpath_Some_valid_result:
  assumes "invar_basic state"
    "invar_feasible_potential state"
    "invar_forest_tight state"
    "invar_matching_tight state"
    "invar_best_even_neighbour_heap state"
    "invar_best_even_neighbour_map state"
    "invar_out_of_heap state"
    "augpath state' \<noteq> None"
    "state' = search_path_loop state"
  shows "invar_feasible_potential state'" (is ?th1)
    "invar_matching_tight state'" (is ?th2)
    "\<forall> e \<in> set (edges_of_path (the (augpath state'))).
          \<exists> u v. e = {u, v} \<and> \<w> u v = \<pi>\<^sup>* state' u + \<pi>\<^sup>* state' v" (is ?th4)
    "graph_augmenting_path G \<M> (the (augpath state'))" (is ?th5)
     "forest_invar \<M> (forest state')" (is ?th6)
proof-
  have  "?th1 \<and> ?th2 \<and> ?th4 \<and> ?th5 \<and> ?th6"
    using assms(1-8)
    unfolding assms(9) 
  proof(induction state rule: search_path_loop_induct, goal_cases)
    case 1
    then show ?case
      by (simp add: assms(1,2,3,4,5,6,7) search_path_loop_term_gen)
  next
    case (2 state)
    note IH = this
    show ?case 
    proof(cases state rule: search_path_loop_cases)
      case 1
      then show ?thesis 
        using IH(10) 2
        by(auto simp add: search_path_loop_simps(1)[OF 1] search_path_loop_fail_upd_def Let_def
            elim!: search_path_loop_fail_condE 
            dest!: sym[of _ "heap_extract_min (heap state)"]) 
    next
      case 2
      show ?thesis
        using search_path_loop_succ_cond_valid_result[OF 2 IH(3-8) refl]
        by(auto simp add: search_path_loop_simps(2)[OF 2])
    next
      case 3
      show ?thesis 
        using IH(10) 
        by(unfold search_path_loop_simps(3)[OF IH(1) 3], intro IH(2))
          (auto intro!: 3 invar_pres_one_step IH(1,3-9)
            simp add: search_path_loop_simps(3)[OF IH(1) 3])
    qed
  qed
  thus ?th1 ?th2 ?th4 ?th5 ?th6
    by auto
qed

subsection \<open>Properties of Initial State\<close>

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
"invar_out_of_heap initial_state"
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
       by(simp add: empty_forest(2) initial_state_def vset(2))
   next
     case 11
     show ?case
     proof(rule, goal_cases)
       case (1 l)
       have "\<exists>la r. l = la \<and> ben_lookup (best_even_neighbour initial_state) r = Some la" 
         using 1[simplified mem_Collect_eq] 
         by (simp add: initial_state_def)
       then obtain r where
                "ben_lookup (best_even_neighbour initial_state) r = Some l"
         by auto
       then show ?case 
         using props_of_init_heap_and_ben(5,6)[OF surjective_pairing[symmetric], of r]
               unmatched_lefts(1) forest_roots(2) empty_forest(1)
         by(auto simp add: initial_state_def)
     qed
   next 
     case 12
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
 next
   case 7
   show ?case
     using  props_of_init_heap_and_ben(5)[OF surjective_pairing[symmetric]]
     by(fastforce intro!: invar_out_of_heapI
                simp add: initial_state_def props_of_init_heap_and_ben(7)[OF surjective_pairing[symmetric]])
 qed

lemma search_path_loop_of_init_dom:  "search_path_loop_dom initial_state" 
  by(auto intro: search_path_loop_term_gen simp add: invars_init)

lemma search_path_loop_of_init_same:
  "search_path_loop_impl initial_state = search_path_loop initial_state"
  using search_path_loop_impl_same search_path_loop_of_init_dom by blast
end

subsection \<open>Correctness of Path Search\<close>
 
lemma Lefts_Matched_all_lefts_matched:
  assumes "search_path = Lefts_Matched"
  shows   "L \<subseteq> Vs \<M>"
  using assms  unmatched_lefts(1)
  by(auto simp add: search_path_def
                    if_split[of "\<lambda> x. x = Lefts_Matched" "unmatched_lefts = []"] 
                    option.split[of  "\<lambda> x. x = Lefts_Matched"] Let_def)

lemma Dual_Unbounded_dual_unbounded:
  assumes "search_path = Dual_Unbounded"
  shows   "\<exists> p.  (\<forall> u v. {u, v} \<in> G \<longrightarrow> edge_costs u v \<ge> p u +  p v)
             \<and> sum p (L \<union> R) \<ge> bound"
  apply(rule augpath_None_gen_unbounded_dual[of initial_state])
  using assms unmatched_lefts(1)[symmetric]
  by(auto simp add: search_path_def  search_path_loop_of_init_same
                    if_split[of "\<lambda> x. x = Dual_Unbounded" "unmatched_lefts = []"] 
                    option.split[of  "\<lambda> x. x = Dual_Unbounded"] Let_def 
             intro: invars_init)

lemma new_potential_correct:
  assumes "forest_invar \<M> (forest state)"
  shows "potential_invar (new_potential state)"
        "abstract_real_map (potential_lookup (new_potential state)) = 
         working_potential state"
        "dom (potential_lookup (new_potential state)) = 
         dom (potential_lookup initial_pot) \<union>
         (vset_to_set (evens (forest state))) \<union>
         (vset_to_set (odds (forest state)))"
proof-
  define evs where "evs = rev (to_list (evens (forest state)))"
  have evs_props: "rev (to_list (evens (forest state))) = evs" "distinct evs"
    using assms evens_and_odds(1) vset(6) by (auto simp add: evs_def)
  define ods where "ods = rev (to_list (odds (forest state)))"
  have ods_props: "rev (to_list (odds (forest state))) = ods" "distinct ods"
    using assms evens_and_odds(2) vset(6) by (auto simp add: ods_def)
  define fo where "fo = (\<lambda>x y. potential_upd y x (\<pi> x - acc state + missed_at state x))"
  define fe where "fe = (\<lambda>x y. potential_upd y x (\<pi> x + acc state - missed_at state x))"
  have fe_it_invar_pres: 
       "potential_invar p \<Longrightarrow> potential_invar (foldr fe evs p)" for p evs
  proof(induction evs)
    case (Cons a evs)
    show ?case 
      by(subst foldr_Cons, subst o_apply, subst fe_def)
        (auto intro!: potential(2) Cons)
  qed auto
  have fo_it_invar_pres: 
       "potential_invar p \<Longrightarrow> potential_invar (foldr fo ods p)" for p ods
  proof(induction ods)
    case (Cons a ods)
    show ?case 
      by(subst foldr_Cons, subst o_apply, subst fo_def)
        (auto intro!: potential(2) Cons)
  qed auto
  show  "potential_invar (new_potential state)"
    by(auto intro!: fo_it_invar_pres fe_it_invar_pres potential(1)
          simp add: new_potential_def foldl_conv_foldr evs_props(1) 
                    ods_props(1) fo_def[symmetric] fe_def[symmetric])
 have fe_it_is: 
       "\<lbrakk>potential_invar p; distinct evs\<rbrakk>
          \<Longrightarrow> abstract_real_map (potential_lookup (foldr fe evs p)) = 
               (\<lambda> x. if x \<in> set evs then \<pi> x + acc state - missed_at state x
                      else abstract_real_map (potential_lookup p) x)" for p evs
 proof(induction evs)
   case (Cons a evs)
   hence distinct_evs: "distinct evs" by auto
   show ?case 
     apply(subst foldr_Cons, subst o_apply)
     apply(subst fe_def)
     by(auto simp add: potential(3)[OF fe_it_invar_pres[OF Cons(2)]]
                        abstract_real_map_fun_upd Cons(1)[OF Cons(2) distinct_evs]) 
 qed auto
 have fo_it_is: 
       "\<lbrakk>potential_invar p; distinct ods\<rbrakk>
          \<Longrightarrow> abstract_real_map (potential_lookup (foldr fo ods p)) = 
               (\<lambda> x. if x \<in> set ods then \<pi> x - acc state + missed_at state x
                      else abstract_real_map (potential_lookup p) x)" for p ods
 proof(induction ods)
   case (Cons a ods)
   hence distinct_ods: "distinct ods" by auto
   show ?case 
     apply(subst foldr_Cons, subst o_apply)
     apply(subst fo_def)
     by(auto simp add: potential(3)[OF fo_it_invar_pres[OF Cons(2)]]
                        abstract_real_map_fun_upd Cons(1)[OF Cons(2) distinct_ods]) 
 qed auto
  note fo_it_is_applied =  fo_it_is[OF fe_it_invar_pres[OF potential(1)] ods_props(2)]
  note fe_it_is_applied =  fe_it_is[OF potential(1) evs_props(2)]
  have "(\<lambda>x. if x \<in> set ods then \<pi> x - acc state + missed_at state x
          else if x \<in> set evs then \<pi> x + acc state - missed_at state x else \<pi> x) =
    \<pi>\<^sup>* state"
    using evens_and_odds(1,2,4)[OF assms]
    by(auto intro!: ext 
          simp add: disjoint_iff working_potential_def evs_def ods_def vset(7)[OF _ refl] vset(5))
  thus "abstract_real_map (potential_lookup (new_potential state)) = \<pi>\<^sup>* state"
    by((subst new_potential_def foldl_conv_foldr evs_props(1) 
                    ods_props(1) fo_def[symmetric] fe_def[symmetric]
                     fo_it_is_applied fe_it_is_applied)+)
      auto
  have fe_it_dom: 
       "potential_invar p \<Longrightarrow> dom (potential_lookup (foldr fe evs p)) =
          dom (potential_lookup p) \<union> set evs" for p evs
  proof(induction evs)
    case (Cons a evs)
    show ?case 
      apply(subst foldr_Cons)
      apply(subst o_apply)
      apply(subst fe_def)
      by(simp add: potential(3)[OF fe_it_invar_pres[OF Cons(2)]] 
                   Cons(1)[OF Cons(2)]) 
  qed auto
  have fo_it_dom: 
       "potential_invar p \<Longrightarrow> dom (potential_lookup (foldr fo ods p)) =
          dom (potential_lookup p) \<union> set ods" for p ods
  proof(induction ods)
    case (Cons a ods)
    show ?case 
      apply(subst foldr_Cons)
      apply(subst o_apply)
      apply(subst fo_def)
      by(simp add: potential(3)[OF fo_it_invar_pres[OF Cons(2)]] 
                   Cons(1)[OF Cons(2)]) 
  qed auto
  note fo_it_dom_applied =  fo_it_dom[OF fe_it_invar_pres[OF potential(1)]]
  note fe_it_dom_applied =  fe_it_dom[OF potential(1)]
  have "dom (potential_lookup initial_pot) \<union> set evs \<union> set ods =
    dom (potential_lookup initial_pot) \<union> aevens state \<union> aodds state"
    using assms evens_and_odds(1,2) evs_props(1) ods_def vset(7) by fastforce
  thus "dom (potential_lookup (new_potential state)) =
    dom (potential_lookup initial_pot) \<union> aevens state \<union> aodds state"
    by(simp add: new_potential_def foldl_conv_foldr evs_props(1) 
                    ods_props(1) fo_def[symmetric] fe_def[symmetric]
                     fo_it_dom_applied fe_it_dom_applied)
qed

lemma Next_Iteration_tight_path_and_new_feasible_potential:
  assumes "search_path = Next_Iteration p \<pi>'"
  shows "\<And> u v. {u, v} \<in> G \<Longrightarrow>
               \<w> u v \<ge> abstract_real_map (potential_lookup \<pi>') u +
                        abstract_real_map (potential_lookup \<pi>') v" 
    "\<And> u v. {u, v} \<in> \<M> \<Longrightarrow>
               \<w> u v = abstract_real_map (potential_lookup \<pi>') u +
                       abstract_real_map (potential_lookup \<pi>') v" 
    "\<And> u v. {u, v} \<in> set (edges_of_path p) \<Longrightarrow>
               \<w> u v = abstract_real_map (potential_lookup \<pi>') u +
                        abstract_real_map (potential_lookup \<pi>') v" 
    "graph_augmenting_path G \<M> p"
proof-
  have from_assms: "L - Vs \<M> \<noteq> {}" 
    "augpath (search_path_loop initial_state) = Some p"
    "\<pi>' = new_potential (search_path_loop initial_state)"
    "augpath (search_path_loop initial_state) \<noteq> None"
    using assms unmatched_lefts(1)[symmetric]
    by(auto simp add: search_path_def  search_path_loop_of_init_same
        if_split[of "\<lambda> x. x = Next_Iteration _ _" "unmatched_lefts = []"] 
        option.split[of  "\<lambda> x. x = Next_Iteration _ _"] Let_def 
        intro: invars_init)
  note result_props = augpath_Some_valid_result[OF invars_init[OF from_assms(1)]
      from_assms(4) refl]
  note new_potential_props = new_potential_correct[OF result_props(5)]
  show "abstract_real_map (potential_lookup \<pi>') u +
           abstract_real_map (potential_lookup \<pi>') v
           \<le> \<w> u v"
    if asm: "{u, v} \<in> G" for u v
    using  invar_feasible_potentialD result_props(1) asm
    by (auto simp add: from_assms(3) new_potential_props(2))
  show "\<w> u v =  abstract_real_map (potential_lookup \<pi>') u +
                        abstract_real_map (potential_lookup \<pi>') v"
    if asm: "{u, v} \<in> \<M>"for u v
    using  invar_matching_tightD result_props(2) asm
    by (auto simp add: from_assms(3) new_potential_props(2))
  show "graph_augmenting_path G \<M> p"
    using result_props(4)
    by (auto simp add: from_assms(2,3) new_potential_props(2) )
  hence "{u, v} \<in> set (edges_of_path p) \<Longrightarrow> {u, v} \<in> G" for u v 
    using path_ball_edges by auto
  thus "\<w> u v =  abstract_real_map (potential_lookup \<pi>') u +
                        abstract_real_map (potential_lookup \<pi>') v"
    if asm: "{u, v} \<in> set (edges_of_path p)" for u v
    using  bspec[OF result_props(3), of "{u, v}"] asm G(7)[of u v]
    by (auto simp add: from_assms(2,3) new_potential_props(2) doubleton_eq_iff)
qed
(*TODO say dual unbounded*)
lemmas search_path_correct = 
 Lefts_Matched_all_lefts_matched
 Dual_Unbounded_dual_unbounded
 Next_Iteration_tight_path_and_new_feasible_potential

end
end