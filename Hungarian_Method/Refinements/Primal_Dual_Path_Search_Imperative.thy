theory Primal_Dual_Path_Search_Imperative
  imports Hungarian_Method.Primal_Dual_Path_Search 
          Data_Structures.Imp_Map_Set_Addons 
          Data_Structures.Fixed_Univ_Key_Value_Queue_Specs_Imp
          Directed_Set_Graphs.Weighted_Neighbourhoods_Imperative_Spec 
          Basic_Matching.Alternating_Forest_Imperative_Spec
          Data_Structures.Real_Embedding

begin

section \<open>Imperative Refinement of the Path Search\<close>

text \<open>The path search of @{locale primal_dual_path_search} is refined to Imperative HOL. The
      refinement follows the discipline of the Dijkstra refinement: a code locale fixes the
      imperative operations (only their types) and defines the imperative programs; a proof locale
      combines the functional locale with the imperative ADT locales, which supply the Hoare
      triples.

      \<^emph>\<open>The programs do not allocate.\<close> All data structures of the search -- the best even
      neighbours, the missed values, the forest, the queue and the collection of neighbourhoods --
      are passed in as handles, emptied in place at the beginning of each search, and reused. The
      path is written into an array @{term Ra} that belongs to the caller.

      Values (weights, potentials, keys) are executable values of type @{typ 'n}, read into the
      reals by an embedding. Weights are only read at the cursor of the collection of
      neighbourhoods. All other quantities that the functional algorithm computes from weights
      are keys that are already in the queue: the key of a right vertex is the reduced weight of
      the edge to its best even neighbour plus the missed value there, and the extracted key is the
      new accumulated value. The programs read these keys from the queue instead of recomputing
      them.\<close>


definition "val_of x = (case x of None \<Rightarrow> 0 | Some c \<Rightarrow> c)"

subsection \<open>The Programs\<close>

locale primal_dual_path_search_imp_code =
  fixes ben_lookup_imp :: "'v::heap \<Rightarrow> 'bi \<Rightarrow> 'v option Heap"
    and ben_update_imp :: "'v \<Rightarrow> 'v \<Rightarrow> 'bi \<Rightarrow> 'bi Heap"
    and ben_clear_imp :: "'bi \<Rightarrow> 'bi Heap"
    and missed_lookup_imp :: "'v \<Rightarrow> 'mi \<Rightarrow> 'n::linordered_idom option Heap"
    and missed_update_imp :: "'v \<Rightarrow> 'n \<Rightarrow> 'mi \<Rightarrow> 'mi Heap"
    and missed_clear_imp :: "'mi \<Rightarrow> 'mi Heap"
    and pot_lookup_imp :: "'v \<Rightarrow> 'pi \<Rightarrow> 'n option Heap"
    and pot_update_imp :: "'v \<Rightarrow> 'n \<Rightarrow> 'pi \<Rightarrow> 'pi Heap"
    and buddy_imp :: "'bdi \<Rightarrow> 'v \<Rightarrow> 'v option Heap"
    and left_it_init :: "'li \<Rightarrow> 'lit Heap"
    and left_it_has_next :: "'lit \<Rightarrow> bool Heap"
    and left_it_next :: "'lit \<Rightarrow> ('v \<times> 'lit) Heap"
    and forest_clear_imp :: "'fi \<Rightarrow> 'fi Heap"
    and forest_add_root_imp :: "'v \<Rightarrow> 'fi \<Rightarrow> 'fi Heap"
    and forest_extend_imp :: "'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'fi \<Rightarrow> 'fi Heap"
    and forest_it_init :: "forest_part \<Rightarrow> 'fi \<Rightarrow> 'fit Heap"
    and forest_it_has_next :: "'fit \<Rightarrow> bool Heap"
    and forest_it_next :: "'fit \<Rightarrow> ('v \<times> 'fit) Heap"
    and get_path_imp :: "'fi \<Rightarrow> 'v array \<Rightarrow> nat \<Rightarrow> 'v \<Rightarrow> nat Heap"
    and queue_clear_imp :: "'qi \<Rightarrow> unit Heap"
    and queue_extract_min_imp :: "'qi \<Rightarrow> ('v \<times> 'n) option Heap"
    and queue_key_of_imp :: "'qi \<Rightarrow> 'v \<Rightarrow> 'n option Heap"
    and queue_decrease_key_imp :: "'qi \<Rightarrow> 'v \<Rightarrow> 'n \<Rightarrow> unit Heap"
    and queue_insert_imp :: "'qi \<Rightarrow> 'v \<Rightarrow> 'n \<Rightarrow> unit Heap"
    and has_imp :: "'ci \<Rightarrow> 'v \<Rightarrow> bool Heap"
    and current_imp :: "'ci \<Rightarrow> 'v \<Rightarrow> 'v Heap"
    and current_cost_imp :: "'ci \<Rightarrow> 'v \<Rightarrow> 'n Heap"
    and move_imp :: "'ci \<Rightarrow> 'v \<Rightarrow> unit Heap"
    and reset_imp :: "'ci \<Rightarrow> 'v \<Rightarrow> unit Heap"
    and reset_all_imp :: "'ci \<Rightarrow> unit Heap"
begin

definition "pot_val Pti v = do { x \<leftarrow> pot_lookup_imp v Pti; return (val_of x) }"

definition "missed_val Mi v = do { x \<leftarrow> missed_lookup_imp v Mi; return (val_of x) }"

text \<open>Relaxing the edge from @{term l} to @{term r} of weight @{term c}, where @{term pl} and
      @{term ml} are the potential and the missed value of @{term l}. The key of the current best
      even neighbour of @{term r} is read from the queue. If @{term r} has a best even neighbour
      but is not in the queue any more, no improvement is possible.\<close>

definition "relax_new_imp Qi l r key Bi = do {
   Bi' \<leftarrow> ben_update_imp r l Bi;
   queue_insert_imp Qi r key;
   return Bi' }"

definition "relax_old_imp Qi l r key Bi = do {
   ko \<leftarrow> queue_key_of_imp Qi r;
   (case ko of
      None \<Rightarrow> return Bi
    | Some k' \<Rightarrow>
        (if key < k'
         then do { Bi' \<leftarrow> ben_update_imp r l Bi;
                   queue_decrease_key_imp Qi r key;
                   return Bi' }
         else return Bi)) }"

definition "relax_imp Pti Qi l pl ml r c Bi = do {
   pr \<leftarrow> pot_val Pti r;
   b \<leftarrow> ben_lookup_imp r Bi;
   (case b of
      None \<Rightarrow> relax_new_imp Qi l r (c - pl - pr + ml) Bi
    | Some _ \<Rightarrow> relax_old_imp Qi l r (c - pl - pr + ml) Bi) }"

partial_function (heap) scan_imp ::
  "'ci \<Rightarrow> 'pi \<Rightarrow> 'qi \<Rightarrow> 'v \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> 'bi \<Rightarrow> 'bi Heap" where
  "scan_imp Ci Pti Qi l pl ml Bi = do {
     b \<leftarrow> has_imp Ci l;
     (if b then do { r \<leftarrow> current_imp Ci l;
                     c \<leftarrow> current_cost_imp Ci l;
                     move_imp Ci l;
                     Bi' \<leftarrow> relax_imp Pti Qi l pl ml r c Bi;
                     scan_imp Ci Pti Qi l pl ml Bi' }
      else return Bi) }"

definition "update_ben_imp Ci Pti Mi Qi l Bi = do {
   reset_imp Ci l;
   pl \<leftarrow> pot_val Pti l;
   ml \<leftarrow> missed_val Mi l;
   scan_imp Ci Pti Qi l pl ml Bi }"

text \<open>Emptying the data structures of the search in place.\<close>

definition "clear_imp Ci Qi Fi Bi Mi = do {
   Bi' \<leftarrow> ben_clear_imp Bi;
   Mi' \<leftarrow> missed_clear_imp Mi;
   Fi' \<leftarrow> forest_clear_imp Fi;
   queue_clear_imp Qi;
   reset_all_imp Ci;
   return (Fi', Bi', Mi') }"

text \<open>The initial state: every unmatched left vertex becomes a root, and its neighbourhood is
      scanned. The filter for the unmatched left vertices is fused with the iteration over the left
      vertices. The flag records whether there is a root at all.\<close>

definition "init_step Ci Pti Mi Qi Bdi l st = (case st of (Fi, Bi, found) \<Rightarrow> do {
   b \<leftarrow> buddy_imp Bdi l;
   (case b of
      None \<Rightarrow> do { Fi' \<leftarrow> forest_add_root_imp l Fi;
                   Bi' \<leftarrow> update_ben_imp Ci Pti Mi Qi l Bi;
                   return (Fi', Bi', True) }
    | Some _ \<Rightarrow> return (Fi, Bi, found)) })"

definition "init_imp Ci Pti Mi Qi Bdi Li Fi Bi = do {
   it \<leftarrow> left_it_init Li;
   iter_fold left_it_has_next left_it_next (init_step Ci Pti Mi Qi Bdi) it (Fi, Bi, False) }"

text \<open>The main loop of the search. The key of the extracted vertex is the new accumulated value.
      On success, the path is written into @{term Ra}, starting at position 0, and its length is
      returned.\<close>

partial_function (heap) loop_imp ::
  "'ci \<Rightarrow> 'qi \<Rightarrow> 'pi \<Rightarrow> 'bdi \<Rightarrow> 'v array \<Rightarrow> 'fi \<Rightarrow> 'bi \<Rightarrow> 'mi \<Rightarrow>
   (imp_search_result \<times> 'n \<times> 'fi \<times> 'bi \<times> 'mi) Heap" where
  "loop_imp Ci Qi Pti Bdi Ra Fi Bi Mi = do {
     x \<leftarrow> queue_extract_min_imp Qi;
     (case x of
        None \<Rightarrow> return (Imp_Unbounded, 0, Fi, Bi, Mi)
      | Some rk \<Rightarrow> do {
          b \<leftarrow> ben_lookup_imp (fst rk) Bi;
          (case b of
             None \<Rightarrow> return (Imp_Unbounded, 0, Fi, Bi, Mi)
           | Some l \<Rightarrow> do {
               bd \<leftarrow> buddy_imp Bdi (fst rk);
               (case bd of
                  None \<Rightarrow> do {
                    _ \<leftarrow> Array.upd 0 (fst rk) Ra;
                    k \<leftarrow> get_path_imp Fi Ra 1 l;
                    return (Imp_Path k, snd rk, Fi, Bi, Mi) }
                | Some l' \<Rightarrow> do {
                    Mi' \<leftarrow> missed_update_imp (fst rk) (snd rk) Mi;
                    Mi'' \<leftarrow> missed_update_imp l' (snd rk) Mi';
                    Fi' \<leftarrow> forest_extend_imp l (fst rk) l' Fi;
                    Bi' \<leftarrow> update_ben_imp Ci Pti Mi'' Qi l' Bi;
                    loop_imp Ci Qi Pti Bdi Ra Fi' Bi' Mi'' }) }) }) }"

text \<open>The new potential. The even vertices are updated first, then the odd ones. Each vertex is
      updated once, and it still has its old potential when it is processed.\<close>

definition "pot_step_even Mi av v Pti = do {
   pv \<leftarrow> pot_val Pti v; mv \<leftarrow> missed_val Mi v; pot_update_imp v (pv + av - mv) Pti }"

definition "pot_step_odd Mi av v Pti = do {
   pv \<leftarrow> pot_val Pti v; mv \<leftarrow> missed_val Mi v; pot_update_imp v (pv - av + mv) Pti }"

definition "new_pot_imp Fi Mi av Pti = do {
   it \<leftarrow> forest_it_init Evens Fi;
   Pti' \<leftarrow> iter_fold forest_it_has_next forest_it_next (pot_step_even Mi av) it Pti;
   it' \<leftarrow> forest_it_init Odds Fi;
   iter_fold forest_it_has_next forest_it_next (pot_step_odd Mi av) it' Pti' }"

text \<open>The path search. It returns the result, the (possibly new) potential and the handles of
      its own data structures.\<close>

definition "search_imp Ci Qi Pti Bdi Li Ra Fi Bi Mi = do {
   (Fi1, Bi1, Mi1) \<leftarrow> clear_imp Ci Qi Fi Bi Mi;
   (Fi2, Bi2, found) \<leftarrow> init_imp Ci Pti Mi1 Qi Bdi Li Fi1 Bi1;
   (if \<not> found then return (Imp_Matched, Pti, Fi2, Bi2, Mi1)
    else do {
      (res, av, Fi3, Bi3, Mi3) \<leftarrow> loop_imp Ci Qi Pti Bdi Ra Fi2 Bi2 Mi1;
      (case res of
         Imp_Path k \<Rightarrow> do { Pti' \<leftarrow> new_pot_imp Fi3 Mi3 av Pti;
                            return (res, Pti', Fi3, Bi3, Mi3) }
       | _ \<Rightarrow> return (res, Pti, Fi3, Bi3, Mi3)) }) }"

end

subsection \<open>The Proof Locale\<close>

text \<open>The imperative data structures of the search are related to the functional ones:

        \<^item> the best even neighbours by an imperative map with the functional values,
        \<^item> the missed values and the potential by imperative maps whose values are read into the
          reals by @{term h},
        \<^item> the queue, the collection of neighbourhoods and the forest by their imperative
          specifications, where the weights of the collection are @{term edge_costs_code},
        \<^item> the left vertices by an imperative set, iterated in the order @{term lst}, and
        \<^item> the buddy function by an imperative lookup.

      The iteration functions of the functional algorithm iterate in the same order.\<close>

locale primal_dual_path_search_imp =
  primal_dual_path_search where G = G +
  real_embedding h +
  queue: key_value_queue_imp
    where U = "Vs G" and queue_empty = heap_empty and queue_extract_min = heap_extract_min
      and queue_decrease_key = heap_decrease_key and queue_insert = heap_insert
      and queue_invar = heap_invar and queue_abstract = heap_abstract and queue_key = h
      and queue_assn = queue_assn and queue_empty_imp = queue_empty_imp
      and queue_clear_imp = queue_clear_imp and queue_extract_min_imp = queue_extract_min_imp
      and queue_key_of_imp = queue_key_of_imp and queue_decrease_key_imp = queue_decrease_key_imp
      and queue_insert_imp = queue_insert_imp +
  nb: weighted_neighbourhoods_imp_spec
    where idx_invar = rnb_invar and idx_abstract = rnb_abstract and idx_current = rnb_current
      and idx_has = rnb_has and idx_iterated = rnb_iterated and idx_remaining = rnb_remaining
      and idx_move = rnb_move and idx_reset = rnb_reset and K = "vset_to_set left"
      and cost = edge_costs_code and wval = h and nb_init = rnb_init and nb_assn = nb_assn
      and has_imp = has_imp and current_imp = current_imp and current_cost_imp = current_cost_imp
      and move_imp = move_imp and reset_imp = reset_imp and reset_all_imp = reset_all_imp +
  forest: alternating_forest_imp_spec
    where vset_invar = vset_invar and vset_to_set = vset_to_set and odds = odds
      and abstract_forest = abstract_forest and forest_invar = forest_invar and roots = roots
      and vset_empty = vset_empty
      and extend_forest_even_unclassified = extend_forest_even_unclassified
      and empty_forest = empty_forest and get_path = get_path and evens = evens and lst = lst
      and forest_assn = forest_assn and forest_empty_imp = forest_empty_imp
      and forest_clear_imp = forest_clear_imp and forest_add_root_imp = forest_add_root_imp
      and forest_extend_imp = forest_extend_imp and evens_memb_imp = evens_memb_imp
      and odds_memb_imp = odds_memb_imp and forest_is_it = forest_is_it
      and forest_it_init = forest_it_init and forest_it_has_next = forest_it_has_next
      and forest_it_next = forest_it_next and get_path_imp = get_path_imp +
  ben: imp_map_conn_clear
    where is_map = ben_is_map and lookup_imp = ben_lookup_imp and update_imp = ben_update_imp
      and m_update = ben_upd and m_lookup = ben_lookup and m_invar = ben_invar
      and R = "\<lambda>_ x y. x = y" and clear_imp = ben_clear_imp and m_empty = ben_empty +
  missed: imp_map_conn_clear
    where is_map = missed_is_map and lookup_imp = missed_lookup_imp
      and update_imp = missed_update_imp
      and m_update = missed_upd and m_lookup = missed_lookup and m_invar = missed_invar
      and R = "\<lambda>_ c x. h c = x" and clear_imp = missed_clear_imp and m_empty = missed_empty +
  pot: imp_map_conn
    where is_map = pot_is_map and lookup_imp = pot_lookup_imp and update_imp = pot_update_imp
      and m_update = potential_upd and m_lookup = potential_lookup and m_invar = potential_invar
      and R = "\<lambda>_ c x. h c = x" +
  left: imp_set_ordered_iterate
    where is_set = left_is_set and lst = lst and is_it = left_is_it and it_init = left_it_init
      and it_has_next = left_it_has_next and it_next = left_it_next
  for G :: "'v::heap set set" and h :: "'n::linordered_idom \<Rightarrow> real"
    and queue_assn queue_empty_imp queue_clear_imp queue_extract_min_imp queue_key_of_imp
        queue_decrease_key_imp queue_insert_imp
    and nb_assn has_imp current_imp current_cost_imp move_imp reset_imp reset_all_imp
    and lst forest_assn forest_empty_imp forest_clear_imp forest_add_root_imp
        forest_extend_imp evens_memb_imp odds_memb_imp forest_is_it forest_it_init
        forest_it_has_next forest_it_next get_path_imp
    and ben_is_map ben_lookup_imp ben_update_imp ben_clear_imp
    and missed_is_map missed_lookup_imp missed_update_imp missed_clear_imp
    and pot_is_map pot_lookup_imp pot_update_imp
    and left_is_set left_is_it left_it_init left_it_has_next left_it_next +
  fixes buddy_assn :: "'bdi \<Rightarrow> assn"
    and buddy_imp :: "'bdi \<Rightarrow> 'v \<Rightarrow> 'v option Heap"
  assumes buddy_rule[sep_heap_rules]:
      "<buddy_assn Bdi> buddy_imp Bdi v <\<lambda>r. buddy_assn Bdi * \<up>(r = buddy v)>"
    and vset_iterate_ben_lst:
      "\<And>V f init. vset_invar V \<Longrightarrow> vset_iterate_ben f init V = foldl f init (lst (vset_to_set V))"
    and vset_iterate_pot_lst:
      "\<And>V f init. vset_invar V \<Longrightarrow> vset_iterate_pot f init V = foldl f init (lst (vset_to_set V))"
begin

end

sublocale primal_dual_path_search_imp \<subseteq> code: primal_dual_path_search_imp_code
  ben_lookup_imp ben_update_imp ben_clear_imp missed_lookup_imp missed_update_imp
  missed_clear_imp pot_lookup_imp pot_update_imp buddy_imp left_it_init left_it_has_next
  left_it_next forest_clear_imp forest_add_root_imp forest_extend_imp forest_it_init
  forest_it_has_next forest_it_next get_path_imp queue_clear_imp queue_extract_min_imp
  queue_key_of_imp queue_decrease_key_imp queue_insert_imp has_imp current_imp current_cost_imp
  move_imp reset_imp reset_all_imp .

context primal_dual_path_search_imp
begin

subsection \<open>Reading Values\<close>

lemma val_of_rel:
  "rel_option (\<lambda>c x. h c = x) r y \<Longrightarrow> h (val_of r) = (case y of None \<Rightarrow> 0 | Some x \<Rightarrow> x)"
  by (cases r; cases y) (auto simp: val_of_def)

lemma pot_val_rule[sep_heap_rules]:
  "<pot.map_assn P Pti> code.pot_val Pti v
   <\<lambda>c. pot.map_assn P Pti * \<up>(h c = abstract_real_map (potential_lookup P) v)>"
  unfolding code.pot_val_def
  by (sep_auto heap: pot.map_assn_lookup_rule simp: val_of_rel abstract_real_map_def)

lemma missed_val_rule[sep_heap_rules]:
  "<missed.map_assn M Mi> code.missed_val Mi v
   <\<lambda>c. missed.map_assn M Mi * \<up>(h c = abstract_real_map (missed_lookup M) v)>"
  unfolding code.missed_val_def
  by (sep_auto heap: missed.map_assn_lookup_rule simp: val_of_rel abstract_real_map_def)

lemma rel_option_eq_iff[simp]: "rel_option (\<lambda>x y. x = y) a b \<longleftrightarrow> a = b"
  by (simp add: option.rel_eq)

lemma ben_lookup_rule[sep_heap_rules]:
  "<ben.map_assn B Bi> ben_lookup_imp r Bi <\<lambda>x. ben.map_assn B Bi * \<up>(x = ben_lookup B r)>"
  by (sep_auto heap: ben.map_assn_lookup_rule)

lemma ben_update_rule[sep_heap_rules]:
  "<ben.map_assn B Bi> ben_update_imp r l Bi <ben.map_assn (ben_upd r l B)>"
  by (sep_auto heap: ben.map_assn_update_rule)

declare ben.map_assn_lookup_rule[sep_heap_rules del] ben.map_assn_update_rule[sep_heap_rules del]
declare pot.map_assn_lookup_rule[sep_heap_rules del] missed.map_assn_lookup_rule[sep_heap_rules del]


subsection \<open>Relaxing an Edge\<close>

text \<open>The queue key of a right vertex with a best even neighbour is the key that the functional
      algorithm recomputes. If the vertex is not in the queue any more, the functional algorithm
      does not change anything.\<close>

lemma relax_queue_key:
  assumes "scan_inv off l ben queue" "r \<in> rneighbs l" "ben_lookup ben r = Some l'"
  shows "(r, k) \<in> heap_abstract queue \<Longrightarrow> k = w\<^sub>\<pi>_code l' r + off l'"
        "\<nexists>k. (r, k) \<in> heap_abstract queue \<Longrightarrow> \<not> w\<^sub>\<pi>_code l r + off l < w\<^sub>\<pi>_code l' r + off l'"
proof-
  note I = scan_invD[OF assms(1)]
  have code': "w\<^sub>\<pi>_code l' r = w\<^sub>\<pi> l' r"
    using w\<^sub>\<pi>_code_is[of l' r] I(6,7)[OF assms(3)] by simp
  show "(r, k) \<in> heap_abstract queue \<Longrightarrow> k = w\<^sub>\<pi>_code l' r + off l'"
    using I(4)[of r k] assms(3) code' by auto
  show "\<nexists>k. (r, k) \<in> heap_abstract queue \<Longrightarrow> \<not> w\<^sub>\<pi>_code l r + off l < w\<^sub>\<pi>_code l' r + off l'"
    using relax_neighbour_Some(2)[OF assms] by blast
qed

lemma relax_new_rule:
  "\<lbrakk>heap_invar queue; r \<in> Vs G; \<nexists>k. (r, k) \<in> heap_abstract queue\<rbrakk> \<Longrightarrow>
   <queue_assn queue Qi * ben.map_assn ben Bi> code.relax_new_imp Qi l r key Bi
   <\<lambda>Bi'. queue_assn (heap_insert queue r (h key)) Qi * ben.map_assn (ben_upd r l ben) Bi'>"
  unfolding code.relax_new_imp_def
  by (sep_auto heap: queue.queue_insert_rule)

lemma relax_old_rule:
  assumes "heap_invar queue" "r \<in> Vs G"
      and in_heap: "\<And>k. (r, k) \<in> heap_abstract queue \<Longrightarrow> k = K'"
      and not_in_heap: "\<nexists>k. (r, k) \<in> heap_abstract queue \<Longrightarrow> \<not> h key < K'"
  shows "<queue_assn queue Qi * ben.map_assn ben Bi> code.relax_old_imp Qi l r key Bi
         <\<lambda>Bi'. if h key < K'
                then queue_assn (heap_decrease_key queue r (h key)) Qi *
                     ben.map_assn (ben_upd r l ben) Bi'
                else queue_assn queue Qi * ben.map_assn ben Bi'>"
proof-
  have some: "(r, h k') \<in> heap_abstract queue \<Longrightarrow> h k' = K'" for k'
    using in_heap by blast
  show ?thesis
    unfolding code.relax_old_imp_def
    apply(sep_auto heap: queue.queue_key_of_rule simp: assms(1,2) split: option.splits)
    subgoal using not_in_heap by (sep_auto)
    subgoal for ha haa ra k'
      using some[of k']
      by (cases "key < k'")
         (sep_auto heap: queue.queue_decrease_key_rule[of queue r "h k'"] simp: assms(1,2))+
    done
qed

lemma relax_imp_rule:
  assumes inv: "scan_inv off l ben queue" and rn: "r \<in> rneighbs l"
      and hc: "h c = edge_costs_code l r" and hpl: "h pl = \<pi> l" and hml: "h ml = off l"
  shows "<pot.map_assn initial_pot Pti * queue_assn queue Qi * ben.map_assn ben Bi>
         code.relax_imp Pti Qi l pl ml r c Bi
         <\<lambda>Bi'. pot.map_assn initial_pot Pti *
                queue_assn (snd (relax_neighbour off l (ben, queue) r)) Qi *
                ben.map_assn (fst (relax_neighbour off l (ben, queue) r)) Bi'>"
proof-
  note I = scan_invD[OF inv]
  have rG: "r \<in> Vs G" using rneighbs_in_G[OF I(3) rn] by (auto intro: edges_are_Vs_2)
  have key: "h pr = \<pi> r \<Longrightarrow> h (c - pl - pr + ml) = w\<^sub>\<pi>_code l r + off l" for pr
    using hc hpl hml by (simp add: w\<^sub>\<pi>_code_def h_add)
  show ?thesis
  proof(cases "ben_lookup ben r")
    case None
    note legal = relax_neighbour_None[OF inv rn None]
    show ?thesis
      unfolding code.relax_imp_def
      by (sep_auto heap: relax_new_rule simp: None relax_neighbour_def key I(2) rG legal(2))
  next
    case (Some l')
    note qk = relax_queue_key[OF inv rn Some]
    have old: "h pr = \<pi> r \<Longrightarrow>
      <queue_assn queue Qi * ben.map_assn ben Bi> code.relax_old_imp Qi l r (c - pl - pr + ml) Bi
      <\<lambda>Bi'. queue_assn (snd (relax_neighbour off l (ben, queue) r)) Qi *
             ben.map_assn (fst (relax_neighbour off l (ben, queue) r)) Bi'>" for pr
      apply(rule ht_cons_post[OF relax_old_rule[OF I(2) rG, of "w\<^sub>\<pi>_code l' r + off l'"]])
      using qk
      by (auto simp: key relax_neighbour_def Some split: if_splits intro: ent_refl_true)
    show ?thesis
      unfolding code.relax_imp_def
      by (sep_auto heap: old simp: Some)
  qed
qed

subsection \<open>Scanning a Neighbourhood\<close>

lemma scan_imp_rule:
  assumes "rnb_invar C" "l \<in> L" "rnb_abstract C = rnb_abstract rnb_init"
      and "scan_inv off l ben queue" "h pl = \<pi> l" "h ml = off l"
  shows "<nb_assn C Ci * pot.map_assn initial_pot Pti * queue_assn queue Qi * ben.map_assn ben Bi>
         code.scan_imp Ci Pti Qi l pl ml Bi
         <\<lambda>Bi'. nb_assn (fst (scan_neighbours off l C (ben, queue))) Ci *
                pot.map_assn initial_pot Pti *
                queue_assn (snd (snd (scan_neighbours off l C (ben, queue)))) Qi *
                ben.map_assn (fst (snd (scan_neighbours off l C (ben, queue)))) Bi'>"
  using assms
proof(induction "card (rnb_remaining C l)" arbitrary: C ben queue Bi rule: less_induct)
  case less
  have sub: "rnb_remaining C l \<subseteq> rneighbs l"
    using rnb.idx_partition_union[OF less.prems(1,2)] less.prems(3) by auto
  have fin: "finite (rnb_remaining C l)"
    using finite_rneighbs[OF less.prems(2)] sub by (rule finite_subset[rotated])
  show ?case
  proof(cases "rnb_has C l")
    case True
    have ne: "rnb_remaining C l \<noteq> {}" using rnb.idx_has[OF less.prems(1,2)] True by simp
    have x_in: "rnb_current C l \<in> rnb_remaining C l"
      using rnb.idx_current[OF less.prems(1,2) ne] .
    have x_rn: "rnb_current C l \<in> rneighbs l" using x_in sub by auto
    have C': "rnb_invar (rnb_move C l)"
             "rnb_abstract (rnb_move C l) = rnb_abstract rnb_init"
             "rnb_remaining (rnb_move C l) l = rnb_remaining C l - {rnb_current C l}"
      using rnb.idx_move_invar[OF less.prems(1,2)] rnb.idx_move_remaining[OF less.prems(1,2) ne]
            rnb.idx_move_abstract[OF less.prems(1,2) ne] less.prems(3)
      by (auto simp: fun_eq_iff)
    have card_less: "card (rnb_remaining (rnb_move C l) l) < card (rnb_remaining C l)"
      using card_Diff1_less[OF fin x_in] by (simp add: C'(3))
    have scan_eq: "scan_neighbours off l C (ben, queue) =
                   scan_neighbours off l (rnb_move C l)
                      (relax_neighbour off l (ben, queue) (rnb_current C l))"
      by (simp add: scan_neighbours.simps[of off l C] True)
    have inv': "scan_inv off l (fst (relax_neighbour off l (ben, queue) (rnb_current C l)))
                               (snd (relax_neighbour off l (ben, queue) (rnb_current C l)))"
      using relax_neighbour_pres(1)[OF less.prems(4) x_rn] .
    note IH = less.hyps[OF card_less C'(1) less.prems(2) C'(2) inv' less.prems(5,6), simplified]
    note relax = relax_imp_rule[OF less.prems(4) x_rn _ less.prems(5,6)]
    show ?thesis
      apply(subst code.scan_imp.simps)
      apply(sep_auto heap: nb.has_rule nb.current_rule nb.current_cost_rule nb.move_rule
                     simp: less.prems(1,2) True ne)
      apply(sep_auto heap: relax)
      by (sep_auto heap: IH simp: scan_eq True)
  next
    case False
    have scan_eq: "scan_neighbours off l C (ben, queue) = (C, ben, queue)"
      by (simp add: scan_neighbours.simps[of off l C] False)
    show ?thesis
      apply(subst code.scan_imp.simps)
      by (sep_auto heap: nb.has_rule simp: less.prems(1,2) False scan_eq)
  qed
qed


lemma update_ben_imp_rule:
  assumes "rnb_invar C" "l \<in> L" "rnb_abstract C = rnb_abstract rnb_init"
      and "scan_inv (abstract_real_map (missed_lookup M)) l ben queue"
  shows "<nb_assn C Ci * pot.map_assn initial_pot Pti * missed.map_assn M Mi *
          queue_assn queue Qi * ben.map_assn ben Bi>
         code.update_ben_imp Ci Pti Mi Qi l Bi
         <\<lambda>Bi'. nb_assn (fst (update_best_even_neighbour
                                  (abstract_real_map (missed_lookup M)) C ben queue l)) Ci *
                pot.map_assn initial_pot Pti * missed.map_assn M Mi *
                queue_assn (snd (snd (update_best_even_neighbour
                                  (abstract_real_map (missed_lookup M)) C ben queue l))) Qi *
                ben.map_assn (fst (snd (update_best_even_neighbour
                                  (abstract_real_map (missed_lookup M)) C ben queue l))) Bi'>"
proof-
  have C0: "rnb_invar (rnb_reset C l)" "rnb_abstract (rnb_reset C l) = rnb_abstract rnb_init"
    using rnb.idx_reset_invar[OF assms(1,2)] rnb.idx_reset_abstract[OF assms(1,2)] assms(3)
    by (auto simp: fun_eq_iff)
  note scan = scan_imp_rule[OF C0(1) assms(2) C0(2) assms(4)]
  show ?thesis
    unfolding code.update_ben_imp_def update_best_even_neighbour_def
    by (sep_auto heap: nb.reset_rule scan simp: assms(1,2))
qed

text \<open>Functional preservation facts for a whole scan.\<close>

lemma foldl_relax_pres:
  "\<lbrakk>scan_inv off l ben queue; set rs \<subseteq> rneighbs l\<rbrakk> \<Longrightarrow>
   scan_inv off l (fst (foldl (relax_neighbour off l) (ben, queue) rs))
                  (snd (foldl (relax_neighbour off l) (ben, queue) rs)) \<and>
   (all_in_heap ben queue \<longrightarrow>
    all_in_heap (fst (foldl (relax_neighbour off l) (ben, queue) rs))
                (snd (foldl (relax_neighbour off l) (ben, queue) rs)))"
proof(induction rs arbitrary: ben queue)
  case (Cons r rs)
  have r: "r \<in> rneighbs l" using Cons.prems(2) by simp
  obtain ben' queue' where bq': "relax_neighbour off l (ben, queue) r = (ben', queue')"
    by (cases "relax_neighbour off l (ben, queue) r") auto
  have inv': "scan_inv off l ben' queue'" "all_in_heap ben queue \<Longrightarrow> all_in_heap ben' queue'"
    using relax_neighbour_pres[OF Cons.prems(1) r] by (auto simp: bq')
  show ?case
    using Cons.IH[OF inv'(1)] Cons.prems(2) inv'(2) by (simp add: bq')
qed simp

lemma ubn_pres:
  assumes "rnb_invar C" "l \<in> L" "rnb_abstract C = rnb_abstract rnb_init"
      and "scan_inv off l ben queue"
  shows "rnb_invar (fst (update_best_even_neighbour off C ben queue l))"
        "rnb_abstract (fst (update_best_even_neighbour off C ben queue l)) = rnb_abstract rnb_init"
        "scan_inv off l (fst (snd (update_best_even_neighbour off C ben queue l)))
                        (snd (snd (update_best_even_neighbour off C ben queue l)))"
        "all_in_heap ben queue \<Longrightarrow>
         all_in_heap (fst (snd (update_best_even_neighbour off C ben queue l)))
                     (snd (snd (update_best_even_neighbour off C ben queue l)))"
proof-
  obtain C' ben' queue' where eq: "update_best_even_neighbour off C ben queue l = (C', ben', queue')"
    by (cases "update_best_even_neighbour off C ben queue l") auto
  note fl = update_best_even_neighbour_is_foldl[OF assms(1-3) eq[symmetric]]
  obtain rs where rs: "set rs = rneighbs l" "(ben', queue') = foldl (relax_neighbour off l) (ben, queue) rs"
    using fl(1) by blast
  note pres = foldl_relax_pres[OF assms(4), of rs]
  show "rnb_invar (fst (update_best_even_neighbour off C ben queue l))"
       "rnb_abstract (fst (update_best_even_neighbour off C ben queue l)) = rnb_abstract rnb_init"
    using fl(2,3) by (auto simp: eq)
  show "scan_inv off l (fst (snd (update_best_even_neighbour off C ben queue l)))
                        (snd (snd (update_best_even_neighbour off C ben queue l)))"
       "all_in_heap ben queue \<Longrightarrow>
         all_in_heap (fst (snd (update_best_even_neighbour off C ben queue l)))
                     (snd (snd (update_best_even_neighbour off C ben queue l)))"
  proof-
    have "set rs \<subseteq> rneighbs l" using rs(1) by simp
    hence "scan_inv off l ben' queue' \<and> (all_in_heap ben queue \<longrightarrow> all_in_heap ben' queue')"
      using pres unfolding rs(2)[symmetric] by simp
    thus "scan_inv off l (fst (snd (update_best_even_neighbour off C ben queue l)))
                        (snd (snd (update_best_even_neighbour off C ben queue l)))"
       "all_in_heap ben queue \<Longrightarrow>
         all_in_heap (fst (snd (update_best_even_neighbour off C ben queue l)))
                     (snd (snd (update_best_even_neighbour off C ben queue l)))"
      by (simp_all add: eq)
  qed
qed

subsection \<open>Clearing\<close>

text \<open>The data structures of the search, with arbitrary contents. Only the collection of
      neighbourhoods has to be one of the collection of the graph.\<close>

definition "scratch_assn Ci Qi Fi Bi Mi =
  (\<exists>\<^sub>AC H F B M. nb_assn C Ci * queue_assn H Qi * forest_assn F Fi * ben.map_assn B Bi *
                 missed.map_assn M Mi *
                 \<up>(rnb_invar C \<and> (\<forall>i\<in>L. rnb_abstract C i = rnb_abstract rnb_init i)))"

lemma clear_imp_rule:
  "<scratch_assn Ci Qi Fi Bi Mi> code.clear_imp Ci Qi Fi Bi Mi
   <\<lambda>(Fi', Bi', Mi'). nb_assn rnb_init Ci * queue_assn heap_empty Qi *
                     forest_assn (empty_forest vset_empty) Fi' *
                     ben.map_assn ben_empty Bi' * missed.map_assn missed_empty Mi'>"
  unfolding code.clear_imp_def scratch_assn_def
  by (sep_auto heap: ben.map_assn_clear_rule missed.map_assn_clear_rule
                     forest.forest_clear_rule[OF vset.invar_empty vset.set_empty]
                     queue.queue_clear_rule nb.reset_all_rule)

subsection \<open>The Initial State: Functional Part\<close>

text \<open>The iteration over the left vertices with the fused test for the unmatched ones. The state
      of the fold consists of the roots so far, the collection, the best even neighbours and the
      queue, and the flag.\<close>

definition "init_g = (\<lambda>(S, cbq, fnd) v.
   if buddy v = None
   then (insert v S,
         update_best_even_neighbour (\<lambda>x. 0) (fst cbq) (fst (snd cbq)) (snd (snd cbq)) v, True)
   else (S, cbq, fnd))"

lemma init_fold:
  "foldl init_g (S, cbq, fnd) xs =
   (S \<union> set (filter (\<lambda>v. buddy v = None) xs),
    foldl (\<lambda>cbq l. update_best_even_neighbour (\<lambda>x. 0) (fst cbq) (fst (snd cbq)) (snd (snd cbq)) l)
          cbq (filter (\<lambda>v. buddy v = None) xs),
    fnd \<or> filter (\<lambda>v. buddy v = None) xs \<noteq> [])"
  by (induction xs arbitrary: S cbq fnd) (auto simp: init_g_def)

definition "init_ok cbq =
  (rnb_invar (fst cbq) \<and> rnb_abstract (fst cbq) = rnb_abstract rnb_init \<and>
   all_in_heap (fst (snd cbq)) (snd (snd cbq)) \<and>
   (\<forall>l\<in>L. scan_inv (\<lambda>x. 0) l (fst (snd cbq)) (snd (snd cbq))))"

lemma scan_inv_zero_other:
  "\<lbrakk>scan_inv (\<lambda>x. 0) l ben queue; all_in_heap ben queue; l' \<in> L\<rbrakk> \<Longrightarrow>
   scan_inv (\<lambda>x. 0) l' ben queue"
  by (auto simp: scan_inv_def all_in_heap_def)

lemma init_ok_step:
  assumes "init_ok cbq" "l \<in> L"
  shows "init_ok (update_best_even_neighbour (\<lambda>x. 0) (fst cbq) (fst (snd cbq)) (snd (snd cbq)) l)"
proof-
  have c: "rnb_invar (fst cbq)" "rnb_abstract (fst cbq) = rnb_abstract rnb_init"
          "all_in_heap (fst (snd cbq)) (snd (snd cbq))"
          "scan_inv (\<lambda>x. 0) l (fst (snd cbq)) (snd (snd cbq))"
    using assms by (auto simp: init_ok_def)
  note P = ubn_pres[OF c(1) assms(2) c(2) c(4)]
  note aih = P(4)[OF c(3)]
  show ?thesis
    unfolding init_ok_def
    using P(1,2) aih scan_inv_zero_other[OF P(3) aih] by blast
qed

lemma init_ok_init: "init_ok (rnb_init, ben_empty, heap_empty)"
  using G(4) best_even_neighbour(1,4) heap(1,11)
  by (auto simp: init_ok_def all_in_heap_def scan_inv_def)

definition "init_P v b = (v \<in> L \<and> init_ok (fst (snd b)))"

lemma init_fold_pre:
  "\<lbrakk>set xs \<subseteq> L; init_ok cbq\<rbrakk> \<Longrightarrow> fold_pre init_P init_g (S, cbq, fnd) xs"
proof(induction xs arbitrary: S cbq fnd)
  case (Cons x xs)
  have x: "x \<in> L" "set xs \<subseteq> L" using Cons.prems(1) by auto
  show ?case
  proof(cases "buddy x = None")
    case True
    thus ?thesis
      using Cons.IH[OF x(2) init_ok_step[OF Cons.prems(2) x(1)]] Cons.prems(2) x(1)
      by (simp add: init_P_def init_g_def)
  next
    case False
    have eq: "init_g (S, cbq, fnd) x = (S, cbq, fnd)" by (simp add: init_g_def False)
    show ?thesis
      using Cons.IH[OF x(2) Cons.prems(2)] Cons.prems(2) x(1)
      by (simp add: init_P_def eq)
  qed
qed simp

lemma init_fold_result:
  defines "res \<equiv> foldl init_g ({}, (rnb_init, ben_empty, heap_empty), False) (lst L)"
  shows "fst res = vset_to_set forest_roots"
        "fst (snd res) = init_best_even_neighbour"
        "snd (snd res) \<longleftrightarrow> \<not> vset_is_empty unmatched_lefts"
proof-
  have U: "vset_to_set unmatched_lefts = L \<inter> Collect (\<lambda>v. buddy v = None)"
    using vset_iterations(4)[OF G(2), of "\<lambda>v. if buddy v = None then True else False"]
    by (simp add: unmatched_lefts_def)
  have lstU: "lst (vset_to_set unmatched_lefts) = filter (\<lambda>v. buddy v = None) (lst L)"
    using forest.lst_filter[OF finite_L] U by simp
  have "set (filter (\<lambda>v. buddy v = None) (lst L)) = vset_to_set unmatched_lefts"
    using forest.lst_set[OF finite_L] U by auto
  thus "fst res = vset_to_set forest_roots"
    by (simp add: res_def init_fold forest_roots_def)
  show "fst (snd res) = init_best_even_neighbour"
    by (simp add: res_def init_fold init_best_even_neighbour_def update_best_even_neighbours_def
                  vset_iterate_ben_lst[OF unmatched_lefts(2)] lstU)
  have "filter (\<lambda>v. buddy v = None) (lst L) \<noteq> [] \<longleftrightarrow> vset_to_set unmatched_lefts \<noteq> {}"
    using forest.lst_set[OF finite_L] U by (auto simp: filter_empty_conv)
  thus "snd (snd res) \<longleftrightarrow> \<not> vset_is_empty unmatched_lefts"
    by (simp add: res_def init_fold vset_is_empty[OF unmatched_lefts(2)])
qed

subsection \<open>The Initial State: Imperative Part\<close>

lemma missed_empty_zero: "abstract_real_map (missed_lookup missed_empty) = (\<lambda>x. 0)"
  by (auto simp: abstract_real_map_def missed(2))

lemma add_root_insert:
  "vset_invar Rs \<Longrightarrow>
   <forest_assn (empty_forest Rs) Fi> forest_add_root_imp v Fi
   <forest_assn (empty_forest (vset_insert v Rs))>"
  by (rule forest.forest_add_root_rule) (auto simp: vset.invar_insert vset.set_insert)

definition "init_A Ci Pti Mi Qi Bdi b c = (case b of (S, cbq, fnd) \<Rightarrow> case c of (Fi, Bi, fndi) \<Rightarrow>
   (\<exists>\<^sub>ARs. forest_assn (empty_forest Rs) Fi * \<up>(vset_invar Rs \<and> vset_to_set Rs = S)) *
   nb_assn (fst cbq) Ci * queue_assn (snd (snd cbq)) Qi * ben.map_assn (fst (snd cbq)) Bi *
   pot.map_assn initial_pot Pti * missed.map_assn missed_empty Mi * buddy_assn Bdi *
   \<up>(fndi = fnd))"

lemma init_step_rule:
  assumes "init_P v b"
  shows "<init_A Ci Pti Mi Qi Bdi b c> code.init_step Ci Pti Mi Qi Bdi v c
         <init_A Ci Pti Mi Qi Bdi (init_g b v)>"
proof-
  obtain S C ben queue fnd where b: "b = (S, (C, ben, queue), fnd)" by (cases b) auto
  obtain Fi Bi fndi where c: "c = (Fi, Bi, fndi)" by (cases c) auto
  have v: "v \<in> L" and ok: "init_ok (C, ben, queue)" using assms by (auto simp: init_P_def b)
  have C: "rnb_invar C" "rnb_abstract C = rnb_abstract rnb_init"
          "scan_inv (abstract_real_map (missed_lookup missed_empty)) v ben queue"
    using ok v by (auto simp: init_ok_def missed_empty_zero)
  note ubi = update_ben_imp_rule[OF C(1) v C(2) C(3), unfolded missed_empty_zero]
  show ?thesis
  proof(cases "buddy v")
    case None
    show ?thesis
      unfolding code.init_step_def init_A_def b c
      by (sep_auto heap: add_root_insert ubi
                   simp: None init_g_def vset.invar_insert vset.set_insert)
  next
    case (Some v')
    show ?thesis
      unfolding code.init_step_def init_A_def b c
      by (sep_auto simp: Some init_g_def)
  qed
qed

lemma forest_roots_cong:
  "\<lbrakk>vset_invar Rs; vset_to_set Rs = vset_to_set forest_roots\<rbrakk> \<Longrightarrow>
   forest_assn (empty_forest Rs) = forest_assn (empty_forest forest_roots)"
  using forest.forest_empty_cong[of Rs forest_roots] unmatched_lefts(2)
  by (simp add: forest_roots_def)

lemma init_imp_rule:
  "<left_is_set L Li * forest_assn (empty_forest vset_empty) Fi * nb_assn rnb_init Ci *
    queue_assn heap_empty Qi * ben.map_assn ben_empty Bi * pot.map_assn initial_pot Pti *
    missed.map_assn missed_empty Mi * buddy_assn Bdi>
   code.init_imp Ci Pti Mi Qi Bdi Li Fi Bi
   <\<lambda>(Fi', Bi', fnd). left_is_set L Li * forest_assn (empty_forest forest_roots) Fi' *
       nb_assn (fst init_best_even_neighbour) Ci *
       queue_assn (snd (snd init_best_even_neighbour)) Qi *
       ben.map_assn (fst (snd init_best_even_neighbour)) Bi' * pot.map_assn initial_pot Pti *
       missed.map_assn missed_empty Mi * buddy_assn Bdi *
       \<up>(fnd \<longleftrightarrow> \<not> vset_is_empty unmatched_lefts)>"
proof-
  define b0 where "b0 = ({}::'v set, (rnb_init, ben_empty, heap_empty), False)"
  have pre: "fold_pre init_P init_g b0 (lst L)"
    unfolding b0_def
    by (rule init_fold_pre[OF _ init_ok_init]) (simp add: forest.lst_set[OF finite_L])
  note fold = iter_fold_rule_gen[where I = "left_is_it L Li" and Q = "left_is_set L Li"
                 and A = "init_A Ci Pti Mi Qi Bdi",
                 OF left.it_has_next_rule left.it_next_rule left.quit_iteration init_step_rule pre]
  have main: "<left_is_set L Li * init_A Ci Pti Mi Qi Bdi b0 (Fi, Bi, False)>
               code.init_imp Ci Pti Mi Qi Bdi Li Fi Bi
               <\<lambda>c'. left_is_set L Li * init_A Ci Pti Mi Qi Bdi (foldl init_g b0 (lst L)) c'>"
    unfolding code.init_imp_def
    by (sep_auto heap: left.it_init_rule fold)
  have res: "foldl init_g b0 (lst L) =
             (vset_to_set forest_roots, init_best_even_neighbour, \<not> vset_is_empty unmatched_lefts)"
    using init_fold_result unfolding b0_def by (simp add: prod_eq_iff)
  show ?thesis
  proof(rule ht_cons[OF _ _ main], goal_cases)
    case 1
    show ?case
      by (sep_auto simp: init_A_def b0_def vset.invar_empty vset.set_empty)
  next
    case (2 c)
    obtain Fi' Bi' fnd where c: "c = (Fi', Bi', fnd)" by (cases c) auto
    show ?case
      unfolding init_A_def res c prod.case
      apply(simp only: ex_assn_move_out star_aci)
      apply(rule ent_ex_preI)
      subgoal for Rs
        by (cases fnd; cases "vset_invar Rs \<and> vset_to_set Rs = vset_to_set forest_roots")
           (sep_auto simp: forest_roots_cong)+
      done
  qed
qed

subsection \<open>The Loop: Functional Part\<close>

lemma extract_key:
  assumes "search_invars state" "heap_extract_min (heap state) = (queue0, Some r)"
      and "(r, k) \<in> heap_abstract (heap state)"
  shows "k = w\<^sub>\<pi>_code (the (ben_lookup (best_even_neighbour state) r)) r +
             missed_at state (the (ben_lookup (best_even_neighbour state) r))"
proof-
  have I: "invar_basic state" "invar_best_even_neighbour_heap state"
          "invar_best_even_neighbour_map state"
    using assms(1) by (auto simp: search_invars_def)
  note F = extract_facts[OF I assms(2)]
  obtain l where l: "ben_lookup (best_even_neighbour state) r = Some l" "k = w\<^sub>\<pi> l r + missed_at state l"
    using invar_best_even_neighbour_heapD[OF I(2)] assms(3) by blast
  have code: "w\<^sub>\<pi>_code l r = w\<^sub>\<pi> l r"
    using w\<^sub>\<pi>_code_is[of l r] F(3,4) l(1) F(1) by simp
  show ?thesis using l code by simp
qed

lemma cont_upd_eq:
  assumes "heap_extract_min (heap state) = (queue0, Some r)" "buddy r = Some l'"
  defines "l \<equiv> the (ben_lookup (best_even_neighbour state) r)"
  defines "acc' \<equiv> w\<^sub>\<pi>_code l r + missed_at state l"
  defines "missed' \<equiv> missed_upd l' acc' (missed_upd r acc' (missed state))"
  defines "U \<equiv> update_best_even_neighbour (abstract_real_map (missed_lookup missed'))
                  (neighb_coll state) (best_even_neighbour state) queue0 l'"
  shows "search_path_loop_cont_upd state =
         state \<lparr> forest := extend_forest_even_unclassified (forest state) l r l',
                 best_even_neighbour := fst (snd U), neighb_coll := fst U,
                 heap := snd (snd U), missed := missed', acc := acc' \<rparr>"
  using assms(1,2)
  by (simp add: search_path_loop_cont_upd_def Let_def l_def acc'_def missed'_def U_def
         split: prod.split)

lemma search_invars_basic:
  "search_invars state \<Longrightarrow> invar_basic state"
  by (simp add: search_invars_def)

lemma invar_basic_upd:
  "invar_basic (state\<lparr>augpath := p\<rparr>) = invar_basic state"
  "invar_basic (state\<lparr>acc := a\<rparr>) = invar_basic state"
  by (simp_all add: invar_basic_def)

lemma succ_upd_shape:
  "\<exists>a p. search_path_loop_succ_upd state = state\<lparr>acc := a, augpath := p\<rparr>"
  by (auto simp: search_path_loop_succ_upd_def Let_def split: prod.split)

lemma loop_final_basic:
  assumes "search_invars state"
  shows "invar_basic (search_path_loop state)"
proof-
  have "search_invars state \<longrightarrow> invar_basic (search_path_loop state)"
  proof(induction rule: search_path_loop_induct[OF search_invars_dom[OF assms]])
    case (1 state)
    show ?case
    proof(rule, cases state rule: search_path_loop_cases)
      assume "search_invars state" "search_path_loop_fail_cond state"
      thus "invar_basic (search_path_loop state)"
        by (simp add: search_path_loop_simps(1) search_path_loop_fail_upd_def
                      search_invars_basic invar_basic_upd)
    next
      assume "search_invars state" "search_path_loop_succ_cond state"
      thus "invar_basic (search_path_loop state)"
        using succ_upd_shape[of state]
        by (auto simp: search_path_loop_simps(2) search_invars_basic invar_basic_upd)
    next
      assume a: "search_invars state" "search_path_loop_cont_cond state"
      thus "invar_basic (search_path_loop state)"
        using 1(2)[OF a(2)] search_invars_step[OF a(2,1)]
        by (simp add: search_path_loop_simps(3)[OF 1(1) a(2)])
    qed
  qed
  thus ?thesis using assms by simp
qed

subsection \<open>The Loop: Imperative Part\<close>

definition "loop_assn st Ci Qi Fi Bi Mi =
  nb_assn (neighb_coll st) Ci * queue_assn (heap st) Qi * forest_assn (forest st) Fi *
  ben.map_assn (best_even_neighbour st) Bi * missed.map_assn (missed st) Mi"

text \<open>After the loop, the queue is not needed any more; its contents are arbitrary.\<close>

definition "loop_post st Ci Qi Fi Bi Mi =
  nb_assn (neighb_coll st) Ci * (\<exists>\<^sub>AH. queue_assn H Qi) * forest_assn (forest st) Fi *
  ben.map_assn (best_even_neighbour st) Bi * missed.map_assn (missed st) Mi"

definition "res_rel res av st xs =
  (case augpath st of
     None \<Rightarrow> res = Imp_Unbounded
   | Some p \<Rightarrow> (\<exists>k. res = Imp_Path k \<and> k \<le> length xs \<and> take k xs = p) \<and> h av = acc st)"

lemma take_path_array:
  "\<lbrakk>0 < length xs; k' = 1 + length p\<rbrakk> \<Longrightarrow>
   take k' (take 1 (xs[0 := r]) @ p @ drop k' (xs[0 := r])) = r # p"
  by (cases xs) auto

lemma length_path_array:
  "\<lbrakk>k' = 1 + length p; k' \<le> length xs\<rbrakk> \<Longrightarrow>
   length (take 1 (xs[0 := r]) @ p @ drop k' (xs[0 := r])) = length xs"
  by (cases xs) auto

lemma loop_imp_rule:
  assumes "search_invars state" "card (L \<union> R) \<le> length xs"
  shows "<loop_assn state Ci Qi Fi Bi Mi * pot.map_assn initial_pot Pti * buddy_assn Bdi *
          Ra \<mapsto>\<^sub>a xs>
         code.loop_imp Ci Qi Pti Bdi Ra Fi Bi Mi
         <\<lambda>(res, av, Fi', Bi', Mi'). \<exists>\<^sub>Axs'.
            loop_post (search_path_loop state) Ci Qi Fi' Bi' Mi' *
            pot.map_assn initial_pot Pti * buddy_assn Bdi * Ra \<mapsto>\<^sub>a xs' *
            \<up>(length xs' = length xs \<and> res_rel res av (search_path_loop state) xs')>"
proof-
  have "search_invars state \<longrightarrow> (\<forall>Fi Bi Mi xs. card (L \<union> R) \<le> length xs \<longrightarrow>
         <loop_assn state Ci Qi Fi Bi Mi * pot.map_assn initial_pot Pti * buddy_assn Bdi *
          Ra \<mapsto>\<^sub>a xs>
         code.loop_imp Ci Qi Pti Bdi Ra Fi Bi Mi
         <\<lambda>(res, av, Fi', Bi', Mi'). \<exists>\<^sub>Axs'.
            loop_post (search_path_loop state) Ci Qi Fi' Bi' Mi' *
            pot.map_assn initial_pot Pti * buddy_assn Bdi * Ra \<mapsto>\<^sub>a xs' *
            \<up>(length xs' = length xs \<and> res_rel res av (search_path_loop state) xs')>)"
  proof(induction rule: search_path_loop_induct[OF search_invars_dom[OF assms(1)]])
    case (1 state)
    show ?case
    proof(intro impI allI)
      fix Fi Bi Mi and xs :: "'v list"
      assume inv: "search_invars state" and len: "card (L \<union> R) \<le> length xs"
      have I: "invar_basic state" "invar_best_even_neighbour_heap state"
              "invar_best_even_neighbour_map state"
        using inv by (auto simp: search_invars_def)
      have hinv: "heap_invar (heap state)" using I(1) by (auto elim: invar_basicE)
      obtain queue0 hm where ext: "heap_extract_min (heap state) = (queue0, hm)"
        by (cases "heap_extract_min (heap state)") auto
      show "<loop_assn state Ci Qi Fi Bi Mi * pot.map_assn initial_pot Pti * buddy_assn Bdi *
             Ra \<mapsto>\<^sub>a xs>
            code.loop_imp Ci Qi Pti Bdi Ra Fi Bi Mi
            <\<lambda>(res, av, Fi', Bi', Mi'). \<exists>\<^sub>Axs'.
               loop_post (search_path_loop state) Ci Qi Fi' Bi' Mi' *
               pot.map_assn initial_pot Pti * buddy_assn Bdi * Ra \<mapsto>\<^sub>a xs' *
               \<up>(length xs' = length xs \<and> res_rel res av (search_path_loop state) xs')>"
      proof(cases hm)
        case None
        have fail: "search_path_loop_fail_cond state"
          by (simp add: search_path_loop_fail_cond_def ext None)
        have sp: "search_path_loop state = state\<lparr>augpath := None\<rparr>"
          by (simp add: search_path_loop_simps(1)[OF fail] search_path_loop_fail_upd_def)
        show ?thesis
          apply(subst code.loop_imp.simps)
          by (sep_auto heap: queue.queue_extract_min_rule
                       simp: hinv ext None sp loop_assn_def loop_post_def res_rel_def)
      next
        case (Some r)
        note ext' = ext[unfolded Some]
        note F = extract_facts[OF I ext']
        define l where "l = the (ben_lookup (best_even_neighbour state) r)"
        have bl: "ben_lookup (best_even_neighbour state) r = Some l" using F(1) by (simp add: l_def)
        have key: "\<And>k. (r, k) \<in> heap_abstract (heap state) \<Longrightarrow>
                         k = w\<^sub>\<pi>_code l r + missed_at state l"
          using extract_key[OF inv ext'] by (simp add: l_def)
        have ext_rule: "<queue_assn (heap state) Qi> queue_extract_min_imp Qi
                        <\<lambda>x. \<exists>\<^sub>Ak. queue_assn queue0 Qi *
                             \<up>(x = Some (r, k) \<and> h k = w\<^sub>\<pi>_code l r + missed_at state l)>"
          apply(rule ht_cons_post[OF queue.queue_extract_min_rule[OF hinv]])
          subgoal for x
            using key by (cases x) (sep_auto simp: ext')+
          done
        show ?thesis
        proof(cases "buddy r")
          case None
          note bud = None
          have succ: "search_path_loop_succ_cond state"
            by (simp add: search_path_loop_succ_cond_def ext' bud)
          have sp: "search_path_loop state =
                    state\<lparr>acc := w\<^sub>\<pi>_code l r + missed_at state l,
                          augpath := Some (r # get_path (forest state) l)\<rparr>"
            by (simp add: search_path_loop_simps(2)[OF succ] search_path_loop_succ_upd_def
                          ext' l_def Let_def)
          have plen: "Suc (length (get_path (forest state) l)) \<le> length xs"
            using succ_path_length[OF I ext'] len by (simp add: l_def)
          hence xsne: "xs \<noteq> []" by auto
          note gp = forest.get_path_rule[OF F(8) F(2)[folded l_def], of "Suc 0"]
          show ?thesis
            apply(subst code.loop_imp.simps)
            apply(sep_auto heap: ext_rule simp: loop_assn_def)
            apply(all \<open>clarsimp simp: bl bud xsne\<close>)
            apply(sep_auto heap: gp simp: bud xsne plen)
            subgoal for k a b
              apply(erule entailsD[rotated])
              apply(rule ent_ex_postI[where x = "[r] @ get_path (forest state) l @
                            drop (Suc (length (get_path (forest state) l))) xs"])
              using xsne plen
              by (sep_auto simp: sp loop_post_def res_rel_def neq_Nil_conv)
            subgoal using bud by simp
            done
        next
          case (Some l')
          note bud = Some
          have cont: "search_path_loop_cont_cond state"
            by (simp add: search_path_loop_cont_cond_def ext' bud)
          have J: "invar_feasible_potential state" "invar_forest_tight state"
                  "invar_matching_tight state" "invar_out_of_heap state"
            using inv by (auto simp: search_invars_def)
          define acc' where "acc' = w\<^sub>\<pi>_code l r + missed_at state l"
          define missed' where "missed' = missed_upd l' acc' (missed_upd r acc' (missed state))"
          define U where "U = update_best_even_neighbour (abstract_real_map (missed_lookup missed'))
                                (neighb_coll state) (best_even_neighbour state) queue0 l'"
          note CF = cont_step_facts[OF cont I(1) J(1,2,3) I(2,3) J(4) ext' bud,
                                    folded l_def, folded acc'_def, folded missed'_def]
          have cu: "search_path_loop_cont_upd state =
                    state \<lparr> forest := extend_forest_even_unclassified (forest state) l r l',
                            best_even_neighbour := fst (snd U), neighb_coll := fst U,
                            heap := snd (snd U), missed := missed', acc := acc' \<rparr>"
            using cont_upd_eq[OF ext' bud] by (simp add: U_def missed'_def acc'_def l_def)
          have sp: "search_path_loop state = search_path_loop (search_path_loop_cont_upd state)"
            using search_path_loop_simps(3)[OF 1(1) cont] .
          have inv': "search_invars (search_path_loop_cont_upd state)"
            using search_invars_step[OF cont inv] .
          note IH = 1(2)[OF cont, rule_format, OF inv' len, unfolded loop_assn_def cu, simplified]
          have nbI: "rnb_invar (neighb_coll state)"
                    "rnb_abstract (neighb_coll state) = rnb_abstract rnb_init"
            using I(1) by (auto elim!: invar_basicE)
          note ubi = update_ben_imp_rule[OF nbI(1) CF(4) nbI(2) CF(6), folded U_def]
          note fe = forest.forest_extend_rule[OF CF(5)]
          show ?thesis
            apply(subst code.loop_imp.simps)
            apply(sep_auto heap: ext_rule simp: loop_assn_def)
            apply(all \<open>clarsimp simp: bl bud\<close>)
            supply forest.forest_extend_rule[sep_heap_rules del]
            apply(sep_auto heap: missed.map_assn_update_rule fe
                                 ubi[unfolded missed'_def acc'_def]
                                 IH[unfolded missed'_def acc'_def]
                           simp: bud sp cu[unfolded missed'_def acc'_def])
            done
        qed
      qed
    qed
  qed
  thus ?thesis using assms by blast
qed

subsection \<open>The New Potential\<close>

definition "pot_pre v p = (potential_invar p \<and> potential_lookup p v = potential_lookup initial_pot v)"

lemma foldl_pot_upd:
  "potential_invar p \<Longrightarrow>
   potential_invar (foldl (\<lambda>p v. potential_upd v (f v) p) p xs) \<and>
   (\<forall>w. w \<notin> set xs \<longrightarrow>
        potential_lookup (foldl (\<lambda>p v. potential_upd v (f v) p) p xs) w = potential_lookup p w)"
  by (induction xs arbitrary: p) (auto simp: potential(2,3))

lemma fold_pre_pot:
  "\<lbrakk>distinct xs; potential_invar p;
    \<forall>v\<in>set xs. potential_lookup p v = potential_lookup initial_pot v\<rbrakk> \<Longrightarrow>
   fold_pre pot_pre (\<lambda>p v. potential_upd v (f v) p) p xs"
  by (induction xs arbitrary: p) (auto simp: pot_pre_def potential(2,3))

lemma pot_step_even_rule:
  assumes "pot_pre v p" "h av = a"
  shows "<pot.map_assn p Pti * missed.map_assn M Mi> code.pot_step_even Mi av v Pti
         <\<lambda>Pti'. pot.map_assn (potential_upd v (\<pi> v + a - abstract_real_map (missed_lookup M) v) p)
                    Pti' * missed.map_assn M Mi>"
proof-
  have "abstract_real_map (potential_lookup p) v = \<pi> v"
    using assms(1) by (simp add: pot_pre_def abstract_real_map_def)
  thus ?thesis
    unfolding code.pot_step_even_def
    using assms by (sep_auto heap: pot.map_assn_update_rule simp: h_add)
qed

lemma pot_step_odd_rule:
  assumes "pot_pre v p" "h av = a"
  shows "<pot.map_assn p Pti * missed.map_assn M Mi> code.pot_step_odd Mi av v Pti
         <\<lambda>Pti'. pot.map_assn (potential_upd v (\<pi> v - a + abstract_real_map (missed_lookup M) v) p)
                    Pti' * missed.map_assn M Mi>"
proof-
  have "abstract_real_map (potential_lookup p) v = \<pi> v"
    using assms(1) by (simp add: pot_pre_def abstract_real_map_def)
  thus ?thesis
    unfolding code.pot_step_odd_def
    using assms by (sep_auto heap: pot.map_assn_update_rule simp: h_add)
qed

lemma new_pot_imp_rule:
  assumes "forest_invar \<M> (forest st)" "h av = acc st"
  shows "<forest_assn (forest st) Fi * missed.map_assn (missed st) Mi * pot.map_assn initial_pot Pti>
         code.new_pot_imp Fi Mi av Pti
         <\<lambda>Pti'. forest_assn (forest st) Fi * missed.map_assn (missed st) Mi *
                 pot.map_assn (new_potential st) Pti'>"
proof-
  define ge where "ge = (\<lambda>p v. potential_upd v (\<pi> v + acc st - missed_at st v) p)"
  define go where "go = (\<lambda>p v. potential_upd v (\<pi> v - acc st + missed_at st v) p)"
  have fin: "finite (aevens st)" "finite (aodds st)"
    using finite_forest(1,2)[OF assms(1)] by auto
  have vinv: "vset_invar (evens (forest st))" "vset_invar (odds (forest st))"
    using evens_and_odds(1,2)[OF assms(1)] by auto
  have disj: "aevens st \<inter> aodds st = {}" using evens_and_odds(4)[OF assms(1)] .
  have NP: "new_potential st = foldl go (foldl ge initial_pot (lst (aevens st))) (lst (aodds st))"
    by (simp add: new_potential_def vset_iterate_pot_lst[OF vinv(1)]
                  vset_iterate_pot_lst[OF vinv(2)] ge_def go_def)
  have pre1: "fold_pre pot_pre ge initial_pot (lst (aevens st))"
    unfolding ge_def
    by (rule fold_pre_pot) (auto simp: forest.lst_distinct[OF fin(1)] potential(1))
  note P1 = foldl_pot_upd[OF potential(1), of "\<lambda>v. \<pi> v + acc st - missed_at st v"
                            "lst (aevens st)", folded ge_def]
  have pre2: "fold_pre pot_pre go (foldl ge initial_pot (lst (aevens st))) (lst (aodds st))"
    unfolding go_def
    using P1 disj forest.lst_set[OF fin(1)] forest.lst_set[OF fin(2)]
    by (intro fold_pre_pot) (auto simp: forest.lst_distinct[OF fin(2)])
  have step1: "\<And>v p Pti. pot_pre v p \<Longrightarrow>
    <pot.map_assn p Pti * missed.map_assn (missed st) Mi> code.pot_step_even Mi av v Pti
    <\<lambda>Pti'. pot.map_assn (ge p v) Pti' * missed.map_assn (missed st) Mi>"
    unfolding ge_def using pot_step_even_rule[OF _ assms(2)] .
  have step2: "\<And>v p Pti. pot_pre v p \<Longrightarrow>
    <pot.map_assn p Pti * missed.map_assn (missed st) Mi> code.pot_step_odd Mi av v Pti
    <\<lambda>Pti'. pot.map_assn (go p v) Pti' * missed.map_assn (missed st) Mi>"
    unfolding go_def using pot_step_odd_rule[OF _ assms(2)] .
  note fold1 = iter_fold_rule_gen[where I = "forest_is_it (forest st) Fi Evens"
      and Q = "forest_assn (forest st) Fi"
      and A = "\<lambda>p Pti. pot.map_assn p Pti * missed.map_assn (missed st) Mi",
      OF forest.forest_it_has_next_rule forest.forest_it_next_rule forest.forest_quit_iteration
         step1 pre1]
  note fold2 = iter_fold_rule_gen[where I = "forest_is_it (forest st) Fi Odds"
      and Q = "forest_assn (forest st) Fi"
      and A = "\<lambda>p Pti. pot.map_assn p Pti * missed.map_assn (missed st) Mi",
      OF forest.forest_it_has_next_rule forest.forest_it_next_rule forest.forest_quit_iteration
         step2 pre2]
  show ?thesis
    unfolding code.new_pot_imp_def
    by (sep_auto heap: forest.forest_it_init_rule fold1 fold2 simp: NP)
qed

subsection \<open>The Path Search\<close>

lemma init_ok_foldl:
  "\<lbrakk>set xs \<subseteq> L; init_ok cbq\<rbrakk> \<Longrightarrow>
   init_ok (foldl (\<lambda>cbq l. update_best_even_neighbour (\<lambda>x. 0) (fst cbq) (fst (snd cbq))
                              (snd (snd cbq)) l) cbq xs)"
proof(induction xs arbitrary: cbq)
  case (Cons x xs)
  have "init_ok (update_best_even_neighbour (\<lambda>x. 0) (fst cbq) (fst (snd cbq)) (snd (snd cbq)) x)"
    using init_ok_step[OF Cons.prems(2), of x] Cons.prems(1) by simp
  from Cons.IH[OF _ this] Cons.prems(1) show ?case by simp
qed simp

lemma init_ok_initial: "init_ok init_best_even_neighbour"
proof-
  have "init_best_even_neighbour =
        foldl (\<lambda>cbq l. update_best_even_neighbour (\<lambda>x. 0) (fst cbq) (fst (snd cbq))
                          (snd (snd cbq)) l)
              (rnb_init, ben_empty, heap_empty) (filter (\<lambda>v. buddy v = None) (lst L))"
    using init_fold_result(2) by (simp add: init_fold)
  thus ?thesis
    using init_ok_foldl[OF _ init_ok_init, of "filter (\<lambda>v. buddy v = None) (lst L)"]
          forest.lst_set[OF finite_L]
    by auto
qed

lemma scratch_assnI:
  "\<lbrakk>rnb_invar C; rnb_abstract C = rnb_abstract rnb_init\<rbrakk> \<Longrightarrow>
   nb_assn C Ci * queue_assn H Qi * forest_assn F Fi * ben.map_assn B Bi * missed.map_assn M Mi
   \<Longrightarrow>\<^sub>A scratch_assn Ci Qi Fi Bi Mi"
  unfolding scratch_assn_def by (sep_auto simp: fun_eq_iff)

text \<open>The result of the imperative search, relative to the functional one.\<close>

definition "search_post Pti' res xs' = (case search_path of
     Lefts_Matched \<Rightarrow> \<up>(res = Imp_Matched) * pot.map_assn initial_pot Pti'
   | Dual_Unbounded \<Rightarrow> \<up>(res = Imp_Unbounded) * pot.map_assn initial_pot Pti'
   | Next_Iteration p \<pi>' \<Rightarrow> \<up>(\<exists>k. res = Imp_Path k \<and> k \<le> length xs' \<and> take k xs' = p) *
                           pot.map_assn \<pi>' Pti')"

theorem search_imp_rule:
  assumes len: "card (L \<union> R) \<le> length xs"
  shows "<scratch_assn Ci Qi Fi Bi Mi * left_is_set L Li * buddy_assn Bdi *
          pot.map_assn initial_pot Pti * Ra \<mapsto>\<^sub>a xs>
         code.search_imp Ci Qi Pti Bdi Li Ra Fi Bi Mi
         <\<lambda>(res, Pti', Fi', Bi', Mi'). \<exists>\<^sub>Axs'.
            scratch_assn Ci Qi Fi' Bi' Mi' * left_is_set L Li * buddy_assn Bdi *
            Ra \<mapsto>\<^sub>a xs' * \<up>(length xs' = length xs) * search_post Pti' res xs'>"
proof-
  have ok: "rnb_invar (fst init_best_even_neighbour)"
           "rnb_abstract (fst init_best_even_neighbour) = rnb_abstract rnb_init"
    using init_ok_initial by (auto simp: init_ok_def)
  show ?thesis
  proof(cases "vset_is_empty unmatched_lefts")
    case True
    have sp: "search_path = Lefts_Matched" by (simp add: search_path_def True)
    show ?thesis
      unfolding code.search_imp_def
      apply(sep_auto heap: clear_imp_rule init_imp_rule simp: True)
      using ok by (sep_auto simp: scratch_assn_def search_post_def sp fun_eq_iff)
  next
    case False
    have ne: "L - Vs \<M> \<noteq> {}"
      using False vset_is_empty[OF unmatched_lefts(2)] unmatched_lefts(1) by simp
    have inv0: "search_invars initial_state" using search_invars_init[OF ne] .
    have dom: "search_path_loop_dom initial_state" using search_invars_dom[OF inv0] .
    define fin where "fin = search_path_loop initial_state"
    have basic: "invar_basic fin" using loop_final_basic[OF inv0] by (simp add: fin_def)
    have fb: "rnb_invar (neighb_coll fin)" "rnb_abstract (neighb_coll fin) = rnb_abstract rnb_init"
             "forest_invar \<M> (forest fin)"
      using basic by (auto elim!: invar_basicE)
    have spe: "search_path = (case augpath fin of None \<Rightarrow> Dual_Unbounded
                              | Some p \<Rightarrow> Next_Iteration p (new_potential fin))"
      unfolding fin_def
      by (simp add: search_path_def False search_path_loop_impl_same[OF dom] Let_def)
    have fields: "neighb_coll initial_state = fst init_best_even_neighbour"
                 "heap initial_state = snd (snd init_best_even_neighbour)"
                 "forest initial_state = empty_forest forest_roots"
                 "best_even_neighbour initial_state = fst (snd init_best_even_neighbour)"
                 "missed initial_state = missed_empty"
      by (simp_all add: initial_state_def)
    note lp = loop_imp_rule[OF inv0 len, unfolded loop_assn_def fields, folded fin_def]
    show ?thesis
    proof(cases "augpath fin")
      case None
      show ?thesis
        unfolding code.search_imp_def
        apply(sep_auto heap: clear_imp_rule init_imp_rule lp simp: False)
        apply(all \<open>clarsimp simp: None res_rel_def False\<close>)
        using fb(1,2)
        by (sep_auto simp: loop_post_def scratch_assn_def search_post_def spe None fun_eq_iff)
    next
      case (Some p)
      note np = new_pot_imp_rule[OF fb(3)]
      show ?thesis
        unfolding code.search_imp_def
        apply(sep_auto heap: clear_imp_rule init_imp_rule lp simp: False)
        apply(all \<open>clarsimp simp: Some res_rel_def False\<close>)
        using fb(1,2)
        by (sep_auto heap: np simp: loop_post_def scratch_assn_def search_post_def spe Some
                                    fun_eq_iff)
    qed
  qed
qed

end
end
