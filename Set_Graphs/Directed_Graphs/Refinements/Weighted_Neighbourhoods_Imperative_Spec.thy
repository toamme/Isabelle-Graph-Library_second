theory Weighted_Neighbourhoods_Imperative_Spec
  imports Data_Structures.Iterable_Set_Specs_Imp
          Separation_Logic_Imperative_HOL_Partial.Sep_Main
          Complex_Main
begin

section \<open>Imperative Collections of Weighted Neighbourhoods\<close>

text \<open>The functional collection of neighbourhoods with cursors, @{locale indexed_iterable_set},
      is extended by a representation assertion @{term nb_assn} and one in-place operation per
      functional operation. The algorithms that use such a collection read the weights of the
      edges through a separate weight function @{term cost}. Imperatively, the weights are only
      available \<^emph>\<open>at the cursor\<close>: @{term current_cost_imp} returns the weight of the edge from the
      index @{term i} to its current element, as an executable value that @{term wval} maps to the
      functional weight. How this weight is found is not visible to the user of the collection
      (in a CSR representation, it is stored next to the current element).

      @{term reset_all_imp} resets all cursors at once, in place, bringing the collection back to
      its initial state @{term nb_init}.\<close>

locale weighted_neighbourhoods_imp_spec =
  indexed_iterable_set idx_invar idx_abstract idx_current idx_has idx_iterated idx_remaining
      idx_move idx_reset K
  for idx_invar :: "'coll \<Rightarrow> bool"
    and idx_abstract :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a set"
    and idx_current :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a"
    and idx_has :: "'coll \<Rightarrow> 'i \<Rightarrow> bool"
    and idx_iterated :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a set"
    and idx_remaining :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a set"
    and idx_move :: "'coll \<Rightarrow> 'i \<Rightarrow> 'coll"
    and idx_reset :: "'coll \<Rightarrow> 'i \<Rightarrow> 'coll"
    and K :: "'i set" +
  fixes cost :: "'i \<Rightarrow> 'a \<Rightarrow> real"
    and wval :: "'w \<Rightarrow> real"
    and nb_init :: "'coll"
    and nb_assn :: "'coll \<Rightarrow> 'colli \<Rightarrow> assn"
    and has_imp :: "'colli \<Rightarrow> 'i \<Rightarrow> bool Heap"
    and current_imp :: "'colli \<Rightarrow> 'i \<Rightarrow> 'a Heap"
    and current_cost_imp :: "'colli \<Rightarrow> 'i \<Rightarrow> 'w Heap"
    and move_imp :: "'colli \<Rightarrow> 'i \<Rightarrow> unit Heap"
    and reset_imp :: "'colli \<Rightarrow> 'i \<Rightarrow> unit Heap"
    and reset_all_imp :: "'colli \<Rightarrow> unit Heap"
  assumes nb_init_invar: "idx_invar nb_init"
    and has_rule[sep_heap_rules]:
      "\<lbrakk>idx_invar C; i \<in> K\<rbrakk> \<Longrightarrow>
       <nb_assn C Ci> has_imp Ci i <\<lambda>r. nb_assn C Ci * \<up>(r = idx_has C i)>"
    and current_rule[sep_heap_rules]:
      "\<lbrakk>idx_invar C; i \<in> K; idx_remaining C i \<noteq> {}\<rbrakk> \<Longrightarrow>
       <nb_assn C Ci> current_imp Ci i <\<lambda>x. nb_assn C Ci * \<up>(x = idx_current C i)>"
    and current_cost_rule[sep_heap_rules]:
      "\<lbrakk>idx_invar C; i \<in> K; idx_remaining C i \<noteq> {}\<rbrakk> \<Longrightarrow>
       <nb_assn C Ci> current_cost_imp Ci i
       <\<lambda>c. nb_assn C Ci * \<up>(wval c = cost i (idx_current C i))>"
    and move_rule[sep_heap_rules]:
      "\<lbrakk>idx_invar C; i \<in> K; idx_remaining C i \<noteq> {}\<rbrakk> \<Longrightarrow>
       <nb_assn C Ci> move_imp Ci i <\<lambda>_. nb_assn (idx_move C i) Ci>"
    and reset_rule[sep_heap_rules]:
      "\<lbrakk>idx_invar C; i \<in> K\<rbrakk> \<Longrightarrow>
       <nb_assn C Ci> reset_imp Ci i <\<lambda>_. nb_assn (idx_reset C i) Ci>"
    and reset_all_rule[sep_heap_rules]:
      "\<lbrakk>idx_invar C; \<forall>i\<in>K. idx_abstract C i = idx_abstract nb_init i\<rbrakk> \<Longrightarrow>
       <nb_assn C Ci> reset_all_imp Ci <\<lambda>_. nb_assn nb_init Ci>"

end
