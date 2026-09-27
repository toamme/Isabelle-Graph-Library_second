theory Fixed_Univ_Map_Specs_Imp
  imports Separation_Logic_Imperative_HOL_Partial.Sep_Main Fixed_Univ_Map_Specs
begin

locale fixed_univ_map_imp =
  fixed_univ_map where K = K
    and fixed_univ_map_invar = fixed_univ_map_invar
    and fixed_univ_map_upd = fixed_univ_map_upd
    and fixed_univ_map_lookup = fixed_univ_map_lookup
  for K :: "'a set"
    and fixed_univ_map_invar :: "'array \<Rightarrow> bool"
    and fixed_univ_map_upd :: "'array \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'array"
    and fixed_univ_map_lookup :: "'array \<Rightarrow> 'a \<Rightarrow> 'b" +
  fixes fixed_univ_map_val :: "'bi::heap \<Rightarrow> 'b"
    and fixed_univ_map_assn :: "'array \<Rightarrow> 'arrayi \<Rightarrow> assn"
    and fixed_univ_map_upd_imp :: "'arrayi \<Rightarrow> 'a \<Rightarrow> 'bi \<Rightarrow> unit Heap"
    and fixed_univ_map_lookup_imp :: "'arrayi \<Rightarrow> 'a \<Rightarrow> 'bi Heap"
  assumes fixed_univ_map_lookup_rule[sep_heap_rules]:
      "\<lbrakk>fixed_univ_map_invar A; k \<in> K\<rbrakk> \<Longrightarrow>
       <fixed_univ_map_assn A Ai> fixed_univ_map_lookup_imp Ai k
       <\<lambda>x. fixed_univ_map_assn A Ai * \<up>(fixed_univ_map_val x = fixed_univ_map_lookup A k)>"
    and fixed_univ_map_upd_rule[sep_heap_rules]:
      "\<lbrakk>fixed_univ_map_invar A; k \<in> K\<rbrakk> \<Longrightarrow>
       <fixed_univ_map_assn A Ai> fixed_univ_map_upd_imp Ai k v
       <\<lambda>_. fixed_univ_map_assn (fixed_univ_map_upd A k (fixed_univ_map_val v)) Ai>"

end