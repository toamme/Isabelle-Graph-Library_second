theory Fixed_Univ_Map_Specs
  imports Main
begin

locale fixed_univ_map =
fixes K::"'a set"
and fixed_univ_map_invar::"'array \<Rightarrow> bool"
and fixed_univ_map_upd::"'array \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'array"
and fixed_univ_map_lookup::"'array \<Rightarrow> 'a \<Rightarrow> 'b"
assumes fixed_univ_map_upd:
"\<And> A k v. 
 \<lbrakk>fixed_univ_map_invar A; k \<in> K\<rbrakk> \<Longrightarrow>
fixed_univ_map_lookup (fixed_univ_map_upd A k v) =
(fixed_univ_map_lookup A) (k := v)"
and fixed_univ_map_upd_invar:
"\<And> A k v. \<lbrakk>fixed_univ_map_invar A; k \<in> K\<rbrakk> 
\<Longrightarrow> fixed_univ_map_invar (fixed_univ_map_upd A k v)"

end