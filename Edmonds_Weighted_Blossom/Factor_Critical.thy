theory Factor_Critical
  imports Basic_Matching.Matching
begin

definition "factor_critical_subgraph G X = 
   (\<forall> x \<in> X. \<exists> M. graph_matching (G\<lbrakk>X\<rbrakk>) M \<and> Vs M = X - {x})"

end