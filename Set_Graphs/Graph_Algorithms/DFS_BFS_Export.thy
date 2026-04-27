theory DFS_BFS_Export
  imports DFS_Imperative BFS_Refinement_Instantiation BFS_Example
begin

export_code
(*nat transforms*)
nat_of_integer integer_of_nat
(*iam for dfs*)
iam_dfs_imp iam_dfs_initial_state iam_graph_from_list
(*string hm for dfs*)
hm_dfs_imp hm_dfs_initial_state hm_graph_from_list 
(*integer hm for dfs*)
him_dfs_imp him_dfs_initial_state him_graph_from_list 
(*functional rbt for dfs*)
rbt_dfs_initial_state rbt_neighbourhood rbt_dfs_impl rbt_add_edge
rbt_from_list
(*dfs state*)
sstack sseen rreturn rreachable not_reachable
(*bfs iam*)
BFS_dag_iam BFS_check_reachable_iam
(*BFS rbt*) 
BFS_dag_rbt BFS_check_reachable_rbt build_rbt_sources

in SML_imp module_name exported file_prefix Unweighted_Graph_imperative



end