theory Dist_BFS
  imports BFS_2
begin

locale Dist_BFS = 
BFS where expand_tree = expand_tree for
expand_tree::"'adjmap \<Rightarrow> 'vset \<Rightarrow> 'vset \<Rightarrow> 'adjmap" +
fixes next_frontier_and_visited



