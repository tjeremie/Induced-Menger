(* ::Package:: *)

(* ::Title:: *)
(*Testing the existence of two non-adjacent paths*)


(* ::Subtitle:: *)
(*Code used in the paper "On an induced version of Menger's theorem" by Kevin Hendrey, Sergey Norin, Raphael Steiner and J\[EAcute]r\[EAcute]mie Turcotte*)
(**)
(*This short script verifies that the example provided in the paper of a subcubic graph with four X-Y paths does not contain a pair of non-adjacent X-Y paths.*)


(* ::Input::Initialization:: *)
(* We first define the graph *)
vertexList={{1,0},{1,1},{1,3},{1,4},{1,6},{1,9},{1,10},{1,12},{1,15},{1,17},{2,0},{2,1},{2,5},{2,6},{2,8},{2,11},{2,12},{2,14},{2,16},{2,17},{3,0},{3,2},{3,3},{3,5},{3,7},{3,10},{3,11},{3,13},{3,16},{3,17},{4,0},{4,2},{4,4},{4,7},{4,8},{4,9},{4,13},{4,14},{4,15},{4,17}};
edgeList={{1,0}\[UndirectedEdge]{1,1},{1,1}\[UndirectedEdge]{1,3},{1,3}\[UndirectedEdge]{1,4},{1,4}\[UndirectedEdge]{1,6},{1,6}\[UndirectedEdge]{1,9},{1,9}\[UndirectedEdge]{1,10},{1,10}\[UndirectedEdge]{1,12},{1,12}\[UndirectedEdge]{1,15},{1,15}\[UndirectedEdge]{1,17},{2,0}\[UndirectedEdge]{2,1},{2,1}\[UndirectedEdge]{2,5},{2,5}\[UndirectedEdge]{2,6},{2,6}\[UndirectedEdge]{2,8},{2,8}\[UndirectedEdge]{2,11},{2,11}\[UndirectedEdge]{2,12},{2,12}\[UndirectedEdge]{2,14},{2,14}\[UndirectedEdge]{2,16},{2,16}\[UndirectedEdge]{2,17},{3,0}\[UndirectedEdge]{3,2},{3,2}\[UndirectedEdge]{3,3},{3,3}\[UndirectedEdge]{3,5},{3,5}\[UndirectedEdge]{3,7},{3,7}\[UndirectedEdge]{3,10},{3,10}\[UndirectedEdge]{3,11},{3,11}\[UndirectedEdge]{3,13},{3,13}\[UndirectedEdge]{3,16},{3,16}\[UndirectedEdge]{3,17},{4,0}\[UndirectedEdge]{4,2},{4,2}\[UndirectedEdge]{4,4},{4,4}\[UndirectedEdge]{4,7},{4,7}\[UndirectedEdge]{4,8},{4,8}\[UndirectedEdge]{4,9},{4,9}\[UndirectedEdge]{4,13},{4,13}\[UndirectedEdge]{4,14},{4,14}\[UndirectedEdge]{4,15},{4,15}\[UndirectedEdge]{4,17},{1,1}\[UndirectedEdge]{2,1},{3,2}\[UndirectedEdge]{4,2},{1,3}\[UndirectedEdge]{3,3},{1,4}\[UndirectedEdge]{4,4},{2,5}\[UndirectedEdge]{3,5},{1,6}\[UndirectedEdge]{2,6},{3,7}\[UndirectedEdge]{4,7},{2,8}\[UndirectedEdge]{4,8},{1,9}\[UndirectedEdge]{4,9},{1,10}\[UndirectedEdge]{3,10},{2,11}\[UndirectedEdge]{3,11},{1,12}\[UndirectedEdge]{2,12},{3,13}\[UndirectedEdge]{4,13},{2,14}\[UndirectedEdge]{4,14},{1,15}\[UndirectedEdge]{4,15},{2,16}\[UndirectedEdge]{3,16}};
g=Graph[vertexList,edgeList,VertexCoordinates->(#->Reverse[#*{-1,1}]&/@vertexList)]
x={{1,0},{2,0},{3,0},{4,0}};
y={{1,17},{2,17},{3,17},{4,17}};


(* ::Input::Initialization:: *)
(* We compute the list of X-Y paths *)
pathList=Flatten[Table[#&/@FindPath[g,vx,vy,Infinity,All],{vx,x},{vy,y}],2]


(* ::Input::Initialization:: *)
(* We test whether there exist two non-adjacent X-Y paths by testing for each path found above whether removing the vertices in this path and their neighbours from the graph leaves the remaining vertices of X and Y in the same connected component *)

removeVertices[g_,vList_]:=Subgraph[g,Complement[VertexList[g],vList]] (* Given a graph g and a list of vertices vList, returns the induced subgraph of g obtained by removing the vertices in vList *)

jointNeighbourhood[g_,vList_]:=DeleteDuplicates[Join[vList,Flatten[AdjacencyList[g,#]&/@vList,1]]]
(* Given a graph g and a list of vertices vList, returns the list of vertices which appear either in vList or are adjacent to some vertex in vList *)

deleteJointNeighbourhood[g_,path_]:=removeVertices[g,jointNeighbourhood[g,path]]
(* Given a graph g and a list of vertices vList, returns the induced subgraph of g obtained by removing the vertices in or adjacent to vList *)

connectedVertices[g_,{v1_,v2_}]:=v1==v2 ||FindPath[g,v1,v2]!={}
(* Given a graph g and vertices v1 and v2, returns True if and only if there exists at least one path between v1 and v2 *)

connectedSets[g_,vList1_,vList2_]:=AnyTrue[Tuples[{Intersection[vList1,VertexList[g]],Intersection[vList2,VertexList[g]]}],connectedVertices[g,#]&]
(* Given a graph g and lists of vertices vList1 and vList2 (not necessarily all in g, we will restrict to those in g), returns True if and only if there exists at least one path with one end in vList1 and one end in vList2 *)

AnyTrue[pathList,connectedSets[deleteJointNeighbourhood[g,#],x,y]&]
(* Main computation, returns True if and only if a pair of non-adjacent X-Y paths exists in our graph *)
