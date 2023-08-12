(* ::Package:: *)

(* ::Title:: *)
(*Proving the existence of two non-adjacent paths*)


(* ::Subtitle:: *)
(*Code used in the paper "An induced version of Menger's theorem" by Kevin Hendrey, Sergey Norin, Raphael Steiner and J\[EAcute]r\[EAcute]mie Turcotte*)
(**)
(*As part of the proof that given a (close to) subcubic graph with 5 X-Y paths, there exists a pair of non-adjacent X-Y paths, this script shows that there is a reachable state for every path system.*)


(* ::Section:: *)
(*Preparatory functions*)


(* ::Subsection:: *)
(*Basic definitions*)


(* ::Input::Initialization:: *)
pathCount=5;
(* The number of paths *)

pathList=Range[pathCount];
(* We will always label the paths 1,...,pathCount *)


(* ::Input::Initialization:: *)
edgeList={#,"Edge"}&/@Subsets[pathList,{2}];
(* The list of edges we can append to a path system (\mathcal E), the indices are always in growing order *)

cycleList={#,"Cycle"}&/@DeleteDuplicatesBy[Flatten[Permutations/@Subsets[pathList,{2,Infinity}],1],Cycles[{#}]&];
(* The list of cycles we can append to a path system (\mathcal C), for each cycle one way of writing it is chosen *)

edgeAndCycleList=Join[edgeList,cycleList];
(* For convenience, we will work with the union of these lists, each edge or cycle has a labelled attached to it *)


(* ::Input::Initialization:: *)
stateList=Select[Subsets[Subsets[pathList,{1,4}],{2}],Intersection[#[[1]],#[[2]]]=={}&];
(* The list of states *)

convertStateToIndex[state_]:=FirstPosition[stateList,state][[1]]
(* Given a state, returns the index of this state in stateList *)


(* ::Input::Initialization:: *)
startStatesIndices=convertStateToIndex/@Select[Subsets[Subsets[pathList,{1,1}],{2}],Intersection[#[[1]],#[[2]]]=={}&];
(* The list of indices of initial states (\mathcal S_0) *)


(* ::Subsection:: *)
(*Computing f*)


(* ::Subsubsection:: *)
(*Defining the graph H_m*)


(* ::Input::Initialization:: *)
(* We define H_m, A_m and B_m from the path system \mathcal H_m =\mathcal H_0 \[CirclePlus] m 

We will write the vertices which start the paths (written b_i in the definition of \[CirclePlus]) as {1,i},and those which are added and end the paths (written b_i' in the definition of \[CirclePlus]) as {2,i}. In the case of cycles, the middle vertices (written c_i in the definition of \[CirclePlus]) will be denoted by {3/2,i}. Note that this notation also allows a direct embedding, every vertex having itself as coordinates.
*)

am={1,#}&/@pathList;
(* The vertices in A_m, does not depend on the operation *)

bm[m_]:=Join[{2,#}&/@m[[1]],{1,#}&/@Complement[pathList,m[[1]]]]
(* The vertices in B_m, depends on which edge or cycle m is appended *)

bmNotam[m_]:=Complement[bm[m],am]
(* The vertices in B_m\A_m, depends on which edge or cycle m is appended *)

hm[{{i1_,i2_},"Edge"}]:=Graph[
Join[am,bmNotam[{{i1,i2},"Edge"}]],
(* Vertices *)
{UndirectedEdge[{1,i1},{2,i1}],UndirectedEdge[{1,i2},{2,i2}],UndirectedEdge[{2,i1},{2,i2}]}, (* Edges *)
VertexCoordinates->Join[am,bmNotam[{{i1,i2},"Edge"}]] (* Coordinates for embedding*)
]
(* The version of H_m for appending an edge *)

hm[{cycle_,"Cycle"}]:=Graph[
Join[am,bmNotam[{cycle,"Cycle"}],Table[{3/2,i},{i,cycle}]],(* Vertices *)
Flatten[Table[{UndirectedEdge[{1,cycle[[i]]},{3/2,cycle[[i]]}],UndirectedEdge[{3/2,cycle[[i]]},{2,cycle[[i]]}],UndirectedEdge[{3/2,cycle[[i]]},{2,cycle[[Mod[i+1,Length[cycle],1]]]}]},{i,Length[cycle]}]], (* Edges *)
VertexCoordinates->Join[am,bmNotam[{cycle,"Cycle"}],Table[{3/2,i},{i,cycle}]] (* Coordinates for embedding*)
]
(* The version of H_m for appending a cycle *)


(* ::Subsubsection:: *)
(*Generating all possible sets C_1,C_2*)


(* ::Input::Initialization:: *)
twoDisjointSubsets[list_]:=Select[Tuples[Subsets[list],{2}],!IntersectingQ[#[[1]],#[[2]]]&]
(* Given a list list, returns a list of all (ordered) pairs of disjoint subsets *)

possibleConfigurations[{s1_,s2_},m_]:={Join[{1,#}&/@s1,#[[1]]],Join[{1,#}&/@s2,#[[2]]]}&/@
twoDisjointSubsets[Complement[VertexList[hm[m]],am]]
(* Given a state (s1,s2) and an edge or cycle m, returns all possible pairs of disjoint subsets of V(H_m) C_1,C_2 such that the second condition, regarding the intersections with A, is respected. In other words, the intersections with A is fixed, but for the remainder of the sets we impose no conditions other than disjointness. *)


(* ::Subsubsection:: *)
(*Testing non-adjacent sets*)


(* ::Input::Initialization:: *)
jointNeighbourhood[g_,vList_]:=DeleteDuplicates[Join[vList,Flatten[AdjacencyList[g,#]&/@vList,1]]]
(* Given a graph g and a list of vertices vList, returns the list of vertices which appear either in vList or are adjacent to some vertex in vList *)

nonAdjacentSets[g_,{vList1_,vList2_}]:=!IntersectingQ[jointNeighbourhood[g,vList1],vList2]&&!IntersectingQ[jointNeighbourhood[g,vList2],vList1]
(* Given a graph g and a pair of lists of vertices vList1,vList2, returns True if and only if vList1 and vList2 are (disjoint and) non-adjacent in g *)


(* ::Subsubsection:: *)
(*Testing for connectivity condition*)


(* ::Input::Initialization:: *)
connectedToA[m_,vList_]:=AllTrue[Intersection[vList,bm[m]],IntersectingQ[VertexComponent[Subgraph[hm[m],vList],{#}],am]&]
(* Given an edge or a cycle m and a list of vertices vList of H_m, returns True if and only if for every vertex in vList \[Intersection] B_m, its component in H[vlist] contains a vertex of A_m *)


(* ::Subsubsection:: *)
(*Defining f*)


(* ::Input::Initialization:: *)
selectedConfigurations[s_,m_]:=
Select[possibleConfigurations[s,m] ,(* Only sets respecting the second condition are proposed *)

nonAdjacentSets[hm[m],#]&&
(* Test for the first condition *)

connectedToA[m,#[[1]]]
&&connectedToA[m,#[[2]]]&&
(* Tests for the fourth condition *)

IntersectingQ[#[[1]],bm[m]]&&IntersectingQ[#[[2]],bm[m]]
(* In order to yield a valid state (both parts must be non-empty), both C_1 and C_2 must intersect B *)
&
]
(* Given a state s and an edge or cycle m, returns the pairs C_1,C_2 which respect the first, third and fourth conditions as specified in the proof of the claim. *)

f[stateIndex_,mIndex_]:=
Union[convertStateToIndex/@
(* This converts the states into their indices in stateList, and we sort these and remove duplicates *)
Map[Sort,
(* We sort the values inside each part of the states, as well as the order of the two parts in the state, to use the same form as in stateList *)
Map[Transpose[Intersection[#,bm[edgeAndCycleList[[mIndex]]]]][[2]]&,
(* To extract the possible states from the possible configurations, we first take the intersection of these with B_m, and then keep only the labelling of the path numbers *)

selectedConfigurations[stateList[[stateIndex]],edgeAndCycleList[[mIndex]]]
,{2}]
,{1,2}]
]
(* Given the index in stateList of a state s and the index in edgeAndCycleList of an edge or cycle m, returns the indices of states in f(s,m). We proceed by computing the possible configurations (sets C_1,C_2) as above, and the state is then exactly the indices of the paths in which these intersect B_m (hence the third condition holds). *)


(* ::Subsection:: *)
(*Defining g*)


(* ::Input::Initialization:: *)
g[collectionStateIndices_,mIndex_]:=Union@@(f[#,mIndex]&/@collectionStateIndices)
(* Given a collection of indices in stateList of states S and the index in edgeAndCycleList of an edge or cycle m, returns the indices of states in f(S,m) *)


(* ::Subsection:: *)
(*Time improvements using permutations*)


(* ::Input::Initialization:: *)
permutationList=AssociationThread[pathList,#]&/@Permutations[pathList];
(* The list of permutations of the (indices of the) paths *)

reversePermutation[permutationIndex_]:=FirstPosition[permutationList,KeySort[Association[Reverse/@Normal[permutationList[[permutationIndex]]]]]][[1]]
(* Given the index in permutationList of a permutation, returns the index of the inverse permutation. KeySort ensures that the permutation is written in the same form as in permutationList. Permutation reversing code taken from https://mathematica.stackexchange.com/questions/284775/how-can-i-invert-the-association *)

replaceState[stateIndex_,permutationIndex_]:=replaceState[stateIndex,permutationIndex]=convertStateToIndex[Sort[Map[Sort,stateList[[stateIndex]]/.permutationList[[permutationIndex]]]]]
(* Returns the index of the state obtained by applying the permutation with index permutationIndex in permutationList to the state with index stateIndex. As earlier, we use sorting to ensure that the states are in the same format as in stateList before finding their indices. *)

canonicalCollectionStates[collectionStateIndices_]:=Sort[Table[Sort[replaceState[#,i]&/@collectionStateIndices],{i,1,Length[permutationList]}]][[1]]
(* Given a collection of indices in stateList of states S, considers all collections of states which can be obtained from S by applying a permutation, and chooses a canonical one using sorting. *)

equivalent[m1_,m2_]:=Cycles[{m1[[1]]}]==Cycles[{m2[[1]]}]&&m1[[2]]==m2[[2]]
(* Given two edges or cycles m1,m2, possibly not written in the same way as in edgeAndCycleList, returns True if and only if m1 and m2 represent the same edge or cycle *)

convertEdgeOrCycleToIndex[m_]:=FirstPosition[edgeAndCycleList,SelectFirst[edgeAndCycleList,equivalent[#,m]&]][[1]]
(* Given an edge or cycle m, possibly not written in the same way as in edgeAndCycleList, returns its index in edgeAndCycleList *)

replaceEdgeOrCycle[mIndex_,permutationIndex_]:=
convertEdgeOrCycleToIndex[edgeAndCycleList[[mIndex]]/.permutationList[[permutationIndex]]]
(* Returns the index in edgeAndCycleList of the edge or cycle obtained by applying the permutation with index permutationIndex to the edge or cycle with index mIndex *)


(* ::Subsection:: *)
(*Filtering out subsets*)


(* ::Input::Initialization:: *)
minimalSubsets[list_]:=DeleteDuplicates[SortBy[list,Length],Intersection[#1,#2]===Sort[#1]&]
(* Given a list of lists, keeps only those which are minimal (not containing any of the other lists), this version is from https://mathematica.stackexchange.com/questions/8154/how-to-select-minimal-subsets *)

minimalSubsets[list1_,list2_]:=Select[minimalSubsets[list1],Function[u,AllTrue[list2,Intersection[u,#]!=Sort[#]&]]]
(* Given two lists of lists list1 and list2, keeps only lists in list1 which are minimal and which also don't contain lists in list2 *)


(* ::Section:: *)
(*Main computation*)


(* ::Subsection:: *)
(*Preloading f*)


(* ::Input::Initialization:: *)
(* Given that computing f can be slow, we only wish to compute f once, which is what the below script does, as it saves the outputs of f. As noted in improvement (iii) in the paper, if \[Sigma] is a permutation of [5], then \[Sigma]^-1 f(\[Sigma]S,\[Sigma]m)=f(S,m). This can be used to greatly reduce the computation time by only running the underlying computation of f once for each equivalence class. However, if you wish to not use this reduction, change symmetryReduction to False. *)

symmetryReduction=True;

Do[
permIndex=SelectFirst[Range[Length[permutationList]],replaceState[stateIndex,#]<stateIndex||(replaceState[stateIndex,#]==stateIndex &&replaceEdgeOrCycle[mIndex,#]<mIndex)&];
(* The index of a permutation \[Sigma] such that f(\[Sigma]S,\[Sigma]m) has already been computed, using the order in which the Do runs. If no such permutation exists, this will be Missing["NotFound"]. *)

If[permIndex===Missing["NotFound"]||!symmetryReduction,

f[stateIndex,mIndex]=f[stateIndex,mIndex],
(* This computes f using its definition *)

f[stateIndex,mIndex]=Sort[replaceState[#,reversePermutation[permIndex]]&/@f[replaceState[stateIndex,permIndex],replaceEdgeOrCycle[mIndex,permIndex]]]
(* This computes f from already computed values using a permutation*)

]
,{stateIndex,Length[stateList]},{mIndex,Length[edgeAndCycleList]}]//AbsoluteTiming

(* Runs in 274.472 seconds on a 2020 MacBook Air with M1 chip and 16GB ram running Mathematica 13.0.0.0
We note that a less naive,but less legible implementation of the definition of f can bring this down to around 25 seconds, more information can be provided upon request. *)


(* ::Subsection:: *)
(*Main computation*)


(* ::Input::Initialization:: *)
AbsoluteTiming[
    processedList = {};
    (* Will contain the collections of states to which we have already applied g to *)

    toProcess ={startStatesIndices};
(* Will contain the collections of states to which we have not yet applied g to starts containing only \mathcal S_0 *)

found = False;
(* This variable will become True if the empty collection of states is ever found as the result of applying g (we want this to never happen, and so that found is still False at the end) *)

    While[
        toProcess != {},
              (* As long as we keep finding unseen collections 
        of states, we continue the process *)

        toProcess = First[Reap[
(* The new toProcess is obtained by collecting the applications of g (see below) to the previous states in toProcess (using Reap and Sow to collect these efficiently) *)

Do[
(* For every collection of states in toProcess and every edge and cycle in edgeAndCycleList, we compute g *)

                    newCollection = canonicalCollectionStates[g[currentCollectionStates, mIndex]];
(* We apply g, and then take an equivalent collection of states obtained by applying some permutation, which implements improvement (i) *)

                    If[newCollection != currentCollectionStates,
 (* We are only interested in collections of states which are new *)

                        Sow[newCollection];

                        If[newCollection == {},
                            found = True
                        ]
(* Changed found to true if we have found the empty collection of states *)
                    ];

                    ,{currentCollectionStates, toProcess},{mIndex, 1, Length[edgeAndCycleList]}];

                processedList = minimalSubsets[Join[processedList, toProcess]]
(* We append the now processed states to processedList, and remove non-minimal elements. This is compatible with (ii) since, when we remove elements in the new toProcess list which contain elements in processedList, we only need to test this for minimal elements. *)

][[2]], {}];

        toProcess = minimalSubsets[toProcess, processedList](* We remove non-minimal subsets in toProcess as well as those which contain elements in processedList as described in improvement (ii) in the paper *)
    ];

    found
]

(* Runs in 559.123642` seconds on a 2020 MacBook Air with M1 chip and 16GB ram running Mathematica 13.0.0.0 *)
