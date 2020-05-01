*****************************************
cs1950y_final_project: PageRank Algorithm
*****************************************

*********
0. Files:
*********

README				- This file
pagerank-tests.rkt	- Implementation of PageRank Algorithm (naive version and full version)


***********
1. Overview
***********

Our implementation models the PageRank Algorithm, including
	- Basic PageRank Algorithm
	- Real PageRank Algorithm
	- Testings


****************
2. Design Choice
****************

Structure:
1) Sigs
	- Page: each of webpage / each node of graph
	- State: states of graph in each iteration
	- Event: transition between two states (pre state and post state)
2) Fields
	- pageRank = Page->Int: a relation from Page to Int (each page has its rank)
	- link = Page->Page: set of edges between pages (directed)

______________________________________________________


Setup:
- Initial State
	- each page has rank = 10 (so, total rank = 10 * #page)
	- there should be at least one link
- Final State
	- needs to have the same graph as initial

______________________________________________________


<<<<< Basic / Naive Version >>>>>

Algorithm:
	- links will be the same between states
	- pages will be the same between states
	- At every iteration,
		- each page split its rank evenly among its outgoing edges
		- each page receives ranks from all its incoming edges

______________________________________________________


<<<<< Real Version >>>>>

Algorithm:
	- links will be the same between states
	- pages will be the same between states
	- At every iteration,
		- Let d (damping factor) = 0.8
		- each page gives a d fraction of its rank to its outgoing edges (evenly)
		- each page gives a 1-d fraction of its rank to all pages (evenly)
		- each page receives ranks from all its incoming edges and from 1-d fraction
		- handling sinks

______________________________________________________


<<<<< Testing >>>>>
1) Check if it is possible to have a page with zero rank
2) Check if it is possible to have a page with all rank
3) Check if page p having rank zero at state = s implies p having rank zero again in the next state s'
4) Sink handling


*************
3. Known Bugs
*************

- No known bugs


********************************************************************