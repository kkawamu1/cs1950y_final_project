==Overview==:

Our implementation models the PageRank Algorithm, including - Basic PageRank Algorithm - Real PageRank Algorithm -Testings

==Design Choice==

--Structure--:
    Sigs: 
        Page: each of webpage / each node of graph
        State: states of graph in each iteration
        Event: transition between two states (pre state and post state)
    Fields:
        pageRank = Page->Int: a relation from Page to Int (each page has its rank)
        link = Page->Page: set of edges between pages (directed)

--Setup--
    Initial State: each page has rank = 10 (so, total rank = 10 * #page). for the full version, we enforce the graph to have no sink to emulate the sink handling.\

==Algorithm==

    Naive Algorithm: - Links will be the same between states. Pages will be the same between states. At every iteration, each page split its rank evenly among its outgoing edges and each page receives ranks from all its incoming edges
    
    Real Algorithm: - Links will be the same between states. Pages will be the same between states. Let d (damping factor) = 0.8. At every iteration, each page gives a d fraction of its rank to its outgoing edges (evenly) and each page gives a 1-d fraction of its rank to all pages (evenly) - each page receives ranks from all its incoming edges and from 1-d fraction, handling sinks.
                      In the real algorithm, for any sink, we add edges to all the pages from it. We emulate this via constraint that no page has zero outgoing edge.

==Testing/Assertion==
Check if it is possible to have a page with zero rank.
    --naive: possible for 4 state, 3 events, 10 Int
    --real: not possible for 4 States, 3 event, 10 Int, 3 Page

Check if it is possible to have a page with all rank
    --naive: possible for 10 Int
    --actual: not possible(unsat) for 10 Int, 3 Page

Check if page p having rank zero at state = s implies p having rank zero again in the next state s'
    --naive: no counterexample for 4 state, 3 events, 10 Int
    --real: not possible for 4 State, 3 Event, 10 Int, Page 3

Check if the existance of the sink implies that some of the page will dry out(i.e. has a rank = 0).
    --naive: counterexample for 8 states, 7 events, 10 Int
    --real: no counterexaple because there is no sink

Check if the rank is conserved:
    --naive: counterexample for 4 State, 3 Event, 10 Int <- rounding issue + sink
    --real: counterexample for 4 State, 3 Event, 10 Int, for 3 page <- rounding issue

Check if there is a page that accumulates all the rank where the number of page is more than 1.
    --naive: possible for 10 Int
    --real: not possible for 10 Int, for 3 Page

Check if there are two pages with four links, the ranks are always the same. (sort of a like an instance test with a trace)
    --naive: true for 10 Int
    --real: true for 10 Int, for 4 Page

Concrete instance tests of graphs with cycle, disconnected graphs and graphs with sink to ensure the correctness of both algorithms and the sink is handled by the real algorithm


Known Bugs: None