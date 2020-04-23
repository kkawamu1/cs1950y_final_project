#lang forge

--sig for pages
sig Page {}


--sig for state, pageRank is a relation from Page to Int (each page get to have its rank), link is a set of edges between the pages (directed)
sig State {
    pageRank: set Page -> Int
    link: set Page -> Page
}


--pred: a set of states is a set containing all the iterations and an initial state.
pred abstractState {
      State = Iteration1 + Iteration2 + Iteration3 + Iteration4 + Iteration5     
}



--pred: no change in the pages themselves across all the iterations. No new pages or no disappearing pages.
pred abstractPage{

}

--pred: all the pages need to have their associated ranks.
pred allPageHasRank {

}
--pred: no change in the edges across all the iterations. No new edges or no disappearing edges.
pred abstractEdge{

}



--pred for general setup
pred setup {
    abstractState
    abstractPage
    abstractEdge
}


pred noZeroRank[pagerank: set Page->Int] {
    -- constraints for no page having zero rank
}


--we should use this pred to check if there will be a page that has zero as its rank.
pred neverZeroRank {
    -- for any state, there's no zero rank page.
     all s: State | {
        noZeroRank[s.pageRank]
    }
}

sig Event {
    pre: one State,
    post: one State,
}

state[State] initState {
    -- constraints for the first state
    -- Fill me in!
    
--we have to decide what value each page should hold as its initial value. In the original implementation, the initial value for a page p = 1 / the total numebr of pages.
    pageRank: set Page -> Int
    link = Page -> Page
}


-- here maybe define the final state as the bad state that we don't want the algorithm to reach. Then we check if it is possible to get to this final state in x amount of transitions.
state[State] finalState {
    -- Fill me in!
    

}
transition[State] crossRiver[e: Event] {
    -- constraints for how the ranks should be distributed
    -- relating current state s, next state s', and event between them e
    -- Fill me in
    this = e.pre
    this' = e.post

    ---boat = Near implies (boat' = Far and e.toMove in near and near' = near - e.toMove and far' = far + e.toMove)
    ---boat = Far implies (boat' = Near and e.toMove in far and near' = near + e.toMove and far' = far - e.toMove)
}

transition[State] puzzle {
    some e: Event | crossRiver[this, this', e]
}

trace<|State, initState, puzzle, finalState|> traces: linear {}

run<|traces|> neverStealing for 12 State, exactly 11 Event, 6 Animal, exactly 3 Pet, exactly 3 Owner, 2 Position, 4 Int





