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

--pred:


--pred for general setup
pred setup {
    abstractState
    abstractPage
    abstractEdge
}


pred noZeroRank[page: set Animal] {
    -- constraints for no page having zero rank

    ( all p: animals & Pet| some animals & Owner -p.owned) implies ( all p: animals & Pet| p.owned in animals )
}

pred neverStealing {
    -- for any state, there's no zero rank page.
     all s: State | {
        noStealing[s.near]
        noStealing[s.far]
    }
    ownedMakesSense
}

sig Event {
    pre: one State,
    post: one State,
}

state[State] initState {
    -- constraints for the first state
    -- Fill me in!
    near = Animal
    no far
    boat = Near
}
state[State] finalState {
    -- constraints for the last state that should hold for a valid solution
    -- Fill me in!
    no near
    far = Animal
    boat = Far
}
transition[State] crossRiver[e: Event] {
    -- constraints for moving across the river
    -- relating current state s, next state s', and event between them e
    -- Fill me in
    this = e.pre
    this' = e.post
    #e.toMove <= 2
    #e.toMove > 0

    boat = Near implies (boat' = Far and e.toMove in near and near' = near - e.toMove and far' = far + e.toMove)
    boat = Far implies (boat' = Near and e.toMove in far and near' = near + e.toMove and far' = far - e.toMove)
}

transition[State] puzzle {
    some e: Event | crossRiver[this, this', e]
}

trace<|State, initState, puzzle, finalState|> traces: linear {}

run<|traces|> neverStealing for 12 State, exactly 11 Event, 6 Animal, exactly 3 Pet, exactly 3 Owner, 2 Position, 4 Int





