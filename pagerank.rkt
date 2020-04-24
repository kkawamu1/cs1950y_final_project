#lang forge

--sig for pages
sig Page {}

---------- States ----------

--sig for state, pageRank is a relation from Page to Int (each page get to have its rank), link is a set of edges between the pages (directed)
sig State {
    pageRank: set Page -> Int,
    link: set Page -> Page
}


---------- Events ----------

sig Event {
    pre: one State,
    post: one State
}

state[State] initState {
    -- constraints for the first state
    -- Fill me in!
    
--we have to decide what value each page should hold as its initial value. In the original implementation, the initial value for a page p = 1 / the total numebr of pages.

--******we need to increase the bounds for int; otherwise, we can only have [-7, 8] you can chage the initial value here.
    pageRank = Page -> sing[10]

    --if there are more than two outgoing edgesm then none of them can be a self loop.
    all p: Page | #p.link>1 implies no link.p & p.link

    --only time, the page will have just one outgoing edge is when it is pointing itself to preserve the total ranks. (it is going to send its rank to itself)
    all p: Page | (one p.link) implies (one link.p & p.link)

    --there should be at least one page;otherwise, it is not so interesting anymore.
　　some link
}



-- here maybe define the final state as the bad state that we don't want the algorithm to reach. Then we check if it is possible to get to this final state in x amount of transitions.
--or just define this final state as some random sate, which does not constrain anything, but there for the sake of trace.
state[State] finalState {
    -- Fill me in!


    ---right now I am defining the final state to be a random state with pretty much no constraint except that it needs to have the same graph.
    all p: Page | #p.link>1 implies no link.p & p.link
　  all p: Page | (one p.link) implies (one link.p & p.link)
　　some link　
}


transition[State] naiveUpdate[e: Event] {
    -- constraints for how the ranks should be distributed
    -- relating current state s, next state s', and event between them e
    -- Fill me in
    this = e.pre
    this' = e.post

    --link will stay the same between the states
    link' = link

    --All the pages stay the same
    pageRank'.Int = pageRank.Int
    
    ---*****We have to be careful when taking sum because if we blindly take the sum, we can mess up since there could be duplicates in what we are summing over.*****----
    --https://github.com/cemcutting/Forge/blob/docs/forge/docs/basicForgeDocumentation.md#integers

    --for each vertex v, the value of v in the next iteration is the sum of the ranks / # outgoing edges over the vertex u where u->v is in link
    all vNext : pageRank.Int| vNext.pageRank' = sing[(sum incoming: link.vNext | {sum[sing[divide[sum[incoming.pageRank], #incoming.link]]] })]
    
}


transition[State] naiveAlgorithm {
    some e: Event | naiveUpdate[this, this', e]
}

trace<|State, initState, naiveAlgorithm, finalState|> traces: linear {}

run<|traces|> for 4 State, exactly 3 Event,  8 Int


----------Assertion --------------
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





