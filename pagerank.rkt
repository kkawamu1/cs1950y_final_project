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

    --all the pages have at least one edge. If there is one outgoing edgem then it could be to itself or to another page
    ---*****If we delte this, the we can have a page with no outgoing edge, then we expect to see the "disappering rank". It will be easy to check that too.****---
　　　
    all p: Page | #p.link >= 1

    --there should be at least one page;otherwise, it is not so interesting anymore.
　　some link
}



-- here maybe define the final state as the bad state that we don't want the algorithm to reach. Then we check if it is possible to get to this final state in x amount of transitions.
--or just define this final state as some random sate, which does not constrain anything, but there for the sake of trace.

state[State] finalState {
    -- Fill me in!
    ---right now I am defining the final state to be a random state with pretty much no constraint except that it needs to have the same graph.
    all p: Page | #p.link>1 implies no link.p & p.link
    all p: Page | #p.link >= 1
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

--trace<|State, initState, naiveAlgorithm, finalState|> traces: linear {}

--run<|traces|> for 4 State, exactly 3 Event,  10 Int


transition[State] fullUpdate[e: Event] {
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

    --damping factor = 0.8
    all vNext : pageRank.Int| vNext.pageRank' = sing[add[(divide[multiply[2, 30], multiply[#Page, 10]]), divide[multiply[(sum incoming: link.vNext | {sum[sing[divide[sum[incoming.pageRank], #incoming.link]]]}), 8],10]]]
}

transition[State] fullAlgorithm {
    some e: Event | fullUpdate[this, this', e]
}

trace<|State, initState, fullAlgorithm, finalState|> traces: linear {}
run<|traces|> for 3 State, exactly 3 Event,  10 Int, exactly 3 Page

----------Assertion --------------

--1. check if it is possible to have a page with zero rank with the naive implementation.
                               
pred noZeroRank[pagerank: set Page->Int] {
    -- constraints for no page having zero rank
    not (sing[0] in Page.pagerank)
}


--we should use this pred to check if there will be a page that has zero as its rank.
pred neverZeroRank {
    -- for any state, there's no zero rank page.
     all s: State | {
        noZeroRank[s.pageRank]
    }
}

/**
We expect this to return some counterexamples. This shows the defect of the naive algorithm.

**/
--check<|traces|> {neverZeroRank} for 4 State, exactly 3 Event,  10 Int




--2. check if page p having rank zero at state = s implies p having rank zero again in the next state s'.

pred zeroThenZero {
    --for each itration, and for each page, check its rank = 0 implies its rank = 0 in the next iteration.
    all iteration: Event | all p: Page| (iteration.pre.pageRank)[Page] = sing[0] implies (iteration.post.pageRank)[Page] = sing[0]    
}


/**
 We expect this to have no couter example. If a page get zero as its rank at some point, then it can never get any rank again.
This checks for the property. This explains why we need to have some mechanism to keep some of the weights to themselvs in the real version of the algorithm.
**/

--check<|traces|> {zeroThenZero} for 4 State, exactly 3 Event,  10 Int


--3. If there is a sink (i.e. a page with only the edge to itself) and some other pages are pointing to the sink, then there will be page with rank zero.
--We added "other pages pointing at the sink", because if all the pages are pointing at themselvs, then it is not interesting.

pred sinkPage {
               --only page that the sink is pointing is itself.
    all s: State | some p: Page| (p.(s.link) = p)
    all s: State | all p: Page| (p.(s.link) = p) implies some ((s.link).p - p)
}



/**
If there is a sink, then it will get at least some amout of the rank from the other pages. If there is an edge between sink and non-sink, then there is a flow of rank from non-sink to sink.
Threfore, with enough iteration, there should be a rank zero page. However, we should see the instances where the sink is not connected to any page. Therefore, the sink does not suck up the rank.
We probably need lot of iterations to congerve...Difficult to check for many pages.
**/

--check<|traces|> {sinkPage implies not (neverZeroRank)} for 8 State, exactly 8 Event,  10 Int, exactly 3 Page




