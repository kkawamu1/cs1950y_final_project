#lang forge

--sig for pages
sig Page {
    link: set Page
}

---------- States ----------

--sig for state, pageRank is a relation from Page to Int (each page gets to have its rank), link is a set of edges between the pages (directed)
sig State {
    pageRank: set Page -> Int
}


---------- Events ----------

sig Event {
    pre: one State,
    post: one State
}

state[State] simpleInitState {
    -- constraints for the first state
    --we allow a page to point to itself.
    --we have to decide the initial value for each page is 10 to approximate the floating points.
    pageRank = Page -> sing[10]
    

    --there should be at least one page; otherwise, it is not so interesting anymore.
　　some Page
}



transition[State] naiveUpdate[e: Event] {
    -- constraints for how the ranks should be distributed
    -- relating current state s, next state s', and event between them e

    this = e.pre
    this' = e.post

    --link will stay the same between the states
    --link' = link

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

trace<|State, simpleInitState, naiveAlgorithm, _|> simpleTrace: linear {}
--run<|simpleTrace|> for 4 State, 3 Event,  10 Int

state[State] initState {
    -- constraints for the first state
    --we have to decide the initial value for each page is 10 to approximate the floating points.
    pageRank = Page -> sing[10]


    --Every page has at least one edge out. This guarantees that we do not have a sink. This emulates "adding edges to all pages".
    all p: Page | some (p.link)

    --there should be at least one page; otherwise, it is not so interesting anymore.
　　some Page
}



transition[State] fullUpdate[e: Event] {
    -- constraints for how the ranks should be distributed
    -- relating current state s, next state s', and event between them e
    -- Fill me in
    this = e.pre
    this' = e.post

    --link will stay the same between the states
    --link' = link

    --All the pages stay the same
    pageRank'.Int = pageRank.Int
    
    ---*****We have to be careful when taking sum because if we blindly take the sum, we can mess up since there could be duplicates in what we are summing over.*****----
    --https://github.com/cemcutting/Forge/blob/docs/forge/docs/basicForgeDocumentation.md#integers

    --damping factor = 0.8
    all vNext : pageRank.Int| vNext.pageRank' = sing[add[(divide[multiply[2, multiply[#Page, 10]], multiply[#Page, 10]]), divide[multiply[(sum incoming: link.vNext | {sum[sing[divide[sum[incoming.pageRank], #incoming.link]]]}), 8],10]]]
}

transition[State] fullAlgorithm {
    some e: Event | fullUpdate[this, this', e]
}

trace<|State, initState, fullAlgorithm, _|> traces: linear {}
run<|traces|> for 3 State, 2 Event,  10 Int, exactly 3 Page

----------Assertion --------------

--1. check if it is possible to have a page with zero rank.
                               
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


--this gives couterexamples. 
--check<|simpleTrace|> {neverZeroRank} for 4 State, exactly 3 Event,  10 Int

--this check is really slow
--check<|traces|> {neverZeroRank} for 4 State, exactly 3 Event,  10 Int

--no counter example
--check<|traces|> {neverZeroRank} for 2 State, exactly 1 Event,  10 Int
--slow
--check<|traces|> {neverZeroRank} for 3 State, exactly 2 Event,  10 Int



--2. check if page p having rank zero at state = s implies p having rank zero again in the next state s'.

pred zeroThenZero {
    --for each itration, and for each page, check its rank = 0 implies its rank = 0 in the next iteration.
    all iteration: Event | all p: Page| (iteration.pre.pageRank)[Page] = sing[0] implies (iteration.post.pageRank)[Page] = sing[0]    
}


/**
 We expect this to have no counter example. If a page get zero as its rank at some point, then it can never get any rank again.
This checks for the property. This explains why we need to have some mechanism to keep some of the weights to themselvs in the real version of the algorithm.
**/

--no counterexample, but really slow
--check<|simpleTrace|> {zeroThenZero} for 4 State, exactly 3 Event,  10 Int

--slow too
--this is effectively checkin whether it is possible for an advanced one to have zero rank at all. Therefore, it makes sense that it takes time.
--check<|traces|> {zeroThenZero} for 4 State, exactly 3 Event,  10 Int

--no counerexample
--check<|traces|> {zeroThenZero} for 2 State, exactly 1 Event,  10 Int




--3. If there is a sink (i.e. a page with only the edge to itself) and some other pages are pointing to the sink, then there will be page with rank zero.
-- I am not sure this pred will work since there might be a cycle and a sink. The rank in the cycle will gradually move to the sink, but the cycle will never become dry.
--it might be the case that rounding will enforce this pred to be true with the finte precision as in the case for any computer.
pred sinkPage {
    --sink page: no edge out from a page.
    ---some p: Page | no (p.link - p) and some (link.p - p)
    some p: Page | no (p.link)
}

--counter-example because trace is not long enough
--check<|simpleTrace|> {sinkPage implies not (neverZeroRank)} for 8 State, exactly 7 Event, 10 Int

--this has no counter-example because there is no sink
--check<|traces|> {sinkPage implies not (neverZeroRank)} for 8 State, 10 Int

pred rankConservation {
    all s1, s2: State | {
        let rank1 = sum p1: Page | sum[s1.pageRank[p1]] |
        let rank2 = sum p2: Page | sum[s2.pageRank[p2]] |
            rank1 = rank2
    }
}

pred rankConservation2 [t: TraceBase] {
    let rank = sum p: Page | sum[(t.init).pageRank[p]] |
        all s: State - t.init | {
        rank = (sum p1: Page | sum[s.pageRank[p1]])
    }
}

-- counter-example because of the possibility of a sink
--check<|simpleTrace|> {rankConservation2[simpleTrace]} for 8 State, exactly 8 Event, 10 Int, 3 Page

--slow
--check<|traces|> {rankConservation2[traces]} for 8 State, exactly 8 Event, 10 Int, exactly 3 Page

pred noRank[s: State] {
    sing[0] in s.pageRank[Page]
}

--run<|traces|> {noRank[traces.term]} for 10 Int, exactly 3 Page

pred concentratedRank[s: State] {
    #Page > 1
    sing[multiply[#Page, 10]] in s.pageRank[Page]
}

--run<|traces|> {concentratedRank[traces.term]} for 10 Int, exactly 3 Page

test expect {
    --<|simpleTrace|> {noRank[simpleTrace.term]} for 10 Int is sat

    --slow
    --<|traces|> {noRank[traces.term]} for 10 Int is unsat

    --<|simpleTrace|> {concentratedRank[simpleTrace.term]} for 10 Int is sat

    --slow
    --<|traces|> {concentratedRank[traces.term]} for 10 Int is unsat
}

pred onePage {
    one Page
    one link
}

-- check whether it is possible for the algorithm to perform on one-page graph
test expect{
    --<|simpleTrace|> {onePage} for 10 Int is sat
    --<|traces|> {onePage} for 10 Int is sat
}

pred twoPage[t: TraceBase] {
    #Page = 2
    #link = 4
    one pageRank[t.term][Page]
}

pred twoPageImpossible[t: TraceBase] {
    #Page = 2
    #link = 4
    #pageRank[t.term][Page] > 1
}

--if the graph is symmetric, the two page have the same rank
test expect{
    --<|simpleTrace|> {twoPage[simpleTrace]} for 10 Int is sat
    --<|traces|> {twoPage[traces]} for 10 Int is sat
    --<|simpleTrace|> {twoPageImpossible[simpleTrace]} for 10 Int is unsat
    --slow
    --<|traces|> {twoPageImpossible[traces]} for 10 Int is unsat
}