#lang forge

--sig for pages
sig Page {}


--sig for state, rank is a set of (page, int) where int represents page's current rank
sig State {
    page: set Page
    rank: set Page -> Int
}


--I just created 6 states/iteration for no reason. We can change this for sure.
one sig Initial extends State {}
one sig Iteration1 extends State {}
one sig Iteration2 extends State {}
one sig Iteration3 extends State {}
one sig Iteration4 extends State {}
one sig Iteration5 extends State {}
one sig Iteration6 extends State {}


--pred: a set of states is a set containing all the iterations and an initial state.
pred abstractState {
      State = Iteration1 + Iteration2 + Iteration3 + Iteration4 + Iteration5     
}



--pred: no change in the pages themselves across all the iterations. No new pages or no disappearing pages.
pred abstractPage{

}




run {setup and some HeapCell - Copy.allocated} for exactly 3 State



