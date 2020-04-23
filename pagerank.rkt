#lang forge

option solver "<Users/kawam.DESKTOP-GQ99D1U/OneDrive/desktop/sat/run.sh>"

sig Person {
    handshakes: set Person
}
one sig Liar extends Person {}

-- Rules for handhakes: nobody shook their own hand, nobody shook anyone's hand more than once, handshakes are reciprocal
pred basicDefinitions {
    -- Fill me in!
    all p: Person | all q: Person-p | no p & p.handshakes and lone (q & p) and (p in q.handshakes implies q in p.handshakes)
}

-- Each person shook a different number of hands
pred allUniqueHandshakes {
    basicDefinitions
    -- Fill me in!
    all p: Person | all q: Person-p | #(p.handshakes) != #(q.handshakes)
}

--run allUniqueHandshakes for exactly 5 Person, 5 Int

-- Everyone except the liar shook a different number of hands

pred oneLiar {
    basicDefinitions
    -- Fill me in!
    all p: Person-Liar | all q: Person-p-Liar | #(p.handshakes) != #(q.handshakes)
    some p: Person | (#(p.handshakes)= #(Liar.handshakes))
}

run oneLiar for exactly 5 Person, 5 Int

-- The number of hands shaken by the Liar is the only solution to this puzzle

pred noOtherSolution {
    -- Fill me in!
    oneLiar implies #(Liar.handshakes) = 2

}


check noOtherSolution for exactly 5 Person, 5 Int
