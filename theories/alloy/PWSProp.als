module PWSProp

open PWSDefs
open PWSSyntax
open PWSSemantics

pred SimpleTermination {
    all p : Process | some s: State, n : EndEvent | n in p.contains && s.nodemarks[n] >= 1
}

pred CorrectTermination {
    all p : Process | some s: State, n: EndEvent {
       n in p.contains && s.nodemarks[n] >= 1
       all nn : p.contains - n | s.nodemarks[nn] = 0
       }
}

pred Safe {
    all s: State, n : Node | s.nodemarks[n] <= 1
    all s: State, e : Edge | s.edgemarks[e] <= 1
}