module PWSProp

open PWSDefs
open PWSSyntax
open PWSSemantics

pred SimpleTermination {
    all p : Process | eventually some n : EndEvent | n in p.contains && n.markn >= 1
}

pred CorrectTermination {
    all p : Process | eventually some n: EndEvent {
       n in p.contains && n.markn >= 1
       all nn : p.contains - n | nn.markn = 0
       }
}

pred Safe {
    always all n : Node | n.markn <= 1
    always all e : Edge | e.marke <= 1
}
