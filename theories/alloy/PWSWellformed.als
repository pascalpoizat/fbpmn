module PWSWellformed

open PWSProp

/* Well-formed conditions */

/* An assert is not checked, why? */
fact MessageDifferentProcesses {
    all m : MessageFlow | !(m.source.processOf = m.target.processOf)
}

/* to be continued */
