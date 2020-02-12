---------------- MODULE Network ----------------

(* This serves only as a proxy to the effectively used network implementation.
 * This allows to parameterize communication without changing the
 * PWSSemantics module. *)

VARIABLES net

CONSTANT Interest

PEERS == DOMAIN Interest

LOCAL NetworkImpl == INSTANCE NetworkCausal WITH PEERS <- PEERS

TypeInvariant == NetworkImpl!TypeInvariant

init == NetworkImpl!init

send(from, to, m) == NetworkImpl!send(from, to, m)

receive(from, to, m) == NetworkImpl!receive(from, to, m)

unchanged == NetworkImpl!unchanged

================================================================
