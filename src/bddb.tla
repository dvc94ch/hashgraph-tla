---- MODULE Bddb ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS NumPeers, NumWriters, NumKeys
ASSUME NumWriters <= NumPeers

Peers == 1..NumPeers
Keys == 1..NumKeys

CONSTANT MaxNumOp

Ops == 1..MaxNumOp 

Tx == [key: Keys, value: Ops]

VARIABLES db, tx, value, writers

Init ==
    /\ value = 1
    /\ writers = {p \in 1..NumWriters : p }
    /\ db = [p \in Peers |-> [k \in Keys |-> 0]]
    /\ tx = [p \in Peers |-> Seq(Tx)]

Read(p, key) == db[r][key] 

SelectWriter(p) == IF p \in writers THEN p ELSE RandomElement(writers)

CreateWrite(p, key) == LET w == SelectWriter(p) IN
    /\ value' = value + 1
    /\ tx' = [tx EXCEPT ![w] = Append(@, [key |-> key, value |-> value]]
    /\ UNCHANGED db

ApplyWrite(p, key, value) ==
    /\ db' = [db EXCEPT ![p] = [@ EXCEPT ![key] = value]]
    /\ UNCHANGED <<value, tx>>

Next == Sync

====
