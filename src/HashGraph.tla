---- MODULE HashGraph ----
EXTENDS FiniteSets, Naturals, Sequences, TLC

\* Number of authors
CONSTANT n
ASSUME n > 1

\* Coin flip constant
CONSTANT c
ASSUME c > 2

\* Number of rounds before election
CONSTANT d
ASSUME d > 0

CONSTANT Payload, MaxEvents

Author == 1..n
Hash == 0..MaxEvents
Time == Hash
Signature == Author

Event == [
    payload: Payload,
    self_parent: Hash,
    other_parent: Hash,
    time: Time,
    author: Author,
    sig: Signature
]

SelfParent(x) == IF x.self_parent = 0 THEN {} ELSE { x.self_parent }

Parents(x) == SelfParent(x) \union IF x.other_parent = 0 THEN {} ELSE { x.other_parent } 

Events(G) == {i \in 1..Len(G) : G[i]}

RECURSIVE Ancestor(_, _)
Ancestor(x, y) ==
    \/ x = y
    \/ \E z \in Parents(x) : Ancestor(z, y)

RECURSIVE SelfAncestor(_, _)
SelfAncestor(x, y) ==
    \/ x = y
    \/ /\ SelfParent(x) # {}
       /\ SelfAncestor(SelfParent(x), y)

ManyCreators(S) ==
    /\ Cardinality(S) > (2 \div 3) * n
    /\ \A x, y \in S : x # y => x.author # y.author

See(x, y, G) ==
    /\ Ancestor(x, y)
    /\ ~(\E a, b \in Events(G) :
      /\ a.author = y.author
      /\ b.author = y.author
      /\ Ancestor(x, a)
      /\ Ancestor(x, b)
      /\ ~SelfAncestor(a, b)
      /\ ~SelfAncestor(b, a))

StronglySee(x, y, G) ==
    /\ See(x, y, G)
    /\ \E S \in SUBSET Events(G) :
           /\ ManyCreators(S)
           /\ \A z \in S :
               /\ See(x, z, G)
               /\ See(z, y, G)

Max(S) ==
    CHOOSE x \in S:
        \A y \in S:
            y <= x

Min(S) ==
    CHOOSE x \in S:
        \A y \in S:
            y >= x

Smaller(x, S) == { s \in S : s < x }

Larger(x, S) == { s \in S : s > x }

Median(S) ==
    CHOOSE x \in S:
        IF Cardinality(S) % 2 = 0
        THEN Cardinality(Smaller(x, S \ x)) = Cardinality(Larger(x, S \ x)) - 1
        ELSE Cardinality(Smaller(x, S \ x)) = Cardinality(Larger(x, S \ x))

RECURSIVE Round(_, _)

SelfParentRound(x, G) ==
    IF SelfParent(x) = {}
    THEN 1
    ELSE Round(SelfParent(x), G)

Round(x, G) == Max(
    { SelfParentRound(x, G) } \union
    { r \in Nat :
        \E S \in SUBSET Events(G) :
            /\ ManyCreators(S)
            /\ \A y \in S :
                /\ Round(y, G) = r - 1
                /\ StronglySee(x, y, G) })

Witness(x, G) == SelfParent(x) \/ Round(x, G) > Round(SelfParent(x), G)

Diff(x, y, G) == Round(x, G) - Round(y, G)

RECURSIVE Vote(_, _, _)

Votes(x, y, v, G) == Cardinality({ z \in Events(G) :
    /\ Diff(x, z, G) = 1
    /\ Witness(z, G)
    /\ StronglySee(x, z, G)
    /\ Vote(z, y, G) = v
})

FractTrue(x, y, G) ==
    LET true == Votes(x, y, TRUE, G)
        false == Votes(x, y, FALSE, G)
        total == true + false
    IN true \div IF total = 0 THEN 1 ELSE total

RECURSIVE Decide(_, _, _)
Decide(x, y, G) ==
    \/ /\ SelfParent(x) # {}
       /\ Decide(SelfParent(x), y, G)
    \/ /\ Witness(x, G)
       /\ Witness(y, G)
       /\ Diff(x, y, G) > d
       /\ Diff(x, y, G) % c > 0
       /\ \E v \in BOOLEAN : Votes(x, y, v, G) > (2 \div 3) * n

CopyVote(x, y, G) ==
    \/ ~Witness(x, G)
    \/ /\ SelfParent(x) # {}
       /\ Decide(SelfParent(x), y, G)

MiddleBit(x) == x.signature % 2

Vote(x, y, G) ==
    IF CopyVote(x, y, G) THEN Vote(SelfParent(x), y, G) ELSE
    IF Diff(x, y, G) = d THEN See(x, y, G) ELSE
    IF /\ Diff(x, y, G) % c = 0
       /\ 1 \div 3 <= FractTrue(x, y, G)
       /\ 2 \div 3 <= FractTrue(x, y, G)
    THEN MiddleBit(x) = 1
    ELSE FractTrue(x, y, G) >= 1 \div 2

Famous(x, G) == \E y \in Events(G) : Decide(y, x, G) /\ Vote(y, x, G)

UniqueFamous(x, G) ==
    /\ Famous(x, G)
    /\ ~\E y \in Events(G) : y # x /\ Famous(y, G)

RoundsDecided(r, G) ==
    \A x \in Events(G) :
        Round(x, G) <= r /\ Witness(x, G) =>
        \E y \in Events(G) : Decide(y, x, G)

RoundReceived(x, G) == Min({r \in Nat :
    /\ RoundsDecided(r, G)
    /\ \A y \in Events(G) :
        /\ r = Round(y, G)
        /\ UniqueFamous(y, G)
        => Ancestor(y, x)
})

TimeReceived(x, G) == Median({ y.time : y \in { y \in Events(G) :
    /\ Ancestor(y, x)
    /\ \E z \in Events(G) :
        /\ Round(z, G) = RoundReceived(x, G)
        /\ UniqueFamous(z, G)
        /\ SelfAncestor(z, y)
    /\ ~\E w \in Events(G) :
        /\ SelfAncestor(y, w)
        /\ Ancestor(w, x)
}})

----
VARIABLE events, self_parent, other_parent

TypeInv ==
    /\ events \in Seq(Event)
    /\ self_parent \in [Author -> Nat]
    /\ other_parent \in [Author -> Nat]

Init ==
    /\ events = << >>
    /\ self_parent = [a \in Author |-> 0] 
    /\ other_parent = [a \in Author |-> 0]

NewEvent(a, p) == [
    payload |-> p,
    self_parent |-> self_parent[a],
    other_parent |-> other_parent[a],
    time |-> 0,
    author |-> a,
    sig |-> a
]

Create(a, p) ==
    /\ events' = Append(events, NewEvent(a, p))
    /\ self_parent' = [self_parent EXCEPT ![a] = Len(events)]
    /\ UNCHANGED other_parent

Sync(a1, a2) ==
    /\ other_parent' = [other_parent EXCEPT ![a2] =
        IF self_parent[a1] > @ THEN self_parent[a1] ELSE @]
    /\ UNCHANGED <<events, self_parent>>

Next ==
    \/ \E a \in Author, p \in Payload : Create(a, p)
    \/ \E a1, a2 \in Author :
        /\ a1 # a2
        /\ Sync(a1, a2)

Spec == Init /\ [][Next]_<<events, self_parent, other_parent>>
====
