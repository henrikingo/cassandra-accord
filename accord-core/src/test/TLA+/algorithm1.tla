------------------------------ MODULE algorithm1 ------------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Coordinators, Nodes, ReplicationFactor, FastElectorate, MaxKey, MaxTrxSize, MaxTime



(* The key(s) operated on / or read, by a transaction *)
Keys == 1..MaxKey

PartitionFor(key) == (key \div MaxKey) * Nodes

ASSUME Nodes \in Nat /\ Nodes > 0
  (* TODO if you know how to draw N random numbers from a set... *)
  /\ MaxTrxSize < 6



(* Compare two Accord timestamps *)
ts1 \prec ts2 ==
    IF ts1[3] < ts2[3]
    THEN (IF ts1[2] < ts2[2]
          THEN (IF ts1[1] < ts2[1]
                THEN TRUE
                ELSE FALSE)
          ELSE FALSE)
    ELSE FALSE

Max(xs) ==  CHOOSE x \in xs : \A y \in xs : x # y => y \prec x

(***********
(* TODO: Review: Probably variables not scoped well (global, per node...) .*)
(* TODO: Quorums completely missing.*)
(* TODO: Slow path and commit completely missing. *)
(* TODO: Coordinator work should maybe be happening in the nodes, not separately *)

--algorithm Accord {

    variables
        (* queues *)
        SimpleQ = <<>>;
        PreAcceptOkQ = <<>>;
        PreAcceptQ = <<>>;
        PreAcceptPointer = [ nod \in 1..Nodes |-> 1];

        keySet = {};
        i = 0;
        seq = 0;
        trx = <<>>;
        now = 0;
        t0 = <<>>;
        T = 0;
        slowTrx = <<>>;
        concurrentTrx = [ nod \in 1..Nodes |-> <<>>];
        conflictingTrx = [ nod \in 1..Nodes |-> <<>>];
        preAccepted = [ nod \in 1..Nodes |-> <<>>];
        fastPathTrx = <<>>;
        deps = {};
        conflicts = {};
        p = {};
        trx_p = {};
        maxtrx = <<>>;
        maxt = <<>>;
        keys = [ nod \in 1..Nodes |-> <<>>];
        msg = <<>>;
        coordinator = 0;
        newTrx = <<>>;
        reply = <<>>;

    define {
        CreateKeySet5(five) == {RandomElement(Keys), RandomElement(Keys), RandomElement(Keys), RandomElement(Keys), RandomElement(Keys)}
        TrxSize(maxsize) == RandomElement(1..maxsize)
        CreateKeySet(size)== CHOOSE keyset \in SUBSET CreateKeySet5(5): Cardinality(keyset) = TrxSize(size)
        Createt0(self) == <<now, seq, self>>
        CreateTrx(self, t0usethis) == << CreateKeySet(MaxTrxSize), t0usethis, <<>>, {}, self >>

    }

    macro SendPreAccept(self) {
            (* print "SendPreAccept" \o "  self=" \o ToString(self); *)

            t0 := Createt0(self);
            trx := CreateTrx(self, t0);
            seq := seq+1;
    }

    macro RecvPreAccept(self) {
            (* print "RecvPreAccept " \o ToString(self);*)
            coordinator := trx[5];
            deps := trx[4];
            t0 := trx[2];
            keySet := trx[1];

            (* TODO Use PartitionFor to divide keys for each node + replicatoin factor. Now skipping for simplicity. *)
            (* So until fixed, the experinece is comparable to ReplicationFactor == Nodes. *)

            keys[self] := trx[1];

            (* TODO bug *)
            conflicts := {};
            (* conflicts := IF concurrentTrx[self] = <<>> THEN {} ELSE {trx2 \in concurrentTrx[self]: Cardinality(  keys[self] \intersect trx2[1]  ) > 0 }; *)

            maxtrx := IF Cardinality(conflicts) > 0 THEN Max(conflicts) ELSE FALSE;
            T := IF Cardinality(conflicts) = 0 THEN t0 ELSE maxtrx[2];
            newTrx := <<keySet, t0, T, deps, coordinator>>;

        };


    macro ReplyPreAcceptOk(self) {
        print "pass";
        (* TODO deal with conflicts and deps later *)
        (* deps[T][self] := {trx2 \in conflictingTrx[self][t0] : trx2[2] \prec T}; *)
        (* trx := <<trx[1], trx[2], trx[3], deps>>;*)
    }

    macro RecvPreAcceptOk(self) {
        print "RecvPreAcceptOk";
        print self;
        print deps;
        print reply;

        (* TODO deal with partitions and deps *)
        (* From here it continues with (fast) Commit or (slow) Accept *)
    };

    macro Tick(self) {
        now := now +1;
        seq := 0;
        when now \in 1..MaxTime;
        print "Time: " \o ToString(now) \o "  self=" \o ToString(self);
    }

    process (clock \in {Nodes+Coordinators+2})    {
        eventLoopClock: while (TRUE) {
              Tick(self);
          }
    }

    process (coord \in (Nodes+1)..(Coordinators+Nodes+1) ) {
        eventLoopCoordinators: while (TRUE) {
                either {
                    SendPreAccept(self);
                    PreAcceptQ := Append(PreAcceptQ, trx);
                }
                or {
                    if (Len(PreAcceptOkQ) > 0 ) {
                        reply := Head(PreAcceptOkQ);
                        PreAcceptOkQ := Tail(PreAcceptOkQ);
                        RecvPreAcceptOk(self);
                    }
                }
          }
    }

    process (node \in 1..(Nodes) ) {
        eventLoopNodes: while (TRUE) {
            if ( Len(PreAcceptQ) >= PreAcceptPointer[self] ) {

                trx := PreAcceptQ[PreAcceptPointer[self]];
                PreAcceptPointer[self] := PreAcceptPointer[self] + 1;

                    RecvPreAccept(self);

                concurrentTrx[self] := Append( concurrentTrx[self], newTrx );


                    ReplyPreAcceptOk(self);

                print T;
                preAccepted[self] := Append(preAccepted[self], T);
                PreAcceptOkQ := Append(PreAcceptOkQ, newTrx);
                print PreAcceptOkQ;

            };




        }
    }
}

*)
\* BEGIN TRANSLATION
VARIABLES SimpleQ, PreAcceptOkQ, PreAcceptQ, PreAcceptPointer, keySet, i, seq,
          trx, now, t0, T, slowTrx, concurrentTrx, conflictingTrx,
          preAccepted, fastPathTrx, deps, conflicts, p, trx_p, maxtrx, maxt,
          keys, msg, coordinator, newTrx, reply

(* define statement *)
CreateKeySet5(five) == {RandomElement(Keys), RandomElement(Keys), RandomElement(Keys), RandomElement(Keys), RandomElement(Keys)}
TrxSize(maxsize) == RandomElement(1..maxsize)
CreateKeySet(size)== CHOOSE keyset \in SUBSET CreateKeySet5(5): Cardinality(keyset) = TrxSize(size)
Createt0(self) == <<now, seq, self>>
CreateTrx(self, t0usethis) == << CreateKeySet(MaxTrxSize), t0usethis, <<>>, {}, self >>


vars == << SimpleQ, PreAcceptOkQ, PreAcceptQ, PreAcceptPointer, keySet, i,
           seq, trx, now, t0, T, slowTrx, concurrentTrx, conflictingTrx,
           preAccepted, fastPathTrx, deps, conflicts, p, trx_p, maxtrx, maxt,
           keys, msg, coordinator, newTrx, reply >>

ProcSet == ({Nodes+Coordinators+2}) \cup ((Nodes+1)..(Coordinators+Nodes+1)) \cup (1..(Nodes))

Init == (* Global variables *)
        /\ SimpleQ = <<>>
        /\ PreAcceptOkQ = <<>>
        /\ PreAcceptQ = <<>>
        /\ PreAcceptPointer = [ nod \in 1..Nodes |-> 1]
        /\ keySet = {}
        /\ i = 0
        /\ seq = 0
        /\ trx = <<>>
        /\ now = 0
        /\ t0 = <<>>
        /\ T = 0
        /\ slowTrx = <<>>
        /\ concurrentTrx = [ nod \in 1..Nodes |-> <<>>]
        /\ conflictingTrx = [ nod \in 1..Nodes |-> <<>>]
        /\ preAccepted = [ nod \in 1..Nodes |-> <<>>]
        /\ fastPathTrx = <<>>
        /\ deps = {}
        /\ conflicts = {}
        /\ p = {}
        /\ trx_p = {}
        /\ maxtrx = <<>>
        /\ maxt = <<>>
        /\ keys = [ nod \in 1..Nodes |-> <<>>]
        /\ msg = <<>>
        /\ coordinator = 0
        /\ newTrx = <<>>
        /\ reply = <<>>

clock(self) == /\ now' = now +1
               /\ seq' = 0
               /\ now' \in 1..MaxTime
               /\ PrintT("Time: " \o ToString(now') \o "  self=" \o ToString(self))
               /\ UNCHANGED << SimpleQ, PreAcceptOkQ, PreAcceptQ,
                               PreAcceptPointer, keySet, i, trx, t0, T,
                               slowTrx, concurrentTrx, conflictingTrx,
                               preAccepted, fastPathTrx, deps, conflicts, p,
                               trx_p, maxtrx, maxt, keys, msg, coordinator,
                               newTrx, reply >>

coord(self) == /\ \/ /\ t0' = Createt0(self)
                     /\ trx' = CreateTrx(self, t0')
                     /\ seq' = seq+1
                     /\ PreAcceptQ' = Append(PreAcceptQ, trx')
                     /\ UNCHANGED <<PreAcceptOkQ, reply>>
                  \/ /\ IF Len(PreAcceptOkQ) > 0
                           THEN /\ reply' = Head(PreAcceptOkQ)
                                /\ PreAcceptOkQ' = Tail(PreAcceptOkQ)
                                /\ PrintT("RecvPreAcceptOk")
                                /\ PrintT(self)
                                /\ PrintT(deps)
                                /\ PrintT(reply')
                           ELSE /\ TRUE
                                /\ UNCHANGED << PreAcceptOkQ, reply >>
                     /\ UNCHANGED <<PreAcceptQ, seq, trx, t0>>
               /\ UNCHANGED << SimpleQ, PreAcceptPointer, keySet, i, now, T,
                               slowTrx, concurrentTrx, conflictingTrx,
                               preAccepted, fastPathTrx, deps, conflicts, p,
                               trx_p, maxtrx, maxt, keys, msg, coordinator,
                               newTrx >>

node(self) == /\ IF Len(PreAcceptQ) >= PreAcceptPointer[self]
                    THEN /\ trx' = PreAcceptQ[PreAcceptPointer[self]]
                         /\ PreAcceptPointer' = [PreAcceptPointer EXCEPT ![self] = PreAcceptPointer[self] + 1]
                         /\ coordinator' = trx'[5]
                         /\ deps' = trx'[4]
                         /\ t0' = trx'[2]
                         /\ keySet' = trx'[1]
                         /\ keys' = [keys EXCEPT ![self] = trx'[1]]
                         /\ conflicts' = {}
                         /\ maxtrx' = (IF Cardinality(conflicts') > 0 THEN Max(conflicts') ELSE FALSE)
                         /\ T' = (IF Cardinality(conflicts') = 0 THEN t0' ELSE maxtrx'[2])
                         /\ newTrx' = <<keySet', t0', T', deps', coordinator'>>
                         /\ concurrentTrx' = [concurrentTrx EXCEPT ![self] = Append( concurrentTrx[self], newTrx' )]
                         /\ PrintT("pass")
                         /\ PrintT(T')
                         /\ preAccepted' = [preAccepted EXCEPT ![self] = Append(preAccepted[self], T')]
                         /\ PreAcceptOkQ' = Append(PreAcceptOkQ, newTrx')
                         /\ PrintT(PreAcceptOkQ')
                    ELSE /\ TRUE
                         /\ UNCHANGED << PreAcceptOkQ, PreAcceptPointer,
                                         keySet, trx, t0, T, concurrentTrx,
                                         preAccepted, deps, conflicts, maxtrx,
                                         keys, coordinator, newTrx >>
              /\ UNCHANGED << SimpleQ, PreAcceptQ, i, seq, now, slowTrx,
                              conflictingTrx, fastPathTrx, p, trx_p, maxt, msg,
                              reply >>

Next == (\E self \in {Nodes+Coordinators+2}: clock(self))
           \/ (\E self \in (Nodes+1)..(Coordinators+Nodes+1): coord(self))
           \/ (\E self \in 1..(Nodes): node(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION


=============================================================================

