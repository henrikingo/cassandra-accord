------------------------------ MODULE algo1 ------------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Nodes, ReplicationFactor, FastElectorate, MaxKey, MaxTrxSize, MaxTime

VARIABLES now, seq, trx, t0, PreAcceptQ, Qidx, PreAcceptReplyQ, ReplyQidx, CommittedQ, AcceptQ


(* The key(s) operated on / or read, by a transaction *)
Keys == 1..MaxKey

PartitionFor(key) == (key \div MaxKey) * Nodes

ASSUME 
  /\ Nodes \in Nat 
  /\ Nodes > 0
  /\ MaxTrxSize < 6
  


(* Compare two Accord timestamps *)
ts1 \prec ts2 ==
    IF ts1[1] < ts2[1]
    THEN TRUE
    ELSE (IF ts1[1] = ts2[1]
          THEN (IF ts1[2] < ts2[2]
                THEN TRUE
                ELSE (IF ts1[2] = ts2[2]
                      THEN (IF ts1[3] < ts2[3]
                            THEN TRUE
                            ELSE FALSE)
                      ELSE FALSE)
                )
          ELSE FALSE)

Max(xs) ==  CHOOSE x \in xs : \A y \in xs : x # y => y \prec x
Min(xs) ==  CHOOSE x \in xs : \A y \in xs : x # y => x \prec y

IsInjective(f) == \A a,b \in DOMAIN f : f[a] = f[b] => a = b
ToSet(s) ==  { s[i] : i \in DOMAIN s }
SetToSeq(S) == CHOOSE f \in [1..Cardinality(S) -> S] : IsInjective(f)

CreateKeySet5(five) == {RandomElement(Keys), RandomElement(Keys), RandomElement(Keys), RandomElement(Keys), RandomElement(Keys)}

RECURSIVE CreateKeySetMax(_)
CreateKeySetMax(maxsize)== IF maxsize > 0 THEN CreateKeySetMax(maxsize-1) \union ({RandomElement(Keys)}) ELSE ({RandomElement(Keys)})
CreateKeySet(maxsize)== RandomElement(SUBSET CreateKeySetMax(5))
Createt0(self) == <<now, seq, self>>
(* Can't get structs to work, but... *)
(* keys, t0, deps, coordinator *)
(* Later we append... *)
(*                           ..., node id, PreAccepted, T *)
CreateTrx(self, t0usethis) == << CreateKeySet(MaxTrxSize), Createt0(self), {}, self>>  
(* CreateTrx(self, t0usethis) == << <<1,2,3>>, t0usethis, <<>>, {}, self >> *) 

RECURSIVE Combinations(_)
Combinations(N) == IF N > 0 THEN {N} \union Combinations(N-1) ELSE {} 

(* TODO FastElectorate should specify the set *)
FastQuorums == {x \in SUBSET Combinations(FastElectorate) : Cardinality(x) >  FastElectorate \div 2}
SlowQuorums == {x \in SUBSET Combinations(Nodes) : Cardinality(x) >  Nodes \div 2}




CreatePreAcceptResp(self,t0Arg,tArg,depsArg)==TRUE

Init == /\ now = 1
        /\ seq = 0
        /\ trx = <<>>
        /\ t0 = <<>>
        /\ PreAcceptQ = <<>>
        /\ Qidx = [x \in 1..(Nodes+1) |-> 1]
        /\ PreAcceptReplyQ = <<>>
        /\ ReplyQidx = 1
        /\ CommittedQ = <<>>
        /\ AcceptQ = <<>>
        
AllVars == <<now, seq, trx, t0, PreAcceptQ, Qidx, PreAcceptReplyQ, ReplyQidx, CommittedQ, AcceptQ>>



clock(self) == /\ now' = now + 1
               /\ seq' = 0
               /\ PrintT("Time: " \o ToString(now') \o "  self=" \o ToString(self))
               /\ UNCHANGED <<t0, trx, PreAcceptQ, Qidx, PreAcceptReplyQ, ReplyQidx, CommittedQ, AcceptQ>>
               
(*    1. t0 ← (now,0,C)                                    *)
(*    2. send PreAccept(τ,t0) to ∀ p ∈ Eτ                  *)
PreAccept(self) ==   /\ t0' = Createt0(self)
                     /\ trx' = CreateTrx(self, t0')
                     /\ seq' = seq+1
                     /\ PreAcceptQ' = Append(PreAcceptQ, trx' )
                     /\ UNCHANGED <<now, Qidx, PreAcceptReplyQ, ReplyQidx, CommittedQ, AcceptQ>>



(*   receive PreAccept(τ,t0 τ) on p:                                    *)
(*   3: if t0 τ > max(Tγ | γ ∼ τ) then                                  *)
(*   4:   tτ ← t0 τ                                                     *)
(*   5: else                                                            *)
(*   6:   tτ ← max(Tγ | γ ∼ τ)                                          *)
(*   7:   tτ.(seq, id) ← (tτ.seq + 1, p)                                *)
(*   8: end if                                                          *)
(*   9: Tτ ← tτ                                                         *)
(*   10: PreAcceptedτ ← true                                            *)
(*   11: reply PreAcceptOK(tτ, deps : {γ | γ ∼ τ ∧ t0 γ < t0 τ})        *)
(*   TODO: Now all threads process transactions in the same order, same RTT latency. *)
PreAcceptReply(self) == /\ Qidx[self] < Len(PreAcceptQ) +1
                            (* TODO: deps and their t0 *)
                        /\ PreAcceptReplyQ'= IF  <<0,0,0>> \prec PreAcceptQ[Qidx[self]][2] 
                                             THEN Append(PreAcceptReplyQ, Append(Append(Append(PreAcceptQ[Qidx[self]], self), TRUE), PreAcceptQ[Qidx[self]][2]))                                                  
                                             ELSE Append(PreAcceptReplyQ, Append(Append(Append(PreAcceptQ[Qidx[self]], self), FALSE), <<PreAcceptQ[Qidx[self]][2][1], PreAcceptQ[Qidx[self]][2][2]+1. self>>)) 
                        /\ Qidx' = [x \in 1..(Nodes+1) |-> IF self=x THEN Qidx[x]+1 ELSE Qidx[x] ]
                        /\ UNCHANGED <<PreAcceptQ, trx, now, seq, t0, ReplyQidx, CommittedQ, AcceptQ>>

(* receive PreAcceptOK(t,deps) from Qτ: *)
(* 12: deps←⋃{p.deps|p∈Qτ} *)
(* 13: if ∃ Fτ ⊆ Qτ(∀p∈Fτ·p.t=t0) then *)
(* 14:   send Commit(τ,t0,t0,deps)  to ∀p∈ρ∈Pτ *)
(* 15:   go to Execution Protocol *)
(* 16: else *)
(* 17:   t←max(p.t|p∈Qτ) *)
(* 18:   send Accept(τ,t0,t,deps) to ∀p∈ρ∈Pτ *)
(* 19: end  *) 


PreAcceptOk(self) == 
                     LET (* TODO replace ReplyQidx with subtracting or removing committed/done trx from the queue *)
                         activeQ == SubSeq(PreAcceptReplyQ, ReplyQidx, Len(PreAcceptReplyQ))
                         myQ == SelectSeq(activeQ, LAMBDA x: x[4]=self)
                         mytrx == IF myQ = <<>> THEN <<>> ELSE Head(myQ)
                         T == mytrx[7]
                         myt0 == mytrx[2]
                         trxAllShards == SelectSeq(myQ, LAMBDA x: x[7] = T)
                         trxPreAccepted == SelectSeq(trxAllShards, LAMBDA x : x[6])
                         shards ==  { trxAllShards[i][5] : i \in DOMAIN trxAllShards }                    
                         shardsPreAccepted ==  { trxPreAccepted[i][5] : i \in DOMAIN trxPreAccepted }                    
                     IN
                     /\ Len(myQ)>0
                     /\ PrintT("trx " \o ToString(self) \o ToString(mytrx)) 
                     /\ PrintT("shards " \o ToString(self) \o ToString(trxAllShards)) 
                     /\ PrintT("pre " \o ToString(self) \o ToString(shardsPreAccepted))
                     /\ PrintT("committedQ " \o ToString(self) \o ToString(CommittedQ))

                     /\ IF shardsPreAccepted \in FastQuorums
                        THEN  
                           /\ PrintT("fast commit: " \o ToString(trxAllShards))  (* TODO another roundtrip + execution protocol *)
                           /\ CommittedQ' = CommittedQ \o SetToSeq(ToSet([ i \in 1..Len(trxPreAccepted) |-> trxPreAccepted[i][2]]))
                           /\ PrintT("commit done" \o ToString(CommittedQ'))
                           /\ AcceptQ' = AcceptQ
                           /\ PreAcceptReplyQ' = SelectSeq(PreAcceptReplyQ, LAMBDA x : x[2] \notin ToSet(CommittedQ'))
                           /\ PrintT("filter queue done" \o ToString(PreAcceptReplyQ'))
                        ELSE
                           IF shards \in SlowQuorums
                           THEN 
                               /\ PrintT("TODO: Execute Accept aka slow path " \o ToString(trxAllShards))
                               /\ PreAcceptReplyQ' = SelectSeq(PreAcceptReplyQ, LAMBDA x : x[2] \notin ({T} \union ToSet(CommittedQ)))
                               /\ AcceptQ' = AcceptQ \o trxAllShards
                               /\ CommittedQ' = CommittedQ 
                           ELSE
                               /\ PrintT("...")
                               /\ CommittedQ' = CommittedQ
                               /\ AcceptQ' = AcceptQ
                               (* The below will filter out replies that are orphaned because a quorum already arrived and was processed earlier *)
                               /\ PrintT("Tossing the following reply, a quorum was already found and processed earlier: " \o ToString(SelectSeq(PreAcceptReplyQ, LAMBDA x : x[2] \in ({T})))) (* \union ToSet(CommittedQ) \union SetToSeq(ToSet([ i \in 1..Len(AcceptQ') |-> AcceptQ'[i][2]]))))) )*)
                               /\ PreAcceptReplyQ' = SelectSeq(PreAcceptReplyQ, LAMBDA x : x[2] \notin ({T} )) (* \union ToSet(CommittedQ) \union SetToSeq(ToSet([ i \in 1..Len(AcceptQ') |-> AcceptQ'[i][2]])))) *)
                     /\ UNCHANGED <<now,seq,trx,t0,PreAcceptQ,Qidx,ReplyQidx>>


PrintResults(self) == 
                  /\ (Len(CommittedQ) >0 /\ PrintT("committed: " \o ToString(CommittedQ)))  \/ TRUE
                  /\ (Len(PreAcceptReplyQ) >0 /\ PrintT("pre acc: " \o ToString(PreAcceptReplyQ)))  \/ TRUE
                  /\ (Len(AcceptQ) >0 /\ PrintT("accept: " \o ToString(AcceptQ)))  \/ TRUE
                  /\ UNCHANGED <<now,seq,trx,t0,PreAcceptQ,Qidx,ReplyQidx, CommittedQ, PreAcceptReplyQ, AcceptQ>>

Next ==     \/ \E self \in Nodes+1..Nodes+1: clock(self)
            \/ \E self \in 1..Nodes: PreAccept(self)
            \/ \E self \in 1..Nodes: PreAcceptReply(self) 
            \/ \E self \in 1..Nodes: PreAcceptOk(self) 
            \/ \E self \in 1..Nodes: PrintResults(self) 
          
Spec == Init /\ [][Next]_AllVars

(* Infinite loop, apparently, is like this...*)
ProcSet == {"while"}


=============================================================================

