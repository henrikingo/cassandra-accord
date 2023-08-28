---- MODULE MC ----
EXTENDS algo1, TLC

\* CONSTANT definitions @modelParameterConstants:0MaxTrxSize
const_169321748040866000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1ReplicationFactor
const_169321748041867000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:2MaxKey
const_169321748042968000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:3MaxTime
const_169321748043969000 == 
120
----

\* CONSTANT definitions @modelParameterConstants:4FastElectorate
const_169321748044970000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:5Nodes
const_169321748045971000 == 
3
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_169321748046972000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_169321748048073000 ==
now<MaxTime
----
=============================================================================
\* Modification History
\* Created Mon Aug 28 13:11:20 EEST 2023 by hingo
