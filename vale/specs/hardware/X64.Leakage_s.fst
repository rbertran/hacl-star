module X64.Leakage_s

open X64.Machine_s
open X64.Taint_Semantics_s
open X64.Bytes_Semantics_s
module F = FStar.FunctionalExtensionality

type reg_taint = F.restricted_t reg (fun _ -> taint)
type xmms_taint = F.restricted_t xmm (fun _ -> taint)

noeq type analysis_taints =
  | AnalysisTaints: regTaint: reg_taint -> flagsTaint: taint -> cfFlagsTaint: taint -> ofFlagsTaint: taint ->
      xmmTaint: xmms_taint -> analysis_taints

let publicFlagValuesAreSame (ts:analysis_taints) (s1:machine_state) (s2:machine_state) =
  ts.flagsTaint = Public ==> (s1.ms_flags = s2.ms_flags)

let publicCfFlagValuesAreSame (ts:analysis_taints) (s1:machine_state) (s2:machine_state) =
  Public? ts.cfFlagsTaint ==> (cf s1.ms_flags = cf s2.ms_flags)

let publicOfFlagValuesAreSame (ts:analysis_taints) (s1:machine_state) (s2:machine_state) =
  Public? ts.ofFlagsTaint ==> (overflow s1.ms_flags = overflow s2.ms_flags)

let publicRegisterValuesAreSame (ts:analysis_taints) (s1:machine_state) (s2:machine_state) =
  forall r.{:pattern ts.regTaint r \/ s1.ms_regs r \/ s2.ms_regs r}
    ts.regTaint r = Public ==>
    (s1.ms_regs r = s2.ms_regs r)

let publicMemValueIsSame
  (mem1 mem2:heap) 
  (memTaint1 memTaint2:Map.t int taint)
  (x:int) =
  (Public? (memTaint1.[x]) || Public? (memTaint2.[x])) ==>
     mem1.[x] == mem2.[x]

let publicMemValuesAreSame (s1:machine_state) (s2:machine_state) =
  forall x.{:pattern s1.ms_memTaint.[x] \/ s2.ms_memTaint.[x] \/ s1.ms_mem.[x] \/ s2.ms_mem.[x]}
    publicMemValueIsSame s1.ms_mem s2.ms_mem s1.ms_memTaint s2.ms_memTaint x

let publicXmmValuesAreSame (ts:analysis_taints) (s1:machine_state) (s2:machine_state) =
  forall r.{:pattern ts.xmmTaint r \/ s1.ms_xmms r \/ s2.ms_xmms r}
    ts.xmmTaint r = Public ==>
    (s1.ms_xmms r = s2.ms_xmms r)

let publicStackValueIsSame
  (stack1 stack2:heap) 
  (stackTaint1 stackTaint2:Map.t int taint)
  (x:int)
  = (Public? (stackTaint1.[x]) || Public? (stackTaint2.[x])) ==>
     stack1.[x] == stack2.[x]


let publicStackValuesAreSame (s1:machine_state) (s2:machine_state) =
  let Vale_stack _ stack1 = s1.ms_stack in
  let Vale_stack _ stack2 = s2.ms_stack in
  forall x.{:pattern s1.ms_stackTaint.[x] \/ s2.ms_stackTaint.[x] \/ stack1.[x] \/ stack2.[x]}
    publicStackValueIsSame stack1 stack2 s1.ms_stackTaint s2.ms_stackTaint x

let publicValuesAreSame (ts:analysis_taints) (s1:machine_state) (s2:machine_state) =
   publicRegisterValuesAreSame ts s1 s2
  /\ publicFlagValuesAreSame ts s1 s2
  /\ publicCfFlagValuesAreSame ts s1 s2
  /\ publicOfFlagValuesAreSame ts s1 s2
  /\ publicMemValuesAreSame s1 s2
  /\ publicStackValuesAreSame s1 s2
  /\ publicXmmValuesAreSame ts s1 s2

let constTimeInvariant (ts:analysis_taints) (s:machine_state) (s':machine_state) =
    publicValuesAreSame ts s s'
  /\ s.ms_trace = s'.ms_trace


let isConstantTimeGivenStates (code:code) (fuel:nat) (ts:analysis_taints) (s1:machine_state) (s2:machine_state) =
  let r1 = taint_eval_code code fuel s1 in
  let r2 = taint_eval_code code fuel s2 in
  ( (Some? r1) /\ (Some? r2)
   /\ s1.ms_ok /\ (Some?.v r1).ms_ok
   /\ s2.ms_ok /\ (Some?.v r2).ms_ok
   /\ constTimeInvariant ts s1 s2
  ) ==> (Some?.v r1).ms_trace = (Some?.v r2).ms_trace

let isConstantTime (code:code) (ts:analysis_taints) =
  forall s1 s2 fuel.
      isConstantTimeGivenStates code fuel ts s1 s2

let is_explicit_leakage_free_lhs (code:code) (fuel:nat)
                                 (ts:analysis_taints) (ts':analysis_taints) (s1:machine_state) (s2:machine_state)
  = s1.ms_ok /\ s2.ms_ok /\ constTimeInvariant ts s1 s2 /\
    (let r1 = taint_eval_code code fuel s1 in
     let r2 = taint_eval_code code fuel s2 in
     Some? r1 /\ Some? r2 /\ (Some?.v r1).ms_ok /\ (Some?.v r2).ms_ok)

let is_explicit_leakage_free_rhs (code:code) (fuel:nat)
                                 (ts:analysis_taints) (ts':analysis_taints) (s1:machine_state) (s2:machine_state)
  = let r1 = taint_eval_code code fuel s1 in
    let r2 = taint_eval_code code fuel s2 in
    Some? r1 /\ Some? r2 /\ publicValuesAreSame ts' (Some?.v r1) (Some?.v r2)

let isExplicitLeakageFreeGivenStates (code:code) (fuel:nat)
                                     (ts:analysis_taints) (ts':analysis_taints) (s1:machine_state) (s2:machine_state)
  = is_explicit_leakage_free_lhs code fuel ts ts' s1 s2 ==> is_explicit_leakage_free_rhs code fuel ts ts' s1 s2

let isExplicitLeakageFree (code:code) (ts:analysis_taints) (ts':analysis_taints) =
  forall s1 s2 fuel.
    isExplicitLeakageFreeGivenStates code fuel ts ts' s1 s2

let isLeakageFree (code:code) (ts:analysis_taints) (ts':analysis_taints) =
    isConstantTime code ts
  /\ isExplicitLeakageFree code ts ts'
