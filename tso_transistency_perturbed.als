// Automated Synthesis of Comprehensive Memory Model Litmus Test Suites
// Daniel Lustig, Andrew Wright, Alexandros Papakonstantinou, Olivier Giroux
// ASPLOS 2017
//
// Copyright (c) 2017, NVIDIA Corporation.  All rights reserved.
//
// This file is licensed under the BSD-3 license.  See LICENSE for details.

// Total Store Ordering (TSO)

////////////////////////////////////////////////////////////////////////////////
// =Perturbations=

abstract sig PTag {}

one sig RE extends PTag {} // Remove Event
one sig RD extends PTag {} // Remove Dependency (RMW)

fun no_p : PTag->univ { // no_p - constant for no perturbation
  (PTag->univ) - (PTag->univ)
}

////////////////////////////////////////////////////////////////////////////////
// =TSO memory model=

pred sc_per_loc[p: PTag->univ] {
  acyclic[rf_p[p] + co_p[p] + fr_p[p] + po_loc_p[p]]
}
pred rmw_atomicity[p: PTag->univ] {
  no (fr_p[p]).(co_p[p]) & rmw_p[p]
}
pred causality[p: PTag->univ] {
  acyclic[rfe_p[p] + co_p[p] + fr_p[p] + ppo_p[p] + fence_p[p]]
}
pred ptw_com_preserved[p: PTag->univ] {
  acyclic[rfi_p[p] + coi_p[p] + fri_p[p] + ptwSource_p[p]]
}
pred pte_access_order_preserved[p: PTag->univ] {
  acyclic[fr_va_p[p] + trans_po_p[p] + remap_p[p]]
}

pred transistency_model[p: PTag->univ] {
  ptw_com_preserved[p]
  pte_access_order_preserved[p]
  tso_p[p]
}

pred tso_p[p: PTag->univ] {
  sc_per_loc[p]
  rmw_atomicity[p]
  causality[p]
}

fun fence_p[p: PTag->univ] : MemoryEvent->MemoryEvent {
  ((MemoryEvent - p[RE]) <: ^po :> (Fence - p[RE])).(^po :> (MemoryEvent - p[RE]))
}
fun ppo_p[p: PTag->univ] : MemoryEvent->MemoryEvent {
  ((MemoryEvent - p[RE]) <: ^po :> (MemoryEvent - p[RE]))
  -
  ((Write - ((Read - p[RD]).rmw))->((Read - p[RD]) - Write.~rmw))
}
fun ptwSource_p[p: PTag->univ] : MemoryEvent->MemoryEvent {
  ((MemoryEvent - p[RE]) <: go :> (ptwalk - p[RE])).(ptw :> (MemoryEvent - go.ptwalk - p[RE]))
}
fun remap_p[p: PTag->univ] : MemoryEvent->Fence {
  (pte_map.pte_mapping - p[RE]) <: remap :> (INVLPG - p[RE])
}
fun trans_po_p[p: PTag->univ] : Event->Event {
  (Event - p[RE]) <: ^po :> (Event - p[RE])
}

////////////////////////////////////////////////////////////////////////////////
// =Basic model of memory=

sig VirtualAddress {
    pte: lone PageTableEntry
}

sig PageTableEntry {
    map: one VirtualAddress
}

// PTE mapping restrictions
fact one_va_per_pte_map { map.~map in iden and ~map.map in iden }

fact no_pte_for_va_in_pte { no PageTableEntry.map.pte }

fact one_va_per_pte { pte.~pte in iden and ~pte.pte in iden }

sig Thread { start: one {Read + Write + Fence} } // we are using one thread per core so this is the same as Core

abstract sig Event { po: lone Event }

abstract sig MemoryEvent extends Event {
  address: one VirtualAddress,
  dep: set MemoryEvent,
  go: set {ptwalk + dirtybit}
}

abstract sig ReadOps extends MemoryEvent { }

sig Read extends ReadOps {
  rmw: lone Write,
  r_fr_pa: set Write  // R->W for R reading from some PA as W writing mapping of new VA to same PA
}

abstract sig WriteOps extends MemoryEvent { 
  rf: set ReadOps,                               
  co: set WriteOps
}

sig Write extends WriteOps {
  r_rf_pa: set Read,  // W->R for R reading from the mapping written by W
  w_rf_pa: set Write, // W->W for W writing to data at mapping written by W
  co_pa: set Write,   // W->W for W writing mapping to same PA as W writing mapping
  w_fr_pa: set Write, // W->W for W writing to some PA as W writing mapping of new VA to same PA
  pte_map: lone pte_mapping,  // does this write to data or a PTE
  remap: set INVLPG   // set of INVLPG pointed to by a PTE Write
}

fun rf_pa : Event->Event { r_rf_pa + w_rf_pa }
fun fr_pa : Event->Event { r_fr_pa + w_fr_pa }

// sig for denoting a PTE Write access
one sig pte_mapping { }

abstract sig Fence extends Event {}

// Access Types

sig ptwalk extends ReadOps {
    ptw: set {Read + Write}
}
sig dirtybit extends WriteOps { }
sig MFENCE extends Fence { }
sig INVLPG extends Fence {
    page: one VirtualAddress
}

fun ghost : Event {ptwalk + dirtybit}

fun rmwinstr : Event { rmw.Write + Read.rmw }

////////////////////////////////////////////////////////////////////////////////
// =Constraints on basic model of memory=

// All communication is via accesses to the same address
fact { all disj e, e': Event | e->e' in com => SamePhysicalAddress[e, e'] }

// Program order is sane
fact { acyclic[po] }
fact po_prior { all e: Event | lone e.~po }
fact { all e: Event | one t: Thread | t->e in {start.*po + start.*po.go} }
fun po_loc_normal : MemoryEvent->MemoryEvent { ^po & {~rf_pa.*co_pa.rf_pa + ~rf_pa.~(*co_pa).rf_pa + ~rf_pa.*co_pa.~fr_pa + ~rf_pa.~(*co_pa).~fr_pa
                        + fr_pa.*co_pa.rf_pa + fr_pa.~(*co_pa).rf_pa + fr_pa.*co_pa.~fr_pa + fr_pa.~(*co_pa).~fr_pa
                        + ~(~rf_pa.*co_pa.rf_pa + ~rf_pa.~(*co_pa).rf_pa + ~rf_pa.*co_pa.~fr_pa + ~rf_pa.~(*co_pa).~fr_pa
                        + fr_pa.*co_pa.rf_pa + fr_pa.~(*co_pa).rf_pa + fr_pa.*co_pa.~fr_pa + fr_pa.~(*co_pa).~fr_pa)
                        + {Read + Write - Write.rf_pa - fr_pa.Write - pte_map.pte_mapping} <: address.~address :> {Read + Write - Write.rf_pa - fr_pa.Write - pte_map.pte_mapping} } }
fun po_loc_pte : MemoryEvent->MemoryEvent { {^po + ^po.go + ~go.^po.go} & {{pte_map.pte_mapping + ghost} <: address.~address :> {pte_map.pte_mapping + ghost}} }
fun po_loc : MemoryEvent->MemoryEvent { po_loc_normal + po_loc_pte }


// Ghost not part of program
fact no_po_ghost { no g: ghost | g in { Event.po + po.Event } }

// Dependencies go from Reads to Reads or Writes
fact { dep in Read <: ^po }

// co is a per-address total order
fact co_transitive { transitive[co] }
fact co_total_pte { all a: VirtualAddress | total[co, a.~address :> (dirtybit + pte_map.pte_mapping)] }
/*fact co_total_pte { all w: WriteOps | w in ghost or (IsNormal[w] and ChangesPTE[w]) => 
                    total[co, address.(w.address) & WriteOps] }*/
fact co_total_pa { all w: Write | ChangesPTE[w] => 
                    total[co, w.*co_pa.w_rf_pa + w_fr_pa.(w.*co_pa) + w.~(*co_pa).w_rf_pa + w_fr_pa.(w.~(*co_pa))] }
fact co_total_init { all w: Write | IsNormalReadWrite[w] and DataFromInitialStateAtPTE[w] and not w in fr_pa.Write =>
                    total[co, (address.(w.address) - Write.w_rf_pa) & WriteOps] }

fact co_pa_transitive { transitive[co_pa] }
fact co_pa_total { acyclic[co_pa] }
fact com_pa_total { acyclic[com_pa] }

// Each read sources from at most one write
// (could be zero if sourcing from the initial condition)
fact { rf.~rf in iden }
// fr is defined in the standard way
fun fr : ReadOps->WriteOps {
  ~rf.^co
  +
  // also include reads that read from the initial state of PA
  ((Read - (Write.rf)) <:  (~r_rf_pa.*co_pa.w_rf_pa + ~r_rf_pa.~(*co_pa).w_rf_pa + ~r_rf_pa.*co_pa.~w_fr_pa + ~r_rf_pa.~(*co_pa).~w_fr_pa + r_fr_pa.*co_pa.w_rf_pa + r_fr_pa.~(*co_pa).w_rf_pa + r_fr_pa.*co_pa.~w_fr_pa + r_fr_pa.~(*co_pa).~w_fr_pa) :> (Write - pte_map.pte_mapping))
  +
  // also includes reads that read from the initial state of PA before the mapping is written to
  ((Read - Write.rf - r_fr_pa.Write - Write.r_rf_pa) <: (address.~address) :> (Write - pte_map.pte_mapping - w_fr_pa.Write - Write.w_rf_pa))
  +
  // also includes the instructions accessing the PTE
  ((ptwalk - (WriteOps.rf)) <: ((address.pte).~(address.pte)) :> WriteOps)
}

fact min_r_fr_pa {
  {~r_rf_pa.co_pa
  +
  ((Read - (Write.r_rf_pa)) <: (fr.~w_rf_pa.*co_pa) :> Write)}
  in r_fr_pa
}

fact min_w_fr_pa {                          
  {~w_rf_pa.co_pa
  +
  ((Write - (Write.w_rf_pa) - pte_map.pte_mapping) <: (rf.~r_rf_pa.*co_pa + co.~w_rf_pa.*co_pa) :> Write)}
  in w_fr_pa
}

fun r_fr_va : Read->Write {
    (Read <: (~r_rf_pa.co) :> Write)
    +
    ((Read - Write.r_rf_pa) <: (address.~(address.pte.map)) :> Write)
}

fun w_fr_va : Write->Write {
    (Write <: (~w_rf_pa.co) :> Write)
    +
    ((Write - Write.w_rf_pa) <: (address.~(address.pte.map)) :> Write)
}

fun fr_va : Event->Write { r_fr_va + w_fr_va }

// same virtual address across fr_va (but different physical address)
fact { all disj e, e': Event | e->e' in {r_fr_va.r_rf_pa + r_fr_va.w_rf_pa + w_fr_va.r_rf_pa + w_fr_va.w_rf_pa} => SameVirtualAddress[e, e'] and !SamePhysicalAddress[e, e'] }

// one end of _pa and _va edges must be PTE Write
fact { all w: Write | w in (Read.~r_rf_pa + Write.~w_rf_pa + Write.co_pa + Write.~co_pa + Read.r_fr_pa + Write.w_fr_pa + Read.r_fr_va + Write.w_fr_va) => ChangesPTE[w] }

// ghost instructions and PTE writes must access PTE
fact { all e: Event | (ChangesPTE[e] or (e in ghost)) => some e.address.pte }

// normal instructions only access data
fact { all e: Event | IsNormalReadWrite[e] => no e.address.pte }

// no remapping between _pa edge events
fact { all w: pte_map.pte_mapping | all e: Event | w->e in rf_pa and SameThread[w, e] => w->e in ^po and !(some w': pte_map.pte_mapping | e->w' in fr_va and e.address = w'.address.pte.map and w->w' in ^po and w'->e in ^po) }

// same VA for same PTE Write source
fact { all disj e, e': Event | SameSourcingPTEWrite[e, e'] => SameVirtualAddress[e, e'] }

fact lone_source_write_pte { rf_pa.~rf_pa in iden }

fact rf_pa_same_pte { all e: Event | e in Write.rf_pa => e.address = e.~rf_pa.address.pte.map }

// all initial accesses to some PA should have same fr_pa edges
fact { all disj e, e': Event | SameVirtualAddress[e, e'] and DataFromInitialStateAtPTE[e] and DataFromInitialStateAtPTE[e'] and (e in fr_pa.Write or e' in fr_pa.Write) => e->e' in fr_pa.~fr_pa }

// all writes to same PA should be in ^co
fact { all disj w, w': WriteOps | SamePhysicalAddress[w, w'] => (w->w' in ^co or w'->w in ^co)}

// all PTE writes for same PA should be connected via co_pa
fact { rf_pa.fr_pa in co_pa }

// PTE maps different VA in fr_pa edges
fact { all e: Event | all w: Write | e->w in fr_pa => not e.address = w.address.pte.map }

// same VA diff PA if separated by fr_va edge
fact { all disj e, e': MemoryEvent | SameVirtualAddress[e, e'] and some e.fr_va and ProgramOrder[e.fr_va, e'] => !SameSourcingPTEWrite[e, e'] }

// fr_va means PTE mappings can't be in co_pa
fact { all e: Event | all disj w, w': Write | e->w in {fr_pa + ~rf_pa} and e->w' in fr_va => not w->w' in {co_pa + ~co_pa} }

fact no_pte_write_between_rf_pa { all e: Event | e in Write.rf_pa and ProgramOrder[rf_pa.e, e] => !(some w: Write | ChangesPTE[w] and ProgramOrder[rf_pa.e, w] and ProgramOrder[w, e] and w.address.pte.map = e.address) }

// PTE Write source can be on same or other thread
pred rf_pa_restrict { all e: MemoryEvent | all w: Write | ChangesPTE[w] and w.address.pte.map = e.address and ProgramOrder[w, e] and
                                      !(some w': Write | ChangesPTE[w'] and w'.address.pte.map = e.address and ProgramOrder[w, w'] and ProgramOrder[w', e]) =>
                                      (w->e in rf_pa or !SameThread[e, rf_pa.e]) }

// rmws

// RMW pairs are sane and overlap with dep
fact { rmw in po & dep & address.~address }

fact rmw_same_pa { all disj e, e': Event | e->e' in rmw => SamePhysicalAddress[e, e'] }

fact rmw_writes { all w: Write | w in Read.rmw => IsNormalReadWrite[w] }

// ghost instructions

// ghost instructions are on the same thread as the triggering instruction, even though they are not connected by po edges
fact { all g: ghost | SameThread[g, GhostInstructionSource[g]] }

fact { all g: ghost | one GhostInstructionSource[g] }

// normal read or write in each go source
fact { all e: Event | e in go.Event => IsNormalReadWrite[e] }

// ghost at each go sink
fact { all e: Event | e in Event.go => e in ghost }

// only normal instructions get ghost instructions
fact { all g: ghost | IsNormalReadWrite[GhostInstructionSource[g]] }

// ghost instructions access correct PTE
fact { all g: ghost | g.address.pte.map = GhostInstructionSource[g].address }

fact { all g: ghost | GhostInstructionSource[g] in Write.rf_pa => g.address = (rf_pa.(GhostInstructionSource[g])).address }

fact ptwalk_ordering { all i: ptwalk | i in Event.go }

// ptwalk only for normal instructions
fact { all e: ptwalk.ptw | IsNormalReadWrite[e] }

// FIXME make sure i include acyclic ptw + po + go to transistency model or something
// FIXME also add acyclic go + com or something to transistency model
fact ptwalk_necessary { all e: Event | IsNormalReadWrite[e] =>
                            some p: ptwalk | ((SameThread[GhostInstructionSource[p], e]
                            and SameSourcingPTEWrite[e, GhostInstructionSource[p]])
                            or e = GhostInstructionSource[p]) 
                            and p->e in ptw }

// source of ptwalk also has ptw edge from that ptwalk
fact { all e: Event | all p: ptwalk | e->p in go => p->e in ptw }

fact lone_source_ptw { ptw.~ptw in iden }

fact ptw_address { all e: ptwalk.ptw | (ptw.e).address.pte.map = e.address }

// dirty bit updates occur for all Writes and nowhere else
fact dirty_bit_ordering { all d: dirtybit | d in {Write - pte_map.pte_mapping}.go }

fact dirty_for_every_write { all w: Write | IsNormalReadWrite[w] =>
                            (one d: dirtybit | d in w.go) }

fact one_type_of_write { all w: Write | IsNormalReadWrite[w] or (!IsNormalReadWrite[w] and ChangesPTE[w]) }

// INVLPG

// INVLPG on all threads after PTE Write
fact { all w: pte_map.pte_mapping | all t: Thread | some i: INVLPG | OnThread[i, t] and w.address.pte.map = i.page and i in w.remap }
fact { all w: pte_map.pte_mapping | some i: INVLPG | w.po = i and w.address.pte.map = i.page }
fact { no {~remap.remap & ^po} }

fact lone_source_remap { remap.~remap in iden }

// remap for PTE Writes only
fact { all w: Write | w in remap.INVLPG => ChangesPTE[w] }

// FIXME acyclic fr_va + po + remap or something for transistency model
// ptw edges for VA can't cross INVLPG
fact { all e: MemoryEvent | e.address in INVLPG.page and e in {INVLPG.^po + ^po.INVLPG} and GhostInstructionSource[ptw.e] in {INVLPG.^po + ^po.INVLPG} =>
                                        some i: INVLPG | SameVirtualAddress[e, i] and ((ProgramOrder[e, i] and ProgramOrder[GhostInstructionSource[ptw.e], i]) or (ProgramOrder[i, e] and ProgramOrder[i, GhostInstructionSource[ptw.e]])) }

fact invlpg_addr { all i: INVLPG | no i.page.pte and i.page in PageTableEntry.map }

// only interesting INVLPG
fact invlpg_with_purpose { all i: INVLPG - Write.remap | some e: MemoryEvent | ProgramOrder[i, e] and SameVirtualAddress[i, e] }

// no thread with just INVLPG
fact invlpg_plus_more { all i: INVLPG | some e: MemoryEvent | ProgramOrder[i, e] or ProgramOrder[e, i] }

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// =Model of memory, under perturbation=

// po is not transitive
fun po_t[p: PTag->univ] : Event->Event { (Event - p[RE]) <: ^po :> (Event - p[RE]) }
fun po_p[p: PTag->univ] : Event->Event { po_t[p] - (po_t[p]).(po_t[p]) }

// po_loc is already transitive
fun po_loc_p[p: PTag->univ] : MemoryEvent->MemoryEvent { (MemoryEvent - p[RE]) <: po_loc :> (MemoryEvent - p[RE]) }

// dep is not transitive
fun dep_p[p: PTag->univ] : MemoryEvent->MemoryEvent {
  (Read - p[RE] - p[RD]) <: *(dep :> p[RE]).dep :> (MemoryEvent - p[RE])
}

fun rf_p[p: PTag->univ] : WriteOps->ReadOps { (WriteOps - p[RE]) <: rf :> (ReadOps - p[RE]) }
fun co_p[p: PTag->univ] : WriteOps->WriteOps { (WriteOps - p[RE]) <: co :> (WriteOps - p[RE]) }
//fun fr_p[p: PTag->univ] : ReadOps->WriteOps { (ReadOps - p[RE]) <: fr :> (WriteOps - p[RE]) }
fun fr_p[p: PTag->univ] : ReadOps->WriteOps {
  ( ~(rf_p[p]).^(co_p[p]) )
  +
  ( (Read-(Write.rf)-p[RE]) <: (~r_rf_pa.*co_pa.w_rf_pa + ~r_rf_pa.~(*co_pa).w_rf_pa + ~r_rf_pa.*co_pa.~w_fr_pa + ~r_rf_pa.~(*co_pa).~w_fr_pa + r_fr_pa.*co_pa.w_rf_pa + r_fr_pa.~(*co_pa).w_rf_pa + r_fr_pa.*co_pa.w_fr_pa + r_fr_pa.~(*co_pa).w_fr_pa) :> (Write - pte_map.pte_mapping - p[RE]) )
  +
  ( (Read - Write.rf - r_fr_pa.Write - Write.r_rf_pa - p[RE]) <: (address.~address) :> (Write - pte_map.pte_mapping - w_fr_pa.Write - Write.w_rf_pa - p[RE]) )
  +
  ((ReadOps - (WriteOps.rf) - p[RE]) <: ((address.pte).~(address.pte)) :> (WriteOps - p[RE]))
}
fun rmw_p[p: PTag->univ] : Read->Write { (Read - p[RE] - p[RD]) <: rmw :> (Write - p[RE]) }
fun fr_va_p[p: PTag->univ] : MemoryEvent->Write { (MemoryEvent - p[RE]) <: fr_va :> (Write - p[RE]) }

////////////////////////////////////////////////////////////////////////////////
// =Shortcuts=

fun same_thread [rel: Event->Event] : Event->Event {
  rel & ( iden + ^po + ~^po + ^po.go + ~^po.go )
}

fun com[] : MemoryEvent->MemoryEvent { rf + fr + co }
fun rfi[] : MemoryEvent->MemoryEvent { same_thread[rf] }
fun rfe[] : MemoryEvent->MemoryEvent { rf - rfi[] }
fun fri[] : MemoryEvent->MemoryEvent { same_thread[fr] }
fun fre[] : MemoryEvent->MemoryEvent { fr - fri }
fun coi[] : MemoryEvent->MemoryEvent { same_thread[co] }
fun coe[] : MemoryEvent->MemoryEvent { co - coi }
fun com_pa[] : MemoryEvent->MemoryEvent { rf_pa + fr_pa + co_pa }

fun com_p[p: PTag->univ] : MemoryEvent->MemoryEvent { rf_p[p] + fr_p[p] + co_p[p] }
fun rfi_p[p: PTag->univ] : MemoryEvent->MemoryEvent { same_thread[rf_p[p]] }
fun rfe_p[p: PTag->univ] : MemoryEvent->MemoryEvent { rf_p[p] - rfi_p[p] }
fun fri_p[p: PTag->univ] : MemoryEvent->MemoryEvent { same_thread[fr_p[p]] }
fun fre_p[p: PTag->univ] : MemoryEvent->MemoryEvent { fr_p[p] - fri_p[p] }
fun coi_p[p: PTag->univ] : MemoryEvent->MemoryEvent { same_thread[co_p[p]] }
fun coe_p[p: PTag->univ] : MemoryEvent->MemoryEvent { co_p[p] - coi_p[p] }

////////////////////////////////////////////////////////////////////////////////
// =Alloy helpers=

pred transitive[rel: Event->Event]        { rel.rel in rel }
pred irreflexive[rel: Event->Event]        { no iden & rel }
pred acyclic[rel: Event->Event]            { irreflexive[^rel] }
pred total[rel: Event->Event, bag: Event] {
  all disj e, e': bag | e->e' in rel + ~rel
  acyclic[rel]
}

////////////////////////////////////////////////////////////////////////////////
// =Alloy predicates and functions=

pred OnThread[e: Event, t: Thread] { e in t.start.*po }
pred DataFromInitialStateAtPTE[e: Event] { e in {Read + Write - pte_map.pte_mapping - Event.rf_pa} }
pred DataFromInitialStateAtPA[ro: ReadOps] { ro in {ReadOps - WriteOps.rf} }
pred IsAnyWrite[e: Event] { e in WriteOps }
pred IsNormalReadWrite[e: Event] { (e in Write and !ChangesPTE[e]) or (e in Read) } // includes RMW
pred IsNormal[e: Event] { e in (Read + Write - rmwinstr) }
pred IsINVLPG[e: Event] { e in INVLPG }
pred SameThread[e: Event, e': Event] { (e->e' in ^po + ^~po) or (e->e' in go + ~go) or (e->e' in ^po.go + ^~po.go + ~go.^po + ~go.^~po) }
pred SameEvent[e: Event, e': Event] { e->e' in iden }
pred ProgramOrder[e: Event, e': Event] { e->e' in ^po }

pred SamePhysicalAddress[e: Event, e': Event] {
    !IsINVLPG[e] and !IsINVLPG[e'] and
    (SameEvent[e, e'] or
    ( ( IsNormalReadWrite[e] =>
        ( IsNormalReadWrite[e'] and
            ((e->e' in ( ~rf_pa.*co_pa.rf_pa + ~rf_pa.~(*co_pa).rf_pa + ~rf_pa.*co_pa.~fr_pa + ~rf_pa.~(*co_pa).~fr_pa
                        + fr_pa.*co_pa.rf_pa + fr_pa.~(*co_pa).rf_pa + fr_pa.*co_pa.~fr_pa + fr_pa.~(*co_pa).~fr_pa
                        + ~(~rf_pa.*co_pa.rf_pa + ~rf_pa.~(*co_pa).rf_pa + ~rf_pa.*co_pa.~fr_pa + ~rf_pa.~(*co_pa).~fr_pa
                        + fr_pa.*co_pa.rf_pa + fr_pa.~(*co_pa).rf_pa + fr_pa.*co_pa.~fr_pa + fr_pa.~(*co_pa).~fr_pa) )) or
            (DataFromInitialStateAtPTE[e] and DataFromInitialStateAtPTE[e'] and SameVirtualAddress[e, e']))))
    and
    ( ChangesPTE[e] =>   // PTE Write
        ( ChangesPTE[e'] and  // normal Write
            e->e' in address.~address ) or
        ( e' in ghost and
            e->e' in address.~address ) )
    and
    ( e in ghost =>
        ( ChangesPTE[e'] and  // normal Write
            e->e' in address.~address ) or
        ( e' in ghost and
            e->e' in address.~address ) ) ) )
}

pred SameVirtualAddress[e: Event, e': Event] { 
    (!IsINVLPG[e] and !IsINVLPG[e'] => e->e' in address.~address) and
    (IsINVLPG[e] and !IsINVLPG[e'] => e->e' in page.~address) and
    (!IsINVLPG[e] and IsINVLPG[e'] => e->e' in address.~page) and
    (IsINVLPG[e] and IsINVLPG[e'] => e->e' in page.~page)
}

pred SameSourcingPTEWrite[e: Event, e': Event] {
    IsNormalReadWrite[e] and IsNormalReadWrite[e'] and
    (not SameEvent[e, e']) and (
        (DataFromInitialStateAtPTE[e] and DataFromInitialStateAtPTE[e'] and e.address = e'.address)
        or
        (!DataFromInitialStateAtPTE[e] and !DataFromInitialStateAtPTE[e'] and (rf_pa.e) = (rf_pa.e'))
    )
}

pred ChangesPTE[e: Event] {
    e in Write and e.pte_map = pte_mapping
}

fun GhostInstructionSource[g: Event] : Event {
    go.g
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// =Constraints on the search space=

fact {
  (all a: VirtualAddress | (no a.pte => some (a.~address) :> Write))
  or
  (some a: pte.map.VirtualAddress | ((some (a.~address) :> Write) and (some (a.~address) :> ghost)))
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// =Perturbation auxiliaries=

let interesting_not_axiom[axiom] {
  not axiom[no_p]

  // All events must be relevant and minimal
  all e: Event - ghost - Write.remap | transistency_model[RE->(e + e.rmw + e.~rmw + e.go + e.remap)]/*
  all e: ptwalk | tso_p[RE->e]*/
  all e: Read | transistency_model[RD->e] or no e.dep
}

////////////////////////////////////////////////////////////////////////////////

// 4 instructions min
run sc_per_loc {
  interesting_not_axiom[sc_per_loc]
} for 4

// 7 instructions min
run rmw_atomicity {
  interesting_not_axiom[rmw_atomicity]
} for 7

// 5 instructions min
run causality {
  interesting_not_axiom[causality]
} for 5

// 4 instructions min
run pte_access_order_preserved {
  interesting_not_axiom[pte_access_order_preserved]
} for 4

// 4 instructions min
run ptw_com_preserved {
  interesting_not_axiom[ptw_com_preserved]
} for 4

run union {
  interesting_not_axiom[sc_per_loc]
  or
  interesting_not_axiom[rmw_atomicity]
  or
  interesting_not_axiom[causality]
  or
  interesting_not_axiom[pte_access_order_preserved]
  or
  interesting_not_axiom[ptw_com_preserved]
} for 4