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
pred tlb_causality[p: PTag->univ] {
  acyclic[rf_p[p] + co_p[p] + fr_p[p] + ptw_source_p[p]]
}
pred invlpg[p: PTag->univ] {
  acyclic[fr_va_p[p] + trans_po_p[p] + remap_p[p]]
}

pred transistency_model[p: PTag->univ] {
  tlb_causality[p]
  invlpg[p]
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
fun ptw_source_p[p: PTag->univ] : MemoryEvent->MemoryEvent {
  ((MemoryEvent - p[RE]) <: ghost :> (ptwalk - p[RE])).(rf_ptw :> (MemoryEvent - ghost.ptwalk - p[RE]))
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

sig Thread { start: one {Read + Write + INVLPG} } // we are using one thread per core so this is the same as Core

abstract sig Event { po: lone Event }

abstract sig MemoryEvent extends Event {
  address: one VirtualAddress,
  dep: set MemoryEvent,
  ghost: set {ptwalk + dirtybit}
}

abstract sig ReadOps extends MemoryEvent { }

sig Read extends ReadOps {
  rmw: lone Write,
  r_fr_pa: set Write  // R->W for R reading from some PA p via VA v where v->p existed before v'->p which was created by W
}

abstract sig WriteOps extends MemoryEvent { 
  rf: set ReadOps,                               
  co: set WriteOps
}

sig Write extends WriteOps {
  r_rf_pa: set Read,  // W->R for R reading from some PA p via VA v where v->p was created by W
  w_rf_pa: set Write, // W->W' for W' writing to some PA p via VA v where v->p was created by W
  co_pa: set Write,   // W->W' for W writing mapping v->p before W' writing mapping v'->p for same PA p
  w_fr_pa: set Write, // W'->W for W' writing to some PA p via VA v where v->p existed before v'->p which was created by W
  pte_map: lone pte_mapping,  // writing to data or a PTE
  remap: set INVLPG   // set of INVLPG pointed to by a PTE Write
}

fun rf_pa : Event->Event { r_rf_pa + w_rf_pa }
fun fr_pa : Event->Event { r_fr_pa + w_fr_pa }

// sig for denoting a PTE Write access
one sig pte_mapping { }

abstract sig Fence extends Event {}

// Access Types

sig ptwalk extends ReadOps {
    rf_ptw: set {Read + Write}
}
sig dirtybit extends WriteOps { }
sig MFENCE extends Fence { }
sig INVLPG extends Fence {
    page: one VirtualAddress
}

fun ghostinstr : Event {ptwalk + dirtybit}

fun rmwinstr : Event { rmw.Write + Read.rmw }

// All normal instruction pairs accessing the same physical address
fun same_pa_normal : Event->Event {
  ~rf_pa.*co_pa.rf_pa + ~rf_pa.~(*co_pa).rf_pa + ~rf_pa.*co_pa.~fr_pa + ~rf_pa.~(*co_pa).~fr_pa
  + fr_pa.*co_pa.rf_pa + fr_pa.~(*co_pa).rf_pa + fr_pa.*co_pa.~fr_pa + fr_pa.~(*co_pa).~fr_pa
  + ~(~rf_pa.*co_pa.rf_pa + ~rf_pa.~(*co_pa).rf_pa + ~rf_pa.*co_pa.~fr_pa + ~rf_pa.~(*co_pa).~fr_pa
  + fr_pa.*co_pa.rf_pa + fr_pa.~(*co_pa).rf_pa + fr_pa.*co_pa.~fr_pa + fr_pa.~(*co_pa).~fr_pa)
}

////////////////////////////////////////////////////////////////////////////////
// =Constraints on basic model of memory=

// All communication is via accesses to the same address
fact { all disj e, e': Event | e->e' in com => SamePhysicalAddress[e, e'] }

// Program order is sane
fact { acyclic[po] }
fact po_prior { all e: Event | lone e.~po }
fact { all e: Event | one t: Thread | t->e in {start.*po + start.*po.ghost} }
fun po_loc_normal : MemoryEvent->MemoryEvent { ^po & { same_pa_normal
                        + {Read + Write - Write.rf_pa - fr_pa.Write - pte_map.pte_mapping} <: address.~address :> {Read + Write - Write.rf_pa - fr_pa.Write - pte_map.pte_mapping} } }
fun po_loc_pte : MemoryEvent->MemoryEvent { {^po + ^po.ghost + ~ghost.^po.ghost} & {{pte_map.pte_mapping + ghostinstr} <: address.~address :> {pte_map.pte_mapping + ghostinstr}} }
fun po_loc : MemoryEvent->MemoryEvent { po_loc_normal + po_loc_pte }


// Ghost not part of program
fact no_po_ghost { no g: ghostinstr | g in { Event.po + po.Event } }

// Dependencies go from Reads to Reads or Writes
fact { dep in Read <: ^po }

// co is a per-address total order
fact co_transitive { transitive[co] }
fact co_total_pte { all a: VirtualAddress | total[co, a.~address :> (dirtybit + pte_map.pte_mapping)] }
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
fact { all e: Event | (ChangesPTE[e] or (e in ghostinstr)) => some e.address.pte }

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
fact { all g: ghostinstr | SameThread[g, GhostInstructionSource[g]] }

fact { all g: ghostinstr | one GhostInstructionSource[g] }

// normal read or write in each ghost source
fact { all e: Event | e in ghost.Event => IsNormalReadWrite[e] }

// ghostinstr at each ghost sink
fact { all e: Event | e in Event.ghost => e in ghostinstr }

// only normal instructions get ghost instructions
fact { all g: ghostinstr | IsNormalReadWrite[GhostInstructionSource[g]] }

// ghost instructions access correct PTE
fact { all g: ghostinstr | g.address.pte.map = GhostInstructionSource[g].address }

fact { all g: ghostinstr | GhostInstructionSource[g] in Write.rf_pa => g.address = (rf_pa.(GhostInstructionSource[g])).address }

fact ptwalk_ordering { all i: ptwalk | i in Event.ghost }

// ptwalk only for normal instructions
fact { all e: ptwalk.rf_ptw | IsNormalReadWrite[e] }

fact ptwalk_necessary { all e: Event | IsNormalReadWrite[e] =>
                            some p: ptwalk | ((SameThread[GhostInstructionSource[p], e]
                            and SameSourcingPTEWrite[e, GhostInstructionSource[p]])
                            or e = GhostInstructionSource[p]) 
                            and p->e in rf_ptw }

// source of ptwalk also has rf_ptw edge from that ptwalk
fact { all e: Event | all p: ptwalk | e->p in ghost => p->e in rf_ptw }

fact lone_source_ptw { rf_ptw.~rf_ptw in iden }

fact ptw_address { all e: ptwalk.rf_ptw | (rf_ptw.e).address.pte.map = e.address }

// dirty bit updates occur for all Writes and nowhere else
fact dirty_bit_ordering { all d: dirtybit | d in {Write - pte_map.pte_mapping}.ghost }

fact dirty_for_every_write { all w: Write | IsNormalReadWrite[w] =>
                            (one d: dirtybit | d in w.ghost) }

fact one_type_of_write { all w: Write | IsNormalReadWrite[w] or (!IsNormalReadWrite[w] and ChangesPTE[w]) }

// INVLPG

// INVLPG on all threads after PTE Write
fact { all w: pte_map.pte_mapping | all t: Thread | some i: INVLPG | OnThread[i, t] and w.address.pte.map = i.page and i in w.remap }
fact { all w: pte_map.pte_mapping | some i: INVLPG | w.po = i and w.address.pte.map = i.page }
fact { no {~remap.remap & ^po} }

fact lone_source_remap { remap.~remap in iden }

// remap for PTE Writes only
fact { all w: Write | w in remap.INVLPG => ChangesPTE[w] }

// rf_ptw edges for VA can't cross INVLPG
fact { all e: MemoryEvent | e.address in INVLPG.page and e in {INVLPG.^po + ^po.INVLPG} and GhostInstructionSource[rf_ptw.e] in {INVLPG.^po + ^po.INVLPG} =>
                                        some i: INVLPG | SameVirtualAddress[e, i] and ((ProgramOrder[e, i] and ProgramOrder[GhostInstructionSource[rf_ptw.e], i]) or (ProgramOrder[i, e] and ProgramOrder[i, GhostInstructionSource[rf_ptw.e]])) }

fact invlpg_addr { all i: INVLPG | no i.page.pte and i.page in PageTableEntry.map }

// only interesting INVLPG
fact invlpg_with_purpose { all i: INVLPG - Write.remap | some e: MemoryEvent | ProgramOrder[i, e] and SameVirtualAddress[i, e] }

// no thread with just INVLPG
fact invlpg_plus_more { all i: Fence | some e: MemoryEvent | ProgramOrder[i, e] or ProgramOrder[e, i] }

// MFENCE

// no MFENCE at end of thread
fact no_mfence_end { MFENCE in po.Event }

// no back-to-back MFENCEs
fact no_btb_mfence { no (MFENCE->MFENCE & po) }

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// =Model of memory, under perturbation=

// po is not transitive
fun po_t[p: PTag->univ] : Event->Event { (Event - p[RE]) <: ^po :> (Event - p[RE]) }

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
  rel & ( iden + ^po + ~^po + ^po.ghost + ~^po.ghost )
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
fun comi_p[p: PTag->univ] : MemoryEvent->MemoryEvent { rfi_p[p] + fri_p[p] + coi_p[p] }

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
pred SameThread[e: Event, e': Event] { (e->e' in ^po + ^~po) or (e->e' in ghost + ~ghost) or (e->e' in ^po.ghost + ^~po.ghost + ~ghost.^po + ~ghost.^~po) }
pred SameEvent[e: Event, e': Event] { e->e' in iden }
pred ProgramOrder[e: Event, e': Event] { e->e' in ^po }

pred SamePhysicalAddress[e: Event, e': Event] {
    !IsINVLPG[e] and !IsINVLPG[e'] and
    (SameEvent[e, e'] or
    ( ( IsNormalReadWrite[e] =>
        ( IsNormalReadWrite[e'] and
            ((e->e' in ( same_pa_normal )) or
            (DataFromInitialStateAtPTE[e] and DataFromInitialStateAtPTE[e'] and SameVirtualAddress[e, e']))))
    and
    ( ChangesPTE[e] =>   // PTE Write
        ( ChangesPTE[e'] and  // normal Write
            e->e' in address.~address ) or
        ( e' in ghostinstr and
            e->e' in address.~address ) )
    and
    ( e in ghostinstr =>
        ( ChangesPTE[e'] and  // normal Write
            e->e' in address.~address ) or
        ( e' in ghostinstr and
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
    ghost.g
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// =Constraints on the search space=

fact {
  (all a: VirtualAddress | (no a.pte => some (a.~address) :> Write))
  or
  (some a: pte.map.VirtualAddress | ((some (a.~address) :> Write) and (some (a.~address) :> ghostinstr)))
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// =Perturbation auxiliaries=

let interesting_not_axiom[axiom] {
  not axiom[no_p]

  // All events must be relevant and minimal
  all e: Event - ghostinstr - Write.remap | transistency_model[RE->(e + e.rmw + e.~rmw + e.ghost + e.remap)]
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
run invlpg {
  interesting_not_axiom[invlpg]
} for 4

// 4 instructions min
run tlb_causality {
  interesting_not_axiom[tlb_causality]
} for 4

pred union {
  interesting_not_axiom[sc_per_loc]
  or
  interesting_not_axiom[rmw_atomicity]
  or
  interesting_not_axiom[causality]
  or
  interesting_not_axiom[invlpg]
  or
  interesting_not_axiom[tlb_causality]
}

// check if synthesized
fact { #Event < 10 }

pred dirtybittest {
  // test bounds
  #Write=1 and
  #Read=1 and
  #MFENCE=0 and
  #INVLPG=0 and
  #ptwalk>=2 and
  #dirtybit>=1 and
  #VirtualAddress=2 and

  // po and com relations
  #po=1 and
  #pte_map=0 and
  #remap=0 and
  #ghost>=3 and
  #rf_ptw>=2 and
  
  // test description
  #Thread=1 and
  (
    some disj w02 : Write |
    some disj r10 : Read |
    some disj p11,p03 : ptwalk |
    some disj d01 : dirtybit |
    w02->r10 in po and
    w02->d01 in ghost and
    w02->p03 in ghost and
    r10->p11 in ghost and
    p03->w02 in rf_ptw and
    p11->r10 in rf_ptw and
    SamePhysicalAddress[d01, p03] and
    SamePhysicalAddress[d01, p11] and
    SamePhysicalAddress[w02, r10] and
    !SamePhysicalAddress[d01, w02]
  )
}
run test_dirtybittest {
  dirtybittest and
  union
} for 5

pred dirtybit2 {
  // test bounds
  #Write=2 and
  #Read=1 and
  #MFENCE=0 and
  #INVLPG=1 and
  #ptwalk>=2 and
  #dirtybit>=1 and
  #VirtualAddress=2 and

  // po and com relations
  #po=3 and
  #pte_map=1 and
  #remap=1 and
  #ghost>=3 and
  #rf_ptw>=2 and
  
  // test description
  #Thread=1 and
  (
    some disj w00,w22 : Write |
    some disj r30 : Read |
    some disj p23,p31 : ptwalk |
    some disj d21 : dirtybit |
    some disj i10 : INVLPG |
    w00 in pte_map.pte_mapping and
    w00->i10 in po and
    i10->w22 in po and
    w22->r30 in po and
    w22->d21 in ghost and
    w22->p23 in ghost and
    r30->p31 in ghost and
    p23->w22 in rf_ptw and
    p31->r30 in rf_ptw and
    w00->i10 in remap and
    SamePhysicalAddress[w00, d21] and
    SamePhysicalAddress[w00, p23] and
    SamePhysicalAddress[w00, p31] and
    SamePhysicalAddress[w22, r30] and
    !SamePhysicalAddress[w00, w22] and
    SameVirtualAddress[i10, w22] and
    SameVirtualAddress[i10, r30]
  )
}
run test_dirtybit2 {
  dirtybit2 and
  union
} for 9

pred dirtybit3 {
  // test bounds
  #Write=2 and
  #Read=1 and
  #MFENCE=0 and
  #INVLPG=1 and
  #ptwalk>=2 and
  #dirtybit>=1 and
  #VirtualAddress=2 and

  // po and com relations
  #po=3 and
  #pte_map=1 and
  #remap=1 and
  #ghost>=3 and
  #rf_ptw>=2 and
  
  // test description
  #Thread=1 and
  (
    some disj w00,w32 : Write |
    some disj r20 : Read |
    some disj p21,p33 : ptwalk |
    some disj d31 : dirtybit |
    some disj i10 : INVLPG |
    w00 in pte_map.pte_mapping and
    w00->i10 in po and
    i10->r20 in po and
    r20->w32 in po and
    r20->p21 in ghost and
    w32->d31 in ghost and
    w32->p33 in ghost and
    p21->r20 in rf_ptw and
    p33->w32 in rf_ptw and
    w00->i10 in remap and
    SamePhysicalAddress[w00, p21] and
    SamePhysicalAddress[w00, d31] and
    SamePhysicalAddress[w00, p33] and
    SamePhysicalAddress[r20, w32] and
    !SamePhysicalAddress[w00, r20] and
    SameVirtualAddress[i10, r20] and
    SameVirtualAddress[i10, w32]
  )
}
run test_dirtybit3 {
  dirtybit3 and
  union
} for 9

pred dirtybit4 {
  // test bounds
  #Write=2 and
  #Read=1 and
  #MFENCE=0 and
  #INVLPG=1 and
  #ptwalk>=2 and
  #dirtybit>=1 and
  #VirtualAddress=2 and

  // po and com relations
  #po=3 and
  #pte_map=1 and
  #remap=1 and
  #ghost>=3 and
  #rf_ptw>=2 and
  
  // test description
  #Thread=1 and
  (
    some disj w00,w32 : Write |
    some disj r20 : Read |
    some disj p21,p33 : ptwalk |
    some disj d31 : dirtybit |
    some disj i10 : INVLPG |
    w00 in pte_map.pte_mapping and
    w00->i10 in po and
    i10->r20 in po and
    r20->w32 in po and
    r20->p21 in ghost and
    w32->d31 in ghost and
    w32->p33 in ghost and
    p21->r20 in rf_ptw and
    p33->w32 in rf_ptw and
    w00->i10 in remap and
    SamePhysicalAddress[w00, p21] and
    SamePhysicalAddress[w00, d31] and
    SamePhysicalAddress[w00, p33] and
    SamePhysicalAddress[r20, w32] and
    !SamePhysicalAddress[w00, r20] and
    SameVirtualAddress[i10, r20] and
    SameVirtualAddress[i10, w32]
  )
}
run test_dirtybit4 {
  dirtybit4 and
  union
} for 9

pred dirtybit5 {
  // test bounds
  #Write=1 and
  #Read=1 and
  #MFENCE=0 and
  #INVLPG=0 and
  #ptwalk>=2 and
  #dirtybit>=1 and
  #VirtualAddress=2 and

  // po and com relations
  #po=1 and
  #pte_map=0 and
  #remap=0 and
  #ghost>=3 and
  #rf_ptw>=2 and
  
  // test description
  #Thread=1 and
  (
    some disj w02 : Write |
    some disj r10 : Read |
    some disj p11,p03 : ptwalk |
    some disj d01 : dirtybit |
    w02->r10 in po and
    w02->d01 in ghost and
    w02->p03 in ghost and
    r10->p11 in ghost and
    p03->w02 in rf_ptw and
    p11->r10 in rf_ptw and
    SamePhysicalAddress[d01, p03] and
    SamePhysicalAddress[d01, p11] and
    SamePhysicalAddress[w02, r10] and
    !SamePhysicalAddress[d01, w02]
  )
}
run test_dirtybit5 {
  dirtybit5 and
  union
} for 5

pred dirtybit6 {
  // test bounds
  #Write=1 and
  #Read=1 and
  #MFENCE=0 and
  #INVLPG=0 and
  #ptwalk>=2 and
  #dirtybit>=1 and
  #VirtualAddress=2 and

  // po and com relations
  #po=1 and
  #pte_map=0 and
  #remap=0 and
  #ghost>=3 and
  #rf_ptw>=2 and
  
  // test description
  #Thread=1 and
  (
    some disj w02 : Write |
    some disj r10 : Read |
    some disj p11,p03 : ptwalk |
    some disj d01 : dirtybit |
    w02->r10 in po and
    w02->d01 in ghost and
    w02->p03 in ghost and
    r10->p11 in ghost and
    p03->w02 in rf_ptw and
    p11->r10 in rf_ptw and
    SamePhysicalAddress[d01, p03] and
    SamePhysicalAddress[d01, p11] and
    SamePhysicalAddress[w02, r10] and
    !SamePhysicalAddress[d01, w02]
  )
}
run test_dirtybit6 {
  dirtybit6 and
  union
} for 5

pred ghosttest {
  // test bounds
  #Write=2 and
  #Read=0 and
  #MFENCE=0 and
  #INVLPG=0 and
  #ptwalk>=0 and
  #dirtybit>=1 and
  #VirtualAddress=4 and

  // po and com relations
  #po=0 and
  #pte_map=0 and
  #remap=0 and
  #ghost>=1 and
  #rf_ptw>=0 and
  
  // test description
  #Thread=2 and
  (
    some disj w10,w00 : Write |
    some disj d01 : dirtybit |
    w00->d01 in ghost and
    !SamePhysicalAddress[w00, d01] and
    !SamePhysicalAddress[w00, w10]
  )
}
run test_ghosttest {
  ghosttest and
  union
} for 6

pred intelbug {
  // test bounds
  #Write=1 and
  #Read=1 and
  #MFENCE=0 and
  #INVLPG=0 and
  #ptwalk>=1 and
  #dirtybit>=1 and
  #VirtualAddress=4 and

  // po and com relations
  #po=1 and
  #pte_map=0 and
  #remap=0 and
  #ghost>=2 and
  #rf_ptw>=1 and
  
  // test description
  #Thread=1 and
  (
    some disj w02 : Write |
    some disj r10 : Read |
    some disj p03 : ptwalk |
    some disj d01 : dirtybit |
    w02->r10 in po and
    w02->d01 in ghost and
    w02->p03 in ghost and
    p03->w02 in rf_ptw and
    SamePhysicalAddress[d01, p03] and
    !SamePhysicalAddress[d01, w02] and
    !SamePhysicalAddress[w02, r10]
  )
}
run test_intelbug {
  intelbug and
  union
} for 5

pred invlpgtest {
  // test bounds
  #Write=0 and
  #Read=1 and
  #MFENCE=0 and
  #INVLPG=1 and
  #ptwalk>=1 and
  #dirtybit>=0 and
  #VirtualAddress=2 and

  // po and com relations
  #po=1 and
  #pte_map=0 and
  #remap=0 and
  #ghost>=1 and
  #rf_ptw>=1 and
  
  // test description
  #Thread=1 and
  (
    some disj r00 : Read |
    some disj p01 : ptwalk |
    some disj i10 : INVLPG |
    i10->r00 in po and
    r00->p01 in ghost and
    p01->r00 in rf_ptw and
    !SamePhysicalAddress[r00, p01] and
    SameVirtualAddress[r00, i10]
  )
}
run test_invlpgtest {
  invlpgtest and
  union
} for 3

pred ipi_ordering {
  // test bounds
  #Write=1 and
  #Read=2 and
  #MFENCE=0 and
  #INVLPG=0 and
  #ptwalk>=0 and
  #dirtybit>=0 and
  #VirtualAddress=2 and

  // po and com relations
  #po=1 and
  #pte_map=0 and
  #remap=0 and
  #ghost>=0 and
  #rf_ptw>=0 and
  
  // test description
  #Thread=2 and
  (
    some disj w20 : Write |
    some disj r10,r00 : Read |
    r10->w20 in po and
    SamePhysicalAddress[r00, r10] and
    SamePhysicalAddress[r00, w20]
  )
}
run test_ipi_ordering {
  ipi_ordering and
  union
} for 7

pred ipi3 {
  // test bounds
  #Write=4 and
  #Read=3 and
  #MFENCE=0 and
  #INVLPG=2 and
  #ptwalk>=0 and
  #dirtybit>=0 and
  #VirtualAddress=4 and

  // po and com relations
  #po=7 and
  #pte_map=1 and
  #remap=2 and
  #ghost>=0 and
  #rf_ptw>=0 and
  
  // test description
  #Thread=2 and
  (
    some disj w00,w20,w70,w80 : Write |
    some disj r30,r40,r60 : Read |
    some disj i10,i50 : INVLPG |
    w00 in pte_map.pte_mapping and
    w00->i10 in po and
    i10->w20 in po and
    w20->r30 in po and
    r30->r40 in po and
    i50->r60 in po and
    r60->w70 in po and
    w70->w80 in po and
    w00->i10 in remap and
    w00->i50 in remap and
    SamePhysicalAddress[w20, r30] and
    SamePhysicalAddress[w20, r60] and
    SamePhysicalAddress[w20, w80] and
    SamePhysicalAddress[r40, w70] and
    !SamePhysicalAddress[w20, r40] and
    SameVirtualAddress[i10, r40] and
    SameVirtualAddress[i10, i50] and
    SameVirtualAddress[i10, w70]
  )
}
run test_ipi3 {
  ipi3 and
  union
} for 20

pred ipi4 {
  // test bounds
  #Write=4 and
  #Read=3 and
  #MFENCE=0 and
  #INVLPG=2 and
  #ptwalk>=1 and
  #dirtybit>=0 and
  #VirtualAddress=4 and

  // po and com relations
  #po=7 and
  #pte_map=1 and
  #remap=2 and
  #ghost>=1 and
  #rf_ptw>=1 and
  
  // test description
  #Thread=2 and
  (
    some disj w00,w20,w70,w80 : Write |
    some disj r30,r40,r60 : Read |
    some disj p41 : ptwalk |
    some disj i10,i50 : INVLPG |
    w00 in pte_map.pte_mapping and
    w00->i10 in po and
    i10->w20 in po and
    w20->r30 in po and
    r30->r40 in po and
    i50->r60 in po and
    r60->w70 in po and
    w70->w80 in po and
    r40->p41 in ghost and
    p41->r40 in rf_ptw and
    w00->i10 in remap and
    w00->i50 in remap and
    SamePhysicalAddress[w00, p41] and
    SamePhysicalAddress[w20, r30] and
    SamePhysicalAddress[w20, r60] and
    SamePhysicalAddress[w20, w80] and
    !SamePhysicalAddress[r40, w70] and
    !SamePhysicalAddress[w00, w20] and
    !SamePhysicalAddress[w00, r40] and
    !SamePhysicalAddress[w00, w70] and
    !SamePhysicalAddress[w20, r40] and
    !SamePhysicalAddress[w20, w70] and
    SameVirtualAddress[i10, r40] and
    SameVirtualAddress[i10, i50] and
    SameVirtualAddress[i10, w70]
  )
}
run test_ipi4 {
  ipi4 and
  union
} for 20

pred ipi5 {
  // test bounds
  #Write=4 and
  #Read=3 and
  #MFENCE=0 and
  #INVLPG=2 and
  #ptwalk>=3 and
  #dirtybit>=0 and
  #VirtualAddress=4 and

  // po and com relations
  #po=7 and
  #pte_map=1 and
  #remap=2 and
  #ghost>=3 and
  #rf_ptw>=3 and
  
  // test description
  #Thread=2 and
  (
    some disj w00,w20,w60,w70 : Write |
    some disj r30,r50,r40 : Read |
    some disj p31,p41,p61 : ptwalk |
    some disj i10,i80 : INVLPG |
    w00 in pte_map.pte_mapping and
    w00->i10 in po and
    i10->w20 in po and
    w20->r30 in po and
    r30->r40 in po and
    r50->w60 in po and
    w60->w70 in po and
    w70->i80 in po and
    r30->p31 in ghost and
    r40->p41 in ghost and
    w60->p61 in ghost and
    p31->r30 in rf_ptw and
    p41->r40 in rf_ptw and
    p61->w60 in rf_ptw and
    w00->i10 in remap and
    w00->i80 in remap and
    SamePhysicalAddress[w00, p41] and
    SamePhysicalAddress[w00, p61] and
    SamePhysicalAddress[w20, r30] and
    SamePhysicalAddress[w20, r50] and
    SamePhysicalAddress[w20, w70] and
    !SamePhysicalAddress[w00, w20] and
    !SamePhysicalAddress[r40, w60] and
    SameVirtualAddress[i10, r40] and
    SameVirtualAddress[i10, w60] and
    SameVirtualAddress[i10, i80]
  )
}
run test_ipi5 {
  ipi5 and
  union
} for 20

pred ipi6 {
  // test bounds
  #Write=4 and
  #Read=3 and
  #MFENCE=0 and
  #INVLPG=2 and
  #ptwalk>=2 and
  #dirtybit>=0 and
  #VirtualAddress=4 and

  // po and com relations
  #po=7 and
  #pte_map=1 and
  #remap=2 and
  #ghost>=2 and
  #rf_ptw>=2 and
  
  // test description
  #Thread=2 and
  (
    some disj w00,w20,w70,w80 : Write |
    some disj r30,r40,r60 : Read |
    some disj p41,p71 : ptwalk |
    some disj i10,i50 : INVLPG |
    w00 in pte_map.pte_mapping and
    w00->i10 in po and
    i10->w20 in po and
    w20->r30 in po and
    r30->r40 in po and
    i50->r60 in po and
    r60->w70 in po and
    w70->w80 in po and
    r40->p41 in ghost and
    w70->p71 in ghost and
    p41->r40 in rf_ptw and
    p71->w70 in rf_ptw and
    w00->i10 in remap and
    w00->i50 in remap and
    SamePhysicalAddress[w00, p41] and
    SamePhysicalAddress[w00, p71] and
    SamePhysicalAddress[w20, r30] and
    SamePhysicalAddress[w20, r60] and
    SamePhysicalAddress[w20, w80] and
    SamePhysicalAddress[r40, w70] and
    !SamePhysicalAddress[w00, w20] and
    !SamePhysicalAddress[w20, r40] and
    !SamePhysicalAddress[w00, r40] and
    SameVirtualAddress[i10, r40] and
    SameVirtualAddress[i10, i50] and
    SameVirtualAddress[i10, w70]
  )
}
run test_ipi6 {
  ipi6 and
  union
} for 20

pred ipi7 {
  // test bounds
  #Write=4 and
  #Read=3 and
  #MFENCE=0 and
  #INVLPG=2 and
  #ptwalk>=2 and
  #dirtybit>=0 and
  #VirtualAddress=4 and

  // po and com relations
  #po=7 and
  #pte_map=1 and
  #remap=2 and
  #ghost>=2 and
  #rf_ptw>=2 and
  
  // test description
  #Thread=2 and
  (
    some disj w00,w40,w90,w80 : Write |
    some disj r50,r60,r70 : Read |
    some disj p61,p81 : ptwalk |
    some disj i10,i130 : INVLPG |
    w00 in pte_map.pte_mapping and
    w00->i10 in po and
    i10->w40 in po and
    w40->r50 in po and
    r50->r60 in po and
    i130->r70 in po and
    r70->w80 in po and
    w80->w90 in po and
    r60->p61 in ghost and
    w80->p81 in ghost and
    p61->r60 in rf_ptw and
    p81->w80 in rf_ptw and
    w00->i10 in remap and
    w00->i130 in remap and
    SamePhysicalAddress[w00, p61] and
    SamePhysicalAddress[w00, p81] and
    SamePhysicalAddress[w40, r50] and
    SamePhysicalAddress[w40, r70] and
    SamePhysicalAddress[w40, w90] and
    SamePhysicalAddress[r60, w80] and
    !SamePhysicalAddress[w00, w40] and
    !SamePhysicalAddress[w40, r60] and
    !SamePhysicalAddress[w00, r60] and
    SameVirtualAddress[i10, r60] and
    SameVirtualAddress[i10, i130] and
    SameVirtualAddress[i10, w80]
  )
}
run test_ipi7 {
  ipi7 and
  union
} for 20

pred ipi8 {
  // test bounds
  #Write=4 and
  #Read=3 and
  #MFENCE=0 and
  #INVLPG=2 and
  #ptwalk>=2 and
  #dirtybit>=0 and
  #VirtualAddress=4 and

  // po and com relations
  #po=7 and
  #pte_map=1 and
  #remap=2 and
  #ghost>=2 and
  #rf_ptw>=2 and
  
  // test description
  #Thread=2 and
  (
    some disj w00,w40,w90,w80 : Write |
    some disj r50,r60,r70 : Read |
    some disj p61,p81 : ptwalk |
    some disj i10,i130 : INVLPG |
    w00 in pte_map.pte_mapping and
    w00->i10 in po and
    i10->w40 in po and
    w40->r50 in po and
    r50->r60 in po and
    i130->r70 in po and
    r70->w80 in po and
    w80->w90 in po and
    r60->p61 in ghost and
    w80->p81 in ghost and
    p61->r60 in rf_ptw and
    p81->w80 in rf_ptw and
    w00->i10 in remap and
    w00->i130 in remap and
    SamePhysicalAddress[w00, p61] and
    SamePhysicalAddress[w00, p81] and
    SamePhysicalAddress[w40, r50] and
    SamePhysicalAddress[w40, r70] and
    SamePhysicalAddress[w40, w90] and
    !SamePhysicalAddress[w00, w40] and
    !SamePhysicalAddress[r60, w80] and
    SameVirtualAddress[i10, r60] and
    SameVirtualAddress[i10, i130] and
    SameVirtualAddress[i10, w80]
  )
}
run test_ipi8 {
  ipi8 and
  union
} for 20

pred mp {
  // test bounds
  #Write=2 and
  #Read=2 and
  #MFENCE=0 and
  #INVLPG=0 and
  #ptwalk>=0 and
  #dirtybit>=0 and
  #VirtualAddress=4 and

  // po and com relations
  #po=2 and
  #pte_map=0 and
  #remap=0 and
  #ghost>=0 and
  #rf_ptw>=0 and
  
  // test description
  #Thread=2 and
  (
    some disj w10,w00 : Write |
    some disj r30,r20 : Read |
    w00->w10 in po and
    r20->r30 in po and
    SamePhysicalAddress[w00, r30] and
    SamePhysicalAddress[w10, r20] and
    !SamePhysicalAddress[w00, w10]
  )
}
run test_mp {
  mp and
  union
} for 10

pred mrf1 {
  // test bounds
  #Write=1 and
  #Read=1 and
  #MFENCE=0 and
  #INVLPG=0 and
  #ptwalk>=0 and
  #dirtybit>=0 and
  #VirtualAddress=2 and

  // po and com relations
  #po=1 and
  #pte_map=1 and
  #remap=0 and
  #ghost>=0 and
  #rf_ptw>=0 and
  
  // test description
  #Thread=1 and
  (
    some disj w00 : Write |
    some disj r10 : Read |
    w00 in pte_map.pte_mapping and
    w00->r10 in po and
    !SamePhysicalAddress[w00, r10]
  )
}
run test_mrf1 {
  mrf1 and
  union
} for 5

pred n2 {
  // test bounds
  #Write=4 and
  #Read=4 and
  #MFENCE=0 and
  #INVLPG=0 and
  #ptwalk>=0 and
  #dirtybit>=0 and
  #VirtualAddress=6 and

  // po and com relations
  #po=4 and
  #pte_map=0 and
  #remap=0 and
  #ghost>=0 and
  #rf_ptw>=0 and
  
  // test description
  #Thread=4 and
  (
    some disj w10,w00,w20,w30 : Write |
    some disj r50,r40,r60,r70 : Read |
    w00->w10 in po and
    w20->w30 in po and
    r40->r50 in po and
    r60->r70 in po and
    SamePhysicalAddress[w00, w20] and
    SamePhysicalAddress[w00, r40] and
    SamePhysicalAddress[w00, r50] and
    SamePhysicalAddress[w10, r70] and
    SamePhysicalAddress[w30, r60] and
    !SamePhysicalAddress[w00, w10] and
    !SamePhysicalAddress[w00, w30] and
    !SamePhysicalAddress[w10, w30]
  )
}
run test_n2 {
  n2 and
  union
} for 20

pred n5 {
  // test bounds
  #Write=2 and
  #Read=2 and
  #MFENCE=0 and
  #INVLPG=0 and
  #ptwalk>=0 and
  #dirtybit>=0 and
  #VirtualAddress=2 and

  // po and com relations
  #po=2 and
  #pte_map=0 and
  #remap=0 and
  #ghost>=0 and
  #rf_ptw>=0 and
  
  // test description
  #Thread=2 and
  (
    some disj w00,w20 : Write |
    some disj r10,r30 : Read |
    w00->r10 in po and
    w20->r30 in po and
    SamePhysicalAddress[w00, r10] and
    SamePhysicalAddress[w00, w20] and
    SamePhysicalAddress[w00, r30]
  )
}
run test_n5 {
  n5 and
  union
} for 10

pred n5_synonym {
  // test bounds
  #Write=3 and
  #Read=2 and
  #MFENCE=0 and
  #INVLPG=2 and
  #ptwalk>=0 and
  #dirtybit>=0 and
  #VirtualAddress=4 and

  // po and com relations
  #po=5 and
  #pte_map=1 and
  #remap=2 and
  #ghost>=0 and
  #rf_ptw>=0 and
  
  // test description
  #Thread=2 and
  (
    some disj w00,w20,w50 : Write |
    some disj r30,r60 : Read |
    some disj i10,i40 : INVLPG |
    w00 in pte_map.pte_mapping and
    w00->i10 in po and
    i10->w20 in po and
    w20->r30 in po and
    i40->w50 in po and
    w50->r60 in po and
    w00->i10 in remap and
    w00->i40 in remap and
    SamePhysicalAddress[w20, r30] and
    SamePhysicalAddress[w20, w50] and
    SamePhysicalAddress[w20, r60] and
    !SamePhysicalAddress[w00, w20] and
    SameVirtualAddress[i10, r30] and
    SameVirtualAddress[i10, i40] and
    SameVirtualAddress[i10, w50]
  )
}
run test_n5_synonym {
  n5_synonym and
  union
} for 15

pred new_sb_synonym_permit {
  // test bounds
  #Write=3 and
  #Read=2 and
  #MFENCE=0 and
  #INVLPG=2 and
  #ptwalk>=0 and
  #dirtybit>=0 and
  #VirtualAddress=4 and

  // po and com relations
  #po=5 and
  #pte_map=1 and
  #remap=2 and
  #ghost>=0 and
  #rf_ptw>=0 and
  
  // test description
  #Thread=2 and
  (
    some disj w00,w20,w50 : Write |
    some disj r30,r60 : Read |
    some disj i10,i40 : INVLPG |
    w00 in pte_map.pte_mapping and
    w00->i10 in po and
    i10->w20 in po and
    w20->r30 in po and
    i40->w50 in po and
    w50->r60 in po and
    w00->i10 in remap and
    w00->i40 in remap and
    SamePhysicalAddress[w20, r30] and
    SamePhysicalAddress[w20, w50] and
    SamePhysicalAddress[w20, r60] and
    !SamePhysicalAddress[w00, w20] and
    SameVirtualAddress[i10, r30] and
    SameVirtualAddress[i10, i40] and
    SameVirtualAddress[i10, w50]
  )
}
run test_new_sb_synonym_permit {
  new_sb_synonym_permit and
  union
} for 15

pred null {
  // test bounds
  #Write=1 and
  #Read=0 and
  #MFENCE=0 and
  #INVLPG=0 and
  #ptwalk>=0 and
  #dirtybit>=0 and
  #VirtualAddress=2 and

  // po and com relations
  #po=0 and
  #pte_map=0 and
  #remap=0 and
  #ghost>=0 and
  #rf_ptw>=0 and
  
  // test description
  #Thread=1 and
  (
    none in univ
  )
}
run test_null {
  null and
  union
} for 3

pred ptwalktest {
  // test bounds
  #Write=2 and
  #Read=1 and
  #MFENCE=0 and
  #INVLPG=1 and
  #ptwalk>=2 and
  #dirtybit>=0 and
  #VirtualAddress=2 and

  // po and com relations
  #po=3 and
  #pte_map=1 and
  #remap=1 and
  #ghost>=2 and
  #rf_ptw>=2 and
  
  // test description
  #Thread=1 and
  (
    some disj w00,w20 : Write |
    some disj r30 : Read |
    some disj p21,p31 : ptwalk |
    some disj i10 : INVLPG |
    w00 in pte_map.pte_mapping and
    w00->i10 in po and
    i10->w20 in po and
    w20->r30 in po and
    w20->p21 in ghost and
    r30->p31 in ghost and
    p21->w20 in rf_ptw and
    p31->r30 in rf_ptw and
    w00->i10 in remap and
    SamePhysicalAddress[w00, p21] and
    SamePhysicalAddress[w00, p31] and
    SamePhysicalAddress[w20, r30] and
    !SamePhysicalAddress[w00, w20] and
    SameVirtualAddress[i10, w20] and
    SameVirtualAddress[i10, r30]
  )
}
run test_ptwalktest {
  ptwalktest and
  union
} for 9

pred ptwalk2 {
  // test bounds
  #Write=1 and
  #Read=1 and
  #MFENCE=0 and
  #INVLPG=1 and
  #ptwalk>=1 and
  #dirtybit>=0 and
  #VirtualAddress=2 and

  // po and com relations
  #po=2 and
  #pte_map=1 and
  #remap=1 and
  #ghost>=1 and
  #rf_ptw>=1 and
  
  // test description
  #Thread=1 and
  (
    some disj w00 : Write |
    some disj r20 : Read |
    some disj p21 : ptwalk |
    some disj i10 : INVLPG |
    w00 in pte_map.pte_mapping and
    w00->i10 in po and
    i10->r20 in po and
    r20->p21 in ghost and
    p21->r20 in rf_ptw and
    w00->i10 in remap and
    SamePhysicalAddress[w00, p21] and
    !SamePhysicalAddress[w00, r20] and
    SameVirtualAddress[i10, r20]
  )
}
run test_ptwalk2 {
  ptwalk2 and
  union
} for 6

pred ptwalk3 {
  // test bounds
  #Write=0 and
  #Read=2 and
  #MFENCE=0 and
  #INVLPG=0 and
  #ptwalk>=2 and
  #dirtybit>=0 and
  #VirtualAddress=2 and

  // po and com relations
  #po=1 and
  #pte_map=0 and
  #remap=0 and
  #ghost>=2 and
  #rf_ptw>=2 and
  
  // test description
  #Thread=1 and
  (
    some disj r10,r00 : Read |
    some disj p11,p01 : ptwalk |
    r00->r10 in po and
    r00->p01 in ghost and
    r10->p11 in ghost and
    p01->r00 in rf_ptw and
    p11->r10 in rf_ptw and
    SamePhysicalAddress[r00, r10] and
    SamePhysicalAddress[p01, p11] and
    !SamePhysicalAddress[r00, p01]
  )
}
run test_ptwalk3 {
  ptwalk3 and
  union
} for 4

pred readfrominitial {
  // test bounds
  #Write=0 and
  #Read=1 and
  #MFENCE=0 and
  #INVLPG=0 and
  #ptwalk>=0 and
  #dirtybit>=0 and
  #VirtualAddress=2 and

  // po and com relations
  #po=0 and
  #pte_map=0 and
  #remap=0 and
  #ghost>=0 and
  #rf_ptw>=0 and
  
  // test description
  #Thread=1 and
  (
    none in univ
  )
}
run test_readfrominitial {
  readfrominitial and
  union
} for 2

pred rftest {
  // test bounds
  #Write=1 and
  #Read=1 and
  #MFENCE=0 and
  #INVLPG=0 and
  #ptwalk>=0 and
  #dirtybit>=0 and
  #VirtualAddress=2 and

  // po and com relations
  #po=0 and
  #pte_map=0 and
  #remap=0 and
  #ghost>=0 and
  #rf_ptw>=0 and
  
  // test description
  #Thread=2 and
  (
    some disj w00 : Write |
    some disj r10 : Read |
    SamePhysicalAddress[w00, r10]
  )
}
run test_rftest {
  rftest and
  union
} for 5

pred sb {
  // test bounds
  #Write=2 and
  #Read=2 and
  #MFENCE=0 and
  #INVLPG=0 and
  #ptwalk>=0 and
  #dirtybit>=0 and
  #VirtualAddress=4 and

  // po and com relations
  #po=2 and
  #pte_map=0 and
  #remap=0 and
  #ghost>=0 and
  #rf_ptw>=0 and
  
  // test description
  #Thread=2 and
  (
    some disj w00,w20 : Write |
    some disj r10,r30 : Read |
    w00->r10 in po and
    w20->r30 in po and
    SamePhysicalAddress[w00, r30] and
    SamePhysicalAddress[r10, w20] and
    !SamePhysicalAddress[w00, r10]
  )
}
run test_sb {
  sb and
  union
} for 10

pred sb_synonym {
  // test bounds
  #Write=3 and
  #Read=2 and
  #MFENCE=0 and
  #INVLPG=2 and
  #ptwalk>=0 and
  #dirtybit>=0 and
  #VirtualAddress=4 and

  // po and com relations
  #po=5 and
  #pte_map=1 and
  #remap=2 and
  #ghost>=0 and
  #rf_ptw>=0 and
  
  // test description
  #Thread=2 and
  (
    some disj w00,w20,w50 : Write |
    some disj r30,r60 : Read |
    some disj i10,i40 : INVLPG |
    w00 in pte_map.pte_mapping and
    w00->i10 in po and
    i10->w20 in po and
    w20->r30 in po and
    i40->w50 in po and
    w50->r60 in po and
    w00->i10 in remap and
    w00->i40 in remap and
    SamePhysicalAddress[w20, r30] and
    SamePhysicalAddress[w20, w50] and
    SamePhysicalAddress[w20, r60] and
    !SamePhysicalAddress[w00, w20] and
    SameVirtualAddress[i10, r30] and
    SameVirtualAddress[i10, i40] and
    SameVirtualAddress[i10, w50]
  )
}
run test_sb_synonym {
  sb_synonym and
  union
} for 15

pred sb_synonym_permit {
  // test bounds
  #Write=3 and
  #Read=2 and
  #MFENCE=0 and
  #INVLPG=2 and
  #ptwalk>=0 and
  #dirtybit>=0 and
  #VirtualAddress=4 and

  // po and com relations
  #po=5 and
  #pte_map=1 and
  #remap=2 and
  #ghost>=0 and
  #rf_ptw>=0 and
  
  // test description
  #Thread=2 and
  (
    some disj w00,w20,w50 : Write |
    some disj r30,r60 : Read |
    some disj i10,i40 : INVLPG |
    w00 in pte_map.pte_mapping and
    w00->i10 in po and
    i10->w20 in po and
    w20->r30 in po and
    i40->w50 in po and
    w50->r60 in po and
    w00->i10 in remap and
    w00->i40 in remap and
    SamePhysicalAddress[w20, r30] and
    SamePhysicalAddress[w20, w50] and
    SamePhysicalAddress[w20, r60] and
    !SamePhysicalAddress[w00, w20] and
    SameVirtualAddress[i10, r30] and
    SameVirtualAddress[i10, i40] and
    SameVirtualAddress[i10, w50]
  )
}
run test_sb_synonym_permit {
  sb_synonym_permit and
  union
} for 15