(****************************************************************************)
(*                           the diy toolsuite                              *)
(*                                                                          *)
(* Jade Alglave, University College London, UK.                             *)
(* Luc Maranget, INRIA Paris-Rocquencourt, France.                          *)
(*                                                                          *)
(* Copyright 2017-present Institut National de Recherche en Informatique et *)
(* en Automatique and the authors. All rights reserved.                     *)
(*                                                                          *)
(* This software is governed by the CeCILL-B license under French law and   *)
(* abiding by the rules of distribution of free software. You can use,      *)
(* modify and/ or redistribute the software under the terms of the CeCILL-B *)
(* license as circulated by CEA, CNRS and INRIA at the following URL        *)
(* "http://www.cecill.info". We also give a copy in LICENSE.txt.            *)
(****************************************************************************)

(** Define herd RISCV architecture *)

  open Printf

module Make (C:Arch_herd.Config) (V:Value.S) =
  struct
    include RISCVBase

    let is_amo = function
      | Amo _ -> true
      | INop|Ret|Li _|J _|JR _|Bcc _|Load _|Store _|LoadReserve _
      | OpI _|OpI2 _|OpIW _|Op _|OpW _|OpA _
      |StoreConditional _|FenceIns _
      |AUIPC _| Ext _
           -> false

    let pp_barrier_short = function
      | FenceI -> "fence.i"
      | FenceTSO -> "fence.tso"
      | Fence (a1,a2) ->  sprintf "F %s,%s" (pp_access a1) (pp_access a2)

    let reject_mixed = false

    type lannot = RISCVAnnot.t
    let get_machsize _ = V.Cst.Scalar.machsize (* TODO, consider machsizes *)
    let empty_annot = RISCVAnnot.N

    include PteValSets.No

    include RISCVExplicit

    let exp_annot = RISCVExplicit.Exp
    let nexp_annot = RISCVExplicit.NExp RISCVExplicit.Other
    let nexp_ifetch = RISCVExplicit.NExp RISCVExplicit.IFetch

    let is_ifetch_annot = function
      | NExp IFetch -> true
      | NExp (AB|DB|ABDB|Other)|Exp -> false

    let is_ab = function (* Setting of access bit *)
      | NExp (AB|ABDB)-> true
      | NExp (DB|IFetch|Other)|Exp -> false

    and is_db = function (* Setting of dirty bit flag *)
      | NExp (DB|ABDB) -> true
      | NExp (AB|IFetch|Other)|Exp -> false

    let pp_explicit e =
      match e with
      | RISCVExplicit.Exp
           when C.verbose <= 2
        -> ""
      | _ -> RISCVExplicit.pp e

    let explicit_sets = [
      "AB", is_ab;
      "DB", is_db;
    ]

    let same_barrier b = fun c -> barrier_equal_semantics b c

    let ifetch_value_sets = []

    let barrier_sets =
      fold_barrier
        (fun f k ->
          let tag = Misc.capitalize (pp_barrier_dot f)
          and pred = same_barrier f in
          (tag,pred)::k)
        []

    let cmo_sets = []

    let annot_sets = RISCVAnnot.sets
    let pp_annot = RISCVAnnot.pp
    let is_atomic = RISCVAnnot.is_atomic

    let isync =  FenceI
    let is_isync = same_barrier isync
    let pp_isync = Misc.capitalize (pp_barrier_dot isync)

    module V = V

    let mem_access_size = function
      | INop | Ret | Li _ | OpI _ | OpI2 _ | OpIW _ | Op _ | OpW _
      | J _ | JR _ | Bcc _ | FenceIns _ | OpA _ | AUIPC _
      | Ext _
        -> None
      | Load (w,_,_,_,_,_) | Store (w,_,_,_,_)
      | LoadReserve (w,_,_,_) | StoreConditional (w,_,_,_,_)
      | Amo (_,w,_,_,_,_)
        -> Some (tr_width w)

    include NoSemEnv

    include  NoLevelNorTLBI

    include ArchExtra_herd.Make(C)
        (struct

          let arch = arch

          type instr = instruction

          module V = V

          let endian = endian

          type arch_reg = reg
          let pp_reg = pp_reg
          let reg_compare = reg_compare

          let fromto_of_instr _ = None

          let get_val _ v = v

          module FaultType=FaultType.No
        end)

    module MemType=MemoryType.No

    module NoConf = struct
      type v = V.v
      type loc = location
      type value_set = V.ValueSet.t
      type solution = V.solution
      type arch_lannot = lannot
      type arch_explicit = explicit
    end

    module ArchAction = ArchAction.No(NoConf)

    module Barrier = AllBarrier.No(struct type a = barrier end)

    module CMO = Cmo.No
  end
