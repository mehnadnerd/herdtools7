(****************************************************************************)
(*                           the diy toolsuite                              *)
(*                                                                          *)
(* Jade Alglave, University College London, UK.                             *)
(* Luc Maranget, INRIA Paris-Rocquencourt, France.                          *)
(*                                                                          *)
(* Copyright 2021-present Institut National de Recherche en Informatique et *)
(* en Automatique, ARM Ltd and the authors. All rights reserved.            *)
(*                                                                          *)
(* This software is governed by the CeCILL-B license under French law and   *)
(* abiding by the rules of distribution of free software. You can use,      *)
(* modify and/ or redistribute the software under the terms of the CeCILL-B *)
(* license as circulated by CEA, CNRS and INRIA at the following URL        *)
(* "http://www.cecill.info". We also give a copy in LICENSE.txt.            *)
(****************************************************************************)

type 'op1 unop =
  | AB (* get AB from PTE entry *)
  | SetAB (* set AB to 1 in PTE entry *)
  | DB (* get DB from PTE entry *)
  | SetDB (* set DB to 1 in PTE entry *)
  | Valid (* get Valid bit from PTE entry *)
  | OA (* get OA from PTE entry *)
  | Extra1 of 'op1

type 'op binop =
  | Extra of 'op

module
   Make
     (S:Scalar.S)
     (Extra:ArchOp.S with type scalar = S.t and type instr = RISCVBase.instruction and type addrreg = AddrReg.No.t and type pteval = RISCVPteVal.t) : ArchOp.S
   with type extra_op1 = Extra.op1
    and type 'a constr_op1 = 'a unop
    and type extra_op = Extra.op
    and type 'a constr_op = 'a binop
    and type scalar = S.t
  = struct

    type extra_op = Extra.op
    type 'a constr_op = 'a binop
    type op = Extra.op binop
    type extra_op1 = Extra.op1
    type 'a constr_op1 = 'a unop
    type op1 = extra_op1 constr_op1

    open RISCVPteVal

    let pp_op = function
      | Extra extra -> Extra.pp_op extra

    let pp_op1 hexa = function
      | AB -> "AB"
      | SetAB -> "SetAB"
      | DB -> "DB"
      | SetDB -> "SetDB"
      | Valid -> "Valid"
      | OA -> "OA"
      | Extra1 op1 -> Extra.pp_op1 hexa op1 |> Printf.sprintf "Extra:%s"

    type scalar = S.t
    type pteval = RISCVPteVal.t
    type addrreg = AddrReg.No.t
    type instr = RISCVBase.instruction
    type cst = (scalar,pteval,addrreg,instr) Constant.t

    (* let pp_cst hexa v = None *)

    let boolToCst =
      let open Constant in
      let zero = Concrete S.zero
      and one = Concrete S.one in
      fun b -> if b then one else zero

    let op_get_pteval op (v:cst) =
      let open Constant in
      match v with
      | PteVal p -> Some (boolToCst (op p))
      | _ -> None

    let op_set_pteval op (v:cst) =
      let open Constant in
      match v with
      | PteVal p -> Some (PteVal (op p))
      | _ -> None

    let getab = op_get_pteval (fun p -> p.ab <> 0)
    let setab = op_set_pteval (fun p -> { p with ab=1; })

    let getdb = op_get_pteval (fun p -> p.db <> 0)
    let setdb = op_set_pteval (fun p -> { p with db=1; })

    let getvalid = op_get_pteval (fun p -> p.valid <> 0)

    let getoa v =
      let open Constant in
      match v with
      | PteVal {oa;_} -> Some (Symbolic (oa2symbol oa))
      | _ -> None

    

    let trToExtra cst =
      Constant.map
        Misc.identity Misc.identity Misc.identity
        Misc.identity cst
    and trFromExtra cst =
      Constant.map
        Misc.identity Misc.identity Misc.identity
        Misc.identity cst

    let do_op = function
      | Extra op -> fun c1 c2 ->
        try
          match Extra.do_op op (trToExtra c1) (trToExtra c2) with
          | None -> None
          | Some cst -> Some (trFromExtra cst)
        with Exit -> None


    let do_op1 op =
      match op with
      | AB -> getab
      | SetAB -> setab
      | DB -> getdb
      | SetDB -> setdb
      | Valid -> getvalid
      | OA -> getoa
      | Extra1 op1 ->
          fun cst ->
           try
             match Extra.do_op1 op1 (trToExtra cst) with
             | None ->  None
             | Some cst -> Some (trFromExtra cst)
           with Exit -> None


    let shift_address_right s c =
      let open Constant in
      if S.equal (S.of_int 12) c then Some (Symbolic (System (TLB,s)))
      else None

    let orop p m =  RISCVPteVal.orop p @@ S.to_int64 m
    and andnot2 p m = RISCVPteVal.andnot2 p @@ S.to_int64 m
    and andop p m  = RISCVPteVal.andop p @@ S.to_int64 m
      |> Misc.app_opt S.of_int64

    (* Share code, placement in ASLOp not ideal *)
    let mask = ASLOp.mask

  end
