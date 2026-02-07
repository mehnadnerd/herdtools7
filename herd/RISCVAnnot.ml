(****************************************************************************)
(*                           the diy toolsuite                              *)
(*                                                                          *)
(* Jade Alglave, University College London, UK.                             *)
(* Luc Maranget, INRIA Paris-Rocquencourt, France.                          *)
(*                                                                          *)
(* Copyright 2015-present Institut National de Recherche en Informatique et *)
(* en Automatique, ARM Ltd and the authors. All rights reserved.            *)
(*                                                                          *)
(* This software is governed by the CeCILL-B license under French law and   *)
(* abiding by the rules of distribution of free software. You can use,      *)
(* modify and/ or redistribute the software under the terms of the CeCILL-B *)
(* license as circulated by CEA, CNRS and INRIA at the following URL        *)
(* "http://www.cecill.info". We also give a copy in LICENSE.txt.            *)
(****************************************************************************)


type t =
  (* We don't have non-atomic acquire or release since that doesn't exist in RISCV *)
  XA | (* Acquire Atomic *)
  XL | (* Release Atomic *)
  (* There is no Acquire-Release Atomic since the load and store events are seperated *)
  X | (* Atomic *)
  N | (* None *)
  NoRet (* No return -- maybe needed for CAS *)

let is_atomic = function
  | XA | XL | X | NoRet -> true
  | _ -> false

let is_noreturn = function
  | NoRet -> true
  | _ -> false

let is_acquire = function
  | XA -> true
  | _ -> false

let is_release = function
  | XL -> true
  | _ -> false

let sets = [
    "X", is_atomic;
    "Acq",  is_acquire;
    "Rel",  is_release;
    "NoRet", is_noreturn;
  ]

let pp = function
  | XA -> "Acq*"
  | XL -> "Rel*"
  | X -> "*"
  | N -> ""
  | NoRet -> "NoRet"

