(****************************************************************************)
(*                           the diy toolsuite                              *)
(*                                                                          *)
(* Jade Alglave, University College London, UK.                             *)
(* Luc Maranget, INRIA Paris-Rocquencourt, France.                          *)
(*                                                                          *)
(* Copyright 2022-present Institut National de Recherche en Informatique et *)
(* en Automatique and the authors. All rights reserved.                     *)
(*                                                                          *)
(* This software is governed by the CeCILL-B license under French law and   *)
(* abiding by the rules of distribution of free software. You can use,      *)
(* modify and/ or redistribute the software under the terms of the CeCILL-B *)
(* license as circulated by CEA, CNRS and INRIA at the following URL        *)
(* "http://www.cecill.info". We also give a copy in LICENSE.txt.            *)
(****************************************************************************)

module IdTr =
 InstrUtils.IdTr
   (struct type instr = RISCVBase.instruction end)

module
  Make
    (C:sig end)
    (Tr:InstrUtils.Tr with type data = RISCVBase.instruction) = struct

  module Lexer =
    RISCVLexer.Make
      (struct
        let debug = false
       end)

  let parse_instr s =
    let lexbuf = Lexing.from_string s in
    let pi =
      GenParserUtils.call_parser
        "RISCVInstr" lexbuf Lexer.token RISCVParser.one_instr in
    RISCVBase.PseudoI.parsed_tr pi

  include
    RISCVBase.MakeInstr
      (struct
        let parser = parse_instr
      end)
      (Tr)
end

module Std =
  Make
    (struct end)
    (IdTr)
