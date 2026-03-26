%{
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

(* We consider memory order and IO as the same*)
let tr_rw = function
  | "r" -> RISCVBase.R
  | "ir" -> RISCVBase.IR
  | "w" -> RISCVBase.W
  | "ow" -> RISCVBase.OW 
  | "rw"  -> RISCVBase.RW
  | "iorw" -> RISCVBase.IORW
  | _ -> raise Parsing.Parse_error
%}

%token EOF
%token <RISCVBase.reg> ARCH_REG
%token <string> SYMB_REG
%token <string> NUM
%token <string> NAME
%token <int> PROC

%token SEMI COMMA PIPE COLON LPAR RPAR

/* Instruction tokens */
%token <RISCVBase.opi> OPI
%token <RISCVBase.opiw> OPIW
%token LI LUI LA
%token <RISCVBase.op> OP
%token <RISCVBase.opw> OPW
%token J
%token JR
%token <RISCVBase.cond> BCC
%token <RISCVBase.width * RISCVBase.signed * RISCVBase.mo > LOAD
%token <RISCVBase.width * RISCVBase.mo> STORE
%token <RISCVBase.width * RISCVBase.mo> LR
%token <RISCVBase.width * RISCVBase.mo> SC
%token <RISCVBase.opamo * RISCVBase.width * RISCVBase.mo> AMO
%token FENCE FENCEI FENCETSO AUIPC
%token <string> META
%token NOP RET MV
%token <RISCVBase.signed * RISCVBase.width> EXT
%type <RISCVBase.pins> one_instr
%type <MiscParser.proc list * (RISCVBase.parsedPseudo) list list> main
%type <RISCVBase.parsedPseudo list> instr_option_seq


%start main instr_option_seq one_instr



%%

main:
| semi_opt proc_list iol_list EOF { $2,$3 }

semi_opt:
| { () }
| SEMI { () }

proc_list:
| ps=separated_nonempty_list(PIPE,PROC) SEMI
  { List.map (fun p -> p,None,MiscParser.Main) ps }

iol_list :
|  instr_option_list SEMI
    {[$1]}
|  instr_option_list SEMI iol_list {$1::$3}

instr_option_list :
  | instr_option
      {[$1]}
  | instr_option PIPE instr_option_list
      {$1::$3}


instr_option_seq :
  | is=separated_nonempty_list(SEMI,instr_option) EOF { is }

instr_option :
|            { RISCVBase.Nop }
| NAME COLON instr_option { RISCVBase.Label ($1,$3) }
| instr      { RISCVBase.Instruction $1}

reg:
| SYMB_REG { RISCVBase.Symbolic_reg $1 }
| ARCH_REG { $1 }

k:
| NUM  { MetaConst.Int (int_of_string $1) }
| META { MetaConst.Meta $1 }

addr:
| NUM LPAR reg RPAR
    { int_of_string $1,$3 }
| LPAR reg RPAR
    { 0,$2 }

addr0:
| NUM LPAR reg RPAR
    { if $1 <> "0" then raise Parsing.Parse_error;
      $3 }
| LPAR reg RPAR
    { $2 }

one_instr:
| i=instr EOF { i }

instr:
| NOP
  { RISCVBase.INop }
| RET
  { RISCVBase.Ret }
/* OPs */
| LI reg COMMA NUM
   { RISCVBase.Li ($2,Int64.of_string $4) }
| LA reg COMMA NAME
  { RISCVBase.OpA (RISCVBase.LA,$2,$4) }
| LUI reg COMMA k
  { RISCVBase.OpI2 (RISCVBase.LUI,$2,$4) }
| OPI reg COMMA reg COMMA k
  { RISCVBase.OpI ($1,$2,$4,$6) }
| OPIW reg COMMA reg COMMA k
  { RISCVBase.OpIW ($1,$2,$4,$6) }
| OP reg COMMA reg COMMA reg
  { RISCVBase.Op ($1,$2,$4,$6) }
| OPW reg COMMA reg COMMA reg
  { RISCVBase.OpW ($1,$2,$4,$6) }
| J NAME
    { RISCVBase.J $2 }
| JR reg
    { RISCVBase.JR $2 }
| BCC reg COMMA reg COMMA NAME
    { RISCVBase.Bcc ($1,$2,$4,$6) }
| MV reg COMMA reg
    { RISCVBase.OpI (RISCVBase.ADDI, $2, $4, MetaConst.Int 0) }
| LOAD reg COMMA addr
    { let w,s,mo = $1 in
    let off,r = $4 in
    RISCVBase.Load (w,s,mo,$2,off,r) }
| STORE reg COMMA addr
    {let w,mo = $1 in
     let off,r = $4 in
     RISCVBase.Store (w,mo,$2,off,r) }
| LR reg COMMA addr0
    { let w,mo = $1 in
    RISCVBase.LoadReserve (w,mo,$2,$4) }
| SC reg COMMA reg COMMA addr0
    { let w,mo = $1 in
    RISCVBase.StoreConditional (w,mo,$2,$4,$6) }
| AUIPC reg COMMA k
    { RISCVBase.AUIPC ($2, $4) }
| AMO reg COMMA reg COMMA addr0
    { let op,w,mo = $1 in
    RISCVBase.Amo (op,w,mo,$2,$4,$6) }
| FENCEI
    { RISCVBase.FenceIns RISCVBase.FenceI }
| FENCETSO
    { RISCVBase.FenceIns RISCVBase.FenceTSO }
| FENCE
    { RISCVBase.FenceIns (RISCVBase.Fence (RISCVBase.RW,RISCVBase.RW)) }
| FENCE NAME COMMA NAME
    { RISCVBase.FenceIns (RISCVBase.Fence (tr_rw $2,tr_rw $4)) }
| EXT reg COMMA reg
    { let s,w = $1 in RISCVBase.Ext (s,w,$2,$4) }
