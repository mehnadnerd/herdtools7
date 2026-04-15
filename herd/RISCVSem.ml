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

(** Semantics of RISC-V instructions *)

module
  Make
    (C:Sem.Config)
    (V:Value.RISCV with type Cst.Instr.t = RISCVBase.instruction)
    =
  struct
    module RISCV = RISCVArch_herd.Make(SemExtra.ConfigToArchConfig(C))(V)
    module Act = MachAction.Make(C.PC)(RISCV)
    include SemExtra.Make(C)(RISCV)(Act)

    include RISCVAnnot

    let mixed = RISCV.is_mixed
    let self = C.variant Variant.Ifetch
    (* TODO maybe need if coherent *)

(* Barrier pretty print *)
    let barriers =
      RISCV.do_fold_fence
        (fun f k -> {barrier=f; pp=RISCV.pp_barrier_dot f;}::k)
        []
    let isync = Some {barrier=RISCV.FenceI; pp="fenceI";}

    let nat_sz = V.Cst.Scalar.machsize

    let atomic_pair_allowed _ _ = true

    let mo_to_annot_atomic_r mo =
      match mo with
      | RISCVBase.Rlx -> X
      | RISCVBase.Acq -> XA
      | RISCVBase.Rel -> X
      | RISCVBase.AcqRel -> XA

    let mo_to_annot_atomic_w mo =
      match mo with
      | RISCVBase.Rlx -> X
      | RISCVBase.Acq -> X
      | RISCVBase.Rel -> XL
      | RISCVBase.AcqRel -> XL

    let mo_to_annot_r mo =
      match mo with
      | RISCVBase.Rlx -> N
      | RISCVBase.Acq -> XA
      | RISCVBase.Rel -> X
      | RISCVBase.AcqRel -> XA

    let mo_to_annot_w mo =
      match mo with
      | RISCVBase.Rlx -> N
      | RISCVBase.Acq -> X
      | RISCVBase.Rel -> XL
      | RISCVBase.AcqRel -> XL

(* Semantics proper *)
    module Mixed(SZ:ByteSize.S) = struct

      module Mixed = M.Mixed(SZ)

      let (>>=) = M.(>>=)
      let (>>==) = M.(>>==)
      let (>>*=) = M.(>>*=)
      let (>>|) = M.(>>|)
      let (>>!) = M.(>>!)
      let (>>::) = M.(>>::)

      let sxt_op sz = 
        match sz with
        | MachSize.Quad -> M.op1 (Op.Mask sz) (* 64-bit sign extension is same as 64-bit zext on RV64 *)
        | _ -> M.op1 (Op.Sxt sz)
      and uxt_op sz = M.op1 (Op.Mask sz)

      let sxtw = sxt_op MachSize.Word
      and uxtw = uxt_op MachSize.Word

      let mask32 _ m = m

(*  Promotion/Demotion *)
      let promote = M.op1 Op.Promote
      and demote = M.op1 Op.Demote

      let xt_op s =
        let open Sign in
        match s with
        | Signed -> sxt_op
        | Unsigned -> uxt_op

      let unimplemented op =
        Warn.user_error "RISCV operation %s is not implemented (yet)" op

      let tr_opi op = match op with
      | RISCV.ADDI ->  Op.Add
      | RISCV.SLTI -> Op.Lt
      | RISCV.ANDI -> Op.And
      | RISCV.ORI -> Op.Or
      | RISCV.XORI -> Op.Xor
      | RISCV.SLLI -> Op.ShiftLeft
      | RISCV.SRLI -> Op.ShiftRight
      | RISCV.SLTIU|RISCV.SRAI
        -> unimplemented (RISCV.pp_opi op)

      let tr_op op = match op  with
      | RISCV.ADD -> Op.Add
      | RISCV.SLT -> Op.Lt
      | RISCV.AND -> Op.And
      | RISCV.OR -> Op.Or
      | RISCV.XOR -> Op.Xor
      | RISCV.SLL -> Op.ShiftLeft
      | RISCV.SUB -> Op.Sub
      | RISCV.SLTU|RISCV.SRA|RISCV.SRL
        -> unimplemented (RISCV.pp_op op)

      let tr_opiw op = match op with
      | RISCV.ADDIW ->  Op.Add
      | RISCV.SLLIW -> Op.ShiftLeft
      | RISCV.SRLIW|RISCV.SRAIW
        -> unimplemented (RISCV.pp_opiw op)

      let tr_opw op = match op with
      | RISCV.ADDW ->  Op.Add
      | RISCV.SLLW -> Op.ShiftLeft
      | RISCV.SUBW -> Op.Sub
      | RISCV.SRLW|RISCV.SRAW
        -> unimplemented (RISCV.pp_opw op)

      let tr_opamo op = match op with
      | RISCV.AMOSWAP -> assert false
      | RISCV.AMOADD -> Op.Add
      | RISCV.AMOAND -> Op.And
      | RISCV.AMOOR -> Op.Or
      | RISCV.AMOXOR -> Op.Xor
      | RISCV.AMOMAX -> Op.Max
      | RISCV.AMOMIN -> Op.Min
      | RISCV.AMOMAXU|RISCV.AMOMINU ->
          unimplemented (RISCV.pp_opamo op)

      let tr_cond cond = match cond with
      | RISCV.EQ -> Op.Eq
      | RISCV.NE -> Op.Ne
      | RISCV.LT -> Op.Lt
      | RISCV.GE -> Op.Ge
      | RISCV.LTU|RISCV.GEU ->  unimplemented (RISCV.pp_bcc cond)

      let mk_read sz ato expl loc v =
        let ac = Act.access_of_location_std loc in
        Act.Access (Dir.R, loc, v, ato, expl, sz, ac)

      let plain = RISCVAnnot.N

      let read_reg port r ii = match r with
      | RISCV.Ireg RISCV.X0 -> M.unitT V.zero
      | _ ->
          M.read_loc port (mk_read nat_sz plain RISCVExplicit.Exp)
            (A.Location_reg (ii.A.proc,r)) ii

      let read_reg_ord = read_reg Port.No
      let read_reg_data = read_reg Port.Data
      let read_reg_addr = read_reg Port.Addr

      let read_mem_annot sz an a expl ii =
        if mixed then
          Mixed.read_mixed Port.No sz (fun sz a v -> mk_read sz an expl a v)
            a ii
        else
          M.read_loc Port.No (mk_read sz an expl) (A.Location_global a) ii

      let read_mem sz mo = read_mem_annot sz (mo_to_annot_r mo)
      let read_mem_atomic sz mo = read_mem_annot sz (mo_to_annot_atomic_r mo)

      let do_write_reg mk r v ii = match r with
      | RISCV.Ireg RISCV.X0 -> M.unitT ()
      | _ ->
          mk
            (Act.Access
               (Dir.W, (A.Location_reg (ii.A.proc,r)), v, plain, RISCVExplicit.Exp, nat_sz, Access.REG))
            ii

      let write_reg = do_write_reg M.mk_singleton_es

      let write_reg_success =
        do_write_reg
          (if O.variant Variant.Success then
            M.mk_singleton_es_success else M.mk_singleton_es)

      let do_write_mem sz an expl a v ii  =
        if mixed then
          Mixed.write_mixed sz
            (fun sz a v -> Act.Access (Dir.W, a, v, an, expl, sz, Access.VIR))
            a v ii
        else
          M.mk_singleton_es
            (Act.Access (Dir.W, A.Location_global a, v, an, expl, sz, Access.VIR))
            ii

      let write_mem sz mo = do_write_mem sz (mo_to_annot_w mo)
      let write_mem_atomic sz mo = do_write_mem sz (mo_to_annot_atomic_w mo)
      let write_mem_annot sz an = do_write_mem sz an

      let lrscdiffok = C.variant Variant.LrScDiffOk

      let write_mem_conditional sz mo a v resa ii =
        if  lrscdiffok then
          (M.mk_singleton_es_eq
             (Act.Access (Dir.W, A.Location_global a, v, mo_to_annot_atomic_w mo, RISCVExplicit.Exp, sz,Access.VIR)) [] ii >>|
             M.neqT resa V.zero) >>! () (* resa = zero <-> no matching load reserve *)
        else
          let eq = [M.VC.Assign (a,M.VC.Atom resa)] in
          M.mk_singleton_es_eq
            (Act.Access (Dir.W, A.Location_global a, v, mo_to_annot_atomic_w mo, RISCVExplicit.Exp, sz,Access.VIR)) eq ii


      let create_barrier b ii = M.mk_singleton_es (Act.Barrier b) ii

    (* Emit commit event *)
      let commit_bcc ii = M.mk_singleton_es (Act.Commit (Act.Bcc,None)) ii
      and commit_pred_txt txt ii =
        M.mk_singleton_es (Act.Commit (Act.Pred,txt)) ii

      let commit_pred ii = commit_pred_txt None ii

(* Compute amo semantics anotations from syntactic  ones *)

      let amo sz op mo rd rv ra ii =
        let open RISCV in
            let amo mo =
              let ra = read_reg_addr ra ii
              and rv = read_reg_data rv ii
              and rmem = fun loc -> read_mem_atomic sz mo loc RISCVExplicit.Exp ii
              and wmem = fun loc v -> write_mem_atomic sz mo RISCVExplicit.Exp loc v ii in
              (match op with
              | AMOSWAP -> M.linux_exch | _ -> M.amo (tr_opamo op))
                ra rv rmem wmem >>= fun r -> write_reg rd r ii in
            amo mo
      
      let get_ra test ii =
        let lbl =
          let a = ii.A.addr + 4 in
          let lbls = test.Test_herd.entry_points a in
          Label.norm lbls in
        match lbl with
        | Some l -> ii.A.addr2v l
        | None ->  V.intToV (ii.A.addr + 4)

      let v2tgt =
        let open Constant in
        function
        | M.A.V.Val (Symbolic (Virtual {name=Symbol.Label (_, lbl); _})) -> Some (B.Lbl lbl)
        | M.A.V.Val (Concrete i) -> Some (B.Addr (M.A.V.Cst.Scalar.to_int i))
        | _ -> None

      let do_indirect_jump test bds i ii v =
        match  v2tgt v with
        | Some tgt ->
          commit_bcc ii
          >>= fun () -> M.unitT (B.Jump (tgt,bds))
        | None ->
           match v with
           | M.A.V.Var(_) as v ->
              let lbls = get_exported_labels test in
              if Label.Full.Set.is_empty lbls  then begin
                if C.variant Variant.Telechat then M.unitT () >>! B.Exit
                else
                  Warn.fatal "Could find no potential target for indirect branch %s \
                    (potential targets are statically known labels)" (RISCV.dump_instruction i)
                end
              else
                commit_bcc ii
                >>= fun () -> B.indirectBranchT v lbls bds
        | _ -> Warn.fatal
            "illegal argument for the indirect branch instruction %s \
            (must be a label)" (RISCV.dump_instruction i)
      
(* Entry point *)
      let tr_sz = RISCV.tr_width

      let ra = RISCV.Ireg RISCV.X1

(* Fetch of an instruction, i.e., a read from a label *)
      let mk_fetch an loc v =
        let ac = Access.VIR in (* Instruction fetch seen as ordinary, non PTE, access *)
        Act.Access (Dir.R, loc, v, an, RISCV.nexp_ifetch, MachSize.Word, ac)

(*********************)
(* Instruction fetch *)
(*********************)

      let make_label_value proc lbl_str =
        A.V.cstToV (Constant.mk_sym_virtual_label proc lbl_str)

      let make_dummy_ifetchloc =
        A.V.cstToV (Constant.mk_sym_virtual_label 99 "dummyifetchloc")

      let read_loc_instr a ii =
        M.read_loc Port.No (mk_fetch RISCVAnnot.N) a ii


      let do_build_semantics test inst ii =
          begin match inst with
          | RISCV.INop-> B.next1T ()
          | RISCV.Ret when O.variant Variant.Telechat -> M.unitT () >>! B.Exit
          | RISCV.Li (r,k) ->
              let v = V.Cst.Scalar.of_int64 k |> V.scalarToV in
              write_reg r v ii >>= B.next1T
          | RISCV.OpI2 (RISCV.LUI,r1,k) ->
              (* put k into upper half of r1*)
              M.op (Op.ShiftLeft) (V.intToV k)
                (V.intToV 12) >>=
                fun v -> write_reg r1 v ii >>= B.next1T
          | RISCV.OpI (RISCV.ADDI,r1,r2,0) ->
            (* A MV*)
            read_reg_ord r2 ii
            >>= fun v -> write_reg r1 v ii
            >>= B.next1T
          | RISCV.OpI (op,r1,r2,k) ->
              read_reg_ord r2 ii >>=
              fun v -> M.op (tr_opi op) v (V.intToV k) >>=
                fun v -> write_reg r1 v ii >>= B.next1T
          | RISCV.OpA (RISCV.LA,r1,lbl) ->
              let v = ii.A.addr2v lbl in
              write_reg r1 v ii >>= B.next1T
          | RISCV.OpIW (op,r1,r2,k) ->
              read_reg_ord r2 ii >>= uxtw >>=
              fun v -> M.op (tr_opiw op) v (V.intToV k) >>= sxtw >>=
              fun v -> write_reg r1 v ii >>= B.next1T
          | RISCV.Op (op,r1,r2,r3) ->
              (read_reg_ord r2 ii >>|  read_reg_ord r3 ii) >>=
              (fun (v1,v2) -> M.op (tr_op op) v1 v2) >>=
              (fun v -> write_reg r1 v ii) >>= B.next1T
          | RISCV.OpW (op,r1,r2,r3) ->
              ((read_reg_ord r2 ii >>= uxtw)
               >>| (read_reg_ord r3 ii >>= uxtw)) >>=
              fun (v1,v2) -> M.op (tr_opw op) v1 v2 >>= sxtw >>=
              fun v -> write_reg r1 v ii >>= B.next1T
          | RISCV.J lbl -> B.branchT lbl
          | RISCV.JAL lbl -> 
                let v_ret = get_ra test ii in
                let write_ra = write_reg ra v_ret ii in
                let branch () = M.unitT (B.Jump (tgt2tgt ii (BranchTarget.Lbl lbl),[ra,v_ret])) in
                M.bind_order write_ra branch
          | RISCV.JR r as i -> read_reg_ord r ii >>= do_indirect_jump test [] i ii
          | RISCV.JALR r as i ->
                let v_ret = get_ra test ii in
                let read_rs1 = read_reg_ord r ii in
                let branch = read_rs1 >>= do_indirect_jump test [ra,v_ret] i ii in
                let write_ra = write_reg ra v_ret ii in
                write_ra >>| branch >>= fun (_, b) -> M.unitT b
          | RISCV.Bcc (cond,r1,r2,lbl) ->
              (read_reg_ord r1 ii >>| read_reg_ord r2 ii) >>=
              fun (v1,v2) -> M.op (tr_cond cond) v1 v2 >>=
                fun v -> commit_bcc ii >>= fun () -> B.bccT v lbl
          | RISCV.Load (sz,s,mo,r1,k,r2) ->
              let sz = tr_sz sz in
              let mk_load mo =
                read_reg_ord r2 ii >>=
                (fun a -> M.add a (V.intToV k)) >>=
                (fun ea -> read_mem sz mo ea RISCVExplicit.Exp ii) >>=
                xt_op s sz >>=
                (fun v -> write_reg r1 v ii) in
              mk_load mo >>= B.next1T

          | RISCV.Store (sz,mo,r1,k,r2) ->
              let sz = tr_sz sz in
              let mk_store mo =
                (read_reg_data r1 ii >>= uxt_op sz
                 >>| read_reg_addr r2 ii) >>=
                (fun (d,a) ->
                  (M.add a (V.intToV k)) >>=
                  (fun ea -> write_mem sz mo RISCVExplicit.Exp ea d ii)) in
              mk_store mo >>= B.next1T
          | RISCV.LoadReserve  ((RISCV.Double|RISCV.Word as sz),mo,r1,r2) ->
              read_reg_addr r2 ii >>=
              (fun ea ->
                write_reg RISCV.RESADDR ea ii
                >>|
                  (read_mem_atomic (tr_sz sz) mo ea RISCVExplicit.Exp ii
                   >>= fun v -> write_reg r1 v ii))
              >>= B.next2T
          | RISCV.StoreConditional
              ((RISCV.Double|RISCV.Word as sz),mo,r1,r2,r3) ->
              M.riscv_store_conditional
                (read_reg_ord RISCV.RESADDR ii)
                (read_reg_data r2 ii)
                (read_reg_addr r3 ii)
                (write_reg RISCV.RESADDR V.zero ii)
                (fun v -> write_reg_success r1 v ii)
                (fun ea resa v ->
                  write_mem_conditional (tr_sz sz) mo ea v resa ii)
              >>= B.next1T
          | RISCV.Amo (op,sz,mo,r1,r2,r3) ->
              amo (tr_sz sz) op mo r1 r2 r3 ii >>= B.next1T
          | RISCV.FenceIns b ->
              create_barrier b ii >>= B.next1T
          | RISCV.Ext (_,w,r1,r2) ->
            read_reg_ord r2 ii
            >>= M.op1 (Op.Sxt (RISCV.tr_width w))
            >>= fun v -> write_reg r1 v ii
            >>= B.next1T
          | ins -> Warn.fatal "RISCV, instruction '%s' not handled" (RISCV.dump_instruction ins)
          end

(* Compute a safe set of instructions that can
 * overwrite another. By convention, those are
 * instructions pointed to by "exported" labels.
 *)
      let get_overwriting_instrs test =
        RISCV.state_fold
          (fun _ v k ->
            match v with
            | V.Val (Constant.Instruction i) -> i::k
            | _ -> k)
          test.Test_herd.init_state []

(* Test all possible instructions, when appropriate *)
      let check_self test ii =
        let module InstrSet = RISCV.V.Cst.Instr.Set in
        let orig_inst = ii.A.inst in
        let lbls = get_exported_labels test in
        let is_exported =
          Label.Set.exists
            (fun lbl ->
              Label.Full.Set.exists
                (fun (_,lbl0) -> Misc.string_eq lbl lbl0)
                lbls)
            ii.A.labels in
        if is_exported then
          match Label.norm ii.A.labels with
          | None -> assert false
          | Some hd ->
              let insts =
                InstrSet.of_list
                  (get_overwriting_instrs test) in
              let insts =
                InstrSet.add orig_inst insts in
                (* Shadow default control sequencing operator *)
                let(>>*=) = M.bind_control_set_data_input_first in
                let a_v = make_label_value ii.A.fetch_proc hd in
                let a = (* Normalised address of instruction *)
                A.Location_global a_v in
              read_loc_instr a ii
                >>=
                fun actual_val ->
                InstrSet.fold
                  (* Ths first thing is the function, second is list, third is base case, so we have fault as base case *)
                    (fun inst k ->
                      M.op Op.Eq actual_val (V.instructionToV inst) >>==
                      fun cond -> M.choiceT cond
                          (commit_pred ii >>*=
                            fun () -> do_build_semantics test inst ii)
                          k)
                    insts
                    begin
                      (* Anything else than a legit instruction is a failure *)
                      (* Just end program since exceptions aren't implemented *)
                      M.unitT B.Exit
                    end
        else (* This isn't a CMODX'd instruction, but we need to create a fetch event for it *)
          let(>>*=) = M.bind_control_set_data_input_first in
          let a_v = make_dummy_ifetchloc in
          let a = (* Normalised address of instruction *)
            A.Location_global a_v in
            (
            read_loc_instr a ii
            >>=
            fun _ -> (* Here is where actual_val would be *)
              M.op Op.Eq (V.instructionToV orig_inst) (V.instructionToV orig_inst) >>==
                fun cond -> M.choiceT cond
                  (commit_pred ii >>*=
                    fun () -> do_build_semantics test orig_inst ii)
                    (M.unitT B.Exit))
      let build_semantics test ii =
        M.addT (A.next_po_index ii.A.program_order_index)
          begin
            if self then check_self test ii
            else do_build_semantics test ii.A.inst ii
          end

      let spurious_setaf _ = assert false

    end

  end
