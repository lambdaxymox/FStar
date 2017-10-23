open Prims
type name = FStar_Syntax_Syntax.bv[@@deriving show]
type env = FStar_TypeChecker_Env.env[@@deriving show]
type implicits = FStar_TypeChecker_Env.implicits[@@deriving show]
let normalize:
  FStar_TypeChecker_Normalize.step Prims.list ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun s  ->
    fun e  ->
      fun t  ->
        FStar_TypeChecker_Normalize.normalize_with_primitive_steps
          FStar_Reflection_Interpreter.reflection_primops s e t
let bnorm:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun e  -> fun t  -> normalize [] e t
type 'a tac =
  {
  tac_f: FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result;}
[@@deriving show]
let __proj__Mktac__item__tac_f:
  'a .
    'a tac ->
      FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  =
  fun projectee  ->
    match projectee with | { tac_f = __fname__tac_f;_} -> __fname__tac_f
let mk_tac:
  'a .
    (FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result) ->
      'a tac
  = fun f  -> { tac_f = f }
let run:
  'Auu____88 .
    'Auu____88 tac ->
      FStar_Tactics_Types.proofstate ->
        'Auu____88 FStar_Tactics_Result.__result
  = fun t  -> fun p  -> t.tac_f p
let ret: 'a . 'a -> 'a tac =
  fun x  -> mk_tac (fun p  -> FStar_Tactics_Result.Success (x, p))
let bind: 'a 'b . 'a tac -> ('a -> 'b tac) -> 'b tac =
  fun t1  ->
    fun t2  ->
      mk_tac
        (fun p  ->
           let uu____155 = run t1 p in
           match uu____155 with
           | FStar_Tactics_Result.Success (a,q) ->
               let uu____162 = t2 a in run uu____162 q
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed (msg, q))
let idtac: Prims.unit tac = ret ()
let goal_to_string: FStar_Tactics_Types.goal -> Prims.string =
  fun g  ->
    let g_binders =
      let uu____174 =
        FStar_TypeChecker_Env.all_binders g.FStar_Tactics_Types.context in
      FStar_All.pipe_right uu____174
        (FStar_Syntax_Print.binders_to_string ", ") in
    let w = bnorm g.FStar_Tactics_Types.context g.FStar_Tactics_Types.witness in
    let t = bnorm g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
    let uu____177 =
      FStar_TypeChecker_Normalize.term_to_string
        g.FStar_Tactics_Types.context w in
    let uu____178 =
      FStar_TypeChecker_Normalize.term_to_string
        g.FStar_Tactics_Types.context t in
    FStar_Util.format3 "%s |- %s : %s" g_binders uu____177 uu____178
let tacprint: Prims.string -> Prims.unit =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s
let tacprint1: Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      let uu____191 = FStar_Util.format1 s x in
      FStar_Util.print1 "TAC>> %s\n" uu____191
let tacprint2: Prims.string -> Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____204 = FStar_Util.format2 s x y in
        FStar_Util.print1 "TAC>> %s\n" uu____204
let tacprint3:
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> Prims.unit
  =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____221 = FStar_Util.format3 s x y z in
          FStar_Util.print1 "TAC>> %s\n" uu____221
let comp_to_typ: FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.typ =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____227) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____237) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
let is_irrelevant: FStar_Tactics_Types.goal -> Prims.bool =
  fun g  ->
    let uu____251 =
      let uu____256 =
        FStar_TypeChecker_Normalize.unfold_whnf g.FStar_Tactics_Types.context
          g.FStar_Tactics_Types.goal_ty in
      FStar_Syntax_Util.un_squash uu____256 in
    match uu____251 with
    | FStar_Pervasives_Native.Some t -> true
    | uu____262 -> false
let dump_goal:
  'Auu____273 . 'Auu____273 -> FStar_Tactics_Types.goal -> Prims.unit =
  fun ps  ->
    fun goal  -> let uu____283 = goal_to_string goal in tacprint uu____283
let dump_cur: FStar_Tactics_Types.proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      match ps.FStar_Tactics_Types.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____293 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____297 = FStar_List.hd ps.FStar_Tactics_Types.goals in
            dump_goal ps uu____297))
let ps_to_string:
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun uu____305  ->
    match uu____305 with
    | (msg,ps) ->
        let uu____312 = FStar_Util.string_of_int ps.FStar_Tactics_Types.depth in
        let uu____313 =
          FStar_Util.string_of_int
            (FStar_List.length ps.FStar_Tactics_Types.goals) in
        let uu____314 =
          let uu____315 =
            FStar_List.map goal_to_string ps.FStar_Tactics_Types.goals in
          FStar_String.concat "\n" uu____315 in
        let uu____318 =
          FStar_Util.string_of_int
            (FStar_List.length ps.FStar_Tactics_Types.smt_goals) in
        let uu____319 =
          let uu____320 =
            FStar_List.map goal_to_string ps.FStar_Tactics_Types.smt_goals in
          FStar_String.concat "\n" uu____320 in
        FStar_Util.format6
          "State dump @ depth %s(%s):\nACTIVE goals (%s):\n%s\nSMT goals (%s):\n%s"
          uu____312 msg uu____313 uu____314 uu____318 uu____319
let goal_to_json: FStar_Tactics_Types.goal -> FStar_Util.json =
  fun g  ->
    let g_binders =
      let uu____328 =
        FStar_TypeChecker_Env.all_binders g.FStar_Tactics_Types.context in
      FStar_All.pipe_right uu____328 FStar_Syntax_Print.binders_to_json in
    let uu____329 =
      let uu____336 =
        let uu____343 =
          let uu____348 =
            let uu____349 =
              let uu____356 =
                let uu____361 =
                  let uu____362 =
                    FStar_TypeChecker_Normalize.term_to_string
                      g.FStar_Tactics_Types.context
                      g.FStar_Tactics_Types.witness in
                  FStar_Util.JsonStr uu____362 in
                ("witness", uu____361) in
              let uu____363 =
                let uu____370 =
                  let uu____375 =
                    let uu____376 =
                      FStar_TypeChecker_Normalize.term_to_string
                        g.FStar_Tactics_Types.context
                        g.FStar_Tactics_Types.goal_ty in
                    FStar_Util.JsonStr uu____376 in
                  ("type", uu____375) in
                [uu____370] in
              uu____356 :: uu____363 in
            FStar_Util.JsonAssoc uu____349 in
          ("goal", uu____348) in
        [uu____343] in
      ("hyps", g_binders) :: uu____336 in
    FStar_Util.JsonAssoc uu____329
let ps_to_json:
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json
  =
  fun uu____408  ->
    match uu____408 with
    | (msg,ps) ->
        let uu____415 =
          let uu____422 =
            let uu____429 =
              let uu____434 =
                let uu____435 =
                  FStar_List.map goal_to_json ps.FStar_Tactics_Types.goals in
                FStar_Util.JsonList uu____435 in
              ("goals", uu____434) in
            let uu____438 =
              let uu____445 =
                let uu____450 =
                  let uu____451 =
                    FStar_List.map goal_to_json
                      ps.FStar_Tactics_Types.smt_goals in
                  FStar_Util.JsonList uu____451 in
                ("smt-goals", uu____450) in
              [uu____445] in
            uu____429 :: uu____438 in
          ("label", (FStar_Util.JsonStr msg)) :: uu____422 in
        FStar_Util.JsonAssoc uu____415
let dump_proofstate:
  FStar_Tactics_Types.proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____480  ->
           FStar_Options.set_option "print_effect_args"
             (FStar_Options.Bool true);
           FStar_Util.print_generic "proof-state" ps_to_string ps_to_json
             (msg, ps))
let print_proof_state1: Prims.string -> Prims.unit tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc in
         let subst1 = FStar_TypeChecker_Normalize.psc_subst psc in
         (let uu____502 = FStar_Tactics_Types.subst_proof_state subst1 ps in
          dump_cur uu____502 msg);
         FStar_Tactics_Result.Success ((), ps))
let print_proof_state: Prims.string -> Prims.unit tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc in
         let subst1 = FStar_TypeChecker_Normalize.psc_subst psc in
         (let uu____519 = FStar_Tactics_Types.subst_proof_state subst1 ps in
          dump_proofstate uu____519 msg);
         FStar_Tactics_Result.Success ((), ps))
let get: FStar_Tactics_Types.proofstate tac =
  mk_tac (fun p  -> FStar_Tactics_Result.Success (p, p))
let tac_verb_dbg: Prims.bool FStar_Pervasives_Native.option FStar_ST.ref =
  FStar_Util.mk_ref FStar_Pervasives_Native.None
let rec log:
  FStar_Tactics_Types.proofstate -> (Prims.unit -> Prims.unit) -> Prims.unit
  =
  fun ps  ->
    fun f  ->
      let uu____550 = FStar_ST.op_Bang tac_verb_dbg in
      match uu____550 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____604 =
              let uu____607 =
                FStar_TypeChecker_Env.debug
                  ps.FStar_Tactics_Types.main_context
                  (FStar_Options.Other "TacVerbose") in
              FStar_Pervasives_Native.Some uu____607 in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____604);
           log ps f)
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
let mlog: 'a . (Prims.unit -> Prims.unit) -> (Prims.unit -> 'a tac) -> 'a tac
  = fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ())
let fail: 'Auu____697 . Prims.string -> 'Auu____697 tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____708 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail") in
          if uu____708
          then dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
let fail1: 'Auu____716 . Prims.string -> Prims.string -> 'Auu____716 tac =
  fun msg  ->
    fun x  -> let uu____727 = FStar_Util.format1 msg x in fail uu____727
let fail2:
  'Auu____736 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____736 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____751 = FStar_Util.format2 msg x y in fail uu____751
let fail3:
  'Auu____762 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____762 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____781 = FStar_Util.format3 msg x y z in fail uu____781
let trytac': 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction () in
         let uu____813 = run t ps in
         match uu____813 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,uu____834) ->
             (FStar_Syntax_Unionfind.rollback tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps)))
let trytac: 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____861 = trytac' t in
    bind uu____861
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____888 -> ret FStar_Pervasives_Native.None)
let wrap_err: 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____917 = run t ps in
           match uu____917 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
let set: FStar_Tactics_Types.proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____935  -> FStar_Tactics_Result.Success ((), p))
let do_unify:
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t1  ->
      fun t2  ->
        try FStar_TypeChecker_Rel.teq_nosmt env t1 t2
        with | uu____953 -> false
let trysolve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun goal  ->
    fun solution  ->
      do_unify goal.FStar_Tactics_Types.context solution
        goal.FStar_Tactics_Types.witness
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____967 =
         let uu___135_968 = p in
         let uu____969 = FStar_List.tl p.FStar_Tactics_Types.goals in
         {
           FStar_Tactics_Types.main_context =
             (uu___135_968.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___135_968.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___135_968.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____969;
           FStar_Tactics_Types.smt_goals =
             (uu___135_968.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___135_968.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___135_968.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___135_968.FStar_Tactics_Types.psc)
         } in
       set uu____967)
let solve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun goal  ->
    fun solution  ->
      let uu____984 = trysolve goal solution in
      if uu____984
      then dismiss
      else
        (let uu____988 =
           let uu____989 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context solution in
           let uu____990 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.witness in
           let uu____991 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           FStar_Util.format3 "%s does not solve %s : %s" uu____989 uu____990
             uu____991 in
         fail uu____988)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___136_998 = p in
          {
            FStar_Tactics_Types.main_context =
              (uu___136_998.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___136_998.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___136_998.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___136_998.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___136_998.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___136_998.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___136_998.FStar_Tactics_Types.psc)
          }))
let check_valid_goal: FStar_Tactics_Types.goal -> Prims.unit =
  fun g  ->
    let b = true in
    let env = g.FStar_Tactics_Types.context in
    let b1 =
      b && (FStar_TypeChecker_Env.closed env g.FStar_Tactics_Types.witness) in
    let b2 =
      b1 && (FStar_TypeChecker_Env.closed env g.FStar_Tactics_Types.goal_ty) in
    let rec aux b3 e =
      let uu____1014 = FStar_TypeChecker_Env.pop_bv e in
      match uu____1014 with
      | FStar_Pervasives_Native.None  -> b3
      | FStar_Pervasives_Native.Some (bv,e1) ->
          let b4 =
            b3 &&
              (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort) in
          aux b4 e1 in
    let uu____1032 =
      let uu____1033 = aux b2 env in Prims.op_Negation uu____1033 in
    if uu____1032
    then
      let uu____1034 =
        let uu____1035 = goal_to_string g in
        FStar_Util.format1
          "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
          uu____1035 in
      FStar_Errors.warn
        (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos uu____1034
    else ()
let add_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___137_1055 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___137_1055.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___137_1055.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___137_1055.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___137_1055.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___137_1055.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___137_1055.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___137_1055.FStar_Tactics_Types.psc)
            }))
let add_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___138_1074 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___138_1074.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___138_1074.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___138_1074.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___138_1074.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___138_1074.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___138_1074.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___138_1074.FStar_Tactics_Types.psc)
            }))
let push_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___139_1093 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___139_1093.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___139_1093.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___139_1093.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___139_1093.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___139_1093.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___139_1093.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___139_1093.FStar_Tactics_Types.psc)
            }))
let push_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___140_1112 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___140_1112.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___140_1112.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___140_1112.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___140_1112.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___140_1112.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___140_1112.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___140_1112.FStar_Tactics_Types.psc)
            }))
let replace_cur: FStar_Tactics_Types.goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____1122  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___141_1135 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___141_1135.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___141_1135.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___141_1135.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___141_1135.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___141_1135.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___141_1135.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___141_1135.FStar_Tactics_Types.psc)
            }))
let new_uvar:
  Prims.string ->
    env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1164 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ in
        match uu____1164 with
        | (u,uu____1180,g_u) ->
            let uu____1194 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits in
            bind uu____1194 (fun uu____1198  -> ret u)
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1203 = FStar_Syntax_Util.un_squash t in
    match uu____1203 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1213 =
          let uu____1214 = FStar_Syntax_Subst.compress t' in
          uu____1214.FStar_Syntax_Syntax.n in
        (match uu____1213 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1218 -> false)
    | uu____1219 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1228 = FStar_Syntax_Util.un_squash t in
    match uu____1228 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1238 =
          let uu____1239 = FStar_Syntax_Subst.compress t' in
          uu____1239.FStar_Syntax_Syntax.n in
        (match uu____1238 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1243 -> false)
    | uu____1244 -> false
let cur_goal: FStar_Tactics_Types.goal tac =
  bind get
    (fun p  ->
       match p.FStar_Tactics_Types.goals with
       | [] -> fail "No more goals (1)"
       | hd1::tl1 -> ret hd1)
let mk_irrelevant_goal:
  Prims.string ->
    env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Options.optionstate -> FStar_Tactics_Types.goal tac
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let typ = FStar_Syntax_Util.mk_squash phi in
          let uu____1282 = new_uvar reason env typ in
          bind uu____1282
            (fun u  ->
               let goal =
                 {
                   FStar_Tactics_Types.context = env;
                   FStar_Tactics_Types.witness = u;
                   FStar_Tactics_Types.goal_ty = typ;
                   FStar_Tactics_Types.opts = opts;
                   FStar_Tactics_Types.is_guard = false
                 } in
               ret goal)
let __tc:
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.typ,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3 tac
  =
  fun e  ->
    fun t  ->
      bind get
        (fun ps  ->
           try
             let uu____1340 =
               (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                 e t in
             ret uu____1340
           with | e1 -> fail "not typeable")
let must_trivial: env -> FStar_TypeChecker_Env.guard_t -> Prims.unit tac =
  fun e  ->
    fun g  ->
      try
        let uu____1390 =
          let uu____1391 =
            let uu____1392 = FStar_TypeChecker_Rel.discharge_guard_no_smt e g in
            FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial uu____1392 in
          Prims.op_Negation uu____1391 in
        if uu____1390 then fail "got non-trivial guard" else ret ()
      with | uu____1401 -> fail "got non-trivial guard"
let tc: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ tac =
  fun t  ->
    let uu____1410 =
      bind cur_goal
        (fun goal  ->
           let uu____1416 = __tc goal.FStar_Tactics_Types.context t in
           bind uu____1416
             (fun uu____1436  ->
                match uu____1436 with
                | (t1,typ,guard) ->
                    let uu____1448 =
                      must_trivial goal.FStar_Tactics_Types.context guard in
                    bind uu____1448 (fun uu____1452  -> ret typ))) in
    FStar_All.pipe_left (wrap_err "tc") uu____1410
let add_irrelevant_goal:
  Prims.string ->
    env ->
      FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> Prims.unit tac
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____1477 = mk_irrelevant_goal reason env phi opts in
          bind uu____1477 (fun goal  -> add_goals [goal])
let istrivial: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  ->
    fun t  ->
      let steps =
        [FStar_TypeChecker_Normalize.Reify;
        FStar_TypeChecker_Normalize.UnfoldUntil
          FStar_Syntax_Syntax.Delta_constant;
        FStar_TypeChecker_Normalize.Primops;
        FStar_TypeChecker_Normalize.Simplify;
        FStar_TypeChecker_Normalize.UnfoldTac;
        FStar_TypeChecker_Normalize.Unmeta] in
      let t1 = normalize steps e t in is_true t1
let trivial: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____1499 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty in
       if uu____1499
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1503 =
            FStar_TypeChecker_Normalize.term_to_string
              goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1503))
let add_goal_from_guard:
  Prims.string ->
    env ->
      FStar_TypeChecker_Env.guard_t ->
        FStar_Options.optionstate -> Prims.unit tac
  =
  fun reason  ->
    fun e  ->
      fun g  ->
        fun opts  ->
          let uu____1524 =
            let uu____1525 = FStar_TypeChecker_Rel.simplify_guard e g in
            uu____1525.FStar_TypeChecker_Env.guard_f in
          match uu____1524 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1529 = istrivial e f in
              if uu____1529
              then ret ()
              else
                (let uu____1533 = mk_irrelevant_goal reason e f opts in
                 bind uu____1533
                   (fun goal  ->
                      let goal1 =
                        let uu___146_1540 = goal in
                        {
                          FStar_Tactics_Types.context =
                            (uu___146_1540.FStar_Tactics_Types.context);
                          FStar_Tactics_Types.witness =
                            (uu___146_1540.FStar_Tactics_Types.witness);
                          FStar_Tactics_Types.goal_ty =
                            (uu___146_1540.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___146_1540.FStar_Tactics_Types.opts);
                          FStar_Tactics_Types.is_guard = true
                        } in
                      push_goals [goal1]))
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____1546 = is_irrelevant g in
       if uu____1546
       then bind dismiss (fun uu____1550  -> add_smt_goals [g])
       else
         (let uu____1552 =
            FStar_TypeChecker_Normalize.term_to_string
              g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1552))
let divide:
  'a 'b .
    Prims.int ->
      'a tac -> 'b tac -> ('a,'b) FStar_Pervasives_Native.tuple2 tac
  =
  fun n1  ->
    fun l  ->
      fun r  ->
        bind get
          (fun p  ->
             let uu____1598 =
               try
                 let uu____1632 =
                   FStar_List.splitAt n1 p.FStar_Tactics_Types.goals in
                 ret uu____1632
               with | uu____1662 -> fail "divide: not enough goals" in
             bind uu____1598
               (fun uu____1689  ->
                  match uu____1689 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___147_1715 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___147_1715.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___147_1715.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___147_1715.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___147_1715.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___147_1715.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___147_1715.FStar_Tactics_Types.psc)
                        } in
                      let rp =
                        let uu___148_1717 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___148_1717.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___148_1717.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___148_1717.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___148_1717.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___148_1717.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___148_1717.FStar_Tactics_Types.psc)
                        } in
                      let uu____1718 = set lp in
                      bind uu____1718
                        (fun uu____1726  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1740 = set rp in
                                     bind uu____1740
                                       (fun uu____1748  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___149_1764 = p in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___149_1764.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___149_1764.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___149_1764.FStar_Tactics_Types.all_implicits);
                                                        FStar_Tactics_Types.goals
                                                          =
                                                          (FStar_List.append
                                                             lp'.FStar_Tactics_Types.goals
                                                             rp'.FStar_Tactics_Types.goals);
                                                        FStar_Tactics_Types.smt_goals
                                                          =
                                                          (FStar_List.append
                                                             lp'.FStar_Tactics_Types.smt_goals
                                                             (FStar_List.append
                                                                rp'.FStar_Tactics_Types.smt_goals
                                                                p.FStar_Tactics_Types.smt_goals));
                                                        FStar_Tactics_Types.depth
                                                          =
                                                          (uu___149_1764.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___149_1764.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___149_1764.FStar_Tactics_Types.psc)
                                                      } in
                                                    let uu____1765 = set p' in
                                                    bind uu____1765
                                                      (fun uu____1773  ->
                                                         ret (a, b))))))))))
let focus: 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1793 = divide (Prims.parse_int "1") f idtac in
    bind uu____1793
      (fun uu____1806  -> match uu____1806 with | (a,()) -> ret a)
let rec map: 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____1841::uu____1842 ->
             let uu____1845 =
               let uu____1854 = map tau in
               divide (Prims.parse_int "1") tau uu____1854 in
             bind uu____1845
               (fun uu____1872  ->
                  match uu____1872 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____1911 =
        bind t1
          (fun uu____1916  ->
             let uu____1917 = map t2 in
             bind uu____1917 (fun uu____1925  -> ret ())) in
      focus uu____1911
let intro: FStar_Syntax_Syntax.binder tac =
  bind cur_goal
    (fun goal  ->
       let uu____1936 =
         FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
       match uu____1936 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____1951 =
             let uu____1952 = FStar_Syntax_Util.is_total_comp c in
             Prims.op_Negation uu____1952 in
           if uu____1951
           then fail "Codomain is effectful"
           else
             (let env' =
                FStar_TypeChecker_Env.push_binders
                  goal.FStar_Tactics_Types.context [b] in
              let typ' = comp_to_typ c in
              let uu____1958 = new_uvar "intro" env' typ' in
              bind uu____1958
                (fun u  ->
                   let uu____1965 =
                     let uu____1966 =
                       FStar_Syntax_Util.abs [b] u
                         FStar_Pervasives_Native.None in
                     trysolve goal uu____1966 in
                   if uu____1965
                   then
                     let uu____1969 =
                       let uu____1972 =
                         let uu___152_1973 = goal in
                         let uu____1974 = bnorm env' u in
                         let uu____1975 = bnorm env' typ' in
                         {
                           FStar_Tactics_Types.context = env';
                           FStar_Tactics_Types.witness = uu____1974;
                           FStar_Tactics_Types.goal_ty = uu____1975;
                           FStar_Tactics_Types.opts =
                             (uu___152_1973.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___152_1973.FStar_Tactics_Types.is_guard)
                         } in
                       replace_cur uu____1972 in
                     bind uu____1969 (fun uu____1977  -> ret b)
                   else fail "intro: unification failed"))
       | FStar_Pervasives_Native.None  ->
           let uu____1983 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____1983)
let intro_rec:
  (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
    FStar_Pervasives_Native.tuple2 tac
  =
  bind cur_goal
    (fun goal  ->
       FStar_Util.print_string
         "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
       FStar_Util.print_string
         "WARNING (intro_rec): proceed at your own risk...\n";
       (let uu____2004 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
        match uu____2004 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____2023 =
              let uu____2024 = FStar_Syntax_Util.is_total_comp c in
              Prims.op_Negation uu____2024 in
            if uu____2023
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty in
               let bs =
                 let uu____2040 = FStar_Syntax_Syntax.mk_binder bv in
                 [uu____2040; b] in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs in
               let uu____2042 =
                 let uu____2045 = comp_to_typ c in
                 new_uvar "intro_rec" env' uu____2045 in
               bind uu____2042
                 (fun u  ->
                    let lb =
                      let uu____2061 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____2061 in
                    let body = FStar_Syntax_Syntax.bv_to_name bv in
                    let uu____2065 =
                      FStar_Syntax_Subst.close_let_rec [lb] body in
                    match uu____2065 with
                    | (lbs,body1) ->
                        let tm =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                            FStar_Pervasives_Native.None
                            (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos in
                        let res = trysolve goal tm in
                        if res
                        then
                          let uu____2102 =
                            let uu____2105 =
                              let uu___153_2106 = goal in
                              let uu____2107 = bnorm env' u in
                              let uu____2108 =
                                let uu____2109 = comp_to_typ c in
                                bnorm env' uu____2109 in
                              {
                                FStar_Tactics_Types.context = env';
                                FStar_Tactics_Types.witness = uu____2107;
                                FStar_Tactics_Types.goal_ty = uu____2108;
                                FStar_Tactics_Types.opts =
                                  (uu___153_2106.FStar_Tactics_Types.opts);
                                FStar_Tactics_Types.is_guard =
                                  (uu___153_2106.FStar_Tactics_Types.is_guard)
                              } in
                            replace_cur uu____2105 in
                          bind uu____2102
                            (fun uu____2116  ->
                               let uu____2117 =
                                 let uu____2122 =
                                   FStar_Syntax_Syntax.mk_binder bv in
                                 (uu____2122, b) in
                               ret uu____2117)
                        else fail "intro_rec: unification failed"))
        | FStar_Pervasives_Native.None  ->
            let uu____2136 =
              FStar_TypeChecker_Normalize.term_to_string
                goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2136))
let norm: FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         let steps =
           let uu____2161 = FStar_TypeChecker_Normalize.tr_norm_steps s in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____2161 in
         let w =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.witness in
         let t =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.goal_ty in
         replace_cur
           (let uu___154_2168 = goal in
            {
              FStar_Tactics_Types.context =
                (uu___154_2168.FStar_Tactics_Types.context);
              FStar_Tactics_Types.witness = w;
              FStar_Tactics_Types.goal_ty = t;
              FStar_Tactics_Types.opts =
                (uu___154_2168.FStar_Tactics_Types.opts);
              FStar_Tactics_Types.is_guard =
                (uu___154_2168.FStar_Tactics_Types.is_guard)
            }))
let norm_term_env:
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2189 =
          bind get
            (fun ps  ->
               let uu____2195 = __tc e t in
               bind uu____2195
                 (fun uu____2217  ->
                    match uu____2217 with
                    | (t1,uu____2227,guard) ->
                        (FStar_TypeChecker_Rel.force_trivial_guard e guard;
                         (let steps =
                            let uu____2233 =
                              FStar_TypeChecker_Normalize.tr_norm_steps s in
                            FStar_List.append
                              [FStar_TypeChecker_Normalize.Reify;
                              FStar_TypeChecker_Normalize.UnfoldTac]
                              uu____2233 in
                          let t2 =
                            normalize steps
                              ps.FStar_Tactics_Types.main_context t1 in
                          ret t2)))) in
        FStar_All.pipe_left (wrap_err "norm_term") uu____2189
let __exact: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun force_guard  ->
    fun t  ->
      bind cur_goal
        (fun goal  ->
           let uu____2256 = __tc goal.FStar_Tactics_Types.context t in
           bind uu____2256
             (fun uu____2276  ->
                match uu____2276 with
                | (t1,typ,guard) ->
                    let uu____2288 =
                      if force_guard
                      then
                        must_trivial goal.FStar_Tactics_Types.context guard
                      else
                        add_goal_from_guard "__exact typing"
                          goal.FStar_Tactics_Types.context guard
                          goal.FStar_Tactics_Types.opts in
                    bind uu____2288
                      (fun uu____2296  ->
                         let uu____2297 =
                           do_unify goal.FStar_Tactics_Types.context typ
                             goal.FStar_Tactics_Types.goal_ty in
                         if uu____2297
                         then solve goal t1
                         else
                           (let uu____2301 =
                              FStar_TypeChecker_Normalize.term_to_string
                                goal.FStar_Tactics_Types.context t1 in
                            let uu____2302 =
                              let uu____2303 =
                                bnorm goal.FStar_Tactics_Types.context typ in
                              FStar_TypeChecker_Normalize.term_to_string
                                goal.FStar_Tactics_Types.context uu____2303 in
                            let uu____2304 =
                              FStar_TypeChecker_Normalize.term_to_string
                                goal.FStar_Tactics_Types.context
                                goal.FStar_Tactics_Types.goal_ty in
                            fail3
                              "%s : %s does not exactly solve the goal %s"
                              uu____2301 uu____2302 uu____2304))))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____2313 =
      mlog
        (fun uu____2318  ->
           let uu____2319 = FStar_Syntax_Print.term_to_string tm in
           FStar_Util.print1 "exact: tm = %s\n" uu____2319)
        (fun uu____2322  ->
           let uu____2323 = __exact true tm in focus uu____2323) in
    FStar_All.pipe_left (wrap_err "exact") uu____2313
let exact_guard: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____2338 =
      mlog
        (fun uu____2343  ->
           let uu____2344 = FStar_Syntax_Print.term_to_string tm in
           FStar_Util.print1 "exact_guard: tm = %s\n" uu____2344)
        (fun uu____2347  ->
           let uu____2348 = __exact false tm in focus uu____2348) in
    FStar_All.pipe_left (wrap_err "exact_guard") uu____2338
let uvar_free_in_goal:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2367 =
             let uu____2374 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty in
             FStar_Util.set_elements uu____2374 in
           FStar_List.map FStar_Pervasives_Native.fst uu____2367 in
         FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars)
let uvar_free:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.proofstate -> Prims.bool =
  fun u  ->
    fun ps  ->
      FStar_List.existsML (uvar_free_in_goal u) ps.FStar_Tactics_Types.goals
exception NoUnif
let uu___is_NoUnif: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2401 -> false
let rec __apply:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> Prims.unit tac
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        bind cur_goal
          (fun goal  ->
             let uu____2421 =
               let uu____2426 = __exact true tm in trytac uu____2426 in
             bind uu____2421
               (fun r  ->
                  match r with
                  | FStar_Pervasives_Native.Some r1 -> ret ()
                  | FStar_Pervasives_Native.None  ->
                      let uu____2439 = FStar_Syntax_Util.arrow_one typ in
                      (match uu____2439 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise NoUnif
                       | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                           mlog
                             (fun uu____2471  ->
                                let uu____2472 =
                                  FStar_Syntax_Print.binder_to_string
                                    (bv, aq) in
                                FStar_Util.print1
                                  "__apply: pushing binder %s\n" uu____2472)
                             (fun uu____2475  ->
                                let uu____2476 =
                                  let uu____2477 =
                                    FStar_Syntax_Util.is_total_comp c in
                                  Prims.op_Negation uu____2477 in
                                if uu____2476
                                then fail "apply: not total codomain"
                                else
                                  (let uu____2481 =
                                     new_uvar "apply"
                                       goal.FStar_Tactics_Types.context
                                       bv.FStar_Syntax_Syntax.sort in
                                   bind uu____2481
                                     (fun u  ->
                                        let tm' =
                                          FStar_Syntax_Syntax.mk_Tm_app tm
                                            [(u, aq)]
                                            FStar_Pervasives_Native.None
                                            (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                        let typ' =
                                          let uu____2501 = comp_to_typ c in
                                          FStar_All.pipe_left
                                            (FStar_Syntax_Subst.subst
                                               [FStar_Syntax_Syntax.NT
                                                  (bv, u)]) uu____2501 in
                                        let uu____2502 =
                                          __apply uopt tm' typ' in
                                        bind uu____2502
                                          (fun uu____2510  ->
                                             let u1 =
                                               bnorm
                                                 goal.FStar_Tactics_Types.context
                                                 u in
                                             let uu____2512 =
                                               let uu____2513 =
                                                 let uu____2516 =
                                                   let uu____2517 =
                                                     FStar_Syntax_Util.head_and_args
                                                       u1 in
                                                   FStar_Pervasives_Native.fst
                                                     uu____2517 in
                                                 FStar_Syntax_Subst.compress
                                                   uu____2516 in
                                               uu____2513.FStar_Syntax_Syntax.n in
                                             match uu____2512 with
                                             | FStar_Syntax_Syntax.Tm_uvar
                                                 (uvar,uu____2545) ->
                                                 bind get
                                                   (fun ps  ->
                                                      let uu____2573 =
                                                        uopt &&
                                                          (uvar_free uvar ps) in
                                                      if uu____2573
                                                      then ret ()
                                                      else
                                                        (let uu____2577 =
                                                           let uu____2580 =
                                                             let uu___155_2581
                                                               = goal in
                                                             let uu____2582 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 u1 in
                                                             let uu____2583 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 bv.FStar_Syntax_Syntax.sort in
                                                             {
                                                               FStar_Tactics_Types.context
                                                                 =
                                                                 (uu___155_2581.FStar_Tactics_Types.context);
                                                               FStar_Tactics_Types.witness
                                                                 = uu____2582;
                                                               FStar_Tactics_Types.goal_ty
                                                                 = uu____2583;
                                                               FStar_Tactics_Types.opts
                                                                 =
                                                                 (uu___155_2581.FStar_Tactics_Types.opts);
                                                               FStar_Tactics_Types.is_guard
                                                                 = false
                                                             } in
                                                           [uu____2580] in
                                                         add_goals uu____2577))
                                             | t -> ret ())))))))
let try_unif: 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
let apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      let uu____2634 =
        mlog
          (fun uu____2639  ->
             let uu____2640 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "apply: tm = %s\n" uu____2640)
          (fun uu____2642  ->
             bind cur_goal
               (fun goal  ->
                  let uu____2646 = __tc goal.FStar_Tactics_Types.context tm in
                  bind uu____2646
                    (fun uu____2667  ->
                       match uu____2667 with
                       | (tm1,typ,guard) ->
                           let uu____2679 =
                             let uu____2682 =
                               let uu____2685 = __apply uopt tm1 typ in
                               bind uu____2685
                                 (fun uu____2689  ->
                                    add_goal_from_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts) in
                             focus uu____2682 in
                           let uu____2690 =
                             let uu____2693 =
                               FStar_TypeChecker_Normalize.term_to_string
                                 goal.FStar_Tactics_Types.context tm1 in
                             let uu____2694 =
                               FStar_TypeChecker_Normalize.term_to_string
                                 goal.FStar_Tactics_Types.context typ in
                             let uu____2695 =
                               FStar_TypeChecker_Normalize.term_to_string
                                 goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____2693 uu____2694 uu____2695 in
                           try_unif uu____2679 uu____2690))) in
      FStar_All.pipe_left (wrap_err "apply") uu____2634
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____2708 =
      let uu____2711 =
        mlog
          (fun uu____2716  ->
             let uu____2717 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____2717)
          (fun uu____2720  ->
             let is_unit_t t =
               let uu____2725 =
                 let uu____2726 = FStar_Syntax_Subst.compress t in
                 uu____2726.FStar_Syntax_Syntax.n in
               match uu____2725 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____2730 -> false in
             bind cur_goal
               (fun goal  ->
                  let uu____2734 = __tc goal.FStar_Tactics_Types.context tm in
                  bind uu____2734
                    (fun uu____2756  ->
                       match uu____2756 with
                       | (tm1,t,guard) ->
                           let uu____2768 =
                             FStar_Syntax_Util.arrow_formals_comp t in
                           (match uu____2768 with
                            | (bs,comp) ->
                                if
                                  Prims.op_Negation
                                    (FStar_Syntax_Util.is_lemma_comp comp)
                                then fail "not a lemma"
                                else
                                  (let uu____2798 =
                                     FStar_List.fold_left
                                       (fun uu____2844  ->
                                          fun uu____2845  ->
                                            match (uu____2844, uu____2845)
                                            with
                                            | ((uvs,guard1,subst1),(b,aq)) ->
                                                let b_t =
                                                  FStar_Syntax_Subst.subst
                                                    subst1
                                                    b.FStar_Syntax_Syntax.sort in
                                                let uu____2948 =
                                                  is_unit_t b_t in
                                                if uu____2948
                                                then
                                                  (((FStar_Syntax_Util.exp_unit,
                                                      aq) :: uvs), guard1,
                                                    ((FStar_Syntax_Syntax.NT
                                                        (b,
                                                          FStar_Syntax_Util.exp_unit))
                                                    :: subst1))
                                                else
                                                  (let uu____2986 =
                                                     FStar_TypeChecker_Util.new_implicit_var
                                                       "apply_lemma"
                                                       (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                       goal.FStar_Tactics_Types.context
                                                       b_t in
                                                   match uu____2986 with
                                                   | (u,uu____3016,g_u) ->
                                                       let uu____3030 =
                                                         FStar_TypeChecker_Rel.conj_guard
                                                           guard1 g_u in
                                                       (((u, aq) :: uvs),
                                                         uu____3030,
                                                         ((FStar_Syntax_Syntax.NT
                                                             (b, u)) ::
                                                         subst1))))
                                       ([], guard, []) bs in
                                   match uu____2798 with
                                   | (uvs,implicits,subst1) ->
                                       let uvs1 = FStar_List.rev uvs in
                                       let comp1 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp in
                                       let uu____3100 =
                                         let uu____3109 =
                                           let uu____3118 =
                                             FStar_Syntax_Util.comp_to_comp_typ
                                               comp1 in
                                           uu____3118.FStar_Syntax_Syntax.effect_args in
                                         match uu____3109 with
                                         | pre::post::uu____3129 ->
                                             ((FStar_Pervasives_Native.fst
                                                 pre),
                                               (FStar_Pervasives_Native.fst
                                                  post))
                                         | uu____3170 ->
                                             failwith
                                               "apply_lemma: impossible: not a lemma" in
                                       (match uu____3100 with
                                        | (pre,post) ->
                                            let post1 =
                                              let uu____3202 =
                                                let uu____3211 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    FStar_Syntax_Util.exp_unit in
                                                [uu____3211] in
                                              FStar_Syntax_Util.mk_app post
                                                uu____3202 in
                                            let uu____3212 =
                                              let uu____3213 =
                                                let uu____3214 =
                                                  FStar_Syntax_Util.mk_squash
                                                    post1 in
                                                do_unify
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3214
                                                  goal.FStar_Tactics_Types.goal_ty in
                                              Prims.op_Negation uu____3213 in
                                            if uu____3212
                                            then
                                              let uu____3217 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  goal.FStar_Tactics_Types.context
                                                  tm1 in
                                              let uu____3218 =
                                                let uu____3219 =
                                                  FStar_Syntax_Util.mk_squash
                                                    post1 in
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3219 in
                                              let uu____3220 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  goal.FStar_Tactics_Types.context
                                                  goal.FStar_Tactics_Types.goal_ty in
                                              fail3
                                                "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                uu____3217 uu____3218
                                                uu____3220
                                            else
                                              (let solution =
                                                 let uu____3223 =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm1 uvs1
                                                     FStar_Pervasives_Native.None
                                                     (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                                 FStar_TypeChecker_Normalize.normalize
                                                   [FStar_TypeChecker_Normalize.Beta]
                                                   goal.FStar_Tactics_Types.context
                                                   uu____3223 in
                                               let uu____3224 =
                                                 add_implicits
                                                   implicits.FStar_TypeChecker_Env.implicits in
                                               bind uu____3224
                                                 (fun uu____3230  ->
                                                    let implicits1 =
                                                      FStar_All.pipe_right
                                                        implicits.FStar_TypeChecker_Env.implicits
                                                        (FStar_List.filter
                                                           (fun uu____3298 
                                                              ->
                                                              match uu____3298
                                                              with
                                                              | (uu____3311,uu____3312,uu____3313,tm2,uu____3315,uu____3316)
                                                                  ->
                                                                  let uu____3317
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    tm2 in
                                                                  (match uu____3317
                                                                   with
                                                                   | 
                                                                   (hd1,uu____3333)
                                                                    ->
                                                                    let uu____3354
                                                                    =
                                                                    let uu____3355
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1 in
                                                                    uu____3355.FStar_Syntax_Syntax.n in
                                                                    (match uu____3354
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____3358
                                                                    -> true
                                                                    | 
                                                                    uu____3375
                                                                    -> false)))) in
                                                    let uu____3376 =
                                                      solve goal solution in
                                                    bind uu____3376
                                                      (fun uu____3387  ->
                                                         let is_free_uvar uv
                                                           t1 =
                                                           let free_uvars =
                                                             let uu____3398 =
                                                               let uu____3405
                                                                 =
                                                                 FStar_Syntax_Free.uvars
                                                                   t1 in
                                                               FStar_Util.set_elements
                                                                 uu____3405 in
                                                             FStar_List.map
                                                               FStar_Pervasives_Native.fst
                                                               uu____3398 in
                                                           FStar_List.existsML
                                                             (fun u  ->
                                                                FStar_Syntax_Unionfind.equiv
                                                                  u uv)
                                                             free_uvars in
                                                         let appears uv goals
                                                           =
                                                           FStar_List.existsML
                                                             (fun g'  ->
                                                                is_free_uvar
                                                                  uv
                                                                  g'.FStar_Tactics_Types.goal_ty)
                                                             goals in
                                                         let checkone t1
                                                           goals =
                                                           let uu____3446 =
                                                             FStar_Syntax_Util.head_and_args
                                                               t1 in
                                                           match uu____3446
                                                           with
                                                           | (hd1,uu____3462)
                                                               ->
                                                               (match 
                                                                  hd1.FStar_Syntax_Syntax.n
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____3484)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                | uu____3509
                                                                    -> false) in
                                                         let sub_goals =
                                                           FStar_All.pipe_right
                                                             implicits1
                                                             (FStar_List.map
                                                                (fun
                                                                   uu____3551
                                                                    ->
                                                                   match uu____3551
                                                                   with
                                                                   | 
                                                                   (_msg,_env,_uvar,term,typ,uu____3569)
                                                                    ->
                                                                    let uu___158_3570
                                                                    = goal in
                                                                    let uu____3571
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term in
                                                                    let uu____3572
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___158_3570.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3571;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3572;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___158_3570.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___158_3570.FStar_Tactics_Types.is_guard)
                                                                    })) in
                                                         let rec filter' f xs
                                                           =
                                                           match xs with
                                                           | [] -> []
                                                           | x::xs1 ->
                                                               let uu____3610
                                                                 = f x xs1 in
                                                               if uu____3610
                                                               then
                                                                 let uu____3613
                                                                   =
                                                                   filter' f
                                                                    xs1 in
                                                                 x ::
                                                                   uu____3613
                                                               else
                                                                 filter' f
                                                                   xs1 in
                                                         let sub_goals1 =
                                                           filter'
                                                             (fun g  ->
                                                                fun goals  ->
                                                                  let uu____3627
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals in
                                                                  Prims.op_Negation
                                                                    uu____3627)
                                                             sub_goals in
                                                         let uu____3628 =
                                                           add_goal_from_guard
                                                             "apply_lemma guard"
                                                             goal.FStar_Tactics_Types.context
                                                             guard
                                                             goal.FStar_Tactics_Types.opts in
                                                         bind uu____3628
                                                           (fun uu____3633 
                                                              ->
                                                              let uu____3634
                                                                =
                                                                let uu____3637
                                                                  =
                                                                  let uu____3638
                                                                    =
                                                                    let uu____3639
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    pre in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____3639 in
                                                                  Prims.op_Negation
                                                                    uu____3638 in
                                                                if uu____3637
                                                                then
                                                                  add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    goal.FStar_Tactics_Types.context
                                                                    pre
                                                                    goal.FStar_Tactics_Types.opts
                                                                else ret () in
                                                              bind uu____3634
                                                                (fun
                                                                   uu____3644
                                                                    ->
                                                                   add_goals
                                                                    sub_goals1))))))))))) in
      focus uu____2711 in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____2708
let destruct_eq':
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3665 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____3665 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____3675::(e1,uu____3677)::(e2,uu____3679)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____3738 -> FStar_Pervasives_Native.None
let destruct_eq:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3761 = destruct_eq' typ in
    match uu____3761 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____3791 = FStar_Syntax_Util.un_squash typ in
        (match uu____3791 with
         | FStar_Pervasives_Native.Some typ1 -> destruct_eq' typ1
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
let split_env:
  FStar_Syntax_Syntax.bv ->
    env ->
      (env,FStar_Syntax_Syntax.bv Prims.list) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  =
  fun bvar  ->
    fun e  ->
      let rec aux e1 =
        let uu____3849 = FStar_TypeChecker_Env.pop_bv e1 in
        match uu____3849 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____3897 = aux e' in
               FStar_Util.map_opt uu____3897
                 (fun uu____3921  ->
                    match uu____3921 with | (e'',bvs) -> (e'', (bv' :: bvs)))) in
      let uu____3942 = aux e in
      FStar_Util.map_opt uu____3942
        (fun uu____3966  ->
           match uu____3966 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
let push_bvs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list -> FStar_TypeChecker_Env.env
  =
  fun e  ->
    fun bvs  ->
      FStar_List.fold_left
        (fun e1  -> fun b  -> FStar_TypeChecker_Env.push_bv e1 b) e bvs
let subst_goal:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.bv ->
      FStar_Syntax_Syntax.subst_elt Prims.list ->
        FStar_Tactics_Types.goal ->
          FStar_Tactics_Types.goal FStar_Pervasives_Native.option
  =
  fun b1  ->
    fun b2  ->
      fun s  ->
        fun g  ->
          let uu____4027 = split_env b1 g.FStar_Tactics_Types.context in
          FStar_Util.map_opt uu____4027
            (fun uu____4051  ->
               match uu____4051 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___159_4068 = bv in
                     let uu____4069 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___159_4068.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___159_4068.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____4069
                     } in
                   let bvs1 = FStar_List.map s1 bvs in
                   let c = push_bvs e0 (b2 :: bvs1) in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty in
                   let uu___160_4078 = g in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___160_4078.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___160_4078.FStar_Tactics_Types.is_guard)
                   })
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____4092 = h in
         match uu____4092 with
         | (bv,uu____4096) ->
             mlog
               (fun uu____4100  ->
                  let uu____4101 = FStar_Syntax_Print.bv_to_string bv in
                  let uu____4102 =
                    FStar_Syntax_Print.term_to_string
                      bv.FStar_Syntax_Syntax.sort in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____4101
                    uu____4102)
               (fun uu____4105  ->
                  let uu____4106 =
                    split_env bv goal.FStar_Tactics_Types.context in
                  match uu____4106 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____4135 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort in
                      (match uu____4135 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____4150 =
                             let uu____4151 = FStar_Syntax_Subst.compress x in
                             uu____4151.FStar_Syntax_Syntax.n in
                           (match uu____4150 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)] in
                                let s1 bv1 =
                                  let uu___161_4164 = bv1 in
                                  let uu____4165 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___161_4164.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___161_4164.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____4165
                                  } in
                                let bvs1 = FStar_List.map s1 bvs in
                                let uu____4171 =
                                  let uu___162_4172 = goal in
                                  let uu____4173 = push_bvs e0 (bv :: bvs1) in
                                  let uu____4174 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness in
                                  let uu____4175 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty in
                                  {
                                    FStar_Tactics_Types.context = uu____4173;
                                    FStar_Tactics_Types.witness = uu____4174;
                                    FStar_Tactics_Types.goal_ty = uu____4175;
                                    FStar_Tactics_Types.opts =
                                      (uu___162_4172.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___162_4172.FStar_Tactics_Types.is_guard)
                                  } in
                                replace_cur uu____4171
                            | uu____4176 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____4177 ->
                           fail "rewrite: Not an equality hypothesis")))
let rename_to: FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____4204 = b in
           match uu____4204 with
           | (bv,uu____4208) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___163_4212 = bv in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___163_4212.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___163_4212.FStar_Syntax_Syntax.sort)
                    }) in
               let s1 =
                 let uu____4216 =
                   let uu____4217 =
                     let uu____4224 = FStar_Syntax_Syntax.bv_to_name bv' in
                     (bv, uu____4224) in
                   FStar_Syntax_Syntax.NT uu____4217 in
                 [uu____4216] in
               let uu____4225 = subst_goal bv bv' s1 goal in
               (match uu____4225 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
let binder_retype: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4245 = b in
         match uu____4245 with
         | (bv,uu____4249) ->
             let uu____4250 = split_env bv goal.FStar_Tactics_Types.context in
             (match uu____4250 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____4279 = FStar_Syntax_Util.type_u () in
                  (match uu____4279 with
                   | (ty,u) ->
                       let uu____4288 = new_uvar "binder_retype" e0 ty in
                       bind uu____4288
                         (fun t'  ->
                            let bv'' =
                              let uu___164_4298 = bv in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___164_4298.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___164_4298.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              } in
                            let s =
                              let uu____4302 =
                                let uu____4303 =
                                  let uu____4310 =
                                    FStar_Syntax_Syntax.bv_to_name bv'' in
                                  (bv, uu____4310) in
                                FStar_Syntax_Syntax.NT uu____4303 in
                              [uu____4302] in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___165_4318 = b1 in
                                   let uu____4319 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___165_4318.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___165_4318.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____4319
                                   }) bvs in
                            let env' = push_bvs e0 (bv'' :: bvs1) in
                            bind dismiss
                              (fun uu____4325  ->
                                 let uu____4326 =
                                   let uu____4329 =
                                     let uu____4332 =
                                       let uu___166_4333 = goal in
                                       let uu____4334 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness in
                                       let uu____4335 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____4334;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____4335;
                                         FStar_Tactics_Types.opts =
                                           (uu___166_4333.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___166_4333.FStar_Tactics_Types.is_guard)
                                       } in
                                     [uu____4332] in
                                   add_goals uu____4329 in
                                 bind uu____4326
                                   (fun uu____4338  ->
                                      let uu____4339 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t' in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____4339
                                        goal.FStar_Tactics_Types.opts))))))
let norm_binder_type:
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> Prims.unit tac
  =
  fun s  ->
    fun b  ->
      bind cur_goal
        (fun goal  ->
           let uu____4362 = b in
           match uu____4362 with
           | (bv,uu____4366) ->
               let uu____4367 = split_env bv goal.FStar_Tactics_Types.context in
               (match uu____4367 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____4399 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____4399 in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort in
                    let bv' =
                      let uu___167_4404 = bv in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___167_4404.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___167_4404.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      } in
                    let env' = push_bvs e0 (bv' :: bvs) in
                    replace_cur
                      (let uu___168_4408 = goal in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___168_4408.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___168_4408.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___168_4408.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___168_4408.FStar_Tactics_Types.is_guard)
                       })))
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4414 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4414 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____4436 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____4436 in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None in
           replace_cur
             (let uu___169_4470 = goal in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___169_4470.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___169_4470.FStar_Tactics_Types.is_guard)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____4482 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4482 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____4503 = FStar_Syntax_Print.bv_to_string x in
               let uu____4504 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____4503 uu____4504
             else revert)
let clear_top: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4511 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4511 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fns_ty =
             FStar_Syntax_Free.names goal.FStar_Tactics_Types.goal_ty in
           let uu____4533 = FStar_Util.set_mem x fns_ty in
           if uu____4533
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____4537 =
                new_uvar "clear_top" env' goal.FStar_Tactics_Types.goal_ty in
              bind uu____4537
                (fun u  ->
                   let uu____4543 =
                     let uu____4544 = trysolve goal u in
                     Prims.op_Negation uu____4544 in
                   if uu____4543
                   then fail "clear: unification failed"
                   else
                     (let new_goal =
                        let uu___170_4549 = goal in
                        let uu____4550 = bnorm env' u in
                        {
                          FStar_Tactics_Types.context = env';
                          FStar_Tactics_Types.witness = uu____4550;
                          FStar_Tactics_Types.goal_ty =
                            (uu___170_4549.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___170_4549.FStar_Tactics_Types.opts);
                          FStar_Tactics_Types.is_guard =
                            (uu___170_4549.FStar_Tactics_Types.is_guard)
                        } in
                      bind dismiss (fun uu____4552  -> add_goals [new_goal])))))
let rec clear: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4564 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4564 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (b',env') ->
             if FStar_Syntax_Syntax.bv_eq (FStar_Pervasives_Native.fst b) b'
             then clear_top
             else
               bind revert
                 (fun uu____4588  ->
                    let uu____4589 = clear b in
                    bind uu____4589
                      (fun uu____4593  ->
                         bind intro (fun uu____4595  -> ret ()))))
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___171_4612 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___171_4612.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___171_4612.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___171_4612.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___171_4612.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____4614  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___172_4631 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___172_4631.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___172_4631.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___172_4631.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___172_4631.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____4633  -> add_goals [g']))
let rec mapM: 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____4675 = f x in
          bind uu____4675
            (fun y  ->
               let uu____4683 = mapM f xs in
               bind uu____4683 (fun ys  -> ret (y :: ys)))
let rec tac_fold_env:
  FStar_Tactics_Types.direction ->
    (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
      env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun d  ->
    fun f  ->
      fun env  ->
        fun t  ->
          let tn =
            let uu____4733 = FStar_Syntax_Subst.compress t in
            uu____4733.FStar_Syntax_Syntax.n in
          let uu____4736 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___174_4742 = t in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___174_4742.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___174_4742.FStar_Syntax_Syntax.vars)
                 })
            else ret t in
          bind uu____4736
            (fun t1  ->
               let tn1 =
                 let uu____4750 =
                   let uu____4751 = FStar_Syntax_Subst.compress t1 in
                   uu____4751.FStar_Syntax_Syntax.n in
                 match uu____4750 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let ff = tac_fold_env d f env in
                     let uu____4783 = ff hd1 in
                     bind uu____4783
                       (fun hd2  ->
                          let fa uu____4803 =
                            match uu____4803 with
                            | (a,q) ->
                                let uu____4816 = ff a in
                                bind uu____4816 (fun a1  -> ret (a1, q)) in
                          let uu____4829 = mapM fa args in
                          bind uu____4829
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____4889 = FStar_Syntax_Subst.open_term bs t2 in
                     (match uu____4889 with
                      | (bs1,t') ->
                          let uu____4898 =
                            let uu____4901 =
                              FStar_TypeChecker_Env.push_binders env bs1 in
                            tac_fold_env d f uu____4901 t' in
                          bind uu____4898
                            (fun t''  ->
                               let uu____4905 =
                                 let uu____4906 =
                                   let uu____4923 =
                                     FStar_Syntax_Subst.close_binders bs1 in
                                   let uu____4924 =
                                     FStar_Syntax_Subst.close bs1 t'' in
                                   (uu____4923, uu____4924, k) in
                                 FStar_Syntax_Syntax.Tm_abs uu____4906 in
                               ret uu____4905))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | uu____4945 -> ret tn in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___173_4952 = t1 in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___173_4952.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___173_4952.FStar_Syntax_Syntax.vars)
                      } in
                    if d = FStar_Tactics_Types.BottomUp
                    then f env t'
                    else ret t'))
let pointwise_rec:
  FStar_Tactics_Types.proofstate ->
    Prims.unit tac ->
      FStar_Options.optionstate ->
        FStar_TypeChecker_Env.env ->
          FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun ps  ->
    fun tau  ->
      fun opts  ->
        fun env  ->
          fun t  ->
            let uu____4986 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____4986 with
            | (t1,lcomp,g) ->
                let uu____4998 =
                  (let uu____5001 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp in
                   Prims.op_Negation uu____5001) ||
                    (let uu____5003 = FStar_TypeChecker_Rel.is_trivial g in
                     Prims.op_Negation uu____5003) in
                if uu____4998
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                     let uu____5013 = new_uvar "pointwise_rec" env typ in
                     bind uu____5013
                       (fun ut  ->
                          log ps
                            (fun uu____5024  ->
                               let uu____5025 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____5026 =
                                 FStar_Syntax_Print.term_to_string ut in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____5025 uu____5026);
                          (let uu____5027 =
                             let uu____5030 =
                               let uu____5031 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ in
                               FStar_Syntax_Util.mk_eq2 uu____5031 typ t1 ut in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____5030 opts in
                           bind uu____5027
                             (fun uu____5034  ->
                                let uu____5035 =
                                  bind tau
                                    (fun uu____5041  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut in
                                       log ps
                                         (fun uu____5047  ->
                                            let uu____5048 =
                                              FStar_Syntax_Print.term_to_string
                                                t1 in
                                            let uu____5049 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1 in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____5048 uu____5049);
                                       ret ut1) in
                                focus uu____5035))) in
                   let uu____5050 = trytac' rewrite_eq in
                   bind uu____5050
                     (fun x  ->
                        match x with
                        | FStar_Util.Inl "SKIP" -> ret t1
                        | FStar_Util.Inl e -> fail e
                        | FStar_Util.Inr x1 -> ret x1))
let pointwise:
  FStar_Tactics_Types.direction -> Prims.unit tac -> Prims.unit tac =
  fun d  ->
    fun tau  ->
      bind get
        (fun ps  ->
           let uu____5094 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals" in
           match uu____5094 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty in
               (log ps
                  (fun uu____5131  ->
                     let uu____5132 = FStar_Syntax_Print.term_to_string gt1 in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____5132);
                bind dismiss_all
                  (fun uu____5135  ->
                     let uu____5136 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1 in
                     bind uu____5136
                       (fun gt'  ->
                          log ps
                            (fun uu____5146  ->
                               let uu____5147 =
                                 FStar_Syntax_Print.term_to_string gt' in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____5147);
                          (let uu____5148 = push_goals gs in
                           bind uu____5148
                             (fun uu____5152  ->
                                add_goals
                                  [(let uu___175_5154 = g in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___175_5154.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___175_5154.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___175_5154.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___175_5154.FStar_Tactics_Types.is_guard)
                                    })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____5174 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty in
       match uu____5174 with
       | FStar_Pervasives_Native.Some t ->
           let uu____5186 = FStar_Syntax_Util.head_and_args' t in
           (match uu____5186 with
            | (hd1,args) ->
                let uu____5219 =
                  let uu____5232 =
                    let uu____5233 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____5233.FStar_Syntax_Syntax.n in
                  (uu____5232, args) in
                (match uu____5219 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____5247::(l,uu____5249)::(r,uu____5251)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____5298 =
                       let uu____5299 =
                         do_unify g.FStar_Tactics_Types.context l r in
                       Prims.op_Negation uu____5299 in
                     if uu____5298
                     then
                       let uu____5302 =
                         FStar_TypeChecker_Normalize.term_to_string
                           g.FStar_Tactics_Types.context l in
                       let uu____5303 =
                         FStar_TypeChecker_Normalize.term_to_string
                           g.FStar_Tactics_Types.context r in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____5302 uu____5303
                     else solve g FStar_Syntax_Util.exp_unit
                 | (hd2,uu____5306) ->
                     let uu____5323 =
                       FStar_TypeChecker_Normalize.term_to_string
                         g.FStar_Tactics_Types.context t in
                     fail1 "trefl: not an equality (%s)" uu____5323))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
let dup: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____5331 =
         new_uvar "dup" g.FStar_Tactics_Types.context
           g.FStar_Tactics_Types.goal_ty in
       bind uu____5331
         (fun u  ->
            let g' =
              let uu___176_5338 = g in
              {
                FStar_Tactics_Types.context =
                  (uu___176_5338.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___176_5338.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___176_5338.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___176_5338.FStar_Tactics_Types.is_guard)
              } in
            bind dismiss
              (fun uu____5341  ->
                 let uu____5342 =
                   let uu____5345 =
                     let uu____5346 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty in
                     FStar_Syntax_Util.mk_eq2 uu____5346
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness in
                   add_irrelevant_goal "dup equation"
                     g.FStar_Tactics_Types.context uu____5345
                     g.FStar_Tactics_Types.opts in
                 bind uu____5342
                   (fun uu____5349  ->
                      let uu____5350 = add_goals [g'] in
                      bind uu____5350 (fun uu____5354  -> ret ())))))
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___177_5371 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___177_5371.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___177_5371.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___177_5371.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___177_5371.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___177_5371.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___177_5371.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___177_5371.FStar_Tactics_Types.psc)
              })
       | uu____5372 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___178_5387 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___178_5387.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___178_5387.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___178_5387.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___178_5387.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___178_5387.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___178_5387.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___178_5387.FStar_Tactics_Types.psc)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____5394 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    let uu____5413 =
      bind cur_goal
        (fun g  ->
           let uu____5427 = __tc g.FStar_Tactics_Types.context t in
           bind uu____5427
             (fun uu____5463  ->
                match uu____5463 with
                | (t1,typ,guard) ->
                    let uu____5479 = FStar_Syntax_Util.head_and_args typ in
                    (match uu____5479 with
                     | (hd1,args) ->
                         let uu____5522 =
                           let uu____5535 =
                             let uu____5536 = FStar_Syntax_Util.un_uinst hd1 in
                             uu____5536.FStar_Syntax_Syntax.n in
                           (uu____5535, args) in
                         (match uu____5522 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____5555)::(q,uu____5557)::[]) when
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.or_lid
                              ->
                              let v_p =
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None p in
                              let v_q =
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None q in
                              let g1 =
                                let uu___179_5595 = g in
                                let uu____5596 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p in
                                {
                                  FStar_Tactics_Types.context = uu____5596;
                                  FStar_Tactics_Types.witness =
                                    (uu___179_5595.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___179_5595.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___179_5595.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___179_5595.FStar_Tactics_Types.is_guard)
                                } in
                              let g2 =
                                let uu___180_5598 = g in
                                let uu____5599 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q in
                                {
                                  FStar_Tactics_Types.context = uu____5599;
                                  FStar_Tactics_Types.witness =
                                    (uu___180_5598.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___180_5598.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___180_5598.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___180_5598.FStar_Tactics_Types.is_guard)
                                } in
                              bind dismiss
                                (fun uu____5606  ->
                                   let uu____5607 = add_goals [g1; g2] in
                                   bind uu____5607
                                     (fun uu____5616  ->
                                        let uu____5617 =
                                          let uu____5622 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p in
                                          let uu____5623 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q in
                                          (uu____5622, uu____5623) in
                                        ret uu____5617))
                          | uu____5628 ->
                              let uu____5641 =
                                FStar_TypeChecker_Normalize.term_to_string
                                  g.FStar_Tactics_Types.context typ in
                              fail1 "Not a disjunction: %s" uu____5641)))) in
    FStar_All.pipe_left (wrap_err "cases") uu____5413
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____5680 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts in
          FStar_Options.set uu____5680);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___181_5687 = g in
                 {
                   FStar_Tactics_Types.context =
                     (uu___181_5687.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___181_5687.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___181_5687.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___181_5687.FStar_Tactics_Types.is_guard)
                 } in
               replace_cur g'
           | FStar_Getopt.Error err1 ->
               fail2 "Setting options `%s` failed: %s" s err1
           | FStar_Getopt.Help  ->
               fail1 "Setting options `%s` failed (got `Help`?)" s)))
let top_env: FStar_TypeChecker_Env.env tac =
  bind get
    (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
let cur_env: FStar_TypeChecker_Env.env tac =
  bind cur_goal
    (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.context)
let cur_goal': FStar_Syntax_Syntax.typ tac =
  bind cur_goal
    (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.goal_ty)
let cur_witness: FStar_Syntax_Syntax.term tac =
  bind cur_goal
    (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.witness)
let unquote:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun ty  ->
    fun tm  ->
      let uu____5725 =
        bind cur_goal
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty in
             let uu____5733 = __tc env tm in
             bind uu____5733
               (fun uu____5753  ->
                  match uu____5753 with
                  | (tm1,typ,guard) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env guard;
                       ret tm1))) in
      FStar_All.pipe_left (wrap_err "unquote") uu____5725
let uvar_env:
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun ty  ->
      let uu____5786 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____5792 =
              let uu____5793 = FStar_Syntax_Util.type_u () in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5793 in
            new_uvar "uvar_env.2" env uu____5792 in
      bind uu____5786
        (fun typ  ->
           let uu____5805 = new_uvar "uvar_env" env typ in
           bind uu____5805 (fun t  -> ret t))
let unshelve: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    let uu____5818 =
      bind cur_goal
        (fun goal  ->
           let uu____5824 = __tc goal.FStar_Tactics_Types.context t in
           bind uu____5824
             (fun uu____5844  ->
                match uu____5844 with
                | (t1,typ,guard) ->
                    let uu____5856 =
                      must_trivial goal.FStar_Tactics_Types.context guard in
                    bind uu____5856
                      (fun uu____5861  ->
                         let uu____5862 =
                           let uu____5865 =
                             let uu___182_5866 = goal in
                             let uu____5867 =
                               bnorm goal.FStar_Tactics_Types.context t1 in
                             let uu____5868 =
                               bnorm goal.FStar_Tactics_Types.context typ in
                             {
                               FStar_Tactics_Types.context =
                                 (uu___182_5866.FStar_Tactics_Types.context);
                               FStar_Tactics_Types.witness = uu____5867;
                               FStar_Tactics_Types.goal_ty = uu____5868;
                               FStar_Tactics_Types.opts =
                                 (uu___182_5866.FStar_Tactics_Types.opts);
                               FStar_Tactics_Types.is_guard = false
                             } in
                           [uu____5865] in
                         add_goals uu____5862))) in
    FStar_All.pipe_left (wrap_err "unshelve") uu____5818
let unify:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____5888 =
             do_unify ps.FStar_Tactics_Types.main_context t1 t2 in
           ret uu____5888)
let launch_process:
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____5908  ->
             let uu____5909 = FStar_Options.unsafe_tactic_exec () in
             if uu____5909
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____5915  -> fun uu____5916  -> false) in
               ret s
             else
               fail
                 "launch_process: will not run anything unless --unsafe_tactic_exec is provided")
let goal_of_goal_ty:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun typ  ->
      let uu____5938 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____5938 with
      | (u,uu____5956,g_u) ->
          let g =
            let uu____5971 = FStar_Options.peek () in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____5971;
              FStar_Tactics_Types.is_guard = false
            } in
          (g, g_u)
let proofstate_of_goal_ty:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Tactics_Types.proofstate,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun typ  ->
      let uu____5988 = goal_of_goal_ty env typ in
      match uu____5988 with
      | (g,g_u) ->
          let ps =
            {
              FStar_Tactics_Types.main_context = env;
              FStar_Tactics_Types.main_goal = g;
              FStar_Tactics_Types.all_implicits =
                (g_u.FStar_TypeChecker_Env.implicits);
              FStar_Tactics_Types.goals = [g];
              FStar_Tactics_Types.smt_goals = [];
              FStar_Tactics_Types.depth = (Prims.parse_int "0");
              FStar_Tactics_Types.__dump =
                (fun ps  -> fun msg  -> dump_proofstate ps msg);
              FStar_Tactics_Types.psc = FStar_TypeChecker_Normalize.null_psc
            } in
          (ps, (g.FStar_Tactics_Types.witness))