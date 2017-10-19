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
        let uu____312 =
          let uu____315 =
            let uu____316 =
              FStar_Util.string_of_int ps.FStar_Tactics_Types.depth in
            FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____316 msg in
          let uu____317 =
            let uu____320 =
              let uu____321 =
                FStar_Range.string_of_range
                  ps.FStar_Tactics_Types.entry_range in
              FStar_Util.format1 "Position: %s\n" uu____321 in
            let uu____322 =
              let uu____325 =
                let uu____326 =
                  FStar_Util.string_of_int
                    (FStar_List.length ps.FStar_Tactics_Types.goals) in
                let uu____327 =
                  let uu____328 =
                    FStar_List.map goal_to_string
                      ps.FStar_Tactics_Types.goals in
                  FStar_String.concat "\n" uu____328 in
                FStar_Util.format2 "ACTIVE goals (%s):\n%s\n" uu____326
                  uu____327 in
              let uu____331 =
                let uu____334 =
                  let uu____335 =
                    FStar_Util.string_of_int
                      (FStar_List.length ps.FStar_Tactics_Types.smt_goals) in
                  let uu____336 =
                    let uu____337 =
                      FStar_List.map goal_to_string
                        ps.FStar_Tactics_Types.smt_goals in
                    FStar_String.concat "\n" uu____337 in
                  FStar_Util.format2 "SMT goals (%s):\n%s\n" uu____335
                    uu____336 in
                [uu____334] in
              uu____325 :: uu____331 in
            uu____320 :: uu____322 in
          uu____315 :: uu____317 in
        FStar_String.concat "" uu____312
let goal_to_json: FStar_Tactics_Types.goal -> FStar_Util.json =
  fun g  ->
    let g_binders =
      let uu____345 =
        FStar_TypeChecker_Env.all_binders g.FStar_Tactics_Types.context in
      FStar_All.pipe_right uu____345 FStar_Syntax_Print.binders_to_json in
    let uu____346 =
      let uu____353 =
        let uu____360 =
          let uu____365 =
            let uu____366 =
              let uu____373 =
                let uu____378 =
                  let uu____379 =
                    FStar_TypeChecker_Normalize.term_to_string
                      g.FStar_Tactics_Types.context
                      g.FStar_Tactics_Types.witness in
                  FStar_Util.JsonStr uu____379 in
                ("witness", uu____378) in
              let uu____380 =
                let uu____387 =
                  let uu____392 =
                    let uu____393 =
                      FStar_TypeChecker_Normalize.term_to_string
                        g.FStar_Tactics_Types.context
                        g.FStar_Tactics_Types.goal_ty in
                    FStar_Util.JsonStr uu____393 in
                  ("type", uu____392) in
                [uu____387] in
              uu____373 :: uu____380 in
            FStar_Util.JsonAssoc uu____366 in
          ("goal", uu____365) in
        [uu____360] in
      ("hyps", g_binders) :: uu____353 in
    FStar_Util.JsonAssoc uu____346
let ps_to_json:
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json
  =
  fun uu____425  ->
    match uu____425 with
    | (msg,ps) ->
        let uu____432 =
          let uu____439 =
            let uu____446 =
              let uu____451 =
                let uu____452 =
                  FStar_List.map goal_to_json ps.FStar_Tactics_Types.goals in
                FStar_Util.JsonList uu____452 in
              ("goals", uu____451) in
            let uu____455 =
              let uu____462 =
                let uu____467 =
                  let uu____468 =
                    FStar_List.map goal_to_json
                      ps.FStar_Tactics_Types.smt_goals in
                  FStar_Util.JsonList uu____468 in
                ("smt-goals", uu____467) in
              [uu____462] in
            uu____446 :: uu____455 in
          ("label", (FStar_Util.JsonStr msg)) :: uu____439 in
        FStar_Util.JsonAssoc uu____432
let dump_proofstate:
  FStar_Tactics_Types.proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____497  ->
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
         (let uu____519 = FStar_Tactics_Types.subst_proof_state subst1 ps in
          dump_cur uu____519 msg);
         FStar_Tactics_Result.Success ((), ps))
let print_proof_state: Prims.string -> Prims.unit tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc in
         let subst1 = FStar_TypeChecker_Normalize.psc_subst psc in
         (let uu____536 = FStar_Tactics_Types.subst_proof_state subst1 ps in
          dump_proofstate uu____536 msg);
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
      let uu____567 = FStar_ST.op_Bang tac_verb_dbg in
      match uu____567 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____621 =
              let uu____624 =
                FStar_TypeChecker_Env.debug
                  ps.FStar_Tactics_Types.main_context
                  (FStar_Options.Other "TacVerbose") in
              FStar_Pervasives_Native.Some uu____624 in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____621);
           log ps f)
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
let mlog: 'a . (Prims.unit -> Prims.unit) -> (Prims.unit -> 'a tac) -> 'a tac
  = fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ())
let fail: 'Auu____714 . Prims.string -> 'Auu____714 tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____725 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail") in
          if uu____725
          then dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
let fail1: 'Auu____733 . Prims.string -> Prims.string -> 'Auu____733 tac =
  fun msg  ->
    fun x  -> let uu____744 = FStar_Util.format1 msg x in fail uu____744
let fail2:
  'Auu____753 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____753 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____768 = FStar_Util.format2 msg x y in fail uu____768
let fail3:
  'Auu____779 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____779 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____798 = FStar_Util.format3 msg x y z in fail uu____798
let trytac: 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction () in
         let uu____826 = run t ps in
         match uu____826 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success
                ((FStar_Pervasives_Native.Some a), q))
         | FStar_Tactics_Result.Failed (uu____840,uu____841) ->
             (FStar_Syntax_Unionfind.rollback tx;
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
let wrap_err: 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____873 = run t ps in
           match uu____873 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
let set: FStar_Tactics_Types.proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____891  -> FStar_Tactics_Result.Success ((), p))
let do_unify:
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t1  ->
      fun t2  ->
        try FStar_TypeChecker_Rel.teq_nosmt env t1 t2
        with | uu____909 -> false
let trysolve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun goal  ->
    fun solution  ->
      do_unify goal.FStar_Tactics_Types.context solution
        goal.FStar_Tactics_Types.witness
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____923 =
         let uu___136_924 = p in
         let uu____925 = FStar_List.tl p.FStar_Tactics_Types.goals in
         {
           FStar_Tactics_Types.main_context =
             (uu___136_924.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___136_924.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___136_924.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____925;
           FStar_Tactics_Types.smt_goals =
             (uu___136_924.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___136_924.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___136_924.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___136_924.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___136_924.FStar_Tactics_Types.entry_range)
         } in
       set uu____923)
let solve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun goal  ->
    fun solution  ->
      let uu____940 = trysolve goal solution in
      if uu____940
      then dismiss
      else
        (let uu____944 =
           let uu____945 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context solution in
           let uu____946 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.witness in
           let uu____947 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           FStar_Util.format3 "%s does not solve %s : %s" uu____945 uu____946
             uu____947 in
         fail uu____944)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___137_954 = p in
          {
            FStar_Tactics_Types.main_context =
              (uu___137_954.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___137_954.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___137_954.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___137_954.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___137_954.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___137_954.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___137_954.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___137_954.FStar_Tactics_Types.entry_range)
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
      let uu____970 = FStar_TypeChecker_Env.pop_bv e in
      match uu____970 with
      | FStar_Pervasives_Native.None  -> b3
      | FStar_Pervasives_Native.Some (bv,e1) ->
          let b4 =
            b3 &&
              (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort) in
          aux b4 e1 in
    let uu____988 = let uu____989 = aux b2 env in Prims.op_Negation uu____989 in
    if uu____988
    then
      let uu____990 =
        let uu____991 = goal_to_string g in
        FStar_Util.format1
          "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
          uu____991 in
      FStar_Errors.warn
        (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos uu____990
    else ()
let add_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___138_1011 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___138_1011.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___138_1011.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___138_1011.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___138_1011.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___138_1011.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___138_1011.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___138_1011.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___138_1011.FStar_Tactics_Types.entry_range)
            }))
let add_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___139_1030 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___139_1030.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___139_1030.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___139_1030.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___139_1030.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___139_1030.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___139_1030.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___139_1030.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___139_1030.FStar_Tactics_Types.entry_range)
            }))
let push_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___140_1049 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___140_1049.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___140_1049.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___140_1049.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___140_1049.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___140_1049.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___140_1049.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___140_1049.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___140_1049.FStar_Tactics_Types.entry_range)
            }))
let push_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___141_1068 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___141_1068.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___141_1068.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___141_1068.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___141_1068.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___141_1068.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___141_1068.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___141_1068.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___141_1068.FStar_Tactics_Types.entry_range)
            }))
let replace_cur: FStar_Tactics_Types.goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____1078  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___142_1091 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___142_1091.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___142_1091.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___142_1091.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___142_1091.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___142_1091.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___142_1091.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___142_1091.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___142_1091.FStar_Tactics_Types.entry_range)
            }))
let new_uvar:
  Prims.string ->
    env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1120 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ in
        match uu____1120 with
        | (u,uu____1136,g_u) ->
            let uu____1150 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits in
            bind uu____1150 (fun uu____1154  -> ret u)
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1159 = FStar_Syntax_Util.un_squash t in
    match uu____1159 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1169 =
          let uu____1170 = FStar_Syntax_Subst.compress t' in
          uu____1170.FStar_Syntax_Syntax.n in
        (match uu____1169 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1174 -> false)
    | uu____1175 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1184 = FStar_Syntax_Util.un_squash t in
    match uu____1184 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1194 =
          let uu____1195 = FStar_Syntax_Subst.compress t' in
          uu____1195.FStar_Syntax_Syntax.n in
        (match uu____1194 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1199 -> false)
    | uu____1200 -> false
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
          let uu____1238 = new_uvar reason env typ in
          bind uu____1238
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
             let uu____1296 =
               (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                 e t in
             ret uu____1296
           with | e1 -> fail "not typeable")
let tc: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ tac =
  fun t  ->
    let uu____1335 =
      bind cur_goal
        (fun goal  ->
           let uu____1341 = __tc goal.FStar_Tactics_Types.context t in
           bind uu____1341
             (fun uu____1361  ->
                match uu____1361 with
                | (t1,typ,guard) ->
                    let uu____1373 =
                      let uu____1374 =
                        let uu____1375 =
                          FStar_TypeChecker_Rel.discharge_guard
                            goal.FStar_Tactics_Types.context guard in
                        FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                          uu____1375 in
                      Prims.op_Negation uu____1374 in
                    if uu____1373
                    then fail "got non-trivial guard"
                    else ret typ)) in
    FStar_All.pipe_left (wrap_err "tc") uu____1335
let add_irrelevant_goal:
  Prims.string ->
    env ->
      FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> Prims.unit tac
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____1403 = mk_irrelevant_goal reason env phi opts in
          bind uu____1403 (fun goal  -> add_goals [goal])
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
       let uu____1425 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty in
       if uu____1425
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1429 =
            FStar_TypeChecker_Normalize.term_to_string
              goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1429))
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
          let uu____1450 =
            let uu____1451 = FStar_TypeChecker_Rel.simplify_guard e g in
            uu____1451.FStar_TypeChecker_Env.guard_f in
          match uu____1450 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1455 = istrivial e f in
              if uu____1455
              then ret ()
              else
                (let uu____1459 = mk_irrelevant_goal reason e f opts in
                 bind uu____1459
                   (fun goal  ->
                      let goal1 =
                        let uu___145_1466 = goal in
                        {
                          FStar_Tactics_Types.context =
                            (uu___145_1466.FStar_Tactics_Types.context);
                          FStar_Tactics_Types.witness =
                            (uu___145_1466.FStar_Tactics_Types.witness);
                          FStar_Tactics_Types.goal_ty =
                            (uu___145_1466.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___145_1466.FStar_Tactics_Types.opts);
                          FStar_Tactics_Types.is_guard = true
                        } in
                      push_goals [goal1]))
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____1472 = is_irrelevant g in
       if uu____1472
       then bind dismiss (fun uu____1476  -> add_smt_goals [g])
       else
         (let uu____1478 =
            FStar_TypeChecker_Normalize.term_to_string
              g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1478))
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
             let uu____1524 =
               try
                 let uu____1558 =
                   FStar_List.splitAt n1 p.FStar_Tactics_Types.goals in
                 ret uu____1558
               with | uu____1588 -> fail "divide: not enough goals" in
             bind uu____1524
               (fun uu____1615  ->
                  match uu____1615 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___146_1641 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___146_1641.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___146_1641.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___146_1641.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___146_1641.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___146_1641.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___146_1641.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___146_1641.FStar_Tactics_Types.entry_range)
                        } in
                      let rp =
                        let uu___147_1643 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___147_1643.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___147_1643.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___147_1643.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___147_1643.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___147_1643.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___147_1643.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___147_1643.FStar_Tactics_Types.entry_range)
                        } in
                      let uu____1644 = set lp in
                      bind uu____1644
                        (fun uu____1652  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1666 = set rp in
                                     bind uu____1666
                                       (fun uu____1674  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___148_1690 = p in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___148_1690.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___148_1690.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___148_1690.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___148_1690.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___148_1690.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___148_1690.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___148_1690.FStar_Tactics_Types.entry_range)
                                                      } in
                                                    let uu____1691 = set p' in
                                                    bind uu____1691
                                                      (fun uu____1699  ->
                                                         ret (a, b))))))))))
let focus: 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1719 = divide (Prims.parse_int "1") f idtac in
    bind uu____1719
      (fun uu____1732  -> match uu____1732 with | (a,()) -> ret a)
let rec map: 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____1767::uu____1768 ->
             let uu____1771 =
               let uu____1780 = map tau in
               divide (Prims.parse_int "1") tau uu____1780 in
             bind uu____1771
               (fun uu____1798  ->
                  match uu____1798 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____1837 =
        bind t1
          (fun uu____1842  ->
             let uu____1843 = map t2 in
             bind uu____1843 (fun uu____1851  -> ret ())) in
      focus uu____1837
let intro: FStar_Syntax_Syntax.binder tac =
  bind cur_goal
    (fun goal  ->
       let uu____1862 =
         FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
       match uu____1862 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____1877 =
             let uu____1878 = FStar_Syntax_Util.is_total_comp c in
             Prims.op_Negation uu____1878 in
           if uu____1877
           then fail "Codomain is effectful"
           else
             (let env' =
                FStar_TypeChecker_Env.push_binders
                  goal.FStar_Tactics_Types.context [b] in
              let typ' = comp_to_typ c in
              let uu____1884 = new_uvar "intro" env' typ' in
              bind uu____1884
                (fun u  ->
                   let uu____1891 =
                     let uu____1892 =
                       FStar_Syntax_Util.abs [b] u
                         FStar_Pervasives_Native.None in
                     trysolve goal uu____1892 in
                   if uu____1891
                   then
                     let uu____1895 =
                       let uu____1898 =
                         let uu___151_1899 = goal in
                         let uu____1900 = bnorm env' u in
                         let uu____1901 = bnorm env' typ' in
                         {
                           FStar_Tactics_Types.context = env';
                           FStar_Tactics_Types.witness = uu____1900;
                           FStar_Tactics_Types.goal_ty = uu____1901;
                           FStar_Tactics_Types.opts =
                             (uu___151_1899.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___151_1899.FStar_Tactics_Types.is_guard)
                         } in
                       replace_cur uu____1898 in
                     bind uu____1895 (fun uu____1903  -> ret b)
                   else fail "intro: unification failed"))
       | FStar_Pervasives_Native.None  ->
           let uu____1909 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____1909)
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
       (let uu____1930 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
        match uu____1930 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____1949 =
              let uu____1950 = FStar_Syntax_Util.is_total_comp c in
              Prims.op_Negation uu____1950 in
            if uu____1949
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty in
               let bs =
                 let uu____1966 = FStar_Syntax_Syntax.mk_binder bv in
                 [uu____1966; b] in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs in
               let uu____1968 =
                 let uu____1971 = comp_to_typ c in
                 new_uvar "intro_rec" env' uu____1971 in
               bind uu____1968
                 (fun u  ->
                    let lb =
                      let uu____1987 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____1987 in
                    let body = FStar_Syntax_Syntax.bv_to_name bv in
                    let uu____1991 =
                      FStar_Syntax_Subst.close_let_rec [lb] body in
                    match uu____1991 with
                    | (lbs,body1) ->
                        let tm =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                            FStar_Pervasives_Native.None
                            (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos in
                        let res = trysolve goal tm in
                        if res
                        then
                          let uu____2028 =
                            let uu____2031 =
                              let uu___152_2032 = goal in
                              let uu____2033 = bnorm env' u in
                              let uu____2034 =
                                let uu____2035 = comp_to_typ c in
                                bnorm env' uu____2035 in
                              {
                                FStar_Tactics_Types.context = env';
                                FStar_Tactics_Types.witness = uu____2033;
                                FStar_Tactics_Types.goal_ty = uu____2034;
                                FStar_Tactics_Types.opts =
                                  (uu___152_2032.FStar_Tactics_Types.opts);
                                FStar_Tactics_Types.is_guard =
                                  (uu___152_2032.FStar_Tactics_Types.is_guard)
                              } in
                            replace_cur uu____2031 in
                          bind uu____2028
                            (fun uu____2042  ->
                               let uu____2043 =
                                 let uu____2048 =
                                   FStar_Syntax_Syntax.mk_binder bv in
                                 (uu____2048, b) in
                               ret uu____2043)
                        else fail "intro_rec: unification failed"))
        | FStar_Pervasives_Native.None  ->
            let uu____2062 =
              FStar_TypeChecker_Normalize.term_to_string
                goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2062))
let norm: FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         let steps =
           let uu____2087 = FStar_TypeChecker_Normalize.tr_norm_steps s in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____2087 in
         let w =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.witness in
         let t =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.goal_ty in
         replace_cur
           (let uu___153_2094 = goal in
            {
              FStar_Tactics_Types.context =
                (uu___153_2094.FStar_Tactics_Types.context);
              FStar_Tactics_Types.witness = w;
              FStar_Tactics_Types.goal_ty = t;
              FStar_Tactics_Types.opts =
                (uu___153_2094.FStar_Tactics_Types.opts);
              FStar_Tactics_Types.is_guard =
                (uu___153_2094.FStar_Tactics_Types.is_guard)
            }))
let norm_term_env:
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2115 =
          bind get
            (fun ps  ->
               let uu____2121 = __tc e t in
               bind uu____2121
                 (fun uu____2143  ->
                    match uu____2143 with
                    | (t1,uu____2153,guard) ->
                        (FStar_TypeChecker_Rel.force_trivial_guard e guard;
                         (let steps =
                            let uu____2159 =
                              FStar_TypeChecker_Normalize.tr_norm_steps s in
                            FStar_List.append
                              [FStar_TypeChecker_Normalize.Reify;
                              FStar_TypeChecker_Normalize.UnfoldTac]
                              uu____2159 in
                          let t2 =
                            normalize steps
                              ps.FStar_Tactics_Types.main_context t1 in
                          ret t2)))) in
        FStar_All.pipe_left (wrap_err "norm_term") uu____2115
let __exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____2178 = __tc goal.FStar_Tactics_Types.context t in
         bind uu____2178
           (fun uu____2198  ->
              match uu____2198 with
              | (t1,typ,guard) ->
                  let uu____2210 =
                    let uu____2211 =
                      let uu____2212 =
                        FStar_TypeChecker_Rel.discharge_guard
                          goal.FStar_Tactics_Types.context guard in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____2212 in
                    Prims.op_Negation uu____2211 in
                  if uu____2210
                  then fail "got non-trivial guard"
                  else
                    (let uu____2216 =
                       do_unify goal.FStar_Tactics_Types.context typ
                         goal.FStar_Tactics_Types.goal_ty in
                     if uu____2216
                     then solve goal t1
                     else
                       (let uu____2220 =
                          FStar_TypeChecker_Normalize.term_to_string
                            goal.FStar_Tactics_Types.context t1 in
                        let uu____2221 =
                          let uu____2222 =
                            bnorm goal.FStar_Tactics_Types.context typ in
                          FStar_TypeChecker_Normalize.term_to_string
                            goal.FStar_Tactics_Types.context uu____2222 in
                        let uu____2223 =
                          FStar_TypeChecker_Normalize.term_to_string
                            goal.FStar_Tactics_Types.context
                            goal.FStar_Tactics_Types.goal_ty in
                        fail3 "%s : %s does not exactly solve the goal %s"
                          uu____2220 uu____2221 uu____2223))))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____2232 =
      mlog
        (fun uu____2237  ->
           let uu____2238 = FStar_Syntax_Print.term_to_string tm in
           FStar_Util.print1 "exact: tm = %s\n" uu____2238)
        (fun uu____2241  -> let uu____2242 = __exact tm in focus uu____2242) in
    FStar_All.pipe_left (wrap_err "exact") uu____2232
let uvar_free_in_goal:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2261 =
             let uu____2268 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty in
             FStar_Util.set_elements uu____2268 in
           FStar_List.map FStar_Pervasives_Native.fst uu____2261 in
         FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars)
let uvar_free:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.proofstate -> Prims.bool =
  fun u  ->
    fun ps  ->
      FStar_List.existsML (uvar_free_in_goal u) ps.FStar_Tactics_Types.goals
exception NoUnif
let uu___is_NoUnif: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2295 -> false
let rec __apply:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> Prims.unit tac
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        bind cur_goal
          (fun goal  ->
             let uu____2315 =
               let uu____2320 = __exact tm in trytac uu____2320 in
             bind uu____2315
               (fun r  ->
                  match r with
                  | FStar_Pervasives_Native.Some r1 -> ret ()
                  | FStar_Pervasives_Native.None  ->
                      let uu____2333 = FStar_Syntax_Util.arrow_one typ in
                      (match uu____2333 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise NoUnif
                       | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                           mlog
                             (fun uu____2365  ->
                                let uu____2366 =
                                  FStar_Syntax_Print.binder_to_string
                                    (bv, aq) in
                                FStar_Util.print1
                                  "__apply: pushing binder %s\n" uu____2366)
                             (fun uu____2369  ->
                                let uu____2370 =
                                  let uu____2371 =
                                    FStar_Syntax_Util.is_total_comp c in
                                  Prims.op_Negation uu____2371 in
                                if uu____2370
                                then fail "apply: not total codomain"
                                else
                                  (let uu____2375 =
                                     new_uvar "apply"
                                       goal.FStar_Tactics_Types.context
                                       bv.FStar_Syntax_Syntax.sort in
                                   bind uu____2375
                                     (fun u  ->
                                        let tm' =
                                          FStar_Syntax_Syntax.mk_Tm_app tm
                                            [(u, aq)]
                                            FStar_Pervasives_Native.None
                                            (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                        let typ' =
                                          let uu____2395 = comp_to_typ c in
                                          FStar_All.pipe_left
                                            (FStar_Syntax_Subst.subst
                                               [FStar_Syntax_Syntax.NT
                                                  (bv, u)]) uu____2395 in
                                        let uu____2396 =
                                          __apply uopt tm' typ' in
                                        bind uu____2396
                                          (fun uu____2404  ->
                                             let u1 =
                                               bnorm
                                                 goal.FStar_Tactics_Types.context
                                                 u in
                                             let uu____2406 =
                                               let uu____2407 =
                                                 let uu____2410 =
                                                   let uu____2411 =
                                                     FStar_Syntax_Util.head_and_args
                                                       u1 in
                                                   FStar_Pervasives_Native.fst
                                                     uu____2411 in
                                                 FStar_Syntax_Subst.compress
                                                   uu____2410 in
                                               uu____2407.FStar_Syntax_Syntax.n in
                                             match uu____2406 with
                                             | FStar_Syntax_Syntax.Tm_uvar
                                                 (uvar,uu____2439) ->
                                                 bind get
                                                   (fun ps  ->
                                                      let uu____2467 =
                                                        uopt &&
                                                          (uvar_free uvar ps) in
                                                      if uu____2467
                                                      then ret ()
                                                      else
                                                        (let uu____2471 =
                                                           let uu____2474 =
                                                             let uu___154_2475
                                                               = goal in
                                                             let uu____2476 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 u1 in
                                                             let uu____2477 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 bv.FStar_Syntax_Syntax.sort in
                                                             {
                                                               FStar_Tactics_Types.context
                                                                 =
                                                                 (uu___154_2475.FStar_Tactics_Types.context);
                                                               FStar_Tactics_Types.witness
                                                                 = uu____2476;
                                                               FStar_Tactics_Types.goal_ty
                                                                 = uu____2477;
                                                               FStar_Tactics_Types.opts
                                                                 =
                                                                 (uu___154_2475.FStar_Tactics_Types.opts);
                                                               FStar_Tactics_Types.is_guard
                                                                 = false
                                                             } in
                                                           [uu____2474] in
                                                         add_goals uu____2471))
                                             | t -> ret ())))))))
let try_unif: 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
let apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      let uu____2528 =
        mlog
          (fun uu____2533  ->
             let uu____2534 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "apply: tm = %s\n" uu____2534)
          (fun uu____2536  ->
             bind cur_goal
               (fun goal  ->
                  let uu____2540 = __tc goal.FStar_Tactics_Types.context tm in
                  bind uu____2540
                    (fun uu____2561  ->
                       match uu____2561 with
                       | (tm1,typ,guard) ->
                           let uu____2573 =
                             let uu____2576 =
                               let uu____2579 = __apply uopt tm1 typ in
                               bind uu____2579
                                 (fun uu____2583  ->
                                    add_goal_from_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts) in
                             focus uu____2576 in
                           let uu____2584 =
                             let uu____2587 =
                               FStar_TypeChecker_Normalize.term_to_string
                                 goal.FStar_Tactics_Types.context tm1 in
                             let uu____2588 =
                               FStar_TypeChecker_Normalize.term_to_string
                                 goal.FStar_Tactics_Types.context typ in
                             let uu____2589 =
                               FStar_TypeChecker_Normalize.term_to_string
                                 goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____2587 uu____2588 uu____2589 in
                           try_unif uu____2573 uu____2584))) in
      FStar_All.pipe_left (wrap_err "apply") uu____2528
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____2602 =
      let uu____2605 =
        mlog
          (fun uu____2610  ->
             let uu____2611 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____2611)
          (fun uu____2614  ->
             let is_unit_t t =
               let uu____2619 =
                 let uu____2620 = FStar_Syntax_Subst.compress t in
                 uu____2620.FStar_Syntax_Syntax.n in
               match uu____2619 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____2624 -> false in
             bind cur_goal
               (fun goal  ->
                  let uu____2628 = __tc goal.FStar_Tactics_Types.context tm in
                  bind uu____2628
                    (fun uu____2650  ->
                       match uu____2650 with
                       | (tm1,t,guard) ->
                           let uu____2662 =
                             FStar_Syntax_Util.arrow_formals_comp t in
                           (match uu____2662 with
                            | (bs,comp) ->
                                if
                                  Prims.op_Negation
                                    (FStar_Syntax_Util.is_lemma_comp comp)
                                then fail "not a lemma"
                                else
                                  (let uu____2692 =
                                     FStar_List.fold_left
                                       (fun uu____2738  ->
                                          fun uu____2739  ->
                                            match (uu____2738, uu____2739)
                                            with
                                            | ((uvs,guard1,subst1),(b,aq)) ->
                                                let b_t =
                                                  FStar_Syntax_Subst.subst
                                                    subst1
                                                    b.FStar_Syntax_Syntax.sort in
                                                let uu____2842 =
                                                  is_unit_t b_t in
                                                if uu____2842
                                                then
                                                  (((FStar_Syntax_Util.exp_unit,
                                                      aq) :: uvs), guard1,
                                                    ((FStar_Syntax_Syntax.NT
                                                        (b,
                                                          FStar_Syntax_Util.exp_unit))
                                                    :: subst1))
                                                else
                                                  (let uu____2880 =
                                                     FStar_TypeChecker_Util.new_implicit_var
                                                       "apply_lemma"
                                                       (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                       goal.FStar_Tactics_Types.context
                                                       b_t in
                                                   match uu____2880 with
                                                   | (u,uu____2910,g_u) ->
                                                       let uu____2924 =
                                                         FStar_TypeChecker_Rel.conj_guard
                                                           guard1 g_u in
                                                       (((u, aq) :: uvs),
                                                         uu____2924,
                                                         ((FStar_Syntax_Syntax.NT
                                                             (b, u)) ::
                                                         subst1))))
                                       ([], guard, []) bs in
                                   match uu____2692 with
                                   | (uvs,implicits,subst1) ->
                                       let uvs1 = FStar_List.rev uvs in
                                       let comp1 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp in
                                       let uu____2994 =
                                         let uu____3003 =
                                           let uu____3012 =
                                             FStar_Syntax_Util.comp_to_comp_typ
                                               comp1 in
                                           uu____3012.FStar_Syntax_Syntax.effect_args in
                                         match uu____3003 with
                                         | pre::post::uu____3023 ->
                                             ((FStar_Pervasives_Native.fst
                                                 pre),
                                               (FStar_Pervasives_Native.fst
                                                  post))
                                         | uu____3064 ->
                                             failwith
                                               "apply_lemma: impossible: not a lemma" in
                                       (match uu____2994 with
                                        | (pre,post) ->
                                            let post1 =
                                              let uu____3096 =
                                                let uu____3105 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    FStar_Syntax_Util.exp_unit in
                                                [uu____3105] in
                                              FStar_Syntax_Util.mk_app post
                                                uu____3096 in
                                            let uu____3106 =
                                              let uu____3107 =
                                                let uu____3108 =
                                                  FStar_Syntax_Util.mk_squash
                                                    post1 in
                                                do_unify
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3108
                                                  goal.FStar_Tactics_Types.goal_ty in
                                              Prims.op_Negation uu____3107 in
                                            if uu____3106
                                            then
                                              let uu____3111 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  goal.FStar_Tactics_Types.context
                                                  tm1 in
                                              let uu____3112 =
                                                let uu____3113 =
                                                  FStar_Syntax_Util.mk_squash
                                                    post1 in
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3113 in
                                              let uu____3114 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  goal.FStar_Tactics_Types.context
                                                  goal.FStar_Tactics_Types.goal_ty in
                                              fail3
                                                "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                uu____3111 uu____3112
                                                uu____3114
                                            else
                                              (let solution =
                                                 let uu____3117 =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm1 uvs1
                                                     FStar_Pervasives_Native.None
                                                     (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                                 FStar_TypeChecker_Normalize.normalize
                                                   [FStar_TypeChecker_Normalize.Beta]
                                                   goal.FStar_Tactics_Types.context
                                                   uu____3117 in
                                               let uu____3118 =
                                                 add_implicits
                                                   implicits.FStar_TypeChecker_Env.implicits in
                                               bind uu____3118
                                                 (fun uu____3124  ->
                                                    let implicits1 =
                                                      FStar_All.pipe_right
                                                        implicits.FStar_TypeChecker_Env.implicits
                                                        (FStar_List.filter
                                                           (fun uu____3192 
                                                              ->
                                                              match uu____3192
                                                              with
                                                              | (uu____3205,uu____3206,uu____3207,tm2,uu____3209,uu____3210)
                                                                  ->
                                                                  let uu____3211
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    tm2 in
                                                                  (match uu____3211
                                                                   with
                                                                   | 
                                                                   (hd1,uu____3227)
                                                                    ->
                                                                    let uu____3248
                                                                    =
                                                                    let uu____3249
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1 in
                                                                    uu____3249.FStar_Syntax_Syntax.n in
                                                                    (match uu____3248
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____3252
                                                                    -> true
                                                                    | 
                                                                    uu____3269
                                                                    -> false)))) in
                                                    let uu____3270 =
                                                      solve goal solution in
                                                    bind uu____3270
                                                      (fun uu____3281  ->
                                                         let is_free_uvar uv
                                                           t1 =
                                                           let free_uvars =
                                                             let uu____3292 =
                                                               let uu____3299
                                                                 =
                                                                 FStar_Syntax_Free.uvars
                                                                   t1 in
                                                               FStar_Util.set_elements
                                                                 uu____3299 in
                                                             FStar_List.map
                                                               FStar_Pervasives_Native.fst
                                                               uu____3292 in
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
                                                           let uu____3340 =
                                                             FStar_Syntax_Util.head_and_args
                                                               t1 in
                                                           match uu____3340
                                                           with
                                                           | (hd1,uu____3356)
                                                               ->
                                                               (match 
                                                                  hd1.FStar_Syntax_Syntax.n
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____3378)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                | uu____3403
                                                                    -> false) in
                                                         let sub_goals =
                                                           FStar_All.pipe_right
                                                             implicits1
                                                             (FStar_List.map
                                                                (fun
                                                                   uu____3445
                                                                    ->
                                                                   match uu____3445
                                                                   with
                                                                   | 
                                                                   (_msg,_env,_uvar,term,typ,uu____3463)
                                                                    ->
                                                                    let uu___157_3464
                                                                    = goal in
                                                                    let uu____3465
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term in
                                                                    let uu____3466
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___157_3464.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3465;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3466;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___157_3464.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___157_3464.FStar_Tactics_Types.is_guard)
                                                                    })) in
                                                         let rec filter' f xs
                                                           =
                                                           match xs with
                                                           | [] -> []
                                                           | x::xs1 ->
                                                               let uu____3504
                                                                 = f x xs1 in
                                                               if uu____3504
                                                               then
                                                                 let uu____3507
                                                                   =
                                                                   filter' f
                                                                    xs1 in
                                                                 x ::
                                                                   uu____3507
                                                               else
                                                                 filter' f
                                                                   xs1 in
                                                         let sub_goals1 =
                                                           filter'
                                                             (fun g  ->
                                                                fun goals  ->
                                                                  let uu____3521
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals in
                                                                  Prims.op_Negation
                                                                    uu____3521)
                                                             sub_goals in
                                                         let uu____3522 =
                                                           add_goal_from_guard
                                                             "apply_lemma guard"
                                                             goal.FStar_Tactics_Types.context
                                                             guard
                                                             goal.FStar_Tactics_Types.opts in
                                                         bind uu____3522
                                                           (fun uu____3527 
                                                              ->
                                                              let uu____3528
                                                                =
                                                                let uu____3531
                                                                  =
                                                                  let uu____3532
                                                                    =
                                                                    let uu____3533
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    pre in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____3533 in
                                                                  Prims.op_Negation
                                                                    uu____3532 in
                                                                if uu____3531
                                                                then
                                                                  add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    goal.FStar_Tactics_Types.context
                                                                    pre
                                                                    goal.FStar_Tactics_Types.opts
                                                                else ret () in
                                                              bind uu____3528
                                                                (fun
                                                                   uu____3538
                                                                    ->
                                                                   add_goals
                                                                    sub_goals1))))))))))) in
      focus uu____2605 in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____2602
let destruct_eq':
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3559 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____3559 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____3569::(e1,uu____3571)::(e2,uu____3573)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____3632 -> FStar_Pervasives_Native.None
let destruct_eq:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3655 = destruct_eq' typ in
    match uu____3655 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____3685 = FStar_Syntax_Util.un_squash typ in
        (match uu____3685 with
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
        let uu____3743 = FStar_TypeChecker_Env.pop_bv e1 in
        match uu____3743 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____3791 = aux e' in
               FStar_Util.map_opt uu____3791
                 (fun uu____3815  ->
                    match uu____3815 with | (e'',bvs) -> (e'', (bv' :: bvs)))) in
      let uu____3836 = aux e in
      FStar_Util.map_opt uu____3836
        (fun uu____3860  ->
           match uu____3860 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
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
          let uu____3921 = split_env b1 g.FStar_Tactics_Types.context in
          FStar_Util.map_opt uu____3921
            (fun uu____3945  ->
               match uu____3945 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___158_3962 = bv in
                     let uu____3963 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___158_3962.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___158_3962.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____3963
                     } in
                   let bvs1 = FStar_List.map s1 bvs in
                   let c = push_bvs e0 (b2 :: bvs1) in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty in
                   let uu___159_3972 = g in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___159_3972.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___159_3972.FStar_Tactics_Types.is_guard)
                   })
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____3986 = h in
         match uu____3986 with
         | (bv,uu____3990) ->
             mlog
               (fun uu____3994  ->
                  let uu____3995 = FStar_Syntax_Print.bv_to_string bv in
                  let uu____3996 =
                    FStar_Syntax_Print.term_to_string
                      bv.FStar_Syntax_Syntax.sort in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____3995
                    uu____3996)
               (fun uu____3999  ->
                  let uu____4000 =
                    split_env bv goal.FStar_Tactics_Types.context in
                  match uu____4000 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____4029 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort in
                      (match uu____4029 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____4044 =
                             let uu____4045 = FStar_Syntax_Subst.compress x in
                             uu____4045.FStar_Syntax_Syntax.n in
                           (match uu____4044 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)] in
                                let s1 bv1 =
                                  let uu___160_4058 = bv1 in
                                  let uu____4059 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___160_4058.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___160_4058.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____4059
                                  } in
                                let bvs1 = FStar_List.map s1 bvs in
                                let uu____4065 =
                                  let uu___161_4066 = goal in
                                  let uu____4067 = push_bvs e0 (bv :: bvs1) in
                                  let uu____4068 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness in
                                  let uu____4069 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty in
                                  {
                                    FStar_Tactics_Types.context = uu____4067;
                                    FStar_Tactics_Types.witness = uu____4068;
                                    FStar_Tactics_Types.goal_ty = uu____4069;
                                    FStar_Tactics_Types.opts =
                                      (uu___161_4066.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___161_4066.FStar_Tactics_Types.is_guard)
                                  } in
                                replace_cur uu____4065
                            | uu____4070 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____4071 ->
                           fail "rewrite: Not an equality hypothesis")))
let rename_to: FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____4098 = b in
           match uu____4098 with
           | (bv,uu____4102) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___162_4106 = bv in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___162_4106.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___162_4106.FStar_Syntax_Syntax.sort)
                    }) in
               let s1 =
                 let uu____4110 =
                   let uu____4111 =
                     let uu____4118 = FStar_Syntax_Syntax.bv_to_name bv' in
                     (bv, uu____4118) in
                   FStar_Syntax_Syntax.NT uu____4111 in
                 [uu____4110] in
               let uu____4119 = subst_goal bv bv' s1 goal in
               (match uu____4119 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
let binder_retype: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4139 = b in
         match uu____4139 with
         | (bv,uu____4143) ->
             let uu____4144 = split_env bv goal.FStar_Tactics_Types.context in
             (match uu____4144 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____4173 = FStar_Syntax_Util.type_u () in
                  (match uu____4173 with
                   | (ty,u) ->
                       let uu____4182 = new_uvar "binder_retype" e0 ty in
                       bind uu____4182
                         (fun t'  ->
                            let bv'' =
                              let uu___163_4192 = bv in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___163_4192.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___163_4192.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              } in
                            let s =
                              let uu____4196 =
                                let uu____4197 =
                                  let uu____4204 =
                                    FStar_Syntax_Syntax.bv_to_name bv'' in
                                  (bv, uu____4204) in
                                FStar_Syntax_Syntax.NT uu____4197 in
                              [uu____4196] in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___164_4212 = b1 in
                                   let uu____4213 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___164_4212.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___164_4212.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____4213
                                   }) bvs in
                            let env' = push_bvs e0 (bv'' :: bvs1) in
                            bind dismiss
                              (fun uu____4219  ->
                                 let uu____4220 =
                                   let uu____4223 =
                                     let uu____4226 =
                                       let uu___165_4227 = goal in
                                       let uu____4228 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness in
                                       let uu____4229 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____4228;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____4229;
                                         FStar_Tactics_Types.opts =
                                           (uu___165_4227.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___165_4227.FStar_Tactics_Types.is_guard)
                                       } in
                                     [uu____4226] in
                                   add_goals uu____4223 in
                                 bind uu____4220
                                   (fun uu____4232  ->
                                      let uu____4233 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t' in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____4233
                                        goal.FStar_Tactics_Types.opts))))))
let norm_binder_type:
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> Prims.unit tac
  =
  fun s  ->
    fun b  ->
      bind cur_goal
        (fun goal  ->
           let uu____4256 = b in
           match uu____4256 with
           | (bv,uu____4260) ->
               let uu____4261 = split_env bv goal.FStar_Tactics_Types.context in
               (match uu____4261 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____4293 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____4293 in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort in
                    let bv' =
                      let uu___166_4298 = bv in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___166_4298.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___166_4298.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      } in
                    let env' = push_bvs e0 (bv' :: bvs) in
                    replace_cur
                      (let uu___167_4302 = goal in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___167_4302.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___167_4302.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___167_4302.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___167_4302.FStar_Tactics_Types.is_guard)
                       })))
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4308 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4308 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____4330 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____4330 in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None in
           replace_cur
             (let uu___168_4364 = goal in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___168_4364.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___168_4364.FStar_Tactics_Types.is_guard)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____4376 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4376 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____4397 = FStar_Syntax_Print.bv_to_string x in
               let uu____4398 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____4397 uu____4398
             else revert)
let clear_top: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4405 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4405 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fns_ty =
             FStar_Syntax_Free.names goal.FStar_Tactics_Types.goal_ty in
           let uu____4427 = FStar_Util.set_mem x fns_ty in
           if uu____4427
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____4431 =
                new_uvar "clear_top" env' goal.FStar_Tactics_Types.goal_ty in
              bind uu____4431
                (fun u  ->
                   let uu____4437 =
                     let uu____4438 = trysolve goal u in
                     Prims.op_Negation uu____4438 in
                   if uu____4437
                   then fail "clear: unification failed"
                   else
                     (let new_goal =
                        let uu___169_4443 = goal in
                        let uu____4444 = bnorm env' u in
                        {
                          FStar_Tactics_Types.context = env';
                          FStar_Tactics_Types.witness = uu____4444;
                          FStar_Tactics_Types.goal_ty =
                            (uu___169_4443.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___169_4443.FStar_Tactics_Types.opts);
                          FStar_Tactics_Types.is_guard =
                            (uu___169_4443.FStar_Tactics_Types.is_guard)
                        } in
                      bind dismiss (fun uu____4446  -> add_goals [new_goal])))))
let rec clear: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4458 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4458 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (b',env') ->
             if FStar_Syntax_Syntax.bv_eq (FStar_Pervasives_Native.fst b) b'
             then clear_top
             else
               bind revert
                 (fun uu____4482  ->
                    let uu____4483 = clear b in
                    bind uu____4483
                      (fun uu____4487  ->
                         bind intro (fun uu____4489  -> ret ()))))
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___170_4506 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___170_4506.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___170_4506.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___170_4506.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___170_4506.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____4508  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___171_4525 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___171_4525.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___171_4525.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___171_4525.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___171_4525.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____4527  -> add_goals [g']))
let rec mapM: 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____4569 = f x in
          bind uu____4569
            (fun y  ->
               let uu____4577 = mapM f xs in
               bind uu____4577 (fun ys  -> ret (y :: ys)))
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
            let uu____4627 = FStar_Syntax_Subst.compress t in
            uu____4627.FStar_Syntax_Syntax.n in
          let uu____4630 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___173_4636 = t in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___173_4636.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___173_4636.FStar_Syntax_Syntax.vars)
                 })
            else ret t in
          bind uu____4630
            (fun t1  ->
               let tn1 =
                 match tn with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let ff = tac_fold_env d f env in
                     let uu____4673 = ff hd1 in
                     bind uu____4673
                       (fun hd2  ->
                          let fa uu____4693 =
                            match uu____4693 with
                            | (a,q) ->
                                let uu____4706 = ff a in
                                bind uu____4706 (fun a1  -> ret (a1, q)) in
                          let uu____4719 = mapM fa args in
                          bind uu____4719
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____4779 = FStar_Syntax_Subst.open_term bs t2 in
                     (match uu____4779 with
                      | (bs1,t') ->
                          let uu____4788 =
                            let uu____4791 =
                              FStar_TypeChecker_Env.push_binders env bs1 in
                            tac_fold_env d f uu____4791 t' in
                          bind uu____4788
                            (fun t''  ->
                               let uu____4795 =
                                 let uu____4796 =
                                   let uu____4813 =
                                     FStar_Syntax_Subst.close_binders bs1 in
                                   let uu____4814 =
                                     FStar_Syntax_Subst.close bs1 t'' in
                                   (uu____4813, uu____4814, k) in
                                 FStar_Syntax_Syntax.Tm_abs uu____4796 in
                               ret uu____4795))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | uu____4835 -> ret tn in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___172_4842 = t1 in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___172_4842.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___172_4842.FStar_Syntax_Syntax.vars)
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
            let uu____4876 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____4876 with
            | (t1,lcomp,g) ->
                let uu____4888 =
                  (let uu____4891 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp in
                   Prims.op_Negation uu____4891) ||
                    (let uu____4893 = FStar_TypeChecker_Rel.is_trivial g in
                     Prims.op_Negation uu____4893) in
                if uu____4888
                then ret t1
                else
                  (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                   let uu____4900 = new_uvar "pointwise_rec" env typ in
                   bind uu____4900
                     (fun ut  ->
                        log ps
                          (fun uu____4911  ->
                             let uu____4912 =
                               FStar_Syntax_Print.term_to_string t1 in
                             let uu____4913 =
                               FStar_Syntax_Print.term_to_string ut in
                             FStar_Util.print2
                               "Pointwise_rec: making equality %s = %s\n"
                               uu____4912 uu____4913);
                        (let uu____4914 =
                           let uu____4917 =
                             let uu____4918 =
                               FStar_TypeChecker_TcTerm.universe_of env typ in
                             FStar_Syntax_Util.mk_eq2 uu____4918 typ t1 ut in
                           add_irrelevant_goal "pointwise_rec equation" env
                             uu____4917 opts in
                         bind uu____4914
                           (fun uu____4921  ->
                              let uu____4922 =
                                bind tau
                                  (fun uu____4927  ->
                                     let ut1 =
                                       FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                         env ut in
                                     ret ut1) in
                              focus uu____4922))))
let pointwise:
  FStar_Tactics_Types.direction -> Prims.unit tac -> Prims.unit tac =
  fun d  ->
    fun tau  ->
      bind get
        (fun ps  ->
           let uu____4952 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals" in
           match uu____4952 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty in
               (log ps
                  (fun uu____4989  ->
                     let uu____4990 = FStar_Syntax_Print.term_to_string gt1 in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____4990);
                bind dismiss_all
                  (fun uu____4993  ->
                     let uu____4994 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1 in
                     bind uu____4994
                       (fun gt'  ->
                          log ps
                            (fun uu____5004  ->
                               let uu____5005 =
                                 FStar_Syntax_Print.term_to_string gt' in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____5005);
                          (let uu____5006 = push_goals gs in
                           bind uu____5006
                             (fun uu____5010  ->
                                add_goals
                                  [(let uu___174_5012 = g in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___174_5012.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___174_5012.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___174_5012.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___174_5012.FStar_Tactics_Types.is_guard)
                                    })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____5032 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty in
       match uu____5032 with
       | FStar_Pervasives_Native.Some t ->
           let uu____5044 = FStar_Syntax_Util.head_and_args' t in
           (match uu____5044 with
            | (hd1,args) ->
                let uu____5077 =
                  let uu____5090 =
                    let uu____5091 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____5091.FStar_Syntax_Syntax.n in
                  (uu____5090, args) in
                (match uu____5077 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____5105::(l,uu____5107)::(r,uu____5109)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____5156 =
                       let uu____5157 =
                         do_unify g.FStar_Tactics_Types.context l r in
                       Prims.op_Negation uu____5157 in
                     if uu____5156
                     then
                       let uu____5160 =
                         FStar_TypeChecker_Normalize.term_to_string
                           g.FStar_Tactics_Types.context l in
                       let uu____5161 =
                         FStar_TypeChecker_Normalize.term_to_string
                           g.FStar_Tactics_Types.context r in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____5160 uu____5161
                     else solve g FStar_Syntax_Util.exp_unit
                 | (hd2,uu____5164) ->
                     let uu____5181 =
                       FStar_TypeChecker_Normalize.term_to_string
                         g.FStar_Tactics_Types.context t in
                     fail1 "trefl: not an equality (%s)" uu____5181))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
let dup: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____5189 =
         new_uvar "dup" g.FStar_Tactics_Types.context
           g.FStar_Tactics_Types.goal_ty in
       bind uu____5189
         (fun u  ->
            let g' =
              let uu___175_5196 = g in
              {
                FStar_Tactics_Types.context =
                  (uu___175_5196.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___175_5196.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___175_5196.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___175_5196.FStar_Tactics_Types.is_guard)
              } in
            bind dismiss
              (fun uu____5199  ->
                 let uu____5200 =
                   let uu____5203 =
                     let uu____5204 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty in
                     FStar_Syntax_Util.mk_eq2 uu____5204
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness in
                   add_irrelevant_goal "dup equation"
                     g.FStar_Tactics_Types.context uu____5203
                     g.FStar_Tactics_Types.opts in
                 bind uu____5200
                   (fun uu____5207  ->
                      let uu____5208 = add_goals [g'] in
                      bind uu____5208 (fun uu____5212  -> ret ())))))
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___176_5229 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___176_5229.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___176_5229.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___176_5229.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___176_5229.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___176_5229.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___176_5229.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___176_5229.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___176_5229.FStar_Tactics_Types.entry_range)
              })
       | uu____5230 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___177_5245 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___177_5245.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___177_5245.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___177_5245.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___177_5245.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___177_5245.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___177_5245.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___177_5245.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___177_5245.FStar_Tactics_Types.entry_range)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____5252 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    let uu____5271 =
      bind cur_goal
        (fun g  ->
           let uu____5285 = __tc g.FStar_Tactics_Types.context t in
           bind uu____5285
             (fun uu____5321  ->
                match uu____5321 with
                | (t1,typ,guard) ->
                    let uu____5337 = FStar_Syntax_Util.head_and_args typ in
                    (match uu____5337 with
                     | (hd1,args) ->
                         let uu____5380 =
                           let uu____5393 =
                             let uu____5394 = FStar_Syntax_Util.un_uinst hd1 in
                             uu____5394.FStar_Syntax_Syntax.n in
                           (uu____5393, args) in
                         (match uu____5380 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____5413)::(q,uu____5415)::[]) when
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
                                let uu___178_5453 = g in
                                let uu____5454 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p in
                                {
                                  FStar_Tactics_Types.context = uu____5454;
                                  FStar_Tactics_Types.witness =
                                    (uu___178_5453.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___178_5453.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___178_5453.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___178_5453.FStar_Tactics_Types.is_guard)
                                } in
                              let g2 =
                                let uu___179_5456 = g in
                                let uu____5457 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q in
                                {
                                  FStar_Tactics_Types.context = uu____5457;
                                  FStar_Tactics_Types.witness =
                                    (uu___179_5456.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___179_5456.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___179_5456.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___179_5456.FStar_Tactics_Types.is_guard)
                                } in
                              bind dismiss
                                (fun uu____5464  ->
                                   let uu____5465 = add_goals [g1; g2] in
                                   bind uu____5465
                                     (fun uu____5474  ->
                                        let uu____5475 =
                                          let uu____5480 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p in
                                          let uu____5481 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q in
                                          (uu____5480, uu____5481) in
                                        ret uu____5475))
                          | uu____5486 ->
                              let uu____5499 =
                                FStar_TypeChecker_Normalize.term_to_string
                                  g.FStar_Tactics_Types.context typ in
                              fail1 "Not a disjunction: %s" uu____5499)))) in
    FStar_All.pipe_left (wrap_err "cases") uu____5271
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____5538 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts in
          FStar_Options.set uu____5538);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___180_5545 = g in
                 {
                   FStar_Tactics_Types.context =
                     (uu___180_5545.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___180_5545.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___180_5545.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___180_5545.FStar_Tactics_Types.is_guard)
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
      let uu____5583 =
        bind cur_goal
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty in
             let uu____5591 = __tc env tm in
             bind uu____5591
               (fun uu____5611  ->
                  match uu____5611 with
                  | (tm1,typ,guard) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env guard;
                       ret tm1))) in
      FStar_All.pipe_left (wrap_err "unquote") uu____5583
let uvar_env:
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun ty  ->
      let uu____5644 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____5650 =
              let uu____5651 = FStar_Syntax_Util.type_u () in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5651 in
            new_uvar "uvar_env.2" env uu____5650 in
      bind uu____5644
        (fun typ  ->
           let uu____5663 = new_uvar "uvar_env" env typ in
           bind uu____5663 (fun t  -> ret t))
let unshelve: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    let uu____5676 =
      bind cur_goal
        (fun goal  ->
           let uu____5682 = __tc goal.FStar_Tactics_Types.context t in
           bind uu____5682
             (fun uu____5702  ->
                match uu____5702 with
                | (t1,typ,guard) ->
                    let uu____5714 =
                      let uu____5715 =
                        let uu____5716 =
                          FStar_TypeChecker_Rel.discharge_guard
                            goal.FStar_Tactics_Types.context guard in
                        FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                          uu____5716 in
                      Prims.op_Negation uu____5715 in
                    if uu____5714
                    then fail "got non-trivial guard"
                    else
                      (let uu____5720 =
                         let uu____5723 =
                           let uu___181_5724 = goal in
                           let uu____5725 =
                             bnorm goal.FStar_Tactics_Types.context t1 in
                           let uu____5726 =
                             bnorm goal.FStar_Tactics_Types.context typ in
                           {
                             FStar_Tactics_Types.context =
                               (uu___181_5724.FStar_Tactics_Types.context);
                             FStar_Tactics_Types.witness = uu____5725;
                             FStar_Tactics_Types.goal_ty = uu____5726;
                             FStar_Tactics_Types.opts =
                               (uu___181_5724.FStar_Tactics_Types.opts);
                             FStar_Tactics_Types.is_guard = false
                           } in
                         [uu____5723] in
                       add_goals uu____5720))) in
    FStar_All.pipe_left (wrap_err "unshelve") uu____5676
let unify:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____5746 =
             do_unify ps.FStar_Tactics_Types.main_context t1 t2 in
           ret uu____5746)
let launch_process:
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____5766  ->
             let uu____5767 = FStar_Options.unsafe_tactic_exec () in
             if uu____5767
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____5773  -> fun uu____5774  -> false) in
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
      let uu____5796 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____5796 with
      | (u,uu____5814,g_u) ->
          let g =
            let uu____5829 = FStar_Options.peek () in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____5829;
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
      let uu____5846 = goal_of_goal_ty env typ in
      match uu____5846 with
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
              FStar_Tactics_Types.psc = FStar_TypeChecker_Normalize.null_psc;
              FStar_Tactics_Types.entry_range = FStar_Range.dummyRange
            } in
          (ps, (g.FStar_Tactics_Types.witness))