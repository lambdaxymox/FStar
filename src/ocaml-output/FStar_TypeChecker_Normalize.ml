open Prims
type step =
  | Beta
  | Iota
  | Zeta
  | Exclude of step
  | Weak
  | HNF
  | Primops
  | Eager_unfolding
  | Inlining
  | NoDeltaSteps
  | UnfoldUntil of FStar_Syntax_Syntax.delta_depth
  | UnfoldOnly of FStar_Ident.lid Prims.list
  | UnfoldTac
  | PureSubtermsWithinComputations
  | Simplify
  | EraseUniverses
  | AllowUnboundUniverses
  | Reify
  | CompressUvars
  | NoFullNorm
  | CheckNoUvars
  | Unmeta[@@deriving show]
let uu___is_Beta: step -> Prims.bool =
  fun projectee  -> match projectee with | Beta  -> true | uu____19 -> false
let uu___is_Iota: step -> Prims.bool =
  fun projectee  -> match projectee with | Iota  -> true | uu____24 -> false
let uu___is_Zeta: step -> Prims.bool =
  fun projectee  -> match projectee with | Zeta  -> true | uu____29 -> false
let uu___is_Exclude: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____35 -> false
let __proj__Exclude__item___0: step -> step =
  fun projectee  -> match projectee with | Exclude _0 -> _0
let uu___is_Weak: step -> Prims.bool =
  fun projectee  -> match projectee with | Weak  -> true | uu____48 -> false
let uu___is_HNF: step -> Prims.bool =
  fun projectee  -> match projectee with | HNF  -> true | uu____53 -> false
let uu___is_Primops: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____58 -> false
let uu___is_Eager_unfolding: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____63 -> false
let uu___is_Inlining: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____68 -> false
let uu___is_NoDeltaSteps: step -> Prims.bool =
  fun projectee  ->
    match projectee with | NoDeltaSteps  -> true | uu____73 -> false
let uu___is_UnfoldUntil: step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____79 -> false
let __proj__UnfoldUntil__item___0: step -> FStar_Syntax_Syntax.delta_depth =
  fun projectee  -> match projectee with | UnfoldUntil _0 -> _0
let uu___is_UnfoldOnly: step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____95 -> false
let __proj__UnfoldOnly__item___0: step -> FStar_Ident.lid Prims.list =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0
let uu___is_UnfoldTac: step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____114 -> false
let uu___is_PureSubtermsWithinComputations: step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____119 -> false
let uu___is_Simplify: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____124 -> false
let uu___is_EraseUniverses: step -> Prims.bool =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____129 -> false
let uu___is_AllowUnboundUniverses: step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____134 -> false
let uu___is_Reify: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____139 -> false
let uu___is_CompressUvars: step -> Prims.bool =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____144 -> false
let uu___is_NoFullNorm: step -> Prims.bool =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____149 -> false
let uu___is_CheckNoUvars: step -> Prims.bool =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____154 -> false
let uu___is_Unmeta: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____159 -> false
type steps = step Prims.list[@@deriving show]
type psc =
  {
  psc_range: FStar_Range.range;
  psc_subst: Prims.unit -> FStar_Syntax_Syntax.subst_t;}[@@deriving show]
let __proj__Mkpsc__item__psc_range: psc -> FStar_Range.range =
  fun projectee  ->
    match projectee with
    | { psc_range = __fname__psc_range; psc_subst = __fname__psc_subst;_} ->
        __fname__psc_range
let __proj__Mkpsc__item__psc_subst:
  psc -> Prims.unit -> FStar_Syntax_Syntax.subst_t =
  fun projectee  ->
    match projectee with
    | { psc_range = __fname__psc_range; psc_subst = __fname__psc_subst;_} ->
        __fname__psc_subst
let null_psc: psc =
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____196  -> []) }
let psc_range: psc -> FStar_Range.range = fun psc  -> psc.psc_range
let psc_subst: psc -> FStar_Syntax_Syntax.subst_t =
  fun psc  -> psc.psc_subst ()
type primitive_step =
  {
  name: FStar_Ident.lid;
  arity: Prims.int;
  strong_reduction_ok: Prims.bool;
  requires_binder_substitution: Prims.bool;
  interpretation:
    psc ->
      FStar_Syntax_Syntax.args ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option;}[@@deriving
                                                                   show]
let __proj__Mkprimitive_step__item__name: primitive_step -> FStar_Ident.lid =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} -> __fname__name
let __proj__Mkprimitive_step__item__arity: primitive_step -> Prims.int =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} -> __fname__arity
let __proj__Mkprimitive_step__item__strong_reduction_ok:
  primitive_step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} ->
        __fname__strong_reduction_ok
let __proj__Mkprimitive_step__item__requires_binder_substitution:
  primitive_step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} ->
        __fname__requires_binder_substitution
let __proj__Mkprimitive_step__item__interpretation:
  primitive_step ->
    psc ->
      FStar_Syntax_Syntax.args ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} ->
        __fname__interpretation
type closure =
  | Clos of
  ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
     FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term,
  ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
     FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple2 FStar_Syntax_Syntax.memo,Prims.bool)
  FStar_Pervasives_Native.tuple4
  | Univ of FStar_Syntax_Syntax.universe
  | Dummy[@@deriving show]
let uu___is_Clos: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Clos _0 -> true | uu____403 -> false
let __proj__Clos__item___0:
  closure ->
    ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
       FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term,
      ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
         FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2 FStar_Syntax_Syntax.memo,Prims.bool)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Clos _0 -> _0
let uu___is_Univ: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____507 -> false
let __proj__Univ__item___0: closure -> FStar_Syntax_Syntax.universe =
  fun projectee  -> match projectee with | Univ _0 -> _0
let uu___is_Dummy: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____520 -> false
type env =
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
let dummy:
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2
  = (FStar_Pervasives_Native.None, Dummy)
let closure_to_string: closure -> Prims.string =
  fun uu___178_540  ->
    match uu___178_540 with
    | Clos (uu____541,t,uu____543,uu____544) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____589 -> "Univ"
    | Dummy  -> "dummy"
type cfg =
  {
  steps: steps;
  tcenv: FStar_TypeChecker_Env.env;
  delta_level: FStar_TypeChecker_Env.delta_level Prims.list;
  primitive_steps: primitive_step Prims.list;}[@@deriving show]
let __proj__Mkcfg__item__steps: cfg -> steps =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps;_} -> __fname__steps
let __proj__Mkcfg__item__tcenv: cfg -> FStar_TypeChecker_Env.env =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps;_} -> __fname__tcenv
let __proj__Mkcfg__item__delta_level:
  cfg -> FStar_TypeChecker_Env.delta_level Prims.list =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps;_} -> __fname__delta_level
let __proj__Mkcfg__item__primitive_steps: cfg -> primitive_step Prims.list =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps;_} ->
        __fname__primitive_steps
let only_strong_steps':
  primitive_step Prims.list -> primitive_step Prims.list =
  fun steps  -> FStar_List.filter (fun ps  -> ps.strong_reduction_ok) steps
let only_strong_steps: cfg -> cfg =
  fun cfg  ->
    let uu___195_682 = cfg in
    let uu____683 = only_strong_steps' cfg.primitive_steps in
    {
      steps = (uu___195_682.steps);
      tcenv = (uu___195_682.tcenv);
      delta_level = (uu___195_682.delta_level);
      primitive_steps = uu____683
    }
type branches =
  (FStar_Syntax_Syntax.pat,FStar_Syntax_Syntax.term
                             FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple3 Prims.list[@@deriving show]
type stack_elt =
  | Arg of (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
  FStar_Pervasives_Native.tuple3
  | UnivArgs of (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
  FStar_Pervasives_Native.tuple2
  | MemoLazy of (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
  FStar_Syntax_Syntax.memo
  | Match of (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3
  | Abs of
  (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                         FStar_Pervasives_Native.option,
  FStar_Range.range) FStar_Pervasives_Native.tuple5
  | App of
  (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
  FStar_Pervasives_Native.tuple4
  | Meta of (FStar_Syntax_Syntax.metadata,FStar_Range.range)
  FStar_Pervasives_Native.tuple2
  | Let of
  (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
  FStar_Pervasives_Native.tuple4
  | Steps of
  (steps,primitive_step Prims.list,FStar_TypeChecker_Env.delta_level
                                     Prims.list)
  FStar_Pervasives_Native.tuple3
  | Debug of (FStar_Syntax_Syntax.term,FStar_Util.time)
  FStar_Pervasives_Native.tuple2[@@deriving show]
let uu___is_Arg: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Arg _0 -> true | uu____830 -> false
let __proj__Arg__item___0:
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Arg _0 -> _0
let uu___is_UnivArgs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____868 -> false
let __proj__UnivArgs__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0
let uu___is_MemoLazy: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____906 -> false
let __proj__MemoLazy__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0
let uu___is_Match: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____965 -> false
let __proj__Match__item___0:
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Abs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____1009 -> false
let __proj__Abs__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Abs _0 -> _0
let uu___is_App: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____1067 -> false
let __proj__App__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Meta: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____1109 -> false
let __proj__Meta__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Meta _0 -> _0
let uu___is_Let: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____1143 -> false
let __proj__Let__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Steps: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Steps _0 -> true | uu____1191 -> false
let __proj__Steps__item___0:
  stack_elt ->
    (steps,primitive_step Prims.list,FStar_TypeChecker_Env.delta_level
                                       Prims.list)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Steps _0 -> _0
let uu___is_Debug: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____1239 -> false
let __proj__Debug__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list[@@deriving show]
let mk:
  'Auu____1268 .
    'Auu____1268 ->
      FStar_Range.range -> 'Auu____1268 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r
let set_memo: 'a . 'a FStar_Syntax_Syntax.memo -> 'a -> Prims.unit =
  fun r  ->
    fun t  ->
      let uu____1319 = FStar_ST.op_Bang r in
      match uu____1319 with
      | FStar_Pervasives_Native.Some uu____1386 ->
          failwith "Unexpected set_memo: thunk already evaluated"
      | FStar_Pervasives_Native.None  ->
          FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____1459 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____1459 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___179_1467  ->
    match uu___179_1467 with
    | Arg (c,uu____1469,uu____1470) ->
        let uu____1471 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____1471
    | MemoLazy uu____1472 -> "MemoLazy"
    | Abs (uu____1479,bs,uu____1481,uu____1482,uu____1483) ->
        let uu____1488 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____1488
    | UnivArgs uu____1493 -> "UnivArgs"
    | Match uu____1500 -> "Match"
    | App (uu____1507,t,uu____1509,uu____1510) ->
        let uu____1511 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____1511
    | Meta (m,uu____1513) -> "Meta"
    | Let uu____1514 -> "Let"
    | Steps (uu____1523,uu____1524,uu____1525) -> "Steps"
    | Debug (t,uu____1535) ->
        let uu____1536 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____1536
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____1545 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____1545 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1563 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____1563 then f () else ()
let log_primops: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1578 =
        (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm"))
          ||
          (FStar_TypeChecker_Env.debug cfg.tcenv
             (FStar_Options.Other "Primops")) in
      if uu____1578 then f () else ()
let is_empty: 'Auu____1584 . 'Auu____1584 Prims.list -> Prims.bool =
  fun uu___180_1590  ->
    match uu___180_1590 with | [] -> true | uu____1593 -> false
let lookup_bvar:
  'Auu____1604 'Auu____1605 .
    ('Auu____1605,'Auu____1604) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____1604
  =
  fun env  ->
    fun x  ->
      try
        let uu____1629 = FStar_List.nth env x.FStar_Syntax_Syntax.index in
        FStar_Pervasives_Native.snd uu____1629
      with
      | uu____1642 ->
          let uu____1643 =
            let uu____1644 = FStar_Syntax_Print.db_to_string x in
            FStar_Util.format1 "Failed to find %s\n" uu____1644 in
          failwith uu____1643
let downgrade_ghost_effect_name:
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option =
  fun l  ->
    if FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      if FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid
      then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
      else
        if FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid
        then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_PURE_lid
        else FStar_Pervasives_Native.None
let norm_universe:
  cfg -> env -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun cfg  ->
    fun env  ->
      fun u  ->
        let norm_univs us =
          let us1 = FStar_Util.sort_with FStar_Syntax_Util.compare_univs us in
          let uu____1685 =
            FStar_List.fold_left
              (fun uu____1711  ->
                 fun u1  ->
                   match uu____1711 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____1736 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____1736 with
                        | (k_u,n1) ->
                            let uu____1751 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____1751
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____1685 with
          | (uu____1769,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____1794 =
                   let uu____1795 = FStar_List.nth env x in
                   FStar_Pervasives_Native.snd uu____1795 in
                 match uu____1794 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____1813 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____1822 ->
                   let uu____1823 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____1823
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____1829 when
              FStar_All.pipe_right cfg.steps
                (FStar_List.contains CheckNoUvars)
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____1838 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____1847 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____1854 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____1854 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____1871 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____1871 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____1879 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____1887 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____1887 with
                                  | (uu____1892,m) -> n1 <= m)) in
                        if uu____1879 then rest1 else us1
                    | uu____1897 -> us1)
               | uu____1902 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1906 = aux u3 in
              FStar_List.map (fun _0_42  -> FStar_Syntax_Syntax.U_succ _0_42)
                uu____1906 in
        let uu____1909 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____1909
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1911 = aux u in
           match uu____1911 with
           | [] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero )::[] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero )::u1::[] -> u1
           | (FStar_Syntax_Syntax.U_zero )::us ->
               FStar_Syntax_Syntax.U_max us
           | u1::[] -> u1
           | us -> FStar_Syntax_Syntax.U_max us)
let rec closure_as_term:
  cfg -> env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun env  ->
      fun t  ->
        log cfg
          (fun uu____2015  ->
             let uu____2016 = FStar_Syntax_Print.tag_of_term t in
             let uu____2017 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____2016
               uu____2017);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____2024 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____2026 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____2051 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____2052 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____2053 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____2054 ->
                  let uu____2071 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains CheckNoUvars) in
                  if uu____2071
                  then
                    let uu____2072 =
                      let uu____2073 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos in
                      let uu____2074 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____2073 uu____2074 in
                    failwith uu____2072
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____2077 =
                    let uu____2078 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____2078 in
                  mk uu____2077 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____2085 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____2085
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____2087 = lookup_bvar env x in
                  (match uu____2087 with
                   | Univ uu____2090 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____2094) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____2206 = closures_as_binders_delayed cfg env bs in
                  (match uu____2206 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____2234 =
                         let uu____2235 =
                           let uu____2252 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____2252) in
                         FStar_Syntax_Syntax.Tm_abs uu____2235 in
                       mk uu____2234 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____2283 = closures_as_binders_delayed cfg env bs in
                  (match uu____2283 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____2325 =
                    let uu____2336 =
                      let uu____2343 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____2343] in
                    closures_as_binders_delayed cfg env uu____2336 in
                  (match uu____2325 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____2361 =
                         let uu____2362 =
                           let uu____2369 =
                             let uu____2370 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____2370
                               FStar_Pervasives_Native.fst in
                           (uu____2369, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____2362 in
                       mk uu____2361 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____2461 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____2461
                    | FStar_Util.Inr c ->
                        let uu____2475 = close_comp cfg env c in
                        FStar_Util.Inr uu____2475 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____2491 =
                    let uu____2492 =
                      let uu____2519 = closure_as_term_delayed cfg env t11 in
                      (uu____2519, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____2492 in
                  mk uu____2491 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____2570 =
                    let uu____2571 =
                      let uu____2578 = closure_as_term_delayed cfg env t' in
                      let uu____2581 =
                        let uu____2582 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____2582 in
                      (uu____2578, uu____2581) in
                    FStar_Syntax_Syntax.Tm_meta uu____2571 in
                  mk uu____2570 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____2642 =
                    let uu____2643 =
                      let uu____2650 = closure_as_term_delayed cfg env t' in
                      let uu____2653 =
                        let uu____2654 =
                          let uu____2661 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____2661) in
                        FStar_Syntax_Syntax.Meta_monadic uu____2654 in
                      (uu____2650, uu____2653) in
                    FStar_Syntax_Syntax.Tm_meta uu____2643 in
                  mk uu____2642 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____2680 =
                    let uu____2681 =
                      let uu____2688 = closure_as_term_delayed cfg env t' in
                      let uu____2691 =
                        let uu____2692 =
                          let uu____2701 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____2701) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____2692 in
                      (uu____2688, uu____2691) in
                    FStar_Syntax_Syntax.Tm_meta uu____2681 in
                  mk uu____2680 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____2714 =
                    let uu____2715 =
                      let uu____2722 = closure_as_term_delayed cfg env t' in
                      (uu____2722, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____2715 in
                  mk uu____2714 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____2762  -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let uu____2781 =
                    let uu____2792 = FStar_Syntax_Syntax.is_top_level [lb] in
                    if uu____2792
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       let uu____2811 =
                         closure_as_term cfg (dummy :: env0) body in
                       ((FStar_Util.Inl
                           (let uu___200_2823 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___200_2823.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___200_2823.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____2811)) in
                  (match uu____2781 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___201_2839 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___201_2839.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___201_2839.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def
                         } in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____2850,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____2909  -> fun env2  -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____2934 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2934
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____2954  -> fun env2  -> dummy :: env2) lbs
                          env_univs in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let nm =
                      let uu____2976 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2976
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                         FStar_All.pipe_right
                           (let uu___202_2988 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___202_2988.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___202_2988.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_43  -> FStar_Util.Inl _0_43)) in
                    let uu___203_2989 = lb in
                    let uu____2990 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___203_2989.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___203_2989.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____2990
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____3020  -> fun env1  -> dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____3109 =
                    match uu____3109 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____3164 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____3185 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____3245  ->
                                        fun uu____3246  ->
                                          match (uu____3245, uu____3246) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____3337 =
                                                norm_pat env3 p1 in
                                              (match uu____3337 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____3185 with
                               | (pats1,env3) ->
                                   ((let uu___204_3419 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___204_3419.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___205_3438 = x in
                                let uu____3439 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___205_3438.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___205_3438.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3439
                                } in
                              ((let uu___206_3453 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___206_3453.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___207_3464 = x in
                                let uu____3465 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___207_3464.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___207_3464.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3465
                                } in
                              ((let uu___208_3479 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___208_3479.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___209_3495 = x in
                                let uu____3496 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___209_3495.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___209_3495.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3496
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___210_3503 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___210_3503.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____3506 = norm_pat env1 pat in
                        (match uu____3506 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3535 =
                                     closure_as_term cfg env2 w in
                                   FStar_Pervasives_Native.Some uu____3535 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____3541 =
                    let uu____3542 =
                      let uu____3565 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____3565) in
                    FStar_Syntax_Syntax.Tm_match uu____3542 in
                  mk uu____3541 t1.FStar_Syntax_Syntax.pos))
and closure_as_term_delayed:
  cfg ->
    env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun cfg  ->
    fun env  ->
      fun t  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains CompressUvars cfg.steps)
            -> t
        | uu____3651 -> closure_as_term cfg env t
and closures_as_args_delayed:
  cfg ->
    env ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
          FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun cfg  ->
    fun env  ->
      fun args  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains CompressUvars cfg.steps)
            -> args
        | uu____3677 ->
            FStar_List.map
              (fun uu____3694  ->
                 match uu____3694 with
                 | (x,imp) ->
                     let uu____3713 = closure_as_term_delayed cfg env x in
                     (uu____3713, imp)) args
and closures_as_binders_delayed:
  cfg ->
    env ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
           FStar_Pervasives_Native.tuple2 Prims.list,env)
          FStar_Pervasives_Native.tuple2
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____3727 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____3776  ->
                  fun uu____3777  ->
                    match (uu____3776, uu____3777) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___211_3847 = b in
                          let uu____3848 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___211_3847.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___211_3847.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____3848
                          } in
                        let env2 = dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____3727 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
and close_comp:
  cfg ->
    env ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax
  =
  fun cfg  ->
    fun env  ->
      fun c  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains CompressUvars cfg.steps)
            -> c
        | uu____3941 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____3954 = closure_as_term_delayed cfg env t in
                 let uu____3955 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____3954 uu____3955
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____3968 = closure_as_term_delayed cfg env t in
                 let uu____3969 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____3968 uu____3969
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   closure_as_term_delayed cfg env
                     c1.FStar_Syntax_Syntax.result_typ in
                 let args =
                   closures_as_args_delayed cfg env
                     c1.FStar_Syntax_Syntax.effect_args in
                 let flags =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___181_3995  ->
                           match uu___181_3995 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____3999 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____3999
                           | f -> f)) in
                 let uu____4003 =
                   let uu___212_4004 = c1 in
                   let uu____4005 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____4005;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___212_4004.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____4003)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags  ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___182_4015  ->
            match uu___182_4015 with
            | FStar_Syntax_Syntax.DECREASES uu____4016 -> false
            | uu____4019 -> true))
and close_lcomp_opt:
  cfg ->
    env ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun env  ->
      fun lopt  ->
        match lopt with
        | FStar_Pervasives_Native.Some rc ->
            let flags =
              FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                (FStar_List.filter
                   (fun uu___183_4037  ->
                      match uu___183_4037 with
                      | FStar_Syntax_Syntax.DECREASES uu____4038 -> false
                      | uu____4041 -> true)) in
            let rc1 =
              let uu___213_4043 = rc in
              let uu____4044 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___213_4043.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____4044;
                FStar_Syntax_Syntax.residual_flags = flags
              } in
            FStar_Pervasives_Native.Some rc1
        | uu____4051 -> lopt
let built_in_primitive_steps: primitive_step Prims.list =
  let arg_as_int a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      FStar_Syntax_Embeddings.unembed_int_safe in
  let arg_as_bool a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      FStar_Syntax_Embeddings.unembed_bool_safe in
  let arg_as_char a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      FStar_Syntax_Embeddings.unembed_char_safe in
  let arg_as_string a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      FStar_Syntax_Embeddings.unembed_string_safe in
  let arg_as_list u a =
    let uu____4139 = FStar_Syntax_Embeddings.unembed_list_safe u in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____4139 in
  let arg_as_bounded_int uu____4167 =
    match uu____4167 with
    | (a,uu____4179) ->
        let uu____4186 =
          let uu____4187 = FStar_Syntax_Subst.compress a in
          uu____4187.FStar_Syntax_Syntax.n in
        (match uu____4186 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____4197;
                FStar_Syntax_Syntax.vars = uu____4198;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____4200;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____4201;_},uu____4202)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____4241 =
               let uu____4246 = FStar_Util.int_of_string i in
               (fv1, uu____4246) in
             FStar_Pervasives_Native.Some uu____4241
         | uu____4251 -> FStar_Pervasives_Native.None) in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4293 = f a in FStar_Pervasives_Native.Some uu____4293
    | uu____4294 -> FStar_Pervasives_Native.None in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4344 = f a0 a1 in FStar_Pervasives_Native.Some uu____4344
    | uu____4345 -> FStar_Pervasives_Native.None in
  let unary_op as_a f res args =
    let uu____4394 = FStar_List.map as_a args in
    lift_unary (f res.psc_range) uu____4394 in
  let binary_op as_a f res args =
    let uu____4450 = FStar_List.map as_a args in
    lift_binary (f res.psc_range) uu____4450 in
  let as_primitive_step uu____4474 =
    match uu____4474 with
    | (l,arity,f) ->
        {
          name = l;
          arity;
          strong_reduction_ok = true;
          requires_binder_substitution = false;
          interpretation = f
        } in
  let unary_int_op f =
    unary_op arg_as_int
      (fun r  ->
         fun x  ->
           let uu____4522 = f x in
           FStar_Syntax_Embeddings.embed_int r uu____4522) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4550 = f x y in
             FStar_Syntax_Embeddings.embed_int r uu____4550) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  ->
           let uu____4571 = f x in
           FStar_Syntax_Embeddings.embed_bool r uu____4571) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4599 = f x y in
             FStar_Syntax_Embeddings.embed_bool r uu____4599) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4627 = f x y in
             FStar_Syntax_Embeddings.embed_string r uu____4627) in
  let list_of_string' rng s =
    let name l =
      let uu____4641 =
        let uu____4642 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____4642 in
      mk uu____4641 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____4652 =
      let uu____4655 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____4655 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____4652 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in
    FStar_Syntax_Embeddings.embed_int rng r in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____4702 = arg_as_string a1 in
        (match uu____4702 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4708 =
               arg_as_list FStar_Syntax_Embeddings.unembed_string_safe a2 in
             (match uu____4708 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____4721 =
                    FStar_Syntax_Embeddings.embed_string psc.psc_range r in
                  FStar_Pervasives_Native.Some uu____4721
              | uu____4722 -> FStar_Pervasives_Native.None)
         | uu____4727 -> FStar_Pervasives_Native.None)
    | uu____4730 -> FStar_Pervasives_Native.None in
  let string_of_int1 rng i =
    let uu____4740 = FStar_Util.string_of_int i in
    FStar_Syntax_Embeddings.embed_string rng uu____4740 in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false") in
  let string_of_int2 rng i =
    let uu____4756 = FStar_Util.string_of_int i in
    FStar_Syntax_Embeddings.embed_string rng uu____4756 in
  let string_of_bool2 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false") in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r in
  let range_of1 uu____4786 args =
    match args with
    | uu____4798::(t,uu____4800)::[] ->
        let uu____4829 = term_of_range t.FStar_Syntax_Syntax.pos in
        FStar_Pervasives_Native.Some uu____4829
    | uu____4834 -> FStar_Pervasives_Native.None in
  let set_range_of1 uu____4856 args =
    match args with
    | uu____4866::(t,uu____4868)::(r,uu____4870)::[] ->
        let uu____4891 = FStar_Syntax_Embeddings.unembed_range_safe r in
        FStar_Util.bind_opt uu____4891
          (fun r1  ->
             FStar_Pervasives_Native.Some
               (let uu___214_4901 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___214_4901.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r1;
                  FStar_Syntax_Syntax.vars =
                    (uu___214_4901.FStar_Syntax_Syntax.vars)
                }))
    | uu____4902 -> FStar_Pervasives_Native.None in
  let mk_range1 uu____4918 args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____4929 =
          let uu____4950 = arg_as_string fn in
          let uu____4953 = arg_as_int from_line in
          let uu____4956 = arg_as_int from_col in
          let uu____4959 = arg_as_int to_line in
          let uu____4962 = arg_as_int to_col in
          (uu____4950, uu____4953, uu____4956, uu____4959, uu____4962) in
        (match uu____4929 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____4993 = FStar_Range.mk_pos from_l from_c in
               let uu____4994 = FStar_Range.mk_pos to_l to_c in
               FStar_Range.mk_range fn1 uu____4993 uu____4994 in
             let uu____4995 = term_of_range r in
             FStar_Pervasives_Native.Some uu____4995
         | uu____5000 -> FStar_Pervasives_Native.None)
    | uu____5021 -> FStar_Pervasives_Native.None in
  let decidable_eq neg psc args =
    let r = psc.psc_range in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r in
    match args with
    | (_typ,uu____5048)::(a1,uu____5050)::(a2,uu____5052)::[] ->
        let uu____5089 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____5089 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____5102 -> FStar_Pervasives_Native.None)
    | uu____5103 -> failwith "Unexpected number of arguments" in
  let idstep psc args =
    match args with
    | (a1,uu____5130)::[] -> FStar_Pervasives_Native.Some a1
    | uu____5139 -> failwith "Unexpected number of arguments" in
  let basic_ops =
    let uu____5163 =
      let uu____5178 =
        let uu____5193 =
          let uu____5208 =
            let uu____5223 =
              let uu____5238 =
                let uu____5253 =
                  let uu____5268 =
                    let uu____5283 =
                      let uu____5298 =
                        let uu____5313 =
                          let uu____5328 =
                            let uu____5343 =
                              let uu____5358 =
                                let uu____5373 =
                                  let uu____5388 =
                                    let uu____5403 =
                                      let uu____5418 =
                                        let uu____5433 =
                                          let uu____5448 =
                                            let uu____5463 =
                                              let uu____5476 =
                                                FStar_Parser_Const.p2l
                                                  ["FStar";
                                                  "String";
                                                  "list_of_string"] in
                                              (uu____5476,
                                                (Prims.parse_int "1"),
                                                (unary_op arg_as_string
                                                   list_of_string')) in
                                            let uu____5483 =
                                              let uu____5498 =
                                                let uu____5511 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "string_of_list"] in
                                                (uu____5511,
                                                  (Prims.parse_int "1"),
                                                  (unary_op
                                                     (arg_as_list
                                                        FStar_Syntax_Embeddings.unembed_char_safe)
                                                     string_of_list')) in
                                              let uu____5520 =
                                                let uu____5535 =
                                                  let uu____5550 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "concat"] in
                                                  (uu____5550,
                                                    (Prims.parse_int "2"),
                                                    string_concat') in
                                                let uu____5559 =
                                                  let uu____5576 =
                                                    let uu____5597 =
                                                      FStar_Parser_Const.p2l
                                                        ["Prims"; "range_of"] in
                                                    (uu____5597,
                                                      (Prims.parse_int "2"),
                                                      range_of1) in
                                                  let uu____5612 =
                                                    let uu____5635 =
                                                      let uu____5654 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "set_range_of"] in
                                                      (uu____5654,
                                                        (Prims.parse_int "3"),
                                                        set_range_of1) in
                                                    let uu____5667 =
                                                      let uu____5688 =
                                                        let uu____5703 =
                                                          FStar_Parser_Const.p2l
                                                            ["Prims";
                                                            "mk_range"] in
                                                        (uu____5703,
                                                          (Prims.parse_int
                                                             "5"), mk_range1) in
                                                      let uu____5712 =
                                                        let uu____5729 =
                                                          let uu____5748 =
                                                            FStar_Parser_Const.p2l
                                                              ["FStar";
                                                              "Range";
                                                              "prims_to_fstar_range"] in
                                                          (uu____5748,
                                                            (Prims.parse_int
                                                               "1"), idstep) in
                                                        [uu____5729] in
                                                      uu____5688 ::
                                                        uu____5712 in
                                                    uu____5635 :: uu____5667 in
                                                  uu____5576 :: uu____5612 in
                                                uu____5535 :: uu____5559 in
                                              uu____5498 :: uu____5520 in
                                            uu____5463 :: uu____5483 in
                                          (FStar_Parser_Const.op_notEq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq true)) ::
                                            uu____5448 in
                                        (FStar_Parser_Const.op_Eq,
                                          (Prims.parse_int "3"),
                                          (decidable_eq false)) :: uu____5433 in
                                      (FStar_Parser_Const.string_compare,
                                        (Prims.parse_int "2"),
                                        (binary_op arg_as_string
                                           string_compare'))
                                        :: uu____5418 in
                                    (FStar_Parser_Const.string_of_bool_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_bool string_of_bool2))
                                      :: uu____5403 in
                                  (FStar_Parser_Const.string_of_int_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_int string_of_int2)) ::
                                    uu____5388 in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____5373 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____5358 in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____5343 in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____5328 in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____5313 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____5298 in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                FStar_Syntax_Embeddings.embed_bool r (x >= y))))
                      :: uu____5283 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              FStar_Syntax_Embeddings.embed_bool r (x > y))))
                    :: uu____5268 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            FStar_Syntax_Embeddings.embed_bool r (x <= y))))
                  :: uu____5253 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          FStar_Syntax_Embeddings.embed_bool r (x < y))))
                :: uu____5238 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____5223 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____5208 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____5193 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____5178 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____5163 in
  let bounded_arith_ops =
    let bounded_int_types =
      ["Int8";
      "UInt8";
      "Int16";
      "UInt16";
      "Int32";
      "UInt32";
      "Int64";
      "UInt64";
      "UInt128"] in
    let int_as_bounded r int_to_t1 n1 =
      let c = FStar_Syntax_Embeddings.embed_int r n1 in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1 in
      let uu____6363 =
        let uu____6364 =
          let uu____6365 = FStar_Syntax_Syntax.as_arg c in [uu____6365] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____6364 in
      uu____6363 FStar_Pervasives_Native.None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____6400 =
              let uu____6413 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
              (uu____6413, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____6432  ->
                        fun uu____6433  ->
                          match (uu____6432, uu____6433) with
                          | ((int_to_t1,x),(uu____6452,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____6462 =
              let uu____6477 =
                let uu____6490 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                (uu____6490, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____6509  ->
                          fun uu____6510  ->
                            match (uu____6509, uu____6510) with
                            | ((int_to_t1,x),(uu____6529,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____6539 =
                let uu____6554 =
                  let uu____6567 = FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                  (uu____6567, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____6586  ->
                            fun uu____6587  ->
                              match (uu____6586, uu____6587) with
                              | ((int_to_t1,x),(uu____6606,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____6554] in
              uu____6477 :: uu____6539 in
            uu____6400 :: uu____6462)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop psc args =
    let r = psc.psc_range in
    match args with
    | (_typ,uu____6705)::(a1,uu____6707)::(a2,uu____6709)::[] ->
        let uu____6746 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6746 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___215_6752 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___215_6752.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___215_6752.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___216_6756 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___216_6756.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___216_6756.FStar_Syntax_Syntax.vars)
                })
         | uu____6757 -> FStar_Pervasives_Native.None)
    | (_typ,uu____6759)::uu____6760::(a1,uu____6762)::(a2,uu____6764)::[] ->
        let uu____6813 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6813 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___215_6819 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___215_6819.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___215_6819.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___216_6823 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___216_6823.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___216_6823.FStar_Syntax_Syntax.vars)
                })
         | uu____6824 -> FStar_Pervasives_Native.None)
    | uu____6825 -> failwith "Unexpected number of arguments" in
  let propositional_equality =
    {
      name = FStar_Parser_Const.eq2_lid;
      arity = (Prims.parse_int "3");
      strong_reduction_ok = true;
      requires_binder_substitution = false;
      interpretation = interp_prop
    } in
  let hetero_propositional_equality =
    {
      name = FStar_Parser_Const.eq3_lid;
      arity = (Prims.parse_int "4");
      strong_reduction_ok = true;
      requires_binder_substitution = false;
      interpretation = interp_prop
    } in
  [propositional_equality; hetero_propositional_equality]
let unembed_binder:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option
  =
  fun t  ->
    try
      let uu____6845 =
        let uu____6846 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____6846 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____6845
    with | uu____6852 -> FStar_Pervasives_Native.None
let mk_psc_subst:
  'Auu____6859 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6859) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____6919  ->
           fun subst1  ->
             match uu____6919 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,memo,uu____6961)) ->
                      let uu____7020 = b in
                      (match uu____7020 with
                       | (bv,uu____7028) ->
                           let uu____7029 =
                             let uu____7030 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.fstar_reflection_types_binder_lid in
                             Prims.op_Negation uu____7030 in
                           if uu____7029
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term in
                              let uu____7035 = unembed_binder term1 in
                              match uu____7035 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____7042 =
                                      let uu___219_7043 = bv in
                                      let uu____7044 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___219_7043.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___219_7043.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____7044
                                      } in
                                    FStar_Syntax_Syntax.freshen_bv uu____7042 in
                                  let b_for_x =
                                    let uu____7048 =
                                      let uu____7055 =
                                        FStar_Syntax_Syntax.bv_to_name b1 in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____7055) in
                                    FStar_Syntax_Syntax.NT uu____7048 in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___184_7064  ->
                                         match uu___184_7064 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____7065,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____7067;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____7068;_})
                                             ->
                                             Prims.op_Negation
                                               (FStar_Ident.ident_equals
                                                  b1.FStar_Syntax_Syntax.ppname
                                                  b'.FStar_Syntax_Syntax.ppname)
                                         | uu____7073 -> true) subst1 in
                                  b_for_x :: subst2))
                  | uu____7074 -> subst1)) env []
let reduce_primops:
  'Auu____7097 'Auu____7098 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7098) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7097 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun tm  ->
          let uu____7139 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Primops cfg.steps) in
          if uu____7139
          then tm
          else
            (let uu____7141 = FStar_Syntax_Util.head_and_args tm in
             match uu____7141 with
             | (head1,args) ->
                 let uu____7178 =
                   let uu____7179 = FStar_Syntax_Util.un_uinst head1 in
                   uu____7179.FStar_Syntax_Syntax.n in
                 (match uu____7178 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____7183 =
                        FStar_List.tryFind
                          (fun ps  ->
                             FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                          cfg.primitive_steps in
                      (match uu____7183 with
                       | FStar_Pervasives_Native.None  -> tm
                       | FStar_Pervasives_Native.Some prim_step ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____7200  ->
                                   let uu____7201 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name in
                                   let uu____7202 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args) in
                                   let uu____7209 =
                                     FStar_Util.string_of_int prim_step.arity in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____7201 uu____7202 uu____7209);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____7214  ->
                                   let uu____7215 =
                                     FStar_Syntax_Print.term_to_string tm in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____7215);
                              (let psc =
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst =
                                     (fun uu____7218  ->
                                        if
                                          prim_step.requires_binder_substitution
                                        then mk_psc_subst cfg env
                                        else [])
                                 } in
                               let uu____7220 =
                                 prim_step.interpretation psc args in
                               match uu____7220 with
                               | FStar_Pervasives_Native.None  ->
                                   (log_primops cfg
                                      (fun uu____7226  ->
                                         let uu____7227 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____7227);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____7233  ->
                                         let uu____7234 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         let uu____7235 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____7234 uu____7235);
                                    reduced))))
                  | uu____7236 -> tm))
let reduce_equality:
  'Auu____7247 'Auu____7248 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7248) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7247 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___220_7286 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___220_7286.tcenv);
           delta_level = (uu___220_7286.delta_level);
           primitive_steps = equality_ops
         }) tm
let maybe_simplify:
  'Auu____7299 'Auu____7300 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7300) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7299 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack1 tm in
          let uu____7342 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Simplify cfg.steps) in
          if uu____7342
          then tm1
          else
            (let w t =
               let uu___221_7354 = t in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___221_7354.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___221_7354.FStar_Syntax_Syntax.vars)
               } in
             let simp_t t =
               match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____7371 -> FStar_Pervasives_Native.None in
             let simplify1 arg =
               ((simp_t (FStar_Pervasives_Native.fst arg)), arg) in
             match tm1.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____7411;
                         FStar_Syntax_Syntax.vars = uu____7412;_},uu____7413);
                    FStar_Syntax_Syntax.pos = uu____7414;
                    FStar_Syntax_Syntax.vars = uu____7415;_},args)
                 ->
                 let uu____7441 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____7441
                 then
                   let uu____7442 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____7442 with
                    | (FStar_Pervasives_Native.Some (true ),uu____7497)::
                        (uu____7498,(arg,uu____7500))::[] -> arg
                    | (uu____7565,(arg,uu____7567))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____7568)::[]
                        -> arg
                    | (FStar_Pervasives_Native.Some (false ),uu____7633)::uu____7634::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7697::(FStar_Pervasives_Native.Some (false
                                   ),uu____7698)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7761 -> tm1)
                 else
                   (let uu____7777 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____7777
                    then
                      let uu____7778 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____7778 with
                      | (FStar_Pervasives_Native.Some (true ),uu____7833)::uu____7834::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____7897::(FStar_Pervasives_Native.Some (true
                                     ),uu____7898)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____7961)::
                          (uu____7962,(arg,uu____7964))::[] -> arg
                      | (uu____8029,(arg,uu____8031))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____8032)::[]
                          -> arg
                      | uu____8097 -> tm1
                    else
                      (let uu____8113 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____8113
                       then
                         let uu____8114 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____8114 with
                         | uu____8169::(FStar_Pervasives_Native.Some (true
                                        ),uu____8170)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____8233)::uu____8234::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____8297)::
                             (uu____8298,(arg,uu____8300))::[] -> arg
                         | (uu____8365,(p,uu____8367))::(uu____8368,(q,uu____8370))::[]
                             ->
                             let uu____8435 = FStar_Syntax_Util.term_eq p q in
                             (if uu____8435
                              then w FStar_Syntax_Util.t_true
                              else tm1)
                         | uu____8437 -> tm1
                       else
                         (let uu____8453 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____8453
                          then
                            let uu____8454 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____8454 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____8509)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____8548)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____8587 -> tm1
                          else
                            (let uu____8603 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____8603
                             then
                               match args with
                               | (t,uu____8605)::[] ->
                                   let uu____8622 =
                                     let uu____8623 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8623.FStar_Syntax_Syntax.n in
                                   (match uu____8622 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8626::[],body,uu____8628) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8655 -> tm1)
                                    | uu____8658 -> tm1)
                               | (uu____8659,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____8660))::
                                   (t,uu____8662)::[] ->
                                   let uu____8701 =
                                     let uu____8702 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8702.FStar_Syntax_Syntax.n in
                                   (match uu____8701 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8705::[],body,uu____8707) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8734 -> tm1)
                                    | uu____8737 -> tm1)
                               | uu____8738 -> tm1
                             else
                               (let uu____8748 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____8748
                                then
                                  match args with
                                  | (t,uu____8750)::[] ->
                                      let uu____8767 =
                                        let uu____8768 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8768.FStar_Syntax_Syntax.n in
                                      (match uu____8767 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8771::[],body,uu____8773)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8800 -> tm1)
                                       | uu____8803 -> tm1)
                                  | (uu____8804,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____8805))::(t,uu____8807)::[] ->
                                      let uu____8846 =
                                        let uu____8847 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8847.FStar_Syntax_Syntax.n in
                                      (match uu____8846 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8850::[],body,uu____8852)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8879 -> tm1)
                                       | uu____8882 -> tm1)
                                  | uu____8883 -> tm1
                                else reduce_equality cfg env stack1 tm1)))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____8894;
                    FStar_Syntax_Syntax.vars = uu____8895;_},args)
                 ->
                 let uu____8917 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____8917
                 then
                   let uu____8918 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____8918 with
                    | (FStar_Pervasives_Native.Some (true ),uu____8973)::
                        (uu____8974,(arg,uu____8976))::[] -> arg
                    | (uu____9041,(arg,uu____9043))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____9044)::[]
                        -> arg
                    | (FStar_Pervasives_Native.Some (false ),uu____9109)::uu____9110::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9173::(FStar_Pervasives_Native.Some (false
                                   ),uu____9174)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9237 -> tm1)
                 else
                   (let uu____9253 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____9253
                    then
                      let uu____9254 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____9254 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9309)::uu____9310::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____9373::(FStar_Pervasives_Native.Some (true
                                     ),uu____9374)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____9437)::
                          (uu____9438,(arg,uu____9440))::[] -> arg
                      | (uu____9505,(arg,uu____9507))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____9508)::[]
                          -> arg
                      | uu____9573 -> tm1
                    else
                      (let uu____9589 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____9589
                       then
                         let uu____9590 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____9590 with
                         | uu____9645::(FStar_Pervasives_Native.Some (true
                                        ),uu____9646)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____9709)::uu____9710::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____9773)::
                             (uu____9774,(arg,uu____9776))::[] -> arg
                         | (uu____9841,(p,uu____9843))::(uu____9844,(q,uu____9846))::[]
                             ->
                             let uu____9911 = FStar_Syntax_Util.term_eq p q in
                             (if uu____9911
                              then w FStar_Syntax_Util.t_true
                              else tm1)
                         | uu____9913 -> tm1
                       else
                         (let uu____9929 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____9929
                          then
                            let uu____9930 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____9930 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____9985)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____10024)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____10063 -> tm1
                          else
                            (let uu____10079 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____10079
                             then
                               match args with
                               | (t,uu____10081)::[] ->
                                   let uu____10098 =
                                     let uu____10099 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10099.FStar_Syntax_Syntax.n in
                                   (match uu____10098 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10102::[],body,uu____10104) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10131 -> tm1)
                                    | uu____10134 -> tm1)
                               | (uu____10135,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____10136))::
                                   (t,uu____10138)::[] ->
                                   let uu____10177 =
                                     let uu____10178 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10178.FStar_Syntax_Syntax.n in
                                   (match uu____10177 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10181::[],body,uu____10183) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10210 -> tm1)
                                    | uu____10213 -> tm1)
                               | uu____10214 -> tm1
                             else
                               (let uu____10224 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____10224
                                then
                                  match args with
                                  | (t,uu____10226)::[] ->
                                      let uu____10243 =
                                        let uu____10244 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10244.FStar_Syntax_Syntax.n in
                                      (match uu____10243 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10247::[],body,uu____10249)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10276 -> tm1)
                                       | uu____10279 -> tm1)
                                  | (uu____10280,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____10281))::(t,uu____10283)::[] ->
                                      let uu____10322 =
                                        let uu____10323 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10323.FStar_Syntax_Syntax.n in
                                      (match uu____10322 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10326::[],body,uu____10328)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10355 -> tm1)
                                       | uu____10358 -> tm1)
                                  | uu____10359 -> tm1
                                else reduce_equality cfg env stack1 tm1)))))
             | uu____10369 -> tm1)
let is_norm_request:
  'Auu____10376 .
    FStar_Syntax_Syntax.term -> 'Auu____10376 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10389 =
        let uu____10396 =
          let uu____10397 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10397.FStar_Syntax_Syntax.n in
        (uu____10396, args) in
      match uu____10389 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10403::uu____10404::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10408::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10413::uu____10414::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10417 -> false
let tr_norm_step: FStar_Syntax_Embeddings.norm_step -> step Prims.list =
  fun uu___185_10429  ->
    match uu___185_10429 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10435 =
          let uu____10438 =
            let uu____10439 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____10439 in
          [uu____10438] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10435
let tr_norm_steps:
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list =
  fun s  -> FStar_List.concatMap tr_norm_step s
let get_norm_request:
  'Auu____10458 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10458) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10496 =
          let uu____10499 =
            let uu____10504 =
              FStar_Syntax_Embeddings.unembed_list
                FStar_Syntax_Embeddings.unembed_norm_step in
            uu____10504 s in
          FStar_All.pipe_right uu____10499 FStar_Util.must in
        FStar_All.pipe_right uu____10496 tr_norm_steps in
      match args with
      | uu____10529::(tm,uu____10531)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____10554)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____10569)::uu____10570::(tm,uu____10572)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____10612 =
              let uu____10615 = full_norm steps in parse_steps uu____10615 in
            Beta :: uu____10612 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____10624 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___186_10642  ->
    match uu___186_10642 with
    | (App
        (uu____10645,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____10646;
                       FStar_Syntax_Syntax.vars = uu____10647;_},uu____10648,uu____10649))::uu____10650
        -> true
    | uu____10657 -> false
let firstn:
  'Auu____10666 .
    Prims.int ->
      'Auu____10666 Prims.list ->
        ('Auu____10666 Prims.list,'Auu____10666 Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun k  ->
    fun l  ->
      if (FStar_List.length l) < k then (l, []) else FStar_Util.first_N k l
let should_reify: cfg -> stack_elt Prims.list -> Prims.bool =
  fun cfg  ->
    fun stack1  ->
      match stack1 with
      | (App
          (uu____10704,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____10705;
                         FStar_Syntax_Syntax.vars = uu____10706;_},uu____10707,uu____10708))::uu____10709
          -> FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)
      | uu____10716 -> false
let rec norm:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun t  ->
          let t1 = FStar_Syntax_Subst.compress t in
          log cfg
            (fun uu____10832  ->
               let uu____10833 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____10834 = FStar_Syntax_Print.term_to_string t1 in
               let uu____10835 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____10842 =
                 let uu____10843 =
                   let uu____10846 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____10846 in
                 stack_to_string uu____10843 in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____10833 uu____10834 uu____10835 uu____10842);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____10869 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____10894 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____10911 =
                 let uu____10912 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____10913 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____10912 uu____10913 in
               failwith uu____10911
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____10914 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____10931 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____10932 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10933;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____10934;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10937;
                 FStar_Syntax_Syntax.fv_delta = uu____10938;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10939;
                 FStar_Syntax_Syntax.fv_delta = uu____10940;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____10941);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar fv when
               let uu____10949 = FStar_Syntax_Syntax.lid_of_fv fv in
               FStar_TypeChecker_Env.is_action cfg.tcenv uu____10949 ->
               let b = should_reify cfg stack1 in
               (log cfg
                  (fun uu____10955  ->
                     let uu____10956 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____10957 = FStar_Util.string_of_bool b in
                     FStar_Util.print2
                       ">>> For DM4F action %s, should_reify = %s\n"
                       uu____10956 uu____10957);
                if b
                then
                  (let uu____10958 = FStar_List.tl stack1 in
                   do_unfold_fv cfg env uu____10958 t1 fv)
                else rebuild cfg env stack1 t1)
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((FStar_Syntax_Util.is_fstar_tactics_embed hd1) ||
                  ((FStar_Syntax_Util.is_fstar_tactics_quote hd1) &&
                     (FStar_List.contains NoDeltaSteps cfg.steps)))
                 || (FStar_Syntax_Util.is_fstar_tactics_by_tactic hd1)
               ->
               let args1 = closures_as_args_delayed cfg env args in
               let hd2 = closure_as_term cfg env hd1 in
               let t2 =
                 let uu___222_10997 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___222_10997.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___222_10997.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____11030 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____11030) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___223_11038 = cfg in
                 let uu____11039 =
                   FStar_List.filter
                     (fun uu___187_11042  ->
                        match uu___187_11042 with
                        | UnfoldOnly uu____11043 -> false
                        | NoDeltaSteps  -> false
                        | uu____11046 -> true) cfg.steps in
                 {
                   steps = uu____11039;
                   tcenv = (uu___223_11038.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___223_11038.primitive_steps)
                 } in
               let uu____11047 = get_norm_request (norm cfg' env []) args in
               (match uu____11047 with
                | (s,tm) ->
                    let delta_level =
                      let uu____11063 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___188_11068  ->
                                match uu___188_11068 with
                                | UnfoldUntil uu____11069 -> true
                                | UnfoldOnly uu____11070 -> true
                                | uu____11073 -> false)) in
                      if uu____11063
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___224_11078 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___224_11078.tcenv);
                        delta_level;
                        primitive_steps = (uu___224_11078.primitive_steps)
                      } in
                    let stack' =
                      let tail1 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let uu____11089 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms") in
                      if uu____11089
                      then
                        let uu____11092 =
                          let uu____11093 =
                            let uu____11098 = FStar_Util.now () in
                            (t1, uu____11098) in
                          Debug uu____11093 in
                        uu____11092 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11100;
                  FStar_Syntax_Syntax.vars = uu____11101;_},a1::a2::rest)
               ->
               let uu____11149 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11149 with
                | (hd1,uu____11165) ->
                    let t' =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_app (hd1, [a1]))
                        FStar_Pervasives_Native.None
                        t1.FStar_Syntax_Syntax.pos in
                    let t2 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_app (t', (a2 :: rest)))
                        FStar_Pervasives_Native.None
                        t1.FStar_Syntax_Syntax.pos in
                    norm cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect uu____11230);
                  FStar_Syntax_Syntax.pos = uu____11231;
                  FStar_Syntax_Syntax.vars = uu____11232;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____11264 = FStar_List.tl stack1 in
               norm cfg env uu____11264 (FStar_Pervasives_Native.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11267;
                  FStar_Syntax_Syntax.vars = uu____11268;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____11300 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11300 with
                | (reify_head,uu____11316) ->
                    let a1 =
                      let uu____11338 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (FStar_Pervasives_Native.fst a) in
                      FStar_Syntax_Subst.compress uu____11338 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____11341);
                            FStar_Syntax_Syntax.pos = uu____11342;
                            FStar_Syntax_Syntax.vars = uu____11343;_},a2::[])
                         ->
                         norm cfg env stack1 (FStar_Pervasives_Native.fst a2)
                     | uu____11377 ->
                         let stack2 =
                           (App
                              (env, reify_head, FStar_Pervasives_Native.None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____11387 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____11387
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11394 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____11394
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____11397 =
                      let uu____11404 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____11404, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____11397 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___189_11417  ->
                         match uu___189_11417 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____11420 =
                   (FStar_List.mem FStar_TypeChecker_Env.UnfoldTac
                      cfg.delta_level)
                     &&
                     (((((((((FStar_Syntax_Syntax.fv_eq_lid f
                                FStar_Parser_Const.and_lid)
                               ||
                               (FStar_Syntax_Syntax.fv_eq_lid f
                                  FStar_Parser_Const.or_lid))
                              ||
                              (FStar_Syntax_Syntax.fv_eq_lid f
                                 FStar_Parser_Const.imp_lid))
                             ||
                             (FStar_Syntax_Syntax.fv_eq_lid f
                                FStar_Parser_Const.forall_lid))
                            ||
                            (FStar_Syntax_Syntax.fv_eq_lid f
                               FStar_Parser_Const.squash_lid))
                           ||
                           (FStar_Syntax_Syntax.fv_eq_lid f
                              FStar_Parser_Const.exists_lid))
                          ||
                          (FStar_Syntax_Syntax.fv_eq_lid f
                             FStar_Parser_Const.eq2_lid))
                         ||
                         (FStar_Syntax_Syntax.fv_eq_lid f
                            FStar_Parser_Const.true_lid))
                        ||
                        (FStar_Syntax_Syntax.fv_eq_lid f
                           FStar_Parser_Const.false_lid)) in
                 if uu____11420
                 then false
                 else
                   (let uu____11422 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___190_11429  ->
                              match uu___190_11429 with
                              | UnfoldOnly uu____11430 -> true
                              | uu____11433 -> false)) in
                    match uu____11422 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____11437 -> should_delta) in
               (log cfg
                  (fun uu____11445  ->
                     let uu____11446 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11447 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                     let uu____11448 =
                       FStar_Util.string_of_bool should_delta1 in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____11446 uu____11447 uu____11448);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack1 t1
                else do_unfold_fv cfg env stack1 t1 f)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11451 = lookup_bvar env x in
               (match uu____11451 with
                | Univ uu____11454 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____11503 = FStar_ST.op_Bang r in
                      (match uu____11503 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11640  ->
                                 let uu____11641 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____11642 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11641
                                   uu____11642);
                            (let uu____11643 =
                               let uu____11644 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____11644.FStar_Syntax_Syntax.n in
                             match uu____11643 with
                             | FStar_Syntax_Syntax.Tm_abs uu____11647 ->
                                 norm cfg env2 stack1 t'
                             | uu____11664 -> rebuild cfg env2 stack1 t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____11722)::uu____11723 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11732)::uu____11733 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11743,uu____11744))::stack_rest ->
                    (match c with
                     | Univ uu____11748 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____11757 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____11778  ->
                                    let uu____11779 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11779);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____11819  ->
                                    let uu____11820 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11820);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg
                                  (((FStar_Pervasives_Native.Some b), c) ::
                                  env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___225_11870 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___225_11870.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____11903  ->
                          let uu____11904 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____11904);
                     norm cfg env stack2 t1)
                | (Debug uu____11905)::uu____11906 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____11913 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11913
                    else
                      (let uu____11915 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11915 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11957  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11985 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11985
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11995 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11995)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___226_12000 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___226_12000.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___226_12000.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12001 -> lopt in
                           (log cfg
                              (fun uu____12007  ->
                                 let uu____12008 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12008);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 = only_strong_steps cfg in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____12031)::uu____12032 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12039 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12039
                    else
                      (let uu____12041 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12041 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12083  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12111 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12111
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12121 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12121)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___226_12126 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___226_12126.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___226_12126.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12127 -> lopt in
                           (log cfg
                              (fun uu____12133  ->
                                 let uu____12134 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12134);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 = only_strong_steps cfg in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____12157)::uu____12158 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12169 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12169
                    else
                      (let uu____12171 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12171 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12213  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12241 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12241
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12251 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12251)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___226_12256 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___226_12256.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___226_12256.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12257 -> lopt in
                           (log cfg
                              (fun uu____12263  ->
                                 let uu____12264 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12264);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 = only_strong_steps cfg in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____12287)::uu____12288 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12299 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12299
                    else
                      (let uu____12301 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12301 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12343  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12371 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12371
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12381 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12381)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___226_12386 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___226_12386.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___226_12386.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12387 -> lopt in
                           (log cfg
                              (fun uu____12393  ->
                                 let uu____12394 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12394);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 = only_strong_steps cfg in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____12417)::uu____12418 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12433 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12433
                    else
                      (let uu____12435 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12435 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12477  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12505 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12505
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12515 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12515)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___226_12520 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___226_12520.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___226_12520.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12521 -> lopt in
                           (log cfg
                              (fun uu____12527  ->
                                 let uu____12528 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12528);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 = only_strong_steps cfg in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12551 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12551
                    else
                      (let uu____12553 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12553 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12595  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12623 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12623
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12633 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12633)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___226_12638 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___226_12638.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___226_12638.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12639 -> lopt in
                           (log cfg
                              (fun uu____12645  ->
                                 let uu____12646 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12646);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 = only_strong_steps cfg in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1))))
           | FStar_Syntax_Syntax.Tm_app (head1,args) ->
               let stack2 =
                 FStar_All.pipe_right stack1
                   (FStar_List.fold_right
                      (fun uu____12707  ->
                         fun stack2  ->
                           match uu____12707 with
                           | (a,aq) ->
                               let uu____12719 =
                                 let uu____12720 =
                                   let uu____12727 =
                                     let uu____12728 =
                                       let uu____12759 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____12759, false) in
                                     Clos uu____12728 in
                                   (uu____12727, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____12720 in
                               uu____12719 :: stack2) args) in
               (log cfg
                  (fun uu____12835  ->
                     let uu____12836 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12836);
                norm cfg env stack2 head1)
           | FStar_Syntax_Syntax.Tm_refine (x,f) ->
               if FStar_List.contains Weak cfg.steps
               then
                 (match (env, stack1) with
                  | ([],[]) ->
                      let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                      let t2 =
                        mk
                          (FStar_Syntax_Syntax.Tm_refine
                             ((let uu___227_12872 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___227_12872.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___227_12872.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____12873 ->
                      let uu____12878 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12878)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____12881 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____12881 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1 in
                      let t2 =
                        let uu____12912 =
                          let uu____12913 =
                            let uu____12920 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___228_12922 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___228_12922.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___228_12922.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12920) in
                          FStar_Syntax_Syntax.Tm_refine uu____12913 in
                        mk uu____12912 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains Weak cfg.steps
               then
                 let uu____12941 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____12941
               else
                 (let uu____12943 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____12943 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12951 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____12975  -> dummy :: env1) env) in
                        norm_comp cfg uu____12951 c1 in
                      let t2 =
                        let uu____12997 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____12997 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____13056)::uu____13057 ->
                    (log cfg
                       (fun uu____13068  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | (Arg uu____13069)::uu____13070 ->
                    (log cfg
                       (fun uu____13081  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | (App
                    (uu____13082,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____13083;
                                   FStar_Syntax_Syntax.vars = uu____13084;_},uu____13085,uu____13086))::uu____13087
                    ->
                    (log cfg
                       (fun uu____13096  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | (MemoLazy uu____13097)::uu____13098 ->
                    (log cfg
                       (fun uu____13109  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | uu____13110 ->
                    (log cfg
                       (fun uu____13113  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11 in
                      log cfg
                        (fun uu____13117  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____13134 = norm cfg env [] t2 in
                             FStar_Util.Inl uu____13134
                         | FStar_Util.Inr c ->
                             let uu____13142 = norm_comp cfg env c in
                             FStar_Util.Inr uu____13142 in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env []) in
                       let uu____13148 =
                         let uu____13149 =
                           let uu____13150 =
                             let uu____13177 =
                               FStar_Syntax_Util.unascribe t12 in
                             (uu____13177, (tc1, tacopt1), l) in
                           FStar_Syntax_Syntax.Tm_ascribed uu____13150 in
                         mk uu____13149 t1.FStar_Syntax_Syntax.pos in
                       rebuild cfg env stack1 uu____13148))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____13253,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____13254;
                               FStar_Syntax_Syntax.lbunivs = uu____13255;
                               FStar_Syntax_Syntax.lbtyp = uu____13256;
                               FStar_Syntax_Syntax.lbeff = uu____13257;
                               FStar_Syntax_Syntax.lbdef = uu____13258;_}::uu____13259),uu____13260)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____13296 =
                 (let uu____13299 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____13299) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____13301 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____13301))) in
               if uu____13296
               then
                 let binder =
                   let uu____13303 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   FStar_Syntax_Syntax.mk_binder uu____13303 in
                 let env1 =
                   let uu____13313 =
                     let uu____13320 =
                       let uu____13321 =
                         let uu____13352 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____13352,
                           false) in
                       Clos uu____13321 in
                     ((FStar_Pervasives_Native.Some binder), uu____13320) in
                   uu____13313 :: env in
                 (log cfg
                    (fun uu____13437  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack1 body)
               else
                 (let uu____13439 =
                    let uu____13444 =
                      let uu____13445 =
                        let uu____13446 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____13446
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____13445] in
                    FStar_Syntax_Subst.open_term uu____13444 body in
                  match uu____13439 with
                  | (bs,body1) ->
                      (log cfg
                         (fun uu____13455  ->
                            FStar_Util.print_string
                              "+++ Normalizing Tm_let -- type\n");
                       (let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let lbname =
                          let x =
                            let uu____13463 = FStar_List.hd bs in
                            FStar_Pervasives_Native.fst uu____13463 in
                          FStar_Util.Inl
                            (let uu___229_13473 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___229_13473.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___229_13473.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = ty
                             }) in
                        log cfg
                          (fun uu____13476  ->
                             FStar_Util.print_string
                               "+++ Normalizing Tm_let -- definiens\n");
                        (let lb1 =
                           let uu___230_13478 = lb in
                           let uu____13479 =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname = lbname;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___230_13478.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = ty;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___230_13478.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____13479
                           } in
                         let env' =
                           FStar_All.pipe_right bs
                             (FStar_List.fold_left
                                (fun env1  ->
                                   fun uu____13514  -> dummy :: env1) env) in
                         let cfg1 = only_strong_steps cfg in
                         log cfg1
                           (fun uu____13536  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- body\n");
                         norm cfg1 env'
                           ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1) body1))))
           | FStar_Syntax_Syntax.Tm_let ((true ,lbs),body) when
               (FStar_List.contains CompressUvars cfg.steps) ||
                 ((FStar_List.contains (Exclude Zeta) cfg.steps) &&
                    (FStar_List.contains PureSubtermsWithinComputations
                       cfg.steps))
               ->
               let uu____13553 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____13553 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____13589 =
                               let uu___231_13590 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___231_13590.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___231_13590.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____13589 in
                           let uu____13591 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____13591 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____13617 =
                                   FStar_List.map (fun uu____13633  -> dummy)
                                     lbs1 in
                                 let uu____13634 =
                                   let uu____13643 =
                                     FStar_List.map
                                       (fun uu____13663  -> dummy) xs1 in
                                   FStar_List.append uu____13643 env in
                                 FStar_List.append uu____13617 uu____13634 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13687 =
                                       let uu___232_13688 = rc in
                                       let uu____13689 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___232_13688.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13689;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___232_13688.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____13687
                                 | uu____13696 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___233_13700 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___233_13700.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___233_13700.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____13710 =
                        FStar_List.map (fun uu____13726  -> dummy) lbs2 in
                      FStar_List.append uu____13710 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____13734 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____13734 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___234_13750 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___234_13750.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___234_13750.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____13777 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____13777
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13796 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13872  ->
                        match uu____13872 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___235_13993 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___235_13993.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___235_13993.FStar_Syntax_Syntax.sort)
                              } in
                            let f_i = FStar_Syntax_Syntax.bv_to_tm bv in
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos in
                            let memo =
                              FStar_Util.mk_ref FStar_Pervasives_Native.None in
                            let rec_env1 =
                              (FStar_Pervasives_Native.None,
                                (Clos (env, fix_f_i, memo, true)))
                              :: rec_env in
                            (rec_env1, (memo :: memos),
                              (i + (Prims.parse_int "1"))))
                   (FStar_Pervasives_Native.snd lbs)
                   (env, [], (Prims.parse_int "0")) in
               (match uu____13796 with
                | (rec_env,memos,uu____14190) ->
                    let uu____14243 =
                      FStar_List.map2
                        (fun lb  ->
                           fun memo  ->
                             FStar_ST.op_Colon_Equals memo
                               (FStar_Pervasives_Native.Some
                                  (rec_env, (lb.FStar_Syntax_Syntax.lbdef))))
                        (FStar_Pervasives_Native.snd lbs) memos in
                    let body_env =
                      FStar_List.fold_right
                        (fun lb  ->
                           fun env1  ->
                             let uu____14774 =
                               let uu____14781 =
                                 let uu____14782 =
                                   let uu____14813 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____14813, false) in
                                 Clos uu____14782 in
                               (FStar_Pervasives_Native.None, uu____14781) in
                             uu____14774 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env in
                    norm cfg body_env stack1 body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (match m with
                | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                    let uu____14918 =
                      let uu____14919 = should_reify cfg stack1 in
                      Prims.op_Negation uu____14919 in
                    if uu____14918
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____14929 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____14929
                        then
                          let uu___236_14930 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___236_14930.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps =
                              (uu___236_14930.primitive_steps)
                          }
                        else
                          (let uu___237_14932 = cfg in
                           {
                             steps =
                               (FStar_List.append [Exclude Zeta] cfg.steps);
                             tcenv = (uu___237_14932.tcenv);
                             delta_level = (uu___237_14932.delta_level);
                             primitive_steps =
                               (uu___237_14932.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____14934 =
                         let uu____14935 = FStar_Syntax_Subst.compress head1 in
                         uu____14935.FStar_Syntax_Syntax.n in
                       match uu____14934 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____14953 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____14953 with
                            | (uu____14954,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____14960 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____14968 =
                                         let uu____14969 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____14969.FStar_Syntax_Syntax.n in
                                       match uu____14968 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____14975,uu____14976))
                                           ->
                                           let uu____14985 =
                                             let uu____14986 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____14986.FStar_Syntax_Syntax.n in
                                           (match uu____14985 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____14992,msrc,uu____14994))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____15003 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu____15003
                                            | uu____15004 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____15005 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____15006 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____15006 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___238_15011 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___238_15011.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___238_15011.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___238_15011.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____15012 =
                                            FStar_List.tl stack1 in
                                          let uu____15013 =
                                            let uu____15014 =
                                              let uu____15017 =
                                                let uu____15018 =
                                                  let uu____15031 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____15031) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____15018 in
                                              FStar_Syntax_Syntax.mk
                                                uu____15017 in
                                            uu____15014
                                              FStar_Pervasives_Native.None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____15012
                                            uu____15013
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____15047 =
                                            let uu____15048 = is_return body in
                                            match uu____15048 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____15052;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____15053;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____15058 -> false in
                                          if uu____15047
                                          then
                                            norm cfg env stack1
                                              lb.FStar_Syntax_Syntax.lbdef
                                          else
                                            (let head2 =
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Util.mk_reify
                                                 lb.FStar_Syntax_Syntax.lbdef in
                                             let body1 =
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Util.mk_reify
                                                 body in
                                             let body_rc =
                                               {
                                                 FStar_Syntax_Syntax.residual_effect
                                                   = m1;
                                                 FStar_Syntax_Syntax.residual_typ
                                                   =
                                                   (FStar_Pervasives_Native.Some
                                                      t2);
                                                 FStar_Syntax_Syntax.residual_flags
                                                   = []
                                               } in
                                             let body2 =
                                               let uu____15082 =
                                                 let uu____15085 =
                                                   let uu____15086 =
                                                     let uu____15103 =
                                                       let uu____15106 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____15106] in
                                                     (uu____15103, body1,
                                                       (FStar_Pervasives_Native.Some
                                                          body_rc)) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____15086 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____15085 in
                                               uu____15082
                                                 FStar_Pervasives_Native.None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____15122 =
                                                 let uu____15123 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____15123.FStar_Syntax_Syntax.n in
                                               match uu____15122 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____15129::uu____15130::[])
                                                   ->
                                                   let uu____15137 =
                                                     let uu____15140 =
                                                       let uu____15141 =
                                                         let uu____15148 =
                                                           let uu____15151 =
                                                             let uu____15152
                                                               =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____15152 in
                                                           let uu____15153 =
                                                             let uu____15156
                                                               =
                                                               let uu____15157
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____15157 in
                                                             [uu____15156] in
                                                           uu____15151 ::
                                                             uu____15153 in
                                                         (bind1, uu____15148) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____15141 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____15140 in
                                                   uu____15137
                                                     FStar_Pervasives_Native.None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____15165 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____15171 =
                                                 let uu____15174 =
                                                   let uu____15175 =
                                                     let uu____15190 =
                                                       let uu____15193 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____15194 =
                                                         let uu____15197 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____15198 =
                                                           let uu____15201 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____15202 =
                                                             let uu____15205
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____15206
                                                               =
                                                               let uu____15209
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____15210
                                                                 =
                                                                 let uu____15213
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____15213] in
                                                               uu____15209 ::
                                                                 uu____15210 in
                                                             uu____15205 ::
                                                               uu____15206 in
                                                           uu____15201 ::
                                                             uu____15202 in
                                                         uu____15197 ::
                                                           uu____15198 in
                                                       uu____15193 ::
                                                         uu____15194 in
                                                     (bind_inst, uu____15190) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____15175 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____15174 in
                                               uu____15171
                                                 FStar_Pervasives_Native.None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____15221 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____15221 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____15245 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____15245 with
                            | (uu____15246,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____15281 =
                                        let uu____15282 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____15282.FStar_Syntax_Syntax.n in
                                      match uu____15281 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____15288) -> t4
                                      | uu____15293 -> head2 in
                                    let uu____15294 =
                                      let uu____15295 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____15295.FStar_Syntax_Syntax.n in
                                    match uu____15294 with
                                    | FStar_Syntax_Syntax.Tm_fvar x ->
                                        FStar_Pervasives_Native.Some x
                                    | uu____15301 ->
                                        FStar_Pervasives_Native.None in
                                  let uu____15302 = maybe_extract_fv head2 in
                                  match uu____15302 with
                                  | FStar_Pervasives_Native.Some x when
                                      let uu____15312 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____15312
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____15317 =
                                          maybe_extract_fv head3 in
                                        match uu____15317 with
                                        | FStar_Pervasives_Native.Some
                                            uu____15322 ->
                                            FStar_Pervasives_Native.Some true
                                        | uu____15323 ->
                                            FStar_Pervasives_Native.Some
                                              false in
                                      (head3, action_unfolded)
                                  | uu____15328 ->
                                      (head2, FStar_Pervasives_Native.None) in
                                ((let is_arg_impure uu____15343 =
                                    match uu____15343 with
                                    | (e,q) ->
                                        let uu____15350 =
                                          let uu____15351 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____15351.FStar_Syntax_Syntax.n in
                                        (match uu____15350 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____15366 -> false) in
                                  let uu____15367 =
                                    let uu____15368 =
                                      let uu____15375 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____15375 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____15368 in
                                  if uu____15367
                                  then
                                    let uu____15380 =
                                      let uu____15381 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____15381 in
                                    failwith uu____15380
                                  else ());
                                 (let uu____15383 =
                                    maybe_unfold_action head_app in
                                  match uu____15383 with
                                  | (head_app1,found_action) ->
                                      let mk1 tm =
                                        FStar_Syntax_Syntax.mk tm
                                          FStar_Pervasives_Native.None
                                          t2.FStar_Syntax_Syntax.pos in
                                      let body =
                                        mk1
                                          (FStar_Syntax_Syntax.Tm_app
                                             (head_app1, args)) in
                                      let body1 =
                                        match found_action with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Syntax_Util.mk_reify body
                                        | FStar_Pervasives_Native.Some (false
                                            ) ->
                                            mk1
                                              (FStar_Syntax_Syntax.Tm_meta
                                                 (body,
                                                   (FStar_Syntax_Syntax.Meta_monadic
                                                      (m1, t2))))
                                        | FStar_Pervasives_Native.Some (true
                                            ) -> body in
                                      let uu____15422 = FStar_List.tl stack1 in
                                      norm cfg env uu____15422 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____15436 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____15436 in
                           let uu____15437 = FStar_List.tl stack1 in
                           norm cfg env uu____15437 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____15558  ->
                                     match uu____15558 with
                                     | (pat,wopt,tm) ->
                                         let uu____15606 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____15606))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____15638 = FStar_List.tl stack1 in
                           norm cfg env uu____15638 tm
                       | uu____15639 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let uu____15647 = should_reify cfg stack1 in
                    if uu____15647
                    then
                      let uu____15648 = FStar_List.tl stack1 in
                      let uu____15649 =
                        let uu____15650 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____15650 in
                      norm cfg env uu____15648 uu____15649
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____15653 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____15653
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___239_15662 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___239_15662.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___239_15662.primitive_steps)
                           } in
                         norm cfg1 env
                           ((Meta
                               ((FStar_Syntax_Syntax.Meta_monadic_lift
                                   (m1, m', t3)),
                                 (head1.FStar_Syntax_Syntax.pos))) :: stack2)
                           head1
                       else
                         norm cfg env
                           ((Meta
                               ((FStar_Syntax_Syntax.Meta_monadic_lift
                                   (m1, m', t3)),
                                 (head1.FStar_Syntax_Syntax.pos))) :: stack1)
                           head1)
                | uu____15664 ->
                    if FStar_List.contains Unmeta cfg.steps
                    then norm cfg env stack1 head1
                    else
                      (match stack1 with
                       | uu____15666::uu____15667 ->
                           (match m with
                            | FStar_Syntax_Syntax.Meta_labeled
                                (l,r,uu____15672) ->
                                norm cfg env ((Meta (m, r)) :: stack1) head1
                            | FStar_Syntax_Syntax.Meta_alien uu____15673 ->
                                rebuild cfg env stack1 t1
                            | FStar_Syntax_Syntax.Meta_pattern args ->
                                let args1 = norm_pattern_args cfg env args in
                                norm cfg env
                                  ((Meta
                                      ((FStar_Syntax_Syntax.Meta_pattern
                                          args1),
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) head1
                            | uu____15704 -> norm cfg env stack1 head1)
                       | [] ->
                           let head2 = norm cfg env [] head1 in
                           let m1 =
                             match m with
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let uu____15718 =
                                   norm_pattern_args cfg env args in
                                 FStar_Syntax_Syntax.Meta_pattern uu____15718
                             | uu____15729 -> m in
                           let t2 =
                             mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                               t1.FStar_Syntax_Syntax.pos in
                           rebuild cfg env stack1 t2)))
and do_unfold_fv:
  cfg ->
    env ->
      stack_elt Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun t0  ->
          fun f  ->
            let r_env =
              let uu____15741 = FStar_Syntax_Syntax.range_of_fv f in
              FStar_TypeChecker_Env.set_range cfg.tcenv uu____15741 in
            let uu____15742 =
              FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            match uu____15742 with
            | FStar_Pervasives_Native.None  ->
                (log cfg
                   (fun uu____15755  ->
                      FStar_Util.print "Tm_fvar case 2\n" []);
                 rebuild cfg env stack1 t0)
            | FStar_Pervasives_Native.Some (us,t) ->
                (log cfg
                   (fun uu____15766  ->
                      let uu____15767 = FStar_Syntax_Print.term_to_string t0 in
                      let uu____15768 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____15767
                        uu____15768);
                 (let t1 =
                    let uu____15770 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.contains
                           (UnfoldUntil FStar_Syntax_Syntax.Delta_constant)) in
                    if uu____15770
                    then t
                    else
                      FStar_Syntax_Subst.set_use_range
                        (FStar_Ident.range_of_lid
                           (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                        t in
                  let n1 = FStar_List.length us in
                  if n1 > (Prims.parse_int "0")
                  then
                    match stack1 with
                    | (UnivArgs (us',uu____15780))::stack2 ->
                        let env1 =
                          FStar_All.pipe_right us'
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun u  ->
                                    (FStar_Pervasives_Native.None, (Univ u))
                                    :: env1) env) in
                        norm cfg env1 stack2 t1
                    | uu____15835 when
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains EraseUniverses)
                        -> norm cfg env stack1 t1
                    | uu____15838 ->
                        let uu____15841 =
                          let uu____15842 =
                            FStar_Syntax_Print.lid_to_string
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                          FStar_Util.format1
                            "Impossible: missing universe instantiation on %s"
                            uu____15842 in
                        failwith uu____15841
                  else norm cfg env stack1 t1))
and reify_lift:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.monad_name ->
        FStar_Syntax_Syntax.monad_name ->
          FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      fun msrc  ->
        fun mtgt  ->
          fun t  ->
            if FStar_Syntax_Util.is_pure_effect msrc
            then
              let ed = FStar_TypeChecker_Env.get_effect_decl env mtgt in
              let uu____15852 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____15852 with
              | (uu____15853,return_repr) ->
                  let return_inst =
                    let uu____15862 =
                      let uu____15863 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____15863.FStar_Syntax_Syntax.n in
                    match uu____15862 with
                    | FStar_Syntax_Syntax.Tm_uinst
                        (return_tm,uu____15869::[]) ->
                        let uu____15876 =
                          let uu____15879 =
                            let uu____15880 =
                              let uu____15887 =
                                let uu____15890 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____15890] in
                              (return_tm, uu____15887) in
                            FStar_Syntax_Syntax.Tm_uinst uu____15880 in
                          FStar_Syntax_Syntax.mk uu____15879 in
                        uu____15876 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____15898 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____15901 =
                    let uu____15904 =
                      let uu____15905 =
                        let uu____15920 =
                          let uu____15923 = FStar_Syntax_Syntax.as_arg t in
                          let uu____15924 =
                            let uu____15927 = FStar_Syntax_Syntax.as_arg e in
                            [uu____15927] in
                          uu____15923 :: uu____15924 in
                        (return_inst, uu____15920) in
                      FStar_Syntax_Syntax.Tm_app uu____15905 in
                    FStar_Syntax_Syntax.mk uu____15904 in
                  uu____15901 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____15936 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____15936 with
               | FStar_Pervasives_Native.None  ->
                   let uu____15939 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____15939
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____15940;
                     FStar_TypeChecker_Env.mtarget = uu____15941;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____15942;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____15953;
                     FStar_TypeChecker_Env.mtarget = uu____15954;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____15955;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____15973 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____15973)
and norm_pattern_args:
  cfg ->
    env ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list Prims.list ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
          FStar_Pervasives_Native.tuple2 Prims.list Prims.list
  =
  fun cfg  ->
    fun env  ->
      fun args  ->
        FStar_All.pipe_right args
          (FStar_List.map
             (FStar_List.map
                (fun uu____16029  ->
                   match uu____16029 with
                   | (a,imp) ->
                       let uu____16040 = norm cfg env [] a in
                       (uu____16040, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___240_16057 = comp1 in
            let uu____16060 =
              let uu____16061 =
                let uu____16070 = norm cfg env [] t in
                let uu____16071 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16070, uu____16071) in
              FStar_Syntax_Syntax.Total uu____16061 in
            {
              FStar_Syntax_Syntax.n = uu____16060;
              FStar_Syntax_Syntax.pos =
                (uu___240_16057.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___240_16057.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___241_16086 = comp1 in
            let uu____16089 =
              let uu____16090 =
                let uu____16099 = norm cfg env [] t in
                let uu____16100 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16099, uu____16100) in
              FStar_Syntax_Syntax.GTotal uu____16090 in
            {
              FStar_Syntax_Syntax.n = uu____16089;
              FStar_Syntax_Syntax.pos =
                (uu___241_16086.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___241_16086.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____16152  ->
                      match uu____16152 with
                      | (a,i) ->
                          let uu____16163 = norm cfg env [] a in
                          (uu____16163, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___191_16174  ->
                      match uu___191_16174 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____16178 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____16178
                      | f -> f)) in
            let uu___242_16182 = comp1 in
            let uu____16185 =
              let uu____16186 =
                let uu___243_16187 = ct in
                let uu____16188 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____16189 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____16192 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____16188;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___243_16187.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____16189;
                  FStar_Syntax_Syntax.effect_args = uu____16192;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____16186 in
            {
              FStar_Syntax_Syntax.n = uu____16185;
              FStar_Syntax_Syntax.pos =
                (uu___242_16182.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___242_16182.FStar_Syntax_Syntax.vars)
            }
and ghost_to_pure_aux:
  cfg ->
    env ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax
  =
  fun cfg  ->
    fun env  ->
      fun c  ->
        let norm1 t =
          norm
            (let uu___244_16210 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___244_16210.tcenv);
               delta_level = (uu___244_16210.delta_level);
               primitive_steps = (uu___244_16210.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____16215 = norm1 t in
          FStar_Syntax_Util.non_informative uu____16215 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____16218 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___245_16237 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.pos =
                (uu___245_16237.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___245_16237.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____16244 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____16244
            then
              let ct1 =
                match downgrade_ghost_effect_name
                        ct.FStar_Syntax_Syntax.effect_name
                with
                | FStar_Pervasives_Native.Some pure_eff ->
                    let flags =
                      if
                        FStar_Ident.lid_equals pure_eff
                          FStar_Parser_Const.effect_Tot_lid
                      then FStar_Syntax_Syntax.TOTAL ::
                        (ct.FStar_Syntax_Syntax.flags)
                      else ct.FStar_Syntax_Syntax.flags in
                    let uu___246_16255 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___246_16255.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___246_16255.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___246_16255.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags = flags
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___247_16257 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___247_16257.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___247_16257.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___247_16257.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___247_16257.FStar_Syntax_Syntax.flags)
                    } in
              let uu___248_16258 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.pos =
                  (uu___248_16258.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___248_16258.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____16260 -> c
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____16263  ->
        match uu____16263 with
        | (x,imp) ->
            let uu____16266 =
              let uu___249_16267 = x in
              let uu____16268 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___249_16267.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___249_16267.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____16268
              } in
            (uu____16266, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____16274 =
          FStar_List.fold_left
            (fun uu____16292  ->
               fun b  ->
                 match uu____16292 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs in
        match uu____16274 with | (nbs,uu____16332) -> FStar_List.rev nbs
and norm_lcomp_opt:
  cfg ->
    env ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun env  ->
      fun lopt  ->
        match lopt with
        | FStar_Pervasives_Native.Some rc ->
            let flags =
              filter_out_lcomp_cflags rc.FStar_Syntax_Syntax.residual_flags in
            let uu____16348 =
              let uu___250_16349 = rc in
              let uu____16350 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___250_16349.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____16350;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___250_16349.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____16348
        | uu____16357 -> lopt
and rebuild:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun t  ->
          log cfg
            (fun uu____16370  ->
               let uu____16371 = FStar_Syntax_Print.tag_of_term t in
               let uu____16372 = FStar_Syntax_Print.term_to_string t in
               let uu____16373 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____16380 =
                 let uu____16381 =
                   let uu____16384 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____16384 in
                 stack_to_string uu____16381 in
               FStar_Util.print4
                 ">>> %s\\Rebuild %s with %s env elements and top of the stack %s \n"
                 uu____16371 uu____16372 uu____16373 uu____16380);
          (match stack1 with
           | [] -> t
           | (Debug (tm,time_then))::stack2 ->
               ((let uu____16413 =
                   FStar_All.pipe_left
                     (FStar_TypeChecker_Env.debug cfg.tcenv)
                     (FStar_Options.Other "print_normalized_terms") in
                 if uu____16413
                 then
                   let time_now = FStar_Util.now () in
                   let uu____16415 =
                     let uu____16416 =
                       let uu____16417 =
                         FStar_Util.time_diff time_then time_now in
                       FStar_Pervasives_Native.snd uu____16417 in
                     FStar_Util.string_of_int uu____16416 in
                   let uu____16422 = FStar_Syntax_Print.term_to_string tm in
                   let uu____16423 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____16415 uu____16422 uu____16423
                 else ());
                rebuild cfg env stack2 t)
           | (Steps (s,ps,dl))::stack2 ->
               rebuild
                 (let uu___251_16441 = cfg in
                  {
                    steps = s;
                    tcenv = (uu___251_16441.tcenv);
                    delta_level = dl;
                    primitive_steps = ps
                  }) env stack2 t
           | (Meta (m,r))::stack2 ->
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
               rebuild cfg env stack2 t1
           | (MemoLazy r)::stack2 ->
               (set_memo r (env, t);
                log cfg
                  (fun uu____16482  ->
                     let uu____16483 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1 "\tSet memo %s\n" uu____16483);
                rebuild cfg env stack2 t)
           | (Let (env',bs,lb,r))::stack2 ->
               let body = FStar_Syntax_Subst.close bs t in
               let t1 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_let ((false, [lb]), body))
                   FStar_Pervasives_Native.None r in
               rebuild cfg env' stack2 t1
           | (Abs (env',bs,env'',lopt,r))::stack2 ->
               let bs1 = norm_binders cfg env' bs in
               let lopt1 = norm_lcomp_opt cfg env'' lopt in
               let uu____16519 =
                 let uu___252_16520 = FStar_Syntax_Util.abs bs1 t lopt1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___252_16520.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___252_16520.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack2 uu____16519
           | (Arg (Univ uu____16521,uu____16522,uu____16523))::uu____16524 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____16527,uu____16528))::uu____16529 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack2 ->
               let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
               rebuild cfg env stack2 t1
           | (Arg (Clos (env_arg,tm,m,uu____16545),aq,r))::stack2 ->
               (log cfg
                  (fun uu____16598  ->
                     let uu____16599 = FStar_Syntax_Print.term_to_string tm in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____16599);
                if FStar_List.contains (Exclude Iota) cfg.steps
                then
                  (if FStar_List.contains HNF cfg.steps
                   then
                     let arg = closure_as_term cfg env_arg tm in
                     let t1 =
                       FStar_Syntax_Syntax.extend_app t (arg, aq)
                         FStar_Pervasives_Native.None r in
                     rebuild cfg env_arg stack2 t1
                   else
                     (let stack3 = (App (env, t, aq, r)) :: stack2 in
                      norm cfg env_arg stack3 tm))
                else
                  (let uu____16609 = FStar_ST.op_Bang m in
                   match uu____16609 with
                   | FStar_Pervasives_Native.None  ->
                       if FStar_List.contains HNF cfg.steps
                       then
                         let arg = closure_as_term cfg env_arg tm in
                         let t1 =
                           FStar_Syntax_Syntax.extend_app t (arg, aq)
                             FStar_Pervasives_Native.None r in
                         rebuild cfg env_arg stack2 t1
                       else
                         (let stack3 = (MemoLazy m) :: (App (env, t, aq, r))
                            :: stack2 in
                          norm cfg env_arg stack3 tm)
                   | FStar_Pervasives_Native.Some (uu____16753,a) ->
                       let t1 =
                         FStar_Syntax_Syntax.extend_app t (a, aq)
                           FStar_Pervasives_Native.None r in
                       rebuild cfg env_arg stack2 t1))
           | (App (env1,head1,aq,r))::stack2 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r in
               let uu____16796 = maybe_simplify cfg env1 stack2 t1 in
               rebuild cfg env1 stack2 uu____16796
           | (Match (env1,branches,r))::stack2 ->
               (log cfg
                  (fun uu____16808  ->
                     let uu____16809 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____16809);
                (let scrutinee = t in
                 let norm_and_rebuild_match uu____16814 =
                   log cfg
                     (fun uu____16819  ->
                        let uu____16820 =
                          FStar_Syntax_Print.term_to_string scrutinee in
                        let uu____16821 =
                          let uu____16822 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____16839  ->
                                    match uu____16839 with
                                    | (p,uu____16849,uu____16850) ->
                                        FStar_Syntax_Print.pat_to_string p)) in
                          FStar_All.pipe_right uu____16822
                            (FStar_String.concat "\n\t") in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____16820 uu____16821);
                   (let whnf =
                      (FStar_List.contains Weak cfg.steps) ||
                        (FStar_List.contains HNF cfg.steps) in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___192_16867  ->
                                match uu___192_16867 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____16868 -> false)) in
                      let steps' =
                        let uu____16872 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____16872
                        then [Exclude Zeta]
                        else [Exclude Iota; Exclude Zeta] in
                      only_strong_steps
                        (let uu___253_16878 = cfg in
                         {
                           steps = (FStar_List.append steps' cfg.steps);
                           tcenv = (uu___253_16878.tcenv);
                           delta_level = new_delta;
                           primitive_steps = (uu___253_16878.primitive_steps)
                         }) in
                    let norm_or_whnf env2 t1 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t1
                      else norm cfg_exclude_iota_zeta env2 [] t1 in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____16910 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____16931 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____16991  ->
                                    fun uu____16992  ->
                                      match (uu____16991, uu____16992) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____17083 = norm_pat env3 p1 in
                                          (match uu____17083 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2)) in
                          (match uu____16931 with
                           | (pats1,env3) ->
                               ((let uu___254_17165 = p in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___254_17165.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___255_17184 = x in
                            let uu____17185 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___255_17184.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___255_17184.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17185
                            } in
                          ((let uu___256_17199 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___256_17199.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___257_17210 = x in
                            let uu____17211 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___257_17210.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___257_17210.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17211
                            } in
                          ((let uu___258_17225 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___258_17225.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                          let x1 =
                            let uu___259_17241 = x in
                            let uu____17242 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___259_17241.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___259_17241.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17242
                            } in
                          let t2 = norm_or_whnf env2 t1 in
                          ((let uu___260_17249 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                              FStar_Syntax_Syntax.p =
                                (uu___260_17249.FStar_Syntax_Syntax.p)
                            }), env2) in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____17259 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____17273 =
                                    FStar_Syntax_Subst.open_branch branch1 in
                                  match uu____17273 with
                                  | (p,wopt,e) ->
                                      let uu____17293 = norm_pat env1 p in
                                      (match uu____17293 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____17318 =
                                                   norm_or_whnf env2 w in
                                                 FStar_Pervasives_Native.Some
                                                   uu____17318 in
                                           let e1 = norm_or_whnf env2 e in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1)))) in
                    let uu____17324 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r in
                    rebuild cfg env1 stack2 uu____17324) in
                 let rec is_cons head1 =
                   match head1.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____17334) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____17339 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17340;
                         FStar_Syntax_Syntax.fv_delta = uu____17341;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17342;
                         FStar_Syntax_Syntax.fv_delta = uu____17343;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____17344);_}
                       -> true
                   | uu____17351 -> false in
                 let guard_when_clause wopt b rest =
                   match wopt with
                   | FStar_Pervasives_Native.None  -> b
                   | FStar_Pervasives_Native.Some w ->
                       let then_branch = b in
                       let else_branch =
                         mk (FStar_Syntax_Syntax.Tm_match (scrutinee, rest))
                           r in
                       FStar_Syntax_Util.if_then_else w then_branch
                         else_branch in
                 let rec matches_pat scrutinee_orig p =
                   let scrutinee1 = FStar_Syntax_Util.unmeta scrutinee_orig in
                   let uu____17496 =
                     FStar_Syntax_Util.head_and_args scrutinee1 in
                   match uu____17496 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____17583 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when 
                                 s = s' -> FStar_Util.Inl []
                             | uu____17622 ->
                                 let uu____17623 =
                                   let uu____17624 = is_cons head1 in
                                   Prims.op_Negation uu____17624 in
                                 FStar_Util.Inr uu____17623)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____17649 =
                              let uu____17650 =
                                FStar_Syntax_Util.un_uinst head1 in
                              uu____17650.FStar_Syntax_Syntax.n in
                            (match uu____17649 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____17668 ->
                                 let uu____17669 =
                                   let uu____17670 = is_cons head1 in
                                   Prims.op_Negation uu____17670 in
                                 FStar_Util.Inr uu____17669))
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t1,uu____17739)::rest_a,(p1,uu____17742)::rest_p) ->
                       let uu____17786 = matches_pat t1 p1 in
                       (match uu____17786 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____17835 -> FStar_Util.Inr false in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____17941 = matches_pat scrutinee1 p1 in
                       (match uu____17941 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____17981  ->
                                  let uu____17982 =
                                    FStar_Syntax_Print.pat_to_string p1 in
                                  let uu____17983 =
                                    let uu____17984 =
                                      FStar_List.map
                                        (fun uu____17994  ->
                                           match uu____17994 with
                                           | (uu____17999,t1) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t1) s in
                                    FStar_All.pipe_right uu____17984
                                      (FStar_String.concat "; ") in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____17982 uu____17983);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____18030  ->
                                       match uu____18030 with
                                       | (bv,t1) ->
                                           let uu____18053 =
                                             let uu____18060 =
                                               let uu____18063 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv in
                                               FStar_Pervasives_Native.Some
                                                 uu____18063 in
                                             let uu____18064 =
                                               let uu____18065 =
                                                 let uu____18096 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t1)) in
                                                 ([], t1, uu____18096, false) in
                                               Clos uu____18065 in
                                             (uu____18060, uu____18064) in
                                           uu____18053 :: env2) env1 s in
                              let uu____18205 = guard_when_clause wopt b rest in
                              norm cfg env2 stack2 uu____18205))) in
                 let uu____18206 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains (Exclude Iota)) in
                 if uu____18206
                 then norm_and_rebuild_match ()
                 else matches scrutinee branches)))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___193_18229  ->
                match uu___193_18229 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____18233 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____18239 -> d in
      {
        steps = s;
        tcenv = e;
        delta_level = d1;
        primitive_steps = built_in_primitive_steps
      }
let normalize_with_primitive_steps:
  primitive_step Prims.list ->
    step Prims.list ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun ps  ->
    fun s  ->
      fun e  ->
        fun t  ->
          let c = config s e in
          let c1 =
            let uu___261_18268 = config s e in
            {
              steps = (uu___261_18268.steps);
              tcenv = (uu___261_18268.tcenv);
              delta_level = (uu___261_18268.delta_level);
              primitive_steps = (FStar_List.append c.primitive_steps ps)
            } in
          norm c1 [] [] t
let normalize:
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun s  -> fun e  -> fun t  -> normalize_with_primitive_steps [] s e t
let normalize_comp:
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun s  ->
    fun e  ->
      fun t  -> let uu____18299 = config s e in norm_comp uu____18299 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____18314 = config [] env in norm_universe uu____18314 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  ->
      let uu____18329 = config [] env in ghost_to_pure_aux uu____18329 [] c
let ghost_to_pure_lcomp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun lc  ->
      let cfg =
        config
          [Eager_unfolding;
          UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
          EraseUniverses;
          AllowUnboundUniverses] env in
      let non_info t =
        let uu____18349 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____18349 in
      let uu____18356 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____18356
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___262_18358 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___262_18358.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___262_18358.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____18361  ->
                    let uu____18362 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____18362))
            }
        | FStar_Pervasives_Native.None  -> lc
      else lc
let term_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun env  ->
    fun t  ->
      let t1 =
        try normalize [AllowUnboundUniverses] env t
        with
        | e ->
            ((let uu____18381 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning
                "Normalization failed with error %s\n" uu____18381);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____18394 = config [AllowUnboundUniverses] env in
          norm_comp uu____18394 [] c
        with
        | e ->
            ((let uu____18407 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning
                "Normalization failed with error %s\n" uu____18407);
             c) in
      FStar_Syntax_Print.comp_to_string c1
let normalize_refinement:
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun steps  ->
    fun env  ->
      fun t0  ->
        let t = normalize (FStar_List.append steps [Beta]) env t0 in
        let rec aux t1 =
          let t2 = FStar_Syntax_Subst.compress t1 in
          match t2.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
              let t01 = aux x.FStar_Syntax_Syntax.sort in
              (match t01.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_refine (y,phi1) ->
                   let uu____18447 =
                     let uu____18448 =
                       let uu____18455 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____18455) in
                     FStar_Syntax_Syntax.Tm_refine uu____18448 in
                   mk uu____18447 t01.FStar_Syntax_Syntax.pos
               | uu____18460 -> t2)
          | uu____18461 -> t2 in
        aux t
let unfold_whnf:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      normalize
        [Weak; HNF; UnfoldUntil FStar_Syntax_Syntax.Delta_constant; Beta] env
        t
let reduce_or_remove_uvar_solutions:
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun remove  ->
    fun env  ->
      fun t  ->
        normalize
          (FStar_List.append (if remove then [CheckNoUvars] else [])
             [Beta;
             NoDeltaSteps;
             CompressUvars;
             Exclude Zeta;
             Exclude Iota;
             NoFullNorm]) env t
let reduce_uvar_solutions:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun env  -> fun t  -> reduce_or_remove_uvar_solutions false env t
let remove_uvar_solutions:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun env  -> fun t  -> reduce_or_remove_uvar_solutions true env t
let eta_expand_with_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      fun t_e  ->
        let uu____18513 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____18513 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____18542 ->
                 let uu____18549 = FStar_Syntax_Util.abs_formals e in
                 (match uu____18549 with
                  | (actuals,uu____18559,uu____18560) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____18574 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____18574 with
                         | (binders,args) ->
                             let uu____18591 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____18591
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c)))))
let eta_expand:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_name x ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____18601 ->
          let uu____18602 = FStar_Syntax_Util.head_and_args t in
          (match uu____18602 with
           | (head1,args) ->
               let uu____18639 =
                 let uu____18640 = FStar_Syntax_Subst.compress head1 in
                 uu____18640.FStar_Syntax_Syntax.n in
               (match uu____18639 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____18643,thead) ->
                    let uu____18669 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____18669 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____18711 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___267_18719 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___267_18719.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___267_18719.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___267_18719.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___267_18719.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___267_18719.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___267_18719.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___267_18719.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___267_18719.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___267_18719.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___267_18719.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___267_18719.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___267_18719.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___267_18719.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___267_18719.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___267_18719.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___267_18719.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___267_18719.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___267_18719.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___267_18719.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___267_18719.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___267_18719.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___267_18719.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___267_18719.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___267_18719.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___267_18719.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___267_18719.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___267_18719.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___267_18719.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___267_18719.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___267_18719.FStar_TypeChecker_Env.dsenv)
                                 }) t in
                            match uu____18711 with
                            | (uu____18720,ty,uu____18722) ->
                                eta_expand_with_type env t ty))
                | uu____18723 ->
                    let uu____18724 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___268_18732 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___268_18732.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___268_18732.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___268_18732.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___268_18732.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___268_18732.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___268_18732.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___268_18732.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___268_18732.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___268_18732.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___268_18732.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___268_18732.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___268_18732.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___268_18732.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___268_18732.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___268_18732.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___268_18732.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___268_18732.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___268_18732.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___268_18732.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___268_18732.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___268_18732.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___268_18732.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___268_18732.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___268_18732.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___268_18732.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___268_18732.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___268_18732.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___268_18732.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___268_18732.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___268_18732.FStar_TypeChecker_Env.dsenv)
                         }) t in
                    (match uu____18724 with
                     | (uu____18733,ty,uu____18735) ->
                         eta_expand_with_type env t ty)))
let elim_uvars_aux_tc:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.comp) FStar_Util.either
          ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,(FStar_Syntax_Syntax.term,
                                                         FStar_Syntax_Syntax.comp'
                                                           FStar_Syntax_Syntax.syntax)
                                                         FStar_Util.either)
            FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun tc  ->
          let t =
            match (binders, tc) with
            | ([],FStar_Util.Inl t) -> t
            | ([],FStar_Util.Inr c) ->
                failwith "Impossible: empty bindes with a comp"
            | (uu____18813,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____18819,FStar_Util.Inl t) ->
                let uu____18825 =
                  let uu____18828 =
                    let uu____18829 =
                      let uu____18842 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____18842) in
                    FStar_Syntax_Syntax.Tm_arrow uu____18829 in
                  FStar_Syntax_Syntax.mk uu____18828 in
                uu____18825 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____18846 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____18846 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____18873 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____18928 ->
                    let uu____18929 =
                      let uu____18938 =
                        let uu____18939 = FStar_Syntax_Subst.compress t3 in
                        uu____18939.FStar_Syntax_Syntax.n in
                      (uu____18938, tc) in
                    (match uu____18929 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____18964) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____19001) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____19040,FStar_Util.Inl uu____19041) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____19064 -> failwith "Impossible") in
              (match uu____18873 with
               | (binders1,tc1) -> (univ_names1, binders1, tc1))
let elim_uvars_aux_t:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun t  ->
          let uu____19173 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____19173 with
          | (univ_names1,binders1,tc) ->
              let uu____19231 = FStar_Util.left tc in
              (univ_names1, binders1, uu____19231)
let elim_uvars_aux_c:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,FStar_Syntax_Syntax.comp'
                                                         FStar_Syntax_Syntax.syntax)
            FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun c  ->
          let uu____19270 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____19270 with
          | (univ_names1,binders1,tc) ->
              let uu____19330 = FStar_Util.right tc in
              (univ_names1, binders1, uu____19330)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____19365 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____19365 with
           | (univ_names1,binders1,typ1) ->
               let uu___269_19393 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___269_19393.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___269_19393.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___269_19393.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___269_19393.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___270_19414 = s in
          let uu____19415 =
            let uu____19416 =
              let uu____19425 = FStar_List.map (elim_uvars env) sigs in
              (uu____19425, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____19416 in
          {
            FStar_Syntax_Syntax.sigel = uu____19415;
            FStar_Syntax_Syntax.sigrng =
              (uu___270_19414.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___270_19414.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___270_19414.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___270_19414.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____19442 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____19442 with
           | (univ_names1,uu____19460,typ1) ->
               let uu___271_19474 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___271_19474.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___271_19474.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___271_19474.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___271_19474.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____19480 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____19480 with
           | (univ_names1,uu____19498,typ1) ->
               let uu___272_19512 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___272_19512.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___272_19512.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___272_19512.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___272_19512.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____19546 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____19546 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____19569 =
                            let uu____19570 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____19570 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____19569 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___273_19573 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___273_19573.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___273_19573.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___274_19574 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___274_19574.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___274_19574.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___274_19574.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___274_19574.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___275_19586 = s in
          let uu____19587 =
            let uu____19588 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____19588 in
          {
            FStar_Syntax_Syntax.sigel = uu____19587;
            FStar_Syntax_Syntax.sigrng =
              (uu___275_19586.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___275_19586.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___275_19586.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___275_19586.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____19592 = elim_uvars_aux_t env us [] t in
          (match uu____19592 with
           | (us1,uu____19610,t1) ->
               let uu___276_19624 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___276_19624.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___276_19624.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___276_19624.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___276_19624.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____19625 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____19627 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____19627 with
           | (univs1,binders,signature) ->
               let uu____19655 =
                 let uu____19664 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____19664 with
                 | (univs_opening,univs2) ->
                     let uu____19691 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____19691) in
               (match uu____19655 with
                | (univs_opening,univs_closing) ->
                    let uu____19708 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____19714 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____19715 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____19714, uu____19715) in
                    (match uu____19708 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____19737 =
                           match uu____19737 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____19755 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____19755 with
                                | (us1,t1) ->
                                    let uu____19766 =
                                      let uu____19771 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____19778 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____19771, uu____19778) in
                                    (match uu____19766 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____19791 =
                                           let uu____19796 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____19805 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____19796, uu____19805) in
                                         (match uu____19791 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____19821 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____19821 in
                                              let uu____19822 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____19822 with
                                               | (uu____19843,uu____19844,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____19859 =
                                                       let uu____19860 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____19860 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____19859 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____19865 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____19865 with
                           | (uu____19878,uu____19879,t1) -> t1 in
                         let elim_action a =
                           let action_typ_templ =
                             let body =
                               FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_ascribed
                                    ((a.FStar_Syntax_Syntax.action_defn),
                                      ((FStar_Util.Inl
                                          (a.FStar_Syntax_Syntax.action_typ)),
                                        FStar_Pervasives_Native.None),
                                      FStar_Pervasives_Native.None))
                                 FStar_Pervasives_Native.None
                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                             match a.FStar_Syntax_Syntax.action_params with
                             | [] -> body
                             | uu____19939 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____19956 =
                               let uu____19957 =
                                 FStar_Syntax_Subst.compress body in
                               uu____19957.FStar_Syntax_Syntax.n in
                             match uu____19956 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____20016 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____20045 =
                               let uu____20046 =
                                 FStar_Syntax_Subst.compress t in
                               uu____20046.FStar_Syntax_Syntax.n in
                             match uu____20045 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____20067) ->
                                 let uu____20088 = destruct_action_body body in
                                 (match uu____20088 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____20133 ->
                                 let uu____20134 = destruct_action_body t in
                                 (match uu____20134 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____20183 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____20183 with
                           | (action_univs,t) ->
                               let uu____20192 = destruct_action_typ_templ t in
                               (match uu____20192 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___277_20233 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___277_20233.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___277_20233.FStar_Syntax_Syntax.action_unqualified_name);
                                        FStar_Syntax_Syntax.action_univs =
                                          action_univs;
                                        FStar_Syntax_Syntax.action_params =
                                          action_params;
                                        FStar_Syntax_Syntax.action_defn =
                                          action_defn;
                                        FStar_Syntax_Syntax.action_typ =
                                          action_typ
                                      } in
                                    a') in
                         let ed1 =
                           let uu___278_20235 = ed in
                           let uu____20236 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____20237 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____20238 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____20239 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____20240 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____20241 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____20242 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____20243 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____20244 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____20245 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____20246 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____20247 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____20248 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____20249 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___278_20235.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___278_20235.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____20236;
                             FStar_Syntax_Syntax.bind_wp = uu____20237;
                             FStar_Syntax_Syntax.if_then_else = uu____20238;
                             FStar_Syntax_Syntax.ite_wp = uu____20239;
                             FStar_Syntax_Syntax.stronger = uu____20240;
                             FStar_Syntax_Syntax.close_wp = uu____20241;
                             FStar_Syntax_Syntax.assert_p = uu____20242;
                             FStar_Syntax_Syntax.assume_p = uu____20243;
                             FStar_Syntax_Syntax.null_wp = uu____20244;
                             FStar_Syntax_Syntax.trivial = uu____20245;
                             FStar_Syntax_Syntax.repr = uu____20246;
                             FStar_Syntax_Syntax.return_repr = uu____20247;
                             FStar_Syntax_Syntax.bind_repr = uu____20248;
                             FStar_Syntax_Syntax.actions = uu____20249
                           } in
                         let uu___279_20252 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___279_20252.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___279_20252.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___279_20252.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___279_20252.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___194_20269 =
            match uu___194_20269 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____20296 = elim_uvars_aux_t env us [] t in
                (match uu____20296 with
                 | (us1,uu____20320,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___280_20339 = sub_eff in
            let uu____20340 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____20343 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___280_20339.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___280_20339.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____20340;
              FStar_Syntax_Syntax.lift = uu____20343
            } in
          let uu___281_20346 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___281_20346.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___281_20346.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___281_20346.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___281_20346.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____20356 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____20356 with
           | (univ_names1,binders1,comp1) ->
               let uu___282_20390 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___282_20390.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___282_20390.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___282_20390.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___282_20390.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____20401 -> s