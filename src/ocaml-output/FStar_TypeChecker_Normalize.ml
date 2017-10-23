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
  primitive_steps: primitive_step Prims.list;
  strong: Prims.bool;}[@@deriving show]
let __proj__Mkcfg__item__steps: cfg -> steps =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps;
        strong = __fname__strong;_} -> __fname__steps
let __proj__Mkcfg__item__tcenv: cfg -> FStar_TypeChecker_Env.env =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps;
        strong = __fname__strong;_} -> __fname__tcenv
let __proj__Mkcfg__item__delta_level:
  cfg -> FStar_TypeChecker_Env.delta_level Prims.list =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps;
        strong = __fname__strong;_} -> __fname__delta_level
let __proj__Mkcfg__item__primitive_steps: cfg -> primitive_step Prims.list =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps;
        strong = __fname__strong;_} -> __fname__primitive_steps
let __proj__Mkcfg__item__strong: cfg -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps;
        strong = __fname__strong;_} -> __fname__strong
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
    match projectee with | Arg _0 -> true | uu____831 -> false
let __proj__Arg__item___0:
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Arg _0 -> _0
let uu___is_UnivArgs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____869 -> false
let __proj__UnivArgs__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0
let uu___is_MemoLazy: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____907 -> false
let __proj__MemoLazy__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0
let uu___is_Match: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____966 -> false
let __proj__Match__item___0:
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Abs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____1010 -> false
let __proj__Abs__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Abs _0 -> _0
let uu___is_App: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____1068 -> false
let __proj__App__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Meta: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____1110 -> false
let __proj__Meta__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Meta _0 -> _0
let uu___is_Let: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____1144 -> false
let __proj__Let__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Steps: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Steps _0 -> true | uu____1192 -> false
let __proj__Steps__item___0:
  stack_elt ->
    (steps,primitive_step Prims.list,FStar_TypeChecker_Env.delta_level
                                       Prims.list)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Steps _0 -> _0
let uu___is_Debug: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____1240 -> false
let __proj__Debug__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list[@@deriving show]
let mk:
  'Auu____1269 .
    'Auu____1269 ->
      FStar_Range.range -> 'Auu____1269 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r
let set_memo: 'a . 'a FStar_Syntax_Syntax.memo -> 'a -> Prims.unit =
  fun r  ->
    fun t  ->
      let uu____1320 = FStar_ST.op_Bang r in
      match uu____1320 with
      | FStar_Pervasives_Native.Some uu____1387 ->
          failwith "Unexpected set_memo: thunk already evaluated"
      | FStar_Pervasives_Native.None  ->
          FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____1460 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____1460 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___179_1468  ->
    match uu___179_1468 with
    | Arg (c,uu____1470,uu____1471) ->
        let uu____1472 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____1472
    | MemoLazy uu____1473 -> "MemoLazy"
    | Abs (uu____1480,bs,uu____1482,uu____1483,uu____1484) ->
        let uu____1489 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____1489
    | UnivArgs uu____1494 -> "UnivArgs"
    | Match uu____1501 -> "Match"
    | App (uu____1508,t,uu____1510,uu____1511) ->
        let uu____1512 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____1512
    | Meta (m,uu____1514) -> "Meta"
    | Let uu____1515 -> "Let"
    | Steps (uu____1524,uu____1525,uu____1526) -> "Steps"
    | Debug (t,uu____1536) ->
        let uu____1537 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____1537
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____1546 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____1546 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1564 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____1564 then f () else ()
let log_primops: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1579 =
        (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm"))
          ||
          (FStar_TypeChecker_Env.debug cfg.tcenv
             (FStar_Options.Other "Primops")) in
      if uu____1579 then f () else ()
let is_empty: 'Auu____1585 . 'Auu____1585 Prims.list -> Prims.bool =
  fun uu___180_1591  ->
    match uu___180_1591 with | [] -> true | uu____1594 -> false
let lookup_bvar:
  'Auu____1605 'Auu____1606 .
    ('Auu____1606,'Auu____1605) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____1605
  =
  fun env  ->
    fun x  ->
      try
        let uu____1630 = FStar_List.nth env x.FStar_Syntax_Syntax.index in
        FStar_Pervasives_Native.snd uu____1630
      with
      | uu____1643 ->
          let uu____1644 =
            let uu____1645 = FStar_Syntax_Print.db_to_string x in
            FStar_Util.format1 "Failed to find %s\n" uu____1645 in
          failwith uu____1644
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
          let uu____1686 =
            FStar_List.fold_left
              (fun uu____1712  ->
                 fun u1  ->
                   match uu____1712 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____1737 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____1737 with
                        | (k_u,n1) ->
                            let uu____1752 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____1752
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____1686 with
          | (uu____1770,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____1795 =
                   let uu____1796 = FStar_List.nth env x in
                   FStar_Pervasives_Native.snd uu____1796 in
                 match uu____1795 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____1814 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____1823 ->
                   let uu____1824 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____1824
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____1830 when
              FStar_All.pipe_right cfg.steps
                (FStar_List.contains CheckNoUvars)
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____1839 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____1848 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____1855 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____1855 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____1872 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____1872 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____1880 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____1888 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____1888 with
                                  | (uu____1893,m) -> n1 <= m)) in
                        if uu____1880 then rest1 else us1
                    | uu____1898 -> us1)
               | uu____1903 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1907 = aux u3 in
              FStar_List.map (fun _0_42  -> FStar_Syntax_Syntax.U_succ _0_42)
                uu____1907 in
        let uu____1910 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____1910
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1912 = aux u in
           match uu____1912 with
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
          (fun uu____2016  ->
             let uu____2017 = FStar_Syntax_Print.tag_of_term t in
             let uu____2018 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____2017
               uu____2018);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____2025 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____2027 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____2052 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____2053 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____2054 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____2055 ->
                  let uu____2072 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains CheckNoUvars) in
                  if uu____2072
                  then
                    let uu____2073 =
                      let uu____2074 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos in
                      let uu____2075 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____2074 uu____2075 in
                    failwith uu____2073
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____2078 =
                    let uu____2079 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____2079 in
                  mk uu____2078 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____2086 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____2086
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____2088 = lookup_bvar env x in
                  (match uu____2088 with
                   | Univ uu____2091 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____2095) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____2207 = closures_as_binders_delayed cfg env bs in
                  (match uu____2207 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____2235 =
                         let uu____2236 =
                           let uu____2253 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____2253) in
                         FStar_Syntax_Syntax.Tm_abs uu____2236 in
                       mk uu____2235 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____2284 = closures_as_binders_delayed cfg env bs in
                  (match uu____2284 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____2326 =
                    let uu____2337 =
                      let uu____2344 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____2344] in
                    closures_as_binders_delayed cfg env uu____2337 in
                  (match uu____2326 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____2362 =
                         let uu____2363 =
                           let uu____2370 =
                             let uu____2371 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____2371
                               FStar_Pervasives_Native.fst in
                           (uu____2370, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____2363 in
                       mk uu____2362 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____2462 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____2462
                    | FStar_Util.Inr c ->
                        let uu____2476 = close_comp cfg env c in
                        FStar_Util.Inr uu____2476 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____2492 =
                    let uu____2493 =
                      let uu____2520 = closure_as_term_delayed cfg env t11 in
                      (uu____2520, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____2493 in
                  mk uu____2492 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____2571 =
                    let uu____2572 =
                      let uu____2579 = closure_as_term_delayed cfg env t' in
                      let uu____2582 =
                        let uu____2583 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____2583 in
                      (uu____2579, uu____2582) in
                    FStar_Syntax_Syntax.Tm_meta uu____2572 in
                  mk uu____2571 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____2643 =
                    let uu____2644 =
                      let uu____2651 = closure_as_term_delayed cfg env t' in
                      let uu____2654 =
                        let uu____2655 =
                          let uu____2662 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____2662) in
                        FStar_Syntax_Syntax.Meta_monadic uu____2655 in
                      (uu____2651, uu____2654) in
                    FStar_Syntax_Syntax.Tm_meta uu____2644 in
                  mk uu____2643 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____2681 =
                    let uu____2682 =
                      let uu____2689 = closure_as_term_delayed cfg env t' in
                      let uu____2692 =
                        let uu____2693 =
                          let uu____2702 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____2702) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____2693 in
                      (uu____2689, uu____2692) in
                    FStar_Syntax_Syntax.Tm_meta uu____2682 in
                  mk uu____2681 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____2715 =
                    let uu____2716 =
                      let uu____2723 = closure_as_term_delayed cfg env t' in
                      (uu____2723, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____2716 in
                  mk uu____2715 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____2763  -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let uu____2782 =
                    let uu____2793 = FStar_Syntax_Syntax.is_top_level [lb] in
                    if uu____2793
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       let uu____2812 =
                         closure_as_term cfg (dummy :: env0) body in
                       ((FStar_Util.Inl
                           (let uu___199_2824 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___199_2824.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___199_2824.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____2812)) in
                  (match uu____2782 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___200_2840 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___200_2840.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___200_2840.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def
                         } in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____2851,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____2910  -> fun env2  -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____2935 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2935
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____2955  -> fun env2  -> dummy :: env2) lbs
                          env_univs in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let nm =
                      let uu____2977 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2977
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                         FStar_All.pipe_right
                           (let uu___201_2989 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___201_2989.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___201_2989.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_43  -> FStar_Util.Inl _0_43)) in
                    let uu___202_2990 = lb in
                    let uu____2991 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___202_2990.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___202_2990.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____2991
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____3021  -> fun env1  -> dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____3110 =
                    match uu____3110 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____3165 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____3186 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____3246  ->
                                        fun uu____3247  ->
                                          match (uu____3246, uu____3247) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____3338 =
                                                norm_pat env3 p1 in
                                              (match uu____3338 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____3186 with
                               | (pats1,env3) ->
                                   ((let uu___203_3420 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___203_3420.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___204_3439 = x in
                                let uu____3440 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___204_3439.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___204_3439.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3440
                                } in
                              ((let uu___205_3454 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___205_3454.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___206_3465 = x in
                                let uu____3466 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___206_3465.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___206_3465.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3466
                                } in
                              ((let uu___207_3480 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___207_3480.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___208_3496 = x in
                                let uu____3497 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___208_3496.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___208_3496.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3497
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___209_3504 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___209_3504.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____3507 = norm_pat env1 pat in
                        (match uu____3507 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3536 =
                                     closure_as_term cfg env2 w in
                                   FStar_Pervasives_Native.Some uu____3536 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____3542 =
                    let uu____3543 =
                      let uu____3566 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____3566) in
                    FStar_Syntax_Syntax.Tm_match uu____3543 in
                  mk uu____3542 t1.FStar_Syntax_Syntax.pos))
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
        | uu____3652 -> closure_as_term cfg env t
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
        | uu____3678 ->
            FStar_List.map
              (fun uu____3695  ->
                 match uu____3695 with
                 | (x,imp) ->
                     let uu____3714 = closure_as_term_delayed cfg env x in
                     (uu____3714, imp)) args
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
        let uu____3728 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____3777  ->
                  fun uu____3778  ->
                    match (uu____3777, uu____3778) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___210_3848 = b in
                          let uu____3849 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___210_3848.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___210_3848.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____3849
                          } in
                        let env2 = dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____3728 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____3942 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____3955 = closure_as_term_delayed cfg env t in
                 let uu____3956 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____3955 uu____3956
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____3969 = closure_as_term_delayed cfg env t in
                 let uu____3970 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____3969 uu____3970
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
                        (fun uu___181_3996  ->
                           match uu___181_3996 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____4000 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____4000
                           | f -> f)) in
                 let uu____4004 =
                   let uu___211_4005 = c1 in
                   let uu____4006 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____4006;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___211_4005.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____4004)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags  ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___182_4016  ->
            match uu___182_4016 with
            | FStar_Syntax_Syntax.DECREASES uu____4017 -> false
            | uu____4020 -> true))
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
                   (fun uu___183_4038  ->
                      match uu___183_4038 with
                      | FStar_Syntax_Syntax.DECREASES uu____4039 -> false
                      | uu____4042 -> true)) in
            let rc1 =
              let uu___212_4044 = rc in
              let uu____4045 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___212_4044.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____4045;
                FStar_Syntax_Syntax.residual_flags = flags
              } in
            FStar_Pervasives_Native.Some rc1
        | uu____4052 -> lopt
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
    let uu____4140 = FStar_Syntax_Embeddings.unembed_list_safe u in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____4140 in
  let arg_as_bounded_int uu____4168 =
    match uu____4168 with
    | (a,uu____4180) ->
        let uu____4187 =
          let uu____4188 = FStar_Syntax_Subst.compress a in
          uu____4188.FStar_Syntax_Syntax.n in
        (match uu____4187 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____4198;
                FStar_Syntax_Syntax.vars = uu____4199;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____4201;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____4202;_},uu____4203)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____4242 =
               let uu____4247 = FStar_Util.int_of_string i in
               (fv1, uu____4247) in
             FStar_Pervasives_Native.Some uu____4242
         | uu____4252 -> FStar_Pervasives_Native.None) in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4294 = f a in FStar_Pervasives_Native.Some uu____4294
    | uu____4295 -> FStar_Pervasives_Native.None in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4345 = f a0 a1 in FStar_Pervasives_Native.Some uu____4345
    | uu____4346 -> FStar_Pervasives_Native.None in
  let unary_op as_a f res args =
    let uu____4395 = FStar_List.map as_a args in
    lift_unary (f res.psc_range) uu____4395 in
  let binary_op as_a f res args =
    let uu____4451 = FStar_List.map as_a args in
    lift_binary (f res.psc_range) uu____4451 in
  let as_primitive_step uu____4475 =
    match uu____4475 with
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
           let uu____4523 = f x in
           FStar_Syntax_Embeddings.embed_int r uu____4523) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4551 = f x y in
             FStar_Syntax_Embeddings.embed_int r uu____4551) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  ->
           let uu____4572 = f x in
           FStar_Syntax_Embeddings.embed_bool r uu____4572) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4600 = f x y in
             FStar_Syntax_Embeddings.embed_bool r uu____4600) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4628 = f x y in
             FStar_Syntax_Embeddings.embed_string r uu____4628) in
  let list_of_string' rng s =
    let name l =
      let uu____4642 =
        let uu____4643 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____4643 in
      mk uu____4642 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____4653 =
      let uu____4656 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____4656 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____4653 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in
    FStar_Syntax_Embeddings.embed_int rng r in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____4703 = arg_as_string a1 in
        (match uu____4703 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4709 =
               arg_as_list FStar_Syntax_Embeddings.unembed_string_safe a2 in
             (match uu____4709 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____4722 =
                    FStar_Syntax_Embeddings.embed_string psc.psc_range r in
                  FStar_Pervasives_Native.Some uu____4722
              | uu____4723 -> FStar_Pervasives_Native.None)
         | uu____4728 -> FStar_Pervasives_Native.None)
    | uu____4731 -> FStar_Pervasives_Native.None in
  let string_of_int1 rng i =
    let uu____4741 = FStar_Util.string_of_int i in
    FStar_Syntax_Embeddings.embed_string rng uu____4741 in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false") in
  let string_of_int2 rng i =
    let uu____4757 = FStar_Util.string_of_int i in
    FStar_Syntax_Embeddings.embed_string rng uu____4757 in
  let string_of_bool2 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false") in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r in
  let mk_range1 uu____4781 args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____4792 =
          let uu____4813 = arg_as_string fn in
          let uu____4816 = arg_as_int from_line in
          let uu____4819 = arg_as_int from_col in
          let uu____4822 = arg_as_int to_line in
          let uu____4825 = arg_as_int to_col in
          (uu____4813, uu____4816, uu____4819, uu____4822, uu____4825) in
        (match uu____4792 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____4856 = FStar_Range.mk_pos from_l from_c in
               let uu____4857 = FStar_Range.mk_pos to_l to_c in
               FStar_Range.mk_range fn1 uu____4856 uu____4857 in
             let uu____4858 = term_of_range r in
             FStar_Pervasives_Native.Some uu____4858
         | uu____4863 -> FStar_Pervasives_Native.None)
    | uu____4884 -> FStar_Pervasives_Native.None in
  let decidable_eq neg psc args =
    let r = psc.psc_range in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r in
    match args with
    | (_typ,uu____4911)::(a1,uu____4913)::(a2,uu____4915)::[] ->
        let uu____4952 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____4952 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____4965 -> FStar_Pervasives_Native.None)
    | uu____4966 -> failwith "Unexpected number of arguments" in
  let idstep psc args =
    match args with
    | (a1,uu____4993)::[] -> FStar_Pervasives_Native.Some a1
    | uu____5002 -> failwith "Unexpected number of arguments" in
  let basic_ops =
    let uu____5026 =
      let uu____5041 =
        let uu____5056 =
          let uu____5071 =
            let uu____5086 =
              let uu____5101 =
                let uu____5116 =
                  let uu____5131 =
                    let uu____5146 =
                      let uu____5161 =
                        let uu____5176 =
                          let uu____5191 =
                            let uu____5206 =
                              let uu____5221 =
                                let uu____5236 =
                                  let uu____5251 =
                                    let uu____5266 =
                                      let uu____5281 =
                                        let uu____5296 =
                                          let uu____5311 =
                                            let uu____5326 =
                                              let uu____5339 =
                                                FStar_Parser_Const.p2l
                                                  ["FStar";
                                                  "String";
                                                  "list_of_string"] in
                                              (uu____5339,
                                                (Prims.parse_int "1"),
                                                (unary_op arg_as_string
                                                   list_of_string')) in
                                            let uu____5346 =
                                              let uu____5361 =
                                                let uu____5374 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "string_of_list"] in
                                                (uu____5374,
                                                  (Prims.parse_int "1"),
                                                  (unary_op
                                                     (arg_as_list
                                                        FStar_Syntax_Embeddings.unembed_char_safe)
                                                     string_of_list')) in
                                              let uu____5383 =
                                                let uu____5398 =
                                                  let uu____5413 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "concat"] in
                                                  (uu____5413,
                                                    (Prims.parse_int "2"),
                                                    string_concat') in
                                                let uu____5422 =
                                                  let uu____5439 =
                                                    let uu____5454 =
                                                      FStar_Parser_Const.p2l
                                                        ["Prims"; "mk_range"] in
                                                    (uu____5454,
                                                      (Prims.parse_int "5"),
                                                      mk_range1) in
                                                  let uu____5463 =
                                                    let uu____5480 =
                                                      let uu____5499 =
                                                        FStar_Parser_Const.p2l
                                                          ["FStar";
                                                          "Range";
                                                          "prims_to_fstar_range"] in
                                                      (uu____5499,
                                                        (Prims.parse_int "1"),
                                                        idstep) in
                                                    [uu____5480] in
                                                  uu____5439 :: uu____5463 in
                                                uu____5398 :: uu____5422 in
                                              uu____5361 :: uu____5383 in
                                            uu____5326 :: uu____5346 in
                                          (FStar_Parser_Const.op_notEq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq true)) ::
                                            uu____5311 in
                                        (FStar_Parser_Const.op_Eq,
                                          (Prims.parse_int "3"),
                                          (decidable_eq false)) :: uu____5296 in
                                      (FStar_Parser_Const.string_compare,
                                        (Prims.parse_int "2"),
                                        (binary_op arg_as_string
                                           string_compare'))
                                        :: uu____5281 in
                                    (FStar_Parser_Const.string_of_bool_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_bool string_of_bool2))
                                      :: uu____5266 in
                                  (FStar_Parser_Const.string_of_int_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_int string_of_int2)) ::
                                    uu____5251 in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____5236 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____5221 in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____5206 in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____5191 in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____5176 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____5161 in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                FStar_Syntax_Embeddings.embed_bool r (x >= y))))
                      :: uu____5146 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              FStar_Syntax_Embeddings.embed_bool r (x > y))))
                    :: uu____5131 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            FStar_Syntax_Embeddings.embed_bool r (x <= y))))
                  :: uu____5116 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          FStar_Syntax_Embeddings.embed_bool r (x < y))))
                :: uu____5101 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____5086 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____5071 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____5056 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____5041 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____5026 in
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
      let uu____6076 =
        let uu____6077 =
          let uu____6078 = FStar_Syntax_Syntax.as_arg c in [uu____6078] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____6077 in
      uu____6076 FStar_Pervasives_Native.None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____6113 =
              let uu____6126 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
              (uu____6126, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____6145  ->
                        fun uu____6146  ->
                          match (uu____6145, uu____6146) with
                          | ((int_to_t1,x),(uu____6165,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____6175 =
              let uu____6190 =
                let uu____6203 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                (uu____6203, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____6222  ->
                          fun uu____6223  ->
                            match (uu____6222, uu____6223) with
                            | ((int_to_t1,x),(uu____6242,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____6252 =
                let uu____6267 =
                  let uu____6280 = FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                  (uu____6280, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____6299  ->
                            fun uu____6300  ->
                              match (uu____6299, uu____6300) with
                              | ((int_to_t1,x),(uu____6319,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____6267] in
              uu____6190 :: uu____6252 in
            uu____6113 :: uu____6175)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop psc args =
    let r = psc.psc_range in
    match args with
    | (_typ,uu____6418)::(a1,uu____6420)::(a2,uu____6422)::[] ->
        let uu____6459 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6459 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___213_6465 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___213_6465.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___213_6465.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___214_6469 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___214_6469.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___214_6469.FStar_Syntax_Syntax.vars)
                })
         | uu____6470 -> FStar_Pervasives_Native.None)
    | (_typ,uu____6472)::uu____6473::(a1,uu____6475)::(a2,uu____6477)::[] ->
        let uu____6526 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6526 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___213_6532 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___213_6532.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___213_6532.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___214_6536 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___214_6536.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___214_6536.FStar_Syntax_Syntax.vars)
                })
         | uu____6537 -> FStar_Pervasives_Native.None)
    | uu____6538 -> failwith "Unexpected number of arguments" in
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
      let uu____6558 =
        let uu____6559 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____6559 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____6558
    with | uu____6565 -> FStar_Pervasives_Native.None
let mk_psc_subst:
  'Auu____6572 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6572) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____6632  ->
           fun subst1  ->
             match uu____6632 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,memo,uu____6674)) ->
                      let uu____6733 = b in
                      (match uu____6733 with
                       | (bv,uu____6741) ->
                           let uu____6742 =
                             let uu____6743 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.fstar_reflection_types_binder_lid in
                             Prims.op_Negation uu____6743 in
                           if uu____6742
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term in
                              let uu____6748 = unembed_binder term1 in
                              match uu____6748 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____6755 =
                                      let uu___217_6756 = bv in
                                      let uu____6757 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___217_6756.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___217_6756.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____6757
                                      } in
                                    FStar_Syntax_Syntax.freshen_bv uu____6755 in
                                  let b_for_x =
                                    let uu____6761 =
                                      let uu____6768 =
                                        FStar_Syntax_Syntax.bv_to_name b1 in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____6768) in
                                    FStar_Syntax_Syntax.NT uu____6761 in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___184_6777  ->
                                         match uu___184_6777 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____6778,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____6780;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____6781;_})
                                             ->
                                             Prims.op_Negation
                                               (FStar_Ident.ident_equals
                                                  b1.FStar_Syntax_Syntax.ppname
                                                  b'.FStar_Syntax_Syntax.ppname)
                                         | uu____6786 -> true) subst1 in
                                  b_for_x :: subst2))
                  | uu____6787 -> subst1)) env []
let reduce_primops:
  'Auu____6810 'Auu____6811 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6811) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____6810 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun tm  ->
          let uu____6852 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Primops cfg.steps) in
          if uu____6852
          then tm
          else
            (let uu____6854 = FStar_Syntax_Util.head_and_args tm in
             match uu____6854 with
             | (head1,args) ->
                 let uu____6891 =
                   let uu____6892 = FStar_Syntax_Util.un_uinst head1 in
                   uu____6892.FStar_Syntax_Syntax.n in
                 (match uu____6891 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____6896 =
                        FStar_List.tryFind
                          (fun ps  ->
                             FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                          cfg.primitive_steps in
                      (match uu____6896 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____6913  ->
                                   let uu____6914 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name in
                                   let uu____6915 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args) in
                                   let uu____6922 =
                                     FStar_Util.string_of_int prim_step.arity in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____6914 uu____6915 uu____6922);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____6927  ->
                                   let uu____6928 =
                                     FStar_Syntax_Print.term_to_string tm in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____6928);
                              (let psc =
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst =
                                     (fun uu____6931  ->
                                        if
                                          prim_step.requires_binder_substitution
                                        then mk_psc_subst cfg env
                                        else [])
                                 } in
                               let uu____6933 =
                                 prim_step.interpretation psc args in
                               match uu____6933 with
                               | FStar_Pervasives_Native.None  ->
                                   (log_primops cfg
                                      (fun uu____6939  ->
                                         let uu____6940 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____6940);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____6946  ->
                                         let uu____6947 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         let uu____6948 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____6947 uu____6948);
                                    reduced)))
                       | FStar_Pervasives_Native.Some uu____6949 ->
                           (log_primops cfg
                              (fun uu____6953  ->
                                 let uu____6954 =
                                   FStar_Syntax_Print.term_to_string tm in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____6954);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____6958  ->
                            let uu____6959 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____6959);
                       (match args with
                        | (a1,uu____6961)::[] ->
                            FStar_Syntax_Embeddings.embed_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____6978 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____6990  ->
                            let uu____6991 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____6991);
                       (match args with
                        | (a1,uu____6993)::(a2,uu____6995)::[] ->
                            let uu____7022 =
                              FStar_Syntax_Embeddings.unembed_range a2 in
                            (match uu____7022 with
                             | FStar_Pervasives_Native.Some r ->
                                 let uu___218_7026 = a1 in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___218_7026.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = r;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___218_7026.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____7029 -> tm))
                  | uu____7038 -> tm))
let reduce_equality:
  'Auu____7049 'Auu____7050 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7050) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7049 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___219_7088 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___219_7088.tcenv);
           delta_level = (uu___219_7088.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___219_7088.strong)
         }) tm
let maybe_simplify:
  'Auu____7101 'Auu____7102 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7102) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7101 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack1 tm in
          let uu____7144 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Simplify cfg.steps) in
          if uu____7144
          then tm1
          else
            (let w t =
               let uu___220_7156 = t in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___220_7156.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___220_7156.FStar_Syntax_Syntax.vars)
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
               | uu____7173 -> FStar_Pervasives_Native.None in
             let simplify1 arg =
               ((simp_t (FStar_Pervasives_Native.fst arg)), arg) in
             match tm1.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____7213;
                         FStar_Syntax_Syntax.vars = uu____7214;_},uu____7215);
                    FStar_Syntax_Syntax.pos = uu____7216;
                    FStar_Syntax_Syntax.vars = uu____7217;_},args)
                 ->
                 let uu____7243 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____7243
                 then
                   let uu____7244 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____7244 with
                    | (FStar_Pervasives_Native.Some (true ),uu____7299)::
                        (uu____7300,(arg,uu____7302))::[] -> arg
                    | (uu____7367,(arg,uu____7369))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____7370)::[]
                        -> arg
                    | (FStar_Pervasives_Native.Some (false ),uu____7435)::uu____7436::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7499::(FStar_Pervasives_Native.Some (false
                                   ),uu____7500)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7563 -> tm1)
                 else
                   (let uu____7579 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____7579
                    then
                      let uu____7580 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____7580 with
                      | (FStar_Pervasives_Native.Some (true ),uu____7635)::uu____7636::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____7699::(FStar_Pervasives_Native.Some (true
                                     ),uu____7700)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____7763)::
                          (uu____7764,(arg,uu____7766))::[] -> arg
                      | (uu____7831,(arg,uu____7833))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____7834)::[]
                          -> arg
                      | uu____7899 -> tm1
                    else
                      (let uu____7915 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____7915
                       then
                         let uu____7916 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____7916 with
                         | uu____7971::(FStar_Pervasives_Native.Some (true
                                        ),uu____7972)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____8035)::uu____8036::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____8099)::
                             (uu____8100,(arg,uu____8102))::[] -> arg
                         | (uu____8167,(p,uu____8169))::(uu____8170,(q,uu____8172))::[]
                             ->
                             let uu____8237 = FStar_Syntax_Util.term_eq p q in
                             (if uu____8237
                              then w FStar_Syntax_Util.t_true
                              else tm1)
                         | uu____8239 -> tm1
                       else
                         (let uu____8255 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____8255
                          then
                            let uu____8256 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____8256 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____8311)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____8350)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____8389 -> tm1
                          else
                            (let uu____8405 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____8405
                             then
                               match args with
                               | (t,uu____8407)::[] ->
                                   let uu____8424 =
                                     let uu____8425 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8425.FStar_Syntax_Syntax.n in
                                   (match uu____8424 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8428::[],body,uu____8430) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8457 -> tm1)
                                    | uu____8460 -> tm1)
                               | (uu____8461,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____8462))::
                                   (t,uu____8464)::[] ->
                                   let uu____8503 =
                                     let uu____8504 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8504.FStar_Syntax_Syntax.n in
                                   (match uu____8503 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8507::[],body,uu____8509) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8536 -> tm1)
                                    | uu____8539 -> tm1)
                               | uu____8540 -> tm1
                             else
                               (let uu____8550 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____8550
                                then
                                  match args with
                                  | (t,uu____8552)::[] ->
                                      let uu____8569 =
                                        let uu____8570 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8570.FStar_Syntax_Syntax.n in
                                      (match uu____8569 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8573::[],body,uu____8575)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8602 -> tm1)
                                       | uu____8605 -> tm1)
                                  | (uu____8606,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____8607))::(t,uu____8609)::[] ->
                                      let uu____8648 =
                                        let uu____8649 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8649.FStar_Syntax_Syntax.n in
                                      (match uu____8648 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8652::[],body,uu____8654)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8681 -> tm1)
                                       | uu____8684 -> tm1)
                                  | uu____8685 -> tm1
                                else
                                  (let uu____8695 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____8695
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8696;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8697;_},uu____8698)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8715;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8716;_},uu____8717)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____8734 -> tm1
                                   else reduce_equality cfg env stack1 tm1))))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____8745;
                    FStar_Syntax_Syntax.vars = uu____8746;_},args)
                 ->
                 let uu____8768 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____8768
                 then
                   let uu____8769 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____8769 with
                    | (FStar_Pervasives_Native.Some (true ),uu____8824)::
                        (uu____8825,(arg,uu____8827))::[] -> arg
                    | (uu____8892,(arg,uu____8894))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____8895)::[]
                        -> arg
                    | (FStar_Pervasives_Native.Some (false ),uu____8960)::uu____8961::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9024::(FStar_Pervasives_Native.Some (false
                                   ),uu____9025)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9088 -> tm1)
                 else
                   (let uu____9104 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____9104
                    then
                      let uu____9105 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____9105 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9160)::uu____9161::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____9224::(FStar_Pervasives_Native.Some (true
                                     ),uu____9225)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____9288)::
                          (uu____9289,(arg,uu____9291))::[] -> arg
                      | (uu____9356,(arg,uu____9358))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____9359)::[]
                          -> arg
                      | uu____9424 -> tm1
                    else
                      (let uu____9440 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____9440
                       then
                         let uu____9441 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____9441 with
                         | uu____9496::(FStar_Pervasives_Native.Some (true
                                        ),uu____9497)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____9560)::uu____9561::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____9624)::
                             (uu____9625,(arg,uu____9627))::[] -> arg
                         | (uu____9692,(p,uu____9694))::(uu____9695,(q,uu____9697))::[]
                             ->
                             let uu____9762 = FStar_Syntax_Util.term_eq p q in
                             (if uu____9762
                              then w FStar_Syntax_Util.t_true
                              else tm1)
                         | uu____9764 -> tm1
                       else
                         (let uu____9780 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____9780
                          then
                            let uu____9781 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____9781 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____9836)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____9875)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____9914 -> tm1
                          else
                            (let uu____9930 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____9930
                             then
                               match args with
                               | (t,uu____9932)::[] ->
                                   let uu____9949 =
                                     let uu____9950 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____9950.FStar_Syntax_Syntax.n in
                                   (match uu____9949 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____9953::[],body,uu____9955) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____9982 -> tm1)
                                    | uu____9985 -> tm1)
                               | (uu____9986,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____9987))::
                                   (t,uu____9989)::[] ->
                                   let uu____10028 =
                                     let uu____10029 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10029.FStar_Syntax_Syntax.n in
                                   (match uu____10028 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10032::[],body,uu____10034) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10061 -> tm1)
                                    | uu____10064 -> tm1)
                               | uu____10065 -> tm1
                             else
                               (let uu____10075 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____10075
                                then
                                  match args with
                                  | (t,uu____10077)::[] ->
                                      let uu____10094 =
                                        let uu____10095 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10095.FStar_Syntax_Syntax.n in
                                      (match uu____10094 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10098::[],body,uu____10100)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10127 -> tm1)
                                       | uu____10130 -> tm1)
                                  | (uu____10131,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____10132))::(t,uu____10134)::[] ->
                                      let uu____10173 =
                                        let uu____10174 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10174.FStar_Syntax_Syntax.n in
                                      (match uu____10173 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10177::[],body,uu____10179)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10206 -> tm1)
                                       | uu____10209 -> tm1)
                                  | uu____10210 -> tm1
                                else
                                  (let uu____10220 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____10220
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10221;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10222;_},uu____10223)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10240;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10241;_},uu____10242)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____10259 -> tm1
                                   else reduce_equality cfg env stack1 tm1))))))
             | uu____10269 -> tm1)
let is_norm_request:
  'Auu____10276 .
    FStar_Syntax_Syntax.term -> 'Auu____10276 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10289 =
        let uu____10296 =
          let uu____10297 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10297.FStar_Syntax_Syntax.n in
        (uu____10296, args) in
      match uu____10289 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10303::uu____10304::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10308::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10313::uu____10314::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10317 -> false
let tr_norm_step: FStar_Syntax_Embeddings.norm_step -> step Prims.list =
  fun uu___185_10329  ->
    match uu___185_10329 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10335 =
          let uu____10338 =
            let uu____10339 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____10339 in
          [uu____10338] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10335
let tr_norm_steps:
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list =
  fun s  -> FStar_List.concatMap tr_norm_step s
let get_norm_request:
  'Auu____10358 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10358) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10396 =
          let uu____10399 =
            let uu____10404 =
              FStar_Syntax_Embeddings.unembed_list
                FStar_Syntax_Embeddings.unembed_norm_step in
            uu____10404 s in
          FStar_All.pipe_right uu____10399 FStar_Util.must in
        FStar_All.pipe_right uu____10396 tr_norm_steps in
      match args with
      | uu____10429::(tm,uu____10431)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____10454)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____10469)::uu____10470::(tm,uu____10472)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____10512 =
              let uu____10515 = full_norm steps in parse_steps uu____10515 in
            Beta :: uu____10512 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____10524 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___186_10542  ->
    match uu___186_10542 with
    | (App
        (uu____10545,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____10546;
                       FStar_Syntax_Syntax.vars = uu____10547;_},uu____10548,uu____10549))::uu____10550
        -> true
    | uu____10557 -> false
let firstn:
  'Auu____10566 .
    Prims.int ->
      'Auu____10566 Prims.list ->
        ('Auu____10566 Prims.list,'Auu____10566 Prims.list)
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
          (uu____10604,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____10605;
                         FStar_Syntax_Syntax.vars = uu____10606;_},uu____10607,uu____10608))::uu____10609
          -> FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)
      | uu____10616 -> false
let rec norm:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun t  ->
          let t1 = FStar_Syntax_Subst.compress t in
          log cfg
            (fun uu____10732  ->
               let uu____10733 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____10734 = FStar_Syntax_Print.term_to_string t1 in
               let uu____10735 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____10742 =
                 let uu____10743 =
                   let uu____10746 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____10746 in
                 stack_to_string uu____10743 in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____10733 uu____10734 uu____10735 uu____10742);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____10769 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____10794 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____10811 =
                 let uu____10812 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____10813 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____10812 uu____10813 in
               failwith uu____10811
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____10814 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____10831 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____10832 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10833;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____10834;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10837;
                 FStar_Syntax_Syntax.fv_delta = uu____10838;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10839;
                 FStar_Syntax_Syntax.fv_delta = uu____10840;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____10841);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar fv when
               let uu____10849 = FStar_Syntax_Syntax.lid_of_fv fv in
               FStar_TypeChecker_Env.is_action cfg.tcenv uu____10849 ->
               let b = should_reify cfg stack1 in
               (log cfg
                  (fun uu____10855  ->
                     let uu____10856 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____10857 = FStar_Util.string_of_bool b in
                     FStar_Util.print2
                       ">>> For DM4F action %s, should_reify = %s\n"
                       uu____10856 uu____10857);
                if b
                then
                  (let uu____10858 = FStar_List.tl stack1 in
                   do_unfold_fv cfg env uu____10858 t1 fv)
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
                 let uu___221_10897 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___221_10897.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___221_10897.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____10930 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____10930) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___222_10938 = cfg in
                 let uu____10939 =
                   FStar_List.filter
                     (fun uu___187_10942  ->
                        match uu___187_10942 with
                        | UnfoldOnly uu____10943 -> false
                        | NoDeltaSteps  -> false
                        | uu____10946 -> true) cfg.steps in
                 {
                   steps = uu____10939;
                   tcenv = (uu___222_10938.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___222_10938.primitive_steps);
                   strong = (uu___222_10938.strong)
                 } in
               let uu____10947 = get_norm_request (norm cfg' env []) args in
               (match uu____10947 with
                | (s,tm) ->
                    let delta_level =
                      let uu____10963 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___188_10968  ->
                                match uu___188_10968 with
                                | UnfoldUntil uu____10969 -> true
                                | UnfoldOnly uu____10970 -> true
                                | uu____10973 -> false)) in
                      if uu____10963
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___223_10978 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___223_10978.tcenv);
                        delta_level;
                        primitive_steps = (uu___223_10978.primitive_steps);
                        strong = (uu___223_10978.strong)
                      } in
                    let stack' =
                      let tail1 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let uu____10989 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms") in
                      if uu____10989
                      then
                        let uu____10992 =
                          let uu____10993 =
                            let uu____10998 = FStar_Util.now () in
                            (t1, uu____10998) in
                          Debug uu____10993 in
                        uu____10992 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of );
                  FStar_Syntax_Syntax.pos = uu____11000;
                  FStar_Syntax_Syntax.vars = uu____11001;_},a1::a2::rest)
               ->
               let uu____11049 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11049 with
                | (hd1,uu____11065) ->
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
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11130;
                  FStar_Syntax_Syntax.vars = uu____11131;_},a1::a2::rest)
               ->
               let uu____11179 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11179 with
                | (hd1,uu____11195) ->
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
                    (FStar_Const.Const_set_range_of );
                  FStar_Syntax_Syntax.pos = uu____11260;
                  FStar_Syntax_Syntax.vars = uu____11261;_},a1::a2::a3::rest)
               ->
               let uu____11322 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11322 with
                | (hd1,uu____11338) ->
                    let t' =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_app (hd1, [a1; a2]))
                        FStar_Pervasives_Native.None
                        t1.FStar_Syntax_Syntax.pos in
                    let t2 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_app (t', (a3 :: rest)))
                        FStar_Pervasives_Native.None
                        t1.FStar_Syntax_Syntax.pos in
                    norm cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect uu____11409);
                  FStar_Syntax_Syntax.pos = uu____11410;
                  FStar_Syntax_Syntax.vars = uu____11411;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____11443 = FStar_List.tl stack1 in
               norm cfg env uu____11443 (FStar_Pervasives_Native.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11446;
                  FStar_Syntax_Syntax.vars = uu____11447;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____11479 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11479 with
                | (reify_head,uu____11495) ->
                    let a1 =
                      let uu____11517 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (FStar_Pervasives_Native.fst a) in
                      FStar_Syntax_Subst.compress uu____11517 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____11520);
                            FStar_Syntax_Syntax.pos = uu____11521;
                            FStar_Syntax_Syntax.vars = uu____11522;_},a2::[])
                         ->
                         norm cfg env stack1 (FStar_Pervasives_Native.fst a2)
                     | uu____11556 ->
                         let stack2 =
                           (App
                              (env, reify_head, FStar_Pervasives_Native.None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____11566 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____11566
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11573 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____11573
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____11576 =
                      let uu____11583 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____11583, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____11576 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___189_11596  ->
                         match uu___189_11596 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____11599 =
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
                 if uu____11599
                 then false
                 else
                   (let uu____11601 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___190_11608  ->
                              match uu___190_11608 with
                              | UnfoldOnly uu____11609 -> true
                              | uu____11612 -> false)) in
                    match uu____11601 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____11616 -> should_delta) in
               (log cfg
                  (fun uu____11624  ->
                     let uu____11625 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11626 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                     let uu____11627 =
                       FStar_Util.string_of_bool should_delta1 in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____11625 uu____11626 uu____11627);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack1 t1
                else do_unfold_fv cfg env stack1 t1 f)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11630 = lookup_bvar env x in
               (match uu____11630 with
                | Univ uu____11633 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____11682 = FStar_ST.op_Bang r in
                      (match uu____11682 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11819  ->
                                 let uu____11820 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____11821 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11820
                                   uu____11821);
                            (let uu____11822 =
                               let uu____11823 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____11823.FStar_Syntax_Syntax.n in
                             match uu____11822 with
                             | FStar_Syntax_Syntax.Tm_abs uu____11826 ->
                                 norm cfg env2 stack1 t'
                             | uu____11843 -> rebuild cfg env2 stack1 t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____11901)::uu____11902 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11911)::uu____11912 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11922,uu____11923))::stack_rest ->
                    (match c with
                     | Univ uu____11927 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____11936 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____11957  ->
                                    let uu____11958 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11958);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____11998  ->
                                    let uu____11999 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11999);
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
                      (let uu___224_12049 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___224_12049.tcenv);
                         delta_level = dl;
                         primitive_steps = ps;
                         strong = (uu___224_12049.strong)
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____12082  ->
                          let uu____12083 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____12083);
                     norm cfg env stack2 t1)
                | (Debug uu____12084)::uu____12085 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12092 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12092
                    else
                      (let uu____12094 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12094 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12136  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12164 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12164
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12174 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12174)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___225_12179 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___225_12179.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___225_12179.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12180 -> lopt in
                           (log cfg
                              (fun uu____12186  ->
                                 let uu____12187 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12187);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___226_12200 = cfg in
                               {
                                 steps = (uu___226_12200.steps);
                                 tcenv = (uu___226_12200.tcenv);
                                 delta_level = (uu___226_12200.delta_level);
                                 primitive_steps =
                                   (uu___226_12200.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____12211)::uu____12212 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12219 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12219
                    else
                      (let uu____12221 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12221 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12263  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12291 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12291
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12301 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12301)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___225_12306 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___225_12306.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___225_12306.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12307 -> lopt in
                           (log cfg
                              (fun uu____12313  ->
                                 let uu____12314 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12314);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___226_12327 = cfg in
                               {
                                 steps = (uu___226_12327.steps);
                                 tcenv = (uu___226_12327.tcenv);
                                 delta_level = (uu___226_12327.delta_level);
                                 primitive_steps =
                                   (uu___226_12327.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____12338)::uu____12339 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12350 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12350
                    else
                      (let uu____12352 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12352 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12394  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12422 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12422
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12432 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12432)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___225_12437 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___225_12437.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___225_12437.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12438 -> lopt in
                           (log cfg
                              (fun uu____12444  ->
                                 let uu____12445 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12445);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___226_12458 = cfg in
                               {
                                 steps = (uu___226_12458.steps);
                                 tcenv = (uu___226_12458.tcenv);
                                 delta_level = (uu___226_12458.delta_level);
                                 primitive_steps =
                                   (uu___226_12458.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____12469)::uu____12470 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12481 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12481
                    else
                      (let uu____12483 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12483 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12525  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12553 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12553
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12563 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12563)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___225_12568 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___225_12568.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___225_12568.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12569 -> lopt in
                           (log cfg
                              (fun uu____12575  ->
                                 let uu____12576 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12576);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___226_12589 = cfg in
                               {
                                 steps = (uu___226_12589.steps);
                                 tcenv = (uu___226_12589.tcenv);
                                 delta_level = (uu___226_12589.delta_level);
                                 primitive_steps =
                                   (uu___226_12589.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____12600)::uu____12601 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12616 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12616
                    else
                      (let uu____12618 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12618 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12660  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12688 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12688
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12698 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12698)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___225_12703 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___225_12703.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___225_12703.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12704 -> lopt in
                           (log cfg
                              (fun uu____12710  ->
                                 let uu____12711 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12711);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___226_12724 = cfg in
                               {
                                 steps = (uu___226_12724.steps);
                                 tcenv = (uu___226_12724.tcenv);
                                 delta_level = (uu___226_12724.delta_level);
                                 primitive_steps =
                                   (uu___226_12724.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12735 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12735
                    else
                      (let uu____12737 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12737 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12779  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12807 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12807
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12817 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12817)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___225_12822 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___225_12822.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___225_12822.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12823 -> lopt in
                           (log cfg
                              (fun uu____12829  ->
                                 let uu____12830 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12830);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___226_12843 = cfg in
                               {
                                 steps = (uu___226_12843.steps);
                                 tcenv = (uu___226_12843.tcenv);
                                 delta_level = (uu___226_12843.delta_level);
                                 primitive_steps =
                                   (uu___226_12843.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1))))
           | FStar_Syntax_Syntax.Tm_app (head1,args) ->
               let stack2 =
                 FStar_All.pipe_right stack1
                   (FStar_List.fold_right
                      (fun uu____12892  ->
                         fun stack2  ->
                           match uu____12892 with
                           | (a,aq) ->
                               let uu____12904 =
                                 let uu____12905 =
                                   let uu____12912 =
                                     let uu____12913 =
                                       let uu____12944 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____12944, false) in
                                     Clos uu____12913 in
                                   (uu____12912, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____12905 in
                               uu____12904 :: stack2) args) in
               (log cfg
                  (fun uu____13020  ->
                     let uu____13021 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____13021);
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
                             ((let uu___227_13057 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___227_13057.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___227_13057.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____13058 ->
                      let uu____13063 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____13063)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____13066 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____13066 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1 in
                      let t2 =
                        let uu____13097 =
                          let uu____13098 =
                            let uu____13105 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___228_13107 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___228_13107.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___228_13107.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____13105) in
                          FStar_Syntax_Syntax.Tm_refine uu____13098 in
                        mk uu____13097 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains Weak cfg.steps
               then
                 let uu____13126 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____13126
               else
                 (let uu____13128 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____13128 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____13136 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____13160  -> dummy :: env1) env) in
                        norm_comp cfg uu____13136 c1 in
                      let t2 =
                        let uu____13182 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____13182 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____13241)::uu____13242 ->
                    (log cfg
                       (fun uu____13253  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | (Arg uu____13254)::uu____13255 ->
                    (log cfg
                       (fun uu____13266  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | (App
                    (uu____13267,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____13268;
                                   FStar_Syntax_Syntax.vars = uu____13269;_},uu____13270,uu____13271))::uu____13272
                    ->
                    (log cfg
                       (fun uu____13281  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | (MemoLazy uu____13282)::uu____13283 ->
                    (log cfg
                       (fun uu____13294  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | uu____13295 ->
                    (log cfg
                       (fun uu____13298  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11 in
                      log cfg
                        (fun uu____13302  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____13319 = norm cfg env [] t2 in
                             FStar_Util.Inl uu____13319
                         | FStar_Util.Inr c ->
                             let uu____13327 = norm_comp cfg env c in
                             FStar_Util.Inr uu____13327 in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env []) in
                       let uu____13333 =
                         let uu____13334 =
                           let uu____13335 =
                             let uu____13362 =
                               FStar_Syntax_Util.unascribe t12 in
                             (uu____13362, (tc1, tacopt1), l) in
                           FStar_Syntax_Syntax.Tm_ascribed uu____13335 in
                         mk uu____13334 t1.FStar_Syntax_Syntax.pos in
                       rebuild cfg env stack1 uu____13333))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____13438,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____13439;
                               FStar_Syntax_Syntax.lbunivs = uu____13440;
                               FStar_Syntax_Syntax.lbtyp = uu____13441;
                               FStar_Syntax_Syntax.lbeff = uu____13442;
                               FStar_Syntax_Syntax.lbdef = uu____13443;_}::uu____13444),uu____13445)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____13481 =
                 (let uu____13484 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____13484) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____13486 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____13486))) in
               if uu____13481
               then
                 let binder =
                   let uu____13488 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   FStar_Syntax_Syntax.mk_binder uu____13488 in
                 let env1 =
                   let uu____13498 =
                     let uu____13505 =
                       let uu____13506 =
                         let uu____13537 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____13537,
                           false) in
                       Clos uu____13506 in
                     ((FStar_Pervasives_Native.Some binder), uu____13505) in
                   uu____13498 :: env in
                 (log cfg
                    (fun uu____13622  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack1 body)
               else
                 (let uu____13624 =
                    let uu____13629 =
                      let uu____13630 =
                        let uu____13631 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____13631
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____13630] in
                    FStar_Syntax_Subst.open_term uu____13629 body in
                  match uu____13624 with
                  | (bs,body1) ->
                      (log cfg
                         (fun uu____13640  ->
                            FStar_Util.print_string
                              "+++ Normalizing Tm_let -- type\n");
                       (let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let lbname =
                          let x =
                            let uu____13648 = FStar_List.hd bs in
                            FStar_Pervasives_Native.fst uu____13648 in
                          FStar_Util.Inl
                            (let uu___229_13658 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___229_13658.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___229_13658.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = ty
                             }) in
                        log cfg
                          (fun uu____13661  ->
                             FStar_Util.print_string
                               "+++ Normalizing Tm_let -- definiens\n");
                        (let lb1 =
                           let uu___230_13663 = lb in
                           let uu____13664 =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname = lbname;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___230_13663.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = ty;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___230_13663.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____13664
                           } in
                         let env' =
                           FStar_All.pipe_right bs
                             (FStar_List.fold_left
                                (fun env1  ->
                                   fun uu____13699  -> dummy :: env1) env) in
                         let cfg1 =
                           let uu___231_13719 = cfg in
                           {
                             steps = (uu___231_13719.steps);
                             tcenv = (uu___231_13719.tcenv);
                             delta_level = (uu___231_13719.delta_level);
                             primitive_steps =
                               (uu___231_13719.primitive_steps);
                             strong = true
                           } in
                         log cfg1
                           (fun uu____13722  ->
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
               let uu____13739 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____13739 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____13775 =
                               let uu___232_13776 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___232_13776.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___232_13776.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____13775 in
                           let uu____13777 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____13777 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____13803 =
                                   FStar_List.map (fun uu____13819  -> dummy)
                                     lbs1 in
                                 let uu____13820 =
                                   let uu____13829 =
                                     FStar_List.map
                                       (fun uu____13849  -> dummy) xs1 in
                                   FStar_List.append uu____13829 env in
                                 FStar_List.append uu____13803 uu____13820 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13873 =
                                       let uu___233_13874 = rc in
                                       let uu____13875 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___233_13874.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13875;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___233_13874.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____13873
                                 | uu____13882 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___234_13886 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___234_13886.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___234_13886.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____13896 =
                        FStar_List.map (fun uu____13912  -> dummy) lbs2 in
                      FStar_List.append uu____13896 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____13920 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____13920 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___235_13936 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___235_13936.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___235_13936.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____13963 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____13963
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13982 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____14058  ->
                        match uu____14058 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___236_14179 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___236_14179.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___236_14179.FStar_Syntax_Syntax.sort)
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
               (match uu____13982 with
                | (rec_env,memos,uu____14376) ->
                    let uu____14429 =
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
                             let uu____14960 =
                               let uu____14967 =
                                 let uu____14968 =
                                   let uu____14999 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____14999, false) in
                                 Clos uu____14968 in
                               (FStar_Pervasives_Native.None, uu____14967) in
                             uu____14960 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env in
                    norm cfg body_env stack1 body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (match m with
                | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                    let uu____15104 =
                      let uu____15105 = should_reify cfg stack1 in
                      Prims.op_Negation uu____15105 in
                    if uu____15104
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____15115 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____15115
                        then
                          let uu___237_15116 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___237_15116.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps =
                              (uu___237_15116.primitive_steps);
                            strong = (uu___237_15116.strong)
                          }
                        else
                          (let uu___238_15118 = cfg in
                           {
                             steps =
                               (FStar_List.append [Exclude Zeta] cfg.steps);
                             tcenv = (uu___238_15118.tcenv);
                             delta_level = (uu___238_15118.delta_level);
                             primitive_steps =
                               (uu___238_15118.primitive_steps);
                             strong = (uu___238_15118.strong)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____15120 =
                         let uu____15121 = FStar_Syntax_Subst.compress head1 in
                         uu____15121.FStar_Syntax_Syntax.n in
                       match uu____15120 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____15139 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____15139 with
                            | (uu____15140,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____15146 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____15154 =
                                         let uu____15155 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____15155.FStar_Syntax_Syntax.n in
                                       match uu____15154 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____15161,uu____15162))
                                           ->
                                           let uu____15171 =
                                             let uu____15172 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____15172.FStar_Syntax_Syntax.n in
                                           (match uu____15171 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____15178,msrc,uu____15180))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____15189 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu____15189
                                            | uu____15190 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____15191 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____15192 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____15192 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___239_15197 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___239_15197.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___239_15197.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___239_15197.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____15198 =
                                            FStar_List.tl stack1 in
                                          let uu____15199 =
                                            let uu____15200 =
                                              let uu____15203 =
                                                let uu____15204 =
                                                  let uu____15217 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____15217) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____15204 in
                                              FStar_Syntax_Syntax.mk
                                                uu____15203 in
                                            uu____15200
                                              FStar_Pervasives_Native.None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____15198
                                            uu____15199
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____15233 =
                                            let uu____15234 = is_return body in
                                            match uu____15234 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____15238;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____15239;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____15244 -> false in
                                          if uu____15233
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
                                               let uu____15268 =
                                                 let uu____15271 =
                                                   let uu____15272 =
                                                     let uu____15289 =
                                                       let uu____15292 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____15292] in
                                                     (uu____15289, body1,
                                                       (FStar_Pervasives_Native.Some
                                                          body_rc)) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____15272 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____15271 in
                                               uu____15268
                                                 FStar_Pervasives_Native.None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____15308 =
                                                 let uu____15309 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____15309.FStar_Syntax_Syntax.n in
                                               match uu____15308 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____15315::uu____15316::[])
                                                   ->
                                                   let uu____15323 =
                                                     let uu____15326 =
                                                       let uu____15327 =
                                                         let uu____15334 =
                                                           let uu____15337 =
                                                             let uu____15338
                                                               =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____15338 in
                                                           let uu____15339 =
                                                             let uu____15342
                                                               =
                                                               let uu____15343
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____15343 in
                                                             [uu____15342] in
                                                           uu____15337 ::
                                                             uu____15339 in
                                                         (bind1, uu____15334) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____15327 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____15326 in
                                                   uu____15323
                                                     FStar_Pervasives_Native.None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____15351 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____15357 =
                                                 let uu____15360 =
                                                   let uu____15361 =
                                                     let uu____15376 =
                                                       let uu____15379 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____15380 =
                                                         let uu____15383 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____15384 =
                                                           let uu____15387 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____15388 =
                                                             let uu____15391
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____15392
                                                               =
                                                               let uu____15395
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____15396
                                                                 =
                                                                 let uu____15399
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____15399] in
                                                               uu____15395 ::
                                                                 uu____15396 in
                                                             uu____15391 ::
                                                               uu____15392 in
                                                           uu____15387 ::
                                                             uu____15388 in
                                                         uu____15383 ::
                                                           uu____15384 in
                                                       uu____15379 ::
                                                         uu____15380 in
                                                     (bind_inst, uu____15376) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____15361 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____15360 in
                                               uu____15357
                                                 FStar_Pervasives_Native.None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____15407 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____15407 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____15431 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____15431 with
                            | (uu____15432,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____15467 =
                                        let uu____15468 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____15468.FStar_Syntax_Syntax.n in
                                      match uu____15467 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____15474) -> t4
                                      | uu____15479 -> head2 in
                                    let uu____15480 =
                                      let uu____15481 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____15481.FStar_Syntax_Syntax.n in
                                    match uu____15480 with
                                    | FStar_Syntax_Syntax.Tm_fvar x ->
                                        FStar_Pervasives_Native.Some x
                                    | uu____15487 ->
                                        FStar_Pervasives_Native.None in
                                  let uu____15488 = maybe_extract_fv head2 in
                                  match uu____15488 with
                                  | FStar_Pervasives_Native.Some x when
                                      let uu____15498 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____15498
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____15503 =
                                          maybe_extract_fv head3 in
                                        match uu____15503 with
                                        | FStar_Pervasives_Native.Some
                                            uu____15508 ->
                                            FStar_Pervasives_Native.Some true
                                        | uu____15509 ->
                                            FStar_Pervasives_Native.Some
                                              false in
                                      (head3, action_unfolded)
                                  | uu____15514 ->
                                      (head2, FStar_Pervasives_Native.None) in
                                ((let is_arg_impure uu____15529 =
                                    match uu____15529 with
                                    | (e,q) ->
                                        let uu____15536 =
                                          let uu____15537 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____15537.FStar_Syntax_Syntax.n in
                                        (match uu____15536 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____15552 -> false) in
                                  let uu____15553 =
                                    let uu____15554 =
                                      let uu____15561 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____15561 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____15554 in
                                  if uu____15553
                                  then
                                    let uu____15566 =
                                      let uu____15567 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____15567 in
                                    failwith uu____15566
                                  else ());
                                 (let uu____15569 =
                                    maybe_unfold_action head_app in
                                  match uu____15569 with
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
                                      let uu____15608 = FStar_List.tl stack1 in
                                      norm cfg env uu____15608 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____15622 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____15622 in
                           let uu____15623 = FStar_List.tl stack1 in
                           norm cfg env uu____15623 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____15744  ->
                                     match uu____15744 with
                                     | (pat,wopt,tm) ->
                                         let uu____15792 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____15792))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____15824 = FStar_List.tl stack1 in
                           norm cfg env uu____15824 tm
                       | uu____15825 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let uu____15833 = should_reify cfg stack1 in
                    if uu____15833
                    then
                      let uu____15834 = FStar_List.tl stack1 in
                      let uu____15835 =
                        let uu____15836 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____15836 in
                      norm cfg env uu____15834 uu____15835
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____15839 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____15839
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___240_15848 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___240_15848.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___240_15848.primitive_steps);
                             strong = (uu___240_15848.strong)
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
                | uu____15850 ->
                    if FStar_List.contains Unmeta cfg.steps
                    then norm cfg env stack1 head1
                    else
                      (match stack1 with
                       | uu____15852::uu____15853 ->
                           (match m with
                            | FStar_Syntax_Syntax.Meta_labeled
                                (l,r,uu____15858) ->
                                norm cfg env ((Meta (m, r)) :: stack1) head1
                            | FStar_Syntax_Syntax.Meta_alien uu____15859 ->
                                rebuild cfg env stack1 t1
                            | FStar_Syntax_Syntax.Meta_pattern args ->
                                let args1 = norm_pattern_args cfg env args in
                                norm cfg env
                                  ((Meta
                                      ((FStar_Syntax_Syntax.Meta_pattern
                                          args1),
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) head1
                            | uu____15890 -> norm cfg env stack1 head1)
                       | [] ->
                           let head2 = norm cfg env [] head1 in
                           let m1 =
                             match m with
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let uu____15904 =
                                   norm_pattern_args cfg env args in
                                 FStar_Syntax_Syntax.Meta_pattern uu____15904
                             | uu____15915 -> m in
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
              let uu____15927 = FStar_Syntax_Syntax.range_of_fv f in
              FStar_TypeChecker_Env.set_range cfg.tcenv uu____15927 in
            let uu____15928 =
              FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            match uu____15928 with
            | FStar_Pervasives_Native.None  ->
                (log cfg
                   (fun uu____15941  ->
                      FStar_Util.print "Tm_fvar case 2\n" []);
                 rebuild cfg env stack1 t0)
            | FStar_Pervasives_Native.Some (us,t) ->
                (log cfg
                   (fun uu____15952  ->
                      let uu____15953 = FStar_Syntax_Print.term_to_string t0 in
                      let uu____15954 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____15953
                        uu____15954);
                 (let t1 =
                    let uu____15956 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.contains
                           (UnfoldUntil FStar_Syntax_Syntax.Delta_constant)) in
                    if uu____15956
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
                    | (UnivArgs (us',uu____15966))::stack2 ->
                        let env1 =
                          FStar_All.pipe_right us'
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun u  ->
                                    (FStar_Pervasives_Native.None, (Univ u))
                                    :: env1) env) in
                        norm cfg env1 stack2 t1
                    | uu____16021 when
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains EraseUniverses)
                        -> norm cfg env stack1 t1
                    | uu____16024 ->
                        let uu____16027 =
                          let uu____16028 =
                            FStar_Syntax_Print.lid_to_string
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                          FStar_Util.format1
                            "Impossible: missing universe instantiation on %s"
                            uu____16028 in
                        failwith uu____16027
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
              let uu____16038 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____16038 with
              | (uu____16039,return_repr) ->
                  let return_inst =
                    let uu____16048 =
                      let uu____16049 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____16049.FStar_Syntax_Syntax.n in
                    match uu____16048 with
                    | FStar_Syntax_Syntax.Tm_uinst
                        (return_tm,uu____16055::[]) ->
                        let uu____16062 =
                          let uu____16065 =
                            let uu____16066 =
                              let uu____16073 =
                                let uu____16076 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____16076] in
                              (return_tm, uu____16073) in
                            FStar_Syntax_Syntax.Tm_uinst uu____16066 in
                          FStar_Syntax_Syntax.mk uu____16065 in
                        uu____16062 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____16084 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____16087 =
                    let uu____16090 =
                      let uu____16091 =
                        let uu____16106 =
                          let uu____16109 = FStar_Syntax_Syntax.as_arg t in
                          let uu____16110 =
                            let uu____16113 = FStar_Syntax_Syntax.as_arg e in
                            [uu____16113] in
                          uu____16109 :: uu____16110 in
                        (return_inst, uu____16106) in
                      FStar_Syntax_Syntax.Tm_app uu____16091 in
                    FStar_Syntax_Syntax.mk uu____16090 in
                  uu____16087 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____16122 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____16122 with
               | FStar_Pervasives_Native.None  ->
                   let uu____16125 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____16125
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16126;
                     FStar_TypeChecker_Env.mtarget = uu____16127;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16128;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16139;
                     FStar_TypeChecker_Env.mtarget = uu____16140;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16141;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____16159 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____16159)
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
                (fun uu____16215  ->
                   match uu____16215 with
                   | (a,imp) ->
                       let uu____16226 = norm cfg env [] a in
                       (uu____16226, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___241_16243 = comp1 in
            let uu____16246 =
              let uu____16247 =
                let uu____16256 = norm cfg env [] t in
                let uu____16257 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16256, uu____16257) in
              FStar_Syntax_Syntax.Total uu____16247 in
            {
              FStar_Syntax_Syntax.n = uu____16246;
              FStar_Syntax_Syntax.pos =
                (uu___241_16243.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___241_16243.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___242_16272 = comp1 in
            let uu____16275 =
              let uu____16276 =
                let uu____16285 = norm cfg env [] t in
                let uu____16286 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16285, uu____16286) in
              FStar_Syntax_Syntax.GTotal uu____16276 in
            {
              FStar_Syntax_Syntax.n = uu____16275;
              FStar_Syntax_Syntax.pos =
                (uu___242_16272.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___242_16272.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____16338  ->
                      match uu____16338 with
                      | (a,i) ->
                          let uu____16349 = norm cfg env [] a in
                          (uu____16349, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___191_16360  ->
                      match uu___191_16360 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____16364 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____16364
                      | f -> f)) in
            let uu___243_16368 = comp1 in
            let uu____16371 =
              let uu____16372 =
                let uu___244_16373 = ct in
                let uu____16374 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____16375 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____16378 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____16374;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___244_16373.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____16375;
                  FStar_Syntax_Syntax.effect_args = uu____16378;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____16372 in
            {
              FStar_Syntax_Syntax.n = uu____16371;
              FStar_Syntax_Syntax.pos =
                (uu___243_16368.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___243_16368.FStar_Syntax_Syntax.vars)
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
            (let uu___245_16396 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___245_16396.tcenv);
               delta_level = (uu___245_16396.delta_level);
               primitive_steps = (uu___245_16396.primitive_steps);
               strong = (uu___245_16396.strong)
             }) env [] t in
        let non_info t =
          let uu____16401 = norm1 t in
          FStar_Syntax_Util.non_informative uu____16401 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____16404 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___246_16423 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.pos =
                (uu___246_16423.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___246_16423.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____16430 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____16430
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
                    let uu___247_16441 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___247_16441.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___247_16441.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___247_16441.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags = flags
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___248_16443 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___248_16443.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___248_16443.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___248_16443.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___248_16443.FStar_Syntax_Syntax.flags)
                    } in
              let uu___249_16444 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.pos =
                  (uu___249_16444.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___249_16444.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____16446 -> c
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____16449  ->
        match uu____16449 with
        | (x,imp) ->
            let uu____16452 =
              let uu___250_16453 = x in
              let uu____16454 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___250_16453.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___250_16453.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____16454
              } in
            (uu____16452, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____16460 =
          FStar_List.fold_left
            (fun uu____16478  ->
               fun b  ->
                 match uu____16478 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs in
        match uu____16460 with | (nbs,uu____16518) -> FStar_List.rev nbs
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
            let uu____16534 =
              let uu___251_16535 = rc in
              let uu____16536 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___251_16535.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____16536;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___251_16535.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____16534
        | uu____16543 -> lopt
and rebuild:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun t  ->
          log cfg
            (fun uu____16556  ->
               let uu____16557 = FStar_Syntax_Print.tag_of_term t in
               let uu____16558 = FStar_Syntax_Print.term_to_string t in
               let uu____16559 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____16566 =
                 let uu____16567 =
                   let uu____16570 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____16570 in
                 stack_to_string uu____16567 in
               FStar_Util.print4
                 ">>> %s\\Rebuild %s with %s env elements and top of the stack %s \n"
                 uu____16557 uu____16558 uu____16559 uu____16566);
          (match stack1 with
           | [] -> t
           | (Debug (tm,time_then))::stack2 ->
               ((let uu____16599 =
                   FStar_All.pipe_left
                     (FStar_TypeChecker_Env.debug cfg.tcenv)
                     (FStar_Options.Other "print_normalized_terms") in
                 if uu____16599
                 then
                   let time_now = FStar_Util.now () in
                   let uu____16601 =
                     let uu____16602 =
                       let uu____16603 =
                         FStar_Util.time_diff time_then time_now in
                       FStar_Pervasives_Native.snd uu____16603 in
                     FStar_Util.string_of_int uu____16602 in
                   let uu____16608 = FStar_Syntax_Print.term_to_string tm in
                   let uu____16609 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____16601 uu____16608 uu____16609
                 else ());
                rebuild cfg env stack2 t)
           | (Steps (s,ps,dl))::stack2 ->
               rebuild
                 (let uu___252_16627 = cfg in
                  {
                    steps = s;
                    tcenv = (uu___252_16627.tcenv);
                    delta_level = dl;
                    primitive_steps = ps;
                    strong = (uu___252_16627.strong)
                  }) env stack2 t
           | (Meta (m,r))::stack2 ->
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
               rebuild cfg env stack2 t1
           | (MemoLazy r)::stack2 ->
               (set_memo r (env, t);
                log cfg
                  (fun uu____16668  ->
                     let uu____16669 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1 "\tSet memo %s\n" uu____16669);
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
               let uu____16705 =
                 let uu___253_16706 = FStar_Syntax_Util.abs bs1 t lopt1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___253_16706.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___253_16706.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack2 uu____16705
           | (Arg (Univ uu____16707,uu____16708,uu____16709))::uu____16710 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____16713,uu____16714))::uu____16715 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack2 ->
               let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
               rebuild cfg env stack2 t1
           | (Arg (Clos (env_arg,tm,m,uu____16731),aq,r))::stack2 ->
               (log cfg
                  (fun uu____16784  ->
                     let uu____16785 = FStar_Syntax_Print.term_to_string tm in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____16785);
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
                  (let uu____16795 = FStar_ST.op_Bang m in
                   match uu____16795 with
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
                   | FStar_Pervasives_Native.Some (uu____16939,a) ->
                       let t1 =
                         FStar_Syntax_Syntax.extend_app t (a, aq)
                           FStar_Pervasives_Native.None r in
                       rebuild cfg env_arg stack2 t1))
           | (App (env1,head1,aq,r))::stack2 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r in
               let uu____16982 = maybe_simplify cfg env1 stack2 t1 in
               rebuild cfg env1 stack2 uu____16982
           | (Match (env1,branches,r))::stack2 ->
               (log cfg
                  (fun uu____16994  ->
                     let uu____16995 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____16995);
                (let scrutinee = t in
                 let norm_and_rebuild_match uu____17000 =
                   log cfg
                     (fun uu____17005  ->
                        let uu____17006 =
                          FStar_Syntax_Print.term_to_string scrutinee in
                        let uu____17007 =
                          let uu____17008 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____17025  ->
                                    match uu____17025 with
                                    | (p,uu____17035,uu____17036) ->
                                        FStar_Syntax_Print.pat_to_string p)) in
                          FStar_All.pipe_right uu____17008
                            (FStar_String.concat "\n\t") in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____17006 uu____17007);
                   (let whnf =
                      (FStar_List.contains Weak cfg.steps) ||
                        (FStar_List.contains HNF cfg.steps) in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___192_17053  ->
                                match uu___192_17053 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____17054 -> false)) in
                      let steps' =
                        let uu____17058 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____17058
                        then [Exclude Zeta]
                        else [Exclude Iota; Exclude Zeta] in
                      let uu___254_17062 = cfg in
                      {
                        steps = (FStar_List.append steps' cfg.steps);
                        tcenv = (uu___254_17062.tcenv);
                        delta_level = new_delta;
                        primitive_steps = (uu___254_17062.primitive_steps);
                        strong = true
                      } in
                    let norm_or_whnf env2 t1 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t1
                      else norm cfg_exclude_iota_zeta env2 [] t1 in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____17094 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____17115 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____17175  ->
                                    fun uu____17176  ->
                                      match (uu____17175, uu____17176) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____17267 = norm_pat env3 p1 in
                                          (match uu____17267 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2)) in
                          (match uu____17115 with
                           | (pats1,env3) ->
                               ((let uu___255_17349 = p in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___255_17349.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___256_17368 = x in
                            let uu____17369 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___256_17368.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___256_17368.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17369
                            } in
                          ((let uu___257_17383 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___257_17383.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___258_17394 = x in
                            let uu____17395 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___258_17394.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___258_17394.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17395
                            } in
                          ((let uu___259_17409 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___259_17409.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                          let x1 =
                            let uu___260_17425 = x in
                            let uu____17426 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___260_17425.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___260_17425.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17426
                            } in
                          let t2 = norm_or_whnf env2 t1 in
                          ((let uu___261_17433 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                              FStar_Syntax_Syntax.p =
                                (uu___261_17433.FStar_Syntax_Syntax.p)
                            }), env2) in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____17443 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____17457 =
                                    FStar_Syntax_Subst.open_branch branch1 in
                                  match uu____17457 with
                                  | (p,wopt,e) ->
                                      let uu____17477 = norm_pat env1 p in
                                      (match uu____17477 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____17502 =
                                                   norm_or_whnf env2 w in
                                                 FStar_Pervasives_Native.Some
                                                   uu____17502 in
                                           let e1 = norm_or_whnf env2 e in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1)))) in
                    let uu____17508 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r in
                    rebuild cfg env1 stack2 uu____17508) in
                 let rec is_cons head1 =
                   match head1.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____17518) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____17523 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17524;
                         FStar_Syntax_Syntax.fv_delta = uu____17525;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17526;
                         FStar_Syntax_Syntax.fv_delta = uu____17527;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____17528);_}
                       -> true
                   | uu____17535 -> false in
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
                   let uu____17680 =
                     FStar_Syntax_Util.head_and_args scrutinee1 in
                   match uu____17680 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____17767 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when 
                                 s = s' -> FStar_Util.Inl []
                             | uu____17806 ->
                                 let uu____17807 =
                                   let uu____17808 = is_cons head1 in
                                   Prims.op_Negation uu____17808 in
                                 FStar_Util.Inr uu____17807)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____17833 =
                              let uu____17834 =
                                FStar_Syntax_Util.un_uinst head1 in
                              uu____17834.FStar_Syntax_Syntax.n in
                            (match uu____17833 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____17852 ->
                                 let uu____17853 =
                                   let uu____17854 = is_cons head1 in
                                   Prims.op_Negation uu____17854 in
                                 FStar_Util.Inr uu____17853))
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t1,uu____17923)::rest_a,(p1,uu____17926)::rest_p) ->
                       let uu____17970 = matches_pat t1 p1 in
                       (match uu____17970 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____18019 -> FStar_Util.Inr false in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____18125 = matches_pat scrutinee1 p1 in
                       (match uu____18125 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____18165  ->
                                  let uu____18166 =
                                    FStar_Syntax_Print.pat_to_string p1 in
                                  let uu____18167 =
                                    let uu____18168 =
                                      FStar_List.map
                                        (fun uu____18178  ->
                                           match uu____18178 with
                                           | (uu____18183,t1) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t1) s in
                                    FStar_All.pipe_right uu____18168
                                      (FStar_String.concat "; ") in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____18166 uu____18167);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____18214  ->
                                       match uu____18214 with
                                       | (bv,t1) ->
                                           let uu____18237 =
                                             let uu____18244 =
                                               let uu____18247 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv in
                                               FStar_Pervasives_Native.Some
                                                 uu____18247 in
                                             let uu____18248 =
                                               let uu____18249 =
                                                 let uu____18280 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t1)) in
                                                 ([], t1, uu____18280, false) in
                                               Clos uu____18249 in
                                             (uu____18244, uu____18248) in
                                           uu____18237 :: env2) env1 s in
                              let uu____18389 = guard_when_clause wopt b rest in
                              norm cfg env2 stack2 uu____18389))) in
                 let uu____18390 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains (Exclude Iota)) in
                 if uu____18390
                 then norm_and_rebuild_match ()
                 else matches scrutinee branches)))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___193_18413  ->
                match uu___193_18413 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____18417 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____18423 -> d in
      {
        steps = s;
        tcenv = e;
        delta_level = d1;
        primitive_steps = built_in_primitive_steps;
        strong = false
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
            let uu___262_18452 = config s e in
            {
              steps = (uu___262_18452.steps);
              tcenv = (uu___262_18452.tcenv);
              delta_level = (uu___262_18452.delta_level);
              primitive_steps = (FStar_List.append c.primitive_steps ps);
              strong = (uu___262_18452.strong)
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
      fun t  -> let uu____18483 = config s e in norm_comp uu____18483 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____18498 = config [] env in norm_universe uu____18498 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  ->
      let uu____18513 = config [] env in ghost_to_pure_aux uu____18513 [] c
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
        let uu____18533 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____18533 in
      let uu____18540 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____18540
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___263_18542 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___263_18542.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___263_18542.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____18545  ->
                    let uu____18546 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____18546))
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
            ((let uu____18565 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning
                "Normalization failed with error %s\n" uu____18565);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____18578 = config [AllowUnboundUniverses] env in
          norm_comp uu____18578 [] c
        with
        | e ->
            ((let uu____18591 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning
                "Normalization failed with error %s\n" uu____18591);
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
                   let uu____18631 =
                     let uu____18632 =
                       let uu____18639 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____18639) in
                     FStar_Syntax_Syntax.Tm_refine uu____18632 in
                   mk uu____18631 t01.FStar_Syntax_Syntax.pos
               | uu____18644 -> t2)
          | uu____18645 -> t2 in
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
        let uu____18697 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____18697 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____18726 ->
                 let uu____18733 = FStar_Syntax_Util.abs_formals e in
                 (match uu____18733 with
                  | (actuals,uu____18743,uu____18744) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____18758 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____18758 with
                         | (binders,args) ->
                             let uu____18775 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____18775
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
      | uu____18785 ->
          let uu____18786 = FStar_Syntax_Util.head_and_args t in
          (match uu____18786 with
           | (head1,args) ->
               let uu____18823 =
                 let uu____18824 = FStar_Syntax_Subst.compress head1 in
                 uu____18824.FStar_Syntax_Syntax.n in
               (match uu____18823 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____18827,thead) ->
                    let uu____18853 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____18853 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____18895 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___268_18903 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___268_18903.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___268_18903.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___268_18903.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___268_18903.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___268_18903.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___268_18903.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___268_18903.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___268_18903.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___268_18903.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___268_18903.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___268_18903.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___268_18903.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___268_18903.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___268_18903.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___268_18903.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___268_18903.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___268_18903.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___268_18903.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___268_18903.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___268_18903.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___268_18903.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___268_18903.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___268_18903.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___268_18903.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___268_18903.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___268_18903.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___268_18903.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___268_18903.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___268_18903.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___268_18903.FStar_TypeChecker_Env.dsenv)
                                 }) t in
                            match uu____18895 with
                            | (uu____18904,ty,uu____18906) ->
                                eta_expand_with_type env t ty))
                | uu____18907 ->
                    let uu____18908 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___269_18916 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___269_18916.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___269_18916.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___269_18916.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___269_18916.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___269_18916.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___269_18916.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___269_18916.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___269_18916.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___269_18916.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___269_18916.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___269_18916.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___269_18916.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___269_18916.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___269_18916.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___269_18916.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___269_18916.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___269_18916.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___269_18916.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___269_18916.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___269_18916.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___269_18916.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___269_18916.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___269_18916.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___269_18916.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___269_18916.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___269_18916.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___269_18916.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___269_18916.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___269_18916.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___269_18916.FStar_TypeChecker_Env.dsenv)
                         }) t in
                    (match uu____18908 with
                     | (uu____18917,ty,uu____18919) ->
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
            | (uu____18997,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____19003,FStar_Util.Inl t) ->
                let uu____19009 =
                  let uu____19012 =
                    let uu____19013 =
                      let uu____19026 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____19026) in
                    FStar_Syntax_Syntax.Tm_arrow uu____19013 in
                  FStar_Syntax_Syntax.mk uu____19012 in
                uu____19009 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____19030 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____19030 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____19057 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____19112 ->
                    let uu____19113 =
                      let uu____19122 =
                        let uu____19123 = FStar_Syntax_Subst.compress t3 in
                        uu____19123.FStar_Syntax_Syntax.n in
                      (uu____19122, tc) in
                    (match uu____19113 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____19148) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____19185) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____19224,FStar_Util.Inl uu____19225) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____19248 -> failwith "Impossible") in
              (match uu____19057 with
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
          let uu____19357 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____19357 with
          | (univ_names1,binders1,tc) ->
              let uu____19415 = FStar_Util.left tc in
              (univ_names1, binders1, uu____19415)
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
          let uu____19454 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____19454 with
          | (univ_names1,binders1,tc) ->
              let uu____19514 = FStar_Util.right tc in
              (univ_names1, binders1, uu____19514)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____19549 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____19549 with
           | (univ_names1,binders1,typ1) ->
               let uu___270_19577 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___270_19577.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___270_19577.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___270_19577.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___270_19577.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___271_19598 = s in
          let uu____19599 =
            let uu____19600 =
              let uu____19609 = FStar_List.map (elim_uvars env) sigs in
              (uu____19609, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____19600 in
          {
            FStar_Syntax_Syntax.sigel = uu____19599;
            FStar_Syntax_Syntax.sigrng =
              (uu___271_19598.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___271_19598.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___271_19598.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___271_19598.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____19626 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____19626 with
           | (univ_names1,uu____19644,typ1) ->
               let uu___272_19658 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___272_19658.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___272_19658.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___272_19658.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___272_19658.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____19664 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____19664 with
           | (univ_names1,uu____19682,typ1) ->
               let uu___273_19696 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___273_19696.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___273_19696.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___273_19696.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___273_19696.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____19730 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____19730 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____19753 =
                            let uu____19754 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____19754 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____19753 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___274_19757 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___274_19757.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___274_19757.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___275_19758 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___275_19758.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___275_19758.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___275_19758.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___275_19758.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___276_19770 = s in
          let uu____19771 =
            let uu____19772 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____19772 in
          {
            FStar_Syntax_Syntax.sigel = uu____19771;
            FStar_Syntax_Syntax.sigrng =
              (uu___276_19770.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___276_19770.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___276_19770.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___276_19770.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____19776 = elim_uvars_aux_t env us [] t in
          (match uu____19776 with
           | (us1,uu____19794,t1) ->
               let uu___277_19808 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___277_19808.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___277_19808.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___277_19808.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___277_19808.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____19809 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____19811 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____19811 with
           | (univs1,binders,signature) ->
               let uu____19839 =
                 let uu____19848 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____19848 with
                 | (univs_opening,univs2) ->
                     let uu____19875 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____19875) in
               (match uu____19839 with
                | (univs_opening,univs_closing) ->
                    let uu____19892 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____19898 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____19899 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____19898, uu____19899) in
                    (match uu____19892 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____19921 =
                           match uu____19921 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____19939 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____19939 with
                                | (us1,t1) ->
                                    let uu____19950 =
                                      let uu____19955 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____19962 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____19955, uu____19962) in
                                    (match uu____19950 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____19975 =
                                           let uu____19980 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____19989 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____19980, uu____19989) in
                                         (match uu____19975 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____20005 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____20005 in
                                              let uu____20006 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____20006 with
                                               | (uu____20027,uu____20028,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____20043 =
                                                       let uu____20044 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____20044 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____20043 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____20049 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____20049 with
                           | (uu____20062,uu____20063,t1) -> t1 in
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
                             | uu____20123 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____20140 =
                               let uu____20141 =
                                 FStar_Syntax_Subst.compress body in
                               uu____20141.FStar_Syntax_Syntax.n in
                             match uu____20140 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____20200 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____20229 =
                               let uu____20230 =
                                 FStar_Syntax_Subst.compress t in
                               uu____20230.FStar_Syntax_Syntax.n in
                             match uu____20229 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____20251) ->
                                 let uu____20272 = destruct_action_body body in
                                 (match uu____20272 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____20317 ->
                                 let uu____20318 = destruct_action_body t in
                                 (match uu____20318 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____20367 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____20367 with
                           | (action_univs,t) ->
                               let uu____20376 = destruct_action_typ_templ t in
                               (match uu____20376 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___278_20417 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___278_20417.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___278_20417.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___279_20419 = ed in
                           let uu____20420 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____20421 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____20422 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____20423 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____20424 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____20425 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____20426 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____20427 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____20428 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____20429 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____20430 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____20431 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____20432 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____20433 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___279_20419.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___279_20419.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____20420;
                             FStar_Syntax_Syntax.bind_wp = uu____20421;
                             FStar_Syntax_Syntax.if_then_else = uu____20422;
                             FStar_Syntax_Syntax.ite_wp = uu____20423;
                             FStar_Syntax_Syntax.stronger = uu____20424;
                             FStar_Syntax_Syntax.close_wp = uu____20425;
                             FStar_Syntax_Syntax.assert_p = uu____20426;
                             FStar_Syntax_Syntax.assume_p = uu____20427;
                             FStar_Syntax_Syntax.null_wp = uu____20428;
                             FStar_Syntax_Syntax.trivial = uu____20429;
                             FStar_Syntax_Syntax.repr = uu____20430;
                             FStar_Syntax_Syntax.return_repr = uu____20431;
                             FStar_Syntax_Syntax.bind_repr = uu____20432;
                             FStar_Syntax_Syntax.actions = uu____20433
                           } in
                         let uu___280_20436 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___280_20436.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___280_20436.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___280_20436.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___280_20436.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___194_20453 =
            match uu___194_20453 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____20480 = elim_uvars_aux_t env us [] t in
                (match uu____20480 with
                 | (us1,uu____20504,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___281_20523 = sub_eff in
            let uu____20524 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____20527 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___281_20523.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___281_20523.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____20524;
              FStar_Syntax_Syntax.lift = uu____20527
            } in
          let uu___282_20530 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___282_20530.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___282_20530.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___282_20530.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___282_20530.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____20540 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____20540 with
           | (univ_names1,binders1,comp1) ->
               let uu___283_20574 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___283_20574.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___283_20574.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___283_20574.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___283_20574.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____20585 -> s