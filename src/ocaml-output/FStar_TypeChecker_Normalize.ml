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
                                else reduce_equality cfg env stack1 tm1)))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____8696;
                    FStar_Syntax_Syntax.vars = uu____8697;_},args)
                 ->
                 let uu____8719 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____8719
                 then
                   let uu____8720 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____8720 with
                    | (FStar_Pervasives_Native.Some (true ),uu____8775)::
                        (uu____8776,(arg,uu____8778))::[] -> arg
                    | (uu____8843,(arg,uu____8845))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____8846)::[]
                        -> arg
                    | (FStar_Pervasives_Native.Some (false ),uu____8911)::uu____8912::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____8975::(FStar_Pervasives_Native.Some (false
                                   ),uu____8976)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9039 -> tm1)
                 else
                   (let uu____9055 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____9055
                    then
                      let uu____9056 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____9056 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9111)::uu____9112::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____9175::(FStar_Pervasives_Native.Some (true
                                     ),uu____9176)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____9239)::
                          (uu____9240,(arg,uu____9242))::[] -> arg
                      | (uu____9307,(arg,uu____9309))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____9310)::[]
                          -> arg
                      | uu____9375 -> tm1
                    else
                      (let uu____9391 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____9391
                       then
                         let uu____9392 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____9392 with
                         | uu____9447::(FStar_Pervasives_Native.Some (true
                                        ),uu____9448)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____9511)::uu____9512::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____9575)::
                             (uu____9576,(arg,uu____9578))::[] -> arg
                         | (uu____9643,(p,uu____9645))::(uu____9646,(q,uu____9648))::[]
                             ->
                             let uu____9713 = FStar_Syntax_Util.term_eq p q in
                             (if uu____9713
                              then w FStar_Syntax_Util.t_true
                              else tm1)
                         | uu____9715 -> tm1
                       else
                         (let uu____9731 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____9731
                          then
                            let uu____9732 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____9732 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____9787)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____9826)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____9865 -> tm1
                          else
                            (let uu____9881 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____9881
                             then
                               match args with
                               | (t,uu____9883)::[] ->
                                   let uu____9900 =
                                     let uu____9901 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____9901.FStar_Syntax_Syntax.n in
                                   (match uu____9900 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____9904::[],body,uu____9906) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____9933 -> tm1)
                                    | uu____9936 -> tm1)
                               | (uu____9937,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____9938))::
                                   (t,uu____9940)::[] ->
                                   let uu____9979 =
                                     let uu____9980 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____9980.FStar_Syntax_Syntax.n in
                                   (match uu____9979 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____9983::[],body,uu____9985) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10012 -> tm1)
                                    | uu____10015 -> tm1)
                               | uu____10016 -> tm1
                             else
                               (let uu____10026 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____10026
                                then
                                  match args with
                                  | (t,uu____10028)::[] ->
                                      let uu____10045 =
                                        let uu____10046 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10046.FStar_Syntax_Syntax.n in
                                      (match uu____10045 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10049::[],body,uu____10051)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10078 -> tm1)
                                       | uu____10081 -> tm1)
                                  | (uu____10082,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____10083))::(t,uu____10085)::[] ->
                                      let uu____10124 =
                                        let uu____10125 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10125.FStar_Syntax_Syntax.n in
                                      (match uu____10124 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10128::[],body,uu____10130)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10157 -> tm1)
                                       | uu____10160 -> tm1)
                                  | uu____10161 -> tm1
                                else reduce_equality cfg env stack1 tm1)))))
             | uu____10171 -> tm1)
let is_norm_request:
  'Auu____10178 .
    FStar_Syntax_Syntax.term -> 'Auu____10178 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10191 =
        let uu____10198 =
          let uu____10199 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10199.FStar_Syntax_Syntax.n in
        (uu____10198, args) in
      match uu____10191 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10205::uu____10206::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10210::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10215::uu____10216::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10219 -> false
let tr_norm_step: FStar_Syntax_Embeddings.norm_step -> step Prims.list =
  fun uu___185_10231  ->
    match uu___185_10231 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10237 =
          let uu____10240 =
            let uu____10241 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____10241 in
          [uu____10240] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10237
let tr_norm_steps:
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list =
  fun s  -> FStar_List.concatMap tr_norm_step s
let get_norm_request:
  'Auu____10260 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10260) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10298 =
          let uu____10301 =
            let uu____10306 =
              FStar_Syntax_Embeddings.unembed_list
                FStar_Syntax_Embeddings.unembed_norm_step in
            uu____10306 s in
          FStar_All.pipe_right uu____10301 FStar_Util.must in
        FStar_All.pipe_right uu____10298 tr_norm_steps in
      match args with
      | uu____10331::(tm,uu____10333)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____10356)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____10371)::uu____10372::(tm,uu____10374)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____10414 =
              let uu____10417 = full_norm steps in parse_steps uu____10417 in
            Beta :: uu____10414 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____10426 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___186_10444  ->
    match uu___186_10444 with
    | (App
        (uu____10447,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____10448;
                       FStar_Syntax_Syntax.vars = uu____10449;_},uu____10450,uu____10451))::uu____10452
        -> true
    | uu____10459 -> false
let firstn:
  'Auu____10468 .
    Prims.int ->
      'Auu____10468 Prims.list ->
        ('Auu____10468 Prims.list,'Auu____10468 Prims.list)
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
          (uu____10506,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____10507;
                         FStar_Syntax_Syntax.vars = uu____10508;_},uu____10509,uu____10510))::uu____10511
          -> FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)
      | uu____10518 -> false
let rec norm:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun t  ->
          let t1 = FStar_Syntax_Subst.compress t in
          log cfg
            (fun uu____10634  ->
               let uu____10635 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____10636 = FStar_Syntax_Print.term_to_string t1 in
               let uu____10637 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____10644 =
                 let uu____10645 =
                   let uu____10648 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____10648 in
                 stack_to_string uu____10645 in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____10635 uu____10636 uu____10637 uu____10644);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____10671 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____10696 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____10713 =
                 let uu____10714 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____10715 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____10714 uu____10715 in
               failwith uu____10713
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____10716 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____10733 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____10734 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10735;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____10736;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10739;
                 FStar_Syntax_Syntax.fv_delta = uu____10740;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10741;
                 FStar_Syntax_Syntax.fv_delta = uu____10742;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____10743);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar fv when
               let uu____10751 = FStar_Syntax_Syntax.lid_of_fv fv in
               FStar_TypeChecker_Env.is_action cfg.tcenv uu____10751 ->
               let b = should_reify cfg stack1 in
               (log cfg
                  (fun uu____10757  ->
                     let uu____10758 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____10759 = FStar_Util.string_of_bool b in
                     FStar_Util.print2
                       ">>> For DM4F action %s, should_reify = %s\n"
                       uu____10758 uu____10759);
                if b
                then
                  (let uu____10760 = FStar_List.tl stack1 in
                   do_unfold_fv cfg env uu____10760 t1 fv)
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
                 let uu___221_10799 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___221_10799.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___221_10799.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____10832 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____10832) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___222_10840 = cfg in
                 let uu____10841 =
                   FStar_List.filter
                     (fun uu___187_10844  ->
                        match uu___187_10844 with
                        | UnfoldOnly uu____10845 -> false
                        | NoDeltaSteps  -> false
                        | uu____10848 -> true) cfg.steps in
                 {
                   steps = uu____10841;
                   tcenv = (uu___222_10840.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___222_10840.primitive_steps);
                   strong = (uu___222_10840.strong)
                 } in
               let uu____10849 = get_norm_request (norm cfg' env []) args in
               (match uu____10849 with
                | (s,tm) ->
                    let delta_level =
                      let uu____10865 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___188_10870  ->
                                match uu___188_10870 with
                                | UnfoldUntil uu____10871 -> true
                                | UnfoldOnly uu____10872 -> true
                                | uu____10875 -> false)) in
                      if uu____10865
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___223_10880 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___223_10880.tcenv);
                        delta_level;
                        primitive_steps = (uu___223_10880.primitive_steps);
                        strong = (uu___223_10880.strong)
                      } in
                    let stack' =
                      let tail1 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let uu____10891 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms") in
                      if uu____10891
                      then
                        let uu____10894 =
                          let uu____10895 =
                            let uu____10900 = FStar_Util.now () in
                            (t1, uu____10900) in
                          Debug uu____10895 in
                        uu____10894 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of );
                  FStar_Syntax_Syntax.pos = uu____10902;
                  FStar_Syntax_Syntax.vars = uu____10903;_},a1::a2::rest)
               ->
               let uu____10951 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____10951 with
                | (hd1,uu____10967) ->
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
                  FStar_Syntax_Syntax.pos = uu____11032;
                  FStar_Syntax_Syntax.vars = uu____11033;_},a1::a2::rest)
               ->
               let uu____11081 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11081 with
                | (hd1,uu____11097) ->
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
                  FStar_Syntax_Syntax.pos = uu____11162;
                  FStar_Syntax_Syntax.vars = uu____11163;_},a1::a2::a3::rest)
               ->
               let uu____11224 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11224 with
                | (hd1,uu____11240) ->
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
                    (FStar_Const.Const_reflect uu____11311);
                  FStar_Syntax_Syntax.pos = uu____11312;
                  FStar_Syntax_Syntax.vars = uu____11313;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____11345 = FStar_List.tl stack1 in
               norm cfg env uu____11345 (FStar_Pervasives_Native.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11348;
                  FStar_Syntax_Syntax.vars = uu____11349;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____11381 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11381 with
                | (reify_head,uu____11397) ->
                    let a1 =
                      let uu____11419 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (FStar_Pervasives_Native.fst a) in
                      FStar_Syntax_Subst.compress uu____11419 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____11422);
                            FStar_Syntax_Syntax.pos = uu____11423;
                            FStar_Syntax_Syntax.vars = uu____11424;_},a2::[])
                         ->
                         norm cfg env stack1 (FStar_Pervasives_Native.fst a2)
                     | uu____11458 ->
                         let stack2 =
                           (App
                              (env, reify_head, FStar_Pervasives_Native.None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____11468 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____11468
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11475 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____11475
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____11478 =
                      let uu____11485 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____11485, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____11478 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___189_11498  ->
                         match uu___189_11498 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____11501 =
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
                 if uu____11501
                 then false
                 else
                   (let uu____11503 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___190_11510  ->
                              match uu___190_11510 with
                              | UnfoldOnly uu____11511 -> true
                              | uu____11514 -> false)) in
                    match uu____11503 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____11518 -> should_delta) in
               (log cfg
                  (fun uu____11526  ->
                     let uu____11527 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11528 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                     let uu____11529 =
                       FStar_Util.string_of_bool should_delta1 in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____11527 uu____11528 uu____11529);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack1 t1
                else do_unfold_fv cfg env stack1 t1 f)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11532 = lookup_bvar env x in
               (match uu____11532 with
                | Univ uu____11535 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____11584 = FStar_ST.op_Bang r in
                      (match uu____11584 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11721  ->
                                 let uu____11722 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____11723 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11722
                                   uu____11723);
                            (let uu____11724 =
                               let uu____11725 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____11725.FStar_Syntax_Syntax.n in
                             match uu____11724 with
                             | FStar_Syntax_Syntax.Tm_abs uu____11728 ->
                                 norm cfg env2 stack1 t'
                             | uu____11745 -> rebuild cfg env2 stack1 t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____11803)::uu____11804 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11813)::uu____11814 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11824,uu____11825))::stack_rest ->
                    (match c with
                     | Univ uu____11829 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____11838 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____11859  ->
                                    let uu____11860 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11860);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____11900  ->
                                    let uu____11901 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11901);
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
                      (let uu___224_11951 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___224_11951.tcenv);
                         delta_level = dl;
                         primitive_steps = ps;
                         strong = (uu___224_11951.strong)
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____11984  ->
                          let uu____11985 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____11985);
                     norm cfg env stack2 t1)
                | (Debug uu____11986)::uu____11987 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____11994 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11994
                    else
                      (let uu____11996 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11996 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12038  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12066 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12066
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12076 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12076)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___225_12081 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___225_12081.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___225_12081.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12082 -> lopt in
                           (log cfg
                              (fun uu____12088  ->
                                 let uu____12089 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12089);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___226_12102 = cfg in
                               {
                                 steps = (uu___226_12102.steps);
                                 tcenv = (uu___226_12102.tcenv);
                                 delta_level = (uu___226_12102.delta_level);
                                 primitive_steps =
                                   (uu___226_12102.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____12113)::uu____12114 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12121 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12121
                    else
                      (let uu____12123 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12123 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12165  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12193 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12193
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12203 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12203)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___225_12208 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___225_12208.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___225_12208.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12209 -> lopt in
                           (log cfg
                              (fun uu____12215  ->
                                 let uu____12216 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12216);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___226_12229 = cfg in
                               {
                                 steps = (uu___226_12229.steps);
                                 tcenv = (uu___226_12229.tcenv);
                                 delta_level = (uu___226_12229.delta_level);
                                 primitive_steps =
                                   (uu___226_12229.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____12240)::uu____12241 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12252 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12252
                    else
                      (let uu____12254 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12254 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12296  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12324 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12324
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12334 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12334)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___225_12339 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___225_12339.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___225_12339.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12340 -> lopt in
                           (log cfg
                              (fun uu____12346  ->
                                 let uu____12347 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12347);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___226_12360 = cfg in
                               {
                                 steps = (uu___226_12360.steps);
                                 tcenv = (uu___226_12360.tcenv);
                                 delta_level = (uu___226_12360.delta_level);
                                 primitive_steps =
                                   (uu___226_12360.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____12371)::uu____12372 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12383 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12383
                    else
                      (let uu____12385 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12385 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12427  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12455 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12455
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12465 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12465)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___225_12470 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___225_12470.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___225_12470.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12471 -> lopt in
                           (log cfg
                              (fun uu____12477  ->
                                 let uu____12478 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12478);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___226_12491 = cfg in
                               {
                                 steps = (uu___226_12491.steps);
                                 tcenv = (uu___226_12491.tcenv);
                                 delta_level = (uu___226_12491.delta_level);
                                 primitive_steps =
                                   (uu___226_12491.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____12502)::uu____12503 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12518 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12518
                    else
                      (let uu____12520 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12520 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12562  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12590 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12590
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12600 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12600)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___225_12605 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___225_12605.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___225_12605.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12606 -> lopt in
                           (log cfg
                              (fun uu____12612  ->
                                 let uu____12613 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12613);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___226_12626 = cfg in
                               {
                                 steps = (uu___226_12626.steps);
                                 tcenv = (uu___226_12626.tcenv);
                                 delta_level = (uu___226_12626.delta_level);
                                 primitive_steps =
                                   (uu___226_12626.primitive_steps);
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
                      let uu____12637 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12637
                    else
                      (let uu____12639 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12639 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12681  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12709 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12709
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12719 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12719)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___225_12724 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___225_12724.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___225_12724.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12725 -> lopt in
                           (log cfg
                              (fun uu____12731  ->
                                 let uu____12732 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12732);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___226_12745 = cfg in
                               {
                                 steps = (uu___226_12745.steps);
                                 tcenv = (uu___226_12745.tcenv);
                                 delta_level = (uu___226_12745.delta_level);
                                 primitive_steps =
                                   (uu___226_12745.primitive_steps);
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
                      (fun uu____12794  ->
                         fun stack2  ->
                           match uu____12794 with
                           | (a,aq) ->
                               let uu____12806 =
                                 let uu____12807 =
                                   let uu____12814 =
                                     let uu____12815 =
                                       let uu____12846 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____12846, false) in
                                     Clos uu____12815 in
                                   (uu____12814, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____12807 in
                               uu____12806 :: stack2) args) in
               (log cfg
                  (fun uu____12922  ->
                     let uu____12923 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12923);
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
                             ((let uu___227_12959 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___227_12959.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___227_12959.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____12960 ->
                      let uu____12965 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12965)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____12968 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____12968 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1 in
                      let t2 =
                        let uu____12999 =
                          let uu____13000 =
                            let uu____13007 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___228_13009 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___228_13009.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___228_13009.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____13007) in
                          FStar_Syntax_Syntax.Tm_refine uu____13000 in
                        mk uu____12999 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains Weak cfg.steps
               then
                 let uu____13028 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____13028
               else
                 (let uu____13030 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____13030 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____13038 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____13062  -> dummy :: env1) env) in
                        norm_comp cfg uu____13038 c1 in
                      let t2 =
                        let uu____13084 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____13084 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____13143)::uu____13144 ->
                    (log cfg
                       (fun uu____13155  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | (Arg uu____13156)::uu____13157 ->
                    (log cfg
                       (fun uu____13168  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | (App
                    (uu____13169,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____13170;
                                   FStar_Syntax_Syntax.vars = uu____13171;_},uu____13172,uu____13173))::uu____13174
                    ->
                    (log cfg
                       (fun uu____13183  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | (MemoLazy uu____13184)::uu____13185 ->
                    (log cfg
                       (fun uu____13196  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | uu____13197 ->
                    (log cfg
                       (fun uu____13200  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11 in
                      log cfg
                        (fun uu____13204  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____13221 = norm cfg env [] t2 in
                             FStar_Util.Inl uu____13221
                         | FStar_Util.Inr c ->
                             let uu____13229 = norm_comp cfg env c in
                             FStar_Util.Inr uu____13229 in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env []) in
                       let uu____13235 =
                         let uu____13236 =
                           let uu____13237 =
                             let uu____13264 =
                               FStar_Syntax_Util.unascribe t12 in
                             (uu____13264, (tc1, tacopt1), l) in
                           FStar_Syntax_Syntax.Tm_ascribed uu____13237 in
                         mk uu____13236 t1.FStar_Syntax_Syntax.pos in
                       rebuild cfg env stack1 uu____13235))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____13340,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____13341;
                               FStar_Syntax_Syntax.lbunivs = uu____13342;
                               FStar_Syntax_Syntax.lbtyp = uu____13343;
                               FStar_Syntax_Syntax.lbeff = uu____13344;
                               FStar_Syntax_Syntax.lbdef = uu____13345;_}::uu____13346),uu____13347)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____13383 =
                 (let uu____13386 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____13386) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____13388 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____13388))) in
               if uu____13383
               then
                 let binder =
                   let uu____13390 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   FStar_Syntax_Syntax.mk_binder uu____13390 in
                 let env1 =
                   let uu____13400 =
                     let uu____13407 =
                       let uu____13408 =
                         let uu____13439 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____13439,
                           false) in
                       Clos uu____13408 in
                     ((FStar_Pervasives_Native.Some binder), uu____13407) in
                   uu____13400 :: env in
                 (log cfg
                    (fun uu____13524  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack1 body)
               else
                 (let uu____13526 =
                    let uu____13531 =
                      let uu____13532 =
                        let uu____13533 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____13533
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____13532] in
                    FStar_Syntax_Subst.open_term uu____13531 body in
                  match uu____13526 with
                  | (bs,body1) ->
                      (log cfg
                         (fun uu____13542  ->
                            FStar_Util.print_string
                              "+++ Normalizing Tm_let -- type\n");
                       (let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let lbname =
                          let x =
                            let uu____13550 = FStar_List.hd bs in
                            FStar_Pervasives_Native.fst uu____13550 in
                          FStar_Util.Inl
                            (let uu___229_13560 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___229_13560.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___229_13560.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = ty
                             }) in
                        log cfg
                          (fun uu____13563  ->
                             FStar_Util.print_string
                               "+++ Normalizing Tm_let -- definiens\n");
                        (let lb1 =
                           let uu___230_13565 = lb in
                           let uu____13566 =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname = lbname;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___230_13565.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = ty;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___230_13565.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____13566
                           } in
                         let env' =
                           FStar_All.pipe_right bs
                             (FStar_List.fold_left
                                (fun env1  ->
                                   fun uu____13601  -> dummy :: env1) env) in
                         let cfg1 =
                           let uu___231_13621 = cfg in
                           {
                             steps = (uu___231_13621.steps);
                             tcenv = (uu___231_13621.tcenv);
                             delta_level = (uu___231_13621.delta_level);
                             primitive_steps =
                               (uu___231_13621.primitive_steps);
                             strong = true
                           } in
                         log cfg1
                           (fun uu____13624  ->
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
               let uu____13641 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____13641 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____13677 =
                               let uu___232_13678 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___232_13678.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___232_13678.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____13677 in
                           let uu____13679 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____13679 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____13705 =
                                   FStar_List.map (fun uu____13721  -> dummy)
                                     lbs1 in
                                 let uu____13722 =
                                   let uu____13731 =
                                     FStar_List.map
                                       (fun uu____13751  -> dummy) xs1 in
                                   FStar_List.append uu____13731 env in
                                 FStar_List.append uu____13705 uu____13722 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13775 =
                                       let uu___233_13776 = rc in
                                       let uu____13777 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___233_13776.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13777;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___233_13776.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____13775
                                 | uu____13784 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___234_13788 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___234_13788.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___234_13788.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____13798 =
                        FStar_List.map (fun uu____13814  -> dummy) lbs2 in
                      FStar_List.append uu____13798 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____13822 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____13822 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___235_13838 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___235_13838.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___235_13838.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____13865 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____13865
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13884 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13960  ->
                        match uu____13960 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___236_14081 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___236_14081.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___236_14081.FStar_Syntax_Syntax.sort)
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
               (match uu____13884 with
                | (rec_env,memos,uu____14278) ->
                    let uu____14331 =
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
                             let uu____14862 =
                               let uu____14869 =
                                 let uu____14870 =
                                   let uu____14901 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____14901, false) in
                                 Clos uu____14870 in
                               (FStar_Pervasives_Native.None, uu____14869) in
                             uu____14862 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env in
                    norm cfg body_env stack1 body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (match m with
                | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                    let uu____15006 =
                      let uu____15007 = should_reify cfg stack1 in
                      Prims.op_Negation uu____15007 in
                    if uu____15006
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____15017 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____15017
                        then
                          let uu___237_15018 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___237_15018.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps =
                              (uu___237_15018.primitive_steps);
                            strong = (uu___237_15018.strong)
                          }
                        else
                          (let uu___238_15020 = cfg in
                           {
                             steps =
                               (FStar_List.append [Exclude Zeta] cfg.steps);
                             tcenv = (uu___238_15020.tcenv);
                             delta_level = (uu___238_15020.delta_level);
                             primitive_steps =
                               (uu___238_15020.primitive_steps);
                             strong = (uu___238_15020.strong)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____15022 =
                         let uu____15023 = FStar_Syntax_Subst.compress head1 in
                         uu____15023.FStar_Syntax_Syntax.n in
                       match uu____15022 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____15041 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____15041 with
                            | (uu____15042,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____15048 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____15056 =
                                         let uu____15057 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____15057.FStar_Syntax_Syntax.n in
                                       match uu____15056 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____15063,uu____15064))
                                           ->
                                           let uu____15073 =
                                             let uu____15074 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____15074.FStar_Syntax_Syntax.n in
                                           (match uu____15073 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____15080,msrc,uu____15082))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____15091 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu____15091
                                            | uu____15092 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____15093 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____15094 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____15094 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___239_15099 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___239_15099.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___239_15099.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___239_15099.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____15100 =
                                            FStar_List.tl stack1 in
                                          let uu____15101 =
                                            let uu____15102 =
                                              let uu____15105 =
                                                let uu____15106 =
                                                  let uu____15119 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____15119) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____15106 in
                                              FStar_Syntax_Syntax.mk
                                                uu____15105 in
                                            uu____15102
                                              FStar_Pervasives_Native.None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____15100
                                            uu____15101
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____15135 =
                                            let uu____15136 = is_return body in
                                            match uu____15136 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____15140;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____15141;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____15146 -> false in
                                          if uu____15135
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
                                               let uu____15170 =
                                                 let uu____15173 =
                                                   let uu____15174 =
                                                     let uu____15191 =
                                                       let uu____15194 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____15194] in
                                                     (uu____15191, body1,
                                                       (FStar_Pervasives_Native.Some
                                                          body_rc)) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____15174 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____15173 in
                                               uu____15170
                                                 FStar_Pervasives_Native.None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____15210 =
                                                 let uu____15211 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____15211.FStar_Syntax_Syntax.n in
                                               match uu____15210 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____15217::uu____15218::[])
                                                   ->
                                                   let uu____15225 =
                                                     let uu____15228 =
                                                       let uu____15229 =
                                                         let uu____15236 =
                                                           let uu____15239 =
                                                             let uu____15240
                                                               =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____15240 in
                                                           let uu____15241 =
                                                             let uu____15244
                                                               =
                                                               let uu____15245
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____15245 in
                                                             [uu____15244] in
                                                           uu____15239 ::
                                                             uu____15241 in
                                                         (bind1, uu____15236) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____15229 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____15228 in
                                                   uu____15225
                                                     FStar_Pervasives_Native.None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____15253 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____15259 =
                                                 let uu____15262 =
                                                   let uu____15263 =
                                                     let uu____15278 =
                                                       let uu____15281 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____15282 =
                                                         let uu____15285 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____15286 =
                                                           let uu____15289 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____15290 =
                                                             let uu____15293
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____15294
                                                               =
                                                               let uu____15297
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____15298
                                                                 =
                                                                 let uu____15301
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____15301] in
                                                               uu____15297 ::
                                                                 uu____15298 in
                                                             uu____15293 ::
                                                               uu____15294 in
                                                           uu____15289 ::
                                                             uu____15290 in
                                                         uu____15285 ::
                                                           uu____15286 in
                                                       uu____15281 ::
                                                         uu____15282 in
                                                     (bind_inst, uu____15278) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____15263 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____15262 in
                                               uu____15259
                                                 FStar_Pervasives_Native.None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____15309 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____15309 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____15333 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____15333 with
                            | (uu____15334,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____15369 =
                                        let uu____15370 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____15370.FStar_Syntax_Syntax.n in
                                      match uu____15369 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____15376) -> t4
                                      | uu____15381 -> head2 in
                                    let uu____15382 =
                                      let uu____15383 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____15383.FStar_Syntax_Syntax.n in
                                    match uu____15382 with
                                    | FStar_Syntax_Syntax.Tm_fvar x ->
                                        FStar_Pervasives_Native.Some x
                                    | uu____15389 ->
                                        FStar_Pervasives_Native.None in
                                  let uu____15390 = maybe_extract_fv head2 in
                                  match uu____15390 with
                                  | FStar_Pervasives_Native.Some x when
                                      let uu____15400 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____15400
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____15405 =
                                          maybe_extract_fv head3 in
                                        match uu____15405 with
                                        | FStar_Pervasives_Native.Some
                                            uu____15410 ->
                                            FStar_Pervasives_Native.Some true
                                        | uu____15411 ->
                                            FStar_Pervasives_Native.Some
                                              false in
                                      (head3, action_unfolded)
                                  | uu____15416 ->
                                      (head2, FStar_Pervasives_Native.None) in
                                ((let is_arg_impure uu____15431 =
                                    match uu____15431 with
                                    | (e,q) ->
                                        let uu____15438 =
                                          let uu____15439 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____15439.FStar_Syntax_Syntax.n in
                                        (match uu____15438 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____15454 -> false) in
                                  let uu____15455 =
                                    let uu____15456 =
                                      let uu____15463 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____15463 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____15456 in
                                  if uu____15455
                                  then
                                    let uu____15468 =
                                      let uu____15469 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____15469 in
                                    failwith uu____15468
                                  else ());
                                 (let uu____15471 =
                                    maybe_unfold_action head_app in
                                  match uu____15471 with
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
                                      let uu____15510 = FStar_List.tl stack1 in
                                      norm cfg env uu____15510 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____15524 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____15524 in
                           let uu____15525 = FStar_List.tl stack1 in
                           norm cfg env uu____15525 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____15646  ->
                                     match uu____15646 with
                                     | (pat,wopt,tm) ->
                                         let uu____15694 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____15694))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____15726 = FStar_List.tl stack1 in
                           norm cfg env uu____15726 tm
                       | uu____15727 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let uu____15735 = should_reify cfg stack1 in
                    if uu____15735
                    then
                      let uu____15736 = FStar_List.tl stack1 in
                      let uu____15737 =
                        let uu____15738 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____15738 in
                      norm cfg env uu____15736 uu____15737
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____15741 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____15741
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___240_15750 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___240_15750.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___240_15750.primitive_steps);
                             strong = (uu___240_15750.strong)
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
                | uu____15752 ->
                    if FStar_List.contains Unmeta cfg.steps
                    then norm cfg env stack1 head1
                    else
                      (match stack1 with
                       | uu____15754::uu____15755 ->
                           (match m with
                            | FStar_Syntax_Syntax.Meta_labeled
                                (l,r,uu____15760) ->
                                norm cfg env ((Meta (m, r)) :: stack1) head1
                            | FStar_Syntax_Syntax.Meta_alien uu____15761 ->
                                rebuild cfg env stack1 t1
                            | FStar_Syntax_Syntax.Meta_pattern args ->
                                let args1 = norm_pattern_args cfg env args in
                                norm cfg env
                                  ((Meta
                                      ((FStar_Syntax_Syntax.Meta_pattern
                                          args1),
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) head1
                            | uu____15792 -> norm cfg env stack1 head1)
                       | [] ->
                           let head2 = norm cfg env [] head1 in
                           let m1 =
                             match m with
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let uu____15806 =
                                   norm_pattern_args cfg env args in
                                 FStar_Syntax_Syntax.Meta_pattern uu____15806
                             | uu____15817 -> m in
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
              let uu____15829 = FStar_Syntax_Syntax.range_of_fv f in
              FStar_TypeChecker_Env.set_range cfg.tcenv uu____15829 in
            let uu____15830 =
              FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            match uu____15830 with
            | FStar_Pervasives_Native.None  ->
                (log cfg
                   (fun uu____15843  ->
                      FStar_Util.print "Tm_fvar case 2\n" []);
                 rebuild cfg env stack1 t0)
            | FStar_Pervasives_Native.Some (us,t) ->
                (log cfg
                   (fun uu____15854  ->
                      let uu____15855 = FStar_Syntax_Print.term_to_string t0 in
                      let uu____15856 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____15855
                        uu____15856);
                 (let t1 =
                    let uu____15858 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.contains
                           (UnfoldUntil FStar_Syntax_Syntax.Delta_constant)) in
                    if uu____15858
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
                    | (UnivArgs (us',uu____15868))::stack2 ->
                        let env1 =
                          FStar_All.pipe_right us'
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun u  ->
                                    (FStar_Pervasives_Native.None, (Univ u))
                                    :: env1) env) in
                        norm cfg env1 stack2 t1
                    | uu____15923 when
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains EraseUniverses)
                        -> norm cfg env stack1 t1
                    | uu____15926 ->
                        let uu____15929 =
                          let uu____15930 =
                            FStar_Syntax_Print.lid_to_string
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                          FStar_Util.format1
                            "Impossible: missing universe instantiation on %s"
                            uu____15930 in
                        failwith uu____15929
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
              let uu____15940 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____15940 with
              | (uu____15941,return_repr) ->
                  let return_inst =
                    let uu____15950 =
                      let uu____15951 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____15951.FStar_Syntax_Syntax.n in
                    match uu____15950 with
                    | FStar_Syntax_Syntax.Tm_uinst
                        (return_tm,uu____15957::[]) ->
                        let uu____15964 =
                          let uu____15967 =
                            let uu____15968 =
                              let uu____15975 =
                                let uu____15978 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____15978] in
                              (return_tm, uu____15975) in
                            FStar_Syntax_Syntax.Tm_uinst uu____15968 in
                          FStar_Syntax_Syntax.mk uu____15967 in
                        uu____15964 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____15986 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____15989 =
                    let uu____15992 =
                      let uu____15993 =
                        let uu____16008 =
                          let uu____16011 = FStar_Syntax_Syntax.as_arg t in
                          let uu____16012 =
                            let uu____16015 = FStar_Syntax_Syntax.as_arg e in
                            [uu____16015] in
                          uu____16011 :: uu____16012 in
                        (return_inst, uu____16008) in
                      FStar_Syntax_Syntax.Tm_app uu____15993 in
                    FStar_Syntax_Syntax.mk uu____15992 in
                  uu____15989 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____16024 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____16024 with
               | FStar_Pervasives_Native.None  ->
                   let uu____16027 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____16027
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16028;
                     FStar_TypeChecker_Env.mtarget = uu____16029;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16030;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16041;
                     FStar_TypeChecker_Env.mtarget = uu____16042;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16043;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____16061 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____16061)
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
                (fun uu____16117  ->
                   match uu____16117 with
                   | (a,imp) ->
                       let uu____16128 = norm cfg env [] a in
                       (uu____16128, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___241_16145 = comp1 in
            let uu____16148 =
              let uu____16149 =
                let uu____16158 = norm cfg env [] t in
                let uu____16159 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16158, uu____16159) in
              FStar_Syntax_Syntax.Total uu____16149 in
            {
              FStar_Syntax_Syntax.n = uu____16148;
              FStar_Syntax_Syntax.pos =
                (uu___241_16145.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___241_16145.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___242_16174 = comp1 in
            let uu____16177 =
              let uu____16178 =
                let uu____16187 = norm cfg env [] t in
                let uu____16188 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16187, uu____16188) in
              FStar_Syntax_Syntax.GTotal uu____16178 in
            {
              FStar_Syntax_Syntax.n = uu____16177;
              FStar_Syntax_Syntax.pos =
                (uu___242_16174.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___242_16174.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____16240  ->
                      match uu____16240 with
                      | (a,i) ->
                          let uu____16251 = norm cfg env [] a in
                          (uu____16251, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___191_16262  ->
                      match uu___191_16262 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____16266 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____16266
                      | f -> f)) in
            let uu___243_16270 = comp1 in
            let uu____16273 =
              let uu____16274 =
                let uu___244_16275 = ct in
                let uu____16276 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____16277 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____16280 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____16276;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___244_16275.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____16277;
                  FStar_Syntax_Syntax.effect_args = uu____16280;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____16274 in
            {
              FStar_Syntax_Syntax.n = uu____16273;
              FStar_Syntax_Syntax.pos =
                (uu___243_16270.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___243_16270.FStar_Syntax_Syntax.vars)
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
            (let uu___245_16298 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___245_16298.tcenv);
               delta_level = (uu___245_16298.delta_level);
               primitive_steps = (uu___245_16298.primitive_steps);
               strong = (uu___245_16298.strong)
             }) env [] t in
        let non_info t =
          let uu____16303 = norm1 t in
          FStar_Syntax_Util.non_informative uu____16303 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____16306 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___246_16325 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.pos =
                (uu___246_16325.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___246_16325.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____16332 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____16332
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
                    let uu___247_16343 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___247_16343.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___247_16343.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___247_16343.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags = flags
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___248_16345 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___248_16345.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___248_16345.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___248_16345.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___248_16345.FStar_Syntax_Syntax.flags)
                    } in
              let uu___249_16346 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.pos =
                  (uu___249_16346.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___249_16346.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____16348 -> c
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____16351  ->
        match uu____16351 with
        | (x,imp) ->
            let uu____16354 =
              let uu___250_16355 = x in
              let uu____16356 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___250_16355.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___250_16355.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____16356
              } in
            (uu____16354, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____16362 =
          FStar_List.fold_left
            (fun uu____16380  ->
               fun b  ->
                 match uu____16380 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs in
        match uu____16362 with | (nbs,uu____16420) -> FStar_List.rev nbs
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
            let uu____16436 =
              let uu___251_16437 = rc in
              let uu____16438 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___251_16437.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____16438;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___251_16437.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____16436
        | uu____16445 -> lopt
and rebuild:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun t  ->
          log cfg
            (fun uu____16458  ->
               let uu____16459 = FStar_Syntax_Print.tag_of_term t in
               let uu____16460 = FStar_Syntax_Print.term_to_string t in
               let uu____16461 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____16468 =
                 let uu____16469 =
                   let uu____16472 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____16472 in
                 stack_to_string uu____16469 in
               FStar_Util.print4
                 ">>> %s\\Rebuild %s with %s env elements and top of the stack %s \n"
                 uu____16459 uu____16460 uu____16461 uu____16468);
          (match stack1 with
           | [] -> t
           | (Debug (tm,time_then))::stack2 ->
               ((let uu____16501 =
                   FStar_All.pipe_left
                     (FStar_TypeChecker_Env.debug cfg.tcenv)
                     (FStar_Options.Other "print_normalized_terms") in
                 if uu____16501
                 then
                   let time_now = FStar_Util.now () in
                   let uu____16503 =
                     let uu____16504 =
                       let uu____16505 =
                         FStar_Util.time_diff time_then time_now in
                       FStar_Pervasives_Native.snd uu____16505 in
                     FStar_Util.string_of_int uu____16504 in
                   let uu____16510 = FStar_Syntax_Print.term_to_string tm in
                   let uu____16511 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____16503 uu____16510 uu____16511
                 else ());
                rebuild cfg env stack2 t)
           | (Steps (s,ps,dl))::stack2 ->
               rebuild
                 (let uu___252_16529 = cfg in
                  {
                    steps = s;
                    tcenv = (uu___252_16529.tcenv);
                    delta_level = dl;
                    primitive_steps = ps;
                    strong = (uu___252_16529.strong)
                  }) env stack2 t
           | (Meta (m,r))::stack2 ->
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
               rebuild cfg env stack2 t1
           | (MemoLazy r)::stack2 ->
               (set_memo r (env, t);
                log cfg
                  (fun uu____16570  ->
                     let uu____16571 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1 "\tSet memo %s\n" uu____16571);
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
               let uu____16607 =
                 let uu___253_16608 = FStar_Syntax_Util.abs bs1 t lopt1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___253_16608.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___253_16608.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack2 uu____16607
           | (Arg (Univ uu____16609,uu____16610,uu____16611))::uu____16612 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____16615,uu____16616))::uu____16617 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack2 ->
               let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
               rebuild cfg env stack2 t1
           | (Arg (Clos (env_arg,tm,m,uu____16633),aq,r))::stack2 ->
               (log cfg
                  (fun uu____16686  ->
                     let uu____16687 = FStar_Syntax_Print.term_to_string tm in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____16687);
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
                  (let uu____16697 = FStar_ST.op_Bang m in
                   match uu____16697 with
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
                   | FStar_Pervasives_Native.Some (uu____16841,a) ->
                       let t1 =
                         FStar_Syntax_Syntax.extend_app t (a, aq)
                           FStar_Pervasives_Native.None r in
                       rebuild cfg env_arg stack2 t1))
           | (App (env1,head1,aq,r))::stack2 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r in
               let uu____16884 = maybe_simplify cfg env1 stack2 t1 in
               rebuild cfg env1 stack2 uu____16884
           | (Match (env1,branches,r))::stack2 ->
               (log cfg
                  (fun uu____16896  ->
                     let uu____16897 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____16897);
                (let scrutinee = t in
                 let norm_and_rebuild_match uu____16902 =
                   log cfg
                     (fun uu____16907  ->
                        let uu____16908 =
                          FStar_Syntax_Print.term_to_string scrutinee in
                        let uu____16909 =
                          let uu____16910 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____16927  ->
                                    match uu____16927 with
                                    | (p,uu____16937,uu____16938) ->
                                        FStar_Syntax_Print.pat_to_string p)) in
                          FStar_All.pipe_right uu____16910
                            (FStar_String.concat "\n\t") in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____16908 uu____16909);
                   (let whnf =
                      (FStar_List.contains Weak cfg.steps) ||
                        (FStar_List.contains HNF cfg.steps) in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___192_16955  ->
                                match uu___192_16955 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____16956 -> false)) in
                      let steps' =
                        let uu____16960 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____16960
                        then [Exclude Zeta]
                        else [Exclude Iota; Exclude Zeta] in
                      let uu___254_16964 = cfg in
                      {
                        steps = (FStar_List.append steps' cfg.steps);
                        tcenv = (uu___254_16964.tcenv);
                        delta_level = new_delta;
                        primitive_steps = (uu___254_16964.primitive_steps);
                        strong = true
                      } in
                    let norm_or_whnf env2 t1 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t1
                      else norm cfg_exclude_iota_zeta env2 [] t1 in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____16996 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____17017 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____17077  ->
                                    fun uu____17078  ->
                                      match (uu____17077, uu____17078) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____17169 = norm_pat env3 p1 in
                                          (match uu____17169 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2)) in
                          (match uu____17017 with
                           | (pats1,env3) ->
                               ((let uu___255_17251 = p in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___255_17251.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___256_17270 = x in
                            let uu____17271 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___256_17270.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___256_17270.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17271
                            } in
                          ((let uu___257_17285 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___257_17285.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___258_17296 = x in
                            let uu____17297 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___258_17296.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___258_17296.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17297
                            } in
                          ((let uu___259_17311 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___259_17311.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                          let x1 =
                            let uu___260_17327 = x in
                            let uu____17328 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___260_17327.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___260_17327.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17328
                            } in
                          let t2 = norm_or_whnf env2 t1 in
                          ((let uu___261_17335 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                              FStar_Syntax_Syntax.p =
                                (uu___261_17335.FStar_Syntax_Syntax.p)
                            }), env2) in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____17345 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____17359 =
                                    FStar_Syntax_Subst.open_branch branch1 in
                                  match uu____17359 with
                                  | (p,wopt,e) ->
                                      let uu____17379 = norm_pat env1 p in
                                      (match uu____17379 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____17404 =
                                                   norm_or_whnf env2 w in
                                                 FStar_Pervasives_Native.Some
                                                   uu____17404 in
                                           let e1 = norm_or_whnf env2 e in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1)))) in
                    let uu____17410 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r in
                    rebuild cfg env1 stack2 uu____17410) in
                 let rec is_cons head1 =
                   match head1.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____17420) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____17425 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17426;
                         FStar_Syntax_Syntax.fv_delta = uu____17427;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17428;
                         FStar_Syntax_Syntax.fv_delta = uu____17429;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____17430);_}
                       -> true
                   | uu____17437 -> false in
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
                   let uu____17582 =
                     FStar_Syntax_Util.head_and_args scrutinee1 in
                   match uu____17582 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____17669 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when 
                                 s = s' -> FStar_Util.Inl []
                             | uu____17708 ->
                                 let uu____17709 =
                                   let uu____17710 = is_cons head1 in
                                   Prims.op_Negation uu____17710 in
                                 FStar_Util.Inr uu____17709)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____17735 =
                              let uu____17736 =
                                FStar_Syntax_Util.un_uinst head1 in
                              uu____17736.FStar_Syntax_Syntax.n in
                            (match uu____17735 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____17754 ->
                                 let uu____17755 =
                                   let uu____17756 = is_cons head1 in
                                   Prims.op_Negation uu____17756 in
                                 FStar_Util.Inr uu____17755))
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t1,uu____17825)::rest_a,(p1,uu____17828)::rest_p) ->
                       let uu____17872 = matches_pat t1 p1 in
                       (match uu____17872 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____17921 -> FStar_Util.Inr false in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____18027 = matches_pat scrutinee1 p1 in
                       (match uu____18027 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____18067  ->
                                  let uu____18068 =
                                    FStar_Syntax_Print.pat_to_string p1 in
                                  let uu____18069 =
                                    let uu____18070 =
                                      FStar_List.map
                                        (fun uu____18080  ->
                                           match uu____18080 with
                                           | (uu____18085,t1) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t1) s in
                                    FStar_All.pipe_right uu____18070
                                      (FStar_String.concat "; ") in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____18068 uu____18069);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____18116  ->
                                       match uu____18116 with
                                       | (bv,t1) ->
                                           let uu____18139 =
                                             let uu____18146 =
                                               let uu____18149 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv in
                                               FStar_Pervasives_Native.Some
                                                 uu____18149 in
                                             let uu____18150 =
                                               let uu____18151 =
                                                 let uu____18182 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t1)) in
                                                 ([], t1, uu____18182, false) in
                                               Clos uu____18151 in
                                             (uu____18146, uu____18150) in
                                           uu____18139 :: env2) env1 s in
                              let uu____18291 = guard_when_clause wopt b rest in
                              norm cfg env2 stack2 uu____18291))) in
                 let uu____18292 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains (Exclude Iota)) in
                 if uu____18292
                 then norm_and_rebuild_match ()
                 else matches scrutinee branches)))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___193_18315  ->
                match uu___193_18315 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____18319 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____18325 -> d in
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
            let uu___262_18354 = config s e in
            {
              steps = (uu___262_18354.steps);
              tcenv = (uu___262_18354.tcenv);
              delta_level = (uu___262_18354.delta_level);
              primitive_steps = (FStar_List.append c.primitive_steps ps);
              strong = (uu___262_18354.strong)
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
      fun t  -> let uu____18385 = config s e in norm_comp uu____18385 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____18400 = config [] env in norm_universe uu____18400 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  ->
      let uu____18415 = config [] env in ghost_to_pure_aux uu____18415 [] c
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
        let uu____18435 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____18435 in
      let uu____18442 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____18442
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___263_18444 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___263_18444.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___263_18444.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____18447  ->
                    let uu____18448 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____18448))
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
            ((let uu____18467 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning
                "Normalization failed with error %s\n" uu____18467);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____18480 = config [AllowUnboundUniverses] env in
          norm_comp uu____18480 [] c
        with
        | e ->
            ((let uu____18493 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning
                "Normalization failed with error %s\n" uu____18493);
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
                   let uu____18533 =
                     let uu____18534 =
                       let uu____18541 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____18541) in
                     FStar_Syntax_Syntax.Tm_refine uu____18534 in
                   mk uu____18533 t01.FStar_Syntax_Syntax.pos
               | uu____18546 -> t2)
          | uu____18547 -> t2 in
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
        let uu____18599 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____18599 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____18628 ->
                 let uu____18635 = FStar_Syntax_Util.abs_formals e in
                 (match uu____18635 with
                  | (actuals,uu____18645,uu____18646) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____18660 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____18660 with
                         | (binders,args) ->
                             let uu____18677 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____18677
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
      | uu____18687 ->
          let uu____18688 = FStar_Syntax_Util.head_and_args t in
          (match uu____18688 with
           | (head1,args) ->
               let uu____18725 =
                 let uu____18726 = FStar_Syntax_Subst.compress head1 in
                 uu____18726.FStar_Syntax_Syntax.n in
               (match uu____18725 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____18729,thead) ->
                    let uu____18755 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____18755 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____18797 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___268_18805 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___268_18805.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___268_18805.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___268_18805.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___268_18805.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___268_18805.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___268_18805.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___268_18805.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___268_18805.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___268_18805.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___268_18805.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___268_18805.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___268_18805.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___268_18805.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___268_18805.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___268_18805.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___268_18805.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___268_18805.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___268_18805.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___268_18805.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___268_18805.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___268_18805.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___268_18805.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___268_18805.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___268_18805.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___268_18805.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___268_18805.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___268_18805.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___268_18805.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___268_18805.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___268_18805.FStar_TypeChecker_Env.dsenv)
                                 }) t in
                            match uu____18797 with
                            | (uu____18806,ty,uu____18808) ->
                                eta_expand_with_type env t ty))
                | uu____18809 ->
                    let uu____18810 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___269_18818 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___269_18818.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___269_18818.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___269_18818.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___269_18818.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___269_18818.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___269_18818.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___269_18818.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___269_18818.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___269_18818.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___269_18818.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___269_18818.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___269_18818.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___269_18818.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___269_18818.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___269_18818.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___269_18818.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___269_18818.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___269_18818.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___269_18818.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___269_18818.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___269_18818.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___269_18818.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___269_18818.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___269_18818.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___269_18818.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___269_18818.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___269_18818.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___269_18818.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___269_18818.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___269_18818.FStar_TypeChecker_Env.dsenv)
                         }) t in
                    (match uu____18810 with
                     | (uu____18819,ty,uu____18821) ->
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
            | (uu____18899,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____18905,FStar_Util.Inl t) ->
                let uu____18911 =
                  let uu____18914 =
                    let uu____18915 =
                      let uu____18928 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____18928) in
                    FStar_Syntax_Syntax.Tm_arrow uu____18915 in
                  FStar_Syntax_Syntax.mk uu____18914 in
                uu____18911 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____18932 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____18932 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____18959 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____19014 ->
                    let uu____19015 =
                      let uu____19024 =
                        let uu____19025 = FStar_Syntax_Subst.compress t3 in
                        uu____19025.FStar_Syntax_Syntax.n in
                      (uu____19024, tc) in
                    (match uu____19015 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____19050) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____19087) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____19126,FStar_Util.Inl uu____19127) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____19150 -> failwith "Impossible") in
              (match uu____18959 with
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
          let uu____19259 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____19259 with
          | (univ_names1,binders1,tc) ->
              let uu____19317 = FStar_Util.left tc in
              (univ_names1, binders1, uu____19317)
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
          let uu____19356 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____19356 with
          | (univ_names1,binders1,tc) ->
              let uu____19416 = FStar_Util.right tc in
              (univ_names1, binders1, uu____19416)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____19451 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____19451 with
           | (univ_names1,binders1,typ1) ->
               let uu___270_19479 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___270_19479.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___270_19479.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___270_19479.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___270_19479.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___271_19500 = s in
          let uu____19501 =
            let uu____19502 =
              let uu____19511 = FStar_List.map (elim_uvars env) sigs in
              (uu____19511, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____19502 in
          {
            FStar_Syntax_Syntax.sigel = uu____19501;
            FStar_Syntax_Syntax.sigrng =
              (uu___271_19500.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___271_19500.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___271_19500.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___271_19500.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____19528 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____19528 with
           | (univ_names1,uu____19546,typ1) ->
               let uu___272_19560 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___272_19560.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___272_19560.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___272_19560.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___272_19560.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____19566 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____19566 with
           | (univ_names1,uu____19584,typ1) ->
               let uu___273_19598 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___273_19598.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___273_19598.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___273_19598.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___273_19598.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____19632 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____19632 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____19655 =
                            let uu____19656 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____19656 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____19655 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___274_19659 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___274_19659.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___274_19659.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___275_19660 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___275_19660.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___275_19660.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___275_19660.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___275_19660.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___276_19672 = s in
          let uu____19673 =
            let uu____19674 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____19674 in
          {
            FStar_Syntax_Syntax.sigel = uu____19673;
            FStar_Syntax_Syntax.sigrng =
              (uu___276_19672.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___276_19672.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___276_19672.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___276_19672.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____19678 = elim_uvars_aux_t env us [] t in
          (match uu____19678 with
           | (us1,uu____19696,t1) ->
               let uu___277_19710 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___277_19710.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___277_19710.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___277_19710.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___277_19710.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____19711 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____19713 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____19713 with
           | (univs1,binders,signature) ->
               let uu____19741 =
                 let uu____19750 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____19750 with
                 | (univs_opening,univs2) ->
                     let uu____19777 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____19777) in
               (match uu____19741 with
                | (univs_opening,univs_closing) ->
                    let uu____19794 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____19800 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____19801 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____19800, uu____19801) in
                    (match uu____19794 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____19823 =
                           match uu____19823 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____19841 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____19841 with
                                | (us1,t1) ->
                                    let uu____19852 =
                                      let uu____19857 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____19864 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____19857, uu____19864) in
                                    (match uu____19852 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____19877 =
                                           let uu____19882 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____19891 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____19882, uu____19891) in
                                         (match uu____19877 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____19907 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____19907 in
                                              let uu____19908 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____19908 with
                                               | (uu____19929,uu____19930,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____19945 =
                                                       let uu____19946 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____19946 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____19945 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____19951 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____19951 with
                           | (uu____19964,uu____19965,t1) -> t1 in
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
                             | uu____20025 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____20042 =
                               let uu____20043 =
                                 FStar_Syntax_Subst.compress body in
                               uu____20043.FStar_Syntax_Syntax.n in
                             match uu____20042 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____20102 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____20131 =
                               let uu____20132 =
                                 FStar_Syntax_Subst.compress t in
                               uu____20132.FStar_Syntax_Syntax.n in
                             match uu____20131 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____20153) ->
                                 let uu____20174 = destruct_action_body body in
                                 (match uu____20174 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____20219 ->
                                 let uu____20220 = destruct_action_body t in
                                 (match uu____20220 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____20269 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____20269 with
                           | (action_univs,t) ->
                               let uu____20278 = destruct_action_typ_templ t in
                               (match uu____20278 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___278_20319 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___278_20319.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___278_20319.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___279_20321 = ed in
                           let uu____20322 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____20323 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____20324 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____20325 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____20326 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____20327 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____20328 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____20329 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____20330 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____20331 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____20332 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____20333 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____20334 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____20335 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___279_20321.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___279_20321.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____20322;
                             FStar_Syntax_Syntax.bind_wp = uu____20323;
                             FStar_Syntax_Syntax.if_then_else = uu____20324;
                             FStar_Syntax_Syntax.ite_wp = uu____20325;
                             FStar_Syntax_Syntax.stronger = uu____20326;
                             FStar_Syntax_Syntax.close_wp = uu____20327;
                             FStar_Syntax_Syntax.assert_p = uu____20328;
                             FStar_Syntax_Syntax.assume_p = uu____20329;
                             FStar_Syntax_Syntax.null_wp = uu____20330;
                             FStar_Syntax_Syntax.trivial = uu____20331;
                             FStar_Syntax_Syntax.repr = uu____20332;
                             FStar_Syntax_Syntax.return_repr = uu____20333;
                             FStar_Syntax_Syntax.bind_repr = uu____20334;
                             FStar_Syntax_Syntax.actions = uu____20335
                           } in
                         let uu___280_20338 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___280_20338.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___280_20338.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___280_20338.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___280_20338.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___194_20355 =
            match uu___194_20355 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____20382 = elim_uvars_aux_t env us [] t in
                (match uu____20382 with
                 | (us1,uu____20406,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___281_20425 = sub_eff in
            let uu____20426 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____20429 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___281_20425.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___281_20425.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____20426;
              FStar_Syntax_Syntax.lift = uu____20429
            } in
          let uu___282_20432 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___282_20432.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___282_20432.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___282_20432.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___282_20432.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____20442 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____20442 with
           | (univ_names1,binders1,comp1) ->
               let uu___283_20476 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___283_20476.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___283_20476.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___283_20476.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___283_20476.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____20487 -> s