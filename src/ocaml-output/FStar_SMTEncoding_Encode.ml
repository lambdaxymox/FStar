open Prims
let add_fuel :
  'Auu____4 . 'Auu____4 -> 'Auu____4 Prims.list -> 'Auu____4 Prims.list =
  fun x  ->
    fun tl1  ->
      let uu____19 = FStar_Options.unthrottle_inductives ()  in
      if uu____19 then tl1 else x :: tl1
  
let withenv :
  'Auu____28 'Auu____29 'Auu____30 .
    'Auu____30 ->
      ('Auu____29,'Auu____28) FStar_Pervasives_Native.tuple2 ->
        ('Auu____29,'Auu____28,'Auu____30) FStar_Pervasives_Native.tuple3
  = fun c  -> fun uu____48  -> match uu____48 with | (a,b) -> (a, b, c) 
let vargs :
  'Auu____59 'Auu____60 'Auu____61 .
    (('Auu____61,'Auu____60) FStar_Util.either,'Auu____59)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      (('Auu____61,'Auu____60) FStar_Util.either,'Auu____59)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun args  ->
    FStar_List.filter
      (fun uu___78_107  ->
         match uu___78_107 with
         | (FStar_Util.Inl uu____116,uu____117) -> false
         | uu____122 -> true) args
  
let (escape : Prims.string -> Prims.string) =
  fun s  -> FStar_Util.replace_char s 39 95 
let (mk_term_projector_name :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string) =
  fun lid  ->
    fun a  ->
      let a1 =
        let uu___101_143 = a  in
        let uu____144 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname
           in
        {
          FStar_Syntax_Syntax.ppname = uu____144;
          FStar_Syntax_Syntax.index =
            (uu___101_143.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___101_143.FStar_Syntax_Syntax.sort)
        }  in
      let uu____145 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
         in
      FStar_All.pipe_left escape uu____145
  
let (primitive_projector_by_pos :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string)
  =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____158 =
          let uu____159 =
            FStar_Util.format2
              "Projector %s on data constructor %s not found"
              (Prims.string_of_int i) lid.FStar_Ident.str
             in
          failwith uu____159  in
        let uu____160 = FStar_TypeChecker_Env.lookup_datacon env lid  in
        match uu____160 with
        | (uu____165,t) ->
            let uu____167 =
              let uu____168 = FStar_Syntax_Subst.compress t  in
              uu____168.FStar_Syntax_Syntax.n  in
            (match uu____167 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____189 = FStar_Syntax_Subst.open_comp bs c  in
                 (match uu____189 with
                  | (binders,uu____195) ->
                      if
                        (i < (Prims.parse_int "0")) ||
                          (i >= (FStar_List.length binders))
                      then fail ()
                      else
                        (let b = FStar_List.nth binders i  in
                         mk_term_projector_name lid
                           (FStar_Pervasives_Native.fst b)))
             | uu____210 -> fail ())
  
let (mk_term_projector_name_by_pos :
  FStar_Ident.lident -> Prims.int -> Prims.string) =
  fun lid  ->
    fun i  ->
      let uu____217 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (Prims.string_of_int i)
         in
      FStar_All.pipe_left escape uu____217
  
let (mk_term_projector :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term)
  =
  fun lid  ->
    fun a  ->
      let uu____224 =
        let uu____229 = mk_term_projector_name lid a  in
        (uu____229,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort)))
         in
      FStar_SMTEncoding_Util.mkFreeV uu____224
  
let (mk_term_projector_by_pos :
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term) =
  fun lid  ->
    fun i  ->
      let uu____236 =
        let uu____241 = mk_term_projector_name_by_pos lid i  in
        (uu____241,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort)))
         in
      FStar_SMTEncoding_Util.mkFreeV uu____236
  
let mk_data_tester :
  'Auu____246 .
    'Auu____246 ->
      FStar_Ident.lident ->
        FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term
  =
  fun env  ->
    fun l  ->
      fun x  -> FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x
  
type varops_t =
  {
  push: Prims.unit -> Prims.unit ;
  pop: Prims.unit -> Prims.unit ;
  new_var: FStar_Ident.ident -> Prims.int -> Prims.string ;
  new_fvar: FStar_Ident.lident -> Prims.string ;
  fresh: Prims.string -> Prims.string ;
  string_const: Prims.string -> FStar_SMTEncoding_Term.term ;
  next_id: Prims.unit -> Prims.int ;
  mk_unique: Prims.string -> Prims.string }[@@deriving show]
let (__proj__Mkvarops_t__item__push : varops_t -> Prims.unit -> Prims.unit) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__push
  
let (__proj__Mkvarops_t__item__pop : varops_t -> Prims.unit -> Prims.unit) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__pop
  
let (__proj__Mkvarops_t__item__new_var :
  varops_t -> FStar_Ident.ident -> Prims.int -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__new_var
  
let (__proj__Mkvarops_t__item__new_fvar :
  varops_t -> FStar_Ident.lident -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__new_fvar
  
let (__proj__Mkvarops_t__item__fresh :
  varops_t -> Prims.string -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__fresh
  
let (__proj__Mkvarops_t__item__string_const :
  varops_t -> Prims.string -> FStar_SMTEncoding_Term.term) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__string_const
  
let (__proj__Mkvarops_t__item__next_id : varops_t -> Prims.unit -> Prims.int)
  =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__next_id
  
let (__proj__Mkvarops_t__item__mk_unique :
  varops_t -> Prims.string -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__mk_unique
  
let (varops : varops_t) =
  let initial_ctr = (Prims.parse_int "100")  in
  let ctr = FStar_Util.mk_ref initial_ctr  in
  let new_scope uu____610 =
    let uu____611 = FStar_Util.smap_create (Prims.parse_int "100")  in
    let uu____614 = FStar_Util.smap_create (Prims.parse_int "100")  in
    (uu____611, uu____614)  in
  let scopes =
    let uu____634 = let uu____645 = new_scope ()  in [uu____645]  in
    FStar_Util.mk_ref uu____634  in
  let mk_unique y =
    let y1 = escape y  in
    let y2 =
      let uu____686 =
        let uu____689 = FStar_ST.op_Bang scopes  in
        FStar_Util.find_map uu____689
          (fun uu____824  ->
             match uu____824 with
             | (names1,uu____836) -> FStar_Util.smap_try_find names1 y1)
         in
      match uu____686 with
      | FStar_Pervasives_Native.None  -> y1
      | FStar_Pervasives_Native.Some uu____845 ->
          (FStar_Util.incr ctr;
           (let uu____958 =
              let uu____959 =
                let uu____960 = FStar_ST.op_Bang ctr  in
                Prims.string_of_int uu____960  in
              Prims.strcat "__" uu____959  in
            Prims.strcat y1 uu____958))
       in
    let top_scope =
      let uu____1057 =
        let uu____1066 = FStar_ST.op_Bang scopes  in FStar_List.hd uu____1066
         in
      FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1057  in
    FStar_Util.smap_add top_scope y2 true; y2  in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn)))
     in
  let new_fvar lid = mk_unique lid.FStar_Ident.str  in
  let next_id1 uu____1227 = FStar_Util.incr ctr; FStar_ST.op_Bang ctr  in
  let fresh1 pfx =
    let uu____1437 =
      let uu____1438 = next_id1 ()  in
      FStar_All.pipe_left Prims.string_of_int uu____1438  in
    FStar_Util.format2 "%s_%s" pfx uu____1437  in
  let string_const s =
    let uu____1443 =
      let uu____1446 = FStar_ST.op_Bang scopes  in
      FStar_Util.find_map uu____1446
        (fun uu____1581  ->
           match uu____1581 with
           | (uu____1592,strings) -> FStar_Util.smap_try_find strings s)
       in
    match uu____1443 with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None  ->
        let id1 = next_id1 ()  in
        let f =
          let uu____1605 = FStar_SMTEncoding_Util.mk_String_const id1  in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____1605  in
        let top_scope =
          let uu____1609 =
            let uu____1618 = FStar_ST.op_Bang scopes  in
            FStar_List.hd uu____1618  in
          FStar_All.pipe_left FStar_Pervasives_Native.snd uu____1609  in
        (FStar_Util.smap_add top_scope s f; f)
     in
  let push1 uu____1768 =
    let uu____1769 =
      let uu____1780 = new_scope ()  in
      let uu____1789 = FStar_ST.op_Bang scopes  in uu____1780 :: uu____1789
       in
    FStar_ST.op_Colon_Equals scopes uu____1769  in
  let pop1 uu____2037 =
    let uu____2038 =
      let uu____2049 = FStar_ST.op_Bang scopes  in FStar_List.tl uu____2049
       in
    FStar_ST.op_Colon_Equals scopes uu____2038  in
  {
    push = push1;
    pop = pop1;
    new_var;
    new_fvar;
    fresh = fresh1;
    string_const;
    next_id = next_id1;
    mk_unique
  } 
let (unmangle : FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.bv) =
  fun x  ->
    let uu___102_2297 = x  in
    let uu____2298 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname  in
    {
      FStar_Syntax_Syntax.ppname = uu____2298;
      FStar_Syntax_Syntax.index = (uu___102_2297.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___102_2297.FStar_Syntax_Syntax.sort)
    }
  
type binding =
  | Binding_var of (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
  FStar_Pervasives_Native.tuple2 
  | Binding_fvar of
  (FStar_Ident.lident,Prims.string,FStar_SMTEncoding_Term.term
                                     FStar_Pervasives_Native.option,FStar_SMTEncoding_Term.term
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple4 [@@deriving show]
let (uu___is_Binding_var : binding -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____2331 -> false
  
let (__proj__Binding_var__item___0 :
  binding ->
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Binding_var _0 -> _0 
let (uu___is_Binding_fvar : binding -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____2367 -> false
  
let (__proj__Binding_fvar__item___0 :
  binding ->
    (FStar_Ident.lident,Prims.string,FStar_SMTEncoding_Term.term
                                       FStar_Pervasives_Native.option,
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Binding_fvar _0 -> _0 
let binder_of_eithervar :
  'Auu____2414 'Auu____2415 .
    'Auu____2415 ->
      ('Auu____2415,'Auu____2414 FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  = fun v1  -> (v1, FStar_Pervasives_Native.None) 
type cache_entry =
  {
  cache_symbol_name: Prims.string ;
  cache_symbol_arg_sorts: FStar_SMTEncoding_Term.sort Prims.list ;
  cache_symbol_decls: FStar_SMTEncoding_Term.decl Prims.list ;
  cache_symbol_assumption_names: Prims.string Prims.list }[@@deriving show]
let (__proj__Mkcache_entry__item__cache_symbol_name :
  cache_entry -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name = __fname__cache_symbol_name;
        cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts;
        cache_symbol_decls = __fname__cache_symbol_decls;
        cache_symbol_assumption_names =
          __fname__cache_symbol_assumption_names;_}
        -> __fname__cache_symbol_name
  
let (__proj__Mkcache_entry__item__cache_symbol_arg_sorts :
  cache_entry -> FStar_SMTEncoding_Term.sort Prims.list) =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name = __fname__cache_symbol_name;
        cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts;
        cache_symbol_decls = __fname__cache_symbol_decls;
        cache_symbol_assumption_names =
          __fname__cache_symbol_assumption_names;_}
        -> __fname__cache_symbol_arg_sorts
  
let (__proj__Mkcache_entry__item__cache_symbol_decls :
  cache_entry -> FStar_SMTEncoding_Term.decl Prims.list) =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name = __fname__cache_symbol_name;
        cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts;
        cache_symbol_decls = __fname__cache_symbol_decls;
        cache_symbol_assumption_names =
          __fname__cache_symbol_assumption_names;_}
        -> __fname__cache_symbol_decls
  
let (__proj__Mkcache_entry__item__cache_symbol_assumption_names :
  cache_entry -> Prims.string Prims.list) =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name = __fname__cache_symbol_name;
        cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts;
        cache_symbol_decls = __fname__cache_symbol_decls;
        cache_symbol_assumption_names =
          __fname__cache_symbol_assumption_names;_}
        -> __fname__cache_symbol_assumption_names
  
type env_t =
  {
  bindings: binding Prims.list ;
  depth: Prims.int ;
  tcenv: FStar_TypeChecker_Env.env ;
  warn: Prims.bool ;
  cache: cache_entry FStar_Util.smap ;
  nolabels: Prims.bool ;
  use_zfuel_name: Prims.bool ;
  encode_non_total_function_typ: Prims.bool ;
  current_module_name: Prims.string }[@@deriving show]
let (__proj__Mkenv_t__item__bindings : env_t -> binding Prims.list) =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__bindings
  
let (__proj__Mkenv_t__item__depth : env_t -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__depth
  
let (__proj__Mkenv_t__item__tcenv : env_t -> FStar_TypeChecker_Env.env) =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__tcenv
  
let (__proj__Mkenv_t__item__warn : env_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__warn
  
let (__proj__Mkenv_t__item__cache : env_t -> cache_entry FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__cache
  
let (__proj__Mkenv_t__item__nolabels : env_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__nolabels
  
let (__proj__Mkenv_t__item__use_zfuel_name : env_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__use_zfuel_name
  
let (__proj__Mkenv_t__item__encode_non_total_function_typ :
  env_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__encode_non_total_function_typ
  
let (__proj__Mkenv_t__item__current_module_name : env_t -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__current_module_name
  
let mk_cache_entry :
  'Auu____2711 .
    'Auu____2711 ->
      Prims.string ->
        FStar_SMTEncoding_Term.sort Prims.list ->
          FStar_SMTEncoding_Term.decl Prims.list -> cache_entry
  =
  fun env  ->
    fun tsym  ->
      fun cvar_sorts  ->
        fun t_decls  ->
          let names1 =
            FStar_All.pipe_right t_decls
              (FStar_List.collect
                 (fun uu___79_2745  ->
                    match uu___79_2745 with
                    | FStar_SMTEncoding_Term.Assume a ->
                        [a.FStar_SMTEncoding_Term.assumption_name]
                    | uu____2749 -> []))
             in
          {
            cache_symbol_name = tsym;
            cache_symbol_arg_sorts = cvar_sorts;
            cache_symbol_decls = t_decls;
            cache_symbol_assumption_names = names1
          }
  
let (use_cache_entry : cache_entry -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun ce  ->
    [FStar_SMTEncoding_Term.RetainAssumptions
       (ce.cache_symbol_assumption_names)]
  
let (print_env : env_t -> Prims.string) =
  fun e  ->
    let uu____2758 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___80_2768  ->
              match uu___80_2768 with
              | Binding_var (x,uu____2770) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____2772,uu____2773,uu____2774) ->
                  FStar_Syntax_Print.lid_to_string l))
       in
    FStar_All.pipe_right uu____2758 (FStar_String.concat ", ")
  
let lookup_binding :
  'Auu____2788 .
    env_t ->
      (binding -> 'Auu____2788 FStar_Pervasives_Native.option) ->
        'Auu____2788 FStar_Pervasives_Native.option
  = fun env  -> fun f  -> FStar_Util.find_map env.bindings f 
let (caption_t :
  env_t ->
    FStar_Syntax_Syntax.term -> Prims.string FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t  ->
      let uu____2816 =
        FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
      if uu____2816
      then
        let uu____2819 = FStar_Syntax_Print.term_to_string t  in
        FStar_Pervasives_Native.Some uu____2819
      else FStar_Pervasives_Native.None
  
let (fresh_fvar :
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string,FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x  in
      let uu____2832 = FStar_SMTEncoding_Util.mkFreeV (xsym, s)  in
      (xsym, uu____2832)
  
let (gen_term_var :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string,FStar_SMTEncoding_Term.term,env_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun x  ->
      let ysym = Prims.strcat "@x" (Prims.string_of_int env.depth)  in
      let y =
        FStar_SMTEncoding_Util.mkFreeV
          (ysym, FStar_SMTEncoding_Term.Term_sort)
         in
      (ysym, y,
        (let uu___103_2848 = env  in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___103_2848.tcenv);
           warn = (uu___103_2848.warn);
           cache = (uu___103_2848.cache);
           nolabels = (uu___103_2848.nolabels);
           use_zfuel_name = (uu___103_2848.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___103_2848.encode_non_total_function_typ);
           current_module_name = (uu___103_2848.current_module_name)
         }))
  
let (new_term_constant :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string,FStar_SMTEncoding_Term.term,env_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun x  ->
      let ysym =
        varops.new_var x.FStar_Syntax_Syntax.ppname
          x.FStar_Syntax_Syntax.index
         in
      let y = FStar_SMTEncoding_Util.mkApp (ysym, [])  in
      (ysym, y,
        (let uu___104_2866 = env  in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___104_2866.depth);
           tcenv = (uu___104_2866.tcenv);
           warn = (uu___104_2866.warn);
           cache = (uu___104_2866.cache);
           nolabels = (uu___104_2866.nolabels);
           use_zfuel_name = (uu___104_2866.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___104_2866.encode_non_total_function_typ);
           current_module_name = (uu___104_2866.current_module_name)
         }))
  
let (new_term_constant_from_string :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      Prims.string ->
        (Prims.string,FStar_SMTEncoding_Term.term,env_t)
          FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun x  ->
      fun str  ->
        let ysym = varops.mk_unique str  in
        let y = FStar_SMTEncoding_Util.mkApp (ysym, [])  in
        (ysym, y,
          (let uu___105_2887 = env  in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___105_2887.depth);
             tcenv = (uu___105_2887.tcenv);
             warn = (uu___105_2887.warn);
             cache = (uu___105_2887.cache);
             nolabels = (uu___105_2887.nolabels);
             use_zfuel_name = (uu___105_2887.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___105_2887.encode_non_total_function_typ);
             current_module_name = (uu___105_2887.current_module_name)
           }))
  
let (push_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t) =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___106_2897 = env  in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___106_2897.depth);
          tcenv = (uu___106_2897.tcenv);
          warn = (uu___106_2897.warn);
          cache = (uu___106_2897.cache);
          nolabels = (uu___106_2897.nolabels);
          use_zfuel_name = (uu___106_2897.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___106_2897.encode_non_total_function_typ);
          current_module_name = (uu___106_2897.current_module_name)
        }
  
let (lookup_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term) =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___81_2921  ->
             match uu___81_2921 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 FStar_Pervasives_Native.Some (b, t)
             | uu____2934 -> FStar_Pervasives_Native.None)
         in
      let uu____2939 = aux a  in
      match uu____2939 with
      | FStar_Pervasives_Native.None  ->
          let a2 = unmangle a  in
          let uu____2951 = aux a2  in
          (match uu____2951 with
           | FStar_Pervasives_Native.None  ->
               let uu____2962 =
                 let uu____2963 = FStar_Syntax_Print.bv_to_string a2  in
                 let uu____2964 = print_env env  in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____2963 uu____2964
                  in
               failwith uu____2962
           | FStar_Pervasives_Native.Some (b,t) -> t)
      | FStar_Pervasives_Native.Some (b,t) -> t
  
let (new_term_constant_and_tok_from_lid :
  env_t ->
    FStar_Ident.lident ->
      (Prims.string,Prims.string,env_t) FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun x  ->
      let fname = varops.new_fvar x  in
      let ftok = Prims.strcat fname "@tok"  in
      let uu____2991 =
        let uu___107_2992 = env  in
        let uu____2993 =
          let uu____2996 =
            let uu____2997 =
              let uu____3010 =
                let uu____3013 = FStar_SMTEncoding_Util.mkApp (ftok, [])  in
                FStar_All.pipe_left
                  (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
                  uu____3013
                 in
              (x, fname, uu____3010, FStar_Pervasives_Native.None)  in
            Binding_fvar uu____2997  in
          uu____2996 :: (env.bindings)  in
        {
          bindings = uu____2993;
          depth = (uu___107_2992.depth);
          tcenv = (uu___107_2992.tcenv);
          warn = (uu___107_2992.warn);
          cache = (uu___107_2992.cache);
          nolabels = (uu___107_2992.nolabels);
          use_zfuel_name = (uu___107_2992.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___107_2992.encode_non_total_function_typ);
          current_module_name = (uu___107_2992.current_module_name)
        }  in
      (fname, ftok, uu____2991)
  
let (try_lookup_lid :
  env_t ->
    FStar_Ident.lident ->
      (Prims.string,FStar_SMTEncoding_Term.term
                      FStar_Pervasives_Native.option,FStar_SMTEncoding_Term.term
                                                       FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple3 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun a  ->
      lookup_binding env
        (fun uu___82_3055  ->
           match uu___82_3055 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               FStar_Pervasives_Native.Some (t1, t2, t3)
           | uu____3094 -> FStar_Pervasives_Native.None)
  
let (contains_name : env_t -> Prims.string -> Prims.bool) =
  fun env  ->
    fun s  ->
      let uu____3111 =
        lookup_binding env
          (fun uu___83_3119  ->
             match uu___83_3119 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 FStar_Pervasives_Native.Some ()
             | uu____3134 -> FStar_Pervasives_Native.None)
         in
      FStar_All.pipe_right uu____3111 FStar_Option.isSome
  
let (lookup_lid :
  env_t ->
    FStar_Ident.lident ->
      (Prims.string,FStar_SMTEncoding_Term.term
                      FStar_Pervasives_Native.option,FStar_SMTEncoding_Term.term
                                                       FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun a  ->
      let uu____3153 = try_lookup_lid env a  in
      match uu____3153 with
      | FStar_Pervasives_Native.None  ->
          let uu____3186 =
            let uu____3187 = FStar_Syntax_Print.lid_to_string a  in
            FStar_Util.format1 "Name not found: %s" uu____3187  in
          failwith uu____3186
      | FStar_Pervasives_Native.Some s -> s
  
let (push_free_var :
  env_t ->
    FStar_Ident.lident ->
      Prims.string ->
        FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option -> env_t)
  =
  fun env  ->
    fun x  ->
      fun fname  ->
        fun ftok  ->
          let uu___108_3235 = env  in
          {
            bindings =
              ((Binding_fvar (x, fname, ftok, FStar_Pervasives_Native.None))
              :: (env.bindings));
            depth = (uu___108_3235.depth);
            tcenv = (uu___108_3235.tcenv);
            warn = (uu___108_3235.warn);
            cache = (uu___108_3235.cache);
            nolabels = (uu___108_3235.nolabels);
            use_zfuel_name = (uu___108_3235.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___108_3235.encode_non_total_function_typ);
            current_module_name = (uu___108_3235.current_module_name)
          }
  
let (push_zfuel_name : env_t -> FStar_Ident.lident -> Prims.string -> env_t)
  =
  fun env  ->
    fun x  ->
      fun f  ->
        let uu____3249 = lookup_lid env x  in
        match uu____3249 with
        | (t1,t2,uu____3262) ->
            let t3 =
              let uu____3272 =
                let uu____3279 =
                  let uu____3282 = FStar_SMTEncoding_Util.mkApp ("ZFuel", [])
                     in
                  [uu____3282]  in
                (f, uu____3279)  in
              FStar_SMTEncoding_Util.mkApp uu____3272  in
            let uu___109_3287 = env  in
            {
              bindings =
                ((Binding_fvar (x, t1, t2, (FStar_Pervasives_Native.Some t3)))
                :: (env.bindings));
              depth = (uu___109_3287.depth);
              tcenv = (uu___109_3287.tcenv);
              warn = (uu___109_3287.warn);
              cache = (uu___109_3287.cache);
              nolabels = (uu___109_3287.nolabels);
              use_zfuel_name = (uu___109_3287.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___109_3287.encode_non_total_function_typ);
              current_module_name = (uu___109_3287.current_module_name)
            }
  
let (try_lookup_free_var :
  env_t ->
    FStar_Ident.lident ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____3300 = try_lookup_lid env l  in
      match uu____3300 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (name,sym,zf_opt) ->
          (match zf_opt with
           | FStar_Pervasives_Native.Some f when env.use_zfuel_name ->
               FStar_Pervasives_Native.Some f
           | uu____3349 ->
               (match sym with
                | FStar_Pervasives_Native.Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____3357,fuel::[]) ->
                         let uu____3361 =
                           let uu____3362 =
                             let uu____3363 =
                               FStar_SMTEncoding_Term.fv_of_term fuel  in
                             FStar_All.pipe_right uu____3363
                               FStar_Pervasives_Native.fst
                              in
                           FStar_Util.starts_with uu____3362 "fuel"  in
                         if uu____3361
                         then
                           let uu____3366 =
                             let uu____3367 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort)
                                in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____3367
                               fuel
                              in
                           FStar_All.pipe_left
                             (fun _0_41  ->
                                FStar_Pervasives_Native.Some _0_41)
                             uu____3366
                         else FStar_Pervasives_Native.Some t
                     | uu____3371 -> FStar_Pervasives_Native.Some t)
                | uu____3372 -> FStar_Pervasives_Native.None))
  
let (lookup_free_var :
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      FStar_SMTEncoding_Term.term)
  =
  fun env  ->
    fun a  ->
      let uu____3385 = try_lookup_free_var env a.FStar_Syntax_Syntax.v  in
      match uu____3385 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let uu____3389 =
            let uu____3390 =
              FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v  in
            FStar_Util.format1 "Name not found: %s" uu____3390  in
          failwith uu____3389
  
let (lookup_free_var_name :
  env_t -> FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t -> Prims.string)
  =
  fun env  ->
    fun a  ->
      let uu____3401 = lookup_lid env a.FStar_Syntax_Syntax.v  in
      match uu____3401 with | (x,uu____3413,uu____3414) -> x
  
let (lookup_free_var_sym :
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      (FStar_SMTEncoding_Term.op,FStar_SMTEncoding_Term.term Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun a  ->
      let uu____3439 = lookup_lid env a.FStar_Syntax_Syntax.v  in
      match uu____3439 with
      | (name,sym,zf_opt) ->
          (match zf_opt with
           | FStar_Pervasives_Native.Some
               {
                 FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                   (g,zf);
                 FStar_SMTEncoding_Term.freevars = uu____3475;
                 FStar_SMTEncoding_Term.rng = uu____3476;_}
               when env.use_zfuel_name -> (g, zf)
           | uu____3491 ->
               (match sym with
                | FStar_Pervasives_Native.None  ->
                    ((FStar_SMTEncoding_Term.Var name), [])
                | FStar_Pervasives_Native.Some sym1 ->
                    (match sym1.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                     | uu____3515 -> ((FStar_SMTEncoding_Term.Var name), []))))
  
let (tok_of_name :
  env_t ->
    Prims.string ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___84_3531  ->
           match uu___84_3531 with
           | Binding_fvar (uu____3534,nm',tok,uu____3537) when nm = nm' ->
               tok
           | uu____3546 -> FStar_Pervasives_Native.None)
  
let mkForall_fuel' :
  'Auu____3550 .
    'Auu____3550 ->
      (FStar_SMTEncoding_Term.pat Prims.list Prims.list,FStar_SMTEncoding_Term.fvs,
        FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple3 ->
        FStar_SMTEncoding_Term.term
  =
  fun n1  ->
    fun uu____3568  ->
      match uu____3568 with
      | (pats,vars,body) ->
          let fallback uu____3593 =
            FStar_SMTEncoding_Util.mkForall (pats, vars, body)  in
          let uu____3598 = FStar_Options.unthrottle_inductives ()  in
          if uu____3598
          then fallback ()
          else
            (let uu____3600 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort
                in
             match uu____3600 with
             | (fsym,fterm) ->
                 let add_fuel1 tms =
                   FStar_All.pipe_right tms
                     (FStar_List.map
                        (fun p  ->
                           match p.FStar_SMTEncoding_Term.tm with
                           | FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var "HasType",args) ->
                               FStar_SMTEncoding_Util.mkApp
                                 ("HasTypeFuel", (fterm :: args))
                           | uu____3631 -> p))
                    in
                 let pats1 = FStar_List.map add_fuel1 pats  in
                 let body1 =
                   match body.FStar_SMTEncoding_Term.tm with
                   | FStar_SMTEncoding_Term.App
                       (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                       let guard1 =
                         match guard.FStar_SMTEncoding_Term.tm with
                         | FStar_SMTEncoding_Term.App
                             (FStar_SMTEncoding_Term.And ,guards) ->
                             let uu____3652 = add_fuel1 guards  in
                             FStar_SMTEncoding_Util.mk_and_l uu____3652
                         | uu____3655 ->
                             let uu____3656 = add_fuel1 [guard]  in
                             FStar_All.pipe_right uu____3656 FStar_List.hd
                          in
                       FStar_SMTEncoding_Util.mkImp (guard1, body')
                   | uu____3661 -> body  in
                 let vars1 = (fsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars
                    in
                 FStar_SMTEncoding_Util.mkForall (pats1, vars1, body1))
  
let (mkForall_fuel :
  (FStar_SMTEncoding_Term.pat Prims.list Prims.list,FStar_SMTEncoding_Term.fvs,
    FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple3 ->
    FStar_SMTEncoding_Term.term)
  = mkForall_fuel' (Prims.parse_int "1") 
let (head_normal : env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow uu____3702 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____3715 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____3722 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____3723 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____3740 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____3757 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3759 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____3759 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____3777;
             FStar_Syntax_Syntax.vars = uu____3778;_},uu____3779)
          ->
          let uu____3800 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____3800 FStar_Option.isNone
      | uu____3817 -> false
  
let (head_redex : env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____3824 =
        let uu____3825 = FStar_Syntax_Util.un_uinst t  in
        uu____3825.FStar_Syntax_Syntax.n  in
      match uu____3824 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____3828,uu____3829,FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___85_3850  ->
                  match uu___85_3850 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____3851 -> false)
               rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3853 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____3853 FStar_Option.isSome
      | uu____3870 -> false
  
let (whnf : env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun t  ->
      let uu____3877 = head_normal env t  in
      if uu____3877
      then t
      else
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Weak;
          FStar_TypeChecker_Normalize.HNF;
          FStar_TypeChecker_Normalize.Exclude
            FStar_TypeChecker_Normalize.Zeta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t
  
let (norm : env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun t  ->
      FStar_TypeChecker_Normalize.normalize
        [FStar_TypeChecker_Normalize.Beta;
        FStar_TypeChecker_Normalize.Exclude FStar_TypeChecker_Normalize.Zeta;
        FStar_TypeChecker_Normalize.Eager_unfolding;
        FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t
  
let (trivial_post : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____3888 =
      let uu____3889 = FStar_Syntax_Syntax.null_binder t  in [uu____3889]  in
    let uu____3890 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
       in
    FStar_Syntax_Util.abs uu____3888 uu____3890 FStar_Pervasives_Native.None
  
let (mk_Apply :
  FStar_SMTEncoding_Term.term ->
    (Prims.string,FStar_SMTEncoding_Term.sort) FStar_Pervasives_Native.tuple2
      Prims.list -> FStar_SMTEncoding_Term.term)
  =
  fun e  ->
    fun vars  ->
      FStar_All.pipe_right vars
        (FStar_List.fold_left
           (fun out  ->
              fun var  ->
                match FStar_Pervasives_Native.snd var with
                | FStar_SMTEncoding_Term.Fuel_sort  ->
                    let uu____3928 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____3928
                | s ->
                    let uu____3933 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____3933) e)
  
let (mk_Apply_args :
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term)
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
  
let (is_app : FStar_SMTEncoding_Term.op -> Prims.bool) =
  fun uu___86_3948  ->
    match uu___86_3948 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____3949 -> false
  
let (is_an_eta_expansion :
  env_t ->
    FStar_SMTEncoding_Term.fv Prims.list ->
      FStar_SMTEncoding_Term.term ->
        FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun vars  ->
      fun body  ->
        let rec check_partial_applications t xs =
          match ((t.FStar_SMTEncoding_Term.tm), xs) with
          | (FStar_SMTEncoding_Term.App
             (app,f::{
                       FStar_SMTEncoding_Term.tm =
                         FStar_SMTEncoding_Term.FreeV y;
                       FStar_SMTEncoding_Term.freevars = uu____3985;
                       FStar_SMTEncoding_Term.rng = uu____3986;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____4009) ->
              let uu____4018 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____4029 -> false) args (FStar_List.rev xs))
                 in
              if uu____4018
              then tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____4033,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t  in
              let uu____4037 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____4041 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars
                           in
                        Prims.op_Negation uu____4041))
                 in
              if uu____4037
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____4045 -> FStar_Pervasives_Native.None  in
        check_partial_applications body (FStar_List.rev vars)
  
type label =
  (FStar_SMTEncoding_Term.fv,Prims.string,FStar_Range.range)
    FStar_Pervasives_Native.tuple3[@@deriving show]
type labels = label Prims.list[@@deriving show]
type pattern =
  {
  pat_vars:
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.fv)
      FStar_Pervasives_Native.tuple2 Prims.list
    ;
  pat_term:
    Prims.unit ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
    ;
  guard: FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term ;
  projections:
    FStar_SMTEncoding_Term.term ->
      (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2 Prims.list
    }[@@deriving show]
let (__proj__Mkpattern__item__pat_vars :
  pattern ->
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.fv)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__pat_vars
  
let (__proj__Mkpattern__item__pat_term :
  pattern ->
    Prims.unit ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__pat_term
  
let (__proj__Mkpattern__item__guard :
  pattern -> FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term) =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__guard
  
let (__proj__Mkpattern__item__projections :
  pattern ->
    FStar_SMTEncoding_Term.term ->
      (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__projections
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____4267 -> false
  
exception Inner_let_rec 
let (uu___is_Inner_let_rec : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inner_let_rec  -> true | uu____4271 -> false
  
let (as_function_typ :
  env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t0  ->
      let rec aux norm1 t =
        let t1 = FStar_Syntax_Subst.compress t  in
        match t1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow uu____4290 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____4303 ->
            let uu____4310 = FStar_Syntax_Util.unrefine t1  in
            aux true uu____4310
        | uu____4311 ->
            if norm1
            then let uu____4312 = whnf env t1  in aux false uu____4312
            else
              (let uu____4314 =
                 let uu____4315 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos  in
                 let uu____4316 = FStar_Syntax_Print.term_to_string t0  in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____4315 uu____4316
                  in
               failwith uu____4314)
         in
      aux true t0
  
let rec (curried_arrow_formals_comp :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2)
  =
  fun k  ->
    let k1 = FStar_Syntax_Subst.compress k  in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        FStar_Syntax_Subst.open_comp bs c
    | FStar_Syntax_Syntax.Tm_refine (bv,uu____4348) ->
        curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort
    | uu____4353 ->
        let uu____4354 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____4354)
  
let is_arithmetic_primitive :
  'Auu____4368 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____4368 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4388::uu____4389::[]) ->
          ((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Addition)
               ||
               (FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.op_Subtraction))
              ||
              (FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.op_Multiply))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Division))
            ||
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Modulus)
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4393::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____4396 -> false
  
let (isInteger : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____4417 -> false
  
let (getInteger : FStar_Syntax_Syntax.term' -> Prims.int) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____4432 -> failwith "Expected an Integer term"
  
let is_BitVector_primitive :
  'Auu____4436 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____4436)
        FStar_Pervasives_Native.tuple2 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____4475)::uu____4476::uu____4477::[]) ->
          (((((((((((FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.bv_and_lid)
                      ||
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.bv_xor_lid))
                     ||
                     (FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.bv_or_lid))
                    ||
                    (FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.bv_add_lid))
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.bv_sub_lid))
                  ||
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_shift_left_lid))
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_shift_right_lid))
                ||
                (FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.bv_udiv_lid))
               ||
               (FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.bv_mod_lid))
              ||
              (FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.bv_uext_lid))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_mul_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____4528)::uu____4529::[])
          ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____4566 -> false
  
let rec (encode_const :
  FStar_Const.sconst ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decl Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun c  ->
    fun env  ->
      match c with
      | FStar_Const.Const_unit  -> (FStar_SMTEncoding_Term.mk_Term_unit, [])
      | FStar_Const.Const_bool (true ) ->
          let uu____4785 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue  in
          (uu____4785, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____4788 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse  in
          (uu____4788, [])
      | FStar_Const.Const_char c1 ->
          let uu____4792 =
            let uu____4793 =
              let uu____4800 =
                let uu____4803 =
                  let uu____4804 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1)
                     in
                  FStar_SMTEncoding_Term.boxInt uu____4804  in
                [uu____4803]  in
              ("FStar.Char.__char_of_int", uu____4800)  in
            FStar_SMTEncoding_Util.mkApp uu____4793  in
          (uu____4792, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____4820 =
            let uu____4821 = FStar_SMTEncoding_Util.mkInteger i  in
            FStar_SMTEncoding_Term.boxInt uu____4821  in
          (uu____4820, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.tcenv).FStar_TypeChecker_Env.dsenv repr sw
              FStar_Range.dummyRange
             in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____4842) ->
          let uu____4843 = varops.string_const s  in (uu____4843, [])
      | FStar_Const.Const_range uu____4846 ->
          let uu____4847 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          (uu____4847, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | c1 ->
          let uu____4853 =
            let uu____4854 = FStar_Syntax_Print.const_to_string c1  in
            FStar_Util.format1 "Unhandled constant: %s" uu____4854  in
          failwith uu____4853

and (encode_binders :
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.binders ->
      env_t ->
        (FStar_SMTEncoding_Term.fv Prims.list,FStar_SMTEncoding_Term.term
                                                Prims.list,env_t,FStar_SMTEncoding_Term.decls_t,
          FStar_Syntax_Syntax.bv Prims.list) FStar_Pervasives_Native.tuple5)
  =
  fun fuel_opt  ->
    fun bs  ->
      fun env  ->
        (let uu____4883 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
         if uu____4883
         then
           let uu____4884 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" uu____4884
         else ());
        (let uu____4886 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____4970  ->
                   fun b  ->
                     match uu____4970 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____5049 =
                           let x = unmangle (FStar_Pervasives_Native.fst b)
                              in
                           let uu____5065 = gen_term_var env1 x  in
                           match uu____5065 with
                           | (xxsym,xx,env') ->
                               let uu____5089 =
                                 let uu____5094 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____5094 env1 xx
                                  in
                               (match uu____5089 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x))
                            in
                         (match uu____5049 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], []))
            in
         match uu____4886 with
         | (vars,guards,env1,decls,names1) ->
             ((FStar_List.rev vars), (FStar_List.rev guards), env1, decls,
               (FStar_List.rev names1)))

and (encode_term_pred :
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.typ ->
      env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
            FStar_Pervasives_Native.tuple2)
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____5253 = encode_term t env  in
          match uu____5253 with
          | (t1,decls) ->
              let uu____5264 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____5264, decls)

and (encode_term_pred' :
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.typ ->
      env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
            FStar_Pervasives_Native.tuple2)
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____5275 = encode_term t env  in
          match uu____5275 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____5290 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____5290, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____5292 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____5292, decls))

and (encode_arith_term :
  env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____5298 = encode_args args_e env  in
        match uu____5298 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____5317 -> failwith "Impossible"  in
            let unary arg_tms1 =
              let uu____5326 = FStar_List.hd arg_tms1  in
              FStar_SMTEncoding_Term.unboxInt uu____5326  in
            let binary arg_tms1 =
              let uu____5339 =
                let uu____5340 = FStar_List.hd arg_tms1  in
                FStar_SMTEncoding_Term.unboxInt uu____5340  in
              let uu____5341 =
                let uu____5342 =
                  let uu____5343 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____5343  in
                FStar_SMTEncoding_Term.unboxInt uu____5342  in
              (uu____5339, uu____5341)  in
            let mk_default uu____5349 =
              let uu____5350 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____5350 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms))
               in
            let mk_l a op mk_args ts =
              let uu____5396 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____5396
              then
                let uu____5397 =
                  let uu____5398 = mk_args ts  in op uu____5398  in
                FStar_All.pipe_right uu____5397 FStar_SMTEncoding_Term.boxInt
              else mk_default ()  in
            let mk_nl nm op ts =
              let uu____5427 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____5427
              then
                let uu____5428 = binary ts  in
                match uu____5428 with
                | (t1,t2) ->
                    let uu____5435 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____5435
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____5439 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____5439
                 then
                   let uu____5440 = op (binary ts)  in
                   FStar_All.pipe_right uu____5440
                     FStar_SMTEncoding_Term.boxInt
                 else mk_default ())
               in
            let add1 =
              mk_l ()
                (fun a415  -> (Obj.magic FStar_SMTEncoding_Util.mkAdd) a415)
                (fun a416  -> (Obj.magic binary) a416)
               in
            let sub1 =
              mk_l ()
                (fun a417  -> (Obj.magic FStar_SMTEncoding_Util.mkSub) a417)
                (fun a418  -> (Obj.magic binary) a418)
               in
            let minus =
              mk_l ()
                (fun a419  -> (Obj.magic FStar_SMTEncoding_Util.mkMinus) a419)
                (fun a420  -> (Obj.magic unary) a420)
               in
            let mul1 = mk_nl "_mul" FStar_SMTEncoding_Util.mkMul  in
            let div1 = mk_nl "_div" FStar_SMTEncoding_Util.mkDiv  in
            let modulus = mk_nl "_mod" FStar_SMTEncoding_Util.mkMod  in
            let ops =
              [(FStar_Parser_Const.op_Addition, add1);
              (FStar_Parser_Const.op_Subtraction, sub1);
              (FStar_Parser_Const.op_Multiply, mul1);
              (FStar_Parser_Const.op_Division, div1);
              (FStar_Parser_Const.op_Modulus, modulus);
              (FStar_Parser_Const.op_Minus, minus)]  in
            let uu____5563 =
              let uu____5572 =
                FStar_List.tryFind
                  (fun uu____5594  ->
                     match uu____5594 with
                     | (l,uu____5604) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____5572 FStar_Util.must  in
            (match uu____5563 with
             | (uu____5643,op) ->
                 let uu____5653 = op arg_tms  in (uu____5653, decls))

and (encode_BitVector_term :
  env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.arg Prims.list ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____5661 = FStar_List.hd args_e  in
        match uu____5661 with
        | (tm_sz,uu____5669) ->
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n  in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz)  in
            let sz_decls =
              let uu____5679 = FStar_Util.smap_try_find env.cache sz_key  in
              match uu____5679 with
              | FStar_Pervasives_Native.Some cache_entry -> []
              | FStar_Pervasives_Native.None  ->
                  let t_decls = FStar_SMTEncoding_Term.mkBvConstructor sz  in
                  ((let uu____5687 = mk_cache_entry env "" [] []  in
                    FStar_Util.smap_add env.cache sz_key uu____5687);
                   t_decls)
               in
            let uu____5688 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5708::(sz_arg,uu____5710)::uu____5711::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____5760 =
                    let uu____5763 = FStar_List.tail args_e  in
                    FStar_List.tail uu____5763  in
                  let uu____5766 =
                    let uu____5769 = getInteger sz_arg.FStar_Syntax_Syntax.n
                       in
                    FStar_Pervasives_Native.Some uu____5769  in
                  (uu____5760, uu____5766)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5775::(sz_arg,uu____5777)::uu____5778::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____5827 =
                    let uu____5828 = FStar_Syntax_Print.term_to_string sz_arg
                       in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____5828
                     in
                  failwith uu____5827
              | uu____5837 ->
                  let uu____5844 = FStar_List.tail args_e  in
                  (uu____5844, FStar_Pervasives_Native.None)
               in
            (match uu____5688 with
             | (arg_tms,ext_sz) ->
                 let uu____5867 = encode_args arg_tms env  in
                 (match uu____5867 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____5888 -> failwith "Impossible"  in
                      let unary arg_tms2 =
                        let uu____5897 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____5897  in
                      let unary_arith arg_tms2 =
                        let uu____5906 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxInt uu____5906  in
                      let binary arg_tms2 =
                        let uu____5919 =
                          let uu____5920 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5920
                           in
                        let uu____5921 =
                          let uu____5922 =
                            let uu____5923 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____5923  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5922
                           in
                        (uu____5919, uu____5921)  in
                      let binary_arith arg_tms2 =
                        let uu____5938 =
                          let uu____5939 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5939
                           in
                        let uu____5940 =
                          let uu____5941 =
                            let uu____5942 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____5942  in
                          FStar_SMTEncoding_Term.unboxInt uu____5941  in
                        (uu____5938, uu____5940)  in
                      let mk_bv a op mk_args resBox ts =
                        let uu____5984 =
                          let uu____5985 = mk_args ts  in op uu____5985  in
                        FStar_All.pipe_right uu____5984 resBox  in
                      let bv_and =
                        mk_bv ()
                          (fun a421  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvAnd) a421)
                          (fun a422  -> (Obj.magic binary) a422)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_xor =
                        mk_bv ()
                          (fun a423  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvXor) a423)
                          (fun a424  -> (Obj.magic binary) a424)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_or =
                        mk_bv ()
                          (fun a425  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvOr) a425)
                          (fun a426  -> (Obj.magic binary) a426)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_add =
                        mk_bv ()
                          (fun a427  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvAdd) a427)
                          (fun a428  -> (Obj.magic binary) a428)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_sub =
                        mk_bv ()
                          (fun a429  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvSub) a429)
                          (fun a430  -> (Obj.magic binary) a430)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_shl =
                        mk_bv ()
                          (fun a431  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkBvShl sz))
                               a431)
                          (fun a432  -> (Obj.magic binary_arith) a432)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_shr =
                        mk_bv ()
                          (fun a433  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkBvShr sz))
                               a433)
                          (fun a434  -> (Obj.magic binary_arith) a434)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_udiv =
                        mk_bv ()
                          (fun a435  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkBvUdiv sz))
                               a435)
                          (fun a436  -> (Obj.magic binary_arith) a436)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_mod =
                        mk_bv ()
                          (fun a437  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkBvMod sz))
                               a437)
                          (fun a438  -> (Obj.magic binary_arith) a438)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_mul =
                        mk_bv ()
                          (fun a439  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkBvMul sz))
                               a439)
                          (fun a440  -> (Obj.magic binary_arith) a440)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_ult =
                        mk_bv ()
                          (fun a441  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvUlt) a441)
                          (fun a442  -> (Obj.magic binary) a442)
                          FStar_SMTEncoding_Term.boxBool
                         in
                      let bv_uext arg_tms2 =
                        let uu____6049 =
                          let uu____6052 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible"
                             in
                          FStar_SMTEncoding_Util.mkBvUext uu____6052  in
                        let uu____6054 =
                          let uu____6057 =
                            let uu____6058 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible"
                               in
                            sz + uu____6058  in
                          FStar_SMTEncoding_Term.boxBitVec uu____6057  in
                        mk_bv () (fun a443  -> (Obj.magic uu____6049) a443)
                          (fun a444  -> (Obj.magic unary) a444) uu____6054
                          arg_tms2
                         in
                      let to_int1 =
                        mk_bv ()
                          (fun a445  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvToNat)
                               a445) (fun a446  -> (Obj.magic unary) a446)
                          FStar_SMTEncoding_Term.boxInt
                         in
                      let bv_to =
                        mk_bv ()
                          (fun a447  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkNatToBv sz))
                               a447)
                          (fun a448  -> (Obj.magic unary_arith) a448)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let ops =
                        [(FStar_Parser_Const.bv_and_lid, bv_and);
                        (FStar_Parser_Const.bv_xor_lid, bv_xor);
                        (FStar_Parser_Const.bv_or_lid, bv_or);
                        (FStar_Parser_Const.bv_add_lid, bv_add);
                        (FStar_Parser_Const.bv_sub_lid, bv_sub);
                        (FStar_Parser_Const.bv_shift_left_lid, bv_shl);
                        (FStar_Parser_Const.bv_shift_right_lid, bv_shr);
                        (FStar_Parser_Const.bv_udiv_lid, bv_udiv);
                        (FStar_Parser_Const.bv_mod_lid, bv_mod);
                        (FStar_Parser_Const.bv_mul_lid, bv_mul);
                        (FStar_Parser_Const.bv_ult_lid, bv_ult);
                        (FStar_Parser_Const.bv_uext_lid, bv_uext);
                        (FStar_Parser_Const.bv_to_nat_lid, to_int1);
                        (FStar_Parser_Const.nat_to_bv_lid, bv_to)]  in
                      let uu____6257 =
                        let uu____6266 =
                          FStar_List.tryFind
                            (fun uu____6288  ->
                               match uu____6288 with
                               | (l,uu____6298) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops
                           in
                        FStar_All.pipe_right uu____6266 FStar_Util.must  in
                      (match uu____6257 with
                       | (uu____6339,op) ->
                           let uu____6349 = op arg_tms1  in
                           (uu____6349, (FStar_List.append sz_decls decls)))))

and (encode_term :
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____6360 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____6360
       then
         let uu____6361 = FStar_Syntax_Print.tag_of_term t  in
         let uu____6362 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____6363 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____6361 uu____6362
           uu____6363
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____6369 ->
           let uu____6394 =
             let uu____6395 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____6396 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____6397 = FStar_Syntax_Print.term_to_string t0  in
             let uu____6398 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6395
               uu____6396 uu____6397 uu____6398
              in
           failwith uu____6394
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____6403 =
             let uu____6404 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____6405 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____6406 = FStar_Syntax_Print.term_to_string t0  in
             let uu____6407 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6404
               uu____6405 uu____6406 uu____6407
              in
           failwith uu____6403
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____6413 =
             let uu____6414 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____6414
              in
           failwith uu____6413
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____6421) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta
           ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
              FStar_Syntax_Syntax.pos = uu____6462;
              FStar_Syntax_Syntax.vars = uu____6463;_},FStar_Syntax_Syntax.Meta_alien
            (obj,desc,ty))
           ->
           let tsym =
             let uu____6480 = varops.fresh "t"  in
             (uu____6480, FStar_SMTEncoding_Term.Term_sort)  in
           let t1 = FStar_SMTEncoding_Util.mkFreeV tsym  in
           let decl =
             let uu____6483 =
               let uu____6494 =
                 let uu____6497 = FStar_Util.format1 "alien term (%s)" desc
                    in
                 FStar_Pervasives_Native.Some uu____6497  in
               ((FStar_Pervasives_Native.fst tsym), [],
                 FStar_SMTEncoding_Term.Term_sort, uu____6494)
                in
             FStar_SMTEncoding_Term.DeclFun uu____6483  in
           (t1, [decl])
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____6505) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____6515 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name  in
           (uu____6515, [])
       | FStar_Syntax_Syntax.Tm_type uu____6518 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6522) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name  in
           let uu____6547 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____6547 with
            | (binders1,res) ->
                let uu____6558 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____6558
                then
                  let uu____6563 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____6563 with
                   | (vars,guards,env',decls,uu____6588) ->
                       let fsym =
                         let uu____6606 = varops.fresh "f"  in
                         (uu____6606, FStar_SMTEncoding_Term.Term_sort)  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____6609 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___110_6618 = env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___110_6618.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___110_6618.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___110_6618.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___110_6618.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___110_6618.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___110_6618.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___110_6618.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___110_6618.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___110_6618.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___110_6618.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___110_6618.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___110_6618.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___110_6618.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___110_6618.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___110_6618.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___110_6618.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___110_6618.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___110_6618.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___110_6618.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___110_6618.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___110_6618.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___110_6618.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___110_6618.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___110_6618.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___110_6618.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___110_6618.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___110_6618.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___110_6618.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___110_6618.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___110_6618.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___110_6618.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___110_6618.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___110_6618.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___110_6618.FStar_TypeChecker_Env.dep_graph)
                            }) res
                          in
                       (match uu____6609 with
                        | (pre_opt,res_t) ->
                            let uu____6629 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____6629 with
                             | (res_pred,decls') ->
                                 let uu____6640 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____6653 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____6653, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____6657 =
                                         encode_formula pre env'  in
                                       (match uu____6657 with
                                        | (guard,decls0) ->
                                            let uu____6670 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____6670, decls0))
                                    in
                                 (match uu____6640 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____6682 =
                                          let uu____6693 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____6693)  in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____6682
                                         in
                                      let cvars =
                                        let uu____6711 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____6711
                                          (FStar_List.filter
                                             (fun uu____6725  ->
                                                match uu____6725 with
                                                | (x,uu____6731) ->
                                                    x <>
                                                      (FStar_Pervasives_Native.fst
                                                         fsym)))
                                         in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp)
                                         in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey
                                         in
                                      let uu____6750 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash
                                         in
                                      (match uu____6750 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____6758 =
                                             let uu____6759 =
                                               let uu____6766 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV)
                                                  in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____6766)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6759
                                              in
                                           (uu____6758,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____6786 =
                                               let uu____6787 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____6787
                                                in
                                             varops.mk_unique uu____6786  in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars
                                              in
                                           let caption =
                                             let uu____6798 =
                                               FStar_Options.log_queries ()
                                                in
                                             if uu____6798
                                             then
                                               let uu____6801 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____6801
                                             else
                                               FStar_Pervasives_Native.None
                                              in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption)
                                              in
                                           let t1 =
                                             let uu____6809 =
                                               let uu____6816 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars
                                                  in
                                               (tsym, uu____6816)  in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6809
                                              in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type
                                              in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym
                                                in
                                             let uu____6828 =
                                               let uu____6835 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind)
                                                  in
                                               (uu____6835,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name)
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6828
                                              in
                                           let f_has_t =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               f t1
                                              in
                                           let f_has_t_z =
                                             FStar_SMTEncoding_Term.mk_HasTypeZ
                                               f t1
                                              in
                                           let pre_typing =
                                             let a_name =
                                               Prims.strcat "pre_typing_"
                                                 tsym
                                                in
                                             let uu____6856 =
                                               let uu____6863 =
                                                 let uu____6864 =
                                                   let uu____6875 =
                                                     let uu____6876 =
                                                       let uu____6881 =
                                                         let uu____6882 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f
                                                            in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____6882
                                                          in
                                                       (f_has_t, uu____6881)
                                                        in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____6876
                                                      in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____6875)
                                                    in
                                                 mkForall_fuel uu____6864  in
                                               (uu____6863,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6856
                                              in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym
                                                in
                                             let uu____6905 =
                                               let uu____6912 =
                                                 let uu____6913 =
                                                   let uu____6924 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp)
                                                      in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____6924)
                                                    in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____6913
                                                  in
                                               (uu____6912,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6905
                                              in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1]))
                                              in
                                           ((let uu____6949 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls
                                                in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____6949);
                                            (t1, t_decls)))))))
                else
                  (let tsym = varops.fresh "Non_total_Tm_arrow"  in
                   let tdecl =
                     FStar_SMTEncoding_Term.DeclFun
                       (tsym, [], FStar_SMTEncoding_Term.Term_sort,
                         FStar_Pervasives_Native.None)
                      in
                   let t1 = FStar_SMTEncoding_Util.mkApp (tsym, [])  in
                   let t_kinding =
                     let a_name =
                       Prims.strcat "non_total_function_typing_" tsym  in
                     let uu____6964 =
                       let uu____6971 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____6971,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____6964  in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)  in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym  in
                     let uu____6983 =
                       let uu____6990 =
                         let uu____6991 =
                           let uu____7002 =
                             let uu____7003 =
                               let uu____7008 =
                                 let uu____7009 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____7009
                                  in
                               (f_has_t, uu____7008)  in
                             FStar_SMTEncoding_Util.mkImp uu____7003  in
                           ([[f_has_t]], [fsym], uu____7002)  in
                         mkForall_fuel uu____6991  in
                       (uu____6990, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____6983  in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____7036 ->
           let uu____7043 =
             let uu____7048 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.Weak;
                 FStar_TypeChecker_Normalize.HNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0
                in
             match uu____7048 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____7055;
                 FStar_Syntax_Syntax.vars = uu____7056;_} ->
                 let uu____7063 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____7063 with
                  | (b,f1) ->
                      let uu____7088 =
                        let uu____7089 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____7089  in
                      (uu____7088, f1))
             | uu____7098 -> failwith "impossible"  in
           (match uu____7043 with
            | (x,f) ->
                let uu____7109 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____7109 with
                 | (base_t,decls) ->
                     let uu____7120 = gen_term_var env x  in
                     (match uu____7120 with
                      | (x1,xtm,env') ->
                          let uu____7134 = encode_formula f env'  in
                          (match uu____7134 with
                           | (refinement,decls') ->
                               let uu____7145 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____7145 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t
                                       in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement)
                                       in
                                    let cvars =
                                      let uu____7161 =
                                        let uu____7164 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____7171 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____7164
                                          uu____7171
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____7161
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____7204  ->
                                              match uu____7204 with
                                              | (y,uu____7210) ->
                                                  (y <> x1) && (y <> fsym)))
                                       in
                                    let xfv =
                                      (x1, FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    let ffv =
                                      (fsym,
                                        FStar_SMTEncoding_Term.Fuel_sort)
                                       in
                                    let tkey =
                                      FStar_SMTEncoding_Util.mkForall
                                        ([], (ffv :: xfv :: cvars1),
                                          encoding)
                                       in
                                    let tkey_hash =
                                      FStar_SMTEncoding_Term.hash_of_term
                                        tkey
                                       in
                                    let uu____7243 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash
                                       in
                                    (match uu____7243 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____7251 =
                                           let uu____7252 =
                                             let uu____7259 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV)
                                                in
                                             ((cache_entry.cache_symbol_name),
                                               uu____7259)
                                              in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____7252
                                            in
                                         (uu____7251,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name  in
                                         let tsym =
                                           let uu____7280 =
                                             let uu____7281 =
                                               let uu____7282 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____7282
                                                in
                                             Prims.strcat module_name
                                               uu____7281
                                              in
                                           varops.mk_unique uu____7280  in
                                         let cvar_sorts =
                                           FStar_List.map
                                             FStar_Pervasives_Native.snd
                                             cvars1
                                            in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None)
                                            in
                                         let t1 =
                                           let uu____7296 =
                                             let uu____7303 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1
                                                in
                                             (tsym, uu____7303)  in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____7296
                                            in
                                         let x_has_base_t =
                                           FStar_SMTEncoding_Term.mk_HasType
                                             xtm base_t
                                            in
                                         let x_has_t =
                                           FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                             (FStar_Pervasives_Native.Some
                                                fterm) xtm t1
                                            in
                                         let t_has_kind =
                                           FStar_SMTEncoding_Term.mk_HasType
                                             t1
                                             FStar_SMTEncoding_Term.mk_Term_type
                                            in
                                         let t_haseq_base =
                                           FStar_SMTEncoding_Term.mk_haseq
                                             base_t
                                            in
                                         let t_haseq_ref =
                                           FStar_SMTEncoding_Term.mk_haseq t1
                                            in
                                         let t_haseq1 =
                                           let uu____7318 =
                                             let uu____7325 =
                                               let uu____7326 =
                                                 let uu____7337 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base)
                                                    in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____7337)
                                                  in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7326
                                                in
                                             (uu____7325,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7318
                                            in
                                         let t_kinding =
                                           let uu____7355 =
                                             let uu____7362 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind)
                                                in
                                             (uu____7362,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7355
                                            in
                                         let t_interp =
                                           let uu____7380 =
                                             let uu____7387 =
                                               let uu____7388 =
                                                 let uu____7399 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding)
                                                    in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____7399)
                                                  in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7388
                                                in
                                             let uu____7422 =
                                               let uu____7425 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____7425
                                                in
                                             (uu____7387, uu____7422,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7380
                                            in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1])
                                            in
                                         ((let uu____7432 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls
                                              in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____7432);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____7462 = FStar_Syntax_Unionfind.uvar_id uv  in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____7462  in
           let uu____7463 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm  in
           (match uu____7463 with
            | (t_has_k,decls) ->
                let d =
                  let uu____7475 =
                    let uu____7482 =
                      let uu____7483 =
                        let uu____7484 =
                          let uu____7485 = FStar_Syntax_Unionfind.uvar_id uv
                             in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____7485
                           in
                        FStar_Util.format1 "uvar_typing_%s" uu____7484  in
                      varops.mk_unique uu____7483  in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____7482)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____7475  in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____7490 ->
           let uu____7505 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____7505 with
            | (head1,args_e) ->
                let uu____7546 =
                  let uu____7559 =
                    let uu____7560 = FStar_Syntax_Subst.compress head1  in
                    uu____7560.FStar_Syntax_Syntax.n  in
                  (uu____7559, args_e)  in
                (match uu____7546 with
                 | uu____7575 when head_redex env head1 ->
                     let uu____7588 = whnf env t  in
                     encode_term uu____7588 env
                 | uu____7589 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____7608 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____7622;
                       FStar_Syntax_Syntax.vars = uu____7623;_},uu____7624),uu____7625::
                    (v1,uu____7627)::(v2,uu____7629)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7680 = encode_term v1 env  in
                     (match uu____7680 with
                      | (v11,decls1) ->
                          let uu____7691 = encode_term v2 env  in
                          (match uu____7691 with
                           | (v21,decls2) ->
                               let uu____7702 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21
                                  in
                               (uu____7702,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____7706::(v1,uu____7708)::(v2,uu____7710)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7757 = encode_term v1 env  in
                     (match uu____7757 with
                      | (v11,decls1) ->
                          let uu____7768 = encode_term v2 env  in
                          (match uu____7768 with
                           | (v21,decls2) ->
                               let uu____7779 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21
                                  in
                               (uu____7779,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____7783)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(arg,uu____7809)::(rng,uu____7811)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____7846) ->
                     let e0 =
                       let uu____7864 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____7864
                        in
                     ((let uu____7872 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____7872
                       then
                         let uu____7873 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____7873
                       else ());
                      (let e =
                         let uu____7878 =
                           let uu____7879 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____7880 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____7879
                             uu____7880
                            in
                         uu____7878 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos
                          in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____7889),(arg,uu____7891)::[]) -> encode_term arg env
                 | uu____7916 ->
                     let uu____7929 = encode_args args_e env  in
                     (match uu____7929 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____7984 = encode_term head1 env  in
                            match uu____7984 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____8048 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____8048 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____8126  ->
                                                 fun uu____8127  ->
                                                   match (uu____8126,
                                                           uu____8127)
                                                   with
                                                   | ((bv,uu____8149),
                                                      (a,uu____8151)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____8169 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____8169
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____8174 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm
                                             in
                                          (match uu____8174 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type
                                                  in
                                               let e_typing =
                                                 let uu____8189 =
                                                   let uu____8196 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____8205 =
                                                     let uu____8206 =
                                                       let uu____8207 =
                                                         let uu____8208 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm
                                                            in
                                                         FStar_Util.digest_of_string
                                                           uu____8208
                                                          in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____8207
                                                        in
                                                     varops.mk_unique
                                                       uu____8206
                                                      in
                                                   (uu____8196,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____8205)
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____8189
                                                  in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing])))))))
                             in
                          let encode_full_app fv =
                            let uu____8225 = lookup_free_var_sym env fv  in
                            match uu____8225 with
                            | (fname,fuel_args) ->
                                let tm =
                                  FStar_SMTEncoding_Util.mkApp'
                                    (fname,
                                      (FStar_List.append fuel_args args))
                                   in
                                (tm, decls)
                             in
                          let head2 = FStar_Syntax_Subst.compress head1  in
                          let head_type =
                            match head2.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_uinst
                                ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_name x;
                                   FStar_Syntax_Syntax.pos = uu____8256;
                                   FStar_Syntax_Syntax.vars = uu____8257;_},uu____8258)
                                ->
                                FStar_Pervasives_Native.Some
                                  (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_name x ->
                                FStar_Pervasives_Native.Some
                                  (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_uinst
                                ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_fvar fv;
                                   FStar_Syntax_Syntax.pos = uu____8269;
                                   FStar_Syntax_Syntax.vars = uu____8270;_},uu____8271)
                                ->
                                let uu____8276 =
                                  let uu____8277 =
                                    let uu____8282 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____8282
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____8277
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____8276
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____8312 =
                                  let uu____8313 =
                                    let uu____8318 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____8318
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____8313
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____8312
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8347,(FStar_Util.Inl t1,uu____8349),uu____8350)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8399,(FStar_Util.Inr c,uu____8401),uu____8402)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____8451 -> FStar_Pervasives_Native.None  in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____8478 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.Weak;
                                     FStar_TypeChecker_Normalize.HNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____8478
                                  in
                               let uu____8479 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____8479 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____8495;
                                            FStar_Syntax_Syntax.vars =
                                              uu____8496;_},uu____8497)
                                         when
                                         (FStar_List.length formals) =
                                           (FStar_List.length args)
                                         ->
                                         encode_full_app
                                           fv.FStar_Syntax_Syntax.fv_name
                                     | FStar_Syntax_Syntax.Tm_fvar fv when
                                         (FStar_List.length formals) =
                                           (FStar_List.length args)
                                         ->
                                         encode_full_app
                                           fv.FStar_Syntax_Syntax.fv_name
                                     | uu____8511 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (FStar_Pervasives_Native.Some
                                                (formals, c))
                                         else
                                           encode_partial_app
                                             FStar_Pervasives_Native.None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____8560 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____8560 with
            | (bs1,body1,opening) ->
                let fallback uu____8583 =
                  let f = varops.fresh "Tm_abs"  in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding"))
                     in
                  let uu____8590 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort)
                     in
                  (uu____8590, [decl])  in
                let is_impure rc =
                  let uu____8597 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____8597 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____8607 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_All.pipe_right uu____8607
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1  in
                  if
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                  then
                    let uu____8627 = FStar_Syntax_Syntax.mk_Total res_typ  in
                    FStar_Pervasives_Native.Some uu____8627
                  else
                    if
                      FStar_Ident.lid_equals
                        rc.FStar_Syntax_Syntax.residual_effect
                        FStar_Parser_Const.effect_GTot_lid
                    then
                      (let uu____8631 = FStar_Syntax_Syntax.mk_GTotal res_typ
                          in
                       FStar_Pervasives_Native.Some uu____8631)
                    else FStar_Pervasives_Native.None
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____8638 =
                         let uu____8643 =
                           let uu____8644 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____8644
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____8643)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____8638);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____8646 =
                       (is_impure rc) &&
                         (let uu____8648 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc
                             in
                          Prims.op_Negation uu____8648)
                        in
                     if uu____8646
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache  in
                        let uu____8655 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____8655 with
                        | (vars,guards,envbody,decls,uu____8680) ->
                            let body2 =
                              let uu____8694 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  rc
                                 in
                              if uu____8694
                              then
                                FStar_TypeChecker_Util.reify_body env.tcenv
                                  body1
                              else body1  in
                            let uu____8696 = encode_term body2 envbody  in
                            (match uu____8696 with
                             | (body3,decls') ->
                                 let uu____8707 =
                                   let uu____8716 = codomain_eff rc  in
                                   match uu____8716 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____8735 = encode_term tfun env
                                          in
                                       (match uu____8735 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1))
                                    in
                                 (match uu____8707 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____8767 =
                                          let uu____8778 =
                                            let uu____8779 =
                                              let uu____8784 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____8784, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8779
                                             in
                                          ([], vars, uu____8778)  in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____8767
                                         in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body
                                         in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            cvars
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____8796 =
                                              let uu____8799 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1
                                                 in
                                              FStar_List.append uu____8799
                                                cvars
                                               in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____8796
                                         in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body)
                                         in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey
                                         in
                                      let uu____8818 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash
                                         in
                                      (match uu____8818 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____8826 =
                                             let uu____8827 =
                                               let uu____8834 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1
                                                  in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____8834)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____8827
                                              in
                                           (uu____8826,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____8845 =
                                             is_an_eta_expansion env vars
                                               body3
                                              in
                                           (match uu____8845 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____8856 =
                                                    let uu____8857 =
                                                      FStar_Util.smap_size
                                                        env.cache
                                                       in
                                                    uu____8857 = cache_size
                                                     in
                                                  if uu____8856
                                                  then []
                                                  else
                                                    FStar_List.append decls
                                                      (FStar_List.append
                                                         decls' decls'')
                                                   in
                                                (t1, decls1)
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                let cvar_sorts =
                                                  FStar_List.map
                                                    FStar_Pervasives_Native.snd
                                                    cvars1
                                                   in
                                                let fsym =
                                                  let module_name =
                                                    env.current_module_name
                                                     in
                                                  let fsym =
                                                    let uu____8873 =
                                                      let uu____8874 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash
                                                         in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____8874
                                                       in
                                                    varops.mk_unique
                                                      uu____8873
                                                     in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym)
                                                   in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None)
                                                   in
                                                let f =
                                                  let uu____8881 =
                                                    let uu____8888 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1
                                                       in
                                                    (fsym, uu____8888)  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____8881
                                                   in
                                                let app = mk_Apply f vars  in
                                                let typing_f =
                                                  match arrow_t_opt with
                                                  | FStar_Pervasives_Native.None
                                                       -> []
                                                  | FStar_Pervasives_Native.Some
                                                      t1 ->
                                                      let f_has_t =
                                                        FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                          FStar_Pervasives_Native.None
                                                          f t1
                                                         in
                                                      let a_name =
                                                        Prims.strcat
                                                          "typing_" fsym
                                                         in
                                                      let uu____8906 =
                                                        let uu____8907 =
                                                          let uu____8914 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t)
                                                             in
                                                          (uu____8914,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name)
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8907
                                                         in
                                                      [uu____8906]
                                                   in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym
                                                     in
                                                  let uu____8927 =
                                                    let uu____8934 =
                                                      let uu____8935 =
                                                        let uu____8946 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3)
                                                           in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____8946)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____8935
                                                       in
                                                    (uu____8934,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____8927
                                                   in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f])))
                                                   in
                                                ((let uu____8963 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls
                                                     in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____8963);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8966,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____8967;
                          FStar_Syntax_Syntax.lbunivs = uu____8968;
                          FStar_Syntax_Syntax.lbtyp = uu____8969;
                          FStar_Syntax_Syntax.lbeff = uu____8970;
                          FStar_Syntax_Syntax.lbdef = uu____8971;_}::uu____8972),uu____8973)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____8999;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____9001;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____9022 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions, and their enclosings let bindings (including the top-level let) are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            FStar_Exn.raise Inner_let_rec)
       | FStar_Syntax_Syntax.Tm_match (e,pats) ->
           encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env
             encode_term)

and (encode_let :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          env_t ->
            (FStar_Syntax_Syntax.term ->
               env_t ->
                 (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
                   FStar_Pervasives_Native.tuple2)
              ->
              (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
                FStar_Pervasives_Native.tuple2)
  =
  fun x  ->
    fun t1  ->
      fun e1  ->
        fun e2  ->
          fun env  ->
            fun encode_body  ->
              let uu____9092 = encode_term e1 env  in
              match uu____9092 with
              | (ee1,decls1) ->
                  let uu____9103 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____9103 with
                   | (xs,e21) ->
                       let uu____9128 = FStar_List.hd xs  in
                       (match uu____9128 with
                        | (x1,uu____9142) ->
                            let env' = push_term_var env x1 ee1  in
                            let uu____9144 = encode_body e21 env'  in
                            (match uu____9144 with
                             | (ee2,decls2) ->
                                 (ee2, (FStar_List.append decls1 decls2)))))

and (encode_match :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.branch Prims.list ->
      FStar_SMTEncoding_Term.term ->
        env_t ->
          (FStar_Syntax_Syntax.term ->
             env_t ->
               (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
                 FStar_Pervasives_Native.tuple2)
            ->
            (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
              FStar_Pervasives_Native.tuple2)
  =
  fun e  ->
    fun pats  ->
      fun default_case  ->
        fun env  ->
          fun encode_br  ->
            let uu____9176 =
              let uu____9183 =
                let uu____9184 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____9184  in
              gen_term_var env uu____9183  in
            match uu____9176 with
            | (scrsym,scr',env1) ->
                let uu____9192 = encode_term e env1  in
                (match uu____9192 with
                 | (scr,decls) ->
                     let uu____9203 =
                       let encode_branch b uu____9228 =
                         match uu____9228 with
                         | (else_case,decls1) ->
                             let uu____9247 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____9247 with
                              | (p,w,br) ->
                                  let uu____9273 = encode_pat env1 p  in
                                  (match uu____9273 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____9310  ->
                                                   match uu____9310 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1)
                                          in
                                       let uu____9317 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____9339 =
                                               encode_term w1 env2  in
                                             (match uu____9339 with
                                              | (w2,decls2) ->
                                                  let uu____9352 =
                                                    let uu____9353 =
                                                      let uu____9358 =
                                                        let uu____9359 =
                                                          let uu____9364 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____9364)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____9359
                                                         in
                                                      (guard, uu____9358)  in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____9353
                                                     in
                                                  (uu____9352, decls2))
                                          in
                                       (match uu____9317 with
                                        | (guard1,decls2) ->
                                            let uu____9377 =
                                              encode_br br env2  in
                                            (match uu____9377 with
                                             | (br1,decls3) ->
                                                 let uu____9390 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____9390,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____9203 with
                      | (match_tm,decls1) ->
                          let uu____9409 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange
                             in
                          (uu____9409, decls1)))

and (encode_pat :
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun pat  ->
      (let uu____9449 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
       if uu____9449
       then
         let uu____9450 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____9450
       else ());
      (let uu____9452 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____9452 with
       | (vars,pat_term) ->
           let uu____9469 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____9522  ->
                     fun v1  ->
                       match uu____9522 with
                       | (env1,vars1) ->
                           let uu____9574 = gen_term_var env1 v1  in
                           (match uu____9574 with
                            | (xx,uu____9596,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, []))
              in
           (match uu____9469 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9675 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9676 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9677 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9685 = encode_const c env1  in
                      (match uu____9685 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____9699::uu____9700 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____9703 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____9726 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name
                           in
                        match uu____9726 with
                        | (uu____9733,uu____9734::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9737 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9770  ->
                                  match uu____9770 with
                                  | (arg,uu____9778) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____9784 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____9784))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9811) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9842 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9865 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9909  ->
                                  match uu____9909 with
                                  | (arg,uu____9923) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____9929 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____9929))
                         in
                      FStar_All.pipe_right uu____9865 FStar_List.flatten
                   in
                let pat_term1 uu____9957 = encode_term pat_term env1  in
                let pattern =
                  {
                    pat_vars = vars1;
                    pat_term = pat_term1;
                    guard = (mk_guard pat);
                    projections = (mk_projections pat)
                  }  in
                (env1, pattern)))

and (encode_args :
  FStar_Syntax_Syntax.args ->
    env_t ->
      (FStar_SMTEncoding_Term.term Prims.list,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun l  ->
    fun env  ->
      let uu____9967 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____10005  ->
                fun uu____10006  ->
                  match (uu____10005, uu____10006) with
                  | ((tms,decls),(t,uu____10042)) ->
                      let uu____10063 = encode_term t env  in
                      (match uu____10063 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____9967 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____10120 = FStar_Syntax_Util.list_elements e  in
        match uu____10120 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____10141 =
          let uu____10156 = FStar_Syntax_Util.unmeta p  in
          FStar_All.pipe_right uu____10156 FStar_Syntax_Util.head_and_args
           in
        match uu____10141 with
        | (head1,args) ->
            let uu____10195 =
              let uu____10208 =
                let uu____10209 = FStar_Syntax_Util.un_uinst head1  in
                uu____10209.FStar_Syntax_Syntax.n  in
              (uu____10208, args)  in
            (match uu____10195 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____10223,uu____10224)::(e,uu____10226)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____10261 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or1 t1 =
          let uu____10297 =
            let uu____10312 = FStar_Syntax_Util.unmeta t1  in
            FStar_All.pipe_right uu____10312 FStar_Syntax_Util.head_and_args
             in
          match uu____10297 with
          | (head1,args) ->
              let uu____10353 =
                let uu____10366 =
                  let uu____10367 = FStar_Syntax_Util.un_uinst head1  in
                  uu____10367.FStar_Syntax_Syntax.n  in
                (uu____10366, args)  in
              (match uu____10353 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____10384)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____10411 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____10433 = smt_pat_or1 t1  in
            (match uu____10433 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____10449 = list_elements1 e  in
                 FStar_All.pipe_right uu____10449
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____10467 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____10467
                           (FStar_List.map one_pat)))
             | uu____10478 ->
                 let uu____10483 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____10483])
        | uu____10504 ->
            let uu____10507 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____10507]
         in
      let uu____10528 =
        let uu____10547 =
          let uu____10548 = FStar_Syntax_Subst.compress t  in
          uu____10548.FStar_Syntax_Syntax.n  in
        match uu____10547 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____10587 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____10587 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____10630;
                        FStar_Syntax_Syntax.effect_name = uu____10631;
                        FStar_Syntax_Syntax.result_typ = uu____10632;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____10634)::(post,uu____10636)::(pats,uu____10638)::[];
                        FStar_Syntax_Syntax.flags = uu____10639;_}
                      ->
                      let uu____10680 = lemma_pats pats  in
                      (binders1, pre, post, uu____10680)
                  | uu____10697 -> failwith "impos"))
        | uu____10716 -> failwith "Impos"  in
      match uu____10528 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___111_10764 = env  in
            {
              bindings = (uu___111_10764.bindings);
              depth = (uu___111_10764.depth);
              tcenv = (uu___111_10764.tcenv);
              warn = (uu___111_10764.warn);
              cache = (uu___111_10764.cache);
              nolabels = (uu___111_10764.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___111_10764.encode_non_total_function_typ);
              current_module_name = (uu___111_10764.current_module_name)
            }  in
          let uu____10765 =
            encode_binders FStar_Pervasives_Native.None binders env1  in
          (match uu____10765 with
           | (vars,guards,env2,decls,uu____10790) ->
               let uu____10803 =
                 let uu____10818 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____10872 =
                             let uu____10883 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_smt_pattern t1 env2))
                                in
                             FStar_All.pipe_right uu____10883
                               FStar_List.unzip
                              in
                           match uu____10872 with
                           | (pats,decls1) -> (pats, decls1)))
                    in
                 FStar_All.pipe_right uu____10818 FStar_List.unzip  in
               (match uu____10803 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls'  in
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
                    let env3 =
                      let uu___112_11035 = env2  in
                      {
                        bindings = (uu___112_11035.bindings);
                        depth = (uu___112_11035.depth);
                        tcenv = (uu___112_11035.tcenv);
                        warn = (uu___112_11035.warn);
                        cache = (uu___112_11035.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___112_11035.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___112_11035.encode_non_total_function_typ);
                        current_module_name =
                          (uu___112_11035.current_module_name)
                      }  in
                    let uu____11036 =
                      let uu____11041 = FStar_Syntax_Util.unmeta pre  in
                      encode_formula uu____11041 env3  in
                    (match uu____11036 with
                     | (pre1,decls'') ->
                         let uu____11048 =
                           let uu____11053 = FStar_Syntax_Util.unmeta post1
                              in
                           encode_formula uu____11053 env3  in
                         (match uu____11048 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls'''))
                                 in
                              let uu____11063 =
                                let uu____11064 =
                                  let uu____11075 =
                                    let uu____11076 =
                                      let uu____11081 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards)
                                         in
                                      (uu____11081, post2)  in
                                    FStar_SMTEncoding_Util.mkImp uu____11076
                                     in
                                  (pats, vars, uu____11075)  in
                                FStar_SMTEncoding_Util.mkForall uu____11064
                                 in
                              (uu____11063, decls1)))))

and (encode_smt_pattern :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    env_t ->
      (FStar_SMTEncoding_Term.pat,FStar_SMTEncoding_Term.decl Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let uu____11094 = FStar_Syntax_Util.head_and_args t  in
      match uu____11094 with
      | (head1,args) ->
          let head2 = FStar_Syntax_Util.un_uinst head1  in
          (match ((head2.FStar_Syntax_Syntax.n), args) with
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,uu____11153::(x,uu____11155)::(t1,uu____11157)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.has_type_lid
               ->
               let uu____11204 = encode_term x env  in
               (match uu____11204 with
                | (x1,decls) ->
                    let uu____11217 = encode_term t1 env  in
                    (match uu____11217 with
                     | (t2,decls') ->
                         let uu____11230 =
                           FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                         (uu____11230, (FStar_List.append decls decls'))))
           | uu____11233 -> encode_term t env)

and (encode_formula :
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____11256 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____11256
        then
          let uu____11257 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____11258 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____11257 uu____11258
        else ()  in
      let enc f r l =
        let uu____11291 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____11319 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____11319 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____11291 with
        | (decls,args) ->
            let uu____11348 =
              let uu___113_11349 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___113_11349.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___113_11349.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____11348, decls)
         in
      let const_op f r uu____11380 =
        let uu____11393 = f r  in (uu____11393, [])  in
      let un_op f l =
        let uu____11412 = FStar_List.hd l  in
        FStar_All.pipe_left f uu____11412  in
      let bin_op f uu___87_11428 =
        match uu___87_11428 with
        | t1::t2::[] -> f (t1, t2)
        | uu____11439 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____11473 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____11496  ->
                 match uu____11496 with
                 | (t,uu____11510) ->
                     let uu____11511 = encode_formula t env  in
                     (match uu____11511 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____11473 with
        | (decls,phis) ->
            let uu____11540 =
              let uu___114_11541 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___114_11541.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___114_11541.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____11540, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____11602  ->
               match uu____11602 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____11621) -> false
                    | uu____11622 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____11637 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____11637
        else
          (let uu____11651 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____11651 r rf)
         in
      let mk_imp1 r uu___88_11676 =
        match uu___88_11676 with
        | (lhs,uu____11682)::(rhs,uu____11684)::[] ->
            let uu____11711 = encode_formula rhs env  in
            (match uu____11711 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11726) ->
                      (l1, decls1)
                  | uu____11731 ->
                      let uu____11732 = encode_formula lhs env  in
                      (match uu____11732 with
                       | (l2,decls2) ->
                           let uu____11743 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____11743, (FStar_List.append decls1 decls2)))))
        | uu____11746 -> failwith "impossible"  in
      let mk_ite r uu___89_11767 =
        match uu___89_11767 with
        | (guard,uu____11773)::(_then,uu____11775)::(_else,uu____11777)::[]
            ->
            let uu____11814 = encode_formula guard env  in
            (match uu____11814 with
             | (g,decls1) ->
                 let uu____11825 = encode_formula _then env  in
                 (match uu____11825 with
                  | (t,decls2) ->
                      let uu____11836 = encode_formula _else env  in
                      (match uu____11836 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11850 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____11875 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l
           in
        f uu____11875  in
      let connectives =
        let uu____11893 =
          let uu____11906 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____11906)  in
        let uu____11923 =
          let uu____11938 =
            let uu____11951 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____11951)  in
          let uu____11968 =
            let uu____11983 =
              let uu____11998 =
                let uu____12011 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____12011)  in
              let uu____12028 =
                let uu____12043 =
                  let uu____12058 =
                    let uu____12071 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____12071)  in
                  [uu____12058;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____12043  in
              uu____11998 :: uu____12028  in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11983  in
          uu____11938 :: uu____11968  in
        uu____11893 :: uu____11923  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____12392 = encode_formula phi' env  in
            (match uu____12392 with
             | (phi2,decls) ->
                 let uu____12403 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____12403, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____12404 ->
            let uu____12411 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____12411 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____12450 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____12450 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____12462;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____12464;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____12485 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____12485 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____12532::(x,uu____12534)::(t,uu____12536)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12583 = encode_term x env  in
                 (match uu____12583 with
                  | (x1,decls) ->
                      let uu____12594 = encode_term t env  in
                      (match uu____12594 with
                       | (t1,decls') ->
                           let uu____12605 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____12605, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12610)::(msg,uu____12612)::(phi2,uu____12614)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12659 =
                   let uu____12664 =
                     let uu____12665 = FStar_Syntax_Subst.compress r  in
                     uu____12665.FStar_Syntax_Syntax.n  in
                   let uu____12668 =
                     let uu____12669 = FStar_Syntax_Subst.compress msg  in
                     uu____12669.FStar_Syntax_Syntax.n  in
                   (uu____12664, uu____12668)  in
                 (match uu____12659 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12678))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | uu____12684 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____12691)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____12716 when head_redex env head2 ->
                 let uu____12729 = whnf env phi1  in
                 encode_formula uu____12729 env
             | uu____12730 ->
                 let uu____12743 = encode_term phi1 env  in
                 (match uu____12743 with
                  | (tt,decls) ->
                      let uu____12754 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___115_12757 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___115_12757.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___115_12757.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      (uu____12754, decls)))
        | uu____12758 ->
            let uu____12759 = encode_term phi1 env  in
            (match uu____12759 with
             | (tt,decls) ->
                 let uu____12770 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___116_12773 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___116_12773.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___116_12773.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 (uu____12770, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____12809 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____12809 with
        | (vars,guards,env2,decls,uu____12848) ->
            let uu____12861 =
              let uu____12874 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____12926 =
                          let uu____12937 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____12977  ->
                                    match uu____12977 with
                                    | (t,uu____12991) ->
                                        encode_smt_pattern t
                                          (let uu___117_12997 = env2  in
                                           {
                                             bindings =
                                               (uu___117_12997.bindings);
                                             depth = (uu___117_12997.depth);
                                             tcenv = (uu___117_12997.tcenv);
                                             warn = (uu___117_12997.warn);
                                             cache = (uu___117_12997.cache);
                                             nolabels =
                                               (uu___117_12997.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___117_12997.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___117_12997.current_module_name)
                                           })))
                             in
                          FStar_All.pipe_right uu____12937 FStar_List.unzip
                           in
                        match uu____12926 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1))))
                 in
              FStar_All.pipe_right uu____12874 FStar_List.unzip  in
            (match uu____12861 with
             | (pats,decls') ->
                 let uu____13106 = encode_formula body env2  in
                 (match uu____13106 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____13138;
                             FStar_SMTEncoding_Term.rng = uu____13139;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____13154 -> guards  in
                      let uu____13159 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____13159, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls'')))))
         in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi  in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____13219  ->
                   match uu____13219 with
                   | (x,uu____13225) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x))
            in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____13233 = FStar_Syntax_Free.names hd1  in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____13245 = FStar_Syntax_Free.names x  in
                      FStar_Util.set_union out uu____13245) uu____13233 tl1
                in
             let uu____13248 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____13275  ->
                       match uu____13275 with
                       | (b,uu____13281) ->
                           let uu____13282 = FStar_Util.set_mem b pat_vars
                              in
                           Prims.op_Negation uu____13282))
                in
             (match uu____13248 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____13288) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1
                     in
                  let uu____13302 =
                    let uu____13307 =
                      let uu____13308 = FStar_Syntax_Print.bv_to_string x  in
                      FStar_Util.format1
                        "SMT pattern misses at least one bound variable: %s"
                        uu____13308
                       in
                    (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                      uu____13307)
                     in
                  FStar_Errors.log_issue pos uu____13302)
          in
       let uu____13309 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____13309 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____13318 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____13376  ->
                     match uu____13376 with
                     | (l,uu____13390) -> FStar_Ident.lid_equals op l))
              in
           (match uu____13318 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____13423,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____13463 = encode_q_body env vars pats body  in
             match uu____13463 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____13508 =
                     let uu____13519 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____13519)  in
                   FStar_SMTEncoding_Term.mkForall uu____13508
                     phi1.FStar_Syntax_Syntax.pos
                    in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____13538 = encode_q_body env vars pats body  in
             match uu____13538 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____13582 =
                   let uu____13583 =
                     let uu____13594 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____13594)  in
                   FStar_SMTEncoding_Term.mkExists uu____13583
                     phi1.FStar_Syntax_Syntax.pos
                    in
                 (uu____13582, decls))))

type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple2
    ;
  is: FStar_Ident.lident -> Prims.bool }[@@deriving show]
let (__proj__Mkprims_t__item__mk :
  prims_t ->
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple2)
  =
  fun projectee  ->
    match projectee with
    | { mk = __fname__mk; is = __fname__is;_} -> __fname__mk
  
let (__proj__Mkprims_t__item__is :
  prims_t -> FStar_Ident.lident -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { mk = __fname__mk; is = __fname__is;_} -> __fname__is
  
let (prims : prims_t) =
  let uu____13687 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort  in
  match uu____13687 with
  | (asym,a) ->
      let uu____13694 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
      (match uu____13694 with
       | (xsym,x) ->
           let uu____13701 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____13701 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____13745 =
                      let uu____13756 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd)
                         in
                      (x1, uu____13756, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____13745  in
                  let xtok = Prims.strcat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                     in
                  let xapp =
                    let uu____13782 =
                      let uu____13789 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____13789)  in
                    FStar_SMTEncoding_Util.mkApp uu____13782  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app = mk_Apply xtok1 vars  in
                  let uu____13802 =
                    let uu____13805 =
                      let uu____13808 =
                        let uu____13811 =
                          let uu____13812 =
                            let uu____13819 =
                              let uu____13820 =
                                let uu____13831 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____13831)  in
                              FStar_SMTEncoding_Util.mkForall uu____13820  in
                            (uu____13819, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____13812  in
                        let uu____13848 =
                          let uu____13851 =
                            let uu____13852 =
                              let uu____13859 =
                                let uu____13860 =
                                  let uu____13871 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____13871)  in
                                FStar_SMTEncoding_Util.mkForall uu____13860
                                 in
                              (uu____13859,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____13852  in
                          [uu____13851]  in
                        uu____13811 :: uu____13848  in
                      xtok_decl :: uu____13808  in
                    xname_decl :: uu____13805  in
                  (xtok1, uu____13802)  in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)]  in
                let prims1 =
                  let uu____13962 =
                    let uu____13975 =
                      let uu____13984 =
                        let uu____13985 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____13985
                         in
                      quant axy uu____13984  in
                    (FStar_Parser_Const.op_Eq, uu____13975)  in
                  let uu____13994 =
                    let uu____14009 =
                      let uu____14022 =
                        let uu____14031 =
                          let uu____14032 =
                            let uu____14033 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____14033  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____14032
                           in
                        quant axy uu____14031  in
                      (FStar_Parser_Const.op_notEq, uu____14022)  in
                    let uu____14042 =
                      let uu____14057 =
                        let uu____14070 =
                          let uu____14079 =
                            let uu____14080 =
                              let uu____14081 =
                                let uu____14086 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____14087 =
                                  FStar_SMTEncoding_Term.unboxInt y  in
                                (uu____14086, uu____14087)  in
                              FStar_SMTEncoding_Util.mkLT uu____14081  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____14080
                             in
                          quant xy uu____14079  in
                        (FStar_Parser_Const.op_LT, uu____14070)  in
                      let uu____14096 =
                        let uu____14111 =
                          let uu____14124 =
                            let uu____14133 =
                              let uu____14134 =
                                let uu____14135 =
                                  let uu____14140 =
                                    FStar_SMTEncoding_Term.unboxInt x  in
                                  let uu____14141 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  (uu____14140, uu____14141)  in
                                FStar_SMTEncoding_Util.mkLTE uu____14135  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____14134
                               in
                            quant xy uu____14133  in
                          (FStar_Parser_Const.op_LTE, uu____14124)  in
                        let uu____14150 =
                          let uu____14165 =
                            let uu____14178 =
                              let uu____14187 =
                                let uu____14188 =
                                  let uu____14189 =
                                    let uu____14194 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    let uu____14195 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    (uu____14194, uu____14195)  in
                                  FStar_SMTEncoding_Util.mkGT uu____14189  in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____14188
                                 in
                              quant xy uu____14187  in
                            (FStar_Parser_Const.op_GT, uu____14178)  in
                          let uu____14204 =
                            let uu____14219 =
                              let uu____14232 =
                                let uu____14241 =
                                  let uu____14242 =
                                    let uu____14243 =
                                      let uu____14248 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____14249 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____14248, uu____14249)  in
                                    FStar_SMTEncoding_Util.mkGTE uu____14243
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____14242
                                   in
                                quant xy uu____14241  in
                              (FStar_Parser_Const.op_GTE, uu____14232)  in
                            let uu____14258 =
                              let uu____14273 =
                                let uu____14286 =
                                  let uu____14295 =
                                    let uu____14296 =
                                      let uu____14297 =
                                        let uu____14302 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____14303 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____14302, uu____14303)  in
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____14297
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____14296
                                     in
                                  quant xy uu____14295  in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____14286)
                                 in
                              let uu____14312 =
                                let uu____14327 =
                                  let uu____14340 =
                                    let uu____14349 =
                                      let uu____14350 =
                                        let uu____14351 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____14351
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____14350
                                       in
                                    quant qx uu____14349  in
                                  (FStar_Parser_Const.op_Minus, uu____14340)
                                   in
                                let uu____14360 =
                                  let uu____14375 =
                                    let uu____14388 =
                                      let uu____14397 =
                                        let uu____14398 =
                                          let uu____14399 =
                                            let uu____14404 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____14405 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____14404, uu____14405)  in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____14399
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____14398
                                         in
                                      quant xy uu____14397  in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____14388)
                                     in
                                  let uu____14414 =
                                    let uu____14429 =
                                      let uu____14442 =
                                        let uu____14451 =
                                          let uu____14452 =
                                            let uu____14453 =
                                              let uu____14458 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____14459 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____14458, uu____14459)  in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____14453
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____14452
                                           in
                                        quant xy uu____14451  in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____14442)
                                       in
                                    let uu____14468 =
                                      let uu____14483 =
                                        let uu____14496 =
                                          let uu____14505 =
                                            let uu____14506 =
                                              let uu____14507 =
                                                let uu____14512 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x
                                                   in
                                                let uu____14513 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y
                                                   in
                                                (uu____14512, uu____14513)
                                                 in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____14507
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____14506
                                             in
                                          quant xy uu____14505  in
                                        (FStar_Parser_Const.op_Division,
                                          uu____14496)
                                         in
                                      let uu____14522 =
                                        let uu____14537 =
                                          let uu____14550 =
                                            let uu____14559 =
                                              let uu____14560 =
                                                let uu____14561 =
                                                  let uu____14566 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____14567 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____14566, uu____14567)
                                                   in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____14561
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____14560
                                               in
                                            quant xy uu____14559  in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____14550)
                                           in
                                        let uu____14576 =
                                          let uu____14591 =
                                            let uu____14604 =
                                              let uu____14613 =
                                                let uu____14614 =
                                                  let uu____14615 =
                                                    let uu____14620 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x
                                                       in
                                                    let uu____14621 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y
                                                       in
                                                    (uu____14620,
                                                      uu____14621)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____14615
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____14614
                                                 in
                                              quant xy uu____14613  in
                                            (FStar_Parser_Const.op_And,
                                              uu____14604)
                                             in
                                          let uu____14630 =
                                            let uu____14645 =
                                              let uu____14658 =
                                                let uu____14667 =
                                                  let uu____14668 =
                                                    let uu____14669 =
                                                      let uu____14674 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      let uu____14675 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y
                                                         in
                                                      (uu____14674,
                                                        uu____14675)
                                                       in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____14669
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____14668
                                                   in
                                                quant xy uu____14667  in
                                              (FStar_Parser_Const.op_Or,
                                                uu____14658)
                                               in
                                            let uu____14684 =
                                              let uu____14699 =
                                                let uu____14712 =
                                                  let uu____14721 =
                                                    let uu____14722 =
                                                      let uu____14723 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____14723
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____14722
                                                     in
                                                  quant qx uu____14721  in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____14712)
                                                 in
                                              [uu____14699]  in
                                            uu____14645 :: uu____14684  in
                                          uu____14591 :: uu____14630  in
                                        uu____14537 :: uu____14576  in
                                      uu____14483 :: uu____14522  in
                                    uu____14429 :: uu____14468  in
                                  uu____14375 :: uu____14414  in
                                uu____14327 :: uu____14360  in
                              uu____14273 :: uu____14312  in
                            uu____14219 :: uu____14258  in
                          uu____14165 :: uu____14204  in
                        uu____14111 :: uu____14150  in
                      uu____14057 :: uu____14096  in
                    uu____14009 :: uu____14042  in
                  uu____13962 :: uu____13994  in
                let mk1 l v1 =
                  let uu____14937 =
                    let uu____14946 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____15004  ->
                              match uu____15004 with
                              | (l',uu____15018) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____14946
                      (FStar_Option.map
                         (fun uu____15078  ->
                            match uu____15078 with | (uu____15097,b) -> b v1))
                     in
                  FStar_All.pipe_right uu____14937 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____15168  ->
                          match uu____15168 with
                          | (l',uu____15182) -> FStar_Ident.lid_equals l l'))
                   in
                { mk = mk1; is }))
  
let (pretype_axiom :
  env_t ->
    FStar_SMTEncoding_Term.term ->
      (Prims.string,FStar_SMTEncoding_Term.sort)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_SMTEncoding_Term.decl)
  =
  fun env  ->
    fun tapp  ->
      fun vars  ->
        let uu____15220 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
        match uu____15220 with
        | (xxsym,xx) ->
            let uu____15227 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort
               in
            (match uu____15227 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp  in
                 let module_name = env.current_module_name  in
                 let uu____15237 =
                   let uu____15244 =
                     let uu____15245 =
                       let uu____15256 =
                         let uu____15257 =
                           let uu____15262 =
                             let uu____15263 =
                               let uu____15268 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx])
                                  in
                               (tapp, uu____15268)  in
                             FStar_SMTEncoding_Util.mkEq uu____15263  in
                           (xx_has_type, uu____15262)  in
                         FStar_SMTEncoding_Util.mkImp uu____15257  in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____15256)
                        in
                     FStar_SMTEncoding_Util.mkForall uu____15245  in
                   let uu____15293 =
                     let uu____15294 =
                       let uu____15295 =
                         let uu____15296 =
                           FStar_Util.digest_of_string tapp_hash  in
                         Prims.strcat "_pretyping_" uu____15296  in
                       Prims.strcat module_name uu____15295  in
                     varops.mk_unique uu____15294  in
                   (uu____15244, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____15293)
                    in
                 FStar_SMTEncoding_Util.mkAssume uu____15237)
  
let (primitive_type_axioms :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      Prims.string ->
        FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
  let x = FStar_SMTEncoding_Util.mkFreeV xx  in
  let yy = ("y", FStar_SMTEncoding_Term.Term_sort)  in
  let y = FStar_SMTEncoding_Util.mkFreeV yy  in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let uu____15332 =
      let uu____15333 =
        let uu____15340 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____15340, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15333  in
    let uu____15343 =
      let uu____15346 =
        let uu____15347 =
          let uu____15354 =
            let uu____15355 =
              let uu____15366 =
                let uu____15367 =
                  let uu____15372 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____15372)  in
                FStar_SMTEncoding_Util.mkImp uu____15367  in
              ([[typing_pred]], [xx], uu____15366)  in
            mkForall_fuel uu____15355  in
          (uu____15354, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____15347  in
      [uu____15346]  in
    uu____15332 :: uu____15343  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____15414 =
      let uu____15415 =
        let uu____15422 =
          let uu____15423 =
            let uu____15434 =
              let uu____15439 =
                let uu____15442 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____15442]  in
              [uu____15439]  in
            let uu____15447 =
              let uu____15448 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____15448 tt  in
            (uu____15434, [bb], uu____15447)  in
          FStar_SMTEncoding_Util.mkForall uu____15423  in
        (uu____15422, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15415  in
    let uu____15469 =
      let uu____15472 =
        let uu____15473 =
          let uu____15480 =
            let uu____15481 =
              let uu____15492 =
                let uu____15493 =
                  let uu____15498 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____15498)  in
                FStar_SMTEncoding_Util.mkImp uu____15493  in
              ([[typing_pred]], [xx], uu____15492)  in
            mkForall_fuel uu____15481  in
          (uu____15480, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____15473  in
      [uu____15472]  in
    uu____15414 :: uu____15469  in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes =
      let uu____15548 =
        let uu____15549 =
          let uu____15556 =
            let uu____15559 =
              let uu____15562 =
                let uu____15565 = FStar_SMTEncoding_Term.boxInt a  in
                let uu____15566 =
                  let uu____15569 = FStar_SMTEncoding_Term.boxInt b  in
                  [uu____15569]  in
                uu____15565 :: uu____15566  in
              tt :: uu____15562  in
            tt :: uu____15559  in
          ("Prims.Precedes", uu____15556)  in
        FStar_SMTEncoding_Util.mkApp uu____15549  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15548  in
    let precedes_y_x =
      let uu____15573 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x])  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15573  in
    let uu____15576 =
      let uu____15577 =
        let uu____15584 =
          let uu____15585 =
            let uu____15596 =
              let uu____15601 =
                let uu____15604 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____15604]  in
              [uu____15601]  in
            let uu____15609 =
              let uu____15610 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____15610 tt  in
            (uu____15596, [bb], uu____15609)  in
          FStar_SMTEncoding_Util.mkForall uu____15585  in
        (uu____15584, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15577  in
    let uu____15631 =
      let uu____15634 =
        let uu____15635 =
          let uu____15642 =
            let uu____15643 =
              let uu____15654 =
                let uu____15655 =
                  let uu____15660 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____15660)  in
                FStar_SMTEncoding_Util.mkImp uu____15655  in
              ([[typing_pred]], [xx], uu____15654)  in
            mkForall_fuel uu____15643  in
          (uu____15642, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____15635  in
      let uu____15685 =
        let uu____15688 =
          let uu____15689 =
            let uu____15696 =
              let uu____15697 =
                let uu____15708 =
                  let uu____15709 =
                    let uu____15714 =
                      let uu____15715 =
                        let uu____15718 =
                          let uu____15721 =
                            let uu____15724 =
                              let uu____15725 =
                                let uu____15730 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____15731 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____15730, uu____15731)  in
                              FStar_SMTEncoding_Util.mkGT uu____15725  in
                            let uu____15732 =
                              let uu____15735 =
                                let uu____15736 =
                                  let uu____15741 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____15742 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____15741, uu____15742)  in
                                FStar_SMTEncoding_Util.mkGTE uu____15736  in
                              let uu____15743 =
                                let uu____15746 =
                                  let uu____15747 =
                                    let uu____15752 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____15753 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____15752, uu____15753)  in
                                  FStar_SMTEncoding_Util.mkLT uu____15747  in
                                [uu____15746]  in
                              uu____15735 :: uu____15743  in
                            uu____15724 :: uu____15732  in
                          typing_pred_y :: uu____15721  in
                        typing_pred :: uu____15718  in
                      FStar_SMTEncoding_Util.mk_and_l uu____15715  in
                    (uu____15714, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____15709  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____15708)
                 in
              mkForall_fuel uu____15697  in
            (uu____15696,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____15689  in
        [uu____15688]  in
      uu____15634 :: uu____15685  in
    uu____15576 :: uu____15631  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____15799 =
      let uu____15800 =
        let uu____15807 =
          let uu____15808 =
            let uu____15819 =
              let uu____15824 =
                let uu____15827 = FStar_SMTEncoding_Term.boxString b  in
                [uu____15827]  in
              [uu____15824]  in
            let uu____15832 =
              let uu____15833 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____15833 tt  in
            (uu____15819, [bb], uu____15832)  in
          FStar_SMTEncoding_Util.mkForall uu____15808  in
        (uu____15807, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15800  in
    let uu____15854 =
      let uu____15857 =
        let uu____15858 =
          let uu____15865 =
            let uu____15866 =
              let uu____15877 =
                let uu____15878 =
                  let uu____15883 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____15883)  in
                FStar_SMTEncoding_Util.mkImp uu____15878  in
              ([[typing_pred]], [xx], uu____15877)  in
            mkForall_fuel uu____15866  in
          (uu____15865, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____15858  in
      [uu____15857]  in
    uu____15799 :: uu____15854  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")]
     in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____15936 =
      let uu____15937 =
        let uu____15944 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____15944, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15937  in
    [uu____15936]  in
  let mk_and_interp env conj uu____15956 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____15981 =
      let uu____15982 =
        let uu____15989 =
          let uu____15990 =
            let uu____16001 =
              let uu____16002 =
                let uu____16007 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____16007, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16002  in
            ([[l_and_a_b]], [aa; bb], uu____16001)  in
          FStar_SMTEncoding_Util.mkForall uu____15990  in
        (uu____15989, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15982  in
    [uu____15981]  in
  let mk_or_interp env disj uu____16045 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____16070 =
      let uu____16071 =
        let uu____16078 =
          let uu____16079 =
            let uu____16090 =
              let uu____16091 =
                let uu____16096 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____16096, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16091  in
            ([[l_or_a_b]], [aa; bb], uu____16090)  in
          FStar_SMTEncoding_Util.mkForall uu____16079  in
        (uu____16078, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16071  in
    [uu____16070]  in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y])  in
    let uu____16159 =
      let uu____16160 =
        let uu____16167 =
          let uu____16168 =
            let uu____16179 =
              let uu____16180 =
                let uu____16185 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____16185, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16180  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____16179)  in
          FStar_SMTEncoding_Util.mkForall uu____16168  in
        (uu____16167, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16160  in
    [uu____16159]  in
  let mk_eq3_interp env eq3 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let eq3_x_y = FStar_SMTEncoding_Util.mkApp (eq3, [a; b; x1; y1])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq3_x_y])  in
    let uu____16258 =
      let uu____16259 =
        let uu____16266 =
          let uu____16267 =
            let uu____16278 =
              let uu____16279 =
                let uu____16284 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____16284, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16279  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____16278)  in
          FStar_SMTEncoding_Util.mkForall uu____16267  in
        (uu____16266, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16259  in
    [uu____16258]  in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____16355 =
      let uu____16356 =
        let uu____16363 =
          let uu____16364 =
            let uu____16375 =
              let uu____16376 =
                let uu____16381 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____16381, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16376  in
            ([[l_imp_a_b]], [aa; bb], uu____16375)  in
          FStar_SMTEncoding_Util.mkForall uu____16364  in
        (uu____16363, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16356  in
    [uu____16355]  in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____16444 =
      let uu____16445 =
        let uu____16452 =
          let uu____16453 =
            let uu____16464 =
              let uu____16465 =
                let uu____16470 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____16470, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16465  in
            ([[l_iff_a_b]], [aa; bb], uu____16464)  in
          FStar_SMTEncoding_Util.mkForall uu____16453  in
        (uu____16452, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16445  in
    [uu____16444]  in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____16522 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____16522  in
    let uu____16525 =
      let uu____16526 =
        let uu____16533 =
          let uu____16534 =
            let uu____16545 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____16545)  in
          FStar_SMTEncoding_Util.mkForall uu____16534  in
        (uu____16533, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16526  in
    [uu____16525]  in
  let mk_forall_interp env for_all1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let l_forall_a_b = FStar_SMTEncoding_Util.mkApp (for_all1, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_forall_a_b])  in
    let valid_b_x =
      let uu____16605 =
        let uu____16612 =
          let uu____16615 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____16615]  in
        ("Valid", uu____16612)  in
      FStar_SMTEncoding_Util.mkApp uu____16605  in
    let uu____16618 =
      let uu____16619 =
        let uu____16626 =
          let uu____16627 =
            let uu____16638 =
              let uu____16639 =
                let uu____16644 =
                  let uu____16645 =
                    let uu____16656 =
                      let uu____16661 =
                        let uu____16664 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____16664]  in
                      [uu____16661]  in
                    let uu____16669 =
                      let uu____16670 =
                        let uu____16675 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____16675, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____16670  in
                    (uu____16656, [xx1], uu____16669)  in
                  FStar_SMTEncoding_Util.mkForall uu____16645  in
                (uu____16644, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16639  in
            ([[l_forall_a_b]], [aa; bb], uu____16638)  in
          FStar_SMTEncoding_Util.mkForall uu____16627  in
        (uu____16626, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16619  in
    [uu____16618]  in
  let mk_exists_interp env for_some1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let l_exists_a_b = FStar_SMTEncoding_Util.mkApp (for_some1, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_exists_a_b])  in
    let valid_b_x =
      let uu____16757 =
        let uu____16764 =
          let uu____16767 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____16767]  in
        ("Valid", uu____16764)  in
      FStar_SMTEncoding_Util.mkApp uu____16757  in
    let uu____16770 =
      let uu____16771 =
        let uu____16778 =
          let uu____16779 =
            let uu____16790 =
              let uu____16791 =
                let uu____16796 =
                  let uu____16797 =
                    let uu____16808 =
                      let uu____16813 =
                        let uu____16816 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____16816]  in
                      [uu____16813]  in
                    let uu____16821 =
                      let uu____16822 =
                        let uu____16827 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____16827, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____16822  in
                    (uu____16808, [xx1], uu____16821)  in
                  FStar_SMTEncoding_Util.mkExists uu____16797  in
                (uu____16796, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16791  in
            ([[l_exists_a_b]], [aa; bb], uu____16790)  in
          FStar_SMTEncoding_Util.mkForall uu____16779  in
        (uu____16778, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16771  in
    [uu____16770]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____16887 =
      let uu____16888 =
        let uu____16895 =
          let uu____16896 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____16896 range_ty  in
        let uu____16897 = varops.mk_unique "typing_range_const"  in
        (uu____16895, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____16897)
         in
      FStar_SMTEncoding_Util.mkAssume uu____16888  in
    [uu____16887]  in
  let mk_inversion_axiom env inversion tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort)  in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let inversion_t = FStar_SMTEncoding_Util.mkApp (inversion, [t])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [inversion_t])  in
    let body =
      let hastypeZ = FStar_SMTEncoding_Term.mk_HasTypeZ x1 t  in
      let hastypeS =
        let uu____16931 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____16931 x1 t  in
      let uu____16932 =
        let uu____16943 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____16943)  in
      FStar_SMTEncoding_Util.mkForall uu____16932  in
    let uu____16966 =
      let uu____16967 =
        let uu____16974 =
          let uu____16975 =
            let uu____16986 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____16986)  in
          FStar_SMTEncoding_Util.mkForall uu____16975  in
        (uu____16974,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16967  in
    [uu____16966]  in
  let mk_with_type_axiom env with_type1 tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort)  in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1  in
    let ee = ("e", FStar_SMTEncoding_Term.Term_sort)  in
    let e = FStar_SMTEncoding_Util.mkFreeV ee  in
    let with_type_t_e = FStar_SMTEncoding_Util.mkApp (with_type1, [t; e])  in
    let uu____17036 =
      let uu____17037 =
        let uu____17044 =
          let uu____17045 =
            let uu____17060 =
              let uu____17061 =
                let uu____17066 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____17067 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____17066, uu____17067)  in
              FStar_SMTEncoding_Util.mkAnd uu____17061  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____17060)
             in
          FStar_SMTEncoding_Util.mkForall' uu____17045  in
        (uu____17044,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____17037  in
    [uu____17036]  in
  let prims1 =
    [(FStar_Parser_Const.unit_lid, mk_unit);
    (FStar_Parser_Const.bool_lid, mk_bool);
    (FStar_Parser_Const.int_lid, mk_int);
    (FStar_Parser_Const.string_lid, mk_str);
    (FStar_Parser_Const.true_lid, mk_true_interp);
    (FStar_Parser_Const.false_lid, mk_false_interp);
    (FStar_Parser_Const.and_lid, mk_and_interp);
    (FStar_Parser_Const.or_lid, mk_or_interp);
    (FStar_Parser_Const.eq2_lid, mk_eq2_interp);
    (FStar_Parser_Const.eq3_lid, mk_eq3_interp);
    (FStar_Parser_Const.imp_lid, mk_imp_interp);
    (FStar_Parser_Const.iff_lid, mk_iff_interp);
    (FStar_Parser_Const.not_lid, mk_not_interp);
    (FStar_Parser_Const.forall_lid, mk_forall_interp);
    (FStar_Parser_Const.exists_lid, mk_exists_interp);
    (FStar_Parser_Const.range_lid, mk_range_interp);
    (FStar_Parser_Const.inversion_lid, mk_inversion_axiom);
    (FStar_Parser_Const.with_type_lid, mk_with_type_axiom)]  in
  fun env  ->
    fun t  ->
      fun s  ->
        fun tt  ->
          let uu____17413 =
            FStar_Util.find_opt
              (fun uu____17439  ->
                 match uu____17439 with
                 | (l,uu____17451) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____17413 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____17476,f) -> f env s tt
  
let (encode_smt_lemma :
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____17512 = encode_function_type_as_formula t env  in
        match uu____17512 with
        | (form,decls) ->
            FStar_List.append decls
              [FStar_SMTEncoding_Util.mkAssume
                 (form,
                   (FStar_Pervasives_Native.Some
                      (Prims.strcat "Lemma: " lid.FStar_Ident.str)),
                   (Prims.strcat "lemma_" lid.FStar_Ident.str))]
  
let (encode_free_var :
  Prims.bool ->
    env_t ->
      FStar_Syntax_Syntax.fv ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.qualifier Prims.list ->
              (FStar_SMTEncoding_Term.decl Prims.list,env_t)
                FStar_Pervasives_Native.tuple2)
  =
  fun uninterpreted  ->
    fun env  ->
      fun fv  ->
        fun tt  ->
          fun t_norm  ->
            fun quals  ->
              let lid =
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
              let uu____17552 =
                ((let uu____17555 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____17555) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____17552
              then
                let uu____17562 = new_term_constant_and_tok_from_lid env lid
                   in
                match uu____17562 with
                | (vname,vtok,env1) ->
                    let arg_sorts =
                      let uu____17581 =
                        let uu____17582 = FStar_Syntax_Subst.compress t_norm
                           in
                        uu____17582.FStar_Syntax_Syntax.n  in
                      match uu____17581 with
                      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____17588) ->
                          FStar_All.pipe_right binders
                            (FStar_List.map
                               (fun uu____17618  ->
                                  FStar_SMTEncoding_Term.Term_sort))
                      | uu____17623 -> []  in
                    let d =
                      FStar_SMTEncoding_Term.DeclFun
                        (vname, arg_sorts, FStar_SMTEncoding_Term.Term_sort,
                          (FStar_Pervasives_Native.Some
                             "Uninterpreted function symbol for impure function"))
                       in
                    let dd =
                      FStar_SMTEncoding_Term.DeclFun
                        (vtok, [], FStar_SMTEncoding_Term.Term_sort,
                          (FStar_Pervasives_Native.Some
                             "Uninterpreted name for impure function"))
                       in
                    ([d; dd], env1)
              else
                (let uu____17637 = prims.is lid  in
                 if uu____17637
                 then
                   let vname = varops.new_fvar lid  in
                   let uu____17645 = prims.mk lid vname  in
                   match uu____17645 with
                   | (tok,definition) ->
                       let env1 =
                         push_free_var env lid vname
                           (FStar_Pervasives_Native.Some tok)
                          in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____17669 =
                      let uu____17680 = curried_arrow_formals_comp t_norm  in
                      match uu____17680 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____17698 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp
                               in
                            if uu____17698
                            then
                              let uu____17699 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___118_17702 = env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___118_17702.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___118_17702.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___118_17702.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___118_17702.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___118_17702.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___118_17702.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___118_17702.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___118_17702.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___118_17702.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___118_17702.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___118_17702.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___118_17702.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___118_17702.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___118_17702.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___118_17702.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___118_17702.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___118_17702.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___118_17702.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___118_17702.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___118_17702.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___118_17702.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___118_17702.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___118_17702.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___118_17702.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___118_17702.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___118_17702.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qname_and_index =
                                       (uu___118_17702.FStar_TypeChecker_Env.qname_and_index);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___118_17702.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth =
                                       (uu___118_17702.FStar_TypeChecker_Env.synth);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___118_17702.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___118_17702.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___118_17702.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___118_17702.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.dep_graph =
                                       (uu___118_17702.FStar_TypeChecker_Env.dep_graph)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____17699
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____17714 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1
                               in
                            (args, uu____17714)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____17669 with
                    | (formals,(pre_opt,res_t)) ->
                        let uu____17759 =
                          new_term_constant_and_tok_from_lid env lid  in
                        (match uu____17759 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____17780 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, [])
                                in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___90_17822  ->
                                       match uu___90_17822 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____17826 =
                                             FStar_Util.prefix vars  in
                                           (match uu____17826 with
                                            | (uu____17847,(xxsym,uu____17849))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort)
                                                   in
                                                let uu____17867 =
                                                  let uu____17868 =
                                                    let uu____17875 =
                                                      let uu____17876 =
                                                        let uu____17887 =
                                                          let uu____17888 =
                                                            let uu____17893 =
                                                              let uu____17894
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____17894
                                                               in
                                                            (vapp,
                                                              uu____17893)
                                                             in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____17888
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____17887)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17876
                                                       in
                                                    (uu____17875,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str)))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17868
                                                   in
                                                [uu____17867])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____17913 =
                                             FStar_Util.prefix vars  in
                                           (match uu____17913 with
                                            | (uu____17934,(xxsym,uu____17936))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort)
                                                   in
                                                let f1 =
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      = f;
                                                    FStar_Syntax_Syntax.index
                                                      = (Prims.parse_int "0");
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      FStar_Syntax_Syntax.tun
                                                  }  in
                                                let tp_name =
                                                  mk_term_projector_name d f1
                                                   in
                                                let prim_app =
                                                  FStar_SMTEncoding_Util.mkApp
                                                    (tp_name, [xx])
                                                   in
                                                let uu____17959 =
                                                  let uu____17960 =
                                                    let uu____17967 =
                                                      let uu____17968 =
                                                        let uu____17979 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app)
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____17979)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17968
                                                       in
                                                    (uu____17967,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17960
                                                   in
                                                [uu____17959])
                                       | uu____17996 -> []))
                                in
                             let uu____17997 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1
                                in
                             (match uu____17997 with
                              | (vars,guards,env',decls1,uu____18024) ->
                                  let uu____18037 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____18046 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards
                                           in
                                        (uu____18046, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____18048 =
                                          encode_formula p env'  in
                                        (match uu____18048 with
                                         | (g,ds) ->
                                             let uu____18059 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards)
                                                in
                                             (uu____18059,
                                               (FStar_List.append decls1 ds)))
                                     in
                                  (match uu____18037 with
                                   | (guard,decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars
                                          in
                                       let vapp =
                                         let uu____18072 =
                                           let uu____18079 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars
                                              in
                                           (vname, uu____18079)  in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____18072
                                          in
                                       let uu____18088 =
                                         let vname_decl =
                                           let uu____18096 =
                                             let uu____18107 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____18117  ->
                                                       FStar_SMTEncoding_Term.Term_sort))
                                                in
                                             (vname, uu____18107,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None)
                                              in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____18096
                                            in
                                         let uu____18126 =
                                           let env2 =
                                             let uu___119_18132 = env1  in
                                             {
                                               bindings =
                                                 (uu___119_18132.bindings);
                                               depth = (uu___119_18132.depth);
                                               tcenv = (uu___119_18132.tcenv);
                                               warn = (uu___119_18132.warn);
                                               cache = (uu___119_18132.cache);
                                               nolabels =
                                                 (uu___119_18132.nolabels);
                                               use_zfuel_name =
                                                 (uu___119_18132.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___119_18132.current_module_name)
                                             }  in
                                           let uu____18133 =
                                             let uu____18134 =
                                               head_normal env2 tt  in
                                             Prims.op_Negation uu____18134
                                              in
                                           if uu____18133
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm
                                            in
                                         match uu____18126 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____18149::uu____18150 ->
                                                   let ff =
                                                     ("ty",
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                      in
                                                   let f =
                                                     FStar_SMTEncoding_Util.mkFreeV
                                                       ff
                                                      in
                                                   let vtok_app_l =
                                                     mk_Apply vtok_tm [ff]
                                                      in
                                                   let vtok_app_r =
                                                     mk_Apply f
                                                       [(vtok,
                                                          FStar_SMTEncoding_Term.Term_sort)]
                                                      in
                                                   let guarded_tok_typing =
                                                     let uu____18190 =
                                                       let uu____18201 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing
                                                          in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____18201)
                                                        in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____18190
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____18228 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                                in
                                             let uu____18231 =
                                               match formals with
                                               | [] ->
                                                   let uu____18248 =
                                                     let uu____18249 =
                                                       let uu____18252 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort)
                                                          in
                                                       FStar_All.pipe_left
                                                         (fun _0_42  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_42)
                                                         uu____18252
                                                        in
                                                     push_free_var env1 lid
                                                       vname uu____18249
                                                      in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____18248)
                                               | uu____18257 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None)
                                                      in
                                                   let name_tok_corr =
                                                     let uu____18264 =
                                                       let uu____18271 =
                                                         let uu____18272 =
                                                           let uu____18283 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp)
                                                              in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____18283)
                                                            in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____18272
                                                          in
                                                       (uu____18271,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname))
                                                        in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____18264
                                                      in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       name_tok_corr;
                                                       tok_typing1]), env1)
                                                in
                                             (match uu____18231 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2))
                                          in
                                       (match uu____18088 with
                                        | (decls2,env2) ->
                                            let uu____18326 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t
                                                 in
                                              let uu____18334 =
                                                encode_term res_t1 env'  in
                                              match uu____18334 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____18347 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t
                                                     in
                                                  (encoded_res_t,
                                                    uu____18347, decls)
                                               in
                                            (match uu____18326 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____18358 =
                                                     let uu____18365 =
                                                       let uu____18366 =
                                                         let uu____18377 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred)
                                                            in
                                                         ([[vapp]], vars,
                                                           uu____18377)
                                                          in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____18366
                                                        in
                                                     (uu____18365,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____18358
                                                    in
                                                 let freshness =
                                                   let uu____18393 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New)
                                                      in
                                                   if uu____18393
                                                   then
                                                     let uu____18398 =
                                                       let uu____18399 =
                                                         let uu____18410 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd)
                                                            in
                                                         let uu____18421 =
                                                           varops.next_id ()
                                                            in
                                                         (vname, uu____18410,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____18421)
                                                          in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____18399
                                                        in
                                                     let uu____18424 =
                                                       let uu____18427 =
                                                         pretype_axiom env2
                                                           vapp vars
                                                          in
                                                       [uu____18427]  in
                                                     uu____18398 ::
                                                       uu____18424
                                                   else []  in
                                                 let g =
                                                   let uu____18432 =
                                                     let uu____18435 =
                                                       let uu____18438 =
                                                         let uu____18441 =
                                                           let uu____18444 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars
                                                              in
                                                           typingAx ::
                                                             uu____18444
                                                            in
                                                         FStar_List.append
                                                           freshness
                                                           uu____18441
                                                          in
                                                       FStar_List.append
                                                         decls3 uu____18438
                                                        in
                                                     FStar_List.append decls2
                                                       uu____18435
                                                      in
                                                   FStar_List.append decls11
                                                     uu____18432
                                                    in
                                                 (g, env2))))))))
  
let (declare_top_level_let :
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          ((Prims.string,FStar_SMTEncoding_Term.term
                           FStar_Pervasives_Native.option)
             FStar_Pervasives_Native.tuple2,FStar_SMTEncoding_Term.decl
                                              Prims.list,env_t)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun x  ->
      fun t  ->
        fun t_norm  ->
          let uu____18475 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____18475 with
          | FStar_Pervasives_Native.None  ->
              let uu____18512 = encode_free_var false env x t t_norm []  in
              (match uu____18512 with
               | (decls,env1) ->
                   let uu____18539 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   (match uu____18539 with
                    | (n1,x',uu____18566) -> ((n1, x'), decls, env1)))
          | FStar_Pervasives_Native.Some (n1,x1,uu____18587) ->
              ((n1, x1), [], env)
  
let (encode_top_level_val :
  Prims.bool ->
    env_t ->
      FStar_Syntax_Syntax.fv ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.qualifier Prims.list ->
            (FStar_SMTEncoding_Term.decl Prims.list,env_t)
              FStar_Pervasives_Native.tuple2)
  =
  fun uninterpreted  ->
    fun env  ->
      fun lid  ->
        fun t  ->
          fun quals  ->
            let tt = norm env t  in
            let uu____18642 =
              encode_free_var uninterpreted env lid t tt quals  in
            match uu____18642 with
            | (decls,env1) ->
                let uu____18661 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____18661
                then
                  let uu____18668 =
                    let uu____18671 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____18671  in
                  (uu____18668, env1)
                else (decls, env1)
  
let (encode_top_level_vals :
  env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bindings  ->
      fun quals  ->
        FStar_All.pipe_right bindings
          (FStar_List.fold_left
             (fun uu____18723  ->
                fun lb  ->
                  match uu____18723 with
                  | (decls,env1) ->
                      let uu____18743 =
                        let uu____18750 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____18750
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____18743 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____18771 = FStar_Syntax_Util.head_and_args t  in
    match uu____18771 with
    | (hd1,args) ->
        let uu____18808 =
          let uu____18809 = FStar_Syntax_Util.un_uinst hd1  in
          uu____18809.FStar_Syntax_Syntax.n  in
        (match uu____18808 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____18813,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____18832 -> false)
  
let (encode_top_level_let :
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun uu____18854  ->
      fun quals  ->
        match uu____18854 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____18930 = FStar_Util.first_N nbinders formals  in
              match uu____18930 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____19011  ->
                         fun uu____19012  ->
                           match (uu____19011, uu____19012) with
                           | ((formal,uu____19030),(binder,uu____19032)) ->
                               let uu____19041 =
                                 let uu____19048 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____19048)  in
                               FStar_Syntax_Syntax.NT uu____19041) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____19056 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____19087  ->
                              match uu____19087 with
                              | (x,i) ->
                                  let uu____19098 =
                                    let uu___120_19099 = x  in
                                    let uu____19100 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___120_19099.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___120_19099.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____19100
                                    }  in
                                  (uu____19098, i)))
                       in
                    FStar_All.pipe_right uu____19056
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____19118 =
                      let uu____19119 = FStar_Syntax_Subst.compress body  in
                      let uu____19120 =
                        let uu____19121 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____19121
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____19119
                        uu____19120
                       in
                    uu____19118 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____19182 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c  in
                if uu____19182
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___121_19185 = env.tcenv  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___121_19185.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___121_19185.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___121_19185.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___121_19185.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___121_19185.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___121_19185.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___121_19185.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___121_19185.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___121_19185.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___121_19185.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___121_19185.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___121_19185.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___121_19185.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___121_19185.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___121_19185.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___121_19185.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___121_19185.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___121_19185.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___121_19185.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___121_19185.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___121_19185.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___121_19185.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___121_19185.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___121_19185.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___121_19185.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___121_19185.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___121_19185.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___121_19185.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___121_19185.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___121_19185.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___121_19185.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___121_19185.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___121_19185.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.dep_graph =
                         (uu___121_19185.FStar_TypeChecker_Env.dep_graph)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c  in
              let rec aux norm1 t_norm1 =
                let uu____19218 = FStar_Syntax_Util.abs_formals e  in
                match uu____19218 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____19282::uu____19283 ->
                         let uu____19298 =
                           let uu____19299 =
                             let uu____19302 =
                               FStar_Syntax_Subst.compress t_norm1  in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____19302
                              in
                           uu____19299.FStar_Syntax_Syntax.n  in
                         (match uu____19298 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____19345 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____19345 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1
                                      in
                                   let nbinders = FStar_List.length binders
                                      in
                                   let tres = get_result_type c1  in
                                   let uu____19387 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1)
                                      in
                                   if uu____19387
                                   then
                                     let uu____19422 =
                                       FStar_Util.first_N nformals binders
                                        in
                                     (match uu____19422 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____19516  ->
                                                   fun uu____19517  ->
                                                     match (uu____19516,
                                                             uu____19517)
                                                     with
                                                     | ((x,uu____19535),
                                                        (b,uu____19537)) ->
                                                         let uu____19546 =
                                                           let uu____19553 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b
                                                              in
                                                           (x, uu____19553)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____19546)
                                                formals1 bs0
                                               in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1
                                             in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt
                                             in
                                          let uu____19555 =
                                            let uu____19576 =
                                              get_result_type c2  in
                                            (bs0, body1, bs0, uu____19576)
                                             in
                                          (uu____19555, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____19644 =
                                          eta_expand1 binders formals1 body
                                            tres
                                           in
                                        match uu____19644 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____19733) ->
                              let uu____19738 =
                                let uu____19759 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort  in
                                FStar_Pervasives_Native.fst uu____19759  in
                              (uu____19738, true)
                          | uu____19824 when Prims.op_Negation norm1 ->
                              let t_norm2 =
                                FStar_TypeChecker_Normalize.normalize
                                  [FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                                  FStar_TypeChecker_Normalize.Beta;
                                  FStar_TypeChecker_Normalize.Weak;
                                  FStar_TypeChecker_Normalize.HNF;
                                  FStar_TypeChecker_Normalize.Exclude
                                    FStar_TypeChecker_Normalize.Zeta;
                                  FStar_TypeChecker_Normalize.UnfoldUntil
                                    FStar_Syntax_Syntax.Delta_constant;
                                  FStar_TypeChecker_Normalize.EraseUniverses]
                                  env.tcenv t_norm1
                                 in
                              aux true t_norm2
                          | uu____19826 ->
                              let uu____19827 =
                                let uu____19828 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____19829 =
                                  FStar_Syntax_Print.term_to_string t_norm1
                                   in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____19828
                                  uu____19829
                                 in
                              failwith uu____19827)
                     | uu____19854 ->
                         let rec aux' t_norm2 =
                           let uu____19879 =
                             let uu____19880 =
                               FStar_Syntax_Subst.compress t_norm2  in
                             uu____19880.FStar_Syntax_Syntax.n  in
                           match uu____19879 with
                           | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                               let uu____19921 =
                                 FStar_Syntax_Subst.open_comp formals c  in
                               (match uu____19921 with
                                | (formals1,c1) ->
                                    let tres = get_result_type c1  in
                                    let uu____19949 =
                                      eta_expand1 [] formals1 e tres  in
                                    (match uu____19949 with
                                     | (binders1,body1) ->
                                         ((binders1, body1, formals1, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv,uu____20029)
                               -> aux' bv.FStar_Syntax_Syntax.sort
                           | uu____20034 -> (([], e, [], t_norm2), false)  in
                         aux' t_norm1)
                 in
              aux false t_norm  in
            (try
               let uu____20090 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                  in
               if uu____20090
               then encode_top_level_vals env bindings quals
               else
                 (let uu____20102 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____20196  ->
                            fun lb  ->
                              match uu____20196 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____20291 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    if uu____20291
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    let uu____20294 =
                                      let uu____20309 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname
                                         in
                                      declare_top_level_let env1 uu____20309
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm
                                       in
                                    match uu____20294 with
                                    | (tok,decl,env2) ->
                                        let uu____20355 =
                                          let uu____20368 =
                                            let uu____20379 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            (uu____20379, tok)  in
                                          uu____20368 :: toks  in
                                        (uu____20355, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env))
                     in
                  match uu____20102 with
                  | (toks,typs,decls,env1) ->
                      let toks1 = FStar_List.rev toks  in
                      let decls1 =
                        FStar_All.pipe_right (FStar_List.rev decls)
                          FStar_List.flatten
                         in
                      let typs1 = FStar_List.rev typs  in
                      let mk_app1 curry f ftok vars =
                        match vars with
                        | [] ->
                            FStar_SMTEncoding_Util.mkFreeV
                              (f, FStar_SMTEncoding_Term.Term_sort)
                        | uu____20562 ->
                            if curry
                            then
                              (match ftok with
                               | FStar_Pervasives_Native.Some ftok1 ->
                                   mk_Apply ftok1 vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____20570 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort)
                                      in
                                   mk_Apply uu____20570 vars)
                            else
                              (let uu____20572 =
                                 let uu____20579 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars
                                    in
                                 (f, uu____20579)  in
                               FStar_SMTEncoding_Util.mkApp uu____20572)
                         in
                      let encode_non_rec_lbdef bindings1 typs2 toks2 env2 =
                        match (bindings1, typs2, toks2) with
                        | ({ FStar_Syntax_Syntax.lbname = uu____20661;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____20663;
                             FStar_Syntax_Syntax.lbeff = uu____20664;
                             FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                           (flid_fv,(f,ftok))::[]) ->
                            let flid =
                              (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            let uu____20727 =
                              let uu____20734 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.tcenv uvs [e; t_norm]
                                 in
                              match uu____20734 with
                              | (tcenv',uu____20752,e_t) ->
                                  let uu____20758 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____20769 -> failwith "Impossible"
                                     in
                                  (match uu____20758 with
                                   | (e1,t_norm1) ->
                                       ((let uu___124_20785 = env2  in
                                         {
                                           bindings =
                                             (uu___124_20785.bindings);
                                           depth = (uu___124_20785.depth);
                                           tcenv = tcenv';
                                           warn = (uu___124_20785.warn);
                                           cache = (uu___124_20785.cache);
                                           nolabels =
                                             (uu___124_20785.nolabels);
                                           use_zfuel_name =
                                             (uu___124_20785.use_zfuel_name);
                                           encode_non_total_function_typ =
                                             (uu___124_20785.encode_non_total_function_typ);
                                           current_module_name =
                                             (uu___124_20785.current_module_name)
                                         }), e1, t_norm1))
                               in
                            (match uu____20727 with
                             | (env',e1,t_norm1) ->
                                 let uu____20795 =
                                   destruct_bound_function flid t_norm1 e1
                                    in
                                 (match uu____20795 with
                                  | ((binders,body,uu____20816,uu____20817),curry)
                                      ->
                                      ((let uu____20828 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding")
                                           in
                                        if uu____20828
                                        then
                                          let uu____20829 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders
                                             in
                                          let uu____20830 =
                                            FStar_Syntax_Print.term_to_string
                                              body
                                             in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____20829 uu____20830
                                        else ());
                                       (let uu____20832 =
                                          encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env'
                                           in
                                        match uu____20832 with
                                        | (vars,guards,env'1,binder_decls,uu____20859)
                                            ->
                                            let body1 =
                                              let uu____20873 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.tcenv t_norm1
                                                 in
                                              if uu____20873
                                              then
                                                FStar_TypeChecker_Util.reify_body
                                                  env'1.tcenv body
                                              else body  in
                                            let app =
                                              mk_app1 curry f ftok vars  in
                                            let uu____20876 =
                                              let uu____20885 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic)
                                                 in
                                              if uu____20885
                                              then
                                                let uu____20896 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app
                                                   in
                                                let uu____20897 =
                                                  encode_formula body1 env'1
                                                   in
                                                (uu____20896, uu____20897)
                                              else
                                                (let uu____20907 =
                                                   encode_term body1 env'1
                                                    in
                                                 (app, uu____20907))
                                               in
                                            (match uu____20876 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____20930 =
                                                     let uu____20937 =
                                                       let uu____20938 =
                                                         let uu____20949 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2)
                                                            in
                                                         ([[app1]], vars,
                                                           uu____20949)
                                                          in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____20938
                                                        in
                                                     let uu____20960 =
                                                       let uu____20963 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str
                                                          in
                                                       FStar_Pervasives_Native.Some
                                                         uu____20963
                                                        in
                                                     (uu____20937,
                                                       uu____20960,
                                                       (Prims.strcat
                                                          "equation_" f))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____20930
                                                    in
                                                 let uu____20966 =
                                                   let uu____20969 =
                                                     let uu____20972 =
                                                       let uu____20975 =
                                                         let uu____20978 =
                                                           primitive_type_axioms
                                                             env2.tcenv flid
                                                             f app1
                                                            in
                                                         FStar_List.append
                                                           [eqn] uu____20978
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____20975
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____20972
                                                      in
                                                   FStar_List.append decls1
                                                     uu____20969
                                                    in
                                                 (uu____20966, env2))))))
                        | uu____20983 -> failwith "Impossible"  in
                      let encode_rec_lbdefs bindings1 typs2 toks2 env2 =
                        let fuel =
                          let uu____21068 = varops.fresh "fuel"  in
                          (uu____21068, FStar_SMTEncoding_Term.Fuel_sort)  in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel  in
                        let env0 = env2  in
                        let uu____21071 =
                          FStar_All.pipe_right toks2
                            (FStar_List.fold_left
                               (fun uu____21159  ->
                                  fun uu____21160  ->
                                    match (uu____21159, uu____21160) with
                                    | ((gtoks,env3),(flid_fv,(f,ftok))) ->
                                        let flid =
                                          (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                           in
                                        let g =
                                          let uu____21308 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented"
                                             in
                                          varops.new_fvar uu____21308  in
                                        let gtok =
                                          let uu____21310 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token"
                                             in
                                          varops.new_fvar uu____21310  in
                                        let env4 =
                                          let uu____21312 =
                                            let uu____21315 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm])
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_43  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_43) uu____21315
                                             in
                                          push_free_var env3 flid gtok
                                            uu____21312
                                           in
                                        (((flid, f, ftok, g, gtok) :: gtoks),
                                          env4)) ([], env2))
                           in
                        match uu____21071 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks  in
                            let encode_one_binding env01 uu____21471 t_norm
                              uu____21473 =
                              match (uu____21471, uu____21473) with
                              | ((flid,f,ftok,g,gtok),{
                                                        FStar_Syntax_Syntax.lbname
                                                          = lbn;
                                                        FStar_Syntax_Syntax.lbunivs
                                                          = uvs;
                                                        FStar_Syntax_Syntax.lbtyp
                                                          = uu____21517;
                                                        FStar_Syntax_Syntax.lbeff
                                                          = uu____21518;
                                                        FStar_Syntax_Syntax.lbdef
                                                          = e;_})
                                  ->
                                  let uu____21546 =
                                    let uu____21553 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.tcenv uvs [e; t_norm]
                                       in
                                    match uu____21553 with
                                    | (tcenv',uu____21575,e_t) ->
                                        let uu____21581 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____21592 ->
                                              failwith "Impossible"
                                           in
                                        (match uu____21581 with
                                         | (e1,t_norm1) ->
                                             ((let uu___125_21608 = env3  in
                                               {
                                                 bindings =
                                                   (uu___125_21608.bindings);
                                                 depth =
                                                   (uu___125_21608.depth);
                                                 tcenv = tcenv';
                                                 warn = (uu___125_21608.warn);
                                                 cache =
                                                   (uu___125_21608.cache);
                                                 nolabels =
                                                   (uu___125_21608.nolabels);
                                                 use_zfuel_name =
                                                   (uu___125_21608.use_zfuel_name);
                                                 encode_non_total_function_typ
                                                   =
                                                   (uu___125_21608.encode_non_total_function_typ);
                                                 current_module_name =
                                                   (uu___125_21608.current_module_name)
                                               }), e1, t_norm1))
                                     in
                                  (match uu____21546 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____21623 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding")
                                            in
                                         if uu____21623
                                         then
                                           let uu____21624 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn
                                              in
                                           let uu____21625 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1
                                              in
                                           let uu____21626 =
                                             FStar_Syntax_Print.term_to_string
                                               e1
                                              in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____21624 uu____21625
                                             uu____21626
                                         else ());
                                        (let uu____21628 =
                                           destruct_bound_function flid
                                             t_norm1 e1
                                            in
                                         match uu____21628 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____21665 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____21665
                                               then
                                                 let uu____21666 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____21667 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 let uu____21668 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals
                                                    in
                                                 let uu____21669 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres
                                                    in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____21666 uu____21667
                                                   uu____21668 uu____21669
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____21673 =
                                                 encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____21673 with
                                               | (vars,guards,env'1,binder_decls,uu____21704)
                                                   ->
                                                   let decl_g =
                                                     let uu____21718 =
                                                       let uu____21729 =
                                                         let uu____21732 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars
                                                            in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____21732
                                                          in
                                                       (g, uu____21729,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name"))
                                                        in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____21718
                                                      in
                                                   let env02 =
                                                     push_zfuel_name env01
                                                       flid g
                                                      in
                                                   let decl_g_tok =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (gtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Token for fuel-instrumented partial applications"))
                                                      in
                                                   let vars_tm =
                                                     FStar_List.map
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                       vars
                                                      in
                                                   let app =
                                                     let uu____21757 =
                                                       let uu____21764 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars
                                                          in
                                                       (f, uu____21764)  in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21757
                                                      in
                                                   let gsapp =
                                                     let uu____21774 =
                                                       let uu____21781 =
                                                         let uu____21784 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm])
                                                            in
                                                         uu____21784 ::
                                                           vars_tm
                                                          in
                                                       (g, uu____21781)  in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21774
                                                      in
                                                   let gmax =
                                                     let uu____21790 =
                                                       let uu____21797 =
                                                         let uu____21800 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", [])
                                                            in
                                                         uu____21800 ::
                                                           vars_tm
                                                          in
                                                       (g, uu____21797)  in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21790
                                                      in
                                                   let body1 =
                                                     let uu____21806 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.tcenv t_norm1
                                                        in
                                                     if uu____21806
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.tcenv body
                                                     else body  in
                                                   let uu____21808 =
                                                     encode_term body1 env'1
                                                      in
                                                   (match uu____21808 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____21826 =
                                                            let uu____21833 =
                                                              let uu____21834
                                                                =
                                                                let uu____21849
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                   in
                                                                ([[gsapp]],
                                                                  (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int "0")),
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____21849)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkForall'
                                                                uu____21834
                                                               in
                                                            let uu____21870 =
                                                              let uu____21873
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  flid.FStar_Ident.str
                                                                 in
                                                              FStar_Pervasives_Native.Some
                                                                uu____21873
                                                               in
                                                            (uu____21833,
                                                              uu____21870,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21826
                                                           in
                                                        let eqn_f =
                                                          let uu____21877 =
                                                            let uu____21884 =
                                                              let uu____21885
                                                                =
                                                                let uu____21896
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)
                                                                   in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____21896)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21885
                                                               in
                                                            (uu____21884,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21877
                                                           in
                                                        let eqn_g' =
                                                          let uu____21910 =
                                                            let uu____21917 =
                                                              let uu____21918
                                                                =
                                                                let uu____21929
                                                                  =
                                                                  let uu____21930
                                                                    =
                                                                    let uu____21935
                                                                    =
                                                                    let uu____21936
                                                                    =
                                                                    let uu____21943
                                                                    =
                                                                    let uu____21946
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____21946
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    (g,
                                                                    uu____21943)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____21936
                                                                     in
                                                                    (gsapp,
                                                                    uu____21935)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____21930
                                                                   in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____21929)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21918
                                                               in
                                                            (uu____21917,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21910
                                                           in
                                                        let uu____21969 =
                                                          let uu____21978 =
                                                            encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02
                                                             in
                                                          match uu____21978
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____22007)
                                                              ->
                                                              let vars_tm1 =
                                                                FStar_List.map
                                                                  FStar_SMTEncoding_Util.mkFreeV
                                                                  vars1
                                                                 in
                                                              let gapp =
                                                                FStar_SMTEncoding_Util.mkApp
                                                                  (g,
                                                                    (fuel_tm
                                                                    ::
                                                                    vars_tm1))
                                                                 in
                                                              let tok_corr =
                                                                let tok_app =
                                                                  let uu____22032
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                  mk_Apply
                                                                    uu____22032
                                                                    (fuel ::
                                                                    vars1)
                                                                   in
                                                                let uu____22037
                                                                  =
                                                                  let uu____22044
                                                                    =
                                                                    let uu____22045
                                                                    =
                                                                    let uu____22056
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____22056)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____22045
                                                                     in
                                                                  (uu____22044,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____22037
                                                                 in
                                                              let uu____22077
                                                                =
                                                                let uu____22084
                                                                  =
                                                                  encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp
                                                                   in
                                                                match uu____22084
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____22097
                                                                    =
                                                                    let uu____22100
                                                                    =
                                                                    let uu____22101
                                                                    =
                                                                    let uu____22108
                                                                    =
                                                                    let uu____22109
                                                                    =
                                                                    let uu____22120
                                                                    =
                                                                    let uu____22121
                                                                    =
                                                                    let uu____22126
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards
                                                                     in
                                                                    (uu____22126,
                                                                    g_typing)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____22121
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____22120)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____22109
                                                                     in
                                                                    (uu____22108,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____22101
                                                                     in
                                                                    [uu____22100]
                                                                     in
                                                                    (d3,
                                                                    uu____22097)
                                                                 in
                                                              (match uu____22077
                                                               with
                                                               | (aux_decls,typing_corr)
                                                                   ->
                                                                   ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr])))
                                                           in
                                                        (match uu____21969
                                                         with
                                                         | (aux_decls,g_typing)
                                                             ->
                                                             ((FStar_List.append
                                                                 binder_decls
                                                                 (FStar_List.append
                                                                    decls2
                                                                    (
                                                                    FStar_List.append
                                                                    aux_decls
                                                                    [decl_g;
                                                                    decl_g_tok]))),
                                                               (FStar_List.append
                                                                  [eqn_g;
                                                                  eqn_g';
                                                                  eqn_f]
                                                                  g_typing),
                                                               env02))))))))
                               in
                            let uu____22191 =
                              let uu____22204 =
                                FStar_List.zip3 gtoks1 typs2 bindings1  in
                              FStar_List.fold_left
                                (fun uu____22283  ->
                                   fun uu____22284  ->
                                     match (uu____22283, uu____22284) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____22439 =
                                           encode_one_binding env01 gtok ty
                                             lb
                                            in
                                         (match uu____22439 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____22204
                               in
                            (match uu____22191 with
                             | (decls2,eqns,env01) ->
                                 let uu____22512 =
                                   let isDeclFun uu___91_22524 =
                                     match uu___91_22524 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____22525 -> true
                                     | uu____22536 -> false  in
                                   let uu____22537 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten
                                      in
                                   FStar_All.pipe_right uu____22537
                                     (FStar_List.partition isDeclFun)
                                    in
                                 (match uu____22512 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns  in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01)))
                         in
                      let uu____22577 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___92_22581  ->
                                 match uu___92_22581 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____22582 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____22588 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t)
                                      in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____22588)))
                         in
                      if uu____22577
                      then (decls1, env1)
                      else
                        (try
                           if Prims.op_Negation is_rec
                           then
                             encode_non_rec_lbdef bindings typs1 toks1 env1
                           else encode_rec_lbdefs bindings typs1 toks1 env1
                         with | Inner_let_rec  -> (decls1, env1)))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____22640 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____22640
                     (FStar_String.concat " and ")
                    in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.strcat "let rec unencodeable: Skipping: " msg)
                    in
                 ([decl], env))
  
let rec (encode_sigelt :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____22689 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____22689 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____22693 = encode_sigelt' env se  in
      match uu____22693 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____22709 =
                  let uu____22710 = FStar_Util.format1 "<Skipped %s/>" nm  in
                  FStar_SMTEncoding_Term.Caption uu____22710  in
                [uu____22709]
            | uu____22711 ->
                let uu____22712 =
                  let uu____22715 =
                    let uu____22716 =
                      FStar_Util.format1 "<Start encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____22716  in
                  uu____22715 :: g  in
                let uu____22717 =
                  let uu____22720 =
                    let uu____22721 =
                      FStar_Util.format1 "</end encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____22721  in
                  [uu____22720]  in
                FStar_List.append uu____22712 uu____22717
             in
          (g1, env1)

and (encode_sigelt' :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____22734 =
          let uu____22735 = FStar_Syntax_Subst.compress t  in
          uu____22735.FStar_Syntax_Syntax.n  in
        match uu____22734 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22739)) -> s = "opaque_to_smt"
        | uu____22740 -> false  in
      let is_uninterpreted_by_smt t =
        let uu____22745 =
          let uu____22746 = FStar_Syntax_Subst.compress t  in
          uu____22746.FStar_Syntax_Syntax.n  in
        match uu____22745 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22750)) -> s = "uninterpreted_by_smt"
        | uu____22751 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____22756 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____22761 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____22764 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____22767 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____22782 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____22786 =
            let uu____22787 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               in
            FStar_All.pipe_right uu____22787 Prims.op_Negation  in
          if uu____22786
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____22813 ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_abs
                        ((ed.FStar_Syntax_Syntax.binders), tm,
                          (FStar_Pervasives_Native.Some
                             (FStar_Syntax_Util.mk_residual_comp
                                FStar_Parser_Const.effect_Tot_lid
                                FStar_Pervasives_Native.None
                                [FStar_Syntax_Syntax.TOTAL]))))
                     FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                in
             let encode_action env1 a =
               let uu____22833 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name
                  in
               match uu____22833 with
               | (aname,atok,env2) ->
                   let uu____22849 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ
                      in
                   (match uu____22849 with
                    | (formals,uu____22867) ->
                        let uu____22880 =
                          let uu____22885 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn
                             in
                          encode_term uu____22885 env2  in
                        (match uu____22880 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____22897 =
                                 let uu____22898 =
                                   let uu____22909 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____22925  ->
                                             FStar_SMTEncoding_Term.Term_sort))
                                      in
                                   (aname, uu____22909,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action"))
                                    in
                                 FStar_SMTEncoding_Term.DeclFun uu____22898
                                  in
                               [uu____22897;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))]
                                in
                             let uu____22938 =
                               let aux uu____22990 uu____22991 =
                                 match (uu____22990, uu____22991) with
                                 | ((bv,uu____23043),(env3,acc_sorts,acc)) ->
                                     let uu____23081 = gen_term_var env3 bv
                                        in
                                     (match uu____23081 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc)))
                                  in
                               FStar_List.fold_right aux formals
                                 (env2, [], [])
                                in
                             (match uu____22938 with
                              | (uu____23153,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs)
                                     in
                                  let a_eq =
                                    let uu____23176 =
                                      let uu____23183 =
                                        let uu____23184 =
                                          let uu____23195 =
                                            let uu____23196 =
                                              let uu____23201 =
                                                mk_Apply tm xs_sorts  in
                                              (app, uu____23201)  in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____23196
                                             in
                                          ([[app]], xs_sorts, uu____23195)
                                           in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____23184
                                         in
                                      (uu____23183,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____23176
                                     in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    let tok_app = mk_Apply tok_term xs_sorts
                                       in
                                    let uu____23221 =
                                      let uu____23228 =
                                        let uu____23229 =
                                          let uu____23240 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app)
                                             in
                                          ([[tok_app]], xs_sorts,
                                            uu____23240)
                                           in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____23229
                                         in
                                      (uu____23228,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____23221
                                     in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence]))))))
                in
             let uu____23259 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions
                in
             match uu____23259 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____23287,uu____23288)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____23289 = new_term_constant_and_tok_from_lid env lid  in
          (match uu____23289 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____23306,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let will_encode_definition =
            let uu____23312 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___93_23316  ->
                      match uu___93_23316 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____23317 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____23322 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____23323 -> false))
               in
            Prims.op_Negation uu____23312  in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None
                in
             let uu____23332 =
               let uu____23339 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt)
                  in
               encode_top_level_val uu____23339 env fv t quals  in
             match uu____23332 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str  in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort)
                    in
                 let uu____23354 =
                   let uu____23357 =
                     primitive_type_axioms env1.tcenv lid tname tsym  in
                   FStar_List.append decls uu____23357  in
                 (uu____23354, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____23365 = FStar_Syntax_Subst.open_univ_vars us f  in
          (match uu____23365 with
           | (uu____23374,f1) ->
               let uu____23376 = encode_formula f1 env  in
               (match uu____23376 with
                | (f2,decls) ->
                    let g =
                      let uu____23390 =
                        let uu____23391 =
                          let uu____23398 =
                            let uu____23401 =
                              let uu____23402 =
                                FStar_Syntax_Print.lid_to_string l  in
                              FStar_Util.format1 "Assumption: %s" uu____23402
                               in
                            FStar_Pervasives_Native.Some uu____23401  in
                          let uu____23403 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str)
                             in
                          (f2, uu____23398, uu____23403)  in
                        FStar_SMTEncoding_Util.mkAssume uu____23391  in
                      [uu____23390]  in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____23409) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs  in
          let uu____23421 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____23439 =
                       let uu____23442 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       uu____23442.FStar_Syntax_Syntax.fv_name  in
                     uu____23439.FStar_Syntax_Syntax.v  in
                   let uu____23443 =
                     let uu____23444 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid
                        in
                     FStar_All.pipe_left FStar_Option.isNone uu____23444  in
                   if uu____23443
                   then
                     let val_decl =
                       let uu___128_23472 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___128_23472.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___128_23472.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___128_23472.FStar_Syntax_Syntax.sigattrs)
                       }  in
                     let uu____23477 = encode_sigelt' env1 val_decl  in
                     match uu____23477 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
             in
          (match uu____23421 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____23505,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____23507;
                          FStar_Syntax_Syntax.lbtyp = uu____23508;
                          FStar_Syntax_Syntax.lbeff = uu____23509;
                          FStar_Syntax_Syntax.lbdef = uu____23510;_}::[]),uu____23511)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____23530 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____23530 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
               let x = FStar_SMTEncoding_Util.mkFreeV xx  in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])
                  in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x])  in
               let decls =
                 let uu____23559 =
                   let uu____23562 =
                     let uu____23563 =
                       let uu____23570 =
                         let uu____23571 =
                           let uu____23582 =
                             let uu____23583 =
                               let uu____23588 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x])
                                  in
                               (valid_b2t_x, uu____23588)  in
                             FStar_SMTEncoding_Util.mkEq uu____23583  in
                           ([[b2t_x]], [xx], uu____23582)  in
                         FStar_SMTEncoding_Util.mkForall uu____23571  in
                       (uu____23570,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def")
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____23563  in
                   [uu____23562]  in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____23559
                  in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____23621,uu____23622) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___94_23631  ->
                  match uu___94_23631 with
                  | FStar_Syntax_Syntax.Discriminator uu____23632 -> true
                  | uu____23633 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____23636,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____23647 =
                     let uu____23648 = FStar_List.hd l.FStar_Ident.ns  in
                     uu____23648.FStar_Ident.idText  in
                   uu____23647 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___95_23652  ->
                     match uu___95_23652 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____23653 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____23657) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___96_23674  ->
                  match uu___96_23674 with
                  | FStar_Syntax_Syntax.Projector uu____23675 -> true
                  | uu____23680 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let uu____23683 = try_lookup_free_var env l  in
          (match uu____23683 with
           | FStar_Pervasives_Native.Some uu____23690 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___129_23694 = se  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___129_23694.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___129_23694.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___129_23694.FStar_Syntax_Syntax.sigattrs)
                 }  in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____23701) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____23719) ->
          let uu____23728 = encode_sigelts env ses  in
          (match uu____23728 with
           | (g,env1) ->
               let uu____23745 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___97_23768  ->
                         match uu___97_23768 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____23769;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____23770;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____23771;_}
                             -> false
                         | uu____23774 -> true))
                  in
               (match uu____23745 with
                | (g',inversions) ->
                    let uu____23789 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___98_23810  ->
                              match uu___98_23810 with
                              | FStar_SMTEncoding_Term.DeclFun uu____23811 ->
                                  true
                              | uu____23822 -> false))
                       in
                    (match uu____23789 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____23840,tps,k,uu____23843,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___99_23860  ->
                    match uu___99_23860 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____23861 -> false))
             in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____23870 = c  in
              match uu____23870 with
              | (name,args,uu____23875,uu____23876,uu____23877) ->
                  let uu____23882 =
                    let uu____23883 =
                      let uu____23894 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____23911  ->
                                match uu____23911 with
                                | (uu____23918,sort,uu____23920) -> sort))
                         in
                      (name, uu____23894, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____23883  in
                  [uu____23882]
            else FStar_SMTEncoding_Term.constructor_to_decl c  in
          let inversion_axioms tapp vars =
            let uu____23947 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____23953 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l  in
                      FStar_All.pipe_right uu____23953 FStar_Option.isNone))
               in
            if uu____23947
            then []
            else
              (let uu____23985 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
               match uu____23985 with
               | (xxsym,xx) ->
                   let uu____23994 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____24033  ->
                             fun l  ->
                               match uu____24033 with
                               | (out,decls) ->
                                   let uu____24053 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l
                                      in
                                   (match uu____24053 with
                                    | (uu____24064,data_t) ->
                                        let uu____24066 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t
                                           in
                                        (match uu____24066 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____24112 =
                                                 let uu____24113 =
                                                   FStar_Syntax_Subst.compress
                                                     res
                                                    in
                                                 uu____24113.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____24112 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____24124,indices) ->
                                                   indices
                                               | uu____24146 -> []  in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____24170  ->
                                                         match uu____24170
                                                         with
                                                         | (x,uu____24176) ->
                                                             let uu____24177
                                                               =
                                                               let uu____24178
                                                                 =
                                                                 let uu____24185
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x
                                                                    in
                                                                 (uu____24185,
                                                                   [xx])
                                                                  in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____24178
                                                                in
                                                             push_term_var
                                                               env1 x
                                                               uu____24177)
                                                    env)
                                                in
                                             let uu____24188 =
                                               encode_args indices env1  in
                                             (match uu____24188 with
                                              | (indices1,decls') ->
                                                  (if
                                                     (FStar_List.length
                                                        indices1)
                                                       <>
                                                       (FStar_List.length
                                                          vars)
                                                   then failwith "Impossible"
                                                   else ();
                                                   (let eqs =
                                                      let uu____24214 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____24230
                                                                 =
                                                                 let uu____24235
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1
                                                                    in
                                                                 (uu____24235,
                                                                   a)
                                                                  in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____24230)
                                                          vars indices1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____24214
                                                        FStar_SMTEncoding_Util.mk_and_l
                                                       in
                                                    let uu____24238 =
                                                      let uu____24239 =
                                                        let uu____24244 =
                                                          let uu____24245 =
                                                            let uu____24250 =
                                                              mk_data_tester
                                                                env1 l xx
                                                               in
                                                            (uu____24250,
                                                              eqs)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____24245
                                                           in
                                                        (out, uu____24244)
                                                         in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____24239
                                                       in
                                                    (uu____24238,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, []))
                      in
                   (match uu____23994 with
                    | (data_ax,decls) ->
                        let uu____24263 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                        (match uu____24263 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____24274 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff])
                                      in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____24274 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                  in
                               let uu____24278 =
                                 let uu____24285 =
                                   let uu____24286 =
                                     let uu____24297 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars)
                                        in
                                     let uu____24312 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax)
                                        in
                                     ([[xx_has_type_sfuel]], uu____24297,
                                       uu____24312)
                                      in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____24286
                                    in
                                 let uu____24327 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str)
                                    in
                                 (uu____24285,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____24327)
                                  in
                               FStar_SMTEncoding_Util.mkAssume uu____24278
                                in
                             FStar_List.append decls [fuel_guarded_inversion])))
             in
          let uu____24330 =
            let uu____24343 =
              let uu____24344 = FStar_Syntax_Subst.compress k  in
              uu____24344.FStar_Syntax_Syntax.n  in
            match uu____24343 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____24389 -> (tps, k)  in
          (match uu____24330 with
           | (formals,res) ->
               let uu____24412 = FStar_Syntax_Subst.open_term formals res  in
               (match uu____24412 with
                | (formals1,res1) ->
                    let uu____24423 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env
                       in
                    (match uu____24423 with
                     | (vars,guards,env',binder_decls,uu____24448) ->
                         let uu____24461 =
                           new_term_constant_and_tok_from_lid env t  in
                         (match uu____24461 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let tapp =
                                let uu____24480 =
                                  let uu____24487 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars
                                     in
                                  (tname, uu____24487)  in
                                FStar_SMTEncoding_Util.mkApp uu____24480  in
                              let uu____24496 =
                                let tname_decl =
                                  let uu____24506 =
                                    let uu____24507 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____24539  ->
                                              match uu____24539 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false)))
                                       in
                                    let uu____24552 = varops.next_id ()  in
                                    (tname, uu____24507,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____24552, false)
                                     in
                                  constructor_or_logic_type_decl uu____24506
                                   in
                                let uu____24561 =
                                  match vars with
                                  | [] ->
                                      let uu____24574 =
                                        let uu____24575 =
                                          let uu____24578 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, [])
                                             in
                                          FStar_All.pipe_left
                                            (fun _0_44  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_44) uu____24578
                                           in
                                        push_free_var env1 t tname
                                          uu____24575
                                         in
                                      ([], uu____24574)
                                  | uu____24585 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token"))
                                         in
                                      let ttok_fresh =
                                        let uu____24594 = varops.next_id ()
                                           in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____24594
                                         in
                                      let ttok_app = mk_Apply ttok_tm vars
                                         in
                                      let pats = [[ttok_app]; [tapp]]  in
                                      let name_tok_corr =
                                        let uu____24608 =
                                          let uu____24615 =
                                            let uu____24616 =
                                              let uu____24631 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp)
                                                 in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____24631)
                                               in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____24616
                                             in
                                          (uu____24615,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____24608
                                         in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1)
                                   in
                                match uu____24561 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2)
                                 in
                              (match uu____24496 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____24671 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp
                                        in
                                     match uu____24671 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____24689 =
                                               let uu____24690 =
                                                 let uu____24697 =
                                                   let uu____24698 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm
                                                      in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____24698
                                                    in
                                                 (uu____24697,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24690
                                                in
                                             [uu____24689]
                                           else []  in
                                         let uu____24702 =
                                           let uu____24705 =
                                             let uu____24708 =
                                               let uu____24709 =
                                                 let uu____24716 =
                                                   let uu____24717 =
                                                     let uu____24728 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1)
                                                        in
                                                     ([[tapp]], vars,
                                                       uu____24728)
                                                      in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____24717
                                                    in
                                                 (uu____24716,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24709
                                                in
                                             [uu____24708]  in
                                           FStar_List.append karr uu____24705
                                            in
                                         FStar_List.append decls1 uu____24702
                                      in
                                   let aux =
                                     let uu____24744 =
                                       let uu____24747 =
                                         inversion_axioms tapp vars  in
                                       let uu____24750 =
                                         let uu____24753 =
                                           pretype_axiom env2 tapp vars  in
                                         [uu____24753]  in
                                       FStar_List.append uu____24747
                                         uu____24750
                                        in
                                     FStar_List.append kindingAx uu____24744
                                      in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux)
                                      in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24760,uu____24761,uu____24762,uu____24763,uu____24764)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24772,t,uu____24774,n_tps,uu____24776) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____24784 = new_term_constant_and_tok_from_lid env d  in
          (match uu____24784 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])  in
               let uu____24801 = FStar_Syntax_Util.arrow_formals t  in
               (match uu____24801 with
                | (formals,t_res) ->
                    let uu____24836 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                    (match uu____24836 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                            in
                         let uu____24850 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1
                            in
                         (match uu____24850 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true  in
                                          let uu____24920 =
                                            mk_term_projector_name d x  in
                                          (uu____24920,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible)))
                                 in
                              let datacons =
                                let uu____24922 =
                                  let uu____24941 = varops.next_id ()  in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____24941, true)
                                   in
                                FStar_All.pipe_right uu____24922
                                  FStar_SMTEncoding_Term.constructor_to_decl
                                 in
                              let app = mk_Apply ddtok_tm vars  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let xvars =
                                FStar_List.map FStar_SMTEncoding_Util.mkFreeV
                                  vars
                                 in
                              let dapp =
                                FStar_SMTEncoding_Util.mkApp
                                  (ddconstrsym, xvars)
                                 in
                              let uu____24980 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm
                                 in
                              (match uu____24980 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____24992::uu____24993 ->
                                         let ff =
                                           ("ty",
                                             FStar_SMTEncoding_Term.Term_sort)
                                            in
                                         let f =
                                           FStar_SMTEncoding_Util.mkFreeV ff
                                            in
                                         let vtok_app_l =
                                           mk_Apply ddtok_tm [ff]  in
                                         let vtok_app_r =
                                           mk_Apply f
                                             [(ddtok,
                                                FStar_SMTEncoding_Term.Term_sort)]
                                            in
                                         let uu____25038 =
                                           let uu____25049 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing
                                              in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____25049)
                                            in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____25038
                                     | uu____25074 -> tok_typing  in
                                   let uu____25083 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1
                                      in
                                   (match uu____25083 with
                                    | (vars',guards',env'',decls_formals,uu____25108)
                                        ->
                                        let uu____25121 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars'
                                             in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1)
                                             in
                                          encode_term_pred
                                            (FStar_Pervasives_Native.Some
                                               fuel_tm) t_res env'' dapp1
                                           in
                                        (match uu____25121 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards'
                                                in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____25152 ->
                                                   let uu____25159 =
                                                     let uu____25160 =
                                                       varops.next_id ()  in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____25160
                                                      in
                                                   [uu____25159]
                                                in
                                             let encode_elim uu____25170 =
                                               let uu____25171 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res
                                                  in
                                               match uu____25171 with
                                               | (head1,args) ->
                                                   let uu____25214 =
                                                     let uu____25215 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____25215.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____25214 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____25225;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____25226;_},uu____25227)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        let uu____25233 =
                                                          encode_args args
                                                            env'
                                                           in
                                                        (match uu____25233
                                                         with
                                                         | (encoded_args,arg_decls)
                                                             ->
                                                             let guards_for_parameter
                                                               orig_arg arg
                                                               xv =
                                                               let fv1 =
                                                                 match 
                                                                   arg.FStar_SMTEncoding_Term.tm
                                                                 with
                                                                 | FStar_SMTEncoding_Term.FreeV
                                                                    fv1 ->
                                                                    fv1
                                                                 | uu____25276
                                                                    ->
                                                                    let uu____25277
                                                                    =
                                                                    let uu____25282
                                                                    =
                                                                    let uu____25283
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____25283
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____25282)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____25277
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                  in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____25299
                                                                    =
                                                                    let uu____25300
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____25300
                                                                     in
                                                                    if
                                                                    uu____25299
                                                                    then
                                                                    let uu____25313
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____25313]
                                                                    else []))
                                                                  in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1
                                                                in
                                                             let uu____25315
                                                               =
                                                               let uu____25328
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args
                                                                  in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____25378
                                                                     ->
                                                                    fun
                                                                    uu____25379
                                                                     ->
                                                                    match 
                                                                    (uu____25378,
                                                                    uu____25379)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25474
                                                                    =
                                                                    let uu____25481
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25481
                                                                     in
                                                                    (match uu____25474
                                                                    with
                                                                    | 
                                                                    (uu____25494,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25502
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____25502
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25504
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____25504
                                                                    ::
                                                                    eqns_or_guards)
                                                                     in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    (Prims.parse_int "1")))))
                                                                 (env', [],
                                                                   [],
                                                                   (Prims.parse_int "0"))
                                                                 uu____25328
                                                                in
                                                             (match uu____25315
                                                              with
                                                              | (uu____25519,arg_vars,elim_eqns_or_guards,uu____25522)
                                                                  ->
                                                                  let arg_vars1
                                                                    =
                                                                    FStar_List.rev
                                                                    arg_vars
                                                                     in
                                                                  let ty =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (encoded_head,
                                                                    arg_vars1)
                                                                     in
                                                                  let xvars1
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                  let dapp1 =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (ddconstrsym,
                                                                    xvars1)
                                                                     in
                                                                  let ty_pred
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                                    (FStar_Pervasives_Native.Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty
                                                                     in
                                                                  let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1
                                                                     in
                                                                  let typing_inversion
                                                                    =
                                                                    let uu____25552
                                                                    =
                                                                    let uu____25559
                                                                    =
                                                                    let uu____25560
                                                                    =
                                                                    let uu____25571
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____25582
                                                                    =
                                                                    let uu____25583
                                                                    =
                                                                    let uu____25588
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____25588)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25583
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25571,
                                                                    uu____25582)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25560
                                                                     in
                                                                    (uu____25559,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25552
                                                                     in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25611
                                                                    =
                                                                    varops.fresh
                                                                    "x"  in
                                                                    (uu____25611,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____25613
                                                                    =
                                                                    let uu____25620
                                                                    =
                                                                    let uu____25621
                                                                    =
                                                                    let uu____25632
                                                                    =
                                                                    let uu____25637
                                                                    =
                                                                    let uu____25640
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____25640]
                                                                     in
                                                                    [uu____25637]
                                                                     in
                                                                    let uu____25645
                                                                    =
                                                                    let uu____25646
                                                                    =
                                                                    let uu____25651
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____25652
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____25651,
                                                                    uu____25652)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25646
                                                                     in
                                                                    (uu____25632,
                                                                    [x],
                                                                    uu____25645)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25621
                                                                     in
                                                                    let uu____25671
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____25620,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25671)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25613
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25678
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    vars
                                                                    (FStar_List.mapi
                                                                    (fun i 
                                                                    ->
                                                                    fun v1 
                                                                    ->
                                                                    if
                                                                    i < n_tps
                                                                    then []
                                                                    else
                                                                    (let uu____25706
                                                                    =
                                                                    let uu____25707
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25707
                                                                    dapp1  in
                                                                    [uu____25706])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____25678
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____25714
                                                                    =
                                                                    let uu____25721
                                                                    =
                                                                    let uu____25722
                                                                    =
                                                                    let uu____25733
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____25744
                                                                    =
                                                                    let uu____25745
                                                                    =
                                                                    let uu____25750
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____25750)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25745
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25733,
                                                                    uu____25744)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25722
                                                                     in
                                                                    (uu____25721,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25714)
                                                                     in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        let uu____25771 =
                                                          encode_args args
                                                            env'
                                                           in
                                                        (match uu____25771
                                                         with
                                                         | (encoded_args,arg_decls)
                                                             ->
                                                             let guards_for_parameter
                                                               orig_arg arg
                                                               xv =
                                                               let fv1 =
                                                                 match 
                                                                   arg.FStar_SMTEncoding_Term.tm
                                                                 with
                                                                 | FStar_SMTEncoding_Term.FreeV
                                                                    fv1 ->
                                                                    fv1
                                                                 | uu____25814
                                                                    ->
                                                                    let uu____25815
                                                                    =
                                                                    let uu____25820
                                                                    =
                                                                    let uu____25821
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____25821
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____25820)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____25815
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                  in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____25837
                                                                    =
                                                                    let uu____25838
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____25838
                                                                     in
                                                                    if
                                                                    uu____25837
                                                                    then
                                                                    let uu____25851
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____25851]
                                                                    else []))
                                                                  in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1
                                                                in
                                                             let uu____25853
                                                               =
                                                               let uu____25866
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args
                                                                  in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____25916
                                                                     ->
                                                                    fun
                                                                    uu____25917
                                                                     ->
                                                                    match 
                                                                    (uu____25916,
                                                                    uu____25917)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____26012
                                                                    =
                                                                    let uu____26019
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____26019
                                                                     in
                                                                    (match uu____26012
                                                                    with
                                                                    | 
                                                                    (uu____26032,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____26040
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____26040
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____26042
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____26042
                                                                    ::
                                                                    eqns_or_guards)
                                                                     in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    (Prims.parse_int "1")))))
                                                                 (env', [],
                                                                   [],
                                                                   (Prims.parse_int "0"))
                                                                 uu____25866
                                                                in
                                                             (match uu____25853
                                                              with
                                                              | (uu____26057,arg_vars,elim_eqns_or_guards,uu____26060)
                                                                  ->
                                                                  let arg_vars1
                                                                    =
                                                                    FStar_List.rev
                                                                    arg_vars
                                                                     in
                                                                  let ty =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (encoded_head,
                                                                    arg_vars1)
                                                                     in
                                                                  let xvars1
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                  let dapp1 =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (ddconstrsym,
                                                                    xvars1)
                                                                     in
                                                                  let ty_pred
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                                    (FStar_Pervasives_Native.Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty
                                                                     in
                                                                  let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1
                                                                     in
                                                                  let typing_inversion
                                                                    =
                                                                    let uu____26090
                                                                    =
                                                                    let uu____26097
                                                                    =
                                                                    let uu____26098
                                                                    =
                                                                    let uu____26109
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____26120
                                                                    =
                                                                    let uu____26121
                                                                    =
                                                                    let uu____26126
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____26126)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____26121
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____26109,
                                                                    uu____26120)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____26098
                                                                     in
                                                                    (uu____26097,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____26090
                                                                     in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____26149
                                                                    =
                                                                    varops.fresh
                                                                    "x"  in
                                                                    (uu____26149,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____26151
                                                                    =
                                                                    let uu____26158
                                                                    =
                                                                    let uu____26159
                                                                    =
                                                                    let uu____26170
                                                                    =
                                                                    let uu____26175
                                                                    =
                                                                    let uu____26178
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____26178]
                                                                     in
                                                                    [uu____26175]
                                                                     in
                                                                    let uu____26183
                                                                    =
                                                                    let uu____26184
                                                                    =
                                                                    let uu____26189
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____26190
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____26189,
                                                                    uu____26190)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____26184
                                                                     in
                                                                    (uu____26170,
                                                                    [x],
                                                                    uu____26183)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____26159
                                                                     in
                                                                    let uu____26209
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____26158,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____26209)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____26151
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____26216
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    vars
                                                                    (FStar_List.mapi
                                                                    (fun i 
                                                                    ->
                                                                    fun v1 
                                                                    ->
                                                                    if
                                                                    i < n_tps
                                                                    then []
                                                                    else
                                                                    (let uu____26244
                                                                    =
                                                                    let uu____26245
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____26245
                                                                    dapp1  in
                                                                    [uu____26244])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____26216
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____26252
                                                                    =
                                                                    let uu____26259
                                                                    =
                                                                    let uu____26260
                                                                    =
                                                                    let uu____26271
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____26282
                                                                    =
                                                                    let uu____26283
                                                                    =
                                                                    let uu____26288
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____26288)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____26283
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____26271,
                                                                    uu____26282)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____26260
                                                                     in
                                                                    (uu____26259,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____26252)
                                                                     in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____26307 ->
                                                        ((let uu____26309 =
                                                            let uu____26314 =
                                                              let uu____26315
                                                                =
                                                                FStar_Syntax_Print.lid_to_string
                                                                  d
                                                                 in
                                                              let uu____26316
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1
                                                                 in
                                                              FStar_Util.format2
                                                                "Constructor %s builds an unexpected type %s\n"
                                                                uu____26315
                                                                uu____26316
                                                               in
                                                            (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                              uu____26314)
                                                             in
                                                          FStar_Errors.log_issue
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____26309);
                                                         ([], [])))
                                                in
                                             let uu____26321 = encode_elim ()
                                                in
                                             (match uu____26321 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____26341 =
                                                      let uu____26344 =
                                                        let uu____26347 =
                                                          let uu____26350 =
                                                            let uu____26353 =
                                                              let uu____26354
                                                                =
                                                                let uu____26365
                                                                  =
                                                                  let uu____26368
                                                                    =
                                                                    let uu____26369
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____26369
                                                                     in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____26368
                                                                   in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____26365)
                                                                 in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____26354
                                                               in
                                                            [uu____26353]  in
                                                          let uu____26374 =
                                                            let uu____26377 =
                                                              let uu____26380
                                                                =
                                                                let uu____26383
                                                                  =
                                                                  let uu____26386
                                                                    =
                                                                    let uu____26389
                                                                    =
                                                                    let uu____26392
                                                                    =
                                                                    let uu____26393
                                                                    =
                                                                    let uu____26400
                                                                    =
                                                                    let uu____26401
                                                                    =
                                                                    let uu____26412
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____26412)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____26401
                                                                     in
                                                                    (uu____26400,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____26393
                                                                     in
                                                                    let uu____26425
                                                                    =
                                                                    let uu____26428
                                                                    =
                                                                    let uu____26429
                                                                    =
                                                                    let uu____26436
                                                                    =
                                                                    let uu____26437
                                                                    =
                                                                    let uu____26448
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars'  in
                                                                    let uu____26459
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____26448,
                                                                    uu____26459)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____26437
                                                                     in
                                                                    (uu____26436,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____26429
                                                                     in
                                                                    [uu____26428]
                                                                     in
                                                                    uu____26392
                                                                    ::
                                                                    uu____26425
                                                                     in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____26389
                                                                     in
                                                                  FStar_List.append
                                                                    uu____26386
                                                                    elim
                                                                   in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____26383
                                                                 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____26380
                                                               in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____26377
                                                             in
                                                          FStar_List.append
                                                            uu____26350
                                                            uu____26374
                                                           in
                                                        FStar_List.append
                                                          decls3 uu____26347
                                                         in
                                                      FStar_List.append
                                                        decls2 uu____26344
                                                       in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____26341
                                                     in
                                                  ((FStar_List.append
                                                      datacons g), env1)))))))))

and (encode_sigelts :
  env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,env_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____26505  ->
              fun se  ->
                match uu____26505 with
                | (g,env1) ->
                    let uu____26525 = encode_sigelt env1 se  in
                    (match uu____26525 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____26582 =
        match uu____26582 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____26614 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.Primops;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort
                    in
                 ((let uu____26620 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____26620
                   then
                     let uu____26621 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____26622 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____26623 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____26621 uu____26622 uu____26623
                   else ());
                  (let uu____26625 = encode_term t1 env1  in
                   match uu____26625 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____26641 =
                         let uu____26648 =
                           let uu____26649 =
                             let uu____26650 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.strcat uu____26650
                               (Prims.strcat "_" (Prims.string_of_int i))
                              in
                           Prims.strcat "x_" uu____26649  in
                         new_term_constant_from_string env1 x uu____26648  in
                       (match uu____26641 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____26666 = FStar_Options.log_queries ()
                                 in
                              if uu____26666
                              then
                                let uu____26669 =
                                  let uu____26670 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____26671 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____26672 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____26670 uu____26671 uu____26672
                                   in
                                FStar_Pervasives_Native.Some uu____26669
                              else FStar_Pervasives_Native.None  in
                            let ax =
                              let a_name = Prims.strcat "binder_" xxsym  in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name)
                               in
                            let g =
                              FStar_List.append
                                [FStar_SMTEncoding_Term.DeclFun
                                   (xxsym, [],
                                     FStar_SMTEncoding_Term.Term_sort,
                                     caption)]
                                (FStar_List.append decls' [ax])
                               in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____26688,t)) ->
                 let t_norm = whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____26702 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____26702 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____26725,se,uu____26727) ->
                 let uu____26732 = encode_sigelt env1 se  in
                 (match uu____26732 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____26749,se) ->
                 let uu____26755 = encode_sigelt env1 se  in
                 (match uu____26755 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____26772 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____26772 with | (uu____26795,decls,env1) -> (decls, env1)
  
let encode_labels :
  'Auu____26807 'Auu____26808 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____26808,'Auu____26807)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____26876  ->
              match uu____26876 with
              | (l,uu____26888,uu____26889) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____26935  ->
              match uu____26935 with
              | (l,uu____26949,uu____26950) ->
                  let uu____26959 =
                    FStar_All.pipe_left
                      (fun _0_45  -> FStar_SMTEncoding_Term.Echo _0_45)
                      (FStar_Pervasives_Native.fst l)
                     in
                  let uu____26960 =
                    let uu____26963 =
                      let uu____26964 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____26964  in
                    [uu____26963]  in
                  uu____26959 :: uu____26960))
       in
    (prefix1, suffix)
  
let (last_env : env_t Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> Prims.unit) =
  fun tcenv  ->
    let uu____27015 =
      let uu____27018 =
        let uu____27019 = FStar_Util.smap_create (Prims.parse_int "100")  in
        let uu____27022 =
          let uu____27023 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____27023 FStar_Ident.string_of_lid  in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____27019;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____27022
        }  in
      [uu____27018]  in
    FStar_ST.op_Colon_Equals last_env uu____27015
  
let (get_env : FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t) =
  fun cmn  ->
    fun tcenv  ->
      let uu____27053 = FStar_ST.op_Bang last_env  in
      match uu____27053 with
      | [] -> failwith "No env; call init first!"
      | e::uu____27080 ->
          let uu___130_27083 = e  in
          let uu____27084 = FStar_Ident.string_of_lid cmn  in
          {
            bindings = (uu___130_27083.bindings);
            depth = (uu___130_27083.depth);
            tcenv;
            warn = (uu___130_27083.warn);
            cache = (uu___130_27083.cache);
            nolabels = (uu___130_27083.nolabels);
            use_zfuel_name = (uu___130_27083.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___130_27083.encode_non_total_function_typ);
            current_module_name = uu____27084
          }
  
let (set_env : env_t -> Prims.unit) =
  fun env  ->
    let uu____27088 = FStar_ST.op_Bang last_env  in
    match uu____27088 with
    | [] -> failwith "Empty env stack"
    | uu____27114::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : Prims.unit -> Prims.unit) =
  fun uu____27143  ->
    let uu____27144 = FStar_ST.op_Bang last_env  in
    match uu____27144 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache  in
        let top =
          let uu___131_27178 = hd1  in
          {
            bindings = (uu___131_27178.bindings);
            depth = (uu___131_27178.depth);
            tcenv = (uu___131_27178.tcenv);
            warn = (uu___131_27178.warn);
            cache = refs;
            nolabels = (uu___131_27178.nolabels);
            use_zfuel_name = (uu___131_27178.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___131_27178.encode_non_total_function_typ);
            current_module_name = (uu___131_27178.current_module_name)
          }  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : Prims.unit -> Prims.unit) =
  fun uu____27204  ->
    let uu____27205 = FStar_ST.op_Bang last_env  in
    match uu____27205 with
    | [] -> failwith "Popping an empty stack"
    | uu____27231::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (init : FStar_TypeChecker_Env.env -> Prims.unit) =
  fun tcenv  ->
    init_env tcenv;
    FStar_SMTEncoding_Z3.init ();
    FStar_SMTEncoding_Z3.giveZ3 [FStar_SMTEncoding_Term.DefPrelude]
  
let (push : Prims.string -> Prims.unit) =
  fun msg  -> push_env (); varops.push (); FStar_SMTEncoding_Z3.push msg 
let (pop : Prims.string -> Prims.unit) =
  fun msg  -> pop_env (); varops.pop (); FStar_SMTEncoding_Z3.pop msg 
let (open_fact_db_tags :
  env_t -> FStar_SMTEncoding_Term.fact_db_id Prims.list) = fun env  -> [] 
let (place_decl_in_fact_dbs :
  env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decl -> FStar_SMTEncoding_Term.decl)
  =
  fun env  ->
    fun fact_db_ids  ->
      fun d  ->
        match (fact_db_ids, d) with
        | (uu____27295::uu____27296,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___132_27304 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___132_27304.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___132_27304.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___132_27304.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____27305 -> d
  
let (fact_dbs_for_lid :
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list) =
  fun env  ->
    fun lid  ->
      let uu____27320 =
        let uu____27323 =
          let uu____27324 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____27324  in
        let uu____27325 = open_fact_db_tags env  in uu____27323 ::
          uu____27325
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____27320
  
let (encode_top_level_facts :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decl Prims.list,env_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun se  ->
      let fact_db_ids =
        FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
          (FStar_List.collect (fact_dbs_for_lid env))
         in
      let uu____27347 = encode_sigelt env se  in
      match uu____27347 with
      | (g,env1) ->
          let g1 =
            FStar_All.pipe_right g
              (FStar_List.map (place_decl_in_fact_dbs env1 fact_db_ids))
             in
          (g1, env1)
  
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit) =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____27383 = FStar_Options.log_queries ()  in
        if uu____27383
        then
          let uu____27386 =
            let uu____27387 =
              let uu____27388 =
                let uu____27389 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____27389 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____27388  in
            FStar_SMTEncoding_Term.Caption uu____27387  in
          uu____27386 :: decls
        else decls  in
      (let uu____27400 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____27400
       then
         let uu____27401 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____27401
       else ());
      (let env =
         let uu____27404 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____27404 tcenv  in
       let uu____27405 = encode_top_level_facts env se  in
       match uu____27405 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____27419 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 uu____27419)))
  
let (encode_modul :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit) =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
         in
      (let uu____27431 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____27431
       then
         let uu____27432 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.declarations)
             Prims.string_of_int
            in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s declarations\n" name
           uu____27432
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv  in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____27467  ->
                 fun se  ->
                   match uu____27467 with
                   | (g,env2) ->
                       let uu____27487 = encode_top_level_facts env2 se  in
                       (match uu____27487 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1))
          in
       let uu____27510 =
         encode_signature
           (let uu___133_27519 = env  in
            {
              bindings = (uu___133_27519.bindings);
              depth = (uu___133_27519.depth);
              tcenv = (uu___133_27519.tcenv);
              warn = false;
              cache = (uu___133_27519.cache);
              nolabels = (uu___133_27519.nolabels);
              use_zfuel_name = (uu___133_27519.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___133_27519.encode_non_total_function_typ);
              current_module_name = (uu___133_27519.current_module_name)
            }) modul.FStar_Syntax_Syntax.declarations
          in
       match uu____27510 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____27536 = FStar_Options.log_queries ()  in
             if uu____27536
             then
               let msg = Prims.strcat "Externals for " name  in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1  in
           (set_env
              (let uu___134_27544 = env1  in
               {
                 bindings = (uu___134_27544.bindings);
                 depth = (uu___134_27544.depth);
                 tcenv = (uu___134_27544.tcenv);
                 warn = true;
                 cache = (uu___134_27544.cache);
                 nolabels = (uu___134_27544.nolabels);
                 use_zfuel_name = (uu___134_27544.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___134_27544.encode_non_total_function_typ);
                 current_module_name = (uu___134_27544.current_module_name)
               });
            (let uu____27546 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
             if uu____27546
             then FStar_Util.print1 "Done encoding externals for %s\n" name
             else ());
            (let decls1 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 decls1)))
  
let (encode_query :
  (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_ErrorReporting.label
                                                  Prims.list,FStar_SMTEncoding_Term.decl,
          FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple4)
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____27598 =
           let uu____27599 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____27599.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____27598);
        (let env =
           let uu____27601 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____27601 tcenv  in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) []
            in
         let uu____27613 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____27648 = aux rest  in
                 (match uu____27648 with
                  | (out,rest1) ->
                      let t =
                        let uu____27678 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____27678 with
                        | FStar_Pervasives_Native.Some uu____27683 ->
                            let uu____27684 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____27684
                              x.FStar_Syntax_Syntax.sort
                        | uu____27685 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t
                         in
                      let uu____27689 =
                        let uu____27692 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___135_27695 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___135_27695.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___135_27695.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____27692 :: out  in
                      (uu____27689, rest1))
             | uu____27700 -> ([], bindings1)  in
           let uu____27707 = aux bindings  in
           match uu____27707 with
           | (closing,bindings1) ->
               let uu____27732 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____27732, bindings1)
            in
         match uu____27613 with
         | (q1,bindings1) ->
             let uu____27755 =
               let uu____27760 =
                 FStar_List.filter
                   (fun uu___100_27765  ->
                      match uu___100_27765 with
                      | FStar_TypeChecker_Env.Binding_sig uu____27766 ->
                          false
                      | uu____27773 -> true) bindings1
                  in
               encode_env_bindings env uu____27760  in
             (match uu____27755 with
              | (env_decls,env1) ->
                  ((let uu____27791 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery"))
                       in
                    if uu____27791
                    then
                      let uu____27792 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____27792
                    else ());
                   (let uu____27794 = encode_formula q1 env1  in
                    match uu____27794 with
                    | (phi,qdecls) ->
                        let uu____27815 =
                          let uu____27820 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____27820 phi
                           in
                        (match uu____27815 with
                         | (labels,phi1) ->
                             let uu____27837 = encode_labels labels  in
                             (match uu____27837 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls)
                                     in
                                  let qry =
                                    let uu____27874 =
                                      let uu____27881 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____27882 =
                                        varops.mk_unique "@query"  in
                                      (uu____27881,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____27882)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____27874
                                     in
                                  let suffix =
                                    FStar_List.append
                                      [FStar_SMTEncoding_Term.Echo "<labels>"]
                                      (FStar_List.append label_suffix
                                         [FStar_SMTEncoding_Term.Echo
                                            "</labels>";
                                         FStar_SMTEncoding_Term.Echo "Done!"])
                                     in
                                  (query_prelude, labels, qry, suffix)))))))
  