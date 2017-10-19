open Prims
let add_fuel:
  'Auu____7 . 'Auu____7 -> 'Auu____7 Prims.list -> 'Auu____7 Prims.list =
  fun x  ->
    fun tl1  ->
      let uu____22 = FStar_Options.unthrottle_inductives () in
      if uu____22 then tl1 else x :: tl1
let withenv:
  'Auu____36 'Auu____37 'Auu____38 .
    'Auu____38 ->
      ('Auu____37,'Auu____36) FStar_Pervasives_Native.tuple2 ->
        ('Auu____37,'Auu____36,'Auu____38) FStar_Pervasives_Native.tuple3
  = fun c  -> fun uu____56  -> match uu____56 with | (a,b) -> (a, b, c)
let vargs:
  'Auu____71 'Auu____72 'Auu____73 .
    (('Auu____73,'Auu____72) FStar_Util.either,'Auu____71)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      (('Auu____73,'Auu____72) FStar_Util.either,'Auu____71)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun args  ->
    FStar_List.filter
      (fun uu___132_119  ->
         match uu___132_119 with
         | (FStar_Util.Inl uu____128,uu____129) -> false
         | uu____134 -> true) args
let subst_lcomp_opt:
  'Auu____149 .
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      (FStar_Syntax_Syntax.lcomp,'Auu____149) FStar_Util.either
        FStar_Pervasives_Native.option ->
        (FStar_Syntax_Syntax.lcomp,'Auu____149) FStar_Util.either
          FStar_Pervasives_Native.option
  =
  fun s  ->
    fun l  ->
      match l with
      | FStar_Pervasives_Native.Some (FStar_Util.Inl l1) ->
          let uu____185 =
            let uu____190 =
              let uu____191 =
                let uu____194 = l1.FStar_Syntax_Syntax.comp () in
                FStar_Syntax_Subst.subst_comp s uu____194 in
              FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____191 in
            FStar_Util.Inl uu____190 in
          FStar_Pervasives_Native.Some uu____185
      | uu____201 -> l
let escape: Prims.string -> Prims.string =
  fun s  -> FStar_Util.replace_char s 39 95
let mk_term_projector_name:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string =
  fun lid  ->
    fun a  ->
      let a1 =
        let uu___155_221 = a in
        let uu____222 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname in
        {
          FStar_Syntax_Syntax.ppname = uu____222;
          FStar_Syntax_Syntax.index =
            (uu___155_221.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___155_221.FStar_Syntax_Syntax.sort)
        } in
      let uu____223 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
      FStar_All.pipe_left escape uu____223
let primitive_projector_by_pos:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string
  =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____239 =
          let uu____240 =
            FStar_Util.format2
              "Projector %s on data constructor %s not found"
              (Prims.string_of_int i) lid.FStar_Ident.str in
          failwith uu____240 in
        let uu____241 = FStar_TypeChecker_Env.lookup_datacon env lid in
        match uu____241 with
        | (uu____246,t) ->
            let uu____248 =
              let uu____249 = FStar_Syntax_Subst.compress t in
              uu____249.FStar_Syntax_Syntax.n in
            (match uu____248 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____270 = FStar_Syntax_Subst.open_comp bs c in
                 (match uu____270 with
                  | (binders,uu____276) ->
                      if
                        (i < (Prims.parse_int "0")) ||
                          (i >= (FStar_List.length binders))
                      then fail ()
                      else
                        (let b = FStar_List.nth binders i in
                         mk_term_projector_name lid
                           (FStar_Pervasives_Native.fst b)))
             | uu____291 -> fail ())
let mk_term_projector_name_by_pos:
  FStar_Ident.lident -> Prims.int -> Prims.string =
  fun lid  ->
    fun i  ->
      let uu____300 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (Prims.string_of_int i) in
      FStar_All.pipe_left escape uu____300
let mk_term_projector:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term
  =
  fun lid  ->
    fun a  ->
      let uu____309 =
        let uu____314 = mk_term_projector_name lid a in
        (uu____314,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____309
let mk_term_projector_by_pos:
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term =
  fun lid  ->
    fun i  ->
      let uu____323 =
        let uu____328 = mk_term_projector_name_by_pos lid i in
        (uu____328,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____323
let mk_data_tester:
  'Auu____337 .
    'Auu____337 ->
      FStar_Ident.lident ->
        FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term
  =
  fun env  ->
    fun l  ->
      fun x  -> FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x
type varops_t =
  {
  push: Prims.unit -> Prims.unit;
  pop: Prims.unit -> Prims.unit;
  new_var: FStar_Ident.ident -> Prims.int -> Prims.string;
  new_fvar: FStar_Ident.lident -> Prims.string;
  fresh: Prims.string -> Prims.string;
  string_const: Prims.string -> FStar_SMTEncoding_Term.term;
  next_id: Prims.unit -> Prims.int;
  mk_unique: Prims.string -> Prims.string;}[@@deriving show]
let __proj__Mkvarops_t__item__push: varops_t -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__push
let __proj__Mkvarops_t__item__pop: varops_t -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__pop
let __proj__Mkvarops_t__item__new_var:
  varops_t -> FStar_Ident.ident -> Prims.int -> Prims.string =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__new_var
let __proj__Mkvarops_t__item__new_fvar:
  varops_t -> FStar_Ident.lident -> Prims.string =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__new_fvar
let __proj__Mkvarops_t__item__fresh: varops_t -> Prims.string -> Prims.string
  =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__fresh
let __proj__Mkvarops_t__item__string_const:
  varops_t -> Prims.string -> FStar_SMTEncoding_Term.term =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__string_const
let __proj__Mkvarops_t__item__next_id: varops_t -> Prims.unit -> Prims.int =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__next_id
let __proj__Mkvarops_t__item__mk_unique:
  varops_t -> Prims.string -> Prims.string =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__mk_unique
let varops: varops_t =
  let initial_ctr = Prims.parse_int "100" in
  let ctr = FStar_Util.mk_ref initial_ctr in
  let new_scope uu____718 =
    let uu____719 = FStar_Util.smap_create (Prims.parse_int "100") in
    let uu____722 = FStar_Util.smap_create (Prims.parse_int "100") in
    (uu____719, uu____722) in
  let scopes =
    let uu____742 = let uu____753 = new_scope () in [uu____753] in
    FStar_Util.mk_ref uu____742 in
  let mk_unique y =
    let y1 = escape y in
    let y2 =
      let uu____794 =
        let uu____797 = FStar_ST.op_Bang scopes in
        FStar_Util.find_map uu____797
          (fun uu____899  ->
             match uu____899 with
             | (names1,uu____911) -> FStar_Util.smap_try_find names1 y1) in
      match uu____794 with
      | FStar_Pervasives_Native.None  -> y1
      | FStar_Pervasives_Native.Some uu____920 ->
          (FStar_Util.incr ctr;
           (let uu____943 =
              let uu____944 =
                let uu____945 = FStar_ST.op_Bang ctr in
                Prims.string_of_int uu____945 in
              Prims.strcat "__" uu____944 in
            Prims.strcat y1 uu____943)) in
    let top_scope =
      let uu____1009 =
        let uu____1018 = FStar_ST.op_Bang scopes in FStar_List.hd uu____1018 in
      FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1009 in
    FStar_Util.smap_add top_scope y2 true; y2 in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn))) in
  let new_fvar lid = mk_unique lid.FStar_Ident.str in
  let next_id1 uu____1146 = FStar_Util.incr ctr; FStar_ST.op_Bang ctr in
  let fresh1 pfx =
    let uu____1233 =
      let uu____1234 = next_id1 () in
      FStar_All.pipe_left Prims.string_of_int uu____1234 in
    FStar_Util.format2 "%s_%s" pfx uu____1233 in
  let string_const s =
    let uu____1239 =
      let uu____1242 = FStar_ST.op_Bang scopes in
      FStar_Util.find_map uu____1242
        (fun uu____1344  ->
           match uu____1344 with
           | (uu____1355,strings) -> FStar_Util.smap_try_find strings s) in
    match uu____1239 with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None  ->
        let id = next_id1 () in
        let f =
          let uu____1368 = FStar_SMTEncoding_Util.mk_String_const id in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____1368 in
        let top_scope =
          let uu____1372 =
            let uu____1381 = FStar_ST.op_Bang scopes in
            FStar_List.hd uu____1381 in
          FStar_All.pipe_left FStar_Pervasives_Native.snd uu____1372 in
        (FStar_Util.smap_add top_scope s f; f) in
  let push1 uu____1498 =
    let uu____1499 =
      let uu____1510 = new_scope () in
      let uu____1519 = FStar_ST.op_Bang scopes in uu____1510 :: uu____1519 in
    FStar_ST.op_Colon_Equals scopes uu____1499 in
  let pop1 uu____1701 =
    let uu____1702 =
      let uu____1713 = FStar_ST.op_Bang scopes in FStar_List.tl uu____1713 in
    FStar_ST.op_Colon_Equals scopes uu____1702 in
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
let unmangle: FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.bv =
  fun x  ->
    let uu___156_1896 = x in
    let uu____1897 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____1897;
      FStar_Syntax_Syntax.index = (uu___156_1896.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___156_1896.FStar_Syntax_Syntax.sort)
    }
type binding =
  | Binding_var of (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
  FStar_Pervasives_Native.tuple2
  | Binding_fvar of
  (FStar_Ident.lident,Prims.string,FStar_SMTEncoding_Term.term
                                     FStar_Pervasives_Native.option,FStar_SMTEncoding_Term.term
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple4[@@deriving show]
let uu___is_Binding_var: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____1931 -> false
let __proj__Binding_var__item___0:
  binding ->
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_fvar: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____1969 -> false
let __proj__Binding_fvar__item___0:
  binding ->
    (FStar_Ident.lident,Prims.string,FStar_SMTEncoding_Term.term
                                       FStar_Pervasives_Native.option,
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Binding_fvar _0 -> _0
let binder_of_eithervar:
  'Auu____2020 'Auu____2021 .
    'Auu____2021 ->
      ('Auu____2021,'Auu____2020 FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  = fun v1  -> (v1, FStar_Pervasives_Native.None)
type cache_entry =
  {
  cache_symbol_name: Prims.string;
  cache_symbol_arg_sorts: FStar_SMTEncoding_Term.sort Prims.list;
  cache_symbol_decls: FStar_SMTEncoding_Term.decl Prims.list;
  cache_symbol_assumption_names: Prims.string Prims.list;}[@@deriving show]
let __proj__Mkcache_entry__item__cache_symbol_name:
  cache_entry -> Prims.string =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name = __fname__cache_symbol_name;
        cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts;
        cache_symbol_decls = __fname__cache_symbol_decls;
        cache_symbol_assumption_names =
          __fname__cache_symbol_assumption_names;_}
        -> __fname__cache_symbol_name
let __proj__Mkcache_entry__item__cache_symbol_arg_sorts:
  cache_entry -> FStar_SMTEncoding_Term.sort Prims.list =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name = __fname__cache_symbol_name;
        cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts;
        cache_symbol_decls = __fname__cache_symbol_decls;
        cache_symbol_assumption_names =
          __fname__cache_symbol_assumption_names;_}
        -> __fname__cache_symbol_arg_sorts
let __proj__Mkcache_entry__item__cache_symbol_decls:
  cache_entry -> FStar_SMTEncoding_Term.decl Prims.list =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name = __fname__cache_symbol_name;
        cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts;
        cache_symbol_decls = __fname__cache_symbol_decls;
        cache_symbol_assumption_names =
          __fname__cache_symbol_assumption_names;_}
        -> __fname__cache_symbol_decls
let __proj__Mkcache_entry__item__cache_symbol_assumption_names:
  cache_entry -> Prims.string Prims.list =
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
  bindings: binding Prims.list;
  depth: Prims.int;
  tcenv: FStar_TypeChecker_Env.env;
  warn: Prims.bool;
  cache: cache_entry FStar_Util.smap;
  nolabels: Prims.bool;
  use_zfuel_name: Prims.bool;
  encode_non_total_function_typ: Prims.bool;
  current_module_name: Prims.string;}[@@deriving show]
let __proj__Mkenv_t__item__bindings: env_t -> binding Prims.list =
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
let __proj__Mkenv_t__item__depth: env_t -> Prims.int =
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
let __proj__Mkenv_t__item__tcenv: env_t -> FStar_TypeChecker_Env.env =
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
let __proj__Mkenv_t__item__warn: env_t -> Prims.bool =
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
let __proj__Mkenv_t__item__cache: env_t -> cache_entry FStar_Util.smap =
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
let __proj__Mkenv_t__item__nolabels: env_t -> Prims.bool =
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
let __proj__Mkenv_t__item__use_zfuel_name: env_t -> Prims.bool =
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
let __proj__Mkenv_t__item__encode_non_total_function_typ: env_t -> Prims.bool
  =
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
let __proj__Mkenv_t__item__current_module_name: env_t -> Prims.string =
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
let mk_cache_entry:
  'Auu____2335 .
    'Auu____2335 ->
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
                 (fun uu___133_2369  ->
                    match uu___133_2369 with
                    | FStar_SMTEncoding_Term.Assume a ->
                        [a.FStar_SMTEncoding_Term.assumption_name]
                    | uu____2373 -> [])) in
          {
            cache_symbol_name = tsym;
            cache_symbol_arg_sorts = cvar_sorts;
            cache_symbol_decls = t_decls;
            cache_symbol_assumption_names = names1
          }
let use_cache_entry: cache_entry -> FStar_SMTEncoding_Term.decl Prims.list =
  fun ce  ->
    [FStar_SMTEncoding_Term.RetainAssumptions
       (ce.cache_symbol_assumption_names)]
let print_env: env_t -> Prims.string =
  fun e  ->
    let uu____2384 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___134_2394  ->
              match uu___134_2394 with
              | Binding_var (x,uu____2396) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____2398,uu____2399,uu____2400) ->
                  FStar_Syntax_Print.lid_to_string l)) in
    FStar_All.pipe_right uu____2384 (FStar_String.concat ", ")
let lookup_binding:
  'Auu____2417 .
    env_t ->
      (binding -> 'Auu____2417 FStar_Pervasives_Native.option) ->
        'Auu____2417 FStar_Pervasives_Native.option
  = fun env  -> fun f  -> FStar_Util.find_map env.bindings f
let caption_t:
  env_t ->
    FStar_Syntax_Syntax.term -> Prims.string FStar_Pervasives_Native.option
  =
  fun env  ->
    fun t  ->
      let uu____2447 =
        FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
      if uu____2447
      then
        let uu____2450 = FStar_Syntax_Print.term_to_string t in
        FStar_Pervasives_Native.Some uu____2450
      else FStar_Pervasives_Native.None
let fresh_fvar:
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string,FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x in
      let uu____2465 = FStar_SMTEncoding_Util.mkFreeV (xsym, s) in
      (xsym, uu____2465)
let gen_term_var:
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string,FStar_SMTEncoding_Term.term,env_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun x  ->
      let ysym = Prims.strcat "@x" (Prims.string_of_int env.depth) in
      let y =
        FStar_SMTEncoding_Util.mkFreeV
          (ysym, FStar_SMTEncoding_Term.Term_sort) in
      (ysym, y,
        (let uu___157_2483 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___157_2483.tcenv);
           warn = (uu___157_2483.warn);
           cache = (uu___157_2483.cache);
           nolabels = (uu___157_2483.nolabels);
           use_zfuel_name = (uu___157_2483.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___157_2483.encode_non_total_function_typ);
           current_module_name = (uu___157_2483.current_module_name)
         }))
let new_term_constant:
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string,FStar_SMTEncoding_Term.term,env_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun x  ->
      let ysym =
        varops.new_var x.FStar_Syntax_Syntax.ppname
          x.FStar_Syntax_Syntax.index in
      let y = FStar_SMTEncoding_Util.mkApp (ysym, []) in
      (ysym, y,
        (let uu___158_2503 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___158_2503.depth);
           tcenv = (uu___158_2503.tcenv);
           warn = (uu___158_2503.warn);
           cache = (uu___158_2503.cache);
           nolabels = (uu___158_2503.nolabels);
           use_zfuel_name = (uu___158_2503.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___158_2503.encode_non_total_function_typ);
           current_module_name = (uu___158_2503.current_module_name)
         }))
let new_term_constant_from_string:
  env_t ->
    FStar_Syntax_Syntax.bv ->
      Prims.string ->
        (Prims.string,FStar_SMTEncoding_Term.term,env_t)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun x  ->
      fun str  ->
        let ysym = varops.mk_unique str in
        let y = FStar_SMTEncoding_Util.mkApp (ysym, []) in
        (ysym, y,
          (let uu___159_2527 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___159_2527.depth);
             tcenv = (uu___159_2527.tcenv);
             warn = (uu___159_2527.warn);
             cache = (uu___159_2527.cache);
             nolabels = (uu___159_2527.nolabels);
             use_zfuel_name = (uu___159_2527.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___159_2527.encode_non_total_function_typ);
             current_module_name = (uu___159_2527.current_module_name)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___160_2540 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___160_2540.depth);
          tcenv = (uu___160_2540.tcenv);
          warn = (uu___160_2540.warn);
          cache = (uu___160_2540.cache);
          nolabels = (uu___160_2540.nolabels);
          use_zfuel_name = (uu___160_2540.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___160_2540.encode_non_total_function_typ);
          current_module_name = (uu___160_2540.current_module_name)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___135_2566  ->
             match uu___135_2566 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 FStar_Pervasives_Native.Some (b, t)
             | uu____2579 -> FStar_Pervasives_Native.None) in
      let uu____2584 = aux a in
      match uu____2584 with
      | FStar_Pervasives_Native.None  ->
          let a2 = unmangle a in
          let uu____2596 = aux a2 in
          (match uu____2596 with
           | FStar_Pervasives_Native.None  ->
               let uu____2607 =
                 let uu____2608 = FStar_Syntax_Print.bv_to_string a2 in
                 let uu____2609 = print_env env in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____2608 uu____2609 in
               failwith uu____2607
           | FStar_Pervasives_Native.Some (b,t) -> t)
      | FStar_Pervasives_Native.Some (b,t) -> t
let new_term_constant_and_tok_from_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string,Prims.string,env_t) FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun x  ->
      let fname = varops.new_fvar x in
      let ftok = Prims.strcat fname "@tok" in
      let uu____2638 =
        let uu___161_2639 = env in
        let uu____2640 =
          let uu____2643 =
            let uu____2644 =
              let uu____2657 =
                let uu____2660 = FStar_SMTEncoding_Util.mkApp (ftok, []) in
                FStar_All.pipe_left
                  (fun _0_41  -> FStar_Pervasives_Native.Some _0_41)
                  uu____2660 in
              (x, fname, uu____2657, FStar_Pervasives_Native.None) in
            Binding_fvar uu____2644 in
          uu____2643 :: (env.bindings) in
        {
          bindings = uu____2640;
          depth = (uu___161_2639.depth);
          tcenv = (uu___161_2639.tcenv);
          warn = (uu___161_2639.warn);
          cache = (uu___161_2639.cache);
          nolabels = (uu___161_2639.nolabels);
          use_zfuel_name = (uu___161_2639.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___161_2639.encode_non_total_function_typ);
          current_module_name = (uu___161_2639.current_module_name)
        } in
      (fname, ftok, uu____2638)
let try_lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string,FStar_SMTEncoding_Term.term
                      FStar_Pervasives_Native.option,FStar_SMTEncoding_Term.term
                                                       FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple3 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun a  ->
      lookup_binding env
        (fun uu___136_2704  ->
           match uu___136_2704 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               FStar_Pervasives_Native.Some (t1, t2, t3)
           | uu____2743 -> FStar_Pervasives_Native.None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____2762 =
        lookup_binding env
          (fun uu___137_2770  ->
             match uu___137_2770 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 FStar_Pervasives_Native.Some ()
             | uu____2785 -> FStar_Pervasives_Native.None) in
      FStar_All.pipe_right uu____2762 FStar_Option.isSome
let lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string,FStar_SMTEncoding_Term.term
                      FStar_Pervasives_Native.option,FStar_SMTEncoding_Term.term
                                                       FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun a  ->
      let uu____2806 = try_lookup_lid env a in
      match uu____2806 with
      | FStar_Pervasives_Native.None  ->
          let uu____2839 =
            let uu____2840 = FStar_Syntax_Print.lid_to_string a in
            FStar_Util.format1 "Name not found: %s" uu____2840 in
          failwith uu____2839
      | FStar_Pervasives_Native.Some s -> s
let push_free_var:
  env_t ->
    FStar_Ident.lident ->
      Prims.string ->
        FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option -> env_t
  =
  fun env  ->
    fun x  ->
      fun fname  ->
        fun ftok  ->
          let uu___162_2892 = env in
          {
            bindings =
              ((Binding_fvar (x, fname, ftok, FStar_Pervasives_Native.None))
              :: (env.bindings));
            depth = (uu___162_2892.depth);
            tcenv = (uu___162_2892.tcenv);
            warn = (uu___162_2892.warn);
            cache = (uu___162_2892.cache);
            nolabels = (uu___162_2892.nolabels);
            use_zfuel_name = (uu___162_2892.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___162_2892.encode_non_total_function_typ);
            current_module_name = (uu___162_2892.current_module_name)
          }
let push_zfuel_name: env_t -> FStar_Ident.lident -> Prims.string -> env_t =
  fun env  ->
    fun x  ->
      fun f  ->
        let uu____2909 = lookup_lid env x in
        match uu____2909 with
        | (t1,t2,uu____2922) ->
            let t3 =
              let uu____2932 =
                let uu____2939 =
                  let uu____2942 = FStar_SMTEncoding_Util.mkApp ("ZFuel", []) in
                  [uu____2942] in
                (f, uu____2939) in
              FStar_SMTEncoding_Util.mkApp uu____2932 in
            let uu___163_2947 = env in
            {
              bindings =
                ((Binding_fvar (x, t1, t2, (FStar_Pervasives_Native.Some t3)))
                :: (env.bindings));
              depth = (uu___163_2947.depth);
              tcenv = (uu___163_2947.tcenv);
              warn = (uu___163_2947.warn);
              cache = (uu___163_2947.cache);
              nolabels = (uu___163_2947.nolabels);
              use_zfuel_name = (uu___163_2947.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___163_2947.encode_non_total_function_typ);
              current_module_name = (uu___163_2947.current_module_name)
            }
let try_lookup_free_var:
  env_t ->
    FStar_Ident.lident ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____2962 = try_lookup_lid env l in
      match uu____2962 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (name,sym,zf_opt) ->
          (match zf_opt with
           | FStar_Pervasives_Native.Some f when env.use_zfuel_name ->
               FStar_Pervasives_Native.Some f
           | uu____3011 ->
               (match sym with
                | FStar_Pervasives_Native.Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____3019,fuel::[]) ->
                         let uu____3023 =
                           let uu____3024 =
                             let uu____3025 =
                               FStar_SMTEncoding_Term.fv_of_term fuel in
                             FStar_All.pipe_right uu____3025
                               FStar_Pervasives_Native.fst in
                           FStar_Util.starts_with uu____3024 "fuel" in
                         if uu____3023
                         then
                           let uu____3028 =
                             let uu____3029 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort) in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____3029
                               fuel in
                           FStar_All.pipe_left
                             (fun _0_42  ->
                                FStar_Pervasives_Native.Some _0_42)
                             uu____3028
                         else FStar_Pervasives_Native.Some t
                     | uu____3033 -> FStar_Pervasives_Native.Some t)
                | uu____3034 -> FStar_Pervasives_Native.None))
let lookup_free_var:
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      FStar_SMTEncoding_Term.term
  =
  fun env  ->
    fun a  ->
      let uu____3049 = try_lookup_free_var env a.FStar_Syntax_Syntax.v in
      match uu____3049 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let uu____3053 =
            let uu____3054 =
              FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v in
            FStar_Util.format1 "Name not found: %s" uu____3054 in
          failwith uu____3053
let lookup_free_var_name:
  env_t -> FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t -> Prims.string
  =
  fun env  ->
    fun a  ->
      let uu____3067 = lookup_lid env a.FStar_Syntax_Syntax.v in
      match uu____3067 with | (x,uu____3079,uu____3080) -> x
let lookup_free_var_sym:
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      (FStar_SMTEncoding_Term.op,FStar_SMTEncoding_Term.term Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun a  ->
      let uu____3107 = lookup_lid env a.FStar_Syntax_Syntax.v in
      match uu____3107 with
      | (name,sym,zf_opt) ->
          (match zf_opt with
           | FStar_Pervasives_Native.Some
               {
                 FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                   (g,zf);
                 FStar_SMTEncoding_Term.freevars = uu____3143;
                 FStar_SMTEncoding_Term.rng = uu____3144;_}
               when env.use_zfuel_name -> (g, zf)
           | uu____3159 ->
               (match sym with
                | FStar_Pervasives_Native.None  ->
                    ((FStar_SMTEncoding_Term.Var name), [])
                | FStar_Pervasives_Native.Some sym1 ->
                    (match sym1.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                     | uu____3183 -> ((FStar_SMTEncoding_Term.Var name), []))))
let tok_of_name:
  env_t ->
    Prims.string ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___138_3201  ->
           match uu___138_3201 with
           | Binding_fvar (uu____3204,nm',tok,uu____3207) when nm = nm' ->
               tok
           | uu____3216 -> FStar_Pervasives_Native.None)
let mkForall_fuel':
  'Auu____3223 .
    'Auu____3223 ->
      (FStar_SMTEncoding_Term.pat Prims.list Prims.list,FStar_SMTEncoding_Term.fvs,
        FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple3 ->
        FStar_SMTEncoding_Term.term
  =
  fun n1  ->
    fun uu____3241  ->
      match uu____3241 with
      | (pats,vars,body) ->
          let fallback uu____3266 =
            FStar_SMTEncoding_Util.mkForall (pats, vars, body) in
          let uu____3271 = FStar_Options.unthrottle_inductives () in
          if uu____3271
          then fallback ()
          else
            (let uu____3273 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
             match uu____3273 with
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
                           | uu____3304 -> p)) in
                 let pats1 = FStar_List.map add_fuel1 pats in
                 let body1 =
                   match body.FStar_SMTEncoding_Term.tm with
                   | FStar_SMTEncoding_Term.App
                       (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                       let guard1 =
                         match guard.FStar_SMTEncoding_Term.tm with
                         | FStar_SMTEncoding_Term.App
                             (FStar_SMTEncoding_Term.And ,guards) ->
                             let uu____3325 = add_fuel1 guards in
                             FStar_SMTEncoding_Util.mk_and_l uu____3325
                         | uu____3328 ->
                             let uu____3329 = add_fuel1 [guard] in
                             FStar_All.pipe_right uu____3329 FStar_List.hd in
                       FStar_SMTEncoding_Util.mkImp (guard1, body')
                   | uu____3334 -> body in
                 let vars1 = (fsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars in
                 FStar_SMTEncoding_Util.mkForall (pats1, vars1, body1))
let mkForall_fuel:
  (FStar_SMTEncoding_Term.pat Prims.list Prims.list,FStar_SMTEncoding_Term.fvs,
    FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple3 ->
    FStar_SMTEncoding_Term.term
  = mkForall_fuel' (Prims.parse_int "1")
let head_normal: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow uu____3378 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____3391 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____3398 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____3399 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____3416 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____3433 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3435 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____3435 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____3453;
             FStar_Syntax_Syntax.vars = uu____3454;_},uu____3455)
          ->
          let uu____3476 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____3476 FStar_Option.isNone
      | uu____3493 -> false
let head_redex: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____3502 =
        let uu____3503 = FStar_Syntax_Util.un_uinst t in
        uu____3503.FStar_Syntax_Syntax.n in
      match uu____3502 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____3506,uu____3507,FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___139_3528  ->
                  match uu___139_3528 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____3529 -> false)
               rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3531 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____3531 FStar_Option.isSome
      | uu____3548 -> false
let whnf: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____3557 = head_normal env t in
      if uu____3557
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
let norm: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      FStar_TypeChecker_Normalize.normalize
        [FStar_TypeChecker_Normalize.Beta;
        FStar_TypeChecker_Normalize.Exclude FStar_TypeChecker_Normalize.Zeta;
        FStar_TypeChecker_Normalize.Eager_unfolding;
        FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t
let trivial_post: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____3571 =
      let uu____3572 = FStar_Syntax_Syntax.null_binder t in [uu____3572] in
    let uu____3573 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
    FStar_Syntax_Util.abs uu____3571 uu____3573 FStar_Pervasives_Native.None
let mk_Apply:
  FStar_SMTEncoding_Term.term ->
    (Prims.string,FStar_SMTEncoding_Term.sort) FStar_Pervasives_Native.tuple2
      Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun vars  ->
      FStar_All.pipe_right vars
        (FStar_List.fold_left
           (fun out  ->
              fun var  ->
                match FStar_Pervasives_Native.snd var with
                | FStar_SMTEncoding_Term.Fuel_sort  ->
                    let uu____3613 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____3613
                | s ->
                    let uu____3618 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____3618) e)
let mk_Apply_args:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
let is_app: FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___140_3636  ->
    match uu___140_3636 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____3637 -> false
let is_an_eta_expansion:
  env_t ->
    FStar_SMTEncoding_Term.fv Prims.list ->
      FStar_SMTEncoding_Term.term ->
        FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option
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
                       FStar_SMTEncoding_Term.freevars = uu____3676;
                       FStar_SMTEncoding_Term.rng = uu____3677;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____3700) ->
              let uu____3709 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____3720 -> false) args (FStar_List.rev xs)) in
              if uu____3709
              then tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____3724,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu____3728 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____3732 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____3732)) in
              if uu____3728
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____3736 -> FStar_Pervasives_Native.None in
        check_partial_applications body (FStar_List.rev vars)
type label =
  (FStar_SMTEncoding_Term.fv,Prims.string,FStar_Range.range)
    FStar_Pervasives_Native.tuple3[@@deriving show]
type labels = label Prims.list[@@deriving show]
type pattern =
  {
  pat_vars:
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.fv)
      FStar_Pervasives_Native.tuple2 Prims.list;
  pat_term:
    Prims.unit ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2;
  guard: FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term;
  projections:
    FStar_SMTEncoding_Term.term ->
      (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2 Prims.list;}[@@deriving show]
let __proj__Mkpattern__item__pat_vars:
  pattern ->
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.fv)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__pat_vars
let __proj__Mkpattern__item__pat_term:
  pattern ->
    Prims.unit ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__pat_term
let __proj__Mkpattern__item__guard:
  pattern -> FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__guard
let __proj__Mkpattern__item__projections:
  pattern ->
    FStar_SMTEncoding_Term.term ->
      (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__projections
exception Let_rec_unencodeable
let uu___is_Let_rec_unencodeable: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____3966 -> false
exception Inner_let_rec
let uu___is_Inner_let_rec: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Inner_let_rec  -> true | uu____3971 -> false
let as_function_typ:
  env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t0  ->
      let rec aux norm1 t =
        let t1 = FStar_Syntax_Subst.compress t in
        match t1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow uu____3992 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____4005 ->
            let uu____4012 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____4012
        | uu____4013 ->
            if norm1
            then let uu____4014 = whnf env t1 in aux false uu____4014
            else
              (let uu____4016 =
                 let uu____4017 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____4018 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____4017 uu____4018 in
               failwith uu____4016) in
      aux true t0
let curried_arrow_formals_comp:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2
  =
  fun k  ->
    let k1 = FStar_Syntax_Subst.compress k in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        FStar_Syntax_Subst.open_comp bs c
    | uu____4050 ->
        let uu____4051 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____4051)
let is_arithmetic_primitive:
  'Auu____4068 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____4068 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4088::uu____4089::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4093::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____4096 -> false
let isInteger: FStar_Syntax_Syntax.term' -> Prims.bool =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____4118 -> false
let getInteger: FStar_Syntax_Syntax.term' -> Prims.int =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____4134 -> failwith "Expected an Integer term"
let is_BitVector_primitive:
  'Auu____4141 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____4141)
        FStar_Pervasives_Native.tuple2 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____4180)::uu____4181::uu____4182::[]) ->
          (((((((((FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_and_lid)
                    ||
                    (FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.bv_xor_lid))
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.bv_or_lid))
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____4233)::uu____4234::[])
          ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____4271 -> false
let rec encode_const:
  FStar_Const.sconst ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decl Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun c  ->
    fun env  ->
      match c with
      | FStar_Const.Const_unit  -> (FStar_SMTEncoding_Term.mk_Term_unit, [])
      | FStar_Const.Const_bool (true ) ->
          let uu____4478 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue in
          (uu____4478, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____4481 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse in
          (uu____4481, [])
      | FStar_Const.Const_char c1 ->
          let uu____4485 =
            let uu____4486 =
              let uu____4493 =
                let uu____4496 =
                  let uu____4497 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1) in
                  FStar_SMTEncoding_Term.boxInt uu____4497 in
                [uu____4496] in
              ("FStar.Char.Char", uu____4493) in
            FStar_SMTEncoding_Util.mkApp uu____4486 in
          (uu____4485, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____4513 =
            let uu____4514 = FStar_SMTEncoding_Util.mkInteger i in
            FStar_SMTEncoding_Term.boxInt uu____4514 in
          (uu____4513, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.tcenv).FStar_TypeChecker_Env.dsenv repr sw
              FStar_Range.dummyRange in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____4535) ->
          let uu____4536 = varops.string_const s in (uu____4536, [])
      | FStar_Const.Const_range r ->
          (FStar_SMTEncoding_Term.mk_Range_const, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | c1 ->
          let uu____4545 =
            let uu____4546 = FStar_Syntax_Print.const_to_string c1 in
            FStar_Util.format1 "Unhandled constant: %s" uu____4546 in
          failwith uu____4545
and encode_binders:
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.binders ->
      env_t ->
        (FStar_SMTEncoding_Term.fv Prims.list,FStar_SMTEncoding_Term.term
                                                Prims.list,env_t,FStar_SMTEncoding_Term.decls_t,
          FStar_Syntax_Syntax.bv Prims.list) FStar_Pervasives_Native.tuple5
  =
  fun fuel_opt  ->
    fun bs  ->
      fun env  ->
        (let uu____4575 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____4575
         then
           let uu____4576 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____4576
         else ());
        (let uu____4578 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____4662  ->
                   fun b  ->
                     match uu____4662 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____4741 =
                           let x = unmangle (FStar_Pervasives_Native.fst b) in
                           let uu____4757 = gen_term_var env1 x in
                           match uu____4757 with
                           | (xxsym,xx,env') ->
                               let uu____4781 =
                                 let uu____4786 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____4786 env1 xx in
                               (match uu____4781 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____4741 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____4578 with
         | (vars,guards,env1,decls,names1) ->
             ((FStar_List.rev vars), (FStar_List.rev guards), env1, decls,
               (FStar_List.rev names1)))
and encode_term_pred:
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.typ ->
      env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
            FStar_Pervasives_Native.tuple2
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____4945 = encode_term t env in
          match uu____4945 with
          | (t1,decls) ->
              let uu____4956 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____4956, decls)
and encode_term_pred':
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.typ ->
      env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
            FStar_Pervasives_Native.tuple2
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____4967 = encode_term t env in
          match uu____4967 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____4982 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____4982, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____4984 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____4984, decls))
and encode_arith_term:
  env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____4990 = encode_args args_e env in
        match uu____4990 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____5009 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____5018 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____5018 in
            let binary arg_tms1 =
              let uu____5031 =
                let uu____5032 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____5032 in
              let uu____5033 =
                let uu____5034 =
                  let uu____5035 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____5035 in
                FStar_SMTEncoding_Term.unboxInt uu____5034 in
              (uu____5031, uu____5033) in
            let mk_default uu____5041 =
              let uu____5042 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____5042 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms)) in
            let mk_l op mk_args ts =
              let uu____5093 = FStar_Options.smtencoding_l_arith_native () in
              if uu____5093
              then
                let uu____5094 = let uu____5095 = mk_args ts in op uu____5095 in
                FStar_All.pipe_right uu____5094 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____5124 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____5124
              then
                let uu____5125 = binary ts in
                match uu____5125 with
                | (t1,t2) ->
                    let uu____5132 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____5132
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____5136 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____5136
                 then
                   let uu____5137 = op (binary ts) in
                   FStar_All.pipe_right uu____5137
                     FStar_SMTEncoding_Term.boxInt
                 else mk_default ()) in
            let add1 = mk_l FStar_SMTEncoding_Util.mkAdd binary in
            let sub1 = mk_l FStar_SMTEncoding_Util.mkSub binary in
            let minus = mk_l FStar_SMTEncoding_Util.mkMinus unary in
            let mul1 = mk_nl "_mul" FStar_SMTEncoding_Util.mkMul in
            let div1 = mk_nl "_div" FStar_SMTEncoding_Util.mkDiv in
            let modulus = mk_nl "_mod" FStar_SMTEncoding_Util.mkMod in
            let ops =
              [(FStar_Parser_Const.op_Addition, add1);
              (FStar_Parser_Const.op_Subtraction, sub1);
              (FStar_Parser_Const.op_Multiply, mul1);
              (FStar_Parser_Const.op_Division, div1);
              (FStar_Parser_Const.op_Modulus, modulus);
              (FStar_Parser_Const.op_Minus, minus)] in
            let uu____5268 =
              let uu____5277 =
                FStar_List.tryFind
                  (fun uu____5299  ->
                     match uu____5299 with
                     | (l,uu____5309) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____5277 FStar_Util.must in
            (match uu____5268 with
             | (uu____5348,op) ->
                 let uu____5358 = op arg_tms in (uu____5358, decls))
and encode_BitVector_term:
  env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.arg Prims.list ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____5366 = FStar_List.hd args_e in
        match uu____5366 with
        | (tm_sz,uu____5374) ->
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz) in
            let sz_decls =
              let uu____5384 = FStar_Util.smap_try_find env.cache sz_key in
              match uu____5384 with
              | FStar_Pervasives_Native.Some cache_entry -> []
              | FStar_Pervasives_Native.None  ->
                  let t_decls = FStar_SMTEncoding_Term.mkBvConstructor sz in
                  ((let uu____5392 = mk_cache_entry env "" [] [] in
                    FStar_Util.smap_add env.cache sz_key uu____5392);
                   t_decls) in
            let uu____5393 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5413::(sz_arg,uu____5415)::uu____5416::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____5465 =
                    let uu____5468 = FStar_List.tail args_e in
                    FStar_List.tail uu____5468 in
                  let uu____5471 =
                    let uu____5474 = getInteger sz_arg.FStar_Syntax_Syntax.n in
                    FStar_Pervasives_Native.Some uu____5474 in
                  (uu____5465, uu____5471)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5480::(sz_arg,uu____5482)::uu____5483::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____5532 =
                    let uu____5533 = FStar_Syntax_Print.term_to_string sz_arg in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____5533 in
                  failwith uu____5532
              | uu____5542 ->
                  let uu____5549 = FStar_List.tail args_e in
                  (uu____5549, FStar_Pervasives_Native.None) in
            (match uu____5393 with
             | (arg_tms,ext_sz) ->
                 let uu____5572 = encode_args arg_tms env in
                 (match uu____5572 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____5593 -> failwith "Impossible" in
                      let unary arg_tms2 =
                        let uu____5602 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____5602 in
                      let unary_arith arg_tms2 =
                        let uu____5611 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxInt uu____5611 in
                      let binary arg_tms2 =
                        let uu____5624 =
                          let uu____5625 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5625 in
                        let uu____5626 =
                          let uu____5627 =
                            let uu____5628 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____5628 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5627 in
                        (uu____5624, uu____5626) in
                      let binary_arith arg_tms2 =
                        let uu____5643 =
                          let uu____5644 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5644 in
                        let uu____5645 =
                          let uu____5646 =
                            let uu____5647 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____5647 in
                          FStar_SMTEncoding_Term.unboxInt uu____5646 in
                        (uu____5643, uu____5645) in
                      let mk_bv op mk_args resBox ts =
                        let uu____5696 =
                          let uu____5697 = mk_args ts in op uu____5697 in
                        FStar_All.pipe_right uu____5696 resBox in
                      let bv_and =
                        mk_bv FStar_SMTEncoding_Util.mkBvAnd binary
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_xor =
                        mk_bv FStar_SMTEncoding_Util.mkBvXor binary
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_or =
                        mk_bv FStar_SMTEncoding_Util.mkBvOr binary
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_shl =
                        mk_bv (FStar_SMTEncoding_Util.mkBvShl sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_shr =
                        mk_bv (FStar_SMTEncoding_Util.mkBvShr sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_udiv =
                        mk_bv (FStar_SMTEncoding_Util.mkBvUdiv sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_mod =
                        mk_bv (FStar_SMTEncoding_Util.mkBvMod sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_mul =
                        mk_bv (FStar_SMTEncoding_Util.mkBvMul sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_ult =
                        mk_bv FStar_SMTEncoding_Util.mkBvUlt binary
                          FStar_SMTEncoding_Term.boxBool in
                      let bv_uext arg_tms2 =
                        let uu____5787 =
                          let uu____5790 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible" in
                          FStar_SMTEncoding_Util.mkBvUext uu____5790 in
                        let uu____5792 =
                          let uu____5795 =
                            let uu____5796 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible" in
                            sz + uu____5796 in
                          FStar_SMTEncoding_Term.boxBitVec uu____5795 in
                        mk_bv uu____5787 unary uu____5792 arg_tms2 in
                      let to_int =
                        mk_bv FStar_SMTEncoding_Util.mkBvToNat unary
                          FStar_SMTEncoding_Term.boxInt in
                      let bv_to =
                        mk_bv (FStar_SMTEncoding_Util.mkNatToBv sz)
                          unary_arith (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let ops =
                        [(FStar_Parser_Const.bv_and_lid, bv_and);
                        (FStar_Parser_Const.bv_xor_lid, bv_xor);
                        (FStar_Parser_Const.bv_or_lid, bv_or);
                        (FStar_Parser_Const.bv_shift_left_lid, bv_shl);
                        (FStar_Parser_Const.bv_shift_right_lid, bv_shr);
                        (FStar_Parser_Const.bv_udiv_lid, bv_udiv);
                        (FStar_Parser_Const.bv_mod_lid, bv_mod);
                        (FStar_Parser_Const.bv_mul_lid, bv_mul);
                        (FStar_Parser_Const.bv_ult_lid, bv_ult);
                        (FStar_Parser_Const.bv_uext_lid, bv_uext);
                        (FStar_Parser_Const.bv_to_nat_lid, to_int);
                        (FStar_Parser_Const.nat_to_bv_lid, bv_to)] in
                      let uu____5971 =
                        let uu____5980 =
                          FStar_List.tryFind
                            (fun uu____6002  ->
                               match uu____6002 with
                               | (l,uu____6012) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops in
                        FStar_All.pipe_right uu____5980 FStar_Util.must in
                      (match uu____5971 with
                       | (uu____6053,op) ->
                           let uu____6063 = op arg_tms1 in
                           (uu____6063, (FStar_List.append sz_decls decls)))))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____6074 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____6074
       then
         let uu____6075 = FStar_Syntax_Print.tag_of_term t in
         let uu____6076 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____6077 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____6075 uu____6076
           uu____6077
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____6083 ->
           let uu____6108 =
             let uu____6109 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____6110 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____6111 = FStar_Syntax_Print.term_to_string t0 in
             let uu____6112 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6109
               uu____6110 uu____6111 uu____6112 in
           failwith uu____6108
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____6117 =
             let uu____6118 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____6119 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____6120 = FStar_Syntax_Print.term_to_string t0 in
             let uu____6121 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6118
               uu____6119 uu____6120 uu____6121 in
           failwith uu____6117
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____6127 =
             let uu____6128 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____6128 in
           failwith uu____6127
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____6135) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta
           ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
              FStar_Syntax_Syntax.pos = uu____6176;
              FStar_Syntax_Syntax.vars = uu____6177;_},FStar_Syntax_Syntax.Meta_alien
            (obj,desc,ty))
           ->
           let tsym =
             let uu____6194 = varops.fresh "t" in
             (uu____6194, FStar_SMTEncoding_Term.Term_sort) in
           let t1 = FStar_SMTEncoding_Util.mkFreeV tsym in
           let decl =
             let uu____6197 =
               let uu____6208 =
                 let uu____6211 = FStar_Util.format1 "alien term (%s)" desc in
                 FStar_Pervasives_Native.Some uu____6211 in
               ((FStar_Pervasives_Native.fst tsym), [],
                 FStar_SMTEncoding_Term.Term_sort, uu____6208) in
             FStar_SMTEncoding_Term.DeclFun uu____6197 in
           (t1, [decl])
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____6219) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____6229 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____6229, [])
       | FStar_Syntax_Syntax.Tm_type uu____6232 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6236) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____6261 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____6261 with
            | (binders1,res) ->
                let uu____6272 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____6272
                then
                  let uu____6277 =
                    encode_binders FStar_Pervasives_Native.None binders1 env in
                  (match uu____6277 with
                   | (vars,guards,env',decls,uu____6302) ->
                       let fsym =
                         let uu____6320 = varops.fresh "f" in
                         (uu____6320, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____6323 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___164_6332 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___164_6332.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___164_6332.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___164_6332.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___164_6332.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___164_6332.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___164_6332.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___164_6332.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___164_6332.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___164_6332.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___164_6332.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___164_6332.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___164_6332.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___164_6332.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___164_6332.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___164_6332.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___164_6332.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___164_6332.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___164_6332.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___164_6332.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___164_6332.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___164_6332.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___164_6332.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___164_6332.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___164_6332.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___164_6332.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___164_6332.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___164_6332.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___164_6332.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___164_6332.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___164_6332.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___164_6332.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___164_6332.FStar_TypeChecker_Env.dsenv)
                            }) res in
                       (match uu____6323 with
                        | (pre_opt,res_t) ->
                            let uu____6343 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app in
                            (match uu____6343 with
                             | (res_pred,decls') ->
                                 let uu____6354 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____6367 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____6367, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____6371 =
                                         encode_formula pre env' in
                                       (match uu____6371 with
                                        | (guard,decls0) ->
                                            let uu____6384 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____6384, decls0)) in
                                 (match uu____6354 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____6396 =
                                          let uu____6407 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____6407) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____6396 in
                                      let cvars =
                                        let uu____6425 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____6425
                                          (FStar_List.filter
                                             (fun uu____6439  ->
                                                match uu____6439 with
                                                | (x,uu____6445) ->
                                                    x <>
                                                      (FStar_Pervasives_Native.fst
                                                         fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____6464 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____6464 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____6472 =
                                             let uu____6473 =
                                               let uu____6480 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____6480) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6473 in
                                           (uu____6472,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____6500 =
                                               let uu____6501 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____6501 in
                                             varops.mk_unique uu____6500 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars in
                                           let caption =
                                             let uu____6512 =
                                               FStar_Options.log_queries () in
                                             if uu____6512
                                             then
                                               let uu____6515 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____6515
                                             else
                                               FStar_Pervasives_Native.None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____6523 =
                                               let uu____6530 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____6530) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6523 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____6542 =
                                               let uu____6549 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____6549,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6542 in
                                           let f_has_t =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               f t1 in
                                           let f_has_t_z =
                                             FStar_SMTEncoding_Term.mk_HasTypeZ
                                               f t1 in
                                           let pre_typing =
                                             let a_name =
                                               Prims.strcat "pre_typing_"
                                                 tsym in
                                             let uu____6570 =
                                               let uu____6577 =
                                                 let uu____6578 =
                                                   let uu____6589 =
                                                     let uu____6590 =
                                                       let uu____6595 =
                                                         let uu____6596 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____6596 in
                                                       (f_has_t, uu____6595) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____6590 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____6589) in
                                                 mkForall_fuel uu____6578 in
                                               (uu____6577,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6570 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____6619 =
                                               let uu____6626 =
                                                 let uu____6627 =
                                                   let uu____6638 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____6638) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____6627 in
                                               (uu____6626,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6619 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____6663 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____6663);
                                            (t1, t_decls)))))))
                else
                  (let tsym = varops.fresh "Non_total_Tm_arrow" in
                   let tdecl =
                     FStar_SMTEncoding_Term.DeclFun
                       (tsym, [], FStar_SMTEncoding_Term.Term_sort,
                         FStar_Pervasives_Native.None) in
                   let t1 = FStar_SMTEncoding_Util.mkApp (tsym, []) in
                   let t_kinding =
                     let a_name =
                       Prims.strcat "non_total_function_typing_" tsym in
                     let uu____6678 =
                       let uu____6685 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____6685,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6678 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____6697 =
                       let uu____6704 =
                         let uu____6705 =
                           let uu____6716 =
                             let uu____6717 =
                               let uu____6722 =
                                 let uu____6723 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____6723 in
                               (f_has_t, uu____6722) in
                             FStar_SMTEncoding_Util.mkImp uu____6717 in
                           ([[f_has_t]], [fsym], uu____6716) in
                         mkForall_fuel uu____6705 in
                       (uu____6704, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6697 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____6750 ->
           let uu____6757 =
             let uu____6762 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.Weak;
                 FStar_TypeChecker_Normalize.HNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____6762 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____6769;
                 FStar_Syntax_Syntax.vars = uu____6770;_} ->
                 let uu____6777 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f in
                 (match uu____6777 with
                  | (b,f1) ->
                      let uu____6802 =
                        let uu____6803 = FStar_List.hd b in
                        FStar_Pervasives_Native.fst uu____6803 in
                      (uu____6802, f1))
             | uu____6812 -> failwith "impossible" in
           (match uu____6757 with
            | (x,f) ->
                let uu____6823 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____6823 with
                 | (base_t,decls) ->
                     let uu____6834 = gen_term_var env x in
                     (match uu____6834 with
                      | (x1,xtm,env') ->
                          let uu____6848 = encode_formula f env' in
                          (match uu____6848 with
                           | (refinement,decls') ->
                               let uu____6859 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____6859 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____6875 =
                                        let uu____6878 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____6885 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____6878
                                          uu____6885 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____6875 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____6918  ->
                                              match uu____6918 with
                                              | (y,uu____6924) ->
                                                  (y <> x1) && (y <> fsym))) in
                                    let xfv =
                                      (x1, FStar_SMTEncoding_Term.Term_sort) in
                                    let ffv =
                                      (fsym,
                                        FStar_SMTEncoding_Term.Fuel_sort) in
                                    let tkey =
                                      FStar_SMTEncoding_Util.mkForall
                                        ([], (ffv :: xfv :: cvars1),
                                          encoding) in
                                    let tkey_hash =
                                      FStar_SMTEncoding_Term.hash_of_term
                                        tkey in
                                    let uu____6957 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____6957 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____6965 =
                                           let uu____6966 =
                                             let uu____6973 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____6973) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____6966 in
                                         (uu____6965,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____6994 =
                                             let uu____6995 =
                                               let uu____6996 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____6996 in
                                             Prims.strcat module_name
                                               uu____6995 in
                                           varops.mk_unique uu____6994 in
                                         let cvar_sorts =
                                           FStar_List.map
                                             FStar_Pervasives_Native.snd
                                             cvars1 in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None) in
                                         let t1 =
                                           let uu____7010 =
                                             let uu____7017 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____7017) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____7010 in
                                         let x_has_base_t =
                                           FStar_SMTEncoding_Term.mk_HasType
                                             xtm base_t in
                                         let x_has_t =
                                           FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                             (FStar_Pervasives_Native.Some
                                                fterm) xtm t1 in
                                         let t_has_kind =
                                           FStar_SMTEncoding_Term.mk_HasType
                                             t1
                                             FStar_SMTEncoding_Term.mk_Term_type in
                                         let t_haseq_base =
                                           FStar_SMTEncoding_Term.mk_haseq
                                             base_t in
                                         let t_haseq_ref =
                                           FStar_SMTEncoding_Term.mk_haseq t1 in
                                         let t_haseq1 =
                                           let uu____7032 =
                                             let uu____7039 =
                                               let uu____7040 =
                                                 let uu____7051 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____7051) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7040 in
                                             (uu____7039,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7032 in
                                         let t_kinding =
                                           let uu____7069 =
                                             let uu____7076 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____7076,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7069 in
                                         let t_interp =
                                           let uu____7094 =
                                             let uu____7101 =
                                               let uu____7102 =
                                                 let uu____7113 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____7113) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7102 in
                                             let uu____7136 =
                                               let uu____7139 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____7139 in
                                             (uu____7101, uu____7136,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7094 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____7146 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____7146);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____7176 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____7176 in
           let uu____7177 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm in
           (match uu____7177 with
            | (t_has_k,decls) ->
                let d =
                  let uu____7189 =
                    let uu____7196 =
                      let uu____7197 =
                        let uu____7198 =
                          let uu____7199 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____7199 in
                        FStar_Util.format1 "uvar_typing_%s" uu____7198 in
                      varops.mk_unique uu____7197 in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____7196) in
                  FStar_SMTEncoding_Util.mkAssume uu____7189 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____7204 ->
           let uu____7219 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____7219 with
            | (head1,args_e) ->
                let uu____7260 =
                  let uu____7273 =
                    let uu____7274 = FStar_Syntax_Subst.compress head1 in
                    uu____7274.FStar_Syntax_Syntax.n in
                  (uu____7273, args_e) in
                (match uu____7260 with
                 | uu____7289 when head_redex env head1 ->
                     let uu____7302 = whnf env t in
                     encode_term uu____7302 env
                 | uu____7303 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____7322 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____7336;
                       FStar_Syntax_Syntax.vars = uu____7337;_},uu____7338),uu____7339::
                    (v1,uu____7341)::(v2,uu____7343)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7394 = encode_term v1 env in
                     (match uu____7394 with
                      | (v11,decls1) ->
                          let uu____7405 = encode_term v2 env in
                          (match uu____7405 with
                           | (v21,decls2) ->
                               let uu____7416 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7416,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____7420::(v1,uu____7422)::(v2,uu____7424)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7471 = encode_term v1 env in
                     (match uu____7471 with
                      | (v11,decls1) ->
                          let uu____7482 = encode_term v2 env in
                          (match uu____7482 with
                           | (v21,decls2) ->
                               let uu____7493 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7493,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____7497)::[]) ->
                     encode_term FStar_Syntax_Util.exp_unit env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(rng,uu____7523)::(arg,uu____7525)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____7560) ->
                     let e0 =
                       let uu____7578 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____7578 in
                     ((let uu____7586 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____7586
                       then
                         let uu____7587 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____7587
                       else ());
                      (let e =
                         let uu____7592 =
                           let uu____7593 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____7594 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____7593
                             uu____7594 in
                         uu____7592 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____7603),(arg,uu____7605)::[]) -> encode_term arg env
                 | uu____7630 ->
                     let uu____7643 = encode_args args_e env in
                     (match uu____7643 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____7698 = encode_term head1 env in
                            match uu____7698 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____7762 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____7762 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____7840  ->
                                                 fun uu____7841  ->
                                                   match (uu____7840,
                                                           uu____7841)
                                                   with
                                                   | ((bv,uu____7863),
                                                      (a,uu____7865)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____7883 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____7883
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____7888 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm in
                                          (match uu____7888 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____7903 =
                                                   let uu____7910 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____7919 =
                                                     let uu____7920 =
                                                       let uu____7921 =
                                                         let uu____7922 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____7922 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____7921 in
                                                     varops.mk_unique
                                                       uu____7920 in
                                                   (uu____7910,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____7919) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____7903 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____7939 = lookup_free_var_sym env fv in
                            match uu____7939 with
                            | (fname,fuel_args) ->
                                let tm =
                                  FStar_SMTEncoding_Util.mkApp'
                                    (fname,
                                      (FStar_List.append fuel_args args)) in
                                (tm, decls) in
                          let head2 = FStar_Syntax_Subst.compress head1 in
                          let head_type =
                            match head2.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_uinst
                                ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_name x;
                                   FStar_Syntax_Syntax.pos = uu____7970;
                                   FStar_Syntax_Syntax.vars = uu____7971;_},uu____7972)
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
                                   FStar_Syntax_Syntax.pos = uu____7983;
                                   FStar_Syntax_Syntax.vars = uu____7984;_},uu____7985)
                                ->
                                let uu____7990 =
                                  let uu____7991 =
                                    let uu____7996 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____7996
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____7991
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____7990
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____8026 =
                                  let uu____8027 =
                                    let uu____8032 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____8032
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____8027
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____8026
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8061,(FStar_Util.Inl t1,uu____8063),uu____8064)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8113,(FStar_Util.Inr c,uu____8115),uu____8116)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____8165 -> FStar_Pervasives_Native.None in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____8192 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.Weak;
                                     FStar_TypeChecker_Normalize.HNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____8192 in
                               let uu____8193 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____8193 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____8209;
                                            FStar_Syntax_Syntax.vars =
                                              uu____8210;_},uu____8211)
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
                                     | uu____8225 ->
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
           let uu____8274 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____8274 with
            | (bs1,body1,opening) ->
                let fallback uu____8297 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding")) in
                  let uu____8304 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____8304, [decl]) in
                let is_impure rc =
                  let uu____8311 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect in
                  FStar_All.pipe_right uu____8311 Prims.op_Negation in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____8321 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____8321
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1 in
                  if
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                  then
                    let uu____8341 = FStar_Syntax_Syntax.mk_Total res_typ in
                    FStar_Pervasives_Native.Some uu____8341
                  else
                    if
                      FStar_Ident.lid_equals
                        rc.FStar_Syntax_Syntax.residual_effect
                        FStar_Parser_Const.effect_GTot_lid
                    then
                      (let uu____8345 = FStar_Syntax_Syntax.mk_GTotal res_typ in
                       FStar_Pervasives_Native.Some uu____8345)
                    else FStar_Pervasives_Native.None in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____8352 =
                         let uu____8353 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____8353 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____8352);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____8355 =
                       (is_impure rc) &&
                         (let uu____8357 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc in
                          Prims.op_Negation uu____8357) in
                     if uu____8355
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____8364 =
                          encode_binders FStar_Pervasives_Native.None bs1 env in
                        match uu____8364 with
                        | (vars,guards,envbody,decls,uu____8389) ->
                            let body2 =
                              let uu____8403 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  rc in
                              if uu____8403
                              then
                                FStar_TypeChecker_Util.reify_body env.tcenv
                                  body1
                              else body1 in
                            let uu____8405 = encode_term body2 envbody in
                            (match uu____8405 with
                             | (body3,decls') ->
                                 let uu____8416 =
                                   let uu____8425 = codomain_eff rc in
                                   match uu____8425 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c in
                                       let uu____8444 = encode_term tfun env in
                                       (match uu____8444 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1)) in
                                 (match uu____8416 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____8476 =
                                          let uu____8487 =
                                            let uu____8488 =
                                              let uu____8493 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____8493, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8488 in
                                          ([], vars, uu____8487) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____8476 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            cvars
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____8505 =
                                              let uu____8508 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1 in
                                              FStar_List.append uu____8508
                                                cvars in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____8505 in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____8527 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____8527 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____8535 =
                                             let uu____8536 =
                                               let uu____8543 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1 in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____8543) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____8536 in
                                           (uu____8535,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____8554 =
                                             is_an_eta_expansion env vars
                                               body3 in
                                           (match uu____8554 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____8565 =
                                                    let uu____8566 =
                                                      FStar_Util.smap_size
                                                        env.cache in
                                                    uu____8566 = cache_size in
                                                  if uu____8565
                                                  then []
                                                  else
                                                    FStar_List.append decls
                                                      (FStar_List.append
                                                         decls' decls'') in
                                                (t1, decls1)
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                let cvar_sorts =
                                                  FStar_List.map
                                                    FStar_Pervasives_Native.snd
                                                    cvars1 in
                                                let fsym =
                                                  let module_name =
                                                    env.current_module_name in
                                                  let fsym =
                                                    let uu____8582 =
                                                      let uu____8583 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____8583 in
                                                    varops.mk_unique
                                                      uu____8582 in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym) in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None) in
                                                let f =
                                                  let uu____8590 =
                                                    let uu____8597 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    (fsym, uu____8597) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____8590 in
                                                let app = mk_Apply f vars in
                                                let typing_f =
                                                  match arrow_t_opt with
                                                  | FStar_Pervasives_Native.None
                                                       -> []
                                                  | FStar_Pervasives_Native.Some
                                                      t1 ->
                                                      let f_has_t =
                                                        FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                          FStar_Pervasives_Native.None
                                                          f t1 in
                                                      let a_name =
                                                        Prims.strcat
                                                          "typing_" fsym in
                                                      let uu____8615 =
                                                        let uu____8616 =
                                                          let uu____8623 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t) in
                                                          (uu____8623,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name) in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8616 in
                                                      [uu____8615] in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym in
                                                  let uu____8636 =
                                                    let uu____8643 =
                                                      let uu____8644 =
                                                        let uu____8655 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3) in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____8655) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____8644 in
                                                    (uu____8643,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____8636 in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f]))) in
                                                ((let uu____8672 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____8672);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8675,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____8676;
                          FStar_Syntax_Syntax.lbunivs = uu____8677;
                          FStar_Syntax_Syntax.lbtyp = uu____8678;
                          FStar_Syntax_Syntax.lbeff = uu____8679;
                          FStar_Syntax_Syntax.lbdef = uu____8680;_}::uu____8681),uu____8682)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____8708;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____8710;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____8731 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions, and their enclosings let bindings (including the top-level let) are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            FStar_Exn.raise Inner_let_rec)
       | FStar_Syntax_Syntax.Tm_match (e,pats) ->
           encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env
             encode_term)
and encode_let:
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
                FStar_Pervasives_Native.tuple2
  =
  fun x  ->
    fun t1  ->
      fun e1  ->
        fun e2  ->
          fun env  ->
            fun encode_body  ->
              let uu____8801 = encode_term e1 env in
              match uu____8801 with
              | (ee1,decls1) ->
                  let uu____8812 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2 in
                  (match uu____8812 with
                   | (xs,e21) ->
                       let uu____8837 = FStar_List.hd xs in
                       (match uu____8837 with
                        | (x1,uu____8851) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____8853 = encode_body e21 env' in
                            (match uu____8853 with
                             | (ee2,decls2) ->
                                 (ee2, (FStar_List.append decls1 decls2)))))
and encode_match:
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
              FStar_Pervasives_Native.tuple2
  =
  fun e  ->
    fun pats  ->
      fun default_case  ->
        fun env  ->
          fun encode_br  ->
            let uu____8885 =
              let uu____8892 =
                let uu____8893 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____8893 in
              gen_term_var env uu____8892 in
            match uu____8885 with
            | (scrsym,scr',env1) ->
                let uu____8901 = encode_term e env1 in
                (match uu____8901 with
                 | (scr,decls) ->
                     let uu____8912 =
                       let encode_branch b uu____8937 =
                         match uu____8937 with
                         | (else_case,decls1) ->
                             let uu____8956 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____8956 with
                              | (p,w,br) ->
                                  let uu____8982 = encode_pat env1 p in
                                  (match uu____8982 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____9019  ->
                                                   match uu____9019 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____9026 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____9048 =
                                               encode_term w1 env2 in
                                             (match uu____9048 with
                                              | (w2,decls2) ->
                                                  let uu____9061 =
                                                    let uu____9062 =
                                                      let uu____9067 =
                                                        let uu____9068 =
                                                          let uu____9073 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____9073) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____9068 in
                                                      (guard, uu____9067) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____9062 in
                                                  (uu____9061, decls2)) in
                                       (match uu____9026 with
                                        | (guard1,decls2) ->
                                            let uu____9086 =
                                              encode_br br env2 in
                                            (match uu____9086 with
                                             | (br1,decls3) ->
                                                 let uu____9099 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____9099,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____8912 with
                      | (match_tm,decls1) ->
                          let uu____9118 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____9118, decls1)))
and encode_pat:
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pat  ->
      (let uu____9158 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____9158
       then
         let uu____9159 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____9159
       else ());
      (let uu____9161 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____9161 with
       | (vars,pat_term) ->
           let uu____9178 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____9231  ->
                     fun v1  ->
                       match uu____9231 with
                       | (env1,vars1) ->
                           let uu____9283 = gen_term_var env1 v1 in
                           (match uu____9283 with
                            | (xx,uu____9305,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____9178 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9384 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9385 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9386 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9394 = encode_const c env1 in
                      (match uu____9394 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____9408::uu____9409 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____9412 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____9435 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____9435 with
                        | (uu____9442,uu____9443::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9446 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9479  ->
                                  match uu____9479 with
                                  | (arg,uu____9487) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9493 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____9493)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9520) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9551 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9574 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9618  ->
                                  match uu____9618 with
                                  | (arg,uu____9632) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9638 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____9638)) in
                      FStar_All.pipe_right uu____9574 FStar_List.flatten in
                let pat_term1 uu____9666 = encode_term pat_term env1 in
                let pattern =
                  {
                    pat_vars = vars1;
                    pat_term = pat_term1;
                    guard = (mk_guard pat);
                    projections = (mk_projections pat)
                  } in
                (env1, pattern)))
and encode_args:
  FStar_Syntax_Syntax.args ->
    env_t ->
      (FStar_SMTEncoding_Term.term Prims.list,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun l  ->
    fun env  ->
      let uu____9676 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____9714  ->
                fun uu____9715  ->
                  match (uu____9714, uu____9715) with
                  | ((tms,decls),(t,uu____9751)) ->
                      let uu____9772 = encode_term t env in
                      (match uu____9772 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____9676 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____9829 = FStar_Syntax_Util.list_elements e in
        match uu____9829 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____9850 =
          let uu____9865 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____9865 FStar_Syntax_Util.head_and_args in
        match uu____9850 with
        | (head1,args) ->
            let uu____9904 =
              let uu____9917 =
                let uu____9918 = FStar_Syntax_Util.un_uinst head1 in
                uu____9918.FStar_Syntax_Syntax.n in
              (uu____9917, args) in
            (match uu____9904 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____9932,uu____9933)::(e,uu____9935)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____9970 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____10006 =
            let uu____10021 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____10021 FStar_Syntax_Util.head_and_args in
          match uu____10006 with
          | (head1,args) ->
              let uu____10062 =
                let uu____10075 =
                  let uu____10076 = FStar_Syntax_Util.un_uinst head1 in
                  uu____10076.FStar_Syntax_Syntax.n in
                (uu____10075, args) in
              (match uu____10062 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____10093)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____10120 -> FStar_Pervasives_Native.None) in
        match elts with
        | t1::[] ->
            let uu____10142 = smt_pat_or1 t1 in
            (match uu____10142 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____10158 = list_elements1 e in
                 FStar_All.pipe_right uu____10158
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____10176 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____10176
                           (FStar_List.map one_pat)))
             | uu____10187 ->
                 let uu____10192 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____10192])
        | uu____10213 ->
            let uu____10216 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____10216] in
      let uu____10237 =
        let uu____10256 =
          let uu____10257 = FStar_Syntax_Subst.compress t in
          uu____10257.FStar_Syntax_Syntax.n in
        match uu____10256 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____10296 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____10296 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____10339;
                        FStar_Syntax_Syntax.effect_name = uu____10340;
                        FStar_Syntax_Syntax.result_typ = uu____10341;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____10343)::(post,uu____10345)::(pats,uu____10347)::[];
                        FStar_Syntax_Syntax.flags = uu____10348;_}
                      ->
                      let uu____10389 = lemma_pats pats in
                      (binders1, pre, post, uu____10389)
                  | uu____10406 -> failwith "impos"))
        | uu____10425 -> failwith "Impos" in
      match uu____10237 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___165_10473 = env in
            {
              bindings = (uu___165_10473.bindings);
              depth = (uu___165_10473.depth);
              tcenv = (uu___165_10473.tcenv);
              warn = (uu___165_10473.warn);
              cache = (uu___165_10473.cache);
              nolabels = (uu___165_10473.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___165_10473.encode_non_total_function_typ);
              current_module_name = (uu___165_10473.current_module_name)
            } in
          let uu____10474 =
            encode_binders FStar_Pervasives_Native.None binders env1 in
          (match uu____10474 with
           | (vars,guards,env2,decls,uu____10499) ->
               let uu____10512 =
                 let uu____10525 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____10569 =
                             let uu____10578 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2)) in
                             FStar_All.pipe_right uu____10578
                               FStar_List.unzip in
                           match uu____10569 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____10525 FStar_List.unzip in
               (match uu____10512 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post in
                    let env3 =
                      let uu___166_10690 = env2 in
                      {
                        bindings = (uu___166_10690.bindings);
                        depth = (uu___166_10690.depth);
                        tcenv = (uu___166_10690.tcenv);
                        warn = (uu___166_10690.warn);
                        cache = (uu___166_10690.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___166_10690.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___166_10690.encode_non_total_function_typ);
                        current_module_name =
                          (uu___166_10690.current_module_name)
                      } in
                    let uu____10691 =
                      let uu____10696 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____10696 env3 in
                    (match uu____10691 with
                     | (pre1,decls'') ->
                         let uu____10703 =
                           let uu____10708 = FStar_Syntax_Util.unmeta post1 in
                           encode_formula uu____10708 env3 in
                         (match uu____10703 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____10718 =
                                let uu____10719 =
                                  let uu____10730 =
                                    let uu____10731 =
                                      let uu____10736 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____10736, post2) in
                                    FStar_SMTEncoding_Util.mkImp uu____10731 in
                                  (pats, vars, uu____10730) in
                                FStar_SMTEncoding_Util.mkForall uu____10719 in
                              (uu____10718, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____10755 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____10755
        then
          let uu____10756 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____10757 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10756 uu____10757
        else () in
      let enc f r l =
        let uu____10790 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10818 =
                   encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu____10818 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____10790 with
        | (decls,args) ->
            let uu____10847 =
              let uu___167_10848 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___167_10848.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___167_10848.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____10847, decls) in
      let const_op f r uu____10879 =
        let uu____10892 = f r in (uu____10892, []) in
      let un_op f l =
        let uu____10911 = FStar_List.hd l in
        FStar_All.pipe_left f uu____10911 in
      let bin_op f uu___141_10927 =
        match uu___141_10927 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10938 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____10972 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____10995  ->
                 match uu____10995 with
                 | (t,uu____11009) ->
                     let uu____11010 = encode_formula t env in
                     (match uu____11010 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____10972 with
        | (decls,phis) ->
            let uu____11039 =
              let uu___168_11040 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___168_11040.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___168_11040.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____11039, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____11101  ->
               match uu____11101 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____11120) -> false
                    | uu____11121 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____11136 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____11136
        else
          (let uu____11150 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____11150 r rf) in
      let mk_imp1 r uu___142_11175 =
        match uu___142_11175 with
        | (lhs,uu____11181)::(rhs,uu____11183)::[] ->
            let uu____11210 = encode_formula rhs env in
            (match uu____11210 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11225) ->
                      (l1, decls1)
                  | uu____11230 ->
                      let uu____11231 = encode_formula lhs env in
                      (match uu____11231 with
                       | (l2,decls2) ->
                           let uu____11242 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____11242, (FStar_List.append decls1 decls2)))))
        | uu____11245 -> failwith "impossible" in
      let mk_ite r uu___143_11266 =
        match uu___143_11266 with
        | (guard,uu____11272)::(_then,uu____11274)::(_else,uu____11276)::[]
            ->
            let uu____11313 = encode_formula guard env in
            (match uu____11313 with
             | (g,decls1) ->
                 let uu____11324 = encode_formula _then env in
                 (match uu____11324 with
                  | (t,decls2) ->
                      let uu____11335 = encode_formula _else env in
                      (match uu____11335 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11349 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____11374 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____11374 in
      let connectives =
        let uu____11392 =
          let uu____11405 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Parser_Const.and_lid, uu____11405) in
        let uu____11422 =
          let uu____11437 =
            let uu____11450 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Parser_Const.or_lid, uu____11450) in
          let uu____11467 =
            let uu____11482 =
              let uu____11497 =
                let uu____11510 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Parser_Const.iff_lid, uu____11510) in
              let uu____11527 =
                let uu____11542 =
                  let uu____11557 =
                    let uu____11570 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Parser_Const.not_lid, uu____11570) in
                  [uu____11557;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11542 in
              uu____11497 :: uu____11527 in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11482 in
          uu____11437 :: uu____11467 in
        uu____11392 :: uu____11422 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____11891 = encode_formula phi' env in
            (match uu____11891 with
             | (phi2,decls) ->
                 let uu____11902 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____11902, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____11903 ->
            let uu____11910 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____11910 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____11949 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____11949 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____11961;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____11963;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____11984 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____11984 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____12031::(x,uu____12033)::(t,uu____12035)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12082 = encode_term x env in
                 (match uu____12082 with
                  | (x1,decls) ->
                      let uu____12093 = encode_term t env in
                      (match uu____12093 with
                       | (t1,decls') ->
                           let uu____12104 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____12104, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12109)::(msg,uu____12111)::(phi2,uu____12113)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12158 =
                   let uu____12163 =
                     let uu____12164 = FStar_Syntax_Subst.compress r in
                     uu____12164.FStar_Syntax_Syntax.n in
                   let uu____12167 =
                     let uu____12168 = FStar_Syntax_Subst.compress msg in
                     uu____12168.FStar_Syntax_Syntax.n in
                   (uu____12163, uu____12167) in
                 (match uu____12158 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12177))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1 in
                      fallback phi3
                  | uu____12183 -> fallback phi2)
             | uu____12188 when head_redex env head2 ->
                 let uu____12201 = whnf env phi1 in
                 encode_formula uu____12201 env
             | uu____12202 ->
                 let uu____12215 = encode_term phi1 env in
                 (match uu____12215 with
                  | (tt,decls) ->
                      let uu____12226 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___169_12229 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___169_12229.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___169_12229.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____12226, decls)))
        | uu____12230 ->
            let uu____12231 = encode_term phi1 env in
            (match uu____12231 with
             | (tt,decls) ->
                 let uu____12242 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___170_12245 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___170_12245.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___170_12245.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____12242, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____12281 = encode_binders FStar_Pervasives_Native.None bs env1 in
        match uu____12281 with
        | (vars,guards,env2,decls,uu____12320) ->
            let uu____12333 =
              let uu____12346 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____12394 =
                          let uu____12403 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____12433  ->
                                    match uu____12433 with
                                    | (t,uu____12443) ->
                                        encode_term t
                                          (let uu___171_12445 = env2 in
                                           {
                                             bindings =
                                               (uu___171_12445.bindings);
                                             depth = (uu___171_12445.depth);
                                             tcenv = (uu___171_12445.tcenv);
                                             warn = (uu___171_12445.warn);
                                             cache = (uu___171_12445.cache);
                                             nolabels =
                                               (uu___171_12445.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___171_12445.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___171_12445.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____12403 FStar_List.unzip in
                        match uu____12394 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____12346 FStar_List.unzip in
            (match uu____12333 with
             | (pats,decls') ->
                 let uu____12544 = encode_formula body env2 in
                 (match uu____12544 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12576;
                             FStar_SMTEncoding_Term.rng = uu____12577;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____12592 -> guards in
                      let uu____12597 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____12597, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____12657  ->
                   match uu____12657 with
                   | (x,uu____12663) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____12671 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____12683 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____12683) uu____12671 tl1 in
             let uu____12686 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____12713  ->
                       match uu____12713 with
                       | (b,uu____12719) ->
                           let uu____12720 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____12720)) in
             (match uu____12686 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____12726) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____12740 =
                    let uu____12741 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____12741 in
                  FStar_Errors.warn pos uu____12740) in
       let uu____12742 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____12742 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12751 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____12809  ->
                     match uu____12809 with
                     | (l,uu____12823) -> FStar_Ident.lid_equals op l)) in
           (match uu____12751 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____12856,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12896 = encode_q_body env vars pats body in
             match uu____12896 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____12941 =
                     let uu____12952 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____12952) in
                   FStar_SMTEncoding_Term.mkForall uu____12941
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12971 = encode_q_body env vars pats body in
             match uu____12971 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____13015 =
                   let uu____13016 =
                     let uu____13027 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____13027) in
                   FStar_SMTEncoding_Term.mkExists uu____13016
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____13015, decls))))
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple2;
  is: FStar_Ident.lident -> Prims.bool;}[@@deriving show]
let __proj__Mkprims_t__item__mk:
  prims_t ->
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun projectee  ->
    match projectee with
    | { mk = __fname__mk; is = __fname__is;_} -> __fname__mk
let __proj__Mkprims_t__item__is: prims_t -> FStar_Ident.lident -> Prims.bool
  =
  fun projectee  ->
    match projectee with
    | { mk = __fname__mk; is = __fname__is;_} -> __fname__is
let prims: prims_t =
  let uu____13125 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____13125 with
  | (asym,a) ->
      let uu____13132 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____13132 with
       | (xsym,x) ->
           let uu____13139 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____13139 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____13183 =
                      let uu____13194 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd) in
                      (x1, uu____13194, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13183 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                  let xapp =
                    let uu____13220 =
                      let uu____13227 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____13227) in
                    FStar_SMTEncoding_Util.mkApp uu____13220 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____13240 =
                    let uu____13243 =
                      let uu____13246 =
                        let uu____13249 =
                          let uu____13250 =
                            let uu____13257 =
                              let uu____13258 =
                                let uu____13269 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____13269) in
                              FStar_SMTEncoding_Util.mkForall uu____13258 in
                            (uu____13257, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____13250 in
                        let uu____13286 =
                          let uu____13289 =
                            let uu____13290 =
                              let uu____13297 =
                                let uu____13298 =
                                  let uu____13309 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____13309) in
                                FStar_SMTEncoding_Util.mkForall uu____13298 in
                              (uu____13297,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____13290 in
                          [uu____13289] in
                        uu____13249 :: uu____13286 in
                      xtok_decl :: uu____13246 in
                    xname_decl :: uu____13243 in
                  (xtok1, uu____13240) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____13400 =
                    let uu____13413 =
                      let uu____13422 =
                        let uu____13423 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____13423 in
                      quant axy uu____13422 in
                    (FStar_Parser_Const.op_Eq, uu____13413) in
                  let uu____13432 =
                    let uu____13447 =
                      let uu____13460 =
                        let uu____13469 =
                          let uu____13470 =
                            let uu____13471 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____13471 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____13470 in
                        quant axy uu____13469 in
                      (FStar_Parser_Const.op_notEq, uu____13460) in
                    let uu____13480 =
                      let uu____13495 =
                        let uu____13508 =
                          let uu____13517 =
                            let uu____13518 =
                              let uu____13519 =
                                let uu____13524 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____13525 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____13524, uu____13525) in
                              FStar_SMTEncoding_Util.mkLT uu____13519 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____13518 in
                          quant xy uu____13517 in
                        (FStar_Parser_Const.op_LT, uu____13508) in
                      let uu____13534 =
                        let uu____13549 =
                          let uu____13562 =
                            let uu____13571 =
                              let uu____13572 =
                                let uu____13573 =
                                  let uu____13578 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____13579 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____13578, uu____13579) in
                                FStar_SMTEncoding_Util.mkLTE uu____13573 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____13572 in
                            quant xy uu____13571 in
                          (FStar_Parser_Const.op_LTE, uu____13562) in
                        let uu____13588 =
                          let uu____13603 =
                            let uu____13616 =
                              let uu____13625 =
                                let uu____13626 =
                                  let uu____13627 =
                                    let uu____13632 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____13633 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____13632, uu____13633) in
                                  FStar_SMTEncoding_Util.mkGT uu____13627 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____13626 in
                              quant xy uu____13625 in
                            (FStar_Parser_Const.op_GT, uu____13616) in
                          let uu____13642 =
                            let uu____13657 =
                              let uu____13670 =
                                let uu____13679 =
                                  let uu____13680 =
                                    let uu____13681 =
                                      let uu____13686 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____13687 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____13686, uu____13687) in
                                    FStar_SMTEncoding_Util.mkGTE uu____13681 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____13680 in
                                quant xy uu____13679 in
                              (FStar_Parser_Const.op_GTE, uu____13670) in
                            let uu____13696 =
                              let uu____13711 =
                                let uu____13724 =
                                  let uu____13733 =
                                    let uu____13734 =
                                      let uu____13735 =
                                        let uu____13740 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____13741 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____13740, uu____13741) in
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____13735 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____13734 in
                                  quant xy uu____13733 in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____13724) in
                              let uu____13750 =
                                let uu____13765 =
                                  let uu____13778 =
                                    let uu____13787 =
                                      let uu____13788 =
                                        let uu____13789 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____13789 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____13788 in
                                    quant qx uu____13787 in
                                  (FStar_Parser_Const.op_Minus, uu____13778) in
                                let uu____13798 =
                                  let uu____13813 =
                                    let uu____13826 =
                                      let uu____13835 =
                                        let uu____13836 =
                                          let uu____13837 =
                                            let uu____13842 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____13843 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____13842, uu____13843) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____13837 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____13836 in
                                      quant xy uu____13835 in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____13826) in
                                  let uu____13852 =
                                    let uu____13867 =
                                      let uu____13880 =
                                        let uu____13889 =
                                          let uu____13890 =
                                            let uu____13891 =
                                              let uu____13896 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____13897 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____13896, uu____13897) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____13891 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____13890 in
                                        quant xy uu____13889 in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____13880) in
                                    let uu____13906 =
                                      let uu____13921 =
                                        let uu____13934 =
                                          let uu____13943 =
                                            let uu____13944 =
                                              let uu____13945 =
                                                let uu____13950 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____13951 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____13950, uu____13951) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____13945 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____13944 in
                                          quant xy uu____13943 in
                                        (FStar_Parser_Const.op_Division,
                                          uu____13934) in
                                      let uu____13960 =
                                        let uu____13975 =
                                          let uu____13988 =
                                            let uu____13997 =
                                              let uu____13998 =
                                                let uu____13999 =
                                                  let uu____14004 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____14005 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____14004, uu____14005) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____13999 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____13998 in
                                            quant xy uu____13997 in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____13988) in
                                        let uu____14014 =
                                          let uu____14029 =
                                            let uu____14042 =
                                              let uu____14051 =
                                                let uu____14052 =
                                                  let uu____14053 =
                                                    let uu____14058 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____14059 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____14058,
                                                      uu____14059) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____14053 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____14052 in
                                              quant xy uu____14051 in
                                            (FStar_Parser_Const.op_And,
                                              uu____14042) in
                                          let uu____14068 =
                                            let uu____14083 =
                                              let uu____14096 =
                                                let uu____14105 =
                                                  let uu____14106 =
                                                    let uu____14107 =
                                                      let uu____14112 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____14113 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____14112,
                                                        uu____14113) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____14107 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____14106 in
                                                quant xy uu____14105 in
                                              (FStar_Parser_Const.op_Or,
                                                uu____14096) in
                                            let uu____14122 =
                                              let uu____14137 =
                                                let uu____14150 =
                                                  let uu____14159 =
                                                    let uu____14160 =
                                                      let uu____14161 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____14161 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____14160 in
                                                  quant qx uu____14159 in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____14150) in
                                              [uu____14137] in
                                            uu____14083 :: uu____14122 in
                                          uu____14029 :: uu____14068 in
                                        uu____13975 :: uu____14014 in
                                      uu____13921 :: uu____13960 in
                                    uu____13867 :: uu____13906 in
                                  uu____13813 :: uu____13852 in
                                uu____13765 :: uu____13798 in
                              uu____13711 :: uu____13750 in
                            uu____13657 :: uu____13696 in
                          uu____13603 :: uu____13642 in
                        uu____13549 :: uu____13588 in
                      uu____13495 :: uu____13534 in
                    uu____13447 :: uu____13480 in
                  uu____13400 :: uu____13432 in
                let mk1 l v1 =
                  let uu____14375 =
                    let uu____14384 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____14442  ->
                              match uu____14442 with
                              | (l',uu____14456) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____14384
                      (FStar_Option.map
                         (fun uu____14516  ->
                            match uu____14516 with | (uu____14535,b) -> b v1)) in
                  FStar_All.pipe_right uu____14375 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____14606  ->
                          match uu____14606 with
                          | (l',uu____14620) -> FStar_Ident.lid_equals l l')) in
                { mk = mk1; is }))
let pretype_axiom:
  env_t ->
    FStar_SMTEncoding_Term.term ->
      (Prims.string,FStar_SMTEncoding_Term.sort)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_SMTEncoding_Term.decl
  =
  fun env  ->
    fun tapp  ->
      fun vars  ->
        let uu____14661 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____14661 with
        | (xxsym,xx) ->
            let uu____14668 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____14668 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____14678 =
                   let uu____14685 =
                     let uu____14686 =
                       let uu____14697 =
                         let uu____14698 =
                           let uu____14703 =
                             let uu____14704 =
                               let uu____14709 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____14709) in
                             FStar_SMTEncoding_Util.mkEq uu____14704 in
                           (xx_has_type, uu____14703) in
                         FStar_SMTEncoding_Util.mkImp uu____14698 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____14697) in
                     FStar_SMTEncoding_Util.mkForall uu____14686 in
                   let uu____14734 =
                     let uu____14735 =
                       let uu____14736 =
                         let uu____14737 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____14737 in
                       Prims.strcat module_name uu____14736 in
                     varops.mk_unique uu____14735 in
                   (uu____14685, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____14734) in
                 FStar_SMTEncoding_Util.mkAssume uu____14678)
let primitive_type_axioms:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      Prims.string ->
        FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.decl Prims.list
  =
  let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
  let x = FStar_SMTEncoding_Util.mkFreeV xx in
  let yy = ("y", FStar_SMTEncoding_Term.Term_sort) in
  let y = FStar_SMTEncoding_Util.mkFreeV yy in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let uu____14777 =
      let uu____14778 =
        let uu____14785 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____14785, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14778 in
    let uu____14788 =
      let uu____14791 =
        let uu____14792 =
          let uu____14799 =
            let uu____14800 =
              let uu____14811 =
                let uu____14812 =
                  let uu____14817 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____14817) in
                FStar_SMTEncoding_Util.mkImp uu____14812 in
              ([[typing_pred]], [xx], uu____14811) in
            mkForall_fuel uu____14800 in
          (uu____14799, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14792 in
      [uu____14791] in
    uu____14777 :: uu____14788 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____14859 =
      let uu____14860 =
        let uu____14867 =
          let uu____14868 =
            let uu____14879 =
              let uu____14884 =
                let uu____14887 = FStar_SMTEncoding_Term.boxBool b in
                [uu____14887] in
              [uu____14884] in
            let uu____14892 =
              let uu____14893 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____14893 tt in
            (uu____14879, [bb], uu____14892) in
          FStar_SMTEncoding_Util.mkForall uu____14868 in
        (uu____14867, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14860 in
    let uu____14914 =
      let uu____14917 =
        let uu____14918 =
          let uu____14925 =
            let uu____14926 =
              let uu____14937 =
                let uu____14938 =
                  let uu____14943 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x in
                  (typing_pred, uu____14943) in
                FStar_SMTEncoding_Util.mkImp uu____14938 in
              ([[typing_pred]], [xx], uu____14937) in
            mkForall_fuel uu____14926 in
          (uu____14925, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14918 in
      [uu____14917] in
    uu____14859 :: uu____14914 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____14993 =
        let uu____14994 =
          let uu____15001 =
            let uu____15004 =
              let uu____15007 =
                let uu____15010 = FStar_SMTEncoding_Term.boxInt a in
                let uu____15011 =
                  let uu____15014 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____15014] in
                uu____15010 :: uu____15011 in
              tt :: uu____15007 in
            tt :: uu____15004 in
          ("Prims.Precedes", uu____15001) in
        FStar_SMTEncoding_Util.mkApp uu____14994 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14993 in
    let precedes_y_x =
      let uu____15018 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15018 in
    let uu____15021 =
      let uu____15022 =
        let uu____15029 =
          let uu____15030 =
            let uu____15041 =
              let uu____15046 =
                let uu____15049 = FStar_SMTEncoding_Term.boxInt b in
                [uu____15049] in
              [uu____15046] in
            let uu____15054 =
              let uu____15055 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____15055 tt in
            (uu____15041, [bb], uu____15054) in
          FStar_SMTEncoding_Util.mkForall uu____15030 in
        (uu____15029, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15022 in
    let uu____15076 =
      let uu____15079 =
        let uu____15080 =
          let uu____15087 =
            let uu____15088 =
              let uu____15099 =
                let uu____15100 =
                  let uu____15105 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x in
                  (typing_pred, uu____15105) in
                FStar_SMTEncoding_Util.mkImp uu____15100 in
              ([[typing_pred]], [xx], uu____15099) in
            mkForall_fuel uu____15088 in
          (uu____15087, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15080 in
      let uu____15130 =
        let uu____15133 =
          let uu____15134 =
            let uu____15141 =
              let uu____15142 =
                let uu____15153 =
                  let uu____15154 =
                    let uu____15159 =
                      let uu____15160 =
                        let uu____15163 =
                          let uu____15166 =
                            let uu____15169 =
                              let uu____15170 =
                                let uu____15175 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____15176 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____15175, uu____15176) in
                              FStar_SMTEncoding_Util.mkGT uu____15170 in
                            let uu____15177 =
                              let uu____15180 =
                                let uu____15181 =
                                  let uu____15186 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____15187 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____15186, uu____15187) in
                                FStar_SMTEncoding_Util.mkGTE uu____15181 in
                              let uu____15188 =
                                let uu____15191 =
                                  let uu____15192 =
                                    let uu____15197 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____15198 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____15197, uu____15198) in
                                  FStar_SMTEncoding_Util.mkLT uu____15192 in
                                [uu____15191] in
                              uu____15180 :: uu____15188 in
                            uu____15169 :: uu____15177 in
                          typing_pred_y :: uu____15166 in
                        typing_pred :: uu____15163 in
                      FStar_SMTEncoding_Util.mk_and_l uu____15160 in
                    (uu____15159, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____15154 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____15153) in
              mkForall_fuel uu____15142 in
            (uu____15141,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____15134 in
        [uu____15133] in
      uu____15079 :: uu____15130 in
    uu____15021 :: uu____15076 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____15244 =
      let uu____15245 =
        let uu____15252 =
          let uu____15253 =
            let uu____15264 =
              let uu____15269 =
                let uu____15272 = FStar_SMTEncoding_Term.boxString b in
                [uu____15272] in
              [uu____15269] in
            let uu____15277 =
              let uu____15278 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____15278 tt in
            (uu____15264, [bb], uu____15277) in
          FStar_SMTEncoding_Util.mkForall uu____15253 in
        (uu____15252, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15245 in
    let uu____15299 =
      let uu____15302 =
        let uu____15303 =
          let uu____15310 =
            let uu____15311 =
              let uu____15322 =
                let uu____15323 =
                  let uu____15328 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x in
                  (typing_pred, uu____15328) in
                FStar_SMTEncoding_Util.mkImp uu____15323 in
              ([[typing_pred]], [xx], uu____15322) in
            mkForall_fuel uu____15311 in
          (uu____15310, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15303 in
      [uu____15302] in
    uu____15244 :: uu____15299 in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____15381 =
      let uu____15382 =
        let uu____15389 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____15389, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15382 in
    [uu____15381] in
  let mk_and_interp env conj uu____15401 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15426 =
      let uu____15427 =
        let uu____15434 =
          let uu____15435 =
            let uu____15446 =
              let uu____15447 =
                let uu____15452 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____15452, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15447 in
            ([[l_and_a_b]], [aa; bb], uu____15446) in
          FStar_SMTEncoding_Util.mkForall uu____15435 in
        (uu____15434, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15427 in
    [uu____15426] in
  let mk_or_interp env disj uu____15490 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15515 =
      let uu____15516 =
        let uu____15523 =
          let uu____15524 =
            let uu____15535 =
              let uu____15536 =
                let uu____15541 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____15541, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15536 in
            ([[l_or_a_b]], [aa; bb], uu____15535) in
          FStar_SMTEncoding_Util.mkForall uu____15524 in
        (uu____15523, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15516 in
    [uu____15515] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____15604 =
      let uu____15605 =
        let uu____15612 =
          let uu____15613 =
            let uu____15624 =
              let uu____15625 =
                let uu____15630 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15630, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15625 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____15624) in
          FStar_SMTEncoding_Util.mkForall uu____15613 in
        (uu____15612, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15605 in
    [uu____15604] in
  let mk_eq3_interp env eq3 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq3_x_y = FStar_SMTEncoding_Util.mkApp (eq3, [a; b; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq3_x_y]) in
    let uu____15703 =
      let uu____15704 =
        let uu____15711 =
          let uu____15712 =
            let uu____15723 =
              let uu____15724 =
                let uu____15729 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15729, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15724 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____15723) in
          FStar_SMTEncoding_Util.mkForall uu____15712 in
        (uu____15711, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15704 in
    [uu____15703] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15800 =
      let uu____15801 =
        let uu____15808 =
          let uu____15809 =
            let uu____15820 =
              let uu____15821 =
                let uu____15826 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____15826, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15821 in
            ([[l_imp_a_b]], [aa; bb], uu____15820) in
          FStar_SMTEncoding_Util.mkForall uu____15809 in
        (uu____15808, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15801 in
    [uu____15800] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15889 =
      let uu____15890 =
        let uu____15897 =
          let uu____15898 =
            let uu____15909 =
              let uu____15910 =
                let uu____15915 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____15915, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15910 in
            ([[l_iff_a_b]], [aa; bb], uu____15909) in
          FStar_SMTEncoding_Util.mkForall uu____15898 in
        (uu____15897, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15890 in
    [uu____15889] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____15967 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____15967 in
    let uu____15970 =
      let uu____15971 =
        let uu____15978 =
          let uu____15979 =
            let uu____15990 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____15990) in
          FStar_SMTEncoding_Util.mkForall uu____15979 in
        (uu____15978, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15971 in
    [uu____15970] in
  let mk_forall_interp env for_all1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let l_forall_a_b = FStar_SMTEncoding_Util.mkApp (for_all1, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_forall_a_b]) in
    let valid_b_x =
      let uu____16050 =
        let uu____16057 =
          let uu____16060 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16060] in
        ("Valid", uu____16057) in
      FStar_SMTEncoding_Util.mkApp uu____16050 in
    let uu____16063 =
      let uu____16064 =
        let uu____16071 =
          let uu____16072 =
            let uu____16083 =
              let uu____16084 =
                let uu____16089 =
                  let uu____16090 =
                    let uu____16101 =
                      let uu____16106 =
                        let uu____16109 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16109] in
                      [uu____16106] in
                    let uu____16114 =
                      let uu____16115 =
                        let uu____16120 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16120, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16115 in
                    (uu____16101, [xx1], uu____16114) in
                  FStar_SMTEncoding_Util.mkForall uu____16090 in
                (uu____16089, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16084 in
            ([[l_forall_a_b]], [aa; bb], uu____16083) in
          FStar_SMTEncoding_Util.mkForall uu____16072 in
        (uu____16071, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16064 in
    [uu____16063] in
  let mk_exists_interp env for_some1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let l_exists_a_b = FStar_SMTEncoding_Util.mkApp (for_some1, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_exists_a_b]) in
    let valid_b_x =
      let uu____16202 =
        let uu____16209 =
          let uu____16212 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16212] in
        ("Valid", uu____16209) in
      FStar_SMTEncoding_Util.mkApp uu____16202 in
    let uu____16215 =
      let uu____16216 =
        let uu____16223 =
          let uu____16224 =
            let uu____16235 =
              let uu____16236 =
                let uu____16241 =
                  let uu____16242 =
                    let uu____16253 =
                      let uu____16258 =
                        let uu____16261 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16261] in
                      [uu____16258] in
                    let uu____16266 =
                      let uu____16267 =
                        let uu____16272 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16272, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16267 in
                    (uu____16253, [xx1], uu____16266) in
                  FStar_SMTEncoding_Util.mkExists uu____16242 in
                (uu____16241, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16236 in
            ([[l_exists_a_b]], [aa; bb], uu____16235) in
          FStar_SMTEncoding_Util.mkForall uu____16224 in
        (uu____16223, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16216 in
    [uu____16215] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____16332 =
      let uu____16333 =
        let uu____16340 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____16341 = varops.mk_unique "typing_range_const" in
        (uu____16340, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____16341) in
      FStar_SMTEncoding_Util.mkAssume uu____16333 in
    [uu____16332] in
  let mk_inversion_axiom env inversion tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort) in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1 in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let inversion_t = FStar_SMTEncoding_Util.mkApp (inversion, [t]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [inversion_t]) in
    let body =
      let hastypeZ = FStar_SMTEncoding_Term.mk_HasTypeZ x1 t in
      let hastypeS =
        let uu____16375 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1") in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____16375 x1 t in
      let uu____16376 =
        let uu____16387 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS) in
        ([[hastypeZ]], [xx1], uu____16387) in
      FStar_SMTEncoding_Util.mkForall uu____16376 in
    let uu____16410 =
      let uu____16411 =
        let uu____16418 =
          let uu____16419 =
            let uu____16430 = FStar_SMTEncoding_Util.mkImp (valid, body) in
            ([[inversion_t]], [tt1], uu____16430) in
          FStar_SMTEncoding_Util.mkForall uu____16419 in
        (uu____16418,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16411 in
    [uu____16410] in
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
    (FStar_Parser_Const.inversion_lid, mk_inversion_axiom)] in
  fun env  ->
    fun t  ->
      fun s  ->
        fun tt  ->
          let uu____16754 =
            FStar_Util.find_opt
              (fun uu____16780  ->
                 match uu____16780 with
                 | (l,uu____16792) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____16754 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____16817,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____16856 = encode_function_type_as_formula t env in
        match uu____16856 with
        | (form,decls) ->
            FStar_List.append decls
              [FStar_SMTEncoding_Util.mkAssume
                 (form,
                   (FStar_Pervasives_Native.Some
                      (Prims.strcat "Lemma: " lid.FStar_Ident.str)),
                   (Prims.strcat "lemma_" lid.FStar_Ident.str))]
let encode_free_var:
  Prims.bool ->
    env_t ->
      FStar_Syntax_Syntax.fv ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.qualifier Prims.list ->
              (FStar_SMTEncoding_Term.decl Prims.list,env_t)
                FStar_Pervasives_Native.tuple2
  =
  fun uninterpreted  ->
    fun env  ->
      fun fv  ->
        fun tt  ->
          fun t_norm  ->
            fun quals  ->
              let lid =
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
              let uu____16902 =
                ((let uu____16905 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm) in
                  FStar_All.pipe_left Prims.op_Negation uu____16905) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted in
              if uu____16902
              then
                let uu____16912 = new_term_constant_and_tok_from_lid env lid in
                match uu____16912 with
                | (vname,vtok,env1) ->
                    let arg_sorts =
                      let uu____16931 =
                        let uu____16932 = FStar_Syntax_Subst.compress t_norm in
                        uu____16932.FStar_Syntax_Syntax.n in
                      match uu____16931 with
                      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____16938) ->
                          FStar_All.pipe_right binders
                            (FStar_List.map
                               (fun uu____16968  ->
                                  FStar_SMTEncoding_Term.Term_sort))
                      | uu____16973 -> [] in
                    let d =
                      FStar_SMTEncoding_Term.DeclFun
                        (vname, arg_sorts, FStar_SMTEncoding_Term.Term_sort,
                          (FStar_Pervasives_Native.Some
                             "Uninterpreted function symbol for impure function")) in
                    let dd =
                      FStar_SMTEncoding_Term.DeclFun
                        (vtok, [], FStar_SMTEncoding_Term.Term_sort,
                          (FStar_Pervasives_Native.Some
                             "Uninterpreted name for impure function")) in
                    ([d; dd], env1)
              else
                (let uu____16987 = prims.is lid in
                 if uu____16987
                 then
                   let vname = varops.new_fvar lid in
                   let uu____16995 = prims.mk lid vname in
                   match uu____16995 with
                   | (tok,definition) ->
                       let env1 =
                         push_free_var env lid vname
                           (FStar_Pervasives_Native.Some tok) in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims" in
                    let uu____17019 =
                      let uu____17030 = curried_arrow_formals_comp t_norm in
                      match uu____17030 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____17048 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp in
                            if uu____17048
                            then
                              let uu____17049 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___172_17052 = env.tcenv in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___172_17052.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___172_17052.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___172_17052.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___172_17052.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___172_17052.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___172_17052.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___172_17052.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___172_17052.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___172_17052.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___172_17052.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___172_17052.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___172_17052.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___172_17052.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___172_17052.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___172_17052.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___172_17052.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___172_17052.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___172_17052.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___172_17052.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___172_17052.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___172_17052.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___172_17052.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___172_17052.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___172_17052.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___172_17052.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qname_and_index =
                                       (uu___172_17052.FStar_TypeChecker_Env.qname_and_index);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___172_17052.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth =
                                       (uu___172_17052.FStar_TypeChecker_Env.synth);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___172_17052.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___172_17052.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___172_17052.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___172_17052.FStar_TypeChecker_Env.dsenv)
                                   }) comp FStar_Syntax_Syntax.U_unknown in
                              FStar_Syntax_Syntax.mk_Total uu____17049
                            else comp in
                          if encode_non_total_function_typ
                          then
                            let uu____17064 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1 in
                            (args, uu____17064)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1))) in
                    match uu____17019 with
                    | (formals,(pre_opt,res_t)) ->
                        let uu____17109 =
                          new_term_constant_and_tok_from_lid env lid in
                        (match uu____17109 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____17130 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, []) in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___144_17172  ->
                                       match uu___144_17172 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____17176 =
                                             FStar_Util.prefix vars in
                                           (match uu____17176 with
                                            | (uu____17197,(xxsym,uu____17199))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort) in
                                                let uu____17217 =
                                                  let uu____17218 =
                                                    let uu____17225 =
                                                      let uu____17226 =
                                                        let uu____17237 =
                                                          let uu____17238 =
                                                            let uu____17243 =
                                                              let uu____17244
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____17244 in
                                                            (vapp,
                                                              uu____17243) in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____17238 in
                                                        ([[vapp]], vars,
                                                          uu____17237) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17226 in
                                                    (uu____17225,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str))) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17218 in
                                                [uu____17217])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____17263 =
                                             FStar_Util.prefix vars in
                                           (match uu____17263 with
                                            | (uu____17284,(xxsym,uu____17286))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort) in
                                                let f1 =
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      = f;
                                                    FStar_Syntax_Syntax.index
                                                      = (Prims.parse_int "0");
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      FStar_Syntax_Syntax.tun
                                                  } in
                                                let tp_name =
                                                  mk_term_projector_name d f1 in
                                                let prim_app =
                                                  FStar_SMTEncoding_Util.mkApp
                                                    (tp_name, [xx]) in
                                                let uu____17309 =
                                                  let uu____17310 =
                                                    let uu____17317 =
                                                      let uu____17318 =
                                                        let uu____17329 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app) in
                                                        ([[vapp]], vars,
                                                          uu____17329) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17318 in
                                                    (uu____17317,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name)) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17310 in
                                                [uu____17309])
                                       | uu____17346 -> [])) in
                             let uu____17347 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1 in
                             (match uu____17347 with
                              | (vars,guards,env',decls1,uu____17374) ->
                                  let uu____17387 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____17396 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards in
                                        (uu____17396, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____17398 =
                                          encode_formula p env' in
                                        (match uu____17398 with
                                         | (g,ds) ->
                                             let uu____17409 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards) in
                                             (uu____17409,
                                               (FStar_List.append decls1 ds))) in
                                  (match uu____17387 with
                                   | (guard,decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars in
                                       let vapp =
                                         let uu____17422 =
                                           let uu____17429 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars in
                                           (vname, uu____17429) in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____17422 in
                                       let uu____17438 =
                                         let vname_decl =
                                           let uu____17446 =
                                             let uu____17457 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____17467  ->
                                                       FStar_SMTEncoding_Term.Term_sort)) in
                                             (vname, uu____17457,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None) in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____17446 in
                                         let uu____17476 =
                                           let env2 =
                                             let uu___173_17482 = env1 in
                                             {
                                               bindings =
                                                 (uu___173_17482.bindings);
                                               depth = (uu___173_17482.depth);
                                               tcenv = (uu___173_17482.tcenv);
                                               warn = (uu___173_17482.warn);
                                               cache = (uu___173_17482.cache);
                                               nolabels =
                                                 (uu___173_17482.nolabels);
                                               use_zfuel_name =
                                                 (uu___173_17482.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___173_17482.current_module_name)
                                             } in
                                           let uu____17483 =
                                             let uu____17484 =
                                               head_normal env2 tt in
                                             Prims.op_Negation uu____17484 in
                                           if uu____17483
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm in
                                         match uu____17476 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____17499::uu____17500 ->
                                                   let ff =
                                                     ("ty",
                                                       FStar_SMTEncoding_Term.Term_sort) in
                                                   let f =
                                                     FStar_SMTEncoding_Util.mkFreeV
                                                       ff in
                                                   let vtok_app_l =
                                                     mk_Apply vtok_tm [ff] in
                                                   let vtok_app_r =
                                                     mk_Apply f
                                                       [(vtok,
                                                          FStar_SMTEncoding_Term.Term_sort)] in
                                                   let guarded_tok_typing =
                                                     let uu____17540 =
                                                       let uu____17551 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____17551) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____17540 in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____17578 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname)) in
                                             let uu____17581 =
                                               match formals with
                                               | [] ->
                                                   let uu____17598 =
                                                     let uu____17599 =
                                                       let uu____17602 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort) in
                                                       FStar_All.pipe_left
                                                         (fun _0_43  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_43)
                                                         uu____17602 in
                                                     push_free_var env1 lid
                                                       vname uu____17599 in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____17598)
                                               | uu____17607 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None) in
                                                   let name_tok_corr =
                                                     let uu____17614 =
                                                       let uu____17621 =
                                                         let uu____17622 =
                                                           let uu____17633 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp) in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____17633) in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____17622 in
                                                       (uu____17621,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname)) in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____17614 in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       name_tok_corr;
                                                       tok_typing1]), env1) in
                                             (match uu____17581 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2)) in
                                       (match uu____17438 with
                                        | (decls2,env2) ->
                                            let uu____17676 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t in
                                              let uu____17684 =
                                                encode_term res_t1 env' in
                                              match uu____17684 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____17697 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t in
                                                  (encoded_res_t,
                                                    uu____17697, decls) in
                                            (match uu____17676 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____17708 =
                                                     let uu____17715 =
                                                       let uu____17716 =
                                                         let uu____17727 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred) in
                                                         ([[vapp]], vars,
                                                           uu____17727) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____17716 in
                                                     (uu____17715,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____17708 in
                                                 let freshness =
                                                   let uu____17743 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New) in
                                                   if uu____17743
                                                   then
                                                     let uu____17748 =
                                                       let uu____17749 =
                                                         let uu____17760 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd) in
                                                         let uu____17771 =
                                                           varops.next_id () in
                                                         (vname, uu____17760,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____17771) in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____17749 in
                                                     let uu____17774 =
                                                       let uu____17777 =
                                                         pretype_axiom env2
                                                           vapp vars in
                                                       [uu____17777] in
                                                     uu____17748 ::
                                                       uu____17774
                                                   else [] in
                                                 let g =
                                                   let uu____17782 =
                                                     let uu____17785 =
                                                       let uu____17788 =
                                                         let uu____17791 =
                                                           let uu____17794 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars in
                                                           typingAx ::
                                                             uu____17794 in
                                                         FStar_List.append
                                                           freshness
                                                           uu____17791 in
                                                       FStar_List.append
                                                         decls3 uu____17788 in
                                                     FStar_List.append decls2
                                                       uu____17785 in
                                                   FStar_List.append decls11
                                                     uu____17782 in
                                                 (g, env2))))))))
let declare_top_level_let:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          ((Prims.string,FStar_SMTEncoding_Term.term
                           FStar_Pervasives_Native.option)
             FStar_Pervasives_Native.tuple2,FStar_SMTEncoding_Term.decl
                                              Prims.list,env_t)
            FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun x  ->
      fun t  ->
        fun t_norm  ->
          let uu____17829 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____17829 with
          | FStar_Pervasives_Native.None  ->
              let uu____17866 = encode_free_var false env x t t_norm [] in
              (match uu____17866 with
               | (decls,env1) ->
                   let uu____17893 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____17893 with
                    | (n1,x',uu____17920) -> ((n1, x'), decls, env1)))
          | FStar_Pervasives_Native.Some (n1,x1,uu____17941) ->
              ((n1, x1), [], env)
let encode_top_level_val:
  Prims.bool ->
    env_t ->
      FStar_Syntax_Syntax.fv ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.qualifier Prims.list ->
            (FStar_SMTEncoding_Term.decl Prims.list,env_t)
              FStar_Pervasives_Native.tuple2
  =
  fun uninterpreted  ->
    fun env  ->
      fun lid  ->
        fun t  ->
          fun quals  ->
            let tt = norm env t in
            let uu____18001 =
              encode_free_var uninterpreted env lid t tt quals in
            match uu____18001 with
            | (decls,env1) ->
                let uu____18020 = FStar_Syntax_Util.is_smt_lemma t in
                if uu____18020
                then
                  let uu____18027 =
                    let uu____18030 = encode_smt_lemma env1 lid tt in
                    FStar_List.append decls uu____18030 in
                  (uu____18027, env1)
                else (decls, env1)
let encode_top_level_vals:
  env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      fun quals  ->
        FStar_All.pipe_right bindings
          (FStar_List.fold_left
             (fun uu____18085  ->
                fun lb  ->
                  match uu____18085 with
                  | (decls,env1) ->
                      let uu____18105 =
                        let uu____18112 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val false env1 uu____18112
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____18105 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____18134 = FStar_Syntax_Util.head_and_args t in
    match uu____18134 with
    | (hd1,args) ->
        let uu____18171 =
          let uu____18172 = FStar_Syntax_Util.un_uinst hd1 in
          uu____18172.FStar_Syntax_Syntax.n in
        (match uu____18171 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____18176,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____18195 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____18220  ->
      fun quals  ->
        match uu____18220 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____18296 = FStar_Util.first_N nbinders formals in
              match uu____18296 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____18377  ->
                         fun uu____18378  ->
                           match (uu____18377, uu____18378) with
                           | ((formal,uu____18396),(binder,uu____18398)) ->
                               let uu____18407 =
                                 let uu____18414 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____18414) in
                               FStar_Syntax_Syntax.NT uu____18407) formals1
                      binders in
                  let extra_formals1 =
                    let uu____18422 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____18453  ->
                              match uu____18453 with
                              | (x,i) ->
                                  let uu____18464 =
                                    let uu___174_18465 = x in
                                    let uu____18466 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___174_18465.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___174_18465.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____18466
                                    } in
                                  (uu____18464, i))) in
                    FStar_All.pipe_right uu____18422
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____18484 =
                      let uu____18485 = FStar_Syntax_Subst.compress body in
                      let uu____18486 =
                        let uu____18487 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____18487 in
                      FStar_Syntax_Syntax.extend_app_n uu____18485
                        uu____18486 in
                    uu____18484 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____18548 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____18548
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___175_18551 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___175_18551.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___175_18551.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___175_18551.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___175_18551.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___175_18551.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___175_18551.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___175_18551.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___175_18551.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___175_18551.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___175_18551.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___175_18551.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___175_18551.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___175_18551.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___175_18551.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___175_18551.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___175_18551.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___175_18551.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___175_18551.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___175_18551.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___175_18551.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___175_18551.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___175_18551.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___175_18551.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___175_18551.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___175_18551.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___175_18551.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___175_18551.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___175_18551.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___175_18551.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___175_18551.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___175_18551.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___175_18551.FStar_TypeChecker_Env.dsenv)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____18584 = FStar_Syntax_Util.abs_formals e in
                match uu____18584 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____18648::uu____18649 ->
                         let uu____18664 =
                           let uu____18665 =
                             let uu____18668 =
                               FStar_Syntax_Subst.compress t_norm1 in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____18668 in
                           uu____18665.FStar_Syntax_Syntax.n in
                         (match uu____18664 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____18711 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____18711 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____18753 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____18753
                                   then
                                     let uu____18788 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____18788 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____18882  ->
                                                   fun uu____18883  ->
                                                     match (uu____18882,
                                                             uu____18883)
                                                     with
                                                     | ((x,uu____18901),
                                                        (b,uu____18903)) ->
                                                         let uu____18912 =
                                                           let uu____18919 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____18919) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____18912)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____18921 =
                                            let uu____18942 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____18942) in
                                          (uu____18921, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____19010 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____19010 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____19099) ->
                              let uu____19104 =
                                let uu____19125 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                FStar_Pervasives_Native.fst uu____19125 in
                              (uu____19104, true)
                          | uu____19190 when Prims.op_Negation norm1 ->
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
                                  env.tcenv t_norm1 in
                              aux true t_norm2
                          | uu____19192 ->
                              let uu____19193 =
                                let uu____19194 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____19195 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____19194
                                  uu____19195 in
                              failwith uu____19193)
                     | uu____19220 ->
                         let uu____19221 =
                           let uu____19222 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____19222.FStar_Syntax_Syntax.n in
                         (match uu____19221 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____19267 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____19267 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____19299 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____19299 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____19382 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____19438 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____19438
               then encode_top_level_vals env bindings quals
               else
                 (let uu____19450 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____19544  ->
                            fun lb  ->
                              match uu____19544 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____19639 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____19639
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____19642 =
                                      let uu____19657 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____19657
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____19642 with
                                    | (tok,decl,env2) ->
                                        let uu____19703 =
                                          let uu____19716 =
                                            let uu____19727 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____19727, tok) in
                                          uu____19716 :: toks in
                                        (uu____19703, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____19450 with
                  | (toks,typs,decls,env1) ->
                      let toks1 = FStar_List.rev toks in
                      let decls1 =
                        FStar_All.pipe_right (FStar_List.rev decls)
                          FStar_List.flatten in
                      let typs1 = FStar_List.rev typs in
                      let mk_app1 curry f ftok vars =
                        match vars with
                        | [] ->
                            FStar_SMTEncoding_Util.mkFreeV
                              (f, FStar_SMTEncoding_Term.Term_sort)
                        | uu____19910 ->
                            if curry
                            then
                              (match ftok with
                               | FStar_Pervasives_Native.Some ftok1 ->
                                   mk_Apply ftok1 vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____19918 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____19918 vars)
                            else
                              (let uu____19920 =
                                 let uu____19927 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____19927) in
                               FStar_SMTEncoding_Util.mkApp uu____19920) in
                      let encode_non_rec_lbdef bindings1 typs2 toks2 env2 =
                        match (bindings1, typs2, toks2) with
                        | ({ FStar_Syntax_Syntax.lbname = uu____20009;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____20011;
                             FStar_Syntax_Syntax.lbeff = uu____20012;
                             FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                           (flid_fv,(f,ftok))::[]) ->
                            let flid =
                              (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                            let uu____20075 =
                              let uu____20082 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.tcenv uvs [e; t_norm] in
                              match uu____20082 with
                              | (tcenv',uu____20100,e_t) ->
                                  let uu____20106 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____20117 -> failwith "Impossible" in
                                  (match uu____20106 with
                                   | (e1,t_norm1) ->
                                       ((let uu___178_20133 = env2 in
                                         {
                                           bindings =
                                             (uu___178_20133.bindings);
                                           depth = (uu___178_20133.depth);
                                           tcenv = tcenv';
                                           warn = (uu___178_20133.warn);
                                           cache = (uu___178_20133.cache);
                                           nolabels =
                                             (uu___178_20133.nolabels);
                                           use_zfuel_name =
                                             (uu___178_20133.use_zfuel_name);
                                           encode_non_total_function_typ =
                                             (uu___178_20133.encode_non_total_function_typ);
                                           current_module_name =
                                             (uu___178_20133.current_module_name)
                                         }), e1, t_norm1)) in
                            (match uu____20075 with
                             | (env',e1,t_norm1) ->
                                 let uu____20143 =
                                   destruct_bound_function flid t_norm1 e1 in
                                 (match uu____20143 with
                                  | ((binders,body,uu____20164,uu____20165),curry)
                                      ->
                                      ((let uu____20176 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding") in
                                        if uu____20176
                                        then
                                          let uu____20177 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders in
                                          let uu____20178 =
                                            FStar_Syntax_Print.term_to_string
                                              body in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____20177 uu____20178
                                        else ());
                                       (let uu____20180 =
                                          encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env' in
                                        match uu____20180 with
                                        | (vars,guards,env'1,binder_decls,uu____20207)
                                            ->
                                            let body1 =
                                              let uu____20221 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.tcenv t_norm1 in
                                              if uu____20221
                                              then
                                                FStar_TypeChecker_Util.reify_body
                                                  env'1.tcenv body
                                              else body in
                                            let app =
                                              mk_app1 curry f ftok vars in
                                            let uu____20224 =
                                              let uu____20233 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic) in
                                              if uu____20233
                                              then
                                                let uu____20244 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app in
                                                let uu____20245 =
                                                  encode_formula body1 env'1 in
                                                (uu____20244, uu____20245)
                                              else
                                                (let uu____20255 =
                                                   encode_term body1 env'1 in
                                                 (app, uu____20255)) in
                                            (match uu____20224 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____20278 =
                                                     let uu____20285 =
                                                       let uu____20286 =
                                                         let uu____20297 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2) in
                                                         ([[app1]], vars,
                                                           uu____20297) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____20286 in
                                                     let uu____20308 =
                                                       let uu____20311 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str in
                                                       FStar_Pervasives_Native.Some
                                                         uu____20311 in
                                                     (uu____20285,
                                                       uu____20308,
                                                       (Prims.strcat
                                                          "equation_" f)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____20278 in
                                                 let uu____20314 =
                                                   let uu____20317 =
                                                     let uu____20320 =
                                                       let uu____20323 =
                                                         let uu____20326 =
                                                           primitive_type_axioms
                                                             env2.tcenv flid
                                                             f app1 in
                                                         FStar_List.append
                                                           [eqn] uu____20326 in
                                                       FStar_List.append
                                                         decls2 uu____20323 in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____20320 in
                                                   FStar_List.append decls1
                                                     uu____20317 in
                                                 (uu____20314, env2))))))
                        | uu____20331 -> failwith "Impossible" in
                      let encode_rec_lbdefs bindings1 typs2 toks2 env2 =
                        let fuel =
                          let uu____20416 = varops.fresh "fuel" in
                          (uu____20416, FStar_SMTEncoding_Term.Fuel_sort) in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                        let env0 = env2 in
                        let uu____20419 =
                          FStar_All.pipe_right toks2
                            (FStar_List.fold_left
                               (fun uu____20507  ->
                                  fun uu____20508  ->
                                    match (uu____20507, uu____20508) with
                                    | ((gtoks,env3),(flid_fv,(f,ftok))) ->
                                        let flid =
                                          (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                        let g =
                                          let uu____20656 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented" in
                                          varops.new_fvar uu____20656 in
                                        let gtok =
                                          let uu____20658 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token" in
                                          varops.new_fvar uu____20658 in
                                        let env4 =
                                          let uu____20660 =
                                            let uu____20663 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm]) in
                                            FStar_All.pipe_left
                                              (fun _0_44  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_44) uu____20663 in
                                          push_free_var env3 flid gtok
                                            uu____20660 in
                                        (((flid, f, ftok, g, gtok) :: gtoks),
                                          env4)) ([], env2)) in
                        match uu____20419 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks in
                            let encode_one_binding env01 uu____20819 t_norm
                              uu____20821 =
                              match (uu____20819, uu____20821) with
                              | ((flid,f,ftok,g,gtok),{
                                                        FStar_Syntax_Syntax.lbname
                                                          = lbn;
                                                        FStar_Syntax_Syntax.lbunivs
                                                          = uvs;
                                                        FStar_Syntax_Syntax.lbtyp
                                                          = uu____20865;
                                                        FStar_Syntax_Syntax.lbeff
                                                          = uu____20866;
                                                        FStar_Syntax_Syntax.lbdef
                                                          = e;_})
                                  ->
                                  let uu____20894 =
                                    let uu____20901 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.tcenv uvs [e; t_norm] in
                                    match uu____20901 with
                                    | (tcenv',uu____20923,e_t) ->
                                        let uu____20929 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____20940 ->
                                              failwith "Impossible" in
                                        (match uu____20929 with
                                         | (e1,t_norm1) ->
                                             ((let uu___179_20956 = env3 in
                                               {
                                                 bindings =
                                                   (uu___179_20956.bindings);
                                                 depth =
                                                   (uu___179_20956.depth);
                                                 tcenv = tcenv';
                                                 warn = (uu___179_20956.warn);
                                                 cache =
                                                   (uu___179_20956.cache);
                                                 nolabels =
                                                   (uu___179_20956.nolabels);
                                                 use_zfuel_name =
                                                   (uu___179_20956.use_zfuel_name);
                                                 encode_non_total_function_typ
                                                   =
                                                   (uu___179_20956.encode_non_total_function_typ);
                                                 current_module_name =
                                                   (uu___179_20956.current_module_name)
                                               }), e1, t_norm1)) in
                                  (match uu____20894 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____20971 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding") in
                                         if uu____20971
                                         then
                                           let uu____20972 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn in
                                           let uu____20973 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1 in
                                           let uu____20974 =
                                             FStar_Syntax_Print.term_to_string
                                               e1 in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____20972 uu____20973
                                             uu____20974
                                         else ());
                                        (let uu____20976 =
                                           destruct_bound_function flid
                                             t_norm1 e1 in
                                         match uu____20976 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____21013 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding") in
                                               if uu____21013
                                               then
                                                 let uu____21014 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders in
                                                 let uu____21015 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body in
                                                 let uu____21016 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals in
                                                 let uu____21017 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____21014 uu____21015
                                                   uu____21016 uu____21017
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____21021 =
                                                 encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env' in
                                               match uu____21021 with
                                               | (vars,guards,env'1,binder_decls,uu____21052)
                                                   ->
                                                   let decl_g =
                                                     let uu____21066 =
                                                       let uu____21077 =
                                                         let uu____21080 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____21080 in
                                                       (g, uu____21077,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name")) in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____21066 in
                                                   let env02 =
                                                     push_zfuel_name env01
                                                       flid g in
                                                   let decl_g_tok =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (gtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Token for fuel-instrumented partial applications")) in
                                                   let vars_tm =
                                                     FStar_List.map
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                       vars in
                                                   let app =
                                                     let uu____21105 =
                                                       let uu____21112 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars in
                                                       (f, uu____21112) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21105 in
                                                   let gsapp =
                                                     let uu____21122 =
                                                       let uu____21129 =
                                                         let uu____21132 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm]) in
                                                         uu____21132 ::
                                                           vars_tm in
                                                       (g, uu____21129) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21122 in
                                                   let gmax =
                                                     let uu____21138 =
                                                       let uu____21145 =
                                                         let uu____21148 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", []) in
                                                         uu____21148 ::
                                                           vars_tm in
                                                       (g, uu____21145) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21138 in
                                                   let body1 =
                                                     let uu____21154 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.tcenv t_norm1 in
                                                     if uu____21154
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.tcenv body
                                                     else body in
                                                   let uu____21156 =
                                                     encode_term body1 env'1 in
                                                   (match uu____21156 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____21174 =
                                                            let uu____21181 =
                                                              let uu____21182
                                                                =
                                                                let uu____21197
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm) in
                                                                ([[gsapp]],
                                                                  (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int
                                                                    "0")),
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____21197) in
                                                              FStar_SMTEncoding_Util.mkForall'
                                                                uu____21182 in
                                                            let uu____21218 =
                                                              let uu____21221
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  flid.FStar_Ident.str in
                                                              FStar_Pervasives_Native.Some
                                                                uu____21221 in
                                                            (uu____21181,
                                                              uu____21218,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21174 in
                                                        let eqn_f =
                                                          let uu____21225 =
                                                            let uu____21232 =
                                                              let uu____21233
                                                                =
                                                                let uu____21244
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____21244) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21233 in
                                                            (uu____21232,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21225 in
                                                        let eqn_g' =
                                                          let uu____21258 =
                                                            let uu____21265 =
                                                              let uu____21266
                                                                =
                                                                let uu____21277
                                                                  =
                                                                  let uu____21278
                                                                    =
                                                                    let uu____21283
                                                                    =
                                                                    let uu____21284
                                                                    =
                                                                    let uu____21291
                                                                    =
                                                                    let uu____21294
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____21294
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____21291) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____21284 in
                                                                    (gsapp,
                                                                    uu____21283) in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____21278 in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____21277) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21266 in
                                                            (uu____21265,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21258 in
                                                        let uu____21317 =
                                                          let uu____21326 =
                                                            encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02 in
                                                          match uu____21326
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____21355)
                                                              ->
                                                              let vars_tm1 =
                                                                FStar_List.map
                                                                  FStar_SMTEncoding_Util.mkFreeV
                                                                  vars1 in
                                                              let gapp =
                                                                FStar_SMTEncoding_Util.mkApp
                                                                  (g,
                                                                    (fuel_tm
                                                                    ::
                                                                    vars_tm1)) in
                                                              let tok_corr =
                                                                let tok_app =
                                                                  let uu____21380
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                  mk_Apply
                                                                    uu____21380
                                                                    (fuel ::
                                                                    vars1) in
                                                                let uu____21385
                                                                  =
                                                                  let uu____21392
                                                                    =
                                                                    let uu____21393
                                                                    =
                                                                    let uu____21404
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21404) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21393 in
                                                                  (uu____21392,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____21385 in
                                                              let uu____21425
                                                                =
                                                                let uu____21432
                                                                  =
                                                                  encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp in
                                                                match uu____21432
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____21445
                                                                    =
                                                                    let uu____21448
                                                                    =
                                                                    let uu____21449
                                                                    =
                                                                    let uu____21456
                                                                    =
                                                                    let uu____21457
                                                                    =
                                                                    let uu____21468
                                                                    =
                                                                    let uu____21469
                                                                    =
                                                                    let uu____21474
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____21474,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____21469 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21468) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21457 in
                                                                    (uu____21456,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____21449 in
                                                                    [uu____21448] in
                                                                    (d3,
                                                                    uu____21445) in
                                                              (match uu____21425
                                                               with
                                                               | (aux_decls,typing_corr)
                                                                   ->
                                                                   ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                        (match uu____21317
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
                                                               env02)))))))) in
                            let uu____21539 =
                              let uu____21552 =
                                FStar_List.zip3 gtoks1 typs2 bindings1 in
                              FStar_List.fold_left
                                (fun uu____21631  ->
                                   fun uu____21632  ->
                                     match (uu____21631, uu____21632) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____21787 =
                                           encode_one_binding env01 gtok ty
                                             lb in
                                         (match uu____21787 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____21552 in
                            (match uu____21539 with
                             | (decls2,eqns,env01) ->
                                 let uu____21860 =
                                   let isDeclFun uu___145_21872 =
                                     match uu___145_21872 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____21873 -> true
                                     | uu____21884 -> false in
                                   let uu____21885 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten in
                                   FStar_All.pipe_right uu____21885
                                     (FStar_List.partition isDeclFun) in
                                 (match uu____21860 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01))) in
                      let uu____21925 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___146_21929  ->
                                 match uu___146_21929 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____21930 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____21936 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____21936))) in
                      if uu____21925
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
                   let uu____21988 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____21988
                     (FStar_String.concat " and ") in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.strcat "let rec unencodeable: Skipping: " msg) in
                 ([decl], env))
let rec encode_sigelt:
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____22037 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____22037 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str in
      let uu____22041 = encode_sigelt' env se in
      match uu____22041 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____22057 =
                  let uu____22058 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____22058 in
                [uu____22057]
            | uu____22059 ->
                let uu____22060 =
                  let uu____22063 =
                    let uu____22064 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____22064 in
                  uu____22063 :: g in
                let uu____22065 =
                  let uu____22068 =
                    let uu____22069 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____22069 in
                  [uu____22068] in
                FStar_List.append uu____22060 uu____22065 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____22082 =
          let uu____22083 = FStar_Syntax_Subst.compress t in
          uu____22083.FStar_Syntax_Syntax.n in
        match uu____22082 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22087)) -> s = "opaque_to_smt"
        | uu____22088 -> false in
      let is_uninterpreted_by_smt t =
        let uu____22093 =
          let uu____22094 = FStar_Syntax_Subst.compress t in
          uu____22094.FStar_Syntax_Syntax.n in
        match uu____22093 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22098)) -> s = "uninterpreted_by_smt"
        | uu____22099 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____22104 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____22109 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____22112 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____22115 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____22130 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____22134 =
            let uu____22135 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____22135 Prims.op_Negation in
          if uu____22134
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____22161 ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_abs
                        ((ed.FStar_Syntax_Syntax.binders), tm,
                          (FStar_Pervasives_Native.Some
                             (FStar_Syntax_Util.mk_residual_comp
                                FStar_Parser_Const.effect_Tot_lid
                                FStar_Pervasives_Native.None
                                [FStar_Syntax_Syntax.TOTAL]))))
                     FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____22181 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____22181 with
               | (aname,atok,env2) ->
                   let uu____22197 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____22197 with
                    | (formals,uu____22215) ->
                        let uu____22228 =
                          let uu____22233 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____22233 env2 in
                        (match uu____22228 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____22245 =
                                 let uu____22246 =
                                   let uu____22257 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____22273  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____22257,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____22246 in
                               [uu____22245;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))] in
                             let uu____22286 =
                               let aux uu____22338 uu____22339 =
                                 match (uu____22338, uu____22339) with
                                 | ((bv,uu____22391),(env3,acc_sorts,acc)) ->
                                     let uu____22429 = gen_term_var env3 bv in
                                     (match uu____22429 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____22286 with
                              | (uu____22501,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____22524 =
                                      let uu____22531 =
                                        let uu____22532 =
                                          let uu____22543 =
                                            let uu____22544 =
                                              let uu____22549 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____22549) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____22544 in
                                          ([[app]], xs_sorts, uu____22543) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22532 in
                                      (uu____22531,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22524 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____22569 =
                                      let uu____22576 =
                                        let uu____22577 =
                                          let uu____22588 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____22588) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22577 in
                                      (uu____22576,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22569 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____22607 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____22607 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22635,uu____22636)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____22637 = new_term_constant_and_tok_from_lid env lid in
          (match uu____22637 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22654,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____22660 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___147_22664  ->
                      match uu___147_22664 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____22665 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____22670 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____22671 -> false)) in
            Prims.op_Negation uu____22660 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____22680 =
               let uu____22687 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt) in
               encode_top_level_val uu____22687 env fv t quals in
             match uu____22680 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____22702 =
                   let uu____22705 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____22705 in
                 (uu____22702, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____22713 = FStar_Syntax_Subst.open_univ_vars us f in
          (match uu____22713 with
           | (uu____22722,f1) ->
               let uu____22724 = encode_formula f1 env in
               (match uu____22724 with
                | (f2,decls) ->
                    let g =
                      let uu____22738 =
                        let uu____22739 =
                          let uu____22746 =
                            let uu____22749 =
                              let uu____22750 =
                                FStar_Syntax_Print.lid_to_string l in
                              FStar_Util.format1 "Assumption: %s" uu____22750 in
                            FStar_Pervasives_Native.Some uu____22749 in
                          let uu____22751 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str) in
                          (f2, uu____22746, uu____22751) in
                        FStar_SMTEncoding_Util.mkAssume uu____22739 in
                      [uu____22738] in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____22757) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs in
          let uu____22769 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____22787 =
                       let uu____22790 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____22790.FStar_Syntax_Syntax.fv_name in
                     uu____22787.FStar_Syntax_Syntax.v in
                   let uu____22791 =
                     let uu____22792 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____22792 in
                   if uu____22791
                   then
                     let val_decl =
                       let uu___182_22820 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___182_22820.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___182_22820.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___182_22820.FStar_Syntax_Syntax.sigattrs)
                       } in
                     let uu____22825 = encode_sigelt' env1 val_decl in
                     match uu____22825 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
          (match uu____22769 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____22853,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____22855;
                          FStar_Syntax_Syntax.lbtyp = uu____22856;
                          FStar_Syntax_Syntax.lbeff = uu____22857;
                          FStar_Syntax_Syntax.lbdef = uu____22858;_}::[]),uu____22859)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____22878 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____22878 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____22907 =
                   let uu____22910 =
                     let uu____22911 =
                       let uu____22918 =
                         let uu____22919 =
                           let uu____22930 =
                             let uu____22931 =
                               let uu____22936 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x]) in
                               (valid_b2t_x, uu____22936) in
                             FStar_SMTEncoding_Util.mkEq uu____22931 in
                           ([[b2t_x]], [xx], uu____22930) in
                         FStar_SMTEncoding_Util.mkForall uu____22919 in
                       (uu____22918,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____22911 in
                   [uu____22910] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____22907 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____22969,uu____22970) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___148_22979  ->
                  match uu___148_22979 with
                  | FStar_Syntax_Syntax.Discriminator uu____22980 -> true
                  | uu____22981 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____22984,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____22995 =
                     let uu____22996 = FStar_List.hd l.FStar_Ident.ns in
                     uu____22996.FStar_Ident.idText in
                   uu____22995 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___149_23000  ->
                     match uu___149_23000 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____23001 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____23005) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___150_23022  ->
                  match uu___150_23022 with
                  | FStar_Syntax_Syntax.Projector uu____23023 -> true
                  | uu____23028 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____23031 = try_lookup_free_var env l in
          (match uu____23031 with
           | FStar_Pervasives_Native.Some uu____23038 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___183_23042 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___183_23042.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___183_23042.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___183_23042.FStar_Syntax_Syntax.sigattrs)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____23049) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____23067) ->
          let uu____23076 = encode_sigelts env ses in
          (match uu____23076 with
           | (g,env1) ->
               let uu____23093 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___151_23116  ->
                         match uu___151_23116 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____23117;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____23118;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____23119;_}
                             -> false
                         | uu____23122 -> true)) in
               (match uu____23093 with
                | (g',inversions) ->
                    let uu____23137 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___152_23158  ->
                              match uu___152_23158 with
                              | FStar_SMTEncoding_Term.DeclFun uu____23159 ->
                                  true
                              | uu____23170 -> false)) in
                    (match uu____23137 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____23188,tps,k,uu____23191,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___153_23208  ->
                    match uu___153_23208 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____23209 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____23218 = c in
              match uu____23218 with
              | (name,args,uu____23223,uu____23224,uu____23225) ->
                  let uu____23230 =
                    let uu____23231 =
                      let uu____23242 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____23259  ->
                                match uu____23259 with
                                | (uu____23266,sort,uu____23268) -> sort)) in
                      (name, uu____23242, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____23231 in
                  [uu____23230]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____23295 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____23301 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____23301 FStar_Option.isNone)) in
            if uu____23295
            then []
            else
              (let uu____23333 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____23333 with
               | (xxsym,xx) ->
                   let uu____23342 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____23381  ->
                             fun l  ->
                               match uu____23381 with
                               | (out,decls) ->
                                   let uu____23401 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____23401 with
                                    | (uu____23412,data_t) ->
                                        let uu____23414 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____23414 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____23460 =
                                                 let uu____23461 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____23461.FStar_Syntax_Syntax.n in
                                               match uu____23460 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____23472,indices) ->
                                                   indices
                                               | uu____23494 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____23518  ->
                                                         match uu____23518
                                                         with
                                                         | (x,uu____23524) ->
                                                             let uu____23525
                                                               =
                                                               let uu____23526
                                                                 =
                                                                 let uu____23533
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____23533,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____23526 in
                                                             push_term_var
                                                               env1 x
                                                               uu____23525)
                                                    env) in
                                             let uu____23536 =
                                               encode_args indices env1 in
                                             (match uu____23536 with
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
                                                      let uu____23562 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____23578
                                                                 =
                                                                 let uu____23583
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____23583,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____23578)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____23562
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____23586 =
                                                      let uu____23587 =
                                                        let uu____23592 =
                                                          let uu____23593 =
                                                            let uu____23598 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____23598,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____23593 in
                                                        (out, uu____23592) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____23587 in
                                                    (uu____23586,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____23342 with
                    | (data_ax,decls) ->
                        let uu____23611 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____23611 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____23622 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____23622 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____23626 =
                                 let uu____23633 =
                                   let uu____23634 =
                                     let uu____23645 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____23660 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____23645,
                                       uu____23660) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____23634 in
                                 let uu____23675 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____23633,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____23675) in
                               FStar_SMTEncoding_Util.mkAssume uu____23626 in
                             FStar_List.append decls [fuel_guarded_inversion]))) in
          let uu____23678 =
            let uu____23691 =
              let uu____23692 = FStar_Syntax_Subst.compress k in
              uu____23692.FStar_Syntax_Syntax.n in
            match uu____23691 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____23737 -> (tps, k) in
          (match uu____23678 with
           | (formals,res) ->
               let uu____23760 = FStar_Syntax_Subst.open_term formals res in
               (match uu____23760 with
                | (formals1,res1) ->
                    let uu____23771 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env in
                    (match uu____23771 with
                     | (vars,guards,env',binder_decls,uu____23796) ->
                         let uu____23809 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____23809 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____23828 =
                                  let uu____23835 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____23835) in
                                FStar_SMTEncoding_Util.mkApp uu____23828 in
                              let uu____23844 =
                                let tname_decl =
                                  let uu____23854 =
                                    let uu____23855 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____23887  ->
                                              match uu____23887 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____23900 = varops.next_id () in
                                    (tname, uu____23855,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____23900, false) in
                                  constructor_or_logic_type_decl uu____23854 in
                                let uu____23909 =
                                  match vars with
                                  | [] ->
                                      let uu____23922 =
                                        let uu____23923 =
                                          let uu____23926 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_45  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_45) uu____23926 in
                                        push_free_var env1 t tname
                                          uu____23923 in
                                      ([], uu____23922)
                                  | uu____23933 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token")) in
                                      let ttok_fresh =
                                        let uu____23942 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____23942 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____23956 =
                                          let uu____23963 =
                                            let uu____23964 =
                                              let uu____23979 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____23979) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____23964 in
                                          (uu____23963,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____23956 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____23909 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____23844 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____24019 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp in
                                     match uu____24019 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____24037 =
                                               let uu____24038 =
                                                 let uu____24045 =
                                                   let uu____24046 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____24046 in
                                                 (uu____24045,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24038 in
                                             [uu____24037]
                                           else [] in
                                         let uu____24050 =
                                           let uu____24053 =
                                             let uu____24056 =
                                               let uu____24057 =
                                                 let uu____24064 =
                                                   let uu____24065 =
                                                     let uu____24076 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____24076) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____24065 in
                                                 (uu____24064,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24057 in
                                             [uu____24056] in
                                           FStar_List.append karr uu____24053 in
                                         FStar_List.append decls1 uu____24050 in
                                   let aux =
                                     let uu____24092 =
                                       let uu____24095 =
                                         inversion_axioms tapp vars in
                                       let uu____24098 =
                                         let uu____24101 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____24101] in
                                       FStar_List.append uu____24095
                                         uu____24098 in
                                     FStar_List.append kindingAx uu____24092 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24108,uu____24109,uu____24110,uu____24111,uu____24112)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24120,t,uu____24122,n_tps,uu____24124) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____24132 = new_term_constant_and_tok_from_lid env d in
          (match uu____24132 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____24149 = FStar_Syntax_Util.arrow_formals t in
               (match uu____24149 with
                | (formals,t_res) ->
                    let uu____24184 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____24184 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____24198 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1 in
                         (match uu____24198 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____24268 =
                                            mk_term_projector_name d x in
                                          (uu____24268,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____24270 =
                                  let uu____24289 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____24289, true) in
                                FStar_All.pipe_right uu____24270
                                  FStar_SMTEncoding_Term.constructor_to_decl in
                              let app = mk_Apply ddtok_tm vars in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let xvars =
                                FStar_List.map FStar_SMTEncoding_Util.mkFreeV
                                  vars in
                              let dapp =
                                FStar_SMTEncoding_Util.mkApp
                                  (ddconstrsym, xvars) in
                              let uu____24328 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm in
                              (match uu____24328 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____24340::uu____24341 ->
                                         let ff =
                                           ("ty",
                                             FStar_SMTEncoding_Term.Term_sort) in
                                         let f =
                                           FStar_SMTEncoding_Util.mkFreeV ff in
                                         let vtok_app_l =
                                           mk_Apply ddtok_tm [ff] in
                                         let vtok_app_r =
                                           mk_Apply f
                                             [(ddtok,
                                                FStar_SMTEncoding_Term.Term_sort)] in
                                         let uu____24386 =
                                           let uu____24397 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____24397) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____24386
                                     | uu____24422 -> tok_typing in
                                   let uu____24431 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1 in
                                   (match uu____24431 with
                                    | (vars',guards',env'',decls_formals,uu____24456)
                                        ->
                                        let uu____24469 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1) in
                                          encode_term_pred
                                            (FStar_Pervasives_Native.Some
                                               fuel_tm) t_res env'' dapp1 in
                                        (match uu____24469 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____24500 ->
                                                   let uu____24507 =
                                                     let uu____24508 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____24508 in
                                                   [uu____24507] in
                                             let encode_elim uu____24518 =
                                               let uu____24519 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____24519 with
                                               | (head1,args) ->
                                                   let uu____24562 =
                                                     let uu____24563 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____24563.FStar_Syntax_Syntax.n in
                                                   (match uu____24562 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____24573;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____24574;_},uu____24575)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____24581 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____24581
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
                                                                 | uu____24624
                                                                    ->
                                                                    let uu____24625
                                                                    =
                                                                    let uu____24626
                                                                    =
                                                                    let uu____24631
                                                                    =
                                                                    let uu____24632
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24632 in
                                                                    (uu____24631,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____24626 in
                                                                    FStar_Exn.raise
                                                                    uu____24625 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____24648
                                                                    =
                                                                    let uu____24649
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24649 in
                                                                    if
                                                                    uu____24648
                                                                    then
                                                                    let uu____24662
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____24662]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____24664
                                                               =
                                                               let uu____24677
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____24727
                                                                     ->
                                                                    fun
                                                                    uu____24728
                                                                     ->
                                                                    match 
                                                                    (uu____24727,
                                                                    uu____24728)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____24823
                                                                    =
                                                                    let uu____24830
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____24830 in
                                                                    (match uu____24823
                                                                    with
                                                                    | 
                                                                    (uu____24843,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____24851
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____24851
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____24853
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____24853
                                                                    ::
                                                                    eqns_or_guards) in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    (Prims.parse_int
                                                                    "1")))))
                                                                 (env', [],
                                                                   [],
                                                                   (Prims.parse_int
                                                                    "0"))
                                                                 uu____24677 in
                                                             (match uu____24664
                                                              with
                                                              | (uu____24868,arg_vars,elim_eqns_or_guards,uu____24871)
                                                                  ->
                                                                  let arg_vars1
                                                                    =
                                                                    FStar_List.rev
                                                                    arg_vars in
                                                                  let ty =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (encoded_head,
                                                                    arg_vars1) in
                                                                  let xvars1
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars in
                                                                  let dapp1 =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (ddconstrsym,
                                                                    xvars1) in
                                                                  let ty_pred
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                                    (FStar_Pervasives_Native.Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty in
                                                                  let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1 in
                                                                  let typing_inversion
                                                                    =
                                                                    let uu____24901
                                                                    =
                                                                    let uu____24908
                                                                    =
                                                                    let uu____24909
                                                                    =
                                                                    let uu____24920
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____24931
                                                                    =
                                                                    let uu____24932
                                                                    =
                                                                    let uu____24937
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____24937) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24932 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24920,
                                                                    uu____24931) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24909 in
                                                                    (uu____24908,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24901 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____24960
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____24960,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____24962
                                                                    =
                                                                    let uu____24969
                                                                    =
                                                                    let uu____24970
                                                                    =
                                                                    let uu____24981
                                                                    =
                                                                    let uu____24986
                                                                    =
                                                                    let uu____24989
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____24989] in
                                                                    [uu____24986] in
                                                                    let uu____24994
                                                                    =
                                                                    let uu____24995
                                                                    =
                                                                    let uu____25000
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25001
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25000,
                                                                    uu____25001) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24995 in
                                                                    (uu____24981,
                                                                    [x],
                                                                    uu____24994) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24970 in
                                                                    let uu____25020
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____24969,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25020) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24962
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25027
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
                                                                    (let uu____25055
                                                                    =
                                                                    let uu____25056
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25056
                                                                    dapp1 in
                                                                    [uu____25055]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25027
                                                                    FStar_List.flatten in
                                                                    let uu____25063
                                                                    =
                                                                    let uu____25070
                                                                    =
                                                                    let uu____25071
                                                                    =
                                                                    let uu____25082
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25093
                                                                    =
                                                                    let uu____25094
                                                                    =
                                                                    let uu____25099
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25099) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25094 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25082,
                                                                    uu____25093) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25071 in
                                                                    (uu____25070,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25063) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____25120 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____25120
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
                                                                 | uu____25163
                                                                    ->
                                                                    let uu____25164
                                                                    =
                                                                    let uu____25165
                                                                    =
                                                                    let uu____25170
                                                                    =
                                                                    let uu____25171
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____25171 in
                                                                    (uu____25170,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____25165 in
                                                                    FStar_Exn.raise
                                                                    uu____25164 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____25187
                                                                    =
                                                                    let uu____25188
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____25188 in
                                                                    if
                                                                    uu____25187
                                                                    then
                                                                    let uu____25201
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____25201]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____25203
                                                               =
                                                               let uu____25216
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____25266
                                                                     ->
                                                                    fun
                                                                    uu____25267
                                                                     ->
                                                                    match 
                                                                    (uu____25266,
                                                                    uu____25267)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25362
                                                                    =
                                                                    let uu____25369
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25369 in
                                                                    (match uu____25362
                                                                    with
                                                                    | 
                                                                    (uu____25382,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25390
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____25390
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25392
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____25392
                                                                    ::
                                                                    eqns_or_guards) in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    (Prims.parse_int
                                                                    "1")))))
                                                                 (env', [],
                                                                   [],
                                                                   (Prims.parse_int
                                                                    "0"))
                                                                 uu____25216 in
                                                             (match uu____25203
                                                              with
                                                              | (uu____25407,arg_vars,elim_eqns_or_guards,uu____25410)
                                                                  ->
                                                                  let arg_vars1
                                                                    =
                                                                    FStar_List.rev
                                                                    arg_vars in
                                                                  let ty =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (encoded_head,
                                                                    arg_vars1) in
                                                                  let xvars1
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars in
                                                                  let dapp1 =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (ddconstrsym,
                                                                    xvars1) in
                                                                  let ty_pred
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                                    (FStar_Pervasives_Native.Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty in
                                                                  let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1 in
                                                                  let typing_inversion
                                                                    =
                                                                    let uu____25440
                                                                    =
                                                                    let uu____25447
                                                                    =
                                                                    let uu____25448
                                                                    =
                                                                    let uu____25459
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25470
                                                                    =
                                                                    let uu____25471
                                                                    =
                                                                    let uu____25476
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____25476) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25471 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25459,
                                                                    uu____25470) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25448 in
                                                                    (uu____25447,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25440 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25499
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____25499,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____25501
                                                                    =
                                                                    let uu____25508
                                                                    =
                                                                    let uu____25509
                                                                    =
                                                                    let uu____25520
                                                                    =
                                                                    let uu____25525
                                                                    =
                                                                    let uu____25528
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____25528] in
                                                                    [uu____25525] in
                                                                    let uu____25533
                                                                    =
                                                                    let uu____25534
                                                                    =
                                                                    let uu____25539
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25540
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25539,
                                                                    uu____25540) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25534 in
                                                                    (uu____25520,
                                                                    [x],
                                                                    uu____25533) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25509 in
                                                                    let uu____25559
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____25508,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25559) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25501
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25566
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
                                                                    (let uu____25594
                                                                    =
                                                                    let uu____25595
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25595
                                                                    dapp1 in
                                                                    [uu____25594]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25566
                                                                    FStar_List.flatten in
                                                                    let uu____25602
                                                                    =
                                                                    let uu____25609
                                                                    =
                                                                    let uu____25610
                                                                    =
                                                                    let uu____25621
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25632
                                                                    =
                                                                    let uu____25633
                                                                    =
                                                                    let uu____25638
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25638) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25633 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25621,
                                                                    uu____25632) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25610 in
                                                                    (uu____25609,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25602) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____25657 ->
                                                        ((let uu____25659 =
                                                            let uu____25660 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____25661 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____25660
                                                              uu____25661 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____25659);
                                                         ([], []))) in
                                             let uu____25666 = encode_elim () in
                                             (match uu____25666 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____25686 =
                                                      let uu____25689 =
                                                        let uu____25692 =
                                                          let uu____25695 =
                                                            let uu____25698 =
                                                              let uu____25699
                                                                =
                                                                let uu____25710
                                                                  =
                                                                  let uu____25713
                                                                    =
                                                                    let uu____25714
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____25714 in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____25713 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____25710) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____25699 in
                                                            [uu____25698] in
                                                          let uu____25719 =
                                                            let uu____25722 =
                                                              let uu____25725
                                                                =
                                                                let uu____25728
                                                                  =
                                                                  let uu____25731
                                                                    =
                                                                    let uu____25734
                                                                    =
                                                                    let uu____25737
                                                                    =
                                                                    let uu____25738
                                                                    =
                                                                    let uu____25745
                                                                    =
                                                                    let uu____25746
                                                                    =
                                                                    let uu____25757
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____25757) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25746 in
                                                                    (uu____25745,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25738 in
                                                                    let uu____25770
                                                                    =
                                                                    let uu____25773
                                                                    =
                                                                    let uu____25774
                                                                    =
                                                                    let uu____25781
                                                                    =
                                                                    let uu____25782
                                                                    =
                                                                    let uu____25793
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____25804
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____25793,
                                                                    uu____25804) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25782 in
                                                                    (uu____25781,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25774 in
                                                                    [uu____25773] in
                                                                    uu____25737
                                                                    ::
                                                                    uu____25770 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____25734 in
                                                                  FStar_List.append
                                                                    uu____25731
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____25728 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____25725 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____25722 in
                                                          FStar_List.append
                                                            uu____25695
                                                            uu____25719 in
                                                        FStar_List.append
                                                          decls3 uu____25692 in
                                                      FStar_List.append
                                                        decls2 uu____25689 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____25686 in
                                                  ((FStar_List.append
                                                      datacons g), env1)))))))))
and encode_sigelts:
  env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,env_t)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____25850  ->
              fun se  ->
                match uu____25850 with
                | (g,env1) ->
                    let uu____25870 = encode_sigelt env1 se in
                    (match uu____25870 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____25929 =
        match uu____25929 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____25961 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.Primops;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort in
                 ((let uu____25967 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____25967
                   then
                     let uu____25968 = FStar_Syntax_Print.bv_to_string x in
                     let uu____25969 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____25970 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____25968 uu____25969 uu____25970
                   else ());
                  (let uu____25972 = encode_term t1 env1 in
                   match uu____25972 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____25988 =
                         let uu____25995 =
                           let uu____25996 =
                             let uu____25997 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____25997
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____25996 in
                         new_term_constant_from_string env1 x uu____25995 in
                       (match uu____25988 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t in
                            let caption =
                              let uu____26013 = FStar_Options.log_queries () in
                              if uu____26013
                              then
                                let uu____26016 =
                                  let uu____26017 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____26018 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____26019 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____26017 uu____26018 uu____26019 in
                                FStar_Pervasives_Native.Some uu____26016
                              else FStar_Pervasives_Native.None in
                            let ax =
                              let a_name = Prims.strcat "binder_" xxsym in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name) in
                            let g =
                              FStar_List.append
                                [FStar_SMTEncoding_Term.DeclFun
                                   (xxsym, [],
                                     FStar_SMTEncoding_Term.Term_sort,
                                     caption)]
                                (FStar_List.append decls' [ax]) in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____26035,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None in
                 let uu____26049 = encode_free_var false env1 fv t t_norm [] in
                 (match uu____26049 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____26072,se,uu____26074) ->
                 let uu____26079 = encode_sigelt env1 se in
                 (match uu____26079 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____26096,se) ->
                 let uu____26102 = encode_sigelt env1 se in
                 (match uu____26102 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____26119 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____26119 with | (uu____26142,decls,env1) -> (decls, env1)
let encode_labels:
  'Auu____26157 'Auu____26158 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____26158,'Auu____26157)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____26226  ->
              match uu____26226 with
              | (l,uu____26238,uu____26239) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None))) in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____26285  ->
              match uu____26285 with
              | (l,uu____26299,uu____26300) ->
                  let uu____26309 =
                    FStar_All.pipe_left
                      (fun _0_46  -> FStar_SMTEncoding_Term.Echo _0_46)
                      (FStar_Pervasives_Native.fst l) in
                  let uu____26310 =
                    let uu____26313 =
                      let uu____26314 = FStar_SMTEncoding_Util.mkFreeV l in
                      FStar_SMTEncoding_Term.Eval uu____26314 in
                    [uu____26313] in
                  uu____26309 :: uu____26310)) in
    (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____26336 =
      let uu____26339 =
        let uu____26340 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____26343 =
          let uu____26344 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____26344 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____26340;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____26343
        } in
      [uu____26339] in
    FStar_ST.op_Colon_Equals last_env uu____26336
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____26403 = FStar_ST.op_Bang last_env in
      match uu____26403 with
      | [] -> failwith "No env; call init first!"
      | e::uu____26457 ->
          let uu___184_26460 = e in
          let uu____26461 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___184_26460.bindings);
            depth = (uu___184_26460.depth);
            tcenv;
            warn = (uu___184_26460.warn);
            cache = (uu___184_26460.cache);
            nolabels = (uu___184_26460.nolabels);
            use_zfuel_name = (uu___184_26460.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___184_26460.encode_non_total_function_typ);
            current_module_name = uu____26461
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____26466 = FStar_ST.op_Bang last_env in
    match uu____26466 with
    | [] -> failwith "Empty env stack"
    | uu____26519::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____26576  ->
    let uu____26577 = FStar_ST.op_Bang last_env in
    match uu____26577 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___185_26638 = hd1 in
          {
            bindings = (uu___185_26638.bindings);
            depth = (uu___185_26638.depth);
            tcenv = (uu___185_26638.tcenv);
            warn = (uu___185_26638.warn);
            cache = refs;
            nolabels = (uu___185_26638.nolabels);
            use_zfuel_name = (uu___185_26638.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___185_26638.encode_non_total_function_typ);
            current_module_name = (uu___185_26638.current_module_name)
          } in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____26692  ->
    let uu____26693 = FStar_ST.op_Bang last_env in
    match uu____26693 with
    | [] -> failwith "Popping an empty stack"
    | uu____26746::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
let init: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    init_env tcenv;
    FStar_SMTEncoding_Z3.init ();
    FStar_SMTEncoding_Z3.giveZ3 [FStar_SMTEncoding_Term.DefPrelude]
let push: Prims.string -> Prims.unit =
  fun msg  -> push_env (); varops.push (); FStar_SMTEncoding_Z3.push msg
let pop: Prims.string -> Prims.unit =
  fun msg  -> pop_env (); varops.pop (); FStar_SMTEncoding_Z3.pop msg
let open_fact_db_tags: env_t -> FStar_SMTEncoding_Term.fact_db_id Prims.list
  = fun env  -> []
let place_decl_in_fact_dbs:
  env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decl -> FStar_SMTEncoding_Term.decl
  =
  fun env  ->
    fun fact_db_ids  ->
      fun d  ->
        match (fact_db_ids, d) with
        | (uu____26844::uu____26845,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___186_26853 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___186_26853.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___186_26853.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___186_26853.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____26854 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____26871 =
        let uu____26874 =
          let uu____26875 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____26875 in
        let uu____26876 = open_fact_db_tags env in uu____26874 :: uu____26876 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____26871
let encode_top_level_facts:
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decl Prims.list,env_t)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let fact_db_ids =
        FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
          (FStar_List.collect (fact_dbs_for_lid env)) in
      let uu____26900 = encode_sigelt env se in
      match uu____26900 with
      | (g,env1) ->
          let g1 =
            FStar_All.pipe_right g
              (FStar_List.map (place_decl_in_fact_dbs env1 fact_db_ids)) in
          (g1, env1)
let encode_sig:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____26938 = FStar_Options.log_queries () in
        if uu____26938
        then
          let uu____26941 =
            let uu____26942 =
              let uu____26943 =
                let uu____26944 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____26944 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____26943 in
            FStar_SMTEncoding_Term.Caption uu____26942 in
          uu____26941 :: decls
        else decls in
      (let uu____26955 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____26955
       then
         let uu____26956 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____26956
       else ());
      (let env =
         let uu____26959 = FStar_TypeChecker_Env.current_module tcenv in
         get_env uu____26959 tcenv in
       let uu____26960 = encode_top_level_facts env se in
       match uu____26960 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____26974 = caption decls in
             FStar_SMTEncoding_Z3.giveZ3 uu____26974)))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____26988 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____26988
       then
         let uu____26989 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____26989
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____27024  ->
                 fun se  ->
                   match uu____27024 with
                   | (g,env2) ->
                       let uu____27044 = encode_top_level_facts env2 se in
                       (match uu____27044 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____27067 =
         encode_signature
           (let uu___187_27076 = env in
            {
              bindings = (uu___187_27076.bindings);
              depth = (uu___187_27076.depth);
              tcenv = (uu___187_27076.tcenv);
              warn = false;
              cache = (uu___187_27076.cache);
              nolabels = (uu___187_27076.nolabels);
              use_zfuel_name = (uu___187_27076.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___187_27076.encode_non_total_function_typ);
              current_module_name = (uu___187_27076.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____27067 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____27093 = FStar_Options.log_queries () in
             if uu____27093
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___188_27101 = env1 in
               {
                 bindings = (uu___188_27101.bindings);
                 depth = (uu___188_27101.depth);
                 tcenv = (uu___188_27101.tcenv);
                 warn = true;
                 cache = (uu___188_27101.cache);
                 nolabels = (uu___188_27101.nolabels);
                 use_zfuel_name = (uu___188_27101.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___188_27101.encode_non_total_function_typ);
                 current_module_name = (uu___188_27101.current_module_name)
               });
            (let uu____27103 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____27103
             then FStar_Util.print1 "Done encoding externals for %s\n" name
             else ());
            (let decls1 = caption decls in FStar_SMTEncoding_Z3.giveZ3 decls1)))
let encode_query:
  (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_ErrorReporting.label
                                                  Prims.list,FStar_SMTEncoding_Term.decl,
          FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple4
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____27158 =
           let uu____27159 = FStar_TypeChecker_Env.current_module tcenv in
           uu____27159.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____27158);
        (let env =
           let uu____27161 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____27161 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____27173 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____27208 = aux rest in
                 (match uu____27208 with
                  | (out,rest1) ->
                      let t =
                        let uu____27238 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____27238 with
                        | FStar_Pervasives_Native.Some uu____27243 ->
                            let uu____27244 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit in
                            FStar_Syntax_Util.refine uu____27244
                              x.FStar_Syntax_Syntax.sort
                        | uu____27245 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____27249 =
                        let uu____27252 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___189_27255 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___189_27255.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___189_27255.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____27252 :: out in
                      (uu____27249, rest1))
             | uu____27260 -> ([], bindings1) in
           let uu____27267 = aux bindings in
           match uu____27267 with
           | (closing,bindings1) ->
               let uu____27292 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____27292, bindings1) in
         match uu____27173 with
         | (q1,bindings1) ->
             let uu____27315 =
               let uu____27320 =
                 FStar_List.filter
                   (fun uu___154_27325  ->
                      match uu___154_27325 with
                      | FStar_TypeChecker_Env.Binding_sig uu____27326 ->
                          false
                      | uu____27333 -> true) bindings1 in
               encode_env_bindings env uu____27320 in
             (match uu____27315 with
              | (env_decls,env1) ->
                  ((let uu____27351 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____27351
                    then
                      let uu____27352 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____27352
                    else ());
                   (let uu____27354 = encode_formula q1 env1 in
                    match uu____27354 with
                    | (phi,qdecls) ->
                        let uu____27375 =
                          let uu____27380 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____27380 phi in
                        (match uu____27375 with
                         | (labels,phi1) ->
                             let uu____27397 = encode_labels labels in
                             (match uu____27397 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____27434 =
                                      let uu____27441 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____27442 =
                                        varops.mk_unique "@query" in
                                      (uu____27441,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____27442) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____27434 in
                                  let suffix =
                                    FStar_List.append
                                      [FStar_SMTEncoding_Term.Echo "<labels>"]
                                      (FStar_List.append label_suffix
                                         [FStar_SMTEncoding_Term.Echo
                                            "</labels>";
                                         FStar_SMTEncoding_Term.Echo "Done!"]) in
                                  (query_prelude, labels, qry, suffix)))))))