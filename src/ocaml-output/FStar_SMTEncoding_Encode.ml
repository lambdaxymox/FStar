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
      | FStar_Const.Const_range uu____4539 ->
          let uu____4540 = FStar_SMTEncoding_Term.mk_Range_const () in
          (uu____4540, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | c1 ->
          let uu____4546 =
            let uu____4547 = FStar_Syntax_Print.const_to_string c1 in
            FStar_Util.format1 "Unhandled constant: %s" uu____4547 in
          failwith uu____4546
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
        (let uu____4576 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____4576
         then
           let uu____4577 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____4577
         else ());
        (let uu____4579 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____4663  ->
                   fun b  ->
                     match uu____4663 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____4742 =
                           let x = unmangle (FStar_Pervasives_Native.fst b) in
                           let uu____4758 = gen_term_var env1 x in
                           match uu____4758 with
                           | (xxsym,xx,env') ->
                               let uu____4782 =
                                 let uu____4787 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____4787 env1 xx in
                               (match uu____4782 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____4742 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____4579 with
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
          let uu____4946 = encode_term t env in
          match uu____4946 with
          | (t1,decls) ->
              let uu____4957 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____4957, decls)
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
          let uu____4968 = encode_term t env in
          match uu____4968 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____4983 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____4983, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____4985 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____4985, decls))
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
        let uu____4991 = encode_args args_e env in
        match uu____4991 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____5010 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____5019 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____5019 in
            let binary arg_tms1 =
              let uu____5032 =
                let uu____5033 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____5033 in
              let uu____5034 =
                let uu____5035 =
                  let uu____5036 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____5036 in
                FStar_SMTEncoding_Term.unboxInt uu____5035 in
              (uu____5032, uu____5034) in
            let mk_default uu____5042 =
              let uu____5043 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____5043 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms)) in
            let mk_l op mk_args ts =
              let uu____5094 = FStar_Options.smtencoding_l_arith_native () in
              if uu____5094
              then
                let uu____5095 = let uu____5096 = mk_args ts in op uu____5096 in
                FStar_All.pipe_right uu____5095 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____5125 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____5125
              then
                let uu____5126 = binary ts in
                match uu____5126 with
                | (t1,t2) ->
                    let uu____5133 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____5133
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____5137 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____5137
                 then
                   let uu____5138 = op (binary ts) in
                   FStar_All.pipe_right uu____5138
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
            let uu____5269 =
              let uu____5278 =
                FStar_List.tryFind
                  (fun uu____5300  ->
                     match uu____5300 with
                     | (l,uu____5310) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____5278 FStar_Util.must in
            (match uu____5269 with
             | (uu____5349,op) ->
                 let uu____5359 = op arg_tms in (uu____5359, decls))
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
        let uu____5367 = FStar_List.hd args_e in
        match uu____5367 with
        | (tm_sz,uu____5375) ->
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz) in
            let sz_decls =
              let uu____5385 = FStar_Util.smap_try_find env.cache sz_key in
              match uu____5385 with
              | FStar_Pervasives_Native.Some cache_entry -> []
              | FStar_Pervasives_Native.None  ->
                  let t_decls = FStar_SMTEncoding_Term.mkBvConstructor sz in
                  ((let uu____5393 = mk_cache_entry env "" [] [] in
                    FStar_Util.smap_add env.cache sz_key uu____5393);
                   t_decls) in
            let uu____5394 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5414::(sz_arg,uu____5416)::uu____5417::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____5466 =
                    let uu____5469 = FStar_List.tail args_e in
                    FStar_List.tail uu____5469 in
                  let uu____5472 =
                    let uu____5475 = getInteger sz_arg.FStar_Syntax_Syntax.n in
                    FStar_Pervasives_Native.Some uu____5475 in
                  (uu____5466, uu____5472)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5481::(sz_arg,uu____5483)::uu____5484::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____5533 =
                    let uu____5534 = FStar_Syntax_Print.term_to_string sz_arg in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____5534 in
                  failwith uu____5533
              | uu____5543 ->
                  let uu____5550 = FStar_List.tail args_e in
                  (uu____5550, FStar_Pervasives_Native.None) in
            (match uu____5394 with
             | (arg_tms,ext_sz) ->
                 let uu____5573 = encode_args arg_tms env in
                 (match uu____5573 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____5594 -> failwith "Impossible" in
                      let unary arg_tms2 =
                        let uu____5603 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____5603 in
                      let unary_arith arg_tms2 =
                        let uu____5612 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxInt uu____5612 in
                      let binary arg_tms2 =
                        let uu____5625 =
                          let uu____5626 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5626 in
                        let uu____5627 =
                          let uu____5628 =
                            let uu____5629 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____5629 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5628 in
                        (uu____5625, uu____5627) in
                      let binary_arith arg_tms2 =
                        let uu____5644 =
                          let uu____5645 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5645 in
                        let uu____5646 =
                          let uu____5647 =
                            let uu____5648 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____5648 in
                          FStar_SMTEncoding_Term.unboxInt uu____5647 in
                        (uu____5644, uu____5646) in
                      let mk_bv op mk_args resBox ts =
                        let uu____5697 =
                          let uu____5698 = mk_args ts in op uu____5698 in
                        FStar_All.pipe_right uu____5697 resBox in
                      let bv_and =
                        mk_bv FStar_SMTEncoding_Util.mkBvAnd binary
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_xor =
                        mk_bv FStar_SMTEncoding_Util.mkBvXor binary
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_or =
                        mk_bv FStar_SMTEncoding_Util.mkBvOr binary
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_add =
                        mk_bv FStar_SMTEncoding_Util.mkBvAdd binary
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_sub =
                        mk_bv FStar_SMTEncoding_Util.mkBvSub binary
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
                        let uu____5806 =
                          let uu____5809 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible" in
                          FStar_SMTEncoding_Util.mkBvUext uu____5809 in
                        let uu____5811 =
                          let uu____5814 =
                            let uu____5815 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible" in
                            sz + uu____5815 in
                          FStar_SMTEncoding_Term.boxBitVec uu____5814 in
                        mk_bv uu____5806 unary uu____5811 arg_tms2 in
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
                        (FStar_Parser_Const.bv_add_lid, bv_add);
                        (FStar_Parser_Const.bv_sub_lid, bv_sub);
                        (FStar_Parser_Const.bv_shift_left_lid, bv_shl);
                        (FStar_Parser_Const.bv_shift_right_lid, bv_shr);
                        (FStar_Parser_Const.bv_udiv_lid, bv_udiv);
                        (FStar_Parser_Const.bv_mod_lid, bv_mod);
                        (FStar_Parser_Const.bv_mul_lid, bv_mul);
                        (FStar_Parser_Const.bv_ult_lid, bv_ult);
                        (FStar_Parser_Const.bv_uext_lid, bv_uext);
                        (FStar_Parser_Const.bv_to_nat_lid, to_int);
                        (FStar_Parser_Const.nat_to_bv_lid, bv_to)] in
                      let uu____6014 =
                        let uu____6023 =
                          FStar_List.tryFind
                            (fun uu____6045  ->
                               match uu____6045 with
                               | (l,uu____6055) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops in
                        FStar_All.pipe_right uu____6023 FStar_Util.must in
                      (match uu____6014 with
                       | (uu____6096,op) ->
                           let uu____6106 = op arg_tms1 in
                           (uu____6106, (FStar_List.append sz_decls decls)))))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____6117 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____6117
       then
         let uu____6118 = FStar_Syntax_Print.tag_of_term t in
         let uu____6119 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____6120 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____6118 uu____6119
           uu____6120
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____6126 ->
           let uu____6151 =
             let uu____6152 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____6153 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____6154 = FStar_Syntax_Print.term_to_string t0 in
             let uu____6155 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6152
               uu____6153 uu____6154 uu____6155 in
           failwith uu____6151
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____6160 =
             let uu____6161 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____6162 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____6163 = FStar_Syntax_Print.term_to_string t0 in
             let uu____6164 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6161
               uu____6162 uu____6163 uu____6164 in
           failwith uu____6160
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____6170 =
             let uu____6171 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____6171 in
           failwith uu____6170
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____6178) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta
           ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
              FStar_Syntax_Syntax.pos = uu____6219;
              FStar_Syntax_Syntax.vars = uu____6220;_},FStar_Syntax_Syntax.Meta_alien
            (obj,desc,ty))
           ->
           let tsym =
             let uu____6237 = varops.fresh "t" in
             (uu____6237, FStar_SMTEncoding_Term.Term_sort) in
           let t1 = FStar_SMTEncoding_Util.mkFreeV tsym in
           let decl =
             let uu____6240 =
               let uu____6251 =
                 let uu____6254 = FStar_Util.format1 "alien term (%s)" desc in
                 FStar_Pervasives_Native.Some uu____6254 in
               ((FStar_Pervasives_Native.fst tsym), [],
                 FStar_SMTEncoding_Term.Term_sort, uu____6251) in
             FStar_SMTEncoding_Term.DeclFun uu____6240 in
           (t1, [decl])
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____6262) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____6272 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____6272, [])
       | FStar_Syntax_Syntax.Tm_type uu____6275 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6279) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____6304 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____6304 with
            | (binders1,res) ->
                let uu____6315 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____6315
                then
                  let uu____6320 =
                    encode_binders FStar_Pervasives_Native.None binders1 env in
                  (match uu____6320 with
                   | (vars,guards,env',decls,uu____6345) ->
                       let fsym =
                         let uu____6363 = varops.fresh "f" in
                         (uu____6363, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____6366 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___164_6375 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___164_6375.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___164_6375.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___164_6375.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___164_6375.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___164_6375.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___164_6375.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___164_6375.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___164_6375.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___164_6375.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___164_6375.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___164_6375.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___164_6375.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___164_6375.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___164_6375.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___164_6375.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___164_6375.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___164_6375.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___164_6375.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___164_6375.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___164_6375.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___164_6375.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___164_6375.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___164_6375.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___164_6375.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___164_6375.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___164_6375.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___164_6375.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___164_6375.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___164_6375.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___164_6375.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___164_6375.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___164_6375.FStar_TypeChecker_Env.dsenv)
                            }) res in
                       (match uu____6366 with
                        | (pre_opt,res_t) ->
                            let uu____6386 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app in
                            (match uu____6386 with
                             | (res_pred,decls') ->
                                 let uu____6397 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____6410 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____6410, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____6414 =
                                         encode_formula pre env' in
                                       (match uu____6414 with
                                        | (guard,decls0) ->
                                            let uu____6427 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____6427, decls0)) in
                                 (match uu____6397 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____6439 =
                                          let uu____6450 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____6450) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____6439 in
                                      let cvars =
                                        let uu____6468 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____6468
                                          (FStar_List.filter
                                             (fun uu____6482  ->
                                                match uu____6482 with
                                                | (x,uu____6488) ->
                                                    x <>
                                                      (FStar_Pervasives_Native.fst
                                                         fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____6507 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____6507 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____6515 =
                                             let uu____6516 =
                                               let uu____6523 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____6523) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6516 in
                                           (uu____6515,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____6543 =
                                               let uu____6544 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____6544 in
                                             varops.mk_unique uu____6543 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars in
                                           let caption =
                                             let uu____6555 =
                                               FStar_Options.log_queries () in
                                             if uu____6555
                                             then
                                               let uu____6558 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____6558
                                             else
                                               FStar_Pervasives_Native.None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____6566 =
                                               let uu____6573 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____6573) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6566 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____6585 =
                                               let uu____6592 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____6592,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6585 in
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
                                             let uu____6613 =
                                               let uu____6620 =
                                                 let uu____6621 =
                                                   let uu____6632 =
                                                     let uu____6633 =
                                                       let uu____6638 =
                                                         let uu____6639 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____6639 in
                                                       (f_has_t, uu____6638) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____6633 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____6632) in
                                                 mkForall_fuel uu____6621 in
                                               (uu____6620,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6613 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____6662 =
                                               let uu____6669 =
                                                 let uu____6670 =
                                                   let uu____6681 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____6681) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____6670 in
                                               (uu____6669,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6662 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____6706 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____6706);
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
                     let uu____6721 =
                       let uu____6728 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____6728,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6721 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____6740 =
                       let uu____6747 =
                         let uu____6748 =
                           let uu____6759 =
                             let uu____6760 =
                               let uu____6765 =
                                 let uu____6766 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____6766 in
                               (f_has_t, uu____6765) in
                             FStar_SMTEncoding_Util.mkImp uu____6760 in
                           ([[f_has_t]], [fsym], uu____6759) in
                         mkForall_fuel uu____6748 in
                       (uu____6747, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6740 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____6793 ->
           let uu____6800 =
             let uu____6805 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.Weak;
                 FStar_TypeChecker_Normalize.HNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____6805 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____6812;
                 FStar_Syntax_Syntax.vars = uu____6813;_} ->
                 let uu____6820 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f in
                 (match uu____6820 with
                  | (b,f1) ->
                      let uu____6845 =
                        let uu____6846 = FStar_List.hd b in
                        FStar_Pervasives_Native.fst uu____6846 in
                      (uu____6845, f1))
             | uu____6855 -> failwith "impossible" in
           (match uu____6800 with
            | (x,f) ->
                let uu____6866 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____6866 with
                 | (base_t,decls) ->
                     let uu____6877 = gen_term_var env x in
                     (match uu____6877 with
                      | (x1,xtm,env') ->
                          let uu____6891 = encode_formula f env' in
                          (match uu____6891 with
                           | (refinement,decls') ->
                               let uu____6902 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____6902 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____6918 =
                                        let uu____6921 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____6928 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____6921
                                          uu____6928 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____6918 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____6961  ->
                                              match uu____6961 with
                                              | (y,uu____6967) ->
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
                                    let uu____7000 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____7000 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____7008 =
                                           let uu____7009 =
                                             let uu____7016 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____7016) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____7009 in
                                         (uu____7008,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____7037 =
                                             let uu____7038 =
                                               let uu____7039 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____7039 in
                                             Prims.strcat module_name
                                               uu____7038 in
                                           varops.mk_unique uu____7037 in
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
                                           let uu____7053 =
                                             let uu____7060 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____7060) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____7053 in
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
                                           let uu____7075 =
                                             let uu____7082 =
                                               let uu____7083 =
                                                 let uu____7094 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____7094) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7083 in
                                             (uu____7082,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7075 in
                                         let t_kinding =
                                           let uu____7112 =
                                             let uu____7119 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____7119,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7112 in
                                         let t_interp =
                                           let uu____7137 =
                                             let uu____7144 =
                                               let uu____7145 =
                                                 let uu____7156 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____7156) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7145 in
                                             let uu____7179 =
                                               let uu____7182 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____7182 in
                                             (uu____7144, uu____7179,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7137 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____7189 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____7189);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____7219 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____7219 in
           let uu____7220 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm in
           (match uu____7220 with
            | (t_has_k,decls) ->
                let d =
                  let uu____7232 =
                    let uu____7239 =
                      let uu____7240 =
                        let uu____7241 =
                          let uu____7242 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____7242 in
                        FStar_Util.format1 "uvar_typing_%s" uu____7241 in
                      varops.mk_unique uu____7240 in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____7239) in
                  FStar_SMTEncoding_Util.mkAssume uu____7232 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____7247 ->
           let uu____7262 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____7262 with
            | (head1,args_e) ->
                let uu____7303 =
                  let uu____7316 =
                    let uu____7317 = FStar_Syntax_Subst.compress head1 in
                    uu____7317.FStar_Syntax_Syntax.n in
                  (uu____7316, args_e) in
                (match uu____7303 with
                 | uu____7332 when head_redex env head1 ->
                     let uu____7345 = whnf env t in
                     encode_term uu____7345 env
                 | uu____7346 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____7365 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____7379;
                       FStar_Syntax_Syntax.vars = uu____7380;_},uu____7381),uu____7382::
                    (v1,uu____7384)::(v2,uu____7386)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7437 = encode_term v1 env in
                     (match uu____7437 with
                      | (v11,decls1) ->
                          let uu____7448 = encode_term v2 env in
                          (match uu____7448 with
                           | (v21,decls2) ->
                               let uu____7459 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7459,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____7463::(v1,uu____7465)::(v2,uu____7467)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7514 = encode_term v1 env in
                     (match uu____7514 with
                      | (v11,decls1) ->
                          let uu____7525 = encode_term v2 env in
                          (match uu____7525 with
                           | (v21,decls2) ->
                               let uu____7536 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7536,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____7540)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(rng,uu____7566)::(arg,uu____7568)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____7603) ->
                     let e0 =
                       let uu____7621 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____7621 in
                     ((let uu____7629 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____7629
                       then
                         let uu____7630 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____7630
                       else ());
                      (let e =
                         let uu____7635 =
                           let uu____7636 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____7637 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____7636
                             uu____7637 in
                         uu____7635 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____7646),(arg,uu____7648)::[]) -> encode_term arg env
                 | uu____7673 ->
                     let uu____7686 = encode_args args_e env in
                     (match uu____7686 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____7741 = encode_term head1 env in
                            match uu____7741 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____7805 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____7805 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____7883  ->
                                                 fun uu____7884  ->
                                                   match (uu____7883,
                                                           uu____7884)
                                                   with
                                                   | ((bv,uu____7906),
                                                      (a,uu____7908)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____7926 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____7926
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____7931 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm in
                                          (match uu____7931 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____7946 =
                                                   let uu____7953 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____7962 =
                                                     let uu____7963 =
                                                       let uu____7964 =
                                                         let uu____7965 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____7965 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____7964 in
                                                     varops.mk_unique
                                                       uu____7963 in
                                                   (uu____7953,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____7962) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____7946 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____7982 = lookup_free_var_sym env fv in
                            match uu____7982 with
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
                                   FStar_Syntax_Syntax.pos = uu____8013;
                                   FStar_Syntax_Syntax.vars = uu____8014;_},uu____8015)
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
                                   FStar_Syntax_Syntax.pos = uu____8026;
                                   FStar_Syntax_Syntax.vars = uu____8027;_},uu____8028)
                                ->
                                let uu____8033 =
                                  let uu____8034 =
                                    let uu____8039 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____8039
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____8034
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____8033
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____8069 =
                                  let uu____8070 =
                                    let uu____8075 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____8075
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____8070
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____8069
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8104,(FStar_Util.Inl t1,uu____8106),uu____8107)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8156,(FStar_Util.Inr c,uu____8158),uu____8159)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____8208 -> FStar_Pervasives_Native.None in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____8235 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.Weak;
                                     FStar_TypeChecker_Normalize.HNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____8235 in
                               let uu____8236 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____8236 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____8252;
                                            FStar_Syntax_Syntax.vars =
                                              uu____8253;_},uu____8254)
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
                                     | uu____8268 ->
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
           let uu____8317 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____8317 with
            | (bs1,body1,opening) ->
                let fallback uu____8340 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding")) in
                  let uu____8347 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____8347, [decl]) in
                let is_impure rc =
                  let uu____8354 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect in
                  FStar_All.pipe_right uu____8354 Prims.op_Negation in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____8364 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____8364
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1 in
                  if
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                  then
                    let uu____8384 = FStar_Syntax_Syntax.mk_Total res_typ in
                    FStar_Pervasives_Native.Some uu____8384
                  else
                    if
                      FStar_Ident.lid_equals
                        rc.FStar_Syntax_Syntax.residual_effect
                        FStar_Parser_Const.effect_GTot_lid
                    then
                      (let uu____8388 = FStar_Syntax_Syntax.mk_GTotal res_typ in
                       FStar_Pervasives_Native.Some uu____8388)
                    else FStar_Pervasives_Native.None in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____8395 =
                         let uu____8396 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____8396 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____8395);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____8398 =
                       (is_impure rc) &&
                         (let uu____8400 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc in
                          Prims.op_Negation uu____8400) in
                     if uu____8398
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____8407 =
                          encode_binders FStar_Pervasives_Native.None bs1 env in
                        match uu____8407 with
                        | (vars,guards,envbody,decls,uu____8432) ->
                            let body2 =
                              let uu____8446 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  rc in
                              if uu____8446
                              then
                                FStar_TypeChecker_Util.reify_body env.tcenv
                                  body1
                              else body1 in
                            let uu____8448 = encode_term body2 envbody in
                            (match uu____8448 with
                             | (body3,decls') ->
                                 let uu____8459 =
                                   let uu____8468 = codomain_eff rc in
                                   match uu____8468 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c in
                                       let uu____8487 = encode_term tfun env in
                                       (match uu____8487 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1)) in
                                 (match uu____8459 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____8519 =
                                          let uu____8530 =
                                            let uu____8531 =
                                              let uu____8536 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____8536, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8531 in
                                          ([], vars, uu____8530) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____8519 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            cvars
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____8548 =
                                              let uu____8551 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1 in
                                              FStar_List.append uu____8551
                                                cvars in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____8548 in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____8570 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____8570 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____8578 =
                                             let uu____8579 =
                                               let uu____8586 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1 in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____8586) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____8579 in
                                           (uu____8578,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____8597 =
                                             is_an_eta_expansion env vars
                                               body3 in
                                           (match uu____8597 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____8608 =
                                                    let uu____8609 =
                                                      FStar_Util.smap_size
                                                        env.cache in
                                                    uu____8609 = cache_size in
                                                  if uu____8608
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
                                                    let uu____8625 =
                                                      let uu____8626 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____8626 in
                                                    varops.mk_unique
                                                      uu____8625 in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym) in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None) in
                                                let f =
                                                  let uu____8633 =
                                                    let uu____8640 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    (fsym, uu____8640) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____8633 in
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
                                                      let uu____8658 =
                                                        let uu____8659 =
                                                          let uu____8666 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t) in
                                                          (uu____8666,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name) in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8659 in
                                                      [uu____8658] in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym in
                                                  let uu____8679 =
                                                    let uu____8686 =
                                                      let uu____8687 =
                                                        let uu____8698 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3) in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____8698) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____8687 in
                                                    (uu____8686,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____8679 in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f]))) in
                                                ((let uu____8715 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____8715);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8718,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____8719;
                          FStar_Syntax_Syntax.lbunivs = uu____8720;
                          FStar_Syntax_Syntax.lbtyp = uu____8721;
                          FStar_Syntax_Syntax.lbeff = uu____8722;
                          FStar_Syntax_Syntax.lbdef = uu____8723;_}::uu____8724),uu____8725)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____8751;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____8753;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____8774 ->
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
              let uu____8844 = encode_term e1 env in
              match uu____8844 with
              | (ee1,decls1) ->
                  let uu____8855 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2 in
                  (match uu____8855 with
                   | (xs,e21) ->
                       let uu____8880 = FStar_List.hd xs in
                       (match uu____8880 with
                        | (x1,uu____8894) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____8896 = encode_body e21 env' in
                            (match uu____8896 with
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
            let uu____8928 =
              let uu____8935 =
                let uu____8936 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____8936 in
              gen_term_var env uu____8935 in
            match uu____8928 with
            | (scrsym,scr',env1) ->
                let uu____8944 = encode_term e env1 in
                (match uu____8944 with
                 | (scr,decls) ->
                     let uu____8955 =
                       let encode_branch b uu____8980 =
                         match uu____8980 with
                         | (else_case,decls1) ->
                             let uu____8999 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____8999 with
                              | (p,w,br) ->
                                  let uu____9025 = encode_pat env1 p in
                                  (match uu____9025 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____9062  ->
                                                   match uu____9062 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____9069 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____9091 =
                                               encode_term w1 env2 in
                                             (match uu____9091 with
                                              | (w2,decls2) ->
                                                  let uu____9104 =
                                                    let uu____9105 =
                                                      let uu____9110 =
                                                        let uu____9111 =
                                                          let uu____9116 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____9116) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____9111 in
                                                      (guard, uu____9110) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____9105 in
                                                  (uu____9104, decls2)) in
                                       (match uu____9069 with
                                        | (guard1,decls2) ->
                                            let uu____9129 =
                                              encode_br br env2 in
                                            (match uu____9129 with
                                             | (br1,decls3) ->
                                                 let uu____9142 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____9142,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____8955 with
                      | (match_tm,decls1) ->
                          let uu____9161 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____9161, decls1)))
and encode_pat:
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pat  ->
      (let uu____9201 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____9201
       then
         let uu____9202 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____9202
       else ());
      (let uu____9204 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____9204 with
       | (vars,pat_term) ->
           let uu____9221 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____9274  ->
                     fun v1  ->
                       match uu____9274 with
                       | (env1,vars1) ->
                           let uu____9326 = gen_term_var env1 v1 in
                           (match uu____9326 with
                            | (xx,uu____9348,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____9221 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9427 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9428 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9429 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9437 = encode_const c env1 in
                      (match uu____9437 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____9451::uu____9452 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____9455 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____9478 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____9478 with
                        | (uu____9485,uu____9486::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9489 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9522  ->
                                  match uu____9522 with
                                  | (arg,uu____9530) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9536 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____9536)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9563) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9594 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9617 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9661  ->
                                  match uu____9661 with
                                  | (arg,uu____9675) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9681 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____9681)) in
                      FStar_All.pipe_right uu____9617 FStar_List.flatten in
                let pat_term1 uu____9709 = encode_term pat_term env1 in
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
      let uu____9719 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____9757  ->
                fun uu____9758  ->
                  match (uu____9757, uu____9758) with
                  | ((tms,decls),(t,uu____9794)) ->
                      let uu____9815 = encode_term t env in
                      (match uu____9815 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____9719 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____9872 = FStar_Syntax_Util.list_elements e in
        match uu____9872 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____9893 =
          let uu____9908 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____9908 FStar_Syntax_Util.head_and_args in
        match uu____9893 with
        | (head1,args) ->
            let uu____9947 =
              let uu____9960 =
                let uu____9961 = FStar_Syntax_Util.un_uinst head1 in
                uu____9961.FStar_Syntax_Syntax.n in
              (uu____9960, args) in
            (match uu____9947 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____9975,uu____9976)::(e,uu____9978)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____10013 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____10049 =
            let uu____10064 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____10064 FStar_Syntax_Util.head_and_args in
          match uu____10049 with
          | (head1,args) ->
              let uu____10105 =
                let uu____10118 =
                  let uu____10119 = FStar_Syntax_Util.un_uinst head1 in
                  uu____10119.FStar_Syntax_Syntax.n in
                (uu____10118, args) in
              (match uu____10105 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____10136)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____10163 -> FStar_Pervasives_Native.None) in
        match elts with
        | t1::[] ->
            let uu____10185 = smt_pat_or1 t1 in
            (match uu____10185 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____10201 = list_elements1 e in
                 FStar_All.pipe_right uu____10201
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____10219 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____10219
                           (FStar_List.map one_pat)))
             | uu____10230 ->
                 let uu____10235 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____10235])
        | uu____10256 ->
            let uu____10259 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____10259] in
      let uu____10280 =
        let uu____10299 =
          let uu____10300 = FStar_Syntax_Subst.compress t in
          uu____10300.FStar_Syntax_Syntax.n in
        match uu____10299 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____10339 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____10339 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____10382;
                        FStar_Syntax_Syntax.effect_name = uu____10383;
                        FStar_Syntax_Syntax.result_typ = uu____10384;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____10386)::(post,uu____10388)::(pats,uu____10390)::[];
                        FStar_Syntax_Syntax.flags = uu____10391;_}
                      ->
                      let uu____10432 = lemma_pats pats in
                      (binders1, pre, post, uu____10432)
                  | uu____10449 -> failwith "impos"))
        | uu____10468 -> failwith "Impos" in
      match uu____10280 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___165_10516 = env in
            {
              bindings = (uu___165_10516.bindings);
              depth = (uu___165_10516.depth);
              tcenv = (uu___165_10516.tcenv);
              warn = (uu___165_10516.warn);
              cache = (uu___165_10516.cache);
              nolabels = (uu___165_10516.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___165_10516.encode_non_total_function_typ);
              current_module_name = (uu___165_10516.current_module_name)
            } in
          let uu____10517 =
            encode_binders FStar_Pervasives_Native.None binders env1 in
          (match uu____10517 with
           | (vars,guards,env2,decls,uu____10542) ->
               let uu____10555 =
                 let uu____10568 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____10612 =
                             let uu____10621 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2)) in
                             FStar_All.pipe_right uu____10621
                               FStar_List.unzip in
                           match uu____10612 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____10568 FStar_List.unzip in
               (match uu____10555 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post in
                    let env3 =
                      let uu___166_10733 = env2 in
                      {
                        bindings = (uu___166_10733.bindings);
                        depth = (uu___166_10733.depth);
                        tcenv = (uu___166_10733.tcenv);
                        warn = (uu___166_10733.warn);
                        cache = (uu___166_10733.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___166_10733.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___166_10733.encode_non_total_function_typ);
                        current_module_name =
                          (uu___166_10733.current_module_name)
                      } in
                    let uu____10734 =
                      let uu____10739 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____10739 env3 in
                    (match uu____10734 with
                     | (pre1,decls'') ->
                         let uu____10746 =
                           let uu____10751 = FStar_Syntax_Util.unmeta post1 in
                           encode_formula uu____10751 env3 in
                         (match uu____10746 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____10761 =
                                let uu____10762 =
                                  let uu____10773 =
                                    let uu____10774 =
                                      let uu____10779 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____10779, post2) in
                                    FStar_SMTEncoding_Util.mkImp uu____10774 in
                                  (pats, vars, uu____10773) in
                                FStar_SMTEncoding_Util.mkForall uu____10762 in
                              (uu____10761, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____10798 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____10798
        then
          let uu____10799 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____10800 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10799 uu____10800
        else () in
      let enc f r l =
        let uu____10833 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10861 =
                   encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu____10861 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____10833 with
        | (decls,args) ->
            let uu____10890 =
              let uu___167_10891 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___167_10891.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___167_10891.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____10890, decls) in
      let const_op f r uu____10922 =
        let uu____10935 = f r in (uu____10935, []) in
      let un_op f l =
        let uu____10954 = FStar_List.hd l in
        FStar_All.pipe_left f uu____10954 in
      let bin_op f uu___141_10970 =
        match uu___141_10970 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10981 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____11015 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____11038  ->
                 match uu____11038 with
                 | (t,uu____11052) ->
                     let uu____11053 = encode_formula t env in
                     (match uu____11053 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____11015 with
        | (decls,phis) ->
            let uu____11082 =
              let uu___168_11083 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___168_11083.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___168_11083.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____11082, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____11144  ->
               match uu____11144 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____11163) -> false
                    | uu____11164 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____11179 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____11179
        else
          (let uu____11193 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____11193 r rf) in
      let mk_imp1 r uu___142_11218 =
        match uu___142_11218 with
        | (lhs,uu____11224)::(rhs,uu____11226)::[] ->
            let uu____11253 = encode_formula rhs env in
            (match uu____11253 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11268) ->
                      (l1, decls1)
                  | uu____11273 ->
                      let uu____11274 = encode_formula lhs env in
                      (match uu____11274 with
                       | (l2,decls2) ->
                           let uu____11285 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____11285, (FStar_List.append decls1 decls2)))))
        | uu____11288 -> failwith "impossible" in
      let mk_ite r uu___143_11309 =
        match uu___143_11309 with
        | (guard,uu____11315)::(_then,uu____11317)::(_else,uu____11319)::[]
            ->
            let uu____11356 = encode_formula guard env in
            (match uu____11356 with
             | (g,decls1) ->
                 let uu____11367 = encode_formula _then env in
                 (match uu____11367 with
                  | (t,decls2) ->
                      let uu____11378 = encode_formula _else env in
                      (match uu____11378 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11392 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____11417 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____11417 in
      let connectives =
        let uu____11435 =
          let uu____11448 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Parser_Const.and_lid, uu____11448) in
        let uu____11465 =
          let uu____11480 =
            let uu____11493 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Parser_Const.or_lid, uu____11493) in
          let uu____11510 =
            let uu____11525 =
              let uu____11540 =
                let uu____11553 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Parser_Const.iff_lid, uu____11553) in
              let uu____11570 =
                let uu____11585 =
                  let uu____11600 =
                    let uu____11613 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Parser_Const.not_lid, uu____11613) in
                  [uu____11600;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11585 in
              uu____11540 :: uu____11570 in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11525 in
          uu____11480 :: uu____11510 in
        uu____11435 :: uu____11465 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____11934 = encode_formula phi' env in
            (match uu____11934 with
             | (phi2,decls) ->
                 let uu____11945 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____11945, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____11946 ->
            let uu____11953 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____11953 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____11992 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____11992 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____12004;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____12006;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____12027 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____12027 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____12074::(x,uu____12076)::(t,uu____12078)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12125 = encode_term x env in
                 (match uu____12125 with
                  | (x1,decls) ->
                      let uu____12136 = encode_term t env in
                      (match uu____12136 with
                       | (t1,decls') ->
                           let uu____12147 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____12147, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12152)::(msg,uu____12154)::(phi2,uu____12156)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12201 =
                   let uu____12206 =
                     let uu____12207 = FStar_Syntax_Subst.compress r in
                     uu____12207.FStar_Syntax_Syntax.n in
                   let uu____12210 =
                     let uu____12211 = FStar_Syntax_Subst.compress msg in
                     uu____12211.FStar_Syntax_Syntax.n in
                   (uu____12206, uu____12210) in
                 (match uu____12201 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12220))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1 in
                      fallback phi3
                  | uu____12226 -> fallback phi2)
             | uu____12231 when head_redex env head2 ->
                 let uu____12244 = whnf env phi1 in
                 encode_formula uu____12244 env
             | uu____12245 ->
                 let uu____12258 = encode_term phi1 env in
                 (match uu____12258 with
                  | (tt,decls) ->
                      let uu____12269 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___169_12272 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___169_12272.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___169_12272.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____12269, decls)))
        | uu____12273 ->
            let uu____12274 = encode_term phi1 env in
            (match uu____12274 with
             | (tt,decls) ->
                 let uu____12285 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___170_12288 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___170_12288.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___170_12288.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____12285, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____12324 = encode_binders FStar_Pervasives_Native.None bs env1 in
        match uu____12324 with
        | (vars,guards,env2,decls,uu____12363) ->
            let uu____12376 =
              let uu____12389 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____12437 =
                          let uu____12446 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____12476  ->
                                    match uu____12476 with
                                    | (t,uu____12486) ->
                                        encode_term t
                                          (let uu___171_12488 = env2 in
                                           {
                                             bindings =
                                               (uu___171_12488.bindings);
                                             depth = (uu___171_12488.depth);
                                             tcenv = (uu___171_12488.tcenv);
                                             warn = (uu___171_12488.warn);
                                             cache = (uu___171_12488.cache);
                                             nolabels =
                                               (uu___171_12488.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___171_12488.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___171_12488.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____12446 FStar_List.unzip in
                        match uu____12437 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____12389 FStar_List.unzip in
            (match uu____12376 with
             | (pats,decls') ->
                 let uu____12587 = encode_formula body env2 in
                 (match uu____12587 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12619;
                             FStar_SMTEncoding_Term.rng = uu____12620;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____12635 -> guards in
                      let uu____12640 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____12640, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____12700  ->
                   match uu____12700 with
                   | (x,uu____12706) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____12714 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____12726 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____12726) uu____12714 tl1 in
             let uu____12729 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____12756  ->
                       match uu____12756 with
                       | (b,uu____12762) ->
                           let uu____12763 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____12763)) in
             (match uu____12729 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____12769) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____12783 =
                    let uu____12784 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____12784 in
                  FStar_Errors.warn pos uu____12783) in
       let uu____12785 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____12785 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12794 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____12852  ->
                     match uu____12852 with
                     | (l,uu____12866) -> FStar_Ident.lid_equals op l)) in
           (match uu____12794 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____12899,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12939 = encode_q_body env vars pats body in
             match uu____12939 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____12984 =
                     let uu____12995 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____12995) in
                   FStar_SMTEncoding_Term.mkForall uu____12984
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____13014 = encode_q_body env vars pats body in
             match uu____13014 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____13058 =
                   let uu____13059 =
                     let uu____13070 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____13070) in
                   FStar_SMTEncoding_Term.mkExists uu____13059
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____13058, decls))))
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
  let uu____13168 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____13168 with
  | (asym,a) ->
      let uu____13175 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____13175 with
       | (xsym,x) ->
           let uu____13182 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____13182 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____13226 =
                      let uu____13237 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd) in
                      (x1, uu____13237, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13226 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                  let xapp =
                    let uu____13263 =
                      let uu____13270 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____13270) in
                    FStar_SMTEncoding_Util.mkApp uu____13263 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____13283 =
                    let uu____13286 =
                      let uu____13289 =
                        let uu____13292 =
                          let uu____13293 =
                            let uu____13300 =
                              let uu____13301 =
                                let uu____13312 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____13312) in
                              FStar_SMTEncoding_Util.mkForall uu____13301 in
                            (uu____13300, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____13293 in
                        let uu____13329 =
                          let uu____13332 =
                            let uu____13333 =
                              let uu____13340 =
                                let uu____13341 =
                                  let uu____13352 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____13352) in
                                FStar_SMTEncoding_Util.mkForall uu____13341 in
                              (uu____13340,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____13333 in
                          [uu____13332] in
                        uu____13292 :: uu____13329 in
                      xtok_decl :: uu____13289 in
                    xname_decl :: uu____13286 in
                  (xtok1, uu____13283) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____13443 =
                    let uu____13456 =
                      let uu____13465 =
                        let uu____13466 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____13466 in
                      quant axy uu____13465 in
                    (FStar_Parser_Const.op_Eq, uu____13456) in
                  let uu____13475 =
                    let uu____13490 =
                      let uu____13503 =
                        let uu____13512 =
                          let uu____13513 =
                            let uu____13514 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____13514 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____13513 in
                        quant axy uu____13512 in
                      (FStar_Parser_Const.op_notEq, uu____13503) in
                    let uu____13523 =
                      let uu____13538 =
                        let uu____13551 =
                          let uu____13560 =
                            let uu____13561 =
                              let uu____13562 =
                                let uu____13567 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____13568 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____13567, uu____13568) in
                              FStar_SMTEncoding_Util.mkLT uu____13562 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____13561 in
                          quant xy uu____13560 in
                        (FStar_Parser_Const.op_LT, uu____13551) in
                      let uu____13577 =
                        let uu____13592 =
                          let uu____13605 =
                            let uu____13614 =
                              let uu____13615 =
                                let uu____13616 =
                                  let uu____13621 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____13622 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____13621, uu____13622) in
                                FStar_SMTEncoding_Util.mkLTE uu____13616 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____13615 in
                            quant xy uu____13614 in
                          (FStar_Parser_Const.op_LTE, uu____13605) in
                        let uu____13631 =
                          let uu____13646 =
                            let uu____13659 =
                              let uu____13668 =
                                let uu____13669 =
                                  let uu____13670 =
                                    let uu____13675 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____13676 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____13675, uu____13676) in
                                  FStar_SMTEncoding_Util.mkGT uu____13670 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____13669 in
                              quant xy uu____13668 in
                            (FStar_Parser_Const.op_GT, uu____13659) in
                          let uu____13685 =
                            let uu____13700 =
                              let uu____13713 =
                                let uu____13722 =
                                  let uu____13723 =
                                    let uu____13724 =
                                      let uu____13729 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____13730 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____13729, uu____13730) in
                                    FStar_SMTEncoding_Util.mkGTE uu____13724 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____13723 in
                                quant xy uu____13722 in
                              (FStar_Parser_Const.op_GTE, uu____13713) in
                            let uu____13739 =
                              let uu____13754 =
                                let uu____13767 =
                                  let uu____13776 =
                                    let uu____13777 =
                                      let uu____13778 =
                                        let uu____13783 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____13784 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____13783, uu____13784) in
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____13778 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____13777 in
                                  quant xy uu____13776 in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____13767) in
                              let uu____13793 =
                                let uu____13808 =
                                  let uu____13821 =
                                    let uu____13830 =
                                      let uu____13831 =
                                        let uu____13832 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____13832 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____13831 in
                                    quant qx uu____13830 in
                                  (FStar_Parser_Const.op_Minus, uu____13821) in
                                let uu____13841 =
                                  let uu____13856 =
                                    let uu____13869 =
                                      let uu____13878 =
                                        let uu____13879 =
                                          let uu____13880 =
                                            let uu____13885 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____13886 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____13885, uu____13886) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____13880 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____13879 in
                                      quant xy uu____13878 in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____13869) in
                                  let uu____13895 =
                                    let uu____13910 =
                                      let uu____13923 =
                                        let uu____13932 =
                                          let uu____13933 =
                                            let uu____13934 =
                                              let uu____13939 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____13940 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____13939, uu____13940) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____13934 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____13933 in
                                        quant xy uu____13932 in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____13923) in
                                    let uu____13949 =
                                      let uu____13964 =
                                        let uu____13977 =
                                          let uu____13986 =
                                            let uu____13987 =
                                              let uu____13988 =
                                                let uu____13993 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____13994 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____13993, uu____13994) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____13988 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____13987 in
                                          quant xy uu____13986 in
                                        (FStar_Parser_Const.op_Division,
                                          uu____13977) in
                                      let uu____14003 =
                                        let uu____14018 =
                                          let uu____14031 =
                                            let uu____14040 =
                                              let uu____14041 =
                                                let uu____14042 =
                                                  let uu____14047 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____14048 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____14047, uu____14048) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____14042 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____14041 in
                                            quant xy uu____14040 in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____14031) in
                                        let uu____14057 =
                                          let uu____14072 =
                                            let uu____14085 =
                                              let uu____14094 =
                                                let uu____14095 =
                                                  let uu____14096 =
                                                    let uu____14101 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____14102 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____14101,
                                                      uu____14102) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____14096 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____14095 in
                                              quant xy uu____14094 in
                                            (FStar_Parser_Const.op_And,
                                              uu____14085) in
                                          let uu____14111 =
                                            let uu____14126 =
                                              let uu____14139 =
                                                let uu____14148 =
                                                  let uu____14149 =
                                                    let uu____14150 =
                                                      let uu____14155 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____14156 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____14155,
                                                        uu____14156) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____14150 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____14149 in
                                                quant xy uu____14148 in
                                              (FStar_Parser_Const.op_Or,
                                                uu____14139) in
                                            let uu____14165 =
                                              let uu____14180 =
                                                let uu____14193 =
                                                  let uu____14202 =
                                                    let uu____14203 =
                                                      let uu____14204 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____14204 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____14203 in
                                                  quant qx uu____14202 in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____14193) in
                                              [uu____14180] in
                                            uu____14126 :: uu____14165 in
                                          uu____14072 :: uu____14111 in
                                        uu____14018 :: uu____14057 in
                                      uu____13964 :: uu____14003 in
                                    uu____13910 :: uu____13949 in
                                  uu____13856 :: uu____13895 in
                                uu____13808 :: uu____13841 in
                              uu____13754 :: uu____13793 in
                            uu____13700 :: uu____13739 in
                          uu____13646 :: uu____13685 in
                        uu____13592 :: uu____13631 in
                      uu____13538 :: uu____13577 in
                    uu____13490 :: uu____13523 in
                  uu____13443 :: uu____13475 in
                let mk1 l v1 =
                  let uu____14418 =
                    let uu____14427 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____14485  ->
                              match uu____14485 with
                              | (l',uu____14499) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____14427
                      (FStar_Option.map
                         (fun uu____14559  ->
                            match uu____14559 with | (uu____14578,b) -> b v1)) in
                  FStar_All.pipe_right uu____14418 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____14649  ->
                          match uu____14649 with
                          | (l',uu____14663) -> FStar_Ident.lid_equals l l')) in
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
        let uu____14704 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____14704 with
        | (xxsym,xx) ->
            let uu____14711 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____14711 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____14721 =
                   let uu____14728 =
                     let uu____14729 =
                       let uu____14740 =
                         let uu____14741 =
                           let uu____14746 =
                             let uu____14747 =
                               let uu____14752 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____14752) in
                             FStar_SMTEncoding_Util.mkEq uu____14747 in
                           (xx_has_type, uu____14746) in
                         FStar_SMTEncoding_Util.mkImp uu____14741 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____14740) in
                     FStar_SMTEncoding_Util.mkForall uu____14729 in
                   let uu____14777 =
                     let uu____14778 =
                       let uu____14779 =
                         let uu____14780 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____14780 in
                       Prims.strcat module_name uu____14779 in
                     varops.mk_unique uu____14778 in
                   (uu____14728, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____14777) in
                 FStar_SMTEncoding_Util.mkAssume uu____14721)
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
    let uu____14820 =
      let uu____14821 =
        let uu____14828 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____14828, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14821 in
    let uu____14831 =
      let uu____14834 =
        let uu____14835 =
          let uu____14842 =
            let uu____14843 =
              let uu____14854 =
                let uu____14855 =
                  let uu____14860 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____14860) in
                FStar_SMTEncoding_Util.mkImp uu____14855 in
              ([[typing_pred]], [xx], uu____14854) in
            mkForall_fuel uu____14843 in
          (uu____14842, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14835 in
      [uu____14834] in
    uu____14820 :: uu____14831 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____14902 =
      let uu____14903 =
        let uu____14910 =
          let uu____14911 =
            let uu____14922 =
              let uu____14927 =
                let uu____14930 = FStar_SMTEncoding_Term.boxBool b in
                [uu____14930] in
              [uu____14927] in
            let uu____14935 =
              let uu____14936 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____14936 tt in
            (uu____14922, [bb], uu____14935) in
          FStar_SMTEncoding_Util.mkForall uu____14911 in
        (uu____14910, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14903 in
    let uu____14957 =
      let uu____14960 =
        let uu____14961 =
          let uu____14968 =
            let uu____14969 =
              let uu____14980 =
                let uu____14981 =
                  let uu____14986 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x in
                  (typing_pred, uu____14986) in
                FStar_SMTEncoding_Util.mkImp uu____14981 in
              ([[typing_pred]], [xx], uu____14980) in
            mkForall_fuel uu____14969 in
          (uu____14968, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14961 in
      [uu____14960] in
    uu____14902 :: uu____14957 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____15036 =
        let uu____15037 =
          let uu____15044 =
            let uu____15047 =
              let uu____15050 =
                let uu____15053 = FStar_SMTEncoding_Term.boxInt a in
                let uu____15054 =
                  let uu____15057 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____15057] in
                uu____15053 :: uu____15054 in
              tt :: uu____15050 in
            tt :: uu____15047 in
          ("Prims.Precedes", uu____15044) in
        FStar_SMTEncoding_Util.mkApp uu____15037 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15036 in
    let precedes_y_x =
      let uu____15061 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15061 in
    let uu____15064 =
      let uu____15065 =
        let uu____15072 =
          let uu____15073 =
            let uu____15084 =
              let uu____15089 =
                let uu____15092 = FStar_SMTEncoding_Term.boxInt b in
                [uu____15092] in
              [uu____15089] in
            let uu____15097 =
              let uu____15098 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____15098 tt in
            (uu____15084, [bb], uu____15097) in
          FStar_SMTEncoding_Util.mkForall uu____15073 in
        (uu____15072, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15065 in
    let uu____15119 =
      let uu____15122 =
        let uu____15123 =
          let uu____15130 =
            let uu____15131 =
              let uu____15142 =
                let uu____15143 =
                  let uu____15148 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x in
                  (typing_pred, uu____15148) in
                FStar_SMTEncoding_Util.mkImp uu____15143 in
              ([[typing_pred]], [xx], uu____15142) in
            mkForall_fuel uu____15131 in
          (uu____15130, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15123 in
      let uu____15173 =
        let uu____15176 =
          let uu____15177 =
            let uu____15184 =
              let uu____15185 =
                let uu____15196 =
                  let uu____15197 =
                    let uu____15202 =
                      let uu____15203 =
                        let uu____15206 =
                          let uu____15209 =
                            let uu____15212 =
                              let uu____15213 =
                                let uu____15218 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____15219 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____15218, uu____15219) in
                              FStar_SMTEncoding_Util.mkGT uu____15213 in
                            let uu____15220 =
                              let uu____15223 =
                                let uu____15224 =
                                  let uu____15229 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____15230 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____15229, uu____15230) in
                                FStar_SMTEncoding_Util.mkGTE uu____15224 in
                              let uu____15231 =
                                let uu____15234 =
                                  let uu____15235 =
                                    let uu____15240 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____15241 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____15240, uu____15241) in
                                  FStar_SMTEncoding_Util.mkLT uu____15235 in
                                [uu____15234] in
                              uu____15223 :: uu____15231 in
                            uu____15212 :: uu____15220 in
                          typing_pred_y :: uu____15209 in
                        typing_pred :: uu____15206 in
                      FStar_SMTEncoding_Util.mk_and_l uu____15203 in
                    (uu____15202, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____15197 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____15196) in
              mkForall_fuel uu____15185 in
            (uu____15184,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____15177 in
        [uu____15176] in
      uu____15122 :: uu____15173 in
    uu____15064 :: uu____15119 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____15287 =
      let uu____15288 =
        let uu____15295 =
          let uu____15296 =
            let uu____15307 =
              let uu____15312 =
                let uu____15315 = FStar_SMTEncoding_Term.boxString b in
                [uu____15315] in
              [uu____15312] in
            let uu____15320 =
              let uu____15321 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____15321 tt in
            (uu____15307, [bb], uu____15320) in
          FStar_SMTEncoding_Util.mkForall uu____15296 in
        (uu____15295, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15288 in
    let uu____15342 =
      let uu____15345 =
        let uu____15346 =
          let uu____15353 =
            let uu____15354 =
              let uu____15365 =
                let uu____15366 =
                  let uu____15371 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x in
                  (typing_pred, uu____15371) in
                FStar_SMTEncoding_Util.mkImp uu____15366 in
              ([[typing_pred]], [xx], uu____15365) in
            mkForall_fuel uu____15354 in
          (uu____15353, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15346 in
      [uu____15345] in
    uu____15287 :: uu____15342 in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____15424 =
      let uu____15425 =
        let uu____15432 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____15432, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15425 in
    [uu____15424] in
  let mk_and_interp env conj uu____15444 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15469 =
      let uu____15470 =
        let uu____15477 =
          let uu____15478 =
            let uu____15489 =
              let uu____15490 =
                let uu____15495 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____15495, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15490 in
            ([[l_and_a_b]], [aa; bb], uu____15489) in
          FStar_SMTEncoding_Util.mkForall uu____15478 in
        (uu____15477, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15470 in
    [uu____15469] in
  let mk_or_interp env disj uu____15533 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15558 =
      let uu____15559 =
        let uu____15566 =
          let uu____15567 =
            let uu____15578 =
              let uu____15579 =
                let uu____15584 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____15584, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15579 in
            ([[l_or_a_b]], [aa; bb], uu____15578) in
          FStar_SMTEncoding_Util.mkForall uu____15567 in
        (uu____15566, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15559 in
    [uu____15558] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____15647 =
      let uu____15648 =
        let uu____15655 =
          let uu____15656 =
            let uu____15667 =
              let uu____15668 =
                let uu____15673 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15673, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15668 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____15667) in
          FStar_SMTEncoding_Util.mkForall uu____15656 in
        (uu____15655, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15648 in
    [uu____15647] in
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
    let uu____15746 =
      let uu____15747 =
        let uu____15754 =
          let uu____15755 =
            let uu____15766 =
              let uu____15767 =
                let uu____15772 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15772, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15767 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____15766) in
          FStar_SMTEncoding_Util.mkForall uu____15755 in
        (uu____15754, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15747 in
    [uu____15746] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15843 =
      let uu____15844 =
        let uu____15851 =
          let uu____15852 =
            let uu____15863 =
              let uu____15864 =
                let uu____15869 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____15869, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15864 in
            ([[l_imp_a_b]], [aa; bb], uu____15863) in
          FStar_SMTEncoding_Util.mkForall uu____15852 in
        (uu____15851, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15844 in
    [uu____15843] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15932 =
      let uu____15933 =
        let uu____15940 =
          let uu____15941 =
            let uu____15952 =
              let uu____15953 =
                let uu____15958 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____15958, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15953 in
            ([[l_iff_a_b]], [aa; bb], uu____15952) in
          FStar_SMTEncoding_Util.mkForall uu____15941 in
        (uu____15940, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15933 in
    [uu____15932] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____16010 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____16010 in
    let uu____16013 =
      let uu____16014 =
        let uu____16021 =
          let uu____16022 =
            let uu____16033 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____16033) in
          FStar_SMTEncoding_Util.mkForall uu____16022 in
        (uu____16021, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16014 in
    [uu____16013] in
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
      let uu____16093 =
        let uu____16100 =
          let uu____16103 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16103] in
        ("Valid", uu____16100) in
      FStar_SMTEncoding_Util.mkApp uu____16093 in
    let uu____16106 =
      let uu____16107 =
        let uu____16114 =
          let uu____16115 =
            let uu____16126 =
              let uu____16127 =
                let uu____16132 =
                  let uu____16133 =
                    let uu____16144 =
                      let uu____16149 =
                        let uu____16152 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16152] in
                      [uu____16149] in
                    let uu____16157 =
                      let uu____16158 =
                        let uu____16163 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16163, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16158 in
                    (uu____16144, [xx1], uu____16157) in
                  FStar_SMTEncoding_Util.mkForall uu____16133 in
                (uu____16132, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16127 in
            ([[l_forall_a_b]], [aa; bb], uu____16126) in
          FStar_SMTEncoding_Util.mkForall uu____16115 in
        (uu____16114, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16107 in
    [uu____16106] in
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
      let uu____16245 =
        let uu____16252 =
          let uu____16255 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16255] in
        ("Valid", uu____16252) in
      FStar_SMTEncoding_Util.mkApp uu____16245 in
    let uu____16258 =
      let uu____16259 =
        let uu____16266 =
          let uu____16267 =
            let uu____16278 =
              let uu____16279 =
                let uu____16284 =
                  let uu____16285 =
                    let uu____16296 =
                      let uu____16301 =
                        let uu____16304 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16304] in
                      [uu____16301] in
                    let uu____16309 =
                      let uu____16310 =
                        let uu____16315 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16315, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16310 in
                    (uu____16296, [xx1], uu____16309) in
                  FStar_SMTEncoding_Util.mkExists uu____16285 in
                (uu____16284, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16279 in
            ([[l_exists_a_b]], [aa; bb], uu____16278) in
          FStar_SMTEncoding_Util.mkForall uu____16267 in
        (uu____16266, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16259 in
    [uu____16258] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____16375 =
      let uu____16376 =
        let uu____16383 =
          let uu____16384 = FStar_SMTEncoding_Term.mk_Range_const () in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____16384 range_ty in
        let uu____16385 = varops.mk_unique "typing_range_const" in
        (uu____16383, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____16385) in
      FStar_SMTEncoding_Util.mkAssume uu____16376 in
    [uu____16375] in
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
        let uu____16419 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1") in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____16419 x1 t in
      let uu____16420 =
        let uu____16431 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS) in
        ([[hastypeZ]], [xx1], uu____16431) in
      FStar_SMTEncoding_Util.mkForall uu____16420 in
    let uu____16454 =
      let uu____16455 =
        let uu____16462 =
          let uu____16463 =
            let uu____16474 = FStar_SMTEncoding_Util.mkImp (valid, body) in
            ([[inversion_t]], [tt1], uu____16474) in
          FStar_SMTEncoding_Util.mkForall uu____16463 in
        (uu____16462,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16455 in
    [uu____16454] in
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
          let uu____16798 =
            FStar_Util.find_opt
              (fun uu____16824  ->
                 match uu____16824 with
                 | (l,uu____16836) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____16798 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____16861,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____16900 = encode_function_type_as_formula t env in
        match uu____16900 with
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
              let uu____16946 =
                ((let uu____16949 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm) in
                  FStar_All.pipe_left Prims.op_Negation uu____16949) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted in
              if uu____16946
              then
                let uu____16956 = new_term_constant_and_tok_from_lid env lid in
                match uu____16956 with
                | (vname,vtok,env1) ->
                    let arg_sorts =
                      let uu____16975 =
                        let uu____16976 = FStar_Syntax_Subst.compress t_norm in
                        uu____16976.FStar_Syntax_Syntax.n in
                      match uu____16975 with
                      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____16982) ->
                          FStar_All.pipe_right binders
                            (FStar_List.map
                               (fun uu____17012  ->
                                  FStar_SMTEncoding_Term.Term_sort))
                      | uu____17017 -> [] in
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
                (let uu____17031 = prims.is lid in
                 if uu____17031
                 then
                   let vname = varops.new_fvar lid in
                   let uu____17039 = prims.mk lid vname in
                   match uu____17039 with
                   | (tok,definition) ->
                       let env1 =
                         push_free_var env lid vname
                           (FStar_Pervasives_Native.Some tok) in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims" in
                    let uu____17063 =
                      let uu____17074 = curried_arrow_formals_comp t_norm in
                      match uu____17074 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____17092 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp in
                            if uu____17092
                            then
                              let uu____17093 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___172_17096 = env.tcenv in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___172_17096.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___172_17096.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___172_17096.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___172_17096.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___172_17096.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___172_17096.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___172_17096.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___172_17096.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___172_17096.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___172_17096.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___172_17096.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___172_17096.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___172_17096.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___172_17096.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___172_17096.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___172_17096.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___172_17096.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___172_17096.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___172_17096.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___172_17096.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___172_17096.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___172_17096.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___172_17096.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___172_17096.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___172_17096.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qname_and_index =
                                       (uu___172_17096.FStar_TypeChecker_Env.qname_and_index);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___172_17096.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth =
                                       (uu___172_17096.FStar_TypeChecker_Env.synth);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___172_17096.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___172_17096.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___172_17096.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___172_17096.FStar_TypeChecker_Env.dsenv)
                                   }) comp FStar_Syntax_Syntax.U_unknown in
                              FStar_Syntax_Syntax.mk_Total uu____17093
                            else comp in
                          if encode_non_total_function_typ
                          then
                            let uu____17108 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1 in
                            (args, uu____17108)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1))) in
                    match uu____17063 with
                    | (formals,(pre_opt,res_t)) ->
                        let uu____17153 =
                          new_term_constant_and_tok_from_lid env lid in
                        (match uu____17153 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____17174 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, []) in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___144_17216  ->
                                       match uu___144_17216 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____17220 =
                                             FStar_Util.prefix vars in
                                           (match uu____17220 with
                                            | (uu____17241,(xxsym,uu____17243))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort) in
                                                let uu____17261 =
                                                  let uu____17262 =
                                                    let uu____17269 =
                                                      let uu____17270 =
                                                        let uu____17281 =
                                                          let uu____17282 =
                                                            let uu____17287 =
                                                              let uu____17288
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____17288 in
                                                            (vapp,
                                                              uu____17287) in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____17282 in
                                                        ([[vapp]], vars,
                                                          uu____17281) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17270 in
                                                    (uu____17269,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str))) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17262 in
                                                [uu____17261])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____17307 =
                                             FStar_Util.prefix vars in
                                           (match uu____17307 with
                                            | (uu____17328,(xxsym,uu____17330))
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
                                                let uu____17353 =
                                                  let uu____17354 =
                                                    let uu____17361 =
                                                      let uu____17362 =
                                                        let uu____17373 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app) in
                                                        ([[vapp]], vars,
                                                          uu____17373) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17362 in
                                                    (uu____17361,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name)) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17354 in
                                                [uu____17353])
                                       | uu____17390 -> [])) in
                             let uu____17391 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1 in
                             (match uu____17391 with
                              | (vars,guards,env',decls1,uu____17418) ->
                                  let uu____17431 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____17440 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards in
                                        (uu____17440, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____17442 =
                                          encode_formula p env' in
                                        (match uu____17442 with
                                         | (g,ds) ->
                                             let uu____17453 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards) in
                                             (uu____17453,
                                               (FStar_List.append decls1 ds))) in
                                  (match uu____17431 with
                                   | (guard,decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars in
                                       let vapp =
                                         let uu____17466 =
                                           let uu____17473 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars in
                                           (vname, uu____17473) in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____17466 in
                                       let uu____17482 =
                                         let vname_decl =
                                           let uu____17490 =
                                             let uu____17501 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____17511  ->
                                                       FStar_SMTEncoding_Term.Term_sort)) in
                                             (vname, uu____17501,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None) in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____17490 in
                                         let uu____17520 =
                                           let env2 =
                                             let uu___173_17526 = env1 in
                                             {
                                               bindings =
                                                 (uu___173_17526.bindings);
                                               depth = (uu___173_17526.depth);
                                               tcenv = (uu___173_17526.tcenv);
                                               warn = (uu___173_17526.warn);
                                               cache = (uu___173_17526.cache);
                                               nolabels =
                                                 (uu___173_17526.nolabels);
                                               use_zfuel_name =
                                                 (uu___173_17526.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___173_17526.current_module_name)
                                             } in
                                           let uu____17527 =
                                             let uu____17528 =
                                               head_normal env2 tt in
                                             Prims.op_Negation uu____17528 in
                                           if uu____17527
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm in
                                         match uu____17520 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____17543::uu____17544 ->
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
                                                     let uu____17584 =
                                                       let uu____17595 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____17595) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____17584 in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____17622 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname)) in
                                             let uu____17625 =
                                               match formals with
                                               | [] ->
                                                   let uu____17642 =
                                                     let uu____17643 =
                                                       let uu____17646 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort) in
                                                       FStar_All.pipe_left
                                                         (fun _0_43  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_43)
                                                         uu____17646 in
                                                     push_free_var env1 lid
                                                       vname uu____17643 in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____17642)
                                               | uu____17651 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None) in
                                                   let name_tok_corr =
                                                     let uu____17658 =
                                                       let uu____17665 =
                                                         let uu____17666 =
                                                           let uu____17677 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp) in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____17677) in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____17666 in
                                                       (uu____17665,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname)) in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____17658 in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       name_tok_corr;
                                                       tok_typing1]), env1) in
                                             (match uu____17625 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2)) in
                                       (match uu____17482 with
                                        | (decls2,env2) ->
                                            let uu____17720 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t in
                                              let uu____17728 =
                                                encode_term res_t1 env' in
                                              match uu____17728 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____17741 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t in
                                                  (encoded_res_t,
                                                    uu____17741, decls) in
                                            (match uu____17720 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____17752 =
                                                     let uu____17759 =
                                                       let uu____17760 =
                                                         let uu____17771 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred) in
                                                         ([[vapp]], vars,
                                                           uu____17771) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____17760 in
                                                     (uu____17759,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____17752 in
                                                 let freshness =
                                                   let uu____17787 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New) in
                                                   if uu____17787
                                                   then
                                                     let uu____17792 =
                                                       let uu____17793 =
                                                         let uu____17804 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd) in
                                                         let uu____17815 =
                                                           varops.next_id () in
                                                         (vname, uu____17804,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____17815) in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____17793 in
                                                     let uu____17818 =
                                                       let uu____17821 =
                                                         pretype_axiom env2
                                                           vapp vars in
                                                       [uu____17821] in
                                                     uu____17792 ::
                                                       uu____17818
                                                   else [] in
                                                 let g =
                                                   let uu____17826 =
                                                     let uu____17829 =
                                                       let uu____17832 =
                                                         let uu____17835 =
                                                           let uu____17838 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars in
                                                           typingAx ::
                                                             uu____17838 in
                                                         FStar_List.append
                                                           freshness
                                                           uu____17835 in
                                                       FStar_List.append
                                                         decls3 uu____17832 in
                                                     FStar_List.append decls2
                                                       uu____17829 in
                                                   FStar_List.append decls11
                                                     uu____17826 in
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
          let uu____17873 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____17873 with
          | FStar_Pervasives_Native.None  ->
              let uu____17910 = encode_free_var false env x t t_norm [] in
              (match uu____17910 with
               | (decls,env1) ->
                   let uu____17937 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____17937 with
                    | (n1,x',uu____17964) -> ((n1, x'), decls, env1)))
          | FStar_Pervasives_Native.Some (n1,x1,uu____17985) ->
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
            let uu____18045 =
              encode_free_var uninterpreted env lid t tt quals in
            match uu____18045 with
            | (decls,env1) ->
                let uu____18064 = FStar_Syntax_Util.is_smt_lemma t in
                if uu____18064
                then
                  let uu____18071 =
                    let uu____18074 = encode_smt_lemma env1 lid tt in
                    FStar_List.append decls uu____18074 in
                  (uu____18071, env1)
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
             (fun uu____18129  ->
                fun lb  ->
                  match uu____18129 with
                  | (decls,env1) ->
                      let uu____18149 =
                        let uu____18156 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val false env1 uu____18156
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____18149 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____18178 = FStar_Syntax_Util.head_and_args t in
    match uu____18178 with
    | (hd1,args) ->
        let uu____18215 =
          let uu____18216 = FStar_Syntax_Util.un_uinst hd1 in
          uu____18216.FStar_Syntax_Syntax.n in
        (match uu____18215 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____18220,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____18239 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____18264  ->
      fun quals  ->
        match uu____18264 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____18340 = FStar_Util.first_N nbinders formals in
              match uu____18340 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____18421  ->
                         fun uu____18422  ->
                           match (uu____18421, uu____18422) with
                           | ((formal,uu____18440),(binder,uu____18442)) ->
                               let uu____18451 =
                                 let uu____18458 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____18458) in
                               FStar_Syntax_Syntax.NT uu____18451) formals1
                      binders in
                  let extra_formals1 =
                    let uu____18466 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____18497  ->
                              match uu____18497 with
                              | (x,i) ->
                                  let uu____18508 =
                                    let uu___174_18509 = x in
                                    let uu____18510 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___174_18509.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___174_18509.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____18510
                                    } in
                                  (uu____18508, i))) in
                    FStar_All.pipe_right uu____18466
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____18528 =
                      let uu____18529 = FStar_Syntax_Subst.compress body in
                      let uu____18530 =
                        let uu____18531 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____18531 in
                      FStar_Syntax_Syntax.extend_app_n uu____18529
                        uu____18530 in
                    uu____18528 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____18592 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____18592
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___175_18595 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___175_18595.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___175_18595.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___175_18595.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___175_18595.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___175_18595.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___175_18595.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___175_18595.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___175_18595.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___175_18595.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___175_18595.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___175_18595.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___175_18595.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___175_18595.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___175_18595.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___175_18595.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___175_18595.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___175_18595.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___175_18595.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___175_18595.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___175_18595.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___175_18595.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___175_18595.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___175_18595.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___175_18595.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___175_18595.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___175_18595.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___175_18595.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___175_18595.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___175_18595.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___175_18595.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___175_18595.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___175_18595.FStar_TypeChecker_Env.dsenv)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____18628 = FStar_Syntax_Util.abs_formals e in
                match uu____18628 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____18692::uu____18693 ->
                         let uu____18708 =
                           let uu____18709 =
                             let uu____18712 =
                               FStar_Syntax_Subst.compress t_norm1 in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____18712 in
                           uu____18709.FStar_Syntax_Syntax.n in
                         (match uu____18708 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____18755 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____18755 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____18797 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____18797
                                   then
                                     let uu____18832 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____18832 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____18926  ->
                                                   fun uu____18927  ->
                                                     match (uu____18926,
                                                             uu____18927)
                                                     with
                                                     | ((x,uu____18945),
                                                        (b,uu____18947)) ->
                                                         let uu____18956 =
                                                           let uu____18963 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____18963) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____18956)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____18965 =
                                            let uu____18986 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____18986) in
                                          (uu____18965, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____19054 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____19054 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____19143) ->
                              let uu____19148 =
                                let uu____19169 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                FStar_Pervasives_Native.fst uu____19169 in
                              (uu____19148, true)
                          | uu____19234 when Prims.op_Negation norm1 ->
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
                          | uu____19236 ->
                              let uu____19237 =
                                let uu____19238 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____19239 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____19238
                                  uu____19239 in
                              failwith uu____19237)
                     | uu____19264 ->
                         let uu____19265 =
                           let uu____19266 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____19266.FStar_Syntax_Syntax.n in
                         (match uu____19265 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____19311 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____19311 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____19343 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____19343 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____19426 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____19482 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____19482
               then encode_top_level_vals env bindings quals
               else
                 (let uu____19494 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____19588  ->
                            fun lb  ->
                              match uu____19588 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____19683 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____19683
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____19686 =
                                      let uu____19701 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____19701
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____19686 with
                                    | (tok,decl,env2) ->
                                        let uu____19747 =
                                          let uu____19760 =
                                            let uu____19771 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____19771, tok) in
                                          uu____19760 :: toks in
                                        (uu____19747, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____19494 with
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
                        | uu____19954 ->
                            if curry
                            then
                              (match ftok with
                               | FStar_Pervasives_Native.Some ftok1 ->
                                   mk_Apply ftok1 vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____19962 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____19962 vars)
                            else
                              (let uu____19964 =
                                 let uu____19971 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____19971) in
                               FStar_SMTEncoding_Util.mkApp uu____19964) in
                      let encode_non_rec_lbdef bindings1 typs2 toks2 env2 =
                        match (bindings1, typs2, toks2) with
                        | ({ FStar_Syntax_Syntax.lbname = uu____20053;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____20055;
                             FStar_Syntax_Syntax.lbeff = uu____20056;
                             FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                           (flid_fv,(f,ftok))::[]) ->
                            let flid =
                              (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                            let uu____20119 =
                              let uu____20126 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.tcenv uvs [e; t_norm] in
                              match uu____20126 with
                              | (tcenv',uu____20144,e_t) ->
                                  let uu____20150 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____20161 -> failwith "Impossible" in
                                  (match uu____20150 with
                                   | (e1,t_norm1) ->
                                       ((let uu___178_20177 = env2 in
                                         {
                                           bindings =
                                             (uu___178_20177.bindings);
                                           depth = (uu___178_20177.depth);
                                           tcenv = tcenv';
                                           warn = (uu___178_20177.warn);
                                           cache = (uu___178_20177.cache);
                                           nolabels =
                                             (uu___178_20177.nolabels);
                                           use_zfuel_name =
                                             (uu___178_20177.use_zfuel_name);
                                           encode_non_total_function_typ =
                                             (uu___178_20177.encode_non_total_function_typ);
                                           current_module_name =
                                             (uu___178_20177.current_module_name)
                                         }), e1, t_norm1)) in
                            (match uu____20119 with
                             | (env',e1,t_norm1) ->
                                 let uu____20187 =
                                   destruct_bound_function flid t_norm1 e1 in
                                 (match uu____20187 with
                                  | ((binders,body,uu____20208,uu____20209),curry)
                                      ->
                                      ((let uu____20220 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding") in
                                        if uu____20220
                                        then
                                          let uu____20221 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders in
                                          let uu____20222 =
                                            FStar_Syntax_Print.term_to_string
                                              body in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____20221 uu____20222
                                        else ());
                                       (let uu____20224 =
                                          encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env' in
                                        match uu____20224 with
                                        | (vars,guards,env'1,binder_decls,uu____20251)
                                            ->
                                            let body1 =
                                              let uu____20265 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.tcenv t_norm1 in
                                              if uu____20265
                                              then
                                                FStar_TypeChecker_Util.reify_body
                                                  env'1.tcenv body
                                              else body in
                                            let app =
                                              mk_app1 curry f ftok vars in
                                            let uu____20268 =
                                              let uu____20277 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic) in
                                              if uu____20277
                                              then
                                                let uu____20288 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app in
                                                let uu____20289 =
                                                  encode_formula body1 env'1 in
                                                (uu____20288, uu____20289)
                                              else
                                                (let uu____20299 =
                                                   encode_term body1 env'1 in
                                                 (app, uu____20299)) in
                                            (match uu____20268 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____20322 =
                                                     let uu____20329 =
                                                       let uu____20330 =
                                                         let uu____20341 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2) in
                                                         ([[app1]], vars,
                                                           uu____20341) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____20330 in
                                                     let uu____20352 =
                                                       let uu____20355 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str in
                                                       FStar_Pervasives_Native.Some
                                                         uu____20355 in
                                                     (uu____20329,
                                                       uu____20352,
                                                       (Prims.strcat
                                                          "equation_" f)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____20322 in
                                                 let uu____20358 =
                                                   let uu____20361 =
                                                     let uu____20364 =
                                                       let uu____20367 =
                                                         let uu____20370 =
                                                           primitive_type_axioms
                                                             env2.tcenv flid
                                                             f app1 in
                                                         FStar_List.append
                                                           [eqn] uu____20370 in
                                                       FStar_List.append
                                                         decls2 uu____20367 in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____20364 in
                                                   FStar_List.append decls1
                                                     uu____20361 in
                                                 (uu____20358, env2))))))
                        | uu____20375 -> failwith "Impossible" in
                      let encode_rec_lbdefs bindings1 typs2 toks2 env2 =
                        let fuel =
                          let uu____20460 = varops.fresh "fuel" in
                          (uu____20460, FStar_SMTEncoding_Term.Fuel_sort) in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                        let env0 = env2 in
                        let uu____20463 =
                          FStar_All.pipe_right toks2
                            (FStar_List.fold_left
                               (fun uu____20551  ->
                                  fun uu____20552  ->
                                    match (uu____20551, uu____20552) with
                                    | ((gtoks,env3),(flid_fv,(f,ftok))) ->
                                        let flid =
                                          (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                        let g =
                                          let uu____20700 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented" in
                                          varops.new_fvar uu____20700 in
                                        let gtok =
                                          let uu____20702 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token" in
                                          varops.new_fvar uu____20702 in
                                        let env4 =
                                          let uu____20704 =
                                            let uu____20707 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm]) in
                                            FStar_All.pipe_left
                                              (fun _0_44  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_44) uu____20707 in
                                          push_free_var env3 flid gtok
                                            uu____20704 in
                                        (((flid, f, ftok, g, gtok) :: gtoks),
                                          env4)) ([], env2)) in
                        match uu____20463 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks in
                            let encode_one_binding env01 uu____20863 t_norm
                              uu____20865 =
                              match (uu____20863, uu____20865) with
                              | ((flid,f,ftok,g,gtok),{
                                                        FStar_Syntax_Syntax.lbname
                                                          = lbn;
                                                        FStar_Syntax_Syntax.lbunivs
                                                          = uvs;
                                                        FStar_Syntax_Syntax.lbtyp
                                                          = uu____20909;
                                                        FStar_Syntax_Syntax.lbeff
                                                          = uu____20910;
                                                        FStar_Syntax_Syntax.lbdef
                                                          = e;_})
                                  ->
                                  let uu____20938 =
                                    let uu____20945 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.tcenv uvs [e; t_norm] in
                                    match uu____20945 with
                                    | (tcenv',uu____20967,e_t) ->
                                        let uu____20973 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____20984 ->
                                              failwith "Impossible" in
                                        (match uu____20973 with
                                         | (e1,t_norm1) ->
                                             ((let uu___179_21000 = env3 in
                                               {
                                                 bindings =
                                                   (uu___179_21000.bindings);
                                                 depth =
                                                   (uu___179_21000.depth);
                                                 tcenv = tcenv';
                                                 warn = (uu___179_21000.warn);
                                                 cache =
                                                   (uu___179_21000.cache);
                                                 nolabels =
                                                   (uu___179_21000.nolabels);
                                                 use_zfuel_name =
                                                   (uu___179_21000.use_zfuel_name);
                                                 encode_non_total_function_typ
                                                   =
                                                   (uu___179_21000.encode_non_total_function_typ);
                                                 current_module_name =
                                                   (uu___179_21000.current_module_name)
                                               }), e1, t_norm1)) in
                                  (match uu____20938 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____21015 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding") in
                                         if uu____21015
                                         then
                                           let uu____21016 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn in
                                           let uu____21017 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1 in
                                           let uu____21018 =
                                             FStar_Syntax_Print.term_to_string
                                               e1 in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____21016 uu____21017
                                             uu____21018
                                         else ());
                                        (let uu____21020 =
                                           destruct_bound_function flid
                                             t_norm1 e1 in
                                         match uu____21020 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____21057 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding") in
                                               if uu____21057
                                               then
                                                 let uu____21058 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders in
                                                 let uu____21059 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body in
                                                 let uu____21060 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals in
                                                 let uu____21061 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____21058 uu____21059
                                                   uu____21060 uu____21061
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____21065 =
                                                 encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env' in
                                               match uu____21065 with
                                               | (vars,guards,env'1,binder_decls,uu____21096)
                                                   ->
                                                   let decl_g =
                                                     let uu____21110 =
                                                       let uu____21121 =
                                                         let uu____21124 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____21124 in
                                                       (g, uu____21121,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name")) in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____21110 in
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
                                                     let uu____21149 =
                                                       let uu____21156 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars in
                                                       (f, uu____21156) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21149 in
                                                   let gsapp =
                                                     let uu____21166 =
                                                       let uu____21173 =
                                                         let uu____21176 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm]) in
                                                         uu____21176 ::
                                                           vars_tm in
                                                       (g, uu____21173) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21166 in
                                                   let gmax =
                                                     let uu____21182 =
                                                       let uu____21189 =
                                                         let uu____21192 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", []) in
                                                         uu____21192 ::
                                                           vars_tm in
                                                       (g, uu____21189) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21182 in
                                                   let body1 =
                                                     let uu____21198 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.tcenv t_norm1 in
                                                     if uu____21198
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.tcenv body
                                                     else body in
                                                   let uu____21200 =
                                                     encode_term body1 env'1 in
                                                   (match uu____21200 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____21218 =
                                                            let uu____21225 =
                                                              let uu____21226
                                                                =
                                                                let uu____21241
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
                                                                  uu____21241) in
                                                              FStar_SMTEncoding_Util.mkForall'
                                                                uu____21226 in
                                                            let uu____21262 =
                                                              let uu____21265
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  flid.FStar_Ident.str in
                                                              FStar_Pervasives_Native.Some
                                                                uu____21265 in
                                                            (uu____21225,
                                                              uu____21262,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21218 in
                                                        let eqn_f =
                                                          let uu____21269 =
                                                            let uu____21276 =
                                                              let uu____21277
                                                                =
                                                                let uu____21288
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____21288) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21277 in
                                                            (uu____21276,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21269 in
                                                        let eqn_g' =
                                                          let uu____21302 =
                                                            let uu____21309 =
                                                              let uu____21310
                                                                =
                                                                let uu____21321
                                                                  =
                                                                  let uu____21322
                                                                    =
                                                                    let uu____21327
                                                                    =
                                                                    let uu____21328
                                                                    =
                                                                    let uu____21335
                                                                    =
                                                                    let uu____21338
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____21338
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____21335) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____21328 in
                                                                    (gsapp,
                                                                    uu____21327) in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____21322 in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____21321) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21310 in
                                                            (uu____21309,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21302 in
                                                        let uu____21361 =
                                                          let uu____21370 =
                                                            encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02 in
                                                          match uu____21370
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____21399)
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
                                                                  let uu____21424
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                  mk_Apply
                                                                    uu____21424
                                                                    (fuel ::
                                                                    vars1) in
                                                                let uu____21429
                                                                  =
                                                                  let uu____21436
                                                                    =
                                                                    let uu____21437
                                                                    =
                                                                    let uu____21448
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21448) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21437 in
                                                                  (uu____21436,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____21429 in
                                                              let uu____21469
                                                                =
                                                                let uu____21476
                                                                  =
                                                                  encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp in
                                                                match uu____21476
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____21489
                                                                    =
                                                                    let uu____21492
                                                                    =
                                                                    let uu____21493
                                                                    =
                                                                    let uu____21500
                                                                    =
                                                                    let uu____21501
                                                                    =
                                                                    let uu____21512
                                                                    =
                                                                    let uu____21513
                                                                    =
                                                                    let uu____21518
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____21518,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____21513 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21512) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21501 in
                                                                    (uu____21500,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____21493 in
                                                                    [uu____21492] in
                                                                    (d3,
                                                                    uu____21489) in
                                                              (match uu____21469
                                                               with
                                                               | (aux_decls,typing_corr)
                                                                   ->
                                                                   ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                        (match uu____21361
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
                            let uu____21583 =
                              let uu____21596 =
                                FStar_List.zip3 gtoks1 typs2 bindings1 in
                              FStar_List.fold_left
                                (fun uu____21675  ->
                                   fun uu____21676  ->
                                     match (uu____21675, uu____21676) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____21831 =
                                           encode_one_binding env01 gtok ty
                                             lb in
                                         (match uu____21831 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____21596 in
                            (match uu____21583 with
                             | (decls2,eqns,env01) ->
                                 let uu____21904 =
                                   let isDeclFun uu___145_21916 =
                                     match uu___145_21916 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____21917 -> true
                                     | uu____21928 -> false in
                                   let uu____21929 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten in
                                   FStar_All.pipe_right uu____21929
                                     (FStar_List.partition isDeclFun) in
                                 (match uu____21904 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01))) in
                      let uu____21969 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___146_21973  ->
                                 match uu___146_21973 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____21974 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____21980 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____21980))) in
                      if uu____21969
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
                   let uu____22032 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____22032
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
        let uu____22081 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____22081 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str in
      let uu____22085 = encode_sigelt' env se in
      match uu____22085 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____22101 =
                  let uu____22102 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____22102 in
                [uu____22101]
            | uu____22103 ->
                let uu____22104 =
                  let uu____22107 =
                    let uu____22108 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____22108 in
                  uu____22107 :: g in
                let uu____22109 =
                  let uu____22112 =
                    let uu____22113 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____22113 in
                  [uu____22112] in
                FStar_List.append uu____22104 uu____22109 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____22126 =
          let uu____22127 = FStar_Syntax_Subst.compress t in
          uu____22127.FStar_Syntax_Syntax.n in
        match uu____22126 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22131)) -> s = "opaque_to_smt"
        | uu____22132 -> false in
      let is_uninterpreted_by_smt t =
        let uu____22137 =
          let uu____22138 = FStar_Syntax_Subst.compress t in
          uu____22138.FStar_Syntax_Syntax.n in
        match uu____22137 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22142)) -> s = "uninterpreted_by_smt"
        | uu____22143 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____22148 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____22153 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____22156 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____22159 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____22174 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____22178 =
            let uu____22179 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____22179 Prims.op_Negation in
          if uu____22178
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____22205 ->
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
               let uu____22225 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____22225 with
               | (aname,atok,env2) ->
                   let uu____22241 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____22241 with
                    | (formals,uu____22259) ->
                        let uu____22272 =
                          let uu____22277 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____22277 env2 in
                        (match uu____22272 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____22289 =
                                 let uu____22290 =
                                   let uu____22301 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____22317  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____22301,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____22290 in
                               [uu____22289;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))] in
                             let uu____22330 =
                               let aux uu____22382 uu____22383 =
                                 match (uu____22382, uu____22383) with
                                 | ((bv,uu____22435),(env3,acc_sorts,acc)) ->
                                     let uu____22473 = gen_term_var env3 bv in
                                     (match uu____22473 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____22330 with
                              | (uu____22545,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____22568 =
                                      let uu____22575 =
                                        let uu____22576 =
                                          let uu____22587 =
                                            let uu____22588 =
                                              let uu____22593 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____22593) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____22588 in
                                          ([[app]], xs_sorts, uu____22587) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22576 in
                                      (uu____22575,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22568 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____22613 =
                                      let uu____22620 =
                                        let uu____22621 =
                                          let uu____22632 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____22632) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22621 in
                                      (uu____22620,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22613 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____22651 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____22651 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22679,uu____22680)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____22681 = new_term_constant_and_tok_from_lid env lid in
          (match uu____22681 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22698,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____22704 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___147_22708  ->
                      match uu___147_22708 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____22709 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____22714 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____22715 -> false)) in
            Prims.op_Negation uu____22704 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____22724 =
               let uu____22731 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt) in
               encode_top_level_val uu____22731 env fv t quals in
             match uu____22724 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____22746 =
                   let uu____22749 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____22749 in
                 (uu____22746, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____22757 = FStar_Syntax_Subst.open_univ_vars us f in
          (match uu____22757 with
           | (uu____22766,f1) ->
               let uu____22768 = encode_formula f1 env in
               (match uu____22768 with
                | (f2,decls) ->
                    let g =
                      let uu____22782 =
                        let uu____22783 =
                          let uu____22790 =
                            let uu____22793 =
                              let uu____22794 =
                                FStar_Syntax_Print.lid_to_string l in
                              FStar_Util.format1 "Assumption: %s" uu____22794 in
                            FStar_Pervasives_Native.Some uu____22793 in
                          let uu____22795 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str) in
                          (f2, uu____22790, uu____22795) in
                        FStar_SMTEncoding_Util.mkAssume uu____22783 in
                      [uu____22782] in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____22801) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs in
          let uu____22813 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____22831 =
                       let uu____22834 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____22834.FStar_Syntax_Syntax.fv_name in
                     uu____22831.FStar_Syntax_Syntax.v in
                   let uu____22835 =
                     let uu____22836 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____22836 in
                   if uu____22835
                   then
                     let val_decl =
                       let uu___182_22864 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___182_22864.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___182_22864.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___182_22864.FStar_Syntax_Syntax.sigattrs)
                       } in
                     let uu____22869 = encode_sigelt' env1 val_decl in
                     match uu____22869 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
          (match uu____22813 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____22897,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____22899;
                          FStar_Syntax_Syntax.lbtyp = uu____22900;
                          FStar_Syntax_Syntax.lbeff = uu____22901;
                          FStar_Syntax_Syntax.lbdef = uu____22902;_}::[]),uu____22903)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____22922 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____22922 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____22951 =
                   let uu____22954 =
                     let uu____22955 =
                       let uu____22962 =
                         let uu____22963 =
                           let uu____22974 =
                             let uu____22975 =
                               let uu____22980 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x]) in
                               (valid_b2t_x, uu____22980) in
                             FStar_SMTEncoding_Util.mkEq uu____22975 in
                           ([[b2t_x]], [xx], uu____22974) in
                         FStar_SMTEncoding_Util.mkForall uu____22963 in
                       (uu____22962,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____22955 in
                   [uu____22954] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____22951 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____23013,uu____23014) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___148_23023  ->
                  match uu___148_23023 with
                  | FStar_Syntax_Syntax.Discriminator uu____23024 -> true
                  | uu____23025 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____23028,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____23039 =
                     let uu____23040 = FStar_List.hd l.FStar_Ident.ns in
                     uu____23040.FStar_Ident.idText in
                   uu____23039 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___149_23044  ->
                     match uu___149_23044 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____23045 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____23049) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___150_23066  ->
                  match uu___150_23066 with
                  | FStar_Syntax_Syntax.Projector uu____23067 -> true
                  | uu____23072 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____23075 = try_lookup_free_var env l in
          (match uu____23075 with
           | FStar_Pervasives_Native.Some uu____23082 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___183_23086 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___183_23086.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___183_23086.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___183_23086.FStar_Syntax_Syntax.sigattrs)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____23093) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____23111) ->
          let uu____23120 = encode_sigelts env ses in
          (match uu____23120 with
           | (g,env1) ->
               let uu____23137 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___151_23160  ->
                         match uu___151_23160 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____23161;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____23162;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____23163;_}
                             -> false
                         | uu____23166 -> true)) in
               (match uu____23137 with
                | (g',inversions) ->
                    let uu____23181 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___152_23202  ->
                              match uu___152_23202 with
                              | FStar_SMTEncoding_Term.DeclFun uu____23203 ->
                                  true
                              | uu____23214 -> false)) in
                    (match uu____23181 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____23232,tps,k,uu____23235,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___153_23252  ->
                    match uu___153_23252 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____23253 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____23262 = c in
              match uu____23262 with
              | (name,args,uu____23267,uu____23268,uu____23269) ->
                  let uu____23274 =
                    let uu____23275 =
                      let uu____23286 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____23303  ->
                                match uu____23303 with
                                | (uu____23310,sort,uu____23312) -> sort)) in
                      (name, uu____23286, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____23275 in
                  [uu____23274]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____23339 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____23345 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____23345 FStar_Option.isNone)) in
            if uu____23339
            then []
            else
              (let uu____23377 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____23377 with
               | (xxsym,xx) ->
                   let uu____23386 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____23425  ->
                             fun l  ->
                               match uu____23425 with
                               | (out,decls) ->
                                   let uu____23445 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____23445 with
                                    | (uu____23456,data_t) ->
                                        let uu____23458 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____23458 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____23504 =
                                                 let uu____23505 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____23505.FStar_Syntax_Syntax.n in
                                               match uu____23504 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____23516,indices) ->
                                                   indices
                                               | uu____23538 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____23562  ->
                                                         match uu____23562
                                                         with
                                                         | (x,uu____23568) ->
                                                             let uu____23569
                                                               =
                                                               let uu____23570
                                                                 =
                                                                 let uu____23577
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____23577,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____23570 in
                                                             push_term_var
                                                               env1 x
                                                               uu____23569)
                                                    env) in
                                             let uu____23580 =
                                               encode_args indices env1 in
                                             (match uu____23580 with
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
                                                      let uu____23606 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____23622
                                                                 =
                                                                 let uu____23627
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____23627,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____23622)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____23606
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____23630 =
                                                      let uu____23631 =
                                                        let uu____23636 =
                                                          let uu____23637 =
                                                            let uu____23642 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____23642,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____23637 in
                                                        (out, uu____23636) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____23631 in
                                                    (uu____23630,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____23386 with
                    | (data_ax,decls) ->
                        let uu____23655 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____23655 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____23666 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____23666 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____23670 =
                                 let uu____23677 =
                                   let uu____23678 =
                                     let uu____23689 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____23704 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____23689,
                                       uu____23704) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____23678 in
                                 let uu____23719 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____23677,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____23719) in
                               FStar_SMTEncoding_Util.mkAssume uu____23670 in
                             FStar_List.append decls [fuel_guarded_inversion]))) in
          let uu____23722 =
            let uu____23735 =
              let uu____23736 = FStar_Syntax_Subst.compress k in
              uu____23736.FStar_Syntax_Syntax.n in
            match uu____23735 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____23781 -> (tps, k) in
          (match uu____23722 with
           | (formals,res) ->
               let uu____23804 = FStar_Syntax_Subst.open_term formals res in
               (match uu____23804 with
                | (formals1,res1) ->
                    let uu____23815 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env in
                    (match uu____23815 with
                     | (vars,guards,env',binder_decls,uu____23840) ->
                         let uu____23853 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____23853 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____23872 =
                                  let uu____23879 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____23879) in
                                FStar_SMTEncoding_Util.mkApp uu____23872 in
                              let uu____23888 =
                                let tname_decl =
                                  let uu____23898 =
                                    let uu____23899 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____23931  ->
                                              match uu____23931 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____23944 = varops.next_id () in
                                    (tname, uu____23899,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____23944, false) in
                                  constructor_or_logic_type_decl uu____23898 in
                                let uu____23953 =
                                  match vars with
                                  | [] ->
                                      let uu____23966 =
                                        let uu____23967 =
                                          let uu____23970 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_45  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_45) uu____23970 in
                                        push_free_var env1 t tname
                                          uu____23967 in
                                      ([], uu____23966)
                                  | uu____23977 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token")) in
                                      let ttok_fresh =
                                        let uu____23986 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____23986 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____24000 =
                                          let uu____24007 =
                                            let uu____24008 =
                                              let uu____24023 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____24023) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____24008 in
                                          (uu____24007,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____24000 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____23953 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____23888 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____24063 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp in
                                     match uu____24063 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____24081 =
                                               let uu____24082 =
                                                 let uu____24089 =
                                                   let uu____24090 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____24090 in
                                                 (uu____24089,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24082 in
                                             [uu____24081]
                                           else [] in
                                         let uu____24094 =
                                           let uu____24097 =
                                             let uu____24100 =
                                               let uu____24101 =
                                                 let uu____24108 =
                                                   let uu____24109 =
                                                     let uu____24120 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____24120) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____24109 in
                                                 (uu____24108,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24101 in
                                             [uu____24100] in
                                           FStar_List.append karr uu____24097 in
                                         FStar_List.append decls1 uu____24094 in
                                   let aux =
                                     let uu____24136 =
                                       let uu____24139 =
                                         inversion_axioms tapp vars in
                                       let uu____24142 =
                                         let uu____24145 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____24145] in
                                       FStar_List.append uu____24139
                                         uu____24142 in
                                     FStar_List.append kindingAx uu____24136 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24152,uu____24153,uu____24154,uu____24155,uu____24156)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24164,t,uu____24166,n_tps,uu____24168) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____24176 = new_term_constant_and_tok_from_lid env d in
          (match uu____24176 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____24193 = FStar_Syntax_Util.arrow_formals t in
               (match uu____24193 with
                | (formals,t_res) ->
                    let uu____24228 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____24228 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____24242 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1 in
                         (match uu____24242 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____24312 =
                                            mk_term_projector_name d x in
                                          (uu____24312,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____24314 =
                                  let uu____24333 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____24333, true) in
                                FStar_All.pipe_right uu____24314
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
                              let uu____24372 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm in
                              (match uu____24372 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____24384::uu____24385 ->
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
                                         let uu____24430 =
                                           let uu____24441 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____24441) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____24430
                                     | uu____24466 -> tok_typing in
                                   let uu____24475 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1 in
                                   (match uu____24475 with
                                    | (vars',guards',env'',decls_formals,uu____24500)
                                        ->
                                        let uu____24513 =
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
                                        (match uu____24513 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____24544 ->
                                                   let uu____24551 =
                                                     let uu____24552 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____24552 in
                                                   [uu____24551] in
                                             let encode_elim uu____24562 =
                                               let uu____24563 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____24563 with
                                               | (head1,args) ->
                                                   let uu____24606 =
                                                     let uu____24607 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____24607.FStar_Syntax_Syntax.n in
                                                   (match uu____24606 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____24617;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____24618;_},uu____24619)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____24625 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____24625
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
                                                                 | uu____24668
                                                                    ->
                                                                    let uu____24669
                                                                    =
                                                                    let uu____24670
                                                                    =
                                                                    let uu____24675
                                                                    =
                                                                    let uu____24676
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24676 in
                                                                    (uu____24675,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____24670 in
                                                                    FStar_Exn.raise
                                                                    uu____24669 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____24692
                                                                    =
                                                                    let uu____24693
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24693 in
                                                                    if
                                                                    uu____24692
                                                                    then
                                                                    let uu____24706
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____24706]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____24708
                                                               =
                                                               let uu____24721
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____24771
                                                                     ->
                                                                    fun
                                                                    uu____24772
                                                                     ->
                                                                    match 
                                                                    (uu____24771,
                                                                    uu____24772)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____24867
                                                                    =
                                                                    let uu____24874
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____24874 in
                                                                    (match uu____24867
                                                                    with
                                                                    | 
                                                                    (uu____24887,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____24895
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____24895
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____24897
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____24897
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
                                                                 uu____24721 in
                                                             (match uu____24708
                                                              with
                                                              | (uu____24912,arg_vars,elim_eqns_or_guards,uu____24915)
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
                                                                    let uu____24945
                                                                    =
                                                                    let uu____24952
                                                                    =
                                                                    let uu____24953
                                                                    =
                                                                    let uu____24964
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____24975
                                                                    =
                                                                    let uu____24976
                                                                    =
                                                                    let uu____24981
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____24981) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24976 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24964,
                                                                    uu____24975) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24953 in
                                                                    (uu____24952,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24945 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25004
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____25004,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____25006
                                                                    =
                                                                    let uu____25013
                                                                    =
                                                                    let uu____25014
                                                                    =
                                                                    let uu____25025
                                                                    =
                                                                    let uu____25030
                                                                    =
                                                                    let uu____25033
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____25033] in
                                                                    [uu____25030] in
                                                                    let uu____25038
                                                                    =
                                                                    let uu____25039
                                                                    =
                                                                    let uu____25044
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25045
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25044,
                                                                    uu____25045) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25039 in
                                                                    (uu____25025,
                                                                    [x],
                                                                    uu____25038) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25014 in
                                                                    let uu____25064
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____25013,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25064) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25006
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25071
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
                                                                    (let uu____25099
                                                                    =
                                                                    let uu____25100
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25100
                                                                    dapp1 in
                                                                    [uu____25099]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25071
                                                                    FStar_List.flatten in
                                                                    let uu____25107
                                                                    =
                                                                    let uu____25114
                                                                    =
                                                                    let uu____25115
                                                                    =
                                                                    let uu____25126
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25137
                                                                    =
                                                                    let uu____25138
                                                                    =
                                                                    let uu____25143
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25143) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25138 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25126,
                                                                    uu____25137) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25115 in
                                                                    (uu____25114,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25107) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____25164 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____25164
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
                                                                 | uu____25207
                                                                    ->
                                                                    let uu____25208
                                                                    =
                                                                    let uu____25209
                                                                    =
                                                                    let uu____25214
                                                                    =
                                                                    let uu____25215
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____25215 in
                                                                    (uu____25214,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____25209 in
                                                                    FStar_Exn.raise
                                                                    uu____25208 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____25231
                                                                    =
                                                                    let uu____25232
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____25232 in
                                                                    if
                                                                    uu____25231
                                                                    then
                                                                    let uu____25245
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____25245]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____25247
                                                               =
                                                               let uu____25260
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____25310
                                                                     ->
                                                                    fun
                                                                    uu____25311
                                                                     ->
                                                                    match 
                                                                    (uu____25310,
                                                                    uu____25311)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25406
                                                                    =
                                                                    let uu____25413
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25413 in
                                                                    (match uu____25406
                                                                    with
                                                                    | 
                                                                    (uu____25426,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25434
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____25434
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25436
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____25436
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
                                                                 uu____25260 in
                                                             (match uu____25247
                                                              with
                                                              | (uu____25451,arg_vars,elim_eqns_or_guards,uu____25454)
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
                                                                    let uu____25484
                                                                    =
                                                                    let uu____25491
                                                                    =
                                                                    let uu____25492
                                                                    =
                                                                    let uu____25503
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25514
                                                                    =
                                                                    let uu____25515
                                                                    =
                                                                    let uu____25520
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____25520) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25515 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25503,
                                                                    uu____25514) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25492 in
                                                                    (uu____25491,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25484 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25543
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____25543,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____25545
                                                                    =
                                                                    let uu____25552
                                                                    =
                                                                    let uu____25553
                                                                    =
                                                                    let uu____25564
                                                                    =
                                                                    let uu____25569
                                                                    =
                                                                    let uu____25572
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____25572] in
                                                                    [uu____25569] in
                                                                    let uu____25577
                                                                    =
                                                                    let uu____25578
                                                                    =
                                                                    let uu____25583
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25584
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25583,
                                                                    uu____25584) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25578 in
                                                                    (uu____25564,
                                                                    [x],
                                                                    uu____25577) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25553 in
                                                                    let uu____25603
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____25552,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25603) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25545
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25610
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
                                                                    (let uu____25638
                                                                    =
                                                                    let uu____25639
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25639
                                                                    dapp1 in
                                                                    [uu____25638]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25610
                                                                    FStar_List.flatten in
                                                                    let uu____25646
                                                                    =
                                                                    let uu____25653
                                                                    =
                                                                    let uu____25654
                                                                    =
                                                                    let uu____25665
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25676
                                                                    =
                                                                    let uu____25677
                                                                    =
                                                                    let uu____25682
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25682) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25677 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25665,
                                                                    uu____25676) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25654 in
                                                                    (uu____25653,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25646) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____25701 ->
                                                        ((let uu____25703 =
                                                            let uu____25704 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____25705 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____25704
                                                              uu____25705 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____25703);
                                                         ([], []))) in
                                             let uu____25710 = encode_elim () in
                                             (match uu____25710 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____25730 =
                                                      let uu____25733 =
                                                        let uu____25736 =
                                                          let uu____25739 =
                                                            let uu____25742 =
                                                              let uu____25743
                                                                =
                                                                let uu____25754
                                                                  =
                                                                  let uu____25757
                                                                    =
                                                                    let uu____25758
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____25758 in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____25757 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____25754) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____25743 in
                                                            [uu____25742] in
                                                          let uu____25763 =
                                                            let uu____25766 =
                                                              let uu____25769
                                                                =
                                                                let uu____25772
                                                                  =
                                                                  let uu____25775
                                                                    =
                                                                    let uu____25778
                                                                    =
                                                                    let uu____25781
                                                                    =
                                                                    let uu____25782
                                                                    =
                                                                    let uu____25789
                                                                    =
                                                                    let uu____25790
                                                                    =
                                                                    let uu____25801
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____25801) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25790 in
                                                                    (uu____25789,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25782 in
                                                                    let uu____25814
                                                                    =
                                                                    let uu____25817
                                                                    =
                                                                    let uu____25818
                                                                    =
                                                                    let uu____25825
                                                                    =
                                                                    let uu____25826
                                                                    =
                                                                    let uu____25837
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____25848
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____25837,
                                                                    uu____25848) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25826 in
                                                                    (uu____25825,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25818 in
                                                                    [uu____25817] in
                                                                    uu____25781
                                                                    ::
                                                                    uu____25814 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____25778 in
                                                                  FStar_List.append
                                                                    uu____25775
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____25772 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____25769 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____25766 in
                                                          FStar_List.append
                                                            uu____25739
                                                            uu____25763 in
                                                        FStar_List.append
                                                          decls3 uu____25736 in
                                                      FStar_List.append
                                                        decls2 uu____25733 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____25730 in
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
           (fun uu____25894  ->
              fun se  ->
                match uu____25894 with
                | (g,env1) ->
                    let uu____25914 = encode_sigelt env1 se in
                    (match uu____25914 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____25973 =
        match uu____25973 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____26005 ->
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
                 ((let uu____26011 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____26011
                   then
                     let uu____26012 = FStar_Syntax_Print.bv_to_string x in
                     let uu____26013 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____26014 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____26012 uu____26013 uu____26014
                   else ());
                  (let uu____26016 = encode_term t1 env1 in
                   match uu____26016 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____26032 =
                         let uu____26039 =
                           let uu____26040 =
                             let uu____26041 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____26041
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____26040 in
                         new_term_constant_from_string env1 x uu____26039 in
                       (match uu____26032 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t in
                            let caption =
                              let uu____26057 = FStar_Options.log_queries () in
                              if uu____26057
                              then
                                let uu____26060 =
                                  let uu____26061 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____26062 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____26063 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____26061 uu____26062 uu____26063 in
                                FStar_Pervasives_Native.Some uu____26060
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____26079,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None in
                 let uu____26093 = encode_free_var false env1 fv t t_norm [] in
                 (match uu____26093 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____26116,se,uu____26118) ->
                 let uu____26123 = encode_sigelt env1 se in
                 (match uu____26123 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____26140,se) ->
                 let uu____26146 = encode_sigelt env1 se in
                 (match uu____26146 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____26163 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____26163 with | (uu____26186,decls,env1) -> (decls, env1)
let encode_labels:
  'Auu____26201 'Auu____26202 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____26202,'Auu____26201)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____26270  ->
              match uu____26270 with
              | (l,uu____26282,uu____26283) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None))) in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____26329  ->
              match uu____26329 with
              | (l,uu____26343,uu____26344) ->
                  let uu____26353 =
                    FStar_All.pipe_left
                      (fun _0_46  -> FStar_SMTEncoding_Term.Echo _0_46)
                      (FStar_Pervasives_Native.fst l) in
                  let uu____26354 =
                    let uu____26357 =
                      let uu____26358 = FStar_SMTEncoding_Util.mkFreeV l in
                      FStar_SMTEncoding_Term.Eval uu____26358 in
                    [uu____26357] in
                  uu____26353 :: uu____26354)) in
    (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____26380 =
      let uu____26383 =
        let uu____26384 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____26387 =
          let uu____26388 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____26388 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____26384;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____26387
        } in
      [uu____26383] in
    FStar_ST.op_Colon_Equals last_env uu____26380
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____26447 = FStar_ST.op_Bang last_env in
      match uu____26447 with
      | [] -> failwith "No env; call init first!"
      | e::uu____26501 ->
          let uu___184_26504 = e in
          let uu____26505 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___184_26504.bindings);
            depth = (uu___184_26504.depth);
            tcenv;
            warn = (uu___184_26504.warn);
            cache = (uu___184_26504.cache);
            nolabels = (uu___184_26504.nolabels);
            use_zfuel_name = (uu___184_26504.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___184_26504.encode_non_total_function_typ);
            current_module_name = uu____26505
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____26510 = FStar_ST.op_Bang last_env in
    match uu____26510 with
    | [] -> failwith "Empty env stack"
    | uu____26563::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____26620  ->
    let uu____26621 = FStar_ST.op_Bang last_env in
    match uu____26621 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___185_26682 = hd1 in
          {
            bindings = (uu___185_26682.bindings);
            depth = (uu___185_26682.depth);
            tcenv = (uu___185_26682.tcenv);
            warn = (uu___185_26682.warn);
            cache = refs;
            nolabels = (uu___185_26682.nolabels);
            use_zfuel_name = (uu___185_26682.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___185_26682.encode_non_total_function_typ);
            current_module_name = (uu___185_26682.current_module_name)
          } in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____26736  ->
    let uu____26737 = FStar_ST.op_Bang last_env in
    match uu____26737 with
    | [] -> failwith "Popping an empty stack"
    | uu____26790::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
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
        | (uu____26888::uu____26889,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___186_26897 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___186_26897.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___186_26897.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___186_26897.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____26898 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____26915 =
        let uu____26918 =
          let uu____26919 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____26919 in
        let uu____26920 = open_fact_db_tags env in uu____26918 :: uu____26920 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____26915
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
      let uu____26944 = encode_sigelt env se in
      match uu____26944 with
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
        let uu____26982 = FStar_Options.log_queries () in
        if uu____26982
        then
          let uu____26985 =
            let uu____26986 =
              let uu____26987 =
                let uu____26988 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____26988 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____26987 in
            FStar_SMTEncoding_Term.Caption uu____26986 in
          uu____26985 :: decls
        else decls in
      (let uu____26999 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____26999
       then
         let uu____27000 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____27000
       else ());
      (let env =
         let uu____27003 = FStar_TypeChecker_Env.current_module tcenv in
         get_env uu____27003 tcenv in
       let uu____27004 = encode_top_level_facts env se in
       match uu____27004 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____27018 = caption decls in
             FStar_SMTEncoding_Z3.giveZ3 uu____27018)))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____27032 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____27032
       then
         let uu____27033 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____27033
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____27068  ->
                 fun se  ->
                   match uu____27068 with
                   | (g,env2) ->
                       let uu____27088 = encode_top_level_facts env2 se in
                       (match uu____27088 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____27111 =
         encode_signature
           (let uu___187_27120 = env in
            {
              bindings = (uu___187_27120.bindings);
              depth = (uu___187_27120.depth);
              tcenv = (uu___187_27120.tcenv);
              warn = false;
              cache = (uu___187_27120.cache);
              nolabels = (uu___187_27120.nolabels);
              use_zfuel_name = (uu___187_27120.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___187_27120.encode_non_total_function_typ);
              current_module_name = (uu___187_27120.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____27111 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____27137 = FStar_Options.log_queries () in
             if uu____27137
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___188_27145 = env1 in
               {
                 bindings = (uu___188_27145.bindings);
                 depth = (uu___188_27145.depth);
                 tcenv = (uu___188_27145.tcenv);
                 warn = true;
                 cache = (uu___188_27145.cache);
                 nolabels = (uu___188_27145.nolabels);
                 use_zfuel_name = (uu___188_27145.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___188_27145.encode_non_total_function_typ);
                 current_module_name = (uu___188_27145.current_module_name)
               });
            (let uu____27147 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____27147
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
        (let uu____27202 =
           let uu____27203 = FStar_TypeChecker_Env.current_module tcenv in
           uu____27203.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____27202);
        (let env =
           let uu____27205 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____27205 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____27217 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____27252 = aux rest in
                 (match uu____27252 with
                  | (out,rest1) ->
                      let t =
                        let uu____27282 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____27282 with
                        | FStar_Pervasives_Native.Some uu____27287 ->
                            let uu____27288 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit in
                            FStar_Syntax_Util.refine uu____27288
                              x.FStar_Syntax_Syntax.sort
                        | uu____27289 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____27293 =
                        let uu____27296 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___189_27299 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___189_27299.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___189_27299.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____27296 :: out in
                      (uu____27293, rest1))
             | uu____27304 -> ([], bindings1) in
           let uu____27311 = aux bindings in
           match uu____27311 with
           | (closing,bindings1) ->
               let uu____27336 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____27336, bindings1) in
         match uu____27217 with
         | (q1,bindings1) ->
             let uu____27359 =
               let uu____27364 =
                 FStar_List.filter
                   (fun uu___154_27369  ->
                      match uu___154_27369 with
                      | FStar_TypeChecker_Env.Binding_sig uu____27370 ->
                          false
                      | uu____27377 -> true) bindings1 in
               encode_env_bindings env uu____27364 in
             (match uu____27359 with
              | (env_decls,env1) ->
                  ((let uu____27395 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____27395
                    then
                      let uu____27396 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____27396
                    else ());
                   (let uu____27398 = encode_formula q1 env1 in
                    match uu____27398 with
                    | (phi,qdecls) ->
                        let uu____27419 =
                          let uu____27424 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____27424 phi in
                        (match uu____27419 with
                         | (labels,phi1) ->
                             let uu____27441 = encode_labels labels in
                             (match uu____27441 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____27478 =
                                      let uu____27485 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____27486 =
                                        varops.mk_unique "@query" in
                                      (uu____27485,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____27486) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____27478 in
                                  let suffix =
                                    FStar_List.append
                                      [FStar_SMTEncoding_Term.Echo "<labels>"]
                                      (FStar_List.append label_suffix
                                         [FStar_SMTEncoding_Term.Echo
                                            "</labels>";
                                         FStar_SMTEncoding_Term.Echo "Done!"]) in
                                  (query_prelude, labels, qry, suffix)))))))