open Prims
let add_fuel x tl1 =
  let uu____16 = FStar_Options.unthrottle_inductives () in
  if uu____16 then tl1 else x :: tl1
let withenv c uu____39 = match uu____39 with | (a,b) -> (a, b, c)
let vargs args =
  FStar_List.filter
    (fun uu___116_74  ->
       match uu___116_74 with
       | (FStar_Util.Inl uu____79,uu____80) -> false
       | uu____83 -> true) args
let subst_lcomp_opt s l =
  match l with
  | Some (FStar_Util.Inl l1) ->
      let uu____114 =
        let uu____117 =
          let uu____118 =
            let uu____121 = l1.FStar_Syntax_Syntax.comp () in
            FStar_Syntax_Subst.subst_comp s uu____121 in
          FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____118 in
        FStar_Util.Inl uu____117 in
      Some uu____114
  | uu____126 -> l
let escape: Prims.string -> Prims.string =
  fun s  -> FStar_Util.replace_char s '\'' '_'
let mk_term_projector_name:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string =
  fun lid  ->
    fun a  ->
      let a1 =
        let uu___140_140 = a in
        let uu____141 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname in
        {
          FStar_Syntax_Syntax.ppname = uu____141;
          FStar_Syntax_Syntax.index =
            (uu___140_140.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___140_140.FStar_Syntax_Syntax.sort)
        } in
      let uu____142 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
      FStar_All.pipe_left escape uu____142
let primitive_projector_by_pos:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string
  =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____155 =
          let uu____156 =
            FStar_Util.format2
              "Projector %s on data constructor %s not found"
              (Prims.string_of_int i) lid.FStar_Ident.str in
          failwith uu____156 in
        let uu____157 = FStar_TypeChecker_Env.lookup_datacon env lid in
        match uu____157 with
        | (uu____160,t) ->
            let uu____162 =
              let uu____163 = FStar_Syntax_Subst.compress t in
              uu____163.FStar_Syntax_Syntax.n in
            (match uu____162 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____178 = FStar_Syntax_Subst.open_comp bs c in
                 (match uu____178 with
                  | (binders,uu____182) ->
                      if
                        (i < (Prims.parse_int "0")) ||
                          (i >= (FStar_List.length binders))
                      then fail ()
                      else
                        (let b = FStar_List.nth binders i in
                         mk_term_projector_name lid (Prims.fst b)))
             | uu____193 -> fail ())
let mk_term_projector_name_by_pos:
  FStar_Ident.lident -> Prims.int -> Prims.string =
  fun lid  ->
    fun i  ->
      let uu____200 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (Prims.string_of_int i) in
      FStar_All.pipe_left escape uu____200
let mk_term_projector:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term
  =
  fun lid  ->
    fun a  ->
      let uu____207 =
        let uu____210 = mk_term_projector_name lid a in
        (uu____210,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____207
let mk_term_projector_by_pos:
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term =
  fun lid  ->
    fun i  ->
      let uu____217 =
        let uu____220 = mk_term_projector_name_by_pos lid i in
        (uu____220,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____217
let mk_data_tester env l x =
  FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x
type varops_t =
  {
  push: Prims.unit -> Prims.unit;
  pop: Prims.unit -> Prims.unit;
  mark: Prims.unit -> Prims.unit;
  reset_mark: Prims.unit -> Prims.unit;
  commit_mark: Prims.unit -> Prims.unit;
  new_var: FStar_Ident.ident -> Prims.int -> Prims.string;
  new_fvar: FStar_Ident.lident -> Prims.string;
  fresh: Prims.string -> Prims.string;
  string_const: Prims.string -> FStar_SMTEncoding_Term.term;
  next_id: Prims.unit -> Prims.int;
  mk_unique: Prims.string -> Prims.string;}
let varops: varops_t =
  let initial_ctr = Prims.parse_int "100" in
  let ctr = FStar_Util.mk_ref initial_ctr in
  let new_scope uu____410 =
    let uu____411 = FStar_Util.smap_create (Prims.parse_int "100") in
    let uu____413 = FStar_Util.smap_create (Prims.parse_int "100") in
    (uu____411, uu____413) in
  let scopes =
    let uu____424 = let uu____430 = new_scope () in [uu____430] in
    FStar_Util.mk_ref uu____424 in
  let mk_unique y =
    let y1 = escape y in
    let y2 =
      let uu____455 =
        let uu____457 = FStar_ST.read scopes in
        FStar_Util.find_map uu____457
          (fun uu____474  ->
             match uu____474 with
             | (names1,uu____481) -> FStar_Util.smap_try_find names1 y1) in
      match uu____455 with
      | None  -> y1
      | Some uu____486 ->
          (FStar_Util.incr ctr;
           (let uu____491 =
              let uu____492 =
                let uu____493 = FStar_ST.read ctr in
                Prims.string_of_int uu____493 in
              Prims.strcat "__" uu____492 in
            Prims.strcat y1 uu____491)) in
    let top_scope =
      let uu____498 =
        let uu____503 = FStar_ST.read scopes in FStar_List.hd uu____503 in
      FStar_All.pipe_left Prims.fst uu____498 in
    FStar_Util.smap_add top_scope y2 true; y2 in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn))) in
  let new_fvar lid = mk_unique lid.FStar_Ident.str in
  let next_id1 uu____542 = FStar_Util.incr ctr; FStar_ST.read ctr in
  let fresh1 pfx =
    let uu____553 =
      let uu____554 = next_id1 () in
      FStar_All.pipe_left Prims.string_of_int uu____554 in
    FStar_Util.format2 "%s_%s" pfx uu____553 in
  let string_const s =
    let uu____559 =
      let uu____561 = FStar_ST.read scopes in
      FStar_Util.find_map uu____561
        (fun uu____578  ->
           match uu____578 with
           | (uu____584,strings) -> FStar_Util.smap_try_find strings s) in
    match uu____559 with
    | Some f -> f
    | None  ->
        let id = next_id1 () in
        let f =
          let uu____593 = FStar_SMTEncoding_Util.mk_String_const id in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____593 in
        let top_scope =
          let uu____596 =
            let uu____601 = FStar_ST.read scopes in FStar_List.hd uu____601 in
          FStar_All.pipe_left Prims.snd uu____596 in
        (FStar_Util.smap_add top_scope s f; f) in
  let push1 uu____629 =
    let uu____630 =
      let uu____636 = new_scope () in
      let uu____641 = FStar_ST.read scopes in uu____636 :: uu____641 in
    FStar_ST.write scopes uu____630 in
  let pop1 uu____668 =
    let uu____669 =
      let uu____675 = FStar_ST.read scopes in FStar_List.tl uu____675 in
    FStar_ST.write scopes uu____669 in
  let mark1 uu____702 = push1 () in
  let reset_mark1 uu____706 = pop1 () in
  let commit_mark1 uu____710 =
    let uu____711 = FStar_ST.read scopes in
    match uu____711 with
    | (hd1,hd2)::(next1,next2)::tl1 ->
        (FStar_Util.smap_fold hd1
           (fun key  ->
              fun value  -> fun v1  -> FStar_Util.smap_add next1 key value)
           ();
         FStar_Util.smap_fold hd2
           (fun key  ->
              fun value  -> fun v1  -> FStar_Util.smap_add next2 key value)
           ();
         FStar_ST.write scopes ((next1, next2) :: tl1))
    | uu____771 -> failwith "Impossible" in
  {
    push = push1;
    pop = pop1;
    mark = mark1;
    reset_mark = reset_mark1;
    commit_mark = commit_mark1;
    new_var;
    new_fvar;
    fresh = fresh1;
    string_const;
    next_id = next_id1;
    mk_unique
  }
let unmangle: FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.bv =
  fun x  ->
    let uu___141_780 = x in
    let uu____781 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____781;
      FStar_Syntax_Syntax.index = (uu___141_780.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___141_780.FStar_Syntax_Syntax.sort)
    }
type binding =
  | Binding_var of (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.term)
  | Binding_fvar of (FStar_Ident.lident* Prims.string*
  FStar_SMTEncoding_Term.term Prims.option* FStar_SMTEncoding_Term.term
  Prims.option)
let uu___is_Binding_var: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____802 -> false
let __proj__Binding_var__item___0:
  binding -> (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.term) =
  fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_fvar: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____826 -> false
let __proj__Binding_fvar__item___0:
  binding ->
    (FStar_Ident.lident* Prims.string* FStar_SMTEncoding_Term.term
      Prims.option* FStar_SMTEncoding_Term.term Prims.option)
  = fun projectee  -> match projectee with | Binding_fvar _0 -> _0
let binder_of_eithervar v1 = (v1, None)
type env_t =
  {
  bindings: binding Prims.list;
  depth: Prims.int;
  tcenv: FStar_TypeChecker_Env.env;
  warn: Prims.bool;
  cache:
    (Prims.string* FStar_SMTEncoding_Term.sort Prims.list*
      FStar_SMTEncoding_Term.decl Prims.list) FStar_Util.smap;
  nolabels: Prims.bool;
  use_zfuel_name: Prims.bool;
  encode_non_total_function_typ: Prims.bool;
  current_module_name: Prims.string;}
let print_env: env_t -> Prims.string =
  fun e  ->
    let uu____952 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___117_956  ->
              match uu___117_956 with
              | Binding_var (x,uu____958) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____960,uu____961,uu____962) ->
                  FStar_Syntax_Print.lid_to_string l)) in
    FStar_All.pipe_right uu____952 (FStar_String.concat ", ")
let lookup_binding env f = FStar_Util.find_map env.bindings f
let caption_t: env_t -> FStar_Syntax_Syntax.term -> Prims.string Prims.option
  =
  fun env  ->
    fun t  ->
      let uu____995 = FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
      if uu____995
      then
        let uu____997 = FStar_Syntax_Print.term_to_string t in Some uu____997
      else None
let fresh_fvar:
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string* FStar_SMTEncoding_Term.term)
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x in
      let uu____1008 = FStar_SMTEncoding_Util.mkFreeV (xsym, s) in
      (xsym, uu____1008)
let gen_term_var:
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string* FStar_SMTEncoding_Term.term* env_t)
  =
  fun env  ->
    fun x  ->
      let ysym = Prims.strcat "@x" (Prims.string_of_int env.depth) in
      let y =
        FStar_SMTEncoding_Util.mkFreeV
          (ysym, FStar_SMTEncoding_Term.Term_sort) in
      (ysym, y,
        (let uu___142_1020 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___142_1020.tcenv);
           warn = (uu___142_1020.warn);
           cache = (uu___142_1020.cache);
           nolabels = (uu___142_1020.nolabels);
           use_zfuel_name = (uu___142_1020.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___142_1020.encode_non_total_function_typ);
           current_module_name = (uu___142_1020.current_module_name)
         }))
let new_term_constant:
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string* FStar_SMTEncoding_Term.term* env_t)
  =
  fun env  ->
    fun x  ->
      let ysym =
        varops.new_var x.FStar_Syntax_Syntax.ppname
          x.FStar_Syntax_Syntax.index in
      let y = FStar_SMTEncoding_Util.mkApp (ysym, []) in
      (ysym, y,
        (let uu___143_1033 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___143_1033.depth);
           tcenv = (uu___143_1033.tcenv);
           warn = (uu___143_1033.warn);
           cache = (uu___143_1033.cache);
           nolabels = (uu___143_1033.nolabels);
           use_zfuel_name = (uu___143_1033.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___143_1033.encode_non_total_function_typ);
           current_module_name = (uu___143_1033.current_module_name)
         }))
let new_term_constant_from_string:
  env_t ->
    FStar_Syntax_Syntax.bv ->
      Prims.string -> (Prims.string* FStar_SMTEncoding_Term.term* env_t)
  =
  fun env  ->
    fun x  ->
      fun str  ->
        let ysym = varops.mk_unique str in
        let y = FStar_SMTEncoding_Util.mkApp (ysym, []) in
        (ysym, y,
          (let uu___144_1049 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___144_1049.depth);
             tcenv = (uu___144_1049.tcenv);
             warn = (uu___144_1049.warn);
             cache = (uu___144_1049.cache);
             nolabels = (uu___144_1049.nolabels);
             use_zfuel_name = (uu___144_1049.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___144_1049.encode_non_total_function_typ);
             current_module_name = (uu___144_1049.current_module_name)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___145_1059 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___145_1059.depth);
          tcenv = (uu___145_1059.tcenv);
          warn = (uu___145_1059.warn);
          cache = (uu___145_1059.cache);
          nolabels = (uu___145_1059.nolabels);
          use_zfuel_name = (uu___145_1059.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___145_1059.encode_non_total_function_typ);
          current_module_name = (uu___145_1059.current_module_name)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___118_1075  ->
             match uu___118_1075 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 Some (b, t)
             | uu____1083 -> None) in
      let uu____1086 = aux a in
      match uu____1086 with
      | None  ->
          let a2 = unmangle a in
          let uu____1093 = aux a2 in
          (match uu____1093 with
           | None  ->
               let uu____1099 =
                 let uu____1100 = FStar_Syntax_Print.bv_to_string a2 in
                 let uu____1101 = print_env env in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____1100 uu____1101 in
               failwith uu____1099
           | Some (b,t) -> t)
      | Some (b,t) -> t
let new_term_constant_and_tok_from_lid:
  env_t -> FStar_Ident.lident -> (Prims.string* Prims.string* env_t) =
  fun env  ->
    fun x  ->
      let fname = varops.new_fvar x in
      let ftok = Prims.strcat fname "@tok" in
      let uu____1121 =
        let uu___146_1122 = env in
        let uu____1123 =
          let uu____1125 =
            let uu____1126 =
              let uu____1133 =
                let uu____1135 = FStar_SMTEncoding_Util.mkApp (ftok, []) in
                FStar_All.pipe_left (fun _0_29  -> Some _0_29) uu____1135 in
              (x, fname, uu____1133, None) in
            Binding_fvar uu____1126 in
          uu____1125 :: (env.bindings) in
        {
          bindings = uu____1123;
          depth = (uu___146_1122.depth);
          tcenv = (uu___146_1122.tcenv);
          warn = (uu___146_1122.warn);
          cache = (uu___146_1122.cache);
          nolabels = (uu___146_1122.nolabels);
          use_zfuel_name = (uu___146_1122.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___146_1122.encode_non_total_function_typ);
          current_module_name = (uu___146_1122.current_module_name)
        } in
      (fname, ftok, uu____1121)
let try_lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string* FStar_SMTEncoding_Term.term Prims.option*
        FStar_SMTEncoding_Term.term Prims.option) Prims.option
  =
  fun env  ->
    fun a  ->
      lookup_binding env
        (fun uu___119_1157  ->
           match uu___119_1157 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               Some (t1, t2, t3)
           | uu____1179 -> None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____1191 =
        lookup_binding env
          (fun uu___120_1193  ->
             match uu___120_1193 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 Some ()
             | uu____1203 -> None) in
      FStar_All.pipe_right uu____1191 FStar_Option.isSome
let lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string* FStar_SMTEncoding_Term.term Prims.option*
        FStar_SMTEncoding_Term.term Prims.option)
  =
  fun env  ->
    fun a  ->
      let uu____1216 = try_lookup_lid env a in
      match uu____1216 with
      | None  ->
          let uu____1233 =
            let uu____1234 = FStar_Syntax_Print.lid_to_string a in
            FStar_Util.format1 "Name not found: %s" uu____1234 in
          failwith uu____1233
      | Some s -> s
let push_free_var:
  env_t ->
    FStar_Ident.lident ->
      Prims.string -> FStar_SMTEncoding_Term.term Prims.option -> env_t
  =
  fun env  ->
    fun x  ->
      fun fname  ->
        fun ftok  ->
          let uu___147_1265 = env in
          {
            bindings = ((Binding_fvar (x, fname, ftok, None)) ::
              (env.bindings));
            depth = (uu___147_1265.depth);
            tcenv = (uu___147_1265.tcenv);
            warn = (uu___147_1265.warn);
            cache = (uu___147_1265.cache);
            nolabels = (uu___147_1265.nolabels);
            use_zfuel_name = (uu___147_1265.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___147_1265.encode_non_total_function_typ);
            current_module_name = (uu___147_1265.current_module_name)
          }
let push_zfuel_name: env_t -> FStar_Ident.lident -> Prims.string -> env_t =
  fun env  ->
    fun x  ->
      fun f  ->
        let uu____1277 = lookup_lid env x in
        match uu____1277 with
        | (t1,t2,uu____1285) ->
            let t3 =
              let uu____1291 =
                let uu____1295 =
                  let uu____1297 = FStar_SMTEncoding_Util.mkApp ("ZFuel", []) in
                  [uu____1297] in
                (f, uu____1295) in
              FStar_SMTEncoding_Util.mkApp uu____1291 in
            let uu___148_1300 = env in
            {
              bindings = ((Binding_fvar (x, t1, t2, (Some t3))) ::
                (env.bindings));
              depth = (uu___148_1300.depth);
              tcenv = (uu___148_1300.tcenv);
              warn = (uu___148_1300.warn);
              cache = (uu___148_1300.cache);
              nolabels = (uu___148_1300.nolabels);
              use_zfuel_name = (uu___148_1300.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___148_1300.encode_non_total_function_typ);
              current_module_name = (uu___148_1300.current_module_name)
            }
let try_lookup_free_var:
  env_t -> FStar_Ident.lident -> FStar_SMTEncoding_Term.term Prims.option =
  fun env  ->
    fun l  ->
      let uu____1310 = try_lookup_lid env l in
      match uu____1310 with
      | None  -> None
      | Some (name,sym,zf_opt) ->
          (match zf_opt with
           | Some f when env.use_zfuel_name -> Some f
           | uu____1337 ->
               (match sym with
                | Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____1342,fuel::[]) ->
                         let uu____1345 =
                           let uu____1346 =
                             let uu____1347 =
                               FStar_SMTEncoding_Term.fv_of_term fuel in
                             FStar_All.pipe_right uu____1347 Prims.fst in
                           FStar_Util.starts_with uu____1346 "fuel" in
                         if uu____1345
                         then
                           let uu____1349 =
                             let uu____1350 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort) in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____1350
                               fuel in
                           FStar_All.pipe_left (fun _0_30  -> Some _0_30)
                             uu____1349
                         else Some t
                     | uu____1353 -> Some t)
                | uu____1354 -> None))
let lookup_free_var env a =
  let uu____1372 = try_lookup_free_var env a.FStar_Syntax_Syntax.v in
  match uu____1372 with
  | Some t -> t
  | None  ->
      let uu____1375 =
        let uu____1376 =
          FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v in
        FStar_Util.format1 "Name not found: %s" uu____1376 in
      failwith uu____1375
let lookup_free_var_name env a =
  let uu____1393 = lookup_lid env a.FStar_Syntax_Syntax.v in
  match uu____1393 with | (x,uu____1400,uu____1401) -> x
let lookup_free_var_sym env a =
  let uu____1425 = lookup_lid env a.FStar_Syntax_Syntax.v in
  match uu____1425 with
  | (name,sym,zf_opt) ->
      (match zf_opt with
       | Some
           { FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g,zf);
             FStar_SMTEncoding_Term.freevars = uu____1446;
             FStar_SMTEncoding_Term.rng = uu____1447;_}
           when env.use_zfuel_name -> (g, zf)
       | uu____1455 ->
           (match sym with
            | None  -> ((FStar_SMTEncoding_Term.Var name), [])
            | Some sym1 ->
                (match sym1.FStar_SMTEncoding_Term.tm with
                 | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                 | uu____1469 -> ((FStar_SMTEncoding_Term.Var name), []))))
let tok_of_name:
  env_t -> Prims.string -> FStar_SMTEncoding_Term.term Prims.option =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___121_1478  ->
           match uu___121_1478 with
           | Binding_fvar (uu____1480,nm',tok,uu____1483) when nm = nm' ->
               tok
           | uu____1488 -> None)
let mkForall_fuel' n1 uu____1505 =
  match uu____1505 with
  | (pats,vars,body) ->
      let fallback uu____1521 =
        FStar_SMTEncoding_Util.mkForall (pats, vars, body) in
      let uu____1524 = FStar_Options.unthrottle_inductives () in
      if uu____1524
      then fallback ()
      else
        (let uu____1526 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
         match uu____1526 with
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
                       | uu____1545 -> p)) in
             let pats1 = FStar_List.map add_fuel1 pats in
             let body1 =
               match body.FStar_SMTEncoding_Term.tm with
               | FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                   let guard1 =
                     match guard.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App
                         (FStar_SMTEncoding_Term.And ,guards) ->
                         let uu____1559 = add_fuel1 guards in
                         FStar_SMTEncoding_Util.mk_and_l uu____1559
                     | uu____1561 ->
                         let uu____1562 = add_fuel1 [guard] in
                         FStar_All.pipe_right uu____1562 FStar_List.hd in
                   FStar_SMTEncoding_Util.mkImp (guard1, body')
               | uu____1565 -> body in
             let vars1 = (fsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars in
             FStar_SMTEncoding_Util.mkForall (pats1, vars1, body1))
let mkForall_fuel:
  (FStar_SMTEncoding_Term.pat Prims.list Prims.list*
    FStar_SMTEncoding_Term.fvs* FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term
  = mkForall_fuel' (Prims.parse_int "1")
let head_normal: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow _
        |FStar_Syntax_Syntax.Tm_refine _
         |FStar_Syntax_Syntax.Tm_bvar _
          |FStar_Syntax_Syntax.Tm_uvar _
           |FStar_Syntax_Syntax.Tm_abs _|FStar_Syntax_Syntax.Tm_constant _
          -> true
      | FStar_Syntax_Syntax.Tm_fvar fv|FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
           FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _;
           FStar_Syntax_Syntax.vars = _;_},_)
          ->
          let uu____1609 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1609 FStar_Option.isNone
      | uu____1622 -> false
let head_redex: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____1629 =
        let uu____1630 = FStar_Syntax_Util.un_uinst t in
        uu____1630.FStar_Syntax_Syntax.n in
      match uu____1629 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1633,uu____1634,Some (FStar_Util.Inr (l,flags))) ->
          ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) ||
             (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___122_1663  ->
                  match uu___122_1663 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____1664 -> false) flags)
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1665,uu____1666,Some (FStar_Util.Inl lc)) ->
          FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____1693 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1693 FStar_Option.isSome
      | uu____1706 -> false
let whnf: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____1713 = head_normal env t in
      if uu____1713
      then t
      else
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.WHNF;
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
    let uu____1724 =
      let uu____1725 = FStar_Syntax_Syntax.null_binder t in [uu____1725] in
    let uu____1726 =
      FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant None in
    FStar_Syntax_Util.abs uu____1724 uu____1726 None
let mk_Apply:
  FStar_SMTEncoding_Term.term ->
    (Prims.string* FStar_SMTEncoding_Term.sort) Prims.list ->
      FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun vars  ->
      FStar_All.pipe_right vars
        (FStar_List.fold_left
           (fun out  ->
              fun var  ->
                match Prims.snd var with
                | FStar_SMTEncoding_Term.Fuel_sort  ->
                    let uu____1753 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____1753
                | s ->
                    let uu____1756 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____1756) e)
let mk_Apply_args:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
let is_app: FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___123_1768  ->
    match uu___123_1768 with
    | FStar_SMTEncoding_Term.Var "ApplyTT"|FStar_SMTEncoding_Term.Var
      "ApplyTF" -> true
    | uu____1769 -> false
let is_an_eta_expansion:
  env_t ->
    FStar_SMTEncoding_Term.fv Prims.list ->
      FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term Prims.option
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
                       FStar_SMTEncoding_Term.freevars = uu____1797;
                       FStar_SMTEncoding_Term.rng = uu____1798;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____1812) ->
              let uu____1817 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____1827 -> false) args (FStar_List.rev xs)) in
              if uu____1817 then tok_of_name env f else None
          | (uu____1830,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu____1833 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____1835 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____1835)) in
              if uu____1833 then Some t else None
          | uu____1838 -> None in
        check_partial_applications body (FStar_List.rev vars)
let reify_body:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let tm = FStar_Syntax_Util.mk_reify t in
      let tm' =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Reify;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses] env tm in
      (let uu____1853 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify") in
       if uu____1853
       then
         let uu____1854 = FStar_Syntax_Print.term_to_string tm in
         let uu____1855 = FStar_Syntax_Print.term_to_string tm' in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____1854 uu____1855
       else ());
      tm'
type label = (FStar_SMTEncoding_Term.fv* Prims.string* FStar_Range.range)
type labels = label Prims.list
type pattern =
  {
  pat_vars: (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.fv) Prims.list;
  pat_term:
    Prims.unit ->
      (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t);
  guard: FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term;
  projections:
    FStar_SMTEncoding_Term.term ->
      (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.term) Prims.list;}
exception Let_rec_unencodeable
let uu___is_Let_rec_unencodeable: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____1937 -> false
let encode_const: FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___124_1940  ->
    match uu___124_1940 with
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
        let uu____1942 =
          let uu____1946 =
            let uu____1948 =
              let uu____1949 =
                FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c) in
              FStar_SMTEncoding_Term.boxInt uu____1949 in
            [uu____1948] in
          ("FStar.Char.Char", uu____1946) in
        FStar_SMTEncoding_Util.mkApp uu____1942
    | FStar_Const.Const_int (i,None ) ->
        let uu____1957 = FStar_SMTEncoding_Util.mkInteger i in
        FStar_SMTEncoding_Term.boxInt uu____1957
    | FStar_Const.Const_int (i,Some uu____1959) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____1968) ->
        let uu____1971 = FStar_All.pipe_left FStar_Util.string_of_bytes bytes in
        varops.string_const uu____1971
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____1975 =
          let uu____1976 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "Unhandled constant: %s" uu____1976 in
        failwith uu____1975
let as_function_typ:
  env_t ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t0  ->
      let rec aux norm1 t =
        let t1 = FStar_Syntax_Subst.compress t in
        match t1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow uu____1995 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____2003 ->
            let uu____2008 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____2008
        | uu____2009 ->
            if norm1
            then let uu____2010 = whnf env t1 in aux false uu____2010
            else
              (let uu____2012 =
                 let uu____2013 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____2014 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____2013 uu____2014 in
               failwith uu____2012) in
      aux true t0
let curried_arrow_formals_comp:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.comp)
  =
  fun k  ->
    let k1 = FStar_Syntax_Subst.compress k in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        FStar_Syntax_Subst.open_comp bs c
    | uu____2035 ->
        let uu____2036 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____2036)
let rec encode_binders:
  FStar_SMTEncoding_Term.term Prims.option ->
    FStar_Syntax_Syntax.binders ->
      env_t ->
        (FStar_SMTEncoding_Term.fv Prims.list* FStar_SMTEncoding_Term.term
          Prims.list* env_t* FStar_SMTEncoding_Term.decls_t*
          FStar_Syntax_Syntax.bv Prims.list)
  =
  fun fuel_opt  ->
    fun bs  ->
      fun env  ->
        (let uu____2179 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____2179
         then
           let uu____2180 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____2180
         else ());
        (let uu____2182 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2218  ->
                   fun b  ->
                     match uu____2218 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2261 =
                           let x = unmangle (Prims.fst b) in
                           let uu____2270 = gen_term_var env1 x in
                           match uu____2270 with
                           | (xxsym,xx,env') ->
                               let uu____2284 =
                                 let uu____2287 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____2287 env1 xx in
                               (match uu____2284 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____2261 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____2182 with
         | (vars,guards,env1,decls,names1) ->
             ((FStar_List.rev vars), (FStar_List.rev guards), env1, decls,
               (FStar_List.rev names1)))
and encode_term_pred:
  FStar_SMTEncoding_Term.term Prims.option ->
    FStar_Syntax_Syntax.typ ->
      env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____2375 = encode_term t env in
          match uu____2375 with
          | (t1,decls) ->
              let uu____2382 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____2382, decls)
and encode_term_pred':
  FStar_SMTEncoding_Term.term Prims.option ->
    FStar_Syntax_Syntax.typ ->
      env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____2390 = encode_term t env in
          match uu____2390 with
          | (t1,decls) ->
              (match fuel_opt with
               | None  ->
                   let uu____2399 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____2399, decls)
               | Some f ->
                   let uu____2401 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____2401, decls))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____2408 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____2408
       then
         let uu____2409 = FStar_Syntax_Print.tag_of_term t in
         let uu____2410 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____2411 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____2409 uu____2410
           uu____2411
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed _|FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____2416 =
             let uu____2417 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____2418 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____2419 = FStar_Syntax_Print.term_to_string t0 in
             let uu____2420 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2417
               uu____2418 uu____2419 uu____2420 in
           failwith uu____2416
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____2424 =
             let uu____2425 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____2425 in
           failwith uu____2424
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____2430) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____2460) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____2469 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____2469, [])
       | FStar_Syntax_Syntax.Tm_type uu____2475 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2478) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____2484 = encode_const c in (uu____2484, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____2499 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____2499 with
            | (binders1,res) ->
                let uu____2506 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____2506
                then
                  let uu____2509 = encode_binders None binders1 env in
                  (match uu____2509 with
                   | (vars,guards,env',decls,uu____2524) ->
                       let fsym =
                         let uu____2534 = varops.fresh "f" in
                         (uu____2534, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____2537 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___149_2541 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___149_2541.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___149_2541.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___149_2541.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___149_2541.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___149_2541.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___149_2541.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___149_2541.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___149_2541.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___149_2541.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___149_2541.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___149_2541.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___149_2541.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___149_2541.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___149_2541.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___149_2541.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___149_2541.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___149_2541.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___149_2541.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___149_2541.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___149_2541.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___149_2541.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___149_2541.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___149_2541.FStar_TypeChecker_Env.qname_and_index)
                            }) res in
                       (match uu____2537 with
                        | (pre_opt,res_t) ->
                            let uu____2548 =
                              encode_term_pred None res_t env' app in
                            (match uu____2548 with
                             | (res_pred,decls') ->
                                 let uu____2555 =
                                   match pre_opt with
                                   | None  ->
                                       let uu____2562 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____2562, [])
                                   | Some pre ->
                                       let uu____2565 =
                                         encode_formula pre env' in
                                       (match uu____2565 with
                                        | (guard,decls0) ->
                                            let uu____2573 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____2573, decls0)) in
                                 (match uu____2555 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____2581 =
                                          let uu____2587 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____2587) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____2581 in
                                      let cvars =
                                        let uu____2597 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____2597
                                          (FStar_List.filter
                                             (fun uu____2603  ->
                                                match uu____2603 with
                                                | (x,uu____2607) ->
                                                    x <> (Prims.fst fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____2618 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____2618 with
                                       | Some (t',sorts,uu____2634) ->
                                           let uu____2644 =
                                             let uu____2645 =
                                               let uu____2649 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               (t', uu____2649) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____2645 in
                                           (uu____2644, [])
                                       | None  ->
                                           let tsym =
                                             let uu____2665 =
                                               let uu____2666 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____2666 in
                                             varops.mk_unique uu____2665 in
                                           let cvar_sorts =
                                             FStar_List.map Prims.snd cvars in
                                           let caption =
                                             let uu____2673 =
                                               FStar_Options.log_queries () in
                                             if uu____2673
                                             then
                                               let uu____2675 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               Some uu____2675
                                             else None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____2681 =
                                               let uu____2685 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____2685) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____2681 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____2693 =
                                               let uu____2697 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____2697, (Some a_name),
                                                 a_name) in
                                             FStar_SMTEncoding_Term.Assume
                                               uu____2693 in
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
                                             let uu____2710 =
                                               let uu____2714 =
                                                 let uu____2715 =
                                                   let uu____2721 =
                                                     let uu____2722 =
                                                       let uu____2725 =
                                                         let uu____2726 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____2726 in
                                                       (f_has_t, uu____2725) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____2722 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____2721) in
                                                 mkForall_fuel uu____2715 in
                                               (uu____2714,
                                                 (Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Term.Assume
                                               uu____2710 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____2739 =
                                               let uu____2743 =
                                                 let uu____2744 =
                                                   let uu____2750 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____2750) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____2744 in
                                               (uu____2743, (Some a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Term.Assume
                                               uu____2739 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           (FStar_Util.smap_add env.cache
                                              tkey_hash
                                              (tsym, cvar_sorts, t_decls);
                                            (t1, t_decls)))))))
                else
                  (let tsym = varops.fresh "Non_total_Tm_arrow" in
                   let tdecl =
                     FStar_SMTEncoding_Term.DeclFun
                       (tsym, [], FStar_SMTEncoding_Term.Term_sort, None) in
                   let t1 = FStar_SMTEncoding_Util.mkApp (tsym, []) in
                   let t_kinding =
                     let a_name =
                       Prims.strcat "non_total_function_typing_" tsym in
                     let uu____2781 =
                       let uu____2785 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____2785, (Some "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Term.Assume uu____2781 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____2794 =
                       let uu____2798 =
                         let uu____2799 =
                           let uu____2805 =
                             let uu____2806 =
                               let uu____2809 =
                                 let uu____2810 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____2810 in
                               (f_has_t, uu____2809) in
                             FStar_SMTEncoding_Util.mkImp uu____2806 in
                           ([[f_has_t]], [fsym], uu____2805) in
                         mkForall_fuel uu____2799 in
                       (uu____2798, (Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Term.Assume uu____2794 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____2824 ->
           let uu____2829 =
             let uu____2832 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____2832 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____2837;
                 FStar_Syntax_Syntax.pos = uu____2838;
                 FStar_Syntax_Syntax.vars = uu____2839;_} ->
                 let uu____2846 = FStar_Syntax_Subst.open_term [(x, None)] f in
                 (match uu____2846 with
                  | (b,f1) ->
                      let uu____2860 =
                        let uu____2861 = FStar_List.hd b in
                        Prims.fst uu____2861 in
                      (uu____2860, f1))
             | uu____2866 -> failwith "impossible" in
           (match uu____2829 with
            | (x,f) ->
                let uu____2873 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____2873 with
                 | (base_t,decls) ->
                     let uu____2880 = gen_term_var env x in
                     (match uu____2880 with
                      | (x1,xtm,env') ->
                          let uu____2889 = encode_formula f env' in
                          (match uu____2889 with
                           | (refinement,decls') ->
                               let uu____2896 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____2896 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (Some fterm) xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____2907 =
                                        let uu____2909 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____2913 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____2909
                                          uu____2913 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____2907 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____2929  ->
                                              match uu____2929 with
                                              | (y,uu____2933) ->
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
                                    let uu____2952 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____2952 with
                                     | Some (t1,uu____2967,uu____2968) ->
                                         let uu____2978 =
                                           let uu____2979 =
                                             let uu____2983 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             (t1, uu____2983) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____2979 in
                                         (uu____2978, [])
                                     | None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____3000 =
                                             let uu____3001 =
                                               let uu____3002 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____3002 in
                                             Prims.strcat module_name
                                               uu____3001 in
                                           varops.mk_unique uu____3000 in
                                         let cvar_sorts =
                                           FStar_List.map Prims.snd cvars1 in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               None) in
                                         let t1 =
                                           let uu____3011 =
                                             let uu____3015 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____3015) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3011 in
                                         let x_has_t =
                                           FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                             (Some fterm) xtm t1 in
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
                                           let uu____3025 =
                                             let uu____3029 =
                                               let uu____3030 =
                                                 let uu____3036 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____3036) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3030 in
                                             (uu____3029,
                                               (Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3025 in
                                         let t_kinding =
                                           let uu____3046 =
                                             let uu____3050 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____3050,
                                               (Some "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3046 in
                                         let t_interp =
                                           let uu____3060 =
                                             let uu____3064 =
                                               let uu____3065 =
                                                 let uu____3071 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____3071) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3065 in
                                             let uu____3083 =
                                               let uu____3085 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               Some uu____3085 in
                                             (uu____3064, uu____3083,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3060 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1]) in
                                         (FStar_Util.smap_add env.cache
                                            tkey_hash
                                            (tsym, cvar_sorts, t_decls);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____3113 = FStar_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____3113 in
           let uu____3117 = encode_term_pred None k env ttm in
           (match uu____3117 with
            | (t_has_k,decls) ->
                let d =
                  let uu____3125 =
                    let uu____3129 =
                      let uu____3130 =
                        let uu____3131 =
                          let uu____3132 = FStar_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____3132 in
                        FStar_Util.format1 "uvar_typing_%s" uu____3131 in
                      varops.mk_unique uu____3130 in
                    (t_has_k, (Some "Uvar typing"), uu____3129) in
                  FStar_SMTEncoding_Term.Assume uu____3125 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____3138 ->
           let uu____3148 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____3148 with
            | (head1,args_e) ->
                let uu____3176 =
                  let uu____3184 =
                    let uu____3185 = FStar_Syntax_Subst.compress head1 in
                    uu____3185.FStar_Syntax_Syntax.n in
                  (uu____3184, args_e) in
                (match uu____3176 with
                 | (uu____3195,uu____3196) when head_redex env head1 ->
                     let uu____3207 = whnf env t in
                     encode_term uu____3207 env
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.tk = _;
                       FStar_Syntax_Syntax.pos = _;
                       FStar_Syntax_Syntax.vars = _;_},_),_::(v1,_)::
                    (v2,_)::[])
                   |(FStar_Syntax_Syntax.Tm_fvar fv,_::(v1,_)::(v2,_)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.lexcons_lid
                     ->
                     let uu____3281 = encode_term v1 env in
                     (match uu____3281 with
                      | (v11,decls1) ->
                          let uu____3288 = encode_term v2 env in
                          (match uu____3288 with
                           | (v21,decls2) ->
                               let uu____3295 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3295,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____3297) ->
                     let e0 =
                       let uu____3311 =
                         let uu____3314 =
                           let uu____3315 =
                             let uu____3325 =
                               let uu____3331 = FStar_List.hd args_e in
                               [uu____3331] in
                             (head1, uu____3325) in
                           FStar_Syntax_Syntax.Tm_app uu____3315 in
                         FStar_Syntax_Syntax.mk uu____3314 in
                       uu____3311 None head1.FStar_Syntax_Syntax.pos in
                     ((let uu____3364 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____3364
                       then
                         let uu____3365 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Trying to normalize %s\n"
                           uu____3365
                       else ());
                      (let e01 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Reify;
                           FStar_TypeChecker_Normalize.Eager_unfolding;
                           FStar_TypeChecker_Normalize.EraseUniverses;
                           FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                           env.tcenv e0 in
                       (let uu____3369 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env.tcenv)
                            (FStar_Options.Other "SMTEncodingReify") in
                        if uu____3369
                        then
                          let uu____3370 =
                            FStar_Syntax_Print.term_to_string e01 in
                          FStar_Util.print1 "Result of normalization %s\n"
                            uu____3370
                        else ());
                       (let e02 =
                          let uu____3373 =
                            let uu____3374 =
                              let uu____3375 =
                                FStar_Syntax_Subst.compress e01 in
                              uu____3375.FStar_Syntax_Syntax.n in
                            match uu____3374 with
                            | FStar_Syntax_Syntax.Tm_app uu____3378 -> false
                            | uu____3388 -> true in
                          if uu____3373
                          then e01
                          else
                            (let uu____3390 =
                               FStar_Syntax_Util.head_and_args e01 in
                             match uu____3390 with
                             | (head2,args) ->
                                 let uu____3416 =
                                   let uu____3417 =
                                     let uu____3418 =
                                       FStar_Syntax_Subst.compress head2 in
                                     uu____3418.FStar_Syntax_Syntax.n in
                                   match uu____3417 with
                                   | FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_reify ) -> true
                                   | uu____3421 -> false in
                                 if uu____3416
                                 then
                                   (match args with
                                    | x::[] -> Prims.fst x
                                    | uu____3437 ->
                                        failwith
                                          "Impossible : Reify applied to multiple arguments after normalization.")
                                 else e01) in
                        let e =
                          match args_e with
                          | uu____3445::[] -> e02
                          | uu____3458 ->
                              let uu____3464 =
                                let uu____3467 =
                                  let uu____3468 =
                                    let uu____3478 = FStar_List.tl args_e in
                                    (e02, uu____3478) in
                                  FStar_Syntax_Syntax.Tm_app uu____3468 in
                                FStar_Syntax_Syntax.mk uu____3467 in
                              uu____3464 None t0.FStar_Syntax_Syntax.pos in
                        encode_term e env)))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____3501),(arg,uu____3503)::[]) -> encode_term arg env
                 | uu____3521 ->
                     let uu____3529 = encode_args args_e env in
                     (match uu____3529 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____3562 = encode_term head1 env in
                            match uu____3562 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____3601 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____3601 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____3643  ->
                                                 fun uu____3644  ->
                                                   match (uu____3643,
                                                           uu____3644)
                                                   with
                                                   | ((bv,uu____3658),
                                                      (a,uu____3660)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____3674 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____3674
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____3679 =
                                            encode_term_pred None ty env
                                              app_tm in
                                          (match uu____3679 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____3689 =
                                                   let uu____3693 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____3698 =
                                                     let uu____3699 =
                                                       let uu____3700 =
                                                         let uu____3701 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____3701 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____3700 in
                                                     varops.mk_unique
                                                       uu____3699 in
                                                   (uu____3693,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____3698) in
                                                 FStar_SMTEncoding_Term.Assume
                                                   uu____3689 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____3718 = lookup_free_var_sym env fv in
                            match uu____3718 with
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
                                 FStar_Syntax_Syntax.tk = _;
                                 FStar_Syntax_Syntax.pos = _;
                                 FStar_Syntax_Syntax.vars = _;_},_)
                              |FStar_Syntax_Syntax.Tm_name x ->
                                Some (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_uinst
                              ({
                                 FStar_Syntax_Syntax.n =
                                   FStar_Syntax_Syntax.Tm_fvar fv;
                                 FStar_Syntax_Syntax.tk = _;
                                 FStar_Syntax_Syntax.pos = _;
                                 FStar_Syntax_Syntax.vars = _;_},_)
                              |FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____3756 =
                                  let uu____3757 =
                                    let uu____3760 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____3760 Prims.fst in
                                  FStar_All.pipe_right uu____3757 Prims.snd in
                                Some uu____3756
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3779,(FStar_Util.Inl t1,uu____3781),uu____3782)
                                -> Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3820,(FStar_Util.Inr c,uu____3822),uu____3823)
                                -> Some (FStar_Syntax_Util.comp_result c)
                            | uu____3861 -> None in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type1 ->
                               let head_type2 =
                                 let uu____3881 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____3881 in
                               let uu____3882 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____3882 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                       ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.tk = _;
                                          FStar_Syntax_Syntax.pos = _;
                                          FStar_Syntax_Syntax.vars = _;_},_)
                                       |FStar_Syntax_Syntax.Tm_fvar fv when
                                         (FStar_List.length formals) =
                                           (FStar_List.length args)
                                         ->
                                         encode_full_app
                                           fv.FStar_Syntax_Syntax.fv_name
                                     | uu____3907 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____3952 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____3952 with
            | (bs1,body1,opening) ->
                let fallback uu____3967 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding")) in
                  let uu____3972 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____3972, [decl]) in
                let is_impure lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____3983 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp lc1 in
                      Prims.op_Negation uu____3983
                  | FStar_Util.Inr (eff,uu____3985) ->
                      let uu____3991 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff in
                      FStar_All.pipe_right uu____3991 Prims.op_Negation in
                let reify_comp_and_body env1 c body2 =
                  let reified_body = reify_body env1.tcenv body2 in
                  let c1 =
                    match c with
                    | FStar_Util.Inl lc ->
                        let typ =
                          let uu____4036 = lc.FStar_Syntax_Syntax.comp () in
                          FStar_TypeChecker_Env.reify_comp
                            (let uu___150_4037 = env1.tcenv in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___150_4037.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___150_4037.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___150_4037.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___150_4037.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___150_4037.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___150_4037.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___150_4037.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___150_4037.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___150_4037.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___150_4037.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___150_4037.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___150_4037.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___150_4037.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___150_4037.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___150_4037.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___150_4037.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___150_4037.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___150_4037.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___150_4037.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___150_4037.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___150_4037.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___150_4037.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___150_4037.FStar_TypeChecker_Env.qname_and_index)
                             }) uu____4036 FStar_Syntax_Syntax.U_unknown in
                        let uu____4038 =
                          let uu____4039 = FStar_Syntax_Syntax.mk_Total typ in
                          FStar_Syntax_Util.lcomp_of_comp uu____4039 in
                        FStar_Util.Inl uu____4038
                    | FStar_Util.Inr (eff_name,uu____4046) -> c in
                  (c1, reified_body) in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4077 =
                        let uu____4078 = lc1.FStar_Syntax_Syntax.comp () in
                        FStar_Syntax_Subst.subst_comp opening uu____4078 in
                      FStar_All.pipe_right uu____4077
                        (fun _0_31  -> Some _0_31)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar1 uu____4090 =
                        let uu____4091 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____4091 Prims.fst in
                      if
                        FStar_Ident.lid_equals eff
                          FStar_Syntax_Const.effect_Tot_lid
                      then
                        let uu____4099 =
                          let uu____4100 = new_uvar1 () in
                          FStar_Syntax_Syntax.mk_Total uu____4100 in
                        FStar_All.pipe_right uu____4099
                          (fun _0_32  -> Some _0_32)
                      else
                        if
                          FStar_Ident.lid_equals eff
                            FStar_Syntax_Const.effect_GTot_lid
                        then
                          (let uu____4104 =
                             let uu____4105 = new_uvar1 () in
                             FStar_Syntax_Syntax.mk_GTotal uu____4105 in
                           FStar_All.pipe_right uu____4104
                             (fun _0_33  -> Some _0_33))
                        else None in
                (match lopt with
                 | None  ->
                     ((let uu____4116 =
                         let uu____4117 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____4117 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____4116);
                      fallback ())
                 | Some lc ->
                     let lc1 = lc in
                     let uu____4132 =
                       (is_impure lc1) &&
                         (let uu____4133 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv lc1 in
                          Prims.op_Negation uu____4133) in
                     if uu____4132
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____4143 = encode_binders None bs1 env in
                        match uu____4143 with
                        | (vars,guards,envbody,decls,uu____4158) ->
                            let uu____4165 =
                              let uu____4173 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  lc1 in
                              if uu____4173
                              then reify_comp_and_body envbody lc1 body1
                              else (lc1, body1) in
                            (match uu____4165 with
                             | (lc2,body2) ->
                                 let uu____4198 = encode_term body2 envbody in
                                 (match uu____4198 with
                                  | (body3,decls') ->
                                      let uu____4205 =
                                        let uu____4210 = codomain_eff lc2 in
                                        match uu____4210 with
                                        | None  -> (None, [])
                                        | Some c ->
                                            let tfun =
                                              FStar_Syntax_Util.arrow bs1 c in
                                            let uu____4222 =
                                              encode_term tfun env in
                                            (match uu____4222 with
                                             | (t1,decls1) ->
                                                 ((Some t1), decls1)) in
                                      (match uu____4205 with
                                       | (arrow_t_opt,decls'') ->
                                           let key_body =
                                             let uu____4241 =
                                               let uu____4247 =
                                                 let uu____4248 =
                                                   let uu____4251 =
                                                     FStar_SMTEncoding_Util.mk_and_l
                                                       guards in
                                                   (uu____4251, body3) in
                                                 FStar_SMTEncoding_Util.mkImp
                                                   uu____4248 in
                                               ([], vars, uu____4247) in
                                             FStar_SMTEncoding_Util.mkForall
                                               uu____4241 in
                                           let cvars =
                                             FStar_SMTEncoding_Term.free_variables
                                               key_body in
                                           let cvars1 =
                                             match arrow_t_opt with
                                             | None  -> cvars
                                             | Some t1 ->
                                                 let uu____4259 =
                                                   let uu____4261 =
                                                     FStar_SMTEncoding_Term.free_variables
                                                       t1 in
                                                   FStar_List.append
                                                     uu____4261 cvars in
                                                 FStar_Util.remove_dups
                                                   FStar_SMTEncoding_Term.fv_eq
                                                   uu____4259 in
                                           let tkey =
                                             FStar_SMTEncoding_Util.mkForall
                                               ([], cvars1, key_body) in
                                           let tkey_hash =
                                             FStar_SMTEncoding_Term.hash_of_term
                                               tkey in
                                           let uu____4272 =
                                             FStar_Util.smap_try_find
                                               env.cache tkey_hash in
                                           (match uu____4272 with
                                            | Some (t1,uu____4287,uu____4288)
                                                ->
                                                let uu____4298 =
                                                  let uu____4299 =
                                                    let uu____4303 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    (t1, uu____4303) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____4299 in
                                                (uu____4298, [])
                                            | None  ->
                                                let uu____4314 =
                                                  is_an_eta_expansion env
                                                    vars body3 in
                                                (match uu____4314 with
                                                 | Some t1 ->
                                                     let decls1 =
                                                       let uu____4321 =
                                                         let uu____4322 =
                                                           FStar_Util.smap_size
                                                             env.cache in
                                                         uu____4322 =
                                                           cache_size in
                                                       if uu____4321
                                                       then []
                                                       else
                                                         FStar_List.append
                                                           decls decls' in
                                                     (t1, decls1)
                                                 | None  ->
                                                     let cvar_sorts =
                                                       FStar_List.map
                                                         Prims.snd cvars1 in
                                                     let fsym =
                                                       let module_name =
                                                         env.current_module_name in
                                                       let fsym =
                                                         let uu____4338 =
                                                           let uu____4339 =
                                                             FStar_Util.digest_of_string
                                                               tkey_hash in
                                                           Prims.strcat
                                                             "Tm_abs_"
                                                             uu____4339 in
                                                         varops.mk_unique
                                                           uu____4338 in
                                                       Prims.strcat
                                                         module_name
                                                         (Prims.strcat "_"
                                                            fsym) in
                                                     let fdecl =
                                                       FStar_SMTEncoding_Term.DeclFun
                                                         (fsym, cvar_sorts,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           None) in
                                                     let f =
                                                       let uu____4344 =
                                                         let uu____4348 =
                                                           FStar_List.map
                                                             FStar_SMTEncoding_Util.mkFreeV
                                                             cvars1 in
                                                         (fsym, uu____4348) in
                                                       FStar_SMTEncoding_Util.mkApp
                                                         uu____4344 in
                                                     let app =
                                                       mk_Apply f vars in
                                                     let typing_f =
                                                       match arrow_t_opt with
                                                       | None  -> []
                                                       | Some t1 ->
                                                           let f_has_t =
                                                             FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                               None f t1 in
                                                           let a_name =
                                                             Prims.strcat
                                                               "typing_" fsym in
                                                           let uu____4360 =
                                                             let uu____4361 =
                                                               let uu____4365
                                                                 =
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   ([[f]],
                                                                    cvars1,
                                                                    f_has_t) in
                                                               (uu____4365,
                                                                 (Some a_name),
                                                                 a_name) in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____4361 in
                                                           [uu____4360] in
                                                     let interp_f =
                                                       let a_name =
                                                         Prims.strcat
                                                           "interpretation_"
                                                           fsym in
                                                       let uu____4373 =
                                                         let uu____4377 =
                                                           let uu____4378 =
                                                             let uu____4384 =
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (app, body3) in
                                                             ([[app]],
                                                               (FStar_List.append
                                                                  vars cvars1),
                                                               uu____4384) in
                                                           FStar_SMTEncoding_Util.mkForall
                                                             uu____4378 in
                                                         (uu____4377,
                                                           (Some a_name),
                                                           a_name) in
                                                       FStar_SMTEncoding_Term.Assume
                                                         uu____4373 in
                                                     let f_decls =
                                                       FStar_List.append
                                                         decls
                                                         (FStar_List.append
                                                            decls'
                                                            (FStar_List.append
                                                               decls''
                                                               (FStar_List.append
                                                                  (fdecl ::
                                                                  typing_f)
                                                                  [interp_f]))) in
                                                     (FStar_Util.smap_add
                                                        env.cache tkey_hash
                                                        (fsym, cvar_sorts,
                                                          f_decls);
                                                      (f, f_decls))))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____4402,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____4403;
                          FStar_Syntax_Syntax.lbunivs = uu____4404;
                          FStar_Syntax_Syntax.lbtyp = uu____4405;
                          FStar_Syntax_Syntax.lbeff = uu____4406;
                          FStar_Syntax_Syntax.lbdef = uu____4407;_}::uu____4408),uu____4409)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____4427;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____4429;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____4445 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None) in
             let uu____4458 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____4458, [decl_e])))
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
                 (FStar_SMTEncoding_Term.term*
                   FStar_SMTEncoding_Term.decls_t))
              ->
              (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun x  ->
    fun t1  ->
      fun e1  ->
        fun e2  ->
          fun env  ->
            fun encode_body  ->
              let uu____4500 = encode_term e1 env in
              match uu____4500 with
              | (ee1,decls1) ->
                  let uu____4507 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2 in
                  (match uu____4507 with
                   | (xs,e21) ->
                       let uu____4521 = FStar_List.hd xs in
                       (match uu____4521 with
                        | (x1,uu____4529) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____4531 = encode_body e21 env' in
                            (match uu____4531 with
                             | (ee2,decls2) ->
                                 (ee2, (FStar_List.append decls1 decls2)))))
and encode_match:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.branch Prims.list ->
      FStar_SMTEncoding_Term.term ->
        env_t ->
          (FStar_Syntax_Syntax.term ->
             env_t ->
               (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t))
            -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun e  ->
    fun pats  ->
      fun default_case  ->
        fun env  ->
          fun encode_br  ->
            let uu____4553 =
              let uu____4557 =
                let uu____4558 =
                  (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown)
                    None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____4558 in
              gen_term_var env uu____4557 in
            match uu____4553 with
            | (scrsym,scr',env1) ->
                let uu____4572 = encode_term e env1 in
                (match uu____4572 with
                 | (scr,decls) ->
                     let uu____4579 =
                       let encode_branch b uu____4595 =
                         match uu____4595 with
                         | (else_case,decls1) ->
                             let uu____4606 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____4606 with
                              | (p,w,br) ->
                                  let patterns = encode_pat env1 p in
                                  FStar_List.fold_right
                                    (fun uu____4636  ->
                                       fun uu____4637  ->
                                         match (uu____4636, uu____4637) with
                                         | ((env0,pattern),(else_case1,decls2))
                                             ->
                                             let guard = pattern.guard scr' in
                                             let projections =
                                               pattern.projections scr' in
                                             let env2 =
                                               FStar_All.pipe_right
                                                 projections
                                                 (FStar_List.fold_left
                                                    (fun env2  ->
                                                       fun uu____4674  ->
                                                         match uu____4674
                                                         with
                                                         | (x,t) ->
                                                             push_term_var
                                                               env2 x t) env1) in
                                             let uu____4679 =
                                               match w with
                                               | None  -> (guard, [])
                                               | Some w1 ->
                                                   let uu____4694 =
                                                     encode_term w1 env2 in
                                                   (match uu____4694 with
                                                    | (w2,decls21) ->
                                                        let uu____4702 =
                                                          let uu____4703 =
                                                            let uu____4706 =
                                                              let uu____4707
                                                                =
                                                                let uu____4710
                                                                  =
                                                                  FStar_SMTEncoding_Term.boxBool
                                                                    FStar_SMTEncoding_Util.mkTrue in
                                                                (w2,
                                                                  uu____4710) in
                                                              FStar_SMTEncoding_Util.mkEq
                                                                uu____4707 in
                                                            (guard,
                                                              uu____4706) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____4703 in
                                                        (uu____4702, decls21)) in
                                             (match uu____4679 with
                                              | (guard1,decls21) ->
                                                  let uu____4718 =
                                                    encode_br br env2 in
                                                  (match uu____4718 with
                                                   | (br1,decls3) ->
                                                       let uu____4726 =
                                                         FStar_SMTEncoding_Util.mkITE
                                                           (guard1, br1,
                                                             else_case1) in
                                                       (uu____4726,
                                                         (FStar_List.append
                                                            decls2
                                                            (FStar_List.append
                                                               decls21 decls3))))))
                                    patterns (else_case, decls1)) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____4579 with
                      | (match_tm,decls1) ->
                          let uu____4738 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____4738, decls1)))
and encode_pat:
  env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) Prims.list =
  fun env  ->
    fun pat  ->
      match pat.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj ps ->
          FStar_List.map (encode_one_pat env) ps
      | uu____4769 -> let uu____4770 = encode_one_pat env pat in [uu____4770]
and encode_one_pat: env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) =
  fun env  ->
    fun pat  ->
      (let uu____4782 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____4782
       then
         let uu____4783 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____4783
       else ());
      (let uu____4785 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____4785 with
       | (vars,pat_term) ->
           let uu____4795 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____4818  ->
                     fun v1  ->
                       match uu____4818 with
                       | (env1,vars1) ->
                           let uu____4846 = gen_term_var env1 v1 in
                           (match uu____4846 with
                            | (xx,uu____4858,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____4795 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4905 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_var _
                    |FStar_Syntax_Syntax.Pat_wild _
                     |FStar_Syntax_Syntax.Pat_dot_term _ ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____4913 =
                        let uu____4916 = encode_const c in
                        (scrutinee, uu____4916) in
                      FStar_SMTEncoding_Util.mkEq uu____4913
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____4935 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____4935 with
                        | (uu____4939,uu____4940::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____4942 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4963  ->
                                  match uu____4963 with
                                  | (arg,uu____4969) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____4979 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____4979)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4998 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_dot_term (x,_)
                    |FStar_Syntax_Syntax.Pat_var x
                     |FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____5013 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____5028 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5050  ->
                                  match uu____5050 with
                                  | (arg,uu____5059) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5069 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____5069)) in
                      FStar_All.pipe_right uu____5028 FStar_List.flatten in
                let pat_term1 uu____5085 = encode_term pat_term env1 in
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
      (FStar_SMTEncoding_Term.term Prims.list*
        FStar_SMTEncoding_Term.decls_t)
  =
  fun l  ->
    fun env  ->
      let uu____5092 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____5107  ->
                fun uu____5108  ->
                  match (uu____5107, uu____5108) with
                  | ((tms,decls),(t,uu____5128)) ->
                      let uu____5139 = encode_term t env in
                      (match uu____5139 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____5092 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_SMTEncoding_Term.term Prims.option ->
    FStar_Syntax_Syntax.term Prims.option ->
      FStar_Syntax_Syntax.typ ->
        env_t ->
          (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun induction_on  ->
    fun new_pats  ->
      fun t  ->
        fun env  ->
          let list_elements1 e =
            let uu____5177 = FStar_Syntax_Util.list_elements e in
            match uu____5177 with
            | Some l -> l
            | None  ->
                (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
                   "SMT pattern is not a list literal; ignoring the pattern";
                 []) in
          let one_pat p =
            let uu____5195 =
              let uu____5205 = FStar_Syntax_Util.unmeta p in
              FStar_All.pipe_right uu____5205 FStar_Syntax_Util.head_and_args in
            match uu____5195 with
            | (head1,args) ->
                let uu____5236 =
                  let uu____5244 =
                    let uu____5245 = FStar_Syntax_Util.un_uinst head1 in
                    uu____5245.FStar_Syntax_Syntax.n in
                  (uu____5244, args) in
                (match uu____5236 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(uu____5259,uu____5260)::(e,uu____5262)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpat_lid
                     -> (e, None)
                 | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5293)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpatT_lid
                     -> (e, None)
                 | uu____5314 -> failwith "Unexpected pattern term") in
          let lemma_pats p =
            let elts = list_elements1 p in
            let smt_pat_or t1 =
              let uu____5347 =
                let uu____5357 = FStar_Syntax_Util.unmeta t1 in
                FStar_All.pipe_right uu____5357
                  FStar_Syntax_Util.head_and_args in
              match uu____5347 with
              | (head1,args) ->
                  let uu____5386 =
                    let uu____5394 =
                      let uu____5395 = FStar_Syntax_Util.un_uinst head1 in
                      uu____5395.FStar_Syntax_Syntax.n in
                    (uu____5394, args) in
                  (match uu____5386 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5408)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.smtpatOr_lid
                       -> Some e
                   | uu____5428 -> None) in
            match elts with
            | t1::[] ->
                let uu____5446 = smt_pat_or t1 in
                (match uu____5446 with
                 | Some e ->
                     let uu____5462 = list_elements1 e in
                     FStar_All.pipe_right uu____5462
                       (FStar_List.map
                          (fun branch1  ->
                             let uu____5479 = list_elements1 branch1 in
                             FStar_All.pipe_right uu____5479
                               (FStar_List.map one_pat)))
                 | uu____5493 ->
                     let uu____5497 =
                       FStar_All.pipe_right elts (FStar_List.map one_pat) in
                     [uu____5497])
            | uu____5528 ->
                let uu____5530 =
                  FStar_All.pipe_right elts (FStar_List.map one_pat) in
                [uu____5530] in
          let uu____5561 =
            let uu____5577 =
              let uu____5578 = FStar_Syntax_Subst.compress t in
              uu____5578.FStar_Syntax_Syntax.n in
            match uu____5577 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____5608 = FStar_Syntax_Subst.open_comp binders c in
                (match uu____5608 with
                 | (binders1,c1) ->
                     (match c1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Comp
                          { FStar_Syntax_Syntax.comp_univs = uu____5643;
                            FStar_Syntax_Syntax.effect_name = uu____5644;
                            FStar_Syntax_Syntax.result_typ = uu____5645;
                            FStar_Syntax_Syntax.effect_args =
                              (pre,uu____5647)::(post,uu____5649)::(pats,uu____5651)::[];
                            FStar_Syntax_Syntax.flags = uu____5652;_}
                          ->
                          let pats' =
                            match new_pats with
                            | Some new_pats' -> new_pats'
                            | None  -> pats in
                          let uu____5686 = lemma_pats pats' in
                          (binders1, pre, post, uu____5686)
                      | uu____5705 -> failwith "impos"))
            | uu____5721 -> failwith "Impos" in
          match uu____5561 with
          | (binders,pre,post,patterns) ->
              let uu____5765 = encode_binders None binders env in
              (match uu____5765 with
               | (vars,guards,env1,decls,uu____5780) ->
                   let uu____5787 =
                     let uu____5794 =
                       FStar_All.pipe_right patterns
                         (FStar_List.map
                            (fun branch1  ->
                               let uu____5825 =
                                 let uu____5830 =
                                   FStar_All.pipe_right branch1
                                     (FStar_List.map
                                        (fun uu____5846  ->
                                           match uu____5846 with
                                           | (t1,uu____5853) ->
                                               encode_term t1
                                                 (let uu___151_5856 = env1 in
                                                  {
                                                    bindings =
                                                      (uu___151_5856.bindings);
                                                    depth =
                                                      (uu___151_5856.depth);
                                                    tcenv =
                                                      (uu___151_5856.tcenv);
                                                    warn =
                                                      (uu___151_5856.warn);
                                                    cache =
                                                      (uu___151_5856.cache);
                                                    nolabels =
                                                      (uu___151_5856.nolabels);
                                                    use_zfuel_name = true;
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___151_5856.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___151_5856.current_module_name)
                                                  }))) in
                                 FStar_All.pipe_right uu____5830
                                   FStar_List.unzip in
                               match uu____5825 with
                               | (pats,decls1) -> (pats, decls1))) in
                     FStar_All.pipe_right uu____5794 FStar_List.unzip in
                   (match uu____5787 with
                    | (pats,decls') ->
                        let decls'1 = FStar_List.flatten decls' in
                        let pats1 =
                          match induction_on with
                          | None  -> pats
                          | Some e ->
                              (match vars with
                               | [] -> pats
                               | l::[] ->
                                   FStar_All.pipe_right pats
                                     (FStar_List.map
                                        (fun p  ->
                                           let uu____5920 =
                                             let uu____5921 =
                                               FStar_SMTEncoding_Util.mkFreeV
                                                 l in
                                             FStar_SMTEncoding_Util.mk_Precedes
                                               uu____5921 e in
                                           uu____5920 :: p))
                               | uu____5922 ->
                                   let rec aux tl1 vars1 =
                                     match vars1 with
                                     | [] ->
                                         FStar_All.pipe_right pats
                                           (FStar_List.map
                                              (fun p  ->
                                                 let uu____5951 =
                                                   FStar_SMTEncoding_Util.mk_Precedes
                                                     tl1 e in
                                                 uu____5951 :: p))
                                     | (x,FStar_SMTEncoding_Term.Term_sort )::vars2
                                         ->
                                         let uu____5959 =
                                           let uu____5960 =
                                             FStar_SMTEncoding_Util.mkFreeV
                                               (x,
                                                 FStar_SMTEncoding_Term.Term_sort) in
                                           FStar_SMTEncoding_Util.mk_LexCons
                                             uu____5960 tl1 in
                                         aux uu____5959 vars2
                                     | uu____5961 -> pats in
                                   let uu____5965 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       ("Prims.LexTop",
                                         FStar_SMTEncoding_Term.Term_sort) in
                                   aux uu____5965 vars) in
                        let env2 =
                          let uu___152_5967 = env1 in
                          {
                            bindings = (uu___152_5967.bindings);
                            depth = (uu___152_5967.depth);
                            tcenv = (uu___152_5967.tcenv);
                            warn = (uu___152_5967.warn);
                            cache = (uu___152_5967.cache);
                            nolabels = true;
                            use_zfuel_name = (uu___152_5967.use_zfuel_name);
                            encode_non_total_function_typ =
                              (uu___152_5967.encode_non_total_function_typ);
                            current_module_name =
                              (uu___152_5967.current_module_name)
                          } in
                        let uu____5968 =
                          let uu____5971 = FStar_Syntax_Util.unmeta pre in
                          encode_formula uu____5971 env2 in
                        (match uu____5968 with
                         | (pre1,decls'') ->
                             let uu____5976 =
                               let uu____5979 = FStar_Syntax_Util.unmeta post in
                               encode_formula uu____5979 env2 in
                             (match uu____5976 with
                              | (post1,decls''') ->
                                  let decls1 =
                                    FStar_List.append decls
                                      (FStar_List.append
                                         (FStar_List.flatten decls'1)
                                         (FStar_List.append decls'' decls''')) in
                                  let uu____5986 =
                                    let uu____5987 =
                                      let uu____5993 =
                                        let uu____5994 =
                                          let uu____5997 =
                                            FStar_SMTEncoding_Util.mk_and_l
                                              (pre1 :: guards) in
                                          (uu____5997, post1) in
                                        FStar_SMTEncoding_Util.mkImp
                                          uu____5994 in
                                      (pats1, vars, uu____5993) in
                                    FStar_SMTEncoding_Util.mkForall
                                      uu____5987 in
                                  (uu____5986, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____6010 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____6010
        then
          let uu____6011 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____6012 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____6011 uu____6012
        else () in
      let enc f r l =
        let uu____6039 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____6052 = encode_term (Prims.fst x) env in
                 match uu____6052 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____6039 with
        | (decls,args) ->
            let uu____6069 =
              let uu___153_6070 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___153_6070.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___153_6070.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6069, decls) in
      let const_op f r uu____6089 = let uu____6092 = f r in (uu____6092, []) in
      let un_op f l =
        let uu____6108 = FStar_List.hd l in FStar_All.pipe_left f uu____6108 in
      let bin_op f uu___125_6121 =
        match uu___125_6121 with
        | t1::t2::[] -> f (t1, t2)
        | uu____6129 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____6156 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____6165  ->
                 match uu____6165 with
                 | (t,uu____6173) ->
                     let uu____6174 = encode_formula t env in
                     (match uu____6174 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____6156 with
        | (decls,phis) ->
            let uu____6191 =
              let uu___154_6192 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___154_6192.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___154_6192.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6191, decls) in
      let eq_op r uu___126_6208 =
        match uu___126_6208 with
        | _::e1::e2::[]|_::_::e1::e2::[] ->
            let uu____6268 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6268 r [e1; e2]
        | l ->
            let uu____6288 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6288 r l in
      let mk_imp1 r uu___127_6307 =
        match uu___127_6307 with
        | (lhs,uu____6311)::(rhs,uu____6313)::[] ->
            let uu____6334 = encode_formula rhs env in
            (match uu____6334 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6343) ->
                      (l1, decls1)
                  | uu____6346 ->
                      let uu____6347 = encode_formula lhs env in
                      (match uu____6347 with
                       | (l2,decls2) ->
                           let uu____6354 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____6354, (FStar_List.append decls1 decls2)))))
        | uu____6356 -> failwith "impossible" in
      let mk_ite r uu___128_6371 =
        match uu___128_6371 with
        | (guard,uu____6375)::(_then,uu____6377)::(_else,uu____6379)::[] ->
            let uu____6408 = encode_formula guard env in
            (match uu____6408 with
             | (g,decls1) ->
                 let uu____6415 = encode_formula _then env in
                 (match uu____6415 with
                  | (t,decls2) ->
                      let uu____6422 = encode_formula _else env in
                      (match uu____6422 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6431 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____6450 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____6450 in
      let connectives =
        let uu____6462 =
          let uu____6471 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Syntax_Const.and_lid, uu____6471) in
        let uu____6484 =
          let uu____6494 =
            let uu____6503 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Syntax_Const.or_lid, uu____6503) in
          let uu____6516 =
            let uu____6526 =
              let uu____6536 =
                let uu____6545 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Syntax_Const.iff_lid, uu____6545) in
              let uu____6558 =
                let uu____6568 =
                  let uu____6578 =
                    let uu____6587 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Syntax_Const.not_lid, uu____6587) in
                  [uu____6578;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____6568 in
              uu____6536 :: uu____6558 in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____6526 in
          uu____6494 :: uu____6516 in
        uu____6462 :: uu____6484 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____6749 = encode_formula phi' env in
            (match uu____6749 with
             | (phi2,decls) ->
                 let uu____6756 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____6756, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____6757 ->
            let uu____6762 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____6762 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____6791 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____6791 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____6799;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____6801;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____6817 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____6817 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____6849::(x,uu____6851)::(t,uu____6853)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____6887 = encode_term x env in
                 (match uu____6887 with
                  | (x1,decls) ->
                      let uu____6894 = encode_term t env in
                      (match uu____6894 with
                       | (t1,decls') ->
                           let uu____6901 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____6901, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____6905)::(msg,uu____6907)::(phi2,uu____6909)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____6943 =
                   let uu____6946 =
                     let uu____6947 = FStar_Syntax_Subst.compress r in
                     uu____6947.FStar_Syntax_Syntax.n in
                   let uu____6950 =
                     let uu____6951 = FStar_Syntax_Subst.compress msg in
                     uu____6951.FStar_Syntax_Syntax.n in
                   (uu____6946, uu____6950) in
                 (match uu____6943 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____6958))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r1,
                                     false))))) None r1 in
                      fallback phi3
                  | uu____6974 -> fallback phi2)
             | uu____6977 when head_redex env head2 ->
                 let uu____6985 = whnf env phi1 in
                 encode_formula uu____6985 env
             | uu____6986 ->
                 let uu____6994 = encode_term phi1 env in
                 (match uu____6994 with
                  | (tt,decls) ->
                      let uu____7001 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___155_7002 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___155_7002.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___155_7002.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____7001, decls)))
        | uu____7005 ->
            let uu____7006 = encode_term phi1 env in
            (match uu____7006 with
             | (tt,decls) ->
                 let uu____7013 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___156_7014 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___156_7014.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___156_7014.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____7013, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____7041 = encode_binders None bs env1 in
        match uu____7041 with
        | (vars,guards,env2,decls,uu____7063) ->
            let uu____7070 =
              let uu____7077 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____7100 =
                          let uu____7105 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____7119  ->
                                    match uu____7119 with
                                    | (t,uu____7125) ->
                                        encode_term t
                                          (let uu___157_7126 = env2 in
                                           {
                                             bindings =
                                               (uu___157_7126.bindings);
                                             depth = (uu___157_7126.depth);
                                             tcenv = (uu___157_7126.tcenv);
                                             warn = (uu___157_7126.warn);
                                             cache = (uu___157_7126.cache);
                                             nolabels =
                                               (uu___157_7126.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___157_7126.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___157_7126.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____7105 FStar_List.unzip in
                        match uu____7100 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____7077 FStar_List.unzip in
            (match uu____7070 with
             | (pats,decls') ->
                 let uu____7178 = encode_formula body env2 in
                 (match uu____7178 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____7197;
                             FStar_SMTEncoding_Term.rng = uu____7198;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____7206 -> guards in
                      let uu____7209 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____7209, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____7243  ->
                   match uu____7243 with
                   | (x,uu____7247) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____7253 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7259 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____7259) uu____7253 tl1 in
             let uu____7261 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7273  ->
                       match uu____7273 with
                       | (b,uu____7277) ->
                           let uu____7278 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____7278)) in
             (match uu____7261 with
              | None  -> ()
              | Some (x,uu____7282) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____7292 =
                    let uu____7293 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7293 in
                  FStar_Errors.warn pos uu____7292) in
       let uu____7294 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____7294 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____7300 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7336  ->
                     match uu____7336 with
                     | (l,uu____7346) -> FStar_Ident.lid_equals op l)) in
           (match uu____7300 with
            | None  -> fallback phi1
            | Some (uu____7369,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7398 = encode_q_body env vars pats body in
             match uu____7398 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____7424 =
                     let uu____7430 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____7430) in
                   FStar_SMTEncoding_Term.mkForall uu____7424
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7442 = encode_q_body env vars pats body in
             match uu____7442 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____7467 =
                   let uu____7468 =
                     let uu____7474 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____7474) in
                   FStar_SMTEncoding_Term.mkExists uu____7468
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____7467, decls))))
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decl Prims.list);
  is: FStar_Ident.lident -> Prims.bool;}
let prims: prims_t =
  let uu____7523 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____7523 with
  | (asym,a) ->
      let uu____7528 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____7528 with
       | (xsym,x) ->
           let uu____7533 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____7533 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____7563 =
                      let uu____7569 =
                        FStar_All.pipe_right vars (FStar_List.map Prims.snd) in
                      (x1, uu____7569, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____7563 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None) in
                  let xapp =
                    let uu____7584 =
                      let uu____7588 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____7588) in
                    FStar_SMTEncoding_Util.mkApp uu____7584 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____7596 =
                    let uu____7598 =
                      let uu____7600 =
                        let uu____7602 =
                          let uu____7603 =
                            let uu____7607 =
                              let uu____7608 =
                                let uu____7614 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____7614) in
                              FStar_SMTEncoding_Util.mkForall uu____7608 in
                            (uu____7607, None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Term.Assume uu____7603 in
                        let uu____7623 =
                          let uu____7625 =
                            let uu____7626 =
                              let uu____7630 =
                                let uu____7631 =
                                  let uu____7637 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____7637) in
                                FStar_SMTEncoding_Util.mkForall uu____7631 in
                              (uu____7630,
                                (Some "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Term.Assume uu____7626 in
                          [uu____7625] in
                        uu____7602 :: uu____7623 in
                      xtok_decl :: uu____7600 in
                    xname_decl :: uu____7598 in
                  (xtok1, uu____7596) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____7686 =
                    let uu____7694 =
                      let uu____7700 =
                        let uu____7701 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____7701 in
                      quant axy uu____7700 in
                    (FStar_Syntax_Const.op_Eq, uu____7694) in
                  let uu____7707 =
                    let uu____7716 =
                      let uu____7724 =
                        let uu____7730 =
                          let uu____7731 =
                            let uu____7732 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____7732 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____7731 in
                        quant axy uu____7730 in
                      (FStar_Syntax_Const.op_notEq, uu____7724) in
                    let uu____7738 =
                      let uu____7747 =
                        let uu____7755 =
                          let uu____7761 =
                            let uu____7762 =
                              let uu____7763 =
                                let uu____7766 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____7767 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____7766, uu____7767) in
                              FStar_SMTEncoding_Util.mkLT uu____7763 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____7762 in
                          quant xy uu____7761 in
                        (FStar_Syntax_Const.op_LT, uu____7755) in
                      let uu____7773 =
                        let uu____7782 =
                          let uu____7790 =
                            let uu____7796 =
                              let uu____7797 =
                                let uu____7798 =
                                  let uu____7801 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____7802 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____7801, uu____7802) in
                                FStar_SMTEncoding_Util.mkLTE uu____7798 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____7797 in
                            quant xy uu____7796 in
                          (FStar_Syntax_Const.op_LTE, uu____7790) in
                        let uu____7808 =
                          let uu____7817 =
                            let uu____7825 =
                              let uu____7831 =
                                let uu____7832 =
                                  let uu____7833 =
                                    let uu____7836 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____7837 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____7836, uu____7837) in
                                  FStar_SMTEncoding_Util.mkGT uu____7833 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____7832 in
                              quant xy uu____7831 in
                            (FStar_Syntax_Const.op_GT, uu____7825) in
                          let uu____7843 =
                            let uu____7852 =
                              let uu____7860 =
                                let uu____7866 =
                                  let uu____7867 =
                                    let uu____7868 =
                                      let uu____7871 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____7872 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____7871, uu____7872) in
                                    FStar_SMTEncoding_Util.mkGTE uu____7868 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____7867 in
                                quant xy uu____7866 in
                              (FStar_Syntax_Const.op_GTE, uu____7860) in
                            let uu____7878 =
                              let uu____7887 =
                                let uu____7895 =
                                  let uu____7901 =
                                    let uu____7902 =
                                      let uu____7903 =
                                        let uu____7906 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____7907 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____7906, uu____7907) in
                                      FStar_SMTEncoding_Util.mkSub uu____7903 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____7902 in
                                  quant xy uu____7901 in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____7895) in
                              let uu____7913 =
                                let uu____7922 =
                                  let uu____7930 =
                                    let uu____7936 =
                                      let uu____7937 =
                                        let uu____7938 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____7938 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____7937 in
                                    quant qx uu____7936 in
                                  (FStar_Syntax_Const.op_Minus, uu____7930) in
                                let uu____7944 =
                                  let uu____7953 =
                                    let uu____7961 =
                                      let uu____7967 =
                                        let uu____7968 =
                                          let uu____7969 =
                                            let uu____7972 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____7973 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____7972, uu____7973) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____7969 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____7968 in
                                      quant xy uu____7967 in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____7961) in
                                  let uu____7979 =
                                    let uu____7988 =
                                      let uu____7996 =
                                        let uu____8002 =
                                          let uu____8003 =
                                            let uu____8004 =
                                              let uu____8007 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____8008 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____8007, uu____8008) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____8004 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____8003 in
                                        quant xy uu____8002 in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____7996) in
                                    let uu____8014 =
                                      let uu____8023 =
                                        let uu____8031 =
                                          let uu____8037 =
                                            let uu____8038 =
                                              let uu____8039 =
                                                let uu____8042 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____8043 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____8042, uu____8043) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____8039 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____8038 in
                                          quant xy uu____8037 in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____8031) in
                                      let uu____8049 =
                                        let uu____8058 =
                                          let uu____8066 =
                                            let uu____8072 =
                                              let uu____8073 =
                                                let uu____8074 =
                                                  let uu____8077 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____8078 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____8077, uu____8078) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____8074 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____8073 in
                                            quant xy uu____8072 in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____8066) in
                                        let uu____8084 =
                                          let uu____8093 =
                                            let uu____8101 =
                                              let uu____8107 =
                                                let uu____8108 =
                                                  let uu____8109 =
                                                    let uu____8112 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____8113 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____8112, uu____8113) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____8109 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____8108 in
                                              quant xy uu____8107 in
                                            (FStar_Syntax_Const.op_And,
                                              uu____8101) in
                                          let uu____8119 =
                                            let uu____8128 =
                                              let uu____8136 =
                                                let uu____8142 =
                                                  let uu____8143 =
                                                    let uu____8144 =
                                                      let uu____8147 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____8148 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____8147,
                                                        uu____8148) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____8144 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____8143 in
                                                quant xy uu____8142 in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____8136) in
                                            let uu____8154 =
                                              let uu____8163 =
                                                let uu____8171 =
                                                  let uu____8177 =
                                                    let uu____8178 =
                                                      let uu____8179 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____8179 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____8178 in
                                                  quant qx uu____8177 in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____8171) in
                                              [uu____8163] in
                                            uu____8128 :: uu____8154 in
                                          uu____8093 :: uu____8119 in
                                        uu____8058 :: uu____8084 in
                                      uu____8023 :: uu____8049 in
                                    uu____7988 :: uu____8014 in
                                  uu____7953 :: uu____7979 in
                                uu____7922 :: uu____7944 in
                              uu____7887 :: uu____7913 in
                            uu____7852 :: uu____7878 in
                          uu____7817 :: uu____7843 in
                        uu____7782 :: uu____7808 in
                      uu____7747 :: uu____7773 in
                    uu____7716 :: uu____7738 in
                  uu____7686 :: uu____7707 in
                let mk1 l v1 =
                  let uu____8307 =
                    let uu____8312 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____8344  ->
                              match uu____8344 with
                              | (l',uu____8353) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____8312
                      (FStar_Option.map
                         (fun uu____8386  ->
                            match uu____8386 with | (uu____8397,b) -> b v1)) in
                  FStar_All.pipe_right uu____8307 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____8438  ->
                          match uu____8438 with
                          | (l',uu____8447) -> FStar_Ident.lid_equals l l')) in
                { mk = mk1; is }))
let pretype_axiom:
  env_t ->
    FStar_SMTEncoding_Term.term ->
      (Prims.string* FStar_SMTEncoding_Term.sort) Prims.list ->
        FStar_SMTEncoding_Term.decl
  =
  fun env  ->
    fun tapp  ->
      fun vars  ->
        let uu____8473 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____8473 with
        | (xxsym,xx) ->
            let uu____8478 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____8478 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____8486 =
                   let uu____8490 =
                     let uu____8491 =
                       let uu____8497 =
                         let uu____8498 =
                           let uu____8501 =
                             let uu____8502 =
                               let uu____8505 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____8505) in
                             FStar_SMTEncoding_Util.mkEq uu____8502 in
                           (xx_has_type, uu____8501) in
                         FStar_SMTEncoding_Util.mkImp uu____8498 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____8497) in
                     FStar_SMTEncoding_Util.mkForall uu____8491 in
                   let uu____8518 =
                     let uu____8519 =
                       let uu____8520 =
                         let uu____8521 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____8521 in
                       Prims.strcat module_name uu____8520 in
                     varops.mk_unique uu____8519 in
                   (uu____8490, (Some "pretyping"), uu____8518) in
                 FStar_SMTEncoding_Term.Assume uu____8486)
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
    let uu____8551 =
      let uu____8552 =
        let uu____8556 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____8556, (Some "unit typing"), "unit_typing") in
      FStar_SMTEncoding_Term.Assume uu____8552 in
    let uu____8558 =
      let uu____8560 =
        let uu____8561 =
          let uu____8565 =
            let uu____8566 =
              let uu____8572 =
                let uu____8573 =
                  let uu____8576 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____8576) in
                FStar_SMTEncoding_Util.mkImp uu____8573 in
              ([[typing_pred]], [xx], uu____8572) in
            mkForall_fuel uu____8566 in
          (uu____8565, (Some "unit inversion"), "unit_inversion") in
        FStar_SMTEncoding_Term.Assume uu____8561 in
      [uu____8560] in
    uu____8551 :: uu____8558 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8604 =
      let uu____8605 =
        let uu____8609 =
          let uu____8610 =
            let uu____8616 =
              let uu____8619 =
                let uu____8621 = FStar_SMTEncoding_Term.boxBool b in
                [uu____8621] in
              [uu____8619] in
            let uu____8624 =
              let uu____8625 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____8625 tt in
            (uu____8616, [bb], uu____8624) in
          FStar_SMTEncoding_Util.mkForall uu____8610 in
        (uu____8609, (Some "bool typing"), "bool_typing") in
      FStar_SMTEncoding_Term.Assume uu____8605 in
    let uu____8636 =
      let uu____8638 =
        let uu____8639 =
          let uu____8643 =
            let uu____8644 =
              let uu____8650 =
                let uu____8651 =
                  let uu____8654 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____8654) in
                FStar_SMTEncoding_Util.mkImp uu____8651 in
              ([[typing_pred]], [xx], uu____8650) in
            mkForall_fuel uu____8644 in
          (uu____8643, (Some "bool inversion"), "bool_inversion") in
        FStar_SMTEncoding_Term.Assume uu____8639 in
      [uu____8638] in
    uu____8604 :: uu____8636 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____8688 =
        let uu____8689 =
          let uu____8693 =
            let uu____8695 =
              let uu____8697 =
                let uu____8699 = FStar_SMTEncoding_Term.boxInt a in
                let uu____8700 =
                  let uu____8702 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____8702] in
                uu____8699 :: uu____8700 in
              tt :: uu____8697 in
            tt :: uu____8695 in
          ("Prims.Precedes", uu____8693) in
        FStar_SMTEncoding_Util.mkApp uu____8689 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8688 in
    let precedes_y_x =
      let uu____8705 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8705 in
    let uu____8707 =
      let uu____8708 =
        let uu____8712 =
          let uu____8713 =
            let uu____8719 =
              let uu____8722 =
                let uu____8724 = FStar_SMTEncoding_Term.boxInt b in
                [uu____8724] in
              [uu____8722] in
            let uu____8727 =
              let uu____8728 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____8728 tt in
            (uu____8719, [bb], uu____8727) in
          FStar_SMTEncoding_Util.mkForall uu____8713 in
        (uu____8712, (Some "int typing"), "int_typing") in
      FStar_SMTEncoding_Term.Assume uu____8708 in
    let uu____8739 =
      let uu____8741 =
        let uu____8742 =
          let uu____8746 =
            let uu____8747 =
              let uu____8753 =
                let uu____8754 =
                  let uu____8757 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____8757) in
                FStar_SMTEncoding_Util.mkImp uu____8754 in
              ([[typing_pred]], [xx], uu____8753) in
            mkForall_fuel uu____8747 in
          (uu____8746, (Some "int inversion"), "int_inversion") in
        FStar_SMTEncoding_Term.Assume uu____8742 in
      let uu____8770 =
        let uu____8772 =
          let uu____8773 =
            let uu____8777 =
              let uu____8778 =
                let uu____8784 =
                  let uu____8785 =
                    let uu____8788 =
                      let uu____8789 =
                        let uu____8791 =
                          let uu____8793 =
                            let uu____8795 =
                              let uu____8796 =
                                let uu____8799 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____8800 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____8799, uu____8800) in
                              FStar_SMTEncoding_Util.mkGT uu____8796 in
                            let uu____8801 =
                              let uu____8803 =
                                let uu____8804 =
                                  let uu____8807 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____8808 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____8807, uu____8808) in
                                FStar_SMTEncoding_Util.mkGTE uu____8804 in
                              let uu____8809 =
                                let uu____8811 =
                                  let uu____8812 =
                                    let uu____8815 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____8816 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____8815, uu____8816) in
                                  FStar_SMTEncoding_Util.mkLT uu____8812 in
                                [uu____8811] in
                              uu____8803 :: uu____8809 in
                            uu____8795 :: uu____8801 in
                          typing_pred_y :: uu____8793 in
                        typing_pred :: uu____8791 in
                      FStar_SMTEncoding_Util.mk_and_l uu____8789 in
                    (uu____8788, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____8785 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____8784) in
              mkForall_fuel uu____8778 in
            (uu____8777, (Some "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Term.Assume uu____8773 in
        [uu____8772] in
      uu____8741 :: uu____8770 in
    uu____8707 :: uu____8739 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8846 =
      let uu____8847 =
        let uu____8851 =
          let uu____8852 =
            let uu____8858 =
              let uu____8861 =
                let uu____8863 = FStar_SMTEncoding_Term.boxString b in
                [uu____8863] in
              [uu____8861] in
            let uu____8866 =
              let uu____8867 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____8867 tt in
            (uu____8858, [bb], uu____8866) in
          FStar_SMTEncoding_Util.mkForall uu____8852 in
        (uu____8851, (Some "string typing"), "string_typing") in
      FStar_SMTEncoding_Term.Assume uu____8847 in
    let uu____8878 =
      let uu____8880 =
        let uu____8881 =
          let uu____8885 =
            let uu____8886 =
              let uu____8892 =
                let uu____8893 =
                  let uu____8896 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____8896) in
                FStar_SMTEncoding_Util.mkImp uu____8893 in
              ([[typing_pred]], [xx], uu____8892) in
            mkForall_fuel uu____8886 in
          (uu____8885, (Some "string inversion"), "string_inversion") in
        FStar_SMTEncoding_Term.Assume uu____8881 in
      [uu____8880] in
    uu____8846 :: uu____8878 in
  let mk_ref1 env reft_name uu____8918 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____8929 =
        let uu____8933 =
          let uu____8935 = FStar_SMTEncoding_Util.mkFreeV aa in [uu____8935] in
        (reft_name, uu____8933) in
      FStar_SMTEncoding_Util.mkApp uu____8929 in
    let refb =
      let uu____8938 =
        let uu____8942 =
          let uu____8944 = FStar_SMTEncoding_Util.mkFreeV bb in [uu____8944] in
        (reft_name, uu____8942) in
      FStar_SMTEncoding_Util.mkApp uu____8938 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____8948 =
      let uu____8949 =
        let uu____8953 =
          let uu____8954 =
            let uu____8960 =
              let uu____8961 =
                let uu____8964 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____8964) in
              FStar_SMTEncoding_Util.mkImp uu____8961 in
            ([[typing_pred]], [xx; aa], uu____8960) in
          mkForall_fuel uu____8954 in
        (uu____8953, (Some "ref inversion"), "ref_inversion") in
      FStar_SMTEncoding_Term.Assume uu____8949 in
    [uu____8948] in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Term.Assume
       (valid, (Some "True interpretation"), "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____9004 =
      let uu____9005 =
        let uu____9009 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____9009, (Some "False interpretation"), "false_interp") in
      FStar_SMTEncoding_Term.Assume uu____9005 in
    [uu____9004] in
  let mk_and_interp env conj uu____9020 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9037 =
      let uu____9038 =
        let uu____9042 =
          let uu____9043 =
            let uu____9049 =
              let uu____9050 =
                let uu____9053 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____9053, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9050 in
            ([[l_and_a_b]], [aa; bb], uu____9049) in
          FStar_SMTEncoding_Util.mkForall uu____9043 in
        (uu____9042, (Some "/\\ interpretation"), "l_and-interp") in
      FStar_SMTEncoding_Term.Assume uu____9038 in
    [uu____9037] in
  let mk_or_interp env disj uu____9077 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9094 =
      let uu____9095 =
        let uu____9099 =
          let uu____9100 =
            let uu____9106 =
              let uu____9107 =
                let uu____9110 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____9110, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9107 in
            ([[l_or_a_b]], [aa; bb], uu____9106) in
          FStar_SMTEncoding_Util.mkForall uu____9100 in
        (uu____9099, (Some "\\/ interpretation"), "l_or-interp") in
      FStar_SMTEncoding_Term.Assume uu____9095 in
    [uu____9094] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____9151 =
      let uu____9152 =
        let uu____9156 =
          let uu____9157 =
            let uu____9163 =
              let uu____9164 =
                let uu____9167 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9167, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9164 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____9163) in
          FStar_SMTEncoding_Util.mkForall uu____9157 in
        (uu____9156, (Some "Eq2 interpretation"), "eq2-interp") in
      FStar_SMTEncoding_Term.Assume uu____9152 in
    [uu____9151] in
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
    let uu____9214 =
      let uu____9215 =
        let uu____9219 =
          let uu____9220 =
            let uu____9226 =
              let uu____9227 =
                let uu____9230 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9230, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9227 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____9226) in
          FStar_SMTEncoding_Util.mkForall uu____9220 in
        (uu____9219, (Some "Eq3 interpretation"), "eq3-interp") in
      FStar_SMTEncoding_Term.Assume uu____9215 in
    [uu____9214] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9275 =
      let uu____9276 =
        let uu____9280 =
          let uu____9281 =
            let uu____9287 =
              let uu____9288 =
                let uu____9291 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____9291, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9288 in
            ([[l_imp_a_b]], [aa; bb], uu____9287) in
          FStar_SMTEncoding_Util.mkForall uu____9281 in
        (uu____9280, (Some "==> interpretation"), "l_imp-interp") in
      FStar_SMTEncoding_Term.Assume uu____9276 in
    [uu____9275] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9332 =
      let uu____9333 =
        let uu____9337 =
          let uu____9338 =
            let uu____9344 =
              let uu____9345 =
                let uu____9348 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____9348, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9345 in
            ([[l_iff_a_b]], [aa; bb], uu____9344) in
          FStar_SMTEncoding_Util.mkForall uu____9338 in
        (uu____9337, (Some "<==> interpretation"), "l_iff-interp") in
      FStar_SMTEncoding_Term.Assume uu____9333 in
    [uu____9332] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____9382 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9382 in
    let uu____9384 =
      let uu____9385 =
        let uu____9389 =
          let uu____9390 =
            let uu____9396 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____9396) in
          FStar_SMTEncoding_Util.mkForall uu____9390 in
        (uu____9389, (Some "not interpretation"), "l_not-interp") in
      FStar_SMTEncoding_Term.Assume uu____9385 in
    [uu____9384] in
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
      let uu____9436 =
        let uu____9440 =
          let uu____9442 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9442] in
        ("Valid", uu____9440) in
      FStar_SMTEncoding_Util.mkApp uu____9436 in
    let uu____9444 =
      let uu____9445 =
        let uu____9449 =
          let uu____9450 =
            let uu____9456 =
              let uu____9457 =
                let uu____9460 =
                  let uu____9461 =
                    let uu____9467 =
                      let uu____9470 =
                        let uu____9472 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9472] in
                      [uu____9470] in
                    let uu____9475 =
                      let uu____9476 =
                        let uu____9479 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9479, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9476 in
                    (uu____9467, [xx1], uu____9475) in
                  FStar_SMTEncoding_Util.mkForall uu____9461 in
                (uu____9460, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9457 in
            ([[l_forall_a_b]], [aa; bb], uu____9456) in
          FStar_SMTEncoding_Util.mkForall uu____9450 in
        (uu____9449, (Some "forall interpretation"), "forall-interp") in
      FStar_SMTEncoding_Term.Assume uu____9445 in
    [uu____9444] in
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
      let uu____9530 =
        let uu____9534 =
          let uu____9536 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9536] in
        ("Valid", uu____9534) in
      FStar_SMTEncoding_Util.mkApp uu____9530 in
    let uu____9538 =
      let uu____9539 =
        let uu____9543 =
          let uu____9544 =
            let uu____9550 =
              let uu____9551 =
                let uu____9554 =
                  let uu____9555 =
                    let uu____9561 =
                      let uu____9564 =
                        let uu____9566 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9566] in
                      [uu____9564] in
                    let uu____9569 =
                      let uu____9570 =
                        let uu____9573 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9573, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9570 in
                    (uu____9561, [xx1], uu____9569) in
                  FStar_SMTEncoding_Util.mkExists uu____9555 in
                (uu____9554, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9551 in
            ([[l_exists_a_b]], [aa; bb], uu____9550) in
          FStar_SMTEncoding_Util.mkForall uu____9544 in
        (uu____9543, (Some "exists interpretation"), "exists-interp") in
      FStar_SMTEncoding_Term.Assume uu____9539 in
    [uu____9538] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____9609 =
      let uu____9610 =
        let uu____9614 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____9615 = varops.mk_unique "typing_range_const" in
        (uu____9614, (Some "Range_const typing"), uu____9615) in
      FStar_SMTEncoding_Term.Assume uu____9610 in
    [uu____9609] in
  let prims1 =
    [(FStar_Syntax_Const.unit_lid, mk_unit);
    (FStar_Syntax_Const.bool_lid, mk_bool);
    (FStar_Syntax_Const.int_lid, mk_int);
    (FStar_Syntax_Const.string_lid, mk_str);
    (FStar_Syntax_Const.ref_lid, mk_ref1);
    (FStar_Syntax_Const.true_lid, mk_true_interp);
    (FStar_Syntax_Const.false_lid, mk_false_interp);
    (FStar_Syntax_Const.and_lid, mk_and_interp);
    (FStar_Syntax_Const.or_lid, mk_or_interp);
    (FStar_Syntax_Const.eq2_lid, mk_eq2_interp);
    (FStar_Syntax_Const.eq3_lid, mk_eq3_interp);
    (FStar_Syntax_Const.imp_lid, mk_imp_interp);
    (FStar_Syntax_Const.iff_lid, mk_iff_interp);
    (FStar_Syntax_Const.not_lid, mk_not_interp);
    (FStar_Syntax_Const.forall_lid, mk_forall_interp);
    (FStar_Syntax_Const.exists_lid, mk_exists_interp);
    (FStar_Syntax_Const.range_lid, mk_range_interp)] in
  fun env  ->
    fun t  ->
      fun s  ->
        fun tt  ->
          let uu____9877 =
            FStar_Util.find_opt
              (fun uu____9895  ->
                 match uu____9895 with
                 | (l,uu____9905) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____9877 with
          | None  -> []
          | Some (uu____9927,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____9964 = encode_function_type_as_formula None None t env in
        match uu____9964 with
        | (form,decls) ->
            FStar_List.append decls
              [FStar_SMTEncoding_Term.Assume
                 (form, (Some (Prims.strcat "Lemma: " lid.FStar_Ident.str)),
                   (Prims.strcat "lemma_" lid.FStar_Ident.str))]
let encode_free_var:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.qualifier Prims.list ->
            (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun fv  ->
      fun tt  ->
        fun t_norm  ->
          fun quals  ->
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            let uu____9996 =
              (let uu____9997 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____9997) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____9996
            then
              let uu____10001 = new_term_constant_and_tok_from_lid env lid in
              match uu____10001 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____10013 =
                      let uu____10014 = FStar_Syntax_Subst.compress t_norm in
                      uu____10014.FStar_Syntax_Syntax.n in
                    match uu____10013 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10019) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____10036  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____10039 -> [] in
                  let d =
                    FStar_SMTEncoding_Term.DeclFun
                      (vname, arg_sorts, FStar_SMTEncoding_Term.Term_sort,
                        (Some
                           "Uninterpreted function symbol for impure function")) in
                  let dd =
                    FStar_SMTEncoding_Term.DeclFun
                      (vtok, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Uninterpreted name for impure function")) in
                  ([d; dd], env1)
            else
              (let uu____10048 = prims.is lid in
               if uu____10048
               then
                 let vname = varops.new_fvar lid in
                 let uu____10053 = prims.mk lid vname in
                 match uu____10053 with
                 | (tok,definition) ->
                     let env1 = push_free_var env lid vname (Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____10068 =
                    let uu____10074 = curried_arrow_formals_comp t_norm in
                    match uu____10074 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____10085 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____10085
                          then
                            let uu____10086 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___158_10087 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___158_10087.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___158_10087.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___158_10087.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___158_10087.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___158_10087.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___158_10087.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___158_10087.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___158_10087.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___158_10087.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___158_10087.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___158_10087.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___158_10087.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___158_10087.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___158_10087.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___158_10087.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___158_10087.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___158_10087.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___158_10087.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___158_10087.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___158_10087.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___158_10087.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___158_10087.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___158_10087.FStar_TypeChecker_Env.qname_and_index)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____10086
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____10094 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____10094)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____10068 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____10121 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____10121 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____10134 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___129_10158  ->
                                     match uu___129_10158 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____10161 =
                                           FStar_Util.prefix vars in
                                         (match uu____10161 with
                                          | (uu____10172,(xxsym,uu____10174))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____10184 =
                                                let uu____10185 =
                                                  let uu____10189 =
                                                    let uu____10190 =
                                                      let uu____10196 =
                                                        let uu____10197 =
                                                          let uu____10200 =
                                                            let uu____10201 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____10201 in
                                                          (vapp, uu____10200) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____10197 in
                                                      ([[vapp]], vars,
                                                        uu____10196) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10190 in
                                                  (uu____10189,
                                                    (Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Term.Assume
                                                  uu____10185 in
                                              [uu____10184])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____10212 =
                                           FStar_Util.prefix vars in
                                         (match uu____10212 with
                                          | (uu____10223,(xxsym,uu____10225))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let f1 =
                                                {
                                                  FStar_Syntax_Syntax.ppname
                                                    = f;
                                                  FStar_Syntax_Syntax.index =
                                                    (Prims.parse_int "0");
                                                  FStar_Syntax_Syntax.sort =
                                                    FStar_Syntax_Syntax.tun
                                                } in
                                              let tp_name =
                                                mk_term_projector_name d f1 in
                                              let prim_app =
                                                FStar_SMTEncoding_Util.mkApp
                                                  (tp_name, [xx]) in
                                              let uu____10239 =
                                                let uu____10240 =
                                                  let uu____10244 =
                                                    let uu____10245 =
                                                      let uu____10251 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____10251) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10245 in
                                                  (uu____10244,
                                                    (Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Term.Assume
                                                  uu____10240 in
                                              [uu____10239])
                                     | uu____10260 -> [])) in
                           let uu____10261 = encode_binders None formals env1 in
                           (match uu____10261 with
                            | (vars,guards,env',decls1,uu____10277) ->
                                let uu____10284 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____10289 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____10289, decls1)
                                  | Some p ->
                                      let uu____10291 = encode_formula p env' in
                                      (match uu____10291 with
                                       | (g,ds) ->
                                           let uu____10298 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____10298,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____10284 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____10307 =
                                         let uu____10311 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____10311) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10307 in
                                     let uu____10316 =
                                       let vname_decl =
                                         let uu____10321 =
                                           let uu____10327 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____10332  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____10327,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10321 in
                                       let uu____10337 =
                                         let env2 =
                                           let uu___159_10341 = env1 in
                                           {
                                             bindings =
                                               (uu___159_10341.bindings);
                                             depth = (uu___159_10341.depth);
                                             tcenv = (uu___159_10341.tcenv);
                                             warn = (uu___159_10341.warn);
                                             cache = (uu___159_10341.cache);
                                             nolabels =
                                               (uu___159_10341.nolabels);
                                             use_zfuel_name =
                                               (uu___159_10341.use_zfuel_name);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___159_10341.current_module_name)
                                           } in
                                         let uu____10342 =
                                           let uu____10343 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____10343 in
                                         if uu____10342
                                         then
                                           encode_term_pred None tt env2
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env2
                                             vtok_tm in
                                       match uu____10337 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____10353::uu____10354 ->
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
                                                   let uu____10377 =
                                                     let uu____10383 =
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
                                                       [ff], uu____10383) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____10377 in
                                                 FStar_SMTEncoding_Term.Assume
                                                   (guarded_tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____10397 ->
                                                 FStar_SMTEncoding_Term.Assume
                                                   (tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname)) in
                                           let uu____10399 =
                                             match formals with
                                             | [] ->
                                                 let uu____10408 =
                                                   let uu____10409 =
                                                     let uu____10411 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_34  ->
                                                          Some _0_34)
                                                       uu____10411 in
                                                   push_free_var env1 lid
                                                     vname uu____10409 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____10408)
                                             | uu____10414 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None) in
                                                 let vtok_fresh =
                                                   let uu____10419 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____10419 in
                                                 let name_tok_corr =
                                                   let uu____10421 =
                                                     let uu____10425 =
                                                       let uu____10426 =
                                                         let uu____10432 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____10432) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____10426 in
                                                     (uu____10425,
                                                       (Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Term.Assume
                                                     uu____10421 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____10399 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____10316 with
                                      | (decls2,env2) ->
                                          let uu____10456 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____10461 =
                                              encode_term res_t1 env' in
                                            match uu____10461 with
                                            | (encoded_res_t,decls) ->
                                                let uu____10469 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____10469,
                                                  decls) in
                                          (match uu____10456 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____10477 =
                                                   let uu____10481 =
                                                     let uu____10482 =
                                                       let uu____10488 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____10488) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____10482 in
                                                   (uu____10481,
                                                     (Some "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Term.Assume
                                                   uu____10477 in
                                               let freshness =
                                                 let uu____10497 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____10497
                                                 then
                                                   let uu____10500 =
                                                     let uu____10501 =
                                                       let uu____10507 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              Prims.snd) in
                                                       let uu____10513 =
                                                         varops.next_id () in
                                                       (vname, uu____10507,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____10513) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____10501 in
                                                   let uu____10515 =
                                                     let uu____10517 =
                                                       pretype_axiom env2
                                                         vapp vars in
                                                     [uu____10517] in
                                                   uu____10500 :: uu____10515
                                                 else [] in
                                               let g =
                                                 let uu____10521 =
                                                   let uu____10523 =
                                                     let uu____10525 =
                                                       let uu____10527 =
                                                         let uu____10529 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____10529 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____10527 in
                                                     FStar_List.append decls3
                                                       uu____10525 in
                                                   FStar_List.append decls2
                                                     uu____10523 in
                                                 FStar_List.append decls11
                                                   uu____10521 in
                                               (g, env2))))))))
let declare_top_level_let:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          ((Prims.string* FStar_SMTEncoding_Term.term Prims.option)*
            FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun x  ->
      fun t  ->
        fun t_norm  ->
          let uu____10551 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____10551 with
          | None  ->
              let uu____10574 = encode_free_var env x t t_norm [] in
              (match uu____10574 with
               | (decls,env1) ->
                   let uu____10589 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____10589 with
                    | (n1,x',uu____10608) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____10620) -> ((n1, x1), [], env)
let encode_top_level_val:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.qualifier Prims.list ->
          (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun lid  ->
      fun t  ->
        fun quals  ->
          let tt = norm env t in
          let uu____10653 = encode_free_var env lid t tt quals in
          match uu____10653 with
          | (decls,env1) ->
              let uu____10664 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____10664
              then
                let uu____10668 =
                  let uu____10670 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____10670 in
                (uu____10668, env1)
              else (decls, env1)
let encode_top_level_vals:
  env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun bindings  ->
      fun quals  ->
        FStar_All.pipe_right bindings
          (FStar_List.fold_left
             (fun uu____10698  ->
                fun lb  ->
                  match uu____10698 with
                  | (decls,env1) ->
                      let uu____10710 =
                        let uu____10714 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____10714
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____10710 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Syntax_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____10728 = FStar_Syntax_Util.head_and_args t in
    match uu____10728 with
    | (hd1,args) ->
        let uu____10754 =
          let uu____10755 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10755.FStar_Syntax_Syntax.n in
        (match uu____10754 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____10759,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____10772 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun uu____10787  ->
      fun quals  ->
        match uu____10787 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____10836 = FStar_Util.first_N nbinders formals in
              match uu____10836 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____10876  ->
                         fun uu____10877  ->
                           match (uu____10876, uu____10877) with
                           | ((formal,uu____10887),(binder,uu____10889)) ->
                               let uu____10894 =
                                 let uu____10899 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____10899) in
                               FStar_Syntax_Syntax.NT uu____10894) formals1
                      binders in
                  let extra_formals1 =
                    let uu____10904 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____10918  ->
                              match uu____10918 with
                              | (x,i) ->
                                  let uu____10925 =
                                    let uu___160_10926 = x in
                                    let uu____10927 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___160_10926.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___160_10926.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____10927
                                    } in
                                  (uu____10925, i))) in
                    FStar_All.pipe_right uu____10904
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____10939 =
                      let uu____10941 =
                        let uu____10942 = FStar_Syntax_Subst.subst subst1 t in
                        uu____10942.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left (fun _0_35  -> Some _0_35)
                        uu____10941 in
                    let uu____10946 =
                      let uu____10947 = FStar_Syntax_Subst.compress body in
                      let uu____10948 =
                        let uu____10949 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left Prims.snd uu____10949 in
                      FStar_Syntax_Syntax.extend_app_n uu____10947
                        uu____10948 in
                    uu____10946 uu____10939 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____10991 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____10991
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___161_10992 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___161_10992.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___161_10992.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___161_10992.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___161_10992.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___161_10992.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___161_10992.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___161_10992.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___161_10992.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___161_10992.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___161_10992.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___161_10992.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___161_10992.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___161_10992.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___161_10992.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___161_10992.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___161_10992.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___161_10992.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___161_10992.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___161_10992.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___161_10992.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___161_10992.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___161_10992.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___161_10992.FStar_TypeChecker_Env.qname_and_index)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____11013 = FStar_Syntax_Util.abs_formals e in
                match uu____11013 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____11062::uu____11063 ->
                         let uu____11071 =
                           let uu____11072 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11072.FStar_Syntax_Syntax.n in
                         (match uu____11071 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11099 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11099 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____11125 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____11125
                                   then
                                     let uu____11143 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____11143 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____11189  ->
                                                   fun uu____11190  ->
                                                     match (uu____11189,
                                                             uu____11190)
                                                     with
                                                     | ((x,uu____11200),
                                                        (b,uu____11202)) ->
                                                         let uu____11207 =
                                                           let uu____11212 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____11212) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____11207)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____11214 =
                                            let uu____11225 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____11225) in
                                          (uu____11214, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____11260 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____11260 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11312) ->
                              let uu____11317 =
                                let uu____11328 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                Prims.fst uu____11328 in
                              (uu____11317, true)
                          | uu____11361 when Prims.op_Negation norm1 ->
                              let t_norm2 =
                                FStar_TypeChecker_Normalize.normalize
                                  [FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                                  FStar_TypeChecker_Normalize.Beta;
                                  FStar_TypeChecker_Normalize.WHNF;
                                  FStar_TypeChecker_Normalize.Exclude
                                    FStar_TypeChecker_Normalize.Zeta;
                                  FStar_TypeChecker_Normalize.UnfoldUntil
                                    FStar_Syntax_Syntax.Delta_constant;
                                  FStar_TypeChecker_Normalize.EraseUniverses]
                                  env.tcenv t_norm1 in
                              aux true t_norm2
                          | uu____11363 ->
                              let uu____11364 =
                                let uu____11365 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____11366 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11365
                                  uu____11366 in
                              failwith uu____11364)
                     | uu____11379 ->
                         let uu____11380 =
                           let uu____11381 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11381.FStar_Syntax_Syntax.n in
                         (match uu____11380 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11408 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11408 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____11426 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____11426 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____11474 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____11502 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____11502
               then encode_top_level_vals env bindings quals
               else
                 (let uu____11509 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____11550  ->
                            fun lb  ->
                              match uu____11550 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____11601 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____11601
                                    then Prims.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____11604 =
                                      let uu____11612 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____11612
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____11604 with
                                    | (tok,decl,env2) ->
                                        let uu____11637 =
                                          let uu____11644 =
                                            let uu____11650 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____11650, tok) in
                                          uu____11644 :: toks in
                                        (uu____11637, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____11509 with
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
                        | uu____11752 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok1 -> mk_Apply ftok1 vars
                               | None  ->
                                   let uu____11757 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____11757 vars)
                            else
                              (let uu____11759 =
                                 let uu____11763 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____11763) in
                               FStar_SMTEncoding_Util.mkApp uu____11759) in
                      let uu____11768 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___130_11770  ->
                                 match uu___130_11770 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____11771 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____11774 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____11774))) in
                      if uu____11768
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____11794;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____11796;
                                FStar_Syntax_Syntax.lbeff = uu____11797;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____11838 =
                                 let uu____11842 =
                                   FStar_TypeChecker_Env.open_universes_in
                                     env1.tcenv uvs [e; t_norm] in
                                 match uu____11842 with
                                 | (tcenv',uu____11853,e_t) ->
                                     let uu____11857 =
                                       match e_t with
                                       | e1::t_norm1::[] -> (e1, t_norm1)
                                       | uu____11864 -> failwith "Impossible" in
                                     (match uu____11857 with
                                      | (e1,t_norm1) ->
                                          ((let uu___164_11873 = env1 in
                                            {
                                              bindings =
                                                (uu___164_11873.bindings);
                                              depth = (uu___164_11873.depth);
                                              tcenv = tcenv';
                                              warn = (uu___164_11873.warn);
                                              cache = (uu___164_11873.cache);
                                              nolabels =
                                                (uu___164_11873.nolabels);
                                              use_zfuel_name =
                                                (uu___164_11873.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___164_11873.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___164_11873.current_module_name)
                                            }), e1, t_norm1)) in
                               (match uu____11838 with
                                | (env',e1,t_norm1) ->
                                    let uu____11880 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____11880 with
                                     | ((binders,body,uu____11892,uu____11893),curry)
                                         ->
                                         ((let uu____11900 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____11900
                                           then
                                             let uu____11901 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____11902 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____11901 uu____11902
                                           else ());
                                          (let uu____11904 =
                                             encode_binders None binders env' in
                                           match uu____11904 with
                                           | (vars,guards,env'1,binder_decls,uu____11920)
                                               ->
                                               let body1 =
                                                 let uu____11928 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____11928
                                                 then
                                                   reify_body env'1.tcenv
                                                     body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____11931 =
                                                 let uu____11936 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____11936
                                                 then
                                                   let uu____11942 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____11943 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____11942, uu____11943)
                                                 else
                                                   (let uu____11949 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____11949)) in
                                               (match uu____11931 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____11963 =
                                                        let uu____11967 =
                                                          let uu____11968 =
                                                            let uu____11974 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____11974) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____11968 in
                                                        let uu____11980 =
                                                          let uu____11982 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          Some uu____11982 in
                                                        (uu____11967,
                                                          uu____11980,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Term.Assume
                                                        uu____11963 in
                                                    let uu____11984 =
                                                      let uu____11986 =
                                                        let uu____11988 =
                                                          let uu____11990 =
                                                            let uu____11992 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____11992 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____11990 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____11988 in
                                                      FStar_List.append
                                                        decls1 uu____11986 in
                                                    (uu____11984, env1))))))
                           | uu____11995 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____12014 = varops.fresh "fuel" in
                             (uu____12014, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____12017 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____12056  ->
                                     fun uu____12057  ->
                                       match (uu____12056, uu____12057) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____12139 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____12139 in
                                           let gtok =
                                             let uu____12141 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____12141 in
                                           let env3 =
                                             let uu____12143 =
                                               let uu____12145 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_36  -> Some _0_36)
                                                 uu____12145 in
                                             push_free_var env2 flid gtok
                                               uu____12143 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____12017 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____12231
                                 t_norm uu____12233 =
                                 match (uu____12231, uu____12233) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____12260;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____12261;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____12278 =
                                       let uu____12282 =
                                         FStar_TypeChecker_Env.open_universes_in
                                           env2.tcenv uvs [e; t_norm] in
                                       match uu____12282 with
                                       | (tcenv',uu____12297,e_t) ->
                                           let uu____12301 =
                                             match e_t with
                                             | e1::t_norm1::[] ->
                                                 (e1, t_norm1)
                                             | uu____12308 ->
                                                 failwith "Impossible" in
                                           (match uu____12301 with
                                            | (e1,t_norm1) ->
                                                ((let uu___165_12317 = env2 in
                                                  {
                                                    bindings =
                                                      (uu___165_12317.bindings);
                                                    depth =
                                                      (uu___165_12317.depth);
                                                    tcenv = tcenv';
                                                    warn =
                                                      (uu___165_12317.warn);
                                                    cache =
                                                      (uu___165_12317.cache);
                                                    nolabels =
                                                      (uu___165_12317.nolabels);
                                                    use_zfuel_name =
                                                      (uu___165_12317.use_zfuel_name);
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___165_12317.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___165_12317.current_module_name)
                                                  }), e1, t_norm1)) in
                                     (match uu____12278 with
                                      | (env',e1,t_norm1) ->
                                          ((let uu____12327 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____12327
                                            then
                                              let uu____12328 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____12329 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____12330 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____12328 uu____12329
                                                uu____12330
                                            else ());
                                           (let uu____12332 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____12332 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____12354 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____12354
                                                  then
                                                    let uu____12355 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____12356 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____12357 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____12358 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____12355 uu____12356
                                                      uu____12357 uu____12358
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____12362 =
                                                    encode_binders None
                                                      binders env' in
                                                  match uu____12362 with
                                                  | (vars,guards,env'1,binder_decls,uu____12380)
                                                      ->
                                                      let decl_g =
                                                        let uu____12388 =
                                                          let uu____12394 =
                                                            let uu____12396 =
                                                              FStar_List.map
                                                                Prims.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____12396 in
                                                          (g, uu____12394,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____12388 in
                                                      let env02 =
                                                        push_zfuel_name env01
                                                          flid g in
                                                      let decl_g_tok =
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          (gtok, [],
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Token for fuel-instrumented partial applications")) in
                                                      let vars_tm =
                                                        FStar_List.map
                                                          FStar_SMTEncoding_Util.mkFreeV
                                                          vars in
                                                      let app =
                                                        let uu____12411 =
                                                          let uu____12415 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____12415) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12411 in
                                                      let gsapp =
                                                        let uu____12421 =
                                                          let uu____12425 =
                                                            let uu____12427 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____12427 ::
                                                              vars_tm in
                                                          (g, uu____12425) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12421 in
                                                      let gmax =
                                                        let uu____12431 =
                                                          let uu____12435 =
                                                            let uu____12437 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____12437 ::
                                                              vars_tm in
                                                          (g, uu____12435) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12431 in
                                                      let body1 =
                                                        let uu____12441 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____12441
                                                        then
                                                          reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____12443 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____12443 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____12454
                                                               =
                                                               let uu____12458
                                                                 =
                                                                 let uu____12459
                                                                   =
                                                                   let uu____12467
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm) in
                                                                   ([[gsapp]],
                                                                    (Some
                                                                    (Prims.parse_int
                                                                    "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12467) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____12459 in
                                                               let uu____12478
                                                                 =
                                                                 let uu____12480
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 Some
                                                                   uu____12480 in
                                                               (uu____12458,
                                                                 uu____12478,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12454 in
                                                           let eqn_f =
                                                             let uu____12483
                                                               =
                                                               let uu____12487
                                                                 =
                                                                 let uu____12488
                                                                   =
                                                                   let uu____12494
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____12494) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12488 in
                                                               (uu____12487,
                                                                 (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12483 in
                                                           let eqn_g' =
                                                             let uu____12502
                                                               =
                                                               let uu____12506
                                                                 =
                                                                 let uu____12507
                                                                   =
                                                                   let uu____12513
                                                                    =
                                                                    let uu____12514
                                                                    =
                                                                    let uu____12517
                                                                    =
                                                                    let uu____12518
                                                                    =
                                                                    let uu____12522
                                                                    =
                                                                    let uu____12524
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____12524
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____12522) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____12518 in
                                                                    (gsapp,
                                                                    uu____12517) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____12514 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12513) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12507 in
                                                               (uu____12506,
                                                                 (Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12502 in
                                                           let uu____12536 =
                                                             let uu____12541
                                                               =
                                                               encode_binders
                                                                 None formals
                                                                 env02 in
                                                             match uu____12541
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____12558)
                                                                 ->
                                                                 let vars_tm1
                                                                   =
                                                                   FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars1 in
                                                                 let gapp =
                                                                   FStar_SMTEncoding_Util.mkApp
                                                                    (g,
                                                                    (fuel_tm
                                                                    ::
                                                                    vars_tm1)) in
                                                                 let tok_corr
                                                                   =
                                                                   let tok_app
                                                                    =
                                                                    let uu____12573
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____12573
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____12576
                                                                    =
                                                                    let uu____12580
                                                                    =
                                                                    let uu____12581
                                                                    =
                                                                    let uu____12587
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12587) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12581 in
                                                                    (uu____12580,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Term.Assume
                                                                    uu____12576 in
                                                                 let uu____12598
                                                                   =
                                                                   let uu____12602
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env3 gapp in
                                                                   match uu____12602
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____12610
                                                                    =
                                                                    let uu____12612
                                                                    =
                                                                    let uu____12613
                                                                    =
                                                                    let uu____12617
                                                                    =
                                                                    let uu____12618
                                                                    =
                                                                    let uu____12624
                                                                    =
                                                                    let uu____12625
                                                                    =
                                                                    let uu____12628
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____12628,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12625 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12624) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12618 in
                                                                    (uu____12617,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____12613 in
                                                                    [uu____12612] in
                                                                    (d3,
                                                                    uu____12610) in
                                                                 (match uu____12598
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____12536
                                                            with
                                                            | (aux_decls,g_typing)
                                                                ->
                                                                ((FStar_List.append
                                                                    binder_decls
                                                                    (
                                                                    FStar_List.append
                                                                    decls2
                                                                    (FStar_List.append
                                                                    aux_decls
                                                                    [decl_g;
                                                                    decl_g_tok]))),
                                                                  (FStar_List.append
                                                                    [eqn_g;
                                                                    eqn_g';
                                                                    eqn_f]
                                                                    g_typing),
                                                                  env02)))))))) in
                               let uu____12663 =
                                 let uu____12670 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____12706  ->
                                      fun uu____12707  ->
                                        match (uu____12706, uu____12707) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____12793 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____12793 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____12670 in
                               (match uu____12663 with
                                | (decls2,eqns,env01) ->
                                    let uu____12833 =
                                      let isDeclFun uu___131_12841 =
                                        match uu___131_12841 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____12842 -> true
                                        | uu____12848 -> false in
                                      let uu____12849 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____12849
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____12833 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____12876 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____12876
                     (FStar_String.concat " and ") in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.strcat "let rec unencodeable: Skipping: " msg) in
                 ([decl], env))
let rec encode_sigelt:
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun se  ->
      (let uu____12909 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____12909
       then
         let uu____12910 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n")
           uu____12910
       else ());
      (let nm =
         let uu____12913 = FStar_Syntax_Util.lid_of_sigelt se in
         match uu____12913 with | None  -> "" | Some l -> l.FStar_Ident.str in
       let uu____12916 = encode_sigelt' env se in
       match uu____12916 with
       | (g,e) ->
           (match g with
            | [] ->
                let uu____12925 =
                  let uu____12927 =
                    let uu____12928 = FStar_Util.format1 "<Skipped %s/>" nm in
                    FStar_SMTEncoding_Term.Caption uu____12928 in
                  [uu____12927] in
                (uu____12925, e)
            | uu____12930 ->
                let uu____12931 =
                  let uu____12933 =
                    let uu____12935 =
                      let uu____12936 =
                        FStar_Util.format1 "<Start encoding %s>" nm in
                      FStar_SMTEncoding_Term.Caption uu____12936 in
                    uu____12935 :: g in
                  let uu____12937 =
                    let uu____12939 =
                      let uu____12940 =
                        FStar_Util.format1 "</end encoding %s>" nm in
                      FStar_SMTEncoding_Term.Caption uu____12940 in
                    [uu____12939] in
                  FStar_List.append uu____12933 uu____12937 in
                (uu____12931, e)))
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12948 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma _
        |FStar_Syntax_Syntax.Sig_main _
         |FStar_Syntax_Syntax.Sig_effect_abbrev _
          |FStar_Syntax_Syntax.Sig_sub_effect _ -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____12957 =
            let uu____12958 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigqual
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____12958 Prims.op_Negation in
          if uu____12957
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____12978 ->
                   let uu____12979 =
                     let uu____12982 =
                       let uu____12983 =
                         let uu____12998 =
                           FStar_All.pipe_left (fun _0_37  -> Some _0_37)
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL])) in
                         ((ed.FStar_Syntax_Syntax.binders), tm, uu____12998) in
                       FStar_Syntax_Syntax.Tm_abs uu____12983 in
                     FStar_Syntax_Syntax.mk uu____12982 in
                   uu____12979 None tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____13051 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____13051 with
               | (aname,atok,env2) ->
                   let uu____13061 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____13061 with
                    | (formals,uu____13071) ->
                        let uu____13078 =
                          let uu____13081 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____13081 env2 in
                        (match uu____13078 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____13089 =
                                 let uu____13090 =
                                   let uu____13096 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____13104  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____13096,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____13090 in
                               [uu____13089;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))] in
                             let uu____13111 =
                               let aux uu____13140 uu____13141 =
                                 match (uu____13140, uu____13141) with
                                 | ((bv,uu____13168),(env3,acc_sorts,acc)) ->
                                     let uu____13189 = gen_term_var env3 bv in
                                     (match uu____13189 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____13111 with
                              | (uu____13227,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____13241 =
                                      let uu____13245 =
                                        let uu____13246 =
                                          let uu____13252 =
                                            let uu____13253 =
                                              let uu____13256 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____13256) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____13253 in
                                          ([[app]], xs_sorts, uu____13252) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13246 in
                                      (uu____13245, (Some "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Term.Assume uu____13241 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____13268 =
                                      let uu____13272 =
                                        let uu____13273 =
                                          let uu____13279 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____13279) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13273 in
                                      (uu____13272,
                                        (Some "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Term.Assume uu____13268 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____13289 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____13289 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13305,uu____13306)
          when FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____13307 = new_term_constant_and_tok_from_lid env lid in
          (match uu____13307 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13318,t) ->
          let quals = se.FStar_Syntax_Syntax.sigqual in
          let will_encode_definition =
            let uu____13323 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___132_13325  ->
                      match uu___132_13325 with
                      | FStar_Syntax_Syntax.Assumption 
                        |FStar_Syntax_Syntax.Projector _
                         |FStar_Syntax_Syntax.Discriminator _
                          |FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13328 -> false)) in
            Prims.op_Negation uu____13323 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None in
             let uu____13334 = encode_top_level_val env fv t quals in
             match uu____13334 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____13346 =
                   let uu____13348 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____13348 in
                 (uu____13346, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,f) ->
          let uu____13353 = encode_formula f env in
          (match uu____13353 with
           | (f1,decls) ->
               let g =
                 let uu____13362 =
                   let uu____13363 =
                     let uu____13367 =
                       let uu____13369 =
                         let uu____13370 = FStar_Syntax_Print.lid_to_string l in
                         FStar_Util.format1 "Assumption: %s" uu____13370 in
                       Some uu____13369 in
                     let uu____13371 =
                       varops.mk_unique
                         (Prims.strcat "assumption_" l.FStar_Ident.str) in
                     (f1, uu____13367, uu____13371) in
                   FStar_SMTEncoding_Term.Assume uu____13363 in
                 [uu____13362] in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____13375,uu____13376) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigqual
            (FStar_List.contains FStar_Syntax_Syntax.Irreducible)
          ->
          let uu____13382 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____13389 =
                       let uu____13394 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____13394.FStar_Syntax_Syntax.fv_name in
                     uu____13389.FStar_Syntax_Syntax.v in
                   let uu____13398 =
                     let uu____13399 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____13399 in
                   if uu____13398
                   then
                     let val_decl =
                       let uu___166_13414 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___166_13414.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigqual =
                           (uu___166_13414.FStar_Syntax_Syntax.sigqual)
                       } in
                     let uu____13418 = encode_sigelt' env1 val_decl in
                     match uu____13418 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (Prims.snd lbs) in
          (match uu____13382 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13435,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____13437;
                          FStar_Syntax_Syntax.lbtyp = uu____13438;
                          FStar_Syntax_Syntax.lbeff = uu____13439;
                          FStar_Syntax_Syntax.lbdef = uu____13440;_}::[]),uu____13441,uu____13442)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____13456 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____13456 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____13479 =
                   let uu____13481 =
                     let uu____13482 =
                       let uu____13486 =
                         let uu____13487 =
                           let uu____13493 =
                             let uu____13494 =
                               let uu____13497 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____13497) in
                             FStar_SMTEncoding_Util.mkEq uu____13494 in
                           ([[b2t_x]], [xx], uu____13493) in
                         FStar_SMTEncoding_Util.mkForall uu____13487 in
                       (uu____13486, (Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Term.Assume uu____13482 in
                   [uu____13481] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____13479 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____13514,uu____13515,uu____13516)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigqual
            (FStar_Util.for_some
               (fun uu___133_13522  ->
                  match uu___133_13522 with
                  | FStar_Syntax_Syntax.Discriminator uu____13523 -> true
                  | uu____13524 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____13526,lids,uu____13528) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13535 =
                     let uu____13536 = FStar_List.hd l.FStar_Ident.ns in
                     uu____13536.FStar_Ident.idText in
                   uu____13535 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigqual
               (FStar_Util.for_some
                  (fun uu___134_13538  ->
                     match uu___134_13538 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13539 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13542,uu____13543)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigqual
            (FStar_Util.for_some
               (fun uu___135_13553  ->
                  match uu___135_13553 with
                  | FStar_Syntax_Syntax.Projector uu____13554 -> true
                  | uu____13557 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____13564 = try_lookup_free_var env l in
          (match uu____13564 with
           | Some uu____13568 -> ([], env)
           | None  ->
               let se1 =
                 let uu___167_13571 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigqual =
                     (uu___167_13571.FStar_Syntax_Syntax.sigqual)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let
          ((is_rec,bindings),uu____13577,uu____13578) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigqual
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13590) ->
          let uu____13595 = encode_signature env ses in
          (match uu____13595 with
           | (g,env1) ->
               let uu____13605 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___136_13615  ->
                         match uu___136_13615 with
                         | FStar_SMTEncoding_Term.Assume
                             (uu____13616,Some "inversion axiom",uu____13617)
                             -> false
                         | uu____13619 -> true)) in
               (match uu____13605 with
                | (g',inversions) ->
                    let uu____13628 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___137_13638  ->
                              match uu___137_13638 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13639 ->
                                  true
                              | uu____13645 -> false)) in
                    (match uu____13628 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13656,tps,k,uu____13659,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigqual in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___138_13669  ->
                    match uu___138_13669 with
                    | FStar_Syntax_Syntax.Logic 
                      |FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13670 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13677 = c in
              match uu____13677 with
              | (name,args,uu____13681,uu____13682,uu____13683) ->
                  let uu____13686 =
                    let uu____13687 =
                      let uu____13693 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13700  ->
                                match uu____13700 with
                                | (uu____13704,sort,uu____13706) -> sort)) in
                      (name, uu____13693, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13687 in
                  [uu____13686]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____13724 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13727 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____13727 FStar_Option.isNone)) in
            if uu____13724
            then []
            else
              (let uu____13744 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____13744 with
               | (xxsym,xx) ->
                   let uu____13750 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____13761  ->
                             fun l  ->
                               match uu____13761 with
                               | (out,decls) ->
                                   let uu____13773 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____13773 with
                                    | (uu____13779,data_t) ->
                                        let uu____13781 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____13781 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____13810 =
                                                 let uu____13811 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____13811.FStar_Syntax_Syntax.n in
                                               match uu____13810 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____13819,indices) ->
                                                   indices
                                               | uu____13835 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____13847  ->
                                                         match uu____13847
                                                         with
                                                         | (x,uu____13851) ->
                                                             let uu____13852
                                                               =
                                                               let uu____13853
                                                                 =
                                                                 let uu____13857
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____13857,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____13853 in
                                                             push_term_var
                                                               env1 x
                                                               uu____13852)
                                                    env) in
                                             let uu____13859 =
                                               encode_args indices env1 in
                                             (match uu____13859 with
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
                                                      let uu____13879 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____13887
                                                                 =
                                                                 let uu____13890
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____13890,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____13887)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____13879
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____13892 =
                                                      let uu____13893 =
                                                        let uu____13896 =
                                                          let uu____13897 =
                                                            let uu____13900 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____13900,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____13897 in
                                                        (out, uu____13896) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____13893 in
                                                    (uu____13892,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____13750 with
                    | (data_ax,decls) ->
                        let uu____13908 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____13908 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____13919 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____13919 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____13922 =
                                 let uu____13926 =
                                   let uu____13927 =
                                     let uu____13933 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____13941 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____13933,
                                       uu____13941) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____13927 in
                                 let uu____13949 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____13926, (Some "inversion axiom"),
                                   uu____13949) in
                               FStar_SMTEncoding_Term.Assume uu____13922 in
                             let pattern_guarded_inversion =
                               let uu____13953 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____13953
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____13961 =
                                   let uu____13962 =
                                     let uu____13966 =
                                       let uu____13967 =
                                         let uu____13973 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____13981 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____13973, uu____13981) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____13967 in
                                     let uu____13989 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____13966, (Some "inversion axiom"),
                                       uu____13989) in
                                   FStar_SMTEncoding_Term.Assume uu____13962 in
                                 [uu____13961]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____13992 =
            let uu____14000 =
              let uu____14001 = FStar_Syntax_Subst.compress k in
              uu____14001.FStar_Syntax_Syntax.n in
            match uu____14000 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____14030 -> (tps, k) in
          (match uu____13992 with
           | (formals,res) ->
               let uu____14045 = FStar_Syntax_Subst.open_term formals res in
               (match uu____14045 with
                | (formals1,res1) ->
                    let uu____14052 = encode_binders None formals1 env in
                    (match uu____14052 with
                     | (vars,guards,env',binder_decls,uu____14067) ->
                         let uu____14074 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____14074 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____14087 =
                                  let uu____14091 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____14091) in
                                FStar_SMTEncoding_Util.mkApp uu____14087 in
                              let uu____14096 =
                                let tname_decl =
                                  let uu____14102 =
                                    let uu____14103 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____14118  ->
                                              match uu____14118 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____14126 = varops.next_id () in
                                    (tname, uu____14103,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____14126, false) in
                                  constructor_or_logic_type_decl uu____14102 in
                                let uu____14131 =
                                  match vars with
                                  | [] ->
                                      let uu____14138 =
                                        let uu____14139 =
                                          let uu____14141 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_38  -> Some _0_38)
                                            uu____14141 in
                                        push_free_var env1 t tname
                                          uu____14139 in
                                      ([], uu____14138)
                                  | uu____14145 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token")) in
                                      let ttok_fresh =
                                        let uu____14151 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____14151 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____14160 =
                                          let uu____14164 =
                                            let uu____14165 =
                                              let uu____14173 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats, None, vars, uu____14173) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____14165 in
                                          (uu____14164,
                                            (Some "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Term.Assume
                                          uu____14160 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____14131 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____14096 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____14196 =
                                       encode_term_pred None res1 env' tapp in
                                     match uu____14196 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____14210 =
                                               let uu____14211 =
                                                 let uu____14215 =
                                                   let uu____14216 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____14216 in
                                                 (uu____14215,
                                                   (Some "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Term.Assume
                                                 uu____14211 in
                                             [uu____14210]
                                           else [] in
                                         let uu____14219 =
                                           let uu____14221 =
                                             let uu____14223 =
                                               let uu____14224 =
                                                 let uu____14228 =
                                                   let uu____14229 =
                                                     let uu____14235 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____14235) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____14229 in
                                                 (uu____14228, None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Term.Assume
                                                 uu____14224 in
                                             [uu____14223] in
                                           FStar_List.append karr uu____14221 in
                                         FStar_List.append decls1 uu____14219 in
                                   let aux =
                                     let uu____14244 =
                                       let uu____14246 =
                                         inversion_axioms tapp vars in
                                       let uu____14248 =
                                         let uu____14250 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____14250] in
                                       FStar_List.append uu____14246
                                         uu____14248 in
                                     FStar_List.append kindingAx uu____14244 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14255,uu____14256,uu____14257,uu____14258,uu____14259)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14264,t,uu____14266,n_tps,uu____14268) ->
          let quals = se.FStar_Syntax_Syntax.sigqual in
          let uu____14273 = new_term_constant_and_tok_from_lid env d in
          (match uu____14273 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____14284 = FStar_Syntax_Util.arrow_formals t in
               (match uu____14284 with
                | (formals,t_res) ->
                    let uu____14306 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____14306 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____14315 =
                           encode_binders (Some fuel_tm) formals env1 in
                         (match uu____14315 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____14353 =
                                            mk_term_projector_name d x in
                                          (uu____14353,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____14355 =
                                  let uu____14365 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14365, true) in
                                FStar_All.pipe_right uu____14355
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
                              let uu____14387 =
                                encode_term_pred None t env1 ddtok_tm in
                              (match uu____14387 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____14395::uu____14396 ->
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
                                         let uu____14421 =
                                           let uu____14427 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____14427) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____14421
                                     | uu____14440 -> tok_typing in
                                   let uu____14445 =
                                     encode_binders (Some fuel_tm) formals
                                       env1 in
                                   (match uu____14445 with
                                    | (vars',guards',env'',decls_formals,uu____14460)
                                        ->
                                        let uu____14467 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1) in
                                          encode_term_pred (Some fuel_tm)
                                            t_res env'' dapp1 in
                                        (match uu____14467 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14486 ->
                                                   let uu____14490 =
                                                     let uu____14491 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14491 in
                                                   [uu____14490] in
                                             let encode_elim uu____14498 =
                                               let uu____14499 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____14499 with
                                               | (head1,args) ->
                                                   let uu____14528 =
                                                     let uu____14529 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____14529.FStar_Syntax_Syntax.n in
                                                   (match uu____14528 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                      ({
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           FStar_Syntax_Syntax.Tm_fvar
                                                           fv;
                                                         FStar_Syntax_Syntax.tk
                                                           = _;
                                                         FStar_Syntax_Syntax.pos
                                                           = _;
                                                         FStar_Syntax_Syntax.vars
                                                           = _;_},_)
                                                      |FStar_Syntax_Syntax.Tm_fvar
                                                      fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____14547 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14547
                                                         with
                                                         | (encoded_args,arg_decls)
                                                             ->
                                                             let guards_for_parameter
                                                               arg xv =
                                                               let fv1 =
                                                                 match 
                                                                   arg.FStar_SMTEncoding_Term.tm
                                                                 with
                                                                 | FStar_SMTEncoding_Term.FreeV
                                                                    fv1 ->
                                                                    fv1
                                                                 | uu____14573
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14581
                                                                    =
                                                                    let uu____14582
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14582 in
                                                                    if
                                                                    uu____14581
                                                                    then
                                                                    let uu____14589
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14589]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____14591
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14604
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14604
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14626
                                                                    =
                                                                    let uu____14630
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14630 in
                                                                    (match uu____14626
                                                                    with
                                                                    | 
                                                                    (uu____14637,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14643
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____14643
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14645
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____14645
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
                                                                 encoded_args in
                                                             (match uu____14591
                                                              with
                                                              | (uu____14653,arg_vars,elim_eqns_or_guards,uu____14656)
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
                                                                    (Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty in
                                                                  let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1 in
                                                                  let typing_inversion
                                                                    =
                                                                    let uu____14675
                                                                    =
                                                                    let uu____14679
                                                                    =
                                                                    let uu____14680
                                                                    =
                                                                    let uu____14686
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14692
                                                                    =
                                                                    let uu____14693
                                                                    =
                                                                    let uu____14696
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____14696) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14693 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14686,
                                                                    uu____14692) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14680 in
                                                                    (uu____14679,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14675 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____14709
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____14709,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____14711
                                                                    =
                                                                    let uu____14715
                                                                    =
                                                                    let uu____14716
                                                                    =
                                                                    let uu____14722
                                                                    =
                                                                    let uu____14725
                                                                    =
                                                                    let uu____14727
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____14727] in
                                                                    [uu____14725] in
                                                                    let uu____14730
                                                                    =
                                                                    let uu____14731
                                                                    =
                                                                    let uu____14734
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____14735
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____14734,
                                                                    uu____14735) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14731 in
                                                                    (uu____14722,
                                                                    [x],
                                                                    uu____14730) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14716 in
                                                                    let uu____14745
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____14715,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____14745) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14711
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14750
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
                                                                    (let uu____14765
                                                                    =
                                                                    let uu____14766
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____14766
                                                                    dapp1 in
                                                                    [uu____14765]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____14750
                                                                    FStar_List.flatten in
                                                                    let uu____14770
                                                                    =
                                                                    let uu____14774
                                                                    =
                                                                    let uu____14775
                                                                    =
                                                                    let uu____14781
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14787
                                                                    =
                                                                    let uu____14788
                                                                    =
                                                                    let uu____14791
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____14791) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14788 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14781,
                                                                    uu____14787) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14775 in
                                                                    (uu____14774,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14770) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____14801 ->
                                                        ((let uu____14803 =
                                                            let uu____14804 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____14805 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____14804
                                                              uu____14805 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____14803);
                                                         ([], []))) in
                                             let uu____14808 = encode_elim () in
                                             (match uu____14808 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____14820 =
                                                      let uu____14822 =
                                                        let uu____14824 =
                                                          let uu____14826 =
                                                            let uu____14828 =
                                                              let uu____14829
                                                                =
                                                                let uu____14835
                                                                  =
                                                                  let uu____14837
                                                                    =
                                                                    let uu____14838
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____14838 in
                                                                  Some
                                                                    uu____14837 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____14835) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____14829 in
                                                            [uu____14828] in
                                                          let uu____14841 =
                                                            let uu____14843 =
                                                              let uu____14845
                                                                =
                                                                let uu____14847
                                                                  =
                                                                  let uu____14849
                                                                    =
                                                                    let uu____14851
                                                                    =
                                                                    let uu____14853
                                                                    =
                                                                    let uu____14854
                                                                    =
                                                                    let uu____14858
                                                                    =
                                                                    let uu____14859
                                                                    =
                                                                    let uu____14865
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____14865) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14859 in
                                                                    (uu____14858,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14854 in
                                                                    let uu____14872
                                                                    =
                                                                    let uu____14874
                                                                    =
                                                                    let uu____14875
                                                                    =
                                                                    let uu____14879
                                                                    =
                                                                    let uu____14880
                                                                    =
                                                                    let uu____14886
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____14892
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____14886,
                                                                    uu____14892) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14880 in
                                                                    (uu____14879,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14875 in
                                                                    [uu____14874] in
                                                                    uu____14853
                                                                    ::
                                                                    uu____14872 in
                                                                    (FStar_SMTEncoding_Term.Assume
                                                                    (tok_typing1,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____14851 in
                                                                  FStar_List.append
                                                                    uu____14849
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____14847 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____14845 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____14843 in
                                                          FStar_List.append
                                                            uu____14826
                                                            uu____14841 in
                                                        FStar_List.append
                                                          decls3 uu____14824 in
                                                      FStar_List.append
                                                        decls2 uu____14822 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____14820 in
                                                  ((FStar_List.append
                                                      datacons g), env1)))))))))
and encode_signature:
  env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____14913  ->
              fun se  ->
                match uu____14913 with
                | (g,env1) ->
                    let uu____14925 = encode_sigelt env1 se in
                    (match uu____14925 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____14961 =
        match uu____14961 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____14979 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort in
                 ((let uu____14984 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____14984
                   then
                     let uu____14985 = FStar_Syntax_Print.bv_to_string x in
                     let uu____14986 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____14987 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____14985 uu____14986 uu____14987
                   else ());
                  (let uu____14989 = encode_term t1 env1 in
                   match uu____14989 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____14999 =
                         let uu____15003 =
                           let uu____15004 =
                             let uu____15005 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____15005
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____15004 in
                         new_term_constant_from_string env1 x uu____15003 in
                       (match uu____14999 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t in
                            let caption =
                              let uu____15016 = FStar_Options.log_queries () in
                              if uu____15016
                              then
                                let uu____15018 =
                                  let uu____15019 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____15020 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____15021 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____15019 uu____15020 uu____15021 in
                                Some uu____15018
                              else None in
                            let ax =
                              let a_name = Prims.strcat "binder_" xxsym in
                              FStar_SMTEncoding_Term.Assume
                                (t2, (Some a_name), a_name) in
                            let g =
                              FStar_List.append
                                [FStar_SMTEncoding_Term.DeclFun
                                   (xxsym, [],
                                     FStar_SMTEncoding_Term.Term_sort,
                                     caption)]
                                (FStar_List.append decls' [ax]) in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____15032,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None in
                 let uu____15041 = encode_free_var env1 fv t t_norm [] in
                 (match uu____15041 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst (_,se,_)
               |FStar_TypeChecker_Env.Binding_sig (_,se) ->
                 let uu____15060 = encode_sigelt env1 se in
                 (match uu____15060 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____15070 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____15070 with | (uu____15082,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____15127  ->
            match uu____15127 with
            | (l,uu____15134,uu____15135) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____15156  ->
            match uu____15156 with
            | (l,uu____15164,uu____15165) ->
                let uu____15170 =
                  FStar_All.pipe_left
                    (fun _0_39  -> FStar_SMTEncoding_Term.Echo _0_39)
                    (Prims.fst l) in
                let uu____15171 =
                  let uu____15173 =
                    let uu____15174 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____15174 in
                  [uu____15173] in
                uu____15170 :: uu____15171)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____15185 =
      let uu____15187 =
        let uu____15188 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____15200 =
          let uu____15201 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____15201 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____15188;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____15200
        } in
      [uu____15187] in
    FStar_ST.write last_env uu____15185
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____15211 = FStar_ST.read last_env in
      match uu____15211 with
      | [] -> failwith "No env; call init first!"
      | e::uu____15217 ->
          let uu___168_15219 = e in
          let uu____15220 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___168_15219.bindings);
            depth = (uu___168_15219.depth);
            tcenv;
            warn = (uu___168_15219.warn);
            cache = (uu___168_15219.cache);
            nolabels = (uu___168_15219.nolabels);
            use_zfuel_name = (uu___168_15219.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___168_15219.encode_non_total_function_typ);
            current_module_name = uu____15220
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____15224 = FStar_ST.read last_env in
    match uu____15224 with
    | [] -> failwith "Empty env stack"
    | uu____15229::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____15237  ->
    let uu____15238 = FStar_ST.read last_env in
    match uu____15238 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___169_15259 = hd1 in
          {
            bindings = (uu___169_15259.bindings);
            depth = (uu___169_15259.depth);
            tcenv = (uu___169_15259.tcenv);
            warn = (uu___169_15259.warn);
            cache = refs;
            nolabels = (uu___169_15259.nolabels);
            use_zfuel_name = (uu___169_15259.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___169_15259.encode_non_total_function_typ);
            current_module_name = (uu___169_15259.current_module_name)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____15265  ->
    let uu____15266 = FStar_ST.read last_env in
    match uu____15266 with
    | [] -> failwith "Popping an empty stack"
    | uu____15271::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____15279  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____15282  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____15285  ->
    let uu____15286 = FStar_ST.read last_env in
    match uu____15286 with
    | hd1::uu____15292::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____15298 -> failwith "Impossible"
let init: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    init_env tcenv;
    FStar_SMTEncoding_Z3.init ();
    FStar_SMTEncoding_Z3.giveZ3 [FStar_SMTEncoding_Term.DefPrelude]
let push: Prims.string -> Prims.unit =
  fun msg  -> push_env (); varops.push (); FStar_SMTEncoding_Z3.push msg
let pop: Prims.string -> Prims.unit =
  fun msg  -> pop_env (); varops.pop (); FStar_SMTEncoding_Z3.pop msg
let mark: Prims.string -> Prims.unit =
  fun msg  -> mark_env (); varops.mark (); FStar_SMTEncoding_Z3.mark msg
let reset_mark: Prims.string -> Prims.unit =
  fun msg  ->
    reset_mark_env ();
    varops.reset_mark ();
    FStar_SMTEncoding_Z3.reset_mark msg
let commit_mark: Prims.string -> Prims.unit =
  fun msg  ->
    commit_mark_env ();
    varops.commit_mark ();
    FStar_SMTEncoding_Z3.commit_mark msg
let encode_sig:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____15343 = FStar_Options.log_queries () in
        if uu____15343
        then
          let uu____15345 =
            let uu____15346 =
              let uu____15347 =
                let uu____15348 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____15348 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____15347 in
            FStar_SMTEncoding_Term.Caption uu____15346 in
          uu____15345 :: decls
        else decls in
      let env =
        let uu____15355 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15355 tcenv in
      let uu____15356 = encode_sigelt env se in
      match uu____15356 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____15362 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____15362))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____15373 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____15373
       then
         let uu____15374 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____15374
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let uu____15379 =
         encode_signature
           (let uu___170_15383 = env in
            {
              bindings = (uu___170_15383.bindings);
              depth = (uu___170_15383.depth);
              tcenv = (uu___170_15383.tcenv);
              warn = false;
              cache = (uu___170_15383.cache);
              nolabels = (uu___170_15383.nolabels);
              use_zfuel_name = (uu___170_15383.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___170_15383.encode_non_total_function_typ);
              current_module_name = (uu___170_15383.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____15379 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____15395 = FStar_Options.log_queries () in
             if uu____15395
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___171_15400 = env1 in
               {
                 bindings = (uu___171_15400.bindings);
                 depth = (uu___171_15400.depth);
                 tcenv = (uu___171_15400.tcenv);
                 warn = true;
                 cache = (uu___171_15400.cache);
                 nolabels = (uu___171_15400.nolabels);
                 use_zfuel_name = (uu___171_15400.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___171_15400.encode_non_total_function_typ);
                 current_module_name = (uu___171_15400.current_module_name)
               });
            (let uu____15402 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____15402
             then FStar_Util.print1 "Done encoding externals for %s\n" name
             else ());
            (let decls1 = caption decls in FStar_SMTEncoding_Z3.giveZ3 decls1)))
let encode_query:
  (Prims.unit -> Prims.string) Prims.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_SMTEncoding_Term.decl Prims.list*
          FStar_SMTEncoding_ErrorReporting.label Prims.list*
          FStar_SMTEncoding_Term.decl* FStar_SMTEncoding_Term.decl
          Prims.list)
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____15437 =
           let uu____15438 = FStar_TypeChecker_Env.current_module tcenv in
           uu____15438.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____15437);
        (let env =
           let uu____15440 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____15440 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____15447 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____15468 = aux rest in
                 (match uu____15468 with
                  | (out,rest1) ->
                      let t =
                        let uu____15486 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____15486 with
                        | Some uu____15490 ->
                            let uu____15491 =
                              FStar_Syntax_Syntax.new_bv None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____15491
                              x.FStar_Syntax_Syntax.sort
                        | uu____15492 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____15495 =
                        let uu____15497 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___172_15498 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___172_15498.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___172_15498.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____15497 :: out in
                      (uu____15495, rest1))
             | uu____15501 -> ([], bindings1) in
           let uu____15505 = aux bindings in
           match uu____15505 with
           | (closing,bindings1) ->
               let uu____15519 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____15519, bindings1) in
         match uu____15447 with
         | (q1,bindings1) ->
             let uu____15532 =
               let uu____15535 =
                 FStar_List.filter
                   (fun uu___139_15537  ->
                      match uu___139_15537 with
                      | FStar_TypeChecker_Env.Binding_sig uu____15538 ->
                          false
                      | uu____15542 -> true) bindings1 in
               encode_env_bindings env uu____15535 in
             (match uu____15532 with
              | (env_decls,env1) ->
                  ((let uu____15553 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____15553
                    then
                      let uu____15554 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____15554
                    else ());
                   (let uu____15556 = encode_formula q1 env1 in
                    match uu____15556 with
                    | (phi,qdecls) ->
                        let uu____15568 =
                          let uu____15571 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____15571 phi in
                        (match uu____15568 with
                         | (labels,phi1) ->
                             let uu____15581 = encode_labels labels in
                             (match uu____15581 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____15602 =
                                      let uu____15606 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____15607 =
                                        varops.mk_unique "@query" in
                                      (uu____15606, (Some "query"),
                                        uu____15607) in
                                    FStar_SMTEncoding_Term.Assume uu____15602 in
                                  let suffix =
                                    FStar_List.append label_suffix
                                      [FStar_SMTEncoding_Term.Echo "Done!"] in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____15620 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15620 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____15622 = encode_formula q env in
       match uu____15622 with
       | (f,uu____15626) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____15628) -> true
             | uu____15631 -> false)))