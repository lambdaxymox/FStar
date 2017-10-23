open Prims
type verify_mode =
  | VerifyAll
  | VerifyUserList
  | VerifyFigureItOut[@@deriving show]
let uu___is_VerifyAll: verify_mode -> Prims.bool =
  fun projectee  ->
    match projectee with | VerifyAll  -> true | uu____5 -> false
let uu___is_VerifyUserList: verify_mode -> Prims.bool =
  fun projectee  ->
    match projectee with | VerifyUserList  -> true | uu____10 -> false
let uu___is_VerifyFigureItOut: verify_mode -> Prims.bool =
  fun projectee  ->
    match projectee with | VerifyFigureItOut  -> true | uu____15 -> false
type map =
  (Prims.int,(Prims.string FStar_Pervasives_Native.option,Prims.string
                                                            FStar_Pervasives_Native.option)
               FStar_Pervasives_Native.tuple2)
    FStar_Pervasives_Native.tuple2 FStar_Util.smap[@@deriving show]
type color =
  | White
  | Gray
  | Black[@@deriving show]
let uu___is_White: color -> Prims.bool =
  fun projectee  -> match projectee with | White  -> true | uu____34 -> false
let uu___is_Gray: color -> Prims.bool =
  fun projectee  -> match projectee with | Gray  -> true | uu____39 -> false
let uu___is_Black: color -> Prims.bool =
  fun projectee  -> match projectee with | Black  -> true | uu____44 -> false
type open_kind =
  | Open_module
  | Open_namespace[@@deriving show]
let uu___is_Open_module: open_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Open_module  -> true | uu____49 -> false
let uu___is_Open_namespace: open_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____54 -> false
let check_and_strip_suffix:
  Prims.string -> Prims.string FStar_Pervasives_Native.option =
  fun f  ->
    let suffixes = [".fsti"; ".fst"; ".fsi"; ".fs"] in
    let matches =
      FStar_List.map
        (fun ext  ->
           let lext = FStar_String.length ext in
           let l = FStar_String.length f in
           let uu____81 =
             (l > lext) &&
               (let uu____93 = FStar_String.substring f (l - lext) lext in
                uu____93 = ext) in
           if uu____81
           then
             let uu____110 =
               FStar_String.substring f (Prims.parse_int "0") (l - lext) in
             FStar_Pervasives_Native.Some uu____110
           else FStar_Pervasives_Native.None) suffixes in
    let uu____122 = FStar_List.filter FStar_Util.is_some matches in
    match uu____122 with
    | (FStar_Pervasives_Native.Some m)::uu____132 ->
        FStar_Pervasives_Native.Some m
    | uu____139 -> FStar_Pervasives_Native.None
let is_interface: Prims.string -> Prims.bool =
  fun f  ->
    let uu____148 =
      FStar_String.get f ((FStar_String.length f) - (Prims.parse_int "1")) in
    uu____148 = 105
let is_implementation: Prims.string -> Prims.bool =
  fun f  -> let uu____153 = is_interface f in Prims.op_Negation uu____153
let list_of_option:
  'Auu____158 .
    'Auu____158 FStar_Pervasives_Native.option -> 'Auu____158 Prims.list
  =
  fun uu___90_166  ->
    match uu___90_166 with
    | FStar_Pervasives_Native.Some x -> [x]
    | FStar_Pervasives_Native.None  -> []
let list_of_pair:
  'Auu____174 .
    ('Auu____174 FStar_Pervasives_Native.option,'Auu____174
                                                  FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 -> 'Auu____174 Prims.list
  =
  fun uu____188  ->
    match uu____188 with
    | (intf,impl) ->
        FStar_List.append (list_of_option intf) (list_of_option impl)
let lowercase_module_name: Prims.string -> Prims.string =
  fun f  ->
    let uu____211 =
      let uu____214 = FStar_Util.basename f in
      check_and_strip_suffix uu____214 in
    match uu____211 with
    | FStar_Pervasives_Native.Some longname ->
        FStar_String.lowercase longname
    | FStar_Pervasives_Native.None  ->
        let uu____216 =
          let uu____217 = FStar_Util.format1 "not a valid FStar file: %s\n" f in
          FStar_Errors.Err uu____217 in
        FStar_Exn.raise uu____216
let build_inclusion_candidates_list:
  Prims.unit ->
    (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____227  ->
    let include_directories = FStar_Options.include_path () in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories in
    let include_directories2 = FStar_List.unique include_directories1 in
    let cwd =
      let uu____244 = FStar_Util.getcwd () in
      FStar_Util.normalize_file_path uu____244 in
    FStar_List.concatMap
      (fun d  ->
         if FStar_Util.file_exists d
         then
           let files = FStar_Util.readdir d in
           FStar_List.filter_map
             (fun f  ->
                let f1 = FStar_Util.basename f in
                let uu____270 = check_and_strip_suffix f1 in
                FStar_All.pipe_right uu____270
                  (FStar_Util.map_option
                     (fun longname  ->
                        let full_path =
                          if d = cwd then f1 else FStar_Util.join_paths d f1 in
                        (longname, full_path)))) files
         else
           (let uu____291 =
              let uu____292 =
                FStar_Util.format1 "not a valid include directory: %s\n" d in
              FStar_Errors.Err uu____292 in
            FStar_Exn.raise uu____291)) include_directories2
let build_map: Prims.string Prims.list -> map =
  fun filenames  ->
    let map1 = FStar_Util.smap_create (Prims.parse_int "41") in
    let add_entry key full_path =
      let uu____341 = FStar_Util.smap_try_find map1 key in
      match uu____341 with
      | FStar_Pervasives_Native.Some (x,(intf,impl)) ->
          let uu____399 = is_interface full_path in
          if uu____399
          then
            FStar_Util.smap_add map1 key
              ((Prims.parse_int "0"),
                ((FStar_Pervasives_Native.Some full_path), impl))
          else
            FStar_Util.smap_add map1 key
              ((Prims.parse_int "0"),
                (intf, (FStar_Pervasives_Native.Some full_path)))
      | FStar_Pervasives_Native.None  ->
          let uu____461 = is_interface full_path in
          if uu____461
          then
            FStar_Util.smap_add map1 key
              ((Prims.parse_int "0"),
                ((FStar_Pervasives_Native.Some full_path),
                  FStar_Pervasives_Native.None))
          else
            FStar_Util.smap_add map1 key
              ((Prims.parse_int "0"),
                (FStar_Pervasives_Native.None,
                  (FStar_Pervasives_Native.Some full_path))) in
    (let uu____512 = build_inclusion_candidates_list () in
     FStar_List.iter
       (fun uu____526  ->
          match uu____526 with
          | (longname,full_path) ->
              add_entry (FStar_String.lowercase longname) full_path)
       uu____512);
    FStar_List.iter
      (fun f  ->
         let uu____537 = lowercase_module_name f in add_entry uu____537 f)
      filenames;
    map1
let enter_namespace: map -> map -> Prims.string -> Prims.bool =
  fun original_map  ->
    fun working_map  ->
      fun prefix1  ->
        let found = FStar_Util.mk_ref false in
        let prefix2 = Prims.strcat prefix1 "." in
        (let uu____555 =
           let uu____558 = FStar_Util.smap_keys original_map in
           FStar_List.unique uu____558 in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                (FStar_ST.op_Colon_Equals found true;
                 (let suffix =
                    FStar_String.substring k (FStar_String.length prefix2)
                      ((FStar_String.length k) -
                         (FStar_String.length prefix2)) in
                  let uu____646 =
                    let uu____659 = FStar_Util.smap_try_find original_map k in
                    FStar_Util.must uu____659 in
                  match uu____646 with
                  | (d,(intf,impl)) ->
                      let uu____717 =
                        FStar_Util.smap_try_find working_map suffix in
                      (match uu____717 with
                       | FStar_Pervasives_Native.Some (d',uu____745) when
                           d' <= d -> ()
                       | uu____774 ->
                           FStar_Util.smap_add working_map suffix
                             ((d + (Prims.parse_int "1")), (intf, impl)))))
              else ()) uu____555);
        FStar_ST.op_Bang found
let string_of_lid: FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else [] in
      let names =
        let uu____891 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns in
        FStar_List.append uu____891 suffix in
      FStar_String.concat "." names
let lowercase_join_longident:
  FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let uu____904 = string_of_lid l last1 in
      FStar_String.lowercase uu____904
let namespace_of_lid: FStar_Ident.lident -> Prims.string =
  fun l  ->
    let uu____909 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns in
    FStar_String.concat "_" uu____909
let check_module_declaration_against_filename:
  FStar_Ident.lident -> Prims.string -> Prims.unit =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true in
      let uu____921 =
        let uu____922 =
          let uu____923 =
            let uu____924 =
              let uu____927 = FStar_Util.basename filename in
              check_and_strip_suffix uu____927 in
            FStar_Util.must uu____924 in
          FStar_String.lowercase uu____923 in
        uu____922 <> k' in
      if uu____921
      then
        let uu____928 =
          let uu____929 = string_of_lid lid true in
          FStar_Util.format2
            "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect.\n"
            uu____929 filename in
        FStar_Errors.warn (FStar_Ident.range_of_lid lid) uu____928
      else ()
exception Exit
let uu___is_Exit: Prims.exn -> Prims.bool =
  fun projectee  -> match projectee with | Exit  -> true | uu____935 -> false
let hard_coded_dependencies:
  Prims.string ->
    (FStar_Ident.lident,open_kind) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun filename  ->
    let filename1 = FStar_Util.basename filename in
    let corelibs =
      let uu____950 = FStar_Options.prims_basename () in
      let uu____951 =
        let uu____954 = FStar_Options.pervasives_basename () in
        let uu____955 =
          let uu____958 = FStar_Options.pervasives_native_basename () in
          [uu____958] in
        uu____954 :: uu____955 in
      uu____950 :: uu____951 in
    if FStar_List.mem filename1 corelibs
    then []
    else
      [(FStar_Parser_Const.fstar_ns_lid, Open_namespace);
      (FStar_Parser_Const.prims_lid, Open_module);
      (FStar_Parser_Const.pervasives_lid, Open_module)]
let collect_one:
  (Prims.string,Prims.bool FStar_ST.ref) FStar_Pervasives_Native.tuple2
    Prims.list ->
    verify_mode ->
      Prims.bool -> map -> Prims.string -> Prims.string Prims.list
  =
  fun verify_flags  ->
    fun verify_mode  ->
      fun is_user_provided_filename  ->
        fun original_map  ->
          fun filename  ->
            let deps = FStar_Util.mk_ref [] in
            let add_dep d =
              let uu____1037 =
                let uu____1038 =
                  let uu____1039 = FStar_ST.op_Bang deps in
                  FStar_List.existsML (fun d'  -> d' = d) uu____1039 in
                Prims.op_Negation uu____1038 in
              if uu____1037
              then
                let uu____1108 =
                  let uu____1111 = FStar_ST.op_Bang deps in d :: uu____1111 in
                FStar_ST.op_Colon_Equals deps uu____1108
              else () in
            let working_map = FStar_Util.smap_copy original_map in
            let record_open_module let_open lid =
              let key = lowercase_join_longident lid true in
              let uu____1278 = FStar_Util.smap_try_find working_map key in
              match uu____1278 with
              | FStar_Pervasives_Native.Some (uu____1305,pair) ->
                  (FStar_List.iter
                     (fun f  ->
                        let uu____1339 = lowercase_module_name f in
                        add_dep uu____1339) (list_of_pair pair);
                   true)
              | FStar_Pervasives_Native.None  ->
                  let r = enter_namespace original_map working_map key in
                  (if Prims.op_Negation r
                   then
                     (if let_open
                      then
                        FStar_Exn.raise
                          (FStar_Errors.Error
                             ("let-open only supported for modules, not namespaces",
                               (FStar_Ident.range_of_lid lid)))
                      else
                        (let uu____1355 =
                           let uu____1356 = string_of_lid lid true in
                           FStar_Util.format1
                             "No modules in namespace %s and no file with that name either"
                             uu____1356 in
                         FStar_Errors.warn (FStar_Ident.range_of_lid lid)
                           uu____1355))
                   else ();
                   false) in
            let record_open_namespace error_msg lid =
              let key = lowercase_join_longident lid true in
              let r = enter_namespace original_map working_map key in
              if Prims.op_Negation r
              then
                match error_msg with
                | FStar_Pervasives_Native.Some e ->
                    FStar_Exn.raise
                      (FStar_Errors.Error (e, (FStar_Ident.range_of_lid lid)))
                | FStar_Pervasives_Native.None  ->
                    let uu____1372 =
                      let uu____1373 = string_of_lid lid true in
                      FStar_Util.format1
                        "No modules in namespace %s and no file with that name either"
                        uu____1373 in
                    FStar_Errors.warn (FStar_Ident.range_of_lid lid)
                      uu____1372
              else () in
            let record_open let_open lid =
              let uu____1382 = record_open_module let_open lid in
              if uu____1382
              then ()
              else
                (let msg =
                   if let_open
                   then
                     FStar_Pervasives_Native.Some
                       "let-open only supported for modules, not namespaces"
                   else FStar_Pervasives_Native.None in
                 record_open_namespace msg lid) in
            let record_open_module_or_namespace uu____1397 =
              match uu____1397 with
              | (lid,kind) ->
                  (match kind with
                   | Open_namespace  ->
                       record_open_namespace FStar_Pervasives_Native.None lid
                   | Open_module  ->
                       let uu____1404 = record_open_module false lid in ()) in
            let record_module_alias ident lid =
              let key = FStar_String.lowercase (FStar_Ident.text_of_id ident) in
              let alias = lowercase_join_longident lid true in
              let uu____1414 = FStar_Util.smap_try_find original_map alias in
              match uu____1414 with
              | FStar_Pervasives_Native.Some deps_of_aliased_module ->
                  FStar_Util.smap_add working_map key deps_of_aliased_module
              | FStar_Pervasives_Native.None  ->
                  let uu____1490 =
                    let uu____1491 =
                      let uu____1496 =
                        FStar_Util.format1
                          "module not found in search path: %s\n" alias in
                      (uu____1496, (FStar_Ident.range_of_lid lid)) in
                    FStar_Errors.Error uu____1491 in
                  FStar_Exn.raise uu____1490 in
            let record_lid lid =
              let try_key key =
                let uu____1505 = FStar_Util.smap_try_find working_map key in
                match uu____1505 with
                | FStar_Pervasives_Native.Some (uu____1532,pair) ->
                    FStar_List.iter
                      (fun f  ->
                         let uu____1565 = lowercase_module_name f in
                         add_dep uu____1565) (list_of_pair pair)
                | FStar_Pervasives_Native.None  ->
                    let uu____1578 =
                      ((FStar_List.length lid.FStar_Ident.ns) >
                         (Prims.parse_int "0"))
                        && (FStar_Options.debug_any ()) in
                    if uu____1578
                    then
                      let uu____1579 =
                        let uu____1580 = string_of_lid lid false in
                        FStar_Util.format1 "Unbound module reference %s"
                          uu____1580 in
                      FStar_Errors.warn (FStar_Ident.range_of_lid lid)
                        uu____1579
                    else () in
              let uu____1583 = lowercase_join_longident lid false in
              try_key uu____1583 in
            let auto_open = hard_coded_dependencies filename in
            FStar_List.iter record_open_module_or_namespace auto_open;
            (let num_of_toplevelmods =
               FStar_Util.mk_ref (Prims.parse_int "0") in
             let rec collect_module uu___91_1668 =
               match uu___91_1668 with
               | FStar_Parser_AST.Module (lid,decls) ->
                   (check_module_declaration_against_filename lid filename;
                    if
                      (FStar_List.length lid.FStar_Ident.ns) >
                        (Prims.parse_int "0")
                    then
                      (let uu____1677 =
                         let uu____1678 = namespace_of_lid lid in
                         enter_namespace original_map working_map uu____1678 in
                       ())
                    else ();
                    (match verify_mode with
                     | VerifyAll  ->
                         let uu____1681 = string_of_lid lid true in
                         FStar_Options.add_verify_module uu____1681
                     | VerifyFigureItOut  ->
                         if is_user_provided_filename
                         then
                           let uu____1682 = string_of_lid lid true in
                           FStar_Options.add_verify_module uu____1682
                         else ()
                     | VerifyUserList  ->
                         FStar_List.iter
                           (fun uu____1786  ->
                              match uu____1786 with
                              | (m,r) ->
                                  let uu____2075 =
                                    let uu____2076 =
                                      let uu____2077 = string_of_lid lid true in
                                      FStar_String.lowercase uu____2077 in
                                    (FStar_String.lowercase m) = uu____2076 in
                                  if uu____2075
                                  then FStar_ST.op_Colon_Equals r true
                                  else ()) verify_flags);
                    collect_decls decls)
               | FStar_Parser_AST.Interface (lid,decls,uu____2223) ->
                   (check_module_declaration_against_filename lid filename;
                    if
                      (FStar_List.length lid.FStar_Ident.ns) >
                        (Prims.parse_int "0")
                    then
                      (let uu____2230 =
                         let uu____2231 = namespace_of_lid lid in
                         enter_namespace original_map working_map uu____2231 in
                       ())
                    else ();
                    (match verify_mode with
                     | VerifyAll  ->
                         let uu____2234 = string_of_lid lid true in
                         FStar_Options.add_verify_module uu____2234
                     | VerifyFigureItOut  ->
                         if is_user_provided_filename
                         then
                           let uu____2235 = string_of_lid lid true in
                           FStar_Options.add_verify_module uu____2235
                         else ()
                     | VerifyUserList  ->
                         FStar_List.iter
                           (fun uu____2339  ->
                              match uu____2339 with
                              | (m,r) ->
                                  let uu____2628 =
                                    let uu____2629 =
                                      let uu____2630 = string_of_lid lid true in
                                      FStar_String.lowercase uu____2630 in
                                    (FStar_String.lowercase m) = uu____2629 in
                                  if uu____2628
                                  then FStar_ST.op_Colon_Equals r true
                                  else ()) verify_flags);
                    collect_decls decls)
             and collect_decls decls =
               FStar_List.iter
                 (fun x  ->
                    collect_decl x.FStar_Parser_AST.d;
                    FStar_List.iter collect_term x.FStar_Parser_AST.attrs)
                 decls
             and collect_decl uu___92_2781 =
               match uu___92_2781 with
               | FStar_Parser_AST.Include lid -> record_open false lid
               | FStar_Parser_AST.Open lid -> record_open false lid
               | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
                   ((let uu____2787 = lowercase_join_longident lid true in
                     add_dep uu____2787);
                    record_module_alias ident lid)
               | FStar_Parser_AST.TopLevelLet (uu____2788,patterms) ->
                   FStar_List.iter
                     (fun uu____2810  ->
                        match uu____2810 with
                        | (pat,t) -> (collect_pattern pat; collect_term t))
                     patterms
               | FStar_Parser_AST.Main t -> collect_term t
               | FStar_Parser_AST.Assume (uu____2819,t) -> collect_term t
               | FStar_Parser_AST.SubEffect
                   { FStar_Parser_AST.msource = uu____2821;
                     FStar_Parser_AST.mdest = uu____2822;
                     FStar_Parser_AST.lift_op =
                       FStar_Parser_AST.NonReifiableLift t;_}
                   -> collect_term t
               | FStar_Parser_AST.SubEffect
                   { FStar_Parser_AST.msource = uu____2824;
                     FStar_Parser_AST.mdest = uu____2825;
                     FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree
                       t;_}
                   -> collect_term t
               | FStar_Parser_AST.Val (uu____2827,t) -> collect_term t
               | FStar_Parser_AST.SubEffect
                   { FStar_Parser_AST.msource = uu____2829;
                     FStar_Parser_AST.mdest = uu____2830;
                     FStar_Parser_AST.lift_op =
                       FStar_Parser_AST.ReifiableLift (t0,t1);_}
                   -> (collect_term t0; collect_term t1)
               | FStar_Parser_AST.Tycon (uu____2834,ts) ->
                   let ts1 =
                     FStar_List.map
                       (fun uu____2864  ->
                          match uu____2864 with | (x,docnik) -> x) ts in
                   FStar_List.iter collect_tycon ts1
               | FStar_Parser_AST.Exception (uu____2877,t) ->
                   FStar_Util.iter_opt t collect_term
               | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
               | FStar_Parser_AST.Fsdoc uu____2884 -> ()
               | FStar_Parser_AST.Pragma uu____2885 -> ()
               | FStar_Parser_AST.TopLevelModule lid ->
                   (FStar_Util.incr num_of_toplevelmods;
                    (let uu____2909 =
                       let uu____2910 = FStar_ST.op_Bang num_of_toplevelmods in
                       uu____2910 > (Prims.parse_int "1") in
                     if uu____2909
                     then
                       let uu____2971 =
                         let uu____2972 =
                           let uu____2977 =
                             let uu____2978 = string_of_lid lid true in
                             FStar_Util.format1
                               "Automatic dependency analysis demands one module per file (module %s not supported)"
                               uu____2978 in
                           (uu____2977, (FStar_Ident.range_of_lid lid)) in
                         FStar_Errors.Error uu____2972 in
                       FStar_Exn.raise uu____2971
                     else ()))
             and collect_tycon uu___93_2980 =
               match uu___93_2980 with
               | FStar_Parser_AST.TyconAbstract (uu____2981,binders,k) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term)
               | FStar_Parser_AST.TyconAbbrev (uu____2993,binders,k,t) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term;
                    collect_term t)
               | FStar_Parser_AST.TyconRecord
                   (uu____3007,binders,k,identterms) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term;
                    FStar_List.iter
                      (fun uu____3053  ->
                         match uu____3053 with
                         | (uu____3062,t,uu____3064) -> collect_term t)
                      identterms)
               | FStar_Parser_AST.TyconVariant
                   (uu____3069,binders,k,identterms) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term;
                    FStar_List.iter
                      (fun uu____3128  ->
                         match uu____3128 with
                         | (uu____3141,t,uu____3143,uu____3144) ->
                             FStar_Util.iter_opt t collect_term) identterms)
             and collect_effect_decl uu___94_3153 =
               match uu___94_3153 with
               | FStar_Parser_AST.DefineEffect (uu____3154,binders,t,decls)
                   ->
                   (collect_binders binders;
                    collect_term t;
                    collect_decls decls)
               | FStar_Parser_AST.RedefineEffect (uu____3168,binders,t) ->
                   (collect_binders binders; collect_term t)
             and collect_binders binders =
               FStar_List.iter collect_binder binders
             and collect_binder uu___95_3179 =
               match uu___95_3179 with
               | {
                   FStar_Parser_AST.b = FStar_Parser_AST.Annotated
                     (uu____3180,t);
                   FStar_Parser_AST.brange = uu____3182;
                   FStar_Parser_AST.blevel = uu____3183;
                   FStar_Parser_AST.aqual = uu____3184;_} -> collect_term t
               | {
                   FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated
                     (uu____3185,t);
                   FStar_Parser_AST.brange = uu____3187;
                   FStar_Parser_AST.blevel = uu____3188;
                   FStar_Parser_AST.aqual = uu____3189;_} -> collect_term t
               | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
                   FStar_Parser_AST.brange = uu____3191;
                   FStar_Parser_AST.blevel = uu____3192;
                   FStar_Parser_AST.aqual = uu____3193;_} -> collect_term t
               | uu____3194 -> ()
             and collect_term t = collect_term' t.FStar_Parser_AST.tm
             and collect_constant uu___96_3196 =
               match uu___96_3196 with
               | FStar_Const.Const_int
                   (uu____3197,FStar_Pervasives_Native.Some
                    (signedness,width))
                   ->
                   let u =
                     match signedness with
                     | FStar_Const.Unsigned  -> "u"
                     | FStar_Const.Signed  -> "" in
                   let w =
                     match width with
                     | FStar_Const.Int8  -> "8"
                     | FStar_Const.Int16  -> "16"
                     | FStar_Const.Int32  -> "32"
                     | FStar_Const.Int64  -> "64" in
                   let uu____3212 = FStar_Util.format2 "fstar.%sint%s" u w in
                   add_dep uu____3212
               | FStar_Const.Const_char uu____3213 -> add_dep "fstar.char"
               | FStar_Const.Const_float uu____3214 -> add_dep "fstar.float"
               | uu____3215 -> ()
             and collect_term' uu___97_3216 =
               match uu___97_3216 with
               | FStar_Parser_AST.Wild  -> ()
               | FStar_Parser_AST.Const c -> collect_constant c
               | FStar_Parser_AST.Op (s,ts) ->
                   (if (FStar_Ident.text_of_id s) = "@"
                    then
                      (let uu____3225 =
                         let uu____3226 =
                           FStar_Ident.lid_of_path
                             (FStar_Ident.path_of_text
                                "FStar.List.Tot.Base.append")
                             FStar_Range.dummyRange in
                         FStar_Parser_AST.Name uu____3226 in
                       collect_term' uu____3225)
                    else ();
                    FStar_List.iter collect_term ts)
               | FStar_Parser_AST.Tvar uu____3228 -> ()
               | FStar_Parser_AST.Uvar uu____3229 -> ()
               | FStar_Parser_AST.Var lid -> record_lid lid
               | FStar_Parser_AST.Projector (lid,uu____3232) ->
                   record_lid lid
               | FStar_Parser_AST.Discrim lid -> record_lid lid
               | FStar_Parser_AST.Name lid -> record_lid lid
               | FStar_Parser_AST.Construct (lid,termimps) ->
                   (if (FStar_List.length termimps) = (Prims.parse_int "1")
                    then record_lid lid
                    else ();
                    FStar_List.iter
                      (fun uu____3262  ->
                         match uu____3262 with
                         | (t,uu____3268) -> collect_term t) termimps)
               | FStar_Parser_AST.Abs (pats,t) ->
                   (collect_patterns pats; collect_term t)
               | FStar_Parser_AST.App (t1,t2,uu____3278) ->
                   (collect_term t1; collect_term t2)
               | FStar_Parser_AST.Let (uu____3280,patterms,t) ->
                   (FStar_List.iter
                      (fun uu____3304  ->
                         match uu____3304 with
                         | (pat,t1) -> (collect_pattern pat; collect_term t1))
                      patterms;
                    collect_term t)
               | FStar_Parser_AST.LetOpen (lid,t) ->
                   (record_open true lid; collect_term t)
               | FStar_Parser_AST.Bind (uu____3315,t1,t2) ->
                   (collect_term t1; collect_term t2)
               | FStar_Parser_AST.Seq (t1,t2) ->
                   (collect_term t1; collect_term t2)
               | FStar_Parser_AST.If (t1,t2,t3) ->
                   (collect_term t1; collect_term t2; collect_term t3)
               | FStar_Parser_AST.Match (t,bs) ->
                   (collect_term t; collect_branches bs)
               | FStar_Parser_AST.TryWith (t,bs) ->
                   (collect_term t; collect_branches bs)
               | FStar_Parser_AST.Ascribed
                   (t1,t2,FStar_Pervasives_Native.None ) ->
                   (collect_term t1; collect_term t2)
               | FStar_Parser_AST.Ascribed
                   (t1,t2,FStar_Pervasives_Native.Some tac) ->
                   (collect_term t1; collect_term t2; collect_term tac)
               | FStar_Parser_AST.Record (t,idterms) ->
                   (FStar_Util.iter_opt t collect_term;
                    FStar_List.iter
                      (fun uu____3411  ->
                         match uu____3411 with
                         | (uu____3416,t1) -> collect_term t1) idterms)
               | FStar_Parser_AST.Project (t,uu____3419) -> collect_term t
               | FStar_Parser_AST.Product (binders,t) ->
                   (collect_binders binders; collect_term t)
               | FStar_Parser_AST.Sum (binders,t) ->
                   (collect_binders binders; collect_term t)
               | FStar_Parser_AST.QForall (binders,ts,t) ->
                   (collect_binders binders;
                    FStar_List.iter (FStar_List.iter collect_term) ts;
                    collect_term t)
               | FStar_Parser_AST.QExists (binders,ts,t) ->
                   (collect_binders binders;
                    FStar_List.iter (FStar_List.iter collect_term) ts;
                    collect_term t)
               | FStar_Parser_AST.Refine (binder,t) ->
                   (collect_binder binder; collect_term t)
               | FStar_Parser_AST.NamedTyp (uu____3475,t) -> collect_term t
               | FStar_Parser_AST.Paren t -> collect_term t
               | FStar_Parser_AST.Assign (uu____3478,t) -> collect_term t
               | FStar_Parser_AST.Requires (t,uu____3481) -> collect_term t
               | FStar_Parser_AST.Ensures (t,uu____3487) -> collect_term t
               | FStar_Parser_AST.Labeled (t,uu____3493,uu____3494) ->
                   collect_term t
               | FStar_Parser_AST.Attributes cattributes ->
                   FStar_List.iter collect_term cattributes
             and collect_patterns ps = FStar_List.iter collect_pattern ps
             and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
             and collect_pattern' uu___98_3502 =
               match uu___98_3502 with
               | FStar_Parser_AST.PatWild  -> ()
               | FStar_Parser_AST.PatOp uu____3503 -> ()
               | FStar_Parser_AST.PatConst uu____3504 -> ()
               | FStar_Parser_AST.PatApp (p,ps) ->
                   (collect_pattern p; collect_patterns ps)
               | FStar_Parser_AST.PatVar uu____3512 -> ()
               | FStar_Parser_AST.PatName uu____3519 -> ()
               | FStar_Parser_AST.PatTvar uu____3520 -> ()
               | FStar_Parser_AST.PatList ps -> collect_patterns ps
               | FStar_Parser_AST.PatOr ps -> collect_patterns ps
               | FStar_Parser_AST.PatTuple (ps,uu____3534) ->
                   collect_patterns ps
               | FStar_Parser_AST.PatRecord lidpats ->
                   FStar_List.iter
                     (fun uu____3553  ->
                        match uu____3553 with
                        | (uu____3558,p) -> collect_pattern p) lidpats
               | FStar_Parser_AST.PatAscribed (p,t) ->
                   (collect_pattern p; collect_term t)
             and collect_branches bs = FStar_List.iter collect_branch bs
             and collect_branch uu____3582 =
               match uu____3582 with
               | (pat,t1,t2) ->
                   (collect_pattern pat;
                    FStar_Util.iter_opt t1 collect_term;
                    collect_term t2) in
             let uu____3600 = FStar_Parser_Driver.parse_file filename in
             match uu____3600 with
             | (ast,uu____3614) ->
                 (collect_module ast; FStar_ST.op_Bang deps))
let print_graph:
  'Auu____3696 .
    (Prims.string Prims.list,'Auu____3696) FStar_Pervasives_Native.tuple2
      FStar_Util.smap -> Prims.unit
  =
  fun graph  ->
    FStar_Util.print_endline
      "A DOT-format graph has been dumped in the current directory as dep.graph";
    FStar_Util.print_endline
      "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph";
    FStar_Util.print_endline
      "Hint: cat dep.graph | grep -v _ | grep -v prims";
    (let uu____3720 =
       let uu____3721 =
         let uu____3722 =
           let uu____3723 =
             let uu____3726 =
               let uu____3729 = FStar_Util.smap_keys graph in
               FStar_List.unique uu____3729 in
             FStar_List.collect
               (fun k  ->
                  let deps =
                    let uu____3745 =
                      let uu____3752 = FStar_Util.smap_try_find graph k in
                      FStar_Util.must uu____3752 in
                    FStar_Pervasives_Native.fst uu____3745 in
                  let r s = FStar_Util.replace_char s 46 95 in
                  FStar_List.map
                    (fun dep1  ->
                       FStar_Util.format2 "  %s -> %s" (r k) (r dep1)) deps)
               uu____3726 in
           FStar_String.concat "\n" uu____3723 in
         Prims.strcat uu____3722 "\n}\n" in
       Prims.strcat "digraph {\n" uu____3721 in
     FStar_Util.write_file "dep.graph" uu____3720)
let collect:
  verify_mode ->
    Prims.string Prims.list ->
      ((Prims.string,Prims.string Prims.list) FStar_Pervasives_Native.tuple2
         Prims.list,Prims.string Prims.list,(Prims.string Prims.list,
                                              color)
                                              FStar_Pervasives_Native.tuple2
                                              FStar_Util.smap)
        FStar_Pervasives_Native.tuple3
  =
  fun verify_mode  ->
    fun filenames  ->
      let graph = FStar_Util.smap_create (Prims.parse_int "41") in
      let verify_flags =
        let uu____3841 = FStar_Options.verify_module () in
        FStar_List.map
          (fun f  ->
             let uu____3853 = FStar_Util.mk_ref false in (f, uu____3853))
          uu____3841 in
      let partial_discovery =
        let uu____3873 =
          (FStar_Options.verify_all ()) || (FStar_Options.extract_all ()) in
        Prims.op_Negation uu____3873 in
      let m = build_map filenames in
      let file_names_of_key k =
        let uu____3879 =
          let uu____3892 = FStar_Util.smap_try_find m k in
          FStar_Util.must uu____3892 in
        match uu____3879 with
        | (uu____3931,(intf,impl)) ->
            (match (intf, impl) with
             | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None )
                 -> failwith "Impossible"
             | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some i)
                 -> i
             | (FStar_Pervasives_Native.Some i,FStar_Pervasives_Native.None )
                 -> i
             | (FStar_Pervasives_Native.Some i,uu____3969) when
                 partial_discovery -> i
             | (FStar_Pervasives_Native.Some i,FStar_Pervasives_Native.Some
                j) -> Prims.strcat i (Prims.strcat " && " j)) in
      let collect_one1 = collect_one verify_flags verify_mode in
      let rec discover_one is_user_provided_filename interface_only key =
        let uu____4001 =
          let uu____4002 = FStar_Util.smap_try_find graph key in
          uu____4002 = FStar_Pervasives_Native.None in
        if uu____4001
        then
          let uu____4031 =
            let uu____4044 = FStar_Util.smap_try_find m key in
            FStar_Util.must uu____4044 in
          match uu____4031 with
          | (uu____4083,(intf,impl)) ->
              let intf_deps =
                match intf with
                | FStar_Pervasives_Native.Some intf1 ->
                    collect_one1 is_user_provided_filename m intf1
                | FStar_Pervasives_Native.None  -> [] in
              let impl_deps =
                match (impl, intf) with
                | (FStar_Pervasives_Native.Some
                   impl1,FStar_Pervasives_Native.Some uu____4118) when
                    interface_only -> []
                | (FStar_Pervasives_Native.Some impl1,uu____4124) ->
                    collect_one1 is_user_provided_filename m impl1
                | (FStar_Pervasives_Native.None ,uu____4131) -> [] in
              let deps =
                FStar_List.unique (FStar_List.append impl_deps intf_deps) in
              (FStar_Util.smap_add graph key (deps, White);
               FStar_List.iter (discover_one false partial_discovery) deps)
        else () in
      let discover_command_line_argument f =
        let m1 = lowercase_module_name f in
        let interface_only =
          (is_interface f) &&
            (let uu____4158 =
               FStar_List.existsML
                 (fun f1  ->
                    (let uu____4163 = lowercase_module_name f1 in
                     uu____4163 = m1) && (is_implementation f1)) filenames in
             Prims.op_Negation uu____4158) in
        discover_one true interface_only m1 in
      FStar_List.iter discover_command_line_argument filenames;
      (let immediate_graph = FStar_Util.smap_copy graph in
       let topologically_sorted = FStar_Util.mk_ref [] in
       let rec discover cycle key =
         let uu____4200 =
           let uu____4207 = FStar_Util.smap_try_find graph key in
           FStar_Util.must uu____4207 in
         match uu____4200 with
         | (direct_deps,color) ->
             (match color with
              | Gray  ->
                  (FStar_Util.print1_warning
                     "Recursive dependency on module %s\n" key;
                   (let cycle1 =
                      FStar_All.pipe_right cycle
                        (FStar_List.map file_names_of_key) in
                    FStar_Util.print1
                      "The cycle contains a subset of the modules in:\n%s \n"
                      (FStar_String.concat "\n`used by` " cycle1);
                    print_graph immediate_graph;
                    FStar_Util.print_string "\n";
                    FStar_All.exit (Prims.parse_int "1")))
              | Black  -> direct_deps
              | White  ->
                  (FStar_Util.smap_add graph key (direct_deps, Gray);
                   (let all_deps =
                      let uu____4263 =
                        let uu____4266 =
                          FStar_List.map
                            (fun dep1  ->
                               let uu____4276 = discover (key :: cycle) dep1 in
                               dep1 :: uu____4276) direct_deps in
                        FStar_List.flatten uu____4266 in
                      FStar_List.unique uu____4263 in
                    FStar_Util.smap_add graph key (all_deps, Black);
                    (let uu____4289 =
                       let uu____4292 = FStar_ST.op_Bang topologically_sorted in
                       key :: uu____4292 in
                     FStar_ST.op_Colon_Equals topologically_sorted uu____4289);
                    all_deps))) in
       let discover1 = discover [] in
       let must_find k =
         let uu____4434 =
           let uu____4443 =
             let uu____4456 = FStar_Util.smap_try_find m k in
             FStar_Util.must uu____4456 in
           FStar_Pervasives_Native.snd uu____4443 in
         match uu____4434 with
         | (FStar_Pervasives_Native.Some intf,FStar_Pervasives_Native.Some
            impl) when
             (Prims.op_Negation partial_discovery) &&
               (let uu____4512 =
                  FStar_List.existsML
                    (fun f  ->
                       let uu____4516 = lowercase_module_name f in
                       uu____4516 = k) filenames in
                Prims.op_Negation uu____4512)
             -> [intf; impl]
         | (FStar_Pervasives_Native.Some intf,FStar_Pervasives_Native.Some
            impl) when
             FStar_List.existsML
               (fun f  ->
                  (is_implementation f) &&
                    (let uu____4526 = lowercase_module_name f in
                     uu____4526 = k)) filenames
             -> [intf; impl]
         | (FStar_Pervasives_Native.Some intf,uu____4528) -> [intf]
         | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some impl)
             -> [impl]
         | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
             [] in
       let must_find_r f =
         let uu____4550 = must_find f in FStar_List.rev uu____4550 in
       let by_target =
         let uu____4562 =
           let uu____4565 = FStar_Util.smap_keys graph in
           FStar_List.sortWith (fun x  -> fun y  -> FStar_String.compare x y)
             uu____4565 in
         FStar_List.collect
           (fun k  ->
              let as_list = must_find k in
              let is_interleaved =
                (FStar_List.length as_list) = (Prims.parse_int "2") in
              FStar_List.map
                (fun f  ->
                   let should_append_fsti =
                     (is_implementation f) && is_interleaved in
                   let k1 = lowercase_module_name f in
                   let suffix =
                     let uu____4610 =
                       let uu____4619 =
                         let uu____4632 = FStar_Util.smap_try_find m k1 in
                         FStar_Util.must uu____4632 in
                       FStar_Pervasives_Native.snd uu____4619 in
                     match uu____4610 with
                     | (FStar_Pervasives_Native.Some intf,uu____4682) when
                         should_append_fsti -> [intf]
                     | uu____4689 -> [] in
                   let deps =
                     let uu____4701 = discover1 k1 in
                     FStar_List.rev uu____4701 in
                   let deps_as_filenames =
                     let uu____4707 = FStar_List.collect must_find deps in
                     FStar_List.append uu____4707 suffix in
                   (f, deps_as_filenames)) as_list) uu____4562 in
       let topologically_sorted1 =
         let uu____4715 = FStar_ST.op_Bang topologically_sorted in
         FStar_List.collect must_find_r uu____4715 in
       FStar_List.iter
         (fun uu____4887  ->
            match uu____4887 with
            | (m1,r) ->
                let uu____5176 =
                  (let uu____5179 = FStar_ST.op_Bang r in
                   Prims.op_Negation uu____5179) &&
                    (let uu____5323 = FStar_Options.interactive () in
                     Prims.op_Negation uu____5323) in
                if uu____5176
                then
                  let maybe_fst =
                    let k = FStar_String.length m1 in
                    let uu____5326 =
                      (k > (Prims.parse_int "4")) &&
                        (let uu____5334 =
                           FStar_String.substring m1
                             (k - (Prims.parse_int "4"))
                             (Prims.parse_int "4") in
                         uu____5334 = ".fst") in
                    if uu____5326
                    then
                      let uu____5341 =
                        FStar_String.substring m1 (Prims.parse_int "0")
                          (k - (Prims.parse_int "4")) in
                      FStar_Util.format1 " Did you mean %s ?" uu____5341
                    else "" in
                  let uu____5349 =
                    let uu____5350 =
                      FStar_Util.format3
                        "You passed --verify_module %s but I found no file that contains [module %s] in the dependency graph.%s\n"
                        m1 m1 maybe_fst in
                    FStar_Errors.Err uu____5350 in
                  FStar_Exn.raise uu____5349
                else ()) verify_flags;
       (by_target, topologically_sorted1, immediate_graph))
let print_make:
  (Prims.string,Prims.string Prims.list) FStar_Pervasives_Native.tuple2
    Prims.list -> Prims.unit
  =
  fun deps  ->
    FStar_List.iter
      (fun uu____5400  ->
         match uu____5400 with
         | (f,deps1) ->
             let deps2 =
               FStar_List.map (fun s  -> FStar_Util.replace_chars s 32 "\\ ")
                 deps1 in
             FStar_Util.print2 "%s: %s\n" f (FStar_String.concat " " deps2))
      deps
let print:
  'a 'b .
    ((Prims.string,Prims.string Prims.list) FStar_Pervasives_Native.tuple2
       Prims.list,'a,(Prims.string Prims.list,'b)
                       FStar_Pervasives_Native.tuple2 FStar_Util.smap)
      FStar_Pervasives_Native.tuple3 -> Prims.unit
  =
  fun uu____5451  ->
    match uu____5451 with
    | (make_deps,uu____5475,graph) ->
        let uu____5509 = FStar_Options.dep () in
        (match uu____5509 with
         | FStar_Pervasives_Native.Some "make" -> print_make make_deps
         | FStar_Pervasives_Native.Some "graph" -> print_graph graph
         | FStar_Pervasives_Native.Some uu____5512 ->
             FStar_Exn.raise (FStar_Errors.Err "unknown tool for --dep\n")
         | FStar_Pervasives_Native.None  -> ())