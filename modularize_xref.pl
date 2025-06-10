:- module(modularize_xref, []).

:- use_module(library(apply)).
:- use_module(library(apply_macros)).
:- use_module(library(filesex)).
:- use_module(library(readutil)).
:- use_module(library(lists)).
:- use_module(library(ordsets)).
:- use_module(library(pairs)).
:- use_module(library(rbtrees)).
:- use_module(library(prolog_source)).
:- use_module(library(yall)).

:- initialization(main, main).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Main
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

main([DirPath]) :-
    debug(modularize_xref),
    add_modules_if_needed(DirPath),
    % load xref data
    load_xrefs(DirPath, FileDefs),
    % get mapping of imports & exports
    findall(File, member(file_def_call_ex(File, _, _, _), FileDefs), AllFiles),
    files_imported_exported(FileDefs, FileImports, FileExports),
    setof(file_import(File, Module, Predicates),
          ImportFile^( setof(Pred,
                             member(file_import(File, Pred, ImportFile), FileImports),
                             Predicates),
                       file_module(ImportFile, Module)
                     ),
          UniqueFileImports),
    maplist([File, File-OpPositions]>>defined_operators(File, OpPositions),
            AllFiles, FileDefinedOps),
    maplist([File-OpPoses, Mod-OpPoses]>>file_module(File, Mod), FileDefinedOps,
            ModuleDefinedOps),
    list_to_rbtree(ModuleDefinedOps, ModDefOps),
    forall( member(file_import(File, Module, Predicates), UniqueFileImports),
            ( add_use_if_needed(File, Module, Predicates),
              ( rb_lookup(Module, Ops, ModDefOps), Ops \= []
              -> pairs_keys_values(Ops, Os, _),
                 add_use_if_needed(File, Module, Os)
              ;  true ) ) ),
    forall( member(file_exports(File, Exports), FileExports),
            add_to_export(File, Exports) ),
    forall( member(File-DefOps, FileDefinedOps),
            export_defined_operators(File, DefOps) ),
    % Remove ensure_loaded/1 decls for things that are now use_module/1'd
    maplist(file_module, AllFiles, AllModules),
    forall(member(File, AllFiles),
           remove_ensure_loaded(File, AllModules)),
    add_all_missing_meta_preds(AllFiles).

add_all_missing_meta_preds(AllFiles) :-
    debug(modularize_xref, "Searching for missing meta_predicate_decls...", []),
    X = a(false),
    forall(member(File, AllFiles),
           ( xref_source(File),
             file_missing_meta_predicates(File, Missing),
             ( Missing = []
             -> true
             ;  nb_setarg(1, X, true),
               insert_meta_predicates(File, Missing),
               xref_source(File) ) )),
    arg(1, X, FoundSome),
    ( FoundSome = true
    -> add_all_missing_meta_preds(AllFiles)
    ;  true ).

% also convert top-level declaration calling of goals into initialization/2

files_imported_exported(FileDefs, FileImports, FileExports) :-
    definition_file_mapping(FileDefs, PredToDefFile),
    files_imported(FileDefs, PredToDefFile, FileImports0),
    sort(FileImports0, FileImports),
    files_exported(FileImports, FileExports).

files_exported(Imports, Exports) :-
    findall(file_exports(File, Defs),
            aggregate(set(Def),
                      Importer^member(file_import(Importer, Def, File), Imports),
                      Defs),
            Exports).

files_imported([], _, []).
files_imported([file_def_call_ex(File, _, Calls, _)|Rest], PredToDefFile, FileImports) :-
    findall(file_import(File, Call, ExporterFile),
            ( member(Call, Calls),
              rb_lookup(Call, ExporterFile, PredToDefFile) ),
            FileImports, ImportsTail),
    files_imported(Rest, PredToDefFile, ImportsTail).

:- dynamic definers_choice/2.

check_definitions(Mapping0, Mapping1) :-
    rb_map_kv(Mapping0, find_source_for, Mapping1).

find_source_for(_, [File], File) :- !.
find_source_for(_, File, File) :- atom(File), !.
find_source_for(_, Files, Choice) :-
    sort(Files, FilesS),
    definers_choice(FilesS, Choice), !.
find_source_for(Defn, Files, Choice) :-
    stream_property(user_input, tty(true)),
    length(Files, NChoices),
    sort(Files, Choices),
    numlist(1, NChoices, Nums),
    maplist([N, F, S]>>format(string(S), "~w. ~w", [N, F]), Nums, Files, ChoicesStrings),
    atomics_to_string(ChoicesStrings, "\n", ChoicesStr),
    repeat,
    format(user_output, "Predicate ~w is defined in~n~s~nWhich should export it: [1-~w]",
           [Defn, ChoicesStr, NChoices]),
    read_line_to_string(user_input, InputString),
    number_string(Number, InputString),
    integer(Number),
    between(1, NChoices, Number),
    nth1(Number, Choices, Choice), !,
    assertz(definers_choice(Choices, Choice)).
find_source_for(Defn, Files, Choice) :-
    debug(modularize_xref, "COULDN'T FIGURE OUT SOURCE FOR ~w ~w", [Defn, Files]),
    Files = [Choice|_].

definition_file_mapping(FileDefs, Mapping) :-
    rb_empty(Mapping0),
    foldl([file_def_call_ex(File, Defns, _, Exports), Tree0, Tree]>>
              ( add_definitions_to_mapping(File, Defns, Tree0, Tree1),
                add_exports_to_mapping(File, Exports, Tree1, Tree) ),
          FileDefs, Mapping0, Mapping1),
    check_definitions(Mapping1, Mapping).

add_exports_to_mapping(File, Exports, Mapping0, Mapping) :-
    foldl({File}/[Defn, T0, T1]>>rb_insert(T0, Defn, File, T1),
          Exports, Mapping0, Mapping).

add_definitions_to_mapping(File, Definitions, Mapping0, Mapping) :-
    foldl({File}/[Defn, T0, T1]>>
              ( rb_insert_new(T0, Defn, [File], T1)
              ->  true
              ; rb_apply(T0, Defn, maybe_add_definition(File), T1) ),
          Definitions, Mapping0, Mapping).

maybe_add_definition(File, OldVal, NewVal) :-
    is_list(OldVal), !, NewVal = [File|OldVal].
maybe_add_definition(_, V, V).

clear_xref :-
    forall(xref_current_source(Source), xref_clean(Source)).

load_xrefs(DirPath, FileDefs) :-
    clear_xref,
    findall(
        file_def_call_ex(File, Defns, Called, AlreadyExported),
        ( directory_member(DirPath, File, [ recursive(true), file_type(prolog) ]),
          file_base_name(File, BaseName),
          \+ ( atom_concat('_', _, BaseName) ),
          xref_source(File, [ silent(true), comments(ignore) ]),
          findall(Pred/Arity, ( xref_exported(File, Head),
                                functor(Head, Pred, Arity) ),
                  AlreadyExported),
          findall(Pred/Arity,
                  ( xref_defined(File, Defn, How),
                    How \= imported(_),
                    How \= multifile(_),
                    Defn \= ':'(_, _),
                    functor(Defn, Pred, Arity)
                  ),
                  Defns0),
          sort(Defns0, Defns),
          findall(Pred/Arity,
                  ( xref_called(File, Call, _By),
                    Call \= ':'(_, _),
                    functor(Call, Pred, Arity) ),
                  Called0),
          sort(Called0, Called1),
          ord_subtract(Called1, Defns, Called)
        ),
        FileDefs
    ).
add_modules_if_needed(DirPath) :-
    forall( directory_member(DirPath, File, [ recursive(true), file_type(prolog) ]),
            add_module_if_needed(File)
    ).

add_module_if_needed(File) :-
    file_base_name(File, Name),
    atom_concat("_", _, Name), !.
add_module_if_needed(File) :-
    setup_call_cleanup(open(File, read, S), read_term(S, Term, []), close(S)),
    Term = (:- module(_, _)), !.
add_module_if_needed(File) :-
    read_file_to_string(File, Content, []),
    file_module(File, Module),
    format(string(ModuleHeader), ":- module(~w, []).~n", [Module]),
    setup_call_cleanup(
        open(File, write, S),
        ( write(S, ModuleHeader), write(S, Content) ),
        close(S)).

file_module(Path, Module) :-
    file_base_name(Path, BaseName),
    file_name_extension(Module, '.pl', BaseName).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Find operator definitions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

defined_operators(Path, Ops) :-
    % deliberately not finding operators defined in module/2, since
    % those are already exported
    find_in_source(Path,
                   [Term, Dict, Result]>>
                       (
                           Term = (:- op(A, B, C)),
                           get_dict(subterm_positions, Dict, TermPos),
                           arg(1, TermPos, Start),
                           arg(2, TermPos, End0), End is End0 + 1, % period
                           Result = op(A, B, C)-position(Start, End)
                       ),
                   Ops).

export_defined_operators(_Path, []) :- !.
export_defined_operators(Path, OpPoses) :-
    pairs_keys_values(OpPoses, Ops, Positions),
    splice_out_terms_in_file(Path, Positions),
    add_to_export(Path, Ops).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Adding imports
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! add_use_if_needed(+Path:atom, +Module:atom, +Predicates:list(term)) is det.
add_use_if_needed(Path, Module, Predicates) :-
    LastModuleAt = acc(0),
    AlreadyImported = acc(false),
    setup_call_cleanup(
        prolog_open_source(Path, Stream),
        add_use_if_needed__(LastModuleAt, AlreadyImported, Stream, Path, Module, Predicates),
        prolog_close_source(Stream)),
    arg(1, AlreadyImported, false), !,
    arg(1, LastModuleAt, UseModuleEnd),
    insert_use_module(Path, Module, Predicates, UseModuleEnd).
add_use_if_needed(_, _, _).

add_use_if_needed__(LastModuleAt, AlreadyImported, Stream, Path, Module, Predicates) :-
    repeat,
    prolog_read_source_term(Stream, Term, _Ex, [subterm_positions(SubTermPos),
                                                syntax_errors(dec10)]),
    once(( Term = (:- use_module(ImpModule)) ;
           Term = (:- use_module(ImpModule, _)) ;
           Term = (:- ensure_loaded(_)) ;
           Term = (:- module(_, _)) ;
           Term = end_of_file )),
    ( Term = end_of_file
    -> !
    ; ( Term = (:- module(_, _))
      -> arg(2, SubTermPos, ModuleEndAt0),
         succ(ModuleEndAt0, ModuleEndAt), % skip the period at the end
         nb_setarg(1, LastModuleAt, ModuleEndAt),
         fail
      ; (  nonvar(ImpModule), ImpModule = Module
         -> debug(loading_message, "Already imported", []),
            arg(1, SubTermPos, ImportStart),
            arg(2, SubTermPos, ImportEnd0), ImportEnd is ImportEnd0 + 1, % to get the full-stop
            update_existing_use_module_if_needed(Term, t(ImportStart, ImportEnd), Path, Module, Predicates),
            nb_setarg(1, AlreadyImported, true), !
         ; arg(2, SubTermPos, ModuleEndAt0),
           succ(ModuleEndAt0, ModuleEndAt), % skip the period at the end
           nb_setarg(1, LastModuleAt, ModuleEndAt),
           fail  ) ) ).

% remove ensure_loaded/1

remove_ensure_loaded(Path, Modules) :-
    find_in_source(Path,
                   {Modules}/[Term, Dict, Result]>>
                       (
                           Term = (:- ensure_loaded(M)),
                           memberchk(M, Modules),
                           get_dict(subterm_positions, Dict, TermPos),
                           arg(1, TermPos, Start),
                           arg(2, TermPos, End0),
                           End is End0 + 1, % include full stop
                           Result = position(Start, End)
                       ),
                   Locations),
    splice_out_terms_in_file(Path, Locations).

splice_out_terms_in_file(Path, Positions) :-
    read_file_to_string(Path, FileContent, []),
    sort(1, @=<, Positions, Positions1),
    splice_out_term_in_file(Positions1, 0, FileContent, NewContents),
    atomics_to_string(NewContents, "", NewContent),
    setup_call_cleanup(open(Path, write, S), write(S, NewContent), close(S)).

splice_out_term_in_file([TermPos|TermPoses], Offset, ContentStr, NewContent0) :-
    arg(1, TermPos, Start), arg(2, TermPos, End),
    ReadLen is Start - Offset,
    sub_string(ContentStr, 0, ReadLen, _After0, BeforeS),
    AfterStart is End - Offset,
    NewContent0 = [BeforeS|NewContent1],
    sub_string(ContentStr, AfterStart, _, 0, AfterS),
    splice_out_term_in_file(TermPoses, End, AfterS, NewContent1).
splice_out_term_in_file([], _, Remainder, [Remainder]).

% TODO: also need to import operators

update_existing_use_module_if_needed((:- use_module(Module)), SubTermPos, Path, Module, Predicates) :- !,
    arg(1, SubTermPos, OldUseStart),
    arg(2, SubTermPos, OldUseEnd),
    format(string(UseStart), ":- use_module(~w, [ ", [Module]),
    string_length(UseStart, IndentLen),
    maplist([Term, TermStr]>>format(string(TermStr), "~q", [Term]),
            Predicates, Predicates1),
    add_indent_to_rest(IndentLen, Predicates1, Predicates2),
    atomics_to_string(Predicates2, ",\n", PredicatesListStr),
    ( OldUseStart =:= OldUseEnd -> MaybeNL = "\n" ; MaybeNL = "" ),
    format(string(UseModule), "~s~s~s ]).~s", [MaybeNL, UseStart, PredicatesListStr, MaybeNL]),
    read_file_to_string(Path, FileContent, []),
    sub_string(FileContent, 0, OldUseStart, After, Before),
    After1 is After - (OldUseEnd - OldUseStart),
    sub_string(FileContent, OldUseEnd, After1, _, AfterContent),
    atomics_to_string([Before, UseModule, AfterContent], NewContentString),
    setup_call_cleanup(open(Path, write, S), format(S, "~s", [NewContentString]), close(S)).
update_existing_use_module_if_needed((:- use_module(Module, ExistingImports)), SubTermPos, Path, Module, Predicates) :-
    sort(ExistingImports, ExistingImports0),
    sort(Predicates, Predicates0),
    \+ ord_subset(Predicates0, ExistingImports0), !,
    ord_union(Predicates0, ExistingImports0, NewImports),
    update_existing_use_module_if_needed((:- use_module(Module)), SubTermPos, Path, Module, NewImports).
update_existing_use_module_if_needed(_, _, _, _, _).


insert_use_module(Path, ModuleName, Predicates, UseEnd) :-
    update_existing_use_module_if_needed((:- use_module(ModuleName)), t(UseEnd, UseEnd), Path, ModuleName, Predicates).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Adding exports
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

add_to_export(Path, PredIndicators) :-
    debug(loading_message, "ADDING ~q TO ~q", [PredIndicators, Path]),
    setup_call_cleanup(
        prolog_open_source(Path, Stream),
        ( repeat,
          prolog_read_source_term(Stream, Term, _Ex, [subterm_positions(SubTermPos),
                                                      syntax_errors(dec10)]),
          once(( Term = (:- module(Module, ExportList)) ; Term = end_of_file )), !,
          ( var(Module) -> throw(couldnt_find_module) ; true ),
          arg(1, SubTermPos, TermStart),
          arg(2, SubTermPos, TermEnd),
          debug(loading_message, "Found module term at ~w -> ~w", [TermStart, TermEnd]),
          insert_export_into_file(Path, TermStart, TermEnd, Module, ExportList, PredIndicators)
        ),
        prolog_close_source(Stream)).

insert_export_into_file(Path, Start, End, Mod, OldExports, NewExports) :-
    sort(NewExports, NewExportsSorted),
    sort(OldExports, OldExportsSorted),
    ord_subtract(NewExportsSorted, OldExportsSorted, ToExport),
    debug(loading_message, "Adding to ~w to exports in ~w", [ToExport, Path]),
    read_file_to_string(Path, FileContents, []),
    append(ToExport, OldExports, Exports),
    formatted_module(Mod, Exports, ModuleString),
    sub_string(FileContents, 0, Start, After, Before),
    After0 is After - (End - Start),
    sub_string(FileContents, End, After0, _, Remainder),
    atomics_to_string([Before, ModuleString, Remainder], NewContentString),
    setup_call_cleanup(open(Path, write, S), format(S, "~s", NewContentString), close(S)).

formatted_module(Module, ExportList, Str) :-
    format(string(ModuleStart), ":- module(~w, [ ", [Module]),
    string_length(ModuleStart, IndentLen),
    maplist([Term, TermStr]>>format(string(TermStr), "~q", [Term]),
            ExportList, ExportList1),
    add_indent_to_rest(IndentLen, ExportList1, ExportList2),
    atomics_to_string(ExportList2, ",\n", ExportListStr),
    format(string(Str), "~s~s ])", [ModuleStart, ExportListStr]).

add_indent_to_rest(Indent, [L|Rest], [L|OutRest]) :-
    add_indent_to_rest_(Indent, Rest, OutRest).
add_indent_to_rest_(_Indent, [], []).
add_indent_to_rest_(Indent, [L|Rest], [L1|OutRest]) :-
    length(IndentCodes, Indent),
    maplist(=(0' ), IndentCodes),
    format(string(L1), "~s~s", [IndentCodes, L]),
    add_indent_to_rest_(Indent, Rest, OutRest).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Guessing missing meta_predicate/1
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

insert_meta_predicates(Path, PredPositions0) :-
    read_file_to_string(Path, FileContent, []),
    sort(2, @=<, PredPositions0, PredPositions),
    insert_meta_predicate(PredPositions, 0, FileContent, NewContents),
    atomics_to_string(NewContents, "", NewContent),
    setup_call_cleanup(open(Path, write, S), write(S, NewContent), close(S)).

insert_meta_predicate([meta_at(Pred, At)|MetaRest], Offset, ContentStr, NewContent) :-
    ReadLen is At - Offset,
    sub_string(ContentStr, 0, ReadLen, After, BeforeS),
    format(string(MetaDecl), "~n:- meta_predicate ~w.~n", [Pred]),
    NewContent = [BeforeS, MetaDecl|NewContentRest],
    sub_string(ContentStr, ReadLen, After, _, AfterS),
    insert_meta_predicate(MetaRest, At, AfterS, NewContentRest).
insert_meta_predicate([], _, Remainder, [Remainder]).

file_missing_meta_predicates(Path, Missing) :-
    find_in_source(Path,
                   {Path}/[_Term, Dict, Result]>>
                       (
                           get_dict(expanded_term, Dict, Term),
                           compound(Term), Term = ':-'(_Head, _Body),
                           check_needs_meta_predicate(Path, Term, MaybeMeta),
                           get_dict(term_position, Dict, TermPos),
                           stream_position_data(char_count, TermPos, InsertAt),
                           Result = meta_at(MaybeMeta, InsertAt)
                       ),
                   Missing).

check_needs_meta_predicate(Path, ':-'(Head, Body), MetaPred) :-
    \+ xref_meta(Path, Head, _),
    compound(Head),
    compound_name_arguments(Head, HeadName, Args),
    check_vars_meta_use(Path, Args, Body, ArgMetas),
    member(N, ArgMetas), integer(N),
    compound_name_arguments(MetaPred, HeadName, ArgMetas).

check_vars_meta_use(_, [], _, []).
check_vars_meta_use(Path, [V|Vs], Body, [Meta|MetaRest]) :-
    var(V),
    var_meta_use(Path, V, Body, Meta), !,
    check_vars_meta_use(Path, Vs, Body, MetaRest).
check_vars_meta_use(Path, [_|Vs], Body, ['?'|MetaRest]) :-
    check_vars_meta_use(Path, Vs, Body, MetaRest).

var_meta_use(Path, V, (G, Gs), Meta) =>
    ( var_meta_use(Path, V, G, Meta)
    -> true
    ;  var_meta_use(Path, V, Gs, Meta) ).
var_meta_use(_, V, G, Meta), var(G), V == G =>
    % top-level use
    Meta = 0.
var_meta_use(Path, V, (I -> T ; E), Meta) =>
    once(var_meta_use(Path, V, I, Meta) ;
         var_meta_use(Path, V, T, Meta) ;
         var_meta_use(Path, V, E, Meta)).
var_meta_use(Path, V, G, Meta) =>
    xref_meta(Path, G, GoalMeta),
    ( member(X, GoalMeta), X == V
    -> Meta = 0
    ; member(X+N, GoalMeta), X == V,
      Meta = N ).
var_meta_use(_, _, _, _) => fail.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% finding dependency loops
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- use_module(library(ugraphs)).

% graph of dependencies between modules
build_graph(FileImports, Graph) :-
    vertices_edges_to_ugraph([], [], G0),
    foldl([file_import(I, _, E), G, G1]>>
              (( I = E
               -> G1 = G
               ; add_edges(G, [I-E], G1) )),
          FileImports, G0, Graph).

% graph of dependencies between predicates
build_file_graph(File, Graph) :-
    xref_source(File),
    findall(edge(Goal, How, Called),
            ( xref_called(File, Called, Goal),
              xref_defined(File, Called, How),
              once(( How = local(_) ; How = imported(_) ))
            ),
            Graph).

xxy_build_deps(Graph) :-
    load_xrefs("prolog", FileDefs),
    files_imported_exported(FileDefs, FileImports, _FileExports),
    build_graph(FileImports, Graph).

find_loops_in_file_graph(Loops) :-
    xxy_build_deps(Graph),
    setof(Loop, loop_in_graph(Graph, Loop), Loops).

expand_graph_in_loop(Loop, LoopGraph) :-
    maplist([F, file_graph(AF, Graph)]>>( build_file_graph(F, Graph),
                                          absolute_file_name(F, AF) ),
            Loop, LoopSubGraphs),
    vertices_edges_to_ugraph([], [], EmptyGraph),
    foldl([file_graph(ThisFile, Edges), Graph0, Graph1]>>
              maybe_add_edges_to_graph(ThisFile, Edges, Graph0, Graph1),
          LoopSubGraphs,
          EmptyGraph,
          LoopGraph
    ).

head_pred('<directive>'(Line), '<directive>'(Line)) :- !.
head_pred(Head, Name/Arity) :-
    functor(Head, Name, Arity).

maybe_add_edges_to_graph(ThisFile, Edges, Graph0, Graph1) :-
    module_property(modularize_xref, file(ModularizeFile)),
    file_directory_name(ModularizeFile, MettaDir),
    foldl({ThisFile, MettaDir}/[edge(FromH, How, ToH), G0, G1]>>
              ( head_pred(FromH, From), head_pred(ToH, To),
                file_module(ThisFile, ThisModule),
                ( How = local(_)
                -> add_edges(G0, [(ThisModule:From)-(ThisModule:To)], G1)
                ;  ( How = imported(ImportFile), atom_concat(MettaDir, _, ImportFile)
                   -> file_module(ImportFile, ImportModule),
                      add_edges(G0, [(ThisModule:From)-(ImportModule:To)], G1)
                   ; G1 = G0 ) ) ),
          Edges, Graph0, Graph1).

cross_module_edges(Graph, CrossingEdges) :-
    findall(CrossingEdge,
            ( member(Vertex-Edges, Graph),
              Vertex = ThisModule:_Pred,
              include({ThisModule}/[CalledMod:_Called]>>( CalledMod \= ThisModule ),
                      Edges,
                      OtherModVertices),
              OtherModVertices = [_|_],
              CrossingEdge = Vertex-OtherModVertices
            ),
            CrossingEdges).

zzz_look_at_min_cuts :-
    find_loops_in_file_graph(Loops),
    Loops = [L|_],
    L = loop(_F, Loop),
    expand_graph_in_loop(Loop, LoopGraph),
    cross_module_edges(LoopGraph, Crossings),
    maplist({LoopGraph}/[V-Edges, Degree-(V-Edges)]>>
                ( neighbours(V, LoopGraph, Neighbours),
                  length(Neighbours, Degree) ),
            Crossings, LengthCrossings),
    findall(mod_preds_degree(Mod, Preds, TotalDegree),
            aggregate(r(sum(Degree), set(Pred)),
                      V^Edges^( member(Degree-(V-Edges), LengthCrossings),
                                V = Mod:Pred ),
                      r(TotalDegree, Preds)),
            ModPredsDegrees),
    sort(3, @=<, ModPredsDegrees, SortedModPredsDegree),
    forall(member(mod_preds_degree(Mod, Preds, TotalDegree), SortedModPredsDegree),
           ( length(Preds, NPreds), format(" ~w: ~q -> ~q~n", [TotalDegree, Mod, NPreds]),
             forall(member(Pred, Preds),
                    ( neighbors(Mod:Pred, LoopGraph, Neighbours),
                      format("     ~q -> ~q~n", [Pred, Neighbours]) ))
           )).

break_dependency_loop :-
    find_loops_in_file_graph(Loops0),
    maplist([loop(_, L), Len-L]>>length(L, Len), Loops0, Loops1),
    sort(1, @=<, Loops1, Loops),
    Loops = [_-Loop|_],
    debug(xxx, "LOOP FOUND ~q", [Loop]),
    expand_graph_in_loop(Loop, LoopGraph),
    maplist(file_module, Loop, ModLoop),
    % checking that there isn't a mutual recursion
    ( pred_graph_disjoint_path(ModLoop, LoopGraph, Path)
      % what what do if true?
    -> debug(xxx, "No disjoint path in graph, need to merge instead: ~q", [Path]),
       fail
    ; true ),
    pick_preds_to_extract(LoopGraph, ModLoop, Extract),
    transitive_closure(LoopGraph, Closure),
    Extract = module_size_preds(ExtractMod, _, ExtractPreds),
    findall(ToExtract,
            ( member(ExtractPred, ExtractPreds),
              ( ToExtract = ExtractMod:ExtractPred ;
                ( memberchk((ExtractMod:ExtractPred)-ExtractPredDeps, Closure),
                  member(ToExtract, ExtractPredDeps),
                  ToExtract = ExtractMod:_) )
            ),
            AllToExtract),
    findall(Module-Preds,
            setof(Pred,
                  ExtractMod^ExtractPredDeps^ExtractPred^(
                      member(ExtractPred, ExtractPreds),
                      member((ExtractMod:ExtractPred)-ExtractPredDeps, Closure),
                      member(Module:Pred, ExtractPredDeps),
                      Module \= ExtractMod
                  ),
                  Preds) ,
            AllToImport),
    ( append(_, [PrevMod, ExtractMod|_], ModLoop) -> true ; PrevMod = '???' ),
    format(user_output, "Loop from ~q -> ~q via ~q~n", [PrevMod, ExtractMod, ExtractPreds]),
    format(user_output, "Inline or extract? [i/e]: ", []),
    ( repeat,
      read_line_to_string(user_input, MethodInput),
      memberchk(MethodInput, ["i", "e"]), ! ),
    ( MethodInput = "e"
    -> break_loop_by_splitting(Loop, ExtractMod, ExtractPreds, AllToImport, AllToExtract)
    ; break_loop_by_inlining(Loop, PrevMod, ExtractMod, AllToImport, AllToExtract) ).

break_loop_by_inlining(Loop, PrevMod, ExtractMod, AllToImport, AllToExtract) :-
    once(( member(ThisModPath, Loop), file_module(ThisModPath, ExtractMod) )),
    once(( member(ParentModPath, Loop), file_module(ParentModPath, PrevMod) )),
    copy_predicates_into_caller(ParentModPath, ThisModPath, AllToExtract),
    % either also import AllToImport or inline those too?
    forall(member(Mod-Preds, AllToImport),
           add_use_if_needed(ParentModPath, Mod, Preds)).

break_loop_by_splitting(Loop, ExtractMod, ExtractPreds, AllToImport, AllToExtract) :-
    length(AllToExtract, NToExtract),
    % ask, then will need to follow the dependency chain for inlining?
    format(user_output, "Name for module to extract ~q:~q and its ~w dependencies to?: ",
           [ExtractMod, ExtractPreds, NToExtract]),
    read_line_to_string(user_input, NewModuleString),
    atom_string(NewModule, NewModuleString),
    once(( member(ThisModPath, Loop), file_module(ThisModPath, ExtractMod) )),
    file_directory_name(ThisModPath, ThisModDir),
    format(string(ExtractModPl), "~w.pl", [NewModule]),
    directory_file_path(ThisModDir, ExtractModPl, NewModulePath),
    maplist([_:Pred, Pred]>>true, AllToExtract, PredsToExtract),
    debug(xxx, "preds to extract ~q", [PredsToExtract]),
    move_predicates_to_new_module(ThisModPath, PredsToExtract, AllToImport, NewModulePath),
    % re-write other dependencies
    change_other_imports(ExtractMod, NewModule, PredsToExtract).

change_other_imports(OldModule, NewModule, ExtractedPreds) :-
    % TODO: pass in directory path
    forall(directory_member("prolog", File, [ recursive(true), file_type(prolog) ]),
           ( file_module(File, FileModule),
             ( FileModule = NewModule
             -> true
             ; change_imports(OldModule, NewModule, ExtractedPreds, File) ) )).

change_imports(OldModule, NewModule, ExtractedPreds, File) :-
    sort(ExtractedPreds, OrdExtractedPreds),
    find_in_source(
        File,
        {OldModule, OrdExtractedPreds}/[(:- use_module(OldModule, Imports)), Info, Info]>>(
            sort(Imports, SortedImports),
            ord_intersect(SortedImports, OrdExtractedPreds)
        ),
        Found),
    Found = [_|_], !,
    % thought was to just excise the position selectively, but we don't know where the commas are
    % and anyway we probably generated all this ourselves, so let's just rewrite the whole import
    %find_old_import_locations(OrdExtractedPreds, Found, Positions),
    %debug(xxx, "To change in ~q: ~q", [File, Positions]),
    rewrite_imports(File, NewModule, OrdExtractedPreds, Found),
    findall(UsedImport,
            ( member(Info, Found),
              get_dict(expanded_term, Info, (:- use_module(_, Imported))),
              member(UsedImport, Imported),
              ord_memberchk(UsedImport, OrdExtractedPreds) ),
            UsedImports
           ),
    add_use_if_needed(File, NewModule, UsedImports).
change_imports(_, _, _, _).

rewrite_imports(_, _, _, []).
rewrite_imports(File, NewModule, OrdExtractedPreds, [Info|Next]) :-
    get_dict(subterm_positions, Info, Position),
    arg(1, Position, UseStart),
    arg(2, Position, UseEnd0),
    % TODO: need to properly find the full-stop end position of the term
    UseEnd is UseEnd0 + 1,
    nb_setarg(2, Position, UseEnd),
    splice_out_terms_in_file(File, [Position]),
    get_dict(expanded_term, Info, (:- use_module(OldModule, OldImports))),
    sort(OldImports, OrderedOldImports),
    ord_subtract(OrderedOldImports, OrdExtractedPreds, RemovedImports),
    ( ( RemovedImports = [] ; forall(member(Imp, RemovedImports), Imp = op(_, _, _)) )
    -> true
    ; format(string(BeginImport), ":- use_module(~w, [ ", [OldModule]),
      string_length(BeginImport, IndentLength),
      length(IndentCodes, IndentLength),
      maplist(=(0' ), IndentCodes),
      read_file_to_string(File, FileContentsString, []),
      sub_string(FileContentsString, 0, UseStart, _After, BeforeContent),
      sub_string(FileContentsString, UseStart, _, 0, AfterContent),
      Contents = [BeforeContent, BeginImport|ContentsRest0],
      RemovedImports = [FirstImport|OtherImports],
      format(string(FirstImportString), "~q", [FirstImport]),
      ContentsRest0 = [FirstImportString|ContentsRest1],
      findall(ImportLine,
              ( member(Import, OtherImports),
                format(string(ImportLine), ",~n~s~q", [IndentCodes, Import]) ),
              ContentsRest1, ContentsRest2),
      ContentsRest2 = [" ]).\n\n", AfterContent],
      atomics_to_string(Contents, "", ContentsString),
      setup_call_cleanup(open(File, write, S), write(S, ContentsString), close(S)) ),
    rewrite_imports(File, NewModule, OrdExtractedPreds, Next).


find_old_import_locations(_, [], []).
find_old_import_locations(ToExtract, [Info|Next], PosTail) :-
    get_dict(expanded_term, Info, UseModuleTerm),
    get_dict(subterm_positions, Info, UseModuleDeclPositions),
    UseModuleTerm = (:- use_module(_, Imports)),
    arg(5, UseModuleDeclPositions, [UseModulePositions]),
    arg(5, UseModulePositions, [_, list_position(_, _, ImportListPositions, _)]),
    maplist([Import, Position, import_pos(Import, Position)]>>true,
            Imports, ImportListPositions, ImportPositions),
    findall(
        import_pos(Import, Position),
        ( member(import_pos(Import, Position), ImportPositions),
          ord_memberchk(Import, ToExtract) ),
        PosTail,
        NewTail
    ),
    find_old_import_locations(ToExtract, Next, NewTail).

pick_preds_to_extract(Graph, ModLoop, Extract) :-
    transitive_closure(Graph, Closure),
    % for each pair of adjacent modules in the ModLoop path
    % find the number of dependencies between those two modules
    % or the size of the transitive closure of the crosses between those two
    % minimize that
    ModLoop = [_|ModLoopRest],
    once(append(ModLoopButLast, [_], ModLoop)),
    maplist([A, B, A-B]>>true, ModLoopButLast, ModLoopRest, ModPairs),
    debug(xxx, "LOOP ~q", [ModLoop]),
    findall(
        module_size_preds(FromMod, Degree, Preds),
        ( aggregate(r(sum(Size), set(Pred)),
                  Deps^OtherPred^TC^ToMod^(
                      member(FromMod-ToMod, ModPairs),
                      member((FromMod:Pred)-Deps, Graph),
                      memberchk(ToMod:OtherPred, Deps),
                      memberchk((FromMod:Pred)-TC, Closure),
                      length(TC, Size)),
                  r(Degree, Preds)),
          forall(( member(Pred, Preds),
                   member(FromMod:Pred-TC, Closure),
                   member(TransDep, TC) ),
                 ( TransDep = TransDepMod:_,
                   select(FromMod, ModLoop, OtherModsInLoop),
                   (  memberchk(TransDepMod, OtherModsInLoop)
                   -> debug(xxx, "Pred goes into loop ~q: ~q", [Pred, TransDep]),
                      fail
                   ; true ) ))
        ),
        ExtractCandidates
    ),
    sort(2, @=<, ExtractCandidates, ExtractSorted),
    %% Extract = ExtractSorted.
    ExtractSorted = [Extract|_].

% if this fails, the predicates themselves don't loop.
% so we can just cut out some preds that cross the boundary
% so what's the smallest cut we can make to break the loop?
pred_graph_disjoint_path(ModuleLoopPath, LoopGraph, Path) :-
    cross_module_edges(LoopGraph, Crossings),
    transpose_ugraph(LoopGraph, Transposed),
    ModuleLoopPath = [FirstMod|_],
    member(StartVertex-Dependencies, Crossings),
    StartVertex = FirstMod:_,
    transitive_closure(Transposed, TransposeClosure),
    memberchk(StartVertex-DependedBy, TransposeClosure),
    setof(DependedByMod,
          Pred^member(DependedByMod:Pred, DependedBy),
          DependendByMods
         ),
    DependendByMods = [FirstMod], % or is it okay if other mods, not in the loop, depend?
    Path = [StartVertex|Next],
    transitive_closure(LoopGraph, Closure),
    pred_graph_path(LoopGraph, Closure, ModuleLoopPath, a([StartVertex]), Dependencies, Next-Next),
    loop_in_path(Path).

loop_in_path(Path) :-
    Path = [Mod:_|Rest],
    loop_in_path([], Mod, Rest).

loop_in_path(_Seen, _Current, []) :- !, fail.
loop_in_path(Seen, Current, [Current:_|Rest]) :-
    !, loop_in_path(Seen, Current, Rest).
loop_in_path(Seen, Current, [Mod:_|Rest]) :-
    Mod \= Current,
    ( member(Mod, Seen)
    -> true
    ;  loop_in_path([Current|Seen], Mod, Rest) ).

pred_graph_path(LoopGraph, Closure, ModulePath, VisitedTerm, Deps, Path-PathTail) :-
    member(NextVertex, Deps),
    VisitedTerm = a(Visited0),
    \+ member(NextVertex, Visited0),
    ord_add_element(Visited0, NextVertex, Visited1),
    nb_setarg(1, VisitedTerm, Visited1),
    ModulePath = [ThisModule,NextModule|RestModules],
    NextVertex = Mod:_,
    memberchk(Mod, [ThisModule, NextModule]),
    ( Mod = NextModule
    -> ModulePath1 = [NextModule|RestModules]
    ;  ModulePath1 = ModulePath ),
    PathTail = [NextVertex|NewTail],
    ( no_external_edges(Closure, NextVertex)
    -> NewTail = []
    ;  memberchk(NextVertex-NextDeps, LoopGraph),
      pred_graph_path(LoopGraph, Closure, ModulePath1, VisitedTerm, NextDeps, Path-NewTail) ).

no_external_edges(Closure, Vertex) :-
    memberchk(Vertex-TransitiveDeps, Closure),
    setof(DependencyMod,
          Pred^member(DependencyMod:Pred, TransitiveDeps),
          OtherModules),
    Vertex = ThisMod:_,
    % or is it okay if other non-loop mods, are here?
    OtherModules = [ThisMod].

zzz_find_predicate_call_loops(ExpandedLoops) :-
    find_loops_in_file_graph(Loops),
    Loops = [L|_],
    L = loop(_F, Loop),
    expand_graph_in_loop(Loop, LoopGraph),
    cross_module_edges(LoopGraph, Crossings),
    vertices_edges_to_ugraph([], Crossings, CrossingsGraph),
    findall(ExpandedLoop,
            loop_in_graph(CrossingsGraph, ExpandedLoop),
            ExpandedLoops).
% So if ExpandedLoops is [] (or remove the findall/3 and just see if it fails)
% then there isn't mutual recursion across modules, so it should be possible to insert a cut somewhere
% where best to insert it?

cut_graph(LoopGraph, ModuleToCut, NewModuleName) :-
    % so we have the graph, degree of the edges
    % now what?
    % we can find the module that has the lowest total degree
    % extract the edges that are in the graph, since those are the ones that are in question?
    % that is, the vertices that either connect to another module or are in the transitive closure of those
    %  do we want to only get the edges that go to a specific other module? I guess so, just those that are in the cycle?
    %  or any cycle, I guess? Hm.
    % above we're considering loops seperately. I guess we need to merge loops? maybe?
    % does it suffice to only count the edges that end in either this module or modules also in the loop?
    % or do we only care about how many internal callees, since we need to pull those out?
    %
    % How are we making sure this isn't just adding a new node into the loop?
    % want to write the predicates such that they don't have dependencies, or only depend on something that doesn't depend on it?
    % so...how can we assure that?
    % we can just pull out all the predicates that depend on "loop modules" & the internal ones they call, so that just imports the appropriate loop modules...but what if other modules depend on those predicates? Now we have a loop again.
    % do we need to merge predicates from multiple modules?
    write([LoopGraph, ModuleToCut, NewModuleName]).

%! copy_predicates_into_caller(+CallerModuleFile:atom, +CalleeModuleFile:atom, +PredIndicators:list(atom)) is det.
copy_predicates_into_caller(CallerModuleFile, CalleeModuleFile, PredIndicators) :-
   find_in_source(
        CalleeModuleFile,
        {PredIndicators}/[Term, Info, term_pos(Start, End)]>>
            ( ( Term = (Head :- _) ; Term = Head ; Term = (:- dynamic(Pred))),
              head_pred(Head, Pred),
              memberchk(Pred, PredIndicators),
              get_dict(subterm_positions, Info, Pos),
              arg(1, Pos, Start),
              get_dict(after_term_position, Info, AfterPos),
              stream_position_data(char_count, AfterPos, End)
            ),
        Found),
   read_file_to_string(CalleeModuleFile, CalleeModuleContent, []),
   maplist({CalleeModuleContent}/[term_pos(Start, End), PredContent]>>(
               Len is End - Start,
               sub_string(CalleeModuleContent, Start, Len, _, PredContent)
           ),
           Found, ExtractedPreds),
   setup_call_cleanup(open(CallerModuleFile, append, S),
                      ( seek(S, 0, eof, _),
                        forall(member(PredContent, ExtractedPreds),
                               format(S, "~n~s~n", [PredContent]))
                      ),
                      close(S)),
   % Remove import from caller
   file_module(CalleeModuleFile, CalleeModule),
   find_in_source(
       CallerModuleFile,
       {CalleeModule}/[(:- use_module(CalleeModule, Imports)), Info, Imports-Info]>>true,
       ModuleLocs),
   sort(PredIndicators, OrdPredIndicators),
   forall(member(Imports-Info, ModuleLocs),
          ( get_dict(subterm_positions, Info, Pos),
            arg(1, Pos, Start),
            get_dict(after_term_position, Info, AfterPos),
            stream_position_data(char_count, AfterPos, End),
            sort(Imports, OrdImports),
            ord_subtract(OrdImports, OrdPredIndicators, Remainder),
            splice_out_terms_in_file(CallerModuleFile, [p(Start, End)]),
            ( Remainder == []
            -> true
            ; add_use_if_needed(CallerModuleFile, CalleeModule, Remainder) ))).

move_predicates_to_new_module(OldModuleFile, PredIndicators, ImportModulePreds, NewModulePath) :-
    % find operators that should be moved over
    find_in_source(OldModuleFile,
                   [(:- module(_, Exports)), Info, Info-Exports]>>true,
                   [OldModuleInfo-OldModuleExports]),
    findall(op(A, B, C),
            ( member(op(A, B, C), OldModuleExports),
              memberchk(C/_, PredIndicators) ),
            OpsToExtract),
    % find locations of predicate definitions
    % TODO: also find dynamic/1 and table/1 declarations involving these?
    find_in_source(
        OldModuleFile,
        {PredIndicators}/[Term, Info, term_info(Term, Info)]>>
            ( ( Term = (Head :- _) ; Term = Head ; Term = (:- dynamic(Pred))),
              head_pred(Head, Pred),
              memberchk(Pred, PredIndicators) ),
        Found),
    maplist([term_info(_, Info), Pos]>>
            ( get_dict(subterm_positions, Info, Pos),
              get_dict(after_term_position, Info, AfterPos),
              stream_position_data(char_count, AfterPos, End),
              nb_setarg(2, Pos, End) ), % note that this changes =Found= too!
            Found, PositionsToExcise),
    % write new module by extracting definitions from old module
    read_file_to_string(OldModuleFile, OldFileContent, []),
    file_module(NewModulePath, NewModule),
    append(PredIndicators, OpsToExtract, NewModuleExports),
    setup_call_cleanup(
        open(NewModulePath, write, S),
        ( formatted_module(NewModule, NewModuleExports, ModuleStr),
          format(S, "~s.~n~n", [ModuleStr]),
          forall(member(Module-Imports, ImportModulePreds),
                 output_module_import(S, Module, Imports)),
          forall(member(term_info(_, Info), Found),
                 ( get_dict(subterm_positions, Info, SubPos),
                   arg(1, SubPos, TermStart),
                   arg(2, SubPos, TermEnd),
                   Len is TermEnd - TermStart,
                   sub_string(OldFileContent, TermStart, Len, _, Extracted),
                   write(S, Extracted),
                   write(S, "\n\n")
                 )),
          write(S, "\n")
        ),
        close(S)),
    % remove definitions & old exports from original file
    get_dict(subterm_positions, OldModuleInfo, OldModPositions),
    arg(1, OldModPositions, OldModStart),
    get_dict(after_term_position, OldModuleInfo, OldModAfterPos),
    stream_position_data(char_count, OldModAfterPos, OldModEnd),
    splice_out_terms_in_file(OldModuleFile, [p(OldModStart, OldModEnd)|PositionsToExcise]),
    % add new exports to old module
    read_file_to_string(OldModuleFile, OldModuleContent, []),
    file_module(OldModuleFile, OldModule),
    findall(Export,
            ( member(Export, OldModuleExports),
              \+ memberchk(Export, OpsToExtract),
              \+ memberchk(Export, PredIndicators) ),
            OldModuleNewExports),
    formatted_module(OldModule, OldModuleNewExports, OldModuleUpdatedExports),
    setup_call_cleanup(
        open(OldModuleFile, write, S1),
        ( write(S1, OldModuleUpdatedExports),
          write(S1, ".\n\n"),
          write(S1, OldModuleContent) ),
        close(S1)),
    % import exported into old module
    % TODO what to import? should do just what's needed
    append(PredIndicators, OpsToExtract, OldModuleNewImports),
    add_use_if_needed(OldModuleFile, NewModule, OldModuleNewImports).

output_module_import(Output, Module, ImportPreds) :-
    format(string(Begin), ":- use_module(~w, [ ", [Module]),
    string_length(Begin, ImportIndent),
    length(IndentCodes, ImportIndent),
    maplist(=(0' ), IndentCodes),
    format(Output, "~N~s", [Begin]),
    [FirstPred|RestPreds] = ImportPreds,
    format(Output, "~q", [FirstPred]),
    forall(member(ImportPred, RestPreds),
           format(Output, ",~n~s~q", [IndentCodes, ImportPred]) ),
    format(Output, " ]).~n~n", []).

zzz_make_graphs :-
    xxy_build_deps(Graph),
    forall(loop_in_graph(Graph, loop(_From, LoopF)),
           ( format(string(Cmd), "dot -Tpng -O ~w", [LoopF]),
             shell(Cmd) )).

graphviz_graph(Graph, FileName) :-
    setup_call_cleanup(
        open(FileName, write, S),
        ( format(S, "digraph {~n", []),
          forall( ( member(V1-Edges, Graph),
                    member(V2, Edges) ),
                  format(S, "\"~q\" -> \"~q\"~n", [V1, V2]) ),
          format(S, "}", [])
        ),
        close(S)
    ).

loop_in_graph(Graph, Loop) :-
    transitive_closure(Graph, Closure),
    member(FileName-Reachable, Closure),
    member(FileName, Reachable),
    %output_deps_graphviz(FileName, Graph, OutputFile),
    %Loop = loop(FileName, OutputFile).
    find_loop_path(Graph, FileName, FileName, [], a([]), PathR),
    reverse(PathR, LoopPath),
    Loop = loop(FileName, LoopPath).

output_deps_graphviz(FileName, Graph, OutputFile) :-
    file_module(FileName, Module),
    format(string(GraphFileName), "~w_deps_graph.dot", [Module]),
    setup_call_cleanup(
        open(GraphFileName, write, S),
        ( format(S, "digraph {~n", []),
          forall(find_loop_path(Graph, FileName, FileName, [], a([]), PathR),
                 ( reverse(Path, PathR),
                   output_path_loop(S, Path) )
          ),
          format(S, "}", [])
        ),
        close(S)
    ),
    absolute_file_name(GraphFileName, OutputFile).

output_path_loop(S, []) :- format(S, "~n", []).
output_path_loop(_, [_]) :- true.
output_path_loop(S, [X, Y|Rest]) :-
    file_module(X, XMod),
    file_module(Y, YMod),
    format(S, "~w -> ~w~n", [XMod, YMod]),
    output_path_loop(S, [Y|Rest]).

find_loop_path(Graph, From, To, Path0, _Visited, Path) :-
    neighbours(From, Graph, Neighbours),
    memberchk(To, Neighbours), !,
    Path = [To, From|Path0].
find_loop_path(Graph, From, To, Path0, Visited, Path) :-
    neighbours(From, Graph, Neighbours),
    member(Neigh, Neighbours),
    arg(1, Visited, AlreadySeen),
    \+ memberchk(Neigh, AlreadySeen),
    nb_setarg(1, Visited, [Neigh|AlreadySeen]),
    find_loop_path(Graph, Neigh, To, [From|Path0], Visited, Path).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% red-black tree helper
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% like rb_map/3, but call with key as well as value

:- meta_predicate rb_map_kv(+, 3, -).

rb_map_kv(t(Nil, Tree), Goal, NewTree2) =>
    NewTree2 = t(Nil, NewTree),
    map_kv(Tree, Goal, NewTree, Nil).

map_kv(black('', _, _, ''), _, Nil0, Nil) => Nil0 = Nil.
map_kv(red(L, K, V, R), Goal, NewTree, Nil) =>
    NewTree = red(NL, K, NV, NR),
    call(Goal, K, V, NV),
    map_kv(L, Goal, NL, Nil),
    map_kv(R, Goal, NR, Nil).
map_kv(black(L, K, V, R), Goal, NewTree, Nil) =>
    NewTree = black(NL, K, NV, NR),
    call(Goal, K, V, NV),
    map_kv(L, Goal, NL, Nil),
    map_kv(R, Goal, NR, Nil).

:- meta_predicate map_kv(?, 3, ?, ?).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% finding source locations helper
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- meta_predicate find_in_source(+, 3, -).

find_in_source(Path, Find, Results) :-
    Acc = a([]),
    setup_call_cleanup(
        prolog_open_source(Path, Stream),
        ( repeat,
          prolog_read_source_term(Stream, Term, ExTerm, [ term_position(TermPos),
                                                          comments(CommentPos),
                                                          subterm_positions(SubTermPos) ]),
          stream_property(Stream, position(AfterPos)),
          ( call(Find, Term, _{term_position: TermPos, subterm_positions: SubTermPos,
                               expanded_term: ExTerm, comments: CommentPos,
                               after_term_position: AfterPos},
                 ToInsert)
          -> arg(1, Acc, L), nb_setarg(1, Acc, [ToInsert|L])
          ; true ),
          Term = end_of_file, !
        ),
        prolog_close_source(Stream)),
    arg(1, Acc, Results).
