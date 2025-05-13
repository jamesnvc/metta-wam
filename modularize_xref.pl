:- module(modularize_xref, []).

:- use_module(library(apply)).
:- use_module(library(apply_macros)).
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
            export_defined_operators(File, DefOps)),
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

load_xrefs(DirPath, FileDefs) :-
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
                   [Term, Dict, Result]>>(
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
        ;  arg(2, SubTermPos, ModuleEndAt0),
           succ(ModuleEndAt0, ModuleEndAt), % skip the period at the end
           nb_setarg(1, LastModuleAt, ModuleEndAt),
           fail  ) ) ).

% remove ensure_loaded/1

remove_ensure_loaded(Path, Modules) :-
    find_in_source(Path,
                   {Modules}/[Term, Dict, Result]>>(
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
                   {Path}/[_Term, Dict, Result]>>(
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

build_graph(FileImports, Graph) :-
    vertices_edges_to_ugraph([], [], G0),
    foldl([file_import(I, _, E), G, G1]>>(
              ( I = E
              -> G1 = G
              ; add_edges(G, [I-E], G1) )
          ), FileImports, G0, Graph).

xxy_build_deps(Graph) :-
    load_xrefs("prolog", FileDefs),
    files_imported_exported(FileDefs, FileImports, _FileExports),
    build_graph(FileImports, Graph).

loop_in_graph(Graph, Loop) :-
    transitive_closure(Graph, Closure),
    member(FileName-Reachable, Closure),
    member(FileName, Reachable),
    output_deps_graphviz(FileName, Graph, OutputFile),
    Loop = loop(FileName, OutputFile).

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
                                                          subterm_positions(SubTermPos) ]),
          ( call(Find, Term, _{term_position: TermPos, subterm_positions: SubTermPos,
                               expanded_term: ExTerm},
                ToInsert)
          -> arg(1, Acc, L), nb_setarg(1, Acc, [ToInsert|L])
          ; true ),
          Term = end_of_file, !
        ),
        prolog_close_source(Stream)),
    arg(1, Acc, Results).
