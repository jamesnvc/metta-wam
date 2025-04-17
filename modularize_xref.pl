:- module(modularize_xref, []).

:- use_module(library(apply)).
:- use_module(library(apply_macros)).
:- use_module(library(readutil)).
:- use_module(library(lists)).
:- use_module(library(ordsets)).
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
    load_xrefs(DirPath, FileDefs),
    files_imported_exported(FileDefs, FileImports, FileExports),
    forall( member(file_exports(File, Exports), FileExports),
          add_to_export(File, Exports) ),
    once(
        setof(file_import(File, Module),
              Pred^FileImports^(
                  member(file_import(File, Pred, ImportFile), FileImports),
                  file_module(ImportFile, Module)
              ),
              UniqueFileImports)),
    forall( member(file_import(File, Module), UniqueFileImports),
          add_use_if_needed(File, Module) ).

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
    rb_map_kv(Mapping0,find_source_for, Mapping1).

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
% Adding imports & exports
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
add_use_if_needed(Path, Module) :-
    debug(loading_message, "ADDING USE FOR ~w IN ~w", [Module, Path]),
    LastModuleAt = acc(0),
    AlreadyImported = acc(false),
    setup_call_cleanup(
        prolog_open_source(Path, Stream),
        add_use_if_needed__(LastModuleAt, AlreadyImported, Stream, Module),
        prolog_close_source(Stream)),
    debug(loading_message, "FINISHED SEARCH", []),
    arg(1, AlreadyImported, false),
    arg(1, LastModuleAt, UseModuleEnd),
    debug(loading_message, "INSERTING AT ~w", [UseModuleEnd]),
    insert_use_module(Path, Module, UseModuleEnd),
    debug(loading_message, "ADDED", []).

add_use_if_needed__(LastModuleAt, AlreadyImported, Stream, Module) :-
    repeat,
    prolog_read_source_term(Stream, Term, _Ex, [subterm_positions(SubTermPos),
                                                syntax_errors(dec10)]),
    once(( Term = (:- use_module(ImpModule)) ;
               Term = (:- use_module(ImpModule, _)) ;
                   Term = (:- module(_, _)) ;
                       Term = end_of_file )),
    debug(loading_message, "FOUND TERM ~q", [Term]),
    ( Term = end_of_file
      *-> !
      ; ( Term = (:- module(_, _))
          *-> arg(2, SubTermPos, ModuleEndAt0),
              succ(ModuleEndAt0, ModuleEndAt), % skip the period at the end
              nb_setarg(1, LastModuleAt, ModuleEndAt),
              fail
          ; (  ImpModule = Module
               *-> debug(loading_message, "Already imported", []),
                   nb_setarg(1, AlreadyImported, true), !
               ;  arg(2, SubTermPos, ModuleEndAt0),
                  succ(ModuleEndAt0, ModuleEndAt), % skip the period at the end
                  nb_setarg(1, LastModuleAt, ModuleEndAt),
                  fail  ) ) ).

insert_use_module(Path, ModuleName, UseEnd) :-
    format(string(UseModule), "~n:- use_module(~w).~n", [ModuleName]),
    read_file_to_string(Path, FileContent, []),
    sub_string(FileContent, 0, UseEnd, After, Before),
    sub_string(FileContent, UseEnd, After, _, AfterContent),
    atomics_to_string([Before, UseModule, AfterContent], NewContentString),
    setup_call_cleanup(open(Path, write, S), format(S, "~s", NewContentString), close(S)).


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
% red-black tree helper
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% like rb_map/3, but call with key as well as value

:- meta_predicate rb_map_kv(+, 3, -).

rb_map_kv(t(Nil,Tree),Goal,NewTree2) =>
    NewTree2 = t(Nil,NewTree),
    map_kv(Tree,Goal,NewTree,Nil).

map_kv(black('',_,_,''),_,Nil0,Nil) => Nil0 = Nil.
map_kv(red(L,K,V,R),Goal,NewTree,Nil) =>
    NewTree = red(NL,K,NV,NR),
    call(Goal,K,V,NV),
    map_kv(L,Goal,NL,Nil),
    map_kv(R,Goal,NR,Nil).
map_kv(black(L,K,V,R),Goal,NewTree,Nil) =>
    NewTree = black(NL,K,NV,NR),
    call(Goal,K,V,NV),
    map_kv(L,Goal,NL,Nil),
    map_kv(R,Goal,NR,Nil).

:- meta_predicate map_kv(?, 3, ?, ?).
