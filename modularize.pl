:- module(modularize, []).

:- use_module(library(prolog_source)).

:- initialization(main, main).

:- multifile user:message_hook/3.

die :- halt(2), !.
die :-
    current_prolog_flag(pid, Pid),
    format(string(Cmd), "kill -9 ~w", [Pid]),
    shell(Cmd),
    sleep(100000).

setup_message_hook :-
    asserta((user:message_hook(Msg, _Level, _Lines) :- thread_send_message(main, Msg))).

:- dynamic current_modularize_file/1.

search_for_definition(_Mod:Pred/Arity) :-
    %using dumb text search because at this point we can't really trust any tools
    format(string(Search), "^~w", [Pred]),
    debug(loading_message, "Searching for ~w...", [Search]),
    run_grep(Search, Files),
    debug(loading_message, "FOUND PRED IN ~q~n", [Files]),
    memberchk(DefiningFile, Files), !,
    file_base_name(DefiningFile, DefiningBaseName),
    file_name_extension(DefModName, '.pl', DefiningBaseName),
    current_modularize_file(CurFile),
    debug(loading_message, "SO EXPORT ~q FROM ~w AND :- use_module(~w) IN ~w",
          [Pred/Arity, DefiningFile, DefModName, CurFile]),
    add_to_export(DefiningFile, Pred/Arity),
    add_use_if_needed(CurFile, DefModName).
search_for_definition(PredIndic) :-
    debug(loading_message, "Couldn't find ~q", [PredIndic]).

main([symbols, Path]) :-
    symbols_defined_in(Path, Symbols),
    forall( member(Sym, Symbols),
            format("~N~w,~n", [Sym])
    ).
main(_Argv) :-
    debug(loading_message),
    %debug(loading_message(other)),
    setup_message_hook,
    %directory_member('prolog', File, [ recursive(true), file_type(prolog) ]),
    member(File, ['prolog/metta_lang/metta_ontology.pfc.pl']),
    % TODO: this should probably be a stack that we update with done/start loading
    retractall(current_modularize_file(_)),
    assertz(current_modularize_file(File)),
    format(user_error, "PROLOG FILE ~q~n", [File]),
    load_files([File], [ must_be_module(true), silent ]),
    message_queue_property(main, size(Size)),
    debug(loading_message, "Size for main queue ~w", [Size]),
    listen_for_messages,
    fail.
main(_) :-
    format(user_error, "done~n", []).

listen_for_messages :-
    thread_get_message(main, Msg, [timeout(3)]), !,
    once(handle_msg(Msg)),
    listen_for_messages.

handle_msg(error(existence_error(procedure, Pred), Ctx)) :-
    debug(loading_message, "UNKNOWN PRED ~k @ ~q~n", [Pred, Ctx]),
    ignore(search_for_definition(Pred)),
    die.
handle_msg(error(existence_error(source_sink, File), Ctx)) :-
    thread_send_message(main, "UNKNOWN FILE ~q @ ~q~n"-[File, Ctx]),
    die.
handle_msg(load_file(start(_, file(Module, File)))) :-
    debug(loading_message, "Start loading ~w from ~q", [Module, File]).
handle_msg(load_file(done(_, file(Module, _File), _, _, _, _))) :-
    debug(loading_message, "Done loading ~w", [Module]).
handle_msg(Msg) :-
    debug(loading_message(other), "MESSAGE ~q~n", [Msg]),
    true.

add_to_export(Path, PredIndicator) :-
    debug(loading_message, "ADDING ~q TO ~q", [PredIndicator, Path]),
    setup_call_cleanup(
        prolog_open_source(Path, Stream),
        ( repeat,
          prolog_read_source_term(Stream, Term, _Ex, [subterm_positions(SubTermPos),
                                                      syntax_errors(dec10)]),
          once(( Term = (:- module(Module, ExportList)) ; Term = end_of_file)), !,
          ( var(Module) -> throw(couldnt_find_module) ; true ),
          arg(1, SubTermPos, TermStart),
          arg(2, SubTermPos, TermEnd),
          debug(loading_message, "Found module term at ~w -> ~w", [TermStart, TermEnd]),
          insert_into_file(Path, TermStart, TermEnd, Module, ExportList, PredIndicator)
        ),
        prolog_close_source(Stream)).

insert_into_file(_Path, _Start, _End, Mod, OldExports, NewExport) :-
    member(NewExport, OldExports),
    debug(loading_message, "~q is already exported in ~w!", [NewExport, Mod]), !.
insert_into_file(Path, Start, End, Mod, OldExports, NewExport) :-
    debug(loading_message, "Adding to ~w to exports in ~w", [NewExport, Path]),
    read_file_to_string(Path, FileContents, []),
    formatted_module(Mod, [NewExport|OldExports], ModuleString),
    sub_string(FileContents, 0, Start, After, Before),
    After0 is After - (End - Start),
    sub_string(FileContents, End, After0, _, Remainder),
    atomics_to_string([Before, ModuleString, Remainder], NewContentString),
    setup_call_cleanup(open(Path, write, S), format(S, "~s", NewContentString), close(S)).

formatted_module(Module, ExportList, Str) :-
    format(string(ModuleStart), ":- module(~w, [ ", [Module]),
    string_length(ModuleStart, IndentLen),
    maplist([Term, TermStr]>>format(string(TermStr), "~w", [Term]),
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

run_grep(Search, Files) :-
    setup_call_cleanup(
        process_create(path(rg), [ "-l", Search, "prolog" ], [ stdout(pipe(Out)) ]),
        read_lines(Out, Files),
        close(Out)).

read_lines(Out, Lines) :-
    read_line_to_string(Out, Line1),
    read_lines(Line1, Out, Lines).

read_lines(end_of_file, _, []) :- !.
read_lines(Line, Out, [Line|Lines]) :-
    read_line_to_string(Out, Line2),
    read_lines(Line2, Out, Lines).

symbols_defined_in(Path, Symbols) :-
    xref_source(Path),
    findall(
        Symbol,
        ( xref_defined(Path, Goal, local(_)),
          functor(Goal, Name, Arity),
          format(string(Symbol), "~w/~w", [Name, Arity]) ),
        Symbols0),
    sort(Symbols0, Symbols).
