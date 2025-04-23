:- dynamic user:file_search_path/2.
:- multifile user:file_search_path/2.

:- prolog_load_context(directory, Dir),
   ( user:file_search_path(metta, _)
   -> true
   ;  directory_file_path(Dir, metta_lang, MettaDir),
      asserta(user:file_search_path(metta, MettaDir)) ).
