:- module(mettalog, []).

:- ensure_loaded(metta_lang/metta_interp).
:- use_module(metta_interp, [ loon/1 ]).

:- initialization(loon(program),prolog).

