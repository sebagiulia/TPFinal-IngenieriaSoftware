% Verification conditions for specslog.pl

% Run check_vcs_specslog to see if the program verifies all the VCs

:- notype_check.

:- consult('specslog.pl').

:- prolog_call((
    retractall(all_unsat_vc(_,_,_,_,_,_)),
    retractall(dinvariant(_,_,_)),
    retractall(daxiom(_,_,_)),
    (exists_file('specslog-all.pl') ->
       open('specslog-all.pl',read,StreamVC)
    ;
       print_notfile('specslog-all.pl')
    ),
    style_check(-singleton),
    setlog:consult_vc(StreamVC),
    style_check(+singleton),
    close(StreamVC))).

% Change this number for a different timeout (ms)
def_to(60000).

:- prolog_call(nb_setval(vc_num,0)).
:- prolog_call(nb_setval(vc_ok,0)).
:- prolog_call(nb_setval(vc_err,0)).
:- prolog_call(nb_setval(vc_to,0)).
:- prolog_call(nb_setval(vc_time,0)).

:- prolog_call(dynamic(unsat_sol/6)).
:- prolog_call(dynamic(vc_proved/1)).

sistemaInit_sat_invSistemaPs :-
  sistemaInit(Prim,Ps,Suscritos) &
  invSistemaPs(Ps).

sistemaInit_sat_inv1 :-
  sistemaInit(Prim,Ps,Suscritos) &
  inv1(Ps,Suscritos).

sistemaInit_sat_inv2 :-
  sistemaInit(Prim,Ps,Suscritos) &
  inv2(Prim,Ps).

sistNuevoProc_is_sat :-
  sistNuevoProc(Prim,Ps,Suscritos,I_i,Rep_o,Prim_,Ps_,Suscritos_) & 
  delay([Prim,Ps,Suscritos] neq [Prim_,Ps_,Suscritos_],false).

sistNuevoProc_pi_invSistemaPs(Ps,Prim,Ps,Suscritos,I_i,Rep_o,Prim_,Ps_,Suscritos_) :-
  % here conjoin other ax/inv as hypotheses if necessary
  neg(
    invSistemaPs(Ps) &
    sistNuevoProc(Prim,Ps,Suscritos,I_i,Rep_o,Prim_,Ps_,Suscritos_) implies
    invSistemaPs(Ps_)
  ).

sistNuevoProc_pi_inv1(Ps,Suscritos,Prim,Ps,Suscritos,I_i,Rep_o,Prim_,Ps_,Suscritos_) :-
  % here conjoin other ax/inv as hypotheses if necessary
  neg(
    inv1(Ps,Suscritos) &
    sistNuevoProc(Prim,Ps,Suscritos,I_i,Rep_o,Prim_,Ps_,Suscritos_) implies
    inv1(Ps_,Suscritos_)
  ).

sistNuevoProc_pi_inv2(Prim,Ps,Prim,Ps,Suscritos,I_i,Rep_o,Prim_,Ps_,Suscritos_) :-
  % here conjoin other ax/inv as hypotheses if necessary
  neg(
    inv2(Prim,Ps) &
    sistNuevoProc(Prim,Ps,Suscritos,I_i,Rep_o,Prim_,Ps_,Suscritos_) implies
    inv2(Prim_,Ps_)
  ).

sistSuscProceso_is_sat :-
  sistSuscProceso(Prim,Ps,Suscritos,I_i,S_i,Rep_o,Prim_,Ps_,Suscritos_) & 
  delay([Prim,Ps,Suscritos] neq [Prim_,Ps_,Suscritos_],false).

sistSuscProceso_pi_invSistemaPs(Ps,Prim,Ps,Suscritos,I_i,S_i,Rep_o,Prim_,Ps_,Suscritos_) :-
  % here conjoin other ax/inv as hypotheses if necessary
  neg(
    invSistemaPs(Ps) &
    sistSuscProceso(Prim,Ps,Suscritos,I_i,S_i,Rep_o,Prim_,Ps_,Suscritos_) implies
    invSistemaPs(Ps_)
  ).

sistSuscProceso_pi_inv1(Ps,Suscritos,Prim,Ps,Suscritos,I_i,S_i,Rep_o,Prim_,Ps_,Suscritos_) :-
  % here conjoin other ax/inv as hypotheses if necessary
  neg(
    inv1(Ps,Suscritos) &
    sistSuscProceso(Prim,Ps,Suscritos,I_i,S_i,Rep_o,Prim_,Ps_,Suscritos_) implies
    inv1(Ps_,Suscritos_)
  ).

sistSuscProceso_pi_inv2(Prim,Ps,Prim,Ps,Suscritos,I_i,S_i,Rep_o,Prim_,Ps_,Suscritos_) :-
  % here conjoin other ax/inv as hypotheses if necessary
  neg(
    inv2(Prim,Ps) &
    sistSuscProceso(Prim,Ps,Suscritos,I_i,S_i,Rep_o,Prim_,Ps_,Suscritos_) implies
    inv2(Prim_,Ps_)
  ).

sistActivate_is_sat :-
  sistActivate(Prim,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o) & 
  delay([Prim,Ps,Suscritos] neq [Prim_,Ps_,Suscritos_],false).

sistActivate_pi_invSistemaPs(Ps,Prim,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o) :-
  % here conjoin other ax/inv as hypotheses if necessary
  neg(
    invSistemaPs(Ps) &
    sistActivate(Prim,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o) implies
    invSistemaPs(Ps_)
  ).

sistActivate_pi_inv1(Ps,Suscritos,Prim,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o) :-
  % here conjoin other ax/inv as hypotheses if necessary
  neg(
    inv1(Ps,Suscritos) &
    sistActivate(Prim,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o) implies
    inv1(Ps_,Suscritos_)
  ).

sistActivate_pi_inv2(Prim,Ps,Prim,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o) :-
  % here conjoin other ax/inv as hypotheses if necessary
  neg(
    inv2(Prim,Ps) &
    sistActivate(Prim,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o) implies
    inv2(Prim_,Ps_)
  ).

sistSuspend_is_sat :-
  sistSuspend(Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o) & 
  delay([Prim,Ps,Suscritos] neq [Prim_,Ps_,Suscritos_],false).

sistSuspend_pi_invSistemaPs(Ps,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o) :-
  % here conjoin other ax/inv as hypotheses if necessary
  neg(
    invSistemaPs(Ps) &
    sistSuspend(Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o) implies
    invSistemaPs(Ps_)
  ).

sistSuspend_pi_inv1(Ps,Suscritos,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o) :-
  % here conjoin other ax/inv as hypotheses if necessary
  neg(
    inv1(Ps,Suscritos) &
    sistSuspend(Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o) implies
    inv1(Ps_,Suscritos_)
  ).

sistSuspend_pi_inv2(Prim,Ps,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o) :-
  % here conjoin other ax/inv as hypotheses if necessary
  neg(
    inv2(Prim,Ps) &
    sistSuspend(Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o) implies
    inv2(Prim_,Ps_)
  ).

sistKillNow_is_sat :-
  sistKillNow(Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o) & 
  delay([Prim,Ps,Suscritos] neq [Prim_,Ps_,Suscritos_],false).

sistKillNow_pi_invSistemaPs(Ps,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o) :-
  % here conjoin other ax/inv as hypotheses if necessary
  neg(
    invSistemaPs(Ps) &
    sistKillNow(Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o) implies
    invSistemaPs(Ps_)
  ).

sistKillNow_pi_inv1(Ps,Suscritos,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o) :-
  % here conjoin other ax/inv as hypotheses if necessary
  neg(
    inv1(Ps,Suscritos) &
    sistKillNow(Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o) implies
    inv1(Ps_,Suscritos_)
  ).

sistKillNow_pi_inv2(Prim,Ps,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o) :-
  % here conjoin other ax/inv as hypotheses if necessary
  neg(
    inv2(Prim,Ps) &
    sistKillNow(Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o) implies
    inv2(Prim_,Ps_)
  ).

sistKill_is_sat :-
  sistKill(Prim,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o) & 
  delay([Prim,Ps,Suscritos] neq [Prim_,Ps_,Suscritos_],false).

sistKill_pi_invSistemaPs(Ps,Prim,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o) :-
  % here conjoin other ax/inv as hypotheses if necessary
  neg(
    invSistemaPs(Ps) &
    sistKill(Prim,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o) implies
    invSistemaPs(Ps_)
  ).

sistKill_pi_inv1(Ps,Suscritos,Prim,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o) :-
  % here conjoin other ax/inv as hypotheses if necessary
  neg(
    inv1(Ps,Suscritos) &
    sistKill(Prim,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o) implies
    inv1(Ps_,Suscritos_)
  ).

sistKill_pi_inv2(Prim,Ps,Prim,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o) :-
  % here conjoin other ax/inv as hypotheses if necessary
  neg(
    inv2(Prim,Ps) &
    sistKill(Prim,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o) implies
    inv2(Prim_,Ps_)
  ).

update_time(Tf,Ti) :-
  prolog_call(
    (nb_getval(vc_time,VCT),
     VCT_ is VCT + Tf - Ti,
     nb_setval(vc_time,VCT_)
    )
  ).

update_count(C) :-
  prolog_call(
    (nb_getval(C,VCN),
     VCN_ is VCN + 1,
     nb_setval(C,VCN_)
    )
  ).

check_sat_vc(VCID) :-
  prolog_call((setlog:vc_proved(VCID) -> R = proved ; R = unproved)) &
  (R == unproved &
   write('\nChecking ') & write(VCID) & write(' ... ') &
   update_count(vc_num) &
   ((prolog_call(setlog(VCID)) &
    update_count(vc_ok) &
    prolog_call(assertz(vc_proved(VCID))) &
    write_ok)!
    or
    update_count(vc_err) &
    write_err
   )
   or
   R == proved
  ).

check_unsat_vc(VCID,TO,Opt) :-
  prolog_call(
    (VCID =.. [H | _],
     (\+setlog:vc_proved(H) ->
        setlog:all_unsat_vc(H,T,ID,VC,Op,VN),
        copy_term([VC,VN],[VCC,VNC]),
        write('\nChecking '), write(H), write(' ... '), flush_output,
        setlog(update_count(vc_num)),
        get_time(Ti),
        rsetlog(VC,TO,Cons,Res,Opt),
        get_time(Tf)
     ;
        Res = proved
     )
    )
  ) &
  ((Res = failure)! &
    update_count(vc_ok) &
    update_time(Tf,Ti) &
    prolog_call((retractall(setlog:unsat_sol(_,H,_,_,_,_)),
                 assertz(vc_proved(H)))) &
    write_ok
  or
   (Res = timeout)! &
    update_count(vc_to) &
    write_to
  or
    (Res = proved)!
  or
    update_count(vc_err) &
    prolog_call((term_string(VCC,VCS,[variable_names(VNC)]),
                 rsetlog_str(VCS,VNC,TO,_,_,[groundsol]))) &
    prolog_call((retractall(setlog:unsat_sol(_,H,_,_,_,_)),
                 assertz(unsat_sol(T,H,ID,Cons,VN,VNC)))) &
    write_err
  ).

write_ok :-
  prolog_call(ansi_format([bold,fg(green)],'OK',[])).

write_to :-
  prolog_call(ansi_format([bold,fg(255,255,50)],'TIMEOUT',[])).

write_err :-
  prolog_call(ansi_format([bold,fg(red)],'ERROR',[])).

check_vcs_specslog :-
   def_to(TO) &
   prolog_call(setlog(check_aux(TO,[])!)).

check_vcs_specslog(Opt) :-
   def_to(TO) &
   prolog_call(setlog(check_aux(TO,Opt)!)).

check_vcs_specslog(TO,Opt) :-
   prolog_call(setlog(check_aux(TO,Opt)!)).

check_aux(TO,Opt) :-
  prolog_call(
    (retractall(unsat_sol(_,_,_,_,_,_)),
     nb_setval(vc_num,0),
     nb_setval(vc_time,0),
     nb_setval(vc_ok,0),
     nb_setval(vc_err,0),
     nb_setval(vc_to,0)
    )
  ) &
  check_sat_vc(sistemaInit_sat_invSistemaPs) &
  check_sat_vc(sistemaInit_sat_inv1) &
  check_sat_vc(sistemaInit_sat_inv2) &
  check_sat_vc(sistNuevoProc_is_sat) &
  check_sat_vc(sistSuscProceso_is_sat) &
  check_sat_vc(sistActivate_is_sat) &
  check_sat_vc(sistSuspend_is_sat) &
  check_sat_vc(sistKillNow_is_sat) &
  check_sat_vc(sistKill_is_sat) &
  check_unsat_vc(sistNuevoProc_pi_invSistemaPs(Ps,Prim,Ps,Suscritos,I_i,Rep_o,Prim_,Ps_,Suscritos_),TO,Opt) &
  check_unsat_vc(sistNuevoProc_pi_inv1(Ps,Suscritos,Prim,Ps,Suscritos,I_i,Rep_o,Prim_,Ps_,Suscritos_),TO,Opt) &
  check_unsat_vc(sistNuevoProc_pi_inv2(Prim,Ps,Prim,Ps,Suscritos,I_i,Rep_o,Prim_,Ps_,Suscritos_),TO,Opt) &
  check_unsat_vc(sistSuscProceso_pi_invSistemaPs(Ps,Prim,Ps,Suscritos,I_i,S_i,Rep_o,Prim_,Ps_,Suscritos_),TO,Opt) &
  check_unsat_vc(sistSuscProceso_pi_inv1(Ps,Suscritos,Prim,Ps,Suscritos,I_i,S_i,Rep_o,Prim_,Ps_,Suscritos_),TO,Opt) &
  check_unsat_vc(sistSuscProceso_pi_inv2(Prim,Ps,Prim,Ps,Suscritos,I_i,S_i,Rep_o,Prim_,Ps_,Suscritos_),TO,Opt) &
  check_unsat_vc(sistActivate_pi_invSistemaPs(Ps,Prim,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o),TO,Opt) &
  check_unsat_vc(sistActivate_pi_inv1(Ps,Suscritos,Prim,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o),TO,Opt) &
  check_unsat_vc(sistActivate_pi_inv2(Prim,Ps,Prim,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o),TO,Opt) &
  check_unsat_vc(sistSuspend_pi_invSistemaPs(Ps,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o),TO,Opt) &
  check_unsat_vc(sistSuspend_pi_inv1(Ps,Suscritos,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o),TO,Opt) &
  check_unsat_vc(sistSuspend_pi_inv2(Prim,Ps,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o),TO,Opt) &
  check_unsat_vc(sistKillNow_pi_invSistemaPs(Ps,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o),TO,Opt) &
  check_unsat_vc(sistKillNow_pi_inv1(Ps,Suscritos,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o),TO,Opt) &
  check_unsat_vc(sistKillNow_pi_inv2(Prim,Ps,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o),TO,Opt) &
  check_unsat_vc(sistKill_pi_invSistemaPs(Ps,Prim,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o),TO,Opt) &
  check_unsat_vc(sistKill_pi_inv1(Ps,Suscritos,Prim,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o),TO,Opt) &
  check_unsat_vc(sistKill_pi_inv2(Prim,Ps,Prim,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o),TO,Opt) &
  prolog_call(
    (nb_getval(vc_num,VCN),
     nb_getval(vc_time,VCT),
     nb_getval(vc_ok,VCOK),
     nb_getval(vc_err,VCE),
     nb_getval(vc_to,VCTO)
    )
  ) &
  nl & nl &
  write("Total VCs: ") & write(VCN) &
  write(" (discharged: ") & write(VCOK) &
  write(", failed: ") & write(VCE) &
  write(", timeout: ") & write(VCTO) & write(")") & nl &
  write("Execution time (discharged): ") & write(VCT) & write(" s").

:- nl & prolog_call(ansi_format([bold,fg(green)],'Type checking has been deactivated.',[])) & nl & nl.

:- nl & prolog_call(ansi_format([bold,fg(green)],'Call check_vcs_specslog to run the verification conditions.',[])) & nl & nl.

