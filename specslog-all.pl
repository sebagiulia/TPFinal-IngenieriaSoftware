dinvariant(invSistemaPs,invSistemaPs(Ps)).
dinvariant(inv1,inv1(Ps,Suscritos)).
dinvariant(inv2,inv2(Prim,Ps)).
all_unsat_vc(sistNuevoProc_pi_invSistemaPs,inv,invSistemaPs,sistNuevoProc_pi_invSistemaPs(Ps,Prim,Ps,Suscritos,I_i,Rep_o,Prim_,Ps_,Suscritos_),sistNuevoProc(Prim,Ps,Suscritos,I_i,Rep_o,Prim_,Ps_,Suscritos_)).
all_unsat_vc(sistNuevoProc_pi_inv1,inv,inv1,sistNuevoProc_pi_inv1(Ps,Suscritos,Prim,Ps,Suscritos,I_i,Rep_o,Prim_,Ps_,Suscritos_),sistNuevoProc(Prim,Ps,Suscritos,I_i,Rep_o,Prim_,Ps_,Suscritos_)).
all_unsat_vc(sistNuevoProc_pi_inv2,inv,inv2,sistNuevoProc_pi_inv2(Prim,Ps,Prim,Ps,Suscritos,I_i,Rep_o,Prim_,Ps_,Suscritos_),sistNuevoProc(Prim,Ps,Suscritos,I_i,Rep_o,Prim_,Ps_,Suscritos_)).
all_unsat_vc(sistSuscProceso_pi_invSistemaPs,inv,invSistemaPs,sistSuscProceso_pi_invSistemaPs(Ps,Prim,Ps,Suscritos,I_i,S_i,Rep_o,Prim_,Ps_,Suscritos_),sistSuscProceso(Prim,Ps,Suscritos,I_i,S_i,Rep_o,Prim_,Ps_,Suscritos_)).
all_unsat_vc(sistSuscProceso_pi_inv1,inv,inv1,sistSuscProceso_pi_inv1(Ps,Suscritos,Prim,Ps,Suscritos,I_i,S_i,Rep_o,Prim_,Ps_,Suscritos_),sistSuscProceso(Prim,Ps,Suscritos,I_i,S_i,Rep_o,Prim_,Ps_,Suscritos_)).
all_unsat_vc(sistSuscProceso_pi_inv2,inv,inv2,sistSuscProceso_pi_inv2(Prim,Ps,Prim,Ps,Suscritos,I_i,S_i,Rep_o,Prim_,Ps_,Suscritos_),sistSuscProceso(Prim,Ps,Suscritos,I_i,S_i,Rep_o,Prim_,Ps_,Suscritos_)).
all_unsat_vc(sistActivate_pi_invSistemaPs,inv,invSistemaPs,sistActivate_pi_invSistemaPs(Ps,Prim,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o),sistActivate(Prim,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o)).
all_unsat_vc(sistActivate_pi_inv1,inv,inv1,sistActivate_pi_inv1(Ps,Suscritos,Prim,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o),sistActivate(Prim,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o)).
all_unsat_vc(sistActivate_pi_inv2,inv,inv2,sistActivate_pi_inv2(Prim,Ps,Prim,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o),sistActivate(Prim,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o)).
all_unsat_vc(sistSuspend_pi_invSistemaPs,inv,invSistemaPs,sistSuspend_pi_invSistemaPs(Ps,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o),sistSuspend(Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o)).
all_unsat_vc(sistSuspend_pi_inv1,inv,inv1,sistSuspend_pi_inv1(Ps,Suscritos,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o),sistSuspend(Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o)).
all_unsat_vc(sistSuspend_pi_inv2,inv,inv2,sistSuspend_pi_inv2(Prim,Ps,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o),sistSuspend(Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o)).
all_unsat_vc(sistKillNow_pi_invSistemaPs,inv,invSistemaPs,sistKillNow_pi_invSistemaPs(Ps,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o),sistKillNow(Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o)).
all_unsat_vc(sistKillNow_pi_inv1,inv,inv1,sistKillNow_pi_inv1(Ps,Suscritos,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o),sistKillNow(Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o)).
all_unsat_vc(sistKillNow_pi_inv2,inv,inv2,sistKillNow_pi_inv2(Prim,Ps,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o),sistKillNow(Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o)).
all_unsat_vc(sistKill_pi_invSistemaPs,inv,invSistemaPs,sistKill_pi_invSistemaPs(Ps,Prim,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o),sistKill(Prim,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o)).
all_unsat_vc(sistKill_pi_inv1,inv,inv1,sistKill_pi_inv1(Ps,Suscritos,Prim,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o),sistKill(Prim,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o)).
all_unsat_vc(sistKill_pi_inv2,inv,inv2,sistKill_pi_inv2(Prim,Ps,Prim,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o),sistKill(Prim,Ps,Suscritos,Prim_,Ps_,Suscritos_,Rep_o)).
