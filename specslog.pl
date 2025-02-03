variables([Prim, Ps, Suscritos]).

% definición de tipos.
def_type(estado, enum([activo, pasivo, muerto])).
def_type(ps, rel(pid, estado)).
def_type(senal, enum([activate, suspend, kill, killNow])).
def_type(suscritos, rel(pid, senal)).
def_type(msg, enum([ok, errProcExist, sinCambios, errProcNoExistente])).

% esquemas
% invaritante de Ps y Suscritos
invariant(invSistemaPs).
dec_p_type(invSistemaPs(ps)).
invSistemaPs(Ps):-
	pfun(Ps).

dec_p_type(n_invSistemaPs(ps)).
n_invSistemaPs(Ps):-
	neg(pfun(Ps)).


invariant(inv1).
dec_p_type(inv1(ps, suscritos)).
inv1(Ps, Suscritos):-
	dec([DomS, Dom], set(pid))
	& dom(Suscritos, DomS)
	& dom(Ps, Dom)
	& subset(DomS,Dom).

dec_p_type(n_inv1(ps, suscritos)).
% negacion de inv1
n_inv1(Ps, Suscritos):-
	neg(let([DomS, Dom], 
	 	dec([DomS, Dom], set(pid))
		& dom(Suscritos, DomS)
		& dom(Ps, Dom)
		, subset(DomS,Dom))).

invariant(inv2).
dec_p_type(inv2(pid, ps)).
inv2(Prim, Ps):- 
		dec(PsA, ps)
		& dec([D,U], set(pid))
		& rres(Ps, {activo}, PsA)
		& dom(PsA, D)
		& un(D, {pid:idle}, U)
		& Prim in U.

dec_p_type(n_inv2(pid, ps)).
% negacion de inv2
n_inv2(Prim, Ps):-
	neg(let([PsA, D, U], 
	 	dec(PsA, ps)
		& dec([D,U], set(pid))
		& rres(Ps, {activo}, PsA)
		& dom(PsA, D)
		& un(D, {pid:idle}, U)
		, Prim in U)).

% estado inicial del sistema.
initial(sistemaInit).
dec_p_type(sistemaInit(pid, ps, suscritos)).
sistemaInit(Prim, Ps, Suscritos) :-
	Prim = pid:idle &
	Ps = {} &
	Suscritos = {}.

% creación de un proceso en el sistema.
dec_p_type(sistNuevoProcOK(pid, ps, suscritos, pid, msg, pid, ps, suscritos)).
sistNuevoProcOK(Prim, Ps, Suscritos, I_i, Rep_o, Prim_, Ps_, Suscritos_):-
	  dec(D, set(pid))
	& dom(Ps, D)
	& I_i nin D
	& Prim_ = Prim
	& un(Ps, {[I_i, pasivo]}, Ps_)
	& Suscritos_ = Suscritos
	& Rep_o = ok.

% proceso existente en el sistema.
dec_p_type(sistNuevoProcERR(pid, ps, suscritos, pid, msg, pid, ps, suscritos)).
sistNuevoProcERR(Prim, Ps, Suscritos, I_i, Rep_o, Prim_, Ps_, Suscritos_):-
	  dec(D, set(pid))
	& dom(Ps, D)
	& I_i in D
	& Prim_ = Prim
	& Ps_ = Ps
	& Suscritos_ = Suscritos
	& Rep_o = errProcExist.

operation(sistNuevoProc).
dec_p_type(sistNuevoProc(pid, ps, suscritos, pid, msg, pid, ps, suscritos)).
sistNuevoProc(Prim, Ps, Suscritos, I_i, Rep_o, Prim_, Ps_, Suscritos_):-
	sistNuevoProcOK(Prim, Ps, Suscritos, I_i, Rep_o, Prim_, Ps_, Suscritos_)
	or
	sistNuevoProcERR(Prim, Ps, Suscritos, I_i, Rep_o, Prim_, Ps_, Suscritos_).



% suscribir un proceso a una señal.
dec_p_type(sistSuscProcesoOK(pid, ps, suscritos, pid, senal, msg, pid, ps, suscritos)).
sistSuscProcesoOK(Prim, Ps, Suscritos, I_i, S_i, Rep_o, Prim_, Ps_, Suscritos_):-
	  dec(D, set(pid))
	& dom(Ps, D)
	& I_i in D
	& Prim_ = Prim
	& Ps_ = Ps
	& un(Suscritos,{[I_i,S_i]},Suscritos_)
    & Rep_o = ok.	

% proceso no existente en el sistema.
dec_p_type(sistProcNoExistenteERR(pid, ps, suscritos, pid, msg, pid, ps, suscritos)).
sistProcNoExistenteERR(Prim, Ps, Suscritos, I_i, Rep_o, Prim_, Ps_, Suscritos_):-
	  dec(D, set(pid))
	& dom(Ps, D)
	& I_i nin D
	& Prim_ = Prim
	& Ps_ = Ps
	& Suscritos_ = Suscritos
	& Rep_o = errProcNoExistente.

operation(sistSuscProceso).
dec_p_type(sistSuscProceso(pid, ps, suscritos, pid, senal, msg, pid, ps, suscritos)).
sistSuscProceso(Prim, Ps, Suscritos, I_i, S_i, Rep_o, Prim_, Ps_, Suscritos_):-
	sistSuscProcesoOK(Prim, Ps, Suscritos, I_i, S_i, Rep_o, Prim_, Ps_, Suscritos_)
	or
	sistProcNoExistenteERR(Prim, Ps, Suscritos, I_i, Rep_o, Prim_, Ps_, Suscritos_).




% sistema recibe la señal Activate
% hay procesos a activar o activos cuando llega la señal.
dec_p_type(sistActivateOK(ps, suscritos, pid, ps, suscritos, msg)).
sistActivateOK(Ps, Suscritos,Prim_, Ps_, Suscritos_, Rep_o):-
	  dec([D, A, I], set(pid))
	& dec(P, ps)
	& dec(DA, suscritos)
	& rres(Suscritos,{activate}, DA)
	& dom(DA, A)
	& rres(Ps, {pasivo}, P)
	& dom(P, D)
	& inters(A, D, I)
	& neq(I,{})
	& Suscritos_ = Suscritos
	& oplus(Ps, cp(I,{activo}),Ps_)
	& Prim_ in I
	& Rep_o = ok.

% no hay procesos a activar cuando llega la señal.
dec_p_type(sistActivateSC(pid, ps, suscritos, pid, ps, suscritos, msg)).
sistActivateSC(Prim, Ps, Suscritos,Prim_, Ps_, Suscritos_, Rep_o):-
	dec([D, A, I], set(pid))
	& dec(P, ps)
	& dec(DA, suscritos)
	& rres(Suscritos,{activate}, DA)
	& dom(DA, A)
	& rres(Ps, {pasivo}, P)
	& dom(P, D)
	& inters(A, D, I)
	& I = {}
	& Suscritos_ = Suscritos
	& Ps_ = Ps
	& Prim_ = Prim
	& Rep_o = ok.

operation(sistActivate).
dec_p_type(sistActivate(pid, ps, suscritos, pid, ps, suscritos, msg)).
sistActivate(Prim, Ps, Suscritos, Prim_, Ps_, Suscritos_, Rep_o):-
	sistActivateOK(Ps, Suscritos, Prim_, Ps_, Suscritos_, Rep_o)
	or
	sistActivateSC(Prim, Ps, Suscritos, Prim_, Ps_, Suscritos_, Rep_o).


% sistema recibe la señal Suspend.
% quedan procesos activos luego de que se procese la señal.
dec_p_type(sistSuspendOK(ps, suscritos, pid, ps, suscritos, msg)).
sistSuspendOK(Ps, Suscritos, Prim_, Ps_, Suscritos_, Rep_o):-
	dec([S, D, Dif, I], set(pid))
	& dec(A, ps)
	& dec(DS, suscritos)
	& rres(Ps, {activo}, A)
	& rres(Suscritos,{suspend}, DS)
	& dom(DS, S)
	& dom(A, D)
	& diff(D, S, Dif)
	& Dif neq {}
	& Suscritos_ = Suscritos
	& inters(S, D, I)
	& oplus(Ps, cp(I,{pasivo}),Ps_)
	& Prim_ in Dif
	& Rep_o = ok.

% no quedan procesos activos cuando luego de procesar la señal.
dec_p_type(sistSuspendIdle(ps, suscritos, pid, ps, suscritos, msg)).
sistSuspendIdle(Ps, Suscritos, Prim_, Ps_, Suscritos_, Rep_o):-
	dec([S, D, Dif], set(pid))
	& dec(A, ps)
	& dec(DS, suscritos)
    & rres(Ps, {activo}, A)
	& rres(Suscritos,{suspend}, DS)
	& dom(DS, S)
	& dom(A, D)
	& diff(D, S, Dif)
	& Dif = {}
	& Suscritos_ = Suscritos
	& oplus(Ps, cp(D,{pasivo}),Ps_)
	& Prim_ = pid:idle
	& Rep_o = ok.

operation(sistSuspend).
dec_p_type(sistSuspend(ps, suscritos, pid, ps, suscritos, msg)).
sistSuspend(Ps, Suscritos, Prim_, Ps_, Suscritos_, Rep_o):-
	sistSuspendOK(Ps, Suscritos, Prim_, Ps_, Suscritos_, Rep_o)
	or
	sistSuspendIdle(Ps, Suscritos,Prim_, Ps_, Suscritos_, Rep_o).




% sistema recibe la señal KillNow.
% quedan procesos activos luego de procesar la señal.
dec_p_type(sistKillNowOK(ps, suscritos, pid, ps, suscritos, msg)).
sistKillNowOK(Ps, Suscritos, Prim_, Ps_, Suscritos_, Rep_o):-
	  dec([D, K, Dif, I], set(pid))
	& dec(A, ps)
	& rres(Ps, {activo}, A)
	& dec(DK, suscritos)
	& rres(Suscritos,{killNow}, DK)
	& dom(DK, K)
	& dom(A, D)
	& diff(D, K, Dif)
	& Dif neq {}
 	& Suscritos_ = Suscritos
	& inters(K, D, I)
	& oplus(Ps, cp(I,{muerto}),Ps_)
	& Prim_ in Dif
	& Rep_o = ok.

% no quedan procesos activos luego de procesar la señal.
dec_p_type(sistKillNowIdle(ps, suscritos, pid, ps, suscritos, msg)).
sistKillNowIdle(Ps, Suscritos, Prim_, Ps_, Suscritos_, Rep_o):-
	dec([D, K, Dif], set(pid))
	& dec(A, ps)
	& rres(Ps, {activo}, A)
	& dec(DK, suscritos)
	& rres(Suscritos,{killNow}, DK)
	& dom(DK, K)
	& dom(A, D)
	& diff(D, K, Dif)
	& Dif = {}
 	& Suscritos_ = Suscritos
	& oplus(Ps, cp(D,{muerto}),Ps_)
	& Prim_ = pid:idle
	& Rep_o = ok.

operation(sistKillNow).
dec_p_type(sistKillNow(ps, suscritos, pid, ps, suscritos, msg)).
sistKillNow(Ps, Suscritos, Prim_, Ps_, Suscritos_, Rep_o):-
	sistKillNowOK(Ps, Suscritos, Prim_, Ps_, Suscritos_, Rep_o)
	or
	sistKillNowIdle(Ps, Suscritos, Prim_, Ps_, Suscritos_, Rep_o).




% sistema recibe la señal Kill.
operation(sistKill).
dec_p_type(sistKill(pid, ps, suscritos, pid, ps, suscritos, msg)).
sistKill(Prim, Ps, Suscritos, Prim_, Ps_, Suscritos_, Rep_o):-
	  dec([D, K], set(pid))
	& dec([SP, SPasivos], ps)
	& dec(DK, suscritos)
	& rres(Suscritos,{kill}, DK)
	& dom(DK, K)
	& dres(K, Ps, SP)
	& rres(SP, {pasivo}, SPasivos)
	& dom(SPasivos, D)
 	& Suscritos_ = Suscritos
	& oplus(Ps, cp(D,{muerto}), Ps_)
	& Prim_ = Prim
	& Rep_o = ok.

