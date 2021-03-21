%*******************************************************************************
%                                    AETOILE
%*******************************************************************************

/*
Rappels sur l'algorithme
 
- structures de donnees principales = 2 ensembles : P (etat pendants) et Q (etats clos)
- P est dedouble en 2 arbres binaires de recherche equilibres (AVL) : Pf et Pu
 
   Pf est l'ensemble des etats pendants (pending states), ordonnes selon
   f croissante (h croissante en cas d'egalite de f). Il permet de trouver
   rapidement le prochain etat a developper (celui qui a f(U) minimum).
   
   Pu est le meme ensemble mais ordonne lexicographiquement (selon la donnee de
   l'etat). Il permet de retrouver facilement n'importe quel etat pendant

   On gere les 2 ensembles de façon synchronisee : chaque fois qu'on modifie
   (ajout ou retrait d'un etat dans Pf) on fait la meme chose dans Pu.

   Q est l'ensemble des etats deja developpes. Comme Pu, il permet de retrouver
   facilement un etat par la donnee de sa situation.
   Q est modelise par un seul arbre binaire de recherche equilibre.

Predicat principal de l'algorithme :

   aetoile(Pf,Pu,Q)

   - reussit si Pf est vide ou bien contient un etat minimum terminal
   - sinon on prend un etat minimum U, on genere chaque successeur S et les valeurs g(S) et h(S)
	 et pour chacun
		si S appartient a Q, on l'oublie
		si S appartient a Ps (etat deja rencontre), on compare
			g(S)+h(S) avec la valeur deja calculee pour f(S)
			si g(S)+h(S) < f(S) on reclasse S dans Pf avec les nouvelles valeurs
				g et f 
			sinon on ne touche pas a Pf
		si S est entierement nouveau on l'insere dans Pf et dans Ps
	- appelle recursivement etoile avec les nouvelles valeurs NewPF, NewPs, NewQs

*/

%*******************************************************************************

:- ['avl.pl'].       % predicats pour gerer des arbres bin. de recherche   
:- ['taquin.pl'].    % predicats definissant le systeme a etudier

%*******************************************************************************

main :-
	% Initialisations 
	initial_state(I),
 	heuristique(I,H0),
	write("I = "), writeln(I),
	write("H = "), writeln(H0),
	% Création des AVL vide puis les initialiser
	empty(Pf0), empty(Pu0),empty(Q),
	insert([[H0,H0,0],I], Pf0, Pf),
	insert([I, [F0,H0,G0],nil,nil], Pu0, Pu),
	% lancement de Aetoile
	aetoile(Pf,Pu,Q).



%*******************************************************************************

% cas particulier 1 : Pf et Pu vides => pas de solution
aetoile(nil,nil,_) :-
	write('PAS de SOLUTION : L ETAT FINAL N EST PAS ATTEIGNABLE !').
% cas particulier 2 : Solution trouvé
aetoile(Pf,Pu,Q) :-
	suppress_min([E,U],Pf, _), % On supprime l element minimum de Pf ayant une valeur de F minimal et on le récupère
	suppress([U,[Ff,H,G],Pere,A], Pu, _), % On recupere son pere
	final_state(F),
	member(F, [E,U]), % On regarde si cet element est l etat final
	insert([U,E,Pere,A], Q, NewQ), % On insere [E,U] dans Q pour l affichage
	affiche_solution(NewQ,F).

% cas général
aetoile(Pf,Pu,Q) :-
	suppress_min([[F,H,G],U], Pf, Pf2), % On supprime l element minimum de Pf ayant une valeur de F minimal et on le récupère
	%write('Evaluation de '),writeln([[F,H,G],U]),
	suppress([U,[F,H,G],Pere,A], Pu, Pu2), % On supprime son noeud frere dans Pu
	expand([U,[F,H,G],Pere,A], Succs), % determination des noeuds successeur de l etat U et determination de F H et U 
	%write('Succs :'),writeln(Succs),
	loop_successors(Succs, Pf2, Pu2, Q, NewPf, NewPu), % On traite les successeurs
	insert([U,[F,H,G],Pere,A], Q, NewQ), % On insere le noeud developpe dans Q
	%write('\nPf : '),put_flat(NewPf),write('\nPu : '),put_flat(NewPu),write('\nQ : '),put_flat(NewQ),writeln('\n-------------'),
	aetoile(NewPf, NewPu, NewQ). 

affiche_solution(Q,nil). % condition d arret

affiche_solution(Q,Fils) :-
	belongs([Fils, _, Pere, A], Q),
	affiche_solution(Q, Pere),
	write(A), write(" : "),writeln(Fils).


expand([U,[_,_,G],Pere,A], Succs):-
	findall([Next,[NextF,NextH,NextG],U,Direc],
	(rule(Direc,Cout,U,Next),
	 NextG is G+Cout,
	 heuristique(Next,NextH),
	 NextF is NextG+NextH), 
	Succs). 

% test unitaire
:- initial_state(Ini),heuristique(Ini,H) % initial 
,rule(up,1,Ini,NextUp),heuristique(NextUp,H_up),F_up is H_up+1 % up
,rule(right,1,Ini,NextRight),heuristique(NextRight,H_right),F_right is H_right+1 % right 
,rule(left,1,Ini,NextLeft),heuristique(NextLeft,H_left),F_left is H_left+1 % left
,expand([Ini,[H,H,0],nil,nil],
     [[NextUp,[F_up,H_up,1],Ini,up],
	 [NextLeft,[F_left,H_left,1],Ini,left],
	 [NextRight,[F_right,H_right,1],Ini,right]]).

% Plus de successeurs => Condition d arret
loop_successors([], Pf, Pu, Q, Pf, Pu).

% Succ1 appartient à Q  => on passe au suivant
loop_successors([Succ1|NextSuccs], Pf, Pu, Q, New_Pf, New_Pu) :- 
	belongs(Succ1, Q),
	loop_successors(NextSuccs, Pf, Pu, Q, New_Pf, New_Pu).

% Succ1 appartient à Pu et l evaluation etait au moins aussi bonne => on passe au suivant
loop_successors([[U, [F,H,G], P, A]|NextSuccs], Pf, Pu, Q, New_Pf, New_Pu) :-
	belongs([U, [F2,H2,G2], _, _], Pu), 
	[F2,H2,G2] @=<[F,H,G], % Succ1 dans Pu à une meilleur ou egale evaluation
	%writeln('***Nouvelle eval moins bonne***'),
	loop_successors(NextSuccs, Pf, Pu, Q, New_Pf, New_Pu).

% Appartient à Pu mais evaluation moins bonne dans Pu => on 'update' Succs dans Pu et de Pf 
loop_successors([[U, [F,H,G], P, A]|NextSuccs], Pf, Pu, Q, New_Pf, New_Pu) :-
	belongs([U, [F2,H2,G2], _, _], Pu), 
	[F2,H2,G2] @> [F,H,G],
	%writeln('***Nouvelle eval meilleur***'),
	suppress([U, [F2,H2,G2], _, _], Pu, Pu1),
	insert([U, [F,H,G], P, A], Pu1, Pu2),
	suppress([[F2,H2,G2],U], Pf, Pf1),
	insert([[F,H,G],U], Pf1, Pf2),
	loop_successors(NextSuccs, Pf2, Pu2, Q, New_Pf, New_Pu).

% Succ1 est une nouvelle situation, on l insere dans Pu et Pf
loop_successors([[U, [F,H,G], P, A]|NextSuccs], Pf, Pu, Q, New_Pf, New_Pu) :-
	insert([U, [F,H,G], P, A], Pu, Pu1),
	insert([[F,H,G],U], Pf, Pf1),
	loop_successors(NextSuccs, Pf1, Pu1, Q, New_Pf, New_Pu).
	

	
