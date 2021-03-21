	/*********************************
	DESCRIPTION DU JEU DU TIC-TAC-TOE
	*********************************/

	/*
	Une situation est decrite par une matrice 3x3.
	Chaque case est soit un emplacement libre (Variable LIBRE), soit contient le symbole d'un des 2 joueurs (o ou x)

	Contrairement a la convention du tp precedent, pour modeliser une case libre
	dans une matrice on n'utilise pas une constante speciale (ex : nil, 'vide', 'libre','inoccupee' ...);
	On utilise plut�t un identificateur de variable, qui n'est pas unifiee (ex : X, A, ... ou _) .
	La situation initiale est une "matrice" 3x3 (liste de 3 listes de 3 termes chacune)
	o� chaque terme est une variable libre.	
	Chaque coup d'un des 2 joureurs consiste a donner une valeur (symbole x ou o) a une case libre de la grille
	et non a deplacer des symboles deja presents sur la grille.		
	
	Pour placer un symbole dans une grille S1, il suffit d'unifier une des variables encore libres de la matrice S1,
	soit en ecrivant directement Case=o ou Case=x, ou bien en accedant a cette case avec les predicats member, nth1, ...
	La grille S1 a change d'etat, mais on n'a pas besoin de 2 arguments representant la grille avant et apres le coup,
	un seul suffit.
	Ainsi si on joue un coup en S, S perd une variable libre, mais peut continuer a s'appeler S (on n'a pas besoin de la designer
	par un nouvel identificateur).
	*/

situation_initiale([ [_,_,_],
                     [_,_,_],
                     [_,_,_] ]).

joueur_initial(x).


	% Definition de la relation adversaire/2

adversaire(x,o).
adversaire(o,x).


	/****************************************************
	 DEFINIR ICI a l'aide du predicat ground/1 comment
	 reconnaitre une situation terminale dans laquelle il
	 n'y a aucun emplacement libre : aucun joueur ne peut
	 continuer a jouer (quel qu'il soit).
	 ****************************************************/

situation_terminale(_J, Etat) :-
    ground(Etat),!.

situation_terminale(J, Etat) :-
    alignement(Ali,Etat),
    alignement_gagnant(Ali,J),!.

situation_terminale(J, Etat) :-
    adversaire(Joueur,Adv),
    alignement(Ali,Etat),
    alignement_gagnant(Ali,Adv),!.

	/***************************
	DEFINITIONS D'UN ALIGNEMENT
	***************************/

alignement(L, Matrix) :- ligne(    L,Matrix).
alignement(C, Matrix) :- colonne(  C,Matrix).
alignement(D, Matrix) :- diagonale(D,Matrix).

	/********************************************
	 DEFINIR ICI chaque type d'alignement maximal 
 	 existant dans une matrice carree NxN.
	 ********************************************/
	
ligne(L,M) :-
    nth1(_,M,L).

% test unitaire
:- M = [[a,b,c],[d,e,f],[g,h,i]], D=[a,b,c], ligne(D,M).
:- M = [[a,b,c],[d,e,f],[g,h,i]], D=[d,e,f], ligne(D,M).
:- M = [[a,b,c],[d,e,f],[g,h,i]], D=[g,h,i], ligne(D,M).
:- M = [[a,b,c],[d,e,f],[g,h,i]], D=[a,h,i], not(ligne(D,M)).

colonne(C,M) :- 
    maplist(nth1(_),M,C).

:- M = [[a,b,c],[d,e,f],[g,h,i]], D=[a,d,g], colonne(D,M).
:- M = [[a,b,c],[d,e,f],[g,h,i]], D=[b,e,h], colonne(D,M).
:- M = [[a,b,c],[d,e,f],[g,h,i]], D=[c,f,i], colonne(D,M).
:- M = [[a,b,c],[d,e,f],[g,h,i]], D=[a,h,i], not(colonne(D,M)).

	/* Definition de la relation liant une diagonale D a la matrice M dans laquelle elle se trouve.
		il y en a 2 sortes de diagonales dans une matrice carree(https://fr.wikipedia.org/wiki/Diagonale) :
		- la premiere diagonale (principale)  : (A I)
		- la seconde diagonale                : (Z R)
		A . . . . . . . Z
		. \ . . . . . / .
		. . \ . . . / . .
		. . . \ . / . . .
		. . . . X . . .
		. . . / . \ . . . 
		. . / . . . \ . .
		. / . . . . . \ .
		R . . . . . . . I
	*/



diagonale(D, M) :- 
	premiere_diag(1,D,M).

diagonale(D,M) :-
    length(M,K),
	deuxieme_diag(K,D,M).

	
premiere_diag(_,[],[]).
premiere_diag(K,[E|D],[Ligne|M]) :-
	nth1(K,Ligne,E),
	K1 is K+1,
	premiere_diag(K1,D,M).

deuxieme_diag(0,[],[]).
deuxieme_diag(K,[E|D],[Ligne|M]) :- 
	nth1(K,Ligne,E),
	K1 is K-1,
	deuxieme_diag(K1,D,M).

:- M = [[a,b,c],[d,e,f],[g,h,i]], D=[a,e,i], diagonale(D,M).
:- M = [[a,b,c],[d,e,f],[g,h,i]], D=[c,e,g], diagonale(D,M).
:- M = [[a,b,c],[d,e,f],[g,h,i]], D=[a,e,g], not(diagonale(D,M)).
	/*****************************
	 DEFINITION D'UN ALIGNEMENT 
	 POSSIBLE POUR UN JOUEUR DONNE
	 *****************************/

possible([X|L], J) :- unifiable(X,J), possible(L,J).
possible(  [],  _).

	/* Attention 
	il faut juste verifier le caractere unifiable
	de chaque emplacement de la liste, mais il ne
	faut pas realiser l'unification.
	*/

% A FAIRE
unifiable(X,_) :- 
    var(X).
unifiable(X,J):-
    ground(X),
    ground(J),
    X=J.
unifiable(X,J):-
    ground(X),
    var(J).

% test unitaire
:- unifiable(X, o), var(X).
:- unifiable(o, J), var(J).
:- unifiable(x, x).
:- not(unifiable(o, x)).
	
	/**********************************
	 DEFINITION D'UN ALIGNEMENT GAGNANT
	 OU PERDANT POUR UN JOUEUR DONNE J
	 **********************************/
	/*
	Un alignement gagnant pour J est un alignement
possible pour J qui n'a aucun element encore libre.
	*/
	
	/*
	Remarque : le predicat ground(X) permet de verifier qu'un terme
	prolog quelconque ne contient aucune partie variable (libre).
	exemples :
		?- ground(Var).
		no
		?- ground([1,2]).
		yes
		?- ground(toto(nil)).
		yes
		?- ground( [1, toto(nil), foo(a,B,c)] ).
		no
	*/
		
	/* Un alignement perdant pour J est un alignement gagnant pour son adversaire. */

% A FAIRE

alignement_gagnant(Ali, J) :- 
    ground(Ali),
    findall(X,(member(X,Ali),X=J),Ali).

%test unitaire
:- alignement_gagnant([x,x,x],x).
:- not(alignement_gagnant([x,o,x],x)).
:- not(alignement_gagnant([_,x,x],x)).
:- not(alignement_gagnant([o,o,o],x)).
%:- alignement_gagnant([x,x,x],X).

alignement_perdant(Ali, J) :- 
    ground(Ali),
    findall(Ali,(member(X,Ali),X=J),[]).

%test unitaire
:- not(alignement_perdant([x,x,x],x)).

:- not(alignement_perdant([x,o,x],x)).
:- not(alignement_perdant([_,x,x],x)).
:- alignement_perdant([o,o,o],x).
%:- alignement_perdant([x,x,x],X).

	/* ****************************
	DEFINITION D'UN ETAT SUCCESSEUR
	****************************** */

	/* 
	Il faut definir quelle operation subit la matrice
	M representant l'Etat courant
	lorsqu'un joueur J joue en coordonnees [L,C]
	*/	

% A FAIRE
successeur(J, Etat,[L,C]) :- 
	nth1(L,Etat,Ligne), 
	nth1(C,Ligne,J).

	/**************************************
   	 EVALUATION HEURISTIQUE D'UNE SITUATION
  	 **************************************/

	/*
	1/ l'heuristique est +infini si la situation J est gagnante pour J
	2/ l'heuristique est -infini si la situation J est perdante pour J
	3/ sinon, on fait la difference entre :
	   le nombre d'alignements possibles pour J
	moins
 	   le nombre d'alignements possibles pour l'adversaire de J
*/


heuristique(J,Situation,H) :-		% cas 1
   H = 10000,				% grand nombre approximant +infini
   alignement(Alig,Situation),
   alignement_gagnant(Alig,J), !.
	
heuristique(J,Situation,H) :-		% cas 2
   H = -10000,				% grand nombre approximant -infini
   alignement(Alig,Situation),
   alignement_perdant(Alig,J), !.	


% on ne vient ici que si les cut precedents n'ont pas fonctionne,
% c-a-d si Situation n'est ni perdante ni gagnante.

% A FAIRE 					cas 3
heuristique(J,Situation,H) :-
    findall(Ali, (alignement(Ali,Situation),possible(Ali,J)),AliJ),
    adversaire(J,OJ),
	findall(Ali, (alignement(Ali,Situation),possible(Ali,OJ)),AliOJ),
    length(AliJ,A),length(AligOJ,B), H is (A-B).


% Situation initial  

:- situation_initiale(SI),joueur_initial(X),heuristique(X,SI,4).
:- situation_initiale(SI),joueur_initial(X),adversaire(X,O),heuristique(O,SI,-4).
:- joueur_initial(X),adversaire(X,O),heuristique(O,[[x,x,x],[x,o,x],[o,o,x]],-10000).

% Situation gagnante
:- joueur_initial(X),heuristique(X,[[x,x],[o,x]],+10000).
% Situation nulle
:- joueur_initial(X),heuristique(X,[[x,o,x],[x,x,o],[o,x,o]],0).

