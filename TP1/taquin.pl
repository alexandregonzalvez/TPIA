/* Fichier du probleme. 

Doit contenir au moins 4 predicats qui seront utilises par A*

   etat_initial(I)                                         % definit l'etat initial

   etat_final(F)                                           % definit l'etat final  

   rule(Rule_Name, Rule_Cost, Before_State, After_State)   % règles applicables

   heuristique(Current_State, Hval)				           % calcul de l'heuristique 


Les autres prédicats sont spécifiques au Taquin.
*/


%:- lib(listut).      % Laisser cette directive en commentaire si vous utilisez Swi-Prolog 
   
                      % Sinon décommentez la ligne si vous utilisez ECLiPSe Prolog :
                      % -> permet de disposer du predicat nth1(N, List, E)
                      % -> permet de disposer du predicat sumlist(List, S)
                      % (qui sont predefinis en Swi-Prolog)

                      
%***************************
%DESCRIPTION DU JEU DU TAKIN
%***************************

   %********************
   % ETAT INITIAL DU JEU
   %********************   
   % format :  initial_state(+State) ou State est une matrice (liste de listes)
   
/*
initial_state([ [b, h, c],       % C'EST L'EXEMPLE PRIS EN COURS
                [a, f, d],       % 
                [g,vide,e] ]).   % h1=4,   h2=5,   f*=5
*/
/*
initial_state([[a, vide,  c],
             [h,b, d],
             [g, f,  e]]).
*/

% AUTRES EXEMPLES POUR LES TESTS DE  A*
%initial_state([[c,d,g],[b,e,vide],[f,a,h]]  ).
%initial_state([[vide,d,g],[c,b,h],f,e,a]]  ).
/*
initial_state([ [ a, b, c],        
                [ g, h, d],
                [vide,f, e] ]). % h2=2, f*=2
*/
/*
initial_state([ [b, c, d],
                [a,vide,g],
                [f, h, e]  ]). % h2=10 f*=10
	*/
/*		
initial_state([ [f, g, a],
                [h,vide,b],
                [d, c, e]  ]). % h2=16, f*=20
		*/
/*	
initial_state([ [e, f, g],
                [d,vide,h],
                [c, b, a]  ]). % h2=24, f*=30 
*/
/*
initial_state([ [a, b, c],
                [g,vide,d],
                [h, f, e]]). % etat non connexe avec l'etat final (PAS DE SOLUTION)
*/  


   %******************
   % ETAT FINAL DU JEU
   %******************
   % format :  final_state(+State) ou State est une matrice (liste de listes)
  /* 
final_state([[a, b,  c],
             [h,vide, d],
             [g, f,  e]]).
*/
initial_state([[1,2,3,4],
               [5,6,7,8],
               [10,vide,11,12],
               [9,13,14,15]]).
final_state([[1,2,3,4],
               [5,6,7,8],
               [9,10,11,12],
               [13,14,15,vide]]).
   %********************
   % AFFICHAGE D'UN ETAT
   %********************
   % format :  write_state(?State) ou State est une liste de lignes a afficher

write_state([]).
write_state([Line|Rest]) :-
   writeln(Line),
   write_state(Rest).
   

%**********************************************
% REGLES DE DEPLACEMENT (up, down, left, right)             
%**********************************************
   % format :   rule(+Rule_Name, ?Rule_Cost, +Current_State, ?Next_State)
   
rule(up,   1, S1, S2) :-
   vertical_permutation(_X,vide,S1,S2).

rule(down, 1, S1, S2) :-
   vertical_permutation(vide,_X,S1,S2).

rule(left, 1, S1, S2) :-
   horizontal_permutation(_X,vide,S1,S2).

rule(right,1, S1, S2) :-
   horizontal_permutation(vide,_X,S1,S2).

   %***********************
   % Deplacement horizontal            
   %***********************
    % format :   horizontal_permutation(?Piece1,?Piece2,+Current_State, ?Next_State)
	
horizontal_permutation(X,Y,S1,S2) :-
   append(Above,[Line1|Rest], S1),
   exchange(X,Y,Line1,Line2),
   append(Above,[Line2|Rest], S2).

   %***********************************************
   % Echange de 2 objets consecutifs dans une liste             
   %***********************************************
   
exchange(X,Y,[X,Y|List], [Y,X|List]).
exchange(X,Y,[Z|List1],  [Z|List2] ):-
   exchange(X,Y,List1,List2).

   %*********************
   % Deplacement vertical            
   %*********************
   
vertical_permutation(X,Y,S1,S2) :-
   append(Above, [Line1,Line2|Below], S1), % decompose S1
   delete(N,X,Line1,Rest1),    % enleve X en position N a Line1,   donne Rest1
   delete(N,Y,Line2,Rest2),    % enleve Y en position N a Line2,   donne Rest2
   delete(N,Y,Line3,Rest1),    % insere Y en position N dans Rest1 donne Line3
   delete(N,X,Line4,Rest2),    % insere X en position N dans Rest2 donne Line4
   append(Above, [Line3,Line4|Below], S2). % recompose S2 

   %***********************************************************************
   % Retrait d'une occurrence X en position N dans une liste L (resultat R) 
   %***********************************************************************
   % use case 1 :   delete(?N,?X,+L,?R)
   % use case 2 :   delete(?N,?X,?L,+R)   
   
delete(1,X,[X|L], L).
delete(N,X,[Y|L], [Y|R]) :-
   delete(N1,X,L,R),
   N is N1 + 1.

   
   %*******************
   % PARTIE A COMPLETER
   %*******************
   

   %*******************************************************************
   % Coordonnees X(colonne),Y(Ligne) d'une piece P dans une situation U
   %*******************************************************************
	% format : coordonnees(?Coord, +Matrice, ?Element)
	% Définit la relation entre des coordonnees [Ligne, Colonne] et un element de la matrice
	/*
	Exemples
	
	?- coordonnees(Coord, [[a,b,c],[d,e,f]],  e).        % quelles sont les coordonnees de e ?
	Coord = [2,2]
	yes
	
	?- coordonnees([2,3], [[a,b,c],[d,e,f]],  P).        % qui a les coordonnees [2,3] ?
	P=f
	yes
	*/

	
coordonnees([L,C], Mat, Elt) :- 
       nth1(L,Mat,Ligne),
       nth1(C,Ligne, Elt).  

% tests unitaires
:- initial_state(Ini),coordonnees([1,1],Ini,b).
:- initial_state(Ini),coordonnees([2,1],Ini,a).
:- initial_state(Ini),coordonnees([3,3],Ini,e).
:- final_state(Fin),coordonnees([1,1],Fin,a).

											 
   %*************
   % HEURISTIQUES
   %*************
   
heuristique(U,H) :-
   heuristique1(U, H).  % au debut on utilise l'heuristique 1 
   %heuristique2(U, H).  % ensuite utilisez plutot l'heuristique 2  
   
   
   %****************
   %HEURISTIQUE no 1
   %****************
   % Nombre de pieces mal placees dans l'etat courant U
   % par rapport a l'etat final F
   
   
   % Suggestions : définir d'abord le prédicat coordonnees(Piece,Etat,Lig,Col) qui associe à une pièce présente dans Etat
   % ses coordonnees (Lig= numero de ligne, Col= numero de Colonne)
   
   % Definir ensuite le predicat malplace(P,U,F) qui est vrai si les coordonnes de P dans U et dans F sont differentes.
malplace(P,U,F):-
    coordonnees([L1,C1],U,P),
    coordonnees([L2,C2],F,P),
    [L1,C1]\=[L2,C2],
    P\=vide.
% tests unitaires
:- initial_state(Ini), final_state(Fin), not(malplace(c,Ini,Fin)).
:- initial_state(Ini), final_state(Fin), malplace(a,Ini,Fin).

   % On peut également comparer les pieces qui se trouvent aux mêmes coordonnees dans U et dans H et voir s'il sagit de la
   % même piece.
   
    % Definir enfin l'heuristique qui détermine toutes les pièces mal placées (voir prédicat findall) 
	% et les compte (voir prédicat length)


heuristique1(U,H) :- 
    final_state(F),
    findall(P,malplace(P,U,F),ListTOCount),
    length(ListTOCount,H).
%tests unitaires
:- initial_state(Ini), heuristique1(Ini,4). 
:- final_state(Fin), heuristique1(Fin,0). 
   
   %****************
   %HEURISTIQUE no 2
   %****************



   % Somme des distances de Manhattan à parcourir par chaque piece
   % entre sa position courante et sa positon dans l'etat final

dist_manhattan(P,U,F,D):-
    coordonnees([L1,C1],U,P),
    coordonnees([L2,C2],F,P),
    D is (abs(L1-L2)+abs(C1-C2)), 
    P\=vide.

%tests unitaires
:- initial_state(Ini), final_state(Fin), dist_manhattan(h,Ini,Fin,2).
:- initial_state(Ini), final_state(Fin), dist_manhattan(c,Ini,Fin,0).
:- initial_state(Ini), final_state(Fin), dist_manhattan(a,Ini,Fin,1).

heuristique2(U,H) :-
    final_state(F),
    findall(Cout,dist_manhattan(_,U,F,Cout),ListeCout),
    sumlist(ListeCout,H).	

% tests unitaires						
:- initial_state(Ini), heuristique2(Ini,5). 
:- final_state(Fin), heuristique2(Fin,0). 