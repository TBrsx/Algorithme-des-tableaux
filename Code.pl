%!! Penser à charger ABox et Tbox



%Démarrage du programme
programme :-
	premiere_etape(Tbox,Abi,Abr),
	deuxieme_etape(Abi,Abi1,Tbox),
	troisieme_etape(Abi1,Abr).

%Partie 1 - abi : ABox assertions de concept, abr : Abox assertions de roles

%Pour afficher pour tester la lecture
tbox(Tbox) :- findall((C,CG),(equiv(C,CG)),Tbox).
abi(Abi) :- findall((I,C),(inst(I,C)),Abi).
abr(Abr) :- findall((I,I2,R),(instR(I,I2,R)),Abr).
recup(X) :- findall((michelAnge,X),instR(michelAnge,X,aCree),X).

premiere_etape(Tbox,Abi,Abr):- tbox(Tbox),!,abi(Abi),!,abr(Abr),!.

	
% Partie 2
%====Fourni====
deuxieme_etape(Abi,Abi1,Tbox) :-
	saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox).

saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox) :-
	nl,write('Entrez le numero du type de proposition que vous voulez demontrer :'),nl,
	write('1 Une instance donnee appartient a un concept donne.'),nl,
	write("2 Deux concepts n'ont pas d'elements en commun(ils ont une intersection vide)."),nl, read(R), suite(R,Abi,Abi1,Tbox),!.
	
suite(1,Abi,Abi1,Tbox) :-
	write('Type 1 choisi !'),nl,acquisition_prop_type1(Abi,Abi1,Tbox),!.
suite(2,Abi,Abi1,Tbox) :-
	write('Type 1 choisi !'),nl,acquisition_prop_type2(Abi,Abi1,Tbox),!.
suite(_,Abi,Abi1,Tbox) :-
	nl,write('Cette reponse est incorrecte.'),nl,
	saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox).

%=============

%Définition du prédicat concept = correction sémantique
concept(C) :- setof(X,cnamea(X),L),member(C,L). %Concept atomique
concept(not(C)) :- concept(C). %Négation
concept(or(C1,C2)) :- concept(C1),concept(C2). %Ou
concept(and(C1,C2)) :- concept(C1),concept(C2). %Et
concept(some(R,C)) :- concept(C),setof(X,rname(X),L),member(R,L). %Existe
concept(all(R,C)) :- concept(C),setof(X,rname(X),L),member(R,L). %Tous
concept(Ccplx) :- setof(X,cnamena(X),L),member(Ccplx,L). %Concept non-atomique
concept(I,C) :- setof(X,iname(X),L),member(I,L),concept(C). %Instance



%Mise sous nnf
%====Fourni====
nnf(not(and(C1,C2)),or(NC1,NC2)):- nnf(not(C1),NC1),
nnf(not(C2),NC2),!.
nnf(not(or(C1,C2)),and(NC1,NC2)):- nnf(not(C1),NC1),
nnf(not(C2),NC2),!.
nnf(not(all(R,C)),some(R,NC)) :- nnf(not(C),NC),!.
nnf(not(some(R,C)),all(R,NC)):- nnf(not(C),NC),!.
nnf(not(not(X)),X):-!.
nnf(not(X),not(X)):-!.
nnf(and(C1,C2),and(NC1,NC2)):- nnf(C1,NC1),nnf(C2,NC2),!.
nnf(or(C1,C2),or(NC1,NC2)):- nnf(C1,NC1), nnf(C2,NC2),!.
nnf(some(R,C),some(R,NC)):- nnf(C,NC),!.
nnf(all(R,C),all(R,NC)) :- nnf(C,NC),!.
nnf(X,X).
%==============

%Décomplexifie récursivement les concepts donnés en entrée
decomplexe(C,X):- equiv(C,X). %Concept complexe
decomplexe(C,C) :- cnamea(C). %Concept atomique, pas besoin de décomplexer
decomplexe(or(C1,C2),X) :- X = or(Y,Z),decomplexe(C1,Y),decomplexe(C2,Z). %Ou
decomplexe(and(C1,C2),X) :- X = and(Y,Z),decomplexe(C1,Y),decomplexe(C2,Z). %And
decomplexe(some(R,C),X) :- X = some(R,Y),decomplexe(C,Y). %Existe
decomplexe(all(R,C),X) :- X = all(R,Y),decomplexe(C,Y). %Pour tout
decomplexe(not(C),X) :- X = not(Y), decomplexe(C,Y). % Non(Concept))


%Si on enlève une des deux lignes, ça ne fonctionne plus, prière de laisser les deux lignes (Oui, ça n'a aucun sens).
lecture(L) :- read_string(user_input,"\n","",_,S), split_string(S," ","",L).
lecture(L) :- read_string(user_input,"\n","",_,S), split_string(S," ","",L).

%Acquisition + vérification type 1

type_1_ok([I,Y,C],In,Co) :- term_string(In,I), setof(U,iname(U),T), member(In,T), 
		       Y=":",
		       term_string(Co,C), concept(Co),!. 
acquisition_prop_type1(Abi,Abi1,_) :- lecture(L), type_1_ok(L,I,C),decomplexe(C,NewC),!,nnf(not(NewC),NotnewC),concat(Abi,[(I,NotnewC)],Abi1),nl,write("On montre l'insatisfiabilité de "),write(NotnewC). 


% Acquisition + vérification type 2
type_2_ok([C1,C2],C_1,C_2) :- term_string(C_1,C1),term_string(C_2,C2), concept(C_1) , concept(C_2).
acquisition_prop_type2(Abi,Abi1,_) :- lecture(L), type_2_ok(L,C1,C2), decomplexe(C1,NewC1),!, decomplexe(C2, NewC2),!, genere(Nom), nnf(NewC1,NnfC1),nnf(NewC2,NnfC2), concat(Abi,[(Nom,and(NnfC1,NnfC2))], Abi1), nl, write("On montre l'insatisfiabilité de "),write("∃"),write(Nom),write(":"),write((Nom,and(NnfC1,NnfC2))).

% Partie 3
%====Fourni====
troisieme_etape(Abi,Abr) :-
nl,nl,write("Troisième étape"),nl,nl,
tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),
write("====Abox initiale===="),nl,
afficher_Abox(Abi),afficher_Abox(Abr),!,
resolution(Lie,Lpt,Li,Lu,Ls,Abr),!,
nl,write("La négation de la clause est insatisfiable, on a donc démontré la proposition initiale.").

%=============

%Tri

tri_Abox([(I,some(R,C))|Q],[(I,some(R,C))|Lie],Lpt,Li,Lu,Ls) :- 
	tri_Abox(Q,Lie,Lpt,Li,Lu,Ls),!. %Existe
	
tri_Abox([(I,all(R,C))|Q],Lie,[(I,all(R,C))|Lpt],Li,Lu,Ls) :- 
	tri_Abox(Q,Lie,Lpt,Li,Lu,Ls),!. %Pour tout
	
tri_Abox([(I,and(C1,C2))|Q],Lie,Lpt,[(I,and(C1,C2))|Li],Lu,Ls) :- 
	tri_Abox(Q,Lie,Lpt,Li,Lu,Ls),!. %Et
	
tri_Abox([(I,or(C1,C2))|Q],Lie,Lpt,Li,[(I,or(C1,C2))|Lu],Ls) :- 
	tri_Abox(Q,Lie,Lpt,Li,Lu,Ls),!. %Ou
	
tri_Abox([T|Q],Lie,Lpt,Li,Lu,[T|Ls]) :- tri_Abox(Q,Lie,Lpt,Li,Lu,Ls),!. %Atome

tri_Abox([],[],[],[],[],[]).


resolution(Lie,Lpt,Li,Lu,Ls,Abr) :- complete_some(Lie,Lpt,Li,Lu,Ls,Abr),!.

%Règles de résolution

complete_some([(I,some(R,C))|Q],Lpt,Li,Lu,Ls,Abr):- 
	evolue((I,some(R,C)),[(I,some(R,C))|Q],Lpt,Li,Lu,Ls,Lie1,Lpt1, Li1, Lu1, Ls1,Abr,Abr1),!. %Si on trouve une règle existe
complete_some([],Lpt,Li,Lu,Ls,Abr) :- transformation_and([],Lpt,Li,Lu,Ls,Abr),!. %Si on n'en trouve pas

transformation_and(Lie,Lpt,[(I,and(C1,C2))|Q],Lu,Ls,Abr):- 
	evolue((I,and(C1,C2)),[],Lpt,[(I,and(C1,C2))|Q],Lu,Ls,Lie1, Lpt1, Li1, Lu1, Ls1,Abr,Abr1),!. %Si on trouve une règle "et"
transformation_and(Lie,Lpt,[],Lu,Ls,Abr) :- deduction_all(Lie,Lpt,[],Lu,Ls,Abr),!. %Si on n'en trouve pas

deduction_all(Lie,[(I,all(R,C))|Q],Li,Lu,Ls,Abr):- 
	evolue((I,all(R,C)),Lie,[(I,all(R,C))|Q],Li,Lu,Ls,Lie1,Lpt1,Lu1,Abr,Abr1),!.%Si on trouve une règle "Pour tout"
deduction_all(Lie,[],Li,Lu,Ls,Abr):- transformation_or(Lie,[],Li,Lu,Ls,Abr),!. %Si on n'en trouve pas

transformation_or(Lie,Lpt,Li,[(I,or(C1,C2))|Q],Ls,Abr) :- 
	evolue((I,or(C1,C2)),Lie,Lpt,Li,[(I,or(C1,C2))|Q],Ls,Lie1,Lpt1,Li1,Lu1,Ls1,Abr,Abr1),!. %Si on trouve une règle "ou"
transformation_or(_,_,_,[],Ls,Abr) :- clash([],[],[],[],Ls,Abr),!. %Si on n'en trouve pas

%Clash

clash(_,_,_,_,Ls,_) :-
	query_clash(Ls),
	nl,
	write("Il y a un clash, on stoppe ce noeud.").
clash([],[],[],[],_,_) :-
	nl,
	write("Il n'y a pas de clash, et de plus on ne peut plus appliquer de règles. La branche est complète, on ne peut donc vérifier la proposition initiale."),sleep(1),nl,abort.
clash(Lie,Lpt,Li,Lu,Ls,Abr) :-
	nl,
	write("Il n'y a pas de clash, on continue la résolution de ce noeud"),
	resolution(Lie,Lpt,Li,Lu,Ls,Abr).

query_clash([T|Q]) :- test_clash(T,Q),!.
query_clash([_|Q]) :- query_clash(Q).
test_clash((I,C),Q) :- member((I,not(C)),Q).
test_clash((I,not(C)),Q) :- member((I,C),Q).



%Évolution

reconstruire_Abox(Abi,L) :- flatten(L,Abi).

evolue((I,some(R,C)), Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1,Abr,Abr1) :-
	reconstruire_Abox(Abi,[Lie,Lpt,Li,Lu,Ls]), %On reconstruit Abi
	genere(Nom),!,concat([(I,Nom,R)],Abr,Abr1),%Ajout du rôle
	concat([(Nom,C)],Abi,Abi1),%On y ajoute l'instance
	enleve((I,some(R,C)),Abi1,Abi1E),!,%On enlève la règle que l'on a traitée
	tri_Abox(Abi1E,Lie1,Lpt1,Li1,Lu1,Ls1),!,%On retrie Abi
	nl,nl,write("Règle ∃"), %Afficher la règle utilisée
	affiche_evolution_Abox(Ls, Lie, Lpt, Li, Lu, Abr, Ls1, Lie1, Lpt1, Li1, Lu1, Abr1),
	clash(Lie1,Lpt1,Li1,Lu1,Ls1,Abr1),!.%Clash ?
	

evolue((I,and(C1,C2)), Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1,Abr,Abr1) :-
	concat([],Abr,Abr1),%Copie de Abr, car il n'est pas modifié
	reconstruire_Abox(Abi,[Lie,Lpt,Li,Lu,Ls]), %On reconstruit Abi
	concat([(I,C1),(I,C2)],Abi,Abi1), %Ajout des deux rôles
	enleve((I,and(C1,C2)),Abi1,Abi1E),%On enlève la règle que l'on a traitée
	tri_Abox(Abi1E,Lie1,Lpt1,Li1,Lu1,Ls1),!,%On retrie Abi
	nl,nl,write("Règle ⊓"), %Afficher la règle utilisée
	affiche_evolution_Abox(Ls, Lie, Lpt, Li, Lu, Abr, Ls1, Lie1, Lpt1, Li1, Lu1, Abr1),
	clash(Lie1,Lpt1,Li1,Lu1,Ls1,Abr1),!.%Clash ?
	
evolue((I,or(C1,C2)), Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1,Abr,Abr1) :-
	concat([],Abr,Abr1),%Copie de Abr, car il n'est pas modifié
	reconstruire_Abox(Abi,[Lie,Lpt,Li,Lu,Ls]), %On reconstruit Abi
	enleve((I,or(C1,C2)),Abi,AbiE),!,%On enlève la règle que l'on a traitée
	concat([(I,C1)],AbiE,Abi1),%On ajoute l'instance C1
	tri_Abox(Abi1,Lie1,Lpt1,Li1,Lu1,Ls1),!,%On retrie Abi
	nl,nl,write("Règle ⊔ - Branche 1"), %Afficher la règle utilisée
	affiche_evolution_Abox(Ls, Lie, Lpt, Li, Lu, Abr, Ls1, Lie1, Lpt1, Li1, Lu1, Abr1),
	clash(Lie1,Lpt1,Li1,Lu1,Ls1,Abr1),!,%Clash ?
	
	concat([],Abr,Abr2),%Copie de Abr, car il n'est pas modifié
	reconstruire_Abox(Abi2,[Lie1,Lpt1,Li1,Lu1,Ls1]), %On reconstruit Abi
	enleve((I,C1),Abi2,Abi2E),!,%On enlève l'instance traitée
	concat([(I,C2)],Abi2E,Abi3),%On ajoute l'instance C2
	tri_Abox(Abi3,Lie2,Lpt2,Li2,Lu2,Ls2),!,%On retrie Abi
	nl,nl,write("Règle ⊔ - Branche 2"), %Afficher la règle utilisée
	affiche_evolution_Abox(Ls, Lie, Lpt, Li, Lu, Abr, Ls2, Lie2, Lpt2, Li2, Lu2, Abr2),
	clash(Lie2,Lpt2,Li2,Lu2,Ls2,Abr1),!.%Clash ?
	
deductions(_,_,_,[],_).
deductions(A,R,C,[(A,B,R)|Abr],[(B,C)|L]):- deductions(A,R,C,Abr,L).
deductions(A,R,C,[(_,_,_)|Abr],L):- deductions(A,R,C,Abr,L).

evolue((I,all(R,C)),Lie,Lpt,Li,Lu,Ls,Lie1,Lpt1,Lu1,Abr,Abr1) :-
	concat([],Abr,Abr1),%Copie de Abr, car il n'est pas modifié
	reconstruire_Abox(Abi,[Lie,Lpt,Li,Lu,Ls]), %On reconstruit Abi
	deductions(I,R,C,Abr,L), %On calcule toutes les déductions possibles
	concat(L,Abi,Abi1), %On ajoute, si il y en a, la ou les instances déduites
	enleve((I,all(R,C)),Abi1,Abi1E), %On enlève la règle
	tri_Abox(Abi1E,Lie1,Lpt1,Li1,Lu1,Ls1),!,%On retrie Abi
	nl,nl,write("Règle ∀"), %Afficher la règle utilisée
	affiche_evolution_Abox(Ls, Lie, Lpt, Li, Lu, Abr, Ls1, Lie1, Lpt1, Li1, Lu1, Abr1),
	clash(Lie1,Lpt1,Li1,Lu1,Ls1,Abr1),!.%Clash ?

% Affichage
affiche_evolution_Abox(Ls1, Lie1, Lpt1, Li1, Lu1, Abr1, Ls2, Lie2, Lpt2, Li2, Lu2, Abr2) :-
nl,write("============ Abe avant règle ============"),nl,
reconstruire_Abox(Abi1,[Lie1,Lpt1,Li1,Lu1,Ls1]),
afficher_Abox(Abi1),
afficher_Abox(Abr1),
nl,write("============ Abe après règle ============"),nl,
reconstruire_Abox(Abi2,[Lie2,Lpt2,Li2,Lu2,Ls2]),
afficher_Abox(Abi2),
afficher_Abox(Abr2).

afficher_Abox_int((A,B,R)) :- write("<"),write(A),write(","),write(B),write(">"),write(": "),write(R).
afficher_Abox_int((I,C)) :-write(I),write(":"),afficher_Abox_concept(C).
afficher_Abox_concept(or(C1,C2)):-write("("),afficher_Abox_concept(C1),write("⊔ "),afficher_Abox_concept(C2),write(")").
afficher_Abox_concept(and(C1,C2)):-write("("),afficher_Abox_concept(C1),write("⊓ "),afficher_Abox_concept(C2),write(")").
afficher_Abox_concept(some(R,C)):-write(R),write("."),write(C).
afficher_Abox_concept(all(R,C)):-write(R),write("."),write(C).
afficher_Abox_concept(not(C)):- write("¬ "),write(C).
afficher_Abox_concept(C):-write(C).
afficher_Abox_concept(anything):-write("⊤").
afficher_Abox_concept(nothing):-write("⊥").

afficher_Abox([T|Q]) :- afficher_Abox_int(T),nl,afficher_Abox(Q).
afficher_Abox([]).



% Utilitaires fournis

concat([],L1,L1).
concat([X|Y],L1,[X|L2]) :- concat(Y,L1,L2).

enleve(X,[X|L],L) :-!.
enleve(X,[Y|L],[Y|L2]) :- enleve(X,L,L2).

compteur(1).

genere(Nom) :- compteur(V),nombre(V,L1),
concat([105,110,115,116],L1,L2),
V1 is V+1,
dynamic(compteur/1),
retract(compteur(V)),
dynamic(compteur/1),
assert(compteur(V1)),nl,nl,nl,
name(Nom,L2).
nombre(0,[]).
nombre(X,L1) :-
R is (X mod 10),
Q is ((X-R)//10),
chiffre_car(R,R1),
char_code(R1,R2),
nombre(Q,L),
concat(L,[R2],L1).

chiffre_car(0,'0').
chiffre_car(1,'1').
chiffre_car(2,'2').
chiffre_car(3,'3').
chiffre_car(4,'4').
chiffre_car(5,'5').
chiffre_car(6,'6').
chiffre_car(7,'7').
chiffre_car(8,'8').
chiffre_car(9,'9').




lecture2([X|L]):-
read(X),
write(X),nl,
X \= fin, !,
lecture2(L).
lecture2([]).


