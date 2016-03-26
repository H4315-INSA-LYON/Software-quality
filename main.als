// ordering du temps 
open util/ordering[Time] as to
// on utilise le framework integer pour faire des operations sur les entiers
open util/integer 


// ------------------  Constantes  ---------------------
// Des valeurs constants comme la taille de la grille, le nombre de receptacles,...
let tailleGrille = 7
let RCAP = 7
let DCAP = 2


// ------------------  SIGNATURE  ---------------------

// le temps
sig Time {}

//definition d'un produit
sig Produit {}

// la position d'une Drone, Receptacle, Entrepot qui est selon les directions x et y
sig Position
{
	x,y : Int
}

// drone qui transporte des produits
sig Drone
{
	pos :  Position one -> Time,
	produits: Produit -> Time,
	destination: Receptacle	one->Time,
	noeud : Noeud one -> Time,
	energie: Int one  -> Time
}

// receptacle qui recoit les produits transportes par une drone
sig Receptacle
{
	pos: Position,
	produits: Produit->Time
	// TODO : capacite
}

// la commande qui va etre realise par une drone
sig Commande
{
	destination: one Receptacle,
	produits: Produit -> Time
}

sig Noeud
{
	currentR : one Receptacle,	
	nextN : lone Noeud

}

// la declaration de l'entrepot qui est de la meme maniere que le receptacle
// entrepot est un singleton
one sig Entrepot extends Receptacle {}



// -----------------  INVARIANTS  ------------------

// le nombre de receptacle doit etre plus grand a un + 1 pour l'entrepot
fact ReceptacleNombre
{ 
	#Receptacle > 1
}

// le nombre de drones doit etre positif
fact DroneNombre
{
	#Drone > 0
}
// Chaque receptacle doit avoir un autre receptacle voisin pour lequelle leur distance est plus
// petit que 3
fact Voisinage 
{
	all r1 : Receptacle | some r2 : Receptacle   
	|  distance[r1.pos, r2.pos]<4
}
// Pour chaque drone l'energie est entre 0 et 3 inclus.
fact EnergieDrone 
{
	all d : Drone,t : Time| d.energie.t>=0 && d.energie.t<4
}

// A n'importe quelle temp, une drone doit avoir au mois un receptacle voisin
fact DroneReceptacleVoisin
{
	all d : Drone, t : Time | some r : Receptacle | distance[r.pos, d.pos.t]<4
}
// Les positions ont des coordonnees differents
fact PositionPasMemeCoordonnes 
{
all disj p1, p2: Position | p1.x != p2.x || p1.y != p2.y 
}

//Deux drones ne peuvent pas avoir la meme position
// sauf dans l'entrepot
fact DronePasMemePosition
{
 	all disj d1, d2 : Drone | all t : Time | some e : Entrepot | d1.pos.t!=d2.pos.t ||
	d1.pos.t = e.pos
}
// Les receptacles sont dans des positions differents
fact ReceptaclePasMemePosition
{
	all disj r1, r2 : Receptacle | r1.pos!=r2.pos
}

// Tous drones et receptacles doit etre a l'interieur de notre grille
fact ObjetPositionGrille
{
all p : Position | p.x>=0 && p.x<tailleGrille && p.y>=0 && p.y<tailleGrille 
}

// La destination d'une commande ne peut pas etre l'entrepot
fact DestinationCommandePasEntrepot
{
all c : Commande | some e : Entrepot | c.destination!=e
}

// Il peut pas avoir de boucle
fact BoucleNoeuds
{
all n : Noeud | n.currentR not in n.^nextN.currentR
}

// La distance entre entre deux receptacles consecutives d'un chemin doit etre plus petit que 3
// ????? cas si chemin sans consecutive
fact distanceReceptacleConsecutive
{
	all n : Noeud | distance[n.currentR.pos, n.nextN.currentR.pos]<=3
}
// On peut arriver a partir d'entrepot a n'importe quelle receptacle
fact RecepctacleAtteignable
{
	all r : Receptacle | one e : Etrepot | some n : Noeud | (n.currentR=e) && r in n.^nextN
}

// On peut pas avoir des noeuds doublons( meme receptacles et meme nextN )
fact NoeudsDifferent
{
	all disj n1, n2 : Noeud | n1.currentR!=n2.currentR || n1.nextN!=n2.nextN
}



// ------------------  FUNCTIONS  ---------------------
fun abs[a : Int]: Int
{
	(a<Int[0]) =>a.mul[-1] else a
}

fun distance [a,b : Position]: Int
{
	add[ abs[sub[a.x,b.x] ], abs[sub[a.y,b.y] ] ]
}



// ------------------  SIMULATION  ---------------------




// ------------------  TESTS  ---------------------


pred show{}

run show for 6













