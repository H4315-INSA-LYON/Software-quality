// ordering du temps 
open util/ordering[Time] as to
// on utilise le framework integer pour faire des operations sur les entiers
open util/integer 


// -----------------------------------  CONSTANTES  --------------------------------------------

let tailleGrille = 7 // la taille de la grille
let RCAP = 7  		// la capacite de stockage d'un receptacle nbProduits <= RCAP
let DCAP = 3  		// la capacite de transport d'une drone nbProduits <= DCAP
let ECAP = 3  		// la capacite de chargement d'une drone energie <= ECAP
let CCAP = 3  		// la capacite maximale d'une commande 


// -----------------------------------  SIGNATURES  --------------------------------------------

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

// Un noeud est represente par un receptacle. Permet de calculer le chemin entre 
// entrepot et un receptacle
// nextN        - le prochain noeud dans le chemin (pour les extremites vide)
// previousN  - le noeud anterieur dans le chemin (pour l'entrepot vide)  
sig Noeud
{
	currentR : one Receptacle,	
	nextN : lone Noeud,
	previousN : lone Noeud
}

// la declaration de l'entrepot qui est de la meme maniere que le receptacle
// entrepot est un singleton
one sig Entrepot extends Receptacle {}



// ------------------  FUNCTIONS  ---------------------

// Renvoie la valure absolue d'un nombre
fun abs[a : Int]: Int
{
	(a<Int[0]) =>a.mul[-1] else a
}

// Renvoie la distance de Manhattan entre deux position a et b
fun distance [a,b : Position]: Int
{
	add[ abs[sub[a.x,b.x] ], abs[sub[a.y,b.y] ] ]
}



// -----------------------------------  INVARIANTS  --------------------------------------------

// ---- Invariants pour la creation de la carte ----

// Tous drones et receptacles doit etre a l'interieur de notre grille
fact ObjetPositionGrille
{
	all p : Position | p.x>=0 && p.x<tailleGrille && p.y>=0 && p.y<tailleGrille 
}

// Les positions ont des coordonnees differents
fact PositionPasMemeCoordonnes 
{
	all disj p1, p2: Position | p1.x != p2.x || p1.y != p2.y 
}



// ---- Invariants d'initialisation des donees ----

// le nombre de receptacle doit etre plus grand a un + 1 pour l'entrepot
fact ReceptacleNombre
{ 
	#Receptacle > 1
}

// le nombre de drones doit etre strictement positif
fact DroneNombre
{
	#Drone > 0
}

// le nombre de commandes est strictement positif
fact CommandeNombre
{
	#Commande > 0
}

// ---- Invariants sur les receptacles ----

// Chaque receptacle doit avoir un autre receptacle voisin pour lequelle leur distance est plus
// petit que 3
fact Voisinage 
{
	all r1 : Receptacle | some r2 : Receptacle   
	| distance[r1.pos,r2.pos]>0 && distance[r1.pos, r2.pos]<4
}

// Les receptacles sont dans des positions differents
fact ReceptaclePasMemePosition
{
	all disj r1, r2 : Receptacle | r1.pos!=r2.pos
}


// ---- Invariants sur les drones

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

// Useless
// Deux drones ne peuvent pas avoir la meme position
// sauf dans l'entrepot 
fact DronePasMemePosition
{
 	all disj d1, d2 : Drone | all t : Time | some e : Entrepot | d1.pos.t!=d2.pos.t ||
	d1.pos.t = e.pos
}


// ---- Invariants sur les commandes ----

// La destination d'une commande ne peut pas etre l'entrepot
fact DestinationCommandePasEntrepot
{
	all c : Commande | one e : Entrepot | c.destination!=e
}

// ---- Invariants sur les noeuds ----

// Il peut pas avoir de boucle
fact BoucleNoeuds
{
	all n : Noeud | n.currentR not in n.^nextN.currentR
}

fact PreviousNoeuds
{
	all n: Noeud | (#n.nextN>0) => (n.nextN.previousN = n)
}

fact EntrepotInvariants
{
	all n : Noeud| one e: Entrepot | (n.currentR = e) => ( #n.previousN =0 )
}

fact NoUniqueNodeForEntrepot
{
	all n : Noeud | one e:Entrepot | (n.currentR=e) => (#n.nextN>0)
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
 	all r : Receptacle | one e : Entrepot  | some n : Noeud | (n.currentR=e) && ((r!=e) => r in n.*nextN.currentR)
 }

// On peut pas avoir des noeuds doublons( meme receptacles et meme nextN )
fact NoeudsDifferent
{
	all disj n1, n2 : Noeud | n1.currentR!=n2.currentR || n1.nextN!=n2.nextN
}


// ------------------  SIMULATION  ---------------------

// initialisation
pred init[t:Time]
{
	// pas de commande vide 
	all commande : Commande | #commande.produits.t > 0 && #commande.produits<=CCAP
	
	// tout les drones sont vides au debut
	all drone : Drone | #drone.produits.t  = 0	

	one e: Entrepot | {
				
				// un receptacle soit c'est l'entrepot soit il est vide
				all r: Receptacle | r = e ||  #r.produits.t = 0

				// toutes les drones a l'entrepot et charges
				all d: Drone | {
					d.pos.t = e.pos
					d.energie.t = ECAP
					#d.produits.t = 0
					d.destination.t = e
				}				

				// toutes les produits se trouvent a l'entrepot et chaque commande a un seule type de produits
				all p: Produit | p in e.produits.t && one c: Commande | p in c.produits.t
	}
}


// simulation
pred simul
{
	init[first]
	all t: Time - last | let t' = t.next 
	{
		all d : Drone | deplacerDrone[t,t',d]

		majMonde [t,t']
	}
}

pred majMonde [t, t' : Time]
{
	all c: Commande, p: Produit| one e: Entrepot |( p in c.produits.t && (no d: Drone| p in d.produits.t') ) => 
													(p in c.produits.t' && p in e.produits.t')
													else (p not in c.produits.t' && p not in e.produits.t')

	all r: Receptacle, p: Produit| (p in r.produits.t && no d: Drone | p in d.produits.t') =>(p in r.produits.t')
													else p not in r.produits.t'
}

pred deplacerDrone[t,t' : Time , d:Drone]
{
	one e: Entrepot | d.pos.t = d.destination.t.pos => 
	{
		// drone a l'entrepot
		d.pos.t = e.pos => 
		{
			one c: Commande | #d.produits.t=0 && #c.produits.t > 0 && (no d': Drone | d!=d' && c.produits.t in d'.produits.t')=>
			{
				d.produits.t' = c.produits.t
				no d' : Drone | d' != d &&  (some p: Produit | p in d'.produits.t' && p in d.produits.t')
				d.destination.t' = c.destination
				one n : Noeud | 
				{
					n.currentR = c.destination
					d.noeud.t'.currentR = e
					no n.nextN
					n in d.noeud.t'.*nextN
				}
			}
			else 
			{
				d.destination.t' = e
				d.pos.t' = e.pos
				d.noeud.t' = d.noeud.t
				d.produits.t' = d.produits.t
			}
			d.energie.t' = d.energie.t
		}
		// drone au dernier receptacle
		else
		{
			one r: Receptacle |  r = d.destination.t =>
			{
				r.produits.t' in d.produits.t
				no p: Produit | p in d.produits.t'
				d.destination.t' = e
				d.pos.t' = r.pos
				d.noeud.t' = d.noeud.t
			}
		}
	}
	//drone en mouvement
	else
	{
		d.destination.t' = d.destination.t
		d.produits.t' = d.produits.t
		// si la drone se trouve dans un noeud (receptacle)
		d.pos.t = d.noeud.t.currentR.pos =>
		{
			// la drone doit etre charge
			d.energie.t < distance[d.pos.t, d.noeud.t.nextN.currentR.pos] =>
			{
				d.pos.t' = d.pos.t
				d.energie.t' = d.energie.t.add[1]
				d.noeud.t' = d.noeud.t
			}
			// la drone est charge, donc elle peut avancer
			else
			{
				// si la drone se retourne
				d.destination.t = e => 
				{
					avancer[t,t',d,d.noeud.t.previousN.currentR]
					d.noeud.t' = d.noeud.t.previousN
				}
				// si la drone va vers un receptacle
				else
				{
					avancer[t,t',d,d.noeud.t.nextN.currentR]
					d.noeud.t = d.noeud.t.nextN
				}
			}
		}
		// si la drone se trouve dans le trajet elle doit juste avancer
		else
		{
				avancer[t,t',d,d.noeud.t.currentR]
				
		}
	}
}


pred avancer[t,t' : Time, d:Drone, r:Receptacle]
{
	one p:  Position | distance[p,d.pos.t] =1 && distance[p,r.pos]<distance[r.pos,d.pos.t] =>
	{
		d.pos.t' = p 	
		d.energie.t' = d.energie.t.sub[1]
	}
}


run simul for 3


