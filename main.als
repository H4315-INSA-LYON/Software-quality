//Ame ni togirete ima kimi no kokoro o tsunagu oto	
//Shoumei o nogareteru parareru shiyou	
//Dakara mitsukete mitsukete yo nee	
//Kioku no mukou ni	
//Sono me ni boku o utsushite yo

// ordering du temps 
open util/ordering[Time] 
// on utilise le framework integer pour faire des operations sur les entiers
open util/integer 


// -----------------------------------  CONSTANTES  --------------------------------------------

let tailleGrille = 2 // la taille de la grille
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
	produits : Produit-> Time,
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
	(a>=0) =>a else a.mul[-1] 
}

// Renvoie la distance de Manhattan entre deux position a et b
fun distance [a,b : Position]: Int
{
	abs[a.x.sub[b.x] ].add[abs[a.y.sub[b.y] ] ]
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

// Les receptacles sont dans des positions differents
fact ReceptaclePasMemePosition
{
	all disj r1, r2 : Receptacle | r1.pos!=r2.pos
}


// ---- Invariants sur les drones
/*
fact EnergiePositive
{
	all d:Drone, t: Time | d.energie.t >=0 && d.energie.t <=ECAP
}*/

// ---- Invariants sur les commandes ----

// La destination d'une commande ne peut pas etre l'entrepot
fact DestinationCommandePasEntrepot
{
	all c : Commande | one e : Entrepot | c.destination !=e
}

// ---- Invariants sur les noeuds ----

// Il peut pas avoir de boucle
fact BoucleNoeuds
{
	all n : Noeud | n.currentR not in n.^nextN.currentR
	all n : Noeud | n.currentR not in n.^previousN.currentR
}

fact PreviousNoeuds
{
	all n: Noeud | (one n.nextN => n.nextN.previousN = n) && 
							(one n.previousN => n.previousN.nextN = n)
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
	all n : Noeud |  one n.nextN => distance[n.currentR.pos, n.nextN.currentR.pos]<=3
}

// On peut arriver a partir d'entrepot a n'importe quelle receptacle
fact RecepctacleAtteignable
 {
 	all r : Receptacle | one e : Entrepot  | some n : Noeud | ((n.currentR=e) && (r!=e) )=> r in n.*nextN.currentR
 }

// On peut pas avoir des noeuds doublons( meme receptacles et meme nextN )
fact NoeudsDifferent
{
	all disj n1, n2 : Noeud | n1.currentR!=n2.currentR || (n1.nextN!=n2.nextN && some n1.nextN && some n2.nextN) 
}

// ------------------  SIMULATION  ---------------------

// initialisation
pred init[t:Time]
{
	// pas de commande vide 
	all commande : Commande | #commande.produits.t > 0 && #commande.produits<=CCAP
	
	all d: Drone | d.energie.t = 3 && #d.produits.t = 0 

	all d: Drone | one e : Entrepot | d.pos.t = e.pos && d.destination.t = e &&  d.noeud.t.currentR = e

	all r: Receptacle| one e: Entrepot | r = e || #r.produits.t = 0
	

	all p:Produit| one e:Entrepot | p in e.produits.t && one c:Commande | p in c.produits.t
}


// simulation
fact simul
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
	all p: Produit, c: Commande | ( p in c.produits.t && (no d: Drone| p in d.produits.t') ) => 
													(p in c.produits.t')
													else (p not in c.produits.t')
	all p:Produit | one e:Entrepot | p in e.produits.t && (no d:Drone | p in d.produits.t') =>
													p in e.produits.t' else p not in e.produits.t'	
	
	all r: Receptacle |one e: Entrepot| r!=e && (no d: Drone | d.destination.t = r && d.pos.t = r.pos) => r.produits.t' = r.produits.t

}

pred deplacerDrone[t,t' : Time , d:Drone]
{
	one e: Entrepot | d.pos.t = d.destination.t.pos => 
	{

		// drone a l'entrepot
		d.pos.t = e.pos => 
		{
				
			(no  c: Commande | #c.produits.t>0 && (no d':Drone|d'!=d && c.produits.t in d'.produits.t')) =>
			{
				d.destination.t' = e
				d.noeud.t' = d.noeud.t
				d.produits.t' = d.produits.t
			}
			else one c: { c:Commande |   #c.produits.t > 0 && (no d': Drone | d!=d' && c.produits.t in d'.produits.t')}|
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
		}
		// drone au dernier receptacle
		else
		{
				d.produits.t in d.destination.t.produits.t'
				d.destination.t.produits.t in d.destination.t.produits.t'
				no p: Produit | p in d.produits.t'
				d.destination.t' = e
				d.noeud.t' = d.noeud.t
		}
		d.pos.t' = d.pos.t
		d.energie.t' = d.energie.t
	}
	//drone en mouvement
	else
	{
		d.produits.t' = d.produits.t
		d.destination.t' = d.destination.t
		d.pos.t = d.noeud.t.currentR.pos =>
		{
			// la drone doit etre charge
			((d.energie.t < distance[d.pos.t, d.noeud.t.nextN.currentR.pos] && d.destination.t!=e )
			|| (d.energie.t < distance[d.pos.t,d.noeud.t.previousN.currentR.pos] && d.destination.t=e))=>
			{
							d.pos.t' = d.pos.t
				d.energie.t' = d.energie.t.add[1]
				d.noeud.t' = d.noeud.t
			}
			else
			{
				d.destination.t = e => 
				{
					(no r: Receptacle | d.noeud.t.previousN.currentR =r) =>
					{
						// for debug
						d.energie.t' = d.energie.t.add[3]
						d.pos.t' = d.pos.t
					}
					else one r:{r:Receptacle | d.noeud.t.previousN.currentR =r} | avancer[t,t',d,r]
					d.noeud.t' = d.noeud.t.previousN
				}
				// si la drone va vers un receptacle
				else
				{
					(no r: Receptacle | d.noeud.t.nextN.currentR =r) =>
					{
						// for debug
						d.energie.t' = d.energie.t.add[3]
						d.pos.t' = d.pos.t
					}
					else one r: {r:Receptacle | d.noeud.t.nextN.currentR =r} | avancer[t,t',d,r]
 					d.noeud.t' = d.noeud.t.nextN
				}
			}
		}
		else
		{
			avancer[t,t',d,d.noeud.t.currentR]
			d.noeud.t' = d.noeud.t
		}
	}
}


pred avancer[t,t' : Time, d:Drone, r:Receptacle]
{
	(no p: Position | distance[p,d.pos.t]=1 && distance[p,r.pos]<distance[d.pos.t,r.pos])
	=>
	{
		d.pos.t = d.pos.t'
		d.energie.t = d.energie.t'
	}
	else one p: {p:Position | distance[p,d.pos.t]=1 && distance[p,r.pos]<distance[d.pos.t,r.pos]} | 
	{
		d.pos.t' = p
		d.energie.t' = d.energie.t.sub[1]
	}
}

// Deux drones ne doivent pas être dans une même position, sauf dans l'entrepot
assert droneMemePosition 
{
 all disj d1,d2 : Drone | all t : Time | one e : Entrepot | d1.pos.t!=d2.pos.t || d1.pos.t=e.pos
}

//L'énergie d'une batterie doit être entre 0 et 3
assert energieEntre0et3
{
all d : Drone | all t : Time| d.energie.t>=0 && d.energie.t<=ECAP
}

/*A la fin, tous les commandes doivent être vides
				il ne doit pas avoir de produits dans l'entrepot
				tous les drones doivent etre dans l'entrepot */
assert verificationFin
{
all c : Commande | #c.produits.last=0
one e : Entrepot | #e.produits.last = 0
all d : Drone | one e : Entrepot | d.pos.last = e.pos
}

// Un produit doit appartenir à une drone ou à un receptacle
assert pasProduitDroneEtReceptacle
{
	all d : Drone | all r : Receptacle | no p : Produit | all t : Time |  
	p in d.produits.t && p in r.produits.t 
}
// Au niveau d’un réceptacle les actions de livrer les produits et de recharger la
// batterie ne peuvent pas avoir lieu en même temps.
assert pasBatterieEtLivraison
{
	all t : Time | all d : Drone | all r : Receptacle | one e : Entrepot |
	(d.pos.t=r.pos) && (#d.produits.t>0) && (t!=last) && (e!=r) => 
	(#d.produits.t.next=0 || d.energie.t=d.energie.t.next)
}


pred go{}

run go for exactly 1 Drone, exactly 2 Receptacle,25 Time, exactly 2 Produit, exactly 4 Position, exactly 2 Commande, 8 Noeud, 4 Int
run go for exactly 2 Drone, exactly 2 Receptacle,5 Time, exactly 2 Produit, exactly 4 Position, exactly 2 Commande, 8 Noeud, 4 Int
check droneMemePosition for exactly 2 Drone, exactly 2 Receptacle,25 Time, exactly 2 Produit, exactly 4 Position, exactly 2 Commande, 8 Noeud, 4 Int
check energieEntre0et3 for exactly 2 Drone, exactly 2 Receptacle,25 Time, exactly 2 Produit, exactly 4 Position, exactly 2 Commande, 8 Noeud, 4 Int
check verificationFin for exactly 2 Drone, exactly 2 Receptacle,25 Time, exactly 2 Produit, exactly 4 Position, exactly 2 Commande, 8 Noeud, 4 Int
check pasProduitDroneEtReceptacle for exactly 2 Drone, exactly 2 Receptacle,25 Time, exactly 2 Produit, exactly 4 Position, exactly 2 Commande, 8 Noeud, 4 Int
check pasBatterieEtLivraison for exactly 2 Drone, exactly 2 Receptacle,25 Time, exactly 2 Produit, exactly 4 Position, exactly 2 Commande, 8 Noeud, 4 Int
run go for exactly 2 Drone, exactly 5 Receptacle,5 Time, exactly 4 Produit, exactly 9 Position, exactly 2 Commande, 8 Noeud, 4 Int
