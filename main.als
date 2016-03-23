// ordering du temps 
open util/ordering[Time] as to
// on utilise le framework integer pour faire des operations sur les entiers
open util/integer 

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
	// chemin
	energie: Int one  -> TIme
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


// ------------------  Functions  ---------------------
fun abs[a Int]: Int
{
}

fun distance [a,b Position]: Int
{
	
}




