
// Based on a B specification from Marie-Laure Potet.

public class Explosives {

	public int nb_inc = 0;
	public String [][] incomp = new String[50][2];
	public int nb_assign = 0;
	public String [][] assign = new String[30][2];

	/*@ public invariant // Prop 1
      @ (0 <= nb_inc && nb_inc < 50);
      @*/
	// Il doit y avoir au maximum 50 incompatibilités renseignées dans le tableau 'incomp'.
	// La variable 'nb_inc' doit être positif et doit être inférieur à 50 car
	// ce nombre est utilisé pour gérer les indices du tableau 'incomp', il doit donc
	// être situé entre l'indice minimum (0) et l'indice maximum (49).

	/*@ public invariant // Prop 2
      @ (0 <= nb_assign && nb_assign < 30);
      @*/
	// Il doit y avoir au maximum 30 affectations renseignées dans le tableau 'assign'.
	// La variable 'nb_assign' doit être positif et doit être inférieur à 30 car
	// ce nombre est utilisé pour gérer les indices du tableau 'assign', il doit donc
	// être situé entre l'indice minimum (0) et l'indice maximum (29).

	/*@ public invariant // Prop 3
      @ (\forall int i; 0 <= i && i < nb_inc; 
      @         incomp[i][0].startsWith("Prod") && incomp[i][1].startsWith("Prod"));
      @*/
	// Tous les produits doivent être référencés par "ProdXXXXXXX" dans la liste des
	// incompatibilités. Cela signifie que toutes les valeurs définies dans le tableau
	// 'incomp' doivent commencer par "Prod".

	/*@ public invariant // Prop 4
      @ (\forall int i; 0 <= i && i < nb_assign; 
      @         assign[i][0].startsWith("Bat") && assign[i][1].startsWith("Prod"));
      @*/
	// Tous les bâtiments doivent être référencés par "BatXXXXXXX" et tous les produits
	// doivent être référencés par "ProdXXXXXXX" dans la liste des affectations. Cela signifie
	// que toutes les valeurs définies dans le tableau 'assign'[0] doivent commencer par "Bat"
	// et toutes les valeurs définies dans le tableau 'assign'[1] doivent commencer par "Prod".

	/*@ public invariant // Prop 5
      @ (\forall int i; 0 <= i && i < nb_inc; !(incomp[i][0]).equals(incomp[i][1]));
      @*/
	// Un produit ne doit pas être incompatible avec lui-même. Cela signifie que le tableau
	// 'incomp' ne doit pas avoir une ligne avec deux fois le même produit.

	/*@ public invariant // Prop 6
      @ (\forall int i; 0 <= i && i < nb_inc; 
      @        (\exists int j; 0 <= j && j < nb_inc; 
      @           (incomp[i][0]).equals(incomp[j][1]) 
      @              && (incomp[j][0]).equals(incomp[i][1]))); 
      @*/
	// Si un produit X est incompatible avec un produit Y, alors le produit Y est incompatible
	// avec le produit X. Cela signifie que le tableau 'incomp' doit contenir 2 entrées pour
	// chaque incompatibilité : la première de la forme [X][Y] et l'autre de la forme [Y][X].

	/*@ public invariant // Prop 7
      @ (\forall int i; 0 <= i &&  i < nb_assign; 
      @     (\forall int j; 0 <= j && j < nb_assign; 
      @        (i != j && (assign[i][0]).equals(assign [j][0])) ==>
      @        (\forall int k; 0 <= k && k < nb_inc;
      @           (!(assign[i][1]).equals(incomp[k][0])) 
      @              || (!(assign[j][1]).equals(incomp[k][1])))));
      @*/
	// Deux produits dans le même bâtiment ne doivent pas être incompatibles. Cela signifique que
	// si le tableau 'assign' contient une entrée [B][P1] et une entrée [B][P2], alors les entrées
	// [P1][P2] et [P2][P1] ne doivent pas se trouver dans le tableau 'incomp'.

	/*@ requires
      @ (0 <= nb_inc+2 && nb_inc+2 < 50) &&
      @ (prod1.startsWith("Prod") && prod2.startsWith("Prod")) &
      @ (!prod1.equals(prod2))
      @ ;
      @*/
	public void add_incomp(String prod1, String prod2){
		incomp[nb_inc][0] = prod1;
		incomp[nb_inc][1] = prod2;
		incomp[nb_inc+1][1] = prod1;
		incomp[nb_inc+1][0] = prod2;
		nb_inc = nb_inc+2;
	}

	/*@ requires
      @ (0 <= nb_assign+1 && nb_assign+2 < 30) &&
      @ (bat.startsWith("Bat") && prod.startsWith("Prod")) &&
      @ (\forall int i; 0 <= i &&  i < nb_assign;
      @		(\forall int j; 0 <= j && j < nb_inc;
      @			( (assign[i][0].equals(bat) && incomp[j][0].equals(assign[i][1]) ) ==>
      @			( !incomp[j][1].equals(prod) )
      @		)))
      @ ;
      @*/
	public void add_assign(String bat, String prod){
		assign[nb_assign][0] = bat;
		assign[nb_assign][1] = prod;
		nb_assign = nb_assign+1;
	}

	/*@ requires (prod1.startsWith("Prod") && prod2.startsWith("Prod")) ;
	  @ ensures (\result == true) ==>
	  @ 		(\forall int i; 0 <= i && i < nb_inc;
	  @				!(incomp[i][0].equals(prod1) && incomp[i][1].equals(prod2)) ) ;
	  @ ensures (\result == false) ==>
	  @			(\exists int i; 0 <= i && i < nb_inc; 
	  @				incomp[i][0].equals(prod1) && incomp[i][1].equals(prod2) ) ;
      @*/
	public /*@ pure @*/ boolean compatible (String prod1, String prod2){
		for (int i=0; i < nb_inc; i++)
			if (incomp[i][0].equals(prod1) && incomp[i][1].equals(prod2))
				return false;	
		return true;
	}

	/*@ requires (bat.startsWith("Bat")) ;
	  @ requires (\exists int i; 0 <= i && i < nb_assign; assign[i][0].equals(bat)) ;
	  @ ensures (\result == true) ==>
	  @ 		((\forall int i; 0 <= i &&  i < nb_assign;
      @				(\forall int j; 0 <= j && j < nb_assign;
      @					(assign[i][0].equals(assign[j][0]) ==>
      @					(i == j)))));
	  @ ensures (\result == false) ==>
	  @ (\exists int i,j;
	  @		0 <= i && i < nb_assign && 0 <= j && j < nb_assign && i != j;
	  @		assign[i][0].equals(assign[j][0])); 
      @*/
	// La méthode doit retourner 'true' que si le bâtiment 
	// Si le résultat est 'false' : 
	public /*@ pure @*/ boolean alone_in_bat (String bat){
		int N = 0;
		for (int i=0; i < nb_assign; i++)
			if (assign[i][0].equals(bat))
				N++;
		return (N == 1);
	}

	// Solution trop simple : mettre chaque produit dans un bâtiment différent.
	/*@ requires (prod.startsWith("Prod")) ;
	  @ ensures (\result.startsWith("Bat")) ;
	  @ ensures (\forall int i; 0 <= i &&  i < nb_assign;
      @				(\forall int j; 0 <= j && j < nb_inc;
      @					( (assign[i][0].equals(assign[j][0]) ==>
      @					(compatible(assign[i][1],assign[j][1])) 
      @				)))) ;
      @ ensures (alone_in_bat(\result)) ==>
      @			(\forall int i; 0 <= i && i < nb_assign;
      @				(compatible(assign[i][1],prod)) ==> (assign[i][0].equals(\result))); 
      @*/
	// Pour ne pas autoriser la solution simple, on vérifie que si le produit a été
	// ajouté dans un bâtiment vide (nouveau bâtiment), alors le produit ne pouvait pas
	// être placé dans un autre bâtiment pour cause d'incompatibilité.
	public String findBat (String  prod){
		// On stock dans un tableau la liste des produits pour chaque bâtiment.
		String[][] liste_bat = new String[30][2];
		int nb_bats = 0;

		for (int i=0; i < nb_assign;i++){
			boolean added = false;
			for (int j=0; j < nb_bats; j++)
				if (liste_bat[j][0].equals(assign[i][0])){
					liste_bat[j][1] += "_" + assign[i][1];
					added = true;
				}
			if (!added){
				liste_bat[nb_bats][0] = assign[i][0];
				liste_bat[nb_bats][1] = assign[i][1];
				nb_bats++;
			}				
		}

		// On cherche pour chaque bâtiment le premier qui peut recevoir le produit :
		for (int i = 0; i < nb_bats; i++){
			String[] liste_prod = liste_bat[i][1].split("_");
			boolean possible = true;
			for (int j = 0; j < liste_prod.length ; j++)
				if (!compatible(prod, liste_prod[j]))
					possible = false;
			if (possible)
				return liste_bat[i][0];
		}

		// Sinon, on ajoute un nouveau bâtiment :
		return "Bat_"+prod;
	}

	public void skip(){}
}
