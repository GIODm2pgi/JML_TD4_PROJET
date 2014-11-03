

// Based on a B specification from Marie-Laure Potet.

public class Explosives {

	public int nb_inc = 0;
	public String [][] incomp = new String[50][2];
	public int nb_assign = 0;
	public String [][] assign = new String[30][2];

	/*@ public invariant // Prop 1
      @ (0 <= nb_inc && nb_inc < 50);
      @*/

	/*@ public invariant // Prop 2
      @ (0 <= nb_assign && nb_assign < 30);
      @*/

	/*@ public invariant // Prop 3
      @ (\forall int i; 0 <= i && i < nb_inc; 
      @         incomp[i][0].startsWith("Prod") && incomp[i][1].startsWith("Prod"));
      @*/

	/*@ public invariant // Prop 4
      @ (\forall int i; 0 <= i && i < nb_assign; 
      @         assign[i][0].startsWith("Bat") && assign[i][1].startsWith("Prod"));
      @*/

	/*@ public invariant // Prop 5
      @ (\forall int i; 0 <= i && i < nb_inc; !(incomp[i][0]).equals(incomp[i][1]));
      @*/

	/*@ public invariant // Prop 6
      @ (\forall int i; 0 <= i && i < nb_inc; 
      @        (\exists int j; 0 <= j && j < nb_inc; 
      @           (incomp[i][0]).equals(incomp[j][1]) 
      @              && (incomp[j][0]).equals(incomp[i][1]))); 
      @*/

	/*@ public invariant // Prop 7
      @ (\forall int i; 0 <= i &&  i < nb_assign; 
      @     (\forall int j; 0 <= j && j < nb_assign; 
      @        (i != j && (assign[i][0]).equals(assign [j][0])) ==>
      @        (\forall int k; 0 <= k && k < nb_inc;
      @           (!(assign[i][1]).equals(incomp[k][0])) 
      @              || (!(assign[j][1]).equals(incomp[k][1])))));
      @*/


	/*@ requires (0 <= nb_inc+2 && nb_inc+2 < 50) ;
      @ requires (prod1.startsWith("Prod") && prod2.startsWith("Prod")) ; 
      @ requires (!prod1.equals(prod2)) ;
      @*/
	public void add_incomp(String prod1, String prod2){
		incomp[nb_inc][0] = prod1;
		incomp[nb_inc][1] = prod2;
		incomp[nb_inc+1][1] = prod1;
		incomp[nb_inc+1][0] = prod2;
		nb_inc = nb_inc+2;
	}

	/*@ requires (0 <= nb_assign+1 && nb_assign+1 < 30) ;
      @ requires (bat.startsWith("Bat") && prod.startsWith("Prod")) ;
      @ requires (\forall int i; 0 <= i &&  i < nb_assign;
      @				(\forall int j; 0 <= j && j < nb_inc;
      @					( (assign[i][0].equals(bat) && incomp[j][0].equals(assign[i][1]) )
      @					==> ( !incomp[j][1].equals(prod) )
      @			))) ;
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
      @ ensures (\result == true) ==>
      @		(\forall int i; 0 <= i &&  i < nb_assign;
      @			!assign[i][0].equals(bat)) ;
	  @ ensures (\result == false) ==>
	  @ 	(\exists int i; 0 <= i && i < nb_assign;
	  @			assign[i][0].equals(bat)); 
      @*/
	public /*@ pure @*/ boolean existe_bat (String bat){
		int N = 0;
		for (int i=0; i < nb_assign; i++)
			if (assign[i][0].equals(bat))
				N++;
		return (N == 0);
	}

	// Solution trop simple : mettre chaque produit dans un bâtiment différent.
	/*@ requires (prod.startsWith("Prod")) ;
	  @ ensures (\result.startsWith("Bat")) ;
	  @ ensures (\forall int i; 0 <= i &&  i < nb_assign;
	  @				(assign[i][0].equals(\result)) ==> (compatible(assign[i][1],prod)) );
	  @*/
	public String findBatSimple (String  prod){
		// On ajoute un nouveau bâtiment :
		return "Bat_"+prod;
	}

	// Solution trop simple interdit :
	/*@ requires (prod.startsWith("Prod")) ;
      @ ensures (\result.startsWith("Bat")) ;
      @ ensures (\forall int i; 0 <= i &&  i < nb_assign;
      @				(assign[i][0].equals(\result)) ==> (compatible(assign[i][1],prod)) );
      @ ensures (existe_bat(\result)) ==>
      @			(\forall int i; 0 <= i && i < nb_assign;
      @				(\exists int k; 0 <= k && k < nb_assign;
      @						(assign[i][0].equals(assign[k][0]) && !compatible(assign[k][1],prod))));
      @*/
	// Pour ne pas autoriser la solution trop simple, on vérifie que si le produit a été
	// ajouté dans un bâtiment vide (nouveau bâtiment), alors le produit ne pouvait pas
	// être placé dans un autre bâtiment pour cause d'incompatibilité.
	public String findBatSimpleInterdit (String  prod){
		// On ajoute un nouveau bâtiment :
		return "Bat_"+prod;
	}

	/*@ requires (prod.startsWith("Prod")) ;
	  @ ensures (\result.startsWith("Bat")) ;
      @ ensures (\forall int i; 0 <= i &&  i < nb_assign;
      @				(assign[i][0].equals(\result)) ==> (compatible(assign[i][1],prod)) );
      @ ensures (existe_bat(\result)) ==>
      @			(\forall int i; 0 <= i && i < nb_assign;
      @				(\exists int k; 0 <= k && k < nb_assign;
      @						(assign[i][0].equals(assign[k][0]) && !compatible(assign[k][1],prod))));
      @*/
	public String findBat (String  prod){

		// On stocke la liste de tous les bâtiments :
		String[] batiments = new String [30];
		int nb_bats = 0;

		// On stocke la liste des bâtiments qui ne peuvent pas recevoir le produit :
		String[] batiments_impossibles = new String [30];
		int nb_bats_imp = 0;

		// On parcourt le tableau assign pour remplir les listes :
		for (int i=0; i < nb_assign; i++){
			String bat_test = assign[i][0];
			String prod_test = assign[i][1];

			// Test de compatibilité
			boolean test_comp = true;
			for (int j=0; j < nb_inc; j++)
				if (incomp[j][0].equals(prod) && incomp[j][1].equals(prod_test))
					test_comp = false;

			// Ajout si nécéssaire dans la liste des bâtiments :
			boolean test_liste_bat = false;
			for (int j=0; j < nb_bats; j++)
				if (batiments[j].equals(bat_test))
					test_liste_bat = true;
			if (!test_liste_bat){
				batiments[nb_bats]=bat_test;
				nb_bats++;
			}

			// Ajout si nécéssaire dans la liste des bâtiments incompatibles :
			if (!test_comp){
				boolean test_liste_bat_imp = false;
				for (int j=0; j < nb_bats_imp; j++)
					if (batiments_impossibles[j].equals(bat_test))
						test_liste_bat_imp = true;
				if (!test_liste_bat_imp){
					batiments_impossibles[nb_bats_imp]=bat_test;
					nb_bats_imp++;
				}
			}
		}

		// On cherche le premier bâtiment qui n'est pas dans la liste des incompatibles :
		for (int i=0; i < nb_bats; i++){
			boolean test_comp = true;
			for (int j=0; j < nb_bats_imp; j++)
				if (batiments_impossibles[j].equals(batiments[i]))
					test_comp = false;
			if (test_comp)
				return batiments[i];
		}

		// Sinon, on ajoute un nouveau bâtiment :
		return "Bat_"+prod;
	}

	public void skip(){}
}
