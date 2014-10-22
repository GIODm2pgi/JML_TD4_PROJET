import static org.junit.Assert.*;

import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;


public class TestExplosivesJUnit4FindBat {

	static int nb_inc = 0;
	static int nb_fail = 0;

	Explosives e;

	public static void main(String args[]) {
		String testClass = "TestExplosivesJUnit4FindBat";
		org.junit.runner.JUnitCore.main(testClass);
	}

	private void handleJMLAssertionError(org.jmlspecs.jmlrac.runtime.JMLAssertionError e) {
		if (e.getClass().equals(org.jmlspecs.jmlrac.runtime.JMLEntryPreconditionError.class)) {
			System.out.println("\n INCONCLUSIVE "+(new Exception().getStackTrace()[0].getMethodName())+ "\n\t "+ e.getMessage());
			nb_inc++;}
		else{
			// test failure	
			nb_fail++;
			junit.framework.Assert.fail("\n\t" + e.getMessage());	
		}  
	}

	@BeforeClass
	public static void setUpBeforeClass() throws Exception {
		nb_inc = 0;
		nb_fail = 0;
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		System.out.println("\n inconclusive tests: "+nb_inc+" -- failures : "+nb_fail );
	}

	@Test
	public void testFindBat1() {
		try{
			e=new Explosives();
			System.out.println("FindBat: " + e.findBat("Prod_Huile"));	
		}   catch(org.jmlspecs.jmlrac.runtime.JMLAssertionError e){
			handleJMLAssertionError(e);		
		} 
	}

	@Test
	public void testFindBat2() {
		try{
			e=new Explosives();
			e.add_incomp("Prod_Huile","Prod_Olive");
			System.out.println("FindBat: " + e.findBat("Prod_Huile"));	
		}   catch(org.jmlspecs.jmlrac.runtime.JMLAssertionError e){
			handleJMLAssertionError(e);		
		} 
	}

	@Test
	public void testFindBat3() {
		try{
			e=new Explosives();
			e.add_incomp("Prod_Huile","Prod_Olive");
			e.add_assign("Bat_1","Prod_Eau");
			System.out.println("FindBat: " + e.findBat("Prod_Huile"));	
		}   catch(org.jmlspecs.jmlrac.runtime.JMLAssertionError e){
			handleJMLAssertionError(e);		
		} 
	}

	@Test
	public void testFindBat4() {
		try{
			e=new Explosives();
			e.add_incomp("Prod_Huile","Prod_Olive");
			e.add_assign("Bat_1","Prod_Olive");
			System.out.println("FindBat: " + e.findBat("Prod_Huile"));	
		}   catch(org.jmlspecs.jmlrac.runtime.JMLAssertionError e){
			handleJMLAssertionError(e);		
		} 
	}

	@Test
	public void testFindBat5() {
		try{
			e=new Explosives();
			e.add_incomp("Prod_Huile","Prod_Olive");
			e.add_assign("Bat_1","Prod_Olive");
			e.add_assign("Bat_2","Prod_Eau");
			System.out.println("FindBat: " + e.findBat("Prod_Huile"));	
		}   catch(org.jmlspecs.jmlrac.runtime.JMLAssertionError e){
			handleJMLAssertionError(e);		
		} 
	}

	@Test
	public void testFindBat6() {
		try{
			e=new Explosives();
			e.add_incomp("Prod_Huile","Prod_Olive");
			e.add_assign("Bat_1","Prod_Olive");
			e.add_assign("Bat_2","Prod_Eau");
			e.add_assign("Bat_2","Prod_Moutarde");
			e.add_assign("Bat_2","Prod_Citron");
			System.out.println("FindBat: " + e.findBat("Prod_Huile"));	
		}   catch(org.jmlspecs.jmlrac.runtime.JMLAssertionError e){
			handleJMLAssertionError(e);		
		} 
	}

	@Test
	public void testFindBat7() {
		try{
			e=new Explosives();
			String[] liste_produits = {
					"Prod_Huile",
					"Prod_Olive",
					"Prod_Chocolat",
					"Prod_Lait",
					"Prod_Alcool",
					"Prod_Poivre",
					"Prod_Sel",
					"Prod_Jambon",
					"Prod_Vinaigre",
					"Prod_Fromage",
					"Prod_Thé",
					"Prod_Café",
					"Prod_Vin",
					"Prod_Dentifrice",
					"Prod_Haricot",
					"Prod_Pain",
					"Prod_Biscotte"
			};

			e.add_incomp("Prod_Huile","Prod_Olive");
			e.add_incomp("Prod_Alcool","Prod_Vin");
			e.add_incomp("Prod_Café","Prod_Thé");
			e.add_incomp("Prod_Jambon","Prod_Fromage");
			e.add_incomp("Prod_Sel","Prod_Poivre");
			e.add_incomp("Prod_Moutarde","Prod_Poivre");
			e.add_incomp("Prod_Vinaigre","Prod_Poivre");
			e.add_incomp("Prod_Vinaigre","Prod_Huile");
			e.add_incomp("Prod_Vinaigre","Prod_Fromage");
			e.add_incomp("Prod_Vinaigre","Prod_Dentifrice");
			e.add_incomp("Prod_Pain","Prod_Dentifrice");
			e.add_incomp("Prod_Pain","Prod_Vinaigre");
			
			System.out.println("=================================");
			
			for (int i=0; i < liste_produits.length; i++){
				String b = e.findBat(liste_produits[i]);
				System.out.println(liste_produits[i] + " -> " + b);
				e.add_assign(b,liste_produits[i]);
			}

		}   catch(org.jmlspecs.jmlrac.runtime.JMLAssertionError e){
			handleJMLAssertionError(e);		
		} 
	}
}
