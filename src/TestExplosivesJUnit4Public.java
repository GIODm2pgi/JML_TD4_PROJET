import static org.junit.Assert.*;

import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;


public class TestExplosivesJUnit4Public {

	static int nb_inc = 0;
	static int nb_fail = 0;

	Explosives e;

	public static void main(String args[]) {
		String testClass = "TestExplosivesJUnit4Public";
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
	public void  testFailInvariant6() {
		try{
			e=new Explosives();
			e.add_incomp("Prod_Glycerine","Prod_Dynamite");
			e.nb_inc--;
			e.skip();
		} 	catch(org.jmlspecs.jmlrac.runtime.JMLAssertionError e){
			handleJMLAssertionError(e);		
		}  
	}
}
