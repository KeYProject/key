package de.uka.ilkd.key.smt.ce;

import java.io.File;

import de.uka.ilkd.key.gui.macros.SemanticsBlastingMacro;
import de.uka.ilkd.key.smt.SolverType;
import de.uka.ilkd.key.smt.test.TestCommons;

public class TestCE extends TestCommons {
	
	public static final String testFile = System.getProperty("key.home")
	        + File.separator + "examples" + File.separator + "_testcase"
	        + File.separator + "smt" + File.separator+"ce"+File.separator;
	
	private static final String SYSTEM_PROPERTY_SOLVER_PATH = "z3SolverPath";

    private static boolean isInstalled = false;
    private static boolean installChecked = false;
    
    
    @Override
    public boolean toolNotInstalled() {
    	if (!installChecked) {    
    		isInstalled = getSolverType().isInstalled(true);
    		installChecked = true;
    		if(!isInstalled) {
    			System.out.println("Warning: " + getSolverType().getName() + " is not installed, tests skipped.");
            System.out.println("Maybe use JVM system property \"" + SYSTEM_PROPERTY_SOLVER_PATH + "\" to define the path to the Z3 command.");
    		}	  
    		
    		if(isInstalled &&!getSolverType().supportHasBeenChecked()){
    			if(!getSolverType().checkForSupport()){
    				System.out.println("Warning: " + "The version of the solver "+ getSolverType().getName() + " used for the following tests may not be supported.");
    			}    			
    		}
    	}

    	
    	

        return !isInstalled;
    }
    
    @Override
    public SolverType getSolverType() {
       SolverType type = SolverType.Z3_CE_SOLVER;
       String solverPathProperty = System.getProperty(SYSTEM_PROPERTY_SOLVER_PATH);
       if (solverPathProperty != null && !solverPathProperty.isEmpty()) {
          type.setSolverCommand(solverPathProperty);
       }
       return type;
    }
    
    public void testArrayClear(){
    	SemanticsBlastingMacro macro = new SemanticsBlastingMacro();
    	
    }
}
