package de.uka.ilkd.key.smt.ce;

import java.io.File;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.macros.FinishSymbolicExecutionMacro;
import de.uka.ilkd.key.gui.macros.SemanticsBlastingMacro;
import de.uka.ilkd.key.gui.macros.TryCloseMacro;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.smt.SolverType;
import de.uka.ilkd.key.smt.test.TestCommons;
import de.uka.ilkd.key.ui.BatchMode;
import de.uka.ilkd.key.ui.ConsoleUserInterface;
import de.uka.ilkd.key.ui.UserInterface;
import de.uka.ilkd.key.util.HelperClassForTests;

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
    	UserInterface ui = new ConsoleUserInterface(new BatchMode("test", true), false, false);
    	KeYMediator mediator = new KeYMediator(ui, false);
    
    	SemanticsBlastingMacro macro = new SemanticsBlastingMacro();
    	TryCloseMacro close = new TryCloseMacro();
    	FinishSymbolicExecutionMacro se = new FinishSymbolicExecutionMacro();
    	
    	HelperClassForTests helper = new HelperClassForTests();
    	
    	File file = new File(testFile+"Middle.java");
    	ui.loadProblem(file);
    	
    	
    	
    	Proof proof = mediator.getSelectedProof();
    	System.out.println(proof.root());
    	//mediator.setProof(proof);
    	
    	try {
    		se.applyTo(mediator, null, null);
    		close.applyTo(mediator, null, null);
	        macro.applyTo(mediator, null, null);
        } catch (InterruptedException e) {	        
	        e.printStackTrace();
        }
    	
    	
    	
    	
    }
}
