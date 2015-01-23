package de.uka.ilkd.key.smt.testgen;

import java.io.File;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.macros.TestGenMacro;
import de.uka.ilkd.key.smt.SolverType;
import de.uka.ilkd.key.smt.TestConsoleUserInterface;
import de.uka.ilkd.key.smt.test.TestCommons;
import de.uka.ilkd.key.ui.BatchMode;
import de.uka.ilkd.key.ui.UserInterface;

public class TestTestgen extends TestCommons{
	public static final String testFile = System.getProperty("key.home")
	        + File.separator + "examples" + File.separator + "_testcase"
	        + File.separator + "smt" + File.separator + "tg" + File.separator;
	private static final String SYSTEM_PROPERTY_SOLVER_PATH = "z3SolverPath";
	private static boolean isInstalled = false;
	private static boolean installChecked = false;

	@Override
	public boolean toolNotInstalled() {
		if (!installChecked) {
			isInstalled = getSolverType().isInstalled(true);
			installChecked = true;
			if (!isInstalled) {
				System.out.println("Warning: " + getSolverType().getName()
				        + " is not installed, tests skipped.");
				System.out.println("Maybe use JVM system property \""
				        + SYSTEM_PROPERTY_SOLVER_PATH
				        + "\" to define the path to the Z3 command.");
			}
			if (isInstalled && !getSolverType().supportHasBeenChecked()) {
				if (!getSolverType().checkForSupport()) {
					System.out
					        .println("Warning: "
					                + "The version of the solver "
					                + getSolverType().getName()
					                + " used for the following tests may not be supported.");
				}
			}
		}
		return !isInstalled;
	}

	@Override
	public SolverType getSolverType() {
		SolverType type = SolverType.Z3_CE_SOLVER;
		// SolverType type = SolverType.Z3_SOLVER;
		String solverPathProperty = System
		        .getProperty(SYSTEM_PROPERTY_SOLVER_PATH);
		if (solverPathProperty != null && !solverPathProperty.isEmpty()) {
			type.setSolverCommand(solverPathProperty);
		}
		return type;
	}
	
	public void testMiddle(){
		
		UserInterface ui = new TestConsoleUserInterface(new BatchMode("test",
		        false), false);
		KeYMediator mediator = ui.getMediator();
		File file = new File(testFile + "middle.key");
		ui.loadProblem(file);
		try {
			TestGenMacro macro = new TestGenMacro();
			macro.applyTo(mediator, null, null);
			assertEquals(mediator.getSelectedProof().openGoals().size(), 5);
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		
	}

}
