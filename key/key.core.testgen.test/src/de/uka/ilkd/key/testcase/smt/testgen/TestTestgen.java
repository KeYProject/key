package de.uka.ilkd.key.testcase.smt.testgen;

import java.io.File;

import org.junit.Test;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.macros.TestGenMacro;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.smt.SolverType;
import de.uka.ilkd.key.smt.test.TestCommons;
import de.uka.ilkd.key.suite.util.HelperClassForTestgenTests;

public class TestTestgen extends TestCommons{
	public static final String testFile = HelperClassForTestgenTests.TESTCASE_DIRECTORY
	        + File.separator + "smt" + File.separator + "tg" + File.separator;
	private static final String SYSTEM_PROPERTY_SOLVER_PATH = "z3SolverPath";
	private static boolean isInstalled = false;
	private static boolean installChecked = false;

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
	
	@Test
	public void testMiddle() throws Exception {
		File file = new File(testFile + "middle.key");
		assertTrue(file.exists());
		KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(file, null, null);
		try {
		   Proof proof = env.getLoadedProof();
		   assertNotNull(proof);
			TestGenMacro macro = new TestGenMacro();
			macro.applyTo(env.getUi(), proof, proof.openEnabledGoals(), null, null);
			assertEquals(proof.openGoals().size(), 5);
		}
		finally {
		   if (env != null) {
	         env.dispose();
		   }
		}
	}

}
