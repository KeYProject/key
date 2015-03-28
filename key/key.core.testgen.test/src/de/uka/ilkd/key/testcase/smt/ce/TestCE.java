package de.uka.ilkd.key.testcase.smt.ce;

import java.io.File;

import org.junit.Test;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.macros.FinishSymbolicExecutionMacro;
import de.uka.ilkd.key.macros.SemanticsBlastingMacro;
import de.uka.ilkd.key.macros.TryCloseMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.smt.SolverType;
import de.uka.ilkd.key.smt.test.TestCommons;
import de.uka.ilkd.key.suite.util.HelperClassForTestgenTests;

public class TestCE extends TestCommons {
	public static final String testFile = HelperClassForTestgenTests.TESTCASE_DIRECTORY
	        + File.separator + "smt" + File.separator + "ce" + File.separator;
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
	public void testOverFlow1() throws Exception {
		assertTrue(this.correctResult(testFile + "overflow1.key", true));
	}

   @Test
	public void testOverFlow2() throws Exception {
		assertTrue(this.correctResult(testFile + "overflow2.key", true));
	}

   @Test
	public void testTypes1() throws Exception {
		assertTrue(this.correctResult(testFile + "types1.key", true));
	}

   @Test
	public void testTypes2() throws Exception {
		assertTrue(this.correctResult(testFile + "types2.key", true));
	}

   @Test
	public void testTypes3() throws Exception {
		assertTrue(this.correctResult(testFile + "types3.key", false));
	}

   @Test
	public void testTypes4() throws Exception {
		assertTrue(this.correctResult(testFile + "types4.key", true));
	}

   @Test
	public void testTypes5() throws Exception {
		assertTrue(this.correctResult(testFile + "types5.key", false));
	}

   @Test
	public void testTypes6() throws Exception {
		assertTrue(this.correctResult(testFile + "types6.key", true));
	}

   @Test
	public void testTypes7() throws Exception {
		assertTrue(this.correctResult(testFile + "types7.key", true));
	}

   @Test
	public void testTypes8() throws Exception {
		assertTrue(this.correctResult(testFile + "types8.key", true));
	}

   @Test
	public void testTypes9() throws Exception {
		assertTrue(this.correctResult(testFile + "types9.key", true));
	}

   @Test
	public void testMiddle() throws Exception {
		File file = new File(testFile + "middle.key");
		KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(file, null, null);
		try {
		   Proof proof = env.getLoadedProof();
		   assertNotNull(proof);
			FinishSymbolicExecutionMacro se = new FinishSymbolicExecutionMacro();
			se.applyTo(env.getUi(), proof, proof.openEnabledGoals(), null, null);
			TryCloseMacro close = new TryCloseMacro();
			close.applyTo(env.getUi(), proof, proof.openEnabledGoals(), null, null);
			// should not be provable
			assertTrue(proof.openGoals().size() > 0);
			// there should be a counterexample for each goal...
			for (Goal g : proof.openGoals()) {
				SemanticsBlastingMacro sb = new SemanticsBlastingMacro();
				sb.applyTo(env.getUi(), g.node(), null, null);
				assertTrue(correctResult(g, false));
			}
		}
		finally {
		   if (env != null) {
		      env.dispose();
		   }
		}
	}
}
