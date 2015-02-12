package de.uka.ilkd.key.smt.ce;

import java.io.File;

import junit.framework.Assert;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.macros.FinishSymbolicExecutionMacro;
import de.uka.ilkd.key.macros.SemanticsBlastingMacro;
import de.uka.ilkd.key.macros.TryCloseMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.smt.SolverType;
import de.uka.ilkd.key.smt.TestConsoleUserInterface;
import de.uka.ilkd.key.smt.test.TestCommons;
import de.uka.ilkd.key.ui.BatchMode;
import de.uka.ilkd.key.ui.UserInterface;

public class TestCE extends TestCommons {
	public static final String testFile = System.getProperty("key.home")
	        + File.separator + "examples" + File.separator + "_testcase"
	        + File.separator + "smt" + File.separator + "ce" + File.separator;
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

	public void testOverFlow1() {
		assertTrue(this.correctResult(testFile + "overflow1.key", true));
	}

	public void testOverFlow2() {
		assertTrue(this.correctResult(testFile + "overflow2.key", true));
	}

	public void testTypes1() {
		assertTrue(this.correctResult(testFile + "types1.key", true));
	}

	public void testTypes2() {
		assertTrue(this.correctResult(testFile + "types2.key", true));
	}

	public void testTypes3() {
		assertTrue(this.correctResult(testFile + "types3.key", false));
	}

	public void testTypes4() {
		assertTrue(this.correctResult(testFile + "types4.key", true));
	}

	public void testTypes5() {
		assertTrue(this.correctResult(testFile + "types5.key", false));
	}

	public void testTypes6() {
		assertTrue(this.correctResult(testFile + "types6.key", true));
	}

	public void testTypes7() {
		assertTrue(this.correctResult(testFile + "types7.key", true));
	}

	public void testTypes8() {
		assertTrue(this.correctResult(testFile + "types8.key", true));
	}

	public void testTypes9() {
		assertTrue(this.correctResult(testFile + "types9.key", true));
	}

	public void testMiddle() {
		UserInterface ui = new TestConsoleUserInterface(new BatchMode("test",
		        false), false);
		KeYMediator mediator = ui.getMediator();
		File file = new File(testFile + "middle.key");
		ui.loadProblem(file);
		try {
			FinishSymbolicExecutionMacro se = new FinishSymbolicExecutionMacro();
			se.applyTo(mediator, null, null);
			TryCloseMacro close = new TryCloseMacro();
			close.applyTo(mediator, null, null);
			// should not be provable
			assertTrue(ui.getMediator().getSelectedProof().openGoals().size() > 0);
			// there should be a counterexample for each goal...
			for (Goal g : ui.getMediator().getSelectedProof().openGoals()) {
				mediator.getSelectionModel().setSelectedGoal(g);
				SemanticsBlastingMacro sb = new SemanticsBlastingMacro();
				sb.applyTo(mediator, null, null);
				Assert.assertTrue(correctResult(mediator.getSelectedGoal(),
				        false));
			}
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
	}
}
