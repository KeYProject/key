package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.core.TaskFinishedInfo;
import de.uka.ilkd.key.ui.BatchMode;
import de.uka.ilkd.key.ui.ConsoleUserInterface;
/**
 * This class is used for loading key proofs only, but not exiting afterwards.
 * @author mihai
 *
 */
public class TestConsoleUserInterface extends ConsoleUserInterface{

	public TestConsoleUserInterface(BatchMode batchMode, boolean verbose) {
		super(batchMode, verbose);
	}

	@Override
	public void taskFinished(TaskFinishedInfo info) {}

}
