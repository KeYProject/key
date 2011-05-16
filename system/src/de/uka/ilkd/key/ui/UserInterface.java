package de.uka.ilkd.key.ui;

import de.uka.ilkd.key.gui.ProverTaskListener;
import de.uka.ilkd.key.proof.init.ProblemInitializer.ProblemInitializerListener;
import de.uka.ilkd.key.util.ProgressMonitor;

public interface UserInterface extends ProblemInitializerListener,
        ProverTaskListener, ProgressMonitor {

}
