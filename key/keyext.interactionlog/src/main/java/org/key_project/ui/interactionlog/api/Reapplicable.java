package org.key_project.ui.interactionlog.api;

import de.uka.ilkd.key.gui.WindowUserInterfaceControl;
import de.uka.ilkd.key.proof.Goal;

/**
 * @author Alexander Weigl
 * @version 1 (08.05.19)
 */
public interface Reapplicable {
    default void reapply(WindowUserInterfaceControl uic, Goal goal) throws Exception {
        throw new UnsupportedOperationException();
    }
}
