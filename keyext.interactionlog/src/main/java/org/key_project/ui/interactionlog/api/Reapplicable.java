/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

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
