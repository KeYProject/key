/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.control.event;

import java.util.EventListener;

import de.uka.ilkd.key.control.TermLabelVisibilityManager;

/**
 * Observes changes on a {@link TermLabelVisibilityManager}.
 *
 * @author Martin Hentschel
 */
public interface TermLabelVisibilityManagerListener extends EventListener {
    /**
     * When the visible term labels have changed.
     *
     * @param e The change event.
     */
    public void visibleLabelsChanged(TermLabelVisibilityManagerEvent e);
}
