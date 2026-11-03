/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.nodeviews;

import de.uka.ilkd.key.gui.MainWindow;

import org.jspecify.annotations.NullMarked;

/**
 * Use this class in case no proof is loaded.
 *
 * @author Kai Wallisch
 */
@NullMarked
public class EmptySequent extends SequentView {
    /**
     * The empty sequent colors itself while the receiver is still under initialization (EISOP
     * initialization check); the color is only read by the look and feel after construction,
     * suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:method.invocation.invalid")
    public EmptySequent(MainWindow mainWindow) {
        super(mainWindow);
        setBackground(INACTIVE_BACKGROUND_COLOR);
    }

    @Override
    public void updateUI() {
        super.updateUI();
        setBackground(INACTIVE_BACKGROUND_COLOR);
    }

    @Override
    public String getTitle() {
        return "No proof loaded";
    }

    @Override
    public void printSequent() {
    }

}
