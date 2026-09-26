/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.nodeviews;

import de.uka.ilkd.key.gui.MainWindow;

/**
 * Use this class in case no proof is loaded.
 *
 * @author Kai Wallisch
 */
public class EmptySequent extends SequentView {
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
