/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.nodeviews;

import java.awt.event.ComponentEvent;
import java.awt.event.ComponentListener;
import java.awt.event.HierarchyBoundsListener;
import java.awt.event.HierarchyEvent;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;

import de.uka.ilkd.key.gui.MainWindow;

class SequentViewChangeListener
        implements ComponentListener, PropertyChangeListener, HierarchyBoundsListener {

    private final SequentView sequentView;

    SequentViewChangeListener(final SequentView sequentView) {
        this.sequentView = sequentView;
    }

    public void reprint() {
        // reprint sequent
        int lw = sequentView.computeLineWidth();
        if (lw != SequentView.getLineWidth()) {
            // When switching sequents, ancestorResized is called while the sequentView has an empty
            // rect
            // Skip this repaint
            if (!sequentView.getVisibleRect().isEmpty()) {
                SequentView.setLineWidth(lw);
                sequentView.printSequent();
            }

            // Update the search results, they are lost otherwise! (MU)
            // But only update them if we have the correct SequentView
            // (i.e., the main window's sequent view) (lanzinger)
            if (sequentView.isMainSequentView()) {
                MainWindow.getInstance().setSequentView(sequentView);
            }
        }

        sequentView.recalculateUserSelectionRange();
    }

    @Override
    public void componentHidden(ComponentEvent e) {
    }

    @Override
    public void componentMoved(ComponentEvent e) {
    }

    @Override
    public void componentResized(ComponentEvent e) {
        reprint();
    }

    @Override
    public void componentShown(ComponentEvent e) {
    }

    @Override
    public void propertyChange(PropertyChangeEvent evt) {
    }

    @Override
    public void ancestorMoved(HierarchyEvent e) {
    }

    @Override
    public void ancestorResized(HierarchyEvent e) {
        reprint();
    }

}
