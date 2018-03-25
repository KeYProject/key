// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui.nodeviews;

import java.awt.event.ComponentEvent;
import java.awt.event.ComponentListener;
import java.awt.event.HierarchyBoundsListener;
import java.awt.event.HierarchyEvent;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;

import de.uka.ilkd.key.gui.MainWindow;

class SequentViewChangeListener implements ComponentListener, PropertyChangeListener, HierarchyBoundsListener {

    private final SequentView sequentView;

    SequentViewChangeListener(final SequentView sequentView) {
        this.sequentView = sequentView;
    }

    public void reprint() {
        // reprint sequent
        int lw = sequentView.computeLineWidth();
        if (lw != SequentView.getLineWidth()) {
            SequentView.setLineWidth(lw);
            sequentView.printSequent();
            // Update the search results, they are lost otherwise! (MU)
            MainWindow.getInstance().sequentViewSearchBar.setSequentView(sequentView);
        }
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
        reprint();
    }

    @Override
    public void ancestorMoved(HierarchyEvent e) {
    }

    @Override
    public void ancestorResized(HierarchyEvent e) {
        reprint();
    }

}