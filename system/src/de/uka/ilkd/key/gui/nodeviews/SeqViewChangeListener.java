
package de.uka.ilkd.key.gui.nodeviews;

import java.awt.event.ComponentEvent;
import java.awt.event.ComponentListener;
import java.awt.event.HierarchyBoundsListener;
import java.awt.event.HierarchyEvent;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;

class SeqViewChangeListener implements ComponentListener, PropertyChangeListener, HierarchyBoundsListener {
    
    private final SequentView sequentView;

    SeqViewChangeListener(final SequentView sequentView) {
        this.sequentView = sequentView;
    }

    public void reprintOnLineWidthChange() {
        // reprint sequent
        int lw = sequentView.computeLineWidth();
        if (lw != SequentView.getLineWidth()) {
            SequentView.setLineWidth(lw);
            sequentView.printSequent();
        }
    }

    public void componentHidden(ComponentEvent e) {
    }

    public void componentMoved(ComponentEvent e) {
    }

    public void componentResized(ComponentEvent e) {
        reprintOnLineWidthChange();
    }

    public void componentShown(ComponentEvent e) {
    }

    public void propertyChange(PropertyChangeEvent evt) {
        // reprint sequent
        sequentView.printSequent();
    }

    public void ancestorMoved(HierarchyEvent e) {
    }

    public void ancestorResized(HierarchyEvent e) {
        reprintOnLineWidthChange();
    }
    
}
