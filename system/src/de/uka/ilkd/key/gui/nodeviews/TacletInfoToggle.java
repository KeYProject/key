/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.gui.nodeviews;

import javax.swing.JCheckBox;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

/**
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class TacletInfoToggle extends JCheckBox {

    InnerNodeView leafNodeView = null;

    public TacletInfoToggle() {
        setText("Show taclet info (Inner Nodes only)");
        addChangeListener(new ChangeListener() {
            public void stateChanged(ChangeEvent e) {
                leafNodeView.tacletInfo.setVisible(isSelected());
            }
        });
        setVisible(false);
    }

    public void setSequentView(SequentView sequentView) {
        if (sequentView instanceof InnerNodeView) {
            leafNodeView = (InnerNodeView) sequentView;
            setVisible(true);
            leafNodeView.tacletInfo.setVisible(isSelected());
        } else {
            leafNodeView = null;
            setVisible(false);
        }
    }
}
