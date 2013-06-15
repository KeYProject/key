// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

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