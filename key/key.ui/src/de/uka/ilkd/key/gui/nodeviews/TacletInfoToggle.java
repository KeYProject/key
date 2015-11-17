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

import javax.swing.JCheckBox;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

/**
 * {@link JCheckBox} indicating whether taclet info is displayed for inner nodes
 * in proof tree.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class TacletInfoToggle extends JCheckBox {

    private static final long serialVersionUID = 8129996113987285946L;
    InnerNodeView innerNodeView = null;

    public TacletInfoToggle() {
        setText("Show taclet info (Inner Nodes only)");
        addChangeListener(new ChangeListener() {
            @Override
            public void stateChanged(ChangeEvent e) {
                if (innerNodeView != null) {
                    innerNodeView.tacletInfo.setVisible(isSelected());
                }
            }
        });
        setVisible(false);
        setName(this.getClass().getSimpleName());
    }

   @Override
   public void setSelected(boolean b) {
      super.setSelected(b);
      if (innerNodeView != null) {
         innerNodeView.tacletInfo.setVisible(isSelected());
      }
   }

   public void setSequentView(SequentView sequentView) {
        if (sequentView instanceof InnerNodeView) {
            innerNodeView = (InnerNodeView) sequentView;
            setVisible(true);
            innerNodeView.tacletInfo.setVisible(isSelected());
        } else {
            innerNodeView = null;
            setVisible(false);
        }
    }
}