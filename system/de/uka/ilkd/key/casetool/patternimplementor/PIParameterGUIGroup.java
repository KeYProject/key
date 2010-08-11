// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.casetool.patternimplementor;

import java.awt.event.ActionEvent;

import javax.swing.BorderFactory;
import javax.swing.BoxLayout;
import javax.swing.JPanel;

public class PIParameterGUIGroup extends PIParameterGUI {

    public PIParameterGUIGroup(PIParameterGroup pip) {
        super(pip);
    }

    protected void buildGUI() {
        content = new JPanel();

        updateGUI();
    }

    public void actionPerformed(ActionEvent e) {
        //Object source = e.getSource();
        //System.out.println("actionPerformed on: " + pip.getName());
    }

    protected void updateGUI() {
        //System.out.println("GUI.updateGUI "+pip.getName());
        content.setVisible(false);

        content.removeAll();
        content.setBorder(BorderFactory.createTitledBorder(pip.getName()));
        this.add(content);
        content.setLayout(new BoxLayout(content, BoxLayout.Y_AXIS));

        for (int i = 0; i < ((PIParameterGroup) pip).size(); i++) {
            if (((PIParameterGroup) pip).get(i) instanceof PIParameterVoid) {
                content.add(new PIParameterGUIVoid(
                        (PIParameterVoid) ((PIParameterGroup) pip).get(i)));
            } else if (((PIParameterGroup) pip).get(i) instanceof PIParameterBoolean) {
                content.add(new PIParameterGUIBoolean(
                        (PIParameterBoolean) ((PIParameterGroup) pip).get(i)));
            } else if (((PIParameterGroup) pip).get(i) instanceof PIParameterString) {
                content.add(new PIParameterGUIString(
                        (PIParameterString) ((PIParameterGroup) pip).get(i)));
            } else if (((PIParameterGroup) pip).get(i) instanceof PIParameterGroup) {
                content.add(new PIParameterGUIGroup(
                        (PIParameterGroup) ((PIParameterGroup) pip).get(i)));
            }
        }

        content.setVisible(true);

        //System.out.println(content);
    }
}
