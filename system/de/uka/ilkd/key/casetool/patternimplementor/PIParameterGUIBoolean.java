// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.casetool.patternimplementor;

import java.awt.GridLayout;
import java.awt.event.ActionEvent;

import javax.swing.JCheckBox;
import javax.swing.JLabel;

public class PIParameterGUIBoolean extends PIParameterGUI {

    public PIParameterGUIBoolean(PIParameterBoolean pip) {
        super(pip);
    }

    protected void buildGUI() {
        this.setLayout(new GridLayout(1, 2));
        this.add(new JLabel(pip.getName()));
        content = new JCheckBox();
        ((JCheckBox) content).setSelected(pip.getValue().equals("true"));
        ((JCheckBox) content).addActionListener(this);
        this.add(content);
        updateGUI();
    }

    public void actionPerformed(ActionEvent e) {
        Object source = e.getSource();

        //System.out.println("actionPerformed on: " + pip.getName());

        ((PIParameterBoolean) pip).setValue(""
                + ((JCheckBox) source).isSelected());
    }
}
