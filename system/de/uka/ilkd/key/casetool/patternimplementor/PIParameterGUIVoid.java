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

import javax.swing.JLabel;

public class PIParameterGUIVoid extends PIParameterGUI {

    public PIParameterGUIVoid(PIParameterVoid pip) {
        super(pip);
    }

    protected void buildGUI() {
        this.setLayout(new GridLayout(1, 2));
        this.add(new JLabel(pip.getName()));
    }

    public void actionPerformed(ActionEvent e) {
    }
}
