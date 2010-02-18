// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.casetool.patternimplementor;

import java.awt.Dimension;
import java.awt.GridLayout;
import java.awt.event.ActionEvent;
import java.awt.event.FocusEvent;
import java.awt.event.FocusListener;

import javax.swing.JLabel;
import javax.swing.JTextField;

public class PIParameterGUIString extends PIParameterGUI implements
        FocusListener {

    public PIParameterGUIString(PIParameterString pip) {
        super(pip);
    }

    public void focusGained(FocusEvent e) {
    }

    public void focusLost(FocusEvent e) {
        //System.out.println(e);
        Object source = e.getSource();
        ((PIParameterString) pip).setValue(((JTextField) source).getText());
    }

    protected void buildGUI() {
        this.setLayout(new GridLayout(1, 2));
        this.add(new JLabel(pip.getName()));
        content = new JTextField();
        ((JTextField) content).addActionListener(this);
        content.addFocusListener(this);

        //((JTextField)content).getDocument().addDocumentListener(this);
        content.setPreferredSize(new Dimension(200, 20));
        this.add(content);
        updateGUI();
    }

    public void actionPerformed(ActionEvent e) {
        Object source = e.getSource();

        //System.out.println("actionPerformed on: " + pip.getName());

        ((PIParameterString) pip).setValue(((JTextField) source).getText());
    }

    protected void updateGUI() {
        //System.out.println("GUI.updateGUI "+pip.getName());
        ((JTextField) content).setText(pip.getValue());
    }
}
