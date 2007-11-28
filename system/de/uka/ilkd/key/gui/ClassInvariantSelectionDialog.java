// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.

package de.uka.ilkd.key.gui;

import java.awt.Dimension;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.Set;

import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JFrame;
import javax.swing.JPanel;

import de.uka.ilkd.key.casetool.ModelClass;
import de.uka.ilkd.key.speclang.ListOfClassInvariant;

public class ClassInvariantSelectionDialog extends JDialog {


    private boolean successful = false;
    private ClassInvariantSelectionPanel panel;

    /**
     * Creates and displays a dialog box asking the user to select a set of
     * invariants.
     * @param modelClasses the classes to choose invariants from
     */
    public ClassInvariantSelectionDialog(String title,
                                         Set modelClasses,
                                         boolean useThroughoutInvs,
                                         ModelClass defaultClass) {
        super(new JFrame(), title, true);
        panel
          = new ClassInvariantSelectionPanel(modelClasses,
                                             useThroughoutInvs,
                                             defaultClass,
                                             true);
        JPanel rightButtonPanel = panel.getButtonPanel();

        Dimension buttonDim = new Dimension(95, 25);

        //      create "ok" button
        JButton okButton = new JButton("OK");
        okButton.setPreferredSize(buttonDim);
        okButton.setMinimumSize(buttonDim);
        okButton.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                successful = true;
                setVisible(false);
            }
        });
        rightButtonPanel.add(okButton);
        getRootPane().setDefaultButton(okButton);

        //create "cancel" button
        JButton cancelButton = new JButton("Cancel");
        cancelButton.setPreferredSize(buttonDim);
        cancelButton.setMinimumSize(buttonDim);
        cancelButton.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                setVisible(false);
            }
        });
        rightButtonPanel.add(cancelButton);


        getContentPane().add(panel);
        pack();
        setLocation(70, 70);
        setVisible(true);
    }

    /**
     * Tells whether the user clicked "ok".
     */
    public boolean wasSuccessful() {
        return successful;
    }

    /**
     * Returns the selected set of invariants.
     */
    public ListOfClassInvariant getClassInvariants() {
        return panel.getClassInvariants();
    }
}
