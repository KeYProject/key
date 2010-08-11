// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
//

package de.uka.ilkd.key.gui;

import java.awt.Dimension;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyEvent;

import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JFrame;
import javax.swing.KeyStroke;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.speclang.ClassInvariant;


public class ClassInvariantSelectionDialog extends JDialog {

    private final ClassInvariantSelectionPanel panel;
    private final JButton okButton;
    private final JButton cancelButton;
    
    private boolean successful = false;
    
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    /**
     * Creates and displays a dialog box asking the user to select a set of
     * class invariants.
     */
    public ClassInvariantSelectionDialog(String title,
                                         Services services,
                                         boolean useThroughoutInvs,
                                         KeYJavaType defaultClass) {
        super(new JFrame(), title, true);
        
        //create invariant selection panel
        panel = new ClassInvariantSelectionPanel(services,
                                             	 useThroughoutInvs,
                                             	 defaultClass,
                                             	 true);
        panel.setPreferredSize(new Dimension(800, 500));
        getContentPane().add(panel);
        Dimension buttonDim = new Dimension(100, 27);

        //create "ok" button
        okButton = new JButton("OK");
        okButton.setPreferredSize(buttonDim);
        okButton.setMinimumSize(buttonDim);
        okButton.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                successful = true;
                setVisible(false);
                dispose();
            }
        });
        panel.getButtonPanel().add(okButton);
        getRootPane().setDefaultButton(okButton);

        //create "cancel" button
        cancelButton = new JButton("Cancel");
        cancelButton.setPreferredSize(buttonDim);
        cancelButton.setMinimumSize(buttonDim);
        cancelButton.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                setVisible(false);
                dispose();
            }
        });
        panel.getButtonPanel().add(cancelButton);
        ActionListener escapeListener = new ActionListener() {
            public void actionPerformed(ActionEvent event) {
                if(event.getActionCommand().equals("ESC")) {
                    cancelButton.doClick();
                }
            }
        };
        cancelButton.registerKeyboardAction(
                            escapeListener,
                            "ESC",
                            KeyStroke.getKeyStroke(KeyEvent.VK_ESCAPE, 0),
                            JButton.WHEN_IN_FOCUSED_WINDOW);

        pack();
        setLocation(70, 70);
        setVisible(true);
    }
    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
    
    /**
     * Tells whether the user clicked "ok".
     */
    public boolean wasSuccessful() {
        return successful;
    }

    
    /**
     * Returns the selected set of invariants.
     */
    public ImmutableSet<ClassInvariant> getSelection() {
        return panel.getClassInvariants();
    }
}
