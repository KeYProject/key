// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.gui;

import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.Arrays;
import java.util.Comparator;

import javax.swing.*;
import javax.swing.border.TitledBorder;

import de.uka.ilkd.key.casetool.*;


/**
 * A dialog for selecting classes (including interfaces).
 */
public class ClassSelectionDialog extends JDialog {
    
    private boolean successful = false;
    private JList classList;
    
    
    /**
     * Creates and displays a dialog box asking the user to make a choice from 
     * a set of classes.
     * @param windowTitle Title for the dialog window.
     * @param classesTitle Title for the list of available classes.
     * @param modelClasses The available classes.
     * @param allowMultipleSelection Whether multiple classes or a single class 
     * are to be selected
     */
    public ClassSelectionDialog(String dialogTitle,
                                String classesTitle,
                                ListOfModelClass modelClasses,
                                ModelClass defaultClass,
                                boolean allowMultipleSelection) {
        super(new JFrame(), dialogTitle, true);
        
        //create type list
        classList = new JList();
        if(allowMultipleSelection) {
            classList.setSelectionMode(
                                ListSelectionModel.MULTIPLE_INTERVAL_SELECTION);
        } else {
            classList.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
        }
        ModelClass[] classesArray = modelClasses.toArray();
        Arrays.sort(classesArray, new Comparator() {
            public int compare(Object o1, Object o2) {
                ModelClass mc1 = (ModelClass)o1;
                ModelClass mc2 = (ModelClass)o2;
                return mc1.getClassName().compareTo(mc2.getClassName());
            }
        });
        classList.setListData(classesArray);
                
        //select default class
        if(defaultClass != null) {
            String defaultName = defaultClass.getFullClassName();
            IteratorOfModelClass it = modelClasses.iterator();
            while(it.hasNext()) {
                ModelClass modelClass = it.next();
                if(modelClass.getFullClassName().equals(defaultName)) {
                    classList.setSelectedValue(modelClass, true);
                    break;
                }
            }
        }
        
        //create type scroll pane
        JScrollPane typeScrollPane = new JScrollPane(classList);
        typeScrollPane.setBorder(new TitledBorder(classesTitle));
        Dimension typeScrollPaneDim = new Dimension(275, 300);
        typeScrollPane.setPreferredSize(typeScrollPaneDim);
        typeScrollPane.setMinimumSize(typeScrollPaneDim);
        getContentPane().add(typeScrollPane);
    
        //create button panel
        JPanel buttonPanel = new JPanel();
        buttonPanel.setLayout(new FlowLayout(FlowLayout.RIGHT, 5, 5));
        getContentPane().add(buttonPanel);
        Dimension buttonDim = new Dimension(80, 25);
    
        //create "ok" button
        JButton okButton = new JButton("OK");
        okButton.setPreferredSize(buttonDim);
        okButton.setMinimumSize(buttonDim);
        okButton.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                successful = true;
                setVisible(false);
            }
        });
        buttonPanel.add(okButton);
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
        buttonPanel.add(cancelButton);
        
        getContentPane().setLayout(new BoxLayout(getContentPane(), 
                                                 BoxLayout.Y_AXIS));
        pack();
        setLocation(70, 70);
        setVisible(true);
    }
    
    
    public ClassSelectionDialog(String dialogTitle,
                                String classesTitle,
                                ListOfModelClass modelClasses,
                                boolean allowMultipleSelection) {
        this(dialogTitle, 
             classesTitle, 
             modelClasses, 
             null, 
             allowMultipleSelection);
    }
        
        
    /**
     * Tells whether the user clicked "ok".
     */
    public boolean wasSuccessful() {
        return successful;
    }

    
    /**
     * Returns the selected classes.
     */
    public ListOfModelClass getSelection() {
        Object[] selectedClasses = classList.getSelectedValues();
        
        ListOfModelClass result = SLListOfModelClass.EMPTY_LIST;
        for(int i = selectedClasses.length - 1; i >= 0; i--) {
            result = result.prepend((UMLModelClass) selectedClasses[i]);
        }
        
        return result;
    }
}
