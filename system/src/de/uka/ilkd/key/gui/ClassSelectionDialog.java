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


package de.uka.ilkd.key.gui;

import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.Arrays;
import java.util.Comparator;
import java.util.Vector;

import javax.swing.*;
import javax.swing.border.TitledBorder;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.abstraction.ClassType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;


/**
 * A dialog for selecting classes (including interfaces).
 */
public class ClassSelectionDialog extends JDialog {
    
    /**
     * 
     */
    private static final long serialVersionUID = -7369508044709282573L;
    private boolean successful = false;
    private JList classList;
    
    
    /**
     * Creates and displays a dialog box asking the user to make a choice from 
     * a set of classes.
     * @param dialogTitle Title for the dialog window.
     * @param classesTitle Title for the list of available classes.
     * @param kjts The available types.
     * @param defaultClass Default selection.
     * @param allowMultipleSelection Whether multiple classes or a single class 
     * are to be selected
     */
    public ClassSelectionDialog(String dialogTitle,
                                String classesTitle,
                                ImmutableSet<KeYJavaType> kjts,
                                KeYJavaType defaultClass,
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
        Vector<WrappedKJT> v = new Vector<WrappedKJT>();
        for (final KeYJavaType kjt : kjts) {
            if(kjt.getJavaType() instanceof ClassType) {
        	v.add(new WrappedKJT(kjt));
            }
        }
        WrappedKJT[] listData = v.toArray(new WrappedKJT[v.size()]);
        Arrays.sort(listData, new Comparator<WrappedKJT>() {
            public int compare(WrappedKJT o1, WrappedKJT o2) {
                KeYJavaType kjt1 = o1.kjt;
                KeYJavaType kjt2 = o2.kjt;
                return kjt1.getName().compareTo(kjt2.getName());
            }
        });
        classList.setListData(listData);

        //select default class
        if(defaultClass != null) {
            classList.setSelectedValue(defaultClass, true);
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
        Dimension buttonDim = new Dimension(100, 27);
        getContentPane().add(buttonPanel);
    
        //create "ok" button
        JButton okButton = new JButton("OK");
        okButton.setPreferredSize(buttonDim);
        okButton.setMinimumSize(buttonDim);
        okButton.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                successful = true;
                setVisible(false);
                dispose();
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
                dispose();
            }
        });
        buttonPanel.add(cancelButton);
        
        //show
        getContentPane().setLayout(new BoxLayout(getContentPane(), 
                                                 BoxLayout.Y_AXIS));
        pack();
        setLocation(70, 70);
        setVisible(true);
    }
    
    
    public ClassSelectionDialog(String dialogTitle,
                                String classesTitle,
                                ImmutableSet<KeYJavaType> kjts,
                                boolean allowMultipleSelection) {
        this(dialogTitle, 
             classesTitle, 
             kjts, 
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
    public ImmutableSet<KeYJavaType> getSelection() {
        Object[] selection = classList.getSelectedValues();
        
        ImmutableSet<KeYJavaType> result = DefaultImmutableSet.<KeYJavaType>nil();
        for(int i = selection.length - 1; i >= 0; i--) {
            result = result.add(((WrappedKJT) selection[i]).kjt);
        }
        
        return result;
    }
    
    
    
    private static class WrappedKJT {
	public final KeYJavaType kjt;
	
	public WrappedKJT(KeYJavaType kjt) {
	    this.kjt = kjt;
	}
	
	public String toString() {
	    return kjt.getFullName();
	}
    }
}
