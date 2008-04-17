// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.encapsulation;

import java.awt.Color;
import java.awt.Dimension;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import javax.swing.*;

import de.uka.ilkd.key.util.Debug;


class UniverseDialog extends JDialog {

    private static final Color COLOR_TRUE      = Color.GREEN;
    private static final Color COLOR_FALSE     = Color.RED;
    private static final Color COLOR_UNDECIDED = Color.LIGHT_GRAY;

    private final ListOfTypeSchemeConstraint constraints;
    private final List /*JLabel*/ constraintLabels;
    

    public UniverseDialog(ListOfTypeSchemeConstraint constraints) {
    	super(new JFrame(), "Universes", true);

        //initialise members
        this.constraints = constraints;
        constraintLabels = new LinkedList();

        //initialise content pane
        getContentPane().setLayout(new BoxLayout(getContentPane(),
                                                 BoxLayout.X_AXIS));

        //create variables panel
        JPanel varsPanel = new JPanel();
        varsPanel.setLayout(new BoxLayout(varsPanel, BoxLayout.Y_AXIS));
        JScrollPane varsPane = new JScrollPane(varsPanel);
        getContentPane().add(varsPane);

        //create variable labels and combo boxes
        SetOfTypeSchemeVariable vars
                = (new TypeSchemeAndConstraint(constraints)).getFreeVars();
        IteratorOfTypeSchemeVariable it = vars.iterator();
        while(it.hasNext()) {
            TypeSchemeVariable var = it.next();

            //prepare values
            SetOfTypeScheme valueRange = var.getValueRange();
            Object[] values = new Object[valueRange.size() + 1];
            values[0] = var.getDefaultValue();
            IteratorOfTypeScheme it2 = valueRange.iterator();
            int i = 1;
            while(it2.hasNext()) {
                values[i++] = it2.next();
            }

            //create variable panel
            JPanel varPanel = new JPanel();
            varPanel.setLayout(new BoxLayout(varPanel, BoxLayout.X_AXIS));
            varsPanel.add(varPanel);

            //create variable label and combo box
            JLabel varLabel = new JLabel(var.toString());
            varLabel.setMinimumSize(new Dimension(200, 20));
            varLabel.setPreferredSize(new Dimension(200, 20));
            varPanel.add(varLabel);
            JComboBox varCombo = new JComboBox(values);
            varCombo.addActionListener(new VarComboListener(var));
            varCombo.setMinimumSize(new Dimension(280, 20));
            varCombo.setPreferredSize(new Dimension(280, 20));
            varPanel.add(varCombo);
        }

        //create constraints panel
        JPanel constraintsPanel = new JPanel();
        constraintsPanel.setLayout(new BoxLayout(constraintsPanel, BoxLayout.Y_AXIS));
        JScrollPane constraintsPane = new JScrollPane(constraintsPanel);
        getContentPane().add(constraintsPane);

        //create constraints labels
        IteratorOfTypeSchemeConstraint it2 = constraints.iterator();
        while(it2.hasNext()) {
            TypeSchemeConstraint constraint = it2.next();

            JLabel constraintLabel = new JLabel(constraint.toString());
            constraintLabels.add(constraintLabel);
            constraintLabel.setOpaque(true);
            constraintsPanel.add(constraintLabel);
        }

        refreshConstraintColors();

        pack();
        setLocation(70, 70);
        setVisible(true);
    }


    private boolean valueIsExact(TypeSchemeConstraint constraint) {
        SetOfTypeSchemeVariable vars = constraint.getFreeVars();
        IteratorOfTypeSchemeVariable it = vars.iterator();
        while(it.hasNext()) {
            if(!it.next().valueIsExact()) {
                return false;
            }
        }
        
        return true;
    }


    private void refreshConstraintColors() {
        IteratorOfTypeSchemeConstraint constraintsIt = constraints.iterator();
        Iterator labelsIt = constraintLabels.iterator();
        while(constraintsIt.hasNext()) {
            Debug.assertTrue(labelsIt.hasNext());
            TypeSchemeConstraint constraint = constraintsIt.next();
            JLabel label = (JLabel) labelsIt.next();
            
            if(!constraint.evaluate()) {
                label.setBackground(COLOR_FALSE);
            } else {
                if(valueIsExact(constraint)) {
                    label.setBackground(COLOR_TRUE);
                } else {
                    label.setBackground(COLOR_UNDECIDED);
                }
            }
        }
    }


    private class VarComboListener implements ActionListener {
        private final TypeSchemeVariable var;
    
        public VarComboListener(TypeSchemeVariable var) {
            this.var = var;
        }
    
        public void actionPerformed(ActionEvent e) {
            JComboBox varCombo = (JComboBox) e.getSource();
            Object newValue = varCombo.getSelectedItem();
            if(newValue instanceof TypeSchemeUnion) {
                var.assignValue((TypeSchemeUnion) newValue);
            } else {
                var.assignValue((TypeScheme) newValue);
            }
            
            refreshConstraintColors();
        }
    }
}
