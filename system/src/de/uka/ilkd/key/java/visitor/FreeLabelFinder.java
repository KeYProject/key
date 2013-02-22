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


package de.uka.ilkd.key.java.visitor;

import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.NonTerminalProgramElement;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.statement.LabeledStatement;

/**
 * descends recursively a given program and looks for free occurrences of a specified label
 */
public class FreeLabelFinder {

    public FreeLabelFinder() {            
    }

    public boolean findLabel(Label label, ProgramElement node) {       
        if (!(node instanceof LabeledStatement && 
                ((LabeledStatement)node).getLabel().equals(label))) {
            if (node instanceof NonTerminalProgramElement) {
                final NonTerminalProgramElement nonTerminalNode = 
                    (NonTerminalProgramElement) node;
                for (int i = 0; i<nonTerminalNode.getChildCount(); i++) {                
                    if (nonTerminalNode.getChildAt(i)!=null) {                                      
                        if (findLabel(label, nonTerminalNode.getChildAt(i))) {
                            return true;
                        }
                    }
                }           
            } else if (node instanceof Label) {
                if (node.equals(label)) {
                    return true;
                }
            }
        }
        return false;
    }

}
