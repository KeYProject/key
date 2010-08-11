// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.java.visitor;

import java.util.HashSet;

import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;

/**
 * Collects all labels found in a given program.
 */
public class LabelCollector extends JavaASTVisitor {

    private HashSet<Label> labels;
    
    public LabelCollector(ProgramElement root,                           
                          Services services) {
        super(root, services);        
        this.labels = new HashSet<Label>(20);
    }
    
    public boolean contains(Label l) {
        return labels.contains(l);
    }
    
    protected void doDefaultAction(SourceElement node) {        
        if (node instanceof Label) {
            labels.add((Label) node);           
        }
    }

    protected void doAction(ProgramElement node) {  
        if (node instanceof Label) {
            labels.add((Label) node);
        }
    }

}
