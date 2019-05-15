// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.visitor.FreeLabelFinder;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


public final class FreeLabelInVariableCondition 
				extends VariableConditionAdapter {

    private final SchemaVariable label;
    private final SchemaVariable statement;
    private final boolean negated;
    private final FreeLabelFinder freeLabelFinder = new FreeLabelFinder();
    
    public FreeLabelInVariableCondition(SchemaVariable label, SchemaVariable statement, boolean negated) {
        this.label = label;
        this.statement = statement;
        this.negated = negated;
    }
    
    
    @Override
    public boolean check(SchemaVariable var, 
	    		 SVSubstitute instCandidate, 
	    		 SVInstantiations instMap, 
	    		 Services services) {
        Label prgLabel = null;
        ProgramElement program = null;
        
        if (var == label) {
            prgLabel = (Label) instCandidate;
            program = (ProgramElement) instMap.getInstantiation(statement);
        } else if (var == statement) {            
            prgLabel = (Label) instMap.getInstantiation(label);
            program = (ProgramElement) instCandidate;
        } 
        
        if (program == null || prgLabel == null) {
            // not yet complete or not responsible            
            return true;
        }      
        
        final boolean freeIn = freeLabelFinder.findLabel(prgLabel, program);
        return negated ? !freeIn : freeIn;
    }
    
    
    @Override
    public String toString() {
        return (negated ? "\\not" : "") + "\\freeLabelIn (" + label.name() + "," + statement.name() + ")";
    }
}