// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.soundness;

import java.util.HashSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.visitor.ProgramVariableCollector;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.Visitor;
import de.uka.ilkd.key.logic.op.NonRigidFunctionLocation;
import de.uka.ilkd.key.logic.op.ProgramVariable;


public class TermProgramVariableCollector extends Visitor {

    private final HashSet result = new HashSet ();
    private final Services services;
    private final boolean collectFunctionLocations;

    
    public TermProgramVariableCollector(Services services, 
                                        boolean collectFunctionLocations) {
        this.services = services;
        this.collectFunctionLocations = collectFunctionLocations;
    }
        
    
    
    public TermProgramVariableCollector(Services services) {
        this(services, false);        
    }
    
    

    /** is called by the execPostOrder-method of a term 
     * @param t the Term to checked if it is a program variable and if true the
     * variable is added to the list of found variables
     */  
    public void visit(Term t) {
	if ( t.op() instanceof ProgramVariable ) {
	    result.add ( t.op() );
	} else if(t.op() instanceof NonRigidFunctionLocation && collectFunctionLocations) {
	    result.add( t.op() );
	}
	
	if ( t.javaBlock () != JavaBlock.EMPTY_JAVABLOCK ) {
	    ProgramVariableCollector pvc
		= new ProgramVariableCollector ( t.javaBlock ().program (), services, collectFunctionLocations );
	    pvc.start();
	    result.addAll ( pvc.result () );
	}
    }

    public HashSet result() { 
	return result;
    }    
}
