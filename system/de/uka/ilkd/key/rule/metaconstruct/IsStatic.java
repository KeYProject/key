// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
//
//

package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.java.reference.VariableReference;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


public class IsStatic extends ProgramMetaConstruct{

    /** creates a typeof ProgramMetaConstruct 
     * @param pe the instance of expression contained by 
     * the meta construct 
     */
    public IsStatic(ProgramElement pe) {
	super("#isstatic", pe); 
    }


    /** performs the program transformation needed for symbolic
     * program execution 
     * @param services the Services with all necessary information 
     * about the java programs
     * @param svInst the instantiations esp. of the inner and outer label 
     * @return the transformed program
     */
    public ProgramElement symbolicExecution(ProgramElement pe,
					    Services services,
					    SVInstantiations svInst) {
	if(pe instanceof VariableReference){
	    if(((VariableReference) pe).getProgramVariable().isStatic()){
		return BooleanLiteral.TRUE;
	    }
	}
	return BooleanLiteral.FALSE;
    }
}

	
