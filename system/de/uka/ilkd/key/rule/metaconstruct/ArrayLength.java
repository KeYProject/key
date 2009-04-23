// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class ArrayLength extends ProgramMetaConstruct {
    
     /** creates a typeof ProgramMetaConstruct 
     * @param expr the instance of expression contained by 
     * the meta construct 
     */
    public ArrayLength(Expression expr) {
	super("#length-reference", expr); 
	
    }

    /** performs the program transformation needed for symbolic
     * program transformation 
     * @return the transformated program
     */
    public ProgramElement symbolicExecution(ProgramElement pe,
					    Services services,
					    SVInstantiations insts) {
	return new FieldReference
	    (services.getJavaInfo().getAttribute
	     ("length", ((Expression)pe).getKeYJavaType(services, 
							insts.getExecutionContext())),
	      (ReferencePrefix)pe);
    }
}
