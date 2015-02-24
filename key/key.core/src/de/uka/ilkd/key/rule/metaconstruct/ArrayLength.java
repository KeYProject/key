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

package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class ArrayLength extends ProgramTransformer {
    
     /** creates a typeof ProgramTransformer 
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
    public ProgramElement transform(ProgramElement pe,
					    Services services,
					    SVInstantiations insts) {
	return KeYJavaASTFactory.fieldReference(services, "length",
		(Expression) pe, insts.getExecutionContext());
    }
}