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


package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.PassiveExpression;
import de.uka.ilkd.key.java.recoderext.ClassInitializeMethodBuilder;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Debug;


public class StaticInitialisation extends ProgramTransformer {
    
    public StaticInitialisation(Expression expr) {
	super("static-initialisation", expr); 
	
    }

    /** performs the program transformation needed for symbolic
     * program transformation 
     * @return the transformated program
     */
    public ProgramElement transform(ProgramElement pe,
					    Services services,
					    SVInstantiations insts) {	
	KeYJavaType typeToBeInitialised = null;
	if (pe instanceof FieldReference) {	  
	    final ProgramVariable pv = ((FieldReference)pe).getProgramVariable(); 
	    if (pv.isStatic()) {
		typeToBeInitialised = pv.getContainerType();
	    } else {
		return null; // no static initialisation necessary
	    }
	} else if (pe instanceof ProgramVariable) {
	    final ProgramVariable pv = (ProgramVariable)pe;
	    if (pv.isStatic()) {
		typeToBeInitialised = pv.getContainerType();
	    }  else {
		return null; // no static initialisation necessary
	    }
	} else if (pe instanceof MethodReference) {
	    final MethodReference mr = (MethodReference)pe;
	    final ExecutionContext ec = 
                insts.getContextInstantiation().activeStatementContext(); 
	    final IProgramMethod m;
	    final KeYJavaType mrPrefixType = 
	        mr.determineStaticPrefixType(services, ec);
	    if (ec == null) {
	        // in this case we are at the top level of a diamond
	        // in this case we assume as scope the type of the method prefix
	        m  = mr.method(services, mrPrefixType, 
	                mr.getMethodSignature(services, null), mrPrefixType);	               
	    } else {
	        m  = mr.method(services, 
	                mr.determineStaticPrefixType(services, ec), 
	                ec);
	    }
	    if (m != null) {
		if (m.isStatic()) {
		    typeToBeInitialised = m.getContainerType();
		} else {
		    return null; // no static initialisation necessary
		}
	    }

	} else {
	    // at the moment the 'new' case is catched via static method 
	    // call of <createObject>
	    Debug.fail("static initialisation: Unexpected case in static initialisation.");
	}

	if (typeToBeInitialised == null) {
	    Debug.fail("static initialisation failed");
	    return null;
	}

 	return new PassiveExpression(new MethodReference
 	    (new ImmutableArray<Expression>(), 
	     new ProgramElementName
	     (ClassInitializeMethodBuilder.CLASS_INITIALIZE_IDENTIFIER),
 	     new TypeRef(typeToBeInitialised)));
    }
}
