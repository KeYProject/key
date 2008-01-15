// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.metaconstruct;

import java.util.HashMap;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.declaration.MethodDeclaration;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.visitor.ProgVarReplaceVisitor;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class ExpandMethodBody extends ProgramMetaConstruct {

    static int counter = 0;

    public ExpandMethodBody(SchemaVariable sv) {
        super(new Name("expand-method-body"), (ProgramSV)sv);
    }

    public ExpandMethodBody(Statement mb) {
        super(new Name("expand-method-body"), mb);
    }

    /** 
     * Replaces the MethodBodyStatement shortcut with the full body,
     * performs prefix adjustments in the body (execution context).
     * @param services the Services with all necessary information 
     * about the java programs
     * @param svInst the instantiations esp. of the inner and outer label 
     * @return the transformed program
     */
    public ProgramElement symbolicExecution(ProgramElement pe,
					    Services services,
					    SVInstantiations svInst) {

	MethodBodyStatement mbs = (MethodBodyStatement) pe;
	//        MethodReference mr = mbs.getMethodReference();

        ProgramMethod pm = mbs.getProgramMethod(services);
	//mr.method(services, mbs.getBodySource());

	MethodDeclaration methDecl = pm.getMethodDeclaration();
	


	StatementBlock result = (StatementBlock) mbs.getBody(services);	
	ReferencePrefix newCalled = mbs.getDesignatedContext();
	if (newCalled instanceof TypeReference) {
	    // static method
	    newCalled = null;
	}
	TypeReference classContext = new TypeRef(mbs.getBodySource());

// removed this again. see bugs #437,#479 -- vladimir
//	result = prettyNewObjectNames(result, methDecl, classContext);

	// at this point all arguments should be program variables
	ArrayOfExpression argsAsParam = mbs.getArguments();

	HashMap map = new HashMap();
	for (int i = 0; i < argsAsParam.size(); i++) {
	    map.put(methDecl.getParameterDeclarationAt(i).
		    getVariableSpecification().getProgramVariable(), 
		    argsAsParam.getExpression(i));
	}
	ProgVarReplaceVisitor paramRepl = 
	    new ProgVarReplaceVisitor(result, map); 
	paramRepl.start();	
	result = (StatementBlock) paramRepl.result();

        return 
	    new MethodFrame(mbs.getResultVariable(),
			    new ExecutionContext(classContext, newCalled),
			    result,
                            pm, PositionInfo.UNDEFINED); 
    }

}
