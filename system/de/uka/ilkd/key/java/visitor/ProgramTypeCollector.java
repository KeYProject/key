// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.java.visitor;

import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.util.Debug;


/** 
 * Walks through a java AST in depth-left-fist-order. 
 * This walker is used to collect all Types in a program.
 */
public class ProgramTypeCollector extends JavaASTVisitor {

    private HashSet result = new HashSet();
    private HashSet programMethods = new HashSet();
    private KeYJavaType type;
    private ProgramVariable self;
    private Set alreadyVisitedProgramMethods;
    
    public ProgramTypeCollector(ProgramElement root, ProgramVariable self, 
				KeYJavaType type, Services services,
				Set alreadyVisitedProgramMethods) {
	super(root, services);
	this.type = type;
	this.self=self;
	this.alreadyVisitedProgramMethods =
	    alreadyVisitedProgramMethods;
    }

    /** starts the walker*/
    public void start() {	
	walk(root());	
    }

    public HashSet getResult() { 
	return result;
    }    

    public HashSet getProgramMethods() {
	return programMethods;
    }
    
    public String toString() {
	return result.toString();
    }


    public void performActionOnTypeReference(TypeReference x) {
	result.add(x.getKeYJavaType());
    }


    public void performActionOnMethodReference(MethodReference x) {
	MethodReference currentMR = x;
	ProgramVariable currentSelf = self;
	KeYJavaType currentType = type;
	ReferencePrefix referencePre = currentMR.getReferencePrefix();

	if (referencePre != null) {
	    if (referencePre instanceof ProgramVariable) {
		currentSelf = (ProgramVariable) referencePre;
		currentType = currentSelf.getKeYJavaType();
	    }
	    if (referencePre instanceof TypeReference) {
		currentType = ((TypeReference) referencePre).
		    getKeYJavaType();
		currentSelf = new LocationVariable
		    (new ProgramElementName("x_" + 
					    referencePre.toString()),
		     currentType);
	    }
	    if (referencePre instanceof Expression) {
		currentType = services.getTypeConverter().getKeYJavaType
		    ((Expression) referencePre,
		     new ExecutionContext(new TypeRef(type), null, new RuntimeInstanceEC(self)));
		currentSelf = new LocationVariable
		    (new ProgramElementName("x_" + 
					    referencePre.toString()),
		     currentType);		   
	    }
	
	    ImmutableList<KeYJavaType> imps = 
		services.getJavaInfo().getKeYProgModelInfo()
		.findImplementations
		(currentType,
		 currentMR.getMethodName().toString(),
		 currentMR.getMethodSignature
		 (services,
		  new ExecutionContext(new TypeRef(currentType), 
		          null, new RuntimeInstanceEC(currentSelf))));

        for (KeYJavaType imp : imps) {
            currentType = imp;

            ProgramMethod currentPM =
                    services.getJavaInfo().getProgramMethod
                            (currentType,
                                    currentMR.getMethodName().toString(),
                                    currentMR.getMethodSignature(services,
                                            new ExecutionContext(new TypeRef(currentType), null,
                                        	    new RuntimeInstanceEC(currentSelf))),
                                    currentSelf.getKeYJavaType());
            //System.out.println("pm: " + currentPM);

            if (!alreadyVisitedProgramMethods.contains(currentPM)) {
                alreadyVisitedProgramMethods.add(currentPM);
                //System.out.println("pm building new ptc: " + currentPM);
                if (services.getJavaInfo().getKeYJavaType
                        (currentPM.getContainerType()) != null) {
                    result.add
                            (services.getJavaInfo().getKeYJavaType
                                    (currentPM.getContainerType()));
                }

                ProgramTypeCollector mCollector =
                        new ProgramTypeCollector
                                (currentPM, currentSelf,
                                        currentType, services,
                                        alreadyVisitedProgramMethods);

                mCollector.start();
                for (Object o : mCollector.getResult()) {
                    result.add(o);
                }
            }

            // ACHTUNG: getProgramMethods ist unnoetig in der jetzigen Implementierung
            // Allerdings ist keine Ueberpruefung ob ggf. eine programmethod mehrfach wiederholt wird

            /*
             it = mCollector.getProgramMethods().iterator();
		      
             Set addToMethodRefs = mCollector.getMethodRefs();
             Iterator addToMethodRefsIt = addToMethodRefs.iterator();
             while (addToMethodRefsIt.hasNext()) {
             MethodReference mR = (MethodReference) addToMethodRefsIt.next();
             // only add those methodReferences which have not been visited
             // to the set of methodReferences which need to be visited
             if (!visitedMethodRefs.contains(mR)) {
             methodRefs.add(mR);
             }
             }
           */
        }
	}
    }

    protected void doDefaultAction(SourceElement x) {
        if (x instanceof Expression) {
	    final KeYJavaType expressionType = 
		services.getTypeConverter().getKeYJavaType
		( (Expression)x, 
		  new ExecutionContext(new TypeRef(type), null, 
			  new RuntimeInstanceEC(self)));
	    Debug.assertTrue(expressionType != null, 
			     "Could not determine type of " + x);
	    result.add(expressionType);
	}
    }
}

