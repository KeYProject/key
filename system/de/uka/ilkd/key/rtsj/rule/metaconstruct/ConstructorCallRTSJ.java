// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.rtsj.rule.metaconstruct;

import java.util.List;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.operator.New;
import de.uka.ilkd.key.java.recoderext.AreaAllocationMethodBuilder;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.metaconstruct.ConstructorCall;

public class ConstructorCallRTSJ extends ConstructorCall {

    public ConstructorCallRTSJ(SchemaVariable newObjectSV,
            ProgramElement consRef) {
	super(new Name("constructor-call-rtsj"), newObjectSV, consRef);
    }

    protected List<Statement> constructorCallSequence(
            final New constructorReference, final KeYJavaType classType,
            SVInstantiations svInst, Services services) {

	List<Statement> stmnts = 
	    super.constructorCallSequence(constructorReference, classType, svInst, services);


	KeYJavaType typePhysicalMemoryArea = null;
	try {
	    typePhysicalMemoryArea = services.getJavaInfo().getKeYJavaType("javax.realtime.PhysicalMemoryArea");
	}catch(RuntimeException ex) {
	    // somebody is using non standard libraries
	}
	if(typePhysicalMemoryArea != null && classType == typePhysicalMemoryArea) {
	    final Expression fstArgument = ((MethodBodyStatement)stmnts.get(stmnts.size())).getArguments().get(0);        	
	    stmnts.add(stmnts.size() - 1, 
		    new MethodReference(new ImmutableArray<Expression>(fstArgument),
			    new ProgramElementName(AreaAllocationMethodBuilder.IMPLICIT_AREA_ALLOCATE), 
			    constructorReference.getTypeReference()));
	}

	return stmnts;
    }

}
