// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.unittest;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.Modifier;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.expression.operator.New;
import de.uka.ilkd.key.java.expression.operator.NewArray;
import de.uka.ilkd.key.java.reference.ArrayReference;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.statement.Branch;
import de.uka.ilkd.key.java.statement.Catch;
import de.uka.ilkd.key.java.statement.Try;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;

/**
 * @author mbender
 * 
 */
public class AssGenFac {

    public AssignmentGenerator create() {
	assert (TestGenFac.testGen == TestGenFac.TG_JAVACARD || TestGenFac.testGen == TestGenFac.TG_JAVA) : "Unhandled case in AssGenFac.";
	if (TestGenFac.testGen == TestGenFac.TG_JAVACARD) {
	    return new JavaCardAssignmentGenerator();
	} else {
	    return new JavaAssignmentGenerator();
	}
    }

    public abstract class AssignmentGenerator {

	/**
	 * Generates either an assignment statement lhs = rhs; or a method call
	 * statement for the appropriate set method in the case that lhs is a
	 * field reference.
	 */
	public abstract Statement assignmentOrSet(Expression lhs,
	        Expression rhs, Services serv);
    }

    private class JavaCardAssignmentGenerator extends AssignmentGenerator {

	private JavaCardAssignmentGenerator() {
	    super();
	}

	@Override
	public Statement assignmentOrSet(final Expression lhs,
	        final Expression rhs, final Services serv) {
	    if (lhs instanceof FieldReference) {
		final ProgramVariable pv = ((FieldReference) lhs)
		        .getProgramVariable();
		String typeName = pv.getKeYJavaType().getName();
		typeName = PrettyPrinter.getTypeNameForAccessMethods(typeName);
		// KeYJavaType kjt = pv.getContainerType();
		String pvName = pv.name().toString();
		pvName = pvName.substring(pvName.lastIndexOf(":") + 1);
		final String methodName = "_set" + pvName + typeName;
		return new MethodReference(new ImmutableArray<Expression>(rhs),
		        new ProgramElementName(methodName),
		        ((FieldReference) lhs).getReferencePrefix());
	    }
	    final CopyAssignment ca = new CopyAssignment(lhs, rhs);
	    if (lhs instanceof ArrayReference) {
		final KeYJavaType ae = serv.getJavaInfo()
		        .getKeYJavaTypeByClassName(
		                "java.lang.ArrayIndexOutOfBoundsException");
		final ParameterDeclaration pd = new ParameterDeclaration(
		        new Modifier[0], new TypeRef(ae),
		        new VariableSpecification(new LocationVariable(
		                new ProgramElementName(
		                        "arrayIndexOutOfBoundsEx"), ae)), false);
		final Branch c = new Catch(pd, new StatementBlock());
		return new Try(new StatementBlock(ca), new Branch[] { c });
	    } else {
		return ca;
	    }
	}
    }

    private class JavaAssignmentGenerator extends AssignmentGenerator {

	private final AccessMethodsManager amm;

	private JavaAssignmentGenerator() {
	    super();
	    amm = AccessMethodsManager.getInstance();
	}

	@Override
	public Statement assignmentOrSet(final Expression lhs, Expression rhs,
	        final Services serv) {
	    // Determine the RightHandSite
	    if (rhs instanceof New) {
		rhs = amm.callNew((New) rhs);
	    } else if (rhs instanceof NewArray) {
		rhs = amm.callNew((NewArray) rhs);
	    } else {
		assert (rhs instanceof Literal
		        || rhs instanceof LocationVariable || rhs instanceof MethodReference) : "\nMissing type for rhs=\n"
		        + rhs + " with class: " + rhs.getClass();
	    }

	    // Determine the LeftHandSite
	    if (lhs instanceof LocationVariable) {
		return new CopyAssignment(lhs, rhs);
	    }
	    if (lhs instanceof FieldReference) {
		return amm.callSetter((FieldReference) lhs, rhs);
	    }
	    if (lhs instanceof ArrayReference) {
		final Statement arrAcc = amm.callSetter((ArrayReference) lhs,
		        rhs);
		final KeYJavaType ae = serv.getJavaInfo()
		        .getKeYJavaTypeByClassName(
		                "java.lang.ArrayIndexOutOfBoundsException");
		final ParameterDeclaration pd = new ParameterDeclaration(
		        new Modifier[0], new TypeRef(ae),
		        new VariableSpecification(new LocationVariable(
		                new ProgramElementName(
		                        "arrayIndexOutOfBoundsEx"), ae)), false);
		final Branch c = new Catch(pd, new StatementBlock());
		return new Try(new StatementBlock(arrAcc), new Branch[] { c });
	    } else {
		assert false : "\nMissing type for lhs=\n" + lhs
		        + " with class: " + lhs.getClass();
		return null;
	    }
	}
    }

}
