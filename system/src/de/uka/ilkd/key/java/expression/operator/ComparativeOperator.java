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



package de.uka.ilkd.key.java.expression.operator;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.util.ExtList;
/**
 *  Comparative operator.
 *  @author <TT>AutoDoc</TT>
 */

public abstract class ComparativeOperator extends Operator {


    /**
     *      Comparative operator.
     *      @param children an ExtList with all children of this node
     *      the first children in list will be the one on the left
     *      side, the second the one on the  right side.
     */

    public ComparativeOperator(ExtList children) {
        super(children);
    }

    public ComparativeOperator(Expression lhs, Expression rhs) {
        super(lhs, rhs);
    }


    /**
 *      Get arity.
 *      @return the int value.
     */

    public int getArity() {
        return 2;
    }

    /**
 *      Get notation.
 *      @return the int value.
     */

    public int getNotation() {
        return INFIX;
    }

    public KeYJavaType getKeYJavaType(Services services, ExecutionContext ec) {
	return getKeYJavaType(services);
    }
    public KeYJavaType getKeYJavaType(Services services) {
	return services.getTypeConverter().getBooleanType();
    }

}
