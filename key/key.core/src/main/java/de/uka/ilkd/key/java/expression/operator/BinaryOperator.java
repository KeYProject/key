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

package de.uka.ilkd.key.java.expression.operator;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

import javax.annotation.Nonnull;
import java.util.List;

/**
 * Operator of arity 2
 *
 * @author AL
 */
public abstract class BinaryOperator extends Operator {

    public BinaryOperator(ExtList children) {
        super(children);
    }

    public BinaryOperator(PositionInfo pi, List<Comment> comments, @Nonnull Expression lhs, @Nonnull Expression rhs) {
        super(pi, comments, new ImmutableArray<>(lhs, rhs));
    }

    public BinaryOperator(Expression lhs, Expression rhs) {
        this(null, null, lhs, rhs);
    }

    /**
     * Get arity.
     *
     * @return the int value.
     */
    public final int getArity() {
        return 2;
    }

    public KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec) {
        final TypeConverter tc = javaServ.getTypeConverter();
        try {
            return tc.getPromotedType
                    (tc.getKeYJavaType((Expression) getChildAt(0), ec),
                            tc.getKeYJavaType((Expression) getChildAt(1), ec));
        } catch (Exception e) {
            throw new RuntimeException("Type promotion failed (see below). Operator was " + this, e);
        }
    }
}