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
import de.uka.ilkd.key.java.visitor.Visitor;
import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

import javax.annotation.Nonnull;
import java.util.List;


public class Positive extends Operator {
    public Positive(PositionInfo pi, List<Comment> comments, @Nonnull Expression child) {
        super(pi, comments, new ImmutableArray<>(child));
    }

    /**
     * Positive.
     *
     * @param expr the Expression
     */
    public Positive(@Nonnull Expression expr) {
        this(null, null, expr);
    }

    /**
     * Positive.
     *
     * @param children an ExtList with all children of this node
     */
    public Positive(ExtList children) {
        super(children);
    }

    /**
     * Get arity.
     *
     * @return the int value.
     */

    public int getArity() {
        return 1;
    }

    /**
     * Get precedence.
     *
     * @return the int value.
     */

    public int getPrecedence() {
        return 1;
    }

    /**
     * Get notation.
     *
     * @return the int value.
     */

    public int getNotation() {
        return PREFIX;
    }

    /**
     * Checks if this operator is left or right associative. Ordinary
     * unary operators are right associative.
     *
     * @return <CODE>true</CODE>, if the operator is left associative,
     * <CODE>false</CODE> otherwise.
     */

    public boolean isLeftAssociative() {
        return false;
    }

    /**
     * calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnPositive(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printPositive(this);
    }

    public KeYJavaType getKeYJavaType(Services services, ExecutionContext ec) {
        return services.getTypeConverter().
                getPromotedType(getExpressionAt(0).getKeYJavaType(services, ec));
    }

}