/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.ldt;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.JFunction;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.util.ExtList;

/**
 * Complete this class if you want to add support for the JML \real type.
 *
 * At the moment this class contains only stubs.
 *
 * @author bruns
 */
public final class RealLDT extends LDT {

    public static final Name NAME = new Name("real");


    public RealLDT(TermServices services) {
        super(NAME, services);
    }


    @Override
    public boolean isResponsible(Operator op, JTerm[] subs,
            Services services, ExecutionContext ec) {
        return false;
    }


    @Override
    public boolean isResponsible(Operator op, JTerm left, JTerm right,
            Services services, ExecutionContext ec) {
        return false;
    }


    @Override
    public boolean isResponsible(Operator op, JTerm sub,
            TermServices services, ExecutionContext ec) {
        return false;
    }


    @Override
    public JTerm translateLiteral(Literal lit, Services services) {
        // return skolem term
        final Function sk =
            new JFunction(new Name(String.valueOf(NAME) + lit), targetSort());
        return services.getTermBuilder().func(sk);
    }

    // @Override
    // public Function getFunctionFor(String op, Services services) {
    // switch (op) {
    // case "gt": return getGreaterThan();
    // case "geq": return getGreaterOrEquals();
    // case "lt": return getLessThan();
    // case "leq": return getLessOrEquals();
    // case "div": return getDivIEEE();
    // case "mul": return getMulIEEE();
    // case "add": return getAddIEEE();
    // case "sub": return getSubIEEE();
    // }
    // return null;
    // }

    @Override
    public Function getFunctionFor(Operator op,
            Services services,
            ExecutionContext ec) {
        assert false;
        return null;
    }


    @Override
    public boolean hasLiteralFunction(Function f) {
        return false;
    }


    @Override
    public Expression translateTerm(JTerm t, ExtList children, Services services) {
        return null;
    }


    @Override
    public Type getType(JTerm t) {
        if (t.sort() == targetSort()) {
            return PrimitiveType.JAVA_REAL;
        } else {
            return null;
        }
    }
}
