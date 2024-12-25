/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.ldt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.SourceElement;
import de.uka.ilkd.key.java.ast.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.ast.abstraction.Type;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.expression.Operator;
import de.uka.ilkd.key.java.ast.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.java.ast.expression.literal.Literal;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.util.Debug;

import org.key_project.logic.Name;

import java.util.List;


/**
 * This class inherits from LDT and implements all method that are necessary to handle the primitive
 * type boolean.
 */
public final class BooleanLDT extends LDT {

    public static final Name NAME = new Name("boolean");

    /** the boolean literals as function symbols and terms */
    private final JFunction boolTrue;
    private final Term termBoolTrue;
    private final JFunction boolFalse;
    private final Term termBoolFalse;


    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    public BooleanLDT(TermServices services) {
        super(NAME, services);
        boolTrue = addFunction(services, "TRUE");
        termBoolTrue = services.getTermBuilder().func(boolTrue);
        boolFalse = addFunction(services, "FALSE");
        termBoolFalse = services.getTermBuilder().func(boolFalse);
    }


    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    public Term getFalseTerm() {
        return termBoolFalse;
    }


    public Term getTrueTerm() {
        return termBoolTrue;
    }


    /**
     * returns the function representing the boolean value <tt>FALSE</tt>
     */
    public JFunction getFalseConst() {
        return boolFalse;
    }


    /**
     * returns the function representing the boolean value <tt>TRUE</tt>
     */
    public JFunction getTrueConst() {
        return boolTrue;
    }


    @Override
    public boolean isResponsible(
            Operator op, Term[] subs,
            Services services, ExecutionContext ec) {
        if (subs.length == 1) {
            return isResponsible(op, subs[0], services, ec);
        } else if (subs.length == 2) {
            return isResponsible(op, subs[0], subs[1], services, ec);
        }
        return false;
    }


    @Override
    public boolean isResponsible(
            Operator op, Term left, Term right,
            Services services, ExecutionContext ec) {
        return false;

    }


    @Override
    public boolean isResponsible(
            Operator op, Term sub,
            TermServices services, ExecutionContext ec) {
        return false;
    }


    @Override
    public Term translateLiteral(Literal lit, Services services) {
        if (lit instanceof BooleanLiteral) {
            return (((BooleanLiteral) lit).getValue() ? termBoolTrue : termBoolFalse);
        }
        Debug.fail("booleanLDT: Wrong literal", lit);
        return null;
    }


    @Override
    public JFunction getFunctionFor(
            Operator op,
            Services services,
            ExecutionContext ec) {
        assert false;
        return null;
    }


    @Override
    public boolean hasLiteralFunction(JFunction f) {
        return containsFunction(f) && f.arity() == 0;
    }


    @Override
    public Expression translateTerm(Term t, List<SourceElement> children, Services services) {
        if (t.op() == boolTrue) {
            return BooleanLiteral.TRUE;
        } else if (t.op() == boolFalse) {
            return BooleanLiteral.FALSE;
        } else {
            assert false : "BooleanLDT: Cannot convert term to program: " + t;
            return null;
        }
    }


    @Override
    public Type getType(Term t) {
        if (t.sort() == targetSort()) {
            return PrimitiveType.JAVA_BOOLEAN;
        } else {
            assert false : "BooleanLDT: Cannot get Java type for term: " + t;
            return null;
        }
    }
}
