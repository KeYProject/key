/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.ldt;

import java.math.BigInteger;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.ast.abstraction.Type;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.expression.literal.Literal;
import de.uka.ilkd.key.java.ast.expression.literal.RealLiteral;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.util.Debug;

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
    /**
     * Name of the function wrapping a real literal as {@code __R(unscaledValue, scale)}. The
     * {@code __} prefix marks it as a reserved built-in symbol, kept out of the way of identifiers
     * a user might declare in a problem file (see also {@code Z}/{@code C}/{@code FP}/{@code DFP},
     * which should eventually adopt the same reserved-prefix convention).
     */
    public static final Name REAL_NUMBERS_NAME = new Name("__R");

    public final Function realNumbers;

    public RealLDT(TermServices services) {
        super(NAME, services);
        realNumbers = addFunction(services, REAL_NUMBERS_NAME.toString());
    }

    public Function getRealNumberSymbol() {
        return realNumbers;
    }


    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.ast.expression.Operator op, JTerm[] subs,
            Services services, ExecutionContext ec) {
        return false;
    }


    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.ast.expression.Operator op, JTerm left,
            JTerm right,
            Services services, ExecutionContext ec) {
        return false;
    }


    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.ast.expression.Operator op, JTerm sub,
            TermServices services, ExecutionContext ec) {
        return false;
    }


    @Override
    public JTerm translateLiteral(Literal lit, Services services) {
        Debug.assertTrue(lit instanceof RealLiteral,
            "Literal '" + lit + "' is not a real valued literal.");

        final RealLiteral real = (RealLiteral) lit;
        return services.getTermBuilder().rTerm(real.getUnscaledValue(), real.getScale());
    }

    private boolean isNumberLiteral(org.key_project.logic.op.Operator f) {
        String n = f.name().toString();
        if (n.length() == 1) {
            char c = n.charAt(0);
            return '0' <= c && c <= '9';
        }
        return false;
    }

    @Override
    public Function getFunctionFor(de.uka.ilkd.key.java.ast.expression.Operator op,
            Services services,
            ExecutionContext ec) {
        assert false;
        return null;
    }



    @Override
    public boolean hasLiteralFunction(Function f) {
        return containsFunction(f) && (f.arity() == 0 || isNumberLiteral(f));
    }


    @Override
    public Expression translateTerm(JTerm t, ExtList children, Services services) {
        if (t.op() instanceof JFunction func && func == realNumbers) {
            // \R(unscaledValue, scale) encodes the value unscaledValue * 10^(-scale). Both operands
            // are unbounded signed numerals, so the value is never squeezed through an int.
            final IntegerLDT intLDT = services.getTypeConverter().getIntegerLDT();
            final BigInteger unscaled = numeralValue(t.sub(0), intLDT);
            final BigInteger scale = numeralValue(t.sub(1), intLDT);
            return new RealLiteral(unscaled, scale);
        }
        return null;
    }

    /**
     * Decode a term of sort {@code numbers} into its integer value. Unlike
     * {@link IntegerLDT#toNumberString} this also handles the negative-sign wrapper
     * ({@code neglit}) that {@code numbers} terms carry for negative values.
     *
     * @param numeral a term of sort {@code numbers}
     * @param intLDT the integer LDT owning the numeral symbols
     * @return the value the numeral represents
     */
    private static BigInteger numeralValue(JTerm numeral, IntegerLDT intLDT) {
        if (numeral.op() == intLDT.getNegativeNumberSign()) {
            return numeralValue(numeral.sub(0), intLDT).negate();
        }
        return new BigInteger(intLDT.toNumberString(numeral));
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
