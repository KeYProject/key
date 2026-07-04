/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.expression.literal;

import java.math.BigDecimal;
import java.math.BigInteger;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.ldt.RealLDT;

import org.key_project.logic.Name;
import org.key_project.util.ExtList;

/**
 * JML {@code \real} literal.
 * <p>
 * A real is an unbounded mathematical value, so it is stored exactly as an arbitrary-precision pair
 * {@code (unscaledValue, scale)} with value {@code unscaledValue * 10^(-scale)} (the same scheme as
 * {@link BigDecimal}, but with an unbounded {@link BigInteger} scale rather than an {@code int}).
 * The pair is kept in canonical form (trailing zeros stripped), so equal values have equal fields.
 * {@link BigDecimal} is used only to parse bounded source strings, never to hold the value.
 *
 * @author bruns
 */
public non-sealed class RealLiteral extends Literal {

    private final BigInteger unscaledValue;
    private final BigInteger scale;

    /**
     * Real literal with value {@code unscaledValue * 10^(-scale)}.
     */
    public RealLiteral(BigInteger unscaledValue, BigInteger scale) {
        final BigInteger[] canonical = canonicalize(unscaledValue, scale);
        this.unscaledValue = canonical[0];
        this.scale = canonical[1];
    }

    public RealLiteral() {
        this(BigInteger.ZERO, BigInteger.ZERO);
    }

    public RealLiteral(int value) {
        this(BigInteger.valueOf(value), BigInteger.ZERO);
    }

    public RealLiteral(double value) {
        this(BigDecimal.valueOf(value));
    }

    public RealLiteral(ExtList children, String value) {
        super(children);
        final BigDecimal parsed = new BigDecimal(value);
        final BigInteger[] canonical =
            canonicalize(parsed.unscaledValue(), BigInteger.valueOf(parsed.scale()));
        this.unscaledValue = canonical[0];
        this.scale = canonical[1];
    }

    public RealLiteral(ExtList children) {
        super(children);
        this.unscaledValue = BigInteger.ZERO;
        this.scale = BigInteger.ZERO;
    }

    /**
     * Real literal parsed from its decimal textual representation (e.g. {@code "1.25"},
     * {@code "-0.5"}, {@code "1.5e3"}).
     *
     * @param value a decimal string.
     */
    public RealLiteral(String value) {
        this(new BigDecimal(value));
    }

    /**
     * Bridge constructor: extracts the exact {@code (unscaledValue, scale)} of a parsed decimal.
     * Private because the value is never <em>stored</em> as a {@link BigDecimal}.
     */
    private RealLiteral(BigDecimal parsed) {
        this(parsed.unscaledValue(), BigInteger.valueOf(parsed.scale()));
    }

    /**
     * Strip trailing decimal zeros so that equal real values have identical {@code (unscaled,
     * scale)} pairs (e.g. {@code 1.0} and {@code 1.00} both become {@code (1, 0)}, {@code 100}
     * becomes {@code (1, -2)}). Zero is canonicalized to {@code (0, 0)}.
     */
    private static BigInteger[] canonicalize(BigInteger unscaled, BigInteger scale) {
        if (unscaled.signum() == 0) {
            return new BigInteger[] { BigInteger.ZERO, BigInteger.ZERO };
        }
        BigInteger u = unscaled;
        BigInteger s = scale;
        while (u.remainder(BigInteger.TEN).signum() == 0) {
            u = u.divide(BigInteger.TEN);
            s = s.subtract(BigInteger.ONE);
        }
        return new BigInteger[] { u, s };
    }

    @Override
    public boolean equals(Object o) {
        if (o == this) {
            return true;
        }
        if (o == null || o.getClass() != this.getClass()) {
            return false;
        }
        final RealLiteral other = (RealLiteral) o;
        return unscaledValue.equals(other.unscaledValue) && scale.equals(other.scale);
    }

    @Override
    public int computeHashCode() {
        return 31 * (17 * super.computeHashCode() + unscaledValue.hashCode()) + scale.hashCode();
    }

    /**
     * @return the unscaled value {@code v} such that the represented number is
     *         {@code v * 10^(-scale)}
     */
    public BigInteger getUnscaledValue() {
        return unscaledValue;
    }

    /**
     * @return the (possibly negative) power-of-ten scale {@code s} such that the represented number
     *         is {@code unscaledValue * 10^(-s)}
     */
    public BigInteger getScale() {
        return scale;
    }

    /**
     * @return the canonical decimal textual representation of the value (e.g. {@code "1.25"},
     *         {@code "-0.5"}, {@code "100"}).
     */
    public String getValue() {
        final String digits = unscaledValue.abs().toString();
        final String sign = unscaledValue.signum() < 0 ? "-" : "";
        final int s = scale.intValueExact();
        if (s <= 0) {
            // integer value: append (-s) trailing zeros
            return sign + digits + "0".repeat(-s);
        }
        if (digits.length() <= s) {
            // pure fraction: 0.00..0digits
            return sign + "0." + "0".repeat(s - digits.length()) + digits;
        }
        final int point = digits.length() - s;
        return sign + digits.substring(0, point) + "." + digits.substring(point);
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v
     *        the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnRealLiteral(this);
    }

    public KeYJavaType getKeYJavaType(Services javaServ) {
        return javaServ.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_REAL);
    }

    @Override
    public Name getLDTName() {
        return RealLDT.NAME;
    }

}
