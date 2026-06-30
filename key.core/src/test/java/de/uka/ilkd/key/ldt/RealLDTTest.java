/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.ldt;

import java.math.BigInteger;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.expression.literal.RealLiteral;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.rule.TacletForTests;

import org.key_project.util.ExtList;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Round-trip tests for the {@code \R(unscaledValue, scale)} real-literal encoding (issue #3570):
 * {@link TermBuilder#rTerm(BigInteger, BigInteger)} must build a term that
 * {@link RealLDT#translateTerm(JTerm, ExtList, Services)} decodes back to the same value.
 */
public class RealLDTTest {

    private static RealLiteral roundTrip(Services services, RealLiteral in) {
        final JTerm term = services.getTermBuilder().rTerm(in.getUnscaledValue(), in.getScale());
        return (RealLiteral) services.getTypeConverter().getRealLDT()
                .translateTerm(term, new ExtList(), services);
    }

    @Test
    void rTermRoundTripsAllValues() {
        final Services services = TacletForTests.services();

        // covers: integer, simple fraction, negative <1, leading-zero fraction (scale matters),
        // trailing-zero integer (negative scale after canonicalization), negative >1, zero
        final String[] values = {
            "0", "1.25", "-0.5", "1.025", "0.001", "100", "-1.5", "3.14159", "-12.0", "42"
        };

        for (String s : values) {
            final RealLiteral in = new RealLiteral(s);
            final RealLiteral out = roundTrip(services, in);
            assertEquals(in, out, () -> "real literal '" + s + "' did not round-trip");
            assertEquals(in.getValue(), out.getValue(),
                () -> "printed form of '" + s + "' changed on round-trip");
        }
    }

    @Test
    void canonicalPrintedForms() {
        assertEquals("1.25", new RealLiteral("1.25").getValue());
        assertEquals("-0.5", new RealLiteral("-0.5").getValue());
        assertEquals("0.001", new RealLiteral("0.001").getValue());
        assertEquals("100", new RealLiteral("100").getValue());
        assertEquals("-12", new RealLiteral("-12.0").getValue()); // trailing zero stripped
        assertEquals("0", new RealLiteral("0.0").getValue());
    }

    /**
     * The whole point of the {@code (unscaledValue, scale)} encoding over {@code numbers}: it is
     * not
     * bounded by {@code int}. A scale beyond {@link Integer#MAX_VALUE} must still round-trip
     * through
     * the term representation (equality compares the unbounded fields, not the printed form).
     */
    @Test
    void encodingIsUnboundedInScale() {
        final Services services = TacletForTests.services();
        final BigInteger hugeScale = BigInteger.valueOf(Integer.MAX_VALUE).add(BigInteger.TEN);
        final RealLiteral in = new RealLiteral(BigInteger.valueOf(7), hugeScale);

        final RealLiteral out = roundTrip(services, in);

        assertEquals(in, out, "huge-scale real did not round-trip");
        assertEquals(hugeScale, out.getScale(), "scale was truncated");
    }
}
