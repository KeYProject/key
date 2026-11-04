/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.metaconstruct.arith;

import java.math.BigInteger;
import java.util.Iterator;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;

import org.key_project.logic.Term;
import org.key_project.logic.op.Operator;
import org.key_project.prover.strategy.costbased.feature.helper.arith.Monomial;
import org.key_project.prover.strategy.costbased.feature.helper.arith.Polynomial;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;

/**
 * Class for analysing and modifying polynomial expressions over the integers
 */
public class JPolynomial {
    private JPolynomial() {
    }

    public static Polynomial create(Term polyTerm, Services services) {
        final Map<Term, Polynomial> cache = services.getCaches().getPolynomialCache();
        polyTerm = TermLabelManager.removeIrrelevantLabels((JTerm) polyTerm,
            services);

        Polynomial res = cache.get(polyTerm);

        if (res == null) {
            res = createHelp(polyTerm, services);
            cache.put(polyTerm, res);
        }
        return res;
    }

    private static Polynomial createHelp(Term polynomial, Services services) {
        final Analyser a = new Analyser(services);
        a.analyse(polynomial);
        return new Polynomial(a.constantPart, a.parts);
    }

    /**
     * Creates a term from this polynomial expression.
     *
     * @param services the services object
     * @return the resulting term
     */
    public static Term toTerm(Polynomial p, Services services) {
        final var intLDT = services.getTypeConverter().getIntegerLDT();
        final Operator add = intLDT.getAdd();
        Term res = null;

        final Iterator<Monomial> it = p.getParts().iterator();
        if (it.hasNext()) {
            res = JMonomial.toTerm(it.next(), services);
            while (it.hasNext()) {
                Term mono = JMonomial.toTerm(it.next(), services);
                res = services.getTermFactory().createTerm(add, (JTerm) res,
                    (JTerm) mono);
            }
        }

        final Term cTerm = services.getTermBuilder().zTerm(p.getConstantTerm().toString());

        if (res == null) {
            res = cTerm;
        } else if (!BigInteger.ZERO.equals(p.getConstantTerm())) {
            res = services.getTermFactory().createTerm(add, (JTerm) cTerm,
                (JTerm) res);
        }

        return res;
    }

    private static class Analyser {
        public BigInteger constantPart = BigInteger.ZERO;
        public ImmutableList<Monomial> parts = ImmutableList.nil();
        private final Services services;
        private final TypeConverter tc;
        private final Operator numbers, add;

        public Analyser(final Services services) {
            this.services = services;
            this.tc = services.getTypeConverter();
            final IntegerLDT intLDT = tc.getIntegerLDT();
            numbers = intLDT.getNumberSymbol();
            add = intLDT.getAdd();
        }

        public void analyse(Term polynomial) {
            final var op = polynomial.op();
            if (op == add) {
                analyse(polynomial.sub(0));
                analyse(polynomial.sub(1));
            } else if (op == numbers) {
                final BigInteger c = new BigInteger(
                    convertToDecimalString(polynomial));
                constantPart = constantPart.add(c);
            } else {
                parts = Polynomial.addPart(parts, JMonomial.create(polynomial, services));
            }
        }

        private @NonNull String convertToDecimalString(Term polynomial) {
            return AbstractTermTransformer.convertToDecimalString(polynomial, services);
        }
    }
}
