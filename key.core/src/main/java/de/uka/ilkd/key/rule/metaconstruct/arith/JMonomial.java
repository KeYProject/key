/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.metaconstruct.arith;

import java.math.BigInteger;
import java.util.Iterator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;

import org.key_project.logic.LogicServices;
import org.key_project.logic.Term;
import org.key_project.logic.op.Operator;
import org.key_project.prover.strategy.costbased.feature.helper.arith.Monomial;
import org.key_project.util.GenerationalCache;
import org.key_project.util.collection.ImmutableList;

/**
 * Class for analysing and modifying monomial expressions over the integers
 */
public class JMonomial {
    private JMonomial() {
    }

    public static Monomial create(Term monoTerm, LogicServices p_services) {
        final Services services = (Services) p_services;
        final GenerationalCache<Term, Monomial> monomialCache =
            services.getCaches().getMonomialCache();
        monoTerm = TermLabelManager.removeIrrelevantLabels((JTerm) monoTerm,
            services);
        // ConcurrentLruCache: get/put are individually atomic, no external lock needed.
        Monomial res = monomialCache.get(monoTerm);

        if (res == null) {
            res = createHelp(monoTerm, services);
            monomialCache.putIfAbsent(monoTerm, res);
        }
        return res;
    }

    private static Monomial createHelp(Term monomial, Services services) {
        final Analyser a = new Analyser(services);
        a.analyse(monomial);
        return new Monomial(a.parts, a.coeff);
    }

    public static Term toTerm(Monomial m, Services services) {
        final Operator mul = services.getTypeConverter().getIntegerLDT().getMul();
        Term res = null;

        final Iterator<Term> it = m.getParts().iterator();
        if (it.hasNext()) {
            res = it.next();
            while (it.hasNext()) {
                res = services.getTermFactory().createTerm(mul, (JTerm) res,
                    (JTerm) it.next());
            }
        }

        final var cTerm = services.getTermBuilder().zTerm(m.getCoefficient().toString());

        if (res == null) {
            res = cTerm;
        } else if (!BigInteger.ONE.equals(m.getCoefficient())) {
            res = services.getTermFactory().createTerm(mul,
                (JTerm) res, cTerm);
        }

        return res;
    }

    private static class Analyser {
        public BigInteger coeff = BigInteger.ONE;
        public ImmutableList<Term> parts = ImmutableList.nil();
        private final Services services;
        private final Operator numbers, mul;

        public Analyser(final Services services) {
            this.services = services;
            final IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
            numbers = integerLDT.getNumberSymbol();
            mul = integerLDT.getMul();
        }

        public void analyse(Term monomial) {
            if (monomial.op() == mul) {
                analyse(monomial.sub(0));
                analyse(monomial.sub(1));
            } else if (monomial.op() == numbers) {
                final BigInteger c = new BigInteger(
                    AbstractTermTransformer.convertToDecimalString(monomial, services));
                coeff = coeff.multiply(c);
            } else {
                parts = parts.prepend(monomial);
            }
        }
    }
}
