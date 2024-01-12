/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.metaconstruct.arith;

import java.math.BigInteger;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


/**
 * Computes the pow function for literals. Computation fails if second argument is negative or
 * exceeds Integer.MAX_VALUE (the latter due to restrictions of class BigInteger).
 *
 */
public final class MetaPow extends AbstractTermTransformer {

    public MetaPow() {
        super(new Name("#pow"), 2);
    }

    /** calculates the resulting term. */
    public Term transform(Term term, SVInstantiations svInst, Services services) {
        final Term arg1 = term.sub(0);
        final Term arg2 = term.sub(1);

        final BigInteger bigIntArg1 = new BigInteger(convertToDecimalString(arg1, services));
        final BigInteger bigIntArg2 = new BigInteger(convertToDecimalString(arg2, services));

        final TermBuilder tb = services.getTermBuilder();
        BigInteger result;
        try {
            result = bigIntArg1.pow(bigIntArg2.intValue());
        } catch (ArithmeticException ae) {
            /*
             * in this case the computation of the value fails and we need to ensure that it fails
             * gracefully, i.e. that it does not change the original term which is pow(arg1, arg2)
             * Attention: Do not return <code>term</code> as this has the {@link TermTransformer}
             * MetaPow (<code>#pow</code>) as top level operator which is supposed to only occur
             * in rules (and which has {@link AbstractTermTransformer#MetaSort} as sort and not
             * <code>int</code>.
             */
            return tb.func(services.getTypeConverter().getIntegerLDT().getPow(), arg1, arg2);
        }

        return services.getTermBuilder().zTerm(result.toString());
    }
}
