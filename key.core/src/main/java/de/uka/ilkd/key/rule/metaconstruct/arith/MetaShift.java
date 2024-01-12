/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.metaconstruct.arith;

import java.math.BigInteger;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


public abstract class MetaShift extends AbstractTermTransformer {

    public final static BigInteger INT_MIN_VALUE = BigInteger.valueOf(Integer.MIN_VALUE);
    public final static BigInteger INT_MAX_VALUE = BigInteger.valueOf(Integer.MAX_VALUE);


    protected MetaShift(Name name) {
        super(name, 2);
    }


    public Term transform(Term term, SVInstantiations svInst, Services services) {
        Term arg1 = term.sub(0);
        Term arg2 = term.sub(1);
        BigInteger left;
        BigInteger right;

        left = new BigInteger(convertToDecimalString(arg1, services));
        right = new BigInteger(convertToDecimalString(arg2, services));

        BigInteger result = left;
        do {

            BigInteger rightActual = right;

            if (rightActual.compareTo(INT_MIN_VALUE) <= 0) {
                rightActual = INT_MIN_VALUE;
            } else {
                if (rightActual.compareTo(INT_MAX_VALUE) >= 0) {
                    rightActual = INT_MAX_VALUE;
                }
            }

            result = shiftOp(result, rightActual);

            right = right.subtract(rightActual);

        } while (!right.equals(BigInteger.ZERO) && !result.equals(BigInteger.ZERO) // if the result
                                                                                   // is zero
                                                                                   // nothing
                                                                                   // changes
                                                                                   // anymore, so we
                                                                                   // can exit the
                                                                                   // loop
        );

        return services.getTermBuilder().zTerm(result.toString());
    }


    protected abstract BigInteger shiftOp(BigInteger result, BigInteger rightOp);
}
