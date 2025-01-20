/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.metaconstruct.arith;

import java.math.BigInteger;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Debug;

import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;



public final class MetaDiv extends AbstractTermTransformer {

    public MetaDiv() {
        super(new Name("#div"), 2);
    }


    /**
     * checks whether the result is consistent with the axiom div_axiom
     */
    private boolean checkResult(BigInteger a, BigInteger b, BigInteger result) {

        // (gt(b,0) -> (leq(0,sub(a,mul(result,b))) & lt(sub(a,mul(result,b)),b)) )
        if (b.compareTo(BigInteger.ZERO) > 0) {
            return ((BigInteger.ZERO.compareTo(a.subtract(result.multiply(b))) <= 0)
                    && (a.subtract(result.multiply(b)).compareTo(b) < 0));
        }

        // ( lt(b,0) -> (leq(0,sub(a,mul(result,b))) & lt(sub(a,mul(result,b)),neg(b))) )
        if (b.compareTo(BigInteger.ZERO) < 0) {
            return ((BigInteger.ZERO.compareTo(a.subtract(result.multiply(b))) <= 0)
                    && (a.subtract(result.multiply(b)).compareTo(b.negate()) < 0));
        }

        return false;
    }


    /** calculates the resulting term. */
    public Term transform(Term term, SVInstantiations svInst, Services services) {
        Term arg1 = term.sub(0);
        Term arg2 = term.sub(1);
        BigInteger bigIntArg1;
        BigInteger bigIntArg2;

        bigIntArg1 = new BigInteger(convertToDecimalString(arg1, services));
        bigIntArg2 = new BigInteger(convertToDecimalString(arg2, services));
        if (bigIntArg2.compareTo(new BigInteger("0")) == 0) {
            Name undefName = new Name("undef(" + term + ")");
            JFunction undef = services.getNamespaces().functions().lookup(undefName);
            if (undef == null) {
                undef = new JFunction(undefName,
                    services.getTypeConverter().getIntegerLDT().targetSort(), new Sort[0]);
                services.getNamespaces().functions().add(undef);
            }
            return services.getTermFactory().createTerm(undef);
        }
        BigInteger remainder = bigIntArg1.remainder(bigIntArg2);
        BigInteger bigIntResult = bigIntArg1.divide(bigIntArg2);
        if (remainder.compareTo(BigInteger.ZERO) != 0) {
            if (bigIntArg1.compareTo(BigInteger.ZERO) < 0) {
                if (bigIntArg2.compareTo(BigInteger.ZERO) > 0) {
                    bigIntResult = bigIntResult.subtract(BigInteger.ONE);
                } else {
                    bigIntResult = bigIntResult.add(BigInteger.ONE);
                }
            }
        }
        Debug.assertTrue(checkResult(bigIntArg1, bigIntArg2, bigIntResult), bigIntArg1 + "/"
            + bigIntArg2 + "=" + bigIntResult + " is inconsistent with the taclet div_axiom");
        return services.getTermBuilder().zTerm(bigIntResult.toString());
    }
}
