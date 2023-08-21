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


public class MetaLeq extends AbstractTermTransformer {

    public MetaLeq() {
        super(new Name("#leq"), 2);
    }


    public Term transform(Term term, SVInstantiations svInst, Services services) {
        Term arg1 = term.sub(0);
        Term arg2 = term.sub(1);
        BigInteger bigIntArg1;
        BigInteger bigIntArg2;

        bigIntArg1 = new BigInteger(convertToDecimalString(arg1, services));
        bigIntArg2 = new BigInteger(convertToDecimalString(arg2, services));
        boolean result = bigIntArg1.compareTo(bigIntArg2) <= 0;

        if (result) {
            return services.getTermBuilder().tt();
        } else {
            return services.getTermBuilder().ff();
        }
    }
}
