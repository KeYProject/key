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

public abstract class MetaArithBitMaskOp extends AbstractTermTransformer {

    public MetaArithBitMaskOp(Name name) {
        super(name, 2);
    }

    protected abstract BigInteger bitmaskOp(BigInteger left, BigInteger right);

    public Term transform(Term term, SVInstantiations svInst, Services services) {
        Term arg1 = term.sub(0);
        Term arg2 = term.sub(1);
        BigInteger left;
        BigInteger right;

        left = new BigInteger(convertToDecimalString(arg1, services));
        right = new BigInteger(convertToDecimalString(arg2, services));

        BigInteger result = bitmaskOp(left, right);

        return services.getTermBuilder().zTerm(result.toString());
    }
}
