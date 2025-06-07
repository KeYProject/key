/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.metaconstruct.arith;

import java.math.BigInteger;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.Name;

public abstract class MetaArithBitMaskOp extends AbstractTermTransformer {

    protected MetaArithBitMaskOp(Name name) {
        super(name, 2);
    }

    protected abstract BigInteger bitmaskOp(BigInteger left, BigInteger right);

    public JTerm transform(JTerm term, SVInstantiations svInst, Services services) {
        JTerm arg1 = term.sub(0);
        JTerm arg2 = term.sub(1);
        BigInteger left;
        BigInteger right;

        left = new BigInteger(convertToDecimalString(arg1, services));
        right = new BigInteger(convertToDecimalString(arg2, services));

        BigInteger result = bitmaskOp(left, right);

        return services.getTermBuilder().zTerm(result.toString());
    }
}
