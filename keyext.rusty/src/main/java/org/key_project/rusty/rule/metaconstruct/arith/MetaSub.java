/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule.metaconstruct.arith;

import java.math.BigInteger;

import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.op.AbstractTermTransformer;
import org.key_project.rusty.rule.inst.SVInstantiations;

public class MetaSub extends AbstractTermTransformer {
    public MetaSub() {
        super(new Name("#sub"), 2);
    }

    public Term transform(Term term, SVInstantiations svInst, Services services) {
        Term arg1 = term.sub(0);
        Term arg2 = term.sub(1);
        BigInteger bigIntArg1;
        BigInteger bigIntArg2;

        bigIntArg1 = new BigInteger(convertToDecimalString(arg1, services));
        bigIntArg2 = new BigInteger(convertToDecimalString(arg2, services));

        BigInteger bigIntResult = bigIntArg1.subtract(bigIntArg2);

        return services.getTermBuilder().zTerm(bigIntResult.toString());
    }
}
