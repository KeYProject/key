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


public class MetaMul extends AbstractTermTransformer {

    public MetaMul() {
        super(new Name("#mul"), 2);
    }


    public JTerm transform(JTerm term, SVInstantiations svInst, Services services) {
        JTerm arg1 = term.sub(0);
        JTerm arg2 = term.sub(1);
        BigInteger bigIntArg1;
        BigInteger bigIntArg2;

        bigIntArg1 = new BigInteger(convertToDecimalString(arg1, services));
        bigIntArg2 = new BigInteger(convertToDecimalString(arg2, services));
        BigInteger bigIntResult = bigIntArg1.multiply(bigIntArg2);

        return services.getTermBuilder().zTerm(bigIntResult.toString());
    }
}
