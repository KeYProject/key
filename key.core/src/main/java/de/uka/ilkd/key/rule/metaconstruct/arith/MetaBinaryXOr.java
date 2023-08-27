/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.metaconstruct.arith;

import java.math.BigInteger;

import de.uka.ilkd.key.logic.Name;


public final class MetaBinaryXOr extends MetaArithBitMaskOp {

    public MetaBinaryXOr() {
        super(new Name("#BinaryXOr"));
    }


    @Override
    protected BigInteger bitmaskOp(BigInteger left, BigInteger right) {
        return left.xor(right);
    }
}
