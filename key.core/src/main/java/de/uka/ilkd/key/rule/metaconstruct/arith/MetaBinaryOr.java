/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.metaconstruct.arith;

import java.math.BigInteger;

import org.key_project.logic.Name;


public final class MetaBinaryOr extends MetaArithBitMaskOp {

    public MetaBinaryOr() {
        super(new Name("#BinaryOr"));
    }


    @Override
    protected BigInteger bitmaskOp(BigInteger left, BigInteger right) {
        return left.or(right);
    }
}
