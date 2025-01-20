/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.metaconstruct.arith;

import java.math.BigInteger;

import org.key_project.logic.Name;

/**
 *
 */
public final class MetaShiftRight extends MetaShift {

    /**
     * creates the transformer for performing a shift to the right
     */
    public MetaShiftRight() {
        super(new Name("#ShiftRight"));
    }

    @Override
    protected BigInteger shiftOp(BigInteger left, BigInteger right) {
        return left.shiftRight(right.intValue());
    }

}
