/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.metaconstruct.arith;

import java.math.BigInteger;

import de.uka.ilkd.key.rule.metaconstruct.TransformerMeta;

import org.key_project.logic.Name;

/**
 *
 */
@TransformerMeta(name = "#ShiftRight")
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
