/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.metaconstruct.arith;

import java.math.BigInteger;

import org.key_project.logic.Name;

import org.jspecify.annotations.NonNull;

public class MetaShiftLeft extends MetaShift {

    public MetaShiftLeft() {
        super(new Name("#ShiftLeft"));
    }

    @Override
    protected @NonNull BigInteger shiftOp(@NonNull BigInteger left, @NonNull BigInteger right) {
        return left.shiftLeft(right.intValue());
    }

}
