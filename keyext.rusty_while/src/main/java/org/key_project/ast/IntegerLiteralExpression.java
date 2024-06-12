/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.ast;

import java.math.BigInteger;

import org.key_project.logic.SyntaxElement;

public class IntegerLiteralExpression extends LiteralExpression {
    public enum IntegerSuffix {
        u8,
        u16,
        u32,
        u64,
        u128,
        usize,
        i8,
        i16,
        i32,
        i64,
        i128,
        isize,
    }

    private final BigInteger value;
    private final IntegerSuffix suffix;


    public IntegerLiteralExpression(BigInteger value, IntegerSuffix suffix) {
        this.value = value;
        this.suffix = suffix;
    }

    @Override
    public SyntaxElement getChild(int n) {
        throw new IndexOutOfBoundsException("IntegerLiteralExpression has no children");
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public String toString() {
        return value + "_" + suffix.toString();
    }
}
