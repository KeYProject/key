/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext.mset;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Literal;

public class EmptyMSetLiteral extends Literal {

    /**
     *
     */
    private static final long serialVersionUID = 8572271426600775146L;
    public static final EmptyMSetLiteral INSTANCE = new EmptyMSetLiteral();

    @Override
    public Expression deepClone() {
        return this;
    }

    @Override
    public void accept(SourceVisitor v) {
    }


    @Override
    public Object getEquivalentJavaType() {
        return null;
    }

    @Override
    public String toSource() {
        return "\\mset_empty";
    }
}
