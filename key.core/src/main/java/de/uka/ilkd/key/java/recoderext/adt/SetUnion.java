/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext.adt;

import recoder.java.Expression;


public class SetUnion extends ADTPrefixConstruct {

    /**
     *
     */
    private static final long serialVersionUID = -8425018389934762589L;


    public SetUnion(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }


    protected SetUnion(SetUnion proto) {
        super(proto);
        makeParentRoleValid();
    }


    @Override
    public SetUnion deepClone() {
        return new SetUnion(this);
    }


    @Override
    public int getArity() {
        return 2;
    }


    @Override
    public int getNotation() {
        return PREFIX;
    }
}
