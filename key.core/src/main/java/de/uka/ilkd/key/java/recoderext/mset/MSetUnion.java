/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext.mset;

import de.uka.ilkd.key.java.recoderext.adt.ADTPrefixConstruct;

import recoder.java.Expression;

public class MSetUnion extends ADTPrefixConstruct {

    private static final long serialVersionUID = -6850638934821692317L;

    public MSetUnion(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }


    protected MSetUnion(MSetUnion proto) {
        super(proto);
        makeParentRoleValid();
    }



    @Override
    public Expression deepClone() {
        return new MSetUnion(this);
    }

    @Override
    public int getArity() {
        return 2;
    }

    @Override
    public int getNotation() {
        return PREFIX;
    }

    @Override
    public String toSource() {
        return "\\mset_union(" + children.get(0).toSource() + "," + children.get(1).toSource()
            + ")";
    }
}
