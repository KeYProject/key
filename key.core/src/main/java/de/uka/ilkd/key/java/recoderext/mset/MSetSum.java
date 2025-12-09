/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext.mset;

import de.uka.ilkd.key.java.recoderext.adt.ADTPrefixConstruct;

import recoder.java.Expression;

public class MSetSum extends ADTPrefixConstruct {

    private static final long serialVersionUID = -6950638934821692317L;

    public MSetSum(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }


    protected MSetSum(MSetSum proto) {
        super(proto);
        makeParentRoleValid();
    }



    @Override
    public Expression deepClone() {
        return new MSetSum(this);
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
        return "\\mset_sum(" + children.get(0).toSource() + "," + children.get(1).toSource()
            + ")";
    }
}
