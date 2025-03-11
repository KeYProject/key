/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext.adt;

import recoder.java.Expression;


public class SeqConcat extends ADTPrefixConstruct {

    /**
     *
     */
    private static final long serialVersionUID = -5950638934821692317L;

    public SeqConcat(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }


    protected SeqConcat(SeqConcat proto) {
        super(proto);
        makeParentRoleValid();
    }


    @Override
    public SeqConcat deepClone() {
        return new SeqConcat(this);
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
        return "\\seq_concat(" + children.get(0).toSource() + "," + children.get(1).toSource()
            + ")";
    }
}
