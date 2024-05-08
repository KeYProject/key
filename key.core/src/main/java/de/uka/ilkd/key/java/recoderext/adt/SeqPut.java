/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext.adt;

import recoder.java.Expression;
import recoder.list.generic.ASTArrayList;


public class SeqPut extends ADTPrefixConstruct {

    private static final long serialVersionUID = -4836079248155746383L;

    public SeqPut(Expression seq, Expression idx, Expression val) {
        children = new ASTArrayList<>(getArity());
        children.add(seq);
        children.add(idx);
        children.add(val);
        makeParentRoleValid();
    }

    protected SeqPut(SeqPut proto) {
        super(proto);
        makeParentRoleValid();
    }

    @Override
    public SeqPut deepClone() {
        return new SeqPut(this);
    }


    @Override
    public int getArity() {
        return 3;
    }


    @Override
    public int getNotation() {
        return PREFIX;
    }

    @Override
    public String toSource() {
        return "\\seq_upd(" + children.get(0).toSource() + ", " + children.get(1).toSource() + ", "
            + children.get(2).toSource() + ")";
    }
}
