/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext.adt;

import recoder.java.Expression;
import recoder.list.generic.ASTArrayList;


public class SeqReverse extends ADTPrefixConstruct {

    /**
     *
     */
    private static final long serialVersionUID = -4836079248155746383L;

    public SeqReverse(Expression e) {
        children = new ASTArrayList<>(getArity());
        children.add(e);
        makeParentRoleValid();
    }


    protected SeqReverse(SeqReverse proto) {
        super(proto);
        makeParentRoleValid();
    }


    @Override
    public SeqReverse deepClone() {
        return new SeqReverse(this);
    }


    @Override
    public int getArity() {
        return 1;
    }


    @Override
    public int getNotation() {
        return PREFIX;
    }

    @Override
    public String toSource() {
        return "\\seq_reverse(" + children.get(0).toSource() + ")";
    }
}
