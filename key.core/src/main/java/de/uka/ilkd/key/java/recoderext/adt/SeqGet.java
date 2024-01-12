/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext.adt;

import recoder.java.Expression;

/**
 * Sequence getter operation.
 *
 * @author bruns
 * @since 1.7.2119
 */
public class SeqGet extends ADTPrefixConstruct {

    /**
     *
     */
    private static final long serialVersionUID = -421447886220796576L;

    /**
     * Creates a sequence getter operator.
     *
     * @param seq Sequence to operate on
     * @param idx Index position (from 0 to length-1)
     */
    public SeqGet(Expression seq, Expression idx) {
        super(seq, idx);
        makeParentRoleValid();
    }


    protected SeqGet(SeqGet proto) {
        super(proto);
        makeParentRoleValid();
    }


    @Override
    public SeqGet deepClone() {
        return new SeqGet(this);
    }


    @Override
    public int getArity() {
        return 2;
    }


    @Override
    public int getNotation() {
        return POSTFIX;
    }

    @Override
    public String toSource() {
        return children.get(0).toSource() + "[" + children.get(1).toSource() + "]";
    }
}
