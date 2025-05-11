/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.expression.literal;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.logic.Name;

import org.jspecify.annotations.NonNull;

/**
 * Null literal. Is used as singleton.
 */

public class NullLiteral extends Literal {

    public static final NullLiteral NULL = new NullLiteral();

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     */
    private NullLiteral() {
        super();
    }

    @Override
    public boolean equals(@org.jspecify.annotations.Nullable Object o) {
        return o == this;
    }

    @Override
    protected int computeHashCode() {
        return System.identityHashCode(this);
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v the Visitor
     */
    public void visit(@NonNull Visitor v) {
        v.performActionOnNullLiteral(this);
    }

    public @NonNull KeYJavaType getKeYJavaType(@NonNull Services javaServ) {
        return javaServ.getJavaInfo().getNullType();
    }

    @Override
    public @NonNull Name getLDTName() {
        throw new UnsupportedOperationException("No LDT is linked to the null literal.");
    }

}
