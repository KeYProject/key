/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.translation;

import javax.annotation.Nonnull;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * This class represents the translation of an expression of an arbitrary specification language,
 * which in the KeY world is either a term or a type.
 */
public final class SLExpression {
    private final Term term;
    private final KeYJavaType type;
    private final boolean isTerm;


    public SLExpression(@Nonnull Term term, @Nonnull KeYJavaType type, boolean isTerm) {
        if (term.sort() != Sort.ANY && term.sort() != type.getSort()) {
            throw new IllegalArgumentException(
                String.format("term has sort: %s; type has sort: %s", term.sort(), type.getSort()));
        }
        this.term = term;
        this.type = type;
        this.isTerm = isTerm;
    }

    public SLExpression(@Nonnull Term term, @Nonnull KeYJavaType type) {
        this(term, type, true);
    }


    /**
     * USE WITH CARE! Term-SLExpressions should have a type!
     */
    public SLExpression(@Nonnull Term term) {
        this.term = term;
        this.type = null;
        this.isTerm = true;
    }


    public SLExpression(@Nonnull KeYJavaType type) {
        this.term = null;
        this.type = type;
        this.isTerm = false;
    }


    public boolean isTerm() {
        return isTerm;
    }


    public boolean isType() {
        return !isTerm;
    }


    public Term getTerm() {
        return term;
    }


    public KeYJavaType getType() {
        return type;
    }


    @Override
    public String toString() {
        if (isTerm()) {
            return term + "(type: " + type + ")";
        } else {
            return type.toString();
        }
    }
}
