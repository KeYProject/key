/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.translation;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.JTerm;

import org.jspecify.annotations.NonNull;

/**
 * This class represents the translation of an expression of an arbitrary specification language,
 * which in the KeY world is either a term or a type.
 */
public final class SLExpression {
    private final JTerm term;
    private final KeYJavaType type;
    private final boolean isTerm;


    public SLExpression(@NonNull JTerm term, @NonNull KeYJavaType type, boolean isTerm) {
        if (term.sort() != JavaDLTheory.ANY && term.sort() != type.getSort()) {
            throw new IllegalArgumentException(
                String.format("term has sort: %s; type has sort: %s", term.sort(), type.getSort()));
        }
        this.term = term;
        this.type = type;
        this.isTerm = isTerm;
    }

    public SLExpression(@NonNull JTerm term, @NonNull KeYJavaType type) {
        this(term, type, true);
    }


    /**
     * USE WITH CARE! Term-SLExpressions should have a type!
     */
    public SLExpression(@NonNull JTerm term) {
        this.term = term;
        this.type = null;
        this.isTerm = true;
    }


    public SLExpression(@NonNull KeYJavaType type) {
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


    public JTerm getTerm() {
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
