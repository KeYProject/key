/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Represents a location term (variable or field access).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * location_term: ident (DOT ident)* (LBRACKET term RBRACKET)*?;
 * }</pre>
 */
@NullMarked
public class LocationTerm extends BaseAstNode {
    private final String baseName;
    private final @Nullable Term qualifier;
    private final java.util.List<String> fieldChain;
    private final java.util.List<Term> arrayIndices;

    public LocationTerm(Position position, String baseName, @Nullable Term qualifier,
                        java.util.List<String> fieldChain, java.util.List<Term> arrayIndices) {
        super(position);
        this.baseName = baseName;
        this.qualifier = qualifier;
        this.fieldChain = fieldChain;
        this.arrayIndices = arrayIndices;
        setChildParent(qualifier);
        for (Term t : arrayIndices) {
            setChildParent(t);
        }
    }

    public String getBaseName() {
        return baseName;
    }

    public @Nullable Term getQualifier() {
        return qualifier;
    }

    public java.util.List<String> getFieldChain() {
        return fieldChain;
    }

    public java.util.List<Term> getArrayIndices() {
        return arrayIndices;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}