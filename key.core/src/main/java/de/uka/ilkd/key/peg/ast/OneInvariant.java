/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Represents a single invariant definition.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * one_invariant: ident COLON term (DISPLAY_STRING string)? NEWLINE;
 * }</pre>
 */
@NullMarked
public class OneInvariant extends BaseAstNode {
    private final String name;
    private final Term formula;
    private final @Nullable String displayName;

    public OneInvariant(Position position, String name, Term formula, @Nullable String displayName) {
        super(position);
        this.name = name;
        this.formula = formula;
        this.displayName = displayName;
        setChildParent(formula);
    }

    public String getName() {
        return name;
    }

    public Term getFormula() {
        return formula;
    }

    public @Nullable String getDisplayName() {
        return displayName;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}