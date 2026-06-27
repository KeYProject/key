/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Represents a proof script command parameter.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * proof_script_param: (ident EQUALS)? expression;
 * }</pre>
 */
@NullMarked
public class ProofScriptParameter extends BaseAstNode {
    private final @Nullable String name;
    private final Object expression;

    public ProofScriptParameter(Position position,
                                @Nullable String name, Object expression) {
        super(position);
        this.name = name;
        this.expression = expression;
    }

    public @Nullable String getName() {
        return name;
    }

    public Object getExpression() {
        return expression;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}