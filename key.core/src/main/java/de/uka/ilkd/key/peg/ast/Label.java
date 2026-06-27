/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

/**
 * Represents a label (for program statements).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * label: LABEL ident COLON;
 * }</pre>
 */
@NullMarked
public class Label extends BaseAstNode {
    private final String name;

    public Label(Position position, String name) {
        super(position);
        this.name = name;
    }

    public String getName() {
        return name;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}