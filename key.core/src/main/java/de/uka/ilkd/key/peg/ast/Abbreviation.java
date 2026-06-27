/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

/**
 * Represents an abbreviation definition.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * abbreviation: ABBREVIATION ident EQUALS term NEWLINE;
 * }</pre>
 */
@NullMarked
public class Abbreviation extends BaseAstNode {
    private final String name;
    private final Term definition;

    public Abbreviation(Position position, String name, Term definition) {
        super(position);
        this.name = name;
        this.definition = definition;
        setChildParent(definition);
    }

    public String getName() {
        return name;
    }

    public Term getDefinition() {
        return definition;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}