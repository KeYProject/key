/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

/**
 * Represents an activated choice (category:choice).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * activated_choice: cat=IDENT COLON choice_=IDENT;
 * }</pre>
 */
@NullMarked
public class ActivatedChoice extends BaseAstNode {
    private final String category;
    private final String choice;

    public ActivatedChoice(Position position, String category, String choice) {
        super(position);
        this.category = category;
        this.choice = choice;
    }

    public String getCategory() {
        return category;
    }

    public String getChoice() {
        return choice;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}