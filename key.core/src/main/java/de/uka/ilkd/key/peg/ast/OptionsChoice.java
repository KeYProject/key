/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

import java.util.List;

/**
 * Represents an options choice declaration.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * options_choice: WITHOPTIONS activated_choice (COMMA activated_choice)* SEMI;
 * }</pre>
 */
@NullMarked
public class OptionsChoice extends BaseAstNode {
    private final List<ActivatedChoice> choices;

    public OptionsChoice(Position position, List<ActivatedChoice> choices) {
        super(position);
        this.choices = choices;
        for (ActivatedChoice c : choices) {
            setChildParent(c);
        }
    }

    public List<ActivatedChoice> getChoices() {
        return choices;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}