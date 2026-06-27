/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

import java.util.List;

/**
 * Represents option declarations.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * option_decls: OPTIONSDECL LBRACE (choice SEMI)* RBRACE;
 * }</pre>
 */
@NullMarked
public class OptionDecls extends BaseAstNode {
    private final List<Choice> choices;

    public OptionDecls(Position position, List<Choice> choices) {
        super(position);
        this.choices = choices;
        for (Choice c : choices) {
            setChildParent(c);
        }
    }

    public List<Choice> getChoices() {
        return choices;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}