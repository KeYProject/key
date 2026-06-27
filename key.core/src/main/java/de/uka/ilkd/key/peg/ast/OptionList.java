/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import de.uka.ilkd.key.peg.ast.StubAstNodes.OptionExpr;
import org.jspecify.annotations.NullMarked;

/**
 * Represents a list of options for taclets.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * option_list: LPAREN option_expr (COMMA option_expr)* RPAREN;
 * }</pre>
 */
@NullMarked
public class OptionList extends BaseAstNode {
    private final java.util.List<OptionExpr> options;

    public OptionList(Position position, java.util.List<OptionExpr> options) {
        super(position);
        this.options = options;
        for (OptionExpr o : options) {
            setChildParent(o);
        }
    }

    public java.util.List<OptionExpr> getOptions() {
        return options;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}