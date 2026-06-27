/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

import java.util.List;

/**
 * Represents a list of variable expressions.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * varexp_list: varexp (COMMA varexp)*;
 * }</pre>
 */
@NullMarked
public class VarexpList extends BaseAstNode {
    private final List<Varexp> items;

    public VarexpList(Position position, List<Varexp> items) {
        super(position);
        this.items = items;
        for (Varexp v : items) {
            setChildParent(v);
        }
    }

    public List<Varexp> getItems() {
        return items;
    }
}