/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

import java.util.List;

/**
 * Represents argument sorts or formula (for transformers).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * arg_sorts_or_formula: (LPAREN arg_sorts_or_formula_helper (COMMA arg_sorts_or_formula_helper)* RPAREN)?;
 * arg_sorts_or_formula_helper: sortId | FORMULA;
 * }</pre>
 */
@NullMarked
public class ArgSortsOrFormula extends BaseAstNode {
    private final List<Object> items; // List of SortId or Boolean (true = FORMULA keyword)

    public ArgSortsOrFormula(Position position, List<Object> items) {
        super(position);
        this.items = items;
        for (Object item : items) {
            if (item instanceof SortId) {
                setChildParent((SortId) item);
            }
        }
    }

    public List<Object> getItems() {
        return items;
    }
}