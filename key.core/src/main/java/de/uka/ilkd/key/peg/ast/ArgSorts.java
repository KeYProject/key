/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

import java.util.List;

/**
 * Represents argument sorts.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * arg_sorts: (LPAREN sortId (COMMA sortId)* RPAREN)?;
 * }</pre>
 */
@NullMarked
public class ArgSorts extends BaseAstNode {
    private final List<SortId> sorts;

    public ArgSorts(Position position, List<SortId> sorts) {
        super(position);
        this.sorts = sorts;
        for (SortId s : sorts) {
            setChildParent(s);
        }
    }

    public List<SortId> getSorts() {
        return sorts;
    }
}