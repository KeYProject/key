/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

import java.util.List;

/**
 * Represents where-to-bind clause.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * where_to_bind: LBRACE b+=(TRUE | FALSE) (COMMA b+=(TRUE | FALSE))* RBRACE;
 * }</pre>
 */
@NullMarked
public class WhereToBind extends BaseAstNode {
    private final List<Boolean> bindValues;

    public WhereToBind(Position position, List<Boolean> bindValues) {
        super(position);
        this.bindValues = bindValues;
    }

    public List<Boolean> getBindValues() {
        return bindValues;
    }
}