/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

import java.util.ArrayList;
import java.util.List;

/**
 * Represents formal sort arguments (type parameters).
 * Corresponds to: OPENTYPEPARAMS sortId (COMMA sortId)* CLOSETYPEPARAMS;
 *
 * @author Cline
 * @version 1.0
 */
@NullMarked
public class FormalSortArgs extends BaseAstNode {
    private final List<SortId> sortIds;

    public FormalSortArgs(Position position,
                          List<SortId> sortIds) {
        super(position);
        this.sortIds = sortIds;
        for (SortId sortId : sortIds) {
            setChildParent(sortId);
        }
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }

    public List<SortId> getSortIds() {
        return sortIds;
    }
}