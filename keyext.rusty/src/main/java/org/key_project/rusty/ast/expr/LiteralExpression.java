/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import org.key_project.logic.Name;
import org.key_project.rusty.ast.SourceData;
import org.key_project.rusty.rule.MatchConditions;

public abstract class LiteralExpression implements Expr {
    /**
     * Return the Name of the LDT, which this Literal belongs to.
     */
    public abstract Name getLDTName();

    @Override
    public MatchConditions match(SourceData source, MatchConditions matchCond) {
        final var src = source.getSource();
        if (this.equals(src)) {
            source.next();
            return matchCond;
        } else {
            return null;
        }
    }
}
