/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.ast;

import java.util.List;

import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.ast.expression.SwitchExpression;
import de.uka.ilkd.key.java.ast.expression.literal.IntLiteral;
import de.uka.ilkd.key.java.ast.statement.Yield;

import org.key_project.util.collection.ImmutableList;

import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Unit tests for the {@link SwitchExpression} node.
 */
class SwitchExpressionAstTest {
    @Test
    void hasSelectorAndBranches() {
        var expr = new SwitchExpression(PositionInfo.UNDEFINED, List.of(), new IntLiteral("1"),
            ImmutableList.of(KeYJavaASTFactory.defaultBlock(new Yield(new IntLiteral("0")))));
        assertThat(expr.getSelector()).isNotNull();
        assertThat(expr.getBranchCount()).isEqualTo(1);
        assertThat(expr.getChildCount()).isEqualTo(2);
    }
}
