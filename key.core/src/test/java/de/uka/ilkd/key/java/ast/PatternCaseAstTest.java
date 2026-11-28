/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.ast;


import de.uka.ilkd.key.java.ast.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.java.ast.expression.literal.IntLiteral;
import de.uka.ilkd.key.java.ast.pattern.AnyPattern;
import de.uka.ilkd.key.java.ast.statement.PatternCase;
import de.uka.ilkd.key.java.ast.statement.Yield;
import de.uka.ilkd.key.pp.PrettyPrinter;

import org.key_project.util.collection.ImmutableList;

import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Unit tests for the {@link PatternCase} branch node.
 */
class PatternCaseAstTest {
    @Test
    void printsPatternAndGuard() {
        var pattern = new AnyPattern(null, null);
        var arm = new PatternCase(ImmutableList.of(pattern),
            new BooleanLiteral(PositionInfo.UNDEFINED, true),
            ImmutableList.of(new Yield(new IntLiteral("7"))));
        var pp = PrettyPrinter.purePrinter();
        pp.print(arm);
        assertThat(pp.result()).contains("case").contains("when").contains("_");
    }
}
