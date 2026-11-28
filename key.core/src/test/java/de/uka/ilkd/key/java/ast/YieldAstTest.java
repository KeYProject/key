/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.ast;

import de.uka.ilkd.key.java.ast.expression.literal.IntLiteral;
import de.uka.ilkd.key.java.ast.statement.Yield;
import de.uka.ilkd.key.pp.PrettyPrinter;

import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Unit tests for the {@link Yield} statement node.
 */
class YieldAstTest {
    @Test
    void printsYieldWithItsExpression() {
        var yield = new Yield(new IntLiteral("10"));
        var pp = PrettyPrinter.purePrinter();
        pp.print(yield);
        assertThat(pp.result()).contains("yield").contains("10");
    }
}
