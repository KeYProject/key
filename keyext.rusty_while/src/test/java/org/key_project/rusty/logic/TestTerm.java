/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic;

import org.key_project.rusty.ast.expr.BooleanLiteralExpression;
import org.key_project.rusty.util.TacletForTests;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;


public class TestTerm {

    private TermBuilder tb;
    private TermFactory tf;

    @BeforeEach
    public void setUp() {
        tb = TacletForTests.services().getTermBuilder();
        tf = tb.tf();
    }

    @Test
    public void generalTest() {
        BooleanLiteralExpression b1 = new BooleanLiteralExpression(true);
        BooleanLiteralExpression b2 = new BooleanLiteralExpression(true);
        // assertTrue(b1.equals(b2));
    }
}
