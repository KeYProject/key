/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import recoder.DefaultServiceConfiguration;
import recoder.ParserException;
import recoder.ProgramFactory;
import recoder.ServiceConfiguration;
import recoder.java.declaration.EnumDeclaration;

public class TestEnumClassDeclaration {
    private static final Logger LOGGER = LoggerFactory.getLogger(TestEnumClassDeclaration.class);

    ProgramFactory factory;

    @BeforeEach
    public void setUp() throws Exception {
        factory = ProofJavaProgramFactory.getInstance();
        ServiceConfiguration sc = new DefaultServiceConfiguration();
        sc.getProjectSettings().setProperty("java5", "true");
        factory.initialize(sc);
    }

    private static final String[] enums = {
        // Simple
        "enum A { a1, a2, a3 }",
        // Two
        "enum B implements C { b1(13), b2(42); B(int i){} void m() {} int j; }",
        // 2 Constructors
        "enum C { c1, c2(23); C(int i) { this(); } C() { j = 0; } int j; }" };

    @Test
    public void testSimple() throws ParserException {
        EnumDeclaration ed =
            (EnumDeclaration) factory.parseCompilationUnit(enums[0]).getTypeDeclarationAt(0);
        EnumClassDeclaration ec = new EnumClassDeclaration(ed);
        LOGGER.debug(ec.toSource());
    }

    @Test
    public void testTwo() throws ParserException {
        EnumDeclaration ed =
            (EnumDeclaration) factory.parseCompilationUnit(enums[1]).getTypeDeclarationAt(0);
        EnumClassDeclaration ec = new EnumClassDeclaration(ed);
        LOGGER.debug(ec.toSource());
    }

    @Test
    public void test2Constr() throws ParserException {
        EnumDeclaration ed =
            (EnumDeclaration) factory.parseCompilationUnit(enums[2]).getTypeDeclarationAt(0);
        EnumClassDeclaration ec = new EnumClassDeclaration(ed);
        LOGGER.debug(ec.toSource());
    }
}
