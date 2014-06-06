// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java.recoderext;

import de.uka.ilkd.key.java.recoderext.EnumClassDeclaration;
import de.uka.ilkd.key.java.recoderext.ProofJavaProgramFactory;
import recoder.DefaultServiceConfiguration;
import recoder.ParserException;
import recoder.ProgramFactory;
import recoder.ServiceConfiguration;
import recoder.java.declaration.EnumDeclaration;
import junit.framework.TestCase;

public class TestEnumClassDeclaration extends TestCase {

    ProgramFactory factory;

    protected void setUp() throws Exception {
        factory = ProofJavaProgramFactory.getInstance();
        ServiceConfiguration sc = new DefaultServiceConfiguration();
        sc.getProjectSettings().setProperty("java5", "true");
        factory.initialize(sc);
    }

    private static String[] enums =
            {
            // Simple
                    "enum A { a1, a2, a3 }",
                    // Two
                    "enum B implements C { b1(13), b2(42); B(int i){} void m() {} int j; }",
                    // 2 Constructors
                    "enum C { c1, c2(23); C(int i) { this(); } C() { j = 0; } int j; }"
                    };

    public void testSimple() throws ParserException {
        EnumDeclaration ed =
                (EnumDeclaration) factory.parseCompilationUnit(enums[0]).getTypeDeclarationAt(
                        0);

        EnumClassDeclaration ec = new EnumClassDeclaration(ed);

        System.out.println(ec.toSource());

    }

    public void testTwo() throws ParserException {
        EnumDeclaration ed =
                (EnumDeclaration) factory.parseCompilationUnit(enums[1]).getTypeDeclarationAt(
                        0);

        EnumClassDeclaration ec = new EnumClassDeclaration(ed);

        System.out.println(ec.toSource());
    }
    
    public void test2Constr() throws ParserException {
        EnumDeclaration ed =
                (EnumDeclaration) factory.parseCompilationUnit(enums[2]).getTypeDeclarationAt(
                        0);

        EnumClassDeclaration ec = new EnumClassDeclaration(ed);

        System.out.println(ec.toSource());
    }
}