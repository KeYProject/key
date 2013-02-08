// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.util.removegenerics;

import recoder.CrossReferenceServiceConfiguration;
import recoder.ParserException;
import recoder.ProgramFactory;
import recoder.java.CompilationUnit;
import recoder.java.declaration.FieldDeclaration;
import recoder.java.reference.TypeReference;
import recoder.kit.TypeKit;

/**
 * This class has been used to point out a bug in recoder.
 * It can be removed as soon as this bug is solved.
 * 
 * @author MU
 */

public class TestComment {
    
    protected static CrossReferenceServiceConfiguration sc = new CrossReferenceServiceConfiguration();

    public static CompilationUnit registerCU(String compilationUnit) throws ParserException {
        ProgramFactory f = sc.getProgramFactory();
        CompilationUnit cu = f.parseCompilationUnit(compilationUnit);
        sc.getChangeHistory().attached(cu);
        return cu;
    }
    
    public static void testComments() throws ParserException {
        CompilationUnit cu = registerCU("class A {\n\n\n" +
                        "// some comment\r\nA a; } class B {}");
        System.out.println(cu.toSource());
        FieldDeclaration fd = (FieldDeclaration) cu.getDeclarations().get(0).getMembers().get(0);
        TypeReference oldType = fd.getTypeReference();
        TypeReference newType = TypeKit.createTypeReference(sc.getProgramFactory(), "B");
        fd.replaceChild(oldType, newType);
        System.out.println(cu.toSource());
        
    }
    
    public static void main(String[] args) throws ParserException {
        testComments();
    }
    
}
