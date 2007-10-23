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
