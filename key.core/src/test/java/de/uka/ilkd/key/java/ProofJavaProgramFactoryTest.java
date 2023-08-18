/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java;

import java.io.File;
import java.io.IOException;
import java.util.Optional;
import java.util.function.Predicate;

import de.uka.ilkd.key.java.recoderext.Ghost;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.key_project.util.helper.FindResources;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.StringUtil;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import recoder.abstraction.Method;
import recoder.convenience.TreeWalker;
import recoder.java.Comment;
import recoder.java.CompilationUnit;
import recoder.java.JavaProgramElement;
import recoder.java.ProgramElement;
import recoder.java.Statement;
import recoder.java.StatementBlock;
import recoder.java.declaration.ClassDeclaration;
import recoder.java.declaration.LocalVariableDeclaration;
import recoder.java.declaration.MethodDeclaration;
import recoder.java.declaration.TypeDeclaration;
import recoder.java.expression.operator.CopyAssignment;
import recoder.java.reference.VariableReference;
import recoder.java.statement.EmptyStatement;
import recoder.java.statement.For;
import recoder.list.generic.ASTList;

/**
 * @author Alexander Weigl
 * @version 1 (9/12/21)
 */
public class ProofJavaProgramFactoryTest {
    private static final Logger LOGGER = LoggerFactory.getLogger(ProofJavaProgramFactoryTest.class);

    final Services services = HelperClassForTests.createServices();
    final Recoder2KeY r2k = new Recoder2KeY(services, services.getNamespaces());

    @Test
    public void testAttachCommentsCompilationUnit_AssertsFalse() throws IOException {
        File inputFile = new File(FindResources.getTestResourcesDirectory(),
            "de/uka/ilkd/key/java/recoderext/AssertsFalse.java");
        final CompilationUnit cu = getCompilationUnit(inputFile);

        Optional<Method> om = findMethod(cu, "AssertsFalse", "m");
        LOGGER.debug("{}", cu);
        Assertions.assertTrue(om.isPresent(), "Could not find method AssertsFalse#m()");
        MethodDeclaration m = (MethodDeclaration) om.get();
        assertContainsComment(m, it -> it.startsWith("/*@ normal_behavior"));

        Statement last = lastStatement(m);
        Assertions.assertTrue(last instanceof EmptyStatement);
        assertContainsComment((JavaProgramElement) last, it -> it.equals("//@ assert false;"));
    }


    @Test
    public void testAttachCommentsCompilationUnit_Steinhofel1() throws IOException {
        File inputFile = new File(FindResources.getTestResourcesDirectory(),
            "de/uka/ilkd/key/java/recoderext/Steinhoefel1.java");
        final CompilationUnit cu = getCompilationUnit(inputFile);

        Optional<Method> ofib = findMethod(cu, "Steinhoefel1", "fib");
        LOGGER.debug("{}", cu);
        Assertions.assertTrue(ofib.isPresent(), "Could not find method Steinhoefel1#fib()");
        MethodDeclaration m = (MethodDeclaration) ofib.get();
        assertContainsComment(m, it -> it.startsWith("/*@ public normal_behavior"));

        LocalVariableDeclaration ghost1 = (LocalVariableDeclaration) m.getBody().getStatementAt(2);
        Assertions.assertTrue(ghost1.getDeclarationSpecifiers().get(0) instanceof Ghost);
        Assertions.assertEquals("k0_old", ghost1.getVariables().get(0).getName());

        LocalVariableDeclaration ghost2 = (LocalVariableDeclaration) m.getBody().getStatementAt(3);
        Assertions.assertTrue(ghost2.getDeclarationSpecifiers().get(0) instanceof Ghost);
        Assertions.assertEquals("k1_old", ghost2.getVariables().get(0).getName());

        For forLoop = (For) m.getBody().getStatementAt(4); // retrieve the for loop
        assertContainsComment(forLoop, it -> it.equals("//@ ghost int k0_old = k0;"));
        assertContainsComment(forLoop, it -> it.equals("//@ ghost int k1_old = k1;"));
        assertContainsComment(forLoop, it -> it.startsWith("/*@ loop_invariant"));

        StatementBlock loopBody = (StatementBlock) forLoop.getBody();

        CopyAssignment ghost3 = (CopyAssignment) loopBody.getStatementAt(3);
        VariableReference var3 = (VariableReference) ghost3.getChildAt(0);
        Assertions.assertEquals("k0_old", var3.getName());

        CopyAssignment ghost4 = (CopyAssignment) loopBody.getStatementAt(5);
        VariableReference var4 = (VariableReference) ghost4.getChildAt(0);
        Assertions.assertEquals("k1_old", var4.getName());

        EmptyStatement empty1 = (EmptyStatement) loopBody.getStatementAt(4);
        EmptyStatement lastStatementInForLoop =
            (EmptyStatement) lastStatement((StatementBlock) forLoop.getBody());
        assertContainsComment(empty1, it -> it.equals("//@ set k0_old = k0;"));
        assertContainsComment(lastStatementInForLoop, it -> it.equals("//@ set k1_old = k1;"));

    }

    @Test
    public void testAttachCommentsCompilationUnit_SetStatements() throws IOException {
        File inputFile = new File(FindResources.getTestResourcesDirectory(),
            "de/uka/ilkd/key/java/recoderext/SetInMethodBody.java");
        final CompilationUnit cu = getCompilationUnit(inputFile);

        Optional<Method> ofib = findMethod(cu, "SetInMethodBody", "foo");
        LOGGER.debug("{}", cu);
        Assertions.assertTrue(ofib.isPresent(), "Could not find method SetInMethodBody#foo()");
        MethodDeclaration m = (MethodDeclaration) ofib.get();
        assertContainsComment(m, it -> it.startsWith("/*@ public normal_behavior"));

        CopyAssignment assign1 = (CopyAssignment) m.getBody().getStatementAt(0);
        VariableReference var1 = (VariableReference) assign1.getChildAt(0);
        Assertions.assertEquals("message", var1.getName());

        EmptyStatement empty1 = (EmptyStatement) m.getBody().getStatementAt(1);
        assertContainsComment(empty1, it -> it.equals("//@ set message = arg0;"));

        CopyAssignment assign2 = (CopyAssignment) m.getBody().getStatementAt(2);
        VariableReference var2 = (VariableReference) assign2.getChildAt(0);
        Assertions.assertEquals("cause", var2.getName());

        EmptyStatement empty2 = (EmptyStatement) m.getBody().getStatementAt(3);
        assertContainsComment(empty2, it -> it.equals("//@ set cause = arg1;"));
    }



    @Test
    public void testAttachCommentsCompilationUnit_SmansEtAlArrayList() throws IOException {
        File inputFile = new File("../key.ui/examples/heap/SmansEtAl/src/ArrayList.java");
        // Regenerate this file by copying the console output
        File expectedFile = new File(FindResources.getTestResourcesDirectory(),
            "de/uka/ilkd/key/java/testAttachCommentsCompilationUnit_SmansEtAlArrayList.txt");
        String expected = StringUtil.replaceNewlines(IOUtil.readFrom(expectedFile), "\n");
        final CompilationUnit cu = getCompilationUnit(inputFile);

        // Optional<Method> ofib = findMethod(cu, "Steinhoefel1", "fib");

        String out = getActualResult(cu);
        LOGGER.debug("{}", out);
        Assertions.assertEquals(expected, out, "Difference in attached comments");
    }


    @Test
    public void testAttachCommentsCompilationUnit_LockSpec() throws IOException {
        File inputFile = new File("../key.ui/examples/heap/permissions/lockspec/src/LockSpec.java");
        // Regenerate this file by copying the console output
        File expectedFile = new File(FindResources.getTestResourcesDirectory(),
            "de/uka/ilkd/key/java/testAttachCommentsCompilationUnit_LockSpec.txt");
        String expected = StringUtil.replaceNewlines(IOUtil.readFrom(expectedFile), "\n");
        final CompilationUnit cu = getCompilationUnit(inputFile);

        String out = getActualResult(cu);
        LOGGER.debug("{}", out);
        Assertions.assertEquals(expected, out, "Difference in attached comments");
    }


    private String getActualResult(CompilationUnit cu) {
        StringBuilder out = new StringBuilder();
        TreeWalker walker = new TreeWalker(cu);
        while (walker.next()) {
            ProgramElement pe = walker.getProgramElement();
            ASTList<Comment> b = pe.getComments();
            if (b != null && !b.isEmpty()) {
                out.append("(")
                        .append(pe.getStartPosition().getLine())
                        .append("/")
                        .append(pe.getEndPosition().getLine())
                        .append(") -- ");
                out.append(pe.getClass().getName()).append("\n");
                for (Comment comment : pe.getComments()) {
                    var text = StringUtil.replaceNewlines(comment.getText(), " ");
                    text = text.substring(0, Math.min(50, text.length())).trim();
                    out.append("  * ").append(text).append("\n");
                }
            }
        }
        return out.toString();
    }

    private Statement lastStatement(MethodDeclaration m) {
        return lastStatement(m.getBody());
    }

    private Statement lastStatement(StatementBlock body) {
        return body.getStatementAt(body.getStatementCount() - 1);
    }

    private void assertContainsComment(JavaProgramElement m, Predicate<String> needle) {
        ASTList<Comment> haystack = m.getComments();
        Optional<Comment> search =
            haystack.stream().filter(it -> needle.test(it.getText())).findFirst();

        Assertions.assertTrue(search.isPresent(),
            "Could not find comment satisfying the given predicate.");
    }

    private CompilationUnit getCompilationUnit(File inputFile) throws IOException {
        Assumptions.assumeTrue(inputFile.exists(),
            "Required input file " + inputFile + " does not exists!");
        String content = IOUtil.readFrom(inputFile);
        return r2k.recoderCompilationUnits(new String[] { content }).get(0);
    }

    private Optional<Method> findMethod(CompilationUnit cu, String className, String methodName) {
        for (int i = 0; i < cu.getTypeDeclarationCount(); i++) {
            TypeDeclaration td = cu.getTypeDeclarationAt(i);
            if (td instanceof ClassDeclaration) {
                ClassDeclaration clazz = (ClassDeclaration) td;
                if (clazz.getName().equals(className)) {
                    return clazz.getMethods().stream().filter(it -> it.getName().equals(methodName))
                            .findFirst();
                }
            }
        }
        return Optional.empty();
    }
}
