package de.uka.ilkd.key.java;

import de.uka.ilkd.key.java.recoderext.Ghost;
import de.uka.ilkd.key.proof.runallproofs.Function;
import de.uka.ilkd.key.util.HelperClassForTests;
import org.junit.Assert;
import org.junit.Assume;
import org.junit.Test;
import org.key_project.util.helper.FindResources;
import org.key_project.util.java.IOUtil;
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
import recoder.java.statement.EmptyStatement;
import recoder.java.statement.For;
import recoder.list.generic.ASTList;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.Optional;
import java.util.function.Predicate;

/**
 * @author Alexander Weigl
 * @version 1 (9/12/21)
 */
public class ProofJavaProgramFactoryTest {
    final Services services = HelperClassForTests.createServices();
    final Recoder2KeY r2k = new Recoder2KeY(services, services.getNamespaces());

    @Test
    public void testAttachCommentsCompilationUnit_AssertsFalse() throws IOException {
        File inputFile = new File(FindResources.getTestResourcesDirectory(),
                "de/uka/ilkd/key/java/recoderext/AssertsFalse.java");
        final CompilationUnit cu = getCompilationUnit(inputFile);

        Optional<Method> om = findMethod(cu, "AssertsFalse", "m");
        System.out.println(cu);
        Assert.assertTrue("Could not find method AssertsFalse#m()", om.isPresent());
        MethodDeclaration m = (MethodDeclaration) om.get();
        assertContainsComment(m, it -> it.startsWith("/*@ normal_behavior"));

        Statement last = lastStatement(m);
        Assert.assertTrue(last instanceof EmptyStatement);
        assertContainsComment((JavaProgramElement) last, it -> it.equals("//@ assert false;"));
    }


    @Test
    public void testAttachCommentsCompilationUnit_Steinhofel1() throws IOException {
        File inputFile = new File(FindResources.getTestResourcesDirectory(),
                "de/uka/ilkd/key/java/recoderext/Steinhoefel1.java");
        final CompilationUnit cu = getCompilationUnit(inputFile);

        Optional<Method> ofib = findMethod(cu, "Steinhoefel1", "fib");
        System.out.println(cu);
        Assert.assertTrue("Could not find method Steinhoefel1#fib()", ofib.isPresent());
        MethodDeclaration m = (MethodDeclaration) ofib.get();
        assertContainsComment(m, it -> it.startsWith("/*@ public normal_behavior"));

        LocalVariableDeclaration ghost1 = (LocalVariableDeclaration) m.getBody().getStatementAt(2);
        Assert.assertTrue(ghost1.getDeclarationSpecifiers().get(0) instanceof Ghost);
        Assert.assertEquals("k0_old", ghost1.getVariables().get(0).getName());

        LocalVariableDeclaration ghost2 = (LocalVariableDeclaration) m.getBody().getStatementAt(3);
        Assert.assertTrue(ghost2.getDeclarationSpecifiers().get(0) instanceof Ghost);
        Assert.assertEquals("k1_old", ghost2.getVariables().get(0).getName());

        For forLoop = (For) m.getBody().getStatementAt(4); //retrieve the for loop
        assertContainsComment(forLoop, it -> it.equals("//@ ghost int k0_old = k0;"));
        assertContainsComment(forLoop, it -> it.equals("//@ ghost int k1_old = k1;"));
        assertContainsComment(forLoop, it -> it.startsWith("/*@ loop_invariant"));

        LocalVariableDeclaration ghost3 = (LocalVariableDeclaration) m.getBody().getStatementAt(2);
        Assert.assertTrue(ghost3.getDeclarationSpecifiers().get(0) instanceof Ghost);
        Assert.assertEquals("k0_old", ghost3.getVariables().get(0).getName());

        LocalVariableDeclaration ghost4 = (LocalVariableDeclaration) m.getBody().getStatementAt(3);
        Assert.assertTrue(ghost4.getDeclarationSpecifiers().get(0) instanceof Ghost);
        Assert.assertEquals("k1_old", ghost4.getVariables().get(0).getName());

        EmptyStatement lastStatementInForLoop = (EmptyStatement) lastStatement((StatementBlock) forLoop.getBody());
        assertContainsComment(lastStatementInForLoop, it -> it.equals("//@ set k0_old = k0;"));
        assertContainsComment(lastStatementInForLoop, it -> it.equals("//@ set k1_old = k1;"));

    }


    @Test
    public void testAttachCommentsCompilationUnit_SmansEtAlArrayList() throws IOException {
        File inputFile = new File("../key.ui/examples/heap/SmansEtAl/src/ArrayList.java");
        File expectedFile = new File(FindResources.getTestResourcesDirectory(),
                "de/uka/ilkd/key/java/testAttachCommentsCompilationUnit_SmansEtAlArrayList.txt");
        String expected = IOUtil.readFrom(expectedFile);
        final CompilationUnit cu = getCompilationUnit(inputFile);

        //Optional<Method> ofib = findMethod(cu, "Steinhoefel1", "fib");

        String out = getActualResult(cu);
        System.out.println(out);
        Assert.assertEquals("Difference in attached comments", expected, out);
        /*
        Assert.assertTrue("Could not find method Steinhoefel1#fib()", ofib.isPresent());
        MethodDeclaration m = (MethodDeclaration) ofib.get();
        assertContainsComment(m, it -> it.startsWith("/*@ public normal_behavior"));

        LocalVariableDeclaration ghost1 = (LocalVariableDeclaration) m.getBody().getStatementAt(2);
        Assert.assertTrue(ghost1.getDeclarationSpecifiers().get(0) instanceof Ghost);
        Assert.assertEquals("k0_old", ghost1.getVariables().get(0).getName());

        LocalVariableDeclaration ghost2 = (LocalVariableDeclaration) m.getBody().getStatementAt(3);
        Assert.assertTrue(ghost2.getDeclarationSpecifiers().get(0) instanceof Ghost);
        Assert.assertEquals("k1_old", ghost2.getVariables().get(0).getName());

        For forLoop = (For) m.getBody().getStatementAt(4); //retrieve the for loop
        assertContainsComment(forLoop, it -> it.equals("//@ ghost int k0_old = k0;"));
        assertContainsComment(forLoop, it -> it.equals("//@ ghost int k1_old = k1;"));
        assertContainsComment(forLoop, it -> it.startsWith("/*@ loop_invariant"));

        LocalVariableDeclaration ghost3 = (LocalVariableDeclaration) m.getBody().getStatementAt(2);
        Assert.assertTrue(ghost3.getDeclarationSpecifiers().get(0) instanceof Ghost);
        Assert.assertEquals("k0_old", ghost3.getVariables().get(0).getName());

        LocalVariableDeclaration ghost4 = (LocalVariableDeclaration) m.getBody().getStatementAt(3);
        Assert.assertTrue(ghost4.getDeclarationSpecifiers().get(0) instanceof Ghost);
        Assert.assertEquals("k1_old", ghost4.getVariables().get(0).getName());

        EmptyStatement lastStatementInForLoop = (EmptyStatement) lastStatement((StatementBlock) forLoop.getBody());
        assertContainsComment(lastStatementInForLoop, it -> it.equals("//@ set k0_old = k0;"));
        assertContainsComment(lastStatementInForLoop, it -> it.equals("//@ set k1_old = k1;"));
        */
    }


    @Test
    public void testAttachCommentsCompilationUnit_LockSpec() throws IOException {
        File inputFile = new File("../key.ui/examples/heap/permissions/lockspec/src/LockSpec.java");
        File expectedFile = new File(FindResources.getTestResourcesDirectory(),
                "de/uka/ilkd/key/java/testAttachCommentsCompilationUnit_LockSpec.txt");
        String expected = IOUtil.readFrom(expectedFile);
        final CompilationUnit cu = getCompilationUnit(inputFile);

        String out = getActualResult(cu);
        System.out.println(out);
        Assert.assertEquals("Difference in attached comments", expected, out);
    }


    private String getActualResult(CompilationUnit cu) {
        Function<String, String> prepareComment = it ->
                it.substring(0, Math.min(50, it.length())).replace('\n', ' ').trim();

        StringWriter out = new StringWriter();
        PrintWriter actual = new PrintWriter(out);
        TreeWalker walker = new TreeWalker(cu);
        while (walker.next()) {
            ProgramElement pe = walker.getProgramElement();
            ASTList<Comment> b = pe.getComments();
            if (b != null && !b.isEmpty()) {
                actual.format("(%d/%d) -- %s\n",
                        pe.getStartPosition().getLine(),
                        pe.getEndPosition().getLine(),
                        pe.getClass().getName());
                for (Comment comment : pe.getComments()) {
                    actual.format("  * %s\n", prepareComment.apply(comment.getText()));
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
        Optional<Comment> search = haystack.stream()
                .filter(it -> needle.test(it.getText()))
                .findFirst();

        //Debug
        //haystack.forEach(it -> System.out.println(it.getText()));
        Assert.assertTrue("Could not find comment satisfying the given predicate.",
                search.isPresent());
    }

    private CompilationUnit getCompilationUnit(File inputFile) throws IOException {
        Assume.assumeTrue("Required input file " + inputFile + " does not exists!", inputFile.exists());
        String content = IOUtil.readFrom(inputFile);
        return r2k.recoderCompilationUnits(new String[]{content}).get(0);
    }

    private Optional<Method> findMethod(CompilationUnit cu, String className, String methodName) {
        for (int i = 0; i < cu.getTypeDeclarationCount(); i++) {
            TypeDeclaration td = cu.getTypeDeclarationAt(i);
            if (td instanceof ClassDeclaration) {
                ClassDeclaration clazz = (ClassDeclaration) td;
                if (clazz.getName().equals(className)) {
                    return clazz.getMethods().stream()
                            .filter(it -> it.getName().equals(methodName))
                            .findFirst();
                }
            }
        }
        return Optional.empty();
    }
}
