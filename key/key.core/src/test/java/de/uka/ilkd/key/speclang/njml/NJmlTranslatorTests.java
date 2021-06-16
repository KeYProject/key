package de.uka.ilkd.key.speclang.njml;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLConstruct;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLMethodDecl;
import de.uka.ilkd.key.util.HelperClassForTests;
import org.junit.Test;
import org.key_project.util.collection.ImmutableList;

import java.io.File;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;

/**
 * @author Alexander Weigl
 * @version 1 (6/1/21)
 */
public class NJmlTranslatorTests {
    public static final String testFile = HelperClassForTests.TESTCASE_DIRECTORY
            + File.separator + "speclang"
            + File.separator + "testFile.key";
    private TermBuilder TB;
    private JavaInfo javaInfo;
    private JmlIO jmlIO;
    private Services services;
    private KeYJavaType testClassType;

    public NJmlTranslatorTests() {
        javaInfo = new HelperClassForTests().parse(
                new File(testFile)).getFirstProof().getJavaInfo();
        services = javaInfo.getServices();
        TB = services.getTermBuilder();
        testClassType = javaInfo.getKeYJavaType("testPackage.TestClass");
        jmlIO = new JmlIO().services(services).classType(testClassType);
    }

    @Test
    public void testModelMethodWithAtSignInBody() {
        ImmutableList<TextualJMLConstruct> result =
                jmlIO.parseClassLevel("/*@ model int f(int x) { \n" +
                        "@  return x+1; " +
                        "@ }*/", "Test.java", new Position(0, 0));
        assertNotNull(result);
        TextualJMLMethodDecl decl = (TextualJMLMethodDecl) result.head();
        assertEquals("int f (int x);", decl.getParsableDeclaration().trim());
        String eqString = Translator.getEqualityExpressionOfModelMethod(decl.getDecl());
        assertEquals("f(x) == (x+1)", eqString);
    }

    @Test
    public void testModelMethodWithAtSignInBody2() {
        ImmutableList<TextualJMLConstruct> result =
                jmlIO.parseClassLevel("/*@ model int f(int[] arr) { \n" +
                        "@  //this is a comment \n" +
                        "@  return arr[1]; //comment\n" +
                        "@ }*/", "Test.java", new Position(0, 0));
        assertNotNull(result);
        TextualJMLMethodDecl decl = (TextualJMLMethodDecl) result.head();
        assertEquals("int f (int[] arr);", decl.getParsableDeclaration().trim());
        String eqString = Translator.getEqualityExpressionOfModelMethod(decl.getDecl());
        assertEquals("f(arr) == (arr[1])", eqString);
    }

    @Test
    public void testWarnRequires() {
        jmlIO.clearWarnings();
        String contract = "/*@ requires true; ensures true; requires true;";
        ImmutableList<TextualJMLConstruct> result =
                jmlIO.parseClassLevel(contract, "Test.java", new Position(5, 5));
        assertNotNull(result);
        ImmutableList<PositionedString> warnings = jmlIO.getWarnings();
        PositionedString message = warnings.head();
        assertEquals(
                "Diverging Semantics form JML Reference: Requires does not initiate a new contract. " +
                        "See https://www.key-project.org/docs/user/JMLGrammar/#TODO (Test.java, 5/37)",
                message.toString());
    }
}
