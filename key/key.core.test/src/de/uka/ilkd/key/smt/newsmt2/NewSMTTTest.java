package de.uka.ilkd.key.smt.newsmt2;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;

import org.antlr.runtime.RecognitionException;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;
import org.stringtemplate.v4.compiler.STParser.templateAndEOF_return;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.operator.Instanceof;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.KeYLexer;
import de.uka.ilkd.key.parser.KeYLexerF;
import de.uka.ilkd.key.parser.KeYParserF;
import de.uka.ilkd.key.parser.ParserMode;
import de.uka.ilkd.key.rule.TacletForTests;
import de.uka.ilkd.key.smt.IllegalFormulaException;

public class NewSMTTTest {

    private Services s;
    private NamespaceSet nss;
    private TermBuilder tb;
    private ModularSMTLib2Translator trans;
    private MasterHandler mh;
    private static Sort intType;
    private static Sort boolType;
    private static Sort heapType;
    private static Sort objectType;
    private static Sort fieldType;
    private static KeYJavaType javaInt;

    File file = new File("/home/i57/cnodes/jschiffl/tmp/smttest/smttestfile");
    FileWriter fw = null;
    BufferedWriter writer = null;

    @Before
    public void setup() {
        this.s = TacletForTests.services();
        nss = s.getNamespaces();
        intType = nss.sorts().lookup("int");
        boolType = nss.sorts().lookup("boolean");
        heapType = nss.sorts().lookup("Heap");
        objectType = nss.sorts().lookup("java.lang.Object");
        fieldType = nss.sorts().lookup("Field");
        this.tb = s.getTermBuilder();
        this.trans = new ModularSMTLib2Translator();
        this.mh = new MasterHandler(s);
        javaInt = s.getJavaInfo().getKeYJavaType(intType);
    }

    private Term s2t(String str) {
        KeYLexerF l = new KeYLexerF(str, null);
        KeYParserF p = new KeYParserF(ParserMode.TERM, l, s, nss);
        Term t = null;
        try {
            t = p.term();
        } catch (RecognitionException e) {
            e.printStackTrace();
        }
        return t;
    }

    private void writeToTestFile(String s) throws IOException {
        try {
            file.delete();
            file.createNewFile();
        } catch (IOException e1) {
            e1.printStackTrace();
        }
        try {
            fw = new FileWriter(file);
        } catch (IOException e) {
            e.printStackTrace();
        }
        writer = new BufferedWriter(fw);
        writer.write(s);
        writer.flush();
        writer.close();
    }

    @Test
    public void testLt() {
        LocationVariable xSym = new LocationVariable(new ProgramElementName("x"), intType);
        Term x = tb.var(xSym);
        Term t = tb.lt(x, x);
        Assert.assertEquals("(< (u2i ui_x) (u2i ui_x))", mh.translate(t).toString());
    }

    @Test
    public void testGt() {

        LocationVariable xSym = new LocationVariable(new ProgramElementName("x"), intType);
        LocationVariable ySym = new LocationVariable(new ProgramElementName("y"), intType);
        Term x = tb.var(xSym);
        Term y = tb.var(ySym);
        Term t = tb.gt(x, y);
        Assert.assertEquals("(> (u2i ui_x) (u2i ui_y))", mh.translate(t).toString());
    }

    @Test
    public void testArithmeticOps() {
        LocationVariable xSym = new LocationVariable(new ProgramElementName("x"), intType);
        LocationVariable ySym = new LocationVariable(new ProgramElementName("y"), intType);
        Term x = tb.var(xSym);
        Term y = tb.var(ySym);
        Term plus = tb.add(x, y);
        Assert.assertEquals("(+ (u2i ui_x) (u2i ui_y))", mh.translate(plus).toString());
    }

    @Test
    public void testBoolConnectives() {

        Function pSym = new Function(new Name("p"), Sort.FORMULA);
        Function qSym = new Function(new Name("q"), Sort.FORMULA);

        Term and = tb.and(tb.func(pSym), tb.func(qSym));
        Term or = tb.or(tb.func(pSym), tb.func(qSym));
        Assert.assertEquals("(and (u2b ui_p) (u2b ui_q))", mh.translate(and).toString());
        Assert.assertEquals("(or (u2b ui_p) (u2b ui_q))", mh.translate(or).toString());
    }

    @Test
    public void numberConstants() {

    }

    @Test
    public void quantifierTest() {
        LocationVariable xSym = new LocationVariable(new ProgramElementName("x"), intType);
        LocationVariable ySym = new LocationVariable(new ProgramElementName("y"), intType);
        LogicVariable xVar = new LogicVariable(new Name("x"), intType);
        LogicVariable yVar = new LogicVariable(new Name("y"), intType);
        Term x = tb.var(xSym);
        Term y = tb.var(ySym);
        Term all = tb.all(yVar, tb.all(xVar, tb.gt(tb.add(x, y), x)));
        Assert.assertEquals(
                "(forall ((var_y u)) (forall ((var_x u)) (> (+ (u2i ui_x) (u2i ui_y)) (u2i ui_x))))",
                mh.translate(all).toString());
    }

    @Test
    public void q2Test() throws IllegalFormulaException, IOException {
        String st = "\\forall int x; \\forall int y; x != y";
        Term all = s2t(st);
        // String ts = trans.translateProblem(all, s, null).toString();
        // writeToTestFile(ts);

        Assert.assertEquals("(forall ((var_x u)) (forall ((var_y u)) (not (= var_x var_y))))",
                mh.translate(all).toString());
    }

    @Test
    public void testContraposition() throws IllegalFormulaException, IOException {
        Function pSym = new Function(new Name("p"), Sort.FORMULA);
        Function qSym = new Function(new Name("q"), Sort.FORMULA);

        Term p = tb.func(pSym);
        Term q = tb.func(qSym);

        Term cp = tb.imp(tb.imp(p, q), tb.imp(tb.not(q), tb.not(p)));

        Assert.assertEquals(
                "(=> (=> (u2b ui_p) (u2b ui_q)) (=> (not (u2b ui_q)) (not (u2b ui_p))))",
                mh.translate(cp).toString());
    }

    @Test
    public void selectTest() throws IllegalFormulaException, IOException {
        Function select = new Function(new Name("select"), Sort.ANY, heapType);
        Term h = tb.var(new LocationVariable(new ProgramElementName("h"), heapType));
        LocationVariable x = new LocationVariable(new ProgramElementName("x"), intType);

        Term sel = tb.equals(tb.var(x), tb.func(select, h));
        // String ts = trans.translateProblem(sel, s, null).toString();
        // writeToTestFile(ts);
        Assert.assertEquals("(ui_select ui_h ui_o ui_f)", mh.translate(sel).toString());
    }

    @Test
    public void instanceOfTest() throws IllegalFormulaException, IOException {
        LogicVariable xVar = new LogicVariable(new ProgramElementName("x"), intType);
        // TypeRef tr = new TypeRef(javaInt);
        Term iot = tb.instance(intType, tb.var(xVar)); // TODO nicht was ich
                                                       // will
        String ts = trans.translateProblem(iot, s, null).toString();
        writeToTestFile(ts);
        Assert.assertEquals("", mh.translate(iot, SExpr.Type.BOOL).toString());
    }
}


