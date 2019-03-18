package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.KeYLexerF;
import de.uka.ilkd.key.parser.KeYParserF;
import de.uka.ilkd.key.parser.ParserMode;
import de.uka.ilkd.key.rule.TacletForTests;
import de.uka.ilkd.key.smt.IllegalFormulaException;
import org.antlr.runtime.RecognitionException;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import java.io.*;

public class NewSMTTTest {

    private static final String TEST_DIR = "/home/jonas/tmp/smttest/";
    private Services services;
    private NamespaceSet nss;
    private TermBuilder tb;
    private ModularSMTLib2Translator trans;
    private MasterHandler mh;
    private static Sort intSort;
    private static Sort boolSort;
    private static Sort heapSort;
    private static Sort objectSort;
    private static Sort fieldSort;
    private static Sort intArraySort;

    private FileWriter fw = null;


    @Before
    public void setup() {
        this.services = TacletForTests.services();
        nss = services.getNamespaces();
        intSort = nss.sorts().lookup("int");
        boolSort = nss.sorts().lookup("boolean");
        heapSort = nss.sorts().lookup("Heap");
        objectSort = nss.sorts().lookup("java.lang.Object");
        fieldSort = nss.sorts().lookup("Field");
        intArraySort = nss.sorts().lookup("int[]");
        this.tb = services.getTermBuilder();
        this.trans = new ModularSMTLib2Translator();
        this.mh = new MasterHandler(services);
    }

    private Term s2t(String str) {
        KeYLexerF l = new KeYLexerF(str, null);
        KeYParserF p = new KeYParserF(ParserMode.TERM, l, services, nss);
        Term t = null;
        try {
            t = p.term();
        } catch (RecognitionException e) {
            e.printStackTrace();
        }
        return t;
    }

    private void writeToTestFile(File file, String s) throws IOException {
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
        BufferedWriter writer = new BufferedWriter(fw);
        writer.write(s);
        writer.flush();
        writer.close();
    }

    @Test
    public void testLt() {
        LocationVariable xSym = new LocationVariable(new ProgramElementName("x"), intSort);
        Term x = tb.var(xSym);
        Term t = tb.lt(x, x);
        Assert.assertEquals("(< (u2i ui_x) (u2i ui_x))", mh.translate(t).toString());
    }

    @Test
    public void testGt() {

        LocationVariable xSym = new LocationVariable(new ProgramElementName("x"), intSort);
        LocationVariable ySym = new LocationVariable(new ProgramElementName("y"), intSort);
        Term x = tb.var(xSym);
        Term y = tb.var(ySym);
        Term t = tb.gt(x, y);
        Assert.assertEquals("(> (u2i ui_x) (u2i ui_y))", mh.translate(t).toString());
    }

    @Test
    public void testArithmeticOps() {
        LocationVariable xSym = new LocationVariable(new ProgramElementName("x"), intSort);
        LocationVariable ySym = new LocationVariable(new ProgramElementName("y"), intSort);
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
        Term t1 = tb.zTerm(42);
        String expected1 = "42";
        Assert.assertEquals(expected1, mh.translate(t1).toString());
        Term t2 = tb.zTerm(-42);
        String expected2 = "-42";
        Assert.assertEquals(expected2, mh.translate(t2).toString());
        Term t3 = tb.zTerm(-0);
        String expected3 = "0";
        Assert.assertEquals(expected3, mh.translate(t3).toString());
    }

    @Test
    public void quantifierTest() {
        LocationVariable xSym = new LocationVariable(new ProgramElementName("x"), intSort);
        LocationVariable ySym = new LocationVariable(new ProgramElementName("y"), intSort);
        LogicVariable xVar = new LogicVariable(new Name("x"), intSort);
        LogicVariable yVar = new LogicVariable(new Name("y"), intSort);
        Term x = tb.var(xSym);
        Term y = tb.var(ySym);
        Term all = tb.all(yVar, tb.all(xVar, tb.gt(tb.add(x, y), x)));
        String expected = "(forall ((var_y U)) (forall ((var_x U)) " +
                "(> (+ (u2i ui_x) (u2i ui_y)) (u2i ui_x))))";
        Assert.assertEquals(
                expected, mh.translate(all).toString());
    }

    @Test
    public void q2Test() throws IllegalFormulaException, IOException {
        String st = "\\forall int x; \\forall int y; x != y";
        Term all = s2t(st);
         String ts = trans.translateProblem(all, services, null).toString();
        File quantTestFile = new File(TEST_DIR + "QuantTest.smt2");
        writeToTestFile(quantTestFile, ts);

        String expected = "(forall ((var_x U)) (forall ((var_y U)) (not (= var_x var_y))))";
        Assert.assertEquals(expected, mh.translate(all).toString());
    }

    @Test
    public void testContraposition() throws IllegalFormulaException, IOException {
        Function pSym = new Function(new Name("p"), Sort.FORMULA);
        Function qSym = new Function(new Name("q"), Sort.FORMULA);

        Term p = tb.func(pSym);
        Term q = tb.func(qSym);

        Term cp = tb.imp(tb.imp(p, q), tb.imp(tb.not(q), tb.not(p)));
        String ts = trans.translateProblem(cp, services, null).toString();
        File cptest = new File(TEST_DIR + "CPTest.smt2");
        writeToTestFile(cptest, ts);
        Assert.assertTrue(solverReturnsUnsat(TEST_DIR + "CPTest.smt2"));
        String expected = "(=> (=> (u2b ui_p) (u2b ui_q)) (=> (not (u2b ui_q)) (not (u2b ui_p))))";
        Assert.assertEquals(
                expected, mh.translate(cp).toString());
    }

    @Test
    public void selectTest() throws IllegalFormulaException, IOException {
        Term h = tb.var(new LogicVariable(new Name("h"), heapSort));
        Term o = tb.var(new LogicVariable(new Name("o"), objectSort));
        Term f = tb.var(new LogicVariable(new Name("f"), fieldSort));
        Term a = tb.var(new LogicVariable(new Name("a"), intArraySort));
        Term arr = tb.var(new LogicVariable(new Name("arr(i)"), fieldSort));
        Term selA = tb.select(intSort, h, o, f);
        Term selB = tb.select(intSort, h, a, arr);
        Term and = tb.equals(selA, selB);
        String ts = trans.translateProblem(and, services, null).toString();
        File quantTestFile = new File(TEST_DIR + "QuantTest.smt2");
        writeToTestFile(quantTestFile, ts);
        String exp = "(= (cast (select var_h var_o var_f) sort_int) " +
                "(cast (select var_h var_a |var_arr(i)|) sort_int))";
        Assert.assertEquals(exp, mh.translate(and, SExpr.Type.BOOL).toString());
    }

    @Test
    public void heapTest() throws IllegalFormulaException, IOException {
        LocationVariable xVar = new LocationVariable(new ProgramElementName("x"), intSort);
        Term x = tb.var(xVar);
        Term h = tb.var(new LocationVariable(new ProgramElementName("h"), heapSort));
        Term o = tb.var(new LocationVariable(new ProgramElementName("o"), objectSort));
        Term f = tb.var(new LocationVariable(new ProgramElementName("f"), fieldSort));
        Term storeTerm = tb.store(h, o, f, x);
        Term selectTerm = tb.select(intSort, storeTerm, o, f);
        Term eqTerm = tb.equals(selectTerm, x);
        String ts = trans.translateProblem(eqTerm, services, null).toString();
        String testFP = TEST_DIR + "HeapTest.smt2";
        File heapTestFile = new File(testFP);
        writeToTestFile(heapTestFile, ts);
        String exp = "(= (cast (select (keystore var_h var_o var_f var_x) " +
                "var_o var_f) sort_int) var_x)";
        Assert.assertEquals(exp, mh.translate(eqTerm, SExpr.Type.BOOL).toString());
        Assert.assertTrue(solverReturnsUnsat(testFP));
    }

    @Test
    public void castTest() throws IllegalFormulaException, IOException {
        LogicVariable xVar = new LogicVariable(new ProgramElementName("x"), intSort);
        LogicVariable yVar = new LogicVariable(new ProgramElementName("y"), intSort);
        Term cast = tb.equals(tb.cast(intSort, tb.var(xVar)), tb.var(yVar));
        String ts = trans.translateProblem(cast, services, null).toString();
        File castTestFile = new File(TEST_DIR + "CastTest.smt2");
        writeToTestFile(castTestFile, ts);
        Assert.assertEquals("(= (cast var_x sort_int) var_y)",
                mh.translate(cast, SExpr.Type.BOOL).toString());
    }

    @Test
    public void instanceOfTest() throws IllegalFormulaException, IOException {
        LocationVariable xSym = new LocationVariable(new ProgramElementName("x"), intSort);
        Term x = tb.var(xSym);
        Term iot = tb.func(intSort.getInstanceofSymbol(services), x);
        String ts = trans.translateProblem(iot, services, null).toString();
        String pathname = TEST_DIR + "InstOfTest.smt2";
        File instofTestFile = new File(pathname);
        writeToTestFile(instofTestFile, ts);
        Assert.assertTrue(solverReturnsUnsat(pathname));
        Assert.assertEquals("(instanceof ui_x sort_int)",
                mh.translate(iot, SExpr.Type.BOOL).toString());
    }

    @Test
    public void updAppTest() throws IllegalFormulaException, IOException {
        LocationVariable xVar = new LocationVariable(new ProgramElementName("x"), intSort);
        LocationVariable yVar = new LocationVariable(new ProgramElementName("y"), intSort);
        LocationVariable zVar = new LocationVariable(new ProgramElementName("z"), intSort);
        Term x = tb.var(xVar);
        Term y = tb.var(yVar);
        Term z = tb.var(zVar);
        Term add = tb.add(x, y);
        Term elemUpd = tb.elementary(x, z);
        Term updApp = tb.apply(elemUpd, add);
        String ts = trans.translateProblem(updApp, services, null).toString();
        File updAppTestFile = new File(TEST_DIR + "UpdAppTest.smt2");
        writeToTestFile(updAppTestFile, ts);
        String expected = "(apply-update (elementary-update x_Var z_Var) (+ x_Var z_Var))";
        Assert.assertEquals(expected, mh.translate(updApp, SExpr.Type.BOOL).toString());
    }

    /**
     * This method runs the Z3 solver on the specified file. It can be used to quickly test whether
     * a translation works as expected.
     * Bear in mind that the solver could time out, or behave weirdly in some unexpected manner.
     * Use as a sanity check, but not as final truth
     * @param filePath the path to the smt file
     * @return true if the solver returns unsat (for us, this means that the corresponding formula
     * is valid!)
     */
    private boolean solverReturnsUnsat(String filePath) {
        Runtime runtime = Runtime.getRuntime();
        String[] commands  = {"z3", "-T:5", filePath};
        Process process;
        try {
            process = runtime.exec(commands);
        } catch (IOException e) {
            e.printStackTrace();
            return false;
        }

        BufferedReader lr = new BufferedReader(new InputStreamReader(process.getInputStream()));
        return lr.lines().anyMatch(s -> s.equals("unsat"));
    }
}