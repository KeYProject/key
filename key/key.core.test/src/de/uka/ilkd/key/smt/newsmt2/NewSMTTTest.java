package de.uka.ilkd.key.smt.newsmt2;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.TacletForTests;
import de.uka.ilkd.key.smt.IllegalFormulaException;

public class NewSMTTTest {

    private Services s;
    private TermBuilder tb;
    private MasterHandler mh;
    private static Sort intType;
    private static Sort boolType;
    private static Sort formulaType;

    @Before
    public void setup() {
        this.s = TacletForTests.services();
        this.tb = s.getTermBuilder();
        this.mh = new MasterHandler(s);
        intType = s.getNamespaces().sorts().lookup("int");
        boolType = s.getNamespaces().sorts().lookup("boolean");
        formulaType = Sort.FORMULA;
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
        LocationVariable pSym = new LocationVariable(new ProgramElementName("p"), boolType);
        LocationVariable qSym = new LocationVariable(new ProgramElementName("q"), boolType);

        LogicVariable b = new LogicVariable(new Name("b"), Sort.FORMULA);
        LogicVariable a = new LogicVariable(new Name("a"), Sort.FORMULA);
        Term and = tb.and(tb.var(a), tb.var(b));
        Assert.assertEquals("(and (u2i ui_x) (u2i ui_y))", mh.translate(and));

        Term and1 = tb.and(tb.convertToFormula(tb.var(pSym)), tb.convertToFormula(tb.var(qSym)));
        Term andTf = tb.tf().createTerm(s.getTypeConverter().getIntegerLDT().getAdd(), tb.var(pSym),
                tb.var(qSym));
        Assert.assertEquals("(and (u2i ui_x) (u2i ui_y))", mh.translate(and1));
        Assert.assertEquals("(and (u2i ui_x) (u2i ui_y))", mh.translate(andTf));
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
        Assert.assertEquals("(forall ((x int) (y int)) > ((+ (x y)) x))", mh.translate(all));
    }

    @Test
    public void testContraposition() {
        LocationVariable pSym = new LocationVariable(new ProgramElementName("p"), boolType);
        LocationVariable qSym = new LocationVariable(new ProgramElementName("q"), boolType);

        Term p = tb.convertToFormula(tb.var(pSym)); // That does not really make
                                                    // sense
        Term q = tb.convertToFormula(tb.var(qSym));

        Term cp = tb.imp(tb.imp(p, q), tb.imp(tb.not(q), tb.not(p)));
        Assert.assertEquals("...", mh.translate(cp));
    }
}


