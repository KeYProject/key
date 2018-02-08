package de.uka.ilkd.key.smt.newsmt2;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.TacletForTests;
import de.uka.ilkd.key.smt.IllegalFormulaException;

public class NewSMTTTest {

    private Services s;
    private TermBuilder tb;
    private MasterHandler mh;
    private static Sort intType;
    private static Sort boolType;

    @Before
    public void setup() {
        this.s = TacletForTests.services();
        this.tb = s.getTermBuilder();
        this.mh = new MasterHandler(s);
        intType = s.getNamespaces().sorts().lookup("int");
        boolType = s.getNamespaces().sorts().lookup("boolean");
    }

    @Test
    public void test() throws IllegalFormulaException {

        LocationVariable jonasSym = new LocationVariable(new ProgramElementName("jonas"), intType);

        Term jonas = tb.var(jonasSym);
        Term testAnd = tb.lt(jonas, jonas);
        Assert.assertEquals("(< (u2i ui_jonas) (u2i ui_jonas))", mh.translate(testAnd).toString());
    }

    @Test
    public void testContraposition() {
        LocationVariable pSym = new LocationVariable(new ProgramElementName("p"), boolType);
        LocationVariable qSym = new LocationVariable(new ProgramElementName("q"), boolType);

        Term p = tb.convertToFormula(tb.var(pSym)); // That does not really make
                                                    // sense
        Term q = tb.convertToFormula(tb.var(qSym));

        Term cp = tb.imp(tb.imp(p, q), tb.imp(tb.not(q), tb.not(p)));
        System.out.println(cp);
        Assert.assertEquals("...", mh.translate(cp));
    }
}


