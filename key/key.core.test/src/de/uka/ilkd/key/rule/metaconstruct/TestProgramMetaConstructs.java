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

/**
 * tests the symbolic execution of the program meta constructs
 */
package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.expression.Assignment;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.statement.Break;
import de.uka.ilkd.key.java.statement.LabeledStatement;
import de.uka.ilkd.key.java.statement.LoopInit;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.visitor.JavaASTCollector;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.rule.TacletForTests;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import junit.framework.TestCase;

public class TestProgramMetaConstructs extends TestCase {

    public TestProgramMetaConstructs(String name) {
        super(name);
        de.uka.ilkd.key.util.Debug.ENABLE_DEBUG = false;
    }

    public void setUp() {
    }

    public void testDoBreak() {
        LabeledStatement labeledBlock = (LabeledStatement) ((StatementBlock) TacletForTests
                .parsePrg
        // ("{l1:l2:{l3:{l4:break l3; int i = 0;} int j=1;}}")).getChildAt(0);
        ("{l4:break l3; int i = 0; int j=1;}")).getChildAt(0);
        DoBreak rmLabel = new DoBreak(labeledBlock);

        ProgramElement result = rmLabel.transform(rmLabel.body(),
            new Services(AbstractProfile.getDefaultProfile()),
            SVInstantiations.EMPTY_SVINSTANTIATIONS)[0];
        assertTrue(result instanceof Break);
    }

    /** tests AST walkers */
    public void xtestASTWalker() {
        ProgramElement block = TacletForTests.parsePrg(
            "{int a=5; test1:test2:while (true) " + "{test3: {int j=3;}}}");
        JavaASTCollector coll = new JavaASTCollector(block,
            de.uka.ilkd.key.java.statement.LabeledStatement.class);
        coll.start();
        assertTrue(coll.getNodes().size() == 3);

        ProgramElement block2 = TacletForTests
                .parsePrg("{while(true) {if (true) break; else continue;}}");
        WhileLoopTransformation trans = new WhileLoopTransformation(block2,
            new ProgramElementName("l1"), new ProgramElementName("l2"),
            new Services(AbstractProfile.getDefaultProfile()));
        trans.start();
        System.out.println("Result:" + trans);
    }

    public void testTypeOf() { // this is no really sufficient test
        Services services = new Services(AbstractProfile.getDefaultProfile());
        // but I can't access programs here
        StatementBlock block = (StatementBlock) TacletForTests
                .parsePrg(" { int i; int j; i=j; }");
        Expression expr = (Expression) ((Assignment) block.getStatementAt(2))
                .getChildAt(1);
        ProgramTransformer typeof = new TypeOf(expr);
        assertTrue(((TypeRef) typeof.transform(expr, services,
            SVInstantiations.EMPTY_SVINSTANTIATIONS)[0]).getName()
                    .equals("int"));
    }

    public void testBugId183() {
        StatementBlock bl = (StatementBlock) TacletForTests
                .parsePrg("{ while ( true ) {} }");
        LoopStatement l = (LoopStatement) bl.getChildAt(0);
        UnwindLoop wlt = new UnwindLoop(
            SchemaVariableFactory.createProgramSV(
                new ProgramElementName("inner"), ProgramSVSort.LABEL, false),
            SchemaVariableFactory.createProgramSV(
                new ProgramElementName("outer"), ProgramSVSort.LABEL, false),
            l);

        SVInstantiations inst = SVInstantiations.EMPTY_SVINSTANTIATIONS;
        try {
            wlt.transform(l, new Services(AbstractProfile.getDefaultProfile()),
                inst);
        } catch (java.util.NoSuchElementException e) {
            assertTrue(" Problem with empty while-blocks. See Bug #183 ",
                false);
        }

    }

    public void testForInitUnfoldTransformer1() {
        forInitUnfoldTransformerTest(
            "{ for (int i = 4, y = 42; i <= 6; i++) { } }",
            new String[] { "int i = 4,y = 42;" });
    }

    public void testForInitUnfoldTransformer2() {
        forInitUnfoldTransformerTest("{ for (int i = 4; i <= 6; i++) { } }",
            new String[] { "int i = 4;" });
    }

    // By Dominic
    public void testForInitUnfoldTransformer3() {
        forInitUnfoldTransformerTest(
            "{ int i = 4, z = 42; for (i++, i--, z = 17; i <= 6; i++) { } }",
            new String[] { "i++;", "i--;", "z=17;" });
    }

    private void forInitUnfoldTransformerTest(String programBlock,
            String[] expectedStmts) {
        final ProgramElement block = TacletForTests.parsePrg(programBlock);

        final JavaASTCollector coll = new JavaASTCollector(block,
            LoopInit.class);
        coll.start();

        assertEquals(1, coll.getNodes().size());

        final ForInitUnfoldTransformer tf = new ForInitUnfoldTransformer(
            (LoopInit) coll.getNodes().head());
        final Statement[] stmts = (Statement[]) tf.transform(
            coll.getNodes().head(),
            new Services(AbstractProfile.getDefaultProfile()),
            SVInstantiations.EMPTY_SVINSTANTIATIONS);

        assertEquals(expectedStmts.length, stmts.length);

        int i = 0;
        for (String stmt : expectedStmts) {
            assertEquals(stmt, stmts[i++].toString());
        }
    }
}
