/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import java.util.Collections;
import java.util.Iterator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.operator.PostIncrement;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.logic.sort.SortImpl;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.rule.AntecTaclet;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.inst.InstantiationEntry;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.tacletbuilder.AntecTacletBuilder;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMapEntry;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;


public class TestVariableNamer {


    private final Proof proof = new Proof("TestVariableNamer",
        new InitConfig(new Services(AbstractProfile.getDefaultProfile())));
    private final Services services = proof.getServices();
    private final ProgramVariable x = constructProgramVariable("x");
    private final ProgramVariable xx = constructProgramVariable("x");
    private final ProgramVariable y = constructProgramVariable("y");
    private final ProgramVariable x_1 = constructProgramVariable("x_1");
    private final ProgramVariable x_2 = constructProgramVariable("x_2");
    private final ProgramVariable var_1 = constructProgramVariable("var_1");
    private final ProgramVariable var_2 = constructProgramVariable("var_2");
    private final SequentFormula formulaWithX = constructFormula(x);
    private final SequentFormula formulaWithX_1 = constructFormula(x_1);
    private final SequentFormula formulaWithVar_1 = constructFormula(var_1);
    private final SchemaVariable variableSV = SchemaVariableFactory
            .createProgramSV(new ProgramElementName("sv"), ProgramSVSort.VARIABLE, false);


    private ProgramVariable constructProgramVariable(ProgramElementName name) {
        KeYJavaType myKeyJavaType = new KeYJavaType(new SortImpl(new Name("mysort")));
        return new LocationVariable(name, myKeyJavaType);
    }

    private ProgramVariable constructProgramVariable(String name) {
        ProgramElementName pen = VariableNamer.parseName(name);
        assertEquals(pen.toString(), name);
        return constructProgramVariable(pen);
    }

    private SequentFormula constructFormula(ProgramVariable containedVar) {
        Statement statement = new PostIncrement(containedVar);
        StatementBlock statementBlock = new StatementBlock(statement);
        JavaBlock javaBlock = JavaBlock.createJavaBlock(statementBlock);

        Term term = services.getTermBuilder().dia(javaBlock, services.getTermBuilder().tt());

        return new SequentFormula(term);
    }


    private PosInOccurrence constructPIO(SequentFormula formula) {
        return new PosInOccurrence(formula, PosInTerm.getTopLevel(), true);
    }


    private Goal constructGoal(SequentFormula containedFormula) {
        Semisequent empty = Semisequent.EMPTY_SEMISEQUENT;
        Semisequent ante = empty.insert(0, containedFormula).semisequent();

        Sequent seq = Sequent.createSequent(ante, empty);
        Node node = new Node(proof, seq);

        TacletIndex tacletIndex = TacletIndexKit.getKit().createTacletIndex();
        BuiltInRuleAppIndex builtInRuleAppIndex = new BuiltInRuleAppIndex(new BuiltInRuleIndex());
        return new Goal(node, tacletIndex, builtInRuleAppIndex, proof.getServices());
    }


    private void addGlobal(Goal goal, ProgramVariable var) {
        goal.getLocalNamespaces().programVariables().addSafely(var);
        goal.node().addLocalProgVars(Collections.singletonList(var));
    }


    private boolean inGlobals(Goal goal, ProgramVariable globalVar) {
        return goal.node().getLocalProgVars().contains(globalVar);
    }

    private void addTacletApp(Goal goal, ProgramVariable containedVar) {
        Term findTerm = services.getTermBuilder().tt();
        AntecTacletBuilder builder = new AntecTacletBuilder();
        builder.setFind(findTerm);
        AntecTaclet taclet = builder.getAntecTaclet();
        NoPosTacletApp app = NoPosTacletApp.createNoPosTacletApp(taclet);

        SchemaVariable sv = SchemaVariableFactory.createProgramSV(new ProgramElementName("sv"),
            ProgramSVSort.STATEMENT, false);
        Statement statement = new PostIncrement(containedVar);
        app = (NoPosTacletApp) app.addCheckedInstantiation(sv, statement,
            goal.proof().getServices(), false);

        goal.ruleAppIndex().tacletIndex().add(app);
    }


    private boolean inTacletApps(Goal goal, ProgramVariable containedVar) {
        RuleAppIndex ruleAppIndex = goal.ruleAppIndex();
        TacletIndex tacletIndex = ruleAppIndex.tacletIndex();
        ImmutableList<NoPosTacletApp> noPosTacletApps = tacletIndex.getPartialInstantiatedApps();

        for (NoPosTacletApp noPosTacletApp : noPosTacletApps) {
            SVInstantiations insts = noPosTacletApp.instantiations();
            Iterator<ImmutableMapEntry<SchemaVariable, InstantiationEntry<?>>> it2;
            it2 = insts.pairIterator();
            while (it2.hasNext()) {
                ImmutableMapEntry<SchemaVariable, InstantiationEntry<?>> e = it2.next();
                Object inst = e.value().getInstantiation();
                if (inst instanceof PostIncrement
                        && ((PostIncrement) inst).getFirstElement() == containedVar) {
                    return true;
                }
            }
        }

        return false;
    }


    @Test
    private void testTemporaryNames(VariableNamer vn) {
        ProgramElementName name = vn.getTemporaryNameProposal("x");
        assertNotEquals("x", name.getProgramName());

        ProgramVariable v = constructProgramVariable(name);
        SequentFormula formula = constructFormula(v);
        Goal goal = constructGoal(formula);
        PosInOccurrence pio = constructPIO(formula);
        v = vn.rename(v, goal, pio);
        assertEquals("x", v.getProgramElementName().getProgramName());
    }


    @Test
    public void testInnerRename() {
        VariableNamer vn = services.getVariableNamer();
        ProgramVariable v, w;

        PosInOccurrence pio = constructPIO(formulaWithX);
        Goal goal = constructGoal(formulaWithX);

        v = vn.rename(y, goal, pio);
        assertEquals("y", v.getProgramElementName().getProgramName());

        v = vn.rename(xx, goal, pio);
        assertEquals("x", v.getProgramElementName().getProgramName());

        // proof.getNamespaces().programVariables().addSafely(v);
        addGlobal(goal, v);
        w = vn.rename(x, goal, pio);
        assertEquals("x_1", w.getProgramElementName().getProgramName());
        assertTrue(inGlobals(goal, v));

        // Reset progVar namespace which was altered due to addGlobal()
        proof.getNamespaces().setProgramVariables(new Namespace<>());
        testTemporaryNames(vn);
    }



    // public void testInnerRenameInTacletApps() {
    // VariableNamer vn = services.getVariableNamer();
    // ProgramVariable v;
    //
    // PosInOccurrence pio = constructPIO(formulaWithX);
    // Goal goal = constructGoal(formulaWithX);
    // proof.getNamespaces().programVariables().addSafely(xx);
    // addGlobal(goal, xx);
    // addTacletApp(goal, x);
    //
    // v = vn.rename(x, goal, pio);
    // assertFalse(inTacletApps(goal, x));
    // assertTrue(inTacletApps(goal, v));
    // }

    @Test
    public void testNameProposals() {
        VariableNamer vn = services.getVariableNamer();
        ProgramElementName proposal;

        PosInOccurrence pio = constructPIO(formulaWithVar_1);
        Goal goal = constructGoal(formulaWithVar_1);

        proposal = vn.getNameProposalForSchemaVariable(null, variableSV, pio, null, null);
        assertEquals("var_2", proposal.toString());

        proof.getNamespaces().programVariables().addSafely(var_2);
        addGlobal(goal, var_2);

        proposal = vn.getNameProposalForSchemaVariable("var", variableSV, pio, null, null);
        assertEquals("var_2", proposal.toString());
    }


    @Test
    public void testInnerRenameUniqueness() {
        VariableNamer vn = services.getVariableNamer();
        ProgramVariable v;

        PosInOccurrence pio = constructPIO(formulaWithX_1);
        Goal goal = constructGoal(formulaWithX_1);
        proof.getNamespaces().programVariables().addSafely(xx);
        addGlobal(goal, xx);
        addTacletApp(goal, x_2);

        v = vn.rename(x, goal, pio);
        assertEquals("x_2", v.getProgramElementName().getProgramName());
    }
}
