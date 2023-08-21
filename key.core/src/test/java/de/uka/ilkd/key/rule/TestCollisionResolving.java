/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.control.instantiation_model.TacletFindModel;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * these tests are used to control if the collision mechanisms work correct. Collisions may be:
 * collisions between variablesv, with the context or or inside formula- and termsvs
 */
public class TestCollisionResolving {

    Sort s;
    Goal goal;
    Services services;

    @BeforeEach
    public void setUp() {
        TacletForTests.setStandardFile(TacletForTests.testRules);
        TacletForTests.parse();
        s = TacletForTests.getSorts().lookup(new Name("s"));

        services = TacletForTests.services();

        // build a goal (needed for creating TacletInstantiationsTableModel)
        Proof proof = new Proof("TestCollisionResolving", TacletForTests.initConfig());
        Semisequent empty = Semisequent.EMPTY_SEMISEQUENT;
        Sequent seq = Sequent.createSequent(empty, empty);

        Node node = new Node(proof, seq);
        TacletIndex tacletIndex = TacletIndexKit.getKit().createTacletIndex();
        BuiltInRuleAppIndex builtInRuleAppIndex = new BuiltInRuleAppIndex(null);
        goal = new Goal(node, tacletIndex, builtInRuleAppIndex, proof.getServices());
    }

    @AfterEach
    public void tearDown() {
        s = null;
        goal = null;
        services = null;
    }

    @Test
    public void testCollisionResolvingOfSchemaVariable() {
        // the term has to be built manually because we have to ensure
        // object equality of the LogicVariable x
        LogicVariable x = new LogicVariable(new Name("x"), s);
        Function p = new Function(new Name("p"), Sort.FORMULA, s);
        Function q = new Function(new Name("q"), Sort.FORMULA, s);

        Term t_x = services.getTermFactory().createTerm(x);
        Term t_p_x = services.getTermFactory().createTerm(p, new Term[] { t_x }, null, null);
        Term t_q_x = services.getTermFactory().createTerm(q, new Term[] { t_x }, null, null);
        TermBuilder tb = services.getTermBuilder();
        Term t_all_p_x = tb.all(x, t_p_x);
        Term t_ex_q_x = tb.ex(x, t_q_x);
        Term term = services.getTermFactory().createTerm(Junctor.AND, t_all_p_x, t_ex_q_x);
        FindTaclet coll_varSV =
            (FindTaclet) TacletForTests.getTaclet("TestCollisionResolving_coll_varSV").taclet();

        TacletApp result = NoPosTacletApp.createNoPosTacletApp(coll_varSV, coll_varSV.getMatcher()
                .matchFind(term, MatchConditions.EMPTY_MATCHCONDITIONS, services),
            services);

        SchemaVariable b = TacletForTests.getSchemaVariables().lookup(new Name("b"));
        SchemaVariable c = TacletForTests.getSchemaVariables().lookup(new Name("c"));
        SchemaVariable u = TacletForTests.getSchemaVariables().lookup(new Name("u"));
        SchemaVariable v = TacletForTests.getSchemaVariables().lookup(new Name("v"));

        SVInstantiations insts = result.instantiations();
        assertNotSame(((Term) insts.getInstantiation(b)).sub(0).op(),
            ((Term) insts.getInstantiation(c)).sub(0).op(),
            "Same object for different conceptual variables");
        assertSame(((Term) insts.getInstantiation(u)).op(),
            ((Term) insts.getInstantiation(b)).sub(0).op());
        assertSame(((Term) insts.getInstantiation(v)).op(),
            ((Term) insts.getInstantiation(c)).sub(0).op());
    }

    @Test
    public void testCollisionResolvingWithContext() {
        // the term has to be built manually because we have to ensure
        // object equality of the LogicVariable x
        LogicVariable x = new LogicVariable(new Name("x"), s);
        Function p = new Function(new Name("p"), Sort.FORMULA, s);
        Function q = new Function(new Name("q"), Sort.FORMULA, s);

        TermBuilder tb = services.getTermBuilder();

        final TermFactory tf = services.getTermFactory();

        Term t_x = tf.createTerm(x);
        Term t_p_x = tf.createTerm(p, new Term[] { t_x }, null, null);
        Term t_q_x = tf.createTerm(q, new Term[] { t_x }, null, null);


        Term t_ex_q_x = tb.ex(x, t_q_x);

        Term t_px_and_exxqx = tf.createTerm(Junctor.AND, t_p_x, t_ex_q_x);
        Term term = tb.all(x, t_px_and_exxqx);

        FindTaclet coll_varSV =
            (FindTaclet) TacletForTests.getTaclet("TestCollisionResolving_coll_context").taclet();

        PosInOccurrence pos =
            new PosInOccurrence(new SequentFormula(term), PosInTerm.getTopLevel().down(0), true);

        TacletApp result =
            PosTacletApp.createPosTacletApp(coll_varSV, coll_varSV.getMatcher().matchFind(
                term.sub(0), MatchConditions.EMPTY_MATCHCONDITIONS, services), pos, services);

        SchemaVariable b = TacletForTests.getSchemaVariables().lookup(new Name("b"));
        SchemaVariable c = TacletForTests.getSchemaVariables().lookup(new Name("c"));
        SchemaVariable u = TacletForTests.getSchemaVariables().lookup(new Name("u"));

        SVInstantiations insts = result.instantiations();
        assertNotSame(((Term) insts.getInstantiation(b)).sub(0).op(),
            ((Term) insts.getInstantiation(c)).sub(0).op(),
            "Same object for different conceptual variables");
        assertSame(((Term) insts.getInstantiation(u)).op(),
            ((Term) insts.getInstantiation(c)).sub(0).op());
    }

    @Test
    public void testVarNamespaceCreationWithContext() {
        Term term = TacletForTests.parseTerm("\\forall s x; p(x)");

        FindTaclet taclet =
            (FindTaclet) TacletForTests.getTaclet("TestCollisionResolving_ns1").taclet();
        PosInOccurrence pos =
            new PosInOccurrence(new SequentFormula(term), PosInTerm.getTopLevel().down(0), true);
        TacletApp app = PosTacletApp.createPosTacletApp(taclet,
            taclet.getMatcher().matchFind(term.sub(0), MatchConditions.EMPTY_MATCHCONDITIONS, null),
            pos, services);
        TacletApp app1 = app.prepareUserInstantiation(services);
        assertSame(app, app1);
        TacletFindModel instModel = new TacletFindModel(app, TacletForTests.services(),
            TacletForTests.getNamespaces(), TacletForTests.getAbbrevs(), goal);

        boolean exceptionthrown = false;
        try {
            app = instModel.createTacletAppFromVarInsts();
        } catch (IllegalStateException | SVInstantiationException e) {
            exceptionthrown = true;
        }
        assertTrue(exceptionthrown,
            "Calling the creation of TacletApps before Input should " + "throw exception");

        instModel.setValueAt("x", 1, 1);

        try {
            app = instModel.createTacletAppFromVarInsts();
        } catch (Exception e) {
            fail("The exception " + e + "has not been expected.");
        }

        assertNotNull(app);
    }

    @Test
    public void testVarNamespaceCreationWithPrefix() {
        TacletApp app = TacletForTests.getTaclet("TestCollisionResolving_ns2");
        TacletApp app1 = app.prepareUserInstantiation(services);
        assertSame(app, app1);

        TacletFindModel instModel = new TacletFindModel(app, services,
            TacletForTests.getNamespaces(), TacletForTests.getAbbrevs(), goal);
        boolean exceptionthrown = false;
        try {
            app = instModel.createTacletAppFromVarInsts();
        } catch (IllegalStateException | SVInstantiationException e) {
            exceptionthrown = true;
        }
        assertTrue(exceptionthrown,
            "Calling the creation of TacletApps before Input should " + "throw exception");
        SchemaVariable u = TacletForTests.getSchemaVariables().lookup(new Name("u"));
        if (instModel.getValueAt(0, 0) == u) {
            instModel.setValueAt("x", 0, 1);
            instModel.setValueAt("f(x)", 1, 1);
        } else {
            instModel.setValueAt("f(x)", 0, 1);
            instModel.setValueAt("x", 1, 1);
        }
        try {
            app = instModel.createTacletAppFromVarInsts();
        } catch (Exception e) {
            fail("The exception " + e + "has not been expected.");
        }
        assertNotNull(app);

    }

    @Test
    public void testNameConflict1() {
        Services services = new Services(AbstractProfile.getDefaultProfile());
        SchemaVariable u = TacletForTests.getSchemaVariables().lookup(new Name("u"));
        SchemaVariable v = TacletForTests.getSchemaVariables().lookup(new Name("v"));
        FindTaclet taclet =
            (FindTaclet) TacletForTests.getTaclet("TestCollisionResolving_name_conflict").taclet();
        Semisequent semiseq = Semisequent.EMPTY_SEMISEQUENT
                .insert(0, new SequentFormula(TacletForTests.parseTerm("\\forall s x; p(x)")))
                .semisequent()
                .insert(1, new SequentFormula(TacletForTests.parseTerm("\\exists s x; p(x)")))
                .semisequent();
        Sequent seq = Sequent.createSuccSequent(semiseq);
        PosInOccurrence pos = new PosInOccurrence(semiseq.get(0), PosInTerm.getTopLevel(), false);

        NoPosTacletApp app0 = NoPosTacletApp.createNoPosTacletApp(taclet);
        app0 = app0.matchFind(pos, services);
        app0 = (NoPosTacletApp) app0.findIfFormulaInstantiations(seq, services).head();
        TacletApp app = app0.setPosInOccurrence(pos, services);
        /*
         * IList<SVInstantiations> sviList=taclet.matchIf (seq,
         * taclet.match(semiseq.get(0).formula(), taclet.find(),
         * MatchConditions.EMPTY_MATCHCONDITIONS, null, Constraint.BOTTOM), null); TacletApp app =
         * PosTacletApp.createPosTacletApp(taclet, sviList.head(), pos);
         */
        TacletApp app1 = app.prepareUserInstantiation(services);
        assertNotSame(app, app1,
            "A different TacletApp should have been created to resolve" + " name conflicts");

        assertNotEquals(((Term) app1.instantiations().getInstantiation(u)).op().name(),
            ((Term) app1.instantiations().getInstantiation(v)).op().name(),
            "The names of the instantiations of u and v should be different");
    }

    @Test
    public void testNameConflictAfterInput() throws SVInstantiationException {

        TacletApp app = TacletForTests.getTaclet("TestCollisionResolving_name_conflict2");
        TacletApp app1 = app.prepareUserInstantiation(services);
        assertSame(app, app1);

        TacletFindModel instModel = new TacletFindModel(app, services,
            TacletForTests.getNamespaces(), TacletForTests.getAbbrevs(), goal);
        boolean exceptionthrown = false;
        try {
            app = instModel.createTacletAppFromVarInsts();
        } catch (IllegalStateException | SVInstantiationException e) {
            exceptionthrown = true;
        }
        assertTrue(exceptionthrown,
            "Calling the creation of TacletApps before Input should " + "throw exception");
        SchemaVariable u = TacletForTests.getSchemaVariables().lookup(new Name("u"));
        SchemaVariable v = TacletForTests.getSchemaVariables().lookup(new Name("v"));
        SchemaVariable w0 = TacletForTests.getSchemaVariables().lookup(new Name("w0"));
        for (int i = 0; i < 3; i++) {
            if (instModel.getValueAt(i, 0) == u) {
                instModel.setValueAt("x", i, 1);
            }
            if (instModel.getValueAt(i, 0) == v) {
                instModel.setValueAt("x", i, 1);
            }
            if (instModel.getValueAt(i, 0) == w0) {
                instModel.setValueAt("f(x)", i, 1);
            }
        }
        exceptionthrown = false;
        try {
            app = instModel.createTacletAppFromVarInsts();
        } catch (IllegalStateException | SVInstantiationException e) {
            exceptionthrown = true;
        }
        assertTrue(exceptionthrown, "As names of instantiations of VarSVs u and v in prefix of w0"
            + "are equal, an exception should be thrown.");
        // next attempt
        for (int i = 0; i < 3; i++) {
            if (instModel.getValueAt(i, 0) == u) {
                instModel.setValueAt("y", i, 1);
            }
            if (instModel.getValueAt(i, 0) == v) {
                instModel.setValueAt("x", i, 1);
            }
            if (instModel.getValueAt(i, 0) == w0) {
                instModel.setValueAt("f(x)", i, 1);
            }
        }
        app = instModel.createTacletAppFromVarInsts();

        assertNotNull(app, "Correct instantiation input should be honored!");
    }

    /*
     * COMMENTED OUT! It has to be checked if the instantiation checking is to restrictive. public
     * void testNameConflictWithContext() {
     *
     * SchemaVariable v = TacletForTests.getVariables().lookup(new Name("v")); FindTaclet taclet =
     * (FindTaclet) TacletForTests.getTaclet
     * ("TestCollisionResolving_name_conflict_with_context").taclet(); Semisequent semiseq =
     * Semisequent.EMPTY_SEMISEQUENT .insert(0, new SequentFormula(TacletForTests.parseTerm("ex x:s"
     * +".p(x)"))) .insert(1, new SequentFormula(TacletForTests.parseTerm("all x:s" +".p(x)")));
     * Sequent seq=Sequent.createSuccSequent(semiseq); PosInOccurrence pos=new
     * PosInOccurrence(semiseq.get(1), PosInTerm.TOP_LEVEL.down(0), seq); IList<SVInstantiations>
     * sviList=taclet.matchIf (seq, taclet.match(semiseq.get(1).formula().sub(0), taclet.find(),
     * taclet.createInitialInstantiation())); TacletApp app =
     * PosTacletApp.createPosTacletApp(taclet, sviList.head(), pos); TacletApp
     * app1=app.prepareUserInstantiation();
     * assertTue("A different TacletApp should have been created to resolve" +" name conflicts",
     * app!=app1); assertTrue("The names of x and the instantiations of v should be different",
     * !(new Name("x")).equals (((Term)app1.instantiations().getInstantiation(v)).op().name()));
     *
     * }
     *
     */

    @Test
    public void testNameConflictWithContextAfterInput() throws SVInstantiationException {

        FindTaclet taclet = (FindTaclet) TacletForTests
                .getTaclet("TestCollisionResolving_name_conflict_with_context2").taclet();
        Term term = TacletForTests.parseTerm("\\forall s x; p(x)");
        PosInOccurrence pos =
            new PosInOccurrence(new SequentFormula(term), PosInTerm.getTopLevel().down(0), true);
        MatchConditions mc =
            taclet.getMatcher().matchFind(term.sub(0), MatchConditions.EMPTY_MATCHCONDITIONS, null);
        TacletApp app = PosTacletApp.createPosTacletApp(taclet, mc, pos, services);
        TacletApp app1 = app.prepareUserInstantiation(services);
        assertSame(app, app1, "Actually there are no conflicts yet.");
        TacletFindModel instModel = new TacletFindModel(app, services,
            TacletForTests.getNamespaces(), TacletForTests.getAbbrevs(), goal);
        boolean exceptionthrown = false;
        try {
            app = instModel.createTacletAppFromVarInsts();
        } catch (IllegalStateException | SVInstantiationException e) {
            exceptionthrown = true;
        }
        assertTrue(exceptionthrown,
            "Calling the creation of TacletApps before Input should " + "throw exception");
        SchemaVariable v = TacletForTests.getSchemaVariables().lookup(new Name("v"));
        SchemaVariable w0 = TacletForTests.getSchemaVariables().lookup(new Name("w0"));
        for (int i = 1; i < 3; i++) {
            if (instModel.getValueAt(i, 0) == v) {
                instModel.setValueAt("x", i, 1);
            }
            if (instModel.getValueAt(i, 0) == w0) {
                instModel.setValueAt("f(x)", i, 1);
            }
        }
        exceptionthrown = false;
        try {
            app = instModel.createTacletAppFromVarInsts();
        } catch (IllegalStateException | SVInstantiationException e) {
            exceptionthrown = true;
        }
        assertTrue(exceptionthrown, "As names of x and instantiations of VarSV v in prefix of w0"
            + "are equal, an exception should be thrown.");
        // next attempt
        for (int i = 1; i < 3; i++) {
            if (instModel.getValueAt(i, 0) == v) {
                instModel.setValueAt("y", i, 1);
            }
            if (instModel.getValueAt(i, 0) == w0) {
                instModel.setValueAt("f(x)", i, 1);
            }
        }
        app = instModel.createTacletAppFromVarInsts();
        assertNotNull(app, "Correct instantiation input should be honored!");

    }

}
