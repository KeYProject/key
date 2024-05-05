/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import java.io.File;
import java.util.*;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.label.*;
import de.uka.ilkd.key.logic.label.TermLabelManager.TermLabelConfiguration;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleAbortException;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.label.ChildTermLabelPolicy;
import de.uka.ilkd.key.rule.label.TermLabelPolicy;
import de.uka.ilkd.key.rule.label.TermLabelRefactoring;
import de.uka.ilkd.key.rule.label.TermLabelRefactoring.RefactoringScope;
import de.uka.ilkd.key.rule.label.TermLabelUpdate;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.key_project.logic.Name;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.jspecify.annotations.NonNull;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests {@link TermLabelManager}
 *
 * @author Martin Hentschel
 */
public class TestTermLabelManager {
    @Test
    public void testrefactorGoal_childrenAndGrandchildren_allRules() throws ProblemLoaderException {
        doRefactoringTestLogging(true, true,
            RefactoringScope.APPLICATION_CHILDREN_AND_GRANDCHILDREN_SUBTREE);
    }

    @Test
    public void testrefactorGoal_childrenAndGrandchildren_ruleSpecific()
            throws ProblemLoaderException {
        doRefactoringTestLogging(true, false,
            RefactoringScope.APPLICATION_CHILDREN_AND_GRANDCHILDREN_SUBTREE, "rule");
    }


    @Test
    public void testrefactorGoal_directChildren_allRules() throws ProblemLoaderException {
        doRefactoringTestLogging(true, true, RefactoringScope.APPLICATION_DIRECT_CHILDREN);
    }

    /**
    *
    */
    @Test
    public void testrefactorGoal_directChildren_ruleSpecific() throws ProblemLoaderException {
        doRefactoringTestLogging(true, false, RefactoringScope.APPLICATION_DIRECT_CHILDREN, "rule");
    }

    /**
    *
    */
    @Test
    public void testrefactorGoal_none_allRules() throws ProblemLoaderException {
        doRefactoringTestLogging(false, false, RefactoringScope.NONE);
    }

    /**
    *
    */
    @Test
    public void testrefactorGoal_none_ruleSpecific() throws ProblemLoaderException {
        doRefactoringTestLogging(false, false, RefactoringScope.NONE, "rule");
    }

    /**
    *
    */
    @Test
    public void testrefactorGoal_sequent_allRules() throws ProblemLoaderException {
        doRefactoringTestLogging(true, true, RefactoringScope.SEQUENT);
    }

    /**
    *
    */
    @Test
    public void testrefactorGoal_sequent_ruleSpecific() throws ProblemLoaderException {
        doRefactoringTestLogging(true, false, RefactoringScope.SEQUENT, "rule");
    }

    protected void doRefactoringTestLogging(boolean ruleChanged, boolean notSupportedRuleChanged,
            RefactoringScope scope, String... supportedRules) throws ProblemLoaderException {
        LoggingTermLabelRefactoring refactoring =
            new LoggingTermLabelRefactoring(scope, supportedRules);
        InitConfig initConfig = createTestServices(null, null, null, null, null, refactoring);
        Services services = initConfig.getServices();
        TermBuilder TB = services.getTermBuilder();
        // Create sequent
        PosInOccurrence pos = createTestPosInOccurrence(services);
        IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        Term one = integerLDT.translateLiteral(new IntLiteral(1), services);
        Term two = integerLDT.translateLiteral(new IntLiteral(2), services);
        one = TB.label(one, new ParameterlessTermLabel(new Name("APPLICATION")));
        two = TB.label(two, new ParameterlessTermLabel(new Name("APPLICATION")));
        Sequent sequent = Sequent.EMPTY_SEQUENT;
        sequent = sequent.addFormula(new SequentFormula(TB.inInt(one)), true, true).sequent();
        sequent = sequent.addFormula(pos.sequentFormula(), true, false).sequent();
        sequent = sequent.addFormula(new SequentFormula(TB.inInt(two)), false, true).sequent();
        // Test supported rule
        Rule rule = new DummyRule("rule");
        Term taclet = TB.tt();
        Goal goal = createGoal(initConfig, sequent);
        TermLabelManager.refactorGoal(new TermLabelState(), services, pos, rule, goal, null,
            taclet);
        compareSequents(sequent, goal.sequent(), ruleChanged, scope);
        // Test other not supported rule
        rule = new DummyRule("notSupportedRule");
        goal = createGoal(initConfig, sequent);
        TermLabelManager.refactorGoal(new TermLabelState(), services, pos, rule, goal, null,
            taclet);
        compareSequents(sequent, goal.sequent(), notSupportedRuleChanged, scope);
    }

    protected Goal createGoal(InitConfig initConfig, Sequent sequent) {
        Proof proof = new Proof("TestTermLabelManager", initConfig.deepCopy());
        Node node = new Node(proof, sequent);
        return new Goal(node,
            TacletIndexKit.getKit().createTacletIndex(),
            new BuiltInRuleAppIndex(new BuiltInRuleIndex()), initConfig.getServices());
    }

    protected void compareSequents(Sequent expected, Sequent current, boolean changed,
            RefactoringScope scope) {
        Iterator<SequentFormula> expectedIter = expected.iterator();
        Iterator<SequentFormula> currentIter = current.iterator();
        while (expectedIter.hasNext() && currentIter.hasNext()) {
            SequentFormula expectedSF = expectedIter.next();
            SequentFormula currentSF = currentIter.next();
            compareTerms(expectedSF.formula(), currentSF.formula(), changed, scope);
        }
        assertFalse(expectedIter.hasNext());
        assertFalse(currentIter.hasNext());
    }

    protected void compareTerms(Term expected, Term current, boolean changed,
            RefactoringScope scope) {
        assertEquals(expected.arity(), current.arity());
        for (int i = 0; i < expected.arity(); i++) {
            compareTerms(expected.sub(i), current.sub(i), changed, scope);
        }
        assertSame(expected.op(), current.op());
        assertSame(expected.boundVars(), current.boundVars());
        assertSame(expected.javaBlock(), current.javaBlock());
        assertEquals(expected.getLabels().size(), current.getLabels().size());
        if (changed) {
            for (int i = 0; i < expected.getLabels().size(); i++) {
                if (RefactoringScope.SEQUENT.equals(scope)) {
                    assertEquals(expected.getLabels().get(i).name().toString() + "-CHANGED",
                        current.getLabels().get(i).name().toString());
                } else if (RefactoringScope.APPLICATION_CHILDREN_AND_GRANDCHILDREN_SUBTREE
                        .equals(scope)) {
                    String expectedName = expected.getLabels().get(i).name().toString();
                    if ("ONE".equals(expectedName) || "ADD".equals(expectedName)
                            || "TWO".equals(expectedName) || "THREE".equals(expectedName)) {
                        assertEquals(expectedName + "-CHANGED",
                            current.getLabels().get(i).name().toString());
                    } else {
                        assertEquals(expectedName, current.getLabels().get(i).name().toString());
                    }
                } else if (RefactoringScope.APPLICATION_DIRECT_CHILDREN.equals(scope)) {
                    String expectedName = expected.getLabels().get(i).name().toString();
                    if ("ONE".equals(expectedName) || "ADD".equals(expectedName)) {
                        assertEquals(expectedName + "-CHANGED",
                            current.getLabels().get(i).name().toString());
                    } else {
                        assertEquals(expectedName, current.getLabels().get(i).name().toString());
                    }
                } else {
                    fail("Unsupported scope \"" + scope + "\".");
                }
            }
        } else {
            assertSame(expected.getLabels(), current.getLabels());
        }
    }

    /**
    *
    */
    @Test
    public void testInstantiateLabels_updates_allRules() {
        LoggingTermLabelUpdate update =
            new LoggingTermLabelUpdate(new ParameterlessTermLabel(new Name("UPDATED")));
        Services services = null;
        try {
            services = createTestServices(null, null, null, null, update, null).getServices();
        } catch (ProblemLoaderException e) {
            fail();
        }
        PosInOccurrence pos = createTestPosInOccurrence(services);
        Rule rule = new DummyRule("rule");
        Term taclet = services.getTermBuilder().tt();
        // Create labels
        ImmutableArray<TermLabel> labels = TermLabelManager.instantiateLabels(new TermLabelState(),
            services, pos, rule, null, null, null, taclet, null);
        assertNotNull(labels);
        assertEquals(1, labels.size());
        assertEquals("UPDATED", labels.get(0).name().toString());
        // Test other not supported rule
        Rule otherRule = new DummyRule("notSupportedRule");
        labels = TermLabelManager.instantiateLabels(new TermLabelState(), services, pos, otherRule,
            null, null, null, taclet, null);
        assertNotNull(labels);
        assertEquals(1, labels.size());
        assertEquals("UPDATED", labels.get(0).name().toString());
    }

    /**
    *
    */
    @Test
    public void testInstantiateLabels_updates_ruleSpecific() {
        LoggingTermLabelUpdate update =
            new LoggingTermLabelUpdate(new ParameterlessTermLabel(new Name("UPDATED")), "rule");
        Services services = null;
        try {
            services = createTestServices(null, null, null, null, update, null).getServices();
        } catch (ProblemLoaderException e) {
            fail();
        }
        PosInOccurrence pos = createTestPosInOccurrence(services);
        Rule rule = new DummyRule("rule");
        Term taclet = services.getTermBuilder().tt();
        // Create labels
        ImmutableArray<TermLabel> labels = TermLabelManager.instantiateLabels(new TermLabelState(),
            services, pos, rule, null, null, null, taclet, null);
        assertNotNull(labels);
        assertEquals(1, labels.size());
        assertEquals("UPDATED", labels.get(0).name().toString());
        // Test other not supported rule
        Rule otherRule = new DummyRule("notSupportedRule");
        labels = TermLabelManager.instantiateLabels(new TermLabelState(), services, pos, otherRule,
            null, null, null, taclet, null);
        assertNotNull(labels);
        assertEquals(0, labels.size());
    }

    /**
    *
    */
    @Test
    public void testInstantiateLabels_childAndGrandchildPolicies_allRules() {
        LoggingChildTermLabelPolicy policy = new LoggingChildTermLabelPolicy();
        Services services = null;
        try {
            services = createTestServices(null, null, null, policy, null, null).getServices();
        } catch (ProblemLoaderException e) {
            fail();
        }
        PosInOccurrence pos = createTestPosInOccurrence(services);
        Rule rule = new DummyRule("rule");
        Term taclet = services.getTermBuilder().tt();
        // Create labels
        ImmutableArray<TermLabel> labels = TermLabelManager.instantiateLabels(new TermLabelState(),
            services, pos, rule, null, null, null, taclet, null);
        assertNotNull(labels);
        assertEquals(4, labels.size());
        assertEquals("ONE", labels.get(0).name().toString());
        assertEquals("ADD", labels.get(1).name().toString());
        assertEquals("TWO", labels.get(2).name().toString());
        assertEquals("THREE", labels.get(3).name().toString());
        // Test log
        assertEquals(4, policy.getLog().size());
        assertEquals("ONE", policy.getLog().get(0).name().toString());
        assertEquals("ADD", policy.getLog().get(1).name().toString());
        assertEquals("TWO", policy.getLog().get(2).name().toString());
        assertEquals("THREE", policy.getLog().get(3).name().toString());
        // Test other not supported rule
        Rule otherRule = new DummyRule("notSupportedRule");
        labels = TermLabelManager.instantiateLabels(new TermLabelState(), services, pos, otherRule,
            null, null, null, taclet, null);
        assertNotNull(labels);
        assertEquals(4, labels.size());
        assertEquals("ONE", labels.get(0).name().toString());
        assertEquals("ADD", labels.get(1).name().toString());
        assertEquals("TWO", labels.get(2).name().toString());
        assertEquals("THREE", labels.get(3).name().toString());
        // Test log
        assertEquals(8, policy.getLog().size());
        assertEquals("ONE", policy.getLog().get(0).name().toString());
        assertEquals("ADD", policy.getLog().get(1).name().toString());
        assertEquals("TWO", policy.getLog().get(2).name().toString());
        assertEquals("THREE", policy.getLog().get(3).name().toString());
        assertEquals("ONE", policy.getLog().get(4).name().toString());
        assertEquals("ADD", policy.getLog().get(5).name().toString());
        assertEquals("TWO", policy.getLog().get(6).name().toString());
        assertEquals("THREE", policy.getLog().get(7).name().toString());
    }

    /**
    *
    */
    @Test
    public void testInstantiateLabels_childAndGrandchildPolicies_ruleSpecific() {
        LoggingChildTermLabelPolicy policy = new LoggingChildTermLabelPolicy("rule");
        Services services = null;
        try {
            services = createTestServices(null, null, null, policy, null, null).getServices();
        } catch (ProblemLoaderException e) {
            fail();
        }
        PosInOccurrence pos = createTestPosInOccurrence(services);
        Rule rule = new DummyRule("rule");
        Term taclet = services.getTermBuilder().tt();
        // Create labels
        ImmutableArray<TermLabel> labels = TermLabelManager.instantiateLabels(new TermLabelState(),
            services, pos, rule, null, null, null, taclet, null);
        assertNotNull(labels);
        assertEquals(4, labels.size());
        assertEquals("ONE", labels.get(0).name().toString());
        assertEquals("ADD", labels.get(1).name().toString());
        assertEquals("TWO", labels.get(2).name().toString());
        assertEquals("THREE", labels.get(3).name().toString());
        // Test log
        assertEquals(4, policy.getLog().size());
        assertEquals("ONE", policy.getLog().get(0).name().toString());
        assertEquals("ADD", policy.getLog().get(1).name().toString());
        assertEquals("TWO", policy.getLog().get(2).name().toString());
        assertEquals("THREE", policy.getLog().get(3).name().toString());
        // Test other not supported rule
        Rule otherRule = new DummyRule("notSupportedRule");
        labels = TermLabelManager.instantiateLabels(new TermLabelState(), services, pos, otherRule,
            null, null, null, taclet, null);
        assertNotNull(labels);
        assertEquals(0, labels.size());
        // Test log
        assertEquals(4, policy.getLog().size());
    }

    /**
     *
     * @throws ProblemLoaderException Occurred Exception
     */
    @Test
    public void testInstantiateLabels_directChildPolicies_allRules() throws ProblemLoaderException {
        LoggingChildTermLabelPolicy policy = new LoggingChildTermLabelPolicy();
        Services services = createTestServices(null, null, policy, null, null, null).getServices();
        PosInOccurrence pos = createTestPosInOccurrence(services);
        Rule rule = new DummyRule("rule");
        Term taclet = services.getTermBuilder().tt();
        // Create labels
        ImmutableArray<TermLabel> labels = TermLabelManager.instantiateLabels(new TermLabelState(),
            services, pos, rule, null, null, null, taclet, null);
        assertNotNull(labels);
        assertEquals(2, labels.size());
        assertEquals("ONE", labels.get(0).name().toString());
        assertEquals("ADD", labels.get(1).name().toString());
        // Test log
        assertEquals(2, policy.getLog().size());
        assertEquals("ONE", policy.getLog().get(0).name().toString());
        assertEquals("ADD", policy.getLog().get(1).name().toString());
        // Test other not supported rule
        Rule otherRule = new DummyRule("notSupportedRule");
        labels = TermLabelManager.instantiateLabels(new TermLabelState(), services, pos, otherRule,
            null, null, null, taclet, null);
        assertNotNull(labels);
        assertEquals(2, labels.size());
        assertEquals("ONE", labels.get(0).name().toString());
        assertEquals("ADD", labels.get(1).name().toString());
        // Test log
        assertEquals(4, policy.getLog().size());
        assertEquals("ONE", policy.getLog().get(0).name().toString());
        assertEquals("ADD", policy.getLog().get(1).name().toString());
        assertEquals("ONE", policy.getLog().get(2).name().toString());
        assertEquals("ADD", policy.getLog().get(3).name().toString());
    }

    /**
    *
    */
    @Test
    public void testInstantiateLabels_directChildPolicies_ruleSpecific() {
        LoggingChildTermLabelPolicy policy = new LoggingChildTermLabelPolicy("rule");
        Services services = null;
        try {
            services = createTestServices(null, null, policy, null, null, null).getServices();
        } catch (ProblemLoaderException e) {
            fail();
        }
        PosInOccurrence pos = createTestPosInOccurrence(services);
        Rule rule = new DummyRule("rule");
        Term taclet = services.getTermBuilder().tt();
        // Create labels
        ImmutableArray<TermLabel> labels = TermLabelManager.instantiateLabels(new TermLabelState(),
            services, pos, rule, null, null, null, taclet, null);
        assertNotNull(labels);
        assertEquals(2, labels.size());
        assertEquals("ONE", labels.get(0).name().toString());
        assertEquals("ADD", labels.get(1).name().toString());
        // Test log
        assertEquals(2, policy.getLog().size());
        assertEquals("ONE", policy.getLog().get(0).name().toString());
        assertEquals("ADD", policy.getLog().get(1).name().toString());
        // Test other not supported rule
        Rule otherRule = new DummyRule("notSupportedRule");
        labels = TermLabelManager.instantiateLabels(new TermLabelState(), services, pos, otherRule,
            null, null, null, taclet, null);
        assertNotNull(labels);
        assertEquals(0, labels.size());
        // Test log
        assertEquals(2, policy.getLog().size());
    }

    /**
    *
    */
    @Test
    public void testInstantiateLabels_modalityTermPolicies() {
        LoggingTermLabelPolicy policy = new LoggingTermLabelPolicy();
        Services services = null;
        try {
            services = createTestServices(null, policy, null, null, null, null).getServices();
        } catch (ProblemLoaderException e) {
            fail();
        }
        TermBuilder TB = services.getTermBuilder();
        Term modality = TB.label(
            TB.box(JavaBlock.EMPTY_JAVABLOCK,
                TB.label(TB.tt(), new ParameterlessTermLabel(new Name("POST")))),
            new ParameterlessTermLabel(new Name("ONE")));
        LocationVariable heap = services.getTypeConverter().getHeapLDT().getSavedHeap();
        Term update = TB.label(TB.elementary(TB.var(heap), TB.var(heap)),
            new ParameterlessTermLabel(new Name("UPDATE")));
        Term updateApp = TB.apply(update, modality,
            new ImmutableArray<>(new ParameterlessTermLabel(new Name("UPDATE-APPLICATION"))));
        PosInOccurrence pos =
            new PosInOccurrence(new SequentFormula(updateApp), PosInTerm.getTopLevel(), true);
        Term taclet = TB.tt();
        Rule rule = new DummyRule("rule");
        // Create labels
        ImmutableArray<TermLabel> labels = TermLabelManager.instantiateLabels(new TermLabelState(),
            services, pos, rule, null, null, null, taclet, null);
        assertNotNull(labels);
        assertEquals(1, labels.size());
        assertEquals("ONE", labels.get(0).name().toString());
        // Test log
        assertEquals(1, policy.getLog().size());
        assertEquals("ONE", policy.getLog().get(0).name().toString());
    }

    /**
    *
    */
    @Test
    public void testInstantiateLabels_applicationTermPolicies() {
        LoggingTermLabelPolicy policy = new LoggingTermLabelPolicy();
        Services services = null;
        try {
            services = createTestServices(policy, null, null, null, null, null).getServices();
        } catch (ProblemLoaderException e) {
            fail();
        }
        PosInOccurrence pos = createTestPosInOccurrence(services);
        Term taclet = services.getTermBuilder().tt();
        Rule rule = new DummyRule("rule");
        // Create labels
        ImmutableArray<TermLabel> labels = TermLabelManager.instantiateLabels(new TermLabelState(),
            services, pos, rule, null, null, null, taclet, null);
        assertNotNull(labels);
        assertEquals(1, labels.size());
        assertEquals("APPLICATION", labels.get(0).name().toString());
        // Test log
        assertEquals(1, policy.getLog().size());
        assertEquals("APPLICATION", policy.getLog().get(0).name().toString());
    }

    /**
    *
    */
    @Test
    public void testInstantiateLabels_taclet() {
        Services services = null;
        try {
            services = createTestServices(null, null, null, null, null, null).getServices();
        } catch (ProblemLoaderException e) {
            fail();
        }
        PosInOccurrence pos = createTestPosInOccurrence(services);
        Rule rule = new DummyRule("rule");
        Term taclet = services.getTermBuilder().label(services.getTermBuilder().tt(),
            new ImmutableArray<>(new ParameterlessTermLabel(new Name("TACLET"))));
        ImmutableArray<TermLabel> labels = TermLabelManager.instantiateLabels(new TermLabelState(),
            services, pos, rule, null, null, null, taclet, null);
        assertNotNull(labels);
        assertEquals(1, labels.size());
        assertEquals("TACLET", labels.get(0).name().toString());
    }

    /**
    *
    */
    @Test
    public void testInstantiateLabels_null() {
        ImmutableArray<TermLabel> labels = TermLabelManager.instantiateLabels(new TermLabelState(),
            null, null, null, null, null, null, null, null);
        assertNotNull(labels);
        assertTrue(labels.isEmpty());
    }

    protected PosInOccurrence createTestPosInOccurrence(Services services) {
        Term testTerm = createTestTerm(services);
        Term inInt = services.getTermBuilder().inInt(testTerm);
        return new PosInOccurrence(new SequentFormula(inInt), PosInTerm.parseReverseString("0"),
            true);
    }

    protected Term createTestTerm(Services services) {
        IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        Term one = integerLDT.translateLiteral(new IntLiteral(1), services);
        Term two = integerLDT.translateLiteral(new IntLiteral(2), services);
        Term three = integerLDT.translateLiteral(new IntLiteral(3), services);
        TermBuilder TB = services.getTermBuilder();
        one = TB.label(one, new ParameterlessTermLabel(new Name("ONE")));
        two = TB.label(one, new ParameterlessTermLabel(new Name("TWO")));
        three = TB.label(one, new ParameterlessTermLabel(new Name("THREE")));
        Term innerAdd = TB.label(TB.add(two, three), new ParameterlessTermLabel(new Name("ADD")));
        return TB.label(TB.add(one, innerAdd), new ParameterlessTermLabel(new Name("APPLICATION")));
    }


    @Test
    public void testParseLabel() throws TermLabelException {
        Services services = null;
        try {
            services = createTestServices(null, null, null, null, null, null).getServices();
        } catch (ProblemLoaderException e1) {
            fail();
        }
        TermLabelManager manager = TermLabelManager.getTermLabelManager(services);
        // Test null parameter
        TermLabel label = manager.parseLabel("ONE", null, services);
        assertTrue(label instanceof LoggingTermLabel);
        assertEquals("ONE", label.name().toString());
        assertEquals(0, label.getChildCount());
        // Test empty parameter
        label = manager.parseLabel("TWO", null, services);
        assertTrue(label instanceof LoggingTermLabel);
        assertEquals("TWO", label.name().toString());
        assertEquals(0, label.getChildCount());
        // Test with parameter
        label = manager.parseLabel("THREE", Collections.singletonList("Param"), services);
        assertTrue(label instanceof LoggingTermLabel);
        assertEquals("THREE", label.name().toString());
        assertEquals(1, label.getChildCount());
        assertEquals("Param", label.getChild(0));
        // Test unsupported
        try {
            manager.parseLabel("UNKNOWN", null, services);
        } catch (TermLabelException e) {
            assertEquals("No TermLabelFactory available for term label name \"UNKNOWN\".",
                e.getMessage());
        }
    }

    /**
     * Tests {@link TermLabelManager#getSupportedTermLabelNames(Services)}.
     */
    @Test
    public void testGetSupportedTermLabelNames() {
        // Test null
        ImmutableList<Name> names = TermLabelManager.getSupportedTermLabelNames(null);
        assertNotNull(names);
        assertTrue(names.isEmpty());
        // Test services
        Services services = null;
        try {
            services = createTestServices(null, null, null, null, null, null).getServices();
        } catch (ProblemLoaderException e) {
            fail();
        }
        names = TermLabelManager.getSupportedTermLabelNames(services);
        assertNotNull(names);
        assertEquals(5, names.size());
        assertTrue(names.contains(new Name("ONE")));
        assertTrue(names.contains(new Name("TWO")));
        assertTrue(names.contains(new Name("THREE")));
        assertTrue(names.contains(new Name("ADD")));
        assertTrue(names.contains(new Name("APPLICATION")));
    }

    /**
     * Tests {@link TermLabelManager#getTermLabelManager(de.uka.ilkd.key.java.Services)}.
     */
    @Test
    public void testGetTermLabelManager() {
        Assertions.assertNull(TermLabelManager.getTermLabelManager(null));
        Services services = new Services(JavaProfile.getDefaultProfile());
        TermLabelManager manager = TermLabelManager.getTermLabelManager(services);
        assertSame(services.getProfile().getTermLabelManager(), manager);
        TermLabelManager managerAgain = TermLabelManager.getTermLabelManager(services);
        assertSame(services.getProfile().getTermLabelManager(), managerAgain);
        assertSame(manager, managerAgain);
    }

    protected InitConfig createTestServices(final TermLabelPolicy applicationTermPolicy,
            final TermLabelPolicy modalityTermPolicy, final ChildTermLabelPolicy directChildPolicy,
            final ChildTermLabelPolicy childAndGrandchildPolicy, final TermLabelUpdate update,
            final TermLabelRefactoring refactoring) throws ProblemLoaderException {
        KeYEnvironment<?> env = null;
        try {
            env = KeYEnvironment.load(new File(HelperClassForTests.TESTCASE_DIRECTORY,
                "termLabels/flatSteps/FlatSteps.java"), null, null, null);
            Profile profile = new JavaProfile() {
                @Override
                protected ImmutableList<TermLabelConfiguration> computeTermLabelConfiguration() {
                    ImmutableList<TermLabelPolicy> applicationTermPolicies = ImmutableSLList.nil();
                    if (applicationTermPolicy != null) {
                        applicationTermPolicies =
                            applicationTermPolicies.prepend(applicationTermPolicy);
                    }
                    ImmutableList<TermLabelPolicy> modalityTermPolicies = ImmutableSLList.nil();
                    if (modalityTermPolicy != null) {
                        modalityTermPolicies = modalityTermPolicies.prepend(modalityTermPolicy);
                    }
                    ImmutableList<ChildTermLabelPolicy> directChildTermLabelPolicies =
                        ImmutableSLList.nil();
                    if (directChildPolicy != null) {
                        directChildTermLabelPolicies =
                            directChildTermLabelPolicies.prepend(directChildPolicy);
                    }
                    ImmutableList<ChildTermLabelPolicy> childAndGrandchildTermLabelPolicies =
                        ImmutableSLList.nil();
                    if (childAndGrandchildPolicy != null) {
                        childAndGrandchildTermLabelPolicies =
                            childAndGrandchildTermLabelPolicies.prepend(childAndGrandchildPolicy);
                    }
                    ImmutableList<TermLabelUpdate> termLabelUpdates = ImmutableSLList.nil();
                    if (update != null) {
                        termLabelUpdates = termLabelUpdates.prepend(update);
                    }
                    ImmutableList<TermLabelRefactoring> termLabelRefactorings =
                        ImmutableSLList.nil();
                    if (refactoring != null) {
                        termLabelRefactorings = termLabelRefactorings.prepend(refactoring);
                    }

                    ImmutableList<TermLabelConfiguration> result = ImmutableSLList.nil();
                    result = result.prepend(new TermLabelConfiguration(new Name("ONE"),
                        new LoggingFactory(new Name("ONE")), applicationTermPolicies,
                        modalityTermPolicies, directChildTermLabelPolicies,
                        childAndGrandchildTermLabelPolicies, termLabelUpdates,
                        termLabelRefactorings, null));
                    result = result.prepend(new TermLabelConfiguration(new Name("TWO"),
                        new LoggingFactory(new Name("TWO")), applicationTermPolicies,
                        modalityTermPolicies, directChildTermLabelPolicies,
                        childAndGrandchildTermLabelPolicies, termLabelUpdates,
                        termLabelRefactorings, null));
                    result = result.prepend(new TermLabelConfiguration(new Name("THREE"),
                        new LoggingFactory(new Name("THREE")), applicationTermPolicies,
                        modalityTermPolicies, directChildTermLabelPolicies,
                        childAndGrandchildTermLabelPolicies, termLabelUpdates,
                        termLabelRefactorings, null));
                    result = result.prepend(new TermLabelConfiguration(new Name("ADD"),
                        new LoggingFactory(new Name("ADD")), applicationTermPolicies,
                        modalityTermPolicies, directChildTermLabelPolicies,
                        childAndGrandchildTermLabelPolicies, termLabelUpdates,
                        termLabelRefactorings, null));
                    result = result.prepend(new TermLabelConfiguration(new Name("APPLICATION"),
                        new LoggingFactory(new Name("APPLICATION")), applicationTermPolicies,
                        modalityTermPolicies, directChildTermLabelPolicies,
                        childAndGrandchildTermLabelPolicies, termLabelUpdates,
                        termLabelRefactorings, null));
                    return result;
                }
            };
            return env.getInitConfig()
                    .copyWithServices(env.getInitConfig().getServices().copy(profile, false));
        } finally {
            if (env != null) {
                env.dispose();
            }
        }
    }

    private static class LoggingTermLabelRefactoring implements TermLabelRefactoring {
        private final RefactoringScope scope;

        private ImmutableList<Name> supportedRuleNames = ImmutableSLList.nil();

        public LoggingTermLabelRefactoring(RefactoringScope scope, String... supportedRules) {
            this.scope = scope;
            for (String rule : supportedRules) {
                supportedRuleNames = supportedRuleNames.prepend(new Name(rule));
            }
        }

        @Override
        public ImmutableList<Name> getSupportedRuleNames() {
            return supportedRuleNames;
        }

        @Override
        public RefactoringScope defineRefactoringScope(TermLabelState state, Services services,
                PosInOccurrence applicationPosInOccurrence, Term applicationTerm, Rule rule,
                Goal goal, Object hint, Term tacletTerm) {
            return scope;
        }

        @Override
        public void refactorLabels(TermLabelState state, Services services,
                PosInOccurrence applicationPosInOccurrence, Term applicationTerm, Rule rule,
                Goal goal, Object hint, Term tacletTerm, Term term, LabelCollection labels) {
            List<TermLabel> changedLabels = new LinkedList<>();
            boolean changed = labels.isModified();
            for (TermLabel label : labels.getLabels()) {
                if (label.name().toString().endsWith("-CHANGED")) {
                    changedLabels.add(label);
                } else {
                    changed |= changedLabels.add(
                        new ParameterlessTermLabel(new Name(label.name().toString() + "-CHANGED")));
                }
            }
            labels.replaceWith(changedLabels, changed);
        }

    }

    private static class LoggingTermLabelUpdate implements TermLabelUpdate {
        private final TermLabel toAdd;

        private ImmutableList<Name> supportedRuleNames = ImmutableSLList.nil();

        public LoggingTermLabelUpdate(TermLabel toAdd, String... supportedRules) {
            this.toAdd = toAdd;
            for (String rule : supportedRules) {
                supportedRuleNames = supportedRuleNames.prepend(new Name(rule));
            }
        }

        @Override
        public ImmutableList<Name> getSupportedRuleNames() {
            return supportedRuleNames;
        }

        @Override
        public void updateLabels(TermLabelState state, Services services,
                PosInOccurrence applicationPosInOccurrence, Term applicationTerm, Term modalityTerm,
                Rule rule, RuleApp ruleApp, Object hint, Term tacletTerm, Term newTerm,
                Set<TermLabel> labels) {
            labels.add(toAdd);
        }
    }

    private static class LoggingChildTermLabelPolicy implements ChildTermLabelPolicy {
        private ImmutableList<Name> supportedRuleNames = ImmutableSLList.nil();

        private final List<TermLabel> log = new LinkedList<>();

        public LoggingChildTermLabelPolicy(String... supportedRules) {
            for (String rule : supportedRules) {
                supportedRuleNames = supportedRuleNames.prepend(new Name(rule));
            }
        }

        @Override
        public ImmutableList<Name> getSupportedRuleNames() {
            return supportedRuleNames;
        }

        @Override
        public boolean isRuleApplicationSupported(TermServices services,
                PosInOccurrence applicationPosInOccurrence, Term applicationTerm, Rule rule,
                Goal goal, Object hint, Term tacletTerm, Term newTerm) {
            return true;
        }

        @Override
        public boolean addLabel(TermServices services, PosInOccurrence applicationPosInOccurrence,
                Term applicationTerm, Rule rule, Goal goal, Object hint, Term tacletTerm,
                Term newTerm, Term childTerm, TermLabel label) {
            log.add(label);
            return true;
        }

        public List<TermLabel> getLog() {
            return log;
        }
    }

    private static class LoggingTermLabelPolicy implements TermLabelPolicy {
        private final List<TermLabel> log = new LinkedList<>();

        @Override
        public TermLabel keepLabel(TermLabelState state, Services services,
                PosInOccurrence applicationPosInOccurrence, Term applicationTerm, Rule rule,
                Goal goal, Object hint, Term tacletTerm,
                Term newTerm, TermLabel label) {
            log.add(label);
            return label;
        }

        public List<TermLabel> getLog() {
            return log;
        }
    }

    private static class LoggingFactory implements TermLabelFactory<TermLabel> {
        private final Name label;

        public LoggingFactory(Name label) {
            this.label = label;
        }

        @Override
        public TermLabel parseInstance(List<String> arguments, TermServices services) {
            return new LoggingTermLabel(label, arguments);
        }
    }

    private static class LoggingTermLabel implements TermLabel {
        private final Name name;

        private final List<String> arguments;

        public LoggingTermLabel(Name name, List<String> arguments) {
            assert name != null;
            this.name = name;
            this.arguments = arguments;
        }

        @Override
        public Name name() {
            return name;
        }

        @Override
        public Object getChild(int i) {
            return arguments.get(i);
        }

        @Override
        public int getChildCount() {
            return arguments != null ? arguments.size() : 0;
        }
    }

    private static class DummyRule implements Rule {
        private final String name;

        public DummyRule(String name) {
            this.name = name;
        }

        @Override
        public @NonNull ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp)
                throws RuleAbortException {
            throw new RuleAbortException("no implementation");
        }

        @Override
        public Name name() {
            return new Name(name);
        }

        @Override
        public String displayName() {
            return name;
        }
    }
}
