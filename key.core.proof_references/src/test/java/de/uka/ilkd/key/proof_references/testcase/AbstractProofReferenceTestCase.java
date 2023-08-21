/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof_references.testcase;

import java.io.File;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.function.Predicate;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Choice;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof_references.ProofReferenceUtil;
import de.uka.ilkd.key.proof_references.analyst.IProofReferencesAnalyst;
import de.uka.ilkd.key.proof_references.reference.IProofReference;
import de.uka.ilkd.key.settings.ChoiceSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.speclang.ClassAxiom;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.helper.FindResources;
import org.key_project.util.java.CollectionUtil;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Provides the basic functionality to test the proof reference API.
 *
 * @author Martin Hentschel
 */
public abstract class AbstractProofReferenceTestCase {
    public static final File TESTCASE_DIRECTORY = FindResources.getTestCasesDirectory();

    static {
        assertNotNull(TESTCASE_DIRECTORY, "Could not find test case directory");
    }

    /**
     * Executes the test steps of test methods.
     *
     * @param baseDir The base directory which contains test and oracle file.
     * @param javaPathInBaseDir The path to the java file inside the base directory.
     * @param containerTypeName The name of the type which contains the method.
     * @param targetName The target name to search.
     * @param useContracts Use contracts or inline method bodies instead.
     * @param analyst The {@link IProofReferencesAnalyst} to use.
     * @param expectedReferences The expected proof references.
     * @throws Exception Occurred Exception.
     */
    protected void doReferenceFunctionTest(File baseDir, String javaPathInBaseDir,
            String containerTypeName, String targetName, boolean useContracts,
            IProofReferencesAnalyst analyst, ExpectedProofReferences... expectedReferences)
            throws Exception {
        doReferenceFunctionTest(baseDir, javaPathInBaseDir, containerTypeName, targetName,
            useContracts, analyst,
            null, expectedReferences);
    }

    /**
     * Executes the test steps of test methods.
     *
     * @param baseDir The base directory which contains test and oracle file.
     * @param javaPathInBaseDir The path to the java file inside the base directory.
     * @param containerTypeName The name of the type which contains the method.
     * @param targetName The target name to search.
     * @param useContracts Use contracts or inline method bodies instead.
     * @param analyst The {@link IProofReferencesAnalyst} to use.
     * @param currentReferenceFilter An optional {@link Predicate} to limit the references to test.
     * @param expectedReferences The expected proof references.
     * @throws Exception Occurred Exception.
     */
    protected void doReferenceFunctionTest(File baseDir, String javaPathInBaseDir,
            String containerTypeName, String targetName, boolean useContracts,
            IProofReferencesAnalyst analyst, Predicate<IProofReference<?>> currentReferenceFilter,
            ExpectedProofReferences... expectedReferences) throws Exception {
        IProofTester tester =
            createReferenceMethodTester(analyst, currentReferenceFilter, expectedReferences);
        doProofFunctionTest(baseDir, javaPathInBaseDir, containerTypeName, targetName, useContracts,
            tester);
    }

    /**
     * Executes the test steps of test methods.
     *
     * @param baseDir The base directory which contains test and oracle file.
     * @param javaPathInBaseDir The path to the java file inside the base directory.
     * @param containerTypeName The name of the type which contains the method.
     * @param methodFullName The method name to search.
     * @param useContracts Use contracts or inline method bodies instead.
     * @param analyst The {@link IProofReferencesAnalyst} to use.
     * @param expectedReferences The expected proof references.
     * @throws Exception Occurred Exception.
     */
    protected void doReferenceMethodTest(File baseDir, String javaPathInBaseDir,
            String containerTypeName, String methodFullName, boolean useContracts,
            IProofReferencesAnalyst analyst, ExpectedProofReferences... expectedReferences)
            throws Exception {
        doReferenceMethodTest(baseDir, javaPathInBaseDir, containerTypeName, methodFullName,
            useContracts, analyst, null, expectedReferences);
    }

    /**
     * Executes the test steps of test methods.
     *
     * @param baseDir The base directory which contains test and oracle file.
     * @param javaPathInBaseDir The path to the java file inside the base directory.
     * @param containerTypeName The name of the type which contains the method.
     * @param methodFullName The method name to search.
     * @param useContracts Use contracts or inline method bodies instead.
     * @param analyst The {@link IProofReferencesAnalyst} to use.
     * @param currentReferenceFilter An optional {@link Predicate} to limit the references to test.
     * @param expectedReferences The expected proof references.
     * @throws Exception Occurred Exception.
     */
    protected void doReferenceMethodTest(File baseDir, String javaPathInBaseDir,
            String containerTypeName, String methodFullName, boolean useContracts,
            IProofReferencesAnalyst analyst, Predicate<IProofReference<?>> currentReferenceFilter,
            ExpectedProofReferences... expectedReferences) throws Exception {
        IProofTester tester =
            createReferenceMethodTester(analyst, currentReferenceFilter, expectedReferences);
        doProofMethodTest(baseDir, javaPathInBaseDir, containerTypeName, methodFullName,
            useContracts, tester);
    }

    /**
     * Creates the {@link IProofTester} used by
     * {@link #doProofFunctionTest(File, String, String, String, boolean, IProofTester)} and
     * {@link #doProofMethodTest(File, String, String, String, boolean, IProofTester)}.
     *
     * @param analyst The {@link IProofReferencesAnalyst} to use.
     * @param currentReferenceFilter An optional {@link Predicate} to limit the references to test.
     * @param expectedReferences The expected proof references.
     * @return The created {@link IProofTester}.
     */
    protected IProofTester createReferenceMethodTester(final IProofReferencesAnalyst analyst,
            final Predicate<IProofReference<?>> currentReferenceFilter,
            final ExpectedProofReferences... expectedReferences) {
        return (environment, proof) -> {
            // Compute proof references
            ImmutableList<IProofReferencesAnalyst> analysts = ImmutableSLList.nil();
            if (analyst != null) {
                analysts = analysts.append(analyst);
            }
            LinkedHashSet<IProofReference<?>> references =
                ProofReferenceUtil.computeProofReferences(proof, analysts);
            // Filter references
            if (currentReferenceFilter != null) {
                LinkedHashSet<IProofReference<?>> filteredReferences =
                    new LinkedHashSet<>();
                for (IProofReference<?> reference : references) {
                    if (currentReferenceFilter.test(reference)) {
                        filteredReferences.add(reference);
                    }
                }
                references = filteredReferences;
            }
            // Assert proof references
            assertReferences(references, expectedReferences);
        };
    }

    /**
     * Extracts all {@link IProofReference}s of the given once which are extracted from the given
     * {@link Node}.
     *
     * @param references The {@link IProofReference}s to search in.
     * @param node The {@link Node} to look for.
     * @return The contained {@link IProofReference}s with the given node.
     */
    protected LinkedHashSet<IProofReference<?>> findReferences(
            LinkedHashSet<IProofReference<?>> references, Node node) {
        LinkedHashSet<IProofReference<?>> result = new LinkedHashSet<>();
        for (IProofReference<?> reference : references) {
            if (reference.getNodes().contains(node)) {
                result.add(reference);
            }
        }
        return result;
    }

    /**
     * Tests the given {@link IProofReference}s.
     *
     * @param expected The expected {@link IProofReference}s.
     * @param current The current {@link IProofReference}s.
     */
    protected void assertReferences(LinkedHashSet<IProofReference<?>> expected,
            LinkedHashSet<IProofReference<?>> current) {
        assertNotNull(current);
        assertNotNull(expected);
        assertEquals(current.size(), expected.size());
        Iterator<IProofReference<?>> expectedIter = expected.iterator();
        Iterator<IProofReference<?>> currentIter = current.iterator();
        while (expectedIter.hasNext() && currentIter.hasNext()) {
            IProofReference<?> expectedReference = expectedIter.next();
            IProofReference<?> currentReference = currentIter.next();
            assertEquals(expectedReference.getKind(), currentReference.getKind());
            if (expectedReference.getTarget() instanceof ClassAxiom) {
                assertTrue(currentReference.getTarget() instanceof ClassAxiom);
                assertEquals(expectedReference.getTarget().toString(),
                    currentReference.getTarget().toString()); // Instances might be different.
            } else {
                assertEquals(expectedReference.getTarget(), currentReference.getTarget());
            }
        }
        assertFalse(expectedIter.hasNext());
        assertFalse(currentIter.hasNext());
    }

    /**
     * Tests the given {@link IProofReference}s.
     *
     * @param current The current {@link IProofReference}s.
     * @param expected The expected {@link ExpectedProofReferences}s.
     */
    protected void assertReferences(LinkedHashSet<IProofReference<?>> current,
            ExpectedProofReferences... expected) {
        assertNotNull(current);
        assertNotNull(expected);
        assertEquals(expected.length, current.size(), "Computed References: " + current);
        int i = 0;
        for (IProofReference<?> currentReference : current) {
            ExpectedProofReferences expectedReference = expected[i];
            assertEquals(expectedReference.getKind(), currentReference.getKind());
            if (expectedReference.getTarget() != null) {
                assertNotNull(currentReference.getTarget());
                assertEquals(expectedReference.getTarget(),
                    currentReference.getTarget().toString());
            } else {
                assertNull(currentReference.getTarget());
            }
            i++;
        }
    }

    /**
     * Defines the values of an expected proof reference.
     *
     * @author Martin Hentschel
     */
    protected static class ExpectedProofReferences {
        /**
         * The expected kind.
         */
        private final String kind;

        /**
         * The expected target.
         */
        private final String target;

        /**
         * Constructor.
         *
         * @param kind The expected kind.
         * @param target The expected target.
         */
        public ExpectedProofReferences(String kind, String target) {
            this.kind = kind;
            this.target = target;
        }

        /**
         * Returns the expected kind.
         *
         * @return The expected kind.
         */
        public String getKind() {
            return kind;
        }

        /**
         * Returns the expected target.
         *
         * @return The expected target.
         */
        public String getTarget() {
            return target;
        }
    }

    /**
     * Does some test steps with a {@link Proof}.
     *
     * @param baseDir The base directory which contains test and oracle file.
     * @param javaPathInBaseDir The path to the java file inside the base directory.
     * @param containerTypeName The name of the type which contains the method.
     * @param targetName The target name to search.
     * @param useContracts Use contracts or inline method bodies instead.
     * @param tester The {@link IProofTester} which executes the test steps.
     * @throws Exception Occurred Exception.
     */
    protected void doProofFunctionTest(File baseDir, String javaPathInBaseDir,
            String containerTypeName, final String targetName, boolean useContracts,
            IProofTester tester) throws Exception {
        assertNotNull(tester);
        KeYEnvironment<?> environment = null;
        Proof proof = null;
        Map<String, String> originalTacletOptions = null;
        boolean usePrettyPrinting = ProofIndependentSettings.isUsePrettyPrinting();
        try {
            // Disable pretty printing to make tests more robust against different term
            // representations
            ProofIndependentSettings.setUsePrettyPrinting(false);
            // Make sure that required files exists
            File javaFile = new File(baseDir, javaPathInBaseDir);
            assertTrue(javaFile.exists());
            // Make sure that the correct taclet options are defined.
            originalTacletOptions = HelperClassForTests.setDefaultTacletOptionsForTarget(javaFile,
                containerTypeName, targetName);
            if (!useContracts) {
                // set non modular reasoning
                ChoiceSettings choiceSettings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
                ImmutableSet<Choice> cs = DefaultImmutableSet.nil();
                cs = cs.add(new Choice("noRestriction", "methodExpansion"));
                choiceSettings.updateWith(cs);
            }
            // Load java file
            environment = KeYEnvironment.load(javaFile, null, null, null);
            // Search type
            KeYJavaType containerKJT =
                environment.getJavaInfo().getTypeByClassName(containerTypeName, null);
            assertNotNull(containerKJT);
            // Search observer function
            ImmutableSet<IObserverFunction> targets =
                environment.getSpecificationRepository().getContractTargets(containerKJT);
            IObserverFunction target =
                CollectionUtil.search(targets, element -> targetName.equals(element.toString()));
            assertNotNull(target);
            // Find first contract.
            ImmutableSet<Contract> contracts =
                environment.getSpecificationRepository().getContracts(containerKJT, target);
            assertFalse(contracts.isEmpty());
            Contract contract = contracts.iterator().next();
            // Start proof
            proof = environment
                    .createProof(contract.createProofObl(environment.getInitConfig(), contract));
            assertNotNull(proof);
            // Start auto mode
            doProofTest(environment, proof, useContracts, tester);
        } finally {
            ProofIndependentSettings.setUsePrettyPrinting(usePrettyPrinting);
            // Restore taclet options
            HelperClassForTests.restoreTacletOptions(originalTacletOptions);
            // Dispose proof and environment
            if (proof != null) {
                proof.dispose();
            }
            if (environment != null) {
                environment.dispose();
            }
        }
    }

    /**
     * Does some test steps with a {@link Proof}.
     *
     * @param baseDir The base directory which contains test and oracle file.
     * @param javaPathInBaseDir The path to the java file inside the base directory.
     * @param containerTypeName The name of the type which contains the method.
     * @param methodFullName The method name to search.
     * @param useContracts Use contracts or inline method bodies instead.
     * @param tester The {@link IProofTester} which executes the test steps.
     * @throws Exception Occurred Exception.
     */
    protected void doProofMethodTest(File baseDir, String javaPathInBaseDir,
            String containerTypeName, String methodFullName, boolean useContracts,
            IProofTester tester) throws Exception {
        assertNotNull(tester);
        KeYEnvironment<?> environment = null;
        Proof proof = null;
        Map<String, String> originalTacletOptions = null;
        boolean usePrettyPrinting = ProofIndependentSettings.isUsePrettyPrinting();
        try {
            // Disable pretty printing to make tests more robust against different term
            // representations
            ProofIndependentSettings.setUsePrettyPrinting(false);
            // Make sure that required files exists
            File javaFile = new File(baseDir, javaPathInBaseDir);
            assertTrue(javaFile.exists());
            // Make sure that the correct taclet options are defined.
            originalTacletOptions =
                HelperClassForTests.setDefaultTacletOptions(baseDir, javaPathInBaseDir);

            if (!useContracts) {
                // set non modular reasoning
                ChoiceSettings choiceSettings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
                ImmutableSet<Choice> cs = DefaultImmutableSet.nil();
                cs = cs.add(new Choice("noRestriction", "methodExpansion"));
                choiceSettings.updateWith(cs);
            }
            // Load java file
            environment = KeYEnvironment.load(javaFile, null, null, null);
            // Search method to proof
            IProgramMethod pm = HelperClassForTests.searchProgramMethod(environment.getServices(),
                containerTypeName, methodFullName);
            // Find first contract.
            ImmutableSet<FunctionalOperationContract> operationContracts = environment
                    .getSpecificationRepository().getOperationContracts(pm.getContainerType(), pm);
            assertFalse(operationContracts.isEmpty());
            FunctionalOperationContract foc = operationContracts.iterator().next();
            // Start proof
            proof = environment.createProof(foc.createProofObl(environment.getInitConfig(), foc));
            assertNotNull(proof);
            // Start auto mode
            doProofTest(environment, proof, useContracts, tester);
        } finally {
            ProofIndependentSettings.setUsePrettyPrinting(usePrettyPrinting);
            // Restore taclet options
            HelperClassForTests.restoreTacletOptions(originalTacletOptions);
            // Dispose proof and environment
            if (proof != null) {
                proof.dispose();
            }
            if (environment != null) {
                environment.dispose();
            }
        }
    }

    /**
     * Does some test steps with a {@link Proof}.
     *
     * @param environment The {@link KeYEnvironment} which provides the {@link Proof}.
     * @param proof The {@link Proof} to test.
     * @param useContracts Use contracts or inline method bodies instead.
     * @param tester The {@link IProofTester} which executes the test steps.
     * @throws Exception Occurred Exception.
     */
    protected void doProofTest(KeYEnvironment<?> environment, Proof proof, boolean useContracts,
            IProofTester tester) throws Exception {
        // Test parameters
        assertNotNull(environment);
        assertNotNull(proof);
        assertNotNull(tester);
        // Start auto mode
        StrategyProperties sp = new StrategyProperties();
        StrategyProperties.setDefaultStrategyProperties(sp, true, useContracts, false, false, false,
            false);
        proof.getSettings().getStrategySettings().setActiveStrategyProperties(sp);
        proof.getSettings().getStrategySettings().setMaxSteps(1000);
        environment.getProofControl().startAndWaitForAutoMode(proof);
        // Do test
        tester.doTest(environment, proof);
    }

    /**
     * Executes some proof steps with on given {@link Proof}.
     *
     * @author Martin Hentschel
     */
    protected interface IProofTester {
        /**
         * Execute the test.
         *
         * @param environment The {@link KeYEnvironment} to test.
         * @param proof The {@link Proof} to test.
         * @throws Exception Occurred Exception.
         */
        void doTest(KeYEnvironment<?> environment, Proof proof) throws Exception;
    }
}
