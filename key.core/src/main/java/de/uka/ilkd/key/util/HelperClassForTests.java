/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;

import java.io.File;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.init.KeYUserProblemFile;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.RuleCollection;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.io.RuleSourceFactory;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.settings.ChoiceSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyProperties;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.helper.FindResources;
import org.key_project.util.java.CollectionUtil;

import static de.uka.ilkd.key.proof.io.RuleSource.ldtFile;

public class HelperClassForTests {

    public static final File TESTCASE_DIRECTORY = FindResources.getTestCasesDirectory();
    public static final File DUMMY_KEY_FILE = new File(TESTCASE_DIRECTORY, "dummyTrue.key");


    private static final Profile profile = new JavaProfile() {
        // we do not want normal standard rules, but ruleSetsDeclarations is needed for string
        // library (HACK)
        @Override
        public RuleCollection getStandardRules() {
            return new RuleCollection(RuleSourceFactory.fromDefaultLocation(ldtFile),
                ImmutableSLList.nil());
        }
    };

    public HelperClassForTests() {

    }

    public ProofAggregate parse(File file) {
        return parse(file, profile);
    }

    public ProofAggregate parse(File file, Profile profile) {
        ProblemInitializer pi = null;
        ProofAggregate result = null;

        try {
            KeYUserProblemFile po = new KeYUserProblemFile("UpdatetermTest", file, null, profile);
            pi = new ProblemInitializer(profile);

            result = pi.startProver(po, po);

        } catch (Exception e) {
            throw new RuntimeException(e);
        }
        return result;
    }

    public ProofAggregate parseThrowException(File file) throws ProofInputException {
        return parseThrowException(file, profile);
    }


    public ProofAggregate parseThrowException(File file, Profile profile)
            throws ProofInputException {
        KeYUserProblemFile po = new KeYUserProblemFile("UpdatetermTest", file, null, profile);
        ProblemInitializer pi = new ProblemInitializer(profile);
        return pi.startProver(po, po);
    }

    public Term extractProblemTerm(Proof p) {
        return p.root().sequent().succedent().iterator().next().formula();
    }

    /**
     * Checks if one step simplification is enabled in the given {@link Proof}.
     *
     * @param proof The {@link Proof} to read from or {@code null} to return the general settings
     *        value.
     * @return {@code true} one step simplification is enabled, {@code false} if disabled.
     */
    public static boolean isOneStepSimplificationEnabled(Proof proof) {
        StrategyProperties props;
        if (proof != null && !proof.isDisposed()) {
            props = proof.getSettings().getStrategySettings().getActiveStrategyProperties();
        } else {
            props =
                ProofSettings.DEFAULT_SETTINGS.getStrategySettings().getActiveStrategyProperties();
        }

        return props.get(StrategyProperties.OSS_OPTIONS_KEY).equals(StrategyProperties.OSS_ON);
    }

    /**
     * Defines if one step simplification is enabled in general and within the {@link Proof}.
     *
     * @param proof The optional {@link Proof}.
     * @param enabled {@code true} use one step simplification, {@code false} do not use one step
     *        simplification.
     */
    public static void setOneStepSimplificationEnabled(Proof proof, boolean enabled) {
        final String newVal = enabled ? StrategyProperties.OSS_ON : StrategyProperties.OSS_OFF;

        {
            final StrategyProperties newProps =
                ProofSettings.DEFAULT_SETTINGS.getStrategySettings().getActiveStrategyProperties();
            newProps.setProperty(StrategyProperties.OSS_OPTIONS_KEY, newVal);
            ProofSettings.DEFAULT_SETTINGS.getStrategySettings()
                    .setActiveStrategyProperties(newProps);
        }

        if (proof != null && !proof.isDisposed()) {
            final StrategyProperties newProps =
                proof.getSettings().getStrategySettings().getActiveStrategyProperties();
            newProps.setProperty(StrategyProperties.OSS_OPTIONS_KEY, newVal);

            Strategy.updateStrategySettings(proof, newProps);
            OneStepSimplifier.refreshOSS(proof);
        }
    }

    /**
     * Ensures that the default taclet options are defined.
     *
     * @param baseDir The base directory which contains the java file.
     * @param javaPathInBaseDir The path in the base directory to the java file.
     * @return The original settings which are overwritten.
     * @throws ProblemLoaderException Occurred Exception.
     * @throws ProofInputException Occurred Exception.
     */
    public static Map<String, String> setDefaultTacletOptions(File baseDir,
            String javaPathInBaseDir)
            throws ProblemLoaderException, ProofInputException {
        if (!ProofSettings.isChoiceSettingInitialised()) {
            // Make sure that required files exists
            File javaFile = new File(baseDir, javaPathInBaseDir);
            // Assert.assertTrue(javaFile.exists());
            // Load java file
            KeYEnvironment<DefaultUserInterfaceControl> environment =
                KeYEnvironment.load(javaFile, null, null, null);
            try {
                // Start proof
                ImmutableSet<Contract> contracts =
                    environment.getServices().getSpecificationRepository().getAllContracts();
                // Assert.assertFalse(contracts.isEmpty());
                Contract contract = contracts.iterator().next();
                ContractPO po = contract.createProofObl(environment.getInitConfig());
                Proof proof = environment.createProof(po);
                // Assert.assertNotNull(proof);
                proof.dispose();
            } finally {
                environment.dispose();
            }
        }
        return setDefaultTacletOptions();
    }

    /**
     * Ensures that the default taclet options are defined.
     *
     * @param javaFile The java file to load.
     * @param containerTypeName The type name which provides the target.
     * @param targetName The target to proof.
     * @return The original settings which are overwritten.
     * @throws ProblemLoaderException Occurred Exception.
     * @throws ProofInputException Occurred Exception.
     */
    public static Map<String, String> setDefaultTacletOptionsForTarget(File javaFile,
            String containerTypeName,
            final String targetName) throws ProblemLoaderException, ProofInputException {
        if (!ProofSettings.isChoiceSettingInitialised()) {
            KeYEnvironment<?> environment = null;
            Proof proof = null;
            try {
                // Load java file
                environment = KeYEnvironment.load(javaFile, null, null, null);
                // Search type
                KeYJavaType containerKJT =
                    environment.getJavaInfo().getTypeByClassName(containerTypeName);
                // Assert.assertNotNull(containerKJT);
                // Search observer function
                ImmutableSet<IObserverFunction> targets =
                    environment.getSpecificationRepository().getContractTargets(containerKJT);
                IObserverFunction target =
                    CollectionUtil.search(targets,
                        element -> targetName.equals(element.toString()));
                // Assert.assertNotNull(target);
                // Find first contract.
                ImmutableSet<Contract> contracts =
                    environment.getSpecificationRepository().getContracts(containerKJT, target);
                // Assert.assertFalse(contracts.isEmpty());
                Contract contract = contracts.iterator().next();
                // Start proof
                proof = environment.createProof(
                    contract.createProofObl(environment.getInitConfig(), contract));
                // Assert.assertNotNull(proof);
            } catch (Exception e) {
                if (proof != null) {
                    proof.dispose();
                }
                if (environment != null) {
                    environment.dispose();
                }
            }
        }
        return setDefaultTacletOptions();
    }

    /**
     * Ensures that the default taclet options are defined.
     *
     * @return The original settings which are overwritten.
     */
    public static Map<String, String> setDefaultTacletOptions() {
        // Assert.assertTrue(ProofSettings.isChoiceSettingInitialised());
        // Set default taclet options
        ChoiceSettings choiceSettings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
        var oldSettings = choiceSettings.getDefaultChoices();
        HashMap<String, String> newSettings = new HashMap<>(oldSettings);
        newSettings.putAll(MiscTools.getDefaultTacletOptions());
        choiceSettings.setDefaultChoices(newSettings);
        // Make sure that default taclet options are set
        var updatedChoiceSettings =
            ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().getDefaultChoices();
        for (Entry<String, String> entry : newSettings.entrySet()) {
            // Assert.assertEquals(entry.getValue(), updatedChoiceSettings.get(entry.getKey()));
        }
        return oldSettings;
    }

    /**
     * Restores the given taclet options.
     *
     * @param options The taclet options to restore.
     */
    public static void restoreTacletOptions(Map<String, String> options) {
        if (options != null) {
            // Assert.assertTrue(ProofSettings.isChoiceSettingInitialised());
            ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().setDefaultChoices(options);
            // Make sure that taclet options are restored
            var updatedChoiceSettings =
                ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().getDefaultChoices();
            for (Entry<String, String> entry : options.entrySet()) {
                // Assert.assertEquals(entry.getValue(), updatedChoiceSettings.get(entry.getKey()));
            }
        }
    }

    /**
     * Searches a {@link IProgramMethod} in the given {@link Services}.
     *
     * @param services The {@link Services} to search in.
     * @param containerTypeName The name of the type which contains the method.
     * @param methodFullName The method name to search.
     * @return The first found {@link IProgramMethod} in the type.
     */
    public static IProgramMethod searchProgramMethod(Services services, String containerTypeName,
            final String methodFullName) {
        JavaInfo javaInfo = services.getJavaInfo();
        KeYJavaType containerKJT = javaInfo.getTypeByClassName(containerTypeName);
        // Assert.assertNotNull(containerKJT);
        ImmutableList<IProgramMethod> pms = javaInfo.getAllProgramMethods(containerKJT);
        IProgramMethod pm =
            CollectionUtil.search(pms, element -> methodFullName.equals(element.getFullName()));
        if (pm == null) {
            pms = javaInfo.getConstructors(containerKJT);
            pm = CollectionUtil.search(pms,
                element -> methodFullName.equals(element.getFullName()));
        }
        // Assert.assertNotNull(pm);
        return pm;
    }

    public static Services createServices(File keyFile) {
        JavaInfo javaInfo = new HelperClassForTests().parse(keyFile).getFirstProof().getJavaInfo();
        return javaInfo.getServices();
    }

    public static Services createServices() {
        return createServices(DUMMY_KEY_FILE);
    }

    public static KeYEnvironment<DefaultUserInterfaceControl> createKeYEnvironment()
            throws ProblemLoaderException {
        return KeYEnvironment.load(DUMMY_KEY_FILE);
    }

}
