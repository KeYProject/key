/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project;

import java.io.File;
import java.util.*;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.settings.ChoiceSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.KeYTypeUtil;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.util.collection.ImmutableSet;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Example application which proves all proof obligations of the source folder 'example' using KeY.
 *
 * @author Martin Hentschel
 */
public class Main {
    private static final Logger LOGGER = LoggerFactory.getLogger(Main.class);

    /**
     * The program entry point.
     *
     * @param args The start parameters.
     */
    public static void main(String[] args) {
        File location = args.length == 1 ? new File(args[0]) : new File("example");
        // Path to the source code folder/file or to a *.proof file
        try {
            // Ensure that Taclets are parsed
            KeYEnvironment<?> env = setupEnvironment(location);
            proveEnvironmemt(env);
        } catch (ProblemLoaderException e) {
            LOGGER.info("Exception at '{}'", location, e);
        }
    }

    /**
     * sets up the environment with the Java project described by its location
     *
     * @param location the File with the path to the source directory of the Java project
     *        to be verified
     * @return the {@KeYEnvironment} that provides the context for all following verification tasks
     * @throws ProblemLoaderException if the setup fails
     */
    private static KeYEnvironment<?> setupEnvironment(File location) throws ProblemLoaderException {
        List<File> classPaths = null; // Optionally: Additional specifications for API classes
        File bootClassPath = null; // Optionally: Different default specifications for Java API
        List<File> includes = null; // Optionally: Additional includes to consider

        if (!ProofSettings.isChoiceSettingInitialised()) {
            KeYEnvironment<?> env =
                KeYEnvironment.load(location, classPaths, bootClassPath, includes);
            env.dispose();
        }
        // Set Taclet options
        ChoiceSettings choiceSettings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
        Map<String, String> oldSettings = choiceSettings.getDefaultChoices();
        Map<String, String> newSettings = new HashMap<>(oldSettings);
        newSettings.putAll(MiscTools.getDefaultTacletOptions());
        choiceSettings.setDefaultChoices(newSettings);
        // Load source code
        KeYEnvironment<?> env =
            KeYEnvironment.load(location, classPaths, bootClassPath, includes);
        // env.getLoadedProof() returns performed proof if a *.proof file is loaded
        return env;
    }

    /**
     * proves every specification for which KeY knows how to generate a contract
     *
     * @param env the {@link KeYEnvironment} to beverified
     */
    private static void proveEnvironmemt(KeYEnvironment<?> env) {
        try {
            final List<Contract> proofContracts = getContracts(env);

            for (Contract contract : proofContracts) {
                proveContract(env, contract);
            }
        } finally {
            env.dispose(); // Ensure always that all instances of KeYEnvironment are disposed
        }
    }

    /**
     * Collect all contracts (proof obligations) for the given environment
     *
     * @param env the {@link KeYEnvironment} to look for contracts
     * @return list of {@link Contract}s to be proven
     */
    private static List<Contract> getContracts(KeYEnvironment<?> env) {
        // List all specifications of all types in the source location (not classPaths and
        // bootClassPath)
        final List<Contract> proofContracts = new LinkedList<>();
        Set<KeYJavaType> kjts = env.getJavaInfo().getAllKeYJavaTypes();
        for (KeYJavaType type : kjts) {
            if (!KeYTypeUtil.isLibraryClass(type)) {
                ImmutableSet<IObserverFunction> targets =
                    env.getSpecificationRepository().getContractTargets(type);
                for (IObserverFunction target : targets) {
                    ImmutableSet<Contract> contracts =
                        env.getSpecificationRepository().getContracts(type, target);
                    for (Contract contract : contracts) {
                        proofContracts.add(contract);
                    }
                }
            }
        }
        return proofContracts;
    }

    /**
     * tries to prove the given contract in the specified environment
     *
     * @param env the {@link KeYEnvironment} in which to prove the contract
     * @param contract the {@link Contract} to be proven
     */
    private static void proveContract(KeYEnvironment<?> env, Contract contract) {
        Proof proof = null;
        try {
            // Create proof
            proof =
                env.createProof(contract.createProofObl(env.getInitConfig(), contract));
            // Set proof strategy options
            StrategyProperties sp =
                proof.getSettings().getStrategySettings().getActiveStrategyProperties();
            sp.setProperty(StrategyProperties.METHOD_OPTIONS_KEY,
                StrategyProperties.METHOD_CONTRACT);
            sp.setProperty(StrategyProperties.DEP_OPTIONS_KEY,
                StrategyProperties.DEP_ON);
            sp.setProperty(StrategyProperties.QUERY_OPTIONS_KEY,
                StrategyProperties.QUERY_ON);
            sp.setProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY,
                StrategyProperties.NON_LIN_ARITH_DEF_OPS);
            sp.setProperty(StrategyProperties.STOPMODE_OPTIONS_KEY,
                StrategyProperties.STOPMODE_NONCLOSE);
            proof.getSettings().getStrategySettings().setActiveStrategyProperties(sp);
            // Make sure that the new options are used
            int maxSteps = 10000;
            ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setMaxSteps(maxSteps);
            ProofSettings.DEFAULT_SETTINGS.getStrategySettings()
                    .setActiveStrategyProperties(sp);
            proof.getSettings().getStrategySettings().setMaxSteps(maxSteps);
            proof.setActiveStrategy(proof.getServices().getProfile()
                    .getDefaultStrategyFactory().create(proof, sp));
            // Start auto mode
            env.getUi().getProofControl().startAndWaitForAutoMode(proof);
            // Show proof result
            boolean closed = proof.openGoals().isEmpty();
            LOGGER.info("Contract '" + contract.getDisplayName() + "' of "
                + contract.getTarget() + " is " + (closed ? "verified" : "still open")
                + ".");
        } catch (ProofInputException e) {
            LOGGER.error("Exception at {} of {}", contract.getDisplayName(),
                contract.getTarget());
        } finally {
            if (proof != null) {
                proof.dispose(); // Ensure always that all instances of Proof are
                                 // disposed
            }
        }
    }
}
