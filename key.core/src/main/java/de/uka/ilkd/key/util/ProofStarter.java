/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.calculus.JavaDLSequentKit;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.AutoSaver;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.prover.impl.ApplyStrategy;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyFactory;
import de.uka.ilkd.key.strategy.StrategyProperties;

import org.key_project.prover.engine.ProofSearchInformation;
import org.key_project.prover.engine.ProverCore;
import org.key_project.prover.engine.ProverTaskListener;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.jspecify.annotations.Nullable;

/**
 * This class encapsulates the registration of a proof for a given problem. It then starts a proof
 * attempt.
 * <p>
 * After the proof attempt stops (successfully or not) the side proof is by default unregistered,
 * but can be accessed via this class.
 * </p>
 *
 * @author Richard Bubel
 */
public class ProofStarter {

    /**
     * Proof obligation for a given formula or sequent
     */
    public static class UserProvidedInput implements ProofOblInput {

        private static final String EMPTY_PROOF_HEADER = "";
        private final ProofEnvironment env;
        private final Sequent seq;
        private final String proofName;

        public UserProvidedInput(Sequent seq, ProofEnvironment env) {
            this(seq, env, null);
        }

        public UserProvidedInput(Sequent seq, ProofEnvironment env, @Nullable String proofName) {
            this.seq = seq;
            this.env = env;
            this.proofName = proofName != null ? proofName
                    : "ProofObligation for " + ProofSaver.printAnything(seq, null);
        }

        public UserProvidedInput(JTerm formula, ProofEnvironment env) {
            this(
                JavaDLSequentKit.createSuccSequent(
                    ImmutableSLList.<SequentFormula>nil().prepend(new SequentFormula(formula))),
                env);
        }

        @Override
        public String name() {
            return proofName;
        }

        @Override
        public void readProblem() throws ProofInputException {
        }


        private Proof createProof(String proofName) {

            final InitConfig initConfig = env.getInitConfigForEnvironment().deepCopy();

            return new Proof(proofName, seq, EMPTY_PROOF_HEADER, initConfig.createTacletIndex(),
                initConfig.createBuiltInRuleIndex(), initConfig);
        }


        @Override
        public ProofAggregate getPO() throws ProofInputException {
            final Proof proof = createProof(proofName);
            return ProofAggregate.createProofAggregate(proof,
                "ProofAggregate for claim: " + proof.name());
        }

        @Override
        public boolean implies(ProofOblInput po) {
            return this == po;
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public KeYJavaType getContainerType() {
            return null;
        }
    }

    private @Nullable Proof proof;

    private int maxSteps = 2000;

    private long timeout = -1L;

    private @Nullable final ProverTaskListener ptl;

    private @Nullable AutoSaver autoSaver;

    private @Nullable Strategy strategy;

    /**
     * creates an instance of the ProofStarter
     *
     * @param useAutoSaver boolean indicating whether the proof shall be auto saved
     */
    public ProofStarter(boolean useAutoSaver) {
        this(null, useAutoSaver);
    }

    /**
     * creates an instance of the ProofStarter
     *
     * @param ptl the ProverTaskListener to be informed about certain events
     * @param useAutoSaver boolean indicating whether the proof shall be auto saved
     */
    public ProofStarter(@Nullable ProverTaskListener ptl, boolean useAutoSaver) {
        this.ptl = ptl;
        if (useAutoSaver) {
            autoSaver = AutoSaver.getDefaultInstance();
        }
    }

    /**
     * creates a new proof object for formulaToProve and registers it in the given environment
     *
     * @throws ProofInputException if the proof obligation generation fails
     */
    public void init(JTerm formulaToProve, ProofEnvironment env) throws ProofInputException {
        final ProofOblInput input = new UserProvidedInput(formulaToProve, env);
        proof = input.getPO().getFirstProof();
        proof.setEnv(env);
    }

    /**
     * creates a new proof object for sequentToProve and registers it in the given environment
     *
     * @throws ProofInputException if the proof obligation generation fails
     */
    public void init(Sequent sequentToProve, ProofEnvironment env, String proofName)
            throws ProofInputException {
        final ProofOblInput input = new UserProvidedInput(sequentToProve, env, proofName);
        proof = input.getPO().getFirstProof();
        proof.setEnv(env);
    }

    /**
     * set timeout for the proof search; the value {@code -1} disables the timeout
     *
     * @param timeout long specifying the time limit in milliseconds (ms)
     */
    public void setTimeout(long timeout) {
        this.timeout = timeout;
    }

    /**
     * Returns the maximal steps to be performed.
     *
     * @return The maximal steps to be performed.
     */
    public int getMaxRuleApplications() {
        return this.maxSteps;
    }

    /**
     * set maximal steps to be performed
     *
     * @param maxSteps the maximal proof steps (rule applications) to be applied during proof search
     */
    public void setMaxRuleApplications(int maxSteps) {
        this.maxSteps = maxSteps;
    }

    public void setStrategy(Strategy strategy) {
        this.strategy = strategy;
    }

    /**
     * Initializes the strategy with the provided settings. The proof object must be created at that
     * point.
     *
     * @param sp the Strategy properties to be used for the proof search
     * @throws NullPointerException if the proof object is not yet created
     */
    public void setStrategyProperties(StrategyProperties sp) {
        final Profile profile = proof.getInitConfig().getProfile();
        StrategyFactory factory = strategy != null ? profile.getStrategyFactory(strategy.name())
                : profile.getDefaultStrategyFactory();
        setStrategy(factory.create(proof, sp));
    }

    /**
     * Starts proof attempt. The proof object must be created at that point.
     *
     * @return the proof after the attempt terminated
     *
     * @throws NullPointerException if the proof object is not yet created
     */
    public ProofSearchInformation<Proof, Goal> start() {
        return start(proof.openGoals());
    }

    /**
     * Starts the proof attempt. The proof object must be created at that point.
     *
     * @return the proof after the attempt terminated
     * @throws NullPointerException if the proof object is not yet created
     */
    public ProofSearchInformation<Proof, Goal> start(ImmutableList<Goal> goals) {
        try {
            final Profile profile = proof.getInitConfig().getProfile();

            if (strategy == null) {
                StrategyFactory factory = profile.getDefaultStrategyFactory();
                StrategyProperties sp = factory.getSettingsDefinition()
                        .getDefaultPropertiesFactory().createDefaultStrategyProperties();
                strategy = factory.create(proof, sp);
            }

            proof.setActiveStrategy(strategy);

            // It is important that OSS is refreshed AFTER the strategy has been
            // set!
            OneStepSimplifier.refreshOSS(proof);

            var goalChooser = profile.<Proof, Goal>getSelectedGoalChooserBuilder().create();
            ProverCore<Proof, Goal> prover = new ApplyStrategy(goalChooser);
            if (ptl != null) {
                prover.addProverTaskObserver(ptl);
            }
            if (autoSaver != null) {
                autoSaver.setProof(proof);
                prover.addProverTaskObserver(autoSaver);
            }

            ProofSearchInformation<Proof, Goal> result;
            proof.setRuleAppIndexToAutoMode();

            result = prover.start(proof, goals, maxSteps, timeout,
                strategy.isStopAtFirstNonCloseableGoal());

            if (result.isError()) {
                throw new RuntimeException(
                    "Proof attempt failed due to exception:" + result.getException(),
                    result.getException());
            }

            if (ptl != null) {
                prover.removeProverTaskObserver(ptl);
            }
            if (autoSaver != null) {
                prover.removeProverTaskObserver(autoSaver);
                autoSaver.setProof(null);
            }

            return result;
        } finally {
            proof.setRuleAppIndexToInteractiveMode();
        }
    }

    /**
     * Initializes the proof starter with the provided proof object. All settings for the proof
     * search
     * are queried from the proof object
     *
     * @param proof the {@link Proof} on which to run the proof attempt
     */
    public void init(Proof proof) {
        this.proof = proof;
        this.setMaxRuleApplications(proof.getSettings().getStrategySettings().getMaxSteps());
        this.setTimeout(proof.getSettings().getStrategySettings().getTimeout());
        this.setStrategy(proof.getActiveStrategy());
    }

    /**
     * Returns the managed side {@link Proof}.
     *
     * @return The managed side {@link Proof}.
     */
    public @Nullable Proof getProof() {
        return proof;
    }
}
