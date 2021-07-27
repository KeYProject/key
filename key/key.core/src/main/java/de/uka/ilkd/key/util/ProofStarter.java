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

package de.uka.ilkd.key.util;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.AutoSaver;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.prover.GoalChooser;
import de.uka.ilkd.key.prover.ProverCore;
import de.uka.ilkd.key.prover.ProverTaskListener;
import de.uka.ilkd.key.prover.impl.ApplyStrategy;
import de.uka.ilkd.key.prover.impl.ApplyStrategyInfo;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyFactory;
import de.uka.ilkd.key.strategy.StrategyProperties;

/**
 * This class encapsulates the registration of a proof for a given problem.
 * It then starts a proof attempt.
 *
 * After the proof attempt stops (successfully or not) the side proof is by default
 * unregistered, but can be accessed via this class.
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

        public UserProvidedInput(Sequent seq, ProofEnvironment env, String proofName) {
            this.seq       = seq;
            this.env       = env;
            this.proofName = proofName;
        }

        public UserProvidedInput(Term formula, ProofEnvironment env) {
            this(Sequent.createSuccSequent(Semisequent.EMPTY_SEMISEQUENT.insertFirst(
                    new SequentFormula(formula)).semisequent()), env);
        }

        @Override
        public String name() {
            return proofName != null ? 
                   proofName : 
                   "ProofObligation for " + ProofSaver.printAnything(seq, null);
        }

        @Override
        public void readProblem() throws ProofInputException {
        }


        private Proof createProof(String proofName) {

            final InitConfig initConfig = env.getInitConfigForEnvironment().deepCopy();

            return new Proof(proofName,
                    seq,
                    EMPTY_PROOF_HEADER,
                    initConfig.createTacletIndex(),
                    initConfig.createBuiltInRuleIndex(),
                    initConfig );
        }


        @Override
        public ProofAggregate getPO() throws ProofInputException {
            final Proof proof = createProof(proofName != null ? proofName : "Proof object for "+ ProofSaver.printAnything(seq, null));

            return ProofAggregate.createProofAggregate(proof,
                                                       "ProofAggregate for claim: "+proof.name());
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
    
    private Proof proof;

    private int maxSteps = 2000;

    private long timeout = -1L;

    private ProverTaskListener ptl;
    
    private AutoSaver autoSaver;
    
    private Strategy strategy;
    
    /**
     * creates an instance of the ProofStarter
     * @param the ProofEnvironment in which the proof shall be performed
     */
    public ProofStarter(boolean useAutoSaver) {
       this(null, useAutoSaver);
    }

    /**
     * creates an instance of the ProofStarter
     * @param the ProofEnvironment in which the proof shall be performed
     */
    public ProofStarter(ProverTaskListener ptl, boolean useAutoSaver) {
    	this.ptl = ptl;
      if (useAutoSaver) {
         autoSaver = AutoSaver.getDefaultInstance();
      }
    }

    /**
     * creates a new proof object for formulaToProve and registers it in the given environment
     *
     * @throws ProofInputException
     */
    public void init(Term formulaToProve, ProofEnvironment env) throws ProofInputException {
        final ProofOblInput input = new UserProvidedInput(formulaToProve, env);
        proof = input.getPO().getFirstProof();
        proof.setEnv(env);
    }

    /**
     * creates a new proof object for sequentToProve and registers it in the given environment
     *
     * @throws ProofInputException
     */
    public void init(Sequent sequentToProve, ProofEnvironment env, String proofName) throws ProofInputException {
       final ProofOblInput input = new UserProvidedInput(sequentToProve, env, proofName);
       proof = input.getPO().getFirstProof();
       proof.setEnv(env);
    }

    /**
     * set timeout
     * @param timeout
     */
    public void setTimeout(long timeout) {
        this.timeout = timeout;
    }
    
    /**
     * Returns the maximal steps to be performed.
     * @return The maximal steps to be performed.
     */
    public int getMaxRuleApplications() {
       return this.maxSteps;
    }

    /**
     * set maximal steps to be performed
     * @param maxSteps
     */
    public void setMaxRuleApplications(int maxSteps) {
        this.maxSteps = maxSteps;
    }

    public void setStrategy(Strategy strategy) {
        this.strategy = strategy;
    }

    public void setStrategyProperties(StrategyProperties sp) {
       final Profile profile = proof.getInitConfig().getProfile();
       StrategyFactory factory = strategy != null ?
                                 profile.getStrategyFactory(strategy.name()) :
                                 profile.getDefaultStrategyFactory();
       setStrategy(factory.create(proof, sp));
    }

    /**
     * starts proof attempt
     * @return the proof after the attempt terminated
     */
     public ApplyStrategyInfo start() {
        return start(proof.openGoals());
     }

   /**
    * starts proof attempt
    * @return the proof after the attempt terminated
    */
    public ApplyStrategyInfo start(ImmutableList<Goal> goals) {
        try {
           final Profile profile = proof.getInitConfig().getProfile();
           
           if (strategy == null) {
              StrategyFactory factory = profile.getDefaultStrategyFactory();
              StrategyProperties sp = factory.getSettingsDefinition().getDefaultPropertiesFactory().createDefaultStrategyProperties();;
              strategy = factory.create(proof, sp);
           }

           proof.setActiveStrategy(strategy);
           
            // It is important that OSS is refreshed AFTER the strategy has been
            // set!
           OneStepSimplifier.refreshOSS(proof);

           GoalChooser goalChooser = profile.getSelectedGoalChooserBuilder().create();
           ProverCore prover = new ApplyStrategy(goalChooser);
           if (ptl != null) {
              prover.addProverTaskObserver(ptl);
           }
           if (autoSaver != null) {
              autoSaver.setProof(proof);
              prover.addProverTaskObserver(autoSaver);
           }

           ApplyStrategyInfo result;
           proof.setRuleAppIndexToAutoMode();
           
           result = prover.start(proof, goals, maxSteps, timeout, strategy.isStopAtFirstNonCloseableGoal());          
           
           if (result.isError()) {
               throw new RuntimeException("Proof attempt failed due to exception:"
                                           + result.getException(),
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
        } 
        finally {         
           proof.setRuleAppIndexToInteractiveMode();
        }
    }

    public void init(Proof proof) {
       this.proof = proof;
       this.setMaxRuleApplications(proof.getSettings().getStrategySettings().getMaxSteps());
       this.setTimeout(proof.getSettings().getStrategySettings().getTimeout());
       this.setStrategy(proof.getActiveStrategy());
    }
    
    /**
     * Returns the managed side {@link Proof}.
     * @return The managed side {@link Proof}.
     */
    public Proof getProof() {
      return proof;
    }
}