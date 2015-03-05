package de.uka.ilkd.key.smt.counterexample;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.util.ProofStarter;
import de.uka.ilkd.key.util.SideProofUtil;

/**
 * Implementation of {@link AbstractCounterExampleGenerator} which instantiates
 * the new {@link Proof} as side proof.
 */
public abstract class AbstractSideProofCounterExampleGenerator extends AbstractCounterExampleGenerator {
   /**
    * {@inheritDoc}
    */
   @Override
   protected Proof createProof(UserInterfaceControl ui, Proof oldProof, Sequent oldSequent, String proofName) throws ProofInputException {
      Sequent newSequent = createNewSequent(oldSequent);
      ProofEnvironment env = SideProofUtil.cloneProofEnvironmentWithOwnOneStepSimplifier(oldProof);
      ProofStarter starter = SideProofUtil.createSideProof(env, newSequent, proofName);
      Proof proof = starter.getProof();
      OneStepSimplifier.refreshOSS(proof);
      return proof;
   }
}
