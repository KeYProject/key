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

package de.uka.ilkd.key.ui;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.TaskFinishedInfo;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;

/**
 * <p>
 * An extended version of {@link AbstractConsoleUserInterface} which can be used
 * to prove manually instantiated proofs.
 * </p>
 * <p>
 * The basic usage is like:
 * <code><pre>
 * // Create user interface
 * CustomUserInterface ui = new CustomUserInterface(false);
 * // Load java file
 * InitConfig initConfig = ui.load(javaFile, null, null);
 * // Find operation contract to proof in services
 * Services services = initConfig.getServices();
 * FunctionalOperationContract contract ...
 * // Start proof
 * ProofOblInput input = new FunctionalOperationContractPO(initConfig, contract);
 * Proof proof = ui.createProof(initConfig, input);
 * // Run proof in auto mode
 * ui.startAndWaitForProof(proof);
 * </pre></code>
 * </p>
 * @author Martin Hentschel
 */
public class CustomUserInterface extends AbstractUserInterface {
   /**
    * The used {@link DefaultProofControl}.
    */
   private final DefaultProofControl proofControl;
   
   /**
    * Constructor.
    */
   public CustomUserInterface() {
      proofControl = new DefaultProofControl(getListener());
   }

   /**
    * Constructor.
    * @param customization An optional {@link RuleCompletionHandler}.
    */
   public CustomUserInterface(RuleCompletionHandler customization) {
      proofControl = new DefaultProofControl(getListener(), customization);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public DefaultProofControl getProofControl() {
      return proofControl;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public ProofEnvironment createProofEnvironmentAndRegisterProof(ProofOblInput proofOblInput, ProofAggregate proofList, InitConfig initConfig) {
      //TODO: Find out why the proof has to be registered. This method should just return null and do nothing.
      initConfig.getServices().getSpecificationRepository().registerProof(proofOblInput, proofList.getFirstProof());
      return null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean selectProofObligation(InitConfig initConfig) {
      return false; // Not supported.
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void removeProof(Proof proof) {
      proof.dispose();
   }

   @Override
   public void taskFinished(TaskFinishedInfo info) {
      // Nothing to do
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void taskStarted(String message, int size) {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void progressStarted(Object sender) {
      // Nothing to do
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void progressStopped(Object sender) {
      // Nothing to do
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void reportStatus(Object sender, String status, int progress) {
      // Nothing to do
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void reportStatus(Object sender, String status) {
      // Nothing to do
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void resetStatus(Object sender) {
      // Nothing to do
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void reportException(Object sender, ProofOblInput input, Exception e) {
      // Nothing to do
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void taskProgress(int position) {
      // Nothing to do
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setProgress(int progress) {
      // Nothing to do
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setMaximum(int maximum) {
      // Nothing to do
   }
}