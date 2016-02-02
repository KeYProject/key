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

package de.uka.ilkd.key.control;

import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.speclang.PositionedString;

/**
 * The {@link DefaultUserInterfaceControl} which allows proving in case
 * that no specific user interface is available.
 * <p>
 * In case that no user interface should be used see also {@link KeYEnvironment}
 * which provides static methods to load source code and to instantiate this
 * class.
 * @author Martin Hentschel
 * @see KeYEnvironment
 */
public class DefaultUserInterfaceControl extends AbstractUserInterfaceControl {
   /**
    * The used {@link DefaultProofControl}.
    */
   private final DefaultProofControl proofControl;
   
   /**
    * Constructor.
    */
   public DefaultUserInterfaceControl() {
      proofControl = new DefaultProofControl(this, this);
   }

   /**
    * Constructor.
    * @param customization An optional {@link RuleCompletionHandler}.
    */
   public DefaultUserInterfaceControl(RuleCompletionHandler customization) {
      proofControl = new DefaultProofControl(this, this, customization);
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

      // This has to be done to prive the proofList with the environment object.
      final ProofEnvironment env = new ProofEnvironment(initConfig);
      env.registerProof(proofOblInput, proofList);
      return env;
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

   /**
    * {@inheritDoc}
    */
   @Override
   public void registerProofAggregate(ProofAggregate pa) {
      // Nothing to do
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void reportWarnings(ImmutableSet<PositionedString> warnings) {
      // Nothing to do
   }
}