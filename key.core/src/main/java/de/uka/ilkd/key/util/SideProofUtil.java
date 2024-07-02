package de.uka.ilkd.key.util;

import java.util.HashMap;

import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.logic.Choice;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.mgt.AxiomJustification;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.proof.mgt.RuleJustification;
import de.uka.ilkd.key.proof.mgt.RuleJustificationInfo;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.tacletbuilder.TacletBuilder;
import de.uka.ilkd.key.settings.ProofSettings;

public final class SideProofUtil {
   /**
    * Forbid instances.
    */
   private SideProofUtil() {
   }

   /**
    * Creates a copy of the {@link ProofEnvironment} of the given {@link Proof}
    * which has his own {@link OneStepSimplifier} instance. Such copies are
    * required for instance during parallel usage of site proofs because
    * {@link OneStepSimplifier} has an internal state.
    * @param source The {@link Proof} to copy its {@link ProofEnvironment}.
    * @param enableChoices The {@link Choice}s that should be changed w.r.t. those derived from {@link Proof#getInitConfig()} 
    * @return The created {@link ProofEnvironment} which is a copy of the environment of the given {@link Proof} but with its own {@link OneStepSimplifier} instance.
    */
   @SuppressWarnings("unchecked")
public static ProofEnvironment cloneProofEnvironmentWithOwnOneStepSimplifier(final Proof source, 
        final Choice... enableChoices) {
      assert source != null;
      assert !source.isDisposed();
      // Get required source instances
      final InitConfig sourceInitConfig = source.getInitConfig();
      final RuleJustificationInfo sourceJustiInfo = sourceInitConfig.getJustifInfo();
      // Create new profile which has separate OneStepSimplifier instance
      JavaProfile profile = new JavaProfile();
      // Create new InitConfig
      final InitConfig initConfig = new InitConfig(source.getServices().copy(profile, false));
      // Set modified taclet options in which runtime exceptions are banned.      
      ImmutableSet<Choice> choices = sourceInitConfig.getActivatedChoices();
      for (Choice enabled : enableChoices) {
          choices = activateChoice(choices, enabled);
      }
      initConfig.setActivatedChoices(choices);
      // Initialize InitConfig with settings from the original InitConfig.
      final ProofSettings clonedSettings = sourceInitConfig.getSettings() != null ? new ProofSettings(sourceInitConfig.getSettings()) : null;
      initConfig.setSettings(clonedSettings);
      initConfig.setTaclet2Builder((HashMap<Taclet, TacletBuilder<? extends Taclet>>) 
              sourceInitConfig.getTaclet2Builder().clone());
      initConfig.setTaclets(sourceInitConfig.getTaclets());
      // Create new ProofEnvironment and initialize it with values from initial one.
      ProofEnvironment env = new ProofEnvironment(initConfig);
      for (Taclet taclet : initConfig.activatedTaclets()) {
         initConfig.getJustifInfo().addJustification(taclet, sourceJustiInfo.getJustification(taclet));
      }
      for (BuiltInRule rule : initConfig.builtInRules()) {
         RuleJustification origJusti = sourceJustiInfo.getJustification(rule);
         if (origJusti == null) {
            assert rule instanceof OneStepSimplifier;
            origJusti = AxiomJustification.INSTANCE;
         }
         initConfig.getJustifInfo().addJustification(rule, origJusti);
      }
      return env;
   }
   
   /**
    * removes all choices with the same category as {@code choiceToActivate} from
    * {@code choices} and adds {@link choiceToActivate} to the set
    * @param choices the currently active choices
    * @param choiceToActivate the {@link Choice} to activate
    * @return the set of choices with {@code choiceToActivate} added (i.e., 
    * {@code choices.contains(choiceToActivate)} will return true) and all
    * other choices of the same category removed 
    */
   public static ImmutableSet<Choice> activateChoice(
           ImmutableSet<Choice> choices, Choice choiceToActivate) {
       boolean alreadySet = false;
       for (Choice choice : choices) {
           if (choiceToActivate.equals(choice)) {
               alreadySet = true;
           } else if (choice.category().equals(choiceToActivate.category())) {
               choices = choices.remove(choice);
           }          
       }
       if (!alreadySet) {
           choices = choices.add(choiceToActivate);
       }
       return choices;
   }

   /**
    * Creates a new {@link ProofStarter} which contains a new site proof
    * of the given {@link Proof}.
    * @param sideProofEnvironment The given {@link ProofEnvironment} of the side proof.
    * @param sequentToProve The {@link Sequent} to proof in a new site proof.
    * @param proofName An optional name for the newly created {@link Proof}.
    * @return The created {@link ProofStarter} with the site proof.
    * @throws ProofInputException Occurred Exception.
    */
   public static ProofStarter createSideProof(ProofEnvironment sideProofEnvironment,
                                              Sequent sequentToProve,
                                              String proofName) throws ProofInputException {
      // Make sure that valid parameters are given
      assert sequentToProve != null;
      // Create ProofStarter
      ProofStarter starter = new ProofStarter(false);
      // Configure ProofStarter
      //TODO: Avoid proof environment use only InitConfig
      starter.init(sequentToProve, sideProofEnvironment, proofName);
      return starter;
   }
}
