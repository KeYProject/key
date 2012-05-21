package de.uka.ilkd.key.symbolic_execution.util;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.mgt.AxiomJustification;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.proof.mgt.RuleJustification;
import de.uka.ilkd.key.proof.mgt.RuleJustificationInfo;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.jml.pretranslation.Behavior;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase;
import de.uka.ilkd.key.speclang.jml.translation.JMLSpecFactory;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;

/**
 * Provides utility methods for symbolic execution with KeY.
 * @author Martin Hentschel
 */
public final class SymbolicExecutionUtil {
   /**
    * Forbid instances.
    */
   private SymbolicExecutionUtil() {
   }
   
   /**
    * Creates a new default contract for the given {@link ProgramMethod}
    * which only ensures that the own invariants ({@code this.<inv>}) hold.
    * @param services The {@link Services} to use.
    * @param pm The {@link ProgramMethod} to create a default contract for.
    * @return The created {@link Contract}.
    * @throws SLTranslationException Occurred Exception.
    */
   public static FunctionalOperationContract createDefaultContract(Services services, ProgramMethod pm) throws SLTranslationException {
      // Create TextualJMLSpecCase
      ImmutableList<String> mods = ImmutableSLList.nil();
      mods = mods.append("public");
      TextualJMLSpecCase textualSpecCase = new TextualJMLSpecCase(mods, Behavior.NORMAL_BEHAVIOR);
      if (!pm.isStatic()) {
         textualSpecCase.addRequires(new PositionedString("this.<inv>")); // Assume own invariants
      }
      // Create contract
      JMLSpecFactory factory = new JMLSpecFactory(services);
      ImmutableSet<Contract> contracts = factory.createJMLOperationContracts(pm, textualSpecCase);
      return (FunctionalOperationContract)contracts.iterator().next();
   }
   
   /**
    * Creates a copy of the {@link ProofEnvironment} of the given {@link Proof}
    * which has his own {@link OneStepSimplifier} instance. Such copies are
    * required for instance during parallel usage of site proofs because
    * {@link OneStepSimplifier} has an internal state.
    * @param source The {@link Proof} to copy its {@link ProofEnvironment}.
    * @return The created {@link ProofEnvironment} which is a copy of the environment of the given {@link Proof} but with its own {@link OneStepSimplifier} instance.
    */
   public static ProofEnvironment cloneProofEnvironmentWithOwnOneStepSimplifier(Proof source) {
      assert source != null;
      // Get required source instances
      ProofEnvironment sourceEnv = source.env();
      InitConfig sourceInitConfig = sourceEnv.getInitConfig();
      RuleJustificationInfo sourceJustiInfo = sourceEnv.getJustifInfo();
      // Create new profile which has separate OneStepSimplifier instance
      JavaProfile profile = new JavaProfile() {
         @Override
         protected OneStepSimplifier getInitialOneStepSimpilifier() {
            return new OneStepSimplifier();
         }
      };
      // Create new InitConfig and initialize it with value from initial one.
      InitConfig initConfig = new InitConfig(source.getServices(), profile);
      initConfig.setActivatedChoices(sourceInitConfig.getActivatedChoices());
      initConfig.setSettings(sourceInitConfig.getSettings());
      initConfig.setTaclet2Builder(sourceInitConfig.getTaclet2Builder());
      initConfig.setTaclets(sourceInitConfig.getTaclets());
      // Create new ProofEnvironment and initialize it with values from initial one.
      ProofEnvironment env = new ProofEnvironment(initConfig);
      env.setJavaModel(sourceEnv.getJavaModel());
      env.setNumber(sourceEnv.getNumber());
      env.setRuleConfig(sourceEnv.getRuleConfig());
      for (Taclet taclet : sourceInitConfig.activatedTaclets()) {
         env.getJustifInfo().addJustification(taclet, sourceJustiInfo.getJustification(taclet));
      }
      for (BuiltInRule rule : initConfig.builtInRules()) {
         RuleJustification origJusti = sourceJustiInfo.getJustification(rule);
         if (origJusti == null) {
            assert rule instanceof OneStepSimplifier;
            origJusti = AxiomJustification.INSTANCE;
         }
         env.getJustifInfo().addJustification(rule, origJusti);
      }
      return env;
   }
}
