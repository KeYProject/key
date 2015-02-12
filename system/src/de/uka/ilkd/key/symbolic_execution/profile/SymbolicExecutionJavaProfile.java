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

package de.uka.ilkd.key.symbolic_execution.profile;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.label.FormulaTermLabel;
import de.uka.ilkd.key.logic.label.FormulaTermLabelFactory;
import de.uka.ilkd.key.logic.label.SingletonLabelFactory;
import de.uka.ilkd.key.logic.label.SymbolicExecutionTermLabel;
import de.uka.ilkd.key.logic.label.SymbolicExecutionTermLabelFactory;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelFactory;
import de.uka.ilkd.key.logic.label.TermLabelManager.TermLabelConfiguration;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.label.LoopBodyTermLabelUpdate;
import de.uka.ilkd.key.rule.label.LoopInvariantNormalBehaviorTermLabelUpdate;
import de.uka.ilkd.key.rule.label.FormulaTermLabelRefactoring;
import de.uka.ilkd.key.rule.label.FormulaTermLabelUpdate;
import de.uka.ilkd.key.rule.label.RemoveInCheckBranchesTermLabelRefactoring;
import de.uka.ilkd.key.rule.label.StayOnOperatorTermLabelPolicy;
import de.uka.ilkd.key.rule.label.StayOnFormulaTermLabelPolicy;
import de.uka.ilkd.key.rule.label.SymbolicExecutionTermLabelUpdate;
import de.uka.ilkd.key.rule.label.TermLabelPolicy;
import de.uka.ilkd.key.rule.label.TermLabelRefactoring;
import de.uka.ilkd.key.rule.label.TermLabelUpdate;
import de.uka.ilkd.key.strategy.StrategyFactory;
import de.uka.ilkd.key.symbolic_execution.rule.ModalitySideProofRule;
import de.uka.ilkd.key.symbolic_execution.rule.QuerySideProofRule;
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionStrategy;

/**
 * An extended {@link JavaProfile} used by the symbolic execution API.
 * @author Martin Hentschel
 */
public class SymbolicExecutionJavaProfile extends JavaProfile {
   /**
    * The {@link Name} of this {@link Profile}.
    */
   public static final String NAME = "Java Profile for Symbolic Execution";
   
   /**
    * The used {@link StrategyFactory} of the {@link SymbolicExecutionStrategy}.
    */
   private final static StrategyFactory SYMBOLIC_EXECUTION_FACTORY = new SymbolicExecutionStrategy.Factory();
   
   /**
    * {@code true} truth value evaluation is enabled, {@code false} truth value evaluation is disabled.
    */
   private final Boolean truthValueEvaluationEnabled;
   
   /**
    * <p>
    * The default instance of this class.
    * </p>
    * <p> 
    * It is typically used in the {@link Thread} of the user interface.
    * Other instances of this class are typically only required to 
    * use them in different {@link Thread}s (not the UI {@link Thread}).
    * </p>
    */
   public static SymbolicExecutionJavaProfile defaultInstance; 
   
   /**
    * <p>
    * The default instance of this class.
    * </p>
    * <p> 
    * It is typically used in the {@link Thread} of the user interface.
    * Other instances of this class are typically only required to 
    * use them in different {@link Thread}s (not the UI {@link Thread}).
    * </p>
    */
   public static SymbolicExecutionJavaProfile defaultInstanceWithTruthValueEvaluation; 

   /**
    * Constructor.
    * @param predicateEvaluationEnabled {@code true} predicate evaluation is enabled, {@code false} predicate evaluation is disabled.
    */
   public SymbolicExecutionJavaProfile(boolean predicateEvaluationEnabled) {
      this.truthValueEvaluationEnabled = predicateEvaluationEnabled;
      initTermLabelManager();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void initTermLabelManager() {
      if (truthValueEvaluationEnabled != null) {
         // Create TermLabelManager only after predicate evaluation enabled flag is set.
         super.initTermLabelManager();
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected ImmutableList<TermLabelConfiguration> computeTermLabelConfiguration() {
      ImmutableList<TermLabelConfiguration> result = super.computeTermLabelConfiguration();
      result = result.prepend(getSymbolicExecutionTermLabelConfigurations(truthValueEvaluationEnabled));
      return result;
   }

   /**
    * Returns the additional {@link TermLabelFactory} instances used for symbolic execution.
    * @param predicateEvaluationEnabled {@code true} predicate evaluation is enabled, {@code false} predicate evaluation is disabled.
    * @return The additional {@link TermLabelFactory} instances used for symbolic execution.
    */
   public static ImmutableList<TermLabelConfiguration> getSymbolicExecutionTermLabelConfigurations(boolean predicateEvaluationEnabled) {
      ImmutableList<TermLabelPolicy> symExcPolicies = ImmutableSLList.<TermLabelPolicy>nil().prepend(new StayOnOperatorTermLabelPolicy());

      ImmutableList<TermLabelUpdate> lbUps = ImmutableSLList.<TermLabelUpdate>nil().prepend(new LoopBodyTermLabelUpdate());
      ImmutableList<TermLabelUpdate> nbUps = ImmutableSLList.<TermLabelUpdate>nil().prepend(new LoopInvariantNormalBehaviorTermLabelUpdate());
      ImmutableList<TermLabelUpdate> seUps = ImmutableSLList.<TermLabelUpdate>nil().prepend(new SymbolicExecutionTermLabelUpdate());

      ImmutableList<TermLabelRefactoring> lbRefs = ImmutableSLList.<TermLabelRefactoring>nil().prepend(new RemoveInCheckBranchesTermLabelRefactoring(ParameterlessTermLabel.LOOP_BODY_LABEL_NAME));
      ImmutableList<TermLabelRefactoring> nbRefs = ImmutableSLList.<TermLabelRefactoring>nil().prepend(new RemoveInCheckBranchesTermLabelRefactoring(ParameterlessTermLabel.LOOP_INVARIANT_NORMAL_BEHAVIOR_LABEL_NAME));
      ImmutableList<TermLabelRefactoring> seRefs = ImmutableSLList.<TermLabelRefactoring>nil().prepend(new RemoveInCheckBranchesTermLabelRefactoring(SymbolicExecutionTermLabel.NAME));
      
      ImmutableList<TermLabelConfiguration> result = ImmutableSLList.nil();
      result = result.prepend(new TermLabelConfiguration(ParameterlessTermLabel.LOOP_BODY_LABEL_NAME,
                                                         new SingletonLabelFactory<TermLabel>(ParameterlessTermLabel.LOOP_BODY_LABEL),
                                                         null,
                                                         symExcPolicies,
                                                         null,
                                                         null,
                                                         lbUps,
                                                         lbRefs));
      result = result.prepend(new TermLabelConfiguration(ParameterlessTermLabel.LOOP_INVARIANT_NORMAL_BEHAVIOR_LABEL_NAME,
                                                         new SingletonLabelFactory<TermLabel>(ParameterlessTermLabel.LOOP_INVARIANT_NORMAL_BEHAVIOR_LABEL),
                                                         null,
                                                         symExcPolicies,
                                                         null,
                                                         null,
                                                         nbUps,
                                                         nbRefs));
      result = result.prepend(new TermLabelConfiguration(SymbolicExecutionTermLabel.NAME,
                                                         new SymbolicExecutionTermLabelFactory(),
                                                         null,
                                                         symExcPolicies,
                                                         null,
                                                         null,
                                                         seUps,
                                                         seRefs));
      if (predicateEvaluationEnabled) {
         ImmutableList<TermLabelPolicy> predPolicies = ImmutableSLList.<TermLabelPolicy>nil().prepend(new StayOnFormulaTermLabelPolicy());
         ImmutableList<TermLabelUpdate> predUpdates = ImmutableSLList.<TermLabelUpdate>nil().prepend(new FormulaTermLabelUpdate());
         ImmutableList<TermLabelRefactoring> predRefs = ImmutableSLList.<TermLabelRefactoring>nil().prepend(new FormulaTermLabelRefactoring());
         result = result.prepend(new TermLabelConfiguration(FormulaTermLabel.NAME,
                                                            new FormulaTermLabelFactory(),
                                                            null,
                                                            predPolicies,
                                                            null,
                                                            null,
                                                            predUpdates,
                                                            predRefs));
      }
      return result;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected ImmutableSet<StrategyFactory> getStrategyFactories() {
      ImmutableSet<StrategyFactory> set = super.getStrategyFactories();
      set = set.add(SYMBOLIC_EXECUTION_FACTORY);
      return set;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected ImmutableList<BuiltInRule> initBuiltInRules() { 
      ImmutableList<BuiltInRule> builtInRules = super.initBuiltInRules();
      builtInRules = builtInRules.prepend(QuerySideProofRule.INSTANCE);
      builtInRules = builtInRules.prepend(ModalitySideProofRule.INSTANCE);
      return builtInRules;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String name() {
      return NAME;
   }

   /**
    * Checks if predicate evaluation is enabled or not.
    * @return {@code true} predicate evaluation is enabled, {@code false} predicate evaluation is disabled.
    */
   public boolean isPredicateEvaluationEnabled() {
      return truthValueEvaluationEnabled;
   }

   /**
    * <p>
    * Returns the default instance of this class.
    * </p>
    * <p>
    * It is typically used in the {@link Thread} of the user interface.
    * Other instances of this class are typically only required to 
    * use them in different {@link Thread}s (not the UI {@link Thread}).
    * </p>
    * @return The default instance for usage in the {@link Thread} of the user interface.
    */
   public static synchronized SymbolicExecutionJavaProfile getDefaultInstance() {
      return getDefaultInstance(false);
   }

   /**
    * <p>
    * Returns the default instance of this class.
    * </p>
    * <p>
    * It is typically used in the {@link Thread} of the user interface.
    * Other instances of this class are typically only required to 
    * use them in different {@link Thread}s (not the UI {@link Thread}).
    * </p>
    * @param truthValueEvaluationEnabled {@code true} truth value evaluation is enabled, {@code false} truth value evaluation is disabled.
    * @return The default instance for usage in the {@link Thread} of the user interface.
    */
   public static synchronized SymbolicExecutionJavaProfile getDefaultInstance(boolean truthValueEvaluationEnabled) {
      if (!truthValueEvaluationEnabled) {
         if (defaultInstance == null) {
            defaultInstance = new SymbolicExecutionJavaProfile(false);
         }
         return defaultInstance;
      }
      else {
         if (defaultInstanceWithTruthValueEvaluation == null) {
            defaultInstanceWithTruthValueEvaluation = new SymbolicExecutionJavaProfile(true);
         }
         return defaultInstanceWithTruthValueEvaluation;
      }
   }

   /**
    * Checks if truth value evaluation is enabled in the given {@link Proof}.
    * @param proof The {@link Proof} to check.
    * @return {@code true} truth value evaluation is enabled, {@code false} truth value evaluation is disabled.
    */
   public static boolean isTruthValueEvaluationEnabled(Proof proof) {
      if (proof != null && !proof.isDisposed()) {
         return isTruthValueEvaluationEnabled(proof.getInitConfig());
      }
      else {
         return false;
      }
   }

   /**
    * Checks if truth value evaluation is enabled in the given {@link InitConfig}.
    * @param initConfig The {@link InitConfig} to check.
    * @return {@code true} truth value evaluation is enabled, {@code false} truth value evaluation is disabled.
    */
   public static boolean isTruthValueEvaluationEnabled(InitConfig initConfig) {
      if (initConfig != null) {
         return isTruthValueEvaluationEnabled(initConfig.getProfile());
      }
      else {
         return false;
      }
   }

   /**
    * Checks if predicate evaluation is enabled in the given {@link Profile}.
    * @param profile The {@link Profile} to check.
    * @return {@code true} predicate evaluation is enabled, {@code false} predicate evaluation is disabled.
    */
   public static boolean isTruthValueEvaluationEnabled(Profile profile) {
      if (profile instanceof SymbolicExecutionJavaProfile) {
         return ((SymbolicExecutionJavaProfile) profile).isPredicateEvaluationEnabled();
      }
      else {
         return false;
      }
   }
}