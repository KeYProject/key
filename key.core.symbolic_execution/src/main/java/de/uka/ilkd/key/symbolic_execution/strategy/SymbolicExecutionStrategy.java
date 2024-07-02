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

package de.uka.ilkd.key.symbolic_execution.strategy;

import java.util.ArrayList;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.rulefilter.SetRuleFilter;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.JavaCardDLStrategy;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyFactory;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.strategy.definition.IDefaultStrategyPropertiesFactory;
import de.uka.ilkd.key.strategy.definition.OneOfStrategyPropertyDefinition;
import de.uka.ilkd.key.strategy.definition.StrategyPropertyValueDefinition;
import de.uka.ilkd.key.strategy.definition.StrategySettingsDefinition;
import de.uka.ilkd.key.strategy.feature.BinaryFeature;
import de.uka.ilkd.key.strategy.feature.ConditionalFeature;
import de.uka.ilkd.key.strategy.feature.CountBranchFeature;
import de.uka.ilkd.key.strategy.feature.Feature;
import de.uka.ilkd.key.strategy.feature.RuleSetDispatchFeature;
import de.uka.ilkd.key.strategy.feature.ScaleFeature;
import de.uka.ilkd.key.strategy.feature.instantiator.OneOfCP;
import de.uka.ilkd.key.strategy.termProjection.TermBuffer;
import de.uka.ilkd.key.strategy.termfeature.ContainsLabelFeature;
import de.uka.ilkd.key.symbolic_execution.rule.ModalitySideProofRule;
import de.uka.ilkd.key.symbolic_execution.rule.QuerySideProofRule;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.util.Triple;

/**
 * {@link Strategy} to use for symbolic execution.
 */
public class SymbolicExecutionStrategy extends JavaCardDLStrategy {
   /**
    * The {@link Name} of the symbolic execution {@link Strategy}.
    */
   public static final Name name = new Name("Symbolic Execution Strategy");
   
   /**
    * The default factory.
    */
   public static IDefaultStrategyPropertiesFactory DEFAULT_FACTORY = new IDefaultStrategyPropertiesFactory() {
      @Override
      public StrategyProperties createDefaultStrategyProperties() {
          return SymbolicExecutionStrategy.getSymbolicExecutionStrategyProperties(true, false, false, false, false, false);
      }
   };
   
   /**
    * Constructor.
    * @param proof The proof.
    * @param sp The {@link StrategyProperties} to use.
    */
   private SymbolicExecutionStrategy(Proof proof, StrategyProperties sp) {
      super(proof, sp);
      // Update cost dispatcher
      RuleSetDispatchFeature costRsd = getCostComputationDispatcher();

      clearRuleSetBindings (costRsd, "simplify_prog" );
      bindRuleSet (costRsd, "simplify_prog",10000);
      
      clearRuleSetBindings (costRsd, "simplify_prog_subset" );
      bindRuleSet (costRsd, "simplify_prog_subset",10000);
      
      Feature splitF = ScaleFeature.createScaled(CountBranchFeature.INSTANCE, -4000);
      bindRuleSet(costRsd, "split_if", splitF); // The costs of rules in heuristic "split_if" is reduced at runtime by numberOfBranches * -400. The result is that rules of "split_if" preferred to "split_cond" and run and step into has the same behavior
      bindRuleSet(costRsd, "instanceof_to_exists", inftyConst());
      
      // Update instantiation dispatcher
      if (StrategyProperties.SYMBOLIC_EXECUTION_ALIAS_CHECK_IMMEDIATELY.equals(sp.get(StrategyProperties.SYMBOLIC_EXECUTION_ALIAS_CHECK_OPTIONS_KEY))) {
         // Make sure that an immediately alias check is performed by doing cuts of objects to find out if they can be the same or not
         RuleSetDispatchFeature instRsd = getInstantiationDispatcher();
         enableInstantiate();
         final TermBuffer buffer = new TermBuffer();
         Feature originalCut = instRsd.get(getHeuristic("cut"));
         Feature newCut = forEach(buffer, new CutHeapObjectsTermGenerator(), add(instantiate ("cutFormula", buffer), longConst(-10000)));
         if (originalCut instanceof OneOfCP) {
            clearRuleSetBindings (instRsd, "cut" );
            bindRuleSet (instRsd, "cut", oneOf(originalCut, newCut));
         }
         else {
            bindRuleSet (instRsd, "cut", newCut);
         }
         disableInstantiate();
      }
      // TODO: For delayed similar to sequentContainsNoPrograms()
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected Feature setupApprovalF() {
      Feature result = super.setupApprovalF();
      // Make sure that cuts are only applied if the cut term is not already part of the sequent. This check is performed exactly before the rule is applied because the sequent might has changed in the time after the schema variable instantiation was instantiated.
      SetRuleFilter depFilter = new SetRuleFilter();
      depFilter.addRuleToSet(getProof().getInitConfig().lookupActiveTaclet(new Name("cut")));
      result = add(result, ConditionalFeature.createConditional(depFilter, new CutHeapObjectsFeature()));
      return result;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected Feature setupGlobalF(Feature dispatcher) {
       Feature globalF = super.setupGlobalF(dispatcher);
       // Make sure that modalities without symbolic execution label are executed first because they might forbid rule application on modalities with symbolic execution label (see loop body branches)
       globalF = add(globalF, ifZero(not(new BinaryFeature() {
          @Override
          protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal) {
             return pos != null && SymbolicExecutionUtil.hasSymbolicExecutionLabel(pos.subTerm());
          }
       }), longConst(-3000)));
       // Make sure that the modality which executes a loop body is preferred against the modalities which executes special loop terminations like return, exceptions or break.
       globalF = add(globalF, ifZero(new ContainsLabelFeature(SymbolicExecutionUtil.LOOP_BODY_LABEL), longConst(-2000)));
       globalF = add(globalF, querySideProofFeature());       
       globalF = add(globalF, modalitySideProofFeature());       
       return globalF;
   }
   
   /**
    * Computes the cost {@link Feature} for the {@link ModalitySideProofRule}.
    * @return The cost {@link Feature} for the {@link ModalitySideProofRule}.
    */
   protected Feature modalitySideProofFeature() {
      SetRuleFilter filter = new SetRuleFilter();
      filter.addRuleToSet(ModalitySideProofRule.INSTANCE);
      if (StrategyProperties.SYMBOLIC_EXECUTION_NON_EXECUTION_BRANCH_HIDING_SIDE_PROOF.equals(strategyProperties.get(StrategyProperties.SYMBOLIC_EXECUTION_NON_EXECUTION_BRANCH_HIDING_OPTIONS_KEY))) {
         return ConditionalFeature.createConditional(filter, longConst(-3050));
      }
      else {
         return ConditionalFeature.createConditional(filter, inftyConst());
      }
   }
   
   /**
    * Computes the cost {@link Feature} for the {@link QuerySideProofRule}.
    * @return The cost {@link Feature} for the {@link QuerySideProofRule}.
    */
   protected Feature querySideProofFeature() {
      SetRuleFilter filter = new SetRuleFilter();
      filter.addRuleToSet(QuerySideProofRule.INSTANCE);
      if (StrategyProperties.SYMBOLIC_EXECUTION_NON_EXECUTION_BRANCH_HIDING_SIDE_PROOF.equals(strategyProperties.get(StrategyProperties.SYMBOLIC_EXECUTION_NON_EXECUTION_BRANCH_HIDING_OPTIONS_KEY))) {
         return ConditionalFeature.createConditional(filter, longConst(-3050)); // Rule must be preferred to rules with heuristic "query_axiom" and rule QueryExpand
      }
      else {
         return ConditionalFeature.createConditional(filter, inftyConst());
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Name name() {
      return name;
   }
   
   /**
    * Returns the default {@link StrategyProperties} of symbolic execution. 
    * @param quantifierInstantiationWithSplitting Instantiate quantifiers?
    * @param methodTreatmentContract Use method contracts or inline method bodies otherwise?
    * @param loopTreatmentInvariant Use loop invariants or unrole loops otherwise?
    * @param blockTreatmentContract Block contracts or expand otherwise?
    * @param nonExecutionBranchHidingSideProofs {@code true} hide non execution branch labels by side proofs, {@code false} do not hide execution branch labels. 
    * @param aliasChecks Do alias checks?
    * @return The default {@link StrategyProperties} for symbolic execution.
    */
   public static StrategyProperties getSymbolicExecutionStrategyProperties(boolean quantifierInstantiationWithSplitting,
                                                                           boolean methodTreatmentContract, 
                                                                           boolean loopTreatmentInvariant,
                                                                           boolean blockTreatmentContract,
                                                                           boolean nonExecutionBranchHidingSideProofs,
                                                                           boolean aliasChecks) {
      StrategyProperties sp = new StrategyProperties();
      StrategyProperties.setDefaultStrategyProperties(sp, 
                                                      quantifierInstantiationWithSplitting, 
                                                      methodTreatmentContract, 
                                                      loopTreatmentInvariant, 
                                                      blockTreatmentContract,
                                                      nonExecutionBranchHidingSideProofs, 
                                                      aliasChecks);
      return sp;
   }

   /**
    * The {@link StrategyFactory} to create instances of {@link SymbolicExecutionStrategy}.
    * @author Martin Hentschel
    */
   public static class Factory implements StrategyFactory {
      /**
       * Shown string for method treatment "Expand".
       */
      public static final String METHOD_TREATMENT_EXPAND = "Inline Methods";

      /**
       * Shown string for method treatment "Contract".
       */
      public static final String METHOD_TREATMENT_CONTRACT = "Use Contracts";

      /**
       * Shown string for loop treatment "Expand".
       */
      public static final String LOOP_TREATMENT_EXPAND = "Unroll Loops";

      /**
       * Shown string for loop treatment "Invariant".
       */
      public static final String LOOP_TREATMENT_INVARIANT = "Use Loop Invariants";

      /**
       * Shown string for block treatment "Expand".
       */
      public static final String BLOCK_TREATMENT_EXPAND = "Expand Blocks";

      /**
       * Shown string for block treatment "Invariant".
       */
      public static final String BLOCK_TREATMENT_INVARIANT = "Use Contracts";

      /**
       * Shown string for alias check "Never".
       */
      public static final String NON_EXECUTION_BRANCH_HIDING_OFF = "Off";

      /**
       * Shown string for alias check "Immediately".
       */
      public static final String NON_EXECUTION_BRANCH_HIDING_SIDE_PROOF = "On";

      /**
       * Shown string for alias check "Never".
       */
      public static final String ALIAS_CHECK_NEVER = "Never";

      /**
       * Shown string for alias check "Immediately".
       */
      public static final String ALIAS_CHECK_IMMEDIATELY = "Immediately";
      
      /**
       * {@inheritDoc}
       */
      @Override
      public Strategy create(Proof proof, StrategyProperties sp) {
         return new SymbolicExecutionStrategy(proof, sp);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Name name() {
         return name;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public StrategySettingsDefinition getSettingsDefinition() {
         // Properties
         OneOfStrategyPropertyDefinition methodTreatment = new OneOfStrategyPropertyDefinition(StrategyProperties.METHOD_OPTIONS_KEY,
               "Method Treatment",
               new StrategyPropertyValueDefinition(StrategyProperties.METHOD_EXPAND, METHOD_TREATMENT_EXPAND, null),
               new StrategyPropertyValueDefinition(StrategyProperties.METHOD_CONTRACT, METHOD_TREATMENT_CONTRACT, null));
         OneOfStrategyPropertyDefinition loopTreatment = new OneOfStrategyPropertyDefinition(StrategyProperties.LOOP_OPTIONS_KEY,
               "Loop Treatment",
               new StrategyPropertyValueDefinition(StrategyProperties.LOOP_EXPAND, LOOP_TREATMENT_EXPAND, null),
               new StrategyPropertyValueDefinition(StrategyProperties.LOOP_INVARIANT, LOOP_TREATMENT_INVARIANT, null));
         OneOfStrategyPropertyDefinition blockTreatment = new OneOfStrategyPropertyDefinition(StrategyProperties.BLOCK_OPTIONS_KEY,
               "Block Treatment",
               new StrategyPropertyValueDefinition(StrategyProperties.BLOCK_EXPAND, BLOCK_TREATMENT_EXPAND, null),
               new StrategyPropertyValueDefinition(StrategyProperties.BLOCK_CONTRACT_INTERNAL, BLOCK_TREATMENT_INVARIANT, null));
         OneOfStrategyPropertyDefinition branchHiding = new OneOfStrategyPropertyDefinition(StrategyProperties.SYMBOLIC_EXECUTION_NON_EXECUTION_BRANCH_HIDING_OPTIONS_KEY,
               "Non Execution Branch Hiding",
               new StrategyPropertyValueDefinition(StrategyProperties.SYMBOLIC_EXECUTION_NON_EXECUTION_BRANCH_HIDING_OFF, NON_EXECUTION_BRANCH_HIDING_OFF, null),
               new StrategyPropertyValueDefinition(StrategyProperties.SYMBOLIC_EXECUTION_NON_EXECUTION_BRANCH_HIDING_SIDE_PROOF, NON_EXECUTION_BRANCH_HIDING_SIDE_PROOF, null));
         OneOfStrategyPropertyDefinition aliasChecks = new OneOfStrategyPropertyDefinition(StrategyProperties.SYMBOLIC_EXECUTION_ALIAS_CHECK_OPTIONS_KEY,
               "Alias Checks",
               new StrategyPropertyValueDefinition(StrategyProperties.SYMBOLIC_EXECUTION_ALIAS_CHECK_NEVER, ALIAS_CHECK_NEVER, null),
               new StrategyPropertyValueDefinition(StrategyProperties.SYMBOLIC_EXECUTION_ALIAS_CHECK_IMMEDIATELY, ALIAS_CHECK_IMMEDIATELY, null));
         // Model
         return new StrategySettingsDefinition(false, 
                                               null, 
                                               1000,
                                               "Symbolic Execution Options",
                                               SymbolicExecutionStrategy.DEFAULT_FACTORY,
                                               new ArrayList<Triple<String,Integer,IDefaultStrategyPropertiesFactory>>(),
                                               methodTreatment,
                                               loopTreatment,
                                               blockTreatment,
                                               branchHiding,
                                               aliasChecks);
      }
   }
}