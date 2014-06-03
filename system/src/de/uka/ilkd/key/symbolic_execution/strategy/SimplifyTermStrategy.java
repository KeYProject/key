package de.uka.ilkd.key.symbolic_execution.strategy;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.rule.IfFormulaInstantiation;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.strategy.JavaCardDLStrategy;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyFactory;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.strategy.TopRuleAppCost;
import de.uka.ilkd.key.strategy.definition.StrategySettingsDefinition;
import de.uka.ilkd.key.strategy.feature.Feature;

/**
 * {@link Strategy} used to simplify {@link Term}s in side proofs.
 * @author Martin Hentschel
 */
public class SimplifyTermStrategy extends JavaCardDLStrategy {
   /**
    * The {@link Name} of the side proof {@link Strategy}.
    */
   public static final Name name = new Name("Simplify Term Strategy");
   
   /**
    * Constructor.
    * @param proof The proof.
    * @param sp The {@link StrategyProperties} to use.
    */
   private SimplifyTermStrategy(Proof proof, StrategyProperties sp) {
      super(proof, sp);
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
   protected Feature setupApprovalF() {
      Feature superFeature = super.setupApprovalF();
      Feature labelFeature = new Feature() {
         @Override
         public RuleAppCost compute(RuleApp app, PosInOccurrence pos, Goal goal) {
            boolean hasLabel = false;
            if (pos != null && app instanceof TacletApp) {
               Term findTerm = pos.subTerm();
               if (!findTerm.containsLabel(ParameterlessTermLabel.RESULT_LABEL)) {
                  // Term with result label is not used in find term and thus is not allowed to be used in an assumes clause
                  TacletApp ta = (TacletApp)app;
                  if (ta.ifFormulaInstantiations() != null) {
                     for (IfFormulaInstantiation ifi : ta.ifFormulaInstantiations()) {
                        if (ifi.getConstrainedFormula().formula().containsLabel(ParameterlessTermLabel.RESULT_LABEL)) {
                           hasLabel = true;
                        }
                     }
                  }
               }
            }
            return hasLabel ? TopRuleAppCost.INSTANCE : NumberRuleAppCost.create(0);
         }
      };
      // The label feature ensures that Taclets mapping an assumes to a Term with a result label are only applicable if also a Term with the result label is used in the find clause
      return add(labelFeature, superFeature);
   }

   /**
    * The {@link StrategyFactory} to create instances of {@link SimplifyTermStrategy}.
    * @author Martin Hentschel
    */
   public static class Factory implements StrategyFactory {
      /**
       * {@inheritDoc}
       */
      @Override
      public Strategy create(Proof proof, StrategyProperties sp) {
         return new SimplifyTermStrategy(proof, sp);
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
         return JavaProfile.DEFAULT.getSettingsDefinition();
      }
   }
}
