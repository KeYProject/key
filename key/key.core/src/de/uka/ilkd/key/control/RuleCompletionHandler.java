package de.uka.ilkd.key.control;

import de.uka.ilkd.key.control.instantiation_model.TacletInstantiationModel;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.Rule;

/**
 * Instances of this class are used by an {@link AbstractProofControl} to complete a {@link Rule} completion.
 * @author Martin Hentschel
 */
public interface RuleCompletionHandler {
   /**
    * called to complete and apply a taclet instantiations
    * @param models the partial models with all different possible instantiations found automatically
    * @param goal the Goal where to apply
    */
   public void completeAndApplyTacletMatch(TacletInstantiationModel[] models, Goal goal);

   /**
    * completes rule applications of built in rules
    * @param app the DefaultBuiltInRuleApp to be completed
    * @param goal the Goal where the app will later be applied to
    * @param forced a boolean indicating if the rule should be applied without any 
    * additional interaction from the user provided that the application object can be 
    * made complete automatically
    * @return a complete app or null if no completion was possible
    */
   public IBuiltInRuleApp completeBuiltInRuleApp(IBuiltInRuleApp app, Goal goal, boolean forced);
}