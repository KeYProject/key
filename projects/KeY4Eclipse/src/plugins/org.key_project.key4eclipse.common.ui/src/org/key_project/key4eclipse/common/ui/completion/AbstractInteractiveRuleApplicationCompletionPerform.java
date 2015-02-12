package org.key_project.key4eclipse.common.ui.completion;

import org.key_project.util.bean.Bean;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;

/**
 * Provides a basic implementation of {@link IInteractiveRuleApplicationCompletionPerform}.
 * @author Martin Hentschel
 */
public abstract class AbstractInteractiveRuleApplicationCompletionPerform extends Bean implements IInteractiveRuleApplicationCompletionPerform {
   /**
    * The DefaultBuiltInRuleApp to be completed.
    */
   private final IBuiltInRuleApp app;

   /**
    * The Goal where the app will later be applied to.
    */
   private final Goal goal;

   /**
    * A boolean indicating if the rule should be applied without any additional interaction from the user provided that the application object can be made complete automatically.
    */
   private final boolean forced;

   /**
    * The current error message.
    */
   private String errorMessage;

   /**
    * Constructor.
    * @param app The DefaultBuiltInRuleApp to be completed.
    * @param goal The Goal where the app will later be applied to.
    * @param forced A boolean indicating if the rule should be applied without any additional interaction from the user provided that the application object can be made complete automatically.
    */
   public AbstractInteractiveRuleApplicationCompletionPerform(IBuiltInRuleApp app, Goal goal, boolean forced) {
      this.app = app;
      this.goal = goal;
      this.forced = forced;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getErrorMessage() {
      return errorMessage;
   }

   /**
    * Sets the current error message.
    * @param errorMessage The error message to set or {@code null} if everything is valid.
    */
   public void setErrorMessage(String errorMessage) {
      String oldValue = getErrorMessage();
      this.errorMessage = errorMessage;
      firePropertyChange(PROP_ERROR_MESSAGE, oldValue, getErrorMessage());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getDescription() {
      return "Define instantiations required to apply the rule.";
   }

   /**
    * Returns the DefaultBuiltInRuleApp to be completed.
    * @return The DefaultBuiltInRuleApp to be completed.
    */
   public IBuiltInRuleApp getApp() {
      return app;
   }

   /**
    * Returns the Goal where the app will later be applied to.
    * @return The Goal where the app will later be applied to.
    */
   public Goal getGoal() {
      return goal;
   }

   /**
    * Returns the boolean indicating if the rule should be applied without any additional interaction from the user provided that the application object can be made complete automatically.
    * @return A boolean indicating if the rule should be applied without any additional interaction from the user provided that the application object can be made complete automatically.
    */
   public boolean isForced() {
      return forced;
   }
   
   /**
    * Returns the {@link Proof} of {@link #getGoal()}.
    * @return The {@link Proof} of {@link #getGoal()}.
    */
   public Proof getProof() {
      return goal.proof();
   }
   
   /**
    * Returns the {@link Services} of {@link #getProof()}.
    * @return The {@link Services} of {@link #getProof()}.
    */
   public Services getServices() {
      return getProof().getServices();
   }
}
