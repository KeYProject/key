package org.key_project.sed.key.evaluation.wizard.manager;

public abstract class AbstractQuestionInputManager implements IQuestionInputManager {
   private boolean enabled = true;
   
   @Override
   public boolean isEnabled() {
      return enabled;
   }

   @Override
   public void setEnabled(boolean enabled) {
      if (this.enabled != enabled) {
         this.enabled = enabled;
         enableControls(enabled);
      }
   }

   protected abstract void enableControls(boolean enabled);
}
