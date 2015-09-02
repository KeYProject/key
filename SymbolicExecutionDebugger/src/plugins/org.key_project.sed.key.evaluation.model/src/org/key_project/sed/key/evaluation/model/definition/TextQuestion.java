package org.key_project.sed.key.evaluation.model.definition;

import org.key_project.sed.key.evaluation.model.validation.IValueValidator;

public class TextQuestion extends AbstractQuestion {
   private final int widthHint;
   
   private final int heightHint;
   
   public TextQuestion(String name, String label, String defaultValue, IValueValidator validator, boolean askForTrust, int widthHint, int heightHint) {
      super(name, label, null, defaultValue, validator, askForTrust);
      this.widthHint = widthHint;
      this.heightHint = heightHint;
   }

   public TextQuestion(String name, String label, String description, String defaultValue, IValueValidator validator, boolean askForTrust, int widthHint, int heightHint) {
      super(name, label, description, defaultValue, validator, askForTrust);
      this.widthHint = widthHint;
      this.heightHint = heightHint;
   }

   public TextQuestion(String name, String label, String description, String defaultValue, IValueValidator validator, boolean askForTrust, Tool[] relatedTools, int widthHint, int heightHint) {
      super(name, label, description, defaultValue, validator, askForTrust, relatedTools);
      this.widthHint = widthHint;
      this.heightHint = heightHint;
   }

   public int getWidthHint() {
      return widthHint;
   }

   public int getHeightHint() {
      return heightHint;
   }
}
