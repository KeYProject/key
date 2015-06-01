package org.key_project.sed.key.evaluation.model.definition;

public class LabelQuestion extends AbstractQuestion {
   private final String text;

   public LabelQuestion(String name, String text) {
      super(name);
      this.text = text;
   }
   
   public String getText() {
      return text;
   }

   @Override
   public boolean isEditable() {
      return false;
   }
}
