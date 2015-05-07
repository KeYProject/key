package org.key_project.sed.key.evaluation.model.definition;


public abstract class AbstractPage {
   private final String name;
   
   private final String title;
   
   private final String message;
   
   private AbstractForm form;
   
   public AbstractPage(String name, String title, String message) {
      assert name != null;
      this.name = name;
      this.title = title;
      this.message = message;
   }
   
   public boolean isReadonly() {
      return false;
   }

   public String getName() {
      return name;
   }

   public String getTitle() {
      return title;
   }

   public String getMessage() {
      return message;
   }

   public AbstractForm getForm() {
      return form;
   }

   public void setForm(AbstractForm form) {
      assert this.form == null : "Form is already set.";
      this.form = form;
   }
}
