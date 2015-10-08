package org.key_project.sed.key.evaluation.model.definition;


public abstract class AbstractPage {
   private final String name;
   
   private final String title;
   
   private final String message;
   
   private AbstractForm form;
   
   private final boolean wrapLayout;
   
   private final boolean toolBased;
   
   private final boolean enabled;
   
   public AbstractPage(String name, String title, String message, boolean wrapLayout, boolean toolBased, boolean enabled) {
      assert name != null;
      this.name = name;
      this.title = title;
      this.message = message;
      this.wrapLayout = wrapLayout;
      this.toolBased = toolBased;
      this.enabled = enabled;
   }

   public boolean isToolBased() {
      return toolBased;
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

   public boolean isWrapLayout() {
      return wrapLayout;
   }

   public boolean isEnabled() {
      return enabled;
   }

   public void setForm(AbstractForm form) {
      assert this.form == null : "Form is already set.";
      this.form = form;
   }
}
