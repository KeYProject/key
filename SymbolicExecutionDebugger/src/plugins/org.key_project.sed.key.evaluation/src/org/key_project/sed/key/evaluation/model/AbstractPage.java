package org.key_project.sed.key.evaluation.model;


public abstract class AbstractPage {
   private final String name;
   
   private final String title;
   
   private final String message;
   
   public AbstractPage(String name, String title, String message) {
      assert name != null;
      this.name = name;
      this.title = title;
      this.message = message;
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
}
