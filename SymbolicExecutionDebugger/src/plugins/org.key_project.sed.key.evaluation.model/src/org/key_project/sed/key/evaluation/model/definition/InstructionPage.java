package org.key_project.sed.key.evaluation.model.definition;

import java.net.URL;

public class InstructionPage extends AbstractPage {
   private final URL descriptionURL;
   
   public InstructionPage(String name, String title, String message, URL descriptionURL) {
      super(name, title, message);
      this.descriptionURL = descriptionURL;
   }

   public URL getDescriptionURL() {
      return descriptionURL;
   }

   public boolean isReadonly() {
      return true;
   }
}
