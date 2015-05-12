package org.key_project.sed.key.evaluation.model.definition;

import java.net.URL;

public class Tool {
   private final String name;
   
   private final URL descriptionURL;

   public Tool(String name, URL descriptionURL) {
      this.name = name;
      this.descriptionURL = descriptionURL;
   }

   public String getName() {
      return name;
   }

   public URL getDescriptionURL() {
      return descriptionURL;
   }
}
