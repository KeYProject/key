package org.key_project.sed.key.evaluation.model.definition;

import java.net.URL;

public class BrowserQuestion extends AbstractQuestion {
   private final URL url;

   public BrowserQuestion(String name, URL url) {
      super(name);
      this.url = url;
   }

   public URL getUrl() {
      return url;
   }
   
   @Override
   public boolean isEditable() {
      return false;
   }
}
