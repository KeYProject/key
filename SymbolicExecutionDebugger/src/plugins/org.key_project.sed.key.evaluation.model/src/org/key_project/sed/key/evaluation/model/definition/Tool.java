package org.key_project.sed.key.evaluation.model.definition;

import java.net.URL;

import org.eclipse.swt.graphics.Image;

public class Tool {
   private final String name;
   
   private final URL descriptionURL;
   
   private final Image image;

   public Tool(String name, URL descriptionURL, Image image) {
      this.name = name;
      this.descriptionURL = descriptionURL;
      this.image = image;
   }

   public String getName() {
      return name;
   }

   public URL getDescriptionURL() {
      return descriptionURL;
   }

   public Image getImage() {
      return image;
   }
}
