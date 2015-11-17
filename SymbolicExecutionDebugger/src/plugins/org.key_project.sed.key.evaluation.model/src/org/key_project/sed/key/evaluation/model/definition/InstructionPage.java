package org.key_project.sed.key.evaluation.model.definition;

import java.net.URL;

import org.eclipse.swt.graphics.Image;

public class InstructionPage extends AbstractPage {
   private final URL descriptionURL;
   
   private final Image image;
   
   public InstructionPage(String name, String title, String message, URL descriptionURL, Image image) {
      super(name, title, message, false, false, true);
      this.descriptionURL = descriptionURL;
      this.image = image;
   }

   public URL getDescriptionURL() {
      return descriptionURL;
   }

   public Image getImage() {
      return image;
   }

   public boolean isReadonly() {
      return true;
   }
}
