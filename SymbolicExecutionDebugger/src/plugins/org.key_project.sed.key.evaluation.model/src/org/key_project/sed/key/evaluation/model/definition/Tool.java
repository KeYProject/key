package org.key_project.sed.key.evaluation.model.definition;

import java.net.URL;

import org.eclipse.swt.graphics.Image;

public class Tool {
   private final String name;
   
   private final String latexName;
   
   private final URL descriptionURL;
   
   private final URL wizardDescriptionURL;
   
   private final Image image;

   public Tool(String name, URL descriptionURL, URL wizardDescriptionURL, Image image) {
      this(name, name, descriptionURL, wizardDescriptionURL, image);
   }

   public Tool(String name, String latexName, URL descriptionURL, URL wizardDescriptionURL, Image image) {
      this.name = name;
      this.latexName = latexName;
      this.descriptionURL = descriptionURL;
      this.wizardDescriptionURL = wizardDescriptionURL;
      this.image = image;
   }

   public String getName() {
      return name;
   }

   public String getLatexName() {
      return latexName;
   }

   public URL getDescriptionURL() {
      return descriptionURL;
   }

   public URL getWizardDescriptionURL() {
      return wizardDescriptionURL;
   }

   public Image getImage() {
      return image;
   }
}
