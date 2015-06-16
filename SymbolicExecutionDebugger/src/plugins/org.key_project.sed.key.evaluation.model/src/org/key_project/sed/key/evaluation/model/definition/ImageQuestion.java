package org.key_project.sed.key.evaluation.model.definition;

import org.eclipse.swt.graphics.ImageData;

public class ImageQuestion extends AbstractQuestion {
   private final ImageData imageData;

   public ImageQuestion(String name, ImageData imageData) {
      super(name);
      this.imageData = imageData;
   }

   public ImageData getImageData() {
      return imageData;
   }

   @Override
   public boolean isEditable() {
      return false;
   }
}
