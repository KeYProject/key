package org.key_project.sed.key.evaluation.model.definition;

import java.util.List;

import org.eclipse.swt.graphics.Image;
import org.key_project.sed.key.evaluation.model.validation.IValueValidator;
import org.key_project.util.java.CollectionUtil;

public abstract class AbstractButtonsQuestion extends AbstractChoicesQuestion {
   private final boolean vertical;
   
   private final Image image;

   public AbstractButtonsQuestion(String name, String label, Image image, boolean vertical, String defaultChoice, IValueValidator validator, boolean askForTrust, Choice... choices) {
      this(name, label, image, vertical, defaultChoice, validator, askForTrust, CollectionUtil.toList(choices));
   }

   public AbstractButtonsQuestion(String name, String label, Image image, boolean vertical, String defaultChoice, IValueValidator validator, boolean askForTrust, List<Choice> choices) {
      super(name, label, defaultChoice, validator, askForTrust, choices);
      this.image = image;
      this.vertical = vertical;
   }

   public Image getImage() {
      return image;
   }

   public boolean isVertical() {
      return vertical;
   }
}
