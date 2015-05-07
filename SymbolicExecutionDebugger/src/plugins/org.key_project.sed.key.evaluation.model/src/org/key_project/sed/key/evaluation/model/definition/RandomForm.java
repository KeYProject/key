package org.key_project.sed.key.evaluation.model.definition;

import java.util.List;

public class RandomForm extends AbstractForm {
   public RandomForm(String name, AbstractPage... pages) {
      super(name, pages);
   }

   public RandomForm(String name, List<AbstractPage> pages) {
      super(name, pages);
   }
}
