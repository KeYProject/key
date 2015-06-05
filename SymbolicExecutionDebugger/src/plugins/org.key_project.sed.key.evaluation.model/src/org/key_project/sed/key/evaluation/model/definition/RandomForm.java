package org.key_project.sed.key.evaluation.model.definition;

import java.util.List;

public class RandomForm extends AbstractForm {
   public RandomForm(String name, boolean collectTimes, AbstractPage... pages) {
      super(name, collectTimes, pages);
   }

   public RandomForm(String name, boolean collectTimes, List<AbstractPage> pages) {
      super(name, collectTimes, pages);
   }
}
