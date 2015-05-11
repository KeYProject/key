package org.key_project.sed.key.evaluation.model.definition;

import java.util.List;

import org.key_project.sed.key.evaluation.model.random.IRandomCompletion;

public class FixedForm extends AbstractForm {
   public FixedForm(String name, AbstractPage... pages) {
      super(name, pages);
   }

   public FixedForm(String name, List<AbstractPage> pages) {
      super(name, pages);
   }

   public FixedForm(String name, IRandomCompletion randomOrderComputer, AbstractPage... pages) {
      super(name, randomOrderComputer, pages);
   }

   public FixedForm(String name, IRandomCompletion randomOrderComputer, List<AbstractPage> pages) {
      super(name, randomOrderComputer, pages);
   }
}
