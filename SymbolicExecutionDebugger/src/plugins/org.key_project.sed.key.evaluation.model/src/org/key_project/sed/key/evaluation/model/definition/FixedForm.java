package org.key_project.sed.key.evaluation.model.definition;

import java.util.List;

import org.key_project.sed.key.evaluation.model.random.IRandomCompletion;

public class FixedForm extends AbstractForm {
   public FixedForm(String name, boolean collectTimes, AbstractPage... pages) {
      super(name, collectTimes, pages);
   }

   public FixedForm(String name, boolean collectTimes, List<AbstractPage> pages) {
      super(name, collectTimes, pages);
   }

   public FixedForm(String name, boolean collectTimes, IRandomCompletion randomOrderComputer, AbstractPage... pages) {
      super(name, collectTimes, randomOrderComputer, pages);
   }

   public FixedForm(String name, boolean collectTimes, IRandomCompletion randomOrderComputer, List<AbstractPage> pages) {
      super(name, collectTimes, randomOrderComputer, pages);
   }
}
