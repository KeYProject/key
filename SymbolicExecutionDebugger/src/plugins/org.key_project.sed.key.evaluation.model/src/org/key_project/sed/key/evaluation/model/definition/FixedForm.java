package org.key_project.sed.key.evaluation.model.definition;

import java.util.List;

public class FixedForm extends AbstractForm {
   public FixedForm(String name, boolean collectTimes, AbstractPage... pages) {
      super(name, collectTimes, pages);
   }

   public FixedForm(String name, boolean collectTimes, List<AbstractPage> pages) {
      super(name, collectTimes, pages);
   }

   public FixedForm(String name, boolean collectTimes, String randomOrderComputerName, AbstractPage... pages) {
      super(name, collectTimes, randomOrderComputerName, pages);
   }

   public FixedForm(String name, boolean collectTimes, String randomOrderComputerName, List<AbstractPage> pages) {
      super(name, collectTimes, randomOrderComputerName, pages);
   }
}
