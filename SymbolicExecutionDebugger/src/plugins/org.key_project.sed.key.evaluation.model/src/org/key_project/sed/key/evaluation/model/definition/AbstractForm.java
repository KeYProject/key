package org.key_project.sed.key.evaluation.model.definition;

import java.util.List;

import org.key_project.sed.key.evaluation.model.random.IRandomCompletion;
import org.key_project.util.java.CollectionUtil;

public abstract class AbstractForm {
   private final String name;
   
   private final List<AbstractPage> pages;
   
   private final IRandomCompletion randomOrderComputer;
   
   private AbstractEvaluation evaluation;

   public AbstractForm(String name, AbstractPage... pages) {
      this(name, null, CollectionUtil.toList(pages));
   }

   public AbstractForm(String name, List<AbstractPage> pages) {
      this(name, null, pages);
   }

   public AbstractForm(String name, IRandomCompletion randomOrderComputer, AbstractPage... pages) {
      this(name, randomOrderComputer, CollectionUtil.toList(pages));
   }

   public AbstractForm(String name, IRandomCompletion randomOrderComputer, List<AbstractPage> pages) {
      this.name = name;
      this.randomOrderComputer = randomOrderComputer;
      this.pages = pages;
      for (AbstractPage page : pages) {
         page.setForm(this);
      }
   }

   public String getName() {
      return name;
   }

   public AbstractPage[] getPages() {
      return pages.toArray(new AbstractPage[pages.size()]);
   }

   public int countPages() {
      return pages.size();
   }

   public AbstractEvaluation getEvaluation() {
      return evaluation;
   }

   public void setEvaluation(AbstractEvaluation evaluation) {
      assert this.evaluation == null : "Evaluation is already defined.";
      this.evaluation = evaluation;
   }

   public IRandomCompletion getRandomOrderComputer() {
      return randomOrderComputer;
   }
}
