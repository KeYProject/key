package org.key_project.sed.key.evaluation.model.definition;

import java.util.List;

import org.key_project.sed.key.evaluation.model.random.IRandomCompletion;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.ObjectUtil;

public abstract class AbstractForm {
   private final String name;
   
   private final List<AbstractPage> pages;
   
   private final IRandomCompletion randomOrderComputer;
   
   private final boolean collectTimes;
   
   private AbstractEvaluation evaluation;

   public AbstractForm(String name, boolean collectTimes, AbstractPage... pages) {
      this(name, collectTimes, null, CollectionUtil.toList(pages));
   }

   public AbstractForm(String name, boolean collectTimes, List<AbstractPage> pages) {
      this(name, collectTimes, null, pages);
   }

   public AbstractForm(String name, boolean collectTimes, IRandomCompletion randomOrderComputer, AbstractPage... pages) {
      this(name, collectTimes, randomOrderComputer, CollectionUtil.toList(pages));
   }

   public AbstractForm(String name, boolean collectTimes, IRandomCompletion randomOrderComputer, List<AbstractPage> pages) {
      this.name = name;
      this.collectTimes = collectTimes;
      this.randomOrderComputer = randomOrderComputer;
      this.pages = pages;
      for (AbstractPage page : pages) {
         page.setForm(this);
      }
   }

   public String getName() {
      return name;
   }

   public boolean isCollectTimes() {
      return collectTimes;
   }

   public AbstractPage[] getPages() {
      return pages.toArray(new AbstractPage[pages.size()]);
   }

   public AbstractPage getPage(final String pageName) {
      return CollectionUtil.search(pages, new IFilter<AbstractPage>() {
         @Override
         public boolean select(AbstractPage element) {
            return ObjectUtil.equals(pageName, element.getName());
         }
      });
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
