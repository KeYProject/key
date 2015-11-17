package org.key_project.sed.key.evaluation.model.input;

import java.util.ArrayList;
import java.util.List;

import org.key_project.sed.key.evaluation.model.definition.AbstractForm;
import org.key_project.sed.key.evaluation.model.definition.AbstractPage;
import org.key_project.sed.key.evaluation.model.definition.InstructionPage;
import org.key_project.sed.key.evaluation.model.definition.QuestionPage;
import org.key_project.sed.key.evaluation.model.definition.SendFormPage;
import org.key_project.sed.key.evaluation.model.definition.ToolPage;
import org.key_project.util.bean.Bean;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.ObjectUtil;

public abstract class AbstractFormInput<F extends AbstractForm> extends Bean {
   public static final String PROP_CURRENT_PAGE_INPUT = "currentPageInput";
   
   private final EvaluationInput evaluationInput;

   private final F form;
   
   private final List<AbstractPageInput<?>> pageInputs;
   
   private AbstractPageInput<?> currentPageInput;

   public AbstractFormInput(EvaluationInput evaluationInput, F form) {
      assert evaluationInput != null;
      assert form != null;
      this.evaluationInput = evaluationInput;
      this.form = form;
      this.pageInputs = new ArrayList<AbstractPageInput<?>>(form.countPages());
      for (AbstractPage page : form.getPages()) {
         if (page instanceof QuestionPage) {
            this.pageInputs.add(new QuestionPageInput(this, (QuestionPage) page));
         }
         else if (page instanceof SendFormPage) {
            this.pageInputs.add(new SendFormPageInput(this, (SendFormPage) page));
         }
         else if (page instanceof ToolPage) {
            this.pageInputs.add(new ToolPageInput(this, (ToolPage) page));
         }
         else if (page instanceof InstructionPage) {
            this.pageInputs.add(new InstructionPageInput(this, (InstructionPage) page));
         }
         else {
            throw new IllegalStateException("Unsupported page: " + page);
         }
      }
      if (!pageInputs.isEmpty()) {
         currentPageInput = pageInputs.get(0);
      }
   }

   public F getForm() {
      return form;
   }

   public AbstractPageInput<?>[] getPageInputs() {
      return pageInputs.toArray(new AbstractPageInput[pageInputs.size()]);
   }

   public AbstractPageInput<?> getCurrentPageInput() {
      return currentPageInput;
   }

   public void setCurrentPageInput(AbstractPageInput<?> currentPageInput) {
      AbstractPageInput<?> oldValue = getCurrentPageInput();
      this.currentPageInput = currentPageInput;
      firePropertyChange(PROP_CURRENT_PAGE_INPUT, oldValue, getCurrentPageInput());
   }

   public AbstractPageInput<?> getPageInput(final String pageName) {
      return CollectionUtil.search(pageInputs, new IFilter<AbstractPageInput<?>>() {
         @Override
         public boolean select(AbstractPageInput<?> element) {
            return ObjectUtil.equals(pageName, element.getPage().getName());
         }
      });
   }

   public AbstractPageInput<?> getPageInput(final AbstractPage page) {
      return CollectionUtil.search(pageInputs, new IFilter<AbstractPageInput<?>>() {
         @Override
         public boolean select(AbstractPageInput<?> element) {
            return ObjectUtil.equals(page, element.getPage());
         }
      });
   }

   public AbstractPageInput<?> getPageInput(int index) {
      return pageInputs.get(index);
   }

   public EvaluationInput getEvaluationInput() {
      return evaluationInput;
   }

   public int countPageInputs() {
      return pageInputs.size();
   }

   public void reset() {
      if (!pageInputs.isEmpty()) {
         setCurrentPageInput(pageInputs.get(0));
      }
      else {
         setCurrentPageInput(null);
      }
      for (AbstractPageInput<?> pageInput : pageInputs) {
         pageInput.reset();
      }
   }
   
   /**
    * Searches the first available {@link SendFormPageInput}.
    * @return The first available {@link SendFormPageInput} or {@code null} if not available.
    */
   public SendFormPageInput searchSendFormPageInput() {
      return (SendFormPageInput) CollectionUtil.search(pageInputs, new IFilter<AbstractPageInput<?>>() {
         @Override
         public boolean select(AbstractPageInput<?> element) {
            return element.getPage() instanceof SendFormPage;
         }
      });
   }
}
