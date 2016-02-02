package org.key_project.sed.key.evaluation.model.definition;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.ObjectUtil;

public class TabbedQuestion extends AbstractQuestion implements IQuestionWithCildren {
   private final List<TabQuestion> childQuestions;

   public TabbedQuestion(String name, TabQuestion... childQuestions) {
      this(name, CollectionUtil.toList(childQuestions));
   }

   public TabbedQuestion(String name, List<TabQuestion> childQuestions) {
      super(name, null, null, null, null, false);
      this.childQuestions = childQuestions;
      validateChildren();
   }
   
   protected void validateChildren() {
      // Ensure that all children have different names
      Set<String> usedNames = new HashSet<String>();
      if (childQuestions != null) {
         for (AbstractQuestion childQuestion : childQuestions) {
            if (!usedNames.add(childQuestion.getName())) {
               throw new IllegalStateException("Chlild question name '" + childQuestion.getName() + "' used multiple times.");
            }
         }
      }
   }

   @Override
   public TabQuestion[] getChildQuestions() {
      return childQuestions.toArray(new TabQuestion[childQuestions.size()]);
   }
   
   @Override
   public int countChildQuestions() {
      return childQuestions.size();
   }

   @Override
   public TabQuestion getChildQuestion(final String name) {
      return CollectionUtil.search(childQuestions, new IFilter<TabQuestion>() {
         @Override
         public boolean select(TabQuestion element) {
            return ObjectUtil.equals(element.getName(), name);
         }
      });
   }

   @Override
   public boolean isEditable() {
      return false;
   }

}
