package org.key_project.sed.key.evaluation.model.definition;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.key_project.util.java.CollectionUtil;

public class SectionQuestion extends AbstractQuestion {
   private final List<AbstractQuestion> childQuestions;

   public SectionQuestion(String name, String label, AbstractQuestion... childQuestions) {
      this(name, label, CollectionUtil.toList(childQuestions));
   }

   public SectionQuestion(String name, String label, List<AbstractQuestion> childQuestions) {
      super(name, label, null, null, false);
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

   public AbstractQuestion[] getChildQuestions() {
      return childQuestions.toArray(new AbstractQuestion[childQuestions.size()]);
   }
   
   public int countChildQuestions() {
      return childQuestions.size();
   }

   @Override
   public boolean isEditable() {
      return false;
   }
}
