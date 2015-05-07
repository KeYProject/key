package org.key_project.sed.key.evaluation.model.definition;

import java.util.List;

import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.ObjectUtil;

public abstract class AbstractEvaluation {
   private final String name;
   
   private final List<AbstractForm> forms;

   public AbstractEvaluation(String name) {
      this.name = name;
      this.forms = (List<AbstractForm>)computeForms();
      for (AbstractForm form : forms) {
         form.setEvaluation(this);
      }
   }

   protected abstract List<AbstractForm> computeForms();

   public String getName() {
      return name;
   }
   
   public AbstractForm[] getForms() {
      return forms.toArray(new AbstractForm[forms.size()]);
   }

   public int countForms() {
      return forms.size();
   }
   
   public static AbstractEvaluation getEvaluationForName(String name) {
      if (UnderstandingProofAttemptsEvaluation.INSTANCE.getName().equals(name)) {
         return UnderstandingProofAttemptsEvaluation.INSTANCE;
      }
      else if (TestEvaluation.INSTANCE.getName().equals(name)) {
         return TestEvaluation.INSTANCE;
      }
      else {
         return null;
      }
   }

   public AbstractForm getForm(final String formName) {
      return CollectionUtil.search(forms, new IFilter<AbstractForm>() {
         @Override
         public boolean select(AbstractForm element) {
            return ObjectUtil.equals(formName, element.getName());
         }
      });
   }
}
