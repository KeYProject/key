package org.key_project.sed.key.evaluation.model_input;

import java.util.ArrayList;
import java.util.List;

import org.key_project.sed.key.evaluation.model.AbstractEvaluation;
import org.key_project.sed.key.evaluation.model.Form;
import org.key_project.util.bean.Bean;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;

public class EvaluationInput extends Bean {
   public static final String PROP_CURRENT_FORM_INPUT = "currentFormInput";
   
   private final AbstractEvaluation evaluation;
   
   private final List<FormInput> formInputs;
   
   private FormInput currentFormInput;

   public EvaluationInput(AbstractEvaluation evaluation) {
      assert evaluation != null;
      this.evaluation = evaluation;
      this.formInputs = new ArrayList<FormInput>(evaluation.countForms());
      for (Form form : evaluation.getForms()) {
         this.formInputs.add(new FormInput(form));
      }
      if (!formInputs.isEmpty()) {
         currentFormInput = formInputs.get(0);
      }
   }

   public AbstractEvaluation getEvaluation() {
      return evaluation;
   }

   public FormInput[] getFormInputs() {
      return formInputs.toArray(new FormInput[formInputs.size()]);
   }

   public FormInput getCurrentFormInput() {
      return currentFormInput;
   }

   public void setCurrentFormInput(FormInput currentFormInput) {
      FormInput oldValue = getCurrentFormInput();
      this.currentFormInput = currentFormInput;
      firePropertyChange(PROP_CURRENT_FORM_INPUT, oldValue, getCurrentFormInput());
   }
   
   public FormInput getFormInput(final Form form) {
      return CollectionUtil.search(formInputs, new IFilter<FormInput>() {
         @Override
         public boolean select(FormInput element) {
            return form == element.getForm();
         }
      });
   }
}
