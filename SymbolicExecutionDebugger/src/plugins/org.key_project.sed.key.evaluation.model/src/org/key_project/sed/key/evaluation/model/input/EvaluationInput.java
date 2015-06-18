package org.key_project.sed.key.evaluation.model.input;

import java.util.ArrayList;
import java.util.List;

import org.key_project.sed.key.evaluation.model.definition.AbstractEvaluation;
import org.key_project.sed.key.evaluation.model.definition.AbstractForm;
import org.key_project.sed.key.evaluation.model.definition.FixedForm;
import org.key_project.sed.key.evaluation.model.definition.RandomForm;
import org.key_project.util.bean.Bean;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;

import de.uka.ilkd.key.util.KeYResourceManager;

public class EvaluationInput extends Bean {
   public static final String PROP_CURRENT_FORM_INPUT = "currentFormInput";

   public static final String PROP_UUID = "uuid";

   public static final String PROP_TIMESTAMP = "timestamp";
   
   private final AbstractEvaluation evaluation;
   
   private final List<AbstractFormInput<?>> formInputs;
   
   private AbstractFormInput<?> currentFormInput;
   
   private String UUID;
   
   private final String keyVersion;
   
   private final String keyInternalVersion;

   private long timestamp;
   
   public EvaluationInput(AbstractEvaluation evaluation) {
      this(evaluation, KeYResourceManager.getManager().getVersion(), KeYResourceManager.getManager().getSHA1());
   }

   public EvaluationInput(AbstractEvaluation evaluation, String keyVersion, String keyInternalVersion) {
      assert evaluation != null;
      this.evaluation = evaluation;
      this.keyVersion = keyVersion;
      this.keyInternalVersion = keyInternalVersion;
      this.formInputs = new ArrayList<AbstractFormInput<?>>(evaluation.countForms());
      for (AbstractForm form : evaluation.getForms()) {
         if (form instanceof FixedForm) {
            this.formInputs.add(new FixedFormInput(this, (FixedForm) form));
         }
         else if (form instanceof RandomForm) {
            this.formInputs.add(new RandomFormInput(this, (RandomForm) form));
         }
         else {
            throw new IllegalStateException("Unsupported from: " + form);
         }
      }
      if (!formInputs.isEmpty()) {
         currentFormInput = formInputs.get(0);
      }
   }

   public AbstractEvaluation getEvaluation() {
      return evaluation;
   }

   public String getKeyVersion() {
      return keyVersion;
   }

   public String getKeyInternalVersion() {
      return keyInternalVersion;
   }

   public AbstractFormInput<?>[] getFormInputs() {
      return formInputs.toArray(new AbstractFormInput[formInputs.size()]);
   }

   public AbstractFormInput<?> getCurrentFormInput() {
      return currentFormInput;
   }

   public void setCurrentFormInput(AbstractFormInput<?> currentFormInput) {
      AbstractFormInput<?> oldValue = getCurrentFormInput();
      this.currentFormInput = currentFormInput;
      firePropertyChange(PROP_CURRENT_FORM_INPUT, oldValue, getCurrentFormInput());
   }
   
   public AbstractFormInput<?> getFormInput(final AbstractForm form) {
      return CollectionUtil.search(formInputs, new IFilter<AbstractFormInput<?>>() {
         @Override
         public boolean select(AbstractFormInput<?> element) {
            return form == element.getForm();
         }
      });
   }

   public String getUUID() {
      return UUID;
   }

   public void setUUID(String UUID) {
      String oldValue = getUUID();
      this.UUID = UUID;
      firePropertyChange(PROP_UUID, oldValue, getUUID());
   }

   public int indexOfFormInput(AbstractFormInput<?> formInput) {
      return formInputs.indexOf(formInput);
   }

   public int countFormInputs() {
      return formInputs.size();
   }

   public AbstractFormInput<?> getFormInput(int index) {
      return formInputs.get(index);
   }

   public long getTimestamp() {
      return timestamp;
   }

   public void setTimestamp(long timestamp) {
      long oldValue = getTimestamp();
      this.timestamp = timestamp;
      firePropertyChange(PROP_TIMESTAMP, oldValue, getTimestamp());
   }

   public void reset() {
      if (!formInputs.isEmpty()) {
         setCurrentFormInput(formInputs.get(0));
      }
      else {
         setCurrentFormInput(null);
      }
      setUUID(null);
      setTimestamp(0);
      for (AbstractFormInput<?> formInput : formInputs) {
         formInput.reset();
      }
   }
}
