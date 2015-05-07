package org.key_project.sed.key.evaluation.model.input;

import org.key_project.sed.key.evaluation.model.definition.AbstractQuestion;
import org.key_project.util.bean.Bean;

public class QuestionInput extends Bean {
   public static final String PROP_VALUE = "value";
   
   private final AbstractQuestion question;
   
   private String value;

   public QuestionInput(AbstractQuestion question) {
      this.question = question;
      this.value = question.getDefaultValue();
   }

   public AbstractQuestion getQuestion() {
      return question;
   }

   public String getValue() {
      return value;
   }

   public void setValue(String value) {
      String oldValue = getValue();
      this.value = value;
      firePropertyChange(PROP_VALUE, oldValue, getValue());
   }
   
   public String validate() {
      return question.validate(getValue());
   }
}
