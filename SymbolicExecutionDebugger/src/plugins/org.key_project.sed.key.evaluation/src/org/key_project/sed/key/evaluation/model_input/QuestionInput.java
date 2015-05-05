package org.key_project.sed.key.evaluation.model_input;

import java.util.LinkedHashMap;
import java.util.Map;

import org.key_project.sed.key.evaluation.model.AbstractQuestion;
import org.key_project.util.bean.Bean;
import org.key_project.util.java.XMLUtil;

public class QuestionInput extends Bean {
   public static final String PROP_VALUE = "value";

   private static final String TAG_QUESTION = "question";

   private static final String ATTRIBUTE_QUESTION_NAME = "name";

   private static final String ATTRIBUTE_QUESTION_VALUE = "value";
   
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

   public void appendXMLContent(int level, StringBuffer sb) {
      if (question.isEditable()) {
         Map<String, String> questionAttributes = new LinkedHashMap<String, String>();
         questionAttributes.put(ATTRIBUTE_QUESTION_NAME, XMLUtil.encodeText(question.getName()));
         questionAttributes.put(ATTRIBUTE_QUESTION_VALUE, XMLUtil.encodeText(value));
         XMLUtil.appendEmptyTag(level, TAG_QUESTION, questionAttributes, sb);
      }
   }
}
