package org.key_project.sed.key.evaluation.model.io;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import org.key_project.sed.key.evaluation.model.definition.AbstractEvaluation;
import org.key_project.sed.key.evaluation.model.definition.AbstractForm;
import org.key_project.sed.key.evaluation.model.definition.AbstractPage;
import org.key_project.sed.key.evaluation.model.definition.AbstractQuestion;
import org.key_project.sed.key.evaluation.model.definition.Choice;
import org.key_project.sed.key.evaluation.model.definition.Tool;
import org.key_project.sed.key.evaluation.model.input.AbstractFormInput;
import org.key_project.sed.key.evaluation.model.input.AbstractPageInput;
import org.key_project.sed.key.evaluation.model.input.EvaluationInput;
import org.key_project.sed.key.evaluation.model.input.FixedFormInput;
import org.key_project.sed.key.evaluation.model.input.InstructionPageInput;
import org.key_project.sed.key.evaluation.model.input.QuestionInput;
import org.key_project.sed.key.evaluation.model.input.QuestionPageInput;
import org.key_project.sed.key.evaluation.model.input.RandomFormInput;
import org.key_project.sed.key.evaluation.model.input.SendFormPageInput;
import org.key_project.sed.key.evaluation.model.input.ToolPageInput;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.StringUtil;
import org.key_project.util.java.XMLUtil;

/**
 * Provides functionality to convert {@link EvaluationInput}s into XML content.
 * @author Martin Hentschel
 */
public class EvaluationInputWriter {
   /**
    * Tag name to store {@link EvaluationInput}s.
    */
   public static final String TAG_EVALUATION = "evaluation";
   
   /**
    * Attribute name to store {@link AbstractEvaluation#getName()}.
    */
   public static final String ATTRIBUTE_EVALUATION_NAME = "evaluation";

   /**
    * Attribute name to store {@link EvaluationInput#getUUID()}.
    */
   public static final String ATTRIBUTE_EVALUATION_UUID = "uuid";

   /**
    * Attribute name to store {@link EvaluationInput#getTimestamp()}.
    */
   public static final String ATTRIBUTE_EVALUATION_TIMESTAMP = "timestamp";
   
   /**
    * Tag name to store {@link AbstractFormInput}s.
    */
   public static final String TAG_FORM = "form";

   /**
    * Attribute name to store {@link AbstractForm#getName()}.
    */
   public static final String ATTRIBUTE_FORM_NAME = "name";

   /**
    * Tag name to store {@link AbstractPageInput}s.
    */
   public static final String TAG_PAGE = "page";

   /**
    * Attribute name to store {@link AbstractPage#getName()}.
    */
   public static final String ATTRIBUTE_PAGE_NAME = "name";

   /**
    * Tag name to store {@link QuestionInput}s.
    */
   public static final String TAG_QUESTION = "question";

   /**
    * Attribute name to store {@link AbstractQuestion#getName()}.
    */
   public static final String ATTRIBUTE_QUESTION_NAME = "name";

   /**
    * Attribute name to store {@link QuestionInput#getValue()}.
    */
   public static final String ATTRIBUTE_QUESTION_VALUE = "value";

   /**
    * Attribute name to store {@link QuestionInput#getTrust()}.
    */
   public static final String ATTRIBUTE_QUESTION_TRUST = "trust";

   /**
    * Tag name to store {@link RandomFormInput#getPageOrder()}.
    */
   public static final String TAG_RANDOM_PAGE_ORDER = "pageOrder";

   /**
    * Attribute name to store {@link RandomFormInput#getTool(AbstractPageInput)} entries.
    */
   public static final String ATTRIBUTE_TOOL_NAME = "tool";

   /**
    * Tag name to store {@link Choice}s.
    */
   public static final String TAG_CHOICE = "choice";

   /**
    * Attribute name to store {@link Choice#getValue()} entries.
    */
   public static final String ATTRIBUTE_CHOICE_VALUE = "value";

   /**
    * Attribute name to store {@link AbstractPageInput#getShownTime()} entries.
    */
   public static final String ATTRIBUTE_PAGE_SHOWN_TIME = "shownTime";

   /**
    * Attribute name to store {@link QuestionInput#getValueSetAt()} entries.
    */
   public static final String ATTRIBUTE_QUESTION_VALUE_SET_AT = "valueSetAt";

   /**
    * Attribute name to store {@link QuestionInput#getTrustSetAt()} entries.
    */
   public static final String ATTRIBUTE_QUESTION_TRUST_SET_AT = "trustSetAt";

   /**
    * Attribute name to store {@link EvaluationInput#getKeyVersion()}.
    */
   public static final String ATTRIBUTE_EVALUATION_VERSION = "keyVersion";

   /**
    * Attribute name to store {@link EvaluationInput#getKeyInternalVersion()}.
    */
   public static final String ATTRIBUTE_EVALUATION_INTERNAL_VERSION = "keyInternalVersion";

   /**
    * Attribute name to store {@link EvaluationInput#getCurrentFormInput()}.
    */
   public static final String ATTRIBUTE_EVALUATION_CURRENT_FORM = "currentForm";

   /**
    * Attribute name to store {@link AbstractFormInput#getCurrentPageInput()}.
    */
   public static final String ATTRIBUTE_FORM_CURRENT_PAGE = "currentPage";

   /**
    * Converts the orders of the given {@link RandomFormInput}s into XML.
    * @param evaluationInput The {@link EvaluationInput}.
    * @param updatedOrders The {@link RandomFormInput}s.
    * @return The random order XML.
    */
   public static String toRandomOrderXML(EvaluationInput evaluationInput, List<RandomFormInput> updatedOrders) {
      StringBuffer sb = new StringBuffer();
      XMLUtil.appendXmlHeader(IOUtil.DEFAULT_CHARSET.displayName(), sb);
      Map<String, String> evaluationAttributes = new LinkedHashMap<String, String>();
      evaluationAttributes.put(ATTRIBUTE_EVALUATION_NAME, evaluationInput.getEvaluation().getName());
      evaluationAttributes.put(ATTRIBUTE_EVALUATION_VERSION, evaluationInput.getKeyVersion());
      evaluationAttributes.put(ATTRIBUTE_EVALUATION_INTERNAL_VERSION, evaluationInput.getKeyInternalVersion());
      if (!StringUtil.isTrimmedEmpty(evaluationInput.getUUID())) {
         evaluationAttributes.put(ATTRIBUTE_EVALUATION_UUID, evaluationInput.getUUID());
      }
      if (evaluationInput.getTimestamp() != 0) {
         evaluationAttributes.put(ATTRIBUTE_EVALUATION_TIMESTAMP, evaluationInput.getTimestamp() + "");
      }
      XMLUtil.appendStartTag(0, TAG_EVALUATION, evaluationAttributes, sb);
      if (!CollectionUtil.isEmpty(updatedOrders)) {
         for (RandomFormInput randomFormInput : updatedOrders) {
            appendRandomOrderFormInput(1, randomFormInput, sb);
         }
      }
      XMLUtil.appendEndTag(0, TAG_EVALUATION, sb);
      return sb.toString();
   }
   
   /**
    * Converts the given {@link AbstractFormInput} into the answer XML.
    * @param formInput The {@link AbstractFormInput} to convert.
    * @param updatedOrders The {@link RandomFormInput}s with updated orders.
    * @return The answer XML.
    */
   public static String toFormAnswerXML(AbstractFormInput<?> formInput, List<RandomFormInput> updatedOrders) {
      EvaluationInput evaluationInput = formInput.getEvaluationInput();
      StringBuffer sb = new StringBuffer();
      XMLUtil.appendXmlHeader(IOUtil.DEFAULT_CHARSET.displayName(), sb);
      Map<String, String> evaluationAttributes = new LinkedHashMap<String, String>();
      evaluationAttributes.put(ATTRIBUTE_EVALUATION_NAME, evaluationInput.getEvaluation().getName());
      evaluationAttributes.put(ATTRIBUTE_EVALUATION_VERSION, evaluationInput.getKeyVersion());
      evaluationAttributes.put(ATTRIBUTE_EVALUATION_INTERNAL_VERSION, evaluationInput.getKeyInternalVersion());
      if (!StringUtil.isTrimmedEmpty(evaluationInput.getUUID())) {
         evaluationAttributes.put(ATTRIBUTE_EVALUATION_UUID, evaluationInput.getUUID());
      }
      if (evaluationInput.getTimestamp() != 0) {
         evaluationAttributes.put(ATTRIBUTE_EVALUATION_TIMESTAMP, evaluationInput.getTimestamp() + "");
      }
      XMLUtil.appendStartTag(0, TAG_EVALUATION, evaluationAttributes, sb);
      // Append answers
      Map<String, String> formAttributes = new LinkedHashMap<String, String>();
      formAttributes.put(ATTRIBUTE_FORM_NAME, formInput.getForm().getName());
      XMLUtil.appendStartTag(1, TAG_FORM, formAttributes, sb);
      for (AbstractPageInput<?> pageInput : formInput.getPageInputs()) {
         if (!pageInput.getPage().isReadonly() && pageInput.getPage().isEnabled()) {
            appendPageInput(2, pageInput, sb);
         }
      }
      XMLUtil.appendEndTag(1, TAG_FORM, sb);
      // Append orders
      if (!CollectionUtil.isEmpty(updatedOrders)) {
         for (RandomFormInput randomFormInput : updatedOrders) {
            appendRandomOrderFormInput(1, randomFormInput, sb);
         }
      }
      XMLUtil.appendEndTag(0, TAG_EVALUATION, sb);
      return sb.toString();
   }

   /**
    * Appends the given {@link AbstractFormInput}.
    * @param level The intent level.
    * @param questionInput The {@link AbstractFormInput} to append.
    * @param sb The {@link StringBuffer} to append to.
    */
   protected static void appendRandomOrderFormInput(int level, AbstractFormInput<?> formInput, StringBuffer sb) {
      Map<String, String> formAttributes = new LinkedHashMap<String, String>();
      formAttributes.put(ATTRIBUTE_FORM_NAME, formInput.getForm().getName());
      XMLUtil.appendStartTag(level, TAG_FORM, formAttributes, sb);
      if (formInput instanceof FixedFormInput) {
         // Nothing to do
      }
      else if (formInput instanceof RandomFormInput) {
         appendRandomOrder(level + 1, (RandomFormInput) formInput, sb);
      }
      else {
         throw new IllegalStateException("Unsupported form input: " + formInput);
      }
      XMLUtil.appendEndTag(level, TAG_FORM, sb);
   }
   
   /**
    * Appends the specified random order.
    * @param level The intent level.
    * @param rfi The {@link RandomFormInput} providing the random order.
    * @param sb The {@link StringBuffer} to append to.
    */
   protected static void appendRandomOrder(int level, RandomFormInput rfi, StringBuffer sb) {
      List<AbstractPageInput<?>> pageOrder = rfi.getPageOrder();
      if (!CollectionUtil.isEmpty(pageOrder)) {
         XMLUtil.appendStartTag(level, TAG_RANDOM_PAGE_ORDER, null, sb);
         for (AbstractPageInput<?> pageInput : pageOrder) {
            Map<String, String> pageAttributes = new LinkedHashMap<String, String>();
            pageAttributes.put(ATTRIBUTE_PAGE_NAME, pageInput.getPage().getName());
            Tool tool = rfi.getTool(pageInput);
            if (tool != null) {
               pageAttributes.put(ATTRIBUTE_TOOL_NAME, tool.getName());
            }
            XMLUtil.appendEmptyTag(level + 1, TAG_PAGE, pageAttributes, sb);
         }
         XMLUtil.appendEndTag(level, TAG_RANDOM_PAGE_ORDER, sb);
      }
   }
   
   /**
    * Converts the given {@link AbstractFormInput} into the answer XML.
    * @param formInput The {@link AbstractFormInput} to convert.
    * @return The answer XML.
    */
   public static String toFormAnswerXML(AbstractFormInput<?> formInput) {
      StringBuffer sb = new StringBuffer();
      XMLUtil.appendXmlHeader(IOUtil.DEFAULT_CHARSET.displayName(), sb);
      Map<String, String> formAttributes = new LinkedHashMap<String, String>();
      formAttributes.put(ATTRIBUTE_FORM_NAME, formInput.getForm().getName());
      formAttributes.put(ATTRIBUTE_EVALUATION_NAME, formInput.getEvaluationInput().getEvaluation().getName());
      formAttributes.put(ATTRIBUTE_EVALUATION_VERSION, formInput.getEvaluationInput().getKeyVersion());
      formAttributes.put(ATTRIBUTE_EVALUATION_INTERNAL_VERSION, formInput.getEvaluationInput().getKeyInternalVersion());
      if (!StringUtil.isTrimmedEmpty(formInput.getEvaluationInput().getUUID())) {
         formAttributes.put(ATTRIBUTE_EVALUATION_UUID, formInput.getEvaluationInput().getUUID());
      }
      if (formInput.getEvaluationInput().getTimestamp() != 0) {
         formAttributes.put(ATTRIBUTE_EVALUATION_TIMESTAMP, formInput.getEvaluationInput().getTimestamp() + "");
      }
      XMLUtil.appendStartTag(0, TAG_FORM, formAttributes, sb);
      for (AbstractPageInput<?> pageInput : formInput.getPageInputs()) {
         if (!pageInput.getPage().isReadonly() && pageInput.getPage().isEnabled()) {
            appendPageInput(1, pageInput, sb);
         }
      }
      XMLUtil.appendEndTag(0, TAG_FORM, sb);
      return sb.toString();
   }

   /**
    * Appends the given {@link AbstractPageInput}.
    * @param level The intent level.
    * @param questionInput The {@link AbstractPageInput} to append.
    * @param sb The {@link StringBuffer} to append to.
    */
   protected static void appendPageInput(int level, AbstractPageInput<?> pageInput, StringBuffer sb) {
      Map<String, String> pageAttributes = new LinkedHashMap<String, String>();
      pageAttributes.put(ATTRIBUTE_PAGE_NAME, pageInput.getPage().getName());
      if (pageInput.getShownTime() > 0) {
         pageAttributes.put(ATTRIBUTE_PAGE_SHOWN_TIME, pageInput.getShownTime() + "");
      }
      XMLUtil.appendStartTag(level, TAG_PAGE, pageAttributes, sb);
      if (pageInput instanceof QuestionPageInput) {
         for (QuestionInput questionInput : ((QuestionPageInput) pageInput).getQuestionInputs()) {
            appendQuestionInput(level + 1, questionInput, sb);
         }
      }
      else if (pageInput instanceof SendFormPageInput) {
         SendFormPageInput sfpi = (SendFormPageInput) pageInput;
         appendQuestionInput(level + 1, sfpi.getAcceptInput(), sb);
      }
      else if (pageInput instanceof InstructionPageInput) {
         // Nothing to do
      }
      else if (pageInput instanceof ToolPageInput) {
         // Nothing to do
      }
      else {
         throw new IllegalStateException("Unsupported page input: " + pageInput);
      }
      XMLUtil.appendEndTag(level, TAG_PAGE, sb);
   }

   /**
    * Appends the given {@link QuestionInput}.
    * @param level The intent level.
    * @param questionInput The {@link QuestionInput} to append.
    * @param sb The {@link StringBuffer} to append to.
    */
   protected static void appendQuestionInput(int level, QuestionInput questionInput, StringBuffer sb) {
      if (questionInput.getQuestion().isEditable() || questionInput.countChildInputs() > 0) {
         Map<String, String> questionAttributes = new LinkedHashMap<String, String>();
         questionAttributes.put(ATTRIBUTE_QUESTION_NAME, questionInput.getQuestion().getName());
         if (questionInput.getValue() != null) {
            questionAttributes.put(ATTRIBUTE_QUESTION_VALUE, questionInput.getValue());
         }
         if (questionInput.getValueSetAt() > 0) {
            questionAttributes.put(ATTRIBUTE_QUESTION_VALUE_SET_AT, questionInput.getValueSetAt() + "");
         }
         if (questionInput.getTrust() != null) {
            questionAttributes.put(ATTRIBUTE_QUESTION_TRUST, questionInput.getTrust().toString());
         }
         if (questionInput.getTrustSetAt() > 0) {
            questionAttributes.put(ATTRIBUTE_QUESTION_TRUST_SET_AT, questionInput.getTrustSetAt() + "");
         }
         if (questionInput.hasChoiceInputs() || questionInput.countChildInputs() > 0) {
            XMLUtil.appendStartTag(level, TAG_QUESTION, questionAttributes, sb);
            if (questionInput.hasChoiceInputs()) {
               for (Choice choice : questionInput.getChoices()) {
                  Map<String, String> choiceAttributes = new LinkedHashMap<String, String>();
                  choiceAttributes.put(ATTRIBUTE_CHOICE_VALUE, choice.getValue());
                  XMLUtil.appendStartTag(level + 1, TAG_CHOICE, choiceAttributes, sb);
                  for (QuestionInput childQuestionInput : questionInput.getChoiceInputs(choice)) {
                     appendQuestionInput(level + 2, childQuestionInput, sb);
                  }
                  XMLUtil.appendEndTag(level + 1, TAG_CHOICE, sb);
               }
            }
            if (questionInput.countChildInputs() > 0) {
               for (QuestionInput childInput : questionInput.getChildInputs()) {
                  appendQuestionInput(level + 1, childInput, sb);
               }
            }
            XMLUtil.appendEndTag(level, TAG_QUESTION, sb);
         }
         else {
            XMLUtil.appendEmptyTag(level, TAG_QUESTION, questionAttributes, sb);
         }
      }
   }

   /**
    * Converts the given {@link EvaluationInput} into XML with all its content.
    * @param evaluationInput The {@link EvaluationInput} to convert.
    * @return The XML.
    */
   public static String toXML(EvaluationInput evaluationInput) {
      StringBuffer sb = new StringBuffer();
      XMLUtil.appendXmlHeader(IOUtil.DEFAULT_CHARSET.displayName(), sb);
      Map<String, String> evaluationAttributes = new LinkedHashMap<String, String>();
      evaluationAttributes.put(ATTRIBUTE_EVALUATION_NAME, evaluationInput.getEvaluation().getName());
      evaluationAttributes.put(ATTRIBUTE_EVALUATION_UUID, evaluationInput.getUUID());
      if (evaluationInput.getTimestamp() != 0) {
         evaluationAttributes.put(ATTRIBUTE_EVALUATION_TIMESTAMP, evaluationInput.getTimestamp() + "");
      }
      evaluationAttributes.put(ATTRIBUTE_EVALUATION_CURRENT_FORM, evaluationInput.getCurrentFormInput().getForm().getName());
      XMLUtil.appendStartTag(0, TAG_EVALUATION, evaluationAttributes, sb);
      for (AbstractFormInput<?> formInput : evaluationInput.getFormInputs()) {
         appendFormInput(1, formInput, sb);
      }
      XMLUtil.appendEndTag(0, TAG_EVALUATION, sb);
      return sb.toString();
   }

   /**
    * Appends the given {@link AbstractFormInput}.
    * @param level The intent level.
    * @param formInput The {@link AbstractFormInput} to append.
    * @param sb The {@link StringBuffer} to append to.
    */
   protected static void appendFormInput(int level, AbstractFormInput<?> formInput, StringBuffer sb) {
      Map<String, String> formAttributes = new LinkedHashMap<String, String>();
      formAttributes.put(ATTRIBUTE_FORM_NAME, formInput.getForm().getName());
      formAttributes.put(ATTRIBUTE_FORM_CURRENT_PAGE, formInput.getCurrentPageInput().getPage().getName());
      XMLUtil.appendStartTag(level, TAG_FORM, formAttributes, sb);
      if (formInput instanceof RandomFormInput) {
         appendRandomOrder(level + 1, (RandomFormInput) formInput, sb);
      }
      else if (formInput instanceof FixedFormInput) {
         // Nothing to do
      }
      else {
         throw new IllegalStateException("Unsupported form input: " + formInput);
      }
      for (AbstractPageInput<?> pageInput : formInput.getPageInputs()) {
         if (pageInput.getPage().isEnabled()) {
            appendPageInput(level + 1, pageInput, sb);
         }
      }
      XMLUtil.appendEndTag(level, TAG_FORM, sb);
   }
}
