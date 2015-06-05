package org.key_project.sed.key.evaluation.model.io;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.Deque;
import java.util.LinkedList;
import java.util.List;

import javax.xml.parsers.ParserConfigurationException;
import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;

import org.key_project.sed.key.evaluation.model.definition.AbstractEvaluation;
import org.key_project.sed.key.evaluation.model.definition.AbstractForm;
import org.key_project.sed.key.evaluation.model.definition.Choice;
import org.key_project.sed.key.evaluation.model.definition.Tool;
import org.key_project.sed.key.evaluation.model.input.AbstractFormInput;
import org.key_project.sed.key.evaluation.model.input.AbstractPageInput;
import org.key_project.sed.key.evaluation.model.input.EvaluationInput;
import org.key_project.sed.key.evaluation.model.input.QuestionInput;
import org.key_project.sed.key.evaluation.model.input.QuestionPageInput;
import org.key_project.sed.key.evaluation.model.input.RandomFormInput;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.java.StringUtil;
import org.xml.sax.Attributes;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;

/**
 * Provides functionality to parse XML files into {@link EvaluationInput}s.
 * @author Martin Hentschel
 */
public class EvaluationInputReader {
   /**
    * Forbid instances.
    */
   private EvaluationInputReader() {
   }
   
   /**
    * Parses the given XML text.
    * @param xml The XML text to parse.
    * @return The parsed {@link EvaluationInput}.
    * @throws ParserConfigurationException Occurred Exception
    * @throws SAXException Occurred Exception
    * @throws IOException Occurred Exception
    */
   public static EvaluationInput parse(String xml) throws ParserConfigurationException, SAXException, IOException {
      return xml != null ? parse(new ByteArrayInputStream(xml.getBytes())) : null;
   }
   
   /**
    * Parses the given {@link InputStream}.
    * @param in The {@link InputStream} to parse.
    * @return The parsed {@link EvaluationInput}.
    * @throws ParserConfigurationException Occurred Exception
    * @throws SAXException Occurred Exception
    * @throws IOException Occurred Exception
    */
   public static EvaluationInput parse(InputStream in) throws ParserConfigurationException, SAXException, IOException {
      SAXParserFactory factory = SAXParserFactory.newInstance();
      factory.setNamespaceAware(true);
      SAXParser saxParser = factory.newSAXParser();
      XMLHandler handler = new XMLHandler();
      saxParser.parse(in, handler);
      return handler.getEvaluationInput();
   }
   
   /**
    * The {@link DefaultHandler} used by {@link EvaluationInputReader#parse(InputStream)}.
    * @author Martin Hentschel
    */
   private static class XMLHandler extends DefaultHandler {
      /**
       * The resulting {@link EvaluationInput}.
       */
      private EvaluationInput evaluationInput;
      
      /**
       * The current {@link AbstractFormInput}.
       */
      private AbstractFormInput<?> currentFormInput;
      
      /**
       * The current {@link AbstractPageInput}.
       */
      private AbstractPageInput<?> currentPageInput;
      
      /**
       * Is currently defining page order?
       */
      private boolean parsingPageOrder = false;
      
      /**
       * Stack to store {@link QuestionInput}s.
       */
      private final Deque<QuestionInput> questionInputStack = new LinkedList<QuestionInput>();
      
      /**
       * Stack to store {@link Choice}s.
       */
      private final Deque<Choice> choiceStack = new LinkedList<Choice>();
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void startElement(String uri, String localName, String qName, Attributes attributes) throws SAXException {
         if (EvaluationInputWriter.TAG_EVALUATION.equals(qName)) {
            if (evaluationInput == null) {
               String evaluationName = attributes.getValue(EvaluationInputWriter.ATTRIBUTE_EVALUATION_NAME);
               AbstractEvaluation evaluation = AbstractEvaluation.getEvaluationForName(evaluationName);
               if (evaluation == null) {
                  throw new SAXException("Evaluation '" + evaluationName + "' is not available.");
               }
               evaluationInput = new EvaluationInput(evaluation);
               String uuid = attributes.getValue(EvaluationInputWriter.ATTRIBUTE_EVALUATION_UUID);
               evaluationInput.setUUID(uuid);
            }
            else {
               throw new SAXException("Tag '" + qName + "' found multiple times.");
            }
         }
         else if (EvaluationInputWriter.TAG_FORM.equals(qName)) {
            String evaluationName = attributes.getValue(EvaluationInputWriter.ATTRIBUTE_EVALUATION_NAME);
            String uuid = attributes.getValue(EvaluationInputWriter.ATTRIBUTE_EVALUATION_UUID);
            boolean setAsCurrentForm;
            if (evaluationInput == null) {
               AbstractEvaluation evaluation = AbstractEvaluation.getEvaluationForName(evaluationName);
               if (evaluation == null) {
                  throw new SAXException("Evaluation '" + evaluationName + "' is not available.");
               }
               evaluationInput = new EvaluationInput(evaluation);
               evaluationInput.setUUID(uuid);
               setAsCurrentForm = true;
            }
            else {
               if (evaluationName != null && !evaluationName.equals(evaluationInput.getEvaluation().getName())) {
                  throw new SAXException("Incompatible evaluations '" + evaluationName + "' and '" + evaluationInput.getEvaluation().getName() + "'.");
               }
               if (uuid != null && !uuid.equals(evaluationInput.getUUID())) {
                  throw new SAXException("Incompatible evaluations '" + uuid + "' and '" + evaluationInput.getUUID() + "'.");
               }
               setAsCurrentForm = false;
            }
            String formName = attributes.getValue(EvaluationInputWriter.ATTRIBUTE_FORM_NAME);
            AbstractForm form = evaluationInput.getEvaluation().getForm(formName);
            if (form == null) {
               throw new SAXException("Form '" + formName + "' is not part of evaluation '" + evaluationInput.getEvaluation().getName() + "'.");
            }
            currentFormInput = evaluationInput.getFormInput(form);
            if (setAsCurrentForm) {
               evaluationInput.setCurrentFormInput(currentFormInput);                  
            }
         }
         else if (EvaluationInputWriter.TAG_PAGE.equals(qName)) {
            if (currentFormInput == null) {
               throw new SAXException("Form is not defined.");
            }
            String pageName = attributes.getValue(EvaluationInputWriter.ATTRIBUTE_PAGE_NAME);
            AbstractPageInput<?> pageInput = currentFormInput.getPageInput(pageName);
            if (pageInput == null) {
               throw new SAXException("Page '" + pageInput + "' is not part of form '" + currentFormInput.getForm().getName() + "'.");
            }               
            if (parsingPageOrder) {
               if (!(currentFormInput instanceof RandomFormInput)) {
                  throw new SAXException("Form is not a random form.");
               }
               RandomFormInput randomFormInput = (RandomFormInput) currentFormInput;
               List<AbstractPageInput<?>> newPageOrder = new LinkedList<AbstractPageInput<?>>();
               CollectionUtil.addAll(newPageOrder, randomFormInput.getPageOrder());
               newPageOrder.add(pageInput);
               randomFormInput.setPageOrder(newPageOrder);
               String toolName = attributes.getValue(EvaluationInputWriter.ATTRIBUTE_TOOL_NAME);
               if (!StringUtil.isTrimmedEmpty(toolName)) {
                  Tool tool = evaluationInput.getEvaluation().getTool(toolName);
                  if (tool == null) {
                     throw new SAXException("Tool '" + toolName + "' is not part of evaluation '" + evaluationInput.getEvaluation().getName() + "'.");
                  }
                  randomFormInput.setTool(pageInput, tool);
               }
            }
            else {
               currentPageInput = pageInput;
               String shownTime = attributes.getValue(EvaluationInputWriter.ATTRIBUTE_PAGE_SHOWN_TIME);
               if (!StringUtil.isTrimmedEmpty(shownTime)) {
                  try {
                     pageInput.setShownTime(Long.parseLong(shownTime));
                  }
                  catch (NumberFormatException e) {
                     throw new SAXException("Shown time '" + shownTime + "' is not a valid long number.");
                  }
               }
               else {
                  pageInput.setShownTime(0);
               }
            }
         }
         else if (EvaluationInputWriter.TAG_QUESTION.equals(qName)) {
            if (currentPageInput == null) {
               throw new SAXException("Page is not defined.");
            }
            if (!(currentPageInput instanceof QuestionPageInput)) {
               throw new SAXException("Page does not support questions.");
            }
            final String questionName = attributes.getValue(EvaluationInputWriter.ATTRIBUTE_QUESTION_NAME);
            QuestionInput questionInput;
            if (choiceStack.isEmpty()) {
               questionInput = ((QuestionPageInput) currentPageInput).getQuestionInput(questionName);
            }
            else {
               QuestionInput[] choiceInputs = questionInputStack.getFirst().getChoiceInputs(choiceStack.getFirst());
               if (choiceInputs == null) {
                  throw new SAXException("Question Inputs of '" + choiceStack.getFirst() + "' are not available.");
               }
               questionInput = ArrayUtil.search(choiceInputs, new IFilter<QuestionInput>() {
                  @Override
                  public boolean select(QuestionInput element) {
                     return ObjectUtil.equals(element.getQuestion().getName(), questionName);
                  }
               });
            }
            if (questionInput == null) {
               throw new SAXException("Question '" + questionInput + "' is not part of page '" + currentPageInput.getPage().getName() + "'.");
            }
            questionInputStack.addFirst(questionInput);
            String questionValue = attributes.getValue(EvaluationInputWriter.ATTRIBUTE_QUESTION_VALUE);
            questionInput.setValue(questionValue);
            String questionValueSetAt = attributes.getValue(EvaluationInputWriter.ATTRIBUTE_QUESTION_VALUE_SET_AT);
            if (!StringUtil.isTrimmedEmpty(questionValueSetAt)) {
               try {
                  questionInput.setValueSetAt(Long.parseLong(questionValueSetAt));
               }
               catch (NumberFormatException e) {
                  throw new SAXException("Value set at '" + questionValueSetAt + "' is not a valid long number.");
               }
            }
            else {
               questionInput.setValueSetAt(0);
            }
            String questionTrust = attributes.getValue(EvaluationInputWriter.ATTRIBUTE_QUESTION_TRUST);
            if (!StringUtil.isEmpty(questionTrust)) {
               questionInput.setTrust(Boolean.valueOf(questionTrust));
            }
            else {
               questionInput.setTrust(null);
            }
            String questionTrustSetAt = attributes.getValue(EvaluationInputWriter.ATTRIBUTE_QUESTION_TRUST_SET_AT);
            if (!StringUtil.isTrimmedEmpty(questionTrustSetAt)) {
               try {
                  questionInput.setTrustSetAt(Long.parseLong(questionTrustSetAt));
               }
               catch (NumberFormatException e) {
                  throw new SAXException("Trust set at '" + questionTrustSetAt + "' is not a valid long number.");
               }
            }
            else {
               questionInput.setTrustSetAt(0);
            }
         }
         else if (EvaluationInputWriter.TAG_RANDOM_PAGE_ORDER.equals(qName)) {
            parsingPageOrder = true;
         }
         else if (EvaluationInputWriter.TAG_CHOICE.equals(qName)) {
            if (questionInputStack.isEmpty()) {
               throw new SAXException("Choice is not a child of a question input.");
            }
            String choiceValue = attributes.getValue(EvaluationInputWriter.ATTRIBUTE_CHOICE_VALUE);
            QuestionInput parentInput = questionInputStack.getFirst();
            Choice choice = parentInput.getChoice(choiceValue);
            if (choice == null) {
               throw new SAXException("Choice '" + choiceValue + "' is not part of question '" + parentInput.getQuestion().getName() + "'.");
            }
            choiceStack.addFirst(choice);
         }
         else {
            throw new SAXException("Unsupported tag '" + qName + "'.");
         }
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void endElement(String uri, String localName, String qName) throws SAXException {
         if (EvaluationInputWriter.TAG_RANDOM_PAGE_ORDER.equals(qName)) {
            parsingPageOrder = false;
         }
         else if (EvaluationInputWriter.TAG_QUESTION.equals(qName)) {
            questionInputStack.removeFirst();
         }
         else if (EvaluationInputWriter.TAG_CHOICE.equals(qName)) {
            choiceStack.removeFirst();
         }
      }

      /**
       * Returns the resulting {@link EvaluationInput}.
       * @return The resulting {@link EvaluationInput}.
       */
      public EvaluationInput getEvaluationInput() {
         return evaluationInput;
      }
   }
}
