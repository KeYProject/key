package org.key_project.sed.key.evaluation.model_input;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import org.key_project.sed.key.evaluation.model.AbstractPage;
import org.key_project.sed.key.evaluation.model.Form;
import org.key_project.sed.key.evaluation.model.QuestionPage;
import org.key_project.sed.key.evaluation.model.SendFormPage;
import org.key_project.util.bean.Bean;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.XMLUtil;

public class FormInput extends Bean {
   public static final String PROP_CURRENT_PAGE_INPUT = "currentPageInput";
   
   private static final String TAG_FORM = "form";

   private static final String ATTRIBUTE_FORM_NAME = "name";

   private final Form form;
   
   private final List<AbstractPageInput<?>> pageInputs;
   
   private AbstractPageInput<?> currentPageInput;

   public FormInput(Form form) {
      assert form != null;
      this.form = form;
      this.pageInputs = new ArrayList<AbstractPageInput<?>>(form.countPages());
      for (AbstractPage page : form.getPages()) {
         if (page instanceof QuestionPage) {
            this.pageInputs.add(new QuestionPageInput((QuestionPage) page));
         }
         else if (page instanceof SendFormPage) {
            this.pageInputs.add(new SendFormPageInput((SendFormPage) page));
         }
         else {
            throw new IllegalStateException("Unsupported page: " + page);
         }
      }
      if (!pageInputs.isEmpty()) {
         currentPageInput = pageInputs.get(0);
      }
   }

   public Form getForm() {
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

   public String toXML() {
      StringBuffer sb = new StringBuffer();
      XMLUtil.appendXmlHeader(IOUtil.DEFAULT_CHARSET.displayName(), sb);
      Map<String, String> formAttributes = new LinkedHashMap<String, String>();
      formAttributes.put(ATTRIBUTE_FORM_NAME, XMLUtil.encodeText(form.getName()));
      XMLUtil.appendStartTag(0, TAG_FORM, formAttributes, sb);
      for (AbstractPageInput<?> pageInput : pageInputs) {
         pageInput.appendXMLContent(1, sb);
      }
      XMLUtil.appendEndTag(0, TAG_FORM, sb);
      return sb.toString();
   }
}
