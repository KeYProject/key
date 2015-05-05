package org.key_project.sed.key.evaluation.model_input;
import java.util.LinkedHashMap;
import java.util.Map;

import org.key_project.sed.key.evaluation.model.AbstractPage;
import org.key_project.util.java.XMLUtil;

public class AbstractPageInput<P extends AbstractPage> {
   private static final String TAG_PAGE = "page";
   private static final String ATTRIBUTE_PAGE_NAME = "name";

   private final P page;

   public AbstractPageInput(P page) {
      assert page != null;
      this.page = page;
   }

   public P getPage() {
      return page;
   }

   public void appendXMLContent(int level, StringBuffer sb) {
      Map<String, String> formAttributes = new LinkedHashMap<String, String>();
      formAttributes.put(ATTRIBUTE_PAGE_NAME, XMLUtil.encodeText(page.getName()));
      XMLUtil.appendStartTag(level, TAG_PAGE, formAttributes, sb);
      appendPageContent(level + 1, sb);
      XMLUtil.appendEndTag(level, TAG_PAGE, sb);
   }
   
   protected void appendPageContent(int level, StringBuffer sb) {
   }
}
