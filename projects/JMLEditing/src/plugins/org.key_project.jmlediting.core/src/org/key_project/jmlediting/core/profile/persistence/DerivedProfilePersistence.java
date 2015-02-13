package org.key_project.jmlediting.core.profile.persistence;

import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

import org.key_project.jmlediting.core.profile.IDerivedProfile;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.core.profile.syntax.UserDefinedKeyword;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

public class DerivedProfilePersistence {

   private static final String CLASS = "class";
   private static final String CODED_KEYWORD = "codedkeyword";
   private static final String DISABLED_PARENT_KEYWORD = "disabledparentkeyword";
   private static final String ADDITONAL_KEYWORD = "additonalkeyword";
   private static final String PARENT_IDENTIFIER = "parentidentifier";
   private static final String NAME = "name";
   private static final String IDENTIFIER = "identifier";
   private static final String DERIVED_PROFILE = "derivedprofile";

   public Document persist(final IDerivedProfile profile)
         throws ParserConfigurationException {
      final Document doc = DocumentBuilderFactory.newInstance()
            .newDocumentBuilder().newDocument();

      final Element topElement = doc.createElement(DERIVED_PROFILE);

      topElement.setAttribute(IDENTIFIER, profile.getIdentifier());
      topElement.setAttribute(NAME, profile.getName());
      topElement.setAttribute(PARENT_IDENTIFIER, profile.getParentProfile()
            .getIdentifier());

      for (final IKeyword additonalKeyword : profile.getAdditionalKeywords()) {
         final Element additionalKeywordElement = doc
               .createElement(ADDITONAL_KEYWORD);
         additionalKeywordElement.appendChild(this.persist(additonalKeyword,
               doc));
         topElement.appendChild(additionalKeywordElement);
      }

      for (final IKeyword disabledKeyword : profile.getParentProfile()
            .getSupportedKeywords()) {
         if (profile.isParentKeywordDisabled(disabledKeyword)) {
            final Element disabledKeywordElem = doc
                  .createElement(DISABLED_PARENT_KEYWORD);
            disabledKeywordElem.appendChild(this.persist(disabledKeyword, doc));
            topElement.appendChild(disabledKeywordElem);
         }
      }

      doc.appendChild(topElement);
      return doc;

   }

   public Element persist(final IKeyword keyword, final Document doc) {
      if (keyword instanceof UserDefinedKeyword) {
         throw new AssertionError("Cannot be persisted yet.");
      }
      else {
         final Element codedKeywordElem = doc.createElement(CODED_KEYWORD);
         codedKeywordElem.setAttribute(CLASS, keyword.getClass().getName());
         return codedKeywordElem;
      }
   }

}
