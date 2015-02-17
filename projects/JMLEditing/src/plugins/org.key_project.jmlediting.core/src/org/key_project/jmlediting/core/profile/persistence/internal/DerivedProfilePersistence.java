package org.key_project.jmlediting.core.profile.persistence.internal;

import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

import org.key_project.jmlediting.core.profile.DerivedProfile;
import org.key_project.jmlediting.core.profile.IDerivedProfile;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLProfileManagement;
import org.key_project.jmlediting.core.profile.persistence.IDerivedProfilePersistence;
import org.key_project.jmlediting.core.profile.persistence.ProfilePersistenceException;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.core.profile.syntax.UserDefinedKeyword;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;

public class DerivedProfilePersistence implements IDerivedProfilePersistence {

   private static final String CLASS = "class";
   private static final String CODED_KEYWORD = "codedkeyword";
   private static final String USER_DEFINED_KEYWORD = "userkeyword";
   private static final String DISABLED_PARENT_KEYWORD = "disabledparentkeyword";
   private static final String ADDITONAL_KEYWORD = "additonalkeyword";
   private static final String PARENT_IDENTIFIER = "parentidentifier";
   private static final String NAME = "name";
   private static final String IDENTIFIER = "identifier";
   private static final String DERIVED_PROFILE = "derivedprofile";

   @Override
   public Document persist(final IDerivedProfile profile)
         throws ProfilePersistenceException {
      final Document doc;
      try {
         doc = DocumentBuilderFactory.newInstance().newDocumentBuilder()
               .newDocument();
      }
      catch (final ParserConfigurationException e) {
         throw new ProfilePersistenceException(e);
      }

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

   public IKeyword readKeyword(final Element elem, final IJMLProfile profile)
         throws ProfilePersistenceException {
      final String name = elem.getNodeName();
      if (USER_DEFINED_KEYWORD.equals(name)) {
         throw new AssertionError("Cannot be persisted yet.");
      }
      else if (CODED_KEYWORD.equals(name)) {
         final String keywordClass = elem.getAttribute(CLASS);
         if ("".equals(keywordClass)) {
            throw new ProfilePersistenceException(
                  "No keyword class specified for the coded keyword node");
         }
         // Search a keyword of this class
         for (final IKeyword keyword : profile.getSupportedKeywords()) {
            if (keyword.getClass().getName().equals(keywordClass)) {
               return keyword;
            }
         }
         throw new ProfilePersistenceException(
               "No keyword with the given class was found");
      }
      else {
         throw new ProfilePersistenceException(
               "Got illegal profile element with name \"" + name + "\"");
      }
   }

   @Override
   public IDerivedProfile read(final Document doc)
         throws ProfilePersistenceException {
      final NodeList topNodes = doc.getElementsByTagName(DERIVED_PROFILE);
      if (topNodes.getLength() != 1) {
         throw new ProfilePersistenceException(
               "Expected exactly one profile but got " + topNodes.getLength());
      }

      final Element profileNode = (Element) topNodes.item(0);
      final String identifier = profileNode.getAttribute(IDENTIFIER);
      if ("".equals(identifier)) {
         throw new ProfilePersistenceException("Profile has no identifier");
      }
      final String name = profileNode.getAttribute(NAME);
      if ("".equals(name)) {
         throw new ProfilePersistenceException("Profile has no name");
      }
      final String parentIdentifer = profileNode
            .getAttribute(PARENT_IDENTIFIER);
      if ("".equals(parentIdentifer)) {
         throw new ProfilePersistenceException(
               "Profile has no parent identifier");
      }

      final IJMLProfile parentProfile = JMLProfileManagement
            .getProfileFromIdentifier(parentIdentifer);
      if (parentProfile == null) {
         throw new ProfilePersistenceException("The parent profile with id \""
               + parentIdentifer + "\" could not be found.");
      }

      final DerivedProfile profile = new DerivedProfile(name, identifier,
            parentProfile);

      final NodeList additonalKeywords = profileNode
            .getElementsByTagName(ADDITONAL_KEYWORD);
      for (int i = 0; i < additonalKeywords.getLength(); i++) {
         final Element addtionalKeywordElem = (Element) additonalKeywords
               .item(i);
         final IKeyword addtionalKeyword = this.readKeyword(
               addtionalKeywordElem, profile);
         profile.addKeyword(addtionalKeyword);
      }

      final NodeList parentDisabledKeywords = profileNode
            .getElementsByTagName(DISABLED_PARENT_KEYWORD);
      for (int i = 0; i < parentDisabledKeywords.getLength(); i++) {
         final Element parentDisabledKeywordElem = (Element) parentDisabledKeywords
               .item(i);
         final IKeyword parentDisabledKeyword = this.readKeyword(
               parentDisabledKeywordElem, profile);
         profile.setParentKeywordDisabled(parentDisabledKeyword, true);
      }

      return profile;
   }
}
