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
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;

public class DerivedProfilePersistence implements IDerivedProfilePersistence {

   protected static final String CLASS = "class";
   protected static final String BUNDLE = "bundle";
   protected static final String CODED_KEYWORD = "codedkeyword";
   protected static final String USER_DEFINED_KEYWORD = "userkeyword";
   protected static final String DISABLED_PARENT_KEYWORDS = "disabledparentkeywords";
   protected static final String ADDITONAL_KEYWORDS = "additonalkeywords";
   protected static final String PARENT_IDENTIFIER = "parentidentifier";
   protected static final String NAME = "name";
   protected static final String IDENTIFIER = "identifier";
   protected static final String DERIVED_PROFILE = "derivedprofile";

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

      final Element additionalKeywords = this.persistAdditionalKeywords(
            profile, doc);
      if (additionalKeywords != null) {
         topElement.appendChild(additionalKeywords);
      }

      final Element disabledKeywords = this.persistDisabledKeywords(profile,
            doc);
      if (disabledKeywords != null) {
         topElement.appendChild(disabledKeywords);
      }

      doc.appendChild(topElement);
      return doc;

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

      this.readAdditonalKeywords(profileNode, profile);

      this.readDisabledKeywords(profileNode, profile);

      return profile;
   }

   private void readAdditonalKeywords(final Element profileNode,
         final DerivedProfile profile) throws ProfilePersistenceException {
      final InstantiateKeywordsPersistence keywordPersistence = new InstantiateKeywordsPersistence();
      final NodeList additonalKeywords = profileNode
            .getElementsByTagName(ADDITONAL_KEYWORDS);
      for (int i = 0; i < additonalKeywords.getLength(); i++) {
         final Element addtionalKeywordElem = (Element) additonalKeywords
               .item(i);
         final NodeList keywordsList = addtionalKeywordElem.getChildNodes();
         for (int j = 0; j < keywordsList.getLength(); j++) {
            final IKeyword addtionalKeyword = keywordPersistence
                  .readKeyword((Element) keywordsList.item(j));
            profile.addKeyword(addtionalKeyword);
         }
      }
   }

   private Element persistAdditionalKeywords(final IDerivedProfile profile,
         final Document doc) throws ProfilePersistenceException {
      final InstantiateKeywordsPersistence keywordPersistence = new InstantiateKeywordsPersistence();
      if (!profile.getAdditionalKeywords().isEmpty()) {
         final Element additionalKeywordElement = doc
               .createElement(ADDITONAL_KEYWORDS);
         for (final IKeyword additonalKeyword : profile.getAdditionalKeywords()) {

            additionalKeywordElement.appendChild(keywordPersistence.persist(
                  additonalKeyword, doc));

         }
         return additionalKeywordElement;
      }
      return null;
   }

   private Element persistDisabledKeywords(final IDerivedProfile profile,
         final Document doc) throws ProfilePersistenceException {
      final LoadFromProfileKeywordPersistence keywordPersistence = new LoadFromProfileKeywordPersistence(
            profile.getParentProfile());
      final Element disabledKeywordElem = doc
            .createElement(DISABLED_PARENT_KEYWORDS);
      for (final IKeyword disabledKeyword : profile.getParentProfile()
            .getSupportedKeywords()) {
         if (profile.isParentKeywordDisabled(disabledKeyword)) {

            disabledKeywordElem.appendChild(keywordPersistence.persist(
                  disabledKeyword, doc));

         }
      }
      if (disabledKeywordElem.getChildNodes().getLength() > 0) {
         return disabledKeywordElem;
      }
      return null;
   }

   private void readDisabledKeywords(final Element profileNode,
         final DerivedProfile profile) throws ProfilePersistenceException {
      final LoadFromProfileKeywordPersistence keywordPersistence = new LoadFromProfileKeywordPersistence(
            profile.getParentProfile());
      final NodeList parentDisabledKeywords = profileNode
            .getElementsByTagName(DISABLED_PARENT_KEYWORDS);
      for (int i = 0; i < parentDisabledKeywords.getLength(); i++) {
         final Element parentDisabledKeywordElem = (Element) parentDisabledKeywords
               .item(i);
         final NodeList keywordsList = parentDisabledKeywordElem
               .getChildNodes();
         for (int j = 0; j < keywordsList.getLength(); j++) {
            final IKeyword parentDisabledKeyword = keywordPersistence
                  .readKeyword((Element) keywordsList.item(j));
            profile.setParentKeywordDisabled(parentDisabledKeyword, true);
         }
      }
   }
}
