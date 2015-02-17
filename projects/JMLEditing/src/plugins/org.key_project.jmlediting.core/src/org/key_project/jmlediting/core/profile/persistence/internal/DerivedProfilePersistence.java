package org.key_project.jmlediting.core.profile.persistence.internal;

import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

import org.eclipse.core.runtime.Platform;
import org.key_project.jmlediting.core.profile.DerivedProfile;
import org.key_project.jmlediting.core.profile.IDerivedProfile;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLProfileManagement;
import org.key_project.jmlediting.core.profile.persistence.IDerivedProfilePersistence;
import org.key_project.jmlediting.core.profile.persistence.ProfilePersistenceException;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.core.profile.syntax.UserDefinedKeyword;
import org.osgi.framework.Bundle;
import org.osgi.framework.FrameworkUtil;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;

public class DerivedProfilePersistence implements IDerivedProfilePersistence {

   private static final String CLASS = "class";
   private static final String BUNDLE = "bundle";
   private static final String CODED_KEYWORD = "codedkeyword";
   private static final String USER_DEFINED_KEYWORD = "userkeyword";
   private static final String DISABLED_PARENT_KEYWORDS = "disabledparentkeywords";
   private static final String ADDITONAL_KEYWORDS = "additonalkeywords";
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

   public Element persist(final IKeyword keyword, final Document doc,
         final boolean loadFromParent) throws ProfilePersistenceException {
      if (keyword instanceof UserDefinedKeyword) {
         throw new AssertionError("Cannot be persisted yet.");
      }
      else {
         final Element codedKeywordElem = doc.createElement(CODED_KEYWORD);
         if (!loadFromParent) {
            try {
               keyword.getClass().getConstructor();
            }
            catch (final NoSuchMethodException e) {
               throw new ProfilePersistenceException(
                     "Cannot persist the keyword because it does not contains a "
                           + "nullary constructor and is not located in the parent profile",
                     e);
            }
         }
         final Bundle keywordBundle = FrameworkUtil.getBundle(keyword
               .getClass());
         if (keywordBundle != null && keywordBundle.getSymbolicName() != null) {
            codedKeywordElem.setAttribute(BUNDLE,
                  keywordBundle.getSymbolicName());
         }
         else if (!loadFromParent) {
            throw new ProfilePersistenceException(
                  "Class is not of a bundle but this is requires to persist the keyword");
         }
         codedKeywordElem.setAttribute(CLASS, keyword.getClass().getName());

         return codedKeywordElem;
      }
   }

   public IKeyword readKeyword(final Element elem, final IJMLProfile profile,
         final boolean loadFromParent) throws ProfilePersistenceException {
      final String name = elem.getNodeName();
      if (USER_DEFINED_KEYWORD.equals(name)) {
         throw new AssertionError("Cannot be persisted yet.");
      }
      else if (CODED_KEYWORD.equals(name)) {
         final String keywordClassName = elem.getAttribute(CLASS);
         if ("".equals(keywordClassName)) {
            throw new ProfilePersistenceException(
                  "No keyword class specified for the coded keyword node");
         }
         final String bundleId = elem.getAttribute(BUNDLE);
         final boolean hasBundle = !"".equals(bundleId);
         // Search a keyword of this class
         if (loadFromParent) {
            for (final IKeyword keyword : profile.getSupportedKeywords()) {
               if (keyword.getClass().getName().equals(keywordClassName)) {
                  if (!hasBundle
                        || FrameworkUtil.getBundle(keyword.getClass())
                              .getSymbolicName().equals(bundleId)) {
                     return keyword;
                  }
               }
            }

            throw new ProfilePersistenceException(
                  "No keyword with the given class \"" + keywordClassName
                        + "\""
                        + (hasBundle ? "and bundle \"" + bundleId + "\"" : "")
                        + " was found");
         }
         else {
            // Need to instantiate the class
            try {

               final Class<?> keywordClass;
               if (hasBundle) {
                  keywordClass = Platform.getBundle(bundleId).loadClass(
                        keywordClassName);
               }
               else {
                  throw new ProfilePersistenceException(
                        "Cannot instatiate a keyworword without a bundle");
               }

               final Object newInstance = keywordClass.getConstructor()
                     .newInstance();
               if (!(newInstance instanceof IKeyword)) {
                  throw new ProfilePersistenceException(
                        "Class of keyword does not implement IKeyword");
               }
               return (IKeyword) newInstance;
            }
            catch (final ClassNotFoundException e) {
               throw new ProfilePersistenceException(
                     "Failed to load keyword class \"" + keywordClassName
                           + "\" from bundle \"" + bundleId + "\"", e);
            }
            catch (final NoSuchMethodException e) {
               throw new ProfilePersistenceException(
                     "Keyword class does not contains a nullary constructor", e);
            }
            catch (final Exception e) {
               throw new ProfilePersistenceException(
                     "Failed to instantiate a new keyword instance", e);
            }

         }
      }
      else {
         throw new ProfilePersistenceException(
               "Got illegal profile element with name \"" + name + "\"");
      }
   }

   private void readAdditonalKeywords(final Element profileNode,
         final DerivedProfile profile) throws ProfilePersistenceException {
      final NodeList additonalKeywords = profileNode
            .getElementsByTagName(ADDITONAL_KEYWORDS);
      for (int i = 0; i < additonalKeywords.getLength(); i++) {
         final Element addtionalKeywordElem = (Element) additonalKeywords
               .item(i);
         final NodeList keywordsList = addtionalKeywordElem.getChildNodes();
         for (int j = 0; j < keywordsList.getLength(); j++) {
            final IKeyword addtionalKeyword = this.readKeyword(
                  (Element) keywordsList.item(j), profile, false);
            profile.addKeyword(addtionalKeyword);
         }
      }
   }

   private Element persistAdditionalKeywords(final IDerivedProfile profile,
         final Document doc) throws ProfilePersistenceException {
      if (!profile.getAdditionalKeywords().isEmpty()) {
         final Element additionalKeywordElement = doc
               .createElement(ADDITONAL_KEYWORDS);
         for (final IKeyword additonalKeyword : profile.getAdditionalKeywords()) {

            additionalKeywordElement.appendChild(this.persist(additonalKeyword,
                  doc, false));

         }
         return additionalKeywordElement;
      }
      return null;
   }

   private Element persistDisabledKeywords(final IDerivedProfile profile,
         final Document doc) throws ProfilePersistenceException {
      final Element disabledKeywordElem = doc
            .createElement(DISABLED_PARENT_KEYWORDS);
      for (final IKeyword disabledKeyword : profile.getParentProfile()
            .getSupportedKeywords()) {
         if (profile.isParentKeywordDisabled(disabledKeyword)) {

            disabledKeywordElem.appendChild(this.persist(disabledKeyword, doc,
                  true));

         }
      }
      if (disabledKeywordElem.getChildNodes().getLength() > 0) {
         return disabledKeywordElem;
      }
      return null;
   }

   private void readDisabledKeywords(final Element profileNode,
         final DerivedProfile profile) throws ProfilePersistenceException {
      final NodeList parentDisabledKeywords = profileNode
            .getElementsByTagName(DISABLED_PARENT_KEYWORDS);
      for (int i = 0; i < parentDisabledKeywords.getLength(); i++) {
         final Element parentDisabledKeywordElem = (Element) parentDisabledKeywords
               .item(i);
         final NodeList keywordsList = parentDisabledKeywordElem
               .getChildNodes();
         for (int j = 0; j < keywordsList.getLength(); j++) {
            final IKeyword parentDisabledKeyword = this.readKeyword(
                  (Element) keywordsList.item(j), profile, true);
            profile.setParentKeywordDisabled(parentDisabledKeyword, true);
         }
      }
   }
}
