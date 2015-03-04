package org.key_project.jmlediting.core.profile.persistence.internal;

import static org.key_project.jmlediting.core.profile.persistence.internal.DerivedProfilePersistence.CLASS_REFERENCE;
import static org.key_project.jmlediting.core.profile.persistence.internal.DerivedProfilePersistence.CLOSING_CHARACTER;
import static org.key_project.jmlediting.core.profile.persistence.internal.DerivedProfilePersistence.CODED_KEYWORD;
import static org.key_project.jmlediting.core.profile.persistence.internal.DerivedProfilePersistence.CONTENT_DESCRIPTION_ID;
import static org.key_project.jmlediting.core.profile.persistence.internal.DerivedProfilePersistence.DESCRIPTION;
import static org.key_project.jmlediting.core.profile.persistence.internal.DerivedProfilePersistence.KEYWORD;
import static org.key_project.jmlediting.core.profile.persistence.internal.DerivedProfilePersistence.SORT;
import static org.key_project.jmlediting.core.profile.persistence.internal.DerivedProfilePersistence.USER_DEFINED_KEYWORD;

import java.util.HashSet;
import java.util.Set;

import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLProfileHelper;
import org.key_project.jmlediting.core.profile.persistence.ProfilePersistenceException;
import org.key_project.jmlediting.core.profile.syntax.AbstractKeywordSort;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywortSort;
import org.key_project.jmlediting.core.profile.syntax.user.IUserDefinedKeyword;
import org.key_project.jmlediting.core.profile.syntax.user.IUserDefinedKeywordContentDescription;
import org.key_project.jmlediting.core.profile.syntax.user.UserDefinedKeyword;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;

public abstract class KeywordPersistence {

   private final IJMLProfile profile;

   public KeywordPersistence(final IJMLProfile profile) {
      super();
      this.profile = profile;
   }

   protected IJMLProfile getProfile() {
      return this.profile;
   }

   public Element persist(final IKeyword keyword, final Document doc)
         throws ProfilePersistenceException {
      if (keyword instanceof IUserDefinedKeyword) {
         return this.persistUserDefinedKeyword((IUserDefinedKeyword) keyword,
               doc);
      }
      else {
         this.validateKeywordToPersist(keyword);
         final Element codedKeywordElem = doc.createElement(CODED_KEYWORD);

         final Element keywordClassElement = new ClassReferencePersistence()
               .persistClassReference(keyword.getClass(), doc);
         codedKeywordElem.appendChild(keywordClassElement);

         return codedKeywordElem;
      }
   }

   protected abstract void validateKeywordToPersist(IKeyword keyword)
         throws ProfilePersistenceException;

   protected abstract IKeyword loadKeyword(
         Class<? extends IKeyword> keywordClass)
         throws ProfilePersistenceException;

   public IKeyword readKeyword(final Element elem)
         throws ProfilePersistenceException {
      final String name = elem.getNodeName();
      if (USER_DEFINED_KEYWORD.equals(name)) {
         return this.loadUserDefinedKeyword(elem);
      }
      else if (CODED_KEYWORD.equals(name)) {

         final NodeList keywordElems = elem
               .getElementsByTagName(CLASS_REFERENCE);
         if (keywordElems.getLength() != 1) {
            throw new ProfilePersistenceException(
                  "Expected excatly one class reference for a coded keyword");
         }
         final Element classElem = (Element) keywordElems.item(0);

         final Class<? extends IKeyword> keywordClass = new ClassReferencePersistence()
               .loadClassReference(classElem, IKeyword.class);
         return this.loadKeyword(keywordClass);
      }
      else {
         throw new ProfilePersistenceException(
               "Got illegal profile element with name \"" + name + "\"");
      }
   }

   private Element persistUserDefinedKeyword(
         final IUserDefinedKeyword userKeyword, final Document doc) {
      final Element userDefinedKeywordElem = doc
            .createElement(USER_DEFINED_KEYWORD);

      userDefinedKeywordElem.setAttribute(CONTENT_DESCRIPTION_ID, userKeyword
            .getContentDescription().getId());
      if (userKeyword.getClosingCharacter() != null) {
         userDefinedKeywordElem.setAttribute(CLOSING_CHARACTER, userKeyword
               .getClosingCharacter().toString());
      }
      final Element descriptionElement = doc.createElement(DESCRIPTION);
      descriptionElement.appendChild(doc.createTextNode(userKeyword
            .getDescription()));
      userDefinedKeywordElem.appendChild(descriptionElement);

      for (final String keywordString : userKeyword.getKeywords()) {
         final Element keywordElement = doc.createElement(KEYWORD);
         keywordElement.appendChild(doc.createTextNode(keywordString));
         userDefinedKeywordElem.appendChild(keywordElement);
      }

      final Element keywordSortElement = doc.createElement(SORT);
      keywordSortElement.appendChild(new ClassReferencePersistence()
            .persistClassReference(userKeyword.getSort().getClass(), doc));

      userDefinedKeywordElem.appendChild(keywordSortElement);

      return userDefinedKeywordElem;
   }

   private IKeyword loadUserDefinedKeyword(final Element elem)
         throws ProfilePersistenceException {
      final String descriptionID = elem.getAttribute(CONTENT_DESCRIPTION_ID);
      if ("".equals(descriptionID)) {
         throw new ProfilePersistenceException(
               "No content description of for user defined keyword");
      }

      String description = null;
      final Set<String> keywords = new HashSet<String>();
      IKeywortSort sort = null;

      final NodeList children = elem.getChildNodes();
      System.err.println("Num children: " + children.getLength());
      for (int i = 0; i < children.getLength(); i++) {
         if (!(children.item(i) instanceof Element)) {
            throw new ProfilePersistenceException("Unexpected content "
                  + children.item(i).getNodeName());
         }
         final Element cElem = (Element) children.item(i);

         System.err.println(elem.getTagName());
         if (cElem.getNodeName().equals(DESCRIPTION)) {
            if (description == null) {
               description = cElem.getFirstChild().getTextContent();// .getNodeValue();
            }
            else {
               throw new ProfilePersistenceException(
                     "Duplicate description node");
            }
         }
         else if (cElem.getNodeName().equals(KEYWORD)) {
            keywords.add(cElem.getFirstChild().getTextContent());
         }
         else if (cElem.getNodeName().equals(SORT)) {
            if (sort == null) {
               final NodeList classNodes = cElem
                     .getElementsByTagName(CLASS_REFERENCE);
               if (classNodes.getLength() != 1) {
                  throw new ProfilePersistenceException(
                        "Expected one class reference for a sort");
               }
               final Class<? extends IKeywortSort> sortClass = new ClassReferencePersistence()
                     .loadClassReference((Element) classNodes.item(0),
                           IKeywortSort.class);
               sort = AbstractKeywordSort.getSortObject(sortClass);
            }
         }
         else {
            throw new ProfilePersistenceException("Unsupported element: "
                  + cElem.getNodeName());
         }
      }

      if (keywords.isEmpty()) {
         throw new ProfilePersistenceException(
               "Found no keyword UserDefinedKeyword");
      }
      if (description == null) {
         throw new ProfilePersistenceException(
               "No description found for UserDefinedKeyword");
      }
      if (sort == null) {
         throw new ProfilePersistenceException(
               "No sort found for UserDefinedKeyword");
      }

      Character closingCharacter = null;
      if (elem.hasAttribute(CLOSING_CHARACTER)) {
         final String closingCharacterString = elem
               .getAttribute(CLOSING_CHARACTER);
         if (closingCharacterString.length() != 1) {
            throw new ProfilePersistenceException(
                  "Closing character attribute is not excatly one char long");
         }
         closingCharacter = closingCharacterString.charAt(0);
      }

      final IUserDefinedKeywordContentDescription descr = JMLProfileHelper
            .getDescriptionById(descriptionID, this.profile);
      if (descr == null) {
         throw new ProfilePersistenceException(
               "Content for UserDefinedKeyword with id \"" + descriptionID
                     + "\" was not found.");
      }

      return new UserDefinedKeyword(keywords, sort, descr, description,
            closingCharacter);
   }
}
