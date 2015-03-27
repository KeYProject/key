package org.key_project.jmlediting.core.profile.persistence.internal;

import static org.key_project.jmlediting.core.profile.persistence.internal.XMLConstants.ADDITONAL_KEYWORDS;
import static org.key_project.jmlediting.core.profile.persistence.internal.XMLConstants.DERIVED_PROFILE;
import static org.key_project.jmlediting.core.profile.persistence.internal.XMLConstants.DISABLED_PARENT_KEYWORDS;
import static org.key_project.jmlediting.core.profile.persistence.internal.XMLConstants.IDENTIFIER;
import static org.key_project.jmlediting.core.profile.persistence.internal.XMLConstants.NAME;
import static org.key_project.jmlediting.core.profile.persistence.internal.XMLConstants.PARENT_IDENTIFIER;

import java.io.IOException;
import java.io.StringReader;
import java.io.StringWriter;

import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.OutputKeys;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerConfigurationException;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;

import org.key_project.jmlediting.core.profile.DerivedProfile;
import org.key_project.jmlediting.core.profile.IDerivedProfile;
import org.key_project.jmlediting.core.profile.IEditableDerivedProfile;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLProfileManagement;
import org.key_project.jmlediting.core.profile.persistence.IDerivedProfilePersistence;
import org.key_project.jmlediting.core.profile.persistence.ProfilePersistenceException;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;
import org.xml.sax.InputSource;
import org.xml.sax.SAXException;

/**
 * Class implementing the persistence of derived profiles.
 *
 * @author Moritz Lichter
 *
 */
public class DerivedProfilePersistence implements IDerivedProfilePersistence {

   @Override
   public String persist(final IDerivedProfile profile)
         throws ProfilePersistenceException {
      // Create document
      final Document doc;
      try {
         doc = DocumentBuilderFactory.newInstance().newDocumentBuilder()
               .newDocument();
      }
      catch (final ParserConfigurationException e) {
         throw new ProfilePersistenceException(e);
      }

      // Create the top element and store the attributes of the profule
      final Element topElement = doc.createElement(DERIVED_PROFILE);

      topElement.setAttribute(IDENTIFIER, profile.getIdentifier());
      topElement.setAttribute(NAME, profile.getName());
      topElement.setAttribute(PARENT_IDENTIFIER, profile.getParentProfile()
            .getIdentifier());

      // Persist new keywords
      final Element additionalKeywords = this.persistAdditionalKeywords(
            profile, doc);
      if (additionalKeywords != null) {
         topElement.appendChild(additionalKeywords);
      }

      // Remember disabled keywords
      final Element disabledKeywords = this.persistDisabledKeywords(profile,
            doc);
      if (disabledKeywords != null) {
         topElement.appendChild(disabledKeywords);
      }

      doc.appendChild(topElement);
      // Write to string
      try {
         final TransformerFactory tf = TransformerFactory.newInstance();
         final Transformer transformer = tf.newTransformer();
         transformer.setOutputProperty(OutputKeys.OMIT_XML_DECLARATION, "yes");
         final StringWriter writer = new StringWriter();
         transformer.transform(new DOMSource(doc), new StreamResult(writer));
         return writer.toString();
      }
      catch (final TransformerConfigurationException e) {
         throw new ProfilePersistenceException(e);
      }
      catch (final TransformerException e) {
         throw new ProfilePersistenceException(e);
      }

   }

   @Override
   public IDerivedProfile read(final String content)
         throws ProfilePersistenceException {
      Document doc;
      try {
         doc = DocumentBuilderFactory.newInstance().newDocumentBuilder()
               .parse(new InputSource(new StringReader(content)));
      }
      catch (final SAXException e) {
         throw new ProfilePersistenceException("Unable to parse XML", e);
      }
      catch (final IOException e) {
         throw new ProfilePersistenceException(e);
      }
      catch (final ParserConfigurationException e) {
         throw new ProfilePersistenceException(e);
      }
      // Need one top node
      final NodeList topNodes = doc.getElementsByTagName(DERIVED_PROFILE);
      if (topNodes.getLength() != 1) {
         throw new ProfilePersistenceException(
               "Expected exactly one profile but got " + topNodes.getLength());
      }

      // Get the attributes and assert that they are available
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

      // Load the parent profile from the profile Management
      final IJMLProfile parentProfile = JMLProfileManagement.instance()
            .getProfileFromIdentifier(parentIdentifer);
      if (parentProfile == null) {
         throw new ProfilePersistenceException("The parent profile with id \""
               + parentIdentifer + "\" could not be found.");
      }

      // Create a new derived profile
      final IEditableDerivedProfile profile = parentProfile.derive(identifier,
            name);

      // And load additional and disabled keywords
      this.readAdditonalKeywords(profileNode, profile);
      this.readDisabledKeywords(profileNode, profile);

      return profile;
   }

   /**
    * Reads all additional keywords nodes from the given profile nodes and puts
    * them in the given {@link DerivedProfile}.
    *
    * @param profileNode
    *           the profile node
    * @param profile
    *           the destination profile of all additional keywords found
    * @throws ProfilePersistenceException
    *            if a keyword cannot be loaded
    */
   private void readAdditonalKeywords(final Element profileNode,
         final IEditableDerivedProfile profile)
         throws ProfilePersistenceException {
      // Additional keywords need to be instantiated
      final InstantiateKeywordsPersistence keywordPersistence = new InstantiateKeywordsPersistence(
            profile);
      // Get all additional keywords
      final NodeList additonalKeywords = profileNode
            .getElementsByTagName(ADDITONAL_KEYWORDS);
      for (int i = 0; i < additonalKeywords.getLength(); i++) {
         // Each elem may contain many keywords, read them all
         final Element addtionalKeywordElem = (Element) additonalKeywords
               .item(i);
         final NodeList keywordsList = addtionalKeywordElem.getChildNodes();
         for (int j = 0; j < keywordsList.getLength(); j++) {
            // Read the keyword and add them to the profile
            final IKeyword addtionalKeyword = keywordPersistence
                  .readKeyword((Element) keywordsList.item(j));
            profile.addKeyword(addtionalKeyword);
         }
      }
   }

   /**
    * Persists the additional keywords of the given profile in one XML element.
    *
    * @param profile
    *           the profile those additional keywords to persist
    * @param doc
    *           the parent document of the element to create
    * @return the created element or null if no additional keyword was found in
    *         the profile
    * @throws ProfilePersistenceException
    *            if a keyword cannot be persisted
    */
   private Element persistAdditionalKeywords(final IDerivedProfile profile,
         final Document doc) throws ProfilePersistenceException {
      // Dont create an element if there is not keyword
      if (profile.getAdditionalKeywords().isEmpty()) {
         return null;
      }
      // Need to persist the keywords in a way, that they can be instantiated
      // when loading
      final InstantiateKeywordsPersistence keywordPersistence = new InstantiateKeywordsPersistence(
            profile);
      // Persist all keywords
      final Element additionalKeywordElement = doc
            .createElement(ADDITONAL_KEYWORDS);
      for (final IKeyword additonalKeyword : profile.getAdditionalKeywords()) {
         additionalKeywordElement.appendChild(keywordPersistence.persist(
               additonalKeyword, doc));
      }
      return additionalKeywordElement;
   }

   /**
    * Persists all disables keywords of this profile into an XML element.
    *
    * @param profile
    *           the profile those keywords to persist
    * @param doc
    *           the parent document of the element to create
    * @return a element for all disabled keywords or null if there are no such
    *         keywords
    * @throws ProfilePersistenceException
    *            if one of the disabled keywords failed to be persisted
    */
   private Element persistDisabledKeywords(final IDerivedProfile profile,
         final Document doc) throws ProfilePersistenceException {
      // Persist the profiles in a way, that they can be reloaded form the
      // parent profile
      final LoadFromProfileKeywordPersistence keywordPersistence = new LoadFromProfileKeywordPersistence(
            profile);
      // Create an element
      final Element disabledKeywordElem = doc
            .createElement(DISABLED_PARENT_KEYWORDS);
      // Check for each keyword in the parent profile whether it is disabled
      for (final IKeyword disabledKeyword : profile.getParentProfile()
            .getSupportedKeywords()) {
         if (profile.isParentKeywordDisabled(disabledKeyword)) {
            // then persist it
            disabledKeywordElem.appendChild(keywordPersistence.persist(
                  disabledKeyword, doc));
         }
      }
      // If something was persisted, return the element
      if (disabledKeywordElem.getChildNodes().getLength() > 0) {
         return disabledKeywordElem;
      }
      // Otherwise null
      return null;
   }

   /**
    * Reads all disabled keywords from the given profile node and disables them
    * in the given {@link DerivedProfile}.
    *
    * @param profileNode
    *           the profile node to read from
    * @param profile
    *           the profile to disable parent keywords in
    * @throws ProfilePersistenceException
    *            if a keyword could not be loaded
    */
   private void readDisabledKeywords(final Element profileNode,
         final IEditableDerivedProfile profile)
         throws ProfilePersistenceException {
      // The disabled keyword already exists in the parent profile
      final LoadFromProfileKeywordPersistence keywordPersistence = new LoadFromProfileKeywordPersistence(
            profile);
      // Get the nodes for disabled keywords
      final NodeList parentDisabledKeywords = profileNode
            .getElementsByTagName(DISABLED_PARENT_KEYWORDS);
      for (int i = 0; i < parentDisabledKeywords.getLength(); i++) {
         // Each node may contain many disabled keywords, read them all
         final Element parentDisabledKeywordElem = (Element) parentDisabledKeywords
               .item(i);
         final NodeList keywordsList = parentDisabledKeywordElem
               .getChildNodes();
         for (int j = 0; j < keywordsList.getLength(); j++) {
            // Read the keyword and disable it
            final IKeyword parentDisabledKeyword = keywordPersistence
                  .readKeyword((Element) keywordsList.item(j));
            profile.setParentKeywordDisabled(parentDisabledKeyword, true);
         }
      }
   }
}
