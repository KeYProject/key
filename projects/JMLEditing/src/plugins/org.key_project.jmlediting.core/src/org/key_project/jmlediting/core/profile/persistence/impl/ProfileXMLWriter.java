package org.key_project.jmlediting.core.profile.persistence.impl;

import static org.key_project.jmlediting.core.profile.persistence.impl.ProfileXMLConstants.BEHAVIOR_SPEC;
import static org.key_project.jmlediting.core.profile.persistence.impl.ProfileXMLConstants.DESCRIPTION;
import static org.key_project.jmlediting.core.profile.persistence.impl.ProfileXMLConstants.GENERIC_SPEC;
import static org.key_project.jmlediting.core.profile.persistence.impl.ProfileXMLConstants.ID;
import static org.key_project.jmlediting.core.profile.persistence.impl.ProfileXMLConstants.KEYWORD;
import static org.key_project.jmlediting.core.profile.persistence.impl.ProfileXMLConstants.NAME;
import static org.key_project.jmlediting.core.profile.persistence.impl.ProfileXMLConstants.PROFILE;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;

import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.persistence.AbstractProfileXMLWriter;
import org.key_project.jmlediting.core.profile.syntax.IJMLBehaviorSpecification;
import org.key_project.jmlediting.core.profile.syntax.IJMLGenericSpecification;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

public class ProfileXMLWriter extends AbstractProfileXMLWriter {

   @Override
   public void writeProfile(IJMLProfile profile, StreamResult result) {
      try {
         DocumentBuilder documentBuilder = DocumentBuilderFactory.newInstance()
               .newDocumentBuilder();
         Document document = documentBuilder.newDocument();
         Element profileElem = writeProfile(profile, document);
         document.appendChild(profileElem);
         // write the content into xml file
         TransformerFactory transformerFactory = TransformerFactory
               .newInstance();
         Transformer transformer = transformerFactory.newTransformer();
         DOMSource source = new DOMSource(document);

         transformer.transform(source, new StreamResult(System.out));
         transformer.transform(source, result);
      }
      catch (ParserConfigurationException e) {
         // TODO Auto-generated catch block
         e.printStackTrace();
      }
      catch (TransformerException e) {
         // TODO Auto-generated catch block
         e.printStackTrace();
      }
   }

   private Element writeProfile(IJMLProfile profile, Document doc) {
      Element elem = doc.createElement(PROFILE);
      elem.setAttribute(NAME, profile.getName());
      elem.setAttribute(ID, profile.getIdentifier());

      for (IJMLBehaviorSpecification bSpec : profile.getSupportedBehaviors()) {
         elem.appendChild(writeBehaviorSpecification(bSpec, doc));
      }
      
      for (IJMLGenericSpecification gSpec : profile.getSupportedGenerics()) {
         elem.appendChild(writeGenericSpecification(gSpec, doc));
      }

      return elem;
   }

   private Element writeGenericSpecification(IJMLGenericSpecification gSpec,
         Document doc) {
      Element elem = doc.createElement(GENERIC_SPEC);
      elem.setAttribute(KEYWORD, gSpec.getKeyword());
      Element desciption = doc.createElement(DESCRIPTION);
      desciption.setTextContent(gSpec.getDescription());
      elem.appendChild(desciption);
      return elem;
   }

   private Element writeBehaviorSpecification(IJMLBehaviorSpecification bSpec,
         Document doc) {
      Element elem = doc.createElement(BEHAVIOR_SPEC);
      for (String keyword : bSpec.getKeywords()) {
         Element keywordElem = doc.createElement(KEYWORD);
         keywordElem.setAttribute(NAME, keyword);
         elem.appendChild(keywordElem);
      }
      return elem;
   }

}
