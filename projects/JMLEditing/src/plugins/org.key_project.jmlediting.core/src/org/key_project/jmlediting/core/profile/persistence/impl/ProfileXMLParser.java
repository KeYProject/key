package org.key_project.jmlediting.core.profile.persistence.impl;

import static org.key_project.jmlediting.core.profile.persistence.impl.ProfileXMLConstants.*;

import java.io.IOException;
import java.net.URL;
import java.util.HashSet;
import java.util.Set;

import javax.xml.XMLConstants;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.dom.DOMSource;
import javax.xml.validation.Schema;
import javax.xml.validation.SchemaFactory;
import javax.xml.validation.Validator;

import org.key_project.jmlediting.core.profile.ConfigurableJMLProfile;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.persistence.AbstractProfileXMLParser;
import org.key_project.jmlediting.core.profile.syntax.IJMLBehaviorSpecification;
import org.key_project.jmlediting.core.profile.syntax.IJMLGenericSpecification;
import org.key_project.jmlediting.core.profile.syntax.impl.JMLBehaviorSpecification;
import org.key_project.jmlediting.core.profile.syntax.impl.JMLGenericSpecification;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.InputSource;
import org.xml.sax.SAXException;

public class ProfileXMLParser extends AbstractProfileXMLParser {
   
   
   @Override
   public IJMLProfile parseProfile(InputSource source) throws IOException, SAXException {
      
      try {
         DocumentBuilder builder = DocumentBuilderFactory.newInstance().newDocumentBuilder();
         Document document = builder.parse(source);
         SchemaFactory sf = SchemaFactory.newInstance( XMLConstants.W3C_XML_SCHEMA_NS_URI );
         Schema schema = sf.newSchema(new URL("platform:/plugin/org.key_project.jmlediting.core/resources/jml_profile.xsd"));
         Validator validator = schema.newValidator();
         validator.validate(new DOMSource(document));
         
         Element profile = (Element) ensureSingleElement(document, PROFILE);
         return parseProfile(profile);
      }
      catch (ParserConfigurationException e) {
         throw new IOException(e);
      }
      
   }
   
   protected IJMLProfile parseProfile(Element element)  {
      final ConfigurableJMLProfile profile = new ConfigurableJMLProfile(element.getAttribute(NAME), element.getAttribute(ID));
      for (Node node : new NodeListIterable(element.getElementsByTagName(GENERIC_SPEC))) {
         profile.addSupportGeneric(parseGenericSpecification((Element) node));
      }
      for (Node node : new NodeListIterable(element.getElementsByTagName(BEHAVIOR_SPEC))) {
         profile.addSupportedBehavior(parseBehaviorSpecification((Element) node));
      }
      return profile;
   }
   
   protected IJMLBehaviorSpecification parseBehaviorSpecification(Element element)  {
      Set<String> keywords = new HashSet<String>();
      for (Node node : new NodeListIterable(element.getElementsByTagName(KEYWORD))) {
         keywords.add(parseKeyword((Element) node));
      }  
      return new JMLBehaviorSpecification(keywords);
   }
   
   protected String parseKeyword(Element element) {
      return element.getAttribute(NAME);
   }
   
   protected IJMLGenericSpecification parseGenericSpecification(Element element) {
      String keyword = element.getAttribute(KEYWORD);
      String description = ensureSingleElement(element, DESCRIPTION).getTextContent();
      return new JMLGenericSpecification(keyword, description);
   }
   
   
   private static Node ensureSingleElement(Document elem, String name) {
      NodeList list = elem.getElementsByTagName(name);
      return list.item(0);
   }
   
   private static Node ensureSingleElement(Element elem, String name) {
      NodeList list = elem.getElementsByTagName(name);
      return list.item(0);
   }

  

}
