package org.key_project.jmlediting.core.profile.persistence;

import static org.key_project.jmlediting.core.profile.persistence.JMLProfileXMLConstants.*;

import java.io.IOException;
import java.util.HashSet;
import java.util.Set;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

import org.key_project.jmlediting.core.profile.ConfigurableJMLProfile;
import org.key_project.jmlediting.core.profile.IJMLProfile;
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

public class JMLProfileXMLParser extends AbstractJMLProfileXMLParser {
   
   
   @Override
   public IJMLProfile parseProfile(InputSource source) throws IOException, SAXException, IllegalProfileXMLException {
      
      try {
         DocumentBuilder builder = DocumentBuilderFactory.newInstance().newDocumentBuilder();
         Document document = builder.parse(source);
         Element wrapper = (Element) ensureSingleElement(document, PROFILE_WRAPPER);
         Element profile = (Element) ensureSingleElement(wrapper, PROFILE);
         return parseProfile(profile);
      }
      catch (ParserConfigurationException e) {
         throw new IOException(e);
      }
      
   }
   
   
   protected IJMLProfile parseProfile(Element element) throws IllegalProfileXMLException {
      if (!element.hasAttribute(NAME)) {
         throw new IllegalProfileXMLException("profile definition required name attribute");
      }
      if (!element.hasAttribute(ID)) {
         throw new IllegalProfileXMLException("profile definition required id attribute");
      }
      
      
      final ConfigurableJMLProfile profile = new ConfigurableJMLProfile(element.getAttribute(NAME), element.getAttribute(ID));
      
      for (Node node : new NodeListIterable(element.getElementsByTagName(GENERIC_SPEC))) {
         profile.addSupportGeneric(parseGenericSpecification((Element) node));
      }
      for (Node node : new NodeListIterable(element.getElementsByTagName(BEHAVIOR_SPEC))) {
         profile.addSupportedBehavior(parseBehaviorSpecification((Element) node));
      }
      
      return profile;
   }
   
   protected IJMLBehaviorSpecification parseBehaviorSpecification(Element element) throws IllegalProfileXMLException {
      Set<String> keywords = new HashSet<String>();
      for (Node node : new NodeListIterable(element.getElementsByTagName(KEYWORD))) {
         keywords.add(parseKeyword((Element) node));
      }
      
      return new JMLBehaviorSpecification(keywords);
   }
   
   protected String parseKeyword(Element element) throws IllegalProfileXMLException {
      return element.getAttribute(NAME);
   }
   
   protected IJMLGenericSpecification parseGenericSpecification(Element element) throws IllegalProfileXMLException{
      if (!element.hasAttribute(KEYWORD)) {
         throw new IllegalProfileXMLException("generic_spec definition does not contain the keyword attribute");
      }
      String keyword = element.getAttribute(KEYWORD);
      if (keyword.length() == 0) {
         throw new IllegalProfileXMLException("keyword for generic_spec definition is empty");
      }
      return new JMLGenericSpecification(keyword);
   }
   
   private static Node ensureSingleElement(Element elem, String name) throws IllegalProfileXMLException{
      NodeList list = elem.getElementsByTagName(name);
      if (list.getLength() != 1) {
         throw new IllegalProfileXMLException("Excatly one element of name " + name + " is required");
      }
      return list.item(0);
   }
   
   private static Node ensureSingleElement(Document elem, String name) throws IllegalProfileXMLException{
      NodeList list = elem.getElementsByTagName(name);
      if (list.getLength() != 1) {
         throw new IllegalProfileXMLException("Excatly one element of name " + name + " is required");
      }
      return list.item(0);
   }

  

}
