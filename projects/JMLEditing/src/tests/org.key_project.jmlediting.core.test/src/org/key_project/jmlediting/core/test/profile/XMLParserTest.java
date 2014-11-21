package org.key_project.jmlediting.core.test.profile;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.io.IOException;
import java.net.MalformedURLException;
import java.net.URI;
import java.util.Arrays;
import java.util.HashSet;

import org.junit.Test;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.persistence.IJMLProfileXMLParser;
import org.key_project.jmlediting.core.profile.persistence.JMLProfileXMLParserFactory;
import org.key_project.jmlediting.core.profile.syntax.IJMLBehaviorSpecification;
import org.key_project.jmlediting.core.profile.syntax.IJMLGenericSpecification;
import org.xml.sax.SAXException;

public class XMLParserTest {

   private static URI getProfileURI(String name) {
      try {
         return new URI("platform:/plugin/org.key_project.jmlediting.core.test/resources/" + name);
      } catch (Exception e) {
         throw new RuntimeException(e);
      }
   }
   
   @Test
   public void testParseProfile() throws MalformedURLException, IOException, SAXException {
      IJMLProfileXMLParser parser = JMLProfileXMLParserFactory.createParser();
      IJMLProfile profile = parser.parseProfile(getProfileURI("test_profile1.xml"));
      
      // Now assert the content
      assertEquals("Wrong profile name", "TestProfile1", profile.getName());
      assertEquals("Wrong identifier", "org.key_project.jmlediting.core.test.profile1", profile.getIdentifier());
      assertTrue("Wrong number of supported Behaviors", profile.getSupportedBehaviors().size() == 1);
      assertTrue("Wrong number of supported Generics", profile.getSupportedGenerics().size() == 1);
      
      // Look deeper
      IJMLBehaviorSpecification bSpec = profile.getSupportedBehaviors().iterator().next();
      assertEquals("Wrong supported behavior keywords", new HashSet<String>(bSpec.getKeywords()), new HashSet<String>(Arrays.asList("behavior", "behaviour")));
      IJMLGenericSpecification gSpec = profile.getSupportedGenerics().iterator().next();
      assertEquals("Wrong supported generic keyword", "ensures", gSpec.getKeyword());
      assertEquals("Wrong description", "ensures description", gSpec.getDescription());
   }
   
   @Test(expected=SAXException.class)
   public void testParseWrongProfile() throws MalformedURLException, IOException, SAXException {
      JMLProfileXMLParserFactory.createParser().parseProfile(getProfileURI("wrong_profile.xml"));
   }

}
