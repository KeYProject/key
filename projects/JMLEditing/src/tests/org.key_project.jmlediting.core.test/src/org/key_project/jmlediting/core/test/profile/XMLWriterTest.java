package org.key_project.jmlediting.core.test.profile;

import static org.junit.Assert.*;

import java.io.File;
import java.io.IOException;

import org.junit.Test;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLProfileManagement;
import org.key_project.jmlediting.core.profile.persistence.ProfileXMLFactory;
import org.xml.sax.SAXException;

public class XMLWriterTest {

   @Test
   public void testWriteAndReadTest() throws IOException, SAXException {
      File tempFile = File.createTempFile("jmlediting_writer_test", "xml");
      tempFile.deleteOnExit();
      IJMLProfile profile = ProfileXMLFactory.createParser().parseProfile(XMLParserTest.getProfileURI("test_profile1.xml"));
      
      ProfileXMLFactory.createWriter().writeProfile(profile, tempFile);
      
      IJMLProfile profileRead = ProfileXMLFactory.createParser().parseProfile(tempFile);
      
      assertEquals("Profile after reading and writing not equal", profile, profileRead);
   }

}
