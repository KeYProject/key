package de.uka.ilkd.key.utils;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.fail;

import java.net.MalformedURLException;
import java.net.URI;
import java.net.URL;

import org.junit.Test;

/**
 * Tests for {@link IOUtils}.
 * @author Martin Hentschel
 *
 */
public class TestIOUtils {
   /**
    * Tests {@link IOUtils#getClassLocation(Class)}
    */
   @Test
   public void testGetClassLocation() {
      assertNull(IOUtils.getClassLocation(null));
      assertNotNull(IOUtils.getClassLocation(getClass()));
   }
   
   /**
    * Tests {@link IOUtils#getProjectRoot(Class)}
    */
   @Test
   public void testGetProjectRoot() {
      assertNull(IOUtils.getProjectRoot(null));
      assertNotNull(IOUtils.getProjectRoot(getClass()));
   }
   
   /**
    * Tests {@link IOUtils#toURI(java.net.URL)}
    * @throws MalformedURLException Occurred Exception
    */
   @Test
   public void testToURI() throws MalformedURLException {
      assertNull(IOUtils.toURI(null));
      URL url = new URL("https://www.google.de");
      URI uri = IOUtils.toURI(url);
      assertNotNull(uri);
      assertEquals(URI.create("https://www.google.de"), uri);
   }
   
   /**
    * Tests {@link IOUtils#toFile(URL)}
    */
   @Test
   public void testToFile() {
      fail();
   }
   
   /**
    * Tests {@link IOUtils#toFileString(URL)}
    */
   @Test
   public void testToFileString() {
      fail();
   }
}
