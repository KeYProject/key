package de.uka.ilkd.key.utils;

import static org.junit.Assert.fail;

import java.io.File;

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
      File result = IOUtils.getClassLocation(getClass());
      fail();
   }
}
