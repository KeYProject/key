package org.key_project.util.test.testcase;

import java.util.Map.Entry;

import org.junit.Test;
import org.key_project.util.java.collection.DefaultEntry;

import junit.framework.TestCase;

/**
 * Tests for {@link DefaultEntry}.
 * @author Martin Hentschel
 */
public class DefaultEntryTest extends TestCase {
   /**
    * Tests {@link DefaultEntry#getKey()}, {@link DefaultEntry#getValue()} and
    * {@link DefaultEntry#setValue(Object)}.
    */
   @Test
   public void testGetterAndSetter() {
      Entry<String, String> entry = new DefaultEntry<String, String>("A", "B");
      assertEquals("A", entry.getKey());
      assertEquals("B", entry.getValue());
      entry.setValue("C");
      assertEquals("A", entry.getKey());
      assertEquals("C", entry.getValue());
   }
}
