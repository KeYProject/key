package de.uka.ilkd.key.symbolic_execution.util;

import java.util.Map.Entry;

import junit.framework.TestCase;

/**
 * Tests for {@link DefaultEntry}.
 * @author Martin Hentschel
 */
public class TestDefaultEntry extends TestCase {
   /**
    * Tests {@link DefaultEntry#getKey()}, {@link DefaultEntry#getValue()} and
    * {@link DefaultEntry#setValue(Object)}.
    */
   public void testGetterAndSetter() {
      Entry<String, String> entry = new DefaultEntry<String, String>("A", "B");
      assertEquals("A", entry.getKey());
      assertEquals("B", entry.getValue());
      entry.setValue("C");
      assertEquals("A", entry.getKey());
      assertEquals("C", entry.getValue());
   }
}
