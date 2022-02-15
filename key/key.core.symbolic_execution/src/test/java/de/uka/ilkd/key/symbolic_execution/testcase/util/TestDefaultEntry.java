// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.symbolic_execution.testcase.util;

import de.uka.ilkd.key.symbolic_execution.util.DefaultEntry;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

import java.util.Map.Entry;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Tests for {@link DefaultEntry}.
 * @author Martin Hentschel
 */
public class TestDefaultEntry {
   /**
    * Tests {@link DefaultEntry#getKey()}, {@link DefaultEntry#getValue()} and
    * {@link DefaultEntry#setValue(Object)}.
    */
   @Test
   public void testGetterAndSetter() {
      Entry<String, String> entry = new DefaultEntry<>("A", "B");
      assertEquals("A", entry.getKey());
      assertEquals("B", entry.getValue());
      entry.setValue("C");
      assertEquals("A", entry.getKey());
      assertEquals("C", entry.getValue());
   }
}