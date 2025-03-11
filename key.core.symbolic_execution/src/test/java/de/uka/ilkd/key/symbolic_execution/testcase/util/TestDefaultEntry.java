/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.testcase.util;

import java.util.Map.Entry;

import de.uka.ilkd.key.symbolic_execution.util.DefaultEntry;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Tests for {@link DefaultEntry}.
 *
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
