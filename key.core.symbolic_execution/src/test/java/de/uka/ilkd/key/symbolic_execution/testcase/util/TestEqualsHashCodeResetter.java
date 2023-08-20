/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.testcase.util;

import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.symbolic_execution.util.EqualsHashCodeResetter;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests for {@link EqualsHashCodeResetter}
 *
 * @author Martin Hentschel
 */
public class TestEqualsHashCodeResetter {
    /**
     * Tests {@link EqualsHashCodeResetter#getWrappedElement()}.
     */
    @Test
    public void testGetWrappedElement() {
        // Create model
        String a1 = "a";
        String a2 = "a";
        String b = "b";
        MyBean a1b = new MyBean(a1);
        MyBean a2b = new MyBean(a2);
        MyBean bb = new MyBean(b);
        EqualsHashCodeResetter<MyBean> a1r = new EqualsHashCodeResetter<>(a1b);
        EqualsHashCodeResetter<MyBean> a2r = new EqualsHashCodeResetter<>(a2b);
        EqualsHashCodeResetter<MyBean> a1ar = new EqualsHashCodeResetter<>(a1b); // Alias of a1r
        EqualsHashCodeResetter<MyBean> br = new EqualsHashCodeResetter<>(bb);
        EqualsHashCodeResetter<MyBean> nullr = new EqualsHashCodeResetter<>(null);
        // Test wrapped elements
        assertSame(a1b, a1r.getWrappedElement());
        assertSame(a2b, a2r.getWrappedElement());
        assertSame(a1b, a1ar.getWrappedElement());
        assertSame(bb, br.getWrappedElement());
        Assertions.assertNull(nullr.getWrappedElement());
    }

    /**
     * Tests {@link EqualsHashCodeResetter#equals(Object)} by direct comparison and used in a
     * {@link LinkedHashSet}.
     */
    @Test
    public void testEquals() {
        // Create model
        String a1 = "a";
        String a2 = "a";
        String b = "b";
        MyBean a1b = new MyBean(a1);
        MyBean a2b = new MyBean(a2);
        MyBean bb = new MyBean(b);
        EqualsHashCodeResetter<MyBean> a1r = new EqualsHashCodeResetter<>(a1b);
        EqualsHashCodeResetter<MyBean> a2r = new EqualsHashCodeResetter<>(a2b);
        EqualsHashCodeResetter<MyBean> a1ar = new EqualsHashCodeResetter<>(a1b); // Alias of a1r
        EqualsHashCodeResetter<MyBean> br = new EqualsHashCodeResetter<>(bb);
        EqualsHashCodeResetter<MyBean> nullr = new EqualsHashCodeResetter<>(null);
        // Test equals on bean
        assertEquals(a1b, a1b);
        assertEquals(a1b, a2b); // Equals is overwritten
        assertNotEquals(a1b, bb);
        assertEquals(a2b, a2b);
        assertNotEquals(a2b, bb);
        assertEquals(bb, bb);
        // Test equals on bean with resetter
        assertNotEquals(a1b, a1r);
        assertNotEquals(a1b, a2r);
        assertNotEquals(a1b, a1ar);
        assertNotEquals(a1b, br);
        assertNotEquals(a1b, nullr);
        assertNotEquals(a2b, a1r);
        assertNotEquals(a2b, a2r);
        assertNotEquals(a2b, a1ar);
        assertNotEquals(a2b, br);
        assertNotEquals(a2b, nullr);
        assertNotEquals(bb, a1r);
        assertNotEquals(bb, a2r);
        assertNotEquals(bb, a1ar);
        assertNotEquals(bb, br);
        assertNotEquals(bb, nullr);
        // Test equals on resetter
        assertEquals(a1r, a1r);
        assertNotEquals(a1r, a2r); // Equals is no longer overwritten
        assertEquals(a1r, a1ar);
        assertNotEquals(a1r, br);
        assertNotEquals(a1r, nullr);
        assertEquals(a2r, a2r);
        assertNotEquals(a2r, a1ar);
        assertNotEquals(a2r, br);
        assertNotEquals(a2r, nullr);
        assertEquals(a1ar, a1ar);
        assertNotEquals(a1ar, br);
        assertNotEquals(a1ar, nullr);
        assertEquals(br, br);
        assertNotEquals(br, nullr);
        assertEquals(nullr, nullr);
        // Test equals on resetter with bean
        assertNotEquals(a1r, a1b);
        assertNotEquals(a1r, a2b);
        assertNotEquals(a1r, bb);
        assertNotEquals(a2r, a1b);
        assertNotEquals(a2r, a2b);
        assertNotEquals(a2r, bb);
        assertNotEquals(a1ar, a1b);
        assertNotEquals(a1ar, a2b);
        assertNotEquals(a1ar, bb);
        assertNotEquals(br, a1b);
        assertNotEquals(br, a2b);
        assertNotEquals(br, bb);
        assertNotEquals(nullr, a1b);
        assertNotEquals(nullr, a2b);
        assertNotEquals(nullr, bb);
        // Test bean in LinkedHashSet
        Set<MyBean> beanSet = new LinkedHashSet<>();
        beanSet.add(a1b);
        beanSet.add(a2b); // Replaces existing element a1b
        beanSet.add(bb);
        assertEquals(2, beanSet.size());
        Assertions.assertTrue(beanSet.contains(a1b));
        Assertions.assertTrue(beanSet.contains(a2b));
        Assertions.assertTrue(beanSet.contains(bb));
        // Test resetter in LinkedHashSet
        Set<EqualsHashCodeResetter<MyBean>> set = new LinkedHashSet<>();
        set.add(a1r);
        set.add(a2r);
        set.add(br);
        assertEquals(3, set.size());
        Assertions.assertTrue(set.contains(a1r));
        Assertions.assertTrue(set.contains(a2r));
        Assertions.assertTrue(set.contains(a1ar));
        Assertions.assertTrue(set.contains(br));
    }

    /**
     * Tests {@link EqualsHashCodeResetter#hashCode()} by direct comparison and used in a
     * {@link HashMap}.
     */
    @Test
    public void testHashCode() {
        // Create model
        String a1 = "a";
        String a2 = "a";
        String b = "b";
        MyBean a1b = new MyBean(a1);
        MyBean a2b = new MyBean(a2);
        MyBean bb = new MyBean(b);
        EqualsHashCodeResetter<MyBean> a1r = new EqualsHashCodeResetter<>(a1b);
        EqualsHashCodeResetter<MyBean> a2r = new EqualsHashCodeResetter<>(a2b);
        EqualsHashCodeResetter<MyBean> a1ar = new EqualsHashCodeResetter<>(a1b); // Alias of a1r
        EqualsHashCodeResetter<MyBean> br = new EqualsHashCodeResetter<>(bb);
        EqualsHashCodeResetter<MyBean> nullr = new EqualsHashCodeResetter<>(null);
        // Compare hashcodes on bean
        assertEquals(a1b.hashCode(), a1b.hashCode());
        assertEquals(a1b.hashCode(), a2b.hashCode()); // Hashcode is overwritten
        assertNotEquals(a1b.hashCode(), bb.hashCode());
        assertEquals(a2b.hashCode(), a2b.hashCode());
        assertNotEquals(a2b.hashCode(), bb.hashCode());
        assertEquals(bb.hashCode(), bb.hashCode());
        // Compare hashcodes on bean with resetter
        assertNotEquals(a1b.hashCode(), a1r.hashCode());
        assertNotEquals(a1b.hashCode(), a2r.hashCode());
        assertNotEquals(a1b.hashCode(), a1ar.hashCode());
        assertNotEquals(a1b.hashCode(), br.hashCode());
        assertNotEquals(a1b.hashCode(), nullr.hashCode());
        assertNotEquals(a2b.hashCode(), a1r.hashCode());
        assertNotEquals(a2b.hashCode(), a2r.hashCode());
        assertNotEquals(a2b.hashCode(), a1ar.hashCode());
        assertNotEquals(a2b.hashCode(), br.hashCode());
        assertNotEquals(a2b.hashCode(), nullr.hashCode());
        assertNotEquals(bb.hashCode(), a1r.hashCode());
        assertNotEquals(bb.hashCode(), a2r.hashCode());
        assertNotEquals(bb.hashCode(), a1ar.hashCode());
        assertNotEquals(bb.hashCode(), br.hashCode());
        assertNotEquals(bb.hashCode(), nullr.hashCode());
        // Compare hashcodes on resetter
        assertEquals(a1r.hashCode(), a1r.hashCode());
        assertNotEquals(a1r.hashCode(), a2r.hashCode()); // Hashcode is no longer overwritten
        assertEquals(a1r.hashCode(), a1ar.hashCode());
        assertNotEquals(a1r.hashCode(), br.hashCode());
        assertNotEquals(a1r.hashCode(), nullr.hashCode());
        assertEquals(a2r.hashCode(), a2r.hashCode());
        assertNotEquals(a2r.hashCode(), a1ar.hashCode());
        assertNotEquals(a2r.hashCode(), br.hashCode());
        assertNotEquals(a2r.hashCode(), nullr.hashCode());
        assertEquals(a1ar.hashCode(), a1ar.hashCode());
        assertNotEquals(a1ar.hashCode(), br.hashCode());
        assertNotEquals(a1ar.hashCode(), nullr.hashCode());
        assertEquals(br.hashCode(), br.hashCode());
        assertNotEquals(br.hashCode(), nullr.hashCode());
        assertEquals(nullr.hashCode(), nullr.hashCode());
        // Compare hashcodes on resetter with bean
        assertNotEquals(a1r.hashCode(), a1b.hashCode());
        assertNotEquals(a1r.hashCode(), a2b.hashCode());
        assertNotEquals(a1r.hashCode(), bb.hashCode());
        assertNotEquals(a2r.hashCode(), a1b.hashCode());
        assertNotEquals(a2r.hashCode(), a2b.hashCode());
        assertNotEquals(a2r.hashCode(), bb.hashCode());
        assertNotEquals(a1ar.hashCode(), a1b.hashCode());
        assertNotEquals(a1ar.hashCode(), a2b.hashCode());
        assertNotEquals(a1ar.hashCode(), bb.hashCode());
        assertNotEquals(br.hashCode(), a1b.hashCode());
        assertNotEquals(br.hashCode(), a2b.hashCode());
        assertNotEquals(br.hashCode(), bb.hashCode());
        assertNotEquals(nullr.hashCode(), a1b.hashCode());
        assertNotEquals(nullr.hashCode(), a2b.hashCode());
        assertNotEquals(nullr.hashCode(), bb.hashCode());
        // Test bean in HashMap
        Map<MyBean, String> beanMap = new HashMap<>();
        beanMap.put(a1b, "a1rValue");
        beanMap.put(a2b, "a2rValue"); // Overwrites existing value "a1rValue"
        beanMap.put(bb, "brValue");
        assertEquals("a2rValue", beanMap.get(a1b));
        assertEquals("a2rValue", beanMap.get(a2b));
        assertEquals("brValue", beanMap.get(bb));
        // Test resetter in HashMap
        Map<EqualsHashCodeResetter<MyBean>, String> map = new HashMap<>();
        map.put(a1r, "a1rValue");
        map.put(a2r, "a2rValue");
        map.put(br, "brValue");
        assertEquals("a1rValue", map.get(a1r));
        assertEquals("a2rValue", map.get(a2r));
        assertEquals("a1rValue", map.get(a1ar));
        assertEquals("brValue", map.get(br));
    }

    /**
     * Utility class used in tests.
     *
     * @author Martin Hentschel
     */
    private static class MyBean {
        /**
         * A value.
         */
        private final String value;

        /**
         * Constructor.
         *
         * @param value A value.
         */
        public MyBean(String value) {
            assertNotNull(value);
            this.value = value;
        }

        /**
         * Overwritten to make {@link MyBean}s equal if they have the same value.
         */
        @Override
        public boolean equals(Object obj) {
            if (obj instanceof MyBean) {
                return value.equals(((MyBean) obj).value);
            } else {
                return false;
            }
        }

        /**
         * Overwritten to make {@link MyBean}s equal if they have the same value.
         */
        @Override
        public int hashCode() {
            return value.hashCode();
        }
    }
}
