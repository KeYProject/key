// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.symbolic_execution.util;

import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import junit.framework.TestCase;

/**
 * Tests for {@link EqualsHashCodeResetter}
 * @author Martin Hentschel
 */
public class TestEqualsHashCodeResetter extends TestCase {
   /**
    * Tests {@link EqualsHashCodeResetter#getWrappedElement()}.
    */
   public void testGetWrappedElement() {
      // Create model
      String a1 = "a";
      String a2 = "a";
      String b = "b";
      MyBean a1b = new MyBean(a1);
      MyBean a2b = new MyBean(a2);
      MyBean bb = new MyBean(b);
      EqualsHashCodeResetter<MyBean> a1r = new EqualsHashCodeResetter<MyBean>(a1b);
      EqualsHashCodeResetter<MyBean> a2r = new EqualsHashCodeResetter<MyBean>(a2b);
      EqualsHashCodeResetter<MyBean> a1ar = new EqualsHashCodeResetter<MyBean>(a1b); // Alias of a1r
      EqualsHashCodeResetter<MyBean> br = new EqualsHashCodeResetter<MyBean>(bb);
      EqualsHashCodeResetter<MyBean> nullr = new EqualsHashCodeResetter<MyBean>(null);
      // Test wrapped elements
      assertTrue(a1b == a1r.getWrappedElement());
      assertTrue(a2b == a2r.getWrappedElement());
      assertTrue(a1b == a1ar.getWrappedElement());
      assertTrue(bb == br.getWrappedElement());
      assertTrue(null == nullr.getWrappedElement());
   }
   
   /**
    * Tests {@link EqualsHashCodeResetter#equals(Object)} by direct comparison
    * and used in a {@link LinkedHashSet}.
    */
   public void testEquals() {
      // Create model
      String a1 = "a";
      String a2 = "a";
      String b = "b";
      MyBean a1b = new MyBean(a1);
      MyBean a2b = new MyBean(a2);
      MyBean bb = new MyBean(b);
      EqualsHashCodeResetter<MyBean> a1r = new EqualsHashCodeResetter<MyBean>(a1b);
      EqualsHashCodeResetter<MyBean> a2r = new EqualsHashCodeResetter<MyBean>(a2b);
      EqualsHashCodeResetter<MyBean> a1ar = new EqualsHashCodeResetter<MyBean>(a1b); // Alias of a1r
      EqualsHashCodeResetter<MyBean> br = new EqualsHashCodeResetter<MyBean>(bb);
      EqualsHashCodeResetter<MyBean> nullr = new EqualsHashCodeResetter<MyBean>(null);
      // Test equals on bean
      assertTrue(a1b.equals(a1b));
      assertTrue(a1b.equals(a2b)); // Equals is overwritten
      assertFalse(a1b.equals(bb));
      assertTrue(a2b.equals(a2b));
      assertFalse(a2b.equals(bb));
      assertTrue(bb.equals(bb));
      // Test equals on bean with resetter
      assertFalse(a1b.equals(a1r));
      assertFalse(a1b.equals(a2r));
      assertFalse(a1b.equals(a1ar));
      assertFalse(a1b.equals(br));
      assertFalse(a1b.equals(nullr));
      assertFalse(a2b.equals(a1r));
      assertFalse(a2b.equals(a2r));
      assertFalse(a2b.equals(a1ar));
      assertFalse(a2b.equals(br));
      assertFalse(a2b.equals(nullr));
      assertFalse(bb.equals(a1r));
      assertFalse(bb.equals(a2r));
      assertFalse(bb.equals(a1ar));
      assertFalse(bb.equals(br));
      assertFalse(bb.equals(nullr));
      // Test equals on resetter
      assertTrue(a1r.equals(a1r));
      assertFalse(a1r.equals(a2r)); // Equals is no longer overwritten
      assertTrue(a1r.equals(a1ar));
      assertFalse(a1r.equals(br));
      assertFalse(a1r.equals(nullr));
      assertTrue(a2r.equals(a2r));
      assertFalse(a2r.equals(a1ar));
      assertFalse(a2r.equals(br));
      assertFalse(a2r.equals(nullr));
      assertTrue(a1ar.equals(a1ar));
      assertFalse(a1ar.equals(br));
      assertFalse(a1ar.equals(nullr));
      assertTrue(br.equals(br));
      assertFalse(br.equals(nullr));
      assertTrue(nullr.equals(nullr));
      // Test equals on resetter with bean
      assertFalse(a1r.equals(a1b));
      assertFalse(a1r.equals(a2b));
      assertFalse(a1r.equals(bb));
      assertFalse(a2r.equals(a1b));
      assertFalse(a2r.equals(a2b));
      assertFalse(a2r.equals(bb));
      assertFalse(a1ar.equals(a1b));
      assertFalse(a1ar.equals(a2b));
      assertFalse(a1ar.equals(bb));
      assertFalse(br.equals(a1b));
      assertFalse(br.equals(a2b));
      assertFalse(br.equals(bb));
      assertFalse(nullr.equals(a1b));
      assertFalse(nullr.equals(a2b));
      assertFalse(nullr.equals(bb));
      // Test bean in LinkedHashSet
      Set<MyBean> beanSet = new LinkedHashSet<MyBean>();
      beanSet.add(a1b);
      beanSet.add(a2b); // Replaces existing element a1b
      beanSet.add(bb);
      assertEquals(2, beanSet.size());
      assertTrue(beanSet.contains(a1b));
      assertTrue(beanSet.contains(a2b));
      assertTrue(beanSet.contains(bb));
       // Test resetter in LinkedHashSet
      Set<EqualsHashCodeResetter<MyBean>> set = new LinkedHashSet<EqualsHashCodeResetter<MyBean>>();
      set.add(a1r);
      set.add(a2r);
      set.add(br);
      assertEquals(3, set.size());
      assertTrue(set.contains(a1r));
      assertTrue(set.contains(a2r));
      assertTrue(set.contains(a1ar));
      assertTrue(set.contains(br));
   }
   
   /**
    * Tests {@link EqualsHashCodeResetter#hashCode()} by direct comparison
    * and used in a {@link HashMap}.
    */
   public void testHashCode() {
      // Create model
      String a1 = "a";
      String a2 = "a";
      String b = "b";
      MyBean a1b = new MyBean(a1);
      MyBean a2b = new MyBean(a2);
      MyBean bb = new MyBean(b);
      EqualsHashCodeResetter<MyBean> a1r = new EqualsHashCodeResetter<MyBean>(a1b);
      EqualsHashCodeResetter<MyBean> a2r = new EqualsHashCodeResetter<MyBean>(a2b);
      EqualsHashCodeResetter<MyBean> a1ar = new EqualsHashCodeResetter<MyBean>(a1b); // Alias of a1r
      EqualsHashCodeResetter<MyBean> br = new EqualsHashCodeResetter<MyBean>(bb);
      EqualsHashCodeResetter<MyBean> nullr = new EqualsHashCodeResetter<MyBean>(null);
      // Compare hashcodes on bean
      assertTrue(a1b.hashCode() == a1b.hashCode());
      assertTrue(a1b.hashCode() == a2b.hashCode()); // Hashcode is overwritten
      assertFalse(a1b.hashCode() == bb.hashCode());
      assertTrue(a2b.hashCode() == a2b.hashCode());
      assertFalse(a2b.hashCode() == bb.hashCode());
      assertTrue(bb.hashCode() == bb.hashCode());
      // Compare hashcodes on bean with resetter
      assertFalse(a1b.hashCode() == a1r.hashCode());
      assertFalse(a1b.hashCode() == a2r.hashCode());
      assertFalse(a1b.hashCode() == a1ar.hashCode());
      assertFalse(a1b.hashCode() == br.hashCode());
      assertFalse(a1b.hashCode() == nullr.hashCode());
      assertFalse(a2b.hashCode() == a1r.hashCode());
      assertFalse(a2b.hashCode() == a2r.hashCode());
      assertFalse(a2b.hashCode() == a1ar.hashCode());
      assertFalse(a2b.hashCode() == br.hashCode());
      assertFalse(a2b.hashCode() == nullr.hashCode());
      assertFalse(bb.hashCode() == a1r.hashCode());
      assertFalse(bb.hashCode() == a2r.hashCode());
      assertFalse(bb.hashCode() == a1ar.hashCode());
      assertFalse(bb.hashCode() == br.hashCode());
      assertFalse(bb.hashCode() == nullr.hashCode());
      // Compare hashcodes on resetter
      assertTrue(a1r.hashCode() == a1r.hashCode());
      assertFalse(a1r.hashCode() == a2r.hashCode()); // Hashcode is no longer overwritten
      assertTrue(a1r.hashCode() == a1ar.hashCode());
      assertFalse(a1r.hashCode() == br.hashCode());
      assertFalse(a1r.hashCode() == nullr.hashCode());
      assertTrue(a2r.hashCode() == a2r.hashCode());
      assertFalse(a2r.hashCode() == a1ar.hashCode());
      assertFalse(a2r.hashCode() == br.hashCode());
      assertFalse(a2r.hashCode() == nullr.hashCode());
      assertTrue(a1ar.hashCode() == a1ar.hashCode());
      assertFalse(a1ar.hashCode() == br.hashCode());
      assertFalse(a1ar.hashCode() == nullr.hashCode());
      assertTrue(br.hashCode() == br.hashCode());
      assertFalse(br.hashCode() == nullr.hashCode());
      assertTrue(nullr.hashCode() == nullr.hashCode());
      // Compare hashcodes on resetter with bean
      assertFalse(a1r.hashCode() == a1b.hashCode());
      assertFalse(a1r.hashCode() == a2b.hashCode());
      assertFalse(a1r.hashCode() == bb.hashCode());
      assertFalse(a2r.hashCode() == a1b.hashCode());
      assertFalse(a2r.hashCode() == a2b.hashCode());
      assertFalse(a2r.hashCode() == bb.hashCode());
      assertFalse(a1ar.hashCode() == a1b.hashCode());
      assertFalse(a1ar.hashCode() == a2b.hashCode());
      assertFalse(a1ar.hashCode() == bb.hashCode());
      assertFalse(br.hashCode() == a1b.hashCode());
      assertFalse(br.hashCode() == a2b.hashCode());
      assertFalse(br.hashCode() == bb.hashCode());
      assertFalse(nullr.hashCode() == a1b.hashCode());
      assertFalse(nullr.hashCode() == a2b.hashCode());
      assertFalse(nullr.hashCode() == bb.hashCode());
      // Test bean in HashMap
      Map<MyBean, String> beanMap = new HashMap<MyBean, String>();
      beanMap.put(a1b, "a1rValue");
      beanMap.put(a2b, "a2rValue"); // Overwrites existing value "a1rValue"
      beanMap.put(bb, "brValue");
      assertEquals(beanMap.get(a1b), "a2rValue");
      assertEquals(beanMap.get(a2b), "a2rValue");
      assertEquals(beanMap.get(bb), "brValue");
      // Test resetter in HashMap
      Map<EqualsHashCodeResetter<MyBean>, String> map = new HashMap<EqualsHashCodeResetter<MyBean>, String>();
      map.put(a1r, "a1rValue");
      map.put(a2r, "a2rValue");
      map.put(br, "brValue");
      assertEquals(map.get(a1r), "a1rValue");
      assertEquals(map.get(a2r), "a2rValue");
      assertEquals(map.get(a1ar), "a1rValue");
      assertEquals(map.get(br), "brValue");
   }
   
   /**
    * Utility class used in tests.
    * @author Martin Hentschel
    */
   private static class MyBean {
      /**
       * A value.
       */
      private String value;

      /**
       * Constructor.
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
            return value.equals(((MyBean)obj).value);
         }
         else {
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