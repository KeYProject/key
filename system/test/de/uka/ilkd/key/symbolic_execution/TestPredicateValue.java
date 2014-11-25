package de.uka.ilkd.key.symbolic_execution;

import de.uka.ilkd.key.symbolic_execution.PredicateEvaluationUtil.PredicateValue;
import junit.framework.TestCase;

/**
 * Tests for {@link PredicateValue}.
 * @author Martin Hentschel
 */
public class TestPredicateValue extends TestCase {
   /**
    * Tests {@link PredicateValue#and(PredicateValue, PredicateValue)}.
    */
   public void testAnd() {
      // true
      assertEquals(PredicateValue.TRUE, PredicateValue.and(PredicateValue.TRUE, PredicateValue.TRUE));
      assertEquals(PredicateValue.FALSE, PredicateValue.and(PredicateValue.TRUE, PredicateValue.FALSE));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.and(PredicateValue.TRUE, PredicateValue.UNKNOWN));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.and(PredicateValue.TRUE, null));
      // false
      assertEquals(PredicateValue.FALSE, PredicateValue.and(PredicateValue.FALSE, PredicateValue.TRUE));
      assertEquals(PredicateValue.FALSE, PredicateValue.and(PredicateValue.FALSE, PredicateValue.FALSE));
      assertEquals(PredicateValue.FALSE, PredicateValue.and(PredicateValue.FALSE, PredicateValue.UNKNOWN));
      assertEquals(PredicateValue.FALSE, PredicateValue.and(PredicateValue.FALSE, null));
      // unknown
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.and(PredicateValue.UNKNOWN, PredicateValue.TRUE));
      assertEquals(PredicateValue.FALSE, PredicateValue.and(PredicateValue.UNKNOWN, PredicateValue.FALSE));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.and(PredicateValue.UNKNOWN, PredicateValue.UNKNOWN));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.and(PredicateValue.UNKNOWN, null));
      // null
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.and(null, PredicateValue.TRUE));
      assertEquals(PredicateValue.FALSE, PredicateValue.and(null, PredicateValue.FALSE));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.and(null, PredicateValue.UNKNOWN));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.and(null, null));
   }
   
   /**
    * Tests {@link PredicateValue#or(PredicateValue, PredicateValue)}.
    */
   public void testOr() {
      // true
      assertEquals(PredicateValue.TRUE, PredicateValue.or(PredicateValue.TRUE, PredicateValue.TRUE));
      assertEquals(PredicateValue.TRUE, PredicateValue.or(PredicateValue.TRUE, PredicateValue.FALSE));
      assertEquals(PredicateValue.TRUE, PredicateValue.or(PredicateValue.TRUE, PredicateValue.UNKNOWN));
      assertEquals(PredicateValue.TRUE, PredicateValue.or(PredicateValue.TRUE, null));
      // false
      assertEquals(PredicateValue.TRUE, PredicateValue.or(PredicateValue.FALSE, PredicateValue.TRUE));
      assertEquals(PredicateValue.FALSE, PredicateValue.or(PredicateValue.FALSE, PredicateValue.FALSE));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.or(PredicateValue.FALSE, PredicateValue.UNKNOWN));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.or(PredicateValue.FALSE, null));
      // unknown
      assertEquals(PredicateValue.TRUE, PredicateValue.or(PredicateValue.UNKNOWN, PredicateValue.TRUE));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.or(PredicateValue.UNKNOWN, PredicateValue.FALSE));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.or(PredicateValue.UNKNOWN, PredicateValue.UNKNOWN));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.or(PredicateValue.UNKNOWN, null));
      // null
      assertEquals(PredicateValue.TRUE, PredicateValue.or(null, PredicateValue.TRUE));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.or(null, PredicateValue.FALSE));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.or(null, PredicateValue.UNKNOWN));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.or(null, null));
   }
   
   /**
    * Tests {@link PredicateValue#imp(PredicateValue, PredicateValue)}.
    */
   public void testImp() {
      // true
      assertEquals(PredicateValue.TRUE, PredicateValue.imp(PredicateValue.TRUE, PredicateValue.TRUE));
      assertEquals(PredicateValue.FALSE, PredicateValue.imp(PredicateValue.TRUE, PredicateValue.FALSE));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.imp(PredicateValue.TRUE, PredicateValue.UNKNOWN));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.imp(PredicateValue.TRUE, null));
      // false
      assertEquals(PredicateValue.TRUE, PredicateValue.imp(PredicateValue.FALSE, PredicateValue.TRUE));
      assertEquals(PredicateValue.TRUE, PredicateValue.imp(PredicateValue.FALSE, PredicateValue.FALSE));
      assertEquals(PredicateValue.TRUE, PredicateValue.imp(PredicateValue.FALSE, PredicateValue.UNKNOWN));
      assertEquals(PredicateValue.TRUE, PredicateValue.imp(PredicateValue.FALSE, null));
      // unknown
      assertEquals(PredicateValue.TRUE, PredicateValue.imp(PredicateValue.UNKNOWN, PredicateValue.TRUE));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.imp(PredicateValue.UNKNOWN, PredicateValue.FALSE));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.imp(PredicateValue.UNKNOWN, PredicateValue.UNKNOWN));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.imp(PredicateValue.UNKNOWN, null));
      // null
      assertEquals(PredicateValue.TRUE, PredicateValue.imp(null, PredicateValue.TRUE));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.imp(null, PredicateValue.FALSE));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.imp(null, PredicateValue.UNKNOWN));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.imp(null, null));
   }
   
   /**
    * Tests {@link PredicateValue#not(PredicateValue)}.
    */
   public void testNot() {
      assertEquals(PredicateValue.FALSE, PredicateValue.not(PredicateValue.TRUE));
      assertEquals(PredicateValue.TRUE, PredicateValue.not(PredicateValue.FALSE));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.not(PredicateValue.UNKNOWN));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.not(null));
   }
}
