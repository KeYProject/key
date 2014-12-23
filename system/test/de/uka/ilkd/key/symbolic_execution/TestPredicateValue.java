package de.uka.ilkd.key.symbolic_execution;

import de.uka.ilkd.key.symbolic_execution.PredicateEvaluationUtil.PredicateValue;
import junit.framework.TestCase;

/**
 * Tests for {@link PredicateValue}.
 * @author Martin Hentschel
 */
public class TestPredicateValue extends TestCase {
   /**
    * Tests {@link PredicateValue#ifThenElse(PredicateValue, PredicateValue, PredicateValue)}.
    */
   public void testIfThenElse() {
      // true
      assertEquals(PredicateValue.TRUE, PredicateValue.ifThenElse(PredicateValue.TRUE, PredicateValue.TRUE, PredicateValue.TRUE));
      assertEquals(PredicateValue.TRUE, PredicateValue.ifThenElse(PredicateValue.TRUE, PredicateValue.TRUE, PredicateValue.FALSE));
      assertEquals(PredicateValue.TRUE, PredicateValue.ifThenElse(PredicateValue.TRUE, PredicateValue.TRUE, PredicateValue.UNKNOWN));
      assertEquals(PredicateValue.TRUE, PredicateValue.ifThenElse(PredicateValue.TRUE, PredicateValue.TRUE, null));
      assertEquals(PredicateValue.FALSE, PredicateValue.ifThenElse(PredicateValue.TRUE, PredicateValue.FALSE, PredicateValue.TRUE));
      assertEquals(PredicateValue.FALSE, PredicateValue.ifThenElse(PredicateValue.TRUE, PredicateValue.FALSE, PredicateValue.FALSE));
      assertEquals(PredicateValue.FALSE, PredicateValue.ifThenElse(PredicateValue.TRUE, PredicateValue.FALSE, PredicateValue.UNKNOWN));
      assertEquals(PredicateValue.FALSE, PredicateValue.ifThenElse(PredicateValue.TRUE, PredicateValue.FALSE, null));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.ifThenElse(PredicateValue.TRUE, PredicateValue.UNKNOWN, PredicateValue.TRUE));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.ifThenElse(PredicateValue.TRUE, PredicateValue.UNKNOWN, PredicateValue.FALSE));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.ifThenElse(PredicateValue.TRUE, PredicateValue.UNKNOWN, PredicateValue.UNKNOWN));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.ifThenElse(PredicateValue.TRUE, PredicateValue.UNKNOWN, null));
      assertEquals(null, PredicateValue.ifThenElse(PredicateValue.TRUE, null, PredicateValue.TRUE));
      assertEquals(null, PredicateValue.ifThenElse(PredicateValue.TRUE, null, PredicateValue.FALSE));
      assertEquals(null, PredicateValue.ifThenElse(PredicateValue.TRUE, null, PredicateValue.UNKNOWN));
      assertEquals(null, PredicateValue.ifThenElse(PredicateValue.TRUE, null, null));
      // false
      assertEquals(PredicateValue.TRUE, PredicateValue.ifThenElse(PredicateValue.FALSE, PredicateValue.TRUE, PredicateValue.TRUE));
      assertEquals(PredicateValue.FALSE, PredicateValue.ifThenElse(PredicateValue.FALSE, PredicateValue.TRUE, PredicateValue.FALSE));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.ifThenElse(PredicateValue.FALSE, PredicateValue.TRUE, PredicateValue.UNKNOWN));
      assertEquals(null, PredicateValue.ifThenElse(PredicateValue.FALSE, PredicateValue.TRUE, null));
      assertEquals(PredicateValue.TRUE, PredicateValue.ifThenElse(PredicateValue.FALSE, PredicateValue.FALSE, PredicateValue.TRUE));
      assertEquals(PredicateValue.FALSE, PredicateValue.ifThenElse(PredicateValue.FALSE, PredicateValue.FALSE, PredicateValue.FALSE));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.ifThenElse(PredicateValue.FALSE, PredicateValue.FALSE, PredicateValue.UNKNOWN));
      assertEquals(null, PredicateValue.ifThenElse(PredicateValue.FALSE, PredicateValue.FALSE, null));
      assertEquals(PredicateValue.TRUE, PredicateValue.ifThenElse(PredicateValue.FALSE, PredicateValue.UNKNOWN, PredicateValue.TRUE));
      assertEquals(PredicateValue.FALSE, PredicateValue.ifThenElse(PredicateValue.FALSE, PredicateValue.UNKNOWN, PredicateValue.FALSE));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.ifThenElse(PredicateValue.FALSE, PredicateValue.UNKNOWN, PredicateValue.UNKNOWN));
      assertEquals(null, PredicateValue.ifThenElse(PredicateValue.FALSE, PredicateValue.UNKNOWN, null));
      assertEquals(PredicateValue.TRUE, PredicateValue.ifThenElse(PredicateValue.FALSE, null, PredicateValue.TRUE));
      assertEquals(PredicateValue.FALSE, PredicateValue.ifThenElse(PredicateValue.FALSE, null, PredicateValue.FALSE));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.ifThenElse(PredicateValue.FALSE, null, PredicateValue.UNKNOWN));
      assertEquals(null, PredicateValue.ifThenElse(PredicateValue.FALSE, null, null));
      // unknown
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.ifThenElse(PredicateValue.UNKNOWN, PredicateValue.TRUE, PredicateValue.TRUE));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.ifThenElse(PredicateValue.UNKNOWN, PredicateValue.TRUE, PredicateValue.FALSE));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.ifThenElse(PredicateValue.UNKNOWN, PredicateValue.TRUE, PredicateValue.UNKNOWN));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.ifThenElse(PredicateValue.UNKNOWN, PredicateValue.TRUE, null));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.ifThenElse(PredicateValue.UNKNOWN, PredicateValue.FALSE, PredicateValue.TRUE));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.ifThenElse(PredicateValue.UNKNOWN, PredicateValue.FALSE, PredicateValue.FALSE));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.ifThenElse(PredicateValue.UNKNOWN, PredicateValue.FALSE, PredicateValue.UNKNOWN));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.ifThenElse(PredicateValue.UNKNOWN, PredicateValue.FALSE, null));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.ifThenElse(PredicateValue.UNKNOWN, PredicateValue.UNKNOWN, PredicateValue.TRUE));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.ifThenElse(PredicateValue.UNKNOWN, PredicateValue.UNKNOWN, PredicateValue.FALSE));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.ifThenElse(PredicateValue.UNKNOWN, PredicateValue.UNKNOWN, PredicateValue.UNKNOWN));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.ifThenElse(PredicateValue.UNKNOWN, PredicateValue.UNKNOWN, null));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.ifThenElse(PredicateValue.UNKNOWN, null, PredicateValue.TRUE));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.ifThenElse(PredicateValue.UNKNOWN, null, PredicateValue.FALSE));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.ifThenElse(PredicateValue.UNKNOWN, null, PredicateValue.UNKNOWN));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.ifThenElse(PredicateValue.UNKNOWN, null, null));
      // null
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.ifThenElse(null, PredicateValue.TRUE, PredicateValue.TRUE));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.ifThenElse(null, PredicateValue.TRUE, PredicateValue.FALSE));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.ifThenElse(null, PredicateValue.TRUE, PredicateValue.UNKNOWN));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.ifThenElse(null, PredicateValue.TRUE, null));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.ifThenElse(null, PredicateValue.FALSE, PredicateValue.TRUE));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.ifThenElse(null, PredicateValue.FALSE, PredicateValue.FALSE));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.ifThenElse(null, PredicateValue.FALSE, PredicateValue.UNKNOWN));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.ifThenElse(null, PredicateValue.FALSE, null));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.ifThenElse(null, PredicateValue.UNKNOWN, PredicateValue.TRUE));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.ifThenElse(null, PredicateValue.UNKNOWN, PredicateValue.FALSE));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.ifThenElse(null, PredicateValue.UNKNOWN, PredicateValue.UNKNOWN));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.ifThenElse(null, PredicateValue.UNKNOWN, null));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.ifThenElse(null, null, PredicateValue.TRUE));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.ifThenElse(null, null, PredicateValue.FALSE));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.ifThenElse(null, null, PredicateValue.UNKNOWN));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.ifThenElse(null, null, null));
   }
   
   /**
    * Tests {@link PredicateValue#eqv(PredicateValue, PredicateValue)}.
    */
   public void testEqv() {
      // true
      assertEquals(PredicateValue.TRUE, PredicateValue.eqv(PredicateValue.TRUE, PredicateValue.TRUE));
      assertEquals(PredicateValue.FALSE, PredicateValue.eqv(PredicateValue.TRUE, PredicateValue.FALSE));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.eqv(PredicateValue.TRUE, PredicateValue.UNKNOWN));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.eqv(PredicateValue.TRUE, null));
      // false
      assertEquals(PredicateValue.FALSE, PredicateValue.eqv(PredicateValue.FALSE, PredicateValue.TRUE));
      assertEquals(PredicateValue.TRUE, PredicateValue.eqv(PredicateValue.FALSE, PredicateValue.FALSE));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.eqv(PredicateValue.FALSE, PredicateValue.UNKNOWN));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.eqv(PredicateValue.FALSE, null));
      // unknown
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.eqv(PredicateValue.UNKNOWN, PredicateValue.TRUE));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.eqv(PredicateValue.UNKNOWN, PredicateValue.FALSE));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.eqv(PredicateValue.UNKNOWN, PredicateValue.UNKNOWN));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.eqv(PredicateValue.UNKNOWN, null));
      // null
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.eqv(null, PredicateValue.TRUE));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.eqv(null, PredicateValue.FALSE));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.eqv(null, PredicateValue.UNKNOWN));
      assertEquals(PredicateValue.UNKNOWN, PredicateValue.eqv(null, null));
   }
   
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
