package org.key_project.jmlediting.profile.key.test.locset;

import static org.junit.Assert.fail;

import org.junit.Test;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.test.parser.ParserTestUtils;
import org.key_project.jmlediting.core.test.parser.StoreRefParserTest;
import org.key_project.jmlediting.profile.key.locset.LocSetExprListParser;
import org.key_project.jmlediting.profile.key.test.KeyProfileTestUtils;

public class LocSetExprTest extends StoreRefParserTest {

   @Override
   protected ParseFunction createParser(final boolean allowInformal) {
      return new LocSetExprListParser(KeyProfileTestUtils.keyProfile());
   }

   @Override
   public void testParseInformalDescription() throws ParserException {
      // No informals in key
   }

   @Test
   public void testEmpty() {
      this.testParse("\\empty");
   }

   @Test
   public void testEverything() {
      this.testParse("\\everything");
   }

   @Test
   public void testIntersect() {
      this.testParse("\\intersect(this.x, y[*])");
   }

   @Test
   public void testSetUnion() {
      this.testParse("\\set_union(me.get.*, \\everything)");
   }

   @Test
   public void testSetMinus() {
      this.testParse("\\set_minus(\\everything, a.b.c.d)");
   }

   @Test
   public void testInfiniteUnion() {
      this.testParse("\\infinite_union( int i; i > 2; x[i%10])");
   }

   @Test
   public void testInfiniteUnionNoBool() {
      this.testParse("\\infinite_union( String s; a)");
   }

   @Test
   public void testReachLocs() {
      this.testParse(" \\reachLocs( test, test.get(), 5 +4 )");
   }

   @Test
   public void testReachLocsNoInt() {
      this.testParse("\\reachLocs( a, a[4].foo() )");
   }

   @Test
   public void testComposed1() {
      this.testParse("\\set_minus( \\infinite_union( int i; i > 0 <==> b; a[i]) , \\everything)");
   }

   @Test
   public void testComposed2() {
      this.testParse("\\set_union( \\intersect(\\everything, x) , a[3 .. g.max()])");
   }

   @Test
   public void testParseList() {
      this.testParse("\\empty, this.x, any[*], \\set_union(x , t) , a");
   }

   @Test
   public void testRejectEmptyList() {
      this.testWrongParse("  ");
   }

   public void testParse(final String text) {
      try {
         ParserTestUtils.testParseComplete(text, this.createParser(false));
      }
      catch (final ParserException e) {
         fail(e.getMessage());
      }
   }
}
