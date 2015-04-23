package org.key_project.jmlediting.profile.key.test.locset;

import static org.junit.Assert.fail;

import org.junit.Test;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.test.utilities.ParserTestUtils;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionParser;
import org.key_project.jmlediting.profile.key.test.utilities.JMLEditingKeYProfileTestUtils;

public class LocSetExprTest {

   protected ParseFunction createParser(final boolean allowInformal) {
      return new ExpressionParser(JMLEditingKeYProfileTestUtils.keyProfile()).exprList();
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
      this.testParse("\\infinite_union(nullable String s; a)");
   }

   @Test
   public void testOperatorWithExpr() {
      this.testParse("\\set_minus(me.get(), you.getToo())");
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

   @Test
   public void testEverythingKeyword() throws ParserException {
      this.testParse("\t \\everything  ");
   }

   @Test
   public void testParseSimpleIdentifier() throws ParserException {
      this.testParse(" state ");
   }

   @Test
   public void testParseQualifiedIdentifier() throws ParserException {
      this.testParse(" this.state . action");
   }

   @Test
   public void testParseArrayIndex() throws ParserException {
      this.testParse(" this.states[5]");
   }

   @Test
   public void testParseArrayRange() throws ParserException {
      this.testParse(" this.states[0..3]");
   }

   @Test
   public void testParseArrayAll() throws ParserException {
      this.testParse(" this.states[*] ");
   }

   @Test
   public void testParseArrayWithExpression() throws ParserException {
      this.testParse("this.states[hello.get() - 3]");
   }

   @Test
   public void testParseAllFields() throws ParserException {
      this.testParse(" this.*");
   }

   @Test
   public void testParseMultipleLocations() throws ParserException {
      this.testParse(" this.state, this.states[4], this.states.*");
   }

   @Test
   public void testParseInformalDescription() {
      // No informal description in key
      this.testWrongParse("  (* Mein Name ist Hase *)  ");
   }

   @Test
   public void testParseKeywordAndLocation() {
      this.testWrongParse("\\nothing, state");
   }

   @Test
   public void testParseEmpty() {
      this.testWrongParse("     ");
   }

   @Test
   public void testParseInvalidArray() {
      this.testWrongParse(" this.state[ ]");
   }

   @Test
   public void testIncompleteLocation() {
      this.testWrongParse(" this.state. ");
   }

   @Test
   public void testNoInformalDescription() {
      this.testWrongParse(" (* hello *) ", false);
   }

   protected void testWrongParse(final String text) {
      this.testWrongParse(text, true);
   }

   protected void testWrongParse(final String text,
         final boolean allowInformalDescr) {
      try {
         this.testParse(text, "", allowInformalDescr);
      }
      catch (final ParserException e) {
         return;
      }
      fail("StoreRefParser parsed \"" + text + "\"");
   }

   private void testParse(final String text, final String resultTerm,
         final boolean allowInformalDescr) throws ParserException {
      ParserTestUtils.testParseComplete(text,
            this.createParser(allowInformalDescr), resultTerm);
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
