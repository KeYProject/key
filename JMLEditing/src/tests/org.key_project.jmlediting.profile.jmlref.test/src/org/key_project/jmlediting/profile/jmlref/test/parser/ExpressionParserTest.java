package org.key_project.jmlediting.profile.jmlref.test.parser;

import static org.junit.Assert.fail;

import org.junit.Test;
import org.key_project.jmlediting.core.parser.ParserBuilder;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.test.utilities.ParserTestUtils;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionParser;
import org.key_project.jmlediting.profile.jmlref.test.utilities.ProfileWrapper;

public class ExpressionParserTest {

   @Test
   public void testSimpleExpressionLIdentifier() {
      testParsePP("hello", "Primary(Identifier(\"hello\"))");
   }

   @Test
   public void testSimpleExpressionIntConstant() {
      testParsePP("12", "Primary(IntegerLiteral(\"12\"))");
   }

   @Test
   public void testSimpleExpressionBoolLiteral() {
      testParsePP("true", "Primary(BooleanLiteral(\"true\"))");
   }

   @Test
   public void testBooleanAnd() {
      testParsePP(
            "hello && goodby",
            "LogicalAnd(Primary(Identifier(\"hello\")),\"&&\",Primary(Identifier(\"goodby\")))");
   }

   @Test
   public void testBooleanOr() {
      testParsePP("a || b",
            "LogicalOr(Primary(Identifier(\"a\")),\"||\",Primary(Identifier(\"b\")))");
   }

   @Test
   public void testCombinedBooleans() {
      testParsePP(
            "a && b || (c && d || e ^ f) | g ",
            "LogicalOr("
                  + "LogicalAnd(Primary(Identifier(\"a\")),\"&&\",Primary(Identifier(\"b\"))),\"||\","
                  + "BinaryOr(Primary(LogicalOr(LogicalAnd(Primary(Identifier(\"c\")),\"&&\","
                  + "Primary(Identifier(\"d\"))),\"||\",BinaryExclusiveOr(Primary(Identifier(\"e\")),\"^\","
                  + "Primary(Identifier(\"f\"))))),\"|\",Primary(Identifier(\"g\"))))");
   }

   @Test
   public void testCombinedInteger() {
      testParse("hallo + 5 * me / (a + b) - this.all");
   }

   @Test
   public void testBooleanOutOfInteger() {
      testParse("a - b + c++ >= h % g");
   }

   @Test
   public void testFunctionCall() {
      testParse("this.foo.bar(3)");
   }

   @Test
   public void testNestedFunctionCalls() {
      testParse("this.foo.bar(me.get(3) + you.get(other.none()))");
   }

   @Test
   public void testCreateObject() {
      testParse("new List(hallo)");
   }

   @Test
   public void testCreateObjectGenerics() {
      testParse("new List<Integer>(hallo)");
   }

   @Test
   public void testCreateArray() {
      testParse("new Integer[3][4][5][this.get(new String())]");
   }

   @Test
   public void testArrayInitializer() {
      testParse("new double[]{2,3,4}");
   }

   @Test
   public void testArrayAccess() {
      testParse("hallo[4].name[foo()]");
   }

   @Test
   public void testJMLEquivalenc() {
      testParse("a && b <==> c || d  <=!=> (b << 1 > 5)");
   }

   @Test
   public void testInstanceOf() {
      testParse("a && (b instanceof C)");
   }

   @Test
   public void testConditionalOp() {
      testParse("a && B || c ? a + b - g : this.calculate(new Integer(3))");
   }

   @Test
   public void testAssignment() {
      testParse("me = you + (z += 5)");
   }

   @Test
   public void testImplications() {
      testParse(" hallo ==> ((you ==> me))");
   }

   @Test
   public void testImplicationsBackward() {
      testParse(" hallo <== you <== (me ==> you) <== me");
   }

   @Test
   public void testPostfix() {
      testParse("myname ++");
   }

   @Test
   public void testResult() {
      testParse("\\result == 5");
   }

   @Test
   public void testOld() {
      testParse("\\old(this.name)");
   }

   @Test
   public void testForall() {
      testParse("(\\forall int i; a[i]<a[j])");
   }

   @Test
   public void testForallQuantifiedExpression() {
      testParse("(\\forall int i,j; 0 <= i && i < j && j < 10; a[i]<a[j])");
   }

   @Test
   public void testForallEmptyQuantifiedExpression() {
      testParse("(\\forall non_null Integer i,j;; a[i]<a[j])");
   }

   public static void testParse(final String content) {
      try {
         ParserBuilder
               .requireComplete(
                     new ExpressionParser(ProfileWrapper.testProfile))
               .parse(content, 0, content.length()).prettyPrintAST();
      }
      catch (final ParserException e) {
         fail(e.getMessage());
      }
   }

   public static void testParsePP(final String content,
         final String expectedPPResult) {
      try {
         ParserTestUtils.testParsePPComplete(content, new ExpressionParser(
               ProfileWrapper.testProfile), expectedPPResult);
      }
      catch (final ParserException e) {
         fail(e.getMessage());
      }
   }

}
