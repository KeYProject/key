package org.key_project.jmlediting.core.test.parser;

import static org.junit.Assert.fail;

import org.junit.Test;
import org.key_project.jmlediting.core.parser.ParserBuilder;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionParser;

public class ExpressionParserTest {

   @Test
   public void testSimpleExpressionLIdentifier() {
      testParse("hello");
   }

   @Test
   public void testSimpleExpressionIntConstant() {
      testParse("12");
   }

   @Test
   public void testSimpleExpressionBoolLiteral() {
      testParse("true");
   }

   @Test
   public void testBooleanAnd() {
      testParse("hello && goodby");
   }

   @Test
   public void testBooleanOr() {
      testParse("a || b");
   }

   @Test
   public void testCombinedBooleans() {
      testParse("a && b || (c && d || e ^ f) | g ");
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

   public static void testParse(final String content) {
      try {
         System.out.println(ParserBuilder
               .requireComplete(
                     new ExpressionParser(ProfileWrapper.testProfile))
               .parse(content, 0, content.length()).prettyPrintAST());
      }
      catch (final ParserException e) {
         fail(e.getMessage());
      }
   }

}
