package org.key_project.jmlediting.profile.jmlref.test.parser;

import static org.key_project.jmlediting.profile.jmlref.test.utilities.JMLRefParserTestUtils.testParsePPComplete;

import org.junit.Test;
import org.key_project.jmlediting.core.parser.ParserException;

public class RequiresParserTest {

   @Test
   public void testRequiresExpression() throws ParserException {
      testParsePPComplete(
            "requires true;",
            "Node(KeywordAppl(Keyword(requires),KeywordContent(Primary(BooleanLiteral(\"true\")))))");
   }

   @Test
   public void testRequiresComplexExpression() throws ParserException {
      testParsePPComplete(
            "requires (\\forall int i; i > 0; foo(i)) && x ==> y;",
            "Node(KeywordAppl(Keyword(requires),KeywordContent(Implies(LogicalAnd(Primary(JMLPrimary(QuantifiedExpression(Keyword(\\forall),Seq(PrimitiveType(\"int\"),List(\"i\")),\";\",QuantifierPredicate(RelationalOp(Primary(Identifier(\"i\")),\">\",Primary(IntegerLiteral(\"0\")))),Primary(Identifier(\"foo\"),List(MethodCall(ExpressionList(Primary(Identifier(\"i\"))))))))),\"&&\",Primary(Identifier(\"x\"))),\"==>\",Primary(Identifier(\"y\"))))))");
   }

   @Test
   public void testRequiresNotSpecified() throws ParserException {
      testParsePPComplete("requires \\not_specified;",
            "Node(KeywordAppl(Keyword(requires),KeywordContent(Keyword(\\not_specified))))");
   }

   @Test
   public void testRequiresSame() throws ParserException {
      testParsePPComplete("requires \\same;",
            "Node(KeywordAppl(Keyword(requires),KeywordContent(Keyword(\\same))))");
   }

}
