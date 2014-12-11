package org.key_project.jmlediting.core.test.parser;

import static org.junit.Assert.fail;
import static org.key_project.jmlediting.core.parser.ParserUtils.parseList;
import static org.key_project.jmlediting.core.parser.ParserUtils.parseNonEmptyList;
import static org.key_project.jmlediting.core.parser.ParserUtils.parseSeparatedList;
import static org.key_project.jmlediting.core.parser.ParserUtils.parseSeparatedNonEmptyList;
import static org.key_project.jmlediting.core.parser.ParserUtils.requireComplete;

import java.util.ArrayList;
import java.util.List;

import org.junit.Test;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.ParserException;

public class ParserUtilTest {

   private static ParseFunction parseSingleCharacter(final char c) {
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            if (start >= end) {
               throw new ParserException("Nothing left to parse", text, start);
            }
            final char nextChar = text.charAt(start);
            if (nextChar == c) {
               return Nodes.createString(start, start + 1,
                     Character.toString(c));
            }
            throw new ParserException("Expected a \"" + c + "\"", text, start);
         }
      };
   }

   private static IASTNode makeList(final char c, final int numOccurrences) {
      return makeList(c, numOccurrences, 0);
   }

   private static IASTNode makeList(final char c, final int numOccurrences,
         final int distance) {
      if (numOccurrences == 0) {
         return Nodes.createNode(0, 0, NodeTypes.LIST);
      }
      final List<IASTNode> nodes = new ArrayList<IASTNode>(numOccurrences);
      int pos = 0;
      for (int i = 0; i < numOccurrences; i++) {
         nodes.add(Nodes.createString(pos, pos + 1, Character.toString(c)));
         pos++;
         pos += distance;
      }
      return Nodes.createList(nodes);
   }

   private static final ParseFunction parseA = parseSingleCharacter('A');

   @Test
   public void testParseEmptyList() throws ParserException {
      testParse("", parseList(parseA), makeList('A', 0));
   }

   @Test
   public void testListWithContent() throws ParserException {
      testParse("AAAAA", parseList(parseA), makeList('A', 5));
   }

   @Test
   public void testParseListWithRest() throws ParserException {
      testParse("AAABBB", parseList(parseA), makeList('A', 3));
   }

   @Test
   public void testParseListWithRestNotComplete() {
      testParseFail("AAABBB", requireComplete(parseList(parseA)));
   }

   @Test
   public void testParseNonEmptyListFailOnEmpty() {
      testParseFail("", parseNonEmptyList(parseA, "Requires an A"));
   }

   @Test
   public void testParseEmptySeparatedList() throws ParserException {
      testParse("", parseSeparatedList('.', parseA), makeList('A', 0, 1));
   }

   @Test
   public void testSingleElementSeparatedList() throws ParserException {
      testParse("A", parseSeparatedList('.', parseA), makeList('A', 1, 1));
   }

   @Test
   public void testSingleElementNonEmptySeparatedList() throws ParserException {
      testParse("A", parseSeparatedNonEmptyList('.', parseA, "Missing an A"),
            makeList('A', 1, 1));
   }

   @Test
   public void testParseSeparatedNonEmptyListWithContent()
         throws ParserException {
      testParse("A,A,A,A",
            parseSeparatedNonEmptyList(',', parseA, "Missing an A"),
            makeList('A', 4, 1));
   }

   @Test
   public void testParseSeparatedNonEmptyListWithRest() throws ParserException {
      testParse("A,A,ABCB",
            parseSeparatedNonEmptyList(',', parseA, "Missing an A"),
            makeList('A', 3, 1));
   }

   @Test
   public void testParseSeparatedNonEmptyListWithSeparatedRest()
         throws ParserException {
      testParse("A,A,A,B",
            parseSeparatedNonEmptyList(',', parseA, "Missing an A"),
            makeList('A', 3, 1));
   }

   @Test
   public void testParseEmptySeparatedNonEmptyList() throws ParserException {
      testParseFail("", parseSeparatedNonEmptyList(',', parseA, "Missed an A"));
   }

   @Test
   public void parseSeparatedListWithWhitespaces() throws ParserException {
      testParse("A ,A ,A ,A", parseSeparatedList(',', parseA),
            makeList('A', 4, 2));
   }

   @Test
   public void testParseSeparatedListEndedWithSeparator()
         throws ParserException {
      testParse("A,A,A,", parseSeparatedList(',', parseA), makeList('A', 3, 1));
   }

   private static void testParse(final String text, final ParseFunction parser,
         final IASTNode expectedResult) throws ParserException {
      final IASTNode parseResult = parser.parse(text, 0, text.length());
      DomCompareUtils.compareIASTNode(expectedResult, parseResult, true);
   }

   private static void testParseFail(final String text,
         final ParseFunction parser) {
      try {
         parser.parse(text, 0, text.length());
      }
      catch (final ParserException e) {
         return;
      }
      fail("Expected a parsing error");
   }

}
