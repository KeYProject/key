package org.key_project.jmlediting.core.test.parser;

import static org.key_project.jmlediting.core.dom.Nodes.*;
import static org.key_project.jmlediting.core.parser.ParserBuilder.*;
import static org.key_project.jmlediting.core.test.utilities.ParserTestUtils.*;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.junit.Test;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.parser.DefaultJMLParser;
import org.key_project.jmlediting.core.parser.IJMLParser;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.AbstractJMLProfile;
import org.key_project.jmlediting.core.profile.DerivedProfile;
import org.key_project.jmlediting.core.profile.IEditableDerivedProfile;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;

public class ParserBuilderTest {

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

   private static IASTNode makeSeq(final int type, final char... chars) {
      final List<IASTNode> nodes = new ArrayList<IASTNode>(chars.length);
      int pos = 0;
      for (final char c : chars) {
         nodes.add(createString(pos, pos + 1, Character.toString(c)));
         pos++;
      }
      return createNode(type, nodes);
   }

   private static final ParseFunction parseA = parseSingleCharacter('A');
   private static final ParseFunction parseB = parseSingleCharacter('B');
   private static final ParseFunction parseC = parseSingleCharacter('C');

   @Test
   public void testParseEmptyList() throws ParserException {
      testParse("", list(parseA), makeList('A', 0));
   }

   @Test
   public void testListWithContent() throws ParserException {
      testParse("AAAAA", list(parseA), makeList('A', 5));
   }

   @Test
   public void testParseListWithRest() throws ParserException {
      testParse("AAABBB", list(parseA), makeList('A', 3));
   }

   @Test
   public void testParseEmptyListErrorRecovery() throws ParserException {
      testParse("", listErrorRecovery(parseA), makeList('A', 0));
   }

   @Test
   public void testListWithContentErrorRecovery() throws ParserException {
      testParse("AAAAA", listErrorRecovery(parseA), makeList('A', 5));
   }

   @Test
   public void testParseListWithRestErrorRecovery() throws ParserException {
      testParse("AAABBB", listErrorRecovery(parseA), makeList('A', 3));
   }

   @Test
   public void testParseListRecovery2() {
      testRecovery(
            "A;A;A",
            listErrorRecovery(closedBy(NodeTypes.NODE, parseA, ';')),
            "List[0-5](Node[0-2](String[0-1](A)),Node[2-4](String[2-3](A)),Node[4-5](ErrorNode[4-5](String[4-5](A))))");
   }

   @Test
   public void testParseListRecovery1() {
      testRecovery(
            "A;AA;AA;",
            listErrorRecovery(closedBy(NodeTypes.NODE, parseA, ';')),
            "List[0-8](Node[0-2](String[0-1](A)),Node[2-3](ErrorNode[2-3](String[2-3](A))),Node[3-5](String[3-4](A)),Node[5-6](ErrorNode[5-6](String[5-6](A))),Node[6-8](String[6-7](A)))");
   }

   @Test
   public void testParseNonEmptyListWithRest() throws ParserException {
      testParse("AAABBB", nonEmptyList(parseA, "Requires an A"),
            makeList('A', 3));
   }

   @Test
   public void testParseListWithRestNotComplete() {
      testParseFail("AAABBB", requireComplete(list(parseA)));
   }

   @Test(expected = IllegalArgumentException.class)
   public void testIllegalList() {
      list(null);
   }

   @Test(expected = IllegalArgumentException.class)
   public void testIllegalListErrorRecovery() {
      listErrorRecovery(null);
   }

   @Test(expected = IllegalArgumentException.class)
   public void testIllegalNonEmptyList() {
      nonEmptyList(null, "");
   }

   @Test
   public void testParseNonEmptyListFailOnEmpty() {
      testParseFail("", nonEmptyList(parseA, "Requires an A"));
   }

   @Test
   public void testParseEmptySeparatedList() throws ParserException {
      testParse("", separatedList('.', parseA), makeList('A', 0, 1));
   }

   @Test
   public void testSingleElementSeparatedList() throws ParserException {
      testParse("A", separatedList('.', parseA), makeList('A', 1, 1));
   }

   @Test
   public void testSingleElementNonEmptySeparatedList() throws ParserException {
      testParse("A", separatedNonEmptyList('.', parseA, "Missing an A"),
            makeList('A', 1, 1));
   }

   @Test
   public void testParseSeparatedNonEmptyListWithContent()
         throws ParserException {
      testParse("A,A,A,A", separatedNonEmptyList(',', parseA, "Missing an A"),
            makeList('A', 4, 1));
   }

   @Test
   public void testParseSeparatedNonEmptyListWithRest() throws ParserException {
      testParse("A,A,ABCB", separatedNonEmptyList(',', parseA, "Missing an A"),
            makeList('A', 3, 1));
   }

   @Test
   public void testParseSeparatedNonEmptyListWithSeparatedRest()
         throws ParserException {
      testParse("A,A,A,B", separatedNonEmptyList(',', parseA, "Missing an A"),
            makeList('A', 3, 1));
   }

   @Test
   public void testParseSeparatedNonEmptyListErrorRecovery()
         throws ParserException {
      testRecovery("A,A,",
            separatedNonEmptyListErrorRecovery(',', parseA, "Missing an A"),
            "List[0-4](String[0-1](A),String[2-3](A),ErrorNode[3-4](String[3-4](,)))");
   }

   @Test
   public void testParseEmptySeparatedNonEmptyList() throws ParserException {
      testParseFail("", separatedNonEmptyList(',', parseA, "Missed an A"));
   }

   @Test
   public void parseSeparatedListWithWhitespaces() throws ParserException {
      testParse("A ,A ,A ,A", separatedList(',', parseA), makeList('A', 4, 2));
   }

   @Test
   public void testParseSeparatedListEndedWithSeparator()
         throws ParserException {
      testParse("A,A,A,", separatedList(',', parseA), makeList('A', 3, 1));
   }

   @Test(expected = IllegalArgumentException.class)
   public void testIllegalSeparatedList() {
      separatedList(',', null);
   }

   @Test(expected = IllegalArgumentException.class)
   public void testIllegalSeparatedNonEmptyList() {
      separatedNonEmptyList(',', null, "");
   }

   @Test
   public void testSeparateBy() throws ParserException {
      testParse("  ,A", separateBy(',', parseA), createString(3, 4, "A"));
   }

   @Test(expected = IllegalArgumentException.class)
   public void testIllegalSeparateBy() {
      separateBy(',', null);
   }

   @Test
   public void testSeparateByWithoutSeparation() {
      testParseFail("A", separateBy('.', parseA));
   }

   @Test
   public void testSeparateByWithWrongContent() {
      testParseFail(",B", separateBy(',', parseA));
   }

   @Test
   public void testSeparateByWithoutContent() {
      testParseFail(";", separateBy(';', parseA));
   }

   @Test
   public void testSeparateByOnlyWhitespaces() {
      testParseFail("  ", separateBy(';', parseA));
   }

   @Test
   public void testSeparateByEmpty() {
      testParseFail("", separateBy(';', parseA));
   }

   @Test
   public void testAlternativeFirst() throws ParserException {
      testParse("A", alt(parseA, parseB, parseC), createString(0, 1, "A"));
   }

   @Test
   public void testAlternativeSecond() throws ParserException {
      testParse("B", alt(parseA, parseB, parseC), createString(0, 1, "B"));
   }

   @Test
   public void testAlternativeThird() throws ParserException {
      testParse("C", alt(parseA, parseB, parseC), createString(0, 1, "C"));
   }

   @Test
   public void testAlternativeNone() {
      testParseFail("D", alt(parseA, parseB, parseC));
   }

   @Test
   public void testAlternativeEmpty() {
      testParseFail("", alt(parseA, parseB, parseC));
   }

   @Test(expected = IllegalArgumentException.class)
   public void testIllegalAlternative() {
      alt();
   }

   @Test(expected = IllegalArgumentException.class)
   public void testIllegalAlternativeWithNulls() {
      alt(parseA, null);
   }

   @Test
   public void testSeqSuccessful() throws ParserException {
      testParse("ABC", seq(parseA, parseB, parseC),
            makeSeq(NodeTypes.SEQ, 'A', 'B', 'C'));
   }

   @Test
   public void testSeqWithRest() throws ParserException {
      testParse("ABCD", seq(parseA, parseB, parseC),
            makeSeq(NodeTypes.SEQ, 'A', 'B', 'C'));
   }

   @Test
   public void testPartialSeq() throws ParserException {
      testParseFail("ABX", seq(parseA, parseB, parseC));
   }

   @Test
   public void testEmptySeq() throws ParserException {
      testParseFail("", seq(parseA, parseB));
   }

   @Test(expected = IllegalArgumentException.class)
   public void testIllegalSeq() {
      seq();
   }

   @Test(expected = IllegalArgumentException.class)
   public void testIllegalSeqWithNulls() {
      seq(parseA, null, parseB);
   }

   @Test
   public void testOptionalSome() throws ParserException {
      testParse("A", opt(parseA), createOptional(createString(0, 1, "A"), 0));
   }

   @Test
   public void testOptionalNone() throws ParserException {
      testParse("B", opt(parseA), createOptional(null, 0));
   }

   @Test
   public void testOptionalEmpty() throws ParserException {
      testParse("", opt(parseA), createOptional(null, 0));
   }

   @Test(expected = IllegalArgumentException.class)
   public void testIllegalOptional() {
      opt(null);
   }

   @Test
   public void testIdentifier() throws ParserException {
      testParse("hallo", identifier(), createString(0, 5, "hallo"));
   }

   @Test
   public void testIdentifierWithWhitespaces() throws ParserException {
      testParse("  hallo  x", identifier(), createString(2, 7, "hallo"));
   }

   @Test
   public void testIdentiferFail() {
      testParseFail("  1", identifier());
   }

   @Test
   public void testIdentifierEmpty() {
      testParseFail("", identifier());
   }

   @Test
   public void testConstant() throws ParserException {
      testParse("  hallo", constant("hallo"), createString(2, 7, "hallo"));
   }

   @Test
   public void testConstantFail() {
      testParseFail("helone", constant("hallo"));
   }

   @Test
   public void testConstantToShort() {
      testParseFail("he", constant("hello"));
   }

   @Test
   public void testConstantEmpty() {
      testParseFail("", constant("hello"));
   }

   @Test(expected = IllegalArgumentException.class)
   public void testIllegalConstant1() {
      constant(null);
   }

   @Test(expected = IllegalArgumentException.class)
   public void testIllegalConstant2() {
      constant("");
   }

   @Test(expected = IllegalArgumentException.class)
   public void testIllegalConstant3() {
      constant(" a");
   }

   @Test
   public void testTyped() throws ParserException {
      testParse("A", typed(NodeTypes.LIST, parseA),
            createNode(NodeTypes.LIST, createString(0, 1, "A")));
   }

   @Test
   public void testTypedFail() {
      testParseFail("B", typed(NodeTypes.LIST, parseA));
   }

   @Test(expected = IllegalArgumentException.class)
   public void testTypedIllegal() {
      typed(0, null);
   }

   @Test
   public void testTypedRecovery() {
      testRecovery(
            "A",
            typed(NodeTypes.SOME, closedBy(NodeTypes.NODE, parseA, ',')),
            createNode(
                  NodeTypes.SOME,
                  createNode(NodeTypes.NODE,
                        createErrorNode(createString(0, 1, "A")))));
   }

   @Test
   public void testNotImplemented() {
      testParseFail("A", notImplemented());
   }

   @Test
   public void testRequireComplete() throws ParserException {
      testParse("A", requireComplete(parseA), createString(0, 1, "A"));
   }

   @Test
   public void testRequireCompleteTrailingWhitespaces() throws ParserException {
      testParse("A  ", requireComplete(parseA), createString(0, 1, "A"));
   }

   @Test
   public void testRequireCompleteFail() {
      testParseFail("A B", requireComplete(parseA));
   }

   @Test(expected = IllegalArgumentException.class)
   public void testRequireCompleteIllegal() {
      requireComplete(null);
   }

   // NO positive tests for parse keyword, this is tested in the various JML
   // tests
   // do not pay the effort of doing it here

   @Test(expected = IllegalArgumentException.class)
   public void testKeywordIllegal1() {
      keywords((Iterable<IKeyword>) null, new AbstractJMLProfile() {

         @Override
         public String getName() {
            return "No keywords profile";
         }

         @Override
         public String getIdentifier() {
            return "no.keyword";
         }

         @Override
         public IJMLParser createParser() {
            return new DefaultJMLParser(this);
         }

         @Override
         public IEditableDerivedProfile derive(final String id,
               final String name) {
            return new DerivedProfile<IJMLProfile>(id, name, this) {
            };
         }
      });
   }

   @Test(expected = IllegalArgumentException.class)
   public void testKeywordIllegal2() {
      keywords(Collections.<IKeyword> emptyList(), (IJMLProfile) null);
   }

   @Test
   public void testAllowWhitespaces() throws ParserException {
      testParse("  A", allowWhitespaces(parseA), createString(2, 3, "A"));
   }

   @Test
   public void testAllowWhitespacesWithoutWhitespaces() throws ParserException {
      testParse("A", allowWhitespaces(parseA), createString(0, 1, "A"));
   }

   @Test
   public void testAllowWhitspacesFail() {
      testParseFail("  B", allowWhitespaces(parseA));
   }

   @Test(expected = IllegalArgumentException.class)
   public void testAllowWhitespacesIllegal() {
      allowWhitespaces(null);
   }

   @Test
   public void testClosedBy() throws ParserException {
      testParse("A,", closedBy(NodeTypes.NODE, parseA, ','),
            createNode(0, 2, NodeTypes.NODE, createString(0, 1, "A")));
   }

   @Test
   public void testClosedByWithWhitespaces() throws ParserException {
      testParse("A   ,", closedBy(NodeTypes.NODE, parseA, ','),
            createNode(0, 5, NodeTypes.NODE, createString(0, 1, "A")));
   }

   @Test
   public void testIllegalClosedCharacter() {
      testParseFail("A;", closedBy(NodeTypes.NODE, parseA, ':'));
   }

   @Test(expected = IllegalArgumentException.class)
   public void testIllegalClosedBy1() {
      closedBy(NodeTypes.NODE, null, ':');
   }

   @Test(expected = IllegalArgumentException.class)
   public void testIllegalClosedBy2() {
      closedBy(NodeTypes.NODE, parseA, ' ');
   }

   @Test
   public void testClosedByErrorRecovery1() {
      testRecovery(
            "A ",
            closedBy(NodeTypes.NODE, parseA, ','),
            createNode(NodeTypes.NODE, createErrorNode(createString(0, 1, "A"))));
   }

   @Test
   public void testClosedByErrorRecovery2() {
      testRecovery(
            "A B",
            closedBy(NodeTypes.NODE, parseA, ','),
            createNode(NodeTypes.NODE, createErrorNode(createString(0, 1, "A"))));
   }

   @Test
   public void testClosedByErrorRecovery3() {
      testRecovery(
            "A ",
            closedBy(NodeTypes.NODE, parseA, ','),
            createNode(NodeTypes.NODE, createErrorNode(createString(0, 1, "A"))));
   }

}
