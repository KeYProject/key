package org.key_project.jmlediting.core.parser;

import static org.key_project.jmlediting.core.parser.LexicalHelper.getJMLKeywordIdentifier;
import static org.key_project.jmlediting.core.parser.LexicalHelper.skipWhiteSpacesOrAt;
import static org.key_project.jmlediting.core.parser.ParserUtils.validatePositions;

import java.util.ArrayList;
import java.util.List;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.profile.JMLProfileHelper;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;

public class ParserUtilsImpl {

   static List<IASTNode> parseListImpl(final String text, final int start,
         final int end, final ParseFunction function) {
      final List<IASTNode> nodes = new ArrayList<IASTNode>();

      int startPosition = start;
      while (true) {
         try {
            final IASTNode listNode = function.parse(text, startPosition, end);
            nodes.add(listNode);
            startPosition = listNode.getEndOffset();
         }
         catch (final ParserException e) {
            break;
         }
      }
      return nodes;
   }

   static IASTNode parseSeparatedList(final String text, final int start,
         final int end, final char sep, final ParseFunction function) {
      final List<IASTNode> nodes = new ArrayList<IASTNode>();
      int startPosition = start;
      try {
         final IASTNode node = function.parse(text, startPosition, end);
         nodes.add(node);
         startPosition = node.getEndOffset();
      }
      catch (final ParserException e) {
         return Nodes.createNode(start, start, NodeTypes.LIST);
      }
      final ParseFunction sepFunction = ParserUtils.separateBy(sep, function);
      while (true) {
         try {
            final IASTNode listNode = sepFunction.parse(text, startPosition,
                  end);
            startPosition = listNode.getEndOffset();
            nodes.add(listNode);
         }
         catch (final ParserException e) {
            break;
         }
      }
      return Nodes.createNode(NodeTypes.LIST, nodes);
   }

   static IASTNode parseSeparatedNonEmptyList(final String text,
         final int start, final int end, final char sep,
         final ParseFunction function, final String missingExceptionText)
               throws ParserException {
      final List<IASTNode> nodes = new ArrayList<IASTNode>();
      int startPosition = start;
      try {
         final IASTNode node = function.parse(text, startPosition, end);
         nodes.add(node);
         startPosition = node.getEndOffset();
      }
      catch (final ParserException e) {
         throw new ParserException(missingExceptionText, text, start, e);
      }
      final ParseFunction sepFunction = ParserUtils.separateBy(sep, function);
      while (true) {
         try {
            final IASTNode listNode = sepFunction.parse(text, startPosition,
                  end);
            startPosition = listNode.getEndOffset();
            nodes.add(listNode);
         }
         catch (final ParserException e) {
            break;
         }
      }
      return Nodes.createNode(NodeTypes.LIST, nodes);
   }

   public static IASTNode parseList(final String text, final int start,
         final int end, final ParseFunction function) {
      final List<IASTNode> nodes = parseListImpl(text, start, end, function);
      if (nodes.isEmpty()) {
         return Nodes.createNode(start, start, NodeTypes.LIST);
      }
      else {
         return Nodes.createNode(NodeTypes.LIST, nodes);
      }
   }

   public static IASTNode parseNonEmptyList(final String text, final int start,
         final int end, final ParseFunction function,
         final String missingExceptionText) throws ParserException {
      final List<IASTNode> nodes = parseListImpl(text, start, end, function);
      if (nodes.isEmpty()) {
         throw new ParserException(missingExceptionText, text, start);
      }
      return Nodes.createNode(NodeTypes.LIST, nodes);
   }

   public static IASTNode parseSeq(final int type, final String text,
         final int start, final int end, final ParseFunction... seqs)
               throws ParserException {
      final List<IASTNode> nodes = new ArrayList<IASTNode>();
      int startPosition = start;
      for (final ParseFunction function : seqs) {
         final IASTNode node = function.parse(text, startPosition, end);
         nodes.add(node);
         startPosition = node.getEndOffset();
      }
      assert (nodes.size() == seqs.length);
      return Nodes.createNode(type, nodes);
   }

   public static IASTNode parseAlternative(final String text, final int start,
         final int end, final ParseFunction... alternatives)
               throws ParserException {
      ParserException exception = null;
      for (final ParseFunction function : alternatives) {
         try {
            return function.parse(text, start, end);
         }
         catch (final ParserException e) {
            exception = e;
         }
      }
      throw exception;
   }

   /**
    * Parses the a single keyword and the rest specified by the parser of the
    * keyword.
    *
    * @param text
    *           the text to parse in
    * @param start
    *           the start position (the position for the next keywords)
    * @param end
    *           the maximum position (exclusive)
    * @param availableKeywords
    *           all keywords which are available
    * @return an IAST node for the keyword
    * @throws ParserException
    *            when parsing in not successful
    */
   public static IASTNode parseKeyword(final String text, final int start,
         final int end, final Iterable<? extends IKeyword> availableKeywords)
               throws ParserException {
      validatePositions(text, start, end);

      // Find keyword in text
      final int keywordStart = skipWhiteSpacesOrAt(text, start, end, false);
      final int keywordEnd = getJMLKeywordIdentifier(text, keywordStart, end);
      final String keyword = text.substring(keywordStart, keywordEnd);

      // Find the corresponding IKeyword instance from the profile
      final IKeyword foundKeyword = JMLProfileHelper.findKeyword(
            availableKeywords, keyword);
      if (foundKeyword == null) {
         throw new ParserException(
               "Not a supported specification statement keyword: \"" + keyword
               + "\"", text, keywordEnd);
      }
      final IASTNode keywordNode = Nodes.createKeyword(keywordStart,
            keywordEnd, foundKeyword, keyword);

      // Now parse according to the keywword
      final IKeywordParser keywordParser = foundKeyword.createParser();
      final IASTNode keywordResult = keywordParser.parse(text, keywordEnd, end);

      // Build the result
      if (keywordResult == null) {
         return keywordNode;
      }
      else {
         return Nodes.createNode(NodeTypes.KEYWORD_APPL, keywordNode,
               keywordResult);
      }
   }

}
