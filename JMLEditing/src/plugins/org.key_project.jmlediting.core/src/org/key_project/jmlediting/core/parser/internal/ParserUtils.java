package org.key_project.jmlediting.core.parser.internal;

import static org.key_project.jmlediting.core.parser.LexicalHelper.getJMLKeywordIdentifier;
import static org.key_project.jmlediting.core.parser.LexicalHelper.skipLayout;

import java.util.ArrayList;
import java.util.List;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.ParserBuilder;
import org.key_project.jmlediting.core.parser.ParserError;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLProfileHelper;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;

public class ParserUtils {

   private static List<IASTNode> parseListImpl(final String text,
         final int start, final int end, final ParseFunction function) {
      return parseListImpl(text, start, end, function,
            new ArrayList<IASTNode>());
   }

   private static List<IASTNode> parseListImpl(final String text,
         final int start, final int end, final ParseFunction function,
         final List<IASTNode> nodes) {

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

   /**
    * Tries to parse as much consecutive applications of functions and places
    * the parsed nodes in the given list. If function fails and provides an
    * error recovery node, this node is also included and the parse error
    * returned in the list.
    *
    * @param text
    *           the text to parse
    * @param start
    *           start index
    * @param end
    *           end index
    * @param function
    *           the parser function
    * @param nodes
    *           a list of nodes to put all parsed node in
    * @return a list of all {@link ParserError} found while parsing, if no error
    *         was found, the method returns null
    */
   private static List<ParserError> parseListErrorRecoveryImpl(
         final String text, final int start, final int end,
         final ParseFunction function, final List<IASTNode> nodes) {
      int startPosition = start;
      List<ParserError> errors = null;

      while (true) {
         try {
            // Parse a new list entry and put in in the list
            final IASTNode listNode = function.parse(text, startPosition, end);
            nodes.add(listNode);
            startPosition = listNode.getEndOffset();
         }
         catch (final ParserException e) {
            // Unable to parse, check whether error recovery is available
            if (e.getErrorNode() != null) {
               // Include in nodes, but collect errors
               nodes.add(e.getErrorNode());
               startPosition = e.getErrorNode().getEndOffset();
               if (errors == null) {
                  errors = new ArrayList<ParserError>();
               }
               errors.addAll(e.getAllErrors());
            }
            else {
               // Unable, stop parsing
               break;
            }
         }
      }
      return errors;

   }

   public static IASTNode parseListErrorRecovery(final String text,
         final int start, final int end, final ParseFunction function)
         throws ParserException {
      final List<IASTNode> nodes = new ArrayList<IASTNode>();
      final List<ParserError> errors = parseListErrorRecoveryImpl(text, start,
            end, function, nodes);
      IASTNode listNode;
      if (nodes.isEmpty()) {
         listNode = Nodes.createNode(start, start, NodeTypes.LIST);
      }
      else {
         listNode = Nodes.createNode(NodeTypes.LIST, nodes);
      }
      if (errors != null) {
         throw new ParserException(errors.get(0), errors.subList(1,
               errors.size()), text, listNode, null);
      }
      return listNode;
   }

   public static IASTNode parseSeparatedList(final String text,
         final int start, final int end, final char sep,
         final ParseFunction function) {
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
      final ParseFunction sepFunction = ParserBuilder.separateBy(sep, function);
      parseListImpl(text, startPosition, end, sepFunction, nodes);
      return Nodes.createNode(NodeTypes.LIST, nodes);
   }

   public static IASTNode parseSeparatedNonEmptyList(final int type,
         final String text, final int start, final int end, final char sep,
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
      final ParseFunction sepFunction = ParserBuilder.separateBy(sep, function);
      parseListImpl(text, startPosition, end, sepFunction, nodes);
      final IASTNode node = Nodes.createNode(type, nodes);
      return node;
   }

   public static IASTNode parseSeparatedNonEmptyListErrorRecovery(
         final String text, final int start, final int end, final char sep,
         final ParseFunction function, final String missingExceptionText)
         throws ParserException {
      final List<IASTNode> nodes = new ArrayList<IASTNode>();
      List<ParserError> errors = null;

      int startPosition = start;

      try {
         final IASTNode node = function.parse(text, startPosition, end);
         nodes.add(node);
         startPosition = node.getEndOffset();
      }
      catch (final ParserException e) {
         if (e.getErrorNode() != null) {
            if (errors == null) {
               errors = new ArrayList<ParserError>();
            }
            errors.addAll(e.getAllErrors());
            startPosition = e.getErrorNode().getEndOffset();
            nodes.add(e.getErrorNode());
         }
         else {
            throw new ParserException(missingExceptionText, text, start, e);
         }
      }
      final ParseFunction sepFunction = ParserBuilder.separateBy(sep, function);
      final List<ParserError> listErrors = parseListErrorRecoveryImpl(text,
            startPosition, end, sepFunction, nodes);
      if (listErrors != null) {
         if (errors == null) {
            errors = listErrors;
         }
         else {
            errors.addAll(listErrors);
         }
      }

      final IASTNode node = Nodes.createNode(NodeTypes.LIST, nodes);
      if (errors != null) {
         throw new ParserException(errors.get(0), errors.subList(1,
               errors.size()), text, node, null);
      }
      return node;
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
      ParserException ex = null;
      for (final ParseFunction function : seqs) {
         try {
            final IASTNode node = function.parse(text, startPosition, end);
            nodes.add(node);
            startPosition = node.getEndOffset();
         }
         catch (final ParserException e) {
            if (e.getErrorNode() != null) {
               nodes.add(e.getErrorNode());
               startPosition = e.getErrorNode().getEndOffset();
               if (ex == null) {
                  ex = e;
               }
            }
            else {
               throw e;
            }
         }
      }
      assert (nodes.size() == seqs.length);
      if (ex != null) {
         throw new ParserException(ex, Nodes.createNode(type, nodes));
      }
      return Nodes.createNode(type, nodes);
   }

   public static IASTNode parseAlternative(final String text, final int start,
         final int end, final ParseFunction... alternatives)
         throws ParserException {
      ParserException exception = null;
      IASTNode firstErrorNode = null;
      for (final ParseFunction function : alternatives) {
         try {
            final IASTNode node = function.parse(text, start, end);
            return node;
         }
         catch (final ParserException e) {
            if (exception == null) {
               exception = e;
            }
            if (e.getErrorNode() != null) {
               firstErrorNode = e.getErrorNode();
               exception = e;
            }
         }
      }
      if (firstErrorNode == null) {
         throw exception;
      }
      else {
         throw new ParserException(exception, firstErrorNode);
      }
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
    * @param enabledKeywords
    *           all keywords which are available
    * @param profile
    *           the current profile we are parsing according to
    * @return an IAST node for the keyword
    * @throws ParserException
    *            when parsing in not successful
    */
   public static IASTNode parseKeyword(final String text, final int start,
         final int end, final Iterable<? extends IKeyword> enabledKeywords,
         final IJMLProfile profile) throws ParserException {
      ParserUtils.validatePositions(text, start, end);

      // Find keyword in text
      final int keywordStart = skipLayout(text, start, end, false);
      final int keywordEnd = getJMLKeywordIdentifier(text, keywordStart, end);
      final String keyword = text.substring(keywordStart, keywordEnd);

      // Find the corresponding IKeyword instance from the profile
      final IKeyword foundKeyword = JMLProfileHelper.findKeyword(
            enabledKeywords, keyword);
      if (foundKeyword == null) {
         throw new ParserException(
               "Not a supported specification statement keyword: \"" + keyword
                     + "\"", text, keywordStart);
      }
      final IASTNode keywordNode = Nodes.createKeyword(keywordStart,
            keywordEnd, foundKeyword, keyword);

      // Now parse according to the keywword
      final IKeywordParser keywordParser = foundKeyword.createParser();
      keywordParser.setProfile(profile);
      IASTNode keywordResult;
      try {
         keywordResult = keywordParser.parse(text, keywordEnd, end);
      }
      catch (final ParserException e) {
         keywordResult = e.getErrorNode();
         if (keywordResult == null) {
            throw new ParserException(e, Nodes.createNode(
                  NodeTypes.KEYWORD_APPL, keywordNode,
                  Nodes.createErrorNode(keywordEnd)));
         }
         throw new ParserException(e, Nodes.createNode(NodeTypes.KEYWORD_APPL,
               keywordNode, keywordResult));
      }

      // Build the result
      if (keywordResult == null) {
         return keywordNode;
      }
      else {
         return Nodes.createNode(NodeTypes.KEYWORD_APPL, keywordNode,
               keywordResult);
      }
   }

   /**
    * Validates the start and end position for a given text.
    *
    * @param text
    *           the text
    * @param start
    *           the start position (inclusive)
    * @param end
    *           the end position (exclusive)
    * @throws ParserException
    *            when the positions are invalid
    */
   public static void validatePositions(final String text, final int start,
         final int end) throws ParserException {
      if (start < 0) {
         throw new ParserException("Given start index is out of bounds: "
               + start + " < 0", text, start);
      }
      if (start >= text.length()) {
         throw new ParserException("Given start index is out of bounds: "
               + start + " >= " + text.length(), text, start);
      }
      if (end < start) {
         throw new ParserException("start < end", text, start);
      }
      if (end > text.length()) {
         throw new ParserException("Given end index is out of bounds: " + end
               + " >= " + text.length(), text, end);
      }
   }

}
