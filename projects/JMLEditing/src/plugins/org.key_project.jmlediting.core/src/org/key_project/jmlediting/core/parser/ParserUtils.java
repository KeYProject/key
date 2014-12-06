package org.key_project.jmlediting.core.parser;

import java.util.ArrayList;
import java.util.List;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;

/**
 * Provides some utility functions for parsing.
 *
 * @author Moritz Lichter
 *
 */
public final class ParserUtils {

   /**
    * No instantiations.
    */
   private ParserUtils() {

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

   private static List<IASTNode> parseListImpl(final String text,
         final int start, final int end, final ParseFunction function) {
      final List<IASTNode> nodes = new ArrayList<IASTNode>();

      while (true) {
         try {
            final IASTNode listNode = function.parse(text, start, end);
            nodes.add(listNode);
         }
         catch (final ParserException e) {
            break;
         }
      }
      return nodes;
   }

   public static IASTNode parseList(final String text, final int start,
         final int end, final ParseFunction function) {
      return Nodes.createNode(NodeTypes.LIST,
            parseListImpl(text, start, end, function));
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

   public static ParseFunction parseList(final ParseFunction function) {
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            return parseList(text, start, end, function);
         }
      };
   }

   public static ParseFunction parseNonEmptyList(final ParseFunction function,
         final String missingExceptionText) {
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            return parseNonEmptyList(text, start, end, function,
                  missingExceptionText);
         }
      };
   }

   public static ParseFunction parseSeparatedNonEmptyList(final char sep,
         final ParseFunction function, final String missingExceptionText) {
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            return parseSeparatedNonEmptyList(sep, text, start, end, function,
                  missingExceptionText);
         }
      };
   }

   public static ParseFunction separateBy(final char sep,
         final ParseFunction function) {
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            final int commaStart = LexicalHelper.skipWhiteSpacesOrAt(text,
                  start, end);
            if (text.charAt(commaStart) != sep) {
               throw new ParserException("Expected a \"" + sep + "\"", text,
                     commaStart);
            }
            return function.parse(text, commaStart + 1, end);
         }
      };
   }

   public static IASTNode parseSeparatedList(final char sep, final String text,
         final int start, final int end, final ParseFunction function) {
      return parseList(text, start, end, separateBy(sep, function));
   }

   public static IASTNode parseSeparatedNonEmptyList(final char sep,
         final String text, final int start, final int end,
         final ParseFunction function, final String missingExceptionText)
               throws ParserException {
      return parseNonEmptyList(text, start, end, separateBy(sep, function),
            missingExceptionText);
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

   public static ParseFunction alternative(final ParseFunction... alternatives) {
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            return parseAlternative(text, start, end, alternatives);
         }
      };
   }

   public static IASTNode parseSeq(final int type, final String text,
         final int start, final int end, final ParseFunction... seqs)
               throws ParserException {
      final List<IASTNode> nodes = new ArrayList<IASTNode>();
      int startPosition = start;
      for (final ParseFunction function : seqs) {
         final IASTNode node = function.parse(text, startPosition, end);
         nodes.add(node);
         startPosition = node.getEndOffset() + 1;
      }
      return Nodes.createNode(type, nodes);
   }

   public static ParseFunction seq(final int type, final ParseFunction... seqs) {
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            return parseSeq(type, text, start, end, seqs);
         }
      };

   }

   public static ParseFunction seq(final ParseFunction... seqs) {
      return seq(NodeTypes.SEQ, seqs);
   }

   public static ParseFunction identifier() {
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            final int identifierStart = LexicalHelper.skipWhiteSpacesOrAt(text,
                  start, end);
            final int identifierEnd = LexicalHelper.getIdentifier(text,
                  identifierStart, end);
            return Nodes.createString(identifierStart, identifierEnd - 1,
                  text.substring(identifierStart, identifierEnd));
         }
      };
   }

   public static ParseFunction constant(final String constant) {
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            final int constantStart = LexicalHelper.skipWhiteSpacesOrAt(text,
                  start, end);
            if (constantStart + constant.length() < text.length()) {
               throw new ParserException("Expected a \"" + constant + "\"",
                     text, constantStart);
            }
            for (int i = 0; i < constant.length(); i++) {
               if (text.charAt(constantStart + i) != constant.charAt(i)) {
                  throw new ParserException("Expected a \"" + constant + "\"",
                        text, constantStart + i);
               }
            }
            return Nodes.createString(constantStart,
                  constantStart + constant.length() - 1, constant);
         }
      };
   }

   public static ParseFunction typed(final int type,
         final ParseFunction function) {
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            return Nodes.createNode(type, function.parse(text, start, end));
         }
      };
   }

}
