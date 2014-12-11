package org.key_project.jmlediting.core.parser;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.parser.iternal.ParserUtilsImpl;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;

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

   // With Java 8 Lambda syntax the following would be much more readable, no
   // anonymous classes, they just wrap the functions implementing the tasks

   /**
    * Creates a {@link ParseFunction} which is able to parse a list of items
    * which are parsed by the given function. That means that the generated
    * ParseFunction tries to parse using the given ParseFunction as often as
    * possible. If no parse is possible, an empty list is returned.<br>
    * The returned node is of type {@link NodeTypes#LIST} and contains the
    * parsed nodes.
    *
    * @param function
    *           the {@link ParseFunction} to parse a single element of the list
    * @return a {@link ParseFunction} that parses a list of elements parseable
    *         by the given function.
    */
   public static ParseFunction parseList(final ParseFunction function) {
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            return ParserUtilsImpl.parseList(text, start, end, function);
         }
      };
   }

   public static ParseFunction parseNonEmptyList(final ParseFunction function,
         final String missingExceptionText) {
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            return ParserUtilsImpl.parseNonEmptyList(text, start, end,
                  function, missingExceptionText);
         }
      };
   }

   public static ParseFunction parseSeparatedNonEmptyList(final char sep,
         final ParseFunction function, final String missingExceptionText) {
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            return ParserUtilsImpl.parseSeparatedNonEmptyList(text, start, end,
                  sep, function, missingExceptionText);
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
            if (commaStart >= end) {
               throw new ParserException("Reached end of text", text, end);
            }
            if (text.charAt(commaStart) != sep) {
               throw new ParserException("Expected a \"" + sep + "\"", text,
                     commaStart);
            }
            return function.parse(text, commaStart + 1, end);
         }
      };
   }

   public static ParseFunction alternative(final ParseFunction... alternatives) {
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            return ParserUtilsImpl.parseAlternative(text, start, end,
                  alternatives);
         }
      };
   }

   public static ParseFunction seq(final int type, final ParseFunction... seqs) {
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            return ParserUtilsImpl.parseSeq(type, text, start, end, seqs);
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
            return Nodes.createString(identifierStart, identifierEnd,
                  text.substring(identifierStart, identifierEnd));
         }
      };
   }

   public static ParseFunction integerConstant() {
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            final int identifierStart = LexicalHelper.skipWhiteSpacesOrAt(text,
                  start, end);
            final int identifierEnd = LexicalHelper.getIntegerConstant(text,
                  identifierStart, end);
            return Nodes.createString(identifierStart, identifierEnd,
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
            if (constantStart + constant.length() > end) {
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
                  constantStart + constant.length(), constant);
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

   public static ParseFunction notImplemented() {
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            throw new ParserException("Not implemented", text, start);
         }
      };
   }

   public static ParseFunction requireComplete(final ParseFunction function) {
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            final IASTNode node = function.parse(text, start, end);
            final int nodeEnd = node.getEndOffset();
            if (nodeEnd == end) {
               return node;
            }
            final int whiteEnd = LexicalHelper.skipWhiteSpaces(text, nodeEnd,
                  end);
            if (whiteEnd < end) {
               throw new ParserException(
                     "requires to parse complete text but stopped", text,
                     nodeEnd);
            }
            return node;
         }

      };
   }

   public static ParseFunction parseKeyword(
         final Iterable<? extends IKeyword> keywords,
         final IJMLProfile activeProfile) {
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            return ParserUtilsImpl.parseKeyword(text, start, end, keywords,
                  activeProfile);
         }
      };
   }

   public static ParseFunction allowWhitespace(final ParseFunction function) {

      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            final int startAfterWhitespaces = LexicalHelper
                  .skipWhiteSpacesOrAt(text, start, end);
            return function.parse(text, startAfterWhitespaces, end);
         }
      };
   }

}
