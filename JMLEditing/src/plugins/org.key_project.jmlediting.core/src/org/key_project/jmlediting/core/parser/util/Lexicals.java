package org.key_project.jmlediting.core.parser.util;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.parser.LexicalHelper;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.ParserException;

/**
 * This class contains some utility functions for lexing the content of
 * keywords.
 *
 * @author Moritz Lichter
 *
 */
public final class Lexicals {

   /**
    * No instances.
    */
   private Lexicals() {

   }

   /**
    * The node type of an informal description.
    */
   public static final int INFORMAL_DESCRIPTION = NodeTypes
         .getNewType("InformalDescription");

   /**
    * Creates a {@link ParseFunction} that lexes an informal description for
    * storage references. An informal description is of the form: (*...*).
    *
    * @return the parse function
    */
   public static ParseFunction lexInformalDescr() {
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            if (start + 2 > end) {
               throw new ParserException("Expected an Informal Description",
                     text, start);
            }
            if (!(text.charAt(start) == '(' && text.charAt(start + 1) == '*')) {
               throw new ParserException("Invalid informal description start",
                     text, start);
            }
            // Scan for end, no string or escapes handles here, so its easy
            int position = start + 2;
            // +1 here because we need to have space for an additional character
            // to
            // find *) end
            boolean foundEnd = false;
            while (position + 1 < end) {
               if (text.charAt(position) == '*'
                     && text.charAt(position + 1) == ')') {
                  foundEnd = true;
                  break;
               }
               position++;
            }
            if (!foundEnd) {
               throw new ParserException(
                     "Expected closing *) for informal description", text, end);
            }

            return Nodes.createNode(
                  start,
                  position + 2,
                  INFORMAL_DESCRIPTION,
                  Nodes.createString(start + 2, position,
                        text.substring(start + 2, position)));

         }

      };
   }

   /**
    * Parses an integer literal starting at the current position accepting
    * whitespaces before the constant. The result is a string term in order not
    * to lose the format of the identifier (hex, oct, dec).
    *
    * @see LexicalHelper#getIntegerConstant(String, int, int)
    * @return a {@link ParseFunction} that parses an integer constant
    */
   public static ParseFunction integerLiteral() {
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            final int identifierStart = LexicalHelper.skipLayout(text, start,
                  end);
            final int identifierEnd = LexicalHelper.getIntegerConstant(text,
                  identifierStart, end);
            return Nodes.createString(identifierStart, identifierEnd,
                  text.substring(identifierStart, identifierEnd));
         }

      };
   }

   /**
    * Parses an integer literal starting at the current position accepting
    * whitespaces before the constant.
    *
    * @see LexicalHelper#getFloatConstant(String, int, int)
    * @return a {@link ParseFunction} that parses a float constant
    */
   public static ParseFunction floatLiteral() {
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            final int identifierStart = LexicalHelper.skipLayout(text, start,
                  end);
            final int identifierEnd = LexicalHelper.getFloatConstant(text,
                  identifierStart, end);
            return Nodes.createString(identifierStart, identifierEnd,
                  text.substring(identifierStart, identifierEnd));
         }
      };
   }

   /**
    * Parses a character literal starting at the current position accepting
    * whitespaces before the constant.
    *
    * @see LexicalHelper#getCharacterConstant(String, int, int)
    * @return a {@link ParseFunction} that parses a character constant
    */
   public static ParseFunction characterLiteral() {
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            final int identifierStart = LexicalHelper.skipLayout(text, start,
                  end);
            final int identifierEnd = LexicalHelper.getCharacterConstant(text,
                  identifierStart, end);
            return Nodes.createString(identifierStart, identifierEnd,
                  text.substring(identifierStart, identifierEnd));
         }
      };
   }

   /**
    * Parses a string literal starting at the current position accepting
    * whitespaces before the constant.
    *
    * @see LexicalHelper#getStringConstant(String, int, int) * @return a
    *      {@link ParseFunction} that parses a string constant
    */
   public static ParseFunction stringLiteral() {
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            final int identifierStart = LexicalHelper.skipLayout(text, start,
                  end);
            final int identifierEnd = LexicalHelper.getStringConstant(text,
                  identifierStart, end);
            return Nodes.createString(identifierStart, identifierEnd,
                  text.substring(identifierStart, identifierEnd));
         }
      };
   }

}
