package org.key_project.jmlediting.core.parser;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.parser.internal.ParserUtils;
import org.key_project.jmlediting.core.parser.internal.RecursiveParseFunction;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLProfileHelper;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.core.profile.syntax.IKeywordSort;

/**
 * Provides abstractions to build a parser from given basic element. A parser is
 * composed by instances of {@link ParseFunction}. This class provides methods
 * to combine {@link ParseFunction} as building alternatives, sequences or
 * lists. The result is a {@link ParseFunction} again which can be combined with
 * others again. <br>
 * There are several rules for combination: This parser parses greedy, if
 * something could be parsed it will not be rejected to continue parsing on an
 * other branch. Take care when using the combinators an this.<br>
 * Some combinations functions adds support to ignore whitespaces. By general,
 * any {@link ParseFunction} which does not care about whitespace must be able
 * to ignore leading whitespaces. <br>
 * With the functions of this class it is rather easy to write a parser for a
 * given grammar because the parser can be expressed rather declarative (with
 * respect to the rules above).
 *
 * @author Moritz Lichter
 *
 */
public final class ParserBuilder {

   /**
    * No instantiations.
    */
   private ParserBuilder() {

   }

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
   public static ParseFunction list(final ParseFunction function) {
      if (function == null) {
         throw new IllegalArgumentException("Provide a non null function");
      }
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            return ParserUtils.parseList(text, start, end, function);
         }
      };
   }

   /**
    * Creates a {@link ParseFunction} which is able to parse a list of items
    * which are parsed by the given function. That means that the generated
    * ParseFunction tries to parse using the given ParseFunction as often as
    * possible. If no parse is possible, an empty list is returned.<br>
    * The returned node is of type {@link NodeTypes#LIST} and contains the
    * parsed nodes.<br>
    * This function contains a certain type of error recovery which is important
    * to note: If an application of function fails but provides an error
    * recovery node, this node is added to the list. If any error node is in the
    * list, the created function returns not normally but throws an exception.<br>
    * This behavior makes the created function differ from the function created
    * by {@link #list(ParseFunction)}: If list can parse three items and the
    * fourth not, list returns these three node and the forth may be covered by
    * a following function. But if the parse function for the list items
    * provides an error recovery for the forth item, listErrorRecovery will fail
    * and provide an error recovery node with these four items. <br>
    * So make sure when using this function, that the function to parse list
    * items cannot provide error recovery for anything which is allowed to be
    * parsed after the list.
    *
    * @param function
    *           the {@link ParseFunction} to parse a single element of the list
    * @return a {@link ParseFunction} that parses a list of elements parseable
    *         by the given function.
    */
   public static ParseFunction listErrorRecovery(final ParseFunction function) {
      if (function == null) {
         throw new IllegalArgumentException("Provide a non null function");
      }
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            return ParserUtils.parseListErrorRecovery(text, start, end,
                  function);
         }
      };
   }

   /**
    * Does the same as {@link ParserBuilder#list(ParseFunction)} but ensures
    * that at least a single element is contained in the list. If no element
    * could be parsed, a {@link ParserException} with the given failure test is
    * thrown.
    *
    * @param function
    *           the {@link ParseFunction} to parse a single list element
    * @param missingExceptionText
    *           the exception text to show that an element is missing
    * @return a {@link ParseFunction} able to parse a non empty list of elements
    *         parseable by the given function
    */
   public static ParseFunction nonEmptyList(final ParseFunction function,
         final String missingExceptionText) {
      if (function == null) {
         throw new IllegalArgumentException("Provide a non null function");
      }
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            return ParserUtils.parseNonEmptyList(text, start, end, function,
                  missingExceptionText);
         }
      };
   }

   /**
    * Parses a list of elements separated by a given separation char. This
    * function builds up a {@link ParseFunction} which is able to parse a list
    * of elements parseable by the given {@link ParseFunction} which are
    * separated by a given separation char. Whitespace before the separation
    * character is allowed. Whitespace before the elements is not implicitly
    * allowed. This follows the rule that {@link ParseFunction} which ignore
    * whitespace should ignore all whitespaces in front. No separation character
    * after the last element is parsed.
    *
    * @param sep
    *           the character to separate the elements
    * @param function
    *           a {@link ParseFunction} which is able to parse a single element
    *           of the list
    * @return a {@link ParseFunction} which is able to parse a list of elements
    *         parseable by the given {@link ParseFunction} separated by the
    *         given separation character.
    */
   public static ParseFunction separatedList(final char sep,
         final ParseFunction function) {
      if (function == null) {
         throw new IllegalArgumentException("Provide a non null function");
      }
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            return ParserUtils.parseSeparatedList(text, start, end, sep,
                  function);
         }
      };
   }

   /**
    * Defaults to
    * {@link #separatedNonEmptyList(int, char, ParseFunction, String)} with type
    * {@link NodeTypes#LIST}.
    *
    * @param sep
    *           the character to separate the elements
    * @param function
    *           a {@link ParseFunction} which is able to parse a single element
    *           of the list
    * @param missingExceptionText
    *           the text for an exception when no element could be parsed
    * @return a {@link ParseFunction} which is able to parse a list of elements
    *         parseable by the given {@link ParseFunction} separated by the
    *         given separation character.
    */
   public static ParseFunction separatedNonEmptyList(final char sep,
         final ParseFunction function, final String missingExceptionText) {
      return separatedNonEmptyList(NodeTypes.LIST, sep, function,
            missingExceptionText);
   }

   /**
    * Does the same as {@link ParserBuilder#separatedList(char, ParseFunction)}
    * but ensures that at least a single element is parsed. If no element could
    * be parsed, a {@link ParserException} with the given exception text is
    * thrown.
    *
    * @param type
    *           the type of the list node to create
    * @param sep
    *           the character to separate the elements
    * @param function
    *           a {@link ParseFunction} which is able to parse a single element
    *           of the list
    * @param missingExceptionText
    *           the text for an exception when no element could be parsed
    * @return a {@link ParseFunction} which is able to parse a list of elements
    *         parseable by the given {@link ParseFunction} separated by the
    *         given separation character.
    */
   public static ParseFunction separatedNonEmptyList(final int type,
         final char sep, final ParseFunction function,
         final String missingExceptionText) {
      if (function == null) {
         throw new IllegalArgumentException("Provide a non null function");
      }
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            return ParserUtils.parseSeparatedNonEmptyList(type, text, start,
                  end, sep, function, missingExceptionText);
         }
      };
   }

   public static ParseFunction separatedNonEmptyListErrorRecovery(
         final char sep, final ParseFunction function,
         final String missingExceptionText) {
      if (function == null) {
         throw new IllegalArgumentException("Provide a non null function");
      }
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            return ParserUtils.parseSeparatedNonEmptyListErrorRecovery(text,
                  start, end, sep, function, missingExceptionText);
         }
      };
   }

   /**
    * Separates the given parse function with a character. That means, that a
    * single character, the separation character) is expected before it is
    * continues with parsing with the given parse function. The separation
    * character will not show up in the AST. Whitespaces before the separation
    * character are allowed, the given parse function should handle whitespaces.
    * after the character.
    *
    * @param sep
    *           the separaction character
    * @param function
    *           the function to continue parsing with
    * @return a {@link ParseFunction} which is able to parse an element of the
    *         given function separated with the given character
    */
   public static ParseFunction separateBy(final char sep,
         final ParseFunction function) {
      if (function == null) {
         throw new IllegalArgumentException("Provide a non null function");
      }
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            final int sepStart = LexicalHelper.skipLayout(text, start, end);
            if (sepStart >= end) {
               throw new ParserException("Reached end of text", text, end);
            }
            if (text.charAt(sepStart) != sep) {
               throw new ParserException("Expected a \"" + sep + "\"", text,
                     sepStart);
            }
            try {
               return function.parse(text, sepStart + 1, end);
            }
            catch (final ParserException e) {
               if (e.getErrorNode() != null) {
                  throw e;
                  // throw new ParserException(e,
                  // Nodes.createErrorNode(sepStart,
                  // e.getErrorNode().getEndOffset(), e.getErrorNode()));
               }
               else {
                  throw new ParserException(e, Nodes.createErrorNode(
                        sepStart,
                        sepStart + 1,
                        Nodes.createString(sepStart, sepStart + 1,
                              Character.toString(sep))));
               }
            }
         }
      };
   }

   /**
    * Creates a {@link ParseFunction} which closes a given {@link ParseFunction}
    * with a given character. The closedBy combinator returns a {@link IASTNode}
    * of the given type containing the node parsed with the given function. The
    * additional node is inserted to cover the position of the closing
    * character. Whitespaces before the separating character is supported. This
    * combinator implements error recovery when the closing character is missing
    * but the given function was able to parse.
    *
    * @param type
    *           the type of node for the wrapping node
    * @param function
    *           the function to parse the content
    * @param close
    *           the separating char which is used to close the content parsed
    *           with the function
    * @return a {@link ParseFunction} able to parse content parseable by the
    *         given function and accepting a character after it.
    * @throws IllegalArgumentException
    *            if function is null
    * @throws IllegalArgumentException
    *            if close is a whitespace
    */
   public static ParseFunction closedBy(final int type,
         final ParseFunction function, final char close) {
      if (function == null) {
         throw new IllegalArgumentException("Provide a non nulll function");
      }
      if (Character.isWhitespace(close)) {
         throw new IllegalArgumentException(
               "Provide a close character which is not a whitespace");
      }
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            // Parse with the given function
            ParserException contentException;
            IASTNode node;
            try {
               node = function.parse(text, start, end);
               contentException = null;
            }
            catch (final ParserException e) {
               contentException = e;
               if (e.getErrorNode() == null) {
                  node = null;
                  throw e;
               }
               else {
                  node = e.getErrorNode();
               }
            }

            // Then scan for the closing semicolon
            if (node.getEndOffset() == end) {
               // error, do not scan for whitespaces
               throw new ParserException("Expected a " + close, end, text,
                     Nodes.createNode(type, Nodes.createErrorNode(node)));
            }
            final int semicolonPos = LexicalHelper.skipLayout(text,
                  node.getEndOffset(), end);
            if (semicolonPos >= end || text.charAt(semicolonPos) != close) {
               // error
               final IASTNode errorNode = Nodes.createNode(type,
                     Nodes.createErrorNode(node));
               throw new ParserException("Expected a " + close, semicolonPos,
                     text, errorNode);
            }
            final IASTNode resultNode = Nodes.createNode(node.getStartOffset(),
                  semicolonPos + 1, type, node);
            if (contentException == null) {
               return resultNode;
            }
            else {
               throw new ParserException(contentException, resultNode);
            }
         }
      };
   }

   /**
    * Parses an alternative of {@link ParseFunction}. The given function are
    * tried in order to parse the content. The result of first function, which
    * is able to parse, will be returned. That means, that one needs to take
    * care of prefixes. If one {@link ParseFunction} A is a prefix of an other
    * one B and A is before B in the given parameter list, then B will never be
    * used to parse the content because A will succeed even if B would be able
    * to parse more. So place B before A in the list or try to rewrite the
    * combination:<br>
    * Say, B = seq(A,C) and D = alternative(A,B), this would never parse B. The
    * other way around, D = alternative(B,A) will parse B if possible, but It
    * parses A twice if B fails but A succeeds. The following should perform
    * better (depends on the complexity of A): D = seq(A, optional(C)). At least
    * one alternative function needs to be provided.
    *
    * @param alternatives
    *           the alternative {@link ParseFunction}
    * @return a {@link ParseFunction} with tries to parse one of the given
    *         functions.
    */
   public static ParseFunction alt(final ParseFunction... alternatives) {
      if (alternatives == null || alternatives.length == 0) {
         throw new IllegalArgumentException(
               "Need to provide at least one alternative");
      }
      for (final ParseFunction f : alternatives) {
         if (f == null) {
            throw new IllegalArgumentException("Cannot provide a null function");
         }
      }
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            return ParserUtils.parseAlternative(text, start, end, alternatives);
         }
      };
   }

   /**
    * Parses a sequence of {@link ParseFunction}. The given
    * {@link ParseFunction}s are required to succeed to parse the input text in
    * the order as given to this function. The result will be a node containing
    * the result of the single {@link ParseFunction} with the given node type.
    * No whitespace is added by default, the single parseFunction should take
    * care of this. At last one sequence has to be provided.
    *
    * @param type
    *           the type of the result node
    * @param seqs
    *           the individual {@link ParseFunction} to build the sequence of
    * @return a {@link ParseFunction} able to parse the given sequence of
    *         functions.
    */
   public static ParseFunction seq(final int type, final ParseFunction... seqs) {
      if (seqs == null || seqs.length == 0) {
         throw new IllegalArgumentException(
               "Provide at least one sequence function");
      }
      for (final ParseFunction f : seqs) {
         if (f == null) {
            throw new IllegalArgumentException("Cannot provide a null function");
         }
      }
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            return ParserUtils.parseSeq(type, text, start, end, seqs);
         }
      };

   }

   /**
    * Does the same as {@link #seq(int, ParseFunction...)} with the default node
    * type {@link NodeTypes#SEQ}.
    *
    * @param seqs
    *           the individual {@link ParseFunction} to build the sequence of
    * @return a {@link ParseFunction} able to parse the given sequence of
    *         functions.
    */
   public static ParseFunction seq(final ParseFunction... seqs) {
      return seq(NodeTypes.SEQ, seqs);
   }

   /**
    * Parses a given {@link ParseFunction} if possible but does not fail if not.
    * The result is a node of type {@link NodeTypes#SOME} of the function could
    * be applied containing the parse result or an empty node of type
    * {@link NodeTypes#NONE} if the function could not be applied.
    *
    * @param function
    *           the {@link ParseFunction} to try
    * @return a {@link ParseFunction} which tries to parse the given one.
    */
   public static ParseFunction opt(final ParseFunction function) {
      if (function == null) {
         throw new IllegalArgumentException("Provide a non null function");
      }
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            IASTNode result;
            try {
               result = function.parse(text, start, end);
            }
            catch (final ParserException e) {
               result = null;
            }
            return Nodes.createOptional(result, start);
         }
      };
   }

   /**
    * Parses an identifier starting at the current position allowing whitespaces
    * before the identifier. The result is a string node containing the text of
    * the identifier.
    *
    * @see LexicalHelper#getIdentifier(String, int, int)
    * @return a {@link ParseFunction} able to parse an identifier;
    */
   public static ParseFunction identifier() {
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            final int identifierStart = LexicalHelper.skipLayout(text, start,
                  end);
            final int identifierEnd = LexicalHelper.getIdentifier(text,
                  identifierStart, end);
            return Nodes.createString(identifierStart, identifierEnd,
                  text.substring(identifierStart, identifierEnd));
         }
      };
   }

   /**
    * Creates a {@link ParseFunction} which parses a constant string allowing
    * whitespaces before that string. The constant needs to contains at least
    * one character. The {@link ParseFunction} returns a string node containing
    * the constant. Also the constant is not allowed to start with whitespaces
    *
    * @param constant
    *           the constant to parse
    * @return a {@link ParseFunction} to parse the given constant
    */
   public static ParseFunction constant(final String constant) {
      if (constant == null) {
         throw new IllegalArgumentException("Cannot provide a null constant");
      }
      if (constant.length() == 0) {
         throw new IllegalArgumentException("Cannot provide an empty constant");
      }
      if (Character.isWhitespace(constant.charAt(0))) {
         throw new IllegalArgumentException(
               "Constant not allowed to start with whitespaces");
      }
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            // Skip whitespaces
            final int constantStart = LexicalHelper
                  .skipLayout(text, start, end);
            // Check that enough characters are left for the constant
            if (constantStart + constant.length() > end) {
               throw new ParserException("Expected a \"" + constant + "\"",
                     text, constantStart);
            }
            // Compare text and constant
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

   /**
    * Creates a {@link ParseFunction} with takes the result of another parse
    * functions and wraps the result of this function into a new node with a
    * specific type. This combinator implements error recovery. If function
    * fails but is able to recover, the resulting error node is also wrapped.
    *
    * @param type
    *           the type of the wrapping node
    * @param function
    *           the {@link ParseFunction} to wrap its result
    * @return the wrapping {@link ParseFunction}
    * @throws IllegalArgumentException
    *            if function is null
    */
   public static ParseFunction typed(final int type,
         final ParseFunction function) {
      if (function == null) {
         throw new IllegalArgumentException(
               "Function is not allowed to be null");
      }
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            try {
               return Nodes.createNode(type, function.parse(text, start, end));
            }
            catch (final ParserException e) {
               if (e.getErrorNode() == null) {
                  throw e;
               }
               else {
                  throw new ParserException(e, Nodes.createNode(type,
                        e.getErrorNode()));
               }
            }
         }
      };
   }

   /**
    * Returns a {@link ParseFunction} which always throws an error. This may be
    * useful to specify a sort but implement it later.
    *
    * @return a {@link ParseFunction} that always fails.
    */
   public static ParseFunction notImplemented() {
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            throw new ParserException("Not implemented", text, start);
         }
      };
   }

   /**
    * Returns a {@link ParseFunction} which always throws an error. This may be
    * useful to specify that a sort is not defined.
    *
    * @return a {@link ParseFunction} that always fails.
    */
   public static ParseFunction fail() {
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            throw new ParserException("Failed.", text, start);
         }
      };
   }

   /**
    * Returns {@link ParseFunction} which checks that the given function parses
    * the complete input string. Trailing whitespaces are allowed.
    *
    * @param function
    *           the {@link ParseFunction} to apply
    * @return a {@link ParseFunction} that checks that the applied function
    *         parsed everything
    */
   public static ParseFunction requireComplete(final ParseFunction function) {
      if (function == null) {
         throw new IllegalArgumentException("Need to give a non null function");
      }
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            final IASTNode node = function.parse(text, start, end);
            final int nodeEnd = node.getEndOffset();
            if (nodeEnd == end) {
               return node;
            }
            final int whiteEnd = LexicalHelper.skipLayout(text, nodeEnd, end);
            if (whiteEnd < end) {
               final IASTNode errorNode = Nodes.createErrorNode(node, Nodes
                     .createUnparsedTextNode(text.substring(whiteEnd, end),
                           whiteEnd, end));
               throw new ParserException("Unexpected content.", whiteEnd, text,
                     errorNode);
            }
            return node;
         }

      };
   }

   /**
    * Checks to parse a keyword contained in the given iterable of keyword.
    * Whitespaces in the front are allowed. When the keyword is found the
    * {@link IKeywordParser} of the keyword is invoked to parse the content
    * after the keyword. It returns a node of type
    * {@link NodeTypes#KEYWORD_APPL}, the first child node is a keyword node
    * containing the keyword text and the second node a node of type
    * {@link NodeTypes#KEYWORD_CONTENT} containing the result of the parser.
    *
    * @param keywords
    *           an iterable through all allowed profiles
    * @param activeProfile
    *           the current active {@link IJMLProfile} to give to the
    *           {@link IKeywordParser}
    * @return a {@link ParseFunction} able to parse keywords of the given
    *         iterable
    */
   public static ParseFunction keywords(
         final Iterable<? extends IKeyword> keywords,
         final IJMLProfile activeProfile) {
      if (keywords == null) {
         throw new IllegalArgumentException(
               "Need to specify a non null profile");
      }
      if (activeProfile == null) {
         throw new IllegalArgumentException("Need to give a non null profile");
      }
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            return ParserUtils.parseKeyword(text, start, end, keywords,
                  activeProfile);
         }
      };
   }

   /**
    * Short cut for filtering all keywords in the given profile by the given
    * sort.
    *
    * @param clazz
    *           the class of keywords to filter
    * @param profile
    *           the profiles to look into
    * @param <T>
    *           the type of the keywords
    * @return a {@link ParseFunction} able to parse keywords of the given type
    */
   public static <T extends IKeyword> ParseFunction keywords(
         final Class<T> clazz, final IJMLProfile profile) {
      return keywords(JMLProfileHelper.filterKeywords(profile, clazz), profile);
   }

   public static ParseFunction keywords(final IKeywordSort sort,
         final IJMLProfile profile) {
      return keywords(JMLProfileHelper.filterKeywords(profile, sort), profile);
   }

   /**
    * Creates a {@link ParseFunction} that consumes all whitespaces found from
    * the current position on. After that, the given function is invoked. This
    * is useful to convert a {@link ParseFunction} that does not ignore
    * whitespaces to a function which does.
    *
    * @param function
    *           the function to wrap
    * @return a {@link ParseFunction} ike function but ignoring leading
    *         whitespaces
    */
   public static ParseFunction allowWhitespaces(final ParseFunction function) {
      if (function == null) {
         throw new IllegalArgumentException("Give a non null function");
      }
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            final int startAfterWhitespaces = LexicalHelper.skipLayout(text,
                  start, end);
            return function.parse(text, startAfterWhitespaces, end);
         }
      };
   }

   public static IRecursiveParseFunction recursiveInit() {
      return new RecursiveParseFunction();
   }

   public static ParseFunction brackets(final ParseFunction p) {
      return brackets("(", p, ")");
   }

   public static ParseFunction squareBrackets(final ParseFunction p) {
      return brackets("[", p, "]");
   }

   public static ParseFunction curlyBrackets(final ParseFunction p) {
      return brackets("{", p, "}");
   }

   public static ParseFunction brackets(final String open,
         final ParseFunction p, final String close) {
      final ParseFunction function = seq(constant(open), p, constant(close));
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            try {
               final IASTNode node = function.parse(text, start, end);
               final IASTNode openNode = node.getChildren().get(0);
               final IASTNode contentNode = node.getChildren().get(1);
               final IASTNode closeNode = node.getChildren().get(2);
               return Nodes.createNode(openNode.getStartOffset(),
                     closeNode.getEndOffset(), contentNode.getType(),
                     contentNode.getChildren());
            }
            catch (final ParserException e) {
               if (e.getErrorNode() == null) {
                  throw e;
               }
               if (e.getErrorNode().getChildren().size() >= 2) {
                  throw new ParserException(e, e.getErrorNode().getChildren()
                        .get(1));
               }
               else {
                  throw e;
               }
            }
         }
      };

   }

   public static ParseFunction oneConstant(final String... constants) {
      ParseFunction f = notImplemented();
      for (final String constant : constants) {
         f = alt(constant(constant), f);
      }
      return f;
   }

   public static ParseFunction oneConstant(final int type,
         final String... constants) {
      ParseFunction f = notImplemented();
      for (final String constant : constants) {
         f = alt(constant(constant), f);
      }
      return typed(type, f);
   }

}
