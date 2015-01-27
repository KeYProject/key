package org.key_project.jmlediting.core.parser.util;

import static org.key_project.jmlediting.core.parser.ParserBuilder.*;
import static org.key_project.jmlediting.core.parser.util.JavaBasicsNodeTypes.*;

import org.key_project.jmlediting.core.parser.ParseFunction;

/**
 * This class contains {@link ParseFunction} to parse basic elements of Java.
 *
 * @author Moritz Lichter
 *
 */
public final class JavaBasicsParser {

   /**
    * no instances.
    */
   private JavaBasicsParser() {

   }

   /**
    * The default instance.
    */
   private static final JavaBasicsParser DEFAULT_INSTANCE = new JavaBasicsParser();

   /**
    *
    * @return a ParseFunction, which parses a Java literal
    */
   public static ParseFunction javaLiteral() {
      return DEFAULT_INSTANCE.javaLiteral;
   }

   /**
    *
    * @return a {@link ParseFunction} which parses a Java name
    */
   public static ParseFunction name() {
      return DEFAULT_INSTANCE.name;
   }

   /**
    *
    * @return a {@link ParseFunction} which parses a Java identifier
    */
   public static ParseFunction ident() {
      return DEFAULT_INSTANCE.ident;
   }

   private final ParseFunction ident = identifier();

   private final ParseFunction integerLiteral = typed(INTEGER_LITERAL,
         Lexicals.integerLiteral());
   private final ParseFunction floatingPointLiteral = typed(FLOAT_LITERAL,
         Lexicals.floatLiteral());
   private final ParseFunction booleanLiteral = oneConstant(BOOLEAN_LITERAL,
         "true", "false");
   private final ParseFunction characterLiteral = typed(CHARACTER_LITERAL,
         Lexicals.characterLiteral());
   private final ParseFunction stringLiteral = typed(STRING_LITERAL,
         Lexicals.stringLiteral());
   private final ParseFunction nullLiteral = typed(NULL_LITERAL,
         constant("null"));

   /**
    * java-literal ::= integer-literal<br>
    * | floating-point-literal | boolean-literal<br>
    * | character-literal | string-literal | null-literal<br>
    * .
    */
   // Float before int, because prefixes of some floats are ints
   private final ParseFunction javaLiteral = alt(this.floatingPointLiteral,
         this.integerLiteral, this.booleanLiteral, this.characterLiteral,
         this.stringLiteral, this.nullLiteral);

   private final ParseFunction name = separatedNonEmptyList(
         JavaBasicsNodeTypes.NAME, '.', this.ident,
         "Expected an identifier for a name");

}
