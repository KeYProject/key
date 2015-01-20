package org.key_project.jmlediting.profile.jmlref.parseutil;

import static org.key_project.jmlediting.core.parser.ParserBuilder.*;
import static org.key_project.jmlediting.profile.jmlref.parseutil.JavaBasicsNodeTypes.*;

import org.key_project.jmlediting.core.parser.ParseFunction;

public class JavaBasicsParser {

   private final static JavaBasicsParser defaultInstance = new JavaBasicsParser();

   public static ParseFunction javaLiteral() {
      return defaultInstance.javaLiteral;
   }

   public static ParseFunction name() {
      return defaultInstance.name;
   }

   public static ParseFunction ident() {
      return defaultInstance.ident;
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
   private final ParseFunction stringLiteral = notImplemented();
   private final ParseFunction nullLiteral = constant("null");

   /**
    * java-literal ::= integer-literal<br>
    * | floating-point-literal | boolean-literal<br>
    * | character-literal | string-literal | null-literal<br>
    */
   // Float before int, because prefixes of some floats are ints
   private final ParseFunction javaLiteral = alt(this.floatingPointLiteral,
         this.integerLiteral, this.booleanLiteral, this.characterLiteral,
         this.stringLiteral, this.nullLiteral);

   private final ParseFunction name = separatedNonEmptyList(
         JavaBasicsNodeTypes.NAME, '.', this.ident,
         "Expected an identifier for a name");

}
