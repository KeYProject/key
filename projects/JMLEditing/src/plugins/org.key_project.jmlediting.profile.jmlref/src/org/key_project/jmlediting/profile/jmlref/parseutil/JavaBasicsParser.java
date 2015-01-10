package org.key_project.jmlediting.profile.jmlref.parseutil;

import static org.key_project.jmlediting.core.parser.ParserBuilder.*;

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

   ParseFunction ident = identifier();

   ParseFunction integerLiteral = integerConstant();
   ParseFunction floatingPointLiteral = notImplemented();
   ParseFunction booleanLiteral = notImplemented();
   ParseFunction characterLiteral = notImplemented();
   ParseFunction stringLiteral = notImplemented();
   ParseFunction nullLiteral = constant("null");

   /**
    * java-literal ::= integer-literal<br>
    * | floating-point-literal | boolean-literal<br>
    * | character-literal | string-literal | null-literal<br>
    */
   ParseFunction javaLiteral = alt(this.integerLiteral,
         this.floatingPointLiteral, this.booleanLiteral, this.characterLiteral,
         this.stringLiteral, this.nullLiteral);

   ParseFunction name = separatedNonEmptyList('.', this.ident,
         "Expected an identifier for a name");

}
