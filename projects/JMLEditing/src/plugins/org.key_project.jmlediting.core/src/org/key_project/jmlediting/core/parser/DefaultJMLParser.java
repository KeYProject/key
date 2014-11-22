package org.key_project.jmlediting.core.parser;

import org.key_project.jmlediting.core.dom.IBehaviorSpecification;
import org.key_project.jmlediting.core.dom.IMethodSpecification;
import org.key_project.jmlediting.core.dom.ISpecificationCase;
import org.key_project.jmlediting.core.dom.ISpecificationStatement;
import org.key_project.jmlediting.core.parser.internal.SpecificationStatement;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.ISpecificationStatementKeyword;

public class DefaultJMLParser implements IJMLParser {
   
   private IJMLProfile profile;
   
   public DefaultJMLParser(IJMLProfile profile) {
      if (profile == null) {
         throw new IllegalArgumentException("Cannot pass a null profile");
      }
      this.profile = profile;
   }

   @Override
   public IMethodSpecification parseMethodSpecification(String text, int start,
         int end) {
      // TODO Auto-generated method stub
      return null;
   }

   @Override
   public ISpecificationCase parseSpecificationCase(String text, int start,
         int end) {
      // TODO Auto-generated method stub
      return null;
   }

   @Override
   public IBehaviorSpecification parseBehaviorSpecification(String text,
         int start, int end) {
      // TODO Auto-generated method stub
      return null;
   }
   
   @Override
   public ISpecificationStatement parseSpecificationStatement(String text,
        int start, int end) throws ParserException{
      int keywordStart = skipWhiteSpaces(text, start, end);
      if (keywordStart == end) {
         throw new ParserException("Requires a specification statement keyword", text, end);
      }
      int keywordEnd = getIdentifier(text, keywordStart, end);
      String keyword = text.substring(keywordStart, keywordEnd);
      ISpecificationStatementKeyword foundKeyword = null;
      for (ISpecificationStatementKeyword availableKeyword : this.profile.getSupportedSpecificationStatementKeywords()) {
         if (keyword.equals(availableKeyword.getKeyword())) {
            foundKeyword = availableKeyword;
            break;
         }
      }
      if (foundKeyword == null) {
         throw new ParserException("Not a supported specification statement keyword: \"" + keyword + "\"",text, keywordEnd);
      }
      
      int closingSemicolon = scanForClosingSemicolon(text, keywordEnd, end);
      // Content without semicolon
      String content = text.substring(keywordEnd+1, closingSemicolon);
      
      return new SpecificationStatement(keywordStart, closingSemicolon, foundKeyword, content);
   }
   
   private int scanForClosingSemicolon(String text, int start, int end) throws ParserException{
      boolean isStringOrChar = false;
      char quoteChar = ' ';
      int position = start;
      while (position <= end) {
         char c = text.charAt(position);
         boolean isQuoteChar = c =='\'' || c == '\"';
         if (isQuoteChar && !isStringOrChar) {
            isStringOrChar = true;
            quoteChar = c;
         }
         else if (isStringOrChar) {
            if (c=='\\' ) {
                  // now escaping a character in a string
                  // this is not a ; to search for
                  position = position +2;
                  // dont look at the next one
                  continue;
            } else {
                  if( c == quoteChar) {
                     // close string or char
                     isStringOrChar = false;
                     quoteChar = ' ';
                  }
            }
         }
         if (!isStringOrChar) {
            if (c==';') {
               break;
            }
         }
         position ++;
      }
      if (position > end) {
         throw new ParserException("No closing semicolon found", text, end);
      }
      return position;
      
   }
   
   private int getIdentifier(String text, int start, int end) throws ParserException{
      int position = start;
      if (start == end) {
         throw new ParserException("Expected an identifier", text, start);
      }
      if (!Character.isJavaIdentifierStart(text.charAt(position))) {
         throw new ParserException("Not a valid Java identifier", text, position);
      }
      position ++;
      while (position <= end && Character.isJavaIdentifierPart(text.charAt(position))) {
         position++;
      }
      if (position > end) {
         position = end; // Occurs if last char belongs to identifier
      }
      return position;
   }
   
   private int skipWhiteSpaces(String text, int start, int end) {
      int position = start;
      while (position <= end && isWhitespace(text.charAt(position))) {
         position ++;
      }
      if (position > end) {
         position = end; // Occurs if last char is whitespace
      }
      return position;
   }
   
   private boolean isWhitespace(char c) {
      return isWhitespaceWithoutNewLine(c) || c=='\n' || c=='\r';
   }
   
   private boolean isWhitespaceWithoutNewLine(int c) {
      return c==' ' || c=='\t';
   }

}
