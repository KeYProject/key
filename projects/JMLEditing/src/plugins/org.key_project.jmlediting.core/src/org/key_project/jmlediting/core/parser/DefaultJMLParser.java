package org.key_project.jmlediting.core.parser;

import java.util.ArrayList;
import java.util.List;

import org.key_project.jmlediting.core.dom.IBehaviorSpecification;
import org.key_project.jmlediting.core.dom.ILightweightSpecification;
import org.key_project.jmlediting.core.dom.IMethodSpecification;
import org.key_project.jmlediting.core.dom.ISpecificationCase;
import org.key_project.jmlediting.core.dom.ISpecificationStatement;
import org.key_project.jmlediting.core.dom.Visibility;
import org.key_project.jmlediting.core.parser.internal.BehaviorSpecification;
import org.key_project.jmlediting.core.parser.internal.LightweightSpecification;
import org.key_project.jmlediting.core.parser.internal.MethodSpecification;
import org.key_project.jmlediting.core.parser.internal.SpecificationStatement;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.IJMLBehaviorKeyword;
import org.key_project.jmlediting.core.profile.syntax.ISpecificationStatementKeyword;

public class DefaultJMLParser implements IJMLParser {

   private IJMLProfile profile;

   public DefaultJMLParser(IJMLProfile profile) {
      if (profile == null) {
         throw new IllegalArgumentException("Cannot pass a null profile");
      }
      this.profile = profile;
   }

   private void validatePositions(String text, int start, int end)
         throws ParserException {
      if (start < 0) {
         throw new ParserException("Given start index is out of bounds: "
               + start + " < 0", text, start);
      }
      if (start > text.length()) {
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

   @Override
   public IMethodSpecification parseMethodSpecification(String text, int start,
         int end, boolean requireComplete) throws ParserException {
      // Temporary implementation, does not support redundant specs
      int alsoStart = skipWhiteSpacesOrAt(text, start, end);
      int alsoEnd = getIdentifier(text, alsoStart, end);
      String keyword = text.substring(alsoStart, alsoEnd);
      boolean isExtendingSpecification = false;
      int position = start;
      int begin = alsoStart;
      if (keyword.equals("also")) {
         isExtendingSpecification = true;
         position = alsoEnd;
      }
      List<ISpecificationCase> specCaseList = new ArrayList<ISpecificationCase>();
      ISpecificationCase specCase = this.parseSpecificationCase(text, position,
            end);
      specCaseList.add(specCase);
      position = specCase.getEndOffset() + 1;

      while (true) {
         try {
            alsoStart = skipWhiteSpacesOrAt(text, position, end);
            alsoEnd = getIdentifier(text, alsoStart, end);
            keyword = text.substring(alsoStart, alsoEnd);
            if (!keyword.equals("also")) {
               throw new ParserException("Expected also", text, alsoStart);
            }
            specCase = this.parseSpecificationCase(text, alsoEnd, end);
            specCaseList.add(specCase);
            position = specCase.getEndOffset() + 1;
         }
         catch (ParserException e) {
            break;
         }
      }
      if (!isExtendingSpecification) {
         begin = specCaseList.get(0).getStartOffset();
      }
      
      int startOffset=begin;
      int endOffset = specCaseList.get(
            specCaseList.size() - 1).getEndOffset();
      if (requireComplete) {
         int completeEnd = skipWhiteSpacesOrAt(text, endOffset, end);
         if (completeEnd < end) {
            throw new ParserException("Parsing method specification cannot parse complete test " + completeEnd + " < " + end, text, endOffset);
         }
      }

      return new MethodSpecification(startOffset, endOffset, isExtendingSpecification,
            specCaseList);
   }

   @Override
   public ISpecificationCase parseSpecificationCase(String text, int start,
         int end) throws ParserException {
      try {
         IBehaviorSpecification bSpec = parseBehaviorSpecification(text, start,
               end);
         return bSpec;
      }
      catch (ParserException e) {
         try {
            ILightweightSpecification lSpec = parseLightweightSpecification(
                  text, start, end);
            return lSpec;
         }
         catch (ParserException e2) {
            throw new ParserException("Unable to parse a specification case",
                  text, start);
         }
      }
   }

   private ILightweightSpecification parseLightweightSpecification(String text,
         int start, int end) throws ParserException {
      List<ISpecificationStatement> statements = new ArrayList<ISpecificationStatement>();
      // We need to parse at least one statement
      ISpecificationStatement spec = parseSpecificationStatement(text, start,
            end);
      int position = spec.getEndOffset() + 1;
      statements.add(spec);
      while (true) {
         try {
            spec = parseSpecificationStatement(text, position, end);
            position = spec.getEndOffset() + 1;
            statements.add(spec);
         }
         catch (ParserException e) {
            break;
         }
      }
      return new LightweightSpecification(statements.get(0).getStartOffset(),
            statements.get(statements.size() - 1).getEndOffset(), statements);
   }

   @Override
   public IBehaviorSpecification parseBehaviorSpecification(String text,
         int start, int end) throws ParserException {
      this.validatePositions(text, start, end);
      start = skipWhiteSpacesOrAt(text, start, end);
      ParseResult<Visibility> visibility = parseVisibility(text, start, end);
      int keywordStart = skipWhiteSpacesOrAt(text, visibility.end, end);
      int keywordEnd = getIdentifier(text, keywordStart, end);
      String keyword = text.substring(keywordStart, keywordEnd);
      IJMLBehaviorKeyword usedKeyword = null;
      for (IJMLBehaviorKeyword availableKeyword : this.profile
            .getSupportedBehaviors()) {
         if (availableKeyword.getKeywords().contains(keyword)) {
            usedKeyword = availableKeyword;
            break;
         }
      }
      if (usedKeyword == null) {
         throw new ParserException(
               "Expected an keyword for an behavior but got: \"" + keyword
                     + "\"", text, keywordStart);
      }
      // Parse specification statements
      List<ISpecificationStatement> statements = new ArrayList<ISpecificationStatement>();
      int position = keywordEnd + 1;
      // require one statement
      ISpecificationStatement statement = parseSpecificationStatement(text,
            position, end);
      statements.add(statement);
      position = statement.getEndOffset() + 1;
      while (true) {
         try {
            statement = parseSpecificationStatement(text, position, end);
            statements.add(statement);
            position = statement.getEndOffset() + 1;
         }
         catch (ParserException e) {
            break;
         }
      }

      int endOffset = statements.get(statements.size() - 1).getEndOffset();

      return new BehaviorSpecification(start, endOffset, visibility.t,
            usedKeyword, statements);
   }

   private ParseResult<Visibility> parseVisibility(String text, int start,
         int end) throws ParserException {
      int identifierStart = this.skipWhiteSpacesOrAt(text, start, end);
      int identifierEnd = this.getIdentifier(text, identifierStart, end);
      String keyword = text.substring(identifierStart, identifierEnd);
      Visibility v = null;
      if (keyword.equals("public")) {
         v = Visibility.PUBLIC;
      }
      else if (keyword.equals("protected")) {
         v = Visibility.PROTECTED;
      }
      else if (keyword.equals("private")) {
         v = Visibility.PRIVATE;
      }
      if (v != null) {
         return new ParseResult<Visibility>(v, identifierEnd);
      }
      else {
         return new ParseResult<Visibility>(Visibility.DEFAULT, start);
      }
   }

   @Override
   public ISpecificationStatement parseSpecificationStatement(String text,
         int start, int end) throws ParserException {
      this.validatePositions(text, start, end);
      int keywordStart = skipWhiteSpacesOrAt(text, start, end);
      if (keywordStart == end) {
         throw new ParserException(
               "Requires a specification statement keyword", text, end);
      }
      int keywordEnd = getIdentifier(text, keywordStart, end);
      String keyword = text.substring(keywordStart, keywordEnd);
      ISpecificationStatementKeyword foundKeyword = null;
      for (ISpecificationStatementKeyword availableKeyword : this.profile
            .getSupportedSpecificationStatementKeywords()) {
         if (keyword.equals(availableKeyword.getKeyword())) {
            foundKeyword = availableKeyword;
            break;
         }
      }
      if (foundKeyword == null) {
         throw new ParserException(
               "Not a supported specification statement keyword: \"" + keyword
                     + "\"", text, keywordEnd);
      }

      int closingSemicolon = scanForClosingSemicolon(text, keywordEnd, end);
      // Content without semicolon
      String content = text.substring(keywordEnd + 1, closingSemicolon);

      return new SpecificationStatement(keywordStart, closingSemicolon,
            foundKeyword, content);
   }

   private int scanForClosingSemicolon(String text, int start, int end)
         throws ParserException {
      boolean isStringOrChar = false;
      char quoteChar = ' ';
      int position = start;
      while (position < end) {
         char c = text.charAt(position);
         boolean isQuoteChar = c == '\'' || c == '\"';
         if (isQuoteChar && !isStringOrChar) {
            isStringOrChar = true;
            quoteChar = c;
         }
         else if (isStringOrChar) {
            if (c == '\\') {
               // now escaping a character in a string
               // this is not a ; to search for
               position = position + 2;
               // dont look at the next one
               continue;
            }
            else {
               if (c == quoteChar) {
                  // close string or char
                  isStringOrChar = false;
                  quoteChar = ' ';
               }
            }
         }
         if (!isStringOrChar) {
            if (c == ';') {
               break;
            }
         }
         position++;
      }
      if (position >= end) {
         throw new ParserException("No closing semicolon found", text, end);
      }
      return position;

   }

   private int getIdentifier(String text, int start, int end)
         throws ParserException {
      validatePositions(text, start, end);
      int position = start;
      if (start == end) {
         throw new ParserException("Expected an identifier", text, start);
      }
      if (!Character.isJavaIdentifierStart(text.charAt(position))) {
         throw new ParserException("Not a valid Java identifier", text,
               position);
      }
      position++;
      while (position < end
            && Character.isJavaIdentifierPart(text.charAt(position))) {
         position++;
      }
      return position;
   }

   private int skipWhiteSpacesOrAt(String text, int start, int end)
         throws ParserException {
      validatePositions(text, start, end);
      int position = start;
      while (position < end
            && ((text.charAt(position) == '@') || isWhitespace(text
                  .charAt(position)))) {
         position++;
      }
      return position;
   }

   private int skipWhiteSpaces(String text, int start, int end)
         throws ParserException {
      validatePositions(text, start, end);
      int position = start;
      while (position < end && isWhitespace(text.charAt(position))) {
         position++;
      }
      return position;
   }

   private boolean isWhitespace(char c) {
      return isWhitespaceWithoutNewLine(c) || c == '\n' || c == '\r';
   }

   private boolean isWhitespaceWithoutNewLine(int c) {
      return c == ' ' || c == '\t';
   }

}
