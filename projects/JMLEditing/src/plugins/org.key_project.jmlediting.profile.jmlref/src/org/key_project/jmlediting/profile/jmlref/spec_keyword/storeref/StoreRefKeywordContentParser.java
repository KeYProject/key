package org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.ParserBuilder;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;

/**
 * Parses the content after a keyword which requires a storage location (or
 * storage locations) as content, e.g. the assignable keyword.
 *
 * @author Moritz Lichter
 *
 */
public class StoreRefKeywordContentParser implements IKeywordParser {

   /**
    * The parser, which is used. The parser depends on the current profile
    * because this specifies the allowed keywords as storage locations.
    */
   private StoreRefParser parser;
   /**
    * Stores whether informal descriptions are allowed as storage locations.
    */
   private final boolean allowInformalDescription;

   private ParseFunction mainParser;

   /**
    * Crates a new {@link StoreRefKeywordContentParser}.
    *
    * @param allowInformalDescription
    *           whether the parser allows informal description
    */
   public StoreRefKeywordContentParser(final boolean allowInformalDescription) {
      super();
      this.allowInformalDescription = allowInformalDescription;
   }

   @Override
   public void setProfile(final IJMLProfile profile) {
      // This method is invoked before the parseToSemicolon method is invoked
      // Thus, the parser is valid then
      this.parser = new StoreRefParser(profile, this.allowInformalDescription);
      this.mainParser = ParserBuilder.closedBy(NodeTypes.KEYWORD_CONTENT,
            this.parser, ';');
   }

   /*
    * @Override protected IASTNode parseToSemicolon(final String text, final int
    * start, final int end) throws ParserException { // We require that the the
    * complete text to the semicolon is parseable return
    * ParserBuilder.requireComplete(this.parser).parse(text, start, end); }
    */

   @Override
   public IASTNode parse(final String text, final int start, final int end)
         throws ParserException {
      return this.mainParser.parse(text, start, end);
   }

}
