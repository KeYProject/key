package org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression;

import static org.key_project.jmlediting.core.parser.ParserBuilder.*;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.NotSpecifiedKeyword;

/**
 * The {@link PredicateOrNotParser} parses predicates or a not specified
 * keyword.
 *
 * @author Moritz Lichter
 *
 */
public class PredicateOrNotParser implements ParseFunction {

   /**
    * The main parser.
    */
   private final ParseFunction parser;

   /**
    * Creates a new {@link PredicateOrNotParser} for the given profile.
    *
    * @param profile
    *           the profile
    */
   public PredicateOrNotParser(final IJMLExpressionProfile profile) {
      this.parser = alt(new PredicateParser(profile),
            keywords(NotSpecifiedKeyword.class, profile));
   }

   @Override
   public IASTNode parse(final String text, final int start, final int end)
         throws ParserException {
      return this.parser.parse(text, start, end);
   }

}
