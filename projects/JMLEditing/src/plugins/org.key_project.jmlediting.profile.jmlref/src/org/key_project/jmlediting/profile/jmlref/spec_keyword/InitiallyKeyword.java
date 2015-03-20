package org.key_project.jmlediting.profile.jmlref.spec_keyword;

import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.profile.jmlref.parser.JMLRefParseFunctionKeywordParser;
import org.key_project.jmlediting.profile.jmlref.parser.PredicateContentParser;

/**
 * Implements the initially keyword.
 *
 * @author Moritz Lichter
 *
 */
public class InitiallyKeyword extends AbstractGenericSpecificationKeyword {

   /**
    * Creates a new keyword instance.
    */
   public InitiallyKeyword() {
      super("initially");
   }

   @Override
   public String getDescription() {
      return "The meaning of an initially-clause is that each non-helper constructor "
            + "for each concrete subtype of the enclosing type (including that type "
            + "itself, if it is concrete) must establish the predicate.";
   }

   @Override
   public IKeywordParser createParser() {
      return JMLRefParseFunctionKeywordParser
            .semicolonClosed(new PredicateContentParser());
   }

}
