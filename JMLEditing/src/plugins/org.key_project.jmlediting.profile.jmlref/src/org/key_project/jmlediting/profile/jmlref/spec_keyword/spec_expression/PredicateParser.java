package org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression;

import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;

/**
 * A predicate parser parses a predicate e.g. for an requires clause. A
 * predicate is an spec expression with type boolean, which is not implemented
 * in the grammar. Any expression is parsed.
 *
 * @author Moritz Lichter
 *
 */
public class PredicateParser extends SpecExpressionParser {

   /**
    * Creates a new parser instance for the given profile.
    *
    * @param profile
    *           the profile that defines the supported JML primaries.
    */
   public PredicateParser(final IJMLExpressionProfile profile) {
      super(profile);
   }

}
