package org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression;

import org.key_project.jmlediting.core.profile.IJMLProfile;

/**
 * A parser which parses a spec expression, which is a new label for an
 * expression.
 *
 * @author Moritz Lichter
 *
 */
public class SpecExpressionParser extends ExpressionParser {

   /**
    * Creates a new parser for the given profile.
    * 
    * @param profile
    *           the profile which defines the supported JML primaries
    */
   public SpecExpressionParser(final IJMLProfile profile) {
      super(profile);
   }

}
