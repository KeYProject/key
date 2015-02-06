package org.key_project.jmlediting.profile.jmlref.spec_keyword;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.PredicateOrNotParser;

/**
 * The ensures keyword.
 *
 * @author Moritz Lichter
 *
 */
public class EnsuresKeyword extends AbstractGenericSpecificationKeyword {

   /**
    * Creates a new ensures keyword instance.
    */
   public EnsuresKeyword() {
      super("ensures");
   }

   @Override
   public String getDescription() {
      return "An ensures clause specifies a normal postcondition, i.e., a property "
            + "that is guaranteed to hold at the end of the method (or constructor) "
            + "invocation in the case that this method (or constructor) invocation "
            + "returns without throwing an exception.";
   }

   @Override
   public IKeywordParser createParser() {
      return new SemicolonClosedKeywordParser() {

         @Override
         protected ParseFunction createContentParseFunction(
               final IJMLProfile profile) {
            return new PredicateOrNotParser(profile);
         }
      };
   }

}
