package org.key_project.jmlediting.profile.jmlref.spec_keyword;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.PredicateOrNotParser;

/**
 * Implementation of the diverges keyword.
 *
 * @author Moritz Lichter
 *
 */
public class DivergesKeyword extends AbstractGenericSpecificationKeyword {

   /**
    * Creates a new keyword instance.
    */
   public DivergesKeyword() {
      super("diverges", "diverges_redundantly");
   }

   @Override
   public String getDescription() {
      return "A diverges clause can be used to specify when a method "
            + "may either loop forever or not return normally to its caller";
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
