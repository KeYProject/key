package org.key_project.jmlediting.profile.jmlref.spec_keyword;

import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.profile.jmlref.parser.JMLRefParseFunctionKeywordParser;
import org.key_project.jmlediting.profile.jmlref.parser.PredicateOtNotSpecifiedParser;

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
      return JMLRefParseFunctionKeywordParser
            .semicolonClosed(new PredicateOtNotSpecifiedParser());
   }

}
