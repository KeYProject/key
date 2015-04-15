package org.key_project.jmlediting.profile.jmlref.primary;

import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.profile.jmlref.parser.UnarySpecExpressionArgParser;

/**
 * Implementation of the invariant keyword.
 *
 * @author Moritz Lichter
 *
 */
public class InvariantForKeyword extends AbstractJMLPrimaryKeyword {

   /**
    * Creates new instance for the invariant_for keyword.
    */
   public InvariantForKeyword() {
      super("\\invariant_for");
   }

   @Override
   public String getDescription() {
      return "The \\invariant_for operator returns true just when its argument satisfies the "
            + "invariant of its static type.";
   }

   @Override
   public IKeywordParser createParser() {
      return new UnarySpecExpressionArgParser();
   }
}
