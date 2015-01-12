package org.key_project.jmlediting.profile.jmlref.spec_keyword.requires;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;

/**
 * Implementation for the \same keyword.
 *
 * @author Moritz Lichter
 *
 */
public class SameKeyword extends AbstractEmptyKeyword implements
      IRequiresValueKeyword {

   /**
    * Creates a new instance of the same keyword.
    */
   public SameKeyword() {
      super("\\same");
   }

   @Override
   public String getDescription() {
      return null;
   }

}
