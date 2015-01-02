package org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;

/**
 * The \nothing keyword.
 *
 * @author Moritz Lichter
 *
 */
public class NothingKeyword extends AbstractEmptyKeyword implements
IStoreRefKeyword {

   /**
    * A new instance for the \nothing keyword.
    */
   public NothingKeyword() {
      super("\\nothing");
   }

   @Override
   public String getDescription() {
      return "Specifies that a method cannot assign to any locations.";
   }
}
