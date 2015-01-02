package org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;

/**
 * The \everything keyword.
 *
 * @author Moritz Lichter
 *
 */
public class EverythingKeyword extends AbstractEmptyKeyword implements
IStoreRefKeyword {

   /**
    * Creates a new instance for the \everything keyword.
    */
   public EverythingKeyword() {
      super("\\everything");
   }

   @Override
   public String getDescription() {
      return "Specifies that a method can assign to any locations.";
   }

}
