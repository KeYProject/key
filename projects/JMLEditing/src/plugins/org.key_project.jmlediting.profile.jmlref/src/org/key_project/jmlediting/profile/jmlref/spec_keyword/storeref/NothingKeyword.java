package org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;

public class NothingKeyword extends AbstractEmptyKeyword implements
      IStoreRefKeyword {

   public NothingKeyword() {
      super("\\nothing");
   }

   @Override
   public String getDescription() {
      return "Specifies that a method cannot assign to any locations.";
   }
}
