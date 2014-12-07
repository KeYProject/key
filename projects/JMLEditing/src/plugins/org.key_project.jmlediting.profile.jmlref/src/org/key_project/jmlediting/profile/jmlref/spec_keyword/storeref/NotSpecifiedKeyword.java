package org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;

public class NotSpecifiedKeyword extends AbstractEmptyKeyword implements
IStoreRefKeyword {

   public NotSpecifiedKeyword() {
      super("\\not_specified");
   }

   @Override
   public String getDescription() {
      return "The form \\not_specified denotes a unspecified set of locations, whose usage is determined by a particular tool";
   }

}
