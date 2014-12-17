package org.key_project.jmlediting.profile.key.other;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.IStoreRefKeyword;

public class StrictlyNothingKeyword extends AbstractEmptyKeyword implements
      IStoreRefKeyword {

   public StrictlyNothingKeyword() {
      super("\\strictly_nothing");
   }

   @Override
   public String getDescription() {
      return "Specifies that a method cannot assign to any locations.<br> <b> The strictly_nothing disallows the creation of new objects additionally.<br>";
   }

}
