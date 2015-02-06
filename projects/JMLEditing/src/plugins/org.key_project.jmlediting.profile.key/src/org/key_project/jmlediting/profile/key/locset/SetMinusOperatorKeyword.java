package org.key_project.jmlediting.profile.key.locset;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;

public class SetMinusOperatorKeyword extends AbstractEmptyKeyword implements
      ILocSetOperatorKeyword {

   public SetMinusOperatorKeyword() {
      super("\\set_minus");
   }

   @Override
   public String getDescription() {
      return null;
   }

}
