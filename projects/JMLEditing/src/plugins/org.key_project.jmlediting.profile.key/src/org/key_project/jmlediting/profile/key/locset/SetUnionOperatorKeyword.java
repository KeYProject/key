package org.key_project.jmlediting.profile.key.locset;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;

public class SetUnionOperatorKeyword extends AbstractEmptyKeyword implements
      ILocSetOperatorKeyword {

   public SetUnionOperatorKeyword() {
      super("\\set_union");
   }

   @Override
   public String getDescription() {
      return null;
   }

}
