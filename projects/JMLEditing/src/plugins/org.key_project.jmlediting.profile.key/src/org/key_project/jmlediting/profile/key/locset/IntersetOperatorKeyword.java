package org.key_project.jmlediting.profile.key.locset;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;

public class IntersetOperatorKeyword extends AbstractEmptyKeyword implements
      ILocSetOperatorKeyword {

   public IntersetOperatorKeyword() {
      super("\\intersect");
   }

   @Override
   public String getDescription() {
      return null;
   }

}
