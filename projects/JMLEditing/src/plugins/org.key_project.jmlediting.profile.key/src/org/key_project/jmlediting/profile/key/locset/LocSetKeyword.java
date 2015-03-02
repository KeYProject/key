package org.key_project.jmlediting.profile.key.locset;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;
import org.key_project.jmlediting.profile.jmlref.type.ITypeKeyword;

public class LocSetKeyword extends AbstractEmptyKeyword implements ITypeKeyword {

   public LocSetKeyword() {
      super("\\locset");
   }

   @Override
   public String getDescription() {
      return null;
   }

}
