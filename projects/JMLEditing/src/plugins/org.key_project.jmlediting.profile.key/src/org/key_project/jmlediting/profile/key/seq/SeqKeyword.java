package org.key_project.jmlediting.profile.key.seq;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;
import org.key_project.jmlediting.profile.jmlref.type.ITypeKeyword;

public class SeqKeyword extends AbstractEmptyKeyword implements ITypeKeyword {

   public SeqKeyword() {
      super("\\seq");
   }

   @Override
   public String getDescription() {
      return null;
   }

}
