package org.key_project.jmlediting.profile.key.seq;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;

public class ValuesKeyword extends AbstractEmptyKeyword implements SeqPrimitiveKeyword {

   public ValuesKeyword() {
      super("\\values");
   }

   @Override
   public String getDescription() {
      return null;
   }

}
