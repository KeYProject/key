package org.key_project.jmlediting.profile.key.seq;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;

public class SeqEmptyKeyword extends AbstractEmptyKeyword implements SeqPrimitiveKeyword {

   public SeqEmptyKeyword() {
      super("\\seq_empty");
   }

   @Override
   public String getDescription() {
      return null;
   }

}
