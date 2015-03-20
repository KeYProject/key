package org.key_project.jmlediting.profile.key.seq;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordSort;

/**
 * The seq def keyowrd. Does not belong to any sort because it is explicitly
 * used in the parser.
 *
 * @author Moritz Lichter
 *
 */
public class SeqDefKeyword extends AbstractEmptyKeyword {

   /**
    * Creates a new seq def keyword instance.
    */
   public SeqDefKeyword() {
      super("\\seq_def");
   }

   @Override
   public String getDescription() {
      return null;
   }

   @Override
   public IKeywordSort getSort() {
      return null;
   }

}
