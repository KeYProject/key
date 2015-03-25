package org.key_project.jmlediting.profile.key.other;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordSort;

/**
 * The measured_by which can be used inside an accessible keyword. This is not
 * the same as the toplevel measured_by keyword.
 *
 * @author Moritz Lichter
 *
 */
public class AccessibleMeasuredByKeyword extends AbstractEmptyKeyword {

   /**
    * Creates a new instance.
    */
   public AccessibleMeasuredByKeyword() {
      super("measured_by", "\\measured_by");
   }

   @Override
   public IKeywordSort getSort() {
      return null;
   }

   @Override
   public String getDescription() {
      return null;
   }

}
