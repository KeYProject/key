package org.key_project.jmlediting.profile.jmlref.model;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywortSort;

/**
 * The implementation of the such that keyword which is used in the
 * {@link RepresentsKeyword}.
 *
 * @author Moritz Lichter
 *
 */
public class SuchThatKeyword extends AbstractEmptyKeyword {

   /**
    * Creates a new instance.
    */
   public SuchThatKeyword() {
      super("\\such_that");
   }

   @Override
   public String getDescription() {
      return null;
   }

   @Override
   public IKeywortSort getSort() {
      return null;
   }

}
