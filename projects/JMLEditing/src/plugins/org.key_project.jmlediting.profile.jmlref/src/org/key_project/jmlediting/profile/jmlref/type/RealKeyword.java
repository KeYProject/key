package org.key_project.jmlediting.profile.jmlref.type;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;

/**
 * Implementation of the real keyword.
 *
 * @author Moritz Lichter
 *
 */
public class RealKeyword extends AbstractEmptyKeyword implements ITypeKeyword {

   /**
    * No instance of real.
    */
   public RealKeyword() {
      super("\\real");
   }

   @Override
   public String getDescription() {
      return "The type \real models arbitrary precision floating point numbers.";
   }

}
