package org.key_project.jmlediting.profile.key.seq;

/**
 * The seq contains keyword for key.
 *
 * @author Moritz Lichter
 *
 */
public class ContainsKeyword extends BinaryOpSeqPrimitiveKeyword {

   /**
    * Creates a new contains keyword instance.
    */
   public ContainsKeyword() {
      super("\\contains");
   }

   @Override
   public String getDescription() {
      return null;
   }

}
