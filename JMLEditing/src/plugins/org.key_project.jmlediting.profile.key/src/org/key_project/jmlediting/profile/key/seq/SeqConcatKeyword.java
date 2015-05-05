package org.key_project.jmlediting.profile.key.seq;

/**
 * The seq concat keyword for KeY.
 *
 * @author Moritz Lichter
 *
 */
public class SeqConcatKeyword extends BinaryOpSeqPrimitiveKeyword {

   /**
    * Creates a new instance of seq concat.
    */
   public SeqConcatKeyword() {
      super("\\seq_concat");
   }

   @Override
   public String getDescription() {
      return null;
   }

}
