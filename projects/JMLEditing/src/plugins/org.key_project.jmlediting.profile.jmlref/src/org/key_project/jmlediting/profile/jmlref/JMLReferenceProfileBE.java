package org.key_project.jmlediting.profile.jmlref;

/**
 * The JML reference profile for British English keywords.
 *
 * @author Moritz Lichter
 *
 */
public class JMLReferenceProfileBE extends JMLReferenceProfile {

   /**
    * Creates a new profile instance.
    */
   public JMLReferenceProfileBE() {
      super(KeywordLocale.BRITISH);
   }

   @Override
   public String getName() {
      return "JML Reference (British)";
   }

   @Override
   public String getIdentifier() {
      return "org.key_project.jmlediting.profile.jmlref.be";
   }

}
