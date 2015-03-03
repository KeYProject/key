package org.key_project.jmlediting.profile.key.other;

import org.key_project.jmlediting.core.profile.syntax.AbstractJMLPrimaryKeyword;
import org.key_project.jmlediting.core.profile.syntax.EmptyKeywordParser;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.profile.key.KeyProfile;

/**
 * Partial implementation of the inv keyword. This class registers inv as a
 * primitive, so requires \inv; is valid now. It does not support inv as in a
 * access sequence like ensures o.\inv; This is implemented in the
 * {@link KeyProfile} itself.
 *
 * @author Moritz Lichter
 *
 */
public class InvKeyword extends AbstractJMLPrimaryKeyword {
   /**
    * Create s a new instance of the keyword.
    */
   public InvKeyword() {
      super("\\inv");
   }

   @Override
   public String getDescription() {
      return "The \\inv operator returns true just when the invariant of the object where \\inv is accessed for is valid.";
   }

   @Override
   public IKeywordParser createParser() {
      return EmptyKeywordParser.getInstance();
   }

}
