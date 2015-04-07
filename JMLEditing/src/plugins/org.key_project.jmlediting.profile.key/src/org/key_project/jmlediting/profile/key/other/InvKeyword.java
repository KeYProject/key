package org.key_project.jmlediting.profile.key.other;

import static org.key_project.jmlediting.core.parser.ParserBuilder.*;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.syntax.EmptyKeywordParser;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;
import org.key_project.jmlediting.profile.jmlref.primary.AbstractJMLPrimaryKeyword;
import org.key_project.jmlediting.profile.key.KeYProfile;

/**
 * Partial implementation of the inv keyword. This class registers inv as a
 * primitive, so requires \inv; is valid now. It does not support inv as in a
 * access sequence like ensures o.\inv; This is implemented in the
 * {@link KeYProfile} itself.
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
      return "The \\inv operator returns true just when the invariant of"
            + "the object where \\inv is accessed for is valid.";
   }

   @Override
   public IKeywordParser createParser() {
      return EmptyKeywordParser.getInstance();
   }

   public static ParseFunction invSuffix(final IJMLExpressionProfile profile) {
      return separateBy('.', keywords(InvKeyword.class, profile));
   }

}
