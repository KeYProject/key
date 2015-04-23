package org.key_project.jmlediting.profile.jmlref.primary;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;

/**
 * A {@link IJMLProfile} is a special parse function which is injected into JML
 * expressions as a new primary. See the section to primaries in the <a href=
 * "http://www.eecs.ucf.edu/~leavens/JML/jmlrefman/jmlrefman_12.html#SEC129"
 * >Reference Manual</a>.
 *
 * @author Moritz Lichter
 *
 */
public interface IJMLPrimary extends ParseFunction {

   /**
    * Sets the profile according to which is parsed. Most parser probably do not
    * need it, but some may. The setProfile method is invoked exactly once after
    * creating an {@link IKeywordParser} by calling
    * {@link IKeyword#createParser()} and the call is done before parsing.
    *
    * @param profile
    *           the profile for which it is parsed
    */
   void setProfile(IJMLExpressionProfile profile);

}
