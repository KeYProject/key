package org.key_project.jmlediting.core.profile.syntax;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.IJMLProfile;

/**
 * An {@link IKeywordParser} defines who to parse the content after an
 * occurrence of a keyword.
 *
 * @author Moritz Lichter
 *
 */
public interface IKeywordParser extends ParseFunction {

   /**
    * Sets the profile according to which is parsed. Most parser probably do not
    * need it, but some may. The setProfile method is invoked exactly once after
    * creating an {@link IKeywordParser} by calling
    * {@link IKeyword#createParser()} and the call is done before parsing.
    *
    * @param profile
    *           the profile for which it is parsed
    */
   void setProfile(IJMLProfile profile);

}
