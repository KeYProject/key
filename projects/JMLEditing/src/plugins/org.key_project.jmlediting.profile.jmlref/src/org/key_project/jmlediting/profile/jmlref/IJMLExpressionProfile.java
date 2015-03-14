package org.key_project.jmlediting.profile.jmlref;

import java.util.Set;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.profile.jmlref.primary.IJMLPrimary;

/**
 * A specialized version of an {@link IJMLProfile} which uses expression as
 * defined in the JML reference manual. This profile allows concrete profiles to
 * modify the supported expressions.
 * 
 * @author Moritz Lichter
 *
 */
public interface IJMLExpressionProfile extends IJMLProfile {

   /**
    * Returns a set of all supported JML primaries in expression. The returned
    * set is not allowed to be modified and is guaranteed not to be null.
    *
    * @return the set of all supported primaries
    */
   Set<IJMLPrimary> getSupportedPrimaries();

   /**
    * Provides alternative parse functions for suffixes to primaries which
    * extend the ones defined in the JML reference manual.
    *
    * @return a non null set of parse functions
    */
   Set<ParseFunction> getPrimarySuffixExtensions();

}
