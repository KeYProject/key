package org.key_project.jmlediting.profile.jmlref;

import java.util.Set;

import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.profile.jmlref.primary.IJMLPrimary;

public interface IJMLExpressionProfile extends IJMLProfile {

   /**
    * Returns a set of all supported JML primaries in expression. The returned
    * set is not allowed to be modified and is guaranteed not to be null.
    *
    * @return the set of all supported primaries
    */
   Set<IJMLPrimary> getSupportedPrimaries();

}
