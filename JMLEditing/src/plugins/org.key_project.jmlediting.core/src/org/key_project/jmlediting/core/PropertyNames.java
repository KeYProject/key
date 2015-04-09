package org.key_project.jmlediting.core;

import org.eclipse.core.runtime.QualifiedName;

/**
 * This class contains property and preferences key used for JML.
 *
 * @author Moritz Lichter
 *
 */
public final class PropertyNames {
   /**
    * The name of the JML profile property of a project.
    */
   public static final QualifiedName PROFILE = new QualifiedName("org.key_project.jmleiditing.ui", "profile");

   /**
    * The name of the global preference for the default JML profile.
    */
   public static final String DEFAULT_JML_PROFILE = "default_jml_profile";

   /**
    * No instantiations.
    */
   private PropertyNames() {
   }
}
