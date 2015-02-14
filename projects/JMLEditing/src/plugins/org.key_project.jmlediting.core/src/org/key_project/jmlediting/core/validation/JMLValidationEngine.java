package org.key_project.jmlediting.core.validation;

import java.util.Collections;
import java.util.List;
import java.util.Set;

import org.eclipse.core.resources.IMarker;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.profile.IJMLProfile;

/**
 *
 * @author David Giessing
 *
 */
public class JMLValidationEngine {

   /**
    * The project activeProfile.
    */
   private final IJMLProfile activeProfile;

   /**
    * the Validation Context used for the Validation.
    */
   private final IJMLValidationContext context;

   /**
    * creates a new JMLValidationEngine.
    *
    * @param activeProfile
    *           the project ActiveProfile
    * @param context
    *           the Validation context that is used for validation
    */
   public JMLValidationEngine(final IJMLProfile activeProfile,
         final IJMLValidationContext context) {
      this.activeProfile = activeProfile;
      this.context = context;
   }

   /**
    * validates all JMLSpecifications in a comment that can be validated via the
    * Profile specific Validators. If a Specification is not valid ErrorMarkers
    * are added to the List
    *
    * @param c
    *           the JMLComment that has to be validated represented by its Top
    *           Node
    * @return a List of IMarkers that represent invalid specifications,
    *         emptylist if all specifications are valid (or could not be checked
    *         because there was no validator)
    */
   public List<IMarker> validateComment(final IASTNode c) {
      final List<IMarker> markers = Collections.emptyList();
      final Set<IJMLValidator> validator = this.activeProfile.getValidator();
      for (final IJMLValidator jmlValidator : validator) {
         markers.addAll(jmlValidator.validate(this.context, c));

      }
      return markers;
   }
}
