package org.key_project.jmlediting.core.validation;

import java.util.ArrayList;
import java.util.List;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.IKeywordNode;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.utilities.CommentRange;
import org.key_project.jmlediting.core.utilities.JMLValidationError;

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
    *
    * @param node
    *           the parse result for CommentRange c
    */
   public List<JMLValidationError> validateComment(final CommentRange c,
         final IASTNode node) {
      final List<JMLValidationError> errors = new ArrayList<JMLValidationError>();
      IKeywordValidator validator = null;
      for (final IKeywordNode keywordNode : Nodes.getAllKeywords(node)) {
         validator = keywordNode.getKeyword().getKeywordValidator();
         if (validator != null) {
            errors.addAll(validator.validate(c, this.context, node));
         }
      }
      return errors;
   }
}
