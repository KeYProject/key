package org.key_project.jmlediting.core.profile.syntax;

import java.util.List;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.utilities.CommentRange;
import org.key_project.jmlediting.core.utilities.JMLValidationError;
import org.key_project.jmlediting.core.validation.IJMLValidationContext;

public abstract class AbstractKeywordValidator implements IKeywordValidator {

   protected final String MARKER_ID;

   public AbstractKeywordValidator(final String ID) {
      this.MARKER_ID = ID;
   }

   @Override
   public abstract List<JMLValidationError> validate(CommentRange c,
         IJMLValidationContext context, IASTNode node);

}
