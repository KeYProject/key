package org.key_project.sed.ui.property;

import org.eclipse.swt.widgets.Composite;
import org.key_project.sed.core.model.ISEDDebugNode;

/**
 * Provides the basic functionalities for a content {@link Composite}
 * shown in an {@link AbstractSEDDebugNodePropertySection}.
 * @author Martin Hentschel
 */
public abstract class AbstractSEDDebugNodeTabComposite extends Composite {
   /**
    * Constructor.
    * @param parent The parent {@link Composite}.
    * @param style The style to use.
    */
   public AbstractSEDDebugNodeTabComposite(Composite parent, int style) {
      super(parent, style);
   }

   /**
    * Updates the shown content.
    * @param node The {@link ISEDDebugNode} which provides the new content.
    */
   public abstract void updateContent(ISEDDebugNode node);
}
