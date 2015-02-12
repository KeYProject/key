package org.key_project.sed.key.ui.text;

import java.util.Collections;

import org.eclipse.debug.ui.DebugUITools;
import org.eclipse.debug.ui.IDebugModelPresentation;
import org.eclipse.debug.ui.IDebugView;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Shell;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.ui.text.SymbolicallyReachedAnnotation;

/**
 * An proposal for {@link SymbolicallyReachedAnnotation}s which selects an
 * {@link ISEDDebugNode} as solution.
 * @author Martin Hentschel
 */
public class SymbolicallyReachedCompletionProposal extends AbstractSymbolicallyReachedCompletionProposal {
   /**
    * The shown text.
    */
   private final String displayString;
   
   /**
    * The shown {@link Image}.
    */
   private final Image image;
   
   /**
    * Constructor.
    * @param shell The parent {@link Shell} which provides the {@link IDebugView}.
    * @param debugNode The {@link ISEDDebugNode} to select.
    */
   public SymbolicallyReachedCompletionProposal(Shell shell, ISEDDebugNode debugNode) {
      super(shell, Collections.singletonList(debugNode));
      IDebugModelPresentation debugModelPresentation = DebugUITools.newDebugModelPresentation();
      try {
         displayString = "Select " + debugModelPresentation.getText(debugNode);
         image = debugModelPresentation.getImage(debugNode);;
      }
      finally {
         debugModelPresentation.dispose();
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getDisplayString() {
      return displayString;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Image getImage() {
      return image;
   }
}
