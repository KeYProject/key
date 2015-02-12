package org.key_project.sed.key.ui.text;

import java.util.List;

import org.eclipse.debug.ui.IDebugView;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Shell;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.ui.text.SymbolicallyReachedAnnotation;

/**
 * An proposal for {@link SymbolicallyReachedAnnotation}s which selects multiple
 * {@link ISEDDebugNode}s as solution.
 * @author Martin Hentschel
 */
public class AllSymbolicallyReachedCompletionProposal extends AbstractSymbolicallyReachedCompletionProposal {
   /**
    * Constructor.
    * @param shell The parent {@link Shell} which provides the {@link IDebugView}.
    * @param debugNodes The {@link ISEDDebugNode}s to select.
    */
   public AllSymbolicallyReachedCompletionProposal(Shell shell, List<ISEDDebugNode> debugNodes) {
      super(shell, debugNodes);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getDisplayString() {
      return "Select all " + countNodes() + " nodes";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Image getImage() {
      return null;
   }
}
