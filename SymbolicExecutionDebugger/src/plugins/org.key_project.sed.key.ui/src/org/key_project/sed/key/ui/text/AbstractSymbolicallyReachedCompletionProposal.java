package org.key_project.sed.key.ui.text;

import java.util.List;

import org.eclipse.debug.ui.IDebugView;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.contentassist.ICompletionProposal;
import org.eclipse.jface.text.contentassist.IContextInformation;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.widgets.Shell;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.ui.text.SymbolicallyReachedAnnotation;
import org.key_project.sed.ui.util.SEDUIUtil;
import org.key_project.util.eclipse.swt.SWTUtil;

/**
 * A basic implementation of a proposal for {@link SymbolicallyReachedAnnotation}s 
 * which selects {@link ISEDDebugNode}s as solution.
 * @author Martin Hentschel
 */
public abstract class AbstractSymbolicallyReachedCompletionProposal implements ICompletionProposal {
   /**
    * The parent {@link Shell} which provides the {@link IDebugView}.
    */
   private final Shell shell;
   
   /**
    * The {@link ISEDDebugNode}s to select.
    */
   private final List<ISEDDebugNode> debugNodes;

   /**
    * Constructor.
    * @param shell The parent {@link Shell} which provides the {@link IDebugView}.
    * @param debugNodes The {@link ISEDDebugNode}s to select.
    */
   public AbstractSymbolicallyReachedCompletionProposal(Shell shell, List<ISEDDebugNode> debugNodes) {
      this.shell = shell;
      this.debugNodes = debugNodes;
   }
   
   /**
    * Returns the number of available {@link ISEDDebugNode}s.
    * @return The number of available {@link ISEDDebugNode}s.
    */
   protected int countNodes() {
      return debugNodes != null ? debugNodes.size() : 0;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void apply(IDocument document) {
      if (debugNodes != null) {
         IDebugView debugView = SEDUIUtil.getDebugView(shell);
         if (debugView != null) {
            SEDUIUtil.selectInDebugView(debugView.getSite().getPart(), debugView, SWTUtil.createSelection(debugNodes));
         }
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Point getSelection(IDocument document) {
      return null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getAdditionalProposalInfo() {
      return null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IContextInformation getContextInformation() {
      return null;
   }
}
