package org.key_project.sed.key.ui.text;

import org.eclipse.debug.ui.DebugUITools;
import org.eclipse.debug.ui.IDebugModelPresentation;
import org.eclipse.debug.ui.IDebugView;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.contentassist.ICompletionProposal;
import org.eclipse.jface.text.contentassist.IContextInformation;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.widgets.Shell;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.ui.text.SymbolicallyReachedAnnotation;
import org.key_project.sed.ui.util.SEDUIUtil;
import org.key_project.util.eclipse.swt.SWTUtil;

/**
 * An proposal for {@link SymbolicallyReachedAnnotation}s which selects an
 * {@link ISEDDebugNode} as solution.
 * @author Martin Hentschel
 */
public class SymbolicallyReachedCompletionProposal implements ICompletionProposal {
   /**
    * The parent {@link Shell} which provides the {@link IDebugView}.
    */
   private final Shell shell;
   
   /**
    * The {@link ISEDDebugNode} to select.
    */
   private final ISEDDebugNode debugNode;

   /**
    * Constructor.
    * @param shell The parent {@link Shell} which provides the {@link IDebugView}.
    * @param debugNode The {@link ISEDDebugNode} to select.
    */
   public SymbolicallyReachedCompletionProposal(Shell shell, ISEDDebugNode debugNode) {
      this.shell = shell;
      this.debugNode = debugNode;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void apply(IDocument document) {
      IDebugView debugView = SEDUIUtil.getDebugView(shell);
      if (debugView != null) {
         SEDUIUtil.selectInDebugView(debugView.getSite().getPart(), debugView, SWTUtil.createSelection(debugNode));
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
   public String getDisplayString() {
      IDebugModelPresentation debugModelPresentation = DebugUITools.newDebugModelPresentation();
      try {
         return debugModelPresentation.getText(debugNode);
      }
      finally {
         debugModelPresentation.dispose();
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Image getImage() {
      IDebugModelPresentation debugModelPresentation = DebugUITools.newDebugModelPresentation();
      try {
         return debugModelPresentation.getImage(debugNode);
      }
      finally {
         debugModelPresentation.dispose();
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IContextInformation getContextInformation() {
      return null;
   }
}
