package org.key_project.sed.key.ui.text;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.jdt.internal.ui.text.java.hover.AbstractAnnotationHover;
import org.eclipse.jdt.ui.text.java.hover.IJavaEditorTextHover;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.contentassist.ICompletionProposal;
import org.eclipse.jface.text.source.Annotation;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.widgets.Shell;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.sourcesummary.ISEDSourceRange;
import org.key_project.sed.ui.text.SymbolicallyReachedAnnotation;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.thread.AbstractRunnableWithResult;
import org.key_project.util.java.thread.IRunnableWithResult;

/**
 * An {@link IJavaEditorTextHover} which provides quick fix proposals
 * ({@link SymbolicallyReachedCompletionProposal}) for {@link SymbolicallyReachedAnnotation}s.
 * @author Martin Hentschel
 */
// TODO: Move this functionality in general SED Java plug-in after merge with JPF branch.
@SuppressWarnings("restriction")
public class SymbolicallyReachedJavaEditorTextHover extends AbstractAnnotationHover {
   /**
    * Constructor.
    */
   public SymbolicallyReachedJavaEditorTextHover() {
      super(true);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected AnnotationInfo createAnnotationInfo(Annotation annotation, Position position, ITextViewer textViewer) {
      if (annotation instanceof SymbolicallyReachedAnnotation) {
         final StyledText text = textViewer.getTextWidget();
         IRunnableWithResult<Shell> run = new AbstractRunnableWithResult<Shell>() {
            @Override
            public void run() {
               setResult(text.getShell());
            }
         };
         text.getDisplay().syncExec(run);
         final Shell shell = run.getResult();
         final SymbolicallyReachedAnnotation sedAnnotation = (SymbolicallyReachedAnnotation)annotation;
         return new AnnotationInfo(annotation, position, textViewer) {
            @Override
            public ICompletionProposal[] getCompletionProposals() {
               List<ISEDDebugNode> nodes = new LinkedList<ISEDDebugNode>();
               for (ISEDSourceRange range : sedAnnotation.getRanges()) {
                  CollectionUtil.addAll(nodes, range.getDebugNodes());
               }
               if (nodes.size() >= 2) {
                  ICompletionProposal[] proposals = new ICompletionProposal[nodes.size() + 1];
                  proposals[0] = new AllSymbolicallyReachedCompletionProposal(shell, nodes);
                  int i = 1;
                  for (ISEDDebugNode node : nodes) {
                     proposals[i] = new SymbolicallyReachedCompletionProposal(shell, node);
                     i++;
                  }
                  return proposals;
               }
               else if (nodes.size() == 1){
                  return new ICompletionProposal[] {new SymbolicallyReachedCompletionProposal(shell, nodes.get(0))};
               }
               else {
                  return new ICompletionProposal[0];
               }
            }
         };
      }
      else {
         return null;
      }
   }
}
