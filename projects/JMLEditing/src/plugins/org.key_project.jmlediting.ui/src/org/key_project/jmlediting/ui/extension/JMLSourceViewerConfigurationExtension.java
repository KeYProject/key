package org.key_project.jmlediting.ui.extension;

import org.eclipse.jdt.internal.ui.text.JavaPresentationReconciler;
import org.eclipse.jface.text.IDocumentPartitioner;
import org.eclipse.jface.text.TextAttribute;
import org.eclipse.jface.text.presentation.IPresentationReconciler;
import org.eclipse.jface.text.presentation.PresentationReconciler;
import org.eclipse.jface.text.rules.DefaultDamagerRepairer;
import org.eclipse.jface.text.rules.FastPartitioner;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.ui.texteditor.ITextEditor;
import org.key_project.javaeditor.extension.DefaultJavaSourceViewerConfigurationExtension;
import org.key_project.javaeditor.extension.IJavaSourceViewerConfigurationExtension;

/**
 * An {@link IJavaSourceViewerConfigurationExtension} to support JML.
 * 
 * @author Martin Hentschel
 */
public class JMLSourceViewerConfigurationExtension extends
      DefaultJavaSourceViewerConfigurationExtension {
   /**
    * {@inheritDoc}
    */
   @Override
   public int getTabWidth(ISourceViewer sourceViewer, int currentResult) {
      //TODO is this Method called only once? 
      return currentResult * 2;
   }

   @Override
   public IPresentationReconciler getPresentationReconciler(
         ISourceViewer sourceViewer, IPresentationReconciler currentResult) {
         PresentationReconciler JMLPresentationReconciler = (PresentationReconciler) currentResult;
         JMLPartitionScanner js= new JMLPartitionScanner();
         System.out.println("Constructor JML PresReconciler");
         FastPartitioner JMLPartitioner = new FastPartitioner(js,JMLPartitionScanner.getLegalContentTypes());
         JMLPartitioner.connect(sourceViewer.getDocument());
         sourceViewer.getDocument().setDocumentPartitioner((JMLPartitioner)); 
         DefaultDamagerRepairer dr= new DefaultDamagerRepairer(new SingleTokenScanner
               (new TextAttribute(this.getColorManager().getColor(new RGB (255,0,0)))));
         JMLPresentationReconciler.setDamager(dr,JMLPartitionScanner.JML_SINGLE_LINE);
         JMLPresentationReconciler.setDamager(dr, JMLPartitionScanner.JML_MULTI_LINE);
         JMLPresentationReconciler.setRepairer(dr, JMLPartitionScanner.JML_SINGLE_LINE);
         JMLPresentationReconciler.setRepairer(dr, JMLPartitionScanner.JML_MULTI_LINE);
         return JMLPresentationReconciler;
      }
   
   /**
    * @return extendedContentTypes A List of the previously defined
    *         ContentTypes, with JMLMultiLine content at first position in the
    *         array, and JMLSingleLine content on the second position followed
    *         by the previously defined content Types
    */
   @Override
   public String[] getConfiguredContentTypes(ISourceViewer sourceViewer,
         String[] currentResult) {
      if (currentResult[0].equals(JMLPartitionScanner.JML_MULTI_LINE)) //if Method was called
         return currentResult;                                         //previously there is
      else {                                                           // nothing to change
         String[] extendedContentTypes = new String[currentResult.length + 2];
         extendedContentTypes[0] = currentResult[0];
         extendedContentTypes[1] = JMLPartitionScanner.JML_MULTI_LINE;
         extendedContentTypes[2] = JMLPartitionScanner.JML_SINGLE_LINE;
         for (int i = 1; i < currentResult.length; i++) {
            extendedContentTypes[i + 2] = currentResult[i];
         }
         return extendedContentTypes;
      }
   }
}
