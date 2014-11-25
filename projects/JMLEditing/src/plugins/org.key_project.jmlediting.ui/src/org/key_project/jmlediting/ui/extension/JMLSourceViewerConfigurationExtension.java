package org.key_project.jmlediting.ui.extension;

import org.eclipse.jdt.ui.text.IJavaPartitions;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.presentation.IPresentationReconciler;
import org.eclipse.jface.text.presentation.PresentationReconciler;
import org.eclipse.jface.text.rules.DefaultDamagerRepairer;
import org.eclipse.jface.text.source.ISourceViewer;
import org.key_project.javaeditor.extension.DefaultJavaSourceViewerConfigurationExtension;
import org.key_project.javaeditor.extension.IJavaSourceViewerConfigurationExtension;

/**
 * An {@link IJavaSourceViewerConfigurationExtension} to support JML.
 * 
 * @author Martin Hentschel, David Giessing
 */

public class JMLSourceViewerConfigurationExtension extends
      DefaultJavaSourceViewerConfigurationExtension {

   IDocument document;

   public JMLSourceViewerConfigurationExtension() {

   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int getTabWidth(ISourceViewer sourceViewer, int currentResult) {
      this.document = sourceViewer.getDocument();
      return currentResult * 2;
   }

   @Override
   public IPresentationReconciler getPresentationReconciler(ISourceViewer sourceViewer, IPresentationReconciler currentResult) {
      PresentationReconciler reconciler = (PresentationReconciler)currentResult;
      // Replace DefaultDamagerRepairer in currentResult to support JML 
      DefaultDamagerRepairer dr= (DefaultDamagerRepairer)reconciler.getDamager(IJavaPartitions.JAVA_MULTI_LINE_COMMENT);
      JMLPresentationDamagerRepairer newDR = new JMLPresentationDamagerRepairer(dr);
      reconciler.setDamager(newDR, IJavaPartitions.JAVA_MULTI_LINE_COMMENT);
      reconciler.setRepairer(newDR, IJavaPartitions.JAVA_MULTI_LINE_COMMENT);
      // Replace DefaultDamagerRepairer in currentResult to support JML 
      dr= (DefaultDamagerRepairer)reconciler.getDamager(IJavaPartitions.JAVA_SINGLE_LINE_COMMENT);
      newDR = new JMLPresentationDamagerRepairer(dr);
      reconciler.setDamager(newDR, IJavaPartitions.JAVA_SINGLE_LINE_COMMENT);
      reconciler.setRepairer(newDR, IJavaPartitions.JAVA_SINGLE_LINE_COMMENT);
      return currentResult;
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
      if (currentResult[0].equals(JMLPartitionScanner.JML_MULTI_LINE)) // if Method was called only once
         return currentResult; // previously there is
      else { // nothing to change
         String[] extendedContentTypes = new String[currentResult.length + 2];
         extendedContentTypes[0] = JMLPartitionScanner.JML_MULTI_LINE;
         extendedContentTypes[1] = JMLPartitionScanner.JML_SINGLE_LINE;
         for (int i = 0; i < currentResult.length; i++) {
            extendedContentTypes[i + 2] = currentResult[i];
         }
         return extendedContentTypes;
      }
   }
}
