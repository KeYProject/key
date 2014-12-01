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
   public int getTabWidth(final ISourceViewer sourceViewer,
         final int currentResult) {
      this.document = sourceViewer.getDocument();
      return currentResult * 2;
   }

   @Override
   public IPresentationReconciler getPresentationReconciler(
         final ISourceViewer sourceViewer,
         final IPresentationReconciler currentResult) {
      final PresentationReconciler reconciler = (PresentationReconciler) currentResult;
      // Replace DefaultDamagerRepairer in currentResult to support JML
      DefaultDamagerRepairer dr = (DefaultDamagerRepairer) reconciler
            .getDamager(IJavaPartitions.JAVA_MULTI_LINE_COMMENT);
      JMLPresentationDamagerRepairer newDR = new JMLPresentationDamagerRepairer(
            dr);
      reconciler.setDamager(newDR, IJavaPartitions.JAVA_MULTI_LINE_COMMENT);
      reconciler.setRepairer(newDR, IJavaPartitions.JAVA_MULTI_LINE_COMMENT);
      // Replace DefaultDamagerRepairer in currentResult to support JML
      dr = (DefaultDamagerRepairer) reconciler
            .getDamager(IJavaPartitions.JAVA_SINGLE_LINE_COMMENT);
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
   public String[] getConfiguredContentTypes(final ISourceViewer sourceViewer,
         final String[] currentResult) {
      return currentResult;
   }
}
