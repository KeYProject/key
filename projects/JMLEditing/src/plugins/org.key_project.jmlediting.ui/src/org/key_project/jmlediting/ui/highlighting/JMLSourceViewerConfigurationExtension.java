package org.key_project.jmlediting.ui.highlighting;

import org.eclipse.jdt.ui.text.IJavaPartitions;
import org.eclipse.jface.text.presentation.IPresentationReconciler;
import org.eclipse.jface.text.presentation.PresentationReconciler;
import org.eclipse.jface.text.rules.DefaultDamagerRepairer;
import org.eclipse.jface.text.source.ISourceViewer;
import org.key_project.javaeditor.extension.DefaultJavaSourceViewerConfigurationExtension;

/**
 * An {@link DefaultJavaSourceViewerConfigurationExtension} to support JML.
 *
 * @author Martin Hentschel, David Giessing
 */

public class JMLSourceViewerConfigurationExtension extends
DefaultJavaSourceViewerConfigurationExtension {

   /**
    * Replaces the original PresentationReconcilers Damager and Repairers for
    * JavaComments so that JML SyntaxColoring is supported.
    *
    * @param sourceViewer
    *           the sourceViewer the PresentationReconciler is used in
    * @param currentResult
    *           the original PresentationReconciler
    * 
    * @return a JML supporting PresentationReconciler
    *
    */
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
}
