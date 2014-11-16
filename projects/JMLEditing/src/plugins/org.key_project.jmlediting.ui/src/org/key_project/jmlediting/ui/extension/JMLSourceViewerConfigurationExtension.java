package org.key_project.jmlediting.ui.extension;

import org.eclipse.jface.text.presentation.IPresentationReconciler;
import org.eclipse.jface.text.source.ISourceViewer;
import org.key_project.javaeditor.extension.DefaultJavaSourceViewerConfigurationExtension;
import org.key_project.javaeditor.extension.IJavaSourceViewerConfigurationExtension;

/**
 * An {@link IJavaSourceViewerConfigurationExtension} to support JML.
 * @author Martin Hentschel
 */
public class JMLSourceViewerConfigurationExtension extends DefaultJavaSourceViewerConfigurationExtension {
   /**
    * {@inheritDoc}
    */
   @Override
   public int getTabWidth(ISourceViewer sourceViewer, int currentResult) {
      return currentResult * 2;
   }
   
   @Override
   public IPresentationReconciler getPresentationReconciler(
         ISourceViewer sourceViewer, IPresentationReconciler currentResult) {
      IPresentationReconciler JMLPresentationReconciler = new JMLPresentationReconciler(currentResult);
      return JMLPresentationReconciler;
   }
}
