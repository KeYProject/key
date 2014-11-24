package org.key_project.jmlediting.ui.extension;

import java.util.LinkedList;
import java.util.ListIterator;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.presentation.IPresentationReconciler;
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
      this.document = sourceViewer.getDocument();// TODO is this Method called
                                                 // only once?
      return currentResult * 2;
   }

   @Override
   public IPresentationReconciler getPresentationReconciler(
         ISourceViewer sourceViewer, IPresentationReconciler currentResult) {
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
      if (currentResult[0].equals(JMLPartitionScanner.JML_MULTI_LINE)) // if
                                                                       // Method
                                                                       // was
                                                                       // called
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
