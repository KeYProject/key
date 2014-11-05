/**
 * 
 */
package org.key_project.javaeditor.extension;

import org.eclipse.jdt.ui.text.IColorManager;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.text.IAutoEditStrategy;
import org.eclipse.jface.text.IAutoIndentStrategy;
import org.eclipse.jface.text.IInformationControlCreator;
import org.eclipse.jface.text.ITextDoubleClickStrategy;
import org.eclipse.jface.text.ITextHover;
import org.eclipse.jface.text.IUndoManager;
import org.eclipse.jface.text.contentassist.IContentAssistant;
import org.eclipse.jface.text.formatter.IContentFormatter;
import org.eclipse.jface.text.hyperlink.IHyperlinkDetector;
import org.eclipse.jface.text.hyperlink.IHyperlinkPresenter;
import org.eclipse.jface.text.information.IInformationPresenter;
import org.eclipse.jface.text.presentation.IPresentationReconciler;
import org.eclipse.jface.text.quickassist.IQuickAssistAssistant;
import org.eclipse.jface.text.reconciler.IReconciler;
import org.eclipse.jface.text.source.IAnnotationHover;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.ui.texteditor.ITextEditor;

/**
 * @author David Giessing
 *
 */
public class JMLJavaSourceViewerConfigurationExtension implements
      IJavaSourceViewerConfigurationExtension {

   /* (non-Javadoc)
    * @see org.key_project.javaeditor.extension.IJavaSourceViewerConfigurationExtension#init(org.eclipse.jdt.ui.text.IColorManager, org.eclipse.jface.preference.IPreferenceStore, org.eclipse.ui.texteditor.ITextEditor, java.lang.String)
    */
   @Override
   public void init(IColorManager colorManager,
         IPreferenceStore preferenceStore, ITextEditor editor,
         String partitioning) {
      // TODO Auto-generated method stub

   }

   /**
    * @{inheritDoc}
    */
   @Override
   public int getTabWidth(ISourceViewer sourceViewer, int currentResult) {
      return currentResult;
   }

   /**
    *@{inheritDoc}
    */
   @Override
   public IUndoManager getUndoManager(ISourceViewer sourceViewer,
         IUndoManager currentResult) {
       return currentResult;
   }
   /* (non-Javadoc)
    * @see org.key_project.javaeditor.extension.IJavaSourceViewerConfigurationExtension#getReconciler(org.eclipse.jface.text.source.ISourceViewer, org.eclipse.jface.text.reconciler.IReconciler)
    */
   @Override
   public IReconciler getReconciler(ISourceViewer sourceViewer,
         IReconciler currentResult) {
      // TODO Auto-generated method stub
      return null;
   }

   /* (non-Javadoc)
    * @see org.key_project.javaeditor.extension.IJavaSourceViewerConfigurationExtension#getPresentationReconciler(org.eclipse.jface.text.source.ISourceViewer, org.eclipse.jface.text.presentation.IPresentationReconciler)
    */
   @Override
   public IPresentationReconciler getPresentationReconciler(
         ISourceViewer sourceViewer, IPresentationReconciler currentResult) {
      // TODO Auto-generated method stub
      return null;
   }

   /**
    * @{inheritDoc}
    */
   @Override
   public IContentFormatter getContentFormatter(ISourceViewer sourceViewer,
         IContentFormatter currentResult) {
      return currentResult;
   }

   /* (non-Javadoc)
    * @see org.key_project.javaeditor.extension.IJavaSourceViewerConfigurationExtension#getContentAssistant(org.eclipse.jface.text.source.ISourceViewer, org.eclipse.jface.text.contentassist.IContentAssistant)
    */
   @Override
   public IContentAssistant getContentAssistant(ISourceViewer sourceViewer,
         IContentAssistant currentResult) {
      // TODO Auto-generated method stub
      return null;
   }

   /* (non-Javadoc)
    * @see org.key_project.javaeditor.extension.IJavaSourceViewerConfigurationExtension#getQuickAssistAssistant(org.eclipse.jface.text.source.ISourceViewer, org.eclipse.jface.text.quickassist.IQuickAssistAssistant)
    */
   @Override
   public IQuickAssistAssistant getQuickAssistAssistant(
         ISourceViewer sourceViewer, IQuickAssistAssistant currentResult) {
      // TODO Auto-generated method stub
      return null;
   }

   /* (non-Javadoc)
    * @see org.key_project.javaeditor.extension.IJavaSourceViewerConfigurationExtension#getAutoIndentStrategy(org.eclipse.jface.text.source.ISourceViewer, java.lang.String, org.eclipse.jface.text.IAutoIndentStrategy)
    */
   @Override
   public IAutoIndentStrategy getAutoIndentStrategy(ISourceViewer sourceViewer,
         String contentType, IAutoIndentStrategy currentResult) {
      // TODO Auto-generated method stub
      return null;
   }

   /**
    * @{inheritDoc}
    */
   @Override
   public IAutoEditStrategy[] getAutoEditStrategies(ISourceViewer sourceViewer,
         String contentType, IAutoEditStrategy[] currentResult) {
      return currentResult;
   }

   /**
    * @{inheritDoc}
    */
   @Override
   public String[] getDefaultPrefixes(ISourceViewer sourceViewer,
         String contentType, String[] currentResult) {
      // TODO Auto-generated method stub
      return null;
   }

   /**
    *@{inheritDoc} 
    */
   @Override
   public ITextDoubleClickStrategy getDoubleClickStrategy(
         ISourceViewer sourceViewer, String contentType,
         ITextDoubleClickStrategy currentResult) {
      return currentResult;
   }

   /**
    * @{inheritDoc}
    */
   @Override
   public String[] getIndentPrefixes(ISourceViewer sourceViewer,
         String contentType, String[] currentResult) {
      return currentResult;
   }

   /**
    * @{inheritDoc}
    */
   @Override
   public IAnnotationHover getAnnotationHover(ISourceViewer sourceViewer,
         IAnnotationHover currentResult) {
      return currentResult;
   }

   /**
    * @{inheritDoc}
    */
   @Override
   public IAnnotationHover getOverviewRulerAnnotationHover(
         ISourceViewer sourceViewer, IAnnotationHover currentResult) {
      return currentResult;
   }

   /**
    * @{inheritDoc}
    */
   @Override
   public int[] getConfiguredTextHoverStateMasks(ISourceViewer sourceViewer,
         String contentType, int[] currentResult) {
      return currentResult;
   }

   /**
    * @{inheritDoc}
    */
   @Override
   public ITextHover getTextHover(ISourceViewer sourceViewer,
         String contentType, int stateMask, ITextHover currentResult) {
      return currentResult;
   }

   /**
    * @{inheritDoc}
    */
   @Override
   public ITextHover getTextHover(ISourceViewer sourceViewer,
         String contentType, ITextHover currentResult) {
      return currentResult;
   }

   /**
    * @{inheritDoc}
    */
   @Override
   public IInformationControlCreator getInformationControlCreator(
         ISourceViewer sourceViewer, IInformationControlCreator currentResult) {
      return currentResult;
   }

   /**
    * @{inheritDoc}
    */
   @Override
   public IInformationPresenter getInformationPresenter(
         ISourceViewer sourceViewer, IInformationPresenter currentResult) {
      return currentResult;
   }

   /**
    * @{inheritDoc}
    */
   @Override
   public String[] getConfiguredContentTypes(ISourceViewer sourceViewer,
         String[] currentResult) {
      return currentResult;
   }

   /* (non-Javadoc)
    * @see org.key_project.javaeditor.extension.IJavaSourceViewerConfigurationExtension#getConfiguredDocumentPartitioning(org.eclipse.jface.text.source.ISourceViewer, java.lang.String)
    */
   @Override
   public String getConfiguredDocumentPartitioning(ISourceViewer sourceViewer,
         String currentResult) {
      // TODO Auto-generated method stub
      return null;
   }

   /**
    * @{inheritDoc}
    */
   @Override
   public IHyperlinkDetector[] getHyperlinkDetectors(
         ISourceViewer sourceViewer, IHyperlinkDetector[] currentResult) {
      return currentResult;
   }

   /**
    * @{inheritDoc}
    */
   @Override
   public IHyperlinkPresenter getHyperlinkPresenter(ISourceViewer sourceViewer,
         IHyperlinkPresenter currentResult) {
      return currentResult;
   }

   /**
    * @{inheritDoc}
    */
   @Override
   public int getHyperlinkStateMask(ISourceViewer sourceViewer,
         int currentResult) {
      return currentResult;
   }

   /**
    * @{inheritDoc}
    */
   @Override
   public IInformationPresenter getOutlinePresenter(ISourceViewer sourceViewer,
         boolean doCodeResolve, IInformationPresenter currentResult) {
      return currentResult;
   }

   /**
    * @{inheritDoc}
    */
   @Override
   public IInformationPresenter getHierarchyPresenter(
         ISourceViewer sourceViewer, boolean doCodeResolve,
         IInformationPresenter currentResult) {
      return currentResult;
   }

   /* (non-Javadoc)
    * @see org.key_project.javaeditor.extension.IJavaSourceViewerConfigurationExtension#affectsTextPresentation(org.eclipse.jface.util.PropertyChangeEvent, boolean)
    */
   @Override
   public boolean affectsTextPresentation(PropertyChangeEvent event,
         boolean currentResult) {
      // TODO Auto-generated method stub
      return false;
   }

}
