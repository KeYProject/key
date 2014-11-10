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
import org.eclipse.jface.text.presentation.PresentationReconciler;
import org.eclipse.jface.text.quickassist.IQuickAssistAssistant;
import org.eclipse.jface.text.reconciler.IReconciler;
import org.eclipse.jface.text.reconciler.Reconciler;
import org.eclipse.jface.text.rules.DefaultDamagerRepairer;
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
   /**
    * The {@link IColorManger} to use
    */
   private IColorManager colorManager;
   
   /**
    * The {@link IPreferenceStore} to use
    */
   private IPreferenceStore preferenceStore;
   
   /**
    * The {@link ITextEditor} to use
    */
   private ITextEditor editor;
   
   /**
    * The partitioning to use
    */
   private String partitioning;
   
   /* (non-Javadoc)
    * @see org.key_project.javaeditor.extension.IJavaSourceViewerConfigurationExtension#init(org.eclipse.jdt.ui.text.IColorManager, org.eclipse.jface.preference.IPreferenceStore, org.eclipse.ui.texteditor.ITextEditor, java.lang.String)
    */
   @Override
   public void init(IColorManager colorManager,
         IPreferenceStore preferenceStore, ITextEditor editor,
         String partitioning) {
      this.colorManager = colorManager;
      this.preferenceStore = preferenceStore;
      this.editor = editor;
      this.partitioning = partitioning;
   }

   /**
    * returns the {@link IColorManager} to use
    * @return the {@link IColorManager} to use
    */
   protected IColorManager getColorManager() {
      return colorManager;
   }

   /**
    * returns the {@link IPreferenceStore} to use
    * @return the {@link IPreferenceStore} to use
    */
   protected IPreferenceStore getPreferenceStore() {
      return preferenceStore;
   }

   /**
    * returns the {@link ITextEditor} to use
    * @return the {@link ITextEditor} to use
    */
   protected ITextEditor getEditor() {
      return editor;
   }

   /**
    * returns the partitioning to use
    * @return the partitioning to use
    */
   protected String getPartitioning() {
      return partitioning;
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
   /**
    * @{inheritDoc}
    */
   @Override
   public IReconciler getReconciler(ISourceViewer sourceViewer,
         IReconciler currentResult) {
      // TODO ggf anpassen
      return currentResult;
   }

   /**
    *@{inheritDoc}
    */
   @Override
   public IPresentationReconciler getPresentationReconciler(
         ISourceViewer sourceViewer, IPresentationReconciler currentResult) {
    //TODO: create PresentationReconciler, install damagers and Repairers for JML ContentTypes
      PresentationReconciler presReconciler = new PresentationReconciler(); //new Reconciler to Modify
      /* NEED: access to configured ContentTypes of JavaSourceViewerConfiguration
         to get Damager and Repairers of currentResult, to add them to reconciler
         Problem: original Config is not accessible via the Extension.
      */
      return presReconciler;
   }

   /**
    * @{inheritDoc}
    */
   @Override
   public IContentFormatter getContentFormatter(ISourceViewer sourceViewer,
         IContentFormatter currentResult) {
      return currentResult;
   }

   /**
    * @{inheritDoc}
    */
   @Override
   public IContentAssistant getContentAssistant(ISourceViewer sourceViewer,
         IContentAssistant currentResult) {
      return currentResult;
   }

   /**
    * @{inheritDoc}
    */
   @Override
   public IQuickAssistAssistant getQuickAssistAssistant(
         ISourceViewer sourceViewer, IQuickAssistAssistant currentResult) {
      return currentResult;
   }

   /**
    * @{inheritDoc}
    */
   @Override
   public IAutoIndentStrategy getAutoIndentStrategy(ISourceViewer sourceViewer,
         String contentType, IAutoIndentStrategy currentResult) {
      return currentResult;
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
    * {@inheritDoc}
    * @returns a modified List of configured ContentTypes, adds JMLSingleLine and JMLMultiLine content Types
    */
   @Override
   public String[] getConfiguredContentTypes(ISourceViewer sourceViewer, String[] currentResult) {
      //TODO: TEST
         String[] modifiedcurrentResult= new String[currentResult.length+2];
         for(int i=0;i<currentResult.length;i++){  //copy currentResult
            modifiedcurrentResult[i]=currentResult[i];
         }
         modifiedcurrentResult[currentResult.length]="JMLSingleLine";   //add JMLSingleLine Type
         modifiedcurrentResult[currentResult.length+1]="JMLMultiLine";  //add JMLMultiLine Type
      return modifiedcurrentResult;
   }

   /**
    * @{inheritDoc}
    */
   @Override
   public String getConfiguredDocumentPartitioning(ISourceViewer sourceViewer,
         String currentResult) {
      return currentResult;
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
   /**
    * @{inheritDoc}
    */
   @Override
   public boolean affectsTextPresentation(PropertyChangeEvent event,
         boolean currentResult) {
      return currentResult;
   }

}
