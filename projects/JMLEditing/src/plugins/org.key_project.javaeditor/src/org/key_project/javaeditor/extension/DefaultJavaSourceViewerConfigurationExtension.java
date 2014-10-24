/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

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
 * Default implementation of {@link IJavaSourceViewerConfigurationExtension} which preserves all current results.
 * <p>
 * Context specified via {@link #init(IColorManager, IPreferenceStore, ITextEditor, String)} is available via
 * {@link #getColorManager()},
 * {@link #getPreferenceStore()},
 * {@link #getEditor()} and
 * {@link #getPartitioning()}.
 * @author Martin Hentschel
 */
@SuppressWarnings("deprecation")
public class DefaultJavaSourceViewerConfigurationExtension implements IJavaSourceViewerConfigurationExtension {
   /**
    * The {@link IColorManager} to use.
    */
   private IColorManager colorManager;
   
   /**
    * The {@link IPreferenceStore} to use.
    */
   private IPreferenceStore preferenceStore;
   
   /**
    * The {@link ITextEditor} in which the extended configuration is used.
    */
   private ITextEditor editor;
   
   /**
    * The partitioning to use.
    */
   private String partitioning;

   /**
    * {@inheritDoc}
    */
   @Override
   public void init(IColorManager colorManager, 
                    IPreferenceStore preferenceStore, 
                    ITextEditor editor, 
                    String partitioning) {
      this.colorManager = colorManager;
      this.preferenceStore = preferenceStore;
      this.editor = editor;
      this.partitioning = partitioning;
   }
   
   /**
    * Returns the {@link IColorManager} to use.
    * @return The {@link IColorManager} to use.
    */
   protected IColorManager getColorManager() {
      return colorManager;
   }

   /**
    * Returns the {@link IPreferenceStore} to use.
    * @return The {@link IPreferenceStore} to use.
    */
   protected IPreferenceStore getPreferenceStore() {
      return preferenceStore;
   }

   /**
    * Returns the {@link ITextEditor} in which the extended configuration is used.
    * @return The {@link ITextEditor} in which the extended configuration is used.
    */
   protected ITextEditor getEditor() {
      return editor;
   }

   /**
    * Returns the partitioning to use.
    * @return The partitioning to use.
    */
   protected String getPartitioning() {
      return partitioning;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int getTabWidth(ISourceViewer sourceViewer, int currentResult) {
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IUndoManager getUndoManager(ISourceViewer sourceViewer, IUndoManager currentResult) {
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IReconciler getReconciler(ISourceViewer sourceViewer, IReconciler currentResult) {
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IPresentationReconciler getPresentationReconciler(ISourceViewer sourceViewer, IPresentationReconciler currentResult) {
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IContentFormatter getContentFormatter(ISourceViewer sourceViewer, IContentFormatter currentResult) {
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IContentAssistant getContentAssistant(ISourceViewer sourceViewer, IContentAssistant currentResult) {
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IQuickAssistAssistant getQuickAssistAssistant(ISourceViewer sourceViewer, IQuickAssistAssistant currentResult) {
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IAutoIndentStrategy getAutoIndentStrategy(ISourceViewer sourceViewer, String contentType, IAutoIndentStrategy currentResult) {
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IAutoEditStrategy[] getAutoEditStrategies(ISourceViewer sourceViewer, String contentType, IAutoEditStrategy[] currentResult) {
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String[] getDefaultPrefixes(ISourceViewer sourceViewer, String contentType, String[] currentResult) {
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ITextDoubleClickStrategy getDoubleClickStrategy(ISourceViewer sourceViewer, String contentType, ITextDoubleClickStrategy currentResult) {
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String[] getIndentPrefixes(ISourceViewer sourceViewer, String contentType, String[] currentResult) {
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IAnnotationHover getAnnotationHover(ISourceViewer sourceViewer, IAnnotationHover currentResult) {
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IAnnotationHover getOverviewRulerAnnotationHover(ISourceViewer sourceViewer, IAnnotationHover currentResult) {
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int[] getConfiguredTextHoverStateMasks(ISourceViewer sourceViewer, String contentType, int[] currentResult) {
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ITextHover getTextHover(ISourceViewer sourceViewer, String contentType, int stateMask, ITextHover currentResult) {
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ITextHover getTextHover(ISourceViewer sourceViewer, String contentType, ITextHover currentResult) {
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IInformationControlCreator getInformationControlCreator(ISourceViewer sourceViewer, IInformationControlCreator currentResult) {
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IInformationPresenter getInformationPresenter(ISourceViewer sourceViewer, IInformationPresenter currentResult) {
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String[] getConfiguredContentTypes(ISourceViewer sourceViewer, String[] currentResult) {
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getConfiguredDocumentPartitioning(ISourceViewer sourceViewer, String currentResult) {
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IHyperlinkDetector[] getHyperlinkDetectors(ISourceViewer sourceViewer, IHyperlinkDetector[] currentResult) {
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IHyperlinkPresenter getHyperlinkPresenter(ISourceViewer sourceViewer, IHyperlinkPresenter currentResult) {
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int getHyperlinkStateMask(ISourceViewer sourceViewer, int currentResult) {
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IInformationPresenter getOutlinePresenter(ISourceViewer sourceViewer, boolean doCodeResolve, IInformationPresenter currentResult) {
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IInformationPresenter getHierarchyPresenter(ISourceViewer sourceViewer, boolean doCodeResolve, IInformationPresenter currentResult) {
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean affectsTextPresentation(PropertyChangeEvent event, boolean currentResult) {
      return currentResult;
   }
}