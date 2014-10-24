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

import org.eclipse.jdt.internal.ui.javaeditor.JavaEditor;
import org.eclipse.jdt.ui.text.IColorManager;
import org.eclipse.jdt.ui.text.JavaSourceViewerConfiguration;
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
import org.key_project.javaeditor.util.ExtendableConfigurationUtil;

/**
 * An {@link IJavaSourceViewerConfigurationExtension} allows to modify the result
 * originally computed by a {@link JavaSourceViewerConfiguration}.
 * <p>
 * Available implementations are registered via extension point {@value ExtendableConfigurationUtil#JAVA_CONFIGURATION_EXTENSIONS_EXTENSION_POINT}.
 * <p>
 * For each {@link JavaEditor} is its own instance of this class created and maintained until the {@link JavaEditor} is closed.
 * The context in which the instance lives is set via {@link #init(IColorManager, IPreferenceStore, ITextEditor, String)}.
 * @author Martin Hentschel
 */
@SuppressWarnings({ "deprecation", "restriction" })
public interface IJavaSourceViewerConfigurationExtension {
   /**
    * Initializes the newly created {@link IJavaSourceViewerConfigurationExtension}.
    * @param colorManager The {@link IColorManager} to use.
    * @param preferenceStore The {@link IPreferenceStore} to use.
    * @param editor The {@link ITextEditor} in which the extended configuration is used.
    * @param partitioning The partitioning to use.
    */
   public void init(IColorManager colorManager, IPreferenceStore preferenceStore, ITextEditor editor, String partitioning);
   
   /**
    * Allows to modify the current result. Fore more details see
    * {@link JavaSourceViewerConfiguration#getTabWidth(ISourceViewer)}.
    */
   public int getTabWidth(ISourceViewer sourceViewer, int currentResult);

   /**
    * Allows to modify the current result. Fore more details see
    * {@link JavaSourceViewerConfiguration#getUndoManager(ISourceViewer)}.
    */
   public IUndoManager getUndoManager(ISourceViewer sourceViewer, IUndoManager currentResult);

   /**
    * Allows to modify the current result. Fore more details see
    * {@link JavaSourceViewerConfiguration#getReconciler(ISourceViewer)}.
    */
   public IReconciler getReconciler(ISourceViewer sourceViewer, IReconciler currentResult);

   /**
    * Allows to modify the current result. Fore more details see
    * {@link JavaSourceViewerConfiguration#getPresentationReconciler(ISourceViewer)}.
    */
   public IPresentationReconciler getPresentationReconciler(ISourceViewer sourceViewer, IPresentationReconciler currentResult);

   /**
    * Allows to modify the current result. Fore more details see
    * {@link JavaSourceViewerConfiguration#getContentFormatter(ISourceViewer)}.
    */
   public IContentFormatter getContentFormatter(ISourceViewer sourceViewer, IContentFormatter currentResult);

   /**
    * Allows to modify the current result. Fore more details see
    * {@link JavaSourceViewerConfiguration#getContentAssistant(ISourceViewer)}.
    */
   public IContentAssistant getContentAssistant(ISourceViewer sourceViewer, IContentAssistant currentResult);

   /**
    * Allows to modify the current result. Fore more details see
    * {@link JavaSourceViewerConfiguration#getQuickAssistAssistant(ISourceViewer)}.
    */
   public IQuickAssistAssistant getQuickAssistAssistant(ISourceViewer sourceViewer, IQuickAssistAssistant currentResult);

   /**
    * Allows to modify the current result. Fore more details see
    * {@link JavaSourceViewerConfiguration#getAutoIndentStrategy(ISourceViewer, String)}.
    */
   public IAutoIndentStrategy getAutoIndentStrategy(ISourceViewer sourceViewer, String contentType, IAutoIndentStrategy currentResult);

   /**
    * Allows to modify the current result. Fore more details see
    * {@link JavaSourceViewerConfiguration#getAutoEditStrategies(ISourceViewer, String)}.
    */
   public IAutoEditStrategy[] getAutoEditStrategies(ISourceViewer sourceViewer, String contentType, IAutoEditStrategy[] currentResult);

   /**
    * Allows to modify the current result. Fore more details see
    * {@link JavaSourceViewerConfiguration#getDefaultPrefixes(ISourceViewer, String)}.
    */
   public String[] getDefaultPrefixes(ISourceViewer sourceViewer, String contentType, String[] currentResult);

   /**
    * Allows to modify the current result. Fore more details see
    * {@link JavaSourceViewerConfiguration#getDoubleClickStrategy(ISourceViewer, String)}.
    */
   public ITextDoubleClickStrategy getDoubleClickStrategy(ISourceViewer sourceViewer, String contentType, ITextDoubleClickStrategy currentResult);

   /**
    * Allows to modify the current result. Fore more details see
    * {@link JavaSourceViewerConfiguration#getIndentPrefixes(ISourceViewer, String)}.
    */
   public String[] getIndentPrefixes(ISourceViewer sourceViewer, String contentType, String[] currentResult);

   /**
    * Allows to modify the current result. Fore more details see
    * {@link JavaSourceViewerConfiguration#getAnnotationHover(ISourceViewer)}.
    */
   public IAnnotationHover getAnnotationHover(ISourceViewer sourceViewer, IAnnotationHover currentResult);

   /**
    * Allows to modify the current result. Fore more details see
    * {@link JavaSourceViewerConfiguration#getOverviewRulerAnnotationHover(ISourceViewer)}.
    */
   public IAnnotationHover getOverviewRulerAnnotationHover(ISourceViewer sourceViewer, IAnnotationHover currentResult);

   /**
    * Allows to modify the current result. Fore more details see
    * {@link JavaSourceViewerConfiguration#getConfiguredTextHoverStateMasks(ISourceViewer, String)}.
    */
   public int[] getConfiguredTextHoverStateMasks(ISourceViewer sourceViewer, String contentType, int[] currentResult);

   /**
    * Allows to modify the current result. Fore more details see
    * {@link JavaSourceViewerConfiguration#getTextHover(ISourceViewer, String, int)}.
    */
   public ITextHover getTextHover(ISourceViewer sourceViewer, String contentType, int stateMask, ITextHover currentResult);

   /**
    * Allows to modify the current result. Fore more details see
    * {@link JavaSourceViewerConfiguration#getTextHover(ISourceViewer, String))}.
    */
   public ITextHover getTextHover(ISourceViewer sourceViewer, String contentType, ITextHover currentResult);

   /**
    * Allows to modify the current result. Fore more details see
    * {@link JavaSourceViewerConfiguration#getInformationControlCreator(ISourceViewer)}.
    */
   public IInformationControlCreator getInformationControlCreator(ISourceViewer sourceViewer, IInformationControlCreator currentResult);

   /**
    * Allows to modify the current result. Fore more details see
    * {@link JavaSourceViewerConfiguration#getInformationPresenter(ISourceViewer)}.
    */
   public IInformationPresenter getInformationPresenter(ISourceViewer sourceViewer, IInformationPresenter currentResult);

   /**
    * Allows to modify the current result. Fore more details see
    * {@link JavaSourceViewerConfiguration#getConfiguredContentTypes(ISourceViewer)}.
    */
   public String[] getConfiguredContentTypes(ISourceViewer sourceViewer, String[] currentResult);

   /**
    * Allows to modify the current result. Fore more details see
    * {@link JavaSourceViewerConfiguration#getConfiguredDocumentPartitioning(ISourceViewer)}.
    */
   public String getConfiguredDocumentPartitioning(ISourceViewer sourceViewer, String currentResult);

   /**
    * Allows to modify the current result. Fore more details see
    * {@link JavaSourceViewerConfiguration#getHyperlinkDetectors(ISourceViewer)}.
    */
   public IHyperlinkDetector[] getHyperlinkDetectors(ISourceViewer sourceViewer, IHyperlinkDetector[] currentResult);

   /**
    * Allows to modify the current result. Fore more details see
    * {@link JavaSourceViewerConfiguration#getHyperlinkPresenter(ISourceViewer)}.
    */
   public IHyperlinkPresenter getHyperlinkPresenter(ISourceViewer sourceViewer, IHyperlinkPresenter currentResult);

   /**
    * Allows to modify the current result. Fore more details see
    * {@link JavaSourceViewerConfiguration#getHyperlinkStateMask(ISourceViewer)}.
    */
   public int getHyperlinkStateMask(ISourceViewer sourceViewer, int currentResult);

   /**
    * Allows to modify the current result. Fore more details see
    * {@link JavaSourceViewerConfiguration#getOutlinePresenter(ISourceViewer, boolean)}.
    */
   public IInformationPresenter getOutlinePresenter(ISourceViewer sourceViewer, boolean doCodeResolve, IInformationPresenter currentResult);

   /**
    * Allows to modify the current result. Fore more details see
    * {@link JavaSourceViewerConfiguration#getHierarchyPresenter(ISourceViewer, boolean)}.
    */
   public IInformationPresenter getHierarchyPresenter(ISourceViewer sourceViewer, boolean doCodeResolve, IInformationPresenter currentResult);

   /**
    * Allows to modify the current result. Fore more details see
    * {@link JavaSourceViewerConfiguration#affectsTextPresentation(PropertyChangeEvent)}.
    */
   public boolean affectsTextPresentation(PropertyChangeEvent event, boolean currentResult);
}