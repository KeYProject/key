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

package org.key_project.javaeditor.management;

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
import org.key_project.javaeditor.extension.IJavaSourceViewerConfigurationExtension;

/**
 * An extended {@link JavaSourceViewerConfiguration} which allows {@link IJavaSourceViewerConfigurationExtension}
 * to modify the original result of the original {@link JavaSourceViewerConfiguration}.
 * @author Martin Hentschel
 */
@SuppressWarnings("deprecation")
public class ExtendableJavaSourceViewerConfiguration extends JavaSourceViewerConfiguration {
   /**
    * The original {@link JavaSourceViewerConfiguration} from which the results are modified by {@link IJavaSourceViewerConfigurationExtension}s.
    */
   private final JavaSourceViewerConfiguration originalConfiguration;
   
   /**
    * The available {@link IJavaSourceViewerConfigurationExtension}s.
    */
   private final IJavaSourceViewerConfigurationExtension[] extensions;

   /**
    * Constructor.
    * @param colorManager The {@link IColorManager} to use.
    * @param preferenceStore The {@link IPreferenceStore} to use.
    * @param editor The {@link ITextEditor} in which this configuration is used.
    * @param partitioning The partitioning to use.
    * @param originalConfiguration The original {@link JavaSourceViewerConfiguration} from which the results are modified by {@link IJavaSourceViewerConfigurationExtension}s.
    * @param extensions The {@link IJavaSourceViewerConfigurationExtension} to use.
    */
   public ExtendableJavaSourceViewerConfiguration(IColorManager colorManager, 
                                                  IPreferenceStore preferenceStore, 
                                                  ITextEditor editor, 
                                                  String partitioning, 
                                                  JavaSourceViewerConfiguration originalConfiguration,
                                                  IJavaSourceViewerConfigurationExtension[] extensions) {
      // Initialize configuration
      super(colorManager, preferenceStore, editor, partitioning);
      this.originalConfiguration = originalConfiguration;
      this.extensions = extensions;
      // Initialize extensions
      for (IJavaSourceViewerConfigurationExtension extension : extensions) {
         extension.init(colorManager, preferenceStore, editor, partitioning);
      } 
   }

   /**
    * Returns the original {@link JavaSourceViewerConfiguration}.
    * @return The original {@link JavaSourceViewerConfiguration}.
    */
   public JavaSourceViewerConfiguration getOriginalConfiguration() {
      return originalConfiguration;
   }

   /**
    * Returns the used {@link IJavaSourceViewerConfigurationExtension}.
    * @return The used {@link IJavaSourceViewerConfigurationExtension}.
    */
   public IJavaSourceViewerConfigurationExtension[] getExtensions() {
      return extensions;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int getTabWidth(ISourceViewer sourceViewer) {
      int currentResult = originalConfiguration.getTabWidth(sourceViewer);
      for (IJavaSourceViewerConfigurationExtension extension : extensions) {
         currentResult = extension.getTabWidth(sourceViewer, currentResult);
      }
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IUndoManager getUndoManager(ISourceViewer sourceViewer) {
      IUndoManager currentResult = originalConfiguration.getUndoManager(sourceViewer);
      for (IJavaSourceViewerConfigurationExtension extension : extensions) {
         currentResult = extension.getUndoManager(sourceViewer, currentResult);
      }
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IReconciler getReconciler(ISourceViewer sourceViewer) {
      IReconciler currentResult = originalConfiguration.getReconciler(sourceViewer);
      for (IJavaSourceViewerConfigurationExtension extension : extensions) {
         currentResult = extension.getReconciler(sourceViewer, currentResult);
      }
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IPresentationReconciler getPresentationReconciler(ISourceViewer sourceViewer) {
      IPresentationReconciler currentResult = originalConfiguration.getPresentationReconciler(sourceViewer);
      for (IJavaSourceViewerConfigurationExtension extension : extensions) {
         currentResult = extension.getPresentationReconciler(sourceViewer, currentResult);
      }
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IContentFormatter getContentFormatter(ISourceViewer sourceViewer) {
      IContentFormatter currentResult = originalConfiguration.getContentFormatter(sourceViewer);
      for (IJavaSourceViewerConfigurationExtension extension : extensions) {
         currentResult = extension.getContentFormatter(sourceViewer, currentResult);
      }
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IContentAssistant getContentAssistant(ISourceViewer sourceViewer) {
      IContentAssistant currentResult = originalConfiguration.getContentAssistant(sourceViewer);
      for (IJavaSourceViewerConfigurationExtension extension : extensions) {
         currentResult = extension.getContentAssistant(sourceViewer, currentResult);
      }
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IQuickAssistAssistant getQuickAssistAssistant(ISourceViewer sourceViewer) {
      IQuickAssistAssistant currentResult = originalConfiguration.getQuickAssistAssistant(sourceViewer);
      for (IJavaSourceViewerConfigurationExtension extension : extensions) {
         currentResult = extension.getQuickAssistAssistant(sourceViewer, currentResult);
      }
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IAutoIndentStrategy getAutoIndentStrategy(ISourceViewer sourceViewer, String contentType) {
      IAutoIndentStrategy currentResult = originalConfiguration.getAutoIndentStrategy(sourceViewer, contentType);
      for (IJavaSourceViewerConfigurationExtension extension : extensions) {
         currentResult = extension.getAutoIndentStrategy(sourceViewer, contentType, currentResult);
      }
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IAutoEditStrategy[] getAutoEditStrategies(ISourceViewer sourceViewer, String contentType) {
      IAutoEditStrategy[] currentResult = originalConfiguration.getAutoEditStrategies(sourceViewer, contentType);
      for (IJavaSourceViewerConfigurationExtension extension : extensions) {
         currentResult = extension.getAutoEditStrategies(sourceViewer, contentType, currentResult);
      }
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String[] getDefaultPrefixes(ISourceViewer sourceViewer, String contentType) {
      String[] currentResult = originalConfiguration.getDefaultPrefixes(sourceViewer, contentType);
      for (IJavaSourceViewerConfigurationExtension extension : extensions) {
         currentResult = extension.getDefaultPrefixes(sourceViewer, contentType, currentResult);
      }
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ITextDoubleClickStrategy getDoubleClickStrategy(ISourceViewer sourceViewer, String contentType) {
      ITextDoubleClickStrategy currentResult = originalConfiguration.getDoubleClickStrategy(sourceViewer, contentType);
      for (IJavaSourceViewerConfigurationExtension extension : extensions) {
         currentResult = extension.getDoubleClickStrategy(sourceViewer, contentType, currentResult);
      }
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String[] getIndentPrefixes(ISourceViewer sourceViewer, String contentType) {
      String[] currentResult = originalConfiguration.getIndentPrefixes(sourceViewer, contentType);
      for (IJavaSourceViewerConfigurationExtension extension : extensions) {
         currentResult = extension.getIndentPrefixes(sourceViewer, contentType, currentResult);
      }
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IAnnotationHover getAnnotationHover(ISourceViewer sourceViewer) {
      IAnnotationHover currentResult = originalConfiguration.getAnnotationHover(sourceViewer);
      for (IJavaSourceViewerConfigurationExtension extension : extensions) {
         currentResult = extension.getAnnotationHover(sourceViewer, currentResult);
      }
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IAnnotationHover getOverviewRulerAnnotationHover(ISourceViewer sourceViewer) {
      IAnnotationHover currentResult = originalConfiguration.getOverviewRulerAnnotationHover(sourceViewer);
      for (IJavaSourceViewerConfigurationExtension extension : extensions) {
         currentResult = extension.getOverviewRulerAnnotationHover(sourceViewer, currentResult);
      }
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int[] getConfiguredTextHoverStateMasks(ISourceViewer sourceViewer, String contentType) {
      int[] currentResult = originalConfiguration.getConfiguredTextHoverStateMasks(sourceViewer, contentType);
      for (IJavaSourceViewerConfigurationExtension extension : extensions) {
         currentResult = extension.getConfiguredTextHoverStateMasks(sourceViewer, contentType, currentResult);
      }
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ITextHover getTextHover(ISourceViewer sourceViewer, String contentType, int stateMask) {
      ITextHover currentResult = originalConfiguration.getTextHover(sourceViewer, contentType, stateMask);
      for (IJavaSourceViewerConfigurationExtension extension : extensions) {
         currentResult = extension.getTextHover(sourceViewer, contentType, stateMask, currentResult);
      }
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ITextHover getTextHover(ISourceViewer sourceViewer, String contentType) {
      ITextHover currentResult = originalConfiguration.getTextHover(sourceViewer, contentType);
      for (IJavaSourceViewerConfigurationExtension extension : extensions) {
         currentResult = extension.getTextHover(sourceViewer, contentType, currentResult);
      }
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IInformationControlCreator getInformationControlCreator(ISourceViewer sourceViewer) {
      IInformationControlCreator currentResult = originalConfiguration.getInformationControlCreator(sourceViewer);
      for (IJavaSourceViewerConfigurationExtension extension : extensions) {
         currentResult = extension.getInformationControlCreator(sourceViewer, currentResult);
      }
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IInformationPresenter getInformationPresenter(ISourceViewer sourceViewer) {
      IInformationPresenter currentResult = originalConfiguration.getInformationPresenter(sourceViewer);
      for (IJavaSourceViewerConfigurationExtension extension : extensions) {
         currentResult = extension.getInformationPresenter(sourceViewer, currentResult);
      }
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String[] getConfiguredContentTypes(ISourceViewer sourceViewer) {
      String[] currentResult = originalConfiguration.getConfiguredContentTypes(sourceViewer);
      for (IJavaSourceViewerConfigurationExtension extension : extensions) {
         currentResult = extension.getConfiguredContentTypes(sourceViewer, currentResult);
      }
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getConfiguredDocumentPartitioning(ISourceViewer sourceViewer) {
      String currentResult = originalConfiguration.getConfiguredDocumentPartitioning(sourceViewer);
      for (IJavaSourceViewerConfigurationExtension extension : extensions) {
         currentResult = extension.getConfiguredDocumentPartitioning(sourceViewer, currentResult);
      }
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IHyperlinkDetector[] getHyperlinkDetectors(ISourceViewer sourceViewer) {
      IHyperlinkDetector[] currentResult = originalConfiguration.getHyperlinkDetectors(sourceViewer);
      for (IJavaSourceViewerConfigurationExtension extension : extensions) {
         currentResult = extension.getHyperlinkDetectors(sourceViewer, currentResult);
      }
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IHyperlinkPresenter getHyperlinkPresenter(ISourceViewer sourceViewer) {
      IHyperlinkPresenter currentResult = originalConfiguration.getHyperlinkPresenter(sourceViewer);
      for (IJavaSourceViewerConfigurationExtension extension : extensions) {
         currentResult = extension.getHyperlinkPresenter(sourceViewer, currentResult);
      }
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int getHyperlinkStateMask(ISourceViewer sourceViewer) {
      int currentResult = originalConfiguration.getHyperlinkStateMask(sourceViewer);
      for (IJavaSourceViewerConfigurationExtension extension : extensions) {
         currentResult = extension.getHyperlinkStateMask(sourceViewer, currentResult);
      }
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IInformationPresenter getOutlinePresenter(ISourceViewer sourceViewer, boolean doCodeResolve) {
      IInformationPresenter currentResult = originalConfiguration.getOutlinePresenter(sourceViewer, doCodeResolve);
      for (IJavaSourceViewerConfigurationExtension extension : extensions) {
         currentResult = extension.getOutlinePresenter(sourceViewer, doCodeResolve, currentResult);
      }
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IInformationPresenter getHierarchyPresenter(ISourceViewer sourceViewer, boolean doCodeResolve) {
      IInformationPresenter currentResult = originalConfiguration.getHierarchyPresenter(sourceViewer, doCodeResolve);
      for (IJavaSourceViewerConfigurationExtension extension : extensions) {
         currentResult = extension.getHierarchyPresenter(sourceViewer, doCodeResolve, currentResult);
      }
      return currentResult;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean affectsTextPresentation(PropertyChangeEvent event) {
      boolean currentResult = originalConfiguration.affectsTextPresentation(event);
      for (IJavaSourceViewerConfigurationExtension extension : extensions) {
         currentResult = extension.affectsTextPresentation(event, currentResult);
      }
      return currentResult;
   }
}
