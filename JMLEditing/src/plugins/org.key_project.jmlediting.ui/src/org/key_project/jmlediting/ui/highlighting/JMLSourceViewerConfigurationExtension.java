package org.key_project.jmlediting.ui.highlighting;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.preferences.IEclipsePreferences.IPreferenceChangeListener;
import org.eclipse.core.runtime.preferences.IEclipsePreferences.PreferenceChangeEvent;
import org.eclipse.jdt.internal.ui.text.javadoc.JavaDocAutoIndentStrategy;
import org.eclipse.jdt.ui.text.IColorManager;
import org.eclipse.jdt.ui.text.IJavaPartitions;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.text.IAutoEditStrategy;
import org.eclipse.jface.text.formatter.IContentFormatter;
import org.eclipse.jface.text.formatter.MultiPassContentFormatter;
import org.eclipse.jface.text.presentation.IPresentationReconciler;
import org.eclipse.jface.text.presentation.PresentationReconciler;
import org.eclipse.jface.text.rules.DefaultDamagerRepairer;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.texteditor.ITextEditor;
import org.key_project.javaeditor.extension.DefaultJavaSourceViewerConfigurationExtension;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.IProjectProfileListener;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.ui.format.JMLContentFormatter;
import org.key_project.jmlediting.ui.format.JavaJMLMultilineCommentAutoIndentStrategy;
import org.key_project.jmlediting.ui.format.UnableToInitializeJMLFormatterException;
import org.key_project.jmlediting.ui.util.JMLUiPreferencesHelper;
import org.key_project.jmlediting.ui.util.LogUtil;

/**
 * An {@link DefaultJavaSourceViewerConfigurationExtension} to support JML.
 *
 * @author Martin Hentschel, David Giessing
 */

@SuppressWarnings("restriction")
public class JMLSourceViewerConfigurationExtension extends
      DefaultJavaSourceViewerConfigurationExtension {

   @Override
   public void init(final IColorManager colorManager,
         final IPreferenceStore preferenceStore, final ITextEditor editor,
         final String partitioning) {
      super.init(colorManager, preferenceStore, editor, partitioning);

   }

   /**
    * a PreferenceChangeListener to check whether the JML Comment Color has
    * changed.
    */
   private IPreferenceChangeListener listener = null;
   private IProjectProfileListener projectListener = null;

   /**
    * A Method for instantiating the listener.
    *
    * @param viewer
    *           the sourceViewer this Configuration works on
    */
   private void configureListener(final ISourceViewer viewer) {
      if (this.listener != null) {
         return;
      }
      if (!(viewer instanceof SourceViewer)) {
         return;
      }
      final SourceViewer sViewer = (SourceViewer) viewer;
      // Listen to changed colors
      this.listener = JMLUiPreferencesHelper
            .addPreferencesListener(new IPreferenceChangeListener() {

               @Override
               public void preferenceChange(final PreferenceChangeEvent event) {
                  Display.getDefault().asyncExec(new Runnable() {

                     @Override
                     public void run() {
                        sViewer.invalidateTextPresentation();
                     }
                  });
               }
            });
      // Listen to changed profiles
      this.projectListener = new IProjectProfileListener() {

         @Override
         public void profileChanged(final IProject project,
               final IJMLProfile newProfile) {
            if (JMLSourceViewerConfigurationExtension.this.getEditor()
                  .getEditorInput() instanceof IFileEditorInput) {
               final IFileEditorInput input = (IFileEditorInput) JMLSourceViewerConfigurationExtension.this
                     .getEditor().getEditorInput();
               final IProject fileProject = input.getFile().getProject();
               if (project == fileProject) {
                  Display.getDefault().asyncExec(new Runnable() {

                     @Override
                     public void run() {
                        sViewer.invalidateTextPresentation();
                     }
                  });
               }
            }
         }
      };

      JMLPreferencesHelper.addProjectProfileListener(this.projectListener);
   }

   /**
    * Replaces the original PresentationReconcilers Damager and Repairers for
    * JavaComments so that JML SyntaxColoring is supported. Also instantiates
    * the Color Preference listener
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
      this.configureListener(sourceViewer);
      final PresentationReconciler reconciler = (PresentationReconciler) currentResult;
      // Replace DefaultDamagerRepairer in currentResult to support JML
      DefaultDamagerRepairer dr = (DefaultDamagerRepairer) reconciler
            .getDamager(IJavaPartitions.JAVA_MULTI_LINE_COMMENT);
      JMLPresentationDamagerRepairer newDR = new JMLPresentationDamagerRepairer(
            dr, this.getEditor());
      reconciler.setDamager(newDR, IJavaPartitions.JAVA_MULTI_LINE_COMMENT);
      reconciler.setRepairer(newDR, IJavaPartitions.JAVA_MULTI_LINE_COMMENT);
      // Replace DefaultDamagerRepairer in currentResult to support JML
      dr = (DefaultDamagerRepairer) reconciler
            .getDamager(IJavaPartitions.JAVA_SINGLE_LINE_COMMENT);
      newDR = new JMLPresentationDamagerRepairer(dr, this.getEditor());
      reconciler.setDamager(newDR, IJavaPartitions.JAVA_SINGLE_LINE_COMMENT);
      reconciler.setRepairer(newDR, IJavaPartitions.JAVA_SINGLE_LINE_COMMENT);
      return currentResult;
   }

   @Override
   public IAutoEditStrategy[] getAutoEditStrategies(
         final ISourceViewer sourceViewer, final String contentType,
         final IAutoEditStrategy[] currentResult) {
      final List<IAutoEditStrategy> newStrategys = new ArrayList<IAutoEditStrategy>(
            currentResult.length);

      for (final IAutoEditStrategy s : currentResult) {
         if (s.getClass() != JavaDocAutoIndentStrategy.class) {
            newStrategys.add(s);
         }
         else {
            newStrategys.add(new JavaJMLMultilineCommentAutoIndentStrategy(s,
                  this.getPartitioning()));
         }
      }

      return newStrategys.toArray(new IAutoEditStrategy[0]);
   }

   @Override
   public IContentFormatter getContentFormatter(
         final ISourceViewer sourceViewer, final IContentFormatter currentResult) {
      // Try to create the JMLformatter
      UnableToInitializeJMLFormatterException exception = null;
      if (currentResult instanceof MultiPassContentFormatter) {
         try {
            return new JMLContentFormatter(
                  (MultiPassContentFormatter) currentResult);
         }
         catch (final UnableToInitializeJMLFormatterException e) {
            exception = e;
         }
      }
      // Could not initialize the formatter, just use the current one
      LogUtil.getLogger().logError("JMLContentFormatter could not be initialized, JML may be modified incorrectly", exception);
      return currentResult;
   }
}
