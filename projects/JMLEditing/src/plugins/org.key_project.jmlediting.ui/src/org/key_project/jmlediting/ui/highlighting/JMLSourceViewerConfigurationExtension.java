package org.key_project.jmlediting.ui.highlighting;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.runtime.preferences.IEclipsePreferences.IPreferenceChangeListener;
import org.eclipse.core.runtime.preferences.IEclipsePreferences.PreferenceChangeEvent;
import org.eclipse.jdt.internal.ui.text.javadoc.JavaDocAutoIndentStrategy;
import org.eclipse.jdt.ui.text.IColorManager;
import org.eclipse.jdt.ui.text.IJavaPartitions;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.text.IAutoEditStrategy;
import org.eclipse.jface.text.presentation.IPresentationReconciler;
import org.eclipse.jface.text.presentation.PresentationReconciler;
import org.eclipse.jface.text.rules.DefaultDamagerRepairer;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.ui.texteditor.ITextEditor;
import org.key_project.javaeditor.extension.DefaultJavaSourceViewerConfigurationExtension;
import org.key_project.jmlediting.ui.util.JMLUiPreferencesHelper;

/**
 * An {@link DefaultJavaSourceViewerConfigurationExtension} to support JML.
 *
 * @author Martin Hentschel, David Giessing
 */

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
      this.listener = JMLUiPreferencesHelper
            .addPreferencesListener(new IPreferenceChangeListener() {

               @Override
               public void preferenceChange(final PreferenceChangeEvent event) {
                  sViewer.invalidateTextPresentation();
               }
            });
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

   @SuppressWarnings("restriction")
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
            newStrategys.add(new JavaJMLMultilineCommentAutoIndentStrategy(this
                  .getPartitioning()));
         }
      }

      return newStrategys.toArray(new IAutoEditStrategy[0]);
   }
}
