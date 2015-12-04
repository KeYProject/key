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

import java.lang.reflect.InvocationTargetException;
import java.util.Arrays;

import javax.naming.OperationNotSupportedException;

import org.eclipse.jdt.internal.ui.javaeditor.JavaEditor;
import org.eclipse.jdt.internal.ui.javaeditor.JavaOutlinePage;
import org.eclipse.jdt.internal.ui.javaeditor.SemanticHighlightingManager;
import org.eclipse.jdt.internal.ui.viewsupport.AppearanceAwareLabelProvider;
import org.eclipse.jdt.internal.ui.viewsupport.DecoratingJavaLabelProvider;
import org.eclipse.jdt.ui.text.IColorManager;
import org.eclipse.jdt.ui.text.JavaSourceViewerConfiguration;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.jface.text.source.SourceViewerConfiguration;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IEditorReference;
import org.eclipse.ui.IPageLayout;
import org.eclipse.ui.IPageListener;
import org.eclipse.ui.IPartListener;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWindowListener;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.editors.text.TextSourceViewerConfiguration;
import org.eclipse.ui.part.IPage;
import org.eclipse.ui.texteditor.AbstractTextEditor;
import org.eclipse.ui.views.contentoutline.ContentOutline;
import org.eclipse.ui.views.contentoutline.IContentOutlinePage;
import org.key_project.javaeditor.extension.IJavaSourceViewerConfigurationExtension;
import org.key_project.javaeditor.outline.OutlineContentProviderWrapper;
import org.key_project.javaeditor.outline.OutlineLabelProviderWrapper;
import org.key_project.javaeditor.util.ExtendableConfigurationUtil;
import org.key_project.javaeditor.util.LogUtil;
import org.key_project.javaeditor.util.PreferenceUtil;
import org.key_project.util.java.ObjectUtil;

/**
 * Ensures at runtime that for each {@link JavaEditor} the configuration is replaced
 * by an {@link ExtendableJavaSourceViewerConfiguration} if {@link PreferenceUtil#isExtensionsEnabled()}.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public final class JavaEditorManager {
   /**
    * Defines if outline manipulations are performed or not.
    */
   public static final boolean OUTLINE_EXTENSIONS_ENABLED = false;
   
   /**
    * The only instance of this class.
    */
   public static final JavaEditorManager instance = new JavaEditorManager();
     
   /**
    * Listens for changes on {@link PreferenceUtil#getStore()}.
    */
   private final IPropertyChangeListener propertyChangeListener = new IPropertyChangeListener() {
      @Override
      public void propertyChange(PropertyChangeEvent event) {
         handlePropertyChange(event);
      }
   }; 
   
   /**
    * Listens for changes of {@link IWorkbenchWindow}s.
    */
   private final IWindowListener windowListener = new IWindowListener() {
      @Override
      public void windowActivated(IWorkbenchWindow window) {
      }

      @Override
      public void windowDeactivated(IWorkbenchWindow window) {
      }

      @Override
      public void windowClosed(IWorkbenchWindow window) {
         handleWindowClosed(window);
      }

      @Override
      public void windowOpened(IWorkbenchWindow window) {
         handleWindowOpened(window);
      }
   };

   /**
    * Listens for changes of {@link IPageListener}s.
    */
   private final IPageListener pageListener = new IPageListener() {
      @Override
      public void pageOpened(IWorkbenchPage page) {
         handlePageOpened(page);
      }
      
      @Override
      public void pageClosed(IWorkbenchPage page) {
         handlePageClosed(page);
      }
      
      @Override
      public void pageActivated(IWorkbenchPage page) {
      }
   };
   
  
   /**
    * Listens for changes of {@link IPartListener}s.
    */
   private final IPartListener partListener = new IPartListener() {
      @Override
      public void partOpened(IWorkbenchPart part) {
         handlePartOpened(part);
      }
      
      @Override
      public void partDeactivated(IWorkbenchPart part) {
      }
      
      @Override
      public void partClosed(IWorkbenchPart part) {
         handlePartClosed(part);
      }
      
      @Override
      public void partBroughtToTop(IWorkbenchPart part) {
      }
      
      @Override
      public void partActivated(IWorkbenchPart part) {
         handlePartActivated(part);
      }
   };
   
   /**
    * Ensure that this class is a singleton.
    */
   private JavaEditorManager() {
      PreferenceUtil.getStore().addPropertyChangeListener(propertyChangeListener);
   }

   /**
    * Disposes the {@link JavaEditorManager}.
    */
   public void dispose() {
      PreferenceUtil.getStore().removePropertyChangeListener(propertyChangeListener);
      stop();
   }
   
   /**
    * When a property on {@link PreferenceUtil#getStore()} has changed.
    * @param event The event.
    */
   private void handlePropertyChange(PropertyChangeEvent event) {
      if (PreferenceUtil.PROP_EXTENSIONS_ENABLED.equals(event.getProperty())) {
         if (PreferenceUtil.isExtensionsEnabled()) {
            start();
         }
         else {
            stop();
         }
      }
      else if (event.getProperty().startsWith(PreferenceUtil.PROP_EXTENSION_ENABLED_PREFIX)) {
         if (PreferenceUtil.isExtensionsEnabled()) {
            ensureCorrectExtensions();
         }
      }
   }

   /**
    * Starts the listening and initializes already available content.
    */
   public void start() {
      if (PreferenceUtil.isExtensionsEnabled()) {
         IWorkbench workbench = PlatformUI.getWorkbench();
         workbench.addWindowListener(windowListener);
         for (IWorkbenchWindow window : workbench.getWorkbenchWindows()) {
            init(window);
         }
      }
   }
   
   /**
    * Initializes the given {@link IWorkbenchWindow}.
    * @param window The {@link IWorkbenchWindow} to initialize.
    */
   private void init(IWorkbenchWindow window) {
      window.addPageListener(pageListener);
      for (IWorkbenchPage page : window.getPages()) {
         init(page);
      }
   }

   /**
    * Initializes the given {@link IWorkbenchPage}.
    * @param page The {@link IWorkbenchPage} to initialize.
    */
   private void init(IWorkbenchPage page) {
      page.addPartListener(partListener);
      for (IEditorReference reference : page.getEditorReferences()) {
         IEditorPart editor = reference.getEditor(false);
         if (editor != null) {
            init(editor);
         }
      }
   }

   /**
    * Initializes the given {@link IEditorPart}.
    * @param editor The {@link IEditorPart} to initialize.
    */
   private void init(final IEditorPart editor) {
      if (editor instanceof JavaEditor) {
         editor.getSite().getShell().getDisplay().syncExec(new Runnable() {
            @Override
            public void run() {
               replaceConfiguration((JavaEditor) editor);
               
            }
         });
      }
   }
   
   /**
    * Replaces the configuration of the {@link JavaEditor} with an {@link ExtendableJavaSourceViewerConfiguration} if required.
    * @param javaEditor The {@link JavaEditor} to modify.
    */
   private void replaceConfiguration(JavaEditor javaEditor) {
      try {
         // Get SourceViewer
         ISourceViewer iviewer = javaEditor.getViewer();
         if (iviewer instanceof SourceViewer) {
            SourceViewer viewer = (SourceViewer) iviewer;
            // Get original JavaSourceViewerConfiguration
            Object configuration = ObjectUtil.invoke(javaEditor, "getSourceViewerConfiguration");
            if (configuration instanceof ExtendableJavaSourceViewerConfiguration) {
               ExtendableJavaSourceViewerConfiguration oldConf = (ExtendableJavaSourceViewerConfiguration) configuration;
               // Check if update is required
               IJavaSourceViewerConfigurationExtension[] newExtensions = ExtendableConfigurationUtil.createEnabledJavaExtensions();
               if (!Arrays.deepEquals(newExtensions, oldConf.getExtensions())) {
                  // Create new JavaSourceViewerConfiguration
                  IColorManager colorManager = ObjectUtil.get(oldConf.getOriginalConfiguration(), JavaSourceViewerConfiguration.class, "fColorManager");
                  IPreferenceStore store = ObjectUtil.get(oldConf.getOriginalConfiguration(), TextSourceViewerConfiguration.class, "fPreferenceStore");
                  String partitioning = ObjectUtil.get(oldConf.getOriginalConfiguration(), JavaSourceViewerConfiguration.class, "fDocumentPartitioning");
                  ExtendableJavaSourceViewerConfiguration newConf = new ExtendableJavaSourceViewerConfiguration(colorManager, store, javaEditor, partitioning, oldConf.getOriginalConfiguration(), newExtensions);
                  
                  
                  
                  
                  // Replace configuration
                  changeConfiguration(javaEditor, viewer, newConf);
               }
            }
            else if (configuration instanceof JavaSourceViewerConfiguration) {
               JavaSourceViewerConfiguration oldConf = (JavaSourceViewerConfiguration) configuration;
               // Create new JavaSourceViewerConfiguration
               IColorManager colorManager = ObjectUtil.get(oldConf, JavaSourceViewerConfiguration.class, "fColorManager");
               IPreferenceStore store = ObjectUtil.get(oldConf, TextSourceViewerConfiguration.class, "fPreferenceStore");
               String partitioning = ObjectUtil.get(oldConf, JavaSourceViewerConfiguration.class, "fDocumentPartitioning");
               IJavaSourceViewerConfigurationExtension[] extensions = ExtendableConfigurationUtil.createEnabledJavaExtensions();
               ExtendableJavaSourceViewerConfiguration newConf = new ExtendableJavaSourceViewerConfiguration(colorManager, store, javaEditor, partitioning, oldConf, extensions);
               // Replace configuration
               changeConfiguration(javaEditor, viewer, newConf);
            }
            else {
               throw new OperationNotSupportedException("AbstractTextEditor implementation has changed, functionality not provided.");
            }
         }
         else {
            throw new OperationNotSupportedException("JavaEditor implementation has changed, functionality not provided.");
         }
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
      }
   }
   
   /**
    * Changes the {@link SourceViewerConfiguration} in the given {@link JavaEditor}.
    * @param javaEditor The {@link JavaEditor} to modify.
    * @param viewer The {@link SourceViewer} of the {@link JavaEditor} to modify.
    * @param newConf The new {@link SourceViewerConfiguration} to use.
    * @throws IllegalArgumentException Occurred Exception.
    * @throws IllegalAccessException Occurred Exception.
    * @throws InvocationTargetException Occurred Exception.
    * @throws NoSuchMethodException Occurred Exception.
    * @throws SecurityException Occurred Exception.
    * @throws NoSuchFieldException Occurred Exception.
    */
   private void changeConfiguration(JavaEditor javaEditor, SourceViewer viewer, SourceViewerConfiguration newConf) throws IllegalArgumentException, IllegalAccessException, InvocationTargetException, NoSuchMethodException, SecurityException, NoSuchFieldException {
      // Change configuration in JavaEditor
      viewer.unconfigure();
      viewer.configure(newConf);
      ObjectUtil.invoke(javaEditor, ObjectUtil.findMethod(AbstractTextEditor.class, "setSourceViewerConfiguration", SourceViewerConfiguration.class), newConf);
      // Change configuration in SemanticHighlightingManager
      Object semanticManager = ObjectUtil.get(javaEditor, "fSemanticManager");
      if (semanticManager instanceof SemanticHighlightingManager) {
         ObjectUtil.invoke(semanticManager, ObjectUtil.findMethod(SemanticHighlightingManager.class, "disable"));
         ObjectUtil.set(semanticManager, "fConfiguration", newConf);
         ObjectUtil.set(semanticManager, "fPresentationReconciler", newConf.getPresentationReconciler(viewer));
         ObjectUtil.invoke(semanticManager, ObjectUtil.findMethod(SemanticHighlightingManager.class, "enable"));
      }
      else {
         LogUtil.getLogger().logWarning("SemanticHighlightingManager no longer available.");
      }
      // Update outline if needed
      updateOutline(javaEditor);
   }
   
   /**
    * Updates the outline of the given {@link JavaEditor} according to 
    * {@link PreferenceUtil#isExtensionsEnabled()}.
    * @param javaEditor The {@link JavaEditor} to update its outline.
    */
   private static void updateOutline(final JavaEditor javaEditor) {

      javaEditor.getEditorSite().getShell().getDisplay().asyncExec(new Runnable() {
         @Override
         public void run() {
            try {
               IContentOutlinePage outline = (IContentOutlinePage)javaEditor.getAdapter(IContentOutlinePage.class);
               updateOutline(outline);
            }
            catch (Exception e) {
               LogUtil.getLogger().logError(e);
            }
         }
      });
   }

   
   /**
    * Updates the given {@link IPage} of the outline view according to 
    * {@link PreferenceUtil#isExtensionsEnabled()}.
    * @param outlinePage The {@link IPage} to update.
    * @throws NoSuchMethodException Occurred Exception.
    * @throws IllegalArgumentException Occurred Exception.
    * @throws IllegalAccessException Occurred Exception.
    * @throws InvocationTargetException Occurred Exception.
    */
   private static void updateOutline(IPage outlinePage) throws NoSuchMethodException, IllegalArgumentException, IllegalAccessException, InvocationTargetException {
      if (OUTLINE_EXTENSIONS_ENABLED && outlinePage instanceof JavaOutlinePage) {
         JavaOutlinePage joutline = (JavaOutlinePage) outlinePage;
         TreeViewer outlineViewer = ObjectUtil.invoke(joutline, "getOutlineViewer");
         ITreeContentProvider contentProvider = (ITreeContentProvider) outlineViewer.getContentProvider();
         DecoratingJavaLabelProvider labelProvider = (DecoratingJavaLabelProvider) outlineViewer.getLabelProvider();
         // Check content provider
         if (contentProvider instanceof OutlineContentProviderWrapper) {
            if (!PreferenceUtil.isExtensionsEnabled()) { // Restore content provider if required
               outlineViewer.setContentProvider(((OutlineContentProviderWrapper) contentProvider).getOriginalProvider());
               contentProvider.dispose();
            }
         }
         else {
            if (PreferenceUtil.isExtensionsEnabled()) { // Change content provider if required
               OutlineContentProviderWrapper contentProvierWrapper = new OutlineContentProviderWrapper(contentProvider, joutline, outlineViewer);
               outlineViewer.setContentProvider(contentProvierWrapper);
            }
         }
         // Check label provider
         if (labelProvider instanceof OutlineLabelProviderWrapper) {
            if (!PreferenceUtil.isExtensionsEnabled()) { // Restore label provider if required
               outlineViewer.setLabelProvider(new DecoratingJavaLabelProvider((AppearanceAwareLabelProvider) labelProvider.getStyledStringProvider()));
               labelProvider.dispose();
            }
         }
         else {
            if (PreferenceUtil.isExtensionsEnabled()) { // Change label provider if required
               OutlineLabelProviderWrapper outlineProviderwrapper = new OutlineLabelProviderWrapper((AppearanceAwareLabelProvider) labelProvider.getStyledStringProvider());
               outlineViewer.setLabelProvider(outlineProviderwrapper);
               labelProvider.dispose();
            }
         }
      }
   }

   /**
    * Stops the listening and removes modifications from available content.
    */
   public void stop() {
      IWorkbench workbench = PlatformUI.getWorkbench();
      workbench.removeWindowListener(windowListener);
      for (IWorkbenchWindow window : workbench.getWorkbenchWindows()) {
         deinit(window, false);
      }
   }
   
   /**
    * Removes modifications on the given {@link IWorkbenchWindow}.
    * @param window The {@link IWorkbenchWindow} to restore.
    * @param closing {@code true} {@link IEditorPart} is going to be closed, {@code false} {@link IEditorPart} remains open.
    */
   private void deinit(IWorkbenchWindow window, boolean closing) {
      window.removePageListener(pageListener);
      for (IWorkbenchPage page : window.getPages()) {
         deinit(page, closing);
      }
   }

   /**
    * Removes modifications on the given {@link IWorkbenchPage}.
    * @param page The {@link IWorkbenchPage} to restore.
    * @param closing {@code true} {@link IEditorPart} is going to be closed, {@code false} {@link IEditorPart} remains open.
    */
   private void deinit(IWorkbenchPage page, boolean closing) {
      page.removePartListener(partListener);
      for (IEditorReference reference : page.getEditorReferences()) {
         IEditorPart editor = reference.getEditor(false);
         if (editor != null) {
            deinit(editor, closing);
         }
      }
   }

   /**
    * Removes modifications on the given {@link IEditorPart}.
    * @param window The {@link IEditorPart} to restore.
    * @param closing {@code true} {@link IEditorPart} is going to be closed, {@code false} {@link IEditorPart} remains open.
    */
   private void deinit(final IEditorPart editor, boolean closing) {
      if (!closing) {
         if (editor instanceof JavaEditor) {
            editor.getSite().getShell().getDisplay().syncExec(new Runnable() {
               @Override
               public void run() {
                  restoreConfiguration((JavaEditor) editor);
               }
            });
         }
      }
   }
   
   /**
    * Restores the original configuration of the {@link JavaEditor}.
    * @param javaEditor The {@link JavaEditor} to modify.
    */
   private void restoreConfiguration(JavaEditor javaEditor) {
      try {
         // Get SourceViewer
         ISourceViewer iviewer = javaEditor.getViewer();
         if (iviewer instanceof SourceViewer) {
            SourceViewer viewer = (SourceViewer) iviewer;
            // Get original JavaSourceViewerConfiguration
            Object configuration = ObjectUtil.invoke(javaEditor, "getSourceViewerConfiguration");
            if (configuration instanceof ExtendableJavaSourceViewerConfiguration) {
               ExtendableJavaSourceViewerConfiguration conf = (ExtendableJavaSourceViewerConfiguration) configuration;
               // Restore configuration
               changeConfiguration(javaEditor, viewer, conf.getOriginalConfiguration());
            }
         }
         // Restore outline
         updateOutline(javaEditor);
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
      }
   }
   
   /**
    * When a new {@link IWorkbenchWindow} is opened.
    * @param window The opened {@link IWorkbenchWindow}.
    */
   private void handleWindowOpened(IWorkbenchWindow window) {
      if (PreferenceUtil.isExtensionsEnabled()) {
         init(window);
      }
   }

   /**
    * When an {@link IWorkbenchWindow} is closed.
    * @param window The closed {@link IWorkbenchWindow}.
    */
   private void handleWindowClosed(IWorkbenchWindow window) {
      if (PreferenceUtil.isExtensionsEnabled()) {
         deinit(window, true);
      }
   }

   /**
    * When a new {@link IWorkbenchPage} is opened.
    * @param page The opened {@link IWorkbenchPage}.
    */
   private void handlePageOpened(IWorkbenchPage page) {
      if (PreferenceUtil.isExtensionsEnabled()) {
         init(page);
      }
   }

   /**
    * When an {@link IWorkbenchPage} is closed.
    * @param page The closed {@link IWorkbenchPage}.
    */
   private void handlePageClosed(IWorkbenchPage page) {
      if (PreferenceUtil.isExtensionsEnabled()) {
         deinit(page, true);
      }
   }

   /**
    * When a new {@link IWorkbenchPart} is opened.
    * @param part The opened {@link IWorkbenchPart}.
    */
   private void handlePartOpened(IWorkbenchPart part) {
      if (PreferenceUtil.isExtensionsEnabled()) {
         if (part instanceof IEditorPart) {
            init((IEditorPart) part);
         }
         else if (part instanceof IViewPart) {
            if (IPageLayout.ID_OUTLINE.equals(part.getSite().getId())) {
               initOutline((IViewPart) part);
            }
         }
      }
   }

   /**
    * Initializes a newly opened outline view.
    * @param part The newly opened outline view.
    */
   private void initOutline(IViewPart part) {
      try {
         if (part instanceof ContentOutline) {
            ContentOutline co = (ContentOutline) part;
            updateOutline(co.getCurrentPage());
         }
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
      }
   }

   /**
    * When an {@link IWorkbenchPart} is activated.
    * @param part The activated {@link IWorkbenchPart}.
    */
   protected void handlePartActivated(IWorkbenchPart part) {
      if (PreferenceUtil.isExtensionsEnabled()) {
         if (part instanceof JavaEditor) {
            updateOutline((JavaEditor) part);
         }
      }
   }

   /**
    * When an {@link IWorkbenchPart} is closed.
    * @param part The closed {@link IWorkbenchPart}.
    */
   private void handlePartClosed(IWorkbenchPart part) {
      if (PreferenceUtil.isExtensionsEnabled()) {
         if (part instanceof IEditorPart) {
            deinit((IEditorPart) part, true);
         }
      }
   }

   /**
    * Ensures that the correct extensions are used in all editors.
    */
   private void ensureCorrectExtensions() {
      IWorkbench workbench = PlatformUI.getWorkbench();
      for (IWorkbenchWindow window : workbench.getWorkbenchWindows()) {
         ensureCorrectExtensions(window);
      }
   }

   /**
    * Ensures that the correct extensions are used in all editors of the given {@link IWorkbenchWindow}.
    * @param window The {@link IWorkbenchWindow} to ensure extensions.
    */
   private void ensureCorrectExtensions(IWorkbenchWindow window) {
      for (IWorkbenchPage page : window.getPages()) {
         ensureCorrectExtensions(page);
      }
   }

   /**
    * Ensures that the correct extensions are used in all editors of the given {@link IWorkbenchPage}.
    * @param page The {@link IWorkbenchPage} to ensure extensions.
    */
   private void ensureCorrectExtensions(IWorkbenchPage page) {
      for (IEditorReference reference : page.getEditorReferences()) {
         IEditorPart editor = reference.getEditor(false);
         if (editor != null) {
            ensureCorrectExtensions(editor);
         }
      }
   }

   /**
    * Ensures that the correct extensions are used in the given {@link IEditorPart}.
    * @param editor The {@link IEditorPart} to ensure extensions.
    */
   private void ensureCorrectExtensions(IEditorPart editor) {
      if (editor instanceof JavaEditor) {
         replaceConfiguration((JavaEditor) editor);
      }
   }

   /**
    * Returns the only instance of this class.
    * @return The only instance of this class.
    */
   public static JavaEditorManager getInstance() {
      return instance;
   }
}
