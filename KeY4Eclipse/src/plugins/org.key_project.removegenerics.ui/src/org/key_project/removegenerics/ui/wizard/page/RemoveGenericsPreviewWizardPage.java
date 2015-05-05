package org.key_project.removegenerics.ui.wizard.page;

import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.jdt.internal.ui.JavaPlugin;
import org.eclipse.jdt.internal.ui.javaeditor.JavaSourceViewer;
import org.eclipse.jdt.internal.ui.text.SimpleJavaSourceViewerConfiguration;
import org.eclipse.jdt.ui.PreferenceConstants;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.SashForm;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.model.WorkbenchContentProvider;
import org.eclipse.ui.model.WorkbenchLabelProvider;
import org.key_project.removegenerics.ui.util.RemoveGenericImages;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.eclipse.swt.viewer.FileExtensionViewerFilter;
import org.key_project.util.jdt.JDTUtil;

/**
 * A {@link WizardPage} which shows the removed generics as preview.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class RemoveGenericsPreviewWizardPage extends WizardPage {
   /**
    * The {@link IResource} containing the source code treated by KeY.
    */
   private final IResource source;
   
   /**
    * The {@link TreeViewer} showing the resources.
    */
   private TreeViewer resourceViewer;
   
   /**
    * The {@link ILabelProvider} of {@link #resourceViewer}.
    */
   private ILabelProvider resourceViewerLabelProvider;
   
   /**
    * The {@link ITreeContentProvider} of {@link #resourceViewer}.
    */
   private ITreeContentProvider resourceViewerContentProvider;
   
   /**
    * Shows the new content of a selected {@link IFile} in {@link #resourceViewer}.
    */
   private JavaSourceViewer sourceViewer;
   
   /**
    * The available new content.
    */
   private Map<IFile, String> contentMap;

   /**
    * Constructor.
    * @param pageName The name of the page.
    * @param source The {@link IResource} containing the source code treated by KeY.
    */
   public RemoveGenericsPreviewWizardPage(String pageName, IResource source) {
      super(pageName);
      this.source = source;
      setTitle("Preview");
      setDescription("Inspect the modifications which will be applied by finishing the wizard.");
      setImageDescriptor(RemoveGenericImages.getImageDescriptor(RemoveGenericImages.REMOVE_GENERICS_WIZARD));
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void createControl(Composite parent) {
      // sash
      SashForm sashForm = new SashForm(parent, SWT.HORIZONTAL);
      setControl(sashForm);
      // resource viewer
      resourceViewer = new TreeViewer(sashForm);
      resourceViewerLabelProvider = new WorkbenchLabelProvider();
      resourceViewer.setLabelProvider(resourceViewerLabelProvider);
      resourceViewerContentProvider = new WorkbenchContentProvider();
      resourceViewer.setContentProvider(resourceViewerContentProvider);
      resourceViewer.addFilter(new FileExtensionViewerFilter(false, JDTUtil.JAVA_FILE_EXTENSION));
      resourceViewer.setInput(source);
      resourceViewer.addSelectionChangedListener(new ISelectionChangedListener() {
         @Override
         public void selectionChanged(SelectionChangedEvent event) {
            handleResourceSelectionChanged(event);
         }
      });
      // source viewer
      IPreferenceStore store = JavaPlugin.getDefault().getCombinedPreferenceStore();
      sourceViewer = new JavaSourceViewer(sashForm, null, null, false, SWT.BORDER | SWT.LEFT_TO_RIGHT | SWT.V_SCROLL | SWT.H_SCROLL | SWT.MULTI | SWT.FULL_SELECTION, store);
      sourceViewer.configure(new SimpleJavaSourceViewerConfiguration(JavaPlugin.getDefault().getJavaTextTools().getColorManager(), 
                                                                     store,
                                                                     null,
                                                                     null,
                                                                     false));
      sourceViewer.getControl().setFont(JFaceResources.getFont(PreferenceConstants.EDITOR_TEXT_FONT));
      sourceViewer.setEditable(false);
      updateShownSourceContent();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      resourceViewerContentProvider.dispose();
      resourceViewerLabelProvider.dispose();
      super.dispose();
   }

   /**
    * Returns the available new content {@link Map}.
    * @return The available new content {@link Map}.
    */
   public Map<IFile, String> getContentMap() {
      return contentMap;
   }

   /**
    * Sets the available new content {@link Map}.
    * @param contentMap The new content {@link Map} to set.
    */
   public void setContentMap(Map<IFile, String> contentMap) {
      this.contentMap = contentMap;
      getShell().getDisplay().syncExec(new Runnable() {
         @Override
         public void run() {
            updateShownSourceContent();
         }
      });
   }

   /**
    * When a new {@link IResource} in {@link #resourceViewer} has been selected.
    * @param event The {@link SelectionChangedEvent}.
    */
   protected void handleResourceSelectionChanged(SelectionChangedEvent event) {
      updateShownSourceContent();
   }
   
   /**
    * Updates the currently shown content in {@link #sourceViewer}.
    */
   protected void updateShownSourceContent() {
      Object selected = SWTUtil.getFirstElement(resourceViewer.getSelection());
      String content = null;
      if (selected instanceof IResource) {
         content = contentMap.get((IResource) selected);
      }
      IDocument document = content != null ? 
                           new Document(content) :
                           new Document();
      JavaPlugin.getDefault().getJavaTextTools().setupJavaDocumentPartitioner(document);
      sourceViewer.setInput(document);
      sourceViewer.getControl().setEnabled(content != null);
   }
}
