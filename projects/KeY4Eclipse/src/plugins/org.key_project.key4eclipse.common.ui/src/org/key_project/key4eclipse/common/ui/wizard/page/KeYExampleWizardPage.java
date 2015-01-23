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

package org.key_project.key4eclipse.common.ui.wizard.page;

import java.io.File;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.jdt.internal.ui.JavaPlugin;
import org.eclipse.jdt.internal.ui.javaeditor.JavaSourceViewer;
import org.eclipse.jdt.internal.ui.text.SimpleJavaSourceViewerConfiguration;
import org.eclipse.jdt.ui.PreferenceConstants;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.StackLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.swt.widgets.Sash;
import org.eclipse.swt.widgets.TabFolder;
import org.eclipse.swt.widgets.TabItem;
import org.eclipse.swt.widgets.Text;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.jdt.JDTUtil;

import de.uka.ilkd.key.core.Main;
import de.uka.ilkd.key.gui.ExampleChooser;
import de.uka.ilkd.key.gui.ExampleChooser.Example;

/**
 * This {@link WizardPage} allows to select a KeY example.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class KeYExampleWizardPage extends WizardPage {
   /**
    * Shows the available examples.
    */
   private TreeViewer examplesViewer;

   /**
    * Shows the available content.  
    */
   private Composite contentComposite;
   
   /**
    * The {@link StackLayout} used by {@link #contentComposite}.
    */
   private StackLayout contentCompositeLayout;
   
   /**
    * The content shown if no valid example is selected.
    */
   private Composite notTabContent;
   
   /**
    * Contains the available content tabs.
    */
   private final Map<ExampleNode, TabFolder> tabFolderMap = new HashMap<KeYExampleWizardPage.ExampleNode, TabFolder>();
   
   /**
    * Constructor.
    * @param pageName The name of this page.
    */
   public KeYExampleWizardPage(String pageName) {
      super(pageName);
      setTitle("KeY Examples");
      setDescription("Select one example to create a Java Project for.");
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void createControl(Composite parent) {
      final Composite root = new Composite(parent, SWT.NONE);
      root.setLayout(new GridLayout(3, false));
      setControl(root);
      // Examples
      examplesViewer = new TreeViewer(root, SWT.BORDER | SWT.SINGLE);
      final GridData viewerLayoutData = new GridData(GridData.FILL_VERTICAL);
      viewerLayoutData.widthHint = 180;
      examplesViewer.getControl().setLayoutData(viewerLayoutData);
      examplesViewer.setContentProvider(new ExampleNodeContentProvider());
      File examplesDir = new File(Main.getExamplesDir());
      List<ExampleChooser.Example> examples = ExampleChooser.listExamples(examplesDir);
      ExampleNode rootNode = createExampleTree(examples);
      examplesViewer.setInput(rootNode);
      selectInitialExample(rootNode);
      examplesViewer.addSelectionChangedListener(new ISelectionChangedListener() {
         @Override
         public void selectionChanged(SelectionChangedEvent event) {
            updatePageCompletedAndShownDescription();
         }
      });
      // Sash 
      final Sash sash = new Sash(root, SWT.VERTICAL);
      sash.setLayoutData(new GridData(GridData.FILL_VERTICAL));
      sash.addListener(SWT.Selection, new Listener() {
         @Override
         public void handleEvent(Event event) {
            if (event.detail != SWT.DRAG) {
               int shift = event.x - sash.getBounds().x;
               viewerLayoutData.widthHint = viewerLayoutData.widthHint + shift;
               root.layout(true);
            }
         }
      });
      // Tabs Content
      contentCompositeLayout = new StackLayout();
      contentComposite = new Composite(root, SWT.NONE);
      contentComposite.setLayout(contentCompositeLayout);
      GridData contentCompositeData = new GridData(GridData.FILL_BOTH);
      contentCompositeData.widthHint = 400;
      contentComposite.setLayoutData(contentCompositeData);
      notTabContent = new Composite(contentComposite, SWT.NONE);
      contentCompositeLayout.topControl = notTabContent;
      // Update initial content
      updatePageCompletedAndShownDescription();
   }
   
   /**
    * Selects the initial example.
    * @param root The {@link ExampleNode} to start search at.
    */
   protected void selectInitialExample(ExampleNode root) {
      ExampleNode[] children = root.getChildren();
      while (children.length >= 1) {
         examplesViewer.expandToLevel(root, 1);
         root = children[0];
         children = root.getChildren();
      }
      examplesViewer.setSelection(SWTUtil.createSelection(root), true);
   }

   /**
    * Updates the page completed stated and the shown description when
    * the selected example has changed.
    */
   protected void updatePageCompletedAndShownDescription() {
      ExampleNode node = getSelectedExampleNode();
      Example selectedExample = node != null ? node.getExample() : null;
      if (selectedExample != null) {
         // Update page completed state
         setErrorMessage(null);
         setPageComplete(true);
         // Update shown tabs
         showTabs(node);
      }
      else {
         // Update page completed state
         setPageComplete(false);
         if (node != null) {
            setErrorMessage("Category '" + node.getText() + "' selected instead of an example.");
         }
         else {
            setErrorMessage("No example selected.");
         }
         // Show no tabs
         contentCompositeLayout.topControl = notTabContent;
         contentComposite.layout();
      }
   }
   
   /**
    * Shows the tabs of the given {@link ExampleNode}.
    * If no previous tabs exist new one will be created.
    * @param node The {@link ExampleNode} to show.
    */
   protected void showTabs(ExampleNode node) {
      TabFolder tabFolder = tabFolderMap.get(node);
      if (tabFolder == null) {
         tabFolder = new TabFolder(contentComposite, SWT.NONE);
         tabFolderMap.put(node, tabFolder);
         // Description
         TabItem descriptionItem = new TabItem(tabFolder, SWT.NONE);
         descriptionItem.setText("Description");
         Text descriptionText = new Text(tabFolder, SWT.BORDER | SWT.V_SCROLL | SWT.MULTI | SWT.WRAP);
         descriptionText.setText(node.getExample().getDescription());
         descriptionText.setEditable(false);
         descriptionItem.setControl(descriptionText);
         // Proof Obligation
         createFileTab(tabFolder, "Proof Obligation", node.getExample().getObligationFile());
         // Additional files
         List<File> additionalFiles = node.getExample().getAdditionalFiles();
         for (File additionalFile : additionalFiles) {
            createFileTab(tabFolder, additionalFile.getName(), additionalFile);
         }
      }
      contentCompositeLayout.topControl = tabFolder;
      contentComposite.layout();
   }
   
   /**
    * Creates a tab showing the given {@link File}.
    * @param tabFolder The parent {@link TabFolder}.
    * @param tabText The tab text to show.
    * @param file The {@link File} to show its content.
    */
   protected void createFileTab(TabFolder tabFolder, String tabText, File file) {
      if (file != null && file.exists()) {
         TabItem poItem = new TabItem(tabFolder, SWT.NONE);
         poItem.setText(tabText);
         String text;
         try {
            text = IOUtil.readFrom(file);
         }
         catch (Exception e) {
            text = e.getMessage();
         }
         IDocument document = new Document(text);
         SourceViewer viewer;
         if (JDTUtil.JAVA_FILE_EXTENSION.equals(IOUtil.getFileExtension(file))) {
            // Have a look at org.eclipse.jdt.internal.ui.refactoring.JavaStatusContextViewer to see how to setup a SourceViewer for Java
            IPreferenceStore store = JavaPlugin.getDefault().getCombinedPreferenceStore();
            viewer = new JavaSourceViewer(tabFolder, null, null, false, SWT.LEFT_TO_RIGHT | SWT.V_SCROLL | SWT.H_SCROLL | SWT.MULTI | SWT.FULL_SELECTION, store);
            viewer.configure(new SimpleJavaSourceViewerConfiguration(JavaPlugin.getDefault().getJavaTextTools().getColorManager(), 
                                                                     store,
                                                                     null,
                                                                     null,
                                                                     false));
            JavaPlugin.getDefault().getJavaTextTools().setupJavaDocumentPartitioner(document);
         }
         else {
            viewer = new SourceViewer(tabFolder, null, SWT.LEFT_TO_RIGHT | SWT.V_SCROLL | SWT.H_SCROLL | SWT.MULTI | SWT.FULL_SELECTION);
         }
         viewer.getControl().setFont(JFaceResources.getFont(PreferenceConstants.EDITOR_TEXT_FONT));
         viewer.setEditable(false);
         viewer.setInput(document);
         poItem.setControl(viewer.getControl());
      }
   }

   /**
    * Returns the selected example.
    * @return The selected example.
    */
   public ExampleChooser.Example getSelectedExample() {
      ExampleNode node = getSelectedExampleNode();
      if (node != null) {
         return node.getExample();
      }
      else {
         return null;
      }
   }
   
   /**
    * Returns the selected {@link ExampleNode}.
    * @return The selected {@link ExampleNode}.
    */
   public ExampleNode getSelectedExampleNode() {
      Object selected = SWTUtil.getFirstElement(examplesViewer.getSelection());
      if (selected instanceof ExampleNode) {
         return (ExampleNode) selected;
      }
      else {
         return null;
      }
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * Changed visibility to public.
    * </p>
    */
   @Override
   public boolean isCurrentPage() {
      return super.isCurrentPage();
   };
   
   /**
    * Converts the given {@link Example}s into a tree of {@link ExampleNode}s.
    * @param examples The available {@link Example}s to convert.
    * @return The root of the created tree.
    */
   protected ExampleNode createExampleTree(List<Example> examples) {
      ExampleNode root = new ExampleNode("examples");
      for (Example example : examples) {
         ExampleNode parent = root;
         String[] path = example.getPath();
         for (String text : path) {
            ExampleNode child = parent.searchChild(text);
            if (child == null) {
               child = new ExampleNode(text);
               parent.addChild(child);
            }
            parent = child;
         }
         parent.addChild(new ExampleNode(example));
      }
      return root;
   }
   
   /**
    * A node in a tree of {@link Example}s.
    * @author Martin Hentschel
    */
   private static class ExampleNode {
      /**
       * The shown node text.
       */
      private final String text;
      
      /**
       * Optionally, the represented {@link Example}.
       */
      private final Example example;
      
      /**
       * The children.
       */
      private final List<ExampleNode> children = new LinkedList<KeYExampleWizardPage.ExampleNode>();
      
      /**
       * Constructor.
       * @param text The text to show.
       */
      public ExampleNode(String text) {
         this.text = text;
         this.example = null;
      }
      
      /**
       * Constructor.
       * @param example The {@link Example} to represent.
       */
      public ExampleNode(Example example) {
         this.text = example.getName();
         this.example = example;
      }

      /**
       * Returns the text to show.
       * @return The text to show.
       */
      public String getText() {
         return text;
      }

      /**
       * Returns the represented {@link Example}.
       * @return The represented {@link Example} or {@code null} otherwise.
       */
      public Example getExample() {
         return example;
      }
      
      /**
       * Adds the given {@link ExampleNode}.
       * @param child The {@link ExampleNode} to add.
       */
      public void addChild(ExampleNode child) {
         if (child != null) {
            children.add(child);
         }
      }
      
      /**
       * Returns all available children.
       * @return All available children.
       */
      public ExampleNode[] getChildren() {
         return children.toArray(new ExampleNode[children.size()]);
      }
      
      /**
       * Searches the child with the given text.
       * @param text The text to search.
       * @return The found {@link ExampleNode} or {@code null} if not available.
       */
      public ExampleNode searchChild(final String text) {
         return CollectionUtil.search(children, new IFilter<ExampleNode>() {
            @Override
            public boolean select(ExampleNode element) {
               return ObjectUtil.equals(text, element.getText());
            }
         });
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String toString() {
         return text;
      }
   }
   
   /**
    * {@link ITreeContentProvider} used to show {@link ExampleNode}s.
    * @author Martin Hentschel
    */
   private static class ExampleNodeContentProvider implements ITreeContentProvider {
      /**
       * {@inheritDoc}
       */
      @Override
      public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Object[] getChildren(Object parentElement) {
         if (parentElement instanceof ExampleNode) {
            return ((ExampleNode) parentElement).getChildren();
         }
         else {
            return new ExampleNode[0];
         }
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public boolean hasChildren(Object element) {
         return !ArrayUtil.isEmpty(getChildren(element));
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Object[] getElements(Object inputElement) {
         return getChildren(inputElement);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Object getParent(Object element) {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void dispose() {
      }
   }
}