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

import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Text;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.gui.ExampleChooser;
import de.uka.ilkd.key.gui.ExampleChooser.Example;
import de.uka.ilkd.key.gui.Main;

/**
 * This {@link WizardPage} allows to select a KeY example.
 * @author Martin Hentschel
 */
public class KeYExampleWizardPage extends WizardPage {
   /**
    * Shows the available examples.
    */
   private TreeViewer examplesViewer;
   
   /**
    * Shows the description of the selected example.
    */
   private Text descriptionText;
   
   /**
    * Maps an example to its description.
    */
   private Map<ExampleChooser.Example, String> example2descriptionMap = new HashMap<ExampleChooser.Example, String>();
   
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
      Composite root = new Composite(parent, SWT.NONE);
      root.setLayout(new GridLayout(2, false));
      // Examples
      Group examplesGroup = new Group(root, SWT.NONE);
      examplesGroup.setLayoutData(new GridData(GridData.FILL_VERTICAL));
      examplesGroup.setText("Examples");
      examplesGroup.setLayout(new FillLayout());
      examplesViewer = new TreeViewer(examplesGroup, SWT.BORDER | SWT.SINGLE);
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
      // Description
      Group descriptionGroup = new Group(root, SWT.NONE);
      GridData descriptionGroupData = new GridData(GridData.FILL_BOTH);
      descriptionGroupData.widthHint = 400;
      descriptionGroup.setLayoutData(descriptionGroupData);
      descriptionGroup.setText("Description");
      descriptionGroup.setLayout(new FillLayout());
      descriptionText = new Text(descriptionGroup, SWT.BORDER | SWT.V_SCROLL | SWT.MULTI | SWT.WRAP);
      descriptionText.setEditable(false);
      setControl(root);
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
         // Update shown description
         String description = example2descriptionMap.get(selectedExample);
         if (description == null) {
            description = selectedExample.getDescription();
            example2descriptionMap.put(selectedExample, description);
         }
         SWTUtil.setText(descriptionText, description);
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
         // Update shown description
         descriptionText.setText(StringUtil.EMPTY_STRING);
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
   
   protected ExampleNode createExampleTree(List<ExampleChooser.Example> examples) {
      ExampleNode root = new ExampleNode("examples");
      for (ExampleChooser.Example example : examples) {
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
   
   private static class ExampleNode {
      private final String text;
      private final ExampleChooser.Example example;
      private final List<ExampleNode> children = new LinkedList<KeYExampleWizardPage.ExampleNode>();
      
      public ExampleNode(String text) {
         this.text = text;
         this.example = null;
      }
      
      public ExampleNode(Example example) {
         this.text = example.getName();
         this.example = example;
      }

      public String getText() {
         return text;
      }

      public ExampleChooser.Example getExample() {
         return example;
      }
      
      public void addChild(ExampleNode child) {
         if (child != null) {
            children.add(child);
         }
      }
      
      public ExampleNode[] getChildren() {
         return children.toArray(new ExampleNode[children.size()]);
      }
      
      public ExampleNode searchChild(final String text) {
         return CollectionUtil.search(children, new IFilter<ExampleNode>() {
            @Override
            public boolean select(ExampleNode element) {
               return ObjectUtil.equals(text, element.getText());
            }
         });
      }

      @Override
      public String toString() {
         return text;
      }
   }
   
   private static class ExampleNodeContentProvider implements ITreeContentProvider {
      @Override
      public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
      }

      @Override
      public Object[] getChildren(Object parentElement) {
         if (parentElement instanceof ExampleNode) {
            return ((ExampleNode) parentElement).getChildren();
         }
         else {
            return new ExampleNode[0];
         }
      }

      @Override
      public boolean hasChildren(Object element) {
         return !ArrayUtil.isEmpty(getChildren(element));
      }

      @Override
      public Object[] getElements(Object inputElement) {
         return getChildren(inputElement);
      }

      @Override
      public Object getParent(Object element) {
         return null;
      }

      @Override
      public void dispose() {
      }
   }
}