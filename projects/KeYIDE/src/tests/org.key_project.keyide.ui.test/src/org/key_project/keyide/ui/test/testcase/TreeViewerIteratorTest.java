/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
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

package org.key_project.keyide.ui.test.testcase;

import java.io.File;

import org.eclipse.core.resources.IFolder;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Tree;
import org.eclipse.swt.widgets.TreeItem;
import org.junit.Test;
import org.key_project.keyide.ui.providers.LazyProofTreeContentProvider;
import org.key_project.keyide.ui.providers.ProofTreeLabelProvider;
import org.key_project.keyide.ui.test.Activator;
import org.key_project.keyide.ui.test.util.TreeViewerIterator;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.test.testcase.AbstractSetupTestCase;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

// TODO: Tests LazyProofTreeContentProvider#getParent() on each possible node (visible structure not proof tree structure!)
// TODO: Tests LazyProofTreeContentProvider#getIndexOf(Object, Object) on each possible parent child combinations (visible structure not proof tree structure!)

// TODO Document class TreeViewerIteratorTest
public class TreeViewerIteratorTest extends AbstractSetupTestCase {
   /**
    * Creates a proof and the viewer of the proof for the tests.
    * @throws Exception
    */
   @Test
   public void testIterator() throws Exception {
      // Create test project
      IJavaProject project = TestUtilsUtil.createJavaProject("TreeViewerIteratorTest_testInitialStructure");
      IFolder src = project.getProject().getFolder("src");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/paycard", src);
      // Get local file in operating system of folder src 
      File location = ResourceUtil.getLocation(src);
      // Load source code in KeY and get contract to proof which is the first contract of PayCard#isValid().
      KeYEnvironment<CustomConsoleUserInterface> environment = KeYEnvironment.load(location, null, null);
      IProgramMethod pm = TestUtilsUtil.searchProgramMethod(environment.getServices(), "PayCard", "isValid");
      ImmutableSet<FunctionalOperationContract> operationContracts = environment.getSpecificationRepository().getOperationContracts(pm.getContainerType(), pm);
      FunctionalOperationContract foc = CollectionUtil.getFirst(operationContracts);
      Proof proof = environment.createProof(foc.createProofObl(environment.getInitConfig(), foc));
      assertNotNull(proof);
      // Close proof automatically
      environment.getUi().startAndWaitForAutoMode(proof);
      // Create viewer to show proof in
      Shell shell = new Shell();
      try {
         shell.setText("TreeViewerIteratorTest");
         shell.setSize(600, 400);
         shell.setLayout(new FillLayout());
         TreeViewer viewer = new TreeViewer(shell, SWT.MULTI | SWT.H_SCROLL | SWT.V_SCROLL | SWT.VIRTUAL);
         viewer.setUseHashlookup(true);
         viewer.setContentProvider(new LazyProofTreeContentProvider(viewer, environment, proof));
         viewer.setLabelProvider(new ProofTreeLabelProvider(viewer, environment, proof));
         viewer.setInput(proof);
         shell.setVisible(true);
         viewer.expandAll();
         TreeViewerIterator vtIter = new TreeViewerIterator(viewer);
         Tree tree = viewer.getTree();
         TreeItem[] items = tree.getItems();
         for(TreeItem item : items){
            assertTreeItem(item, vtIter);
         }
         if(vtIter.hasNext()){
            fail("ViewerTreeIterator has more items then the TreeViewer");
         }
      }
      finally {
         shell.setVisible(false);
         shell.dispose();
      }
   }
   
   protected void assertTreeItem(TreeItem item, TreeViewerIterator vtIter){
      if(vtIter.hasNext()){
         Object vtIterItem = vtIter.next();
         assertTrue(item.equals(vtIterItem));
         TreeItem[] children = item.getItems();
         for (TreeItem child : children) {
            assertTreeItem(child, vtIter);
         }
      }
      else fail("TreeViewer has more items then the TreeViewerIterator");
   }
}