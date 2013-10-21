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
import org.junit.Test;
import org.key_project.keyide.ui.providers.BranchFolder;
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
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;
import de.uka.ilkd.key.util.NodePreorderIterator;

//TODO Document class OutlineContentAndLabelProviderTest
public class OutlineContentAndLabelProviderTest extends AbstractSetupTestCase {
   // TODO: Write test cases which makes sure that the shown content is updated when some rules are applied via auto mode (With and without new branches) 
   // TODO: Write test cases which makes sure that the shown conten tis updated when a rule is applied manually (with and without new branches)
   
   /**
    * Creates a proof and the viewer of the proof for the tests.
    * @throws Exception
    */
   @Test
   public void testInitialStructure() throws Exception {
      // Create test project
      IJavaProject project = TestUtilsUtil.createJavaProject("OutlineContentAndLabelProviderTest_testInitialStructure");
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
         shell.setText("OutlineContentAndLabelProviderTest");
         shell.setSize(600, 400);
         shell.setLayout(new FillLayout());
         TreeViewer viewer = new TreeViewer(shell, SWT.MULTI | SWT.H_SCROLL | SWT.V_SCROLL | SWT.VIRTUAL);
         viewer.setUseHashlookup(true);
         viewer.setContentProvider(new LazyProofTreeContentProvider(viewer, environment, proof));
         viewer.setLabelProvider(new ProofTreeLabelProvider(viewer, environment, proof));
         viewer.setInput(proof);
         shell.setVisible(true);
         viewer.expandAll();
         TreeViewerIterator viewerIter = new TreeViewerIterator(viewer);
         NodePreorderIterator nodeIter = new NodePreorderIterator(proof.root());
         while(nodeIter.hasNext()){
            assertTree(nodeIter, viewerIter);
         }
      }
      finally {
         shell.setVisible(false);
         shell.dispose();
      }
   }
   
   protected void assertTree(NodePreorderIterator nodeIter, TreeViewerIterator viewerIter){
      
      if(nodeIter.hasNext()){
         Node proofNode = nodeIter.next();
      
         if(!proofNode.equals(proofNode.proof().root())){
            if(proofNode.parent().childrenCount() == 1){
               if(viewerIter.hasNext()){
                  Object itemData = viewerIter.next().getData();
                  if(itemData instanceof Node){
                     assertTrue(proofNode.equals(itemData));
                  }
                  else fail("There must be a Node after a Node wit childCount == 1");
               }
               else fail("Less elements in the Proof then in the Viewer"); 
            }
            else{
               if(viewerIter.hasNext()){
                  Object itemData = viewerIter.next().getData();
                  if(itemData instanceof BranchFolder){
                     BranchFolder bf = (BranchFolder) itemData;
                     assertTrue(proofNode.equals(bf.getChild()));
                     if(viewerIter.hasNext()){
                       itemData = viewerIter.next().getData();
                       if(itemData instanceof Node){
                          assertTrue(proofNode.equals(itemData));
                       }
                       else fail("There must be a Node after a BranchFolder");
                     }
                     else fail("Less elements in the Proof then in the Viewer");
                  }
                  else fail("There must be a BranchFolder after a Node with childCount > 1");
               }
               else fail("Less elements in the Proof then in the Viewer");
            }
         }
         else{
            if(viewerIter.hasNext()){
               Object itemData = viewerIter.next().getData();
               if(itemData instanceof Node){
                  assertTrue(proofNode.equals(itemData));
               }
               else fail("The first item must be a Node");
            }
            else fail("Less elements in the Proof then in the Viewer");
         }
      }
      else assertFalse(viewerIter.hasNext());
   }
}
