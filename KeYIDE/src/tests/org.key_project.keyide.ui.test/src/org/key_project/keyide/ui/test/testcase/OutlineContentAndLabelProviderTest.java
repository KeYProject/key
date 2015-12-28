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

package org.key_project.keyide.ui.test.testcase;

import java.io.File;

import org.eclipse.core.commands.Command;
import org.eclipse.core.commands.State;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.TreeItem;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.commands.ICommandService;
import org.eclipse.ui.handlers.RegistryToggleState;
import org.junit.Test;
import org.key_project.keyide.ui.handlers.HideIntermediateProofstepsHandler;
import org.key_project.keyide.ui.providers.BranchFolder;
import org.key_project.keyide.ui.providers.LazyProofTreeContentProvider;
import org.key_project.keyide.ui.providers.ProofTreeLabelProvider;
import org.key_project.keyide.ui.test.Activator;
import org.key_project.keyide.ui.test.util.TreeViewerIterator;
import org.key_project.ui.test.util.TestKeYUIUtil;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.test.testcase.AbstractSetupTestCase;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodePreorderIterator;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
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
      KeYEnvironment<DefaultUserInterfaceControl> environment = KeYEnvironment.load(location, null, null, null);
      IProgramMethod pm = TestKeYUIUtil.searchProgramMethod(environment.getServices(), "PayCard", "isValid");
      ImmutableSet<FunctionalOperationContract> operationContracts = environment.getSpecificationRepository().getOperationContracts(pm.getContainerType(), pm);
      FunctionalOperationContract foc = CollectionUtil.getFirst(operationContracts);
      Proof proof = environment.createProof(foc.createProofObl(environment.getInitConfig(), foc));
      assertNotNull(proof);
      // Close proof automatically
      environment.getProofControl().startAndWaitForAutoMode(proof);
      // Create viewer to show proof in
      Shell shell = new Shell();
      try {
         shell.setText("OutlineContentAndLabelProviderTest");
         shell.setSize(600, 400);
         shell.setLayout(new FillLayout());
         TreeViewer viewer = new TreeViewer(shell, SWT.MULTI | SWT.H_SCROLL | SWT.V_SCROLL | SWT.VIRTUAL);
         viewer.setUseHashlookup(true);
         viewer.setContentProvider(new LazyProofTreeContentProvider());
         viewer.setLabelProvider(new ProofTreeLabelProvider(viewer, environment.getProofControl(), proof));
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
   
   
   /**
    * creates a viewer for the proof and checks if the hide intermediate proofsteps filter is working correctly.
    * @throws CoreException
    * @throws InterruptedException
    * @throws ProblemLoaderException
    * @throws ProofInputException
    */
   @Test
   public void testHideIntermediateProofsteps() throws CoreException, InterruptedException, ProblemLoaderException, ProofInputException {
	  // Create test project
      IJavaProject project = TestUtilsUtil.createJavaProject("OutlineContentAndLabelProviderTest_testHideIntermediateProofsteps_beforeAutoMode");
	  IFolder src = project.getProject().getFolder("src");
	  BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/paycard", src);
	  // Get local file in operating system of folder src 
	  File location = ResourceUtil.getLocation(src);
	  // Load source code in KeY and get contract to proof which is the first contract of PayCard#isValid().
	  KeYEnvironment<DefaultUserInterfaceControl> environment = KeYEnvironment.load(location, null, null, null);
	  IProgramMethod pm = TestKeYUIUtil.searchProgramMethod(environment.getServices(), "PayCard", "isValid");
	  ImmutableSet<FunctionalOperationContract> operationContracts = environment.getSpecificationRepository().getOperationContracts(pm.getContainerType(), pm);
	  FunctionalOperationContract foc = CollectionUtil.getFirst(operationContracts);
	  Proof proof = environment.createProof(foc.createProofObl(environment.getInitConfig(), foc));
	  assertNotNull(proof);
	  // create viewer to show proof in
	  Shell shell = new Shell();
	  try {
		  shell.setText("OutlineContentAndLabelProviderTest");
	      shell.setSize(600, 400);
	      shell.setLayout(new FillLayout());
	      TreeViewer viewer = new TreeViewer(shell, SWT.MULTI | SWT.H_SCROLL | SWT.V_SCROLL | SWT.VIRTUAL);
	      viewer.setUseHashlookup(true);
	      LazyProofTreeContentProvider lazyContentProvider = new LazyProofTreeContentProvider();
	      // deactivate hiding intermediate proofsteps filter and show symbolic execution tree filter
	      lazyContentProvider.setHideState(false);
	      lazyContentProvider.setSymbolicState(false);
	      viewer.setContentProvider(lazyContentProvider);
	      viewer.setLabelProvider(new ProofTreeLabelProvider(viewer, environment.getProofControl(), proof));
	      viewer.setInput(proof);
	      shell.setVisible(true);
	      viewer.expandAll();
	      // check if initial toggle States are false
	      assertFalse(lazyContentProvider.getHideState());
	      assertFalse(lazyContentProvider.getSymbolicState());
	      // check if proof tree is correct before activating the filter
	      TreeViewerIterator viewerIter = new TreeViewerIterator(viewer);
	      NodePreorderIterator nodeIter = new NodePreorderIterator(proof.root());
	      while (nodeIter.hasNext()) {
	    	  assertTree(nodeIter, viewerIter);
	      }
	      // activate hide intermediate proofsteps filter
	      lazyContentProvider.setHideState(true);
	      // start auto mode
	      environment.getProofControl().startAndWaitForAutoMode(proof);
	      viewer.setInput(proof);
	      viewer.expandAll();
	      TreeViewerIterator viewerIterHide = new TreeViewerIterator(viewer);
	      NodePreorderIterator nodeIterHide = new NodePreorderIterator(proof.root());
	      // check if proof tree contains only branchfolders and leaves
	      while (nodeIterHide.hasNext()) {
	    	  assertHideIntermediateProofstepsTree(nodeIterHide, viewerIterHide);
          }
	          
          // deactivate hide intermediate proofsteps filter
          lazyContentProvider.setHideState(false);
          viewer.setInput(proof);
          viewer.expandAll();
          TreeViewerIterator viewerIterShow = new TreeViewerIterator(viewer);
          NodePreorderIterator nodeIterShow = new NodePreorderIterator(proof.root());
             
          // check if the complete proof tree is shown correctly again
          while (nodeIterShow.hasNext()) {
        	  assertTree(nodeIterShow, viewerIterShow);
          }
		} finally {
       		shell.setVisible(false);
       		shell.dispose();
		}
   	}
   
   /**
    * creates a viewer for the proof and checks if the show symbolic execution tree filter is working correctly.
    * @throws CoreException
 	* @throws InterruptedException
 	* @throws ProblemLoaderException
 	* @throws ProofInputException
 	*/
   @Test
   public void testShowSymbolicExecutionTree() throws CoreException, InterruptedException, ProblemLoaderException, ProofInputException {
	   // Create test project
	      IJavaProject project = TestUtilsUtil.createJavaProject("OutlineContentAndLabelProviderTest_showSymbolicExecutionTree");
		  IFolder src = project.getProject().getFolder("src");
		  BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/paycard", src);
		  // Get local file in operating system of folder src 
		  File location = ResourceUtil.getLocation(src);
		  // Load source code in KeY and get contract to proof which is the first contract of PayCard#isValid().
		  KeYEnvironment<DefaultUserInterfaceControl> environment = KeYEnvironment.load(location, null, null, null);
		  IProgramMethod pm = TestKeYUIUtil.searchProgramMethod(environment.getServices(), "PayCard", "isValid");
		  ImmutableSet<FunctionalOperationContract> operationContracts = environment.getSpecificationRepository().getOperationContracts(pm.getContainerType(), pm);
		  FunctionalOperationContract foc = CollectionUtil.getFirst(operationContracts);
		  Proof proof = environment.createProof(foc.createProofObl(environment.getInitConfig(), foc, true));
		  assertNotNull(proof);
		  // create viewer to show proof in
		  Shell shell = new Shell();
		  try {
			  shell.setText("OutlineContentAndLabelProviderTest");
		      shell.setSize(600, 400);
		      shell.setLayout(new FillLayout());
		      TreeViewer viewer = new TreeViewer(shell, SWT.MULTI | SWT.H_SCROLL | SWT.V_SCROLL | SWT.VIRTUAL);
		      viewer.setUseHashlookup(true);
		      LazyProofTreeContentProvider lazyContentProvider = new LazyProofTreeContentProvider();
		      // deactivate hiding intermediate proofsteps filter and show symbolic execution tree filter
		      lazyContentProvider.setHideState(false);
		      lazyContentProvider.setSymbolicState(false);
		      viewer.setContentProvider(lazyContentProvider);
		      viewer.setLabelProvider(new ProofTreeLabelProvider(viewer, environment.getProofControl(), proof));
		      viewer.setInput(proof);
		      shell.setVisible(true);
		      viewer.expandAll();
		      // check if initial toggle States are false
		      assertFalse(lazyContentProvider.getHideState());
		      assertFalse(lazyContentProvider.getSymbolicState());
		      // check if proof tree is correct before activating the filter
		      TreeViewerIterator viewerIter = new TreeViewerIterator(viewer);
		      NodePreorderIterator nodeIter = new NodePreorderIterator(proof.root());
		      while (nodeIter.hasNext()) {
		    	  assertTree(nodeIter, viewerIter);
		      }
		      // start auto mode
		      environment.getProofControl().startAndWaitForAutoMode(proof);
		      
		      // activate show symbolic execution tree filter
		      lazyContentProvider.setSymbolicState(true);
		      viewer.setInput(proof);
		      viewer.expandAll();
		      viewerIter = new TreeViewerIterator(viewer);
		      // create symbolic execution tree iterator
		      SymbolicExecutionTreeBuilder symExeTreeBuilder = new SymbolicExecutionTreeBuilder(proof, false, false, false, false, false);
		      symExeTreeBuilder.analyse();
		      ExecutionNodePreorderIterator exeNodeIter = new ExecutionNodePreorderIterator(symExeTreeBuilder.getStartNode());
		      // check if proof tree is correct
		      assertShowSymbolicExecutionTree(exeNodeIter, viewerIter);
		          
	          // deactivate show symbolic execution tree filter
	          lazyContentProvider.setSymbolicState(false);
	          viewer.setInput(proof);
	          viewer.expandAll();
	          viewerIter = new TreeViewerIterator(viewer);
	          nodeIter = new NodePreorderIterator(proof.root());
	             
	          // check if the complete proof tree is shown correctly again
	          while (nodeIter.hasNext()) {
	        	  assertTree(nodeIter, viewerIter);
	          }
			} finally {
	       		shell.setVisible(false);
	       		shell.dispose();
			}
   }
   
   /**
    * checks whether a filtered TreeViewer contains the correct symbolic execution tree.
    * @param exeNodeIter execution node iterator over the execution tree
 	* @param viewerIter an iterator over the filtered tree viewer
 	*/
   protected void assertShowSymbolicExecutionTree(ExecutionNodePreorderIterator exeNodeIter, TreeViewerIterator viewerIter) {
	   boolean isBranchNode = false;
	   IExecutionNode<?> exeNode = null;
	   while (exeNodeIter.hasNext()) {
		   if (!isBranchNode) {
			   exeNode = exeNodeIter.next();
		   }
		   if (viewerIter.hasNext()) {
			   Object itemData = viewerIter.next().getData();
			   if (itemData instanceof Node) {
				   assertTrue(itemData.equals(exeNode.getProofNode()));
				   if (isBranchNode) {
					   isBranchNode = false;
				   }
			   } else if (itemData instanceof BranchFolder) {
				   if (isBranchNode) {
					   exeNode = exeNodeIter.next();
				   }
				   BranchFolder bf = (BranchFolder) itemData;
				   assertTrue(bf.getChild().equals(exeNode.getProofNode()));
				   isBranchNode = true;
			   }
		   }
		   if (exeNode.getChildren().length == 0) {
			   for (int i = 0; i < exeNode.getProofNode().childrenCount(); i++) {
				   NodePreorderIterator nodeIter = new NodePreorderIterator(exeNode.getProofNode().child(i));
				   while (nodeIter.hasNext()) {
					   assertTree(nodeIter, viewerIter);
				   }
			   }
		   }
	   }
   }
   
   /**
    * Checks whether a filtered TreeViewer contains any intermediate proof steps of a proof.
    * @param nodeIter a node iterator over the proof tree
    * @param viewerIter an iterator over the filtered tree viewer
    */
   protected void assertHideIntermediateProofstepsTree(NodePreorderIterator nodeIter, TreeViewerIterator viewerIter) {
	   if (nodeIter.hasNext()) {
		   Node node = nodeIter.next();
		   
		   if (node.leaf()) {
			   if (viewerIter.hasNext()) {
				   assertTrue(viewerIter.next().getData().equals(node));
			   } else {
				   fail("There is a Goal missing in the TreeViewer.");
			   }
		   } else if (node.parent() != null && node.parent().childrenCount() > 1) {
			   if (viewerIter.hasNext()) {
				   Object itemData = viewerIter.next().getData();
				   if (itemData instanceof BranchFolder) {
					   BranchFolder bf = (BranchFolder) itemData;
					   assertTrue(bf.getChild().equals(node));
				   } else {
					   fail("Next item of the TreeViewer must be a BranchFolder");
				   }
			   } else {
				   fail("There is a BranchFolder missing in the TreeViewer");
			   }
		   }
	   } else {
		   assertFalse("The TreeViewer contains too many proof steps.",viewerIter.hasNext());
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