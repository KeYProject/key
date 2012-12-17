package org.key_project.keyide.ui.test.testcase;

import java.io.File;

import junit.framework.TestCase;

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
import org.key_project.keyide.ui.util.TreeViewerIterator;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.symbolic_execution.util.IFilter;
import de.uka.ilkd.key.symbolic_execution.util.JavaUtil;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

public class TreeViewerIteratorTest extends TestCase {
   // TODO Comments
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
      IProgramMethod pm = searchProgramMethod(environment.getServices(), "PayCard", "isValid");
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

   
   
   /**
    * Searches a {@link IProgramMethod} in the given {@link Services}.
    * @param services The {@link Services} to search in.
    * @param containerTypeName The name of the type which contains the method.
    * @param methodFullName The method name to search.
    * @return The first found {@link IProgramMethod} in the type.
    */
   protected static IProgramMethod searchProgramMethod(Services services, 
                                                      String containerTypeName, 
                                                      final String methodFullName) {
      JavaInfo javaInfo = services.getJavaInfo();
      KeYJavaType containerKJT = javaInfo.getTypeByClassName(containerTypeName);
      assertNotNull(containerKJT);
      ImmutableList<IProgramMethod> pms = javaInfo.getAllProgramMethods(containerKJT);
      IProgramMethod pm = JavaUtil.search(pms, new IFilter<IProgramMethod>() {
         @Override
         public boolean select(IProgramMethod element) {
            return methodFullName.equals(element.getFullName());
         }
      });
      assertNotNull(pm);
      return pm;
   }
}
