package org.key_project.key4eclipse.resources.test.testcase.junit;

import junit.framework.TestCase;

import org.eclipse.core.resources.ICommand;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.IJavaProject;
import org.junit.Test;
import org.key_project.key4eclipse.resources.builder.KeYProjectBuilder;
import org.key_project.key4eclipse.resources.nature.KeYProjectNature;
import org.key_project.key4eclipse.resources.test.Activator;
import org.key_project.key4eclipse.resources.test.util.KeY4EclipseResourceTestUtil;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.test.util.TestUtilsUtil;

public class KeYProjectBuilderTest extends TestCase{
   
   
   @Test
   public void testAddResource() throws CoreException, InterruptedException{
      IJavaProject keyProject = KeY4EclipseResourceTestUtil.createKeYProject("KeYProjectBuilderTest_testAddResource");
      IProject project = keyProject.getProject();
      assertTrue(hasNature(KeYProjectNature.NATURE_ID, project));
      assertTrue(hasBuilder(KeYProjectBuilder.BUILDER_ID, project));
      IFolder src = project.getProject().getFolder("src");
      project.getProject().build(IncrementalProjectBuilder.INCREMENTAL_BUILD, null);
      TestUtilsUtil.waitForBuild();
      IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      IPath pathAdd = project.getFullPath().append("Proofs").append("the").append("add").append("test").append("AddTest.java").append("the.add.test.AddTest[the.add.test.AddTest__add(int,int)].JML operation contract.0.proof");
      IPath pathSub = project.getFullPath().append("Proofs").append("the").append("add").append("test").append("AddTest.java").append("the.add.test.AddTest[the.add.test.AddTest__sub(int,int)].JML operation contract.0.proof");
      IFile proofAdd = root.getFile(pathAdd);
      IFile proofSub = root.getFile(pathSub);
      assertFalse(proofAdd.exists() || proofSub.exists());
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/AddTest", src);
      project.getProject().build(IncrementalProjectBuilder.INCREMENTAL_BUILD, null);
      TestUtilsUtil.waitForBuild();
      
      assertTrue(proofAdd.exists() && proofSub.exists());  
   }
   
   public boolean hasNature(String natureId, IProject project) throws CoreException{
      IProjectDescription description = project.getDescription();
      return ArrayUtil.contains(description.getNatureIds(), natureId);
   }
   
   public boolean hasBuilder(String builderId, IProject project) throws CoreException{
      IProjectDescription description = project.getDescription();
      ICommand keyBuilder = ArrayUtil.search(description.getBuildSpec(), new IFilter<ICommand>() {
         @Override
         public boolean select(ICommand element) {
            return element.getBuilderName().equals(KeYProjectBuilder.BUILDER_ID);
         }
      });
      if(keyBuilder != null){
         return keyBuilder.getBuilderName().equals(builderId);
      }
      else return false;
   }
}
