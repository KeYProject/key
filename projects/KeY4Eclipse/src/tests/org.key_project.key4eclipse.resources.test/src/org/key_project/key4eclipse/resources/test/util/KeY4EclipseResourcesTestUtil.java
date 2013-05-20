package org.key_project.key4eclipse.resources.test.util;

import static org.junit.Assert.assertTrue;

import java.io.File;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.ICommand;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.IWorkspaceDescription;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.jdt.core.IJavaProject;
import org.key_project.key4eclipse.resources.builder.KeYProjectBuilder;
import org.key_project.key4eclipse.resources.marker.MarkerManager;
import org.key_project.key4eclipse.resources.nature.KeYProjectNature;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.proof.ProblemLoaderException;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

public class KeY4EclipseResourcesTestUtil {

   public static IJavaProject createKeYProject(String name) throws CoreException, InterruptedException{
      IJavaProject javaProject = TestUtilsUtil.createJavaProject(name);
      IProject project = javaProject.getProject();
      IProjectDescription description = project.getDescription();
      //Add KeYNature
      String[] natures = description.getNatureIds();
      String[] newNatures = new String[natures.length + 1];
      System.arraycopy(natures, 0, newNatures, 0, natures.length);
      newNatures[natures.length] = KeYProjectNature.NATURE_ID;
      description.setNatureIds(newNatures);
      project.setDescription(description, null);
      assertTrue(hasNature(KeYProjectNature.NATURE_ID, javaProject.getProject()) && hasBuilder(KeYProjectBuilder.BUILDER_ID, javaProject.getProject()));
      return javaProject;
   }
   
   public static boolean hasNature(String natureId, IProject project) throws CoreException{
      IProjectDescription description = project.getDescription();
      return ArrayUtil.contains(description.getNatureIds(), natureId);
   }
   
   public static boolean hasBuilder(String builderId, IProject project) throws CoreException{
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
   
   public static void enableAutoBuild(boolean enable) throws CoreException{
      IWorkspace workspace = ResourcesPlugin.getWorkspace();
      IWorkspaceDescription desc = workspace.getDescription();
      if(desc.isAutoBuilding() != enable){
         desc.setAutoBuilding(enable);
         workspace.setDescription(desc);
      }
   }
   
   public static void build(IProject project) throws CoreException{
      project.build(IncrementalProjectBuilder.INCREMENTAL_BUILD, null);
      TestUtilsUtil.waitForBuild();
   }
   
   public static Proof loadProofFile(File file, IProject project) throws CoreException, ProblemLoaderException{
      
      final File location = ResourceUtil.getLocation(project);
      final File bootClassPath = KeYResourceProperties.getKeYBootClassPathLocation(project);
      final List<File> classPaths = KeYResourceProperties.getKeYClassPathEntries(project);
      KeYEnvironment<CustomConsoleUserInterface> environment = KeYEnvironment.load(location, classPaths, bootClassPath);
      environment = KeYEnvironment.load(file, null, null);
      return environment.getLoadedProof();
   }
   
   
   public static IFolder getProofFolder(IProject project){
      IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      IPath proofFolderPath = project.getFullPath().append("Proofs");
      return root.getFolder(proofFolderPath);
   }
   
   public static boolean hasKeYMarkerClosed(IResource res) throws CoreException{
      LinkedList<IMarker> markerList = getKeYMarkerClosed(res);
      return (markerList.isEmpty() ? false : true);  
   }
   
   public static boolean hasKeYMarkerNotClosed(IResource res) throws CoreException{
      LinkedList<IMarker> markerList = getKeYMarkerNotClosed(res);
      return (markerList.isEmpty() ? false : true);  
   }
   
   public static boolean hasKeYMarker(IResource res) throws CoreException{
      return hasKeYMarkerClosed(res) || hasKeYMarkerNotClosed(res);
   }
   
   public static LinkedList<IMarker> getKeYMarkerClosed(IResource res) throws CoreException{
      LinkedList<IMarker> markerList = new LinkedList<IMarker>();
      IMarker[] markers = res.findMarkers(MarkerManager.CLOSEDMARKER_ID, true, IResource.DEPTH_INFINITE);
      for(IMarker marker : markers){
         markerList.add(marker);
      }
      return markerList;
   }
   
   public static LinkedList<IMarker> getKeYMarkerNotClosed(IResource res) throws CoreException{
      LinkedList<IMarker> markerList = new LinkedList<IMarker>();
      IMarker[] markers = res.findMarkers(MarkerManager.NOTCLOSEDMARKER_ID, true, IResource.DEPTH_INFINITE);
      for(IMarker marker : markers){
         markerList.add(marker);
      }
      return markerList;
   }
   
   public static LinkedList<IMarker> getAllKeYMarker(IResource res) throws CoreException{
      LinkedList<IMarker> allMarkerList = getKeYMarkerClosed(res);
      allMarkerList.addAll(getKeYMarkerNotClosed(res));
      return allMarkerList;
   }
}
