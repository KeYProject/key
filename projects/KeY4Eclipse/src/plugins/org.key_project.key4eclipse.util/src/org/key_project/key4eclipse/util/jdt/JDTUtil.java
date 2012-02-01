/*******************************************************************************
 * Copyright (c) 2011 Martin Hentschel.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Martin Hentschel - initial API and implementation
 *******************************************************************************/

package org.key_project.key4eclipse.util.jdt;

import java.io.File;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Assert;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageDeclaration;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.ui.JavaElementLabels;
import org.key_project.key4eclipse.util.eclipse.ResourceUtil;
import org.key_project.key4eclipse.util.java.ArrayUtil;
import org.key_project.key4eclipse.util.java.ObjectUtil;

/**
 * Provides static methods to work with JDT.
 * @author Martin Hentschel
 */
public class JDTUtil {
   /**
    * Forbid instances by this private constructor.
    */
   private JDTUtil() {
   }
   
   /**
    * Returns a human readable text label for the given {@link IJavaElement}.
    * @param element The {@link IJavaElement} to convert,
    * @return The human readable text label. An empty {@link String} is returned if the given {@link IJavaElement} is {@code null}.
    */
   public static String getTextLabel(IJavaElement element) {
       return JavaElementLabels.getTextLabel(element, JavaElementLabels.ALL_DEFAULT);
   }
   
   /**
    * Returns the first {@link IJavaElement} from the given once that
    * has the given text label.
    * @param elements The {@link IJavaElement}s to search in.
    * @param textLabel The text label for that the {@link IJavaElement} is needed.
    * @return The first found {@link IJavaElement} or {@code null} if no one was found.
    */
   public static IJavaElement getElementForTextLabel(IJavaElement[] elements, String textLabel) {
       IJavaElement result = null;
       if (elements != null) {
           int i = 0;
           while (result == null && i < elements.length) {
               if (ObjectUtil.equals(textLabel, getTextLabel(elements[i]))) {
                   result = elements[i];
               }
               i++;
           }
       }
       return result;
   }
   
   /**
    * Adds the given {@link IClasspathEntry} to the {@link IJavaProject}.
    * @param javaProject The {@link IJavaProject} to add to.
    * @param entryToAdd The {@link IClasspathEntry} to add.
    * @throws JavaModelException Occurred Exception.
    */
   public static void addClasspathEntry(IJavaProject javaProject,
                                        IClasspathEntry entryToAdd) throws JavaModelException {
       if (javaProject != null && entryToAdd != null) {
           IClasspathEntry[] newEntries = ArrayUtil.add(javaProject.getRawClasspath(), entryToAdd);
           javaProject.setRawClasspath(newEntries, null);
       }
   }
   
   /**
    * Returns all {@link IJavaProject}s.
    * @return All {@link IJavaProject}s.
    * @throws JavaModelException
    */
   public static IJavaProject[] getAllJavaProjects() throws JavaModelException {
      return JavaCore.create(ResourcesPlugin.getWorkspace().getRoot()).getJavaProjects();
   }

   /**
    * Returns all available packages.
    * @return All packages.
    * @throws JavaModelException Occurred Exception.
    */
   public static IJavaElement[] getAllPackageFragmentRoot() throws JavaModelException {
      IJavaProject[] jProjects = getAllJavaProjects();
      Set<IJavaElement> packages = new HashSet<IJavaElement>();
      for (IJavaProject jProject : jProjects) {
         IPackageFragmentRoot[] froots = jProject.getAllPackageFragmentRoots();
         for (IPackageFragmentRoot froot : froots) {
            if (froot != null && froot.exists() && !froot.isReadOnly()) {
               IJavaElement[] children = froot.getChildren();
               for (IJavaElement element : children) {
                  packages.add(element);
               }
            }
         }
      }
      return packages.toArray(new IJavaElement[packages.size()]);
   }
   
   /**
    * Returns the package that contains the {@link IJavaElement}.
    * @param element The {@link IJavaElement}.
    * @return The package that contains the given {@link IJavaElement}.
    */
   public static IJavaElement getPackage(IJavaElement element) {
      if (element != null) {
         if (element instanceof IPackageDeclaration) {
            return element;
         }
         else if (element instanceof IPackageFragment) {
            return element;
         }
         else if (element instanceof IPackageFragmentRoot) {
            return element;
         }
         else {
            return getPackage(element.getParent());
         }
      }
      else {
         return null;
      }
   }
   
   /**
    * <p>
    * Returns the {@link IJavaProject} for the given {@link IProject}.
    * </p>
    * <p>
    * <b>Attention:</b> It is also an {@link IJavaProject} returned even
    * if the {@link IProject} is no Java project (has no JDT nature).
    * To verify if an {@link IProject} is a real Java project use
    * {@link JDTUtil#isJavaProject(IProject)}.
    * </p>
    * @param project The {@link IProject} for that an {@link IJavaProject} is needed.
    * @return The {@link IJavaProject} representation of the {@link IProject} or {@code null} if the given {@link IProject} is {@code null}.
    */
   public static IJavaProject getJavaProject(IProject project) {
       return JavaCore.create(project);
   }

   /**
    * <p>
    * Returns the {@link IJavaProject} for the given {@link IProject}.
    * </p>
    * <p>
    * <b>Attention:</b> It is also an {@link IJavaProject} returned even
    * if the {@link IProject} is no Java project (has no JDT nature).
    * To verify if an {@link IProject} is a real Java project use
    * {@link JDTUtil#isJavaProject(IProject)}.
    * </p>
    * @param projectName The name of the {@link IProject} for that an {@link IJavaProject} is needed.
    * @return The {@link IJavaProject} representation of the {@link IProject} with the given name or {@code null} if the given project name is {@code null}/empty.
    */
   public static IJavaProject getJavaProject(String projectName) {
       IProject project = ResourceUtil.getProject(projectName);
       return getJavaProject(project);
   }
   
   /**
    * Checks if the given {@link IProject} is a Java project.
    * @param project The {@link IProject} to check.
    * @return {@code true} is Java project, {@code false} is no Java project.
    */
   public static boolean isJavaProject(IProject project) {
       if (project != null) {
           IJavaProject javaProject = getJavaProject(project);
           return javaProject != null && javaProject.exists();
       }
       else {
           return false;
       }
   }
   
   /**
    * Returns the locations in the local file system of all used
    * source entries in the java build path of the given project.
    * @param project The given Project.
    * @return The found source locations in the file system.
    * @throws JavaModelException Occurred Exception.
    */
   public static List<File> getSourceLocations(IProject project) throws JavaModelException {
       return getSourceLocations(project, new HashSet<IProject>());
   }
   
   /**
    * Internal helper method that is used in {@link #getSourceLocations(IProject)}
    * to compute the source path. It is required to solve cycles in project dependencies.
    * @param project The given Project.
    * @param alreadyHandledProjects The already handled {@link IProject} that don't need to be analysed again.
    * @return The found source locations in the file system.
    * @throws JavaModelException Occurred Exception.
    */    
   private static List<File> getSourceLocations(IProject project, Set<IProject> alreadyHandledProjects) throws JavaModelException {
       List<File> result = new LinkedList<File>();
       if (project != null) {
           Assert.isNotNull(alreadyHandledProjects);
           alreadyHandledProjects.add(project);
           IJavaProject javaProject = getJavaProject(project);
           if (javaProject != null && javaProject.exists()) {
               IClasspathEntry[] entries = javaProject.getRawClasspath();
               for (IClasspathEntry entry : entries) {
                   if (entry.getContentKind() == IPackageFragmentRoot.K_SOURCE) {
                       List<File> location = getLocationFor(javaProject, entry, IPackageFragmentRoot.K_SOURCE, alreadyHandledProjects);
                       if (location != null) {
                           result.addAll(location);
                       }
                   }
               }
           }
       }
       return result;
   }
   
   /**
    * Returns the locations of the given {@link IClasspathEntry}.
    * @param javaProject The actual {@link IJavaProject} that provides the {@link IClasspathEntry}.
    * @param entry The given {@link IClasspathEntry}.
    * @param alreadyHandledProjects The already handled {@link IProject} that don't need to be analysed again.
    * @return The found locations.
    * @throws JavaModelException 
    */
   private static List<File> getLocationFor(IJavaProject javaProject, 
                                            IClasspathEntry entry,
                                            int expectedKind,
                                            Set<IProject> alreadyHandledProjects) throws JavaModelException {
       if (entry != null) {
           if (entry.getEntryKind() == IClasspathEntry.CPE_CONTAINER ||
               entry.getEntryKind() == IClasspathEntry.CPE_SOURCE ||
               entry.getEntryKind() == IClasspathEntry.CPE_LIBRARY ||
               entry.getEntryKind() == IClasspathEntry.CPE_VARIABLE) {
               List<File> result = new LinkedList<File>();
               IPackageFragmentRoot[] roots = javaProject.findPackageFragmentRoots(entry);
               for (IPackageFragmentRoot root : roots) {
                   if (root.getKind() == expectedKind) {
                       if (root.getResource() != null) {
                           if (root.getResource().getLocationURI() != null) {
                               result.add(ResourceUtil.getLocation(root.getResource()));
                           }
                       }
                       else if (root.getPath() != null) {
                           File location = new File(root.getPath().toString());
                           if (location.exists()) {
                               result.add(location);
                           }
                       }
                   }
               }
               return result; // Ignore containers
           }
           else if (entry.getEntryKind() == IClasspathEntry.CPE_PROJECT) {
               Assert.isNotNull(entry.getPath());
               IResource project = ResourcesPlugin.getWorkspace().getRoot().findMember(entry.getPath());
               Assert.isTrue(project instanceof IProject);
               if (!alreadyHandledProjects.contains(project)) {
                   return getSourceLocations((IProject)project, alreadyHandledProjects);
               }
               else {
                   return null; // Project was already analyzed, no need to do it again.
               }
           }
           else {
               Assert.isTrue(false, "Unknown content kind \"" + entry.getContentKind() + "\" of class path entry \"" + entry + "\".");
               return null;
           }
       }
       else {
           return null;
       }
   }
}
