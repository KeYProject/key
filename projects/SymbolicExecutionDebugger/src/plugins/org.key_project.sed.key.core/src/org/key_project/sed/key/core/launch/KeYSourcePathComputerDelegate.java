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

package org.key_project.sed.key.core.launch;

import java.io.File;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.sourcelookup.ISourceContainer;
import org.eclipse.debug.core.sourcelookup.ISourcePathComputerDelegate;
import org.eclipse.debug.core.sourcelookup.containers.ArchiveSourceContainer;
import org.eclipse.debug.core.sourcelookup.containers.DirectorySourceContainer;
import org.eclipse.debug.core.sourcelookup.containers.ExternalArchiveSourceContainer;
import org.eclipse.debug.core.sourcelookup.containers.FolderSourceContainer;
import org.eclipse.debug.core.sourcelookup.containers.ProjectSourceContainer;
import org.eclipse.debug.core.sourcelookup.containers.WorkspaceSourceContainer;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.launching.sourcelookup.containers.JavaProjectSourceContainer;
import org.key_project.key4eclipse.starter.core.property.KeYClassPathEntry;
import org.key_project.key4eclipse.starter.core.property.KeYClassPathEntry.KeYClassPathEntryKind;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties.UseBootClassPathKind;
import org.key_project.sed.key.core.util.KeySEDUtil;
import org.key_project.sed.key.core.util.LogUtil;

/**
 * {@link ISourcePathComputerDelegate} for the Symbolic Execution Debugger
 * based on KeY. It returns just the whole workspace.
 * @author Martin Hentschel
 */
public class KeYSourcePathComputerDelegate implements ISourcePathComputerDelegate {
    /**
     * {@inheritDoc}
     */
    @Override
    public ISourceContainer[] computeSourceContainers(ILaunchConfiguration configuration, IProgressMonitor monitor) throws CoreException {
        IMethod method = KeySEDUtil.findMethod(configuration);
        if (method != null) {
           List<ISourceContainer> result = new LinkedList<ISourceContainer>();
           IProject project = method.getResource().getProject();
           // Add KeY boot class path if defined.
           UseBootClassPathKind kind = KeYResourceProperties.getUseBootClassPathKind(project);
           if (UseBootClassPathKind.WORKSPACE.equals(kind)) {
              String path = KeYResourceProperties.getBootClassPath(project);
              IResource resource = ResourcesPlugin.getWorkspace().getRoot().findMember(new Path(path));
              result.add(createSourceContainer(resource));
           }
           else if (UseBootClassPathKind.EXTERNAL_IN_FILE_SYSTEM.equals(kind)) {
              String path = KeYResourceProperties.getBootClassPath(project);
              File file = new File(path);
              result.add(createSourceContainer(file));
           }
           // Add class path entries
           List<KeYClassPathEntry> entries = KeYResourceProperties.getClassPathEntries(project);
           for (KeYClassPathEntry entry : entries) {
              if (KeYClassPathEntryKind.WORKSPACE.equals(entry.getKind())) {
                 IResource resource = entry.getResource();
                 result.add(createSourceContainer(resource));
              }
              else if (KeYClassPathEntryKind.EXTERNAL_IN_FILE_SYSTEM.equals(entry.getKind())) {
                 File file = entry.getLocation();
                 result.add(createSourceContainer(file));
              }
           }
           // Add source project, functionality was adapted from JavaSourceLookupUtil
           IJavaProject javaProject = method.getJavaProject();
           if (javaProject.exists()) {
              result.add(new JavaProjectSourceContainer(javaProject));
           }
           else {
              result.add(new ProjectSourceContainer(project, false));
           }
           return result.toArray(new ISourceContainer[result.size()]);
        }
        else {
           return new ISourceContainer[] {new WorkspaceSourceContainer()};
        }
    }
    
   /**
     * Creates an {@link ISourceContainer} for the given {@link File}.
     * @param resource The {@link File} for that an {@link ISourceContainer} is needed.
     * @return The created {@link ISourceContainer}.
     * @throws CoreException Occurred Exception if the given {@link File} is invalid.
     */
    protected ISourceContainer createSourceContainer(File file) throws CoreException {
       if (file != null) {
          if (file.isFile()) {
             return new ExternalArchiveSourceContainer(file.getAbsolutePath(), false);
          }
          else {
             return new DirectorySourceContainer(file, false);
          }
       }
       else {
          throw new CoreException(LogUtil.getLogger().createErrorStatus("File is not defined."));
       }
    }
    
    /**
     * Creates an {@link ISourceContainer} for the given {@link IResource}.
     * @param resource The {@link IResource} for that an {@link ISourceContainer} is needed.
     * @return The created {@link ISourceContainer}.
     * @throws CoreException Occurred Exception if the given {@link IResource} is invalid.
     */
    protected ISourceContainer createSourceContainer(IResource resource) throws CoreException {
       if (resource instanceof IFile) {
          return new ArchiveSourceContainer((IFile)resource, false);
       }
       else if (resource instanceof IProject) {
          return new ProjectSourceContainer((IProject)resource, false);
       }
       else if (resource instanceof IContainer) {
          return new FolderSourceContainer((IContainer)resource, false);
       }
       else {
          throw new CoreException(LogUtil.getLogger().createErrorStatus("Not supported resource \"" + resource + "\"."));
       }
    }
}