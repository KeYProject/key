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

package org.key_project.key4eclipse.starter.core.property;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.QualifiedName;
import org.eclipse.jdt.core.JavaModelException;
import org.key_project.key4eclipse.starter.core.property.KeYClassPathEntry.KeYClassPathEntryKind;
import org.key_project.key4eclipse.starter.core.util.LogUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.StringUtil;
import org.key_project.util.jdt.JDTUtil;
import org.xml.sax.Attributes;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;

/**
 * Provides static methods to read and set KeY specific project settings.
 * @author Martin Hentschel
 */
public final class KeYResourceProperties {
    /**
     * Property for the use custom boot class path.
     */
    public static final QualifiedName PROP_USE_BOOT_CLASS_PATH = new QualifiedName("org.key_project.key4eclipse.starter", "useBootClassPath");

    /**
     * Property for the source class path.
     */
    public static final QualifiedName PROP_SOURCE_CLASS_PATH = new QualifiedName("org.key_project.key4eclipse.starter", "sourceClassPath");

    /**
     * Property for the custom boot class path.
     */
    public static final QualifiedName PROP_BOOT_CLASS_PATH = new QualifiedName("org.key_project.key4eclipse.starter", "bootClassPath");

    /**
     * Property for the class path entries.
     */
    public static final QualifiedName PROP_CLASS_PATH_ENTRIES = new QualifiedName("org.key_project.key4eclipse.starter", "classPathEntries");
    
    /**
     * Possible kinds of boot class paths.
     * @author Martin Hentschel
     */
    public static enum UseBootClassPathKind {
        /**
         * Use default boot class path from KeY.
         */
        KEY_DEFAULT,
        
        /**
         * Use defined boot class path in workspace.
         */
        WORKSPACE,
        
        /**
         * Use external boot class path.
         */
        EXTERNAL_IN_FILE_SYSTEM
    }
    
    /**
     * Forbid instances.
     */
    private KeYResourceProperties() {
    }
    
    /**
     * Returns the use boot class path entry value.
     * @param project The {@link IProject} to read from.
     * @return The use boot class path entry value.
     * @throws CoreException Occurred Exception.
     */
    public static UseBootClassPathKind getUseBootClassPathKind(IProject project) throws CoreException {
        try {
            return UseBootClassPathKind.valueOf(project.getPersistentProperty(PROP_USE_BOOT_CLASS_PATH));
        }
        catch (Exception e) {
            return UseBootClassPathKind.KEY_DEFAULT;
        }
    }
    
    /**
     * Sets the use boot class path entry.
     * @param project The {@link IProject} to configure.
     * @param kind The value to save.
     * @throws CoreException Occurred Exception.
     */
    public static void setUseBootClassPathKind(IProject project, UseBootClassPathKind kind) throws CoreException {
        if (project != null) {
            project.setPersistentProperty(PROP_USE_BOOT_CLASS_PATH, kind != null ? kind.toString() : null);
        }
    }
    
    /**
     * Returns the boot class path entry value.
     * @param project The {@link IProject} to read from.
     * @return The boot class path entry value.
     * @throws CoreException Occurred Exception.
     */    
    public static String getBootClassPath(IProject project) throws CoreException {
        if (project != null) {
            return project.getPersistentProperty(PROP_BOOT_CLASS_PATH);
        }
        else {
            return null;
        }
    }
    
    /**
     * Sets the boot class path entry.
     * @param project The {@link IProject} to configure.
     * @param bootClassPath The value to save.
     * @throws CoreException Occurred Exception.
     */
    public static void setBootClassPath(IProject project, String bootClassPath) throws CoreException {
        if (project != null) {
            project.setPersistentProperty(PROP_BOOT_CLASS_PATH, bootClassPath);
        }
    }
    
    /**
     * Returns the class path entries.
     * @param project The {@link IProject} to read from.
     * @return The class path entries.
     * @throws CoreException Occurred Exception.
     */
    public static List<KeYClassPathEntry> getClassPathEntries(IProject project) throws CoreException {
        try {
            if (project != null) {
                String xml = project.getPersistentProperty(PROP_CLASS_PATH_ENTRIES);
                final List<KeYClassPathEntry> result = new LinkedList<KeYClassPathEntry>();
                if (!StringUtil.isEmpty(xml)) {
                    SAXParser parser = SAXParserFactory.newInstance().newSAXParser();
                    DefaultHandler handler = new DefaultHandler() {
                        @Override
                        public void startElement(String uri, String localName, String qName, Attributes attributes) throws SAXException {
                            try {
                                if ("entry".equals(qName)) {
                                    String kind = attributes.getValue("kind");
                                    String path = attributes.getValue("path");
                                    if (!StringUtil.isEmpty(kind) && !StringUtil.isEmpty(path)) {
                                        result.add(new KeYClassPathEntry(KeYClassPathEntryKind.valueOf(kind), path));
                                    }
                                }
                            }
                            catch (Exception e) {
                                // Just ignore the entry, nothing to do.
                            }
                        }
                    };
                    parser.parse(new ByteArrayInputStream(xml.getBytes()), handler);
                }
                return result;
            }
            else {
                return null;
            }
        }
        catch (Exception e) {
            return null;
        }
    }
    
    /**
     * Sets the class path entries.
     * @param project The {@link IProject} to configure.
     * @param entries The values to save.
     * @throws CoreException Occurred Exception.
     */
    public static void setClassPathEntries(IProject project, List<KeYClassPathEntry> entries) throws CoreException {
        if (project != null) {
            StringBuffer sb = new StringBuffer();
            sb.append("<?xml version=\"1.0\"?>");
            sb.append("<classPathEntries>");
            if (entries != null) {
                for (KeYClassPathEntry entry : entries) {
                    sb.append("<entry");
                    if (entry.getKind() != null) {
                        sb.append(" kind=\"" + entry.getKind().toString() + "\"");
                    }
                    if (!StringUtil.isEmpty(entry.getPath())) {
                        sb.append(" path=\"" + entry.getPath() + "\"");
                    }
                    sb.append(" />");
                }
            }
            sb.append("</classPathEntries>");
            project.setPersistentProperty(PROP_CLASS_PATH_ENTRIES, sb.toString());
        }
    }
    
    /**
     * Returns the boot class path to use in KeY for the given {@link IProject}.
     * @param project The given {@link IProject}.
     * @return The boot class path to use in KeY.
     * @throws CoreException Occurred Exception.
     */
    public static File getKeYBootClassPathLocation(IProject project) throws CoreException {
        UseBootClassPathKind kind = getUseBootClassPathKind(project);
        if (UseBootClassPathKind.WORKSPACE.equals(kind)) {
            String path = getBootClassPath(project);
            if (!StringUtil.isEmpty(path)) {
                IResource resource = ResourcesPlugin.getWorkspace().getRoot().findMember(new Path(path));
                return ResourceUtil.getLocation(resource);
            }
            else {
                return null;
            }
        }
        else if (UseBootClassPathKind.EXTERNAL_IN_FILE_SYSTEM.equals(kind)) {
            String path = getBootClassPath(project);
            return !StringUtil.isEmpty(path) ? new File(path) : null;
        }
        else {
            return null;
        }
    }
    
    /**
     * Returns the class path entries to use in KeY.
     * @param project The given {@link IProject}.
     * @return The class path entries to use in KeY.
     * @throws CoreException Occurred Exception.
     */
    public static List<File> getKeYClassPathEntries(IProject project) throws CoreException {
        List<KeYClassPathEntry> entries = getClassPathEntries(project);
        if (entries != null) {
            List<File> result = new ArrayList<File>(entries.size());
            for (KeYClassPathEntry entry : entries) {
                File location = entry.getLocation();
                if (location != null) {
                    result.add(location);
                }
            }
            return result;
        }
        else {
            return null;
        }
    }

    /**
     * Returns the source class path location in the local file system of the given {@link IProject}.
     * @param project The {@link IProject}.
     * @return The source class path location in the local file system or {@code null} if not availale.
     * @throws CoreException Occurred Exception.
     */
    public static File getSourceClassPathLocation(IProject project) throws CoreException {
       IResource resource = getSourceClassPathResource(project);
       return ResourceUtil.getLocation(resource);
    }

    /**
     * Returns the source class path of the given {@link IProject} as {@link IResource}.
     * @param project The {@link IProject}.
     * @return The {@link IResource} or {@code null} if not available.
     * @throws CoreException Occurred Exception.
     */
    public static IResource getSourceClassPathResource(IProject project) throws CoreException {
       String path = getSourceClassPath(project);
       if (path != null) {
          return ResourcesPlugin.getWorkspace().getRoot().findMember(path);
       }
       else {
          return null;
       }
    }

    /**
     * Returns the source class path entry value.
     * @param project The {@link IProject} to read from.
     * @return The source class path entry value.
     * @throws CoreException Occurred Exception.
     */    
    public static String getSourceClassPath(IProject project) throws CoreException {
        if (project != null) {
            String value = project.getPersistentProperty(PROP_SOURCE_CLASS_PATH);
            if (value == null) {
               value = getDefaultSourceClassPath(project);
            }
            return value;
        }
        else {
            return null;
        }
    }
    
    /**
     * Sets the source class path entry.
     * @param project The {@link IProject} to configure.
     * @param sourceClassPath The value to save.
     * @throws CoreException Occurred Exception.
     */
    public static void setSourceClassPath(IProject project, String sourceClassPath) throws CoreException {
        if (project != null) {
            project.setPersistentProperty(PROP_SOURCE_CLASS_PATH, sourceClassPath);
        }
    }

   /**
    * Returns the default source path to use in the given {@link IProject}.
    * @param project The {@link IProject}.
    * @return The default source path to use or {@code null} if unknown.
    */
   public static String getDefaultSourceClassPath(IProject project) {
      try {
         if (project != null) {
            if (JDTUtil.isJavaProject(project)) {
               List<IResource> sourcePaths = JDTUtil.getSourceResources(project);
               if (!CollectionUtil.isEmpty(sourcePaths)) {
                  return sourcePaths.get(0).getFullPath().toString();
               }
               else {
                  return null;
               }
            }
            else {
               return null;
            }
         }
         else {
            return null;
         }
      }
      catch (JavaModelException e) {
         LogUtil.getLogger().logError(e);
         return null;
      }
   }
}