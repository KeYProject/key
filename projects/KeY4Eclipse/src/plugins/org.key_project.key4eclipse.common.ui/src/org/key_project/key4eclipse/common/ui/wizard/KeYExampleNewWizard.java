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

package org.key_project.key4eclipse.common.ui.wizard;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.ui.wizards.NewJavaProjectWizardPageOne;
import org.eclipse.jface.wizard.IWizardPage;
import org.key_project.key4eclipse.common.ui.wizard.page.KeYExampleWizardPage;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.eclipse.ResourceUtil.IFileOpener;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.gui.ExampleChooser;
import de.uka.ilkd.key.gui.ExampleChooser.Example;

/**
 * The "KeY Example" wizard used to create new Java Projects with example
 * content provided by the KeY project.
 * @author Martin Hentschel
 */
public class KeYExampleNewWizard extends AbstractNewJavaExampleProjectWizard {
   /**
    * {@code true} add only {@link File}s specified by the {@link Example} to the created Java project.
    * {@code false} to add all files in the example directory {@link Example#getDescription()} to the created Java project.
    */
   public static final boolean ONLY_SPECIFIED_EXAMPLE_CONTENT = false;
   
   /**
    * The used {@link KeYExampleWizardPage} in which the user selects one example.
    */
   private KeYExampleWizardPage examplePage;

   /**
    * {@inheritDoc}
    */
   @Override
   protected String getExampleName() {
      return "KeY Example";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void addPages() {
      examplePage = new KeYExampleWizardPage("examplePage");
      addPage(examplePage);
      super.addPages();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IWizardPage getNextPage(IWizardPage page) {
      // Compute next page
      IWizardPage nextPage = super.getNextPage(page);
      // Update project name if required
      ExampleChooser.Example example = examplePage.getSelectedExample();
      if (example != null) {
         if (nextPage instanceof NewJavaProjectWizardPageOne) {
            NewJavaProjectWizardPageOne one = (NewJavaProjectWizardPageOne)nextPage;
            one.setProjectName(example.toString());
         }
      }
      // Return next page
      return nextPage;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canFinish() {
      return super.canFinish() && !examplePage.isCurrentPage();
   }

   /**
    * {@inheritDoc}
    */
   @SuppressWarnings("restriction")
   @Override
   protected boolean createExampleContent(IContainer sourceDirectory) throws Exception {
      // List example content
      final ExampleChooser.Example example = examplePage.getSelectedExample();
      final File exampleDirectory = example.getDirectory();
      final File[] exampleContent;
      if (ONLY_SPECIFIED_EXAMPLE_CONTENT) {
         final List<File> exampleContentList = new LinkedList<File>(example.getAdditionalFiles());
         exampleContentList.addAll(example.getExportFiles());
         if (IOUtil.exists(example.getObligationFile())) {
            exampleContentList.add(example.getObligationFile());
         }
         if (IOUtil.exists(example.getExampleFile())) {
            exampleContentList.add(example.getExampleFile());
         }
         if (IOUtil.exists(example.getProofFile())) {
            exampleContentList.add(example.getProofFile());
         }
         exampleContent = exampleContentList.toArray(new File[exampleContentList.size()]);
      }
      else {
         exampleContent = exampleDirectory.listFiles();
      }
      final boolean descriptionAvailable = !StringUtil.isTrimmedEmpty(example.getDescription());
      // Separate between source and project content
      List<File> projectContent = new LinkedList<File>();
      List<File> sourceContent = new LinkedList<File>();
      Set<String> oldNames = new HashSet<String>();
      File sourceSubDirectory = null;
      // Separate between source and project content
      for (File content : exampleContent) {
         // List java files
         List<File> javaFiles = IOUtil.search(content, new IFilter<File>() {
            @Override
            public boolean select(File file) {
               String extension = IOUtil.getFileExtension(file);
               return "java".equals(StringUtil.toLowerCase(extension));
            }
         });
         // Check if java files are available
         if (javaFiles.isEmpty()) {
            // No java files, add to project
            if (!descriptionAvailable || !example.getExampleFile().equals(content)) { // Do not add example definition file if description is available because only its description will be added later.
               projectContent.add(content);
            }
         }
         else {
            // Get package definition
            File javaFile = javaFiles.get(0);
            File firstJavaFile = javaFile;
            String packageDefinition = extractPackage(firstJavaFile);
            // Find source root folder which contains the source files
            File firstFolder = firstJavaFile.getParentFile();
            if (packageDefinition != null) {
               String[] packages = packageDefinition.split("\\.");
               for (int i = packages.length - 1; i >= 0; i--) {
                  Assert.isTrue(ObjectUtil.equals(firstFolder.getName(), packages[i]), "Package \"" + packages[i] + "\" is not in a folder with this name.");
                  firstFolder = firstFolder.getParentFile();
               }
               Assert.isTrue(sourceSubDirectory == null | firstFolder.equals(sourceSubDirectory), "Different source folders '" + sourceSubDirectory + "' and '" + firstFolder + "' are not supported.");
               sourceSubDirectory = firstFolder;
            }
            else {
               File newSourceSubDirectory = javaFile.getParentFile();
               Assert.isTrue(sourceSubDirectory == null | newSourceSubDirectory.equals(sourceSubDirectory), "Different source folders '" + sourceSubDirectory + "' and '" + newSourceSubDirectory + "' are not supported.");
               sourceSubDirectory = newSourceSubDirectory;
            }
            // Make sure that no additional folders exist and source root folder content is stored in projects source folder
            if (exampleDirectory.equals(firstFolder)) {
               // Java file is contained in example root folder
               sourceContent.add(content);
            }
            else {
               // Remove additional folder
               File parent = firstFolder;
               if (!ONLY_SPECIFIED_EXAMPLE_CONTENT) {
                  Assert.isTrue(exampleDirectory.equals(parent.getParentFile()), "Additional deep source folder structures are not supported.");
               }
               // Add source content
               CollectionUtil.addAll(sourceContent, parent.listFiles());
               oldNames.add(firstFolder.getName());
            }
         }
      }
      // Copy example content into new created Java Project and its source directory
      KeYFileOpener opener = new KeYFileOpener(sourceDirectory, oldNames);
      IProject project = sourceDirectory.getProject();
      if (ONLY_SPECIFIED_EXAMPLE_CONTENT) {
         ResourceUtil.copyIntoWorkspace(sourceDirectory, opener, sourceSubDirectory != null ? sourceSubDirectory : exampleDirectory, sourceContent);
      }
      else {
         ResourceUtil.copyIntoWorkspace(sourceDirectory, opener, null, sourceContent);
      }
      ResourceUtil.copyIntoWorkspace(project, opener, exampleDirectory, projectContent);
      // Create example definition file only with its description
      if (descriptionAvailable) { // Otherwise the README file is directly copied without any modification
         ResourceUtil.createFile(project.getFile(example.getExampleFile().getName()), new ByteArrayInputStream(example.getDescription().getBytes()), null);
      }
      // Set source sub directory if required
      if (!StringUtil.isTrimmedEmpty(opener.getSourceSubDirectory())) {
         KeYResourceProperties.setSourceClassPath(project, sourceDirectory.getFullPath().append(opener.getSourceSubDirectory()).toString());
      }
      // Select project file
      IFile projectFile = project.getFile(new Path(ExampleChooser.KEY_FILE_NAME));
      if (projectFile.exists()) {
         selectAndReveal(projectFile);
      }
      return true;
   }
   
   private static class KeYFileOpener implements IFileOpener {
      private final IContainer sourceDirectory;
      
      private final Set<String> oldNames;
      
      private String sourceSubDirectory;
      
      public KeYFileOpener(IContainer sourceDirectory, Set<String> oldNames) {
         this.sourceDirectory = sourceDirectory;
         this.oldNames = oldNames;
      }

      @Override
      public InputStream open(File file) throws IOException {
         // Make sure that javaSource is correct in all *.key and *.proof files
         if (KeYUtil.isFileExtensionSupported(IOUtil.getFileExtension(file))) {
            String content = IOUtil.readFrom(file);
            final String JAVA_SOURCE_START = "\\javaSource \"";
            final String JAVA_SOURCE_END = "\";";
            int start = content.indexOf(JAVA_SOURCE_START);
            if (start >= 0) {
               int end = content.indexOf(JAVA_SOURCE_END, start);
               if (end >= 0) {
                  String currentDir = content.substring(start + JAVA_SOURCE_START.length(), end);
                  String newSourceDir = sourceDirectory instanceof IProject ? "." : sourceDirectory.getName();
                  if (oldNames.contains(currentDir)) {
                     content = content.substring(0, start) +
                               JAVA_SOURCE_START +
                               newSourceDir +
                               content.substring(end);
                  }
                  else {
                     sourceSubDirectory = currentDir;
                     content = content.substring(0, start) +
                               JAVA_SOURCE_START +
                               newSourceDir + '/' + currentDir +
                               content.substring(end);
                  }
               }
            }
            return new ByteArrayInputStream(content.getBytes());
         }
         else {
            return new FileInputStream(file);
         }
      }

      public String getSourceSubDirectory() {
         return sourceSubDirectory;
      }
   }

   /**
    * Extracts the package definition from the given java file.
    * @param file The given java file.
    * @return The found package definition or {@code null} if not available.
    * @throws IOException Occurred Exception
    */
   protected String extractPackage(File file) throws IOException {
      String content = IOUtil.readFrom(file);
      int packageStart = content.indexOf("package ");
      if (packageStart >= 0) {
         int packageEnd = content.indexOf(";", packageStart);
         if (packageEnd >= 0) {
            return content.substring(packageStart + "package ".length(), packageEnd);
         }
         else {
            return null;
         }
      }
      else {
         return null;
      }
   }
}