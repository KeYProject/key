package org.key_project.key4eclipse.common.ui.stubby;

import java.util.List;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaProject;
import org.key_project.key4eclipse.starter.core.property.KeYClassPathEntry;
import org.key_project.key4eclipse.starter.core.property.KeYClassPathEntry.KeYClassPathEntryKind;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.stubby.core.customization.IGeneratorCustomization;

/**
 * {@link IGeneratorCustomization} for KeY.
 * @author Martin Hentschel
 */
public class KeYGeneratorCustomization implements IGeneratorCustomization {
   /**
    * Is stub folder part of class path?
    */
   private final boolean classPath;
   
   /**
    * Constructor.
    * @param classPath Is stub folder part of class path?
    */
   public KeYGeneratorCustomization(boolean classPath) {
      this.classPath = classPath;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void stubFilesGenerated(IJavaProject javaProject, String stubFolderPath) throws CoreException {
      IProject project = javaProject.getProject();
      final String fullPath = KeYStubGenerationCustomization.computeFullPath(project, stubFolderPath);
      // Ensure that class path is correct according to KeYGeneratorCustomization#classPath.
      List<KeYClassPathEntry> entries = KeYResourceProperties.getClassPathEntries(project);
      KeYClassPathEntry entry = KeYResourceProperties.searchClassPathEntry(entries, KeYClassPathEntryKind.WORKSPACE, fullPath);
      if (classPath) {
         if (entry == null) {
            entry = new KeYClassPathEntry(KeYClassPathEntryKind.WORKSPACE, fullPath);
            entries.add(entry);
            KeYResourceProperties.setClassPathEntries(project, entries);
         }
      }
      else {
         if (entry != null) {
            entries.remove(entry);
            KeYResourceProperties.setClassPathEntries(project, entries);
         }
      }
   }
}
