package org.key_project.stubby.ui.customization;

import org.eclipse.core.resources.IProject;
import org.eclipse.jdt.core.IJavaProject;

/**
 * Provides a basic implementation of {@link IStubGenerationCustomization}.
 * @author Martin Hentschel
 */
public abstract class AbstractStubGenerationCustomization implements IStubGenerationCustomization {
   /**
    * The {@link IJavaProject} to generate stubs for.
    */
   private IJavaProject javaProject;

   /**
    * {@inheritDoc}
    */
   @Override
   public void init(IJavaProject javaProject) {
      this.javaProject = javaProject;
   }

   /**
    * Returns the {@link IJavaProject} to generate stubs for.
    * @return The {@link IJavaProject} to generate stubs for.
    */
   protected IJavaProject getJavaProject() {
      return javaProject;
   }

   /**
    * Returns the {@link IProject} to generate stubs for.
    * @return The {@link IProject} to generate stubs for.
    */
   protected IProject getProject() {
      return javaProject != null ? javaProject.getProject() : null;
   }
}
