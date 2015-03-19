package org.key_project.stubby.core.customization;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaProject;
import org.key_project.stubby.core.util.StubGeneratorUtil;
import org.key_project.stubby.model.dependencymodel.AbstractType;
import org.key_project.stubby.model.dependencymodel.DependencyModel;

/**
 * Instances of this class can be used by {@link StubGeneratorUtil} to
 * customize the generation process.
 * @author Martin Hentschel
 */
public interface IGeneratorCustomization {
   /**
    * Is called by {@link StubGeneratorUtil#generateStubs(IJavaProject, String, org.eclipse.core.runtime.IProgressMonitor, IGeneratorCustomization...)}
    * after the {@link DependencyModel} has been created.
    * @param javaProject The {@link IJavaProject} to generate stubs for.
    * @param stubFolderPath The path to the stub folder.
    * @param dependencyModel The created {@link DependencyModel}.
    * @throws CoreException Occurred Exception.
    */
   public void dependencyModelCreated(IJavaProject javaProject, 
                                      String stubFolderPath, 
                                      DependencyModel dependencyModel) throws CoreException;

   /**
    * Is called by {@link StubGeneratorUtil#generateStubs(IJavaProject, String, org.eclipse.core.runtime.IProgressMonitor, IGeneratorCustomization...)}
    * if the stub folder was newly created.
    * @param stubFolder The created {@link IFolder}.
    * @throws CoreException Occurred Exception.
    */
   public void stubFolderCreated(IFolder stubFolder) throws CoreException;

   /**
    * Returns the reason why the given {@link AbstractType} should be ignored.
    * @param javaProject The {@link IJavaProject} to generate stubs for.
    * @param stubFolderPath The path to the stub folder.
    * @param abstractType The {@link AbstractType} to check.
    * @return The reason why the given {@link AbstractType} should be ignored or {@code null} if not be ignored.
    * @throws CoreException Occurred Exception.
    */
   public String getIgnoreReason(IJavaProject javaProject, 
                                 String stubFolderPath, 
                                 AbstractType abstractType) throws CoreException;
   
   /**
    * Is called by {@link StubGeneratorUtil#generateStubs(IJavaProject, String, org.eclipse.core.runtime.IProgressMonitor, IGeneratorCustomization...)}
    * when stub generation has finished.
    * @param javaProject The {@link IJavaProject} to generate stubs for.
    * @param stubFolderPath The path to the stub folder.
    * @throws CoreException Occurred Exception.
    */
   public void stubFilesGenerated(IJavaProject javaProject, String stubFolderPath) throws CoreException;
}
