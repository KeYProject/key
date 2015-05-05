package org.key_project.stubby.core.customization;

import java.util.List;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.key_project.stubby.core.jdt.DependencyAnalyzer;
import org.key_project.stubby.core.util.StubGeneratorUtil;
import org.key_project.stubby.model.dependencymodel.DependencyModel;
import org.key_project.stubby.model.dependencymodel.Type;

/**
 * Instances of this class can be used by {@link StubGeneratorUtil} to
 * customize the generation process.
 * @author Martin Hentschel
 */
public interface IGeneratorCustomization {
   /**
    * Is called by {@link StubGeneratorUtil#createDependencyModel(IJavaProject, org.eclipse.core.runtime.IProgressMonitor, IGeneratorCustomization...)}
    * to optionally define the {@link IJavaElement}s of interest.
    * @param javaProject The {@link IJavaProject} to generate stubs for.
    * @return The {@link IJavaElement}s of interest or {@code null} to consider all.
    * @throws CoreException Occurred Exception.
    */
   public List<? extends IJavaElement> defineSources(IJavaProject javaProject) throws CoreException;
   
   /**
    * Is called by {@link StubGeneratorUtil#createDependencyModel(IJavaProject, org.eclipse.core.runtime.IProgressMonitor, IGeneratorCustomization...)}
    * before the {@link DependencyModel} is created to add additional content to the {@link DependencyAnalyzer}.
    * @param javaProject The {@link IJavaProject} to generate stubs for.
    * @param analyzer The {@link DependencyAnalyzer} which might be extended.
    * @throws CoreException Occurred Exception.
    */
   public void addAdditionalContent(IJavaProject javaProject, 
                                    DependencyAnalyzer analyzer) throws CoreException;
   
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
    * Returns the reason why the given {@link Type} should be ignored.
    * @param javaProject The {@link IJavaProject} to generate stubs for.
    * @param stubFolderPath The path to the stub folder.
    * @param Type The {@link Type} to check.
    * @return The reason why the given {@link Type} should be ignored or {@code null} if not be ignored.
    * @throws CoreException Occurred Exception.
    */
   public String getIgnoreReason(IJavaProject javaProject, 
                                 String stubFolderPath, 
                                 Type Type) throws CoreException;

   /**
    * Checks if generics are supported or not.
    * @param javaProject The {@link IJavaProject} to generate stubs for.
    * @param dependencyModel The created {@link DependencyModel}.
    * @return {@code true} generics are supported, {@code false} generics are not supported.
    */
   public boolean canSupportGenerics(IJavaProject javaProject, DependencyModel dependencyModel);
   
   /**
    * Is called by {@link StubGeneratorUtil#generateStubs(IJavaProject, String, org.eclipse.core.runtime.IProgressMonitor, IGeneratorCustomization...)}
    * when stub generation has finished.
    * @param javaProject The {@link IJavaProject} to generate stubs for.
    * @param stubFolderPath The path to the stub folder.
    * @throws CoreException Occurred Exception.
    */
   public void stubFilesGenerated(IJavaProject javaProject, String stubFolderPath) throws CoreException;
}
