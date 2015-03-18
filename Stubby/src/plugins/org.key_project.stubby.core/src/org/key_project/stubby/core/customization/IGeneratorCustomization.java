package org.key_project.stubby.core.customization;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaProject;
import org.key_project.stubby.core.util.StubGeneratorUtil;

/**
 * Instances of this class can be used by {@link StubGeneratorUtil} to
 * customize the generation process.
 * @author Martin Hentschel
 */
public interface IGeneratorCustomization {
   /**
    * Is called by {@link StubGeneratorUtil#generateStubs(IJavaProject, String, org.eclipse.core.runtime.IProgressMonitor, IGeneratorCustomization...)}
    * when stub generation has finished.
    * @param javaProject The {@link IJavaProject} to generate stubs for.
    * @param stubFolderPath The path to the stub folder.
    * @throws CoreException Occurred Exception.
    */
   public void stubFilesGenerated(IJavaProject javaProject, String stubFolderPath) throws CoreException;
}
