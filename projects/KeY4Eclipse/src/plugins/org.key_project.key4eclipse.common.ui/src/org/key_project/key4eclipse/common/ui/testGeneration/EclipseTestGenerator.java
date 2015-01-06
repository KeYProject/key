package org.key_project.key4eclipse.common.ui.testGeneration;

import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.StringUtil;
import org.key_project.util.jdt.JDTUtil;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.SolverLauncher;
import de.uka.ilkd.key.smt.testgen.AbstractTestGenerator;
import de.uka.ilkd.key.smt.testgen.TestGenerationLog;
import de.uka.ilkd.key.testgen.TestCaseGenerator;

/**
 * Implementation of {@link AbstractTestGenerator} which stores the generated
 * test cases in a separate {@link IJavaProject}.
 * @author Martin Hentschel
 */
public class EclipseTestGenerator extends AbstractTestGenerator {
   /**
    * Suffix for the {@link IJavaProject} which contains the tests.
    */
   public static final String TEST_PROJECT_SUFFIX = "Tests";

   /**
    * The folder which provides required libraries.
    */
   private static final String LIB_FOLDER_NAME = "libs";

   /**
    * Name of the readme file which explains which libraries are needed.
    */
   private static final String LIB_FOLDER_README_NAME = "Readme.txt";

   /**
    * The {@link IFile} which provides the proof file to generate test cases for.
    */
   private final IFile proofFile;

   /**
    * Constructor.
    * @param proofFile The {@link IFile} which provides the proof file to generate test cases for.
    * @param mediator The {@link KeYMediator} to use.
    * @param originalProof The {@link Proof} to generate test cases for.
    */
   public EclipseTestGenerator(IFile proofFile, 
                               KeYMediator mediator, 
                               Proof originalProof) {
      super(mediator, originalProof);
      this.proofFile = proofFile;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void generateFiles(SolverLauncher launcher, 
                                Collection<SMTSolver> problemSolvers, 
                                TestGenerationLog log, 
                                Proof originalProof) throws Exception {
      final TestCaseGenerator tg = new TestCaseGenerator(originalProof);
      tg.setJUnit(true);
      tg.setLogger(log);
      // Create test project
      IProject sourceProject = proofFile.getProject();
      IJavaProject testProject = JDTUtil.createJavaProject(sourceProject.getName() + TEST_PROJECT_SUFFIX, sourceProject);
      List<IPackageFragmentRoot> sourceResources = JDTUtil.getSourcePackageFragmentRoots(testProject);
      IContainer sourceContainer = findFirstSourceContainer(sourceResources);
      if (sourceContainer == null) {
         throw new IllegalStateException("The Java project '" + testProject.getProject().getName() + "' has no source folder.");
      }
      // Create library folder
      IFolder libFolder = ResourceUtil.createFolder(testProject.getProject(), LIB_FOLDER_NAME);
      IFile readmeFile = libFolder.getFile(LIB_FOLDER_README_NAME);
      ResourceUtil.createFile(readmeFile, createLibFolderReadmeContent(), null);
      // Create RFL file
      StringBuffer rflSb = tg.createRFLFileConent();
      IFile rflFile = sourceContainer.getFile(new Path("RFL.java"));
      ResourceUtil.createFile(rflFile, new ByteArrayInputStream(rflSb.toString().getBytes()), null);
      // Create test file
      IFile testFile = sourceContainer.getFile(new Path("Test.java"));
      StringBuffer testSb = tg.createTestCaseCotent(problemSolvers);
      ResourceUtil.createFile(testFile, new ByteArrayInputStream(testSb.toString().getBytes()), null);
   }

   /**
    * Returns the first fund {@link IContainer} of a source location.
    * @param sourceResources The available source {@link IPackageFragmentRoot}s.
    * @return The first found {@link IContainer} or {@code null} if no one was found.
    */
   protected IContainer findFirstSourceContainer(List<IPackageFragmentRoot> sourceResources) {
      IContainer result = null;
      Iterator<IPackageFragmentRoot> iter = sourceResources.iterator();
      while (result == null && iter.hasNext()) {
         IPackageFragmentRoot root = iter.next();
         IResource resource = root.getResource();
         if (resource instanceof IContainer) {
            result = (IContainer) resource;
         }
      }
      return result;
   }

   /**
    * Creates the readme content.
    * @return The readme content.
    */
   protected InputStream createLibFolderReadmeContent() {
      String text = "Add the following libraries to the Java Build Path of this project: " + StringUtil.NEW_LINE +
                    "- Objenesis 2.1" + StringUtil.NEW_LINE +
                    "  http://objenesis.org/download.html" + StringUtil.NEW_LINE +
                    "- JUnit 4.9" + StringUtil.NEW_LINE +
                    "  http://junit.org";
      return new ByteArrayInputStream(text.getBytes());
   }
}
