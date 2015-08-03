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
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.PartInitException;
import org.key_project.key4eclipse.common.ui.util.LogUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.eclipse.swt.dialog.TextFieldMessageDialog;
import org.key_project.util.java.StringUtil;
import org.key_project.util.jdt.JDTUtil;

import de.uka.ilkd.key.control.UserInterfaceControl;
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
   public static final String LIB_FOLDER_NAME = "libs";

   /**
    * Name of the readme file which explains which libraries are needed.
    */
   public static final String LIB_FOLDER_README_NAME = "Readme.txt";

   /**
    * Name of the log folder.
    */
   public static final String LOG_FOLDER_NAME = "log";

   /**
    * Extension of log files.
    */
   public static final String LOG_FILE_EXTENSION_WITH_DOT = ".txt";

   /**
    * The {@link IProject} which provides the source files to generate test cases for.
    */
   private final IProject sourceProject;
   
   /**
    * The name of the test file to generate without file extension.
    */
   private final String testFileName;
   
   /**
    * The name of the files package.
    */
   private final String testFilePackageName;
   
   /**
    * Determines whether the created test file should be opened.
    */
   private final boolean openTestFile;

   /**
    * Constructor.
    * @param sourceProject The {@link IProject} which provides the source files to generate test cases for.
    * @param testFileName The name of the test file to generate without file extension.
    * @param ui The {@link UserInterfaceControl} to use.
    * @param originalProof The {@link Proof} to generate test cases for.
    */
   public EclipseTestGenerator(IProject sourceProject, 
                               String testFileName,
                               UserInterfaceControl ui, 
                               Proof originalProof) {
      super(ui, originalProof);
      this.sourceProject = sourceProject;
      this.testFileName = testFileName;
      this.testFilePackageName = "";
      this.openTestFile = true;
   }
   
   public EclipseTestGenerator(IProject sourceProject, 
                              String testFileName,
                              String testFilePackageName, 
                              UserInterfaceControl ui, 
                              Proof originalProof,
                              boolean openTestFile) {
      super(ui, originalProof);
      this.sourceProject = sourceProject;
      this.testFileName = testFileName;
      this.testFilePackageName = testFilePackageName;
      this.openTestFile = openTestFile;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void informAboutNoTestResults(final SolverLauncher launcher, 
                                           final Collection<SMTSolver> problemSolvers, 
                                           final TestGenerationLog log, 
                                           final Proof originalProof) {
      super.informAboutNoTestResults(launcher, problemSolvers, log, originalProof);
      Display.getDefault().asyncExec(new Runnable() {
         @Override
         public void run() {
            TextFieldMessageDialog.openError(WorkbenchUtil.getActiveShell(), "Test Generation Log", "No tests generated.", log.toString());
         }
      });
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void generateFiles(final SolverLauncher launcher, 
                                final Collection<SMTSolver> problemSolvers, 
                                final TestGenerationLog log, 
                                final Proof originalProof) throws Exception {
      ResourcesPlugin.getWorkspace().run(new IWorkspaceRunnable() {
         @Override
         public void run(IProgressMonitor monitor) throws CoreException {
            try {
               generateEclipseFiles(launcher, problemSolvers, log, originalProof);
            }
            catch (Exception e) {
               LogUtil.getLogger().logError(e);              
               throw new CoreException(LogUtil.getLogger().createErrorStatus(e));
            }
         }
      }, null);
   }

   /**
    * Generates all eclipse files.
    * @param launcher The {@link SolverLauncher}.
    * @param problemSolvers The {@link SMTSolver}s.
    * @param log The {@link TestGenerationLog}.
    * @param originalProof The original {@link Proof}.
    * @throws Exception Occurred Exception.
    */
   protected void generateEclipseFiles(final SolverLauncher launcher, 
                                       final Collection<SMTSolver> problemSolvers, 
                                       final TestGenerationLog log, 
                                       final Proof originalProof) throws Exception {
      // Create test project
      IJavaProject testProject = JDTUtil.createJavaProject(sourceProject.getName() + TEST_PROJECT_SUFFIX, sourceProject);
      List<IPackageFragmentRoot> sourceResources = JDTUtil.getSourcePackageFragmentRoots(testProject);
      IPackageFragmentRoot sourceRoot = findFirstSourceRoot(sourceResources);
      IContainer sourceContainer = sourceRoot == null ? null : (IContainer) sourceRoot.getResource();
      if (sourceRoot == null || sourceContainer == null) {
         throw new IllegalStateException("The Java project '" + testProject.getProject().getName() + "' has no source folder.");
      }
      // Create test generator
      originalProof.getProofIndependentSettings().getTestGenerationSettings().setRFL(true);
      originalProof.getProofIndependentSettings().getTestGenerationSettings().setUseJunit(true);
      final TestCaseGenerator tg = new TestCaseGenerator(originalProof, true);
      tg.setLogger(log);
      tg.setFileName(JDTUtil.ensureValidJavaTypeName(testFileName, testProject));
      tg.setPackageName("".equals(testFilePackageName) ? null : testFilePackageName);
      //Add JUnit 4
      Path junitPath = new Path("org.eclipse.jdt.junit.JUNIT_CONTAINER/4");
      IClasspathEntry junitEntry = JavaCore.newContainerEntry(junitPath);
      JDTUtil.addClasspathEntry(testProject, junitEntry);
      // Create library folder
      IFolder libFolder = ResourceUtil.createFolder(testProject.getProject(), LIB_FOLDER_NAME);
      IFile readmeFile = libFolder.getFile(LIB_FOLDER_README_NAME);
      ResourceUtil.createFile(readmeFile, createLibFolderReadmeContent(), null);
      // Create test file
      IContainer packageContainer = sourceContainer;
      IPackageFragment packageFragment = sourceRoot.createPackageFragment(testFilePackageName, true, null);
      IResource packageRes = packageFragment.getResource();
      if(packageRes instanceof IContainer) {
         packageContainer = (IContainer) packageRes;
      }
      final IFile testFile = packageContainer.getFile(new Path(tg.getFileName() + TestCaseGenerator.JAVA_FILE_EXTENSION_WITH_DOT));
      StringBuffer testSb = tg.createTestCaseCotent(problemSolvers);
      ResourceUtil.createFile(testFile, new ByteArrayInputStream(testSb.toString().getBytes()), null);
      // Create RFL file (needs to be done after the test file is created)
      if (tg.isUseRFL() && !tg.isRflAsInternalClass()) {
         StringBuffer rflSb = tg.createRFLFileContent();
         IFile rflFile = sourceContainer.getFile(new Path("RFL.java"));
         ResourceUtil.createFile(rflFile, new ByteArrayInputStream(rflSb.toString().getBytes()), null);
      }
      // Update log
      IFolder logFolder = ResourceUtil.createFolder(testProject.getProject(), LOG_FOLDER_NAME);
      IFile logFile = logFolder.getFile(tg.getFileName() + LOG_FILE_EXTENSION_WITH_DOT);
      ResourceUtil.createFile(logFile, new ByteArrayInputStream(log.toString().getBytes()), null);
      // Select and open generated test file
      if(openTestFile) {
         Display.getDefault().asyncExec(new Runnable() {
            @Override
            public void run() {
               try {
                  WorkbenchUtil.selectAndReveal(testFile);
                  WorkbenchUtil.openEditor(testFile);
               }
               catch (PartInitException e) {
                  LogUtil.getLogger().openErrorDialog(null, e);
               }
            }
         });
      }
   }

   /**
    * Returns the first fund {@link IContainer} of a source location.
    * @param sourceResources The available source {@link IPackageFragmentRoot}s.
    * @return The first found {@link IContainer} or {@code null} if no one was found.
    */
   protected IPackageFragmentRoot findFirstSourceRoot(List<IPackageFragmentRoot> sourceResources) {
      IContainer result = null;
      Iterator<IPackageFragmentRoot> iter = sourceResources.iterator();
      while (result == null && iter.hasNext()) {
         IPackageFragmentRoot root = iter.next();
         IResource resource = root.getResource();
         if (resource instanceof IContainer) {
            return root;
         }
      }
      return null;
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
   public static InputStream createLibFolderReadmeContent() {
      String text = "Add the following libraries to the Java Build Path of this project: " + StringUtil.NEW_LINE +
                    "- Objenesis 2.1" + StringUtil.NEW_LINE +
                    "  http://objenesis.org/download.html" + StringUtil.NEW_LINE +
                    "- JUnit 4.9" + StringUtil.NEW_LINE +
                    "  http://junit.org";
      return new ByteArrayInputStream(text.getBytes());
   }
}
