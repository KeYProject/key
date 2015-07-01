package org.key_project.key4eclipse.resources.builder;

import java.io.ByteArrayInputStream;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaModelException;
import org.key_project.key4eclipse.common.ui.testGeneration.EclipseTestGenerator;
import org.key_project.key4eclipse.common.ui.util.LogUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.StringUtil;
import org.key_project.util.jdt.JDTUtil;

public class TestSuiteGenerator {
   
   IProject testProject;
   IJavaProject testJavaProject;
   List<ProofElement> proofElements;
   public static final String TESTSUITE_TYPENAME = "AllTests";
   public static final String TESTSUITE_PACKAGE = "suite";
   
   
   public TestSuiteGenerator(IProject sourceProject, List<ProofElement> proofElements) {
      testJavaProject = null;
      this.proofElements = proofElements;
      testProject = ResourcesPlugin.getWorkspace().getRoot().getProject(sourceProject.getName() + EclipseTestGenerator.TEST_PROJECT_SUFFIX);
      if(testProject != null && testProject.exists() && testProject.isOpen() && JDTUtil.isJavaProject(testProject)) {
         testJavaProject = JDTUtil.getJavaProject(testProject);
      }
   }
   
   public void cleanUpTestProject(){
      if(testProject != null && testProject.exists() && testProject.isOpen() && testJavaProject != null) {
         IPackageFragmentRoot packageRoot = getPackageRoot();
         if(packageRoot != null) {
            try {
               IPackageFragment testPackage = getPackage(packageRoot, EclipseTestGenerator.TESTCASES_PACKAGE, false);
               if(testPackage != null) {
                  IResource testPackageResource = testPackage.getResource();
                  if(testPackageResource.getType() == IResource.FOLDER && testPackageResource.exists()) {
                     IFolder testPackageFolder = (IFolder) testPackageResource;
                     List<IFile> toDelete = new LinkedList<IFile>();
                     for(IResource member : testPackageFolder.members()) {
                        if(member != null && member.getType() == IResource.FILE) {
                           IFile file = (IFile) member;
                           if(file.exists()) {
                              if(!isInProofElements(file.getName())) {
                                 toDelete.add(file);
                              }
                           }
                        }
                     }
                     for(IFile file : toDelete) {
                        file.delete(true, null);
                     }
                  }
               }
               IPackageFragment suitePackage = getPackage(packageRoot, EclipseTestGenerator.TESTCASES_PACKAGE, false);
               if (suitePackage != null) {
                  IResource suitePackageResource = suitePackage.getResource();
                  if(suitePackageResource.getType() == IResource.FOLDER && suitePackageResource.exists()) {
                     IFolder suitePackageFolder = (IFolder) suitePackageResource;
                     IFile suiteFile = suitePackageFolder.getFile(TESTSUITE_TYPENAME + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT);
                     if(suiteFile != null && suiteFile.exists()) {
                        suiteFile.delete(true, null);
                     }
                  }
               }
            }
            catch (CoreException e) {
               LogUtil.getLogger().logError(e);
            }
         }
      }
   }
   
   public void generateTestSuit() {
      if(testJavaProject != null) {
         IPackageFragmentRoot packageRoot = getPackageRoot();
         if(packageRoot != null) {
            IPackageFragment testPackage = getPackage(packageRoot, EclipseTestGenerator.TESTCASES_PACKAGE, false);
            if(testPackage != null) {
               try {
                  List<String> classes = new LinkedList<String>();
                  for(ICompilationUnit cu : testPackage.getCompilationUnits()) {
                     for(IType type : cu.getTypes()) {
                        String name = type.getTypeQualifiedName();
                        if(!TESTSUITE_TYPENAME.equals(name) && cu.getResource().exists()) {
                           classes.add(name + ".class");
                        }
                     }
                  }
                  IPackageFragment suitePackage = getPackage(packageRoot, TESTSUITE_PACKAGE, true);
                  IResource suitePackageResource = suitePackage.getResource();
                  if(suitePackageResource.getType() == IResource.FOLDER && suitePackageResource.exists()) {
                     IFolder suitePackageFolder = (IFolder) suitePackageResource;
                     IFile testSuiteFile = suitePackageFolder.getFile(TESTSUITE_TYPENAME + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT);
                     Collections.sort(classes);
                     String content = createContent(classes);
                     ResourceUtil.createFile(testSuiteFile, new ByteArrayInputStream(content.getBytes()) , null);
                  }
               }
               catch (CoreException e) {
                  LogUtil.getLogger().logError(e);
               }
            }
         }
      }
   }
   
   private boolean isInProofElements(String name) {
      if(name != null) {
         for(ProofElement pe : proofElements) {
            String validPeName = JDTUtil.ensureValidJavaTypeName(pe.getContract().getName(), testJavaProject) + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT;
            if(name.equals(validPeName)) {
               return true;
            }
         }
      }
      return false;
   }
   
   private IPackageFragmentRoot getPackageRoot(){
      try {
         IPackageFragmentRoot[] roots = testJavaProject.getAllPackageFragmentRoots();
         for(IPackageFragmentRoot r : roots) {
            if(r.getKind() == IPackageFragmentRoot.K_SOURCE && r.getResource() instanceof IContainer) {
               return r;
            }
         }
      }
      catch (JavaModelException e) {
         LogUtil.getLogger().logError(e);
      }
      return null;
   }
   
   private IPackageFragment getPackage(IPackageFragmentRoot root, String name, boolean create){
      IPackageFragment pf = root.getPackageFragment(name);
      if(!pf.exists()) {
         if(!create) {
            return null;
         }
         try {
            pf = root.createPackageFragment(name, true, null);
         }
         catch (JavaModelException e) {
            LogUtil.getLogger().logError(e);
            return null;
         }
      }
      return pf;
   }

   private String createContent(List<String> classes) {
      String newLine = StringUtil.NEW_LINE;
      StringBuffer sb = new StringBuffer();
      sb.append("package " + TESTSUITE_PACKAGE + ";" + newLine);
      sb.append(newLine);
      sb.append("import org.junit.runner.RunWith;" + newLine);
      sb.append("import org.junit.runners.Suite;" + newLine);
      sb.append("import org.junit.runners.Suite.SuiteClasses;" + newLine);
      sb.append(newLine);
      sb.append("import " + EclipseTestGenerator.TESTCASES_PACKAGE + ".*;" + newLine);
      sb.append(newLine);
      sb.append("@RunWith(Suite.class)" + newLine);
      sb.append("@SuiteClasses({" + newLine);
      for(int i = 0; i < classes.size(); i++) {
         sb.append("\t"+classes.get(i));
         if(i < classes.size()-1) {
            sb.append(",");
         }
         sb.append(newLine);
      }
      sb.append("})" + newLine);
      sb.append("public class " + TESTSUITE_TYPENAME + " { }");
      return sb.toString();
   }
}
