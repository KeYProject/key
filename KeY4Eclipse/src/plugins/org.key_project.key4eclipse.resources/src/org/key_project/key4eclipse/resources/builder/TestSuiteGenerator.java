package org.key_project.key4eclipse.resources.builder;

import java.io.ByteArrayInputStream;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

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
import org.key_project.util.jdt.JDTUtil;

public class TestSuiteGenerator {
   
   IProject testProject;
   IJavaProject testJavaProject;
   List<ProofElement> proofElements;
   private final String TESTSUITE_TYPENAME = "_AllTests";
   
   
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
         IPackageFragment defaultPackage = getDefaultPackage();
         if(defaultPackage != null) {
            try {
               IResource defaultPackageResource = defaultPackage.getResource();
               if(defaultPackageResource.getType() == IResource.FOLDER) {
                  IFolder defaultPackageFolder = (IFolder) defaultPackageResource;
                  List<IFile> toDelete = new LinkedList<IFile>();
                  for(IResource member : defaultPackageFolder.members()) {
                     if(member != null && member.getType() == IResource.FILE) {
                        IFile file = (IFile) member;
                        if(file.exists()) {
                           if(!isInProofElementsOrIsSuite(file.getName())) {
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
            catch (CoreException e) {
               LogUtil.getLogger().logError(e);
            }
         }
      }
   }
   
   public void generateTestSuit() {
      if(testJavaProject != null) {
         IPackageFragment defaultPackage = getDefaultPackage();
         if(defaultPackage != null) {
            try {
               List<String> classes = new LinkedList<String>();
               for(ICompilationUnit cu : defaultPackage.getCompilationUnits()) {
                  for(IType type : cu.getTypes()) {
                     String name = type.getTypeQualifiedName();
                     if(!TESTSUITE_TYPENAME.equals(name) && cu.getResource().exists()) {
                        classes.add(name + ".class");
                     }
                  }
               }
               IResource defaultPackageResource = defaultPackage.getResource();
               if(defaultPackageResource.getType() == IResource.FOLDER) {
                  IFolder defaultPackageFolder = (IFolder) defaultPackageResource;
                  IFile testSuiteFile = defaultPackageFolder.getFile(TESTSUITE_TYPENAME + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT);
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
   
   private boolean isInProofElementsOrIsSuite(String name) {
      if(name != null) {
         if(name.equals(TESTSUITE_TYPENAME + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT)) {
            return true;
         }
         for(ProofElement pe : proofElements) {
            String validPeName = JDTUtil.ensureValidJavaTypeName(pe.getContract().getName(), testJavaProject) + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT;
            if(name.equals(validPeName)) {
               return true;
            }
         }
      }
      return false;
   }
   
   private IPackageFragment getDefaultPackage(){
      IPackageFragmentRoot root = null;
      try {
         IPackageFragmentRoot[] roots = testJavaProject.getAllPackageFragmentRoots();
         for(IPackageFragmentRoot r : roots) {
            if(r.getKind() == IPackageFragmentRoot.K_SOURCE) {
               root = r;
               break;
            }
         }
      }
      catch (JavaModelException e) {
         LogUtil.getLogger().logError(e);
      }
      if(root != null) {
         IPackageFragment defaultPackage = root.getPackageFragment("");
         return defaultPackage;
      }
      else {
         return null;
      }
   }

   private String createContent(List<String> classes) {
      String newLine = "\n";
      StringBuffer sb = new StringBuffer();
      sb.append("import org.junit.runner.RunWith;" + newLine);
      sb.append("import org.junit.runners.Suite;" + newLine);
      sb.append("import org.junit.runners.Suite.SuiteClasses;" + newLine);
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
