package org.key_project.key4eclipse.resources.builder;

import java.util.Arrays;
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
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaModelException;
import org.key_project.key4eclipse.common.ui.testGeneration.EclipseTestGenerator;
import org.key_project.key4eclipse.common.ui.util.LogUtil;
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
         IPackageFragmentRoot packageRoot = getSourcePackageRoot();
         if(packageRoot != null) {
            try {
               IJavaElement[] children = packageRoot.getChildren();
               for(IJavaElement child : children) {
                  if(child instanceof IPackageFragment) {
                     IPackageFragment pf = (IPackageFragment) child;
                     if(pf != null) {
                        IResource pfResource = pf.getResource();
                        if(pfResource.getType() == IResource.FOLDER && pfResource.exists()) {
                           IFolder pfFolder = (IFolder) pfResource;
                           List<IResource> toDelete = new LinkedList<IResource>();
                           for(IResource member : pfFolder.members()) {
                              if(member != null && member.getType() == IResource.FILE) {
                                 IFile file = (IFile) member;
                                 if(file.exists()) {
                                    if(!isInProofElements(file.getName())) {
                                       toDelete.add(file);
                                    }
                                 }
                              }
                           }
                           for(IResource res : toDelete) {
                              res.delete(true, null);
                           }
                           if(pfFolder.members().length == 0) {
                              if(packageRoot.getResource() instanceof IFolder) {
                                 IFolder src = (IFolder) packageRoot.getResource();
                                 List<String> folderList = new LinkedList<String>();
                                 folderList.addAll(Arrays.asList(pf.getElementName().split("\\.")));
                                 while(folderList != null) {
                                    String folderPath = "";
                                    for(String folderPart : folderList) {
                                       folderPath += folderPart + "/";
                                    }
                                    IFolder packageFolder = src.getFolder(folderPath);
                                    if(packageFolder != null && packageFolder.exists() && packageFolder.members().length == 0 && !"".equals(folderPath)) {
                                       packageFolder.delete(true, null);
                                       folderList.remove(folderList.size()-1);
                                    }
                                    else {
                                       folderList = null;
                                    }
                                 }
                              }
                           }
                        }
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
         IPackageFragmentRoot packageRoot = getSourcePackageRoot();
         if(packageRoot != null) {
            try {
               List<String> classes = new LinkedList<String>();
               IJavaElement[] children = packageRoot.getChildren();
               for(IJavaElement child : children) {
                  if(child instanceof IPackageFragment) {
                     IPackageFragment pf = (IPackageFragment) child;
                     if(pf != null) {
                        for(ICompilationUnit cu : pf.getCompilationUnits()) {
                           for(IType type : cu.getTypes()) {
                              String name = type.getFullyQualifiedName();
                              if(!(TESTSUITE_TYPENAME.equals(name) && "".equalsIgnoreCase(pf.getElementName())) && cu.getResource().exists()) {
                                 String className = name + ".class";
                                 if(!classes.contains(className)) {
                                    classes.add(name + ".class");
                                 }
                              }
                           }
                        }
                     }
                  }
               }
               IPackageFragment defaultPackage = getPackage(packageRoot, "", true);
               Collections.sort(classes);
               String content = createContent(classes);
               defaultPackage.createCompilationUnit(TESTSUITE_TYPENAME + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT, content, true, null);
            }
            catch (CoreException e) {
               LogUtil.getLogger().logError(e);
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
   
   private IPackageFragmentRoot getSourcePackageRoot(){
      try {
         List<IPackageFragmentRoot> roots = JDTUtil.getSourcePackageFragmentRoots(testJavaProject);
         for(IPackageFragmentRoot root : roots) {
            if(root.getResource() instanceof IContainer) {
               return root;
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
