/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.util.jdt;

import java.io.File;
import java.io.IOException;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Assert;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.ILocalVariable;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IPackageDeclaration;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.ISourceRange;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.Signature;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTParser;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.Block;
import org.eclipse.jdt.internal.corext.util.CodeFormatterUtil;
import org.eclipse.jdt.internal.ui.javaeditor.ASTProvider;
import org.eclipse.jdt.internal.ui.viewsupport.JavaElementLabelComposer;
import org.eclipse.jdt.ui.JavaElementLabels;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.ObjectUtil;

/**
 * Provides static methods to work with JDT.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class JDTUtil {
   public static final String JAVA_FILE_EXTENSION = "java";
   
   /**
    * Forbid instances by this private constructor.
    */
   private JDTUtil() {
   }
   
   /**
    * Searches the {@link IMethod} as JDT representation which ends
    * at the given index.
    * @param cu The {@link ICompilationUnit} to search in.
    * @param endIndex The index in the file at that the required method ends.
    * @return The found {@link IMethod} or {@code null} if the JDT representation is not available.
    * @throws JavaModelException Occurred Exception.
    * @throws IOException Occurred Exception.
    */
   public static IMethod findJDTMethod(ICompilationUnit cu, int endIndex) throws JavaModelException, IOException {
      IMethod result = null;
      if (cu != null) {
         IType[] types = cu.getAllTypes();
         int i = 0;
         while (result == null && i < types.length) {
            IMethod[] methods = types[i].getMethods();
            int j = 0;
            while (result == null && j < methods.length) {
               ISourceRange methodRange = methods[j].getSourceRange();
               if (endIndex == methodRange.getOffset() + methodRange.getLength()) {
                  result = methods[j];
               }
               j++;
            }
            i++;
         }
      }
      return result;
   }
   
   /**
    * Returns the tab width used in the given {@link IJavaElement}.
    * @param element The {@link IJavaElement} to get its tab width.
    * @return The tab width.
    */
   public static int getTabWidth(IJavaElement element) {
      return element != null ? CodeFormatterUtil.getTabWidth(element.getJavaProject()) : 0;
   }
   
   /**
    * Returns the first {@link IJavaElement} from the given once that
    * has the given text label.
    * @param elements The {@link IJavaElement}s to search in.
    * @param textLabel The text label for that the {@link IJavaElement} is needed.
    * @return The first found {@link IJavaElement} or {@code null} if no one was found.
    * @throws JavaModelException Occurred Exception 
    */
   public static IMethod getElementForQualifiedMethodLabel(IMethod[] elements, String textLabel) throws JavaModelException {
       IMethod result = null;
       if (elements != null) {
           int i = 0;
           while (result == null && i < elements.length) {
               if (ObjectUtil.equals(textLabel, getQualifiedMethodLabel(elements[i]))) {
                   result = elements[i];
               }
               i++;
           }
       }
       return result;
   }
   
   /**
    * <p>
    * Returns the unique method signature for the given {@link IMethod}.
    * Parameter types are replaced with the full qualified type names.
    * </p>
    * <p>
    * Example method declaration: {@code public int foo(Date ud, java.sql.Date sd)}<br>
    * Created signature: {@code foo(java.util.Date, java.sql.Date)}
    * </p>
    * @param method The {@link IMethod} for that the signature label is needed.
    * @return The created label.
    * @throws JavaModelException Occurred Exception.
    */
   public static String getQualifiedMethodLabel(IMethod method) throws JavaModelException {
      try {
         if (method != null) {
            StringBuffer sb = new StringBuffer();
            sb.append(method.getElementName());
            sb.append("(");
            ILocalVariable[] parameters = method.getParameters();
            boolean afterFirst = false;
            JavaElementLabelComposerHelper c = new JavaElementLabelComposerHelper(sb, method.getDeclaringType());
            for (ILocalVariable parameter : parameters) {
               if (afterFirst) {
                  sb.append(", ");
               }
               else {
                  afterFirst = true;
               }
               c.appendTypeSignatureLabel(parameter, parameter.getTypeSignature(), JavaElementLabels.F_PRE_TYPE_SIGNATURE);
            }
            sb.append(")");
            return sb.toString();
         }
         else {
            return null;
         }
      }
      catch (JavaModelRuntimeException e) {
         throw e.getCause();
      }
   }
   
   /**
    * Returns the full qualified type name of the given method parameter.
    * @param declaringType The {@link IType} that contains the {@link IMethod} which has the given parameter as {@link ILocalVariable} instance.
    * @param parameter The parameter.
    * @return The full qualified name.
    * @throws JavaModelException Occurred Exception.
    */
   public static String getQualifiedParameterType(IType declaringType, ILocalVariable parameter) throws JavaModelException {
      try {
         if (declaringType != null && parameter != null) {
            StringBuffer sb = new StringBuffer();
            JavaElementLabelComposerHelper c = new JavaElementLabelComposerHelper(sb, declaringType);
            c.appendTypeSignatureLabel(parameter, parameter.getTypeSignature(), JavaElementLabels.F_PRE_TYPE_SIGNATURE);
            return sb.toString();
         }
         else {
            return null;
         }
      }
      catch (JavaModelRuntimeException e) {
         throw e.getCause();
      }
   }
   
   /**
    * Utility class to compute the full qualified type of a method parameter.
    * @author Martin Hentschel
    */
   private static class JavaElementLabelComposerHelper extends JavaElementLabelComposer {
      /**
       * The Type that contains the method.
       */
      private IType declaringType;

      /**
       * Constructor.
       * @param buffer The {@link StringBuffer} to fill.
       * @param declaringType The Type that contains the method.
       */
      private JavaElementLabelComposerHelper(StringBuffer buffer, IType declaringType) {
         super(buffer);
         this.declaringType = declaringType;
      }

      /**
       * <p>
       * {@inheritDoc}
       * </p>
       * <p>
       * Changed visibility to public.
       * </p>
       */
      @Override
      public void appendTypeSignatureLabel(IJavaElement enclosingElement, String typeSig, long flags) {
         super.appendTypeSignatureLabel(enclosingElement, typeSig, flags);
      }

      /**
       * Overwritten to return the fulil qualified type name instead of the simple type name.
       */
      @Override
      protected String getSimpleTypeName(IJavaElement enclosingElement, String typeSig) {
         try {
            String simpleName = Signature.toString(Signature.getTypeErasure(typeSig));
            String[][] resolvedTypes = declaringType.resolveType(simpleName);
            if (resolvedTypes != null && resolvedTypes.length > 0) {
               return (resolvedTypes[0][0].equals("") ? "" : resolvedTypes[0][0] + ".") + resolvedTypes[0][1];
            } 
            else {
               return simpleName;
            }
         }
         catch (JavaModelException e) {
            throw new JavaModelRuntimeException(e);
         }
      }
   }
   
   /**
    * A utility {@link RuntimeException} that is used to transfer
    * a {@link JavaModelException} back in the call hierarchy.
    * @author Martin Hentschel
    */
   private static class JavaModelRuntimeException extends RuntimeException {
      /**
       * Generated UID.
       */
      private static final long serialVersionUID = 9027197807876279139L;

      /**
       * Constructor.
       * @param cause The {@link JavaModelException} to wrap.
       */
      private JavaModelRuntimeException(JavaModelException cause) {
         super(cause);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public JavaModelException getCause() {
         return (JavaModelException)super.getCause();
      }
   }
   
   /**
    * Returns a human readable text label for the given {@link IJavaElement}.
    * @param element The {@link IJavaElement} to convert,
    * @return The human readable text label. An empty {@link String} is returned if the given {@link IJavaElement} is {@code null}.
    */
   public static String getTextLabel(IJavaElement element) {
       return JavaElementLabels.getTextLabel(element, JavaElementLabels.ALL_DEFAULT);
   }
   
   /**
    * Returns the first {@link IJavaElement} from the given once that
    * has the given text label.
    * @param elements The {@link IJavaElement}s to search in.
    * @param textLabel The text label for that the {@link IJavaElement} is needed.
    * @return The first found {@link IJavaElement} or {@code null} if no one was found.
    */
   public static IJavaElement getElementForTextLabel(IJavaElement[] elements, String textLabel) {
       IJavaElement result = null;
       if (elements != null) {
           int i = 0;
           while (result == null && i < elements.length) {
               if (ObjectUtil.equals(textLabel, getTextLabel(elements[i]))) {
                   result = elements[i];
               }
               i++;
           }
       }
       return result;
   }
   
   /**
    * Adds the given {@link IClasspathEntry} to the {@link IJavaProject}.
    * @param javaProject The {@link IJavaProject} to add to.
    * @param entryToAdd The {@link IClasspathEntry} to add.
    * @throws JavaModelException Occurred Exception.
    */
   public static void addClasspathEntry(IJavaProject javaProject,
                                        IClasspathEntry entryToAdd) throws JavaModelException {
       if (javaProject != null && entryToAdd != null) {
           IClasspathEntry[] newEntries = ArrayUtil.add(javaProject.getRawClasspath(), entryToAdd);
           javaProject.setRawClasspath(newEntries, null);
       }
   }
   
   /**
    * Returns all {@link IJavaProject}s.
    * @return All {@link IJavaProject}s.
    * @throws JavaModelException
    */
   public static IJavaProject[] getAllJavaProjects() throws JavaModelException {
      return JavaCore.create(ResourcesPlugin.getWorkspace().getRoot()).getJavaProjects();
   }

   /**
    * Returns all available packages.
    * @return All packages.
    * @throws JavaModelException Occurred Exception.
    */
   public static IJavaElement[] getAllPackageFragmentRoot() throws JavaModelException {
      IJavaProject[] jProjects = getAllJavaProjects();
      Set<IJavaElement> packages = new HashSet<IJavaElement>();
      for (IJavaProject jProject : jProjects) {
         IPackageFragmentRoot[] froots = jProject.getAllPackageFragmentRoots();
         for (IPackageFragmentRoot froot : froots) {
            if (froot != null && froot.exists() && !froot.isReadOnly()) {
               IJavaElement[] children = froot.getChildren();
               for (IJavaElement element : children) {
                  packages.add(element);
               }
            }
         }
      }
      return packages.toArray(new IJavaElement[packages.size()]);
   }
   
   /**
    * Returns the package that contains the {@link IJavaElement}.
    * @param element The {@link IJavaElement}.
    * @return The package that contains the given {@link IJavaElement}.
    */
   public static IJavaElement getPackage(IJavaElement element) {
      if (element != null) {
         if (element instanceof IPackageDeclaration) {
            return element;
         }
         else if (element instanceof IPackageFragment) {
            return element;
         }
         else if (element instanceof IPackageFragmentRoot) {
            return element;
         }
         else {
            return getPackage(element.getParent());
         }
      }
      else {
         return null;
      }
   }
   
   /**
    * <p>
    * Returns the {@link IJavaProject} for the given {@link IProject}.
    * </p>
    * <p>
    * <b>Attention:</b> It is also an {@link IJavaProject} returned even
    * if the {@link IProject} is no Java project (has no JDT nature).
    * To verify if an {@link IProject} is a real Java project use
    * {@link JDTUtil#isJavaProject(IProject)}.
    * </p>
    * @param project The {@link IProject} for that an {@link IJavaProject} is needed.
    * @return The {@link IJavaProject} representation of the {@link IProject} or {@code null} if the given {@link IProject} is {@code null}.
    */
   public static IJavaProject getJavaProject(IProject project) {
       return JavaCore.create(project);
   }

   /**
    * <p>
    * Returns the {@link IJavaProject} for the given {@link IProject}.
    * </p>
    * <p>
    * <b>Attention:</b> It is also an {@link IJavaProject} returned even
    * if the {@link IProject} is no Java project (has no JDT nature).
    * To verify if an {@link IProject} is a real Java project use
    * {@link JDTUtil#isJavaProject(IProject)}.
    * </p>
    * @param projectName The name of the {@link IProject} for that an {@link IJavaProject} is needed.
    * @return The {@link IJavaProject} representation of the {@link IProject} with the given name or {@code null} if the given project name is {@code null}/empty.
    */
   public static IJavaProject getJavaProject(String projectName) {
       IProject project = ResourceUtil.getProject(projectName);
       return getJavaProject(project);
   }
   
   /**
    * Checks if the given {@link IProject} is a Java project.
    * @param project The {@link IProject} to check.
    * @return {@code true} is Java project, {@code false} is no Java project.
    */
   public static boolean isJavaProject(IProject project) {
       if (project != null) {
           IJavaProject javaProject = getJavaProject(project);
           return javaProject != null && javaProject.exists();
       }
       else {
           return false;
       }
   }
   
   /**
    * Checks if the given {@link IResource} is a "Java" file.
    * @param file The {@link IResource} to check.
    * @return {@code true} is Java file, {@code false} is something else or {@code null}.
    */
   public static boolean isJavaFile(IResource file) {
      if (file != null) {
         String extension = file.getFileExtension();
         return extension != null && extension.equalsIgnoreCase(JAVA_FILE_EXTENSION);
      }
      else {
         return false;
      }
   }
   
   /**
    * Checks if the given {@link IResource} is or is contained in a source folder of its project.
    * @param resource The {@link IResource} to check.
    * @return {@code true} is source folder of its project or contained in a source folder of its project, {@code false} is somewhere else.
    * @throws JavaModelException Occurred Exception.
    */
   public static boolean isInSourceFolder(IResource resource) throws JavaModelException {
      boolean inSourceFolder = false;
      if (resource != null) {
         IJavaProject javaProject = getJavaProject(resource.getProject());
         if (javaProject != null && javaProject.exists()) {
             IClasspathEntry[] entries = javaProject.getRawClasspath();
             int i = 0;
             while (!inSourceFolder && i < entries.length) {
                if (entries[i].getContentKind() == IPackageFragmentRoot.K_SOURCE) {
                   IPackageFragmentRoot[] roots = javaProject.findPackageFragmentRoots(entries[i]);
                   int j = 0;
                   while (!inSourceFolder && j < roots.length) {
                      IResource rootResource = roots[j].getResource();
                      if (rootResource != null && rootResource.contains(resource)) {
                         inSourceFolder = true;
                      }
                      j++;
                   }
                }
                i++;
             }
         }
      }
      return inSourceFolder;
   }
   
   /**
    * Returns the locations in the local file system of all used
    * source entries in the java build path of the given project.
    * @param project The given Project.
    * @return The found source locations in the file system.
    * @throws JavaModelException Occurred Exception.
    */
   public static List<File> getSourceLocations(IProject project) throws JavaModelException {
       return getSourceLocations(project, new HashSet<IProject>());
   }
   
   /**
    * Internal helper method that is used in {@link #getSourceLocations(IProject)}
    * to compute the source path. It is required to solve cycles in project dependencies.
    * @param project The given Project.
    * @param alreadyHandledProjects The already handled {@link IProject} that don't need to be analysed again.
    * @return The found source locations in the file system.
    * @throws JavaModelException Occurred Exception.
    */    
   private static List<File> getSourceLocations(IProject project, Set<IProject> alreadyHandledProjects) throws JavaModelException {
       List<File> result = new LinkedList<File>();
       if (project != null) {
           Assert.isNotNull(alreadyHandledProjects);
           alreadyHandledProjects.add(project);
           IJavaProject javaProject = getJavaProject(project);
           if (javaProject != null && javaProject.exists()) {
               IClasspathEntry[] entries = javaProject.getRawClasspath();
               for (IClasspathEntry entry : entries) {
                   if (entry.getContentKind() == IPackageFragmentRoot.K_SOURCE) {
                       List<File> location = getLocationFor(javaProject, entry, IPackageFragmentRoot.K_SOURCE, alreadyHandledProjects);
                       if (location != null) {
                           result.addAll(location);
                       }
                   }
               }
           }
       }
       return result;
   }
   
   /**
    * Returns the locations of the given {@link IClasspathEntry}.
    * @param javaProject The actual {@link IJavaProject} that provides the {@link IClasspathEntry}.
    * @param entry The given {@link IClasspathEntry}.
    * @param alreadyHandledProjects The already handled {@link IProject} that don't need to be analysed again.
    * @return The found locations.
    * @throws JavaModelException 
    */
   private static List<File> getLocationFor(IJavaProject javaProject, 
                                            IClasspathEntry entry,
                                            int expectedKind,
                                            Set<IProject> alreadyHandledProjects) throws JavaModelException {
       if (entry != null) {
           if (entry.getEntryKind() == IClasspathEntry.CPE_CONTAINER ||
               entry.getEntryKind() == IClasspathEntry.CPE_SOURCE ||
               entry.getEntryKind() == IClasspathEntry.CPE_LIBRARY ||
               entry.getEntryKind() == IClasspathEntry.CPE_VARIABLE) {
               List<File> result = new LinkedList<File>();
               IPackageFragmentRoot[] roots = javaProject.findPackageFragmentRoots(entry);
               for (IPackageFragmentRoot root : roots) {
                   if (root.getKind() == expectedKind) {
                       if (root.getResource() != null) {
                           if (root.getResource().getLocationURI() != null) {
                               result.add(ResourceUtil.getLocation(root.getResource()));
                           }
                       }
                       else if (root.getPath() != null) {
                           File location = new File(root.getPath().toString());
                           if (location.exists()) {
                               result.add(location);
                           }
                       }
                   }
               }
               return result; // Ignore containers
           }
           else if (entry.getEntryKind() == IClasspathEntry.CPE_PROJECT) {
               Assert.isNotNull(entry.getPath());
               IResource project = ResourcesPlugin.getWorkspace().getRoot().findMember(entry.getPath());
               Assert.isTrue(project instanceof IProject);
               if (!alreadyHandledProjects.contains(project)) {
                   return getSourceLocations((IProject)project, alreadyHandledProjects);
               }
               else {
                   return null; // Project was already analyzed, no need to do it again.
               }
           }
           else {
               Assert.isTrue(false, "Unknown content kind \"" + entry.getContentKind() + "\" of class path entry \"" + entry + "\".");
               return null;
           }
       }
       else {
           return null;
       }
   }
   
   /**
    * Parses the given {@link ICompilationUnit} in the specified range into an AST. 
    * @param compilationUnit The {@link ICompilationUnit} to parse.
    * @param offset The start index in the text to parse.
    * @param length The length of the text to parse.
    * @return The {@link ASTNode} which is the root of the AST.
    */
   public static ASTNode parse(ICompilationUnit compilationUnit, int offset, int length) {
      ASTParser parser = ASTParser.newParser(ASTProvider.SHARED_AST_LEVEL); // Hopefully always the newest AST level (e.g. AST.JLS4)
      parser.setSource(compilationUnit);
      parser.setSourceRange(offset, length);
      return parser.createAST(null);
   }
   
   /**
    * Returns the {@link Block} which represents the method body
    * of the given {@link IMethod} in an {@link ASTParser}.
    * @param method The {@link IMethod} to lookup its body.
    * @return The found {@link Block} or {@code null} if not available.
    * @throws JavaModelException Occurred Exception.
    */
   public static Block getMethodBody(IMethod method) throws JavaModelException {
      if (method != null) {
         int methodStart = method.getSourceRange().getOffset();
         int methodLength = method.getSourceRange().getLength();
         ASTNode node = JDTUtil.parse(method.getCompilationUnit(), methodStart, methodLength);
         MethodBodySearcher searcher = new MethodBodySearcher(methodStart, methodLength);
         node.accept(searcher);
         return searcher.getResult();
      }
      else {
         return null;
      }
   }
   
   /**
    * Utility class used by {@link JDTUtil#getMethodBody(IMethod)}
    * to compute the result.
    * @author Martin Hentschel
    */
   private static class MethodBodySearcher extends ASTVisitor {
      /**
       * The result.
       */
      private Block result;
      
      /**
       * The start index of the method.
       */
      private int methodStart;
      
      /**
       * The end index of the method.
       */
      private int methodEnd;
      
      /**
       * Constructor.
       * @param methodStart The start index of the method.
       * @param methodLength The end index of the method.
       */
      public MethodBodySearcher(int methodStart, int methodLength) {
         this.methodStart = methodStart;
         this.methodEnd = methodStart + methodLength;
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public boolean visit(Block node) {
         if (node.getStartPosition() >= methodStart &&
             node.getStartPosition() + node.getLength() <= methodEnd) {
            result = node;
            return false;
         }
         else {
            return true;
         }
      }

      /**
       * Returns the result.
       * @return The result.
       */
      public Block getResult() {
         return result;
      }
   }
}