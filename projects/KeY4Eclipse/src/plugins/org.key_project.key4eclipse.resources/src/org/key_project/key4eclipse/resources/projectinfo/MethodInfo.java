package org.key_project.key4eclipse.resources.projectinfo;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.Assert;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.jdt.JDTUtil;

/**
 * Represents a method as known by KeY.
 * @author Martin Hentschel
 */
public class MethodInfo extends AbstractContractContainer implements IStatusInfo {
   /**
    * The parent {@link TypeInfo} in which this {@link MethodInfo} is contained in.
    */
   private final TypeInfo parent;
   
   /**
    * The display name.
    */
   private final String displayName;
   
   /**
    * The name.
    */
   private final String name;
   
   /**
    * The full qualified name of the type in which the method is declared.
    */
   private String declaringType;
   
   /**
    * The {@link IFile} in which the type {@link #declaringType} is defined.
    */
   private IFile declaringFile;
   
   /**
    * The full qualified parameter type names.
    */
   private final String[] parameterTypes;
   
   /**
    * Constructor.
    * @param projectInfo The {@link ProjectInfo} in which this {@link PackageInfo} is part of.
    * @param parent The parent {@link TypeInfo} in which this {@link MethodInfo} is contained in.
    * @param displayName The display name.
    * @param name The name.
    * @param declaringType The full qualified name of the type in which the method is declared.
    * @param declaringFile The {@link IFile} in which the type {@link #declaringType} is defined.
    * @param parameterTypes The full qualified parameter type names.
    */
   public MethodInfo(ProjectInfo projectInfo, TypeInfo parent, String displayName, String name, String declaringType, IFile declaringFile, String[] parameterTypes) {
      super(projectInfo);
      Assert.isNotNull(parent);
      Assert.isNotNull(displayName);
      Assert.isNotNull(name);
      Assert.isNotNull(declaringType);
      Assert.isNotNull(parameterTypes);
      this.parent = parent;
      this.displayName = displayName;
      this.name = name;
      this.declaringType = declaringType;
      this.declaringFile = declaringFile;
      this.parameterTypes = parameterTypes;
   }

   /**
    * Returns the parent {@link TypeInfo} in which this {@link MethodInfo} is contained in.
    * @return The parent {@link TypeInfo} in which this {@link MethodInfo} is contained in.
    */
   public TypeInfo getParent() {
      return parent;
   }

   /**
    * Returns the name.
    * @return The name.
    */
   public String getName() {
      return name;
   }

   /**
    * Returns the display name.
    * @return The display name.
    */
   public String getDisplayName() {
      return displayName;
   }
   
   /**
    * Returns the full qualified parameter type names.
    * @return The full qualified parameter type names.
    */
   public String[] getParameterTypes() {
      return parameterTypes;
   }

   /**
    * Returns the full qualified name of the type in which the method is declared.
    * @return The full qualified name of the type in which the method is declared.
    */
   public String getDeclaringType() {
      return declaringType;
   }

   /**
    * Sets the full qualified name of the type in which the method is declared.
    * @param declaringType The full qualified name of the type in which the method is declared.
    */
   public void setDeclaringType(String declaringType) {
      Assert.isNotNull(declaringType);
      this.declaringType = declaringType;
   }

   /**
    * Returns The {@link IFile} in which the type {@link #declaringType} is defined.
    * @return The {@link IFile} in which the type {@link #declaringType} is defined or {@code null} if not available.
    */
   public IFile getDeclaringFile() {
      return declaringFile;
   }

   /**
    * Sets the {@link IFile} in which the type {@link #declaringType} is defined.
    * @param declaringFile The {@link IFile} in which the type {@link #declaringType} is defined or {@code null} if not available.
    */
   public void setDeclaringFile(IFile declaringFile) {
      this.declaringFile = declaringFile;
   }
   
   /**
    * Tries to find the {@link IType} in which this method is declared.
    * @return The found {@link IType} or {@code null} if not available.
    * @throws JavaModelException Occurred Exception.
    */
   public IType findJDTDeclaringType() throws JavaModelException {
      if (declaringFile != null && declaringFile.exists()) {
         ICompilationUnit compilationUnit = null;
         IJavaElement element = JavaCore.create(declaringFile);
         if (element instanceof ICompilationUnit) {
            compilationUnit = (ICompilationUnit)element;
         }
         if (compilationUnit != null) {
            IType[] allTypes = compilationUnit.getAllTypes();
            return ArrayUtil.search(allTypes, new IFilter<IType>() {
               @Override
               public boolean select(IType element) {
                  return declaringType.equals(JDTUtil.getQualifiedTypeName(element));
               }
            });
         }
         else {
            return null;
         }
      }
      else {
         return null;
      }
   }

   /**
    * Tries to find the {@link IMethod} represented by this method.
    * @return The found {@link IMethod} or {@code null} if not available.
    */
   public IMethod findJDTMethod() throws JavaModelException {
      IType jdtType = findJDTDeclaringType();
      if (jdtType != null && jdtType.exists()) {
         return JDTUtil.findJDTMethod(jdtType, name, parameterTypes);
      }
      else {
         return null;
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isUnspecified() {
      return countContracts() == 0;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String toString() {
      return displayName;
   }
}
