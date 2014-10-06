package org.key_project.key4eclipse.resources.projectinfo;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.Assert;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.jdt.JDTUtil;

/**
 * Represents an observer function as known by KeY.
 * @author Martin Hentschel
 */
public class ObserverFunctionInfo extends AbstractContractContainer {
   /**
    * The {@link TypeInfo} in which this {@link ObserverFunctionInfo} is contained in.
    */
   private final TypeInfo parent;
   
   /**
    * The display name.
    */
   private final String displayName;
   
   /**
    * The full qualified name of the type in which the observer function is declared.
    */
   private String declaringType;
   
   /**
    * The {@link IFile} in which the type {@link #declaringType} is defined.
    */
   private IFile declaringFile;

   /**
    * Constructor.
    * @param projectInfo The {@link ProjectInfo} in which this {@link PackageInfo} is part of.
    * @param parent The {@link TypeInfo} in which this {@link ObserverFunctionInfo} is contained in.
    * @param displayName The display name.
    * @param declaringType The full qualified name of the type in which the observer function is declared.
    * @param declaringFile The {@link IFile} in which the type {@link #declaringType} is defined.
    */
   public ObserverFunctionInfo(ProjectInfo projectInfo, TypeInfo parent, String displayName, String declaringType, IFile declaringFile) {
      super(projectInfo);
      Assert.isNotNull(parent);
      Assert.isNotNull(displayName);
      Assert.isNotNull(declaringType);
      this.displayName = displayName;
      this.parent = parent;
      this.declaringType = declaringType;
      this.declaringFile = declaringFile;
   }

   /**
    * Returns the {@link TypeInfo} in which this {@link ObserverFunctionInfo} is contained in.
    * @return The {@link TypeInfo} in which this {@link ObserverFunctionInfo} is contained in.
    */
   public TypeInfo getParent() {
      return parent;
   }

   /**
    * Returns the display name.
    * @return The display name.
    */
   public String getDisplayName() {
      return displayName;
   }

   /**
    * Returns the full qualified name of the type in which the observer function is declared.
    * @return The full qualified name of the type in which the observer function is declared.
    */
   public String getDeclaringType() {
      return declaringType;
   }

   /**
    * Sets the full qualified name of the type in which the observer function is declared.
    * @param declaringType The full qualified name of the type in which the observer function is declared.
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
    * Tries to find the {@link IType} in which this observer function is declared.
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
    * {@inheritDoc}
    */
   @Override
   public String toString() {
      return displayName;
   }
}
