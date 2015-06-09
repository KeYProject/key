package org.key_project.javaeditor.outline;

import java.io.InputStream;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jdt.core.CompletionRequestor;
import org.eclipse.jdt.core.IAnnotation;
import org.eclipse.jdt.core.IClassFile;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.ICompletionRequestor;
import org.eclipse.jdt.core.IField;
import org.eclipse.jdt.core.IInitializer;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.ISourceRange;
import org.eclipse.jdt.core.ISourceReference;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.ITypeHierarchy;
import org.eclipse.jdt.core.ITypeParameter;
import org.eclipse.jdt.core.ITypeRoot;
import org.eclipse.jdt.core.IWorkingCopy;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.WorkingCopyOwner;

/**
 * Wraps an {@link ICompilationUnit} to change the content in the outline.
 * @author Martin Hentschel
 */
@SuppressWarnings("deprecation")
public class OutlineTypeWrapper extends OutlineJavaElementWrapper<IType> implements IType {
   /**
    * Constructor.
    * @param wrappedObject The wrapped {@link IType}.
    */
   public OutlineTypeWrapper(IType wrappedObject) {
      super(wrappedObject);
   }

   @Override
   public String[] getCategories() throws JavaModelException {
      return getWrappedObject().getCategories();
   }

   @Override
   public IClassFile getClassFile() {
      // TODO Auto-generated method stub
      return getWrappedObject().getClassFile();
   }

   @Override
   public ICompilationUnit getCompilationUnit() {
      // TODO Auto-generated method stub
      return getWrappedObject().getCompilationUnit();
   }

   @Override
   public IType getDeclaringType() {
      // TODO Auto-generated method stub
      return getWrappedObject().getDeclaringType();
   }

   @Override
   public int getFlags() throws JavaModelException {
      // TODO Auto-generated method stub
      return getWrappedObject().getFlags();
   }

   @Override
   public ISourceRange getJavadocRange() throws JavaModelException {
      // TODO Auto-generated method stub
      return getWrappedObject().getJavadocRange();
   }

   @Override
   public int getOccurrenceCount() {
      // TODO Auto-generated method stub
      return getWrappedObject().getOccurrenceCount();
   }

   @Override
   public ITypeRoot getTypeRoot() {
      // TODO Auto-generated method stub
      return getWrappedObject().getTypeRoot();
   }

   @Override
   public IType getType(String name, int occurrenceCount) {
      // TODO Auto-generated method stub
      return getWrappedObject().getType(name,occurrenceCount);
   }

   @Override
   public boolean isBinary() {
      // TODO Auto-generated method stub
      return getWrappedObject().isBinary();
   }

   @Override
   public String getSource() throws JavaModelException {
      // TODO Auto-generated method stub
      return getWrappedObject().getSource();
   }

   @Override
   public ISourceRange getSourceRange() throws JavaModelException {
      // TODO Auto-generated method stub
      return getWrappedObject().getSourceRange();
   }

   @Override
   public ISourceRange getNameRange() throws JavaModelException {
      // TODO Auto-generated method stub
      return getWrappedObject().getNameRange();
   }

   @Override
   public void copy(IJavaElement container, IJavaElement sibling,
         String rename, boolean replace, IProgressMonitor monitor)
         throws JavaModelException {
      // TODO Auto-generated method stub
      getWrappedObject().copy(container, sibling, rename, replace, monitor);
   }

   @Override
   public void delete(boolean force, IProgressMonitor monitor)
         throws JavaModelException {
      // TODO Auto-generated method stub
      getWrappedObject().delete(force, monitor);
   }

   @Override
   public void move(IJavaElement container, IJavaElement sibling,
         String rename, boolean replace, IProgressMonitor monitor)
         throws JavaModelException {
      // TODO Auto-generated method stub
      getWrappedObject().move(container, sibling, rename, replace, monitor);
   }
   

   @Override
   public void rename(String name, boolean replace, IProgressMonitor monitor)
         throws JavaModelException {
      // TODO Auto-generated method stub
      getWrappedObject().rename(name, replace, monitor);
   }

   @Override
   public IJavaElement[] getChildren() throws JavaModelException {
      return getWrappedObject().getChildren();
   }

   @Override
   public boolean hasChildren() throws JavaModelException {
      return getWrappedObject().hasChildren();
   }

   @Override
   public IAnnotation getAnnotation(String name) {
      // TODO Auto-generated method stub
      return getWrappedObject().getAnnotation(name);
   }

   @Override
   public IAnnotation[] getAnnotations() throws JavaModelException {
      // TODO Auto-generated method stub
      return getWrappedObject().getAnnotations();
   }

   @Override
   public void codeComplete(char[] snippet, int insertion, int position,
         char[][] localVariableTypeNames, char[][] localVariableNames,
         int[] localVariableModifiers, boolean isStatic,
         ICompletionRequestor requestor) throws JavaModelException {
      // TODO Auto-generated method stub
      getWrappedObject().codeComplete(snippet, insertion, position, localVariableTypeNames, localVariableNames, localVariableModifiers, isStatic, requestor);
   }

   @Override
   public void codeComplete(char[] snippet, int insertion, int position,
         char[][] localVariableTypeNames, char[][] localVariableNames,
         int[] localVariableModifiers, boolean isStatic,
         ICompletionRequestor requestor, WorkingCopyOwner owner)
         throws JavaModelException {
      // TODO Auto-generated method stub
      getWrappedObject().codeComplete(snippet, insertion, position, localVariableTypeNames, localVariableNames, localVariableModifiers, isStatic, requestor, owner);
   }

   @Override
   public void codeComplete(char[] snippet, int insertion, int position,
         char[][] localVariableTypeNames, char[][] localVariableNames,
         int[] localVariableModifiers, boolean isStatic,
         CompletionRequestor requestor) throws JavaModelException {
      // TODO Auto-generated method stub
      getWrappedObject().codeComplete(snippet, insertion, position, localVariableTypeNames, localVariableNames, localVariableModifiers, isStatic, requestor);
   }

   @Override
   public void codeComplete(char[] snippet, int insertion, int position,
         char[][] localVariableTypeNames, char[][] localVariableNames,
         int[] localVariableModifiers, boolean isStatic,
         CompletionRequestor requestor, IProgressMonitor monitor)
         throws JavaModelException {
      // TODO Auto-generated method stub
      getWrappedObject().codeComplete(snippet, insertion, position, localVariableTypeNames, localVariableNames, localVariableModifiers, isStatic, requestor, monitor);
   }

   @Override
   public void codeComplete(char[] snippet, int insertion, int position,
         char[][] localVariableTypeNames, char[][] localVariableNames,
         int[] localVariableModifiers, boolean isStatic,
         CompletionRequestor requestor, WorkingCopyOwner owner)
         throws JavaModelException {
      // TODO Auto-generated method stub
      getWrappedObject().codeComplete(snippet, insertion, position, localVariableTypeNames, localVariableNames, localVariableModifiers, isStatic, requestor, owner);
   }

   @Override
   public void codeComplete(char[] snippet, int insertion, int position,
         char[][] localVariableTypeNames, char[][] localVariableNames,
         int[] localVariableModifiers, boolean isStatic,
         CompletionRequestor requestor, WorkingCopyOwner owner,
         IProgressMonitor monitor) throws JavaModelException {
      // TODO Auto-generated method stub
      getWrappedObject().codeComplete(snippet, insertion, position, localVariableTypeNames, localVariableNames, localVariableModifiers, isStatic, requestor, owner, monitor);
   }

   @Override
   public IField createField(String contents, IJavaElement sibling,
         boolean force, IProgressMonitor monitor) throws JavaModelException {
      // TODO Auto-generated method stub
      return getWrappedObject().createField(contents, sibling, force, monitor);
   }

   @Override
   public IInitializer createInitializer(String contents, IJavaElement sibling,
         IProgressMonitor monitor) throws JavaModelException {
      // TODO Auto-generated method stub
      return getWrappedObject().createInitializer(contents, sibling, monitor);
   }

   @Override
   public IMethod createMethod(String contents, IJavaElement sibling,
         boolean force, IProgressMonitor monitor) throws JavaModelException {
      // TODO Auto-generated method stub
      return getWrappedObject().createMethod(contents, sibling, force, monitor);
   }

   @Override
   public IType createType(String contents, IJavaElement sibling,
         boolean force, IProgressMonitor monitor) throws JavaModelException {
      // TODO Auto-generated method stub
      return getWrappedObject().createType(contents, sibling, force, monitor);
   }

   @Override
   public IMethod[] findMethods(IMethod method) {
      // TODO Auto-generated method stub
      return getWrappedObject().findMethods(method);
   }

   @Override
   public IJavaElement[] getChildrenForCategory(String category)
         throws JavaModelException {
      // TODO Auto-generated method stub
      return getWrappedObject().getChildrenForCategory(category);
   }

   @Override
   public IField getField(String name) {
      // TODO Auto-generated method stub
      return getWrappedObject().getField(name);
   }

   @Override
   public IField[] getFields() throws JavaModelException {
      // TODO Auto-generated method stub
      return getWrappedObject().getFields();
   }

   @Override
   public String getFullyQualifiedName() {
      // TODO Auto-generated method stub
      return getWrappedObject().getFullyQualifiedName();
   }

   @Override
   public String getFullyQualifiedName(char enclosingTypeSeparator) {
      // TODO Auto-generated method stub
      return getWrappedObject().getFullyQualifiedName(enclosingTypeSeparator);
   }

   @Override
   public String getFullyQualifiedParameterizedName() throws JavaModelException {
      // TODO Auto-generated method stub
      return getWrappedObject().getFullyQualifiedParameterizedName();
   }

   @Override
   public IInitializer getInitializer(int occurrenceCount) {
      // TODO Auto-generated method stub
      return getWrappedObject().getInitializer(occurrenceCount);
   }

   @Override
   public IInitializer[] getInitializers() throws JavaModelException {
      // TODO Auto-generated method stub
      return getWrappedObject().getInitializers();
   }

   @Override
   public String getKey() {
      // TODO Auto-generated method stub
      return getWrappedObject().getKey();
   }

   @Override
   public IMethod getMethod(String name, String[] parameterTypeSignatures) {
      // TODO Auto-generated method stub
      return getWrappedObject().getMethod(name, parameterTypeSignatures);
   }

   @Override
   public IMethod[] getMethods() throws JavaModelException {
      // TODO Auto-generated method stub
      return getWrappedObject().getMethods();
   }

   @Override
   public IPackageFragment getPackageFragment() {
      // TODO Auto-generated method stub
      return getWrappedObject().getPackageFragment();
   }

   @Override
   public String getSuperclassName() throws JavaModelException {
      // TODO Auto-generated method stub
      return getWrappedObject().getSuperclassName();
   }

   @Override
   public String getSuperclassTypeSignature() throws JavaModelException {
      // TODO Auto-generated method stub
      return getWrappedObject().getSuperclassTypeSignature();
   }

   @Override
   public String[] getSuperInterfaceTypeSignatures() throws JavaModelException {
      // TODO Auto-generated method stub
      return getWrappedObject().getSuperInterfaceTypeSignatures();
   }

   @Override
   public String[] getSuperInterfaceNames() throws JavaModelException {
      // TODO Auto-generated method stub
      return getWrappedObject().getSuperInterfaceNames();
   }

   @Override
   public String[] getTypeParameterSignatures() throws JavaModelException {
      // TODO Auto-generated method stub
      return getWrappedObject().getTypeParameterSignatures();
   }

   @Override
   public ITypeParameter[] getTypeParameters() throws JavaModelException {
      // TODO Auto-generated method stub
      return getWrappedObject().getTypeParameters();
   }

   @Override
   public IType getType(String name) {
      // TODO Auto-generated method stub
      return getWrappedObject().getType(name);
   }

   @Override
   public ITypeParameter getTypeParameter(String name) {
      // TODO Auto-generated method stub
      return getWrappedObject().getTypeParameter(name);
   }

   @Override
   public String getTypeQualifiedName() {
      // TODO Auto-generated method stub
      return getWrappedObject().getTypeQualifiedName();
   }

   @Override
   public String getTypeQualifiedName(char enclosingTypeSeparator) {
      // TODO Auto-generated method stub
      return getWrappedObject().getTypeQualifiedName(enclosingTypeSeparator);
   }

   @Override
   public IType[] getTypes() throws JavaModelException {
      // TODO Auto-generated method stub
      return getWrappedObject().getTypes();
   }

   @Override
   public boolean isAnonymous() throws JavaModelException {
      // TODO Auto-generated method stub
      return getWrappedObject().isAnonymous();
   }

   @Override
   public boolean isClass() throws JavaModelException {
      // TODO Auto-generated method stub
      return getWrappedObject().isClass();
   }

   @Override
   public boolean isEnum() throws JavaModelException {
      // TODO Auto-generated method stub
      return getWrappedObject().isEnum();
   }

   @Override
   public boolean isInterface() throws JavaModelException {
      // TODO Auto-generated method stub
      return getWrappedObject().isInterface();
   }

   @Override
   public boolean isAnnotation() throws JavaModelException {
      // TODO Auto-generated method stub
      return getWrappedObject().isAnnotation();
   }

   @Override
   public boolean isLocal() throws JavaModelException {
      // TODO Auto-generated method stub
      return getWrappedObject().isLocal();
   }

   @Override
   public boolean isMember() throws JavaModelException {
      // TODO Auto-generated method stub
      return getWrappedObject().isMember();
   }

   @Override
   public boolean isResolved() {
      // TODO Auto-generated method stub
      return getWrappedObject().isResolved();
   }

   @Override
   public ITypeHierarchy loadTypeHierachy(InputStream input,
         IProgressMonitor monitor) throws JavaModelException {
      // TODO Auto-generated method stub
      return getWrappedObject().loadTypeHierachy(input, monitor);
   }

   @Override
   public ITypeHierarchy newSupertypeHierarchy(IProgressMonitor monitor)
         throws JavaModelException {
      // TODO Auto-generated method stub
      return getWrappedObject().newSupertypeHierarchy(monitor);
   }

   @Override
   public ITypeHierarchy newSupertypeHierarchy(
         ICompilationUnit[] workingCopies, IProgressMonitor monitor)
         throws JavaModelException {
      // TODO Auto-generated method stub
      return getWrappedObject().newSupertypeHierarchy(workingCopies,monitor);
   }

   @Override
   public ITypeHierarchy newSupertypeHierarchy(IWorkingCopy[] workingCopies,
         IProgressMonitor monitor) throws JavaModelException {
      // TODO Auto-generated method stub
      return getWrappedObject().newSupertypeHierarchy(workingCopies, monitor);
   }

   @Override
   public ITypeHierarchy newSupertypeHierarchy(WorkingCopyOwner owner,
         IProgressMonitor monitor) throws JavaModelException {
      // TODO Auto-generated method stub
      return getWrappedObject().newSupertypeHierarchy(owner, monitor);
   }

   @Override
   public ITypeHierarchy newTypeHierarchy(IJavaProject project,
         IProgressMonitor monitor) throws JavaModelException {
      // TODO Auto-generated method stub
      return getWrappedObject().newTypeHierarchy(project, monitor);
   }

   @Override
   public ITypeHierarchy newTypeHierarchy(IJavaProject project,
         WorkingCopyOwner owner, IProgressMonitor monitor)
         throws JavaModelException {
      // TODO Auto-generated method stub
      return getWrappedObject().newTypeHierarchy(project, owner, monitor);
   }

   @Override
   public ITypeHierarchy newTypeHierarchy(IProgressMonitor monitor)
         throws JavaModelException {
      // TODO Auto-generated method stub
      return getWrappedObject().newTypeHierarchy(monitor);
   }

   @Override
   public ITypeHierarchy newTypeHierarchy(ICompilationUnit[] workingCopies,
         IProgressMonitor monitor) throws JavaModelException {
      // TODO Auto-generated method stub
      return getWrappedObject().newTypeHierarchy(workingCopies, monitor);
   }

   @Override
   public ITypeHierarchy newTypeHierarchy(IWorkingCopy[] workingCopies,
         IProgressMonitor monitor) throws JavaModelException {
      // TODO Auto-generated method stub
      return getWrappedObject().newTypeHierarchy(workingCopies,monitor);
   }

   @Override
   public ITypeHierarchy newTypeHierarchy(WorkingCopyOwner owner,
         IProgressMonitor monitor) throws JavaModelException {
      // TODO Auto-generated method stub
      return getWrappedObject().newTypeHierarchy(owner, monitor);
   }

   @Override
   public String[][] resolveType(String typeName) throws JavaModelException {
      // TODO Auto-generated method stub
      return getWrappedObject().resolveType(typeName);
   }

   @Override
   public String[][] resolveType(String typeName, WorkingCopyOwner owner)
         throws JavaModelException {
      // TODO Auto-generated method stub
      return getWrappedObject().resolveType(typeName);
   }

   @Override
   public boolean isLambda() {
      // TODO Auto-generated method stub
      return getWrappedObject().isLambda();
   }
}